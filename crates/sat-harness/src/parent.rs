//! Parent-process scheduling and child outcome classification.

use std::collections::VecDeque;
use std::env;
use std::fs;
use std::io::{self, IsTerminal};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use indicatif::{HumanCount, HumanDuration};
use tempfile::NamedTempFile;

use crate::cli::RunArgs;
use crate::discover::discover_cases;
use crate::model::{
    CaseOutcome, CaseSpec, ChildReport, ChildReportKind, ExpectedResult, OutcomeCategory,
    OutcomeStats, RunSummary,
};
use crate::render::{build_progress_bar, format_failure, print_summary, progress_message};
use crate::util::{default_jobs, exit_signal, trim_detail};

/// Executes the top-level parent harness flow.
pub(crate) fn run_parent(args: RunArgs) -> Result<RunSummary, String> {
    let requested_roots = if args.roots.is_empty() {
        vec![PathBuf::from("test/fixture/sat")]
    } else {
        args.roots
    };
    let cases = discover_cases(&requested_roots)?;
    if cases.is_empty() {
        return Err("no supported benchmark cases were found".to_string());
    }

    let jobs = args
        .jobs
        .unwrap_or_else(default_jobs)
        .get()
        .min(cases.len())
        .max(1);
    let total = cases.len();
    let current_exe = env::current_exe()
        .map_err(|error| format!("failed to locate current executable: {error}"))?;
    let queue = Arc::new(Mutex::new(VecDeque::from(cases)));
    let (sender, receiver) = mpsc::channel();
    let mut handles = Vec::with_capacity(jobs);

    for _ in 0..jobs {
        let worker_queue = Arc::clone(&queue);
        let worker_sender = sender.clone();
        let worker_exe = current_exe.clone();
        let timeout = args.timeout;
        handles.push(thread::spawn(move || {
            worker_loop(worker_queue, worker_sender, worker_exe, timeout);
        }));
    }
    drop(sender);

    let interactive = io::stderr().is_terminal();
    let progress_bar = build_progress_bar(total, interactive);
    if !interactive {
        eprintln!(
            "running {} cases with {} workers (timeout {})",
            HumanCount(total as u64),
            HumanCount(jobs as u64),
            HumanDuration(args.timeout),
        );
    }

    let started = Instant::now();
    let mut outcomes = Vec::with_capacity(total);
    let mut stats = OutcomeStats::default();

    for outcome in receiver {
        stats.record(outcome.category);
        progress_bar.inc(1);
        progress_bar.set_message(progress_message(&stats, jobs));
        if outcome.category.is_failure() {
            let rendered = format_failure(&outcome);
            if interactive {
                progress_bar.println(rendered);
            } else {
                eprintln!("{rendered}");
            }
        }
        outcomes.push(outcome);
    }

    for handle in handles {
        handle
            .join()
            .map_err(|_| "worker thread panicked in parent harness".to_string())?;
    }

    let elapsed = started.elapsed();
    progress_bar.finish_and_clear();
    print_summary(&outcomes, &stats, elapsed, jobs, args.slowest);
    Ok(RunSummary { stats })
}

/// Repeatedly executes cases from the shared queue until all work is exhausted.
fn worker_loop(
    queue: Arc<Mutex<VecDeque<CaseSpec>>>,
    sender: mpsc::Sender<CaseOutcome>,
    current_exe: PathBuf,
    timeout: Duration,
) {
    loop {
        let next_case = match queue.lock() {
            Ok(mut queue) => queue.pop_front(),
            Err(_) => None,
        };
        let Some(case) = next_case else {
            break;
        };
        let outcome = run_case_subprocess(&current_exe, case, timeout);
        if sender.send(outcome).is_err() {
            break;
        }
    }
}

/// Executes one case in a fresh child process and classifies its outcome.
fn run_case_subprocess(current_exe: &Path, case: CaseSpec, timeout: Duration) -> CaseOutcome {
    let started = Instant::now();
    let report_file = match NamedTempFile::new() {
        Ok(file) => file,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("tempfile error: {error}"));
        }
    };
    let stderr_file = match NamedTempFile::new() {
        Ok(file) => file,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("tempfile error: {error}"));
        }
    };
    let stderr_stdio = match stderr_file.reopen() {
        Ok(file) => Stdio::from(file),
        Err(error) => {
            return harness_error(
                case,
                started.elapsed(),
                format!("stderr capture error: {error}"),
            );
        }
    };

    let mut child = match Command::new(current_exe)
        .arg("__internal-run-case")
        .arg("--case")
        .arg(&case.absolute_path)
        .arg("--report")
        .arg(report_file.path())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr_stdio)
        .spawn()
    {
        Ok(child) => child,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("spawn error: {error}"));
        }
    };

    let mut timed_out = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if started.elapsed() >= timeout {
                    timed_out = true;
                    let _ = child.kill();
                    match child.wait() {
                        Ok(status) => break status,
                        Err(error) => {
                            return harness_error(
                                case,
                                started.elapsed(),
                                format!("failed to wait after timeout: {error}"),
                            );
                        }
                    }
                }
                thread::sleep(Duration::from_millis(10));
            }
            Err(error) => {
                return harness_error(case, started.elapsed(), format!("wait error: {error}"));
            }
        }
    };

    let elapsed = started.elapsed();
    if timed_out {
        return CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::Timeout,
            actual: None,
            detail: Some(format!("timed out after {}", humantime::format_duration(timeout)).into()),
            variables: None,
        };
    }

    let stderr = fs::read_to_string(stderr_file.path()).unwrap_or_default();
    let report_text = fs::read_to_string(report_file.path()).ok();
    classify_child_completion(case, elapsed, status, report_text.as_deref(), &stderr)
}

/// Classifies a completed child process into a stable harness outcome.
fn classify_child_completion(
    case: CaseSpec,
    elapsed: Duration,
    status: ExitStatus,
    report_text: Option<&str>,
    stderr: &str,
) -> CaseOutcome {
    if status.success() {
        let Some(report_text) = report_text else {
            return harness_error(case, elapsed, "missing child report".to_string());
        };
        let report: ChildReport = match serde_json::from_str(report_text) {
            Ok(report) => report,
            Err(error) => {
                return harness_error(case, elapsed, format!("invalid child report: {error}"));
            }
        };
        return classify_report(case, elapsed, report);
    }

    let signal = exit_signal(status);
    let stderr = stderr.trim();
    if stderr.contains("panicked at") {
        return CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::Panic,
            actual: None,
            detail: Some(trim_detail(stderr).into()),
            variables: None,
        };
    }

    if let Some(signal) = signal {
        let detail = if signal == 9 {
            "terminated by SIGKILL (possible OOM kill)".to_string()
        } else {
            format!("terminated by signal {signal}")
        };
        return CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::Killed,
            actual: None,
            detail: Some(detail.into()),
            variables: None,
        };
    }

    let detail = match status.code() {
        Some(code) => {
            if stderr.is_empty() {
                format!("child exited with status code {code}")
            } else {
                format!(
                    "child exited with status code {code}: {}",
                    trim_detail(stderr)
                )
            }
        }
        None => "child exited without status code".to_string(),
    };
    harness_error(case, elapsed, detail)
}

/// Maps a structured child report onto the final parent outcome categories.
fn classify_report(case: CaseSpec, elapsed: Duration, report: ChildReport) -> CaseOutcome {
    match report.kind {
        ChildReportKind::Sat | ChildReportKind::Unsat => {
            let actual = match report.kind {
                ChildReportKind::Sat => ExpectedResult::Sat,
                ChildReportKind::Unsat => ExpectedResult::Unsat,
                ChildReportKind::ParseError(_) | ChildReportKind::InputError(_) => unreachable!(),
            };
            match case.expected {
                Some(expected) if expected == actual => CaseOutcome {
                    case,
                    elapsed,
                    category: OutcomeCategory::Pass,
                    actual: Some(actual),
                    detail: None,
                    variables: Some(report.variables),
                },
                Some(expected) => CaseOutcome {
                    detail: Some(
                        format!(
                            "expected {} from {}, got {}",
                            expected.as_str(),
                            case.source.as_deref().unwrap_or("manifest"),
                            actual.as_str()
                        )
                        .into(),
                    ),
                    case,
                    elapsed,
                    category: OutcomeCategory::WrongAnswer,
                    actual: Some(actual),
                    variables: Some(report.variables),
                },
                None => CaseOutcome {
                    case,
                    elapsed,
                    category: OutcomeCategory::NoOracle,
                    actual: Some(actual),
                    detail: None,
                    variables: Some(report.variables),
                },
            }
        }
        ChildReportKind::ParseError(error) => CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::ParseError,
            actual: None,
            detail: Some(trim_detail(&error).into()),
            variables: Some(report.variables),
        },
        ChildReportKind::InputError(error) => harness_error(case, elapsed, error),
    }
}

/// Creates one infrastructure error outcome.
fn harness_error(case: CaseSpec, elapsed: Duration, detail: String) -> CaseOutcome {
    CaseOutcome {
        case,
        elapsed,
        category: OutcomeCategory::HarnessError,
        actual: None,
        detail: Some(detail.into()),
        variables: None,
    }
}
