//! Parent-process scheduling and child outcome classification.

use std::collections::VecDeque;
use std::env;
use std::fs;
use std::io::{self, IsTerminal};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use indicatif::{HumanCount, HumanDuration};
use tempfile::NamedTempFile;

use crate::cli::RunArgs;
use crate::discover::discover_cases;
use crate::model::{
    CaseOutcome, ChildReport, ChildReportKind, DiscoveredCase, ExpectedResult, OutcomeCategory,
    OutcomeStats, RunSummary,
};
use crate::render::{
    PROGRESS_HEARTBEAT_INTERVAL, build_progress_bar, format_outcome, print_summary,
    print_written_summary, progress_message,
};
use crate::util::{default_jobs, exit_signal, trim_detail};

/// Executes the top-level parent harness flow.
pub(crate) fn run_parent(args: RunArgs) -> Result<RunSummary, String> {
    let RunArgs {
        roots,
        jobs,
        timeout,
        all: print_all_outcomes,
        save,
    } = args;

    let requested_roots = if roots.is_empty() {
        vec![PathBuf::from("test/fixture/sat")]
    } else {
        roots
    };
    let cases = discover_cases(&requested_roots)?;
    if cases.is_empty() {
        return Err("no supported benchmark cases were found".to_string());
    }

    let jobs = jobs
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
        let worker_timeout = timeout;
        handles.push(thread::spawn(move || {
            worker_loop(worker_queue, worker_sender, worker_exe, worker_timeout);
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
            HumanDuration(timeout),
        );
    }

    let started = Instant::now();
    let mut outcomes = Vec::with_capacity(total);
    let mut stats = OutcomeStats::default();
    progress_bar.set_message(progress_message(&stats, total.min(jobs)));

    while outcomes.len() < total {
        match receiver.recv_timeout(PROGRESS_HEARTBEAT_INTERVAL) {
            Ok(outcome) => {
                stats.record(outcome.category);
                progress_bar.inc(1);
                progress_bar.set_message(progress_message(
                    &stats,
                    total.saturating_sub(stats.done).min(jobs),
                ));
                if should_print_outcome(print_all_outcomes, outcome.category) {
                    let rendered = format_outcome(&outcome);
                    if interactive {
                        progress_bar.println(rendered);
                    } else {
                        eprintln!("{rendered}");
                    }
                }
                outcomes.push(outcome);
            }
            Err(RecvTimeoutError::Timeout) => {
                progress_bar.set_message(progress_message(
                    &stats,
                    total.saturating_sub(stats.done).min(jobs),
                ));
                if !interactive {
                    continue;
                }
                progress_bar.tick();
            }
            Err(RecvTimeoutError::Disconnected) => {
                break;
            }
        }
    }

    for handle in handles {
        handle
            .join()
            .map_err(|_| "worker thread panicked in parent harness".to_string())?;
    }

    let elapsed = started.elapsed();
    progress_bar.finish_and_clear();
    print_summary(&outcomes, &stats, elapsed, jobs);
    outcomes.sort_by(|left, right| left.case.comparison_key().cmp(right.case.comparison_key()));

    let summary = RunSummary {
        format_version: RunSummary::FORMAT_VERSION,
        roots: requested_roots.into_boxed_slice(),
        jobs,
        timeout,
        total_elapsed: elapsed,
        cases: outcomes,
        stats,
    };

    if let Some(path) = save {
        write_summary_file(&path, &summary)?;
        print_written_summary(&path);
    }

    Ok(summary)
}

/// Returns whether one completed case should be printed immediately.
fn should_print_outcome(print_all_outcomes: bool, category: OutcomeCategory) -> bool {
    print_all_outcomes || category.is_failure()
}

/// Repeatedly executes cases from the shared queue until all work is exhausted.
fn worker_loop(
    queue: Arc<Mutex<VecDeque<DiscoveredCase>>>,
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
fn run_case_subprocess(current_exe: &Path, case: DiscoveredCase, timeout: Duration) -> CaseOutcome {
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
        .arg(case.absolute_path())
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
            case: case.into_record(),
            elapsed,
            category: OutcomeCategory::Timeout,
            detail: None,
        };
    }

    let stderr = fs::read_to_string(stderr_file.path()).unwrap_or_default();
    let report_text = fs::read_to_string(report_file.path()).ok();
    classify_child_completion(case, elapsed, status, report_text.as_deref(), &stderr)
}

/// Classifies a completed child process into a stable harness outcome.
fn classify_child_completion(
    case: DiscoveredCase,
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
            case: case.into_record(),
            elapsed,
            category: OutcomeCategory::Panic,
            detail: Some(trim_detail(stderr).into()),
        };
    }

    if let Some(signal) = signal {
        let detail = if signal == 9 {
            "terminated by SIGKILL (possible OOM kill)".to_string()
        } else {
            format!("terminated by signal {signal}")
        };
        return CaseOutcome {
            case: case.into_record(),
            elapsed,
            category: OutcomeCategory::Killed,
            detail: Some(detail.into()),
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
fn classify_report(case: DiscoveredCase, elapsed: Duration, report: ChildReport) -> CaseOutcome {
    match report.kind {
        ChildReportKind::Sat | ChildReportKind::Unsat => {
            let actual = match report.kind {
                ChildReportKind::Sat => ExpectedResult::Sat,
                ChildReportKind::Unsat => ExpectedResult::Unsat,
                ChildReportKind::ParseError(_) | ChildReportKind::InputError(_) => unreachable!(),
            };
            let record = case.record();
            match record.expected {
                Some(expected) if expected == actual => CaseOutcome {
                    case: case.into_record(),
                    elapsed,
                    category: OutcomeCategory::Pass,
                    detail: None,
                },
                Some(expected) => CaseOutcome {
                    detail: Some(
                        format!(
                            "expected {} from {}, got {}",
                            expected.as_str(),
                            record.source.as_deref().unwrap_or("manifest"),
                            actual.as_str()
                        )
                        .into(),
                    ),
                    case: case.into_record(),
                    elapsed,
                    category: OutcomeCategory::WrongAnswer,
                },
                None => CaseOutcome {
                    case: case.into_record(),
                    elapsed,
                    category: OutcomeCategory::NoOracle,
                    detail: None,
                },
            }
        }
        ChildReportKind::ParseError(error) => CaseOutcome {
            case: case.into_record(),
            elapsed,
            category: OutcomeCategory::ParseError,
            detail: Some(trim_detail(&error).into()),
        },
        ChildReportKind::InputError(error) => harness_error(case, elapsed, error),
    }
}

/// Creates one infrastructure error outcome.
fn harness_error(case: DiscoveredCase, elapsed: Duration, detail: String) -> CaseOutcome {
    CaseOutcome {
        case: case.into_record(),
        elapsed,
        category: OutcomeCategory::HarnessError,
        detail: Some(detail.into()),
    }
}

/// Writes one complete run summary to the requested JSON output path.
fn write_summary_file(path: &Path, summary: &RunSummary) -> Result<(), String> {
    let payload = serde_json::to_vec_pretty(summary)
        .map_err(|error| format!("failed to serialize run summary: {error}"))?;
    fs::write(path, payload)
        .map_err(|error| format!("failed to write run summary {}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::time::Duration;

    use super::{should_print_outcome, write_summary_file};
    use crate::model::{
        CaseOutcome, CaseRecord, ExpectedResult, OutcomeCategory, OutcomeStats, RunSummary,
    };

    /// Ensures the default live stream remains failure-only.
    #[test]
    fn default_output_filters_successes() {
        assert!(!should_print_outcome(false, OutcomeCategory::Pass));
        assert!(should_print_outcome(false, OutcomeCategory::WrongAnswer));
    }

    /// Ensures the verbose mode prints every completed case outcome.
    #[test]
    fn verbose_output_prints_every_outcome() {
        assert!(should_print_outcome(true, OutcomeCategory::Pass));
        assert!(should_print_outcome(true, OutcomeCategory::NoOracle));
    }

    /// Ensures saved summaries round-trip through the JSON artifact writer.
    #[test]
    fn write_summary_file_serializes_json() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        let path = temp_dir.path().join("summary.json");
        let summary = RunSummary {
            format_version: RunSummary::FORMAT_VERSION,
            roots: vec![PathBuf::from("test/fixture/sat")].into_boxed_slice(),
            jobs: 2,
            timeout: Duration::from_secs(30),
            total_elapsed: Duration::from_millis(50),
            cases: vec![CaseOutcome {
                case: CaseRecord {
                    key: "cases/example.cnf".into(),
                    bytes: 12,
                    expected: Some(ExpectedResult::Sat),
                    source: Some("fixture".into()),
                },
                elapsed: Duration::from_millis(5),
                category: OutcomeCategory::Pass,
                detail: None,
            }],
            stats: OutcomeStats {
                done: 1,
                pass: 1,
                ..OutcomeStats::default()
            },
        };

        write_summary_file(&path, &summary).expect("write summary");
        let round_trip: RunSummary =
            serde_json::from_str(&std::fs::read_to_string(path).expect("read summary"))
                .expect("parse summary");
        assert_eq!(round_trip.format_version, RunSummary::FORMAT_VERSION);
        assert_eq!(round_trip.cases.len(), 1);
        assert_eq!(
            round_trip.cases[0].case.comparison_key(),
            "cases/example.cnf"
        );
    }
}
