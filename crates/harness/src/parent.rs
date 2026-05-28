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
#[cfg(feature = "telemetry")]
use telemetry::{Sample, Summary};
use tempfile::NamedTempFile;

use crate::cli::{OutputMode, RunArgs};
use crate::discover::discover_cases;
use crate::jobs::default_jobs;
use crate::model::{
    CaseOutcome, CaseTelemetry, ChildReport, ChildReportKind, DiscoveredCase, OutcomeCategory,
    OutcomeStats, QueryAnswer, QueryOutcome, RunSummary,
};
use crate::render::{
    PROGRESS_HEARTBEAT_INTERVAL, build_progress_bar, format_outcome, print_summary,
    print_written_summary, progress_message,
};
use crate::util::{exit_signal, trim_detail};

/// Executes the top-level parent harness flow.
pub(crate) fn run_parent(args: RunArgs) -> Result<RunSummary, String> {
    let output_mode = args.output_mode();
    let RunArgs {
        roots,
        jobs,
        timeout,
        save,
        ..
    } = args;

    let requested_roots = if roots.is_empty() {
        vec![PathBuf::from(".")]
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
    let retain_telemetry_samples = save.is_some();

    for _ in 0..jobs {
        let worker_queue = Arc::clone(&queue);
        let worker_sender = sender.clone();
        let worker_exe = current_exe.clone();
        let worker_timeout = timeout;
        let worker_retain_telemetry_samples = retain_telemetry_samples;
        handles.push(thread::spawn(move || {
            worker_loop(
                worker_queue,
                worker_sender,
                worker_exe,
                worker_timeout,
                worker_retain_telemetry_samples,
            );
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
                if should_print_outcome(output_mode, outcome.category) {
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
fn should_print_outcome(output_mode: OutputMode, category: OutcomeCategory) -> bool {
    match output_mode {
        OutputMode::All => true,
        OutputMode::FailOnly => category.is_failure(),
        OutputMode::Terse => false,
    }
}

/// Repeatedly executes cases from the shared queue until all work is exhausted.
fn worker_loop(
    queue: Arc<Mutex<VecDeque<DiscoveredCase>>>,
    sender: mpsc::Sender<CaseOutcome>,
    current_exe: PathBuf,
    timeout: Duration,
    retain_telemetry_samples: bool,
) {
    loop {
        let next_case = match queue.lock() {
            Ok(mut queue) => queue.pop_front(),
            Err(_) => None,
        };
        let Some(case) = next_case else {
            break;
        };
        let outcome = run_case_subprocess(&current_exe, case, timeout, retain_telemetry_samples);
        if sender.send(outcome).is_err() {
            break;
        }
    }
}

/// Executes one case in a fresh child process and classifies its outcome.
fn run_case_subprocess(
    current_exe: &Path,
    case: DiscoveredCase,
    timeout: Duration,
    retain_telemetry_samples: bool,
) -> CaseOutcome {
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
    let telemetry_file = match create_telemetry_file() {
        Ok(file) => file,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("tempfile error: {error}"));
        }
    };

    let mut command = Command::new(current_exe);
    command
        .arg("case")
        .arg(case.absolute_path())
        .arg("--report")
        .arg(report_file.path())
        .arg("--expected-query-count")
        .arg(case.expected_queries().len().to_string());
    #[cfg(feature = "telemetry")]
    {
        let telemetry_path = telemetry_file
            .as_ref()
            .expect("telemetry temp file exists when feature is enabled")
            .path();
        command.arg("--telemetry").arg(telemetry_path);
    }

    let mut child = match command
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
            total_elapsed: elapsed,
            category: OutcomeCategory::Timeout,
            queries: Vec::new(),
            detail: None,
            telemetry: load_case_telemetry(
                telemetry_file.as_ref().map(NamedTempFile::path),
                retain_telemetry_samples,
            )
            .ok()
            .flatten(),
        };
    }

    let stderr = fs::read_to_string(stderr_file.path()).unwrap_or_default();
    let report_text = fs::read_to_string(report_file.path()).ok();
    let telemetry = load_case_telemetry(
        telemetry_file.as_ref().map(NamedTempFile::path),
        retain_telemetry_samples,
    );
    classify_child_completion(
        case,
        elapsed,
        status,
        report_text.as_deref(),
        &stderr,
        telemetry,
    )
}

/// Creates the child telemetry file only when the feature is enabled.
#[cfg(feature = "telemetry")]
fn create_telemetry_file() -> Result<Option<NamedTempFile>, std::io::Error> {
    NamedTempFile::new().map(Some)
}

/// Skips telemetry tempfile creation when the feature is disabled.
#[cfg(not(feature = "telemetry"))]
fn create_telemetry_file() -> Result<Option<NamedTempFile>, std::io::Error> {
    Ok(None)
}

/// Classifies a completed child process into a stable harness outcome.
fn classify_child_completion(
    case: DiscoveredCase,
    elapsed: Duration,
    status: ExitStatus,
    report_text: Option<&str>,
    stderr: &str,
    telemetry: Result<Option<CaseTelemetry>, String>,
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
        let telemetry = match telemetry {
            Ok(telemetry) => telemetry,
            Err(error) => {
                return harness_error(case, elapsed, format!("invalid child telemetry: {error}"));
            }
        };
        return classify_report(case, elapsed, report, telemetry);
    }

    let signal = exit_signal(status);
    let stderr = stderr.trim();
    let telemetry = telemetry.ok().flatten();
    if stderr.contains("panicked at") {
        return CaseOutcome {
            case: case.into_record(),
            total_elapsed: elapsed,
            category: OutcomeCategory::Panic,
            queries: Vec::new(),
            detail: Some(trim_detail(stderr).into()),
            telemetry,
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
            total_elapsed: elapsed,
            category: OutcomeCategory::Killed,
            queries: Vec::new(),
            detail: Some(detail.into()),
            telemetry,
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
    let mut outcome = harness_error(case, elapsed, detail);
    outcome.telemetry = telemetry;
    outcome
}

/// Maps a structured child report onto the final parent outcome categories.
fn classify_report(
    case: DiscoveredCase,
    elapsed: Duration,
    report: ChildReport,
    telemetry: Option<CaseTelemetry>,
) -> CaseOutcome {
    match report.kind {
        ChildReportKind::Completed(run) => classify_completed_run(case, elapsed, run, telemetry),
        ChildReportKind::ParseError(error) => CaseOutcome {
            case: case.into_record(),
            total_elapsed: elapsed,
            category: OutcomeCategory::ParseError,
            queries: Vec::new(),
            detail: Some(trim_detail(&error).into()),
            telemetry,
        },
        ChildReportKind::InputError(error) | ChildReportKind::ProtocolError(error) => {
            harness_error(case, elapsed, error)
        }
    }
}

/// Maps one completed child query sequence into the final parent outcome categories.
fn classify_completed_run(
    case: DiscoveredCase,
    elapsed: Duration,
    run: crate::model::CompletedQueryRun,
    telemetry: Option<CaseTelemetry>,
) -> CaseOutcome {
    let mut queries = Vec::new();
    let mut wrong = false;
    let mut no_oracle = false;
    let mut first_wrong = None;

    for (query_index, actual) in run.actual_answers.iter().copied().enumerate() {
        let expected = case
            .expected_queries()
            .get(query_index)
            .map(|query| query.expected)
            .unwrap_or(QueryAnswer::Unknown);
        let category = match expected {
            QueryAnswer::Unknown => {
                no_oracle = true;
                OutcomeCategory::NoOracle
            }
            _ if expected == actual => OutcomeCategory::Pass,
            _ => {
                wrong = true;
                first_wrong.get_or_insert((query_index, expected, actual));
                OutcomeCategory::WrongAnswer
            }
        };
        queries.push(QueryOutcome {
            query_index,
            expected,
            actual,
            elapsed,
            category,
        });
    }

    let missing = case.expected_queries().len().saturating_sub(queries.len());
    if missing > 0 {
        wrong = true;
        for query in case.expected_queries().iter().skip(queries.len()) {
            let category = if query.expected == QueryAnswer::Unknown {
                no_oracle = true;
                OutcomeCategory::NoOracle
            } else {
                first_wrong.get_or_insert((
                    query.query_index,
                    query.expected,
                    QueryAnswer::Unknown,
                ));
                OutcomeCategory::WrongAnswer
            };
            queries.push(QueryOutcome {
                query_index: query.query_index,
                expected: query.expected,
                actual: QueryAnswer::Unknown,
                elapsed,
                category,
            });
        }
    }

    let category = if wrong {
        OutcomeCategory::WrongAnswer
    } else if queries.is_empty() || no_oracle {
        OutcomeCategory::NoOracle
    } else {
        OutcomeCategory::Pass
    };

    let detail = if let Some((query_index, expected, actual)) = first_wrong {
        Some(
            format!(
                "query {} expected {:?}, got {:?}",
                query_index + 1,
                expected,
                actual
            )
            .into_boxed_str(),
        )
    } else if missing > 0 {
        Some(
            format!(
                "expected {} queries, got {}",
                case.expected_queries().len(),
                run.actual_answers.len()
            )
            .into_boxed_str(),
        )
    } else {
        None
    };

    CaseOutcome {
        case: case.into_record(),
        total_elapsed: elapsed,
        category,
        queries,
        detail,
        telemetry,
    }
}

/// Creates one infrastructure error outcome.
fn harness_error(case: DiscoveredCase, elapsed: Duration, detail: String) -> CaseOutcome {
    CaseOutcome {
        case: case.into_record(),
        total_elapsed: elapsed,
        category: OutcomeCategory::HarnessError,
        queries: Vec::new(),
        detail: Some(detail.into()),
        telemetry: None,
    }
}

/// Loads one child telemetry file and optionally retains raw samples for saving.
#[cfg(feature = "telemetry")]
fn load_case_telemetry(
    path: Option<&Path>,
    retain_samples: bool,
) -> Result<Option<CaseTelemetry>, String> {
    let Some(path) = path else {
        return Ok(None);
    };
    let samples = load_telemetry_samples(path)?;
    let Some(summary) = Summary::from_samples(&samples) else {
        return Ok(None);
    };

    Ok(Some(CaseTelemetry {
        summary,
        samples: if retain_samples { samples } else { Vec::new() },
    }))
}

/// Reads one JSONL telemetry file emitted by the child process.
#[cfg(feature = "telemetry")]
fn load_telemetry_samples(path: &Path) -> Result<Vec<Sample>, String> {
    let payload = fs::read_to_string(path)
        .map_err(|error| format!("failed to read telemetry file {}: {error}", path.display()))?;
    let mut samples = Vec::new();

    for (line_index, line) in payload.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        let sample = serde_json::from_str::<Sample>(line).map_err(|error| {
            format!(
                "failed to parse telemetry sample {} from {}: {error}",
                line_index + 1,
                path.display()
            )
        })?;
        samples.push(sample);
    }

    Ok(samples)
}

/// Returns no telemetry when the feature is disabled for the harness build.
#[cfg(not(feature = "telemetry"))]
fn load_case_telemetry(
    _path: Option<&Path>,
    _retain_samples: bool,
) -> Result<Option<CaseTelemetry>, String> {
    Ok(None)
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

    use super::{classify_completed_run, should_print_outcome, write_summary_file};
    use crate::cli::OutputMode;
    use crate::model::{
        CaseOutcome, CaseRecord, CompletedQueryRun, DiscoveredCase, ExpectedQueryResult,
        OutcomeCategory, OutcomeStats, QueryAnswer, RunSummary,
    };

    /// Ensures the default live stream remains failure-only.
    #[test]
    fn default_output_filters_successes() {
        assert!(!should_print_outcome(
            OutputMode::FailOnly,
            OutcomeCategory::Pass
        ));
        assert!(should_print_outcome(
            OutputMode::FailOnly,
            OutcomeCategory::WrongAnswer
        ));
    }

    /// Ensures the verbose mode prints every completed case outcome.
    #[test]
    fn verbose_output_prints_every_outcome() {
        assert!(should_print_outcome(OutputMode::All, OutcomeCategory::Pass));
        assert!(should_print_outcome(
            OutputMode::All,
            OutcomeCategory::NoOracle
        ));
    }

    /// Ensures the terse mode suppresses every per-case outcome line.
    #[test]
    fn terse_output_prints_nothing() {
        assert!(!should_print_outcome(
            OutputMode::Terse,
            OutcomeCategory::Pass
        ));
        assert!(!should_print_outcome(
            OutputMode::Terse,
            OutcomeCategory::WrongAnswer
        ));
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
                    logic: Some("QF_UF".into()),
                    query_count: Some(1),
                },
                total_elapsed: Duration::from_millis(5),
                category: OutcomeCategory::Pass,
                queries: Vec::new(),
                detail: None,
                telemetry: None,
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

    /// Ensures unknown oracle entries classify as `NoOracle` instead of wrong answer.
    #[test]
    fn classify_completed_run_marks_unknown_expectations_as_no_oracle() {
        let case = DiscoveredCase::new(
            PathBuf::from("/tmp/case.smt2"),
            CaseRecord {
                key: "cases/example.smt2".into(),
                bytes: 12,
                logic: Some("QF_UF".into()),
                query_count: Some(1),
            },
            vec![ExpectedQueryResult {
                query_index: 0,
                expected: QueryAnswer::Unknown,
            }],
        );

        let outcome = classify_completed_run(
            case,
            Duration::from_millis(5),
            CompletedQueryRun {
                actual_answers: vec![QueryAnswer::Sat],
            },
            None,
        );

        assert_eq!(outcome.category, OutcomeCategory::NoOracle);
        assert_eq!(outcome.queries.len(), 1);
        assert_eq!(outcome.queries[0].category, OutcomeCategory::NoOracle);
        assert!(outcome.detail.is_none());
    }
}
