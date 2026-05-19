//! Terminal rendering for progress updates and final summaries.

use std::fmt::Write as _;
use std::path::Path;
use std::time::Duration;

use console::style;
use indicatif::{HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};
use sat::telemetry::Summary;

use crate::model::{CaseOutcome, OutcomeCategory, OutcomeStats};
use crate::util::{format_compact_duration, truncate_display_path};

/// The interactive refresh cadence used while waiting for the next completed case.
pub(crate) const PROGRESS_HEARTBEAT_INTERVAL: Duration = Duration::from_millis(100);
/// Builds the live progress bar used by the parent process.
pub(crate) fn build_progress_bar(total: usize, interactive: bool) -> ProgressBar {
    let draw_target = if interactive {
        ProgressDrawTarget::stderr_with_hz(10)
    } else {
        ProgressDrawTarget::hidden()
    };
    let progress_bar = ProgressBar::with_draw_target(Some(total as u64), draw_target);
    let style = ProgressStyle::with_template("{pos}/{len} {wide_bar} {elapsed}/{duration} {msg}")
        .expect("valid progress template")
        .progress_chars("=>-");
    progress_bar.set_style(style);
    if interactive {
        progress_bar.enable_steady_tick(PROGRESS_HEARTBEAT_INTERVAL);
    }
    progress_bar.set_message("starting");
    progress_bar
}

/// Formats the live status counters shown beside the progress bar.
pub(crate) fn progress_message(stats: &OutcomeStats, running: usize) -> String {
    let failures =
        stats.wrong + stats.parse + stats.timeout + stats.panic + stats.killed + stats.harness;
    let mut message = format!(
        "run {} | ok {} | no-oracle {} | fail {}",
        HumanCount(running as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(failures as u64),
    );

    if failures > 0 {
        message.push_str(" [");
        let mut has_detail = false;
        for (label, count) in [
            ("wrong", stats.wrong),
            ("parse", stats.parse),
            ("time", stats.timeout),
            ("panic", stats.panic),
            ("killed", stats.killed),
            ("error", stats.harness),
        ] {
            if count == 0 {
                continue;
            }
            if has_detail {
                message.push(' ');
            }
            let _ = write!(message, "{label} {}", HumanCount(count as u64));
            has_detail = true;
        }
        message.push(']');
    }

    message
}

/// Formats one case outcome line that can be printed immediately during the run.
pub(crate) fn format_outcome(outcome: &CaseOutcome) -> String {
    let label = outcome.category.styled_label();
    let width = OutcomeCategory::LABEL_WIDTH;
    let elapsed = format_compact_duration(outcome.elapsed);
    let path = truncate_display_path(outcome.case.comparison_key());

    let detail = if let Some(detail) = outcome.detail.as_deref() {
        format!(" :: {}", detail)
    } else {
        String::new()
    };

    let metrices = if let Some(telemetry) = outcome.telemetry.as_ref() {
        format!(
            "\n{}{}",
            " ".repeat(4),
            style(format_telemetry_summary(&telemetry.summary)).dim()
        )
    } else {
        String::new()
    };

    format!("    {label:<width$} {elapsed:>6} {path}{detail}{metrices}")
}

/// Formats one compact telemetry summary for a per-case outcome line.
fn format_telemetry_summary(summary: &Summary) -> String {
    format!(
        "conf {} prop {} dec {} rst {} red {} peak-lvl {} peak-assign {} final-learnt {}",
        HumanCount(summary.total_conflicts),
        HumanCount(summary.total_propagations),
        HumanCount(summary.total_decisions),
        HumanCount(summary.total_restarts),
        HumanCount(summary.total_reductions),
        HumanCount(summary.peak_decision_level),
        HumanCount(summary.peak_assigned_vars),
        HumanCount(summary.final_live_learnt_clauses),
    )
}

/// Prints the final summary.
pub(crate) fn print_summary(
    outcomes: &[CaseOutcome],
    stats: &OutcomeStats,
    elapsed: Duration,
    jobs: usize,
) {
    let total = outcomes.len();
    let throughput = if elapsed.is_zero() {
        0.0
    } else {
        total as f64 / elapsed.as_secs_f64()
    };

    eprintln!();

    eprintln!(
        "{} in {} with {} workers, throughput: {:.1} cases/s",
        style("finished").cyan().bold(),
        format_compact_duration(elapsed),
        HumanCount(jobs as u64),
        throughput
    );

    eprintln!(
        "{} total {} | pass {} | no-oracle {} | fail {}",
        style("cases").cyan().bold(),
        HumanCount(total as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(stats.done as u64 - stats.pass as u64 - stats.no_oracle as u64),
    );

    eprintln!(
        "{} wrong {} | timeout {} | panic {} | parse {} | killed {} | harness {}",
        style("failures").cyan().bold(),
        HumanCount(stats.wrong as u64),
        HumanCount(stats.timeout as u64),
        HumanCount(stats.panic as u64),
        HumanCount(stats.parse as u64),
        HumanCount(stats.killed as u64),
        HumanCount(stats.harness as u64)
    );
}

/// Prints the path of a saved run summary artifact.
pub(crate) fn print_written_summary(path: &Path) {
    eprintln!("{} {}", style("saved").cyan().bold(), path.display(),);
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::{format_outcome, progress_message};
    use crate::model::{CaseOutcome, CaseRecord, CaseTelemetry, OutcomeCategory, OutcomeStats};
    use sat::telemetry::Summary;

    /// Ensures the live message exposes worker activity even before any case finishes.
    #[test]
    fn progress_message_reports_running_workers() {
        let message = progress_message(&OutcomeStats::default(), 3);
        assert!(message.contains("run 3"));
        assert!(message.contains("ok 0"));
        assert!(message.contains("fail 0"));
        assert!(!message.contains("jobs"));
    }

    /// Ensures failures add a compact breakdown to the live progress message.
    #[test]
    fn progress_message_reports_failures_compactly() {
        let stats = OutcomeStats {
            wrong: 2,
            timeout: 1,
            harness: 3,
            ..OutcomeStats::default()
        };
        let message = progress_message(&stats, 1);
        assert!(message.contains("run 1"));
        assert!(message.contains("fail 6"));
        assert!(message.contains("[wrong 2 time 1 error 3]"));
    }

    /// Ensures successful outcomes can be rendered for the optional verbose stream.
    #[test]
    fn format_outcome_renders_successful_cases() {
        let outcome = CaseOutcome {
            case: CaseRecord {
                key: "fixture/example.cnf".into(),
                bytes: 123,
                expected: None,
                source: None,
            },
            elapsed: Duration::from_millis(42),
            category: OutcomeCategory::Pass,
            detail: None,
            telemetry: None,
        };

        let rendered = format_outcome(&outcome);
        assert!(rendered.contains("PASS"));
        assert!(rendered.contains("fixture/example.cnf"));
    }

    /// Ensures rendered output truncates long paths instead of persisting a separate field.
    #[test]
    fn format_outcome_truncates_long_paths_when_rendering() {
        let outcome = CaseOutcome {
            case: CaseRecord {
                key: "cases/satlib/instance-group/very-long-case-name.cnf.gz".into(),
                bytes: 123,
                expected: None,
                source: None,
            },
            elapsed: Duration::from_millis(42),
            category: OutcomeCategory::Pass,
            detail: None,
            telemetry: None,
        };

        let rendered = format_outcome(&outcome);
        assert!(rendered.contains("cases/satl..ery-long-case-name.cnf.gz"));
    }

    /// Ensures rendered outcome lines append compact telemetry when available.
    #[test]
    fn format_outcome_renders_telemetry_summary() {
        let outcome = CaseOutcome {
            case: CaseRecord {
                key: "fixture/example.cnf".into(),
                bytes: 123,
                expected: None,
                source: None,
            },
            elapsed: Duration::from_secs(1),
            category: OutcomeCategory::Pass,
            detail: None,
            telemetry: Some(CaseTelemetry {
                summary: Summary {
                    sample_count: 1,
                    total_conflicts: 7,
                    total_propagations: 42,
                    total_decisions: 3,
                    total_restarts: 1,
                    total_reductions: 0,
                    total_learnt_clauses: 0,
                    total_deleted_clauses: 0,
                    peak_decision_level: 5,
                    peak_assigned_vars: 11,
                    peak_trail_len: 0,
                    peak_pending_propagations: 0,
                    peak_live_irredundant_clauses: 0,
                    peak_live_learnt_clauses: 0,
                    peak_watcher_entries: 0,
                    peak_clause_words: 0,
                    peak_wasted_clause_words: 0,
                    final_decision_level: 0,
                    final_assigned_vars: 0,
                    final_trail_len: 0,
                    final_live_learnt_clauses: 9,
                    final_live_irredundant_clauses: 0,
                },
                samples: Vec::new(),
            }),
        };

        let rendered = format_outcome(&outcome);
        assert!(rendered.contains("tele conf 7"));
        assert!(rendered.contains("peak-lvl 5"));
        assert!(rendered.contains("final-learnt 9"));
    }
}
