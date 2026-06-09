//! Terminal rendering for progress updates and final summaries.

use std::fmt::Write as _;
use std::path::Path;
use std::time::Duration;

use console::style;
use indicatif::{HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};
use telemetry::Summary;

use crate::model::{CaseOutcome, OutcomeCategory, OutcomeStats};
use crate::util::format_duration;

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
    let elapsed = format_duration(outcome.elapsed);
    let path = outcome.key.as_str();

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
        "sat conf {} prop {} dec {} | euf eq {} cong {} tprop {} tconf {} | peak-lvl {} peak-assign {} peak-terms {}",
        HumanCount(summary.sat.total_conflicts),
        HumanCount(summary.sat.total_propagations),
        HumanCount(summary.sat.total_decisions),
        HumanCount(summary.euf.total_input_equalities),
        HumanCount(summary.euf.total_congruence_merges),
        HumanCount(summary.euf.total_theory_propagations),
        HumanCount(summary.euf.total_theory_conflicts),
        HumanCount(summary.sat.peak_decision_level),
        HumanCount(summary.sat.peak_assigned_vars),
        HumanCount(summary.euf.peak_registry_terms),
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
        format_duration(elapsed),
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
    use crate::model::{CaseOutcome, CaseTelemetry, ComparisonKey, OutcomeCategory, OutcomeStats};
    use telemetry::{EufSummary, SatSummary, Summary};

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
            key: ComparisonKey::new("fixture/example.cnf"),
            elapsed: Duration::from_millis(42),
            category: OutcomeCategory::Pass,
            detail: None,
            telemetry: None,
        };

        let rendered = format_outcome(&outcome);
        assert!(rendered.contains("PASS"));
        assert!(rendered.contains("42.0ms"));
        assert!(rendered.contains("fixture/example.cnf"));
    }

    /// Ensures rendered output preserves the complete case path.
    #[test]
    fn format_outcome_renders_complete_long_paths() {
        let outcome = CaseOutcome {
            key: ComparisonKey::new("cases/satlib/instance-group/very-long-case-name.cnf.gz"),
            elapsed: Duration::from_millis(42),
            category: OutcomeCategory::Pass,
            detail: None,
            telemetry: None,
        };

        let rendered = format_outcome(&outcome);
        assert!(rendered.contains("cases/satlib/instance-group/very-long-case-name.cnf.gz"));
    }

    /// Ensures rendered outcome lines append compact telemetry when available.
    #[test]
    fn format_outcome_renders_telemetry_summary() {
        let outcome = CaseOutcome {
            key: ComparisonKey::new("fixture/example.cnf"),
            elapsed: Duration::from_secs(1),
            category: OutcomeCategory::Pass,
            detail: None,
            telemetry: Some(CaseTelemetry {
                summary: Summary {
                    sample_count: 1,
                    sat: SatSummary {
                        total_conflicts: 7,
                        total_propagations: 42,
                        total_decisions: 3,
                        total_restarts: 1,
                        peak_decision_level: 5,
                        peak_assigned_vars: 11,
                        final_live_learnt_clauses: 9,
                        ..SatSummary::default()
                    },
                    euf: EufSummary {
                        total_input_equalities: 4,
                        total_congruence_merges: 2,
                        total_theory_propagations: 1,
                        total_theory_conflicts: 0,
                        peak_registry_terms: 12,
                        ..EufSummary::default()
                    },
                },
            }),
        };

        let rendered = format_outcome(&outcome);
        assert!(rendered.contains("conf 7"));
        assert!(rendered.contains("eq 4"));
        assert!(rendered.contains("peak-lvl 5"));
        assert!(rendered.contains("peak-terms 12"));
    }
}
