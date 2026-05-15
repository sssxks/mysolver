//! Terminal rendering for progress updates and final summaries.

use std::fmt::Write as _;
use std::time::Duration;

use console::style;
use indicatif::{HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};

use crate::model::{CaseOutcome, OutcomeCategory, OutcomeStats};
use crate::util::format_compact_duration;

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
    let style =
        ProgressStyle::with_template("{pos:>6}/{len:6} {wide_bar} {elapsed}/{duration} {msg}")
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

/// Formats a failure line that is printed immediately during the run.
pub(crate) fn format_failure(outcome: &CaseOutcome) -> String {
    let label = match outcome.category {
        OutcomeCategory::WrongAnswer => style(outcome.category.label()).red().bold(),
        OutcomeCategory::ParseError => style(outcome.category.label()).yellow().bold(),
        OutcomeCategory::Timeout => style(outcome.category.label()).yellow().bold(),
        OutcomeCategory::Panic => style(outcome.category.label()).magenta().bold(),
        OutcomeCategory::Killed => style(outcome.category.label()).red().bold(),
        OutcomeCategory::HarnessError => style(outcome.category.label()).red().bold(),
        OutcomeCategory::Pass | OutcomeCategory::NoOracle => {
            style(outcome.category.label()).green().bold()
        }
    };
    let detail = outcome.detail.as_deref().unwrap_or("no detail");
    format!(
        "{label} {:>10} {} :: {}",
        format_compact_duration(outcome.elapsed),
        outcome.case.display_path,
        detail,
    )
}

/// Prints the final run summary.
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

    let divider = "─".repeat(78);
    eprintln!("{divider}");

    eprintln!(
        "{} in {} with {} workers, throughput: {:.1} cases/s",
        style("finished").cyan().bold(),
        format_compact_duration(elapsed),
        HumanCount(jobs as u64),
        throughput
    );

    eprintln!(
        "{}: total {} | pass {} | no-oracle {} | fail {}",
        style("cases").cyan().bold(),
        HumanCount(total as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(stats.done as u64 - stats.pass as u64 - stats.no_oracle as u64),
    );

    eprintln!(
        "{}: wrong {} | timeout {} | panic {} | parse {} | killed {} | harness {}",
        style("failures").cyan().bold(),
        HumanCount(stats.wrong as u64),
        HumanCount(stats.timeout as u64),
        HumanCount(stats.panic as u64),
        HumanCount(stats.parse as u64),
        HumanCount(stats.killed as u64),
        HumanCount(stats.harness as u64)
    );
}

#[cfg(test)]
mod tests {
    use super::progress_message;
    use crate::model::OutcomeStats;

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
}
