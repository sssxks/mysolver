//! Terminal rendering for progress updates and final summaries.

use std::cmp::Reverse;
use std::time::Duration;

use console::style;
use indicatif::{HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};

use crate::model::{CaseOutcome, ExpectedResult, OutcomeCategory, OutcomeStats};
use crate::util::format_compact_duration;

/// Builds the live progress bar used by the parent process.
pub(crate) fn build_progress_bar(total: usize, interactive: bool) -> ProgressBar {
    let draw_target = if interactive {
        ProgressDrawTarget::stderr_with_hz(10)
    } else {
        ProgressDrawTarget::hidden()
    };
    let progress_bar = ProgressBar::with_draw_target(Some(total as u64), draw_target);
    let style = ProgressStyle::with_template(
        "{spinner:.cyan} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos:>6}/{len:6} {msg}",
    )
    .expect("valid progress template")
    .progress_chars("=>-");
    progress_bar.set_style(style);
    progress_bar.set_message("pass 0 | wrong 0 | timeout 0");
    progress_bar
}

/// Formats the live status counters shown beside the progress bar.
pub(crate) fn progress_message(stats: &OutcomeStats, jobs: usize) -> String {
    format!(
        "jobs {} | pass {} | no-oracle {} | wrong {} | parse {} | timeout {} | panic {} | killed {} | error {}",
        HumanCount(jobs as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(stats.wrong as u64),
        HumanCount(stats.parse as u64),
        HumanCount(stats.timeout as u64),
        HumanCount(stats.panic as u64),
        HumanCount(stats.killed as u64),
        HumanCount(stats.harness as u64),
    )
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

/// Prints the final run summary and the slowest cases.
pub(crate) fn print_summary(
    outcomes: &[CaseOutcome],
    stats: &OutcomeStats,
    elapsed: Duration,
    jobs: usize,
    slowest: usize,
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
        "{} in {} with {} workers",
        style("finished").cyan().bold(),
        format_compact_duration(elapsed),
        HumanCount(jobs as u64),
    );
    eprintln!(
        "cases: total {} | pass {} | no-oracle {} | wrong {} | parse {} | timeout {} | panic {} | killed {} | error {}",
        HumanCount(total as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(stats.wrong as u64),
        HumanCount(stats.parse as u64),
        HumanCount(stats.timeout as u64),
        HumanCount(stats.panic as u64),
        HumanCount(stats.killed as u64),
        HumanCount(stats.harness as u64),
    );
    eprintln!("throughput: {:.1} cases/s", throughput);

    if slowest > 0 {
        let mut ranked: Vec<&CaseOutcome> = outcomes.iter().collect();
        ranked.sort_by_key(|outcome| Reverse(outcome.elapsed));
        let limit = slowest.min(ranked.len());
        if limit > 0 {
            eprintln!("slowest cases:");
            for outcome in ranked.into_iter().take(limit) {
                let label = outcome
                    .actual
                    .map(ExpectedResult::as_str)
                    .unwrap_or_else(|| outcome.category.label());
                let variables = outcome
                    .variables
                    .map(|count| format!("vars {}", HumanCount(count as u64)))
                    .unwrap_or_else(|| "vars ?".to_string());
                eprintln!(
                    "  {:>10} {:<6} {} ({})",
                    format_compact_duration(outcome.elapsed),
                    label,
                    outcome.case.display_path,
                    variables,
                );
            }
        }
    }

    if stats.has_failures() {
        eprintln!("{}", style("run failed").red().bold());
    } else {
        eprintln!("{}", style("run passed").green().bold());
    }
}
