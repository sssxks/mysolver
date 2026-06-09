//! Saved-result loading, comparison, and terminal rendering.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use console::style;
use indicatif::HumanCount;

use crate::cli::CompareArgs;
use crate::model::{CaseOutcome, OutcomeCategory, RunSummary};
use crate::util::format_compact_duration;

/// The maximum number of entries printed for any one difference section.
const MAX_PRINTED_CASES_PER_SECTION: usize = 20;

/// Loads two saved run summaries, prints a comparison, and returns whether they match.
pub(crate) fn compare_saved_runs(args: CompareArgs) -> Result<bool, String> {
    let left = load_saved_run(&args.left)?;
    let right = load_saved_run(&args.right)?;
    let comparison = RunComparison::build(&left, &right);
    print_comparison(&left, &right, &comparison);
    Ok(comparison.is_match())
}

/// Reads and validates one saved run summary from disk.
fn load_saved_run(path: &Path) -> Result<RunSummary, String> {
    let payload = fs::read_to_string(path)
        .map_err(|error| format!("failed to read saved run {}: {error}", path.display()))?;
    let summary: RunSummary = serde_json::from_str(&payload)
        .map_err(|error| format!("failed to parse saved run {}: {error}", path.display()))?;
    summary.validate()?;
    Ok(summary)
}

/// One difference where the same case key produced different outcome data.
#[derive(Clone, Debug)]
struct ChangedCase {
    /// The manifest-relative key shared by both saved runs.
    key: Box<str>,
    /// The left-hand saved case outcome.
    left: CaseOutcome,
    /// The right-hand saved case outcome.
    right: CaseOutcome,
}

/// The full comparison result between two saved run summaries.
#[derive(Debug)]
struct RunComparison {
    /// Cases present only in the left-hand summary.
    only_left: Vec<CaseOutcome>,
    /// Cases present only in the right-hand summary.
    only_right: Vec<CaseOutcome>,
    /// Shared cases whose semantic outcome changed.
    changed: Vec<ChangedCase>,
    /// The number of shared cases whose semantic outcome stayed identical.
    identical: usize,
}

impl RunComparison {
    /// Builds a case-by-case comparison from two saved run summaries.
    fn build(left: &RunSummary, right: &RunSummary) -> Self {
        let left_cases = index_cases(&left.cases);
        let mut right_cases = index_cases(&right.cases);
        let mut only_left = Vec::new();
        let mut only_right = Vec::new();
        let mut changed = Vec::new();
        let mut identical = 0;

        for (key, left_case) in &left_cases {
            match right_cases.remove(key) {
                Some(right_case) => {
                    if outcomes_match(left_case, &right_case) {
                        identical += 1;
                    } else {
                        changed.push(ChangedCase {
                            key: key.clone().into_boxed_str(),
                            left: left_case.clone(),
                            right: right_case,
                        });
                    }
                }
                None => only_left.push(left_case.clone()),
            }
        }

        only_right.extend(right_cases.into_values());
        only_left
            .sort_by(|left, right| left.case.comparison_key().cmp(right.case.comparison_key()));
        only_right
            .sort_by(|left, right| left.case.comparison_key().cmp(right.case.comparison_key()));
        changed.sort_by(|left, right| left.key.cmp(&right.key));

        Self {
            only_left,
            only_right,
            changed,
            identical,
        }
    }

    /// Returns `true` when the saved runs have the same cases and semantic outcomes.
    fn is_match(&self) -> bool {
        self.only_left.is_empty() && self.only_right.is_empty() && self.changed.is_empty()
    }
}

/// Indexes saved outcomes by their stable comparison key.
fn index_cases(cases: &[CaseOutcome]) -> BTreeMap<String, CaseOutcome> {
    cases
        .iter()
        .cloned()
        .map(|case| (case.case.comparison_key().to_owned(), case))
        .collect()
}

/// Returns whether two saved outcomes represent the same semantic result.
fn outcomes_match(left: &CaseOutcome, right: &CaseOutcome) -> bool {
    left.category == right.category
        && left.detail == right.detail
        && left.queries.len() == right.queries.len()
        && left
            .queries
            .iter()
            .zip(&right.queries)
            .all(|(left_query, right_query)| {
                left_query.query_index == right_query.query_index
                    && left_query.category == right_query.category
                    && left_query.expected == right_query.expected
                    && left_query.actual == right_query.actual
            })
}

/// Prints a complete human-readable comparison report.
fn print_comparison(left: &RunSummary, right: &RunSummary, comparison: &RunComparison) {
    let shared = comparison.identical + comparison.changed.len();
    eprintln!(
        "{} shared {} | identical {} | changed {} | only-left {} | only-right {}",
        style("cases").cyan().bold(),
        HumanCount(shared as u64),
        HumanCount(comparison.identical as u64),
        HumanCount(comparison.changed.len() as u64),
        HumanCount(comparison.only_left.len() as u64),
        HumanCount(comparison.only_right.len() as u64),
    );

    let (improvements, regressions, lateral_changes) = classify_changes(&comparison.changed);
    eprintln!(
        "{} improvement {} | regression {} | lateral {}",
        style("changed").cyan().bold(),
        HumanCount(improvements as u64),
        HumanCount(regressions as u64),
        HumanCount(lateral_changes as u64),
    );

    print_case_section(
        "only in left cases",
        &comparison.only_left,
        format_missing_case,
    );
    print_case_section(
        "only in right cases",
        &comparison.only_right,
        format_missing_case,
    );
    print_case_section("changed cases", &comparison.changed, format_changed_case);

    eprintln!();

    print_run_header("left", left);
    print_run_header("right", right);
}

/// Prints one per-run summary line inside a comparison report.
fn print_run_header(label: &str, summary: &RunSummary) {
    eprintln!(
        "{} {:6} total {} | pass {} | no-oracle {} | fail {} | elapsed {} | jobs {} | timeout {}",
        style("summary").cyan().bold(),
        label,
        HumanCount(summary.cases.len() as u64),
        HumanCount(summary.stats.pass as u64),
        HumanCount(summary.stats.no_oracle as u64),
        HumanCount(
            summary.stats.done as u64 - summary.stats.pass as u64 - summary.stats.no_oracle as u64
        ),
        format_compact_duration(summary.total_elapsed),
        HumanCount(summary.jobs as u64),
        format_compact_duration(summary.timeout),
    );
}

/// Classifies changed cases by whether the right-hand side improved or regressed.
fn classify_changes(changes: &[ChangedCase]) -> (usize, usize, usize) {
    let mut improvements = 0;
    let mut regressions = 0;
    let mut lateral = 0;

    for change in changes {
        match (
            change.left.category.is_failure(),
            change.right.category.is_failure(),
        ) {
            (true, false) => improvements += 1,
            (false, true) => regressions += 1,
            _ => lateral += 1,
        }
    }

    (improvements, regressions, lateral)
}

/// Prints one named comparison section using a formatter callback.
fn print_case_section<T>(title: &str, entries: &[T], format_entry: fn(&T) -> String) {
    if entries.is_empty() {
        return;
    }

    eprintln!();
    if entries.len() > MAX_PRINTED_CASES_PER_SECTION {
        eprintln!(
            "{} {} (showing up to {})",
            style(title).cyan().bold(),
            HumanCount(entries.len() as u64),
            MAX_PRINTED_CASES_PER_SECTION
        );
    } else {
        eprintln!(
            "{} {}",
            style(title).cyan().bold(),
            HumanCount(entries.len() as u64),
        );
    }

    for entry in entries.iter().take(MAX_PRINTED_CASES_PER_SECTION) {
        eprintln!("{}", format_entry(entry));
    }

    if entries.len() > MAX_PRINTED_CASES_PER_SECTION {
        eprintln!(
            "    ... {} more",
            HumanCount((entries.len() - MAX_PRINTED_CASES_PER_SECTION) as u64)
        );
    }
}

/// Formats one case that is missing from the opposite saved run.
fn format_missing_case(outcome: &CaseOutcome) -> String {
    let width = OutcomeCategory::LABEL_WIDTH;
    let detail = format_case_detail(outcome.detail.as_deref());
    let path = outcome.case.comparison_key();
    format!(
        "    {:<width$} {:>6} {}{detail}",
        outcome.category.styled_label(),
        format_compact_duration(outcome.displayed_elapsed()),
        path,
        width = width,
    )
}

/// Formats one changed case for terminal output.
fn format_changed_case(change: &ChangedCase) -> String {
    let label = format_category_change(change.left.category, change.right.category);
    let elapsed = format_elapsed_change(
        change.left.displayed_elapsed(),
        change.right.displayed_elapsed(),
    );
    let detail = format_detail_change(
        change.left.detail.as_deref(),
        change.right.detail.as_deref(),
    );
    format!("    {label} {elapsed} {}{detail}", change.key)
}

/// Formats one optional missing-case detail suffix.
fn format_case_detail(detail: Option<&str>) -> String {
    detail.map_or_else(String::new, |detail| format!(" :: {detail}"))
}

/// Formats a category change, omitting the arrow when both sides share one category.
fn format_category_change(left: OutcomeCategory, right: OutcomeCategory) -> String {
    let width = OutcomeCategory::LABEL_WIDTH;
    if left == right {
        format!("{:<width$}", left.styled_label(), width = width)
    } else {
        format!(
            "{:<width$} -> {:<width$}",
            left.styled_label(),
            right.styled_label(),
            width = width,
        )
    }
}

/// Formats an elapsed-time change, omitting the arrow when both sides match.
fn format_elapsed_change(left: std::time::Duration, right: std::time::Duration) -> String {
    let left = format_compact_duration(left);
    let right = format_compact_duration(right);
    if left == right {
        format!("{left:>6}")
    } else {
        format!("{left:>6} -> {right:>6}")
    }
}

/// Formats one optional detail change suffix, omitting separators when both sides are empty.
fn format_detail_change(left: Option<&str>, right: Option<&str>) -> String {
    if left == right {
        return String::new();
    }

    let left = left.unwrap_or("-");
    let right = right.unwrap_or("-");
    format!(" :: {left} -> {right}")
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::time::Duration;

    use super::{RunComparison, format_changed_case, format_missing_case, outcomes_match};
    use crate::model::{CaseOutcome, CaseRecord, OutcomeCategory, OutcomeStats, RunSummary};

    /// Ensures saved-run comparisons ignore wall-clock runtime differences.
    #[test]
    fn outcomes_ignore_elapsed_time() {
        let left = sample_outcome(
            "case.cnf",
            OutcomeCategory::Pass,
            Duration::from_secs(1),
            None,
        );
        let right = sample_outcome(
            "case.cnf",
            OutcomeCategory::Pass,
            Duration::from_secs(2),
            None,
        );
        assert!(outcomes_match(&left, &right));
    }

    /// Ensures the comparison distinguishes missing and changed cases.
    #[test]
    fn run_comparison_classifies_differences() {
        let left = sample_summary(vec![
            sample_outcome(
                "same.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(1),
                None,
            ),
            sample_outcome(
                "changed.cnf",
                OutcomeCategory::WrongAnswer,
                Duration::from_secs(1),
                Some("expected sat, got unsat"),
            ),
            sample_outcome(
                "left-only.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(1),
                None,
            ),
        ]);
        let right = sample_summary(vec![
            sample_outcome(
                "same.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(2),
                None,
            ),
            sample_outcome(
                "changed.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(1),
                None,
            ),
            sample_outcome(
                "right-only.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(1),
                None,
            ),
        ]);

        let comparison = RunComparison::build(&left, &right);
        assert_eq!(comparison.identical, 1);
        assert_eq!(comparison.changed.len(), 1);
        assert_eq!(comparison.only_left.len(), 1);
        assert_eq!(comparison.only_right.len(), 1);
        assert!(!comparison.is_match());
    }

    /// Ensures missing-case output preserves long paths and prints detail only when present.
    #[test]
    fn format_missing_case_renders_complete_paths_and_omits_empty_detail_separator() {
        let outcome = sample_outcome(
            "cases/satlib/instance-group/very-long-case-name.cnf.gz",
            OutcomeCategory::WrongAnswer,
            Duration::from_millis(42),
            None,
        );

        let rendered = format_missing_case(&outcome);
        assert!(rendered.contains("cases/satlib/instance-group/very-long-case-name.cnf.gz"));
        assert!(!rendered.contains("::"));
    }

    /// Ensures changed-case output suppresses redundant separators for unchanged fields.
    #[test]
    fn format_changed_case_omits_redundant_separators() {
        let rendered = format_changed_case(&super::ChangedCase {
            key: "fixture/example.cnf".into(),
            left: sample_outcome(
                "fixture/example.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(1),
                None,
            ),
            right: sample_outcome(
                "fixture/example.cnf",
                OutcomeCategory::Pass,
                Duration::from_secs(2),
                None,
            ),
        });

        assert!(rendered.contains("PASS"));
        assert!(rendered.contains("1.00s"));
        assert!(rendered.contains("2.00s"));
        assert!(!rendered.contains("PASS -> PASS"));
        assert!(!rendered.contains("::"));
    }

    /// Builds one saved outcome fixture for comparison tests.
    fn sample_outcome(
        key: &str,
        category: OutcomeCategory,
        elapsed: Duration,
        detail: Option<&str>,
    ) -> CaseOutcome {
        CaseOutcome {
            case: CaseRecord {
                key: key.into(),
                bytes: 1,
                logic: Some("QF_UF".into()),
                query_count: Some(1),
            },
            total_elapsed: elapsed,
            solver_elapsed: None,
            category,
            queries: Vec::new(),
            detail: detail.map(Into::into),
            telemetry: None,
        }
    }

    /// Builds one minimal saved run summary fixture for comparison tests.
    fn sample_summary(cases: Vec<CaseOutcome>) -> RunSummary {
        let mut stats = OutcomeStats::default();
        for case in &cases {
            stats.record(case.category);
        }
        RunSummary {
            format_version: RunSummary::FORMAT_VERSION,
            roots: vec![PathBuf::from("test/fixture/sat")].into_boxed_slice(),
            jobs: 1,
            timeout: Duration::from_secs(30),
            total_elapsed: Duration::from_secs(3),
            cases,
            stats,
        }
    }
}
