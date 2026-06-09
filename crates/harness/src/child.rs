//! Child-process execution for isolated benchmark runs.

use std::fs;
use std::time::{Duration, Instant};

use crate::case_io::read_case_text;
use crate::cli::RunCaseArgs;
use crate::discover::query_count;
use crate::model::{ChildReport, ChildReportKind, CompletedQueryRun, QueryAnswer};

/// Runs the isolated single-case entrypoint and writes the structured report.
pub(crate) fn run_child(args: RunCaseArgs) -> Result<(), String> {
    let report = match read_case_text(&args.case) {
        Ok(input) => {
            let kind = solve_case_with_optional_telemetry(&input, &args)?;
            ChildReport { kind }
        }
        Err(error) => ChildReport {
            kind: ChildReportKind::InputError(error),
        },
    };
    let payload = serde_json::to_vec(&report)
        .map_err(|error| format!("failed to serialize child report: {error}"))?;
    fs::write(&args.report, payload).map_err(|error| {
        format!(
            "failed to write child report {}: {error}",
            args.report.display()
        )
    })
}

/// Solves one case, recording periodic telemetry samples when the feature is enabled.
#[cfg(feature = "telemetry")]
fn solve_case_with_optional_telemetry(
    input: &str,
    args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    let expected_queries = match args.expected_query_count {
        Some(count) => count,
        None => match query_count(input) {
            Ok(count) => count,
            Err(error) => return Ok(ChildReportKind::ParseError(error)),
        },
    };

    let solver_started = Instant::now();
    let output = match qfuf::run_script_with_telemetry(input, &args.telemetry) {
        Ok(output) => output,
        Err(error) => return Ok(ChildReportKind::ParseError(error)),
    };
    let solver_elapsed = solver_started.elapsed();

    classify_output(output, expected_queries, solver_elapsed)
}

/// Solves one case without compiling in telemetry instrumentation.
#[cfg(not(feature = "telemetry"))]
fn solve_case_with_optional_telemetry(
    input: &str,
    args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    let expected_queries = match args.expected_query_count {
        Some(count) => count,
        None => match query_count(input) {
            Ok(count) => count,
            Err(error) => return Ok(ChildReportKind::ParseError(error)),
        },
    };

    let solver_started = Instant::now();
    let output = match qfuf::run_script(input) {
        Ok(output) => output,
        Err(error) => return Ok(ChildReportKind::ParseError(error)),
    };
    let solver_elapsed = solver_started.elapsed();

    classify_output(output, expected_queries, solver_elapsed)
}

/// Parses solver output lines and validates the answer count.
fn classify_output(
    output: String,
    expected_queries: usize,
    solver_elapsed: Duration,
) -> Result<ChildReportKind, String> {
    let actual_answers = output
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| QueryAnswer::parse(line.trim()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ChildReportKind::ProtocolError)
        .map_err(|error| match error {
            ChildReportKind::ProtocolError(detail) => detail,
            _ => unreachable!(),
        })?;
    if actual_answers.len() != expected_queries {
        return Ok(ChildReportKind::ProtocolError(format!(
            "expected {expected_queries} query answers from qfuf, got {}",
            actual_answers.len()
        )));
    }
    Ok(ChildReportKind::Completed(CompletedQueryRun {
        actual_answers,
        solver_elapsed,
    }))
}
