//! Child-process execution for isolated benchmark runs.

use std::fs;

use crate::case_io::read_case_text;
use crate::cli::RunCaseArgs;
use crate::discover::query_count;
use crate::model::{ChildReport, QueryAnswer};

/// Runs the isolated single-case entrypoint and writes the structured report.
pub(crate) fn run_child(args: RunCaseArgs) -> Result<(), String> {
    let report = match read_case_text(&args.case) {
        Ok(input) => solve_case_with_optional_telemetry(&input, &args)?,
        Err(error) => ChildReport::InputError(error),
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
) -> Result<ChildReport, String> {
    let expected_queries = match expected_query_count(input, args) {
        Ok(count) => count,
        Err(error) => return Ok(ChildReport::ParseError(error)),
    };
    let output = match qfuf::run_script_with_telemetry(input, &args.telemetry) {
        Ok(output) => output,
        Err(error) => return Ok(ChildReport::ParseError(error)),
    };

    classify_output(output, expected_queries)
}

/// Solves one case without compiling in telemetry instrumentation.
#[cfg(not(feature = "telemetry"))]
fn solve_case_with_optional_telemetry(
    input: &str,
    args: &RunCaseArgs,
) -> Result<ChildReport, String> {
    let expected_queries = match expected_query_count(input, args) {
        Ok(count) => count,
        Err(error) => return Ok(ChildReport::ParseError(error)),
    };
    let output = match qfuf::run_script(input) {
        Ok(output) => output,
        Err(error) => return Ok(ChildReport::ParseError(error)),
    };

    classify_output(output, expected_queries)
}

/// Returns the expected number of solver answers for one child run.
fn expected_query_count(input: &str, args: &RunCaseArgs) -> Result<usize, String> {
    match args.expected_query_count {
        Some(count) => Ok(count),
        None => query_count(input),
    }
}

/// Parses solver output lines and validates the answer count.
fn classify_output(output: String, expected_queries: usize) -> Result<ChildReport, String> {
    let answers = output
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| QueryAnswer::parse(line.trim()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ChildReport::ProtocolError)
        .map_err(|error| match error {
            ChildReport::ProtocolError(detail) => detail,
            _ => unreachable!(),
        })?;
    if answers.len() != expected_queries {
        return Ok(ChildReport::ProtocolError(format!(
            "expected {expected_queries} query answers from qfuf, got {}",
            answers.len()
        )));
    }
    Ok(ChildReport::Completed { actual: answers })
}
