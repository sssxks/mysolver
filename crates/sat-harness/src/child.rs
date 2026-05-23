//! Child-process execution for isolated benchmark runs.

use std::env;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use bzip2::read::BzDecoder;
use flate2::read::MultiGzDecoder;
#[cfg(feature = "telemetry")]
use sat::telemetry::TelemetryRecorder;

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

/// Solves one case and records telemetry only when the feature is enabled.
#[cfg(feature = "telemetry")]
fn solve_case_with_optional_telemetry(
    input: &str,
    args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    let recorder = TelemetryRecorder::start(&args.telemetry).map_err(|error| {
        format!(
            "failed to start telemetry recorder {}: {error}",
            args.telemetry.display()
        )
    })?;
    let kind = run_qfuf_process(input)?;
    recorder.finish(sat::telemetry::Gauges::default()).map_err(|error| {
        format!(
            "failed to finalize telemetry file {}: {error}",
            args.telemetry.display()
        )
    })?;
    Ok(kind)
}

/// Solves one case without compiling in telemetry instrumentation.
#[cfg(not(feature = "telemetry"))]
fn solve_case_with_optional_telemetry(
    input: &str,
    _args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    run_qfuf_process(input)
}

/// Executes the `qfuf` solver binary over stdin/stdout for one whole trace.
fn run_qfuf_process(input: &str) -> Result<ChildReportKind, String> {
    let expected_queries = match query_count(input) {
        Ok(count) => count,
        Err(error) => return Ok(ChildReportKind::ParseError(error)),
    };
    let current_exe = env::current_exe()
        .map_err(|error| format!("failed to locate current executable: {error}"))?;
    let qfuf_exe = sibling_solver_path(&current_exe);

    let mut child = Command::new(&qfuf_exe)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to spawn {}: {error}", qfuf_exe.display()))?;

    {
        let stdin = child
            .stdin
            .as_mut()
            .ok_or_else(|| "failed to open qfuf stdin".to_owned())?;
        stdin
            .write_all(input.as_bytes())
            .map_err(|error| format!("failed to write qfuf stdin: {error}"))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|error| format!("failed to wait for qfuf: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let detail = stderr.trim();
        return Ok(ChildReportKind::ParseError(if detail.is_empty() {
            format!("qfuf exited with {}", output.status)
        } else {
            detail.to_owned()
        }));
    }

    let stdout = String::from_utf8(output.stdout)
        .map_err(|error| format!("qfuf wrote non-utf8 stdout: {error}"))?;
    let actual_answers = stdout
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
    }))
}

/// Returns the sibling solver-binary path located beside `current_exe`.
fn sibling_solver_path(current_exe: &Path) -> PathBuf {
    current_exe.with_file_name("qfuf")
}

/// Reads one benchmark file, transparently decompressing gzip and bzip2 inputs.
fn read_case_text(path: &Path) -> Result<String, String> {
    let mut text = String::new();
    if has_suffix(path, ".gz") {
        let file = File::open(path)
            .map_err(|error| format!("failed to open {}: {error}", path.display()))?;
        let mut decoder = MultiGzDecoder::new(file);
        decoder
            .read_to_string(&mut text)
            .map_err(|error| format!("failed to decode gzip {}: {error}", path.display()))?;
    } else if has_suffix(path, ".bz2") {
        let file = File::open(path)
            .map_err(|error| format!("failed to open {}: {error}", path.display()))?;
        let mut decoder = BzDecoder::new(file);
        decoder
            .read_to_string(&mut text)
            .map_err(|error| format!("failed to decode bzip2 {}: {error}", path.display()))?;
    } else {
        let mut file = File::open(path)
            .map_err(|error| format!("failed to open {}: {error}", path.display()))?;
        file.read_to_string(&mut text)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    }
    Ok(text)
}

/// Returns `true` when the path ends with the provided suffix.
fn has_suffix(path: &Path, suffix: &str) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(suffix))
}
