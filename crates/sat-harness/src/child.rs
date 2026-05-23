//! Child-process execution for isolated benchmark runs.

use std::fs::{self, File};
use std::io::Read;
use std::path::Path;

use bzip2::read::BzDecoder;
use flate2::read::MultiGzDecoder;
#[cfg(feature = "telemetry")]
use sat::telemetry::TelemetryRecorder;
use sat::{SatResult as SolverSatResult, Solver, parse_dimacs};

use crate::cli::RunCaseArgs;
use crate::model::{ChildReport, ChildReportKind};

/// Runs the isolated single-case entrypoint and writes the structured report.
pub(crate) fn run_child(args: RunCaseArgs) -> Result<(), String> {
    let report = match load_case_and_solver(&args.case) {
        Ok(mut solver) => {
            let kind = solve_case_with_optional_telemetry(&mut solver, &args)?;
            ChildReport { kind }
        }
        Err(LoadCaseError::Input(error)) => ChildReport {
            kind: ChildReportKind::InputError(error),
        },
        Err(LoadCaseError::Parse(error)) => ChildReport {
            kind: ChildReportKind::ParseError(error),
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
    solver: &mut Solver,
    args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    let recorder = TelemetryRecorder::start(&args.telemetry).map_err(|error| {
        format!(
            "failed to start telemetry recorder {}: {error}",
            args.telemetry.display()
        )
    })?;
    let kind = match solver.solve() {
        SolverSatResult::Sat => ChildReportKind::Sat,
        SolverSatResult::Unsat => ChildReportKind::Unsat,
    };
    recorder
        .finish(solver.telemetry_gauges())
        .map_err(|error| {
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
    solver: &mut Solver,
    _args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    let kind = match solver.solve() {
        SolverSatResult::Sat => ChildReportKind::Sat,
        SolverSatResult::Unsat => ChildReportKind::Unsat,
    };
    Ok(kind)
}

/// Loads one DIMACS case and builds a solver instance from it.
fn load_case_and_solver(path: &Path) -> Result<Solver, LoadCaseError> {
    let input = read_case_text(path).map_err(LoadCaseError::Input)?;
    parse_dimacs(&input).map_err(LoadCaseError::Parse)
}

/// All load failures handled inside the child process.
#[derive(Debug)]
enum LoadCaseError {
    /// The file could not be read or decompressed.
    Input(String),
    /// The text could be read, but DIMACS parsing failed.
    Parse(String),
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
