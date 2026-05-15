//! Child-process execution for isolated benchmark runs.

use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
use std::time::Instant;

use bzip2::read::BzDecoder;
use flate2::read::MultiGzDecoder;
use sat::{SatResult as SolverSatResult, Solver, parse_dimacs};

use crate::cli::InternalRunCaseArgs;
use crate::model::{ChildReport, ChildReportKind};
use crate::util::saturating_millis;

/// Runs the hidden child process entrypoint and writes the structured report.
pub(crate) fn run_child(args: InternalRunCaseArgs) -> Result<(), String> {
    let started = Instant::now();
    let report = match load_case_and_solver(&args.case) {
        Ok(mut solver) => ChildReport {
            variables: solver.num_vars(),
            elapsed_millis: 0,
            kind: match solver.solve() {
                SolverSatResult::Sat => ChildReportKind::Sat,
                SolverSatResult::Unsat => ChildReportKind::Unsat,
            },
        },
        Err(LoadCaseError::Input(error)) => ChildReport {
            variables: 0,
            elapsed_millis: 0,
            kind: ChildReportKind::InputError(error),
        },
        Err(LoadCaseError::Parse(error, variables)) => ChildReport {
            variables,
            elapsed_millis: 0,
            kind: ChildReportKind::ParseError(error),
        },
    };
    let mut report = report;
    report.elapsed_millis = saturating_millis(started.elapsed());
    let payload = serde_json::to_vec(&report)
        .map_err(|error| format!("failed to serialize child report: {error}"))?;
    fs::write(&args.report, payload).map_err(|error| {
        format!(
            "failed to write child report {}: {error}",
            args.report.display()
        )
    })
}

/// Loads one DIMACS case and builds a solver instance from it.
fn load_case_and_solver(path: &Path) -> Result<Solver, LoadCaseError> {
    let input = read_case_text(path).map_err(LoadCaseError::Input)?;
    parse_dimacs(&input).map_err(|error| LoadCaseError::Parse(error, extract_declared_vars(&input)))
}

/// All load failures handled inside the child process.
#[derive(Debug)]
enum LoadCaseError {
    /// The file could not be read or decompressed.
    Input(String),
    /// The text could be read, but DIMACS parsing failed.
    Parse(String, usize),
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

/// Extracts the declared variable count from a DIMACS problem line when present.
fn extract_declared_vars(input: &str) -> usize {
    input
        .lines()
        .map(str::trim)
        .find_map(|line| {
            let mut parts = line.split_whitespace();
            match (parts.next(), parts.next(), parts.next()) {
                (Some("p"), Some("cnf"), Some(vars)) => vars.parse::<usize>().ok(),
                _ => None,
            }
        })
        .unwrap_or(0)
}
