//! Child-process execution for isolated benchmark runs.

use std::env;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use bzip2::read::BzDecoder;
use flate2::read::MultiGzDecoder;
#[cfg(feature = "telemetry")]
use qfuf_telemetry::PATH_ENV_VAR;

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
    run_qfuf_process(input, Some(&args.telemetry))
}

/// Solves one case without compiling in telemetry instrumentation.
#[cfg(not(feature = "telemetry"))]
fn solve_case_with_optional_telemetry(
    input: &str,
    _args: &RunCaseArgs,
) -> Result<ChildReportKind, String> {
    run_qfuf_process(input, None)
}

/// Executes the `qfuf` solver binary over stdin/stdout for one whole trace.
fn run_qfuf_process(input: &str, telemetry_path: Option<&Path>) -> Result<ChildReportKind, String> {
    let expected_queries = match query_count(input) {
        Ok(count) => count,
        Err(error) => return Ok(ChildReportKind::ParseError(error)),
    };
    #[cfg(not(feature = "telemetry"))]
    let _ = telemetry_path;
    let current_exe = env::current_exe()
        .map_err(|error| format!("failed to locate current executable: {error}"))?;
    let mut command = qfuf_command(&current_exe);
    #[cfg(feature = "telemetry")]
    if let Some(telemetry_path) = telemetry_path {
        command.env(PATH_ENV_VAR, telemetry_path);
    }

    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to spawn qfuf through cargo: {error}"))?;

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

/// Builds the stable `cargo run` command used to compile and execute `qfuf`.
fn qfuf_command(current_exe: &Path) -> Command {
    let mut command = Command::new("cargo");
    command.arg("run").arg("--quiet");
    append_inferred_cargo_profile(&mut command, current_exe);
    command
        .arg("--manifest-path")
        .arg(qfuf_manifest_path())
        .arg("--bin")
        .arg("qfuf");
    command
}

/// Appends the cargo profile that matches the currently running harness binary.
fn append_inferred_cargo_profile(command: &mut Command, current_exe: &Path) {
    match infer_cargo_profile(current_exe) {
        Some(CargoProfile::Release) => {
            command.arg("--release");
        }
        Some(CargoProfile::Named(profile)) => {
            command.arg("--profile").arg(profile.as_ref());
        }
        Some(CargoProfile::Dev) | None => {}
    }
}

/// Resolves the solver manifest path relative to this crate's manifest.
fn qfuf_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../qfuf")
        .join("Cargo.toml")
}

/// The cargo profile to reuse when spawning `qfuf`.
#[derive(Debug, Eq, PartialEq)]
enum CargoProfile {
    /// The default development profile stored under `target/debug`.
    Dev,
    /// The built-in optimized profile stored under `target/release`.
    Release,
    /// Any custom named profile, such as `perf`.
    Named(Box<str>),
}

/// Infers the cargo profile from the harness executable's location under `target/`.
fn infer_cargo_profile(current_exe: &Path) -> Option<CargoProfile> {
    let executable_dir = current_exe.parent()?;
    let profile_dir = if executable_dir.file_name() == Some(OsStr::new("deps")) {
        executable_dir.parent()?
    } else {
        executable_dir
    };
    if profile_dir.parent()?.file_name() != Some(OsStr::new("target")) {
        return None;
    }
    let profile_name = profile_dir.file_name()?.to_str()?;
    match profile_name {
        "debug" => Some(CargoProfile::Dev),
        "release" => Some(CargoProfile::Release),
        other => Some(CargoProfile::Named(other.into())),
    }
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

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{CargoProfile, infer_cargo_profile, qfuf_command, qfuf_manifest_path};

    /// Reuses Cargo's default dev profile for binaries under `target/debug`.
    #[test]
    fn infers_dev_profile_from_debug_binary() {
        let profile = infer_cargo_profile(Path::new("/tmp/mysolver/target/debug/my-harness"));
        assert_eq!(profile, Some(CargoProfile::Dev));
    }

    /// Reuses Cargo's optimized release profile for binaries under `target/release`.
    #[test]
    fn infers_release_profile_from_release_binary() {
        let profile = infer_cargo_profile(Path::new("/tmp/mysolver/target/release/my-harness"));
        assert_eq!(profile, Some(CargoProfile::Release));
    }

    /// Preserves custom named profiles such as `perf`.
    #[test]
    fn infers_named_profile_from_custom_binary() {
        let profile = infer_cargo_profile(Path::new("/tmp/mysolver/target/perf/my-harness"));
        assert_eq!(profile, Some(CargoProfile::Named("perf".into())));
    }

    /// Ignores paths that are not cargo target outputs.
    #[test]
    fn rejects_non_target_binaries() {
        let profile = infer_cargo_profile(Path::new("/usr/local/bin/my-harness"));
        assert_eq!(profile, None);
    }

    /// Builds `cargo run` against the solver manifest instead of guessing a sibling binary.
    #[test]
    fn qfuf_command_uses_manifest_path() {
        let command = qfuf_command(Path::new("/tmp/mysolver/target/release/my-harness"));
        let args = command
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert!(args.starts_with(&[
            "run".to_string(),
            "--quiet".to_string(),
            "--release".to_string(),
            "--manifest-path".to_string(),
            qfuf_manifest_path().display().to_string(),
            "--bin".to_string(),
            "qfuf".to_string(),
        ]));
    }
}
