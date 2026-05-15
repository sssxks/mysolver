//! Harness that runs the demo solver and persists its emitted samples.

use std::env;
use std::error::Error;
use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::thread;
use telemetry_exp::StatsSample;

/// Convenient result alias for the harness binary.
type AppResult<T> = Result<T, Box<dyn Error + Send + Sync>>;

/// Output file names written by the harness.
struct OutputPaths {
    /// CSV export path.
    csv: PathBuf,
    /// JSONL export path.
    jsonl: PathBuf,
}

impl OutputPaths {
    /// Builds the output paths rooted at the crate directory.
    fn new(root: &Path) -> Self {
        Self {
            csv: root.join("stats.csv"),
            jsonl: root.join("stats.jsonl"),
        }
    }
}

/// Spawns the solver via Cargo from the package directory.
fn spawn_solver() -> io::Result<std::process::Child> {
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));

    Command::new(cargo)
        .args([
            "run",
            "--quiet",
            "--release",
            "--bin",
            "solver",
            "-p",
            env!("CARGO_PKG_NAME"),
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
}

/// Streams solver stdout to the parent stdout for visibility.
fn forward_stdout(stdout: impl io::Read + Send + 'static) -> thread::JoinHandle<AppResult<()>> {
    thread::spawn(move || {
        let reader = BufReader::new(stdout);

        for line in reader.lines() {
            let line = line?;
            println!("solver stdout: {line}");
        }

        Ok(())
    })
}

/// Parses solver stderr, collecting JSON samples and forwarding any plain text.
fn collect_samples(
    stderr: impl io::Read + Send + 'static,
) -> thread::JoinHandle<AppResult<Vec<StatsSample>>> {
    thread::spawn(move || {
        let reader = BufReader::new(stderr);
        let mut samples = Vec::new();

        for line in reader.lines() {
            let line = line?;

            match serde_json::from_str::<StatsSample>(&line) {
                Ok(sample) => {
                    eprintln!("stats: {sample:?}");
                    samples.push(sample);
                }
                Err(_) => {
                    eprintln!("solver stderr: {line}");
                }
            }
        }

        Ok(samples)
    })
}

/// Joins a worker thread and converts panics into ordinary errors.
fn join_thread<T>(name: &'static str, handle: thread::JoinHandle<AppResult<T>>) -> AppResult<T> {
    match handle.join() {
        Ok(result) => result,
        Err(_) => Err(format!("{name} thread panicked").into()),
    }
}

/// Writes the collected samples to a CSV file.
fn write_csv(path: &Path, samples: &[StatsSample]) -> io::Result<()> {
    let mut csv = File::create(path)?;
    writeln!(csv, "t,steps,conflicts,propagations,decisions")?;

    for sample in samples {
        writeln!(
            csv,
            "{},{},{},{},{}",
            sample.t, sample.steps, sample.conflicts, sample.propagations, sample.decisions
        )?;
    }

    Ok(())
}

/// Writes the collected samples back out as JSON lines.
fn write_jsonl(path: &Path, samples: &[StatsSample]) -> io::Result<()> {
    let mut json = File::create(path)?;

    for sample in samples {
        serde_json::to_writer(&mut json, sample)?;
        writeln!(json)?;
    }

    Ok(())
}

/// Reports the child exit status and output paths.
fn report_completion(status: ExitStatus, outputs: &OutputPaths) {
    eprintln!("solver exited with: {status}");
    eprintln!(
        "wrote {} and {}",
        outputs.csv.display(),
        outputs.jsonl.display()
    );
}

/// Runs the harness end to end.
fn main() -> AppResult<()> {
    let mut child = spawn_solver()?;
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| String::from("solver stdout pipe was not available"))?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| String::from("solver stderr pipe was not available"))?;

    let stdout_thread = forward_stdout(stdout);
    let stderr_thread = collect_samples(stderr);

    let status = child.wait()?;
    join_thread("stdout", stdout_thread)?;
    let samples = join_thread("stderr", stderr_thread)?;

    let outputs = OutputPaths::new(Path::new(env!("CARGO_MANIFEST_DIR")));
    write_csv(&outputs.csv, &samples)?;
    write_jsonl(&outputs.jsonl, &samples)?;
    report_completion(status, &outputs);
    Ok(())
}
