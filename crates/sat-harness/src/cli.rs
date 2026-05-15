//! Command-line definitions for the benchmark harness.

use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::time::Duration;

use clap::{Args, Parser, Subcommand};

use crate::util::parse_timeout;

/// The benchmark runner command line.
#[derive(Debug, Parser)]
#[command(
    author,
    version,
    about = "Run SAT benchmarks with subprocess isolation and live progress output."
)]
pub(crate) struct Cli {
    /// The subcommand to execute.
    #[command(subcommand)]
    pub(crate) command: HarnessCommand,
}

/// All supported harness subcommands.
#[derive(Debug, Subcommand)]
pub(crate) enum HarnessCommand {
    /// Discover and execute benchmark cases.
    Run(RunArgs),
    /// Compare two previously saved harness result files.
    Compare(CompareArgs),
    /// Run one benchmark case in an isolated child process.
    #[command(hide = true, name = "__internal-run-case")]
    InternalRunCase(InternalRunCaseArgs),
}

/// Arguments for the user-facing `run` command.
#[derive(Debug, Args)]
pub(crate) struct RunArgs {
    /// Benchmark roots to scan.
    ///
    /// When omitted, the harness scans `test/fixture/sat`.
    pub(crate) roots: Vec<PathBuf>,
    /// The number of child processes to run concurrently.
    #[arg(short, long)]
    pub(crate) jobs: Option<NonZeroUsize>,
    /// The per-case timeout.
    #[arg(short, long, default_value = "30s", value_parser = parse_timeout)]
    pub(crate) timeout: Duration,
    /// Prints one outcome line for every completed case instead of failures only.
    #[arg(short, long)]
    pub(crate) all: bool,
    /// Writes the complete run result to this JSON file.
    #[arg(long)]
    pub(crate) save: Option<PathBuf>,
}

/// Arguments for the user-facing `compare` command.
#[derive(Debug, Args)]
pub(crate) struct CompareArgs {
    /// The first saved JSON result file.
    pub(crate) left: PathBuf,
    /// The second saved JSON result file.
    pub(crate) right: PathBuf,
}

/// Arguments for the hidden child-process entrypoint.
#[derive(Debug, Args)]
pub(crate) struct InternalRunCaseArgs {
    /// The case file to execute.
    #[arg(long)]
    pub(crate) case: PathBuf,
    /// The JSON report written back to the parent process.
    #[arg(long)]
    pub(crate) report: PathBuf,
    /// The JSONL telemetry file written back to the parent process.
    #[arg(long)]
    pub(crate) telemetry: PathBuf,
}
