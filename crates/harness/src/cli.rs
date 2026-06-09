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
    about = "Run incremental SMT-LIB benchmarks with subprocess isolation and live progress output."
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
    /// Run one benchmark case repeatedly and report elapsed-time distribution.
    Bench(BenchmarkArgs),
    /// Compare two previously saved harness result files.
    Compare(CompareArgs),
    /// Run one benchmark case in an isolated process and emit raw artifacts.
    ///
    /// This command is primarily useful when inspecting the raw JSON report,
    /// telemetry stream, or an uncaptured Rust panic backtrace for one case.
    Case(RunCaseArgs),
}

/// Arguments for the user-facing `benchmark` command.
#[derive(Debug, Args)]
pub(crate) struct BenchmarkArgs {
    /// The case file to execute repeatedly.
    pub(crate) case: PathBuf,
    /// The number of measured runs.
    #[arg(short = 'n', long, default_value = "20")]
    pub(crate) iterations: NonZeroUsize,
    /// The number of unmeasured runs to execute before measurement.
    #[arg(long, default_value_t = 0)]
    pub(crate) warmup: usize,
    /// The per-run timeout.
    #[arg(short, long, default_value = "30s", value_parser = parse_timeout)]
    pub(crate) timeout: Duration,
}

/// Arguments for the user-facing `run` command.
#[derive(Debug, Args)]
pub(crate) struct RunArgs {
    /// Benchmark roots to scan.
    ///
    /// When omitted, the harness scans the current directory.
    pub(crate) roots: Vec<PathBuf>,
    /// The number of child processes to run concurrently.
    ///
    /// When omitted, the harness defaults to the number of physical CPU cores
    /// available to the current process.
    #[arg(short, long)]
    pub(crate) jobs: Option<NonZeroUsize>,
    /// The per-case timeout.
    #[arg(short, long, default_value = "30s", value_parser = parse_timeout)]
    pub(crate) timeout: Duration,
    /// Controls which per-case outcome lines are printed during the live run.
    #[command(flatten)]
    output: OutputModeArgs,
    /// Writes the complete run result to this JSON file.
    #[arg(long)]
    pub(crate) save: Option<PathBuf>,
}

impl RunArgs {
    /// Returns the effective per-case output mode chosen on the command line.
    pub(crate) fn output_mode(&self) -> OutputMode {
        self.output.mode()
    }
}

/// Controls which per-case outcome lines are printed during a live run.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub(crate) enum OutputMode {
    /// Print one outcome line for every completed case.
    All,
    /// Print outcome lines only for failures. This is the default.
    #[default]
    FailOnly,
    /// Do not print per-case outcome lines.
    Terse,
}

/// Mutually exclusive command-line flags that select one [`OutputMode`].
#[derive(Copy, Clone, Debug, Default, Args, Eq, PartialEq)]
#[group(id = "output-mode", multiple = false)]
struct OutputModeArgs {
    /// Print one outcome line for every completed case.
    #[arg(long, group = "output-mode")]
    all: bool,
    /// Print outcome lines only for failures.
    #[arg(long, group = "output-mode")]
    fail_only: bool,
    /// Do not print per-case outcome lines.
    #[arg(long, group = "output-mode")]
    terse: bool,
}

impl OutputModeArgs {
    /// Resolves the mutually exclusive flags into one effective output mode.
    fn mode(self) -> OutputMode {
        if self.all {
            OutputMode::All
        } else if self.terse {
            OutputMode::Terse
        } else {
            OutputMode::FailOnly
        }
    }
}

/// Arguments for the user-facing `compare` command.
#[derive(Debug, Args)]
pub(crate) struct CompareArgs {
    /// The first saved JSON result file.
    pub(crate) left: PathBuf,
    /// The second saved JSON result file.
    pub(crate) right: PathBuf,
}

/// Arguments for the isolated single-case execution entrypoint.
#[derive(Debug, Args)]
pub(crate) struct RunCaseArgs {
    /// The case file to execute.
    pub(crate) case: PathBuf,
    /// The JSON report destination path.
    #[arg(long)]
    pub(crate) report: PathBuf,
    /// The precomputed number of `check-sat` queries discovered by the parent.
    #[arg(long, hide = true)]
    pub(crate) expected_query_count: Option<usize>,
    /// The JSONL telemetry destination path.
    #[cfg(feature = "telemetry")]
    #[arg(long)]
    pub(crate) telemetry: PathBuf,
}

#[cfg(test)]
mod tests {
    use clap::Parser as _;

    use super::{Cli, HarnessCommand, OutputMode};

    /// Ensures the default `run` output mode remains failure-only.
    #[test]
    fn run_defaults_to_failure_only_output() {
        let cli = Cli::parse_from(["my-harness", "run"]);
        let HarnessCommand::Run(args) = cli.command else {
            panic!("expected run command");
        };
        assert_eq!(args.output_mode(), OutputMode::FailOnly);
    }

    /// Ensures each public output-mode flag maps to the intended enum variant.
    #[test]
    fn run_accepts_each_output_mode_flag() {
        for (flag, expected_mode) in [
            ("--all", OutputMode::All),
            ("--fail-only", OutputMode::FailOnly),
            ("--terse", OutputMode::Terse),
        ] {
            let cli = Cli::parse_from(["my-harness", "run", flag]);
            let HarnessCommand::Run(args) = cli.command else {
                panic!("expected run command");
            };
            assert_eq!(args.output_mode(), expected_mode, "flag {flag}");
        }
    }

    /// Ensures the output-mode flags stay mutually exclusive.
    #[test]
    fn run_rejects_multiple_output_mode_flags() {
        let result = Cli::try_parse_from(["my-harness", "run", "--all", "--terse"]);
        assert!(result.is_err());
    }

    /// Ensures the repeated single-case benchmark command is publicly parseable.
    #[test]
    fn benchmark_is_publicly_parseable() {
        let cli = Cli::parse_from([
            "my-harness",
            "benchmark",
            "fixture/example.smt2",
            "--iterations",
            "7",
            "--warmup",
            "2",
            "--timeout",
            "5s",
        ]);
        let HarnessCommand::Bench(args) = cli.command else {
            panic!("expected benchmark command");
        };
        assert_eq!(args.iterations.get(), 7);
        assert_eq!(args.warmup, 2);
    }

    /// Ensures the single-case entrypoint is publicly available under `case`.
    #[test]
    fn run_case_is_publicly_parseable() {
        let cli = Cli::parse_from([
            "my-harness",
            "case",
            "fixture/example.smt2",
            "--report",
            "report.json",
            #[cfg(feature = "telemetry")]
            "--telemetry",
            #[cfg(feature = "telemetry")]
            "telemetry.jsonl",
        ]);
        assert!(matches!(cli.command, HarnessCommand::Case(_)));
    }
}
