//! A subprocess-isolated benchmark harness for the [`sat`] solver.
//!
//! The parent process discovers benchmark inputs, runs one benchmark per child
//! process, enforces wall-clock timeouts, and renders a friendly terminal view.
//! Each child process loads exactly one DIMACS case and emits a compact JSON
//! report so that panics, signals, and out-of-memory kills stay isolated.

mod child;
mod cli;
mod discover;
mod model;
mod parent;
mod render;
mod util;

use std::process::ExitCode;

use clap::Parser;
use console::style;

use crate::child::run_child;
use crate::cli::{Cli, HarnessCommand};
use crate::model::{OutcomeStats, RunSummary};
use crate::parent::run_parent;

/// Runs the selected harness subcommand and maps the result onto an exit code.
pub fn main() -> ExitCode {
    match run_command(Cli::parse()) {
        Ok(summary) => {
            if summary.stats.has_failures() {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(error) => {
            eprintln!("{} {error}", style("error").red().bold());
            ExitCode::from(2)
        }
    }
}

/// Dispatches one parsed CLI command.
fn run_command(cli: Cli) -> Result<RunSummary, String> {
    match cli.command {
        HarnessCommand::Run(args) => run_parent(args),
        HarnessCommand::InternalRunCase(args) => {
            run_child(args)?;
            Ok(RunSummary {
                stats: OutcomeStats::default(),
            })
        }
    }
}
