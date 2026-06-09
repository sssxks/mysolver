//! A subprocess-isolated benchmark harness for the local solver libraries.
//!
//! The parent process discovers benchmark inputs, runs one benchmark per child
//! process, enforces wall-clock timeouts, and renders a friendly terminal view.
//! Each child process loads one SMT-LIB trace, calls the `qfuf` solver library
//! directly, and emits a compact JSON report so that panics, signals,
//! and out-of-memory kills stay isolated.

mod benchmark;
mod case_io;
mod child;
mod cli;
mod compare;
mod discover;
mod model;
mod parent;
mod render;
mod util;

use std::process::ExitCode;

use clap::Parser;
use console::style;

use crate::benchmark::run_benchmark;
use crate::child::run_child;
use crate::cli::{Cli, HarnessCommand};
use crate::compare::compare_saved_runs;
use crate::parent::run_parent;

/// Runs the selected harness subcommand and maps the result onto an exit code.
pub fn main() -> ExitCode {
    match run_command(Cli::parse()) {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("{} {error}", style("error").red().bold());
            ExitCode::from(2)
        }
    }
}

/// Dispatches one parsed CLI command.
fn run_command(cli: Cli) -> Result<u8, String> {
    match cli.command {
        HarnessCommand::Run(args) => Ok(u8::from(run_parent(args)?.stats.has_failures())),
        HarnessCommand::Bench(args) => Ok(u8::from(run_benchmark(args)?.has_failures())),
        HarnessCommand::Compare(args) => Ok(u8::from(!compare_saved_runs(args)?)),
        HarnessCommand::Case(args) => {
            run_child(args)?;
            Ok(0)
        }
    }
}
