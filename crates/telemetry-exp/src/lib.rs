//! Shared types for the observability experiment crate.
//!
//! The package contains two binaries:
//! - `solver`, which emits periodic statistics samples on stderr as JSON lines.
//! - `harness`, which launches the solver, parses those samples, and writes them
//!   to CSV and JSONL files for inspection.

use serde::{Deserialize, Serialize};

/// Wire-format sample emitted by the solver and consumed by the harness.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
pub struct StatsSample {
    /// Elapsed wall-clock time, measured in seconds since solver start.
    pub t: f64,
    /// Number of solver steps completed since the previous sample.
    pub steps: u64,
    /// Number of conflicts observed since the previous sample.
    pub conflicts: u64,
    /// Number of propagations observed since the previous sample.
    pub propagations: u64,
    /// Number of decisions observed since the previous sample.
    pub decisions: u64,
}

impl StatsSample {
    /// Sample discriminator written by the solver.
    pub const KIND: &'static str = "stats";
}
