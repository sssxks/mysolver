//! Telemetry implementation compiled when solver instrumentation is disabled.

use std::io;
use std::path::Path;
use std::time::Duration;

use super::Gauges;

/// A guard that preserves the telemetry API while instrumentation is compiled out.
#[derive(Debug, Default)]
pub struct TelemetryRecorder;

impl TelemetryRecorder {
    /// Starts a no-op telemetry recorder.
    #[inline(always)]
    pub fn start(_path: &Path) -> io::Result<Self> {
        Ok(Self)
    }

    /// Starts a no-op telemetry recorder with a custom sampling period.
    #[inline(always)]
    pub fn with_period(_path: &Path, _period: Duration) -> io::Result<Self> {
        Ok(Self)
    }

    /// Finishes a no-op telemetry recorder.
    #[inline(always)]
    pub fn finish(self, _gauges: Gauges) -> io::Result<()> {
        Ok(())
    }
}

/// Records one conflict event.
#[inline(always)]
pub(crate) fn record_conflict() {}

/// Records one propagated assignment.
#[inline(always)]
pub(crate) fn record_propagation() {}

/// Records one branching decision.
#[inline(always)]
pub(crate) fn record_decision() {}

/// Records one restart.
#[inline(always)]
pub(crate) fn record_restart() {}

/// Records one learned-database reduction.
#[inline(always)]
pub(crate) fn record_reduction() {}

/// Records one learned clause insertion.
#[inline(always)]
pub(crate) fn record_learnt_clause() {}

/// Records `count` deleted clauses from a learned-database reduction.
#[inline(always)]
pub(crate) fn record_deleted_clauses(_count: usize) {}

/// Initializes the current-value gauges for one solver run.
#[inline(always)]
pub(crate) fn initialize_solver_gauges(_live_irredundant_clauses: usize, _watcher_entries: usize) {}

/// Increments the watcher-entry gauge by `count`.
#[inline(always)]
pub(crate) fn record_added_watchers(_count: usize) {}

/// Decrements the watcher-entry gauge by `count`.
#[inline(always)]
pub(crate) fn record_removed_watchers(_count: usize) {}
