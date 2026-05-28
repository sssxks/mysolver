//! SAT-local telemetry adapters.
//!
//! The concrete recorder, sample format, and cross-theory aggregation now live
//! in the standalone `qfuf-telemetry` crate. This module keeps the SAT solver's
//! hot-path API compact and feature-gated.

#[cfg(feature = "telemetry")]
pub use telemetry::{EufGauges, Gauges as CombinedGauges, SatGauges as Gauges};

#[cfg(not(feature = "telemetry"))]
/// Placeholder SAT gauge type used when telemetry instrumentation is disabled.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Gauges;

#[cfg(not(feature = "telemetry"))]
/// Placeholder theory-gauge type used when telemetry instrumentation is disabled.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct EufGauges;

#[cfg(not(feature = "telemetry"))]
/// Placeholder combined gauge type used when telemetry instrumentation is disabled.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CombinedGauges;

/// Initializes the SAT current-value gauges for one solver run.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn initialize_solver_gauges(live_irredundant_clauses: usize, watcher_entries: usize) {
    telemetry::initialize_sat_solver_gauges(live_irredundant_clauses, watcher_entries);
}

/// Initializes the SAT current-value gauges for one solver run.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn initialize_solver_gauges(_live_irredundant_clauses: usize, _watcher_entries: usize) {}

/// Increments the watcher-entry gauge by `count`.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_added_watchers(count: usize) {
    telemetry::record_sat_added_watchers(count);
}

/// Increments the watcher-entry gauge by `count`.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_added_watchers(_count: usize) {}

/// Decrements the watcher-entry gauge by `count`.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_removed_watchers(count: usize) {
    telemetry::record_sat_removed_watchers(count);
}

/// Decrements the watcher-entry gauge by `count`.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_removed_watchers(_count: usize) {}

/// Records one SAT conflict event.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_conflict() {
    telemetry::record_sat_conflict();
}

/// Records one SAT conflict event.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_conflict() {}

/// Records one SAT propagated assignment.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_propagation() {
    telemetry::record_sat_propagation();
}

/// Records one SAT propagated assignment.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_propagation() {}

/// Records one SAT branching decision.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_decision() {
    telemetry::record_sat_decision();
}

/// Records one SAT branching decision.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_decision() {}

/// Records one SAT restart event.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_restart() {
    telemetry::record_sat_restart();
}

/// Records one SAT restart event.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_restart() {}

/// Records one SAT learned-database reduction.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_reduction() {
    telemetry::record_sat_reduction();
}

/// Records one SAT learned-database reduction.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_reduction() {}

/// Records one learned clause insertion.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_learnt_clause() {
    telemetry::record_sat_learnt_clause();
}

/// Records one learned clause insertion.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_learnt_clause() {}

/// Records `count` deleted learned clauses.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_deleted_clauses(count: usize) {
    telemetry::record_sat_deleted_clauses(count);
}

/// Records `count` deleted learned clauses.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_deleted_clauses(_count: usize) {}

/// Returns the current irredundant-clause gauge.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn live_irredundant_clauses() -> u64 {
    telemetry::sat_live_irredundant_clauses()
}

/// Returns the current irredundant-clause gauge.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn live_irredundant_clauses() -> u64 {
    0
}

/// Returns the current watcher-entry gauge.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn watcher_entries() -> u64 {
    telemetry::sat_watcher_entries()
}

/// Returns the current watcher-entry gauge.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn watcher_entries() -> u64 {
    0
}

/// Emits one combined SAT-plus-theory sample when a timer tick is pending.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn maybe_emit_sample<F: FnOnce() -> CombinedGauges>(gauges: F) {
    telemetry::maybe_emit_sample(gauges);
}

/// Emits one combined SAT-plus-theory sample when a timer tick is pending.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn maybe_emit_sample<F>(_gauges: F)
where
    F: FnOnce(),
{
}
