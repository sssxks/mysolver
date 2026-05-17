//! Low-overhead solver telemetry backed by thread-local counters.
//!
//! When the `telemetry` Cargo feature is enabled, the hot solver paths record
//! counter bumps into thread-local [`std::cell::Cell`]s. A background timer
//! thread requests periodic flushes, and the solving thread serializes one JSON
//! line sample whenever it next reaches a safe checkpoint.
//!
//! When the feature is disabled, the same API remains available but
//! instrumentation compiles to no-op implementations so optimized builds can
//! remove the hot-path telemetry cost entirely.

#[cfg(not(feature = "telemetry"))]
mod disabled;
#[cfg(feature = "telemetry")]
mod enabled;

use serde::{Deserialize, Serialize};

#[cfg(not(feature = "telemetry"))]
pub use disabled::TelemetryRecorder;
#[cfg(feature = "telemetry")]
pub use enabled::TelemetryRecorder;

#[cfg(not(feature = "telemetry"))]
pub(crate) use disabled::{
    initialize_solver_gauges, record_added_watchers, record_conflict, record_decision,
    record_deleted_clauses, record_learnt_clause, record_propagation, record_reduction,
    record_removed_watchers, record_restart,
};
#[cfg(feature = "telemetry")]
pub(crate) use enabled::{
    initialize_solver_gauges, live_irredundant_clauses, maybe_emit_sample, record_added_watchers,
    record_conflict, record_decision, record_deleted_clauses, record_learnt_clause,
    record_propagation, record_reduction, record_removed_watchers, record_restart, watcher_entries,
};

/// Default interval between periodic telemetry samples.
pub const DEFAULT_SAMPLE_PERIOD: std::time::Duration = std::time::Duration::from_secs(1);

/// Counter metrics accumulated between flushed samples.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Counters {
    /// Number of conflicts encountered since the previous sample.
    pub conflicts: u64,
    /// Number of propagated assignments enqueued since the previous sample.
    pub propagations: u64,
    /// Number of branching decisions made since the previous sample.
    pub decisions: u64,
    /// Number of restart events executed since the previous sample.
    pub restarts: u64,
    /// Number of learned-database reduction passes since the previous sample.
    pub reductions: u64,
    /// Number of learned clauses added since the previous sample.
    pub learnt_clauses: u64,
    /// Number of clauses deleted from the learned database since the previous sample.
    pub deleted_clauses: u64,
}

/// Gauge metrics sampled from the live solver state.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Gauges {
    /// Current decision level.
    pub decision_level: u64,
    /// Number of variables currently assigned.
    pub assigned_vars: u64,
    /// Length of the assignment trail.
    pub trail_len: u64,
    /// Number of queued-but-not-yet-propagated trail entries.
    pub pending_propagations: u64,
    /// Number of live irredundant long clauses.
    pub live_irredundant_clauses: u64,
    /// Number of live learned clauses.
    pub live_learnt_clauses: u64,
    /// Number of watcher entries across all watch lists.
    pub watcher_entries: u64,
    /// Number of literal words currently stored in the clause arena.
    pub clause_words: u64,
    /// Number of dead literal words awaiting compaction.
    pub wasted_clause_words: u64,
}

/// One periodic JSONL telemetry sample emitted by the solver.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Sample {
    /// Seconds elapsed since the telemetry session started.
    pub elapsed_secs: f64,
    /// Counter deltas accumulated since the previous sample.
    pub counters: Counters,
    /// Point-in-time gauges captured at the sample boundary.
    pub gauges: Gauges,
}

/// Aggregate telemetry derived from one case's emitted samples.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    /// Number of samples observed for the case.
    pub sample_count: u64,
    /// Total conflicts across all samples.
    pub total_conflicts: u64,
    /// Total propagated assignments across all samples.
    pub total_propagations: u64,
    /// Total branching decisions across all samples.
    pub total_decisions: u64,
    /// Total restart events across all samples.
    pub total_restarts: u64,
    /// Total learned-database reductions across all samples.
    pub total_reductions: u64,
    /// Total learned clauses added across all samples.
    pub total_learnt_clauses: u64,
    /// Total clauses deleted across all samples.
    pub total_deleted_clauses: u64,
    /// Highest sampled decision level.
    pub peak_decision_level: u64,
    /// Highest sampled assigned-variable count.
    pub peak_assigned_vars: u64,
    /// Highest sampled trail length.
    pub peak_trail_len: u64,
    /// Highest sampled propagation-queue depth.
    pub peak_pending_propagations: u64,
    /// Highest sampled irredundant long-clause count.
    pub peak_live_irredundant_clauses: u64,
    /// Highest sampled learned-clause count.
    pub peak_live_learnt_clauses: u64,
    /// Highest sampled watcher-entry count.
    pub peak_watcher_entries: u64,
    /// Highest sampled clause-arena literal payload.
    pub peak_clause_words: u64,
    /// Highest sampled dead literal payload.
    pub peak_wasted_clause_words: u64,
    /// Final sampled decision level.
    pub final_decision_level: u64,
    /// Final sampled assigned-variable count.
    pub final_assigned_vars: u64,
    /// Final sampled trail length.
    pub final_trail_len: u64,
    /// Final sampled learned-clause count.
    pub final_live_learnt_clauses: u64,
    /// Final sampled irredundant long-clause count.
    pub final_live_irredundant_clauses: u64,
}

impl Summary {
    /// Aggregates one full sample stream into one compact summary.
    pub fn from_samples(samples: &[Sample]) -> Option<Self> {
        let last = samples.last()?;
        let mut summary = Self {
            sample_count: samples.len() as u64,
            final_decision_level: last.gauges.decision_level,
            final_assigned_vars: last.gauges.assigned_vars,
            final_trail_len: last.gauges.trail_len,
            final_live_learnt_clauses: last.gauges.live_learnt_clauses,
            final_live_irredundant_clauses: last.gauges.live_irredundant_clauses,
            ..Self::default()
        };

        for sample in samples {
            summary.total_conflicts += sample.counters.conflicts;
            summary.total_propagations += sample.counters.propagations;
            summary.total_decisions += sample.counters.decisions;
            summary.total_restarts += sample.counters.restarts;
            summary.total_reductions += sample.counters.reductions;
            summary.total_learnt_clauses += sample.counters.learnt_clauses;
            summary.total_deleted_clauses += sample.counters.deleted_clauses;

            summary.peak_decision_level = summary
                .peak_decision_level
                .max(sample.gauges.decision_level);
            summary.peak_assigned_vars =
                summary.peak_assigned_vars.max(sample.gauges.assigned_vars);
            summary.peak_trail_len = summary.peak_trail_len.max(sample.gauges.trail_len);
            summary.peak_pending_propagations = summary
                .peak_pending_propagations
                .max(sample.gauges.pending_propagations);
            summary.peak_live_irredundant_clauses = summary
                .peak_live_irredundant_clauses
                .max(sample.gauges.live_irredundant_clauses);
            summary.peak_live_learnt_clauses = summary
                .peak_live_learnt_clauses
                .max(sample.gauges.live_learnt_clauses);
            summary.peak_watcher_entries = summary
                .peak_watcher_entries
                .max(sample.gauges.watcher_entries);
            summary.peak_clause_words = summary.peak_clause_words.max(sample.gauges.clause_words);
            summary.peak_wasted_clause_words = summary
                .peak_wasted_clause_words
                .max(sample.gauges.wasted_clause_words);
        }

        Some(summary)
    }
}

#[cfg(test)]
mod tests {
    use super::{Counters, Gauges, Sample, Summary};

    /// Ensures telemetry aggregation combines counter totals and gauge peaks.
    #[test]
    fn summary_aggregates_samples() {
        let samples = [
            Sample {
                elapsed_secs: 0.5,
                counters: Counters {
                    conflicts: 2,
                    propagations: 10,
                    decisions: 1,
                    restarts: 0,
                    reductions: 0,
                    learnt_clauses: 2,
                    deleted_clauses: 0,
                },
                gauges: Gauges {
                    decision_level: 3,
                    assigned_vars: 8,
                    trail_len: 8,
                    pending_propagations: 2,
                    live_irredundant_clauses: 20,
                    live_learnt_clauses: 2,
                    watcher_entries: 40,
                    clause_words: 90,
                    wasted_clause_words: 0,
                },
            },
            Sample {
                elapsed_secs: 1.0,
                counters: Counters {
                    conflicts: 5,
                    propagations: 12,
                    decisions: 3,
                    restarts: 1,
                    reductions: 1,
                    learnt_clauses: 4,
                    deleted_clauses: 2,
                },
                gauges: Gauges {
                    decision_level: 5,
                    assigned_vars: 11,
                    trail_len: 11,
                    pending_propagations: 4,
                    live_irredundant_clauses: 20,
                    live_learnt_clauses: 4,
                    watcher_entries: 48,
                    clause_words: 95,
                    wasted_clause_words: 3,
                },
            },
        ];

        let summary = Summary::from_samples(&samples).expect("summary");
        assert_eq!(summary.sample_count, 2);
        assert_eq!(summary.total_conflicts, 7);
        assert_eq!(summary.total_propagations, 22);
        assert_eq!(summary.total_decisions, 4);
        assert_eq!(summary.total_restarts, 1);
        assert_eq!(summary.total_reductions, 1);
        assert_eq!(summary.total_learnt_clauses, 6);
        assert_eq!(summary.total_deleted_clauses, 2);
        assert_eq!(summary.peak_decision_level, 5);
        assert_eq!(summary.peak_assigned_vars, 11);
        assert_eq!(summary.final_live_learnt_clauses, 4);
    }
}
