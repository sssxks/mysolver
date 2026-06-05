//! Periodic telemetry for one full `qfuf` solve session.
//!
//! Semantically, one telemetry stream is a time-ordered list of periodic samples:
//! `Sample*`.
//!
//! # Encoding
//!
//! - Each sample is serialized as one JSON line.
//! - `Counters` store deltas since the previous emitted sample.
//! - `Gauges` store a point-in-time snapshot at the sample boundary.
//! - The final sample is emitted explicitly when the recorder finishes, so the
//!   caller always controls the closing snapshot.
//!
//! # Backends
//!
//! This crate exposes one stable facade over two runtime backends:
//! - `backend-atomic`: the timer thread snapshots atomically readable counters
//!   directly, so telemetry continues even if the solver stops yielding.
//! - `backend-cooperative`: the timer thread only requests a flush, and the
//!   solver thread emits the sample when it reaches a safe checkpoint.
//!
//! Unless `backend-cooperative` is explicitly enabled, the facade falls back to
//! the atomic backend.

use std::time::Duration;

use serde::{Deserialize, Serialize};

/// Atomic telemetry backend that keeps sampling even if the solver stops yielding.
#[cfg(not(feature = "backend-cooperative"))]
mod backend_atomic;
/// Cooperative telemetry backend that only emits samples at solver checkpoints.
#[cfg(feature = "backend-cooperative")]
mod backend_cooperative;

#[cfg(not(feature = "backend-cooperative"))]
use backend_atomic as backend;
#[cfg(feature = "backend-cooperative")]
use backend_cooperative as backend;

pub use backend::{
    TelemetryRecorder, initialize_sat_solver_gauges, maybe_emit_sample, publish_gauges,
    record_euf_congruence_merge, record_euf_input_disequality, record_euf_input_equality,
    record_euf_theory_conflict, record_euf_theory_propagation, record_sat_added_watchers,
    record_sat_conflict, record_sat_decision, record_sat_deleted_clauses, record_sat_learnt_clause,
    record_sat_propagation, record_sat_reduction, record_sat_removed_watchers, record_sat_restart,
    sat_live_irredundant_clauses, sat_watcher_entries,
};

/// Default interval between periodic telemetry samples.
pub(crate) const DEFAULT_SAMPLE_PERIOD: Duration = Duration::from_secs(1);

/// Counter metrics accumulated between flushed samples.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Counters {
    /// SAT-local counter deltas.
    sat: SatCounters,
    /// EUF-local counter deltas.
    euf: EufCounters,
}

/// Gauge metrics sampled from the live solver state.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Gauges {
    /// SAT-local point-in-time gauges.
    pub sat: SatGauges,
    /// EUF-local point-in-time gauges.
    pub euf: EufGauges,
}

/// One periodic JSONL telemetry sample emitted by `qfuf`.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Sample {
    /// Seconds elapsed since the telemetry session started.
    elapsed_secs: f64,
    /// Counter deltas accumulated since the previous sample.
    counters: Counters,
    /// Point-in-time gauges captured at the sample boundary.
    gauges: Gauges,
}

/// Aggregate telemetry derived from one case's emitted sample stream.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    /// Number of samples observed for the case.
    pub sample_count: u64,
    /// Aggregated SAT metrics.
    pub sat: SatSummary,
    /// Aggregated EUF metrics.
    pub euf: EufSummary,
}

impl Summary {
    /// Aggregates one full sample stream into one compact summary.
    pub fn from_samples(samples: &[Sample]) -> Option<Self> {
        let last = samples.last()?;
        let mut summary = Self {
            sample_count: samples.len() as u64,
            sat: SatSummary::from_final_gauges(last.gauges.sat),
            euf: EufSummary::from_final_gauges(last.gauges.euf),
        };

        for sample in samples {
            summary
                .sat
                .accumulate(sample.counters.sat, sample.gauges.sat);
            summary
                .euf
                .accumulate(sample.counters.euf, sample.gauges.euf);
        }

        Some(summary)
    }
}

/// SAT counter metrics accumulated between sample boundaries.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct SatCounters {
    /// Number of conflicts encountered since the previous sample.
    conflicts: u64,
    /// Number of propagated assignments enqueued since the previous sample.
    propagations: u64,
    /// Number of branching decisions made since the previous sample.
    decisions: u64,
    /// Number of restart events executed since the previous sample.
    restarts: u64,
    /// Number of learned-database reduction passes since the previous sample.
    reductions: u64,
    /// Number of learned clauses added since the previous sample.
    learnt_clauses: u64,
    /// Number of clauses deleted from the learned database since the previous sample.
    deleted_clauses: u64,
}

/// SAT gauge metrics sampled from the live solver state.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct SatGauges {
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

/// EUF counter metrics accumulated between sample boundaries.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct EufCounters {
    /// Number of asserted input equalities processed since the previous sample.
    input_equalities: u64,
    /// Number of asserted input disequalities processed since the previous sample.
    input_disequalities: u64,
    /// Number of congruence-driven merges performed since the previous sample.
    congruence_merges: u64,
    /// Number of theory propagation clauses emitted since the previous sample.
    theory_propagations: u64,
    /// Number of theory conflict clauses emitted since the previous sample.
    theory_conflicts: u64,
}

/// EUF gauge metrics sampled from the live theory state.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct EufGauges {
    /// Number of canonical terms in the permanent registry.
    pub registry_terms: u64,
    /// Number of canonical theory atoms in the permanent registry.
    pub registry_atoms: u64,
    /// Number of SAT assignments buffered for EUF processing.
    pub pending_assignments: u64,
    /// Number of theory atoms currently assigned on the EUF trail.
    pub assigned_atoms: u64,
    /// Number of pending merge inputs.
    pub pending_merges: u64,
    /// Number of pending congruence repairs.
    pub pending_repairs: u64,
    /// Number of pending atom triggers not yet processed.
    pub pending_atom_triggers: u64,
    /// Number of pending theory clauses buffered for SAT.
    pub pending_theory_clauses: u64,
    /// Number of active disequalities currently tracked.
    pub active_disequalities: u64,
    /// Number of live congruence-table entries.
    pub congruence_table_entries: u64,
}

/// Aggregate SAT telemetry derived from one case's sample stream.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct SatSummary {
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

impl SatSummary {
    /// Builds one summary seeded from the final gauge snapshot.
    fn from_final_gauges(gauges: SatGauges) -> Self {
        Self {
            final_decision_level: gauges.decision_level,
            final_assigned_vars: gauges.assigned_vars,
            final_trail_len: gauges.trail_len,
            final_live_learnt_clauses: gauges.live_learnt_clauses,
            final_live_irredundant_clauses: gauges.live_irredundant_clauses,
            ..Self::default()
        }
    }

    /// Folds one sample into this aggregate summary.
    fn accumulate(&mut self, counters: SatCounters, gauges: SatGauges) {
        self.total_conflicts += counters.conflicts;
        self.total_propagations += counters.propagations;
        self.total_decisions += counters.decisions;
        self.total_restarts += counters.restarts;
        self.total_reductions += counters.reductions;
        self.total_learnt_clauses += counters.learnt_clauses;
        self.total_deleted_clauses += counters.deleted_clauses;

        self.peak_decision_level = self.peak_decision_level.max(gauges.decision_level);
        self.peak_assigned_vars = self.peak_assigned_vars.max(gauges.assigned_vars);
        self.peak_trail_len = self.peak_trail_len.max(gauges.trail_len);
        self.peak_pending_propagations = self
            .peak_pending_propagations
            .max(gauges.pending_propagations);
        self.peak_live_irredundant_clauses = self
            .peak_live_irredundant_clauses
            .max(gauges.live_irredundant_clauses);
        self.peak_live_learnt_clauses = self
            .peak_live_learnt_clauses
            .max(gauges.live_learnt_clauses);
        self.peak_watcher_entries = self.peak_watcher_entries.max(gauges.watcher_entries);
        self.peak_clause_words = self.peak_clause_words.max(gauges.clause_words);
        self.peak_wasted_clause_words = self
            .peak_wasted_clause_words
            .max(gauges.wasted_clause_words);
    }
}

/// Aggregate EUF telemetry derived from one case's sample stream.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct EufSummary {
    /// Total asserted input equalities processed across all samples.
    pub total_input_equalities: u64,
    /// Total asserted input disequalities processed across all samples.
    pub total_input_disequalities: u64,
    /// Total congruence-driven merges across all samples.
    pub total_congruence_merges: u64,
    /// Total theory propagation clauses across all samples.
    pub total_theory_propagations: u64,
    /// Total theory conflict clauses across all samples.
    pub total_theory_conflicts: u64,
    /// Highest sampled registry-term count.
    pub peak_registry_terms: u64,
    /// Highest sampled registry-atom count.
    pub peak_registry_atoms: u64,
    /// Highest sampled pending-assignment count.
    pub peak_pending_assignments: u64,
    /// Highest sampled assigned-atom count.
    pub peak_assigned_atoms: u64,
    /// Highest sampled pending-merge count.
    pub peak_pending_merges: u64,
    /// Highest sampled pending-repair count.
    pub peak_pending_repairs: u64,
    /// Highest sampled pending-atom-trigger count.
    pub peak_pending_atom_triggers: u64,
    /// Highest sampled pending-theory-clause count.
    pub peak_pending_theory_clauses: u64,
    /// Highest sampled active-disequality count.
    pub peak_active_disequalities: u64,
    /// Highest sampled congruence-table size.
    pub peak_congruence_table_entries: u64,
    /// Highest sampled proof-edge count.
    pub peak_proof_edges: u64,
    /// Final sampled registry-term count.
    pub final_registry_terms: u64,
    /// Final sampled registry-atom count.
    pub final_registry_atoms: u64,
    /// Final sampled assigned-atom count.
    pub final_assigned_atoms: u64,
    /// Final sampled active-disequality count.
    pub final_active_disequalities: u64,
}

impl EufSummary {
    /// Builds one summary seeded from the final gauge snapshot.
    fn from_final_gauges(gauges: EufGauges) -> Self {
        Self {
            final_registry_terms: gauges.registry_terms,
            final_registry_atoms: gauges.registry_atoms,
            final_assigned_atoms: gauges.assigned_atoms,
            final_active_disequalities: gauges.active_disequalities,
            ..Self::default()
        }
    }

    /// Folds one sample into this aggregate summary.
    fn accumulate(&mut self, counters: EufCounters, gauges: EufGauges) {
        self.total_input_equalities += counters.input_equalities;
        self.total_input_disequalities += counters.input_disequalities;
        self.total_congruence_merges += counters.congruence_merges;
        self.total_theory_propagations += counters.theory_propagations;
        self.total_theory_conflicts += counters.theory_conflicts;

        self.peak_registry_terms = self.peak_registry_terms.max(gauges.registry_terms);
        self.peak_registry_atoms = self.peak_registry_atoms.max(gauges.registry_atoms);
        self.peak_pending_assignments = self
            .peak_pending_assignments
            .max(gauges.pending_assignments);
        self.peak_assigned_atoms = self.peak_assigned_atoms.max(gauges.assigned_atoms);
        self.peak_pending_merges = self.peak_pending_merges.max(gauges.pending_merges);
        self.peak_pending_repairs = self.peak_pending_repairs.max(gauges.pending_repairs);
        self.peak_pending_atom_triggers = self
            .peak_pending_atom_triggers
            .max(gauges.pending_atom_triggers);
        self.peak_pending_theory_clauses = self
            .peak_pending_theory_clauses
            .max(gauges.pending_theory_clauses);
        self.peak_active_disequalities = self
            .peak_active_disequalities
            .max(gauges.active_disequalities);
        self.peak_congruence_table_entries = self
            .peak_congruence_table_entries
            .max(gauges.congruence_table_entries);
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Counters, EufCounters, EufGauges, Gauges, Sample, SatCounters, SatGauges, Summary,
    };

    /// Ensures telemetry aggregation combines SAT and EUF counters plus gauge peaks.
    #[test]
    fn summary_aggregates_samples() {
        let samples = [
            Sample {
                elapsed_secs: 0.5,
                counters: Counters {
                    sat: SatCounters {
                        conflicts: 2,
                        propagations: 10,
                        decisions: 1,
                        restarts: 0,
                        reductions: 0,
                        learnt_clauses: 2,
                        deleted_clauses: 0,
                    },
                    euf: EufCounters {
                        input_equalities: 3,
                        input_disequalities: 1,
                        congruence_merges: 4,
                        theory_propagations: 2,
                        theory_conflicts: 0,
                    },
                },
                gauges: Gauges {
                    sat: SatGauges {
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
                    euf: EufGauges {
                        registry_terms: 11,
                        registry_atoms: 5,
                        pending_assignments: 1,
                        assigned_atoms: 3,
                        pending_merges: 2,
                        pending_repairs: 1,
                        pending_atom_triggers: 4,
                        pending_theory_clauses: 0,
                        active_disequalities: 1,
                        congruence_table_entries: 7,
                    },
                },
            },
            Sample {
                elapsed_secs: 1.0,
                counters: Counters {
                    sat: SatCounters {
                        conflicts: 5,
                        propagations: 12,
                        decisions: 3,
                        restarts: 1,
                        reductions: 1,
                        learnt_clauses: 4,
                        deleted_clauses: 2,
                    },
                    euf: EufCounters {
                        input_equalities: 2,
                        input_disequalities: 0,
                        congruence_merges: 3,
                        theory_propagations: 1,
                        theory_conflicts: 1,
                    },
                },
                gauges: Gauges {
                    sat: SatGauges {
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
                    euf: EufGauges {
                        registry_terms: 13,
                        registry_atoms: 6,
                        pending_assignments: 2,
                        assigned_atoms: 4,
                        pending_merges: 3,
                        pending_repairs: 2,
                        pending_atom_triggers: 5,
                        pending_theory_clauses: 1,
                        active_disequalities: 2,
                        congruence_table_entries: 9,
                    },
                },
            },
        ];

        let summary = Summary::from_samples(&samples).expect("summary");
        assert_eq!(summary.sample_count, 2);
        assert_eq!(summary.sat.total_conflicts, 7);
        assert_eq!(summary.sat.total_propagations, 22);
        assert_eq!(summary.sat.total_decisions, 4);
        assert_eq!(summary.sat.total_restarts, 1);
        assert_eq!(summary.sat.total_reductions, 1);
        assert_eq!(summary.sat.total_learnt_clauses, 6);
        assert_eq!(summary.sat.total_deleted_clauses, 2);
        assert_eq!(summary.sat.peak_decision_level, 5);
        assert_eq!(summary.sat.peak_assigned_vars, 11);
        assert_eq!(summary.sat.final_live_learnt_clauses, 4);
        assert_eq!(summary.euf.total_input_equalities, 5);
        assert_eq!(summary.euf.total_congruence_merges, 7);
        assert_eq!(summary.euf.total_theory_conflicts, 1);
        assert_eq!(summary.euf.peak_registry_terms, 13);
        assert_eq!(summary.euf.peak_congruence_table_entries, 9);
        assert_eq!(summary.euf.final_registry_terms, 13);
    }
}
