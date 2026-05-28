//! Low-overhead telemetry for one full `qfuf` solve session.
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
//! SAT and EUF hot paths update thread-local counters. Periodic sample requests
//! are issued by a timer thread and fulfilled cooperatively by the solving
//! thread at safe checkpoints.

use std::cell::{Cell, RefCell};
use std::env;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, Sender};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

/// Environment variable used by `qfuf` to discover the telemetry JSONL path.
pub const PATH_ENV_VAR: &str = "MYSOLVER_QFUF_TELEMETRY_PATH";
/// Default interval between periodic telemetry samples.
pub const DEFAULT_SAMPLE_PERIOD: Duration = Duration::from_secs(1);

/// Counter metrics accumulated between flushed samples.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Counters {
    /// SAT-local counter deltas.
    pub sat: SatCounters,
    /// EUF-local counter deltas.
    pub euf: EufCounters,
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
    pub elapsed_secs: f64,
    /// Counter deltas accumulated since the previous sample.
    pub counters: Counters,
    /// Point-in-time gauges captured at the sample boundary.
    pub gauges: Gauges,
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
    pub input_equalities: u64,
    /// Number of asserted input disequalities processed since the previous sample.
    pub input_disequalities: u64,
    /// Number of congruence-driven merges performed since the previous sample.
    pub congruence_merges: u64,
    /// Number of theory propagation clauses emitted since the previous sample.
    pub theory_propagations: u64,
    /// Number of theory conflict clauses emitted since the previous sample.
    pub theory_conflicts: u64,
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
    /// Number of directed proof edges in the explanation graph.
    pub proof_edges: u64,
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
        self.peak_proof_edges = self.peak_proof_edges.max(gauges.proof_edges);
    }
}

/// Periodic sampling request shared between the timer thread and the solver thread.
static SAMPLE_TICK: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Thread-local counter storage for SAT and EUF hot paths.
    static COUNTERS: CounterCells = const { CounterCells::new() };
    /// Thread-local current-value SAT gauges maintained incrementally on the solver thread.
    static SAT_GAUGES: SatGaugeCells = const { SatGaugeCells::new() };
    /// Per-thread telemetry session state that owns the JSONL output writer.
    static SESSION: RefCell<Option<LocalSession>> = const { RefCell::new(None) };
}

/// A guard that owns one telemetry JSONL writer and its timer thread.
#[derive(Debug)]
pub struct TelemetryRecorder {
    /// Cooperative stop signal used to interrupt the timer thread immediately.
    stop_sender: Option<Sender<()>>,
    /// Background timer thread that requests periodic flushes.
    timer_thread: Option<JoinHandle<()>>,
}

impl TelemetryRecorder {
    /// Starts writing JSONL telemetry samples to `path`.
    pub fn start(path: &Path) -> io::Result<Self> {
        Self::with_period(path, DEFAULT_SAMPLE_PERIOD)
    }

    /// Starts writing JSONL telemetry samples to the path named by [`PATH_ENV_VAR`].
    pub fn start_from_env() -> io::Result<Option<Self>> {
        let Some(path) = env::var_os(PATH_ENV_VAR) else {
            return Ok(None);
        };
        let path = PathBuf::from(path);
        Self::start(&path).map(Some)
    }

    /// Starts writing JSONL telemetry samples to `path` using a custom period.
    pub fn with_period(path: &Path, period: Duration) -> io::Result<Self> {
        install_session(path)?;
        SAMPLE_TICK.store(false, Ordering::Relaxed);
        let (stop_sender, stop_receiver) = mpsc::channel();

        let timer_thread = thread::spawn(move || {
            loop {
                match stop_receiver.recv_timeout(period) {
                    Ok(()) | Err(RecvTimeoutError::Disconnected) => break,
                    Err(RecvTimeoutError::Timeout) => {
                        SAMPLE_TICK.store(true, Ordering::Relaxed);
                    }
                }
            }
        });

        Ok(Self {
            stop_sender: Some(stop_sender),
            timer_thread: Some(timer_thread),
        })
    }

    /// Emits the final sample, stops the timer thread, and returns any write error.
    pub fn finish(mut self, gauges: Gauges) -> io::Result<()> {
        emit_sample(gauges);
        self.shutdown();
        take_session_result()
    }

    /// Stops the timer thread without emitting any additional sample.
    fn shutdown(&mut self) {
        SAMPLE_TICK.store(false, Ordering::Relaxed);
        if let Some(sender) = self.stop_sender.take() {
            let _ = sender.send(());
        }
        if let Some(handle) = self.timer_thread.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for TelemetryRecorder {
    fn drop(&mut self) {
        self.shutdown();
        clear_session();
    }
}

/// Records one SAT conflict event.
#[inline(always)]
pub fn record_sat_conflict() {
    COUNTERS.with(|counters| counters.bump(&counters.sat_conflicts, 1));
}

/// Records one SAT propagated assignment.
#[inline(always)]
pub fn record_sat_propagation() {
    COUNTERS.with(|counters| counters.bump(&counters.sat_propagations, 1));
}

/// Records one SAT branching decision.
#[inline(always)]
pub fn record_sat_decision() {
    COUNTERS.with(|counters| counters.bump(&counters.sat_decisions, 1));
}

/// Records one SAT restart.
#[inline(always)]
pub fn record_sat_restart() {
    COUNTERS.with(|counters| counters.bump(&counters.sat_restarts, 1));
}

/// Records one SAT learned-database reduction.
#[inline(always)]
pub fn record_sat_reduction() {
    COUNTERS.with(|counters| counters.bump(&counters.sat_reductions, 1));
}

/// Records one SAT learned clause insertion.
#[inline(always)]
pub fn record_sat_learnt_clause() {
    COUNTERS.with(|counters| counters.bump(&counters.sat_learnt_clauses, 1));
}

/// Records `count` SAT clause deletions from a learned-database reduction.
#[inline(always)]
pub fn record_sat_deleted_clauses(count: usize) {
    COUNTERS.with(|counters| counters.bump(&counters.sat_deleted_clauses, count as u64));
}

/// Initializes the SAT current-value gauges for one solver run.
#[inline(always)]
pub fn initialize_sat_solver_gauges(live_irredundant_clauses: usize, watcher_entries: usize) {
    SAT_GAUGES.with(|gauges| {
        gauges
            .live_irredundant_clauses
            .set(live_irredundant_clauses as u64);
        gauges.watcher_entries.set(watcher_entries as u64);
    });
}

/// Increments the SAT watcher-entry gauge by `count`.
#[inline(always)]
pub fn record_sat_added_watchers(count: usize) {
    SAT_GAUGES.with(|gauges| gauges.bump(&gauges.watcher_entries, count as u64));
}

/// Decrements the SAT watcher-entry gauge by `count`.
#[inline(always)]
pub fn record_sat_removed_watchers(count: usize) {
    SAT_GAUGES.with(|gauges| gauges.subtract(&gauges.watcher_entries, count as u64));
}

/// Returns the current SAT irredundant long-clause count gauge.
#[inline(always)]
pub fn sat_live_irredundant_clauses() -> u64 {
    SAT_GAUGES.with(|gauges| gauges.live_irredundant_clauses.get())
}

/// Returns the current SAT watcher-entry gauge.
#[inline(always)]
pub fn sat_watcher_entries() -> u64 {
    SAT_GAUGES.with(|gauges| gauges.watcher_entries.get())
}

/// Records one EUF input equality assignment.
#[inline(always)]
pub fn record_euf_input_equality() {
    COUNTERS.with(|counters| counters.bump(&counters.euf_input_equalities, 1));
}

/// Records one EUF input disequality assignment.
#[inline(always)]
pub fn record_euf_input_disequality() {
    COUNTERS.with(|counters| counters.bump(&counters.euf_input_disequalities, 1));
}

/// Records one congruence-driven EUF merge.
#[inline(always)]
pub fn record_euf_congruence_merge() {
    COUNTERS.with(|counters| counters.bump(&counters.euf_congruence_merges, 1));
}

/// Records one EUF theory propagation clause.
#[inline(always)]
pub fn record_euf_theory_propagation() {
    COUNTERS.with(|counters| counters.bump(&counters.euf_theory_propagations, 1));
}

/// Records one EUF theory conflict clause.
#[inline(always)]
pub fn record_euf_theory_conflict() {
    COUNTERS.with(|counters| counters.bump(&counters.euf_theory_conflicts, 1));
}

/// Emits one sample when the timer thread requested a flush.
#[inline(always)]
pub fn maybe_emit_sample<F: FnOnce() -> Gauges>(gauges: F) {
    if SAMPLE_TICK
        .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
        .is_ok()
    {
        emit_sample(gauges());
    }
}

/// Installs the per-thread session writer and resets all thread-local counters.
fn install_session(path: &Path) -> io::Result<()> {
    let file = File::create(path)?;
    SESSION.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "telemetry recorder already installed on this thread",
            ));
        }

        *slot = Some(LocalSession::new(file));
        Ok(())
    })?;
    COUNTERS.with(CounterCells::reset);
    SAT_GAUGES.with(SatGaugeCells::reset);
    Ok(())
}

/// Emits one JSONL sample to the active session, if any.
fn emit_sample(gauges: Gauges) {
    let counters = COUNTERS.with(CounterCells::take);
    SESSION.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(session) = slot.as_mut() else {
            return;
        };
        let sample = Sample {
            elapsed_secs: session.started.elapsed().as_secs_f64(),
            counters,
            gauges,
        };
        session.write_sample(&sample);
    });
}

/// Removes the active per-thread session and returns its terminal write status.
fn take_session_result() -> io::Result<()> {
    SESSION.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(mut session) = slot.take() else {
            return Ok(());
        };
        session.writer.flush()?;
        match session.write_error.take() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    })
}

/// Removes the active per-thread session, discarding any stored error.
fn clear_session() {
    SESSION.with(|slot| {
        let _ = slot.borrow_mut().take();
    });
    COUNTERS.with(CounterCells::reset);
    SAT_GAUGES.with(SatGaugeCells::reset);
}

/// Thread-local counter cells used by the SAT and EUF hot paths.
struct CounterCells {
    /// SAT conflict counter delta.
    sat_conflicts: Cell<u64>,
    /// SAT propagation counter delta.
    sat_propagations: Cell<u64>,
    /// SAT decision counter delta.
    sat_decisions: Cell<u64>,
    /// SAT restart counter delta.
    sat_restarts: Cell<u64>,
    /// SAT reduction counter delta.
    sat_reductions: Cell<u64>,
    /// SAT learned-clause counter delta.
    sat_learnt_clauses: Cell<u64>,
    /// SAT deleted-clause counter delta.
    sat_deleted_clauses: Cell<u64>,
    /// EUF input-equality counter delta.
    euf_input_equalities: Cell<u64>,
    /// EUF input-disequality counter delta.
    euf_input_disequalities: Cell<u64>,
    /// EUF congruence-merge counter delta.
    euf_congruence_merges: Cell<u64>,
    /// EUF theory-propagation counter delta.
    euf_theory_propagations: Cell<u64>,
    /// EUF theory-conflict counter delta.
    euf_theory_conflicts: Cell<u64>,
}

impl CounterCells {
    /// Creates one zeroed counter bundle.
    const fn new() -> Self {
        Self {
            sat_conflicts: Cell::new(0),
            sat_propagations: Cell::new(0),
            sat_decisions: Cell::new(0),
            sat_restarts: Cell::new(0),
            sat_reductions: Cell::new(0),
            sat_learnt_clauses: Cell::new(0),
            sat_deleted_clauses: Cell::new(0),
            euf_input_equalities: Cell::new(0),
            euf_input_disequalities: Cell::new(0),
            euf_congruence_merges: Cell::new(0),
            euf_theory_propagations: Cell::new(0),
            euf_theory_conflicts: Cell::new(0),
        }
    }

    /// Increments one counter by `amount`.
    fn bump(&self, counter: &Cell<u64>, amount: u64) {
        counter.set(counter.get() + amount);
    }

    /// Resets all counters to zero.
    fn reset(&self) {
        self.sat_conflicts.set(0);
        self.sat_propagations.set(0);
        self.sat_decisions.set(0);
        self.sat_restarts.set(0);
        self.sat_reductions.set(0);
        self.sat_learnt_clauses.set(0);
        self.sat_deleted_clauses.set(0);
        self.euf_input_equalities.set(0);
        self.euf_input_disequalities.set(0);
        self.euf_congruence_merges.set(0);
        self.euf_theory_propagations.set(0);
        self.euf_theory_conflicts.set(0);
    }

    /// Takes the current counter deltas and resets them to zero.
    fn take(&self) -> Counters {
        Counters {
            sat: SatCounters {
                conflicts: self.sat_conflicts.replace(0),
                propagations: self.sat_propagations.replace(0),
                decisions: self.sat_decisions.replace(0),
                restarts: self.sat_restarts.replace(0),
                reductions: self.sat_reductions.replace(0),
                learnt_clauses: self.sat_learnt_clauses.replace(0),
                deleted_clauses: self.sat_deleted_clauses.replace(0),
            },
            euf: EufCounters {
                input_equalities: self.euf_input_equalities.replace(0),
                input_disequalities: self.euf_input_disequalities.replace(0),
                congruence_merges: self.euf_congruence_merges.replace(0),
                theory_propagations: self.euf_theory_propagations.replace(0),
                theory_conflicts: self.euf_theory_conflicts.replace(0),
            },
        }
    }
}

/// Thread-local SAT gauges that reflect current structural state.
struct SatGaugeCells {
    /// Number of live irredundant long clauses for the current solver input.
    live_irredundant_clauses: Cell<u64>,
    /// Number of watcher entries currently present across all watch lists.
    watcher_entries: Cell<u64>,
}

impl SatGaugeCells {
    /// Creates one zeroed gauge bundle.
    const fn new() -> Self {
        Self {
            live_irredundant_clauses: Cell::new(0),
            watcher_entries: Cell::new(0),
        }
    }

    /// Increments one gauge by `amount`.
    fn bump(&self, gauge: &Cell<u64>, amount: u64) {
        gauge.set(gauge.get() + amount);
    }

    /// Decrements one gauge by `amount`.
    fn subtract(&self, gauge: &Cell<u64>, amount: u64) {
        let current = gauge.get();
        debug_assert!(current >= amount, "telemetry gauge underflow");
        gauge.set(current - amount);
    }

    /// Resets all gauges to zero.
    fn reset(&self) {
        self.live_irredundant_clauses.set(0);
        self.watcher_entries.set(0);
    }
}

/// Per-thread telemetry state that owns the JSONL writer.
struct LocalSession {
    /// Time at which sampling started.
    started: Instant,
    /// Buffered writer for the telemetry JSONL file.
    writer: BufWriter<File>,
    /// The first persistent write error observed while emitting samples.
    write_error: Option<io::Error>,
}

impl LocalSession {
    /// Creates one fresh local session around `file`.
    fn new(file: File) -> Self {
        Self {
            started: Instant::now(),
            writer: BufWriter::new(file),
            write_error: None,
        }
    }

    /// Attempts to append one JSONL sample, remembering only the first error.
    fn write_sample(&mut self, sample: &Sample) {
        if self.write_error.is_some() {
            return;
        }
        if let Err(error) = serde_json::to_writer(&mut self.writer, sample) {
            self.write_error = Some(io::Error::other(error));
            return;
        }
        if let Err(error) = self.writer.write_all(b"\n") {
            self.write_error = Some(error);
        }
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
                        proof_edges: 6,
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
                        pending_assignments: 0,
                        assigned_atoms: 4,
                        pending_merges: 1,
                        pending_repairs: 2,
                        pending_atom_triggers: 3,
                        pending_theory_clauses: 1,
                        active_disequalities: 2,
                        congruence_table_entries: 8,
                        proof_edges: 10,
                    },
                },
            },
        ];

        let summary = Summary::from_samples(&samples).expect("summary");
        assert_eq!(summary.sample_count, 2);
        assert_eq!(summary.sat.total_conflicts, 7);
        assert_eq!(summary.sat.total_propagations, 22);
        assert_eq!(summary.sat.total_decisions, 4);
        assert_eq!(summary.sat.peak_decision_level, 5);
        assert_eq!(summary.sat.final_live_learnt_clauses, 4);
        assert_eq!(summary.euf.total_input_equalities, 5);
        assert_eq!(summary.euf.total_congruence_merges, 7);
        assert_eq!(summary.euf.total_theory_conflicts, 1);
        assert_eq!(summary.euf.peak_registry_terms, 13);
        assert_eq!(summary.euf.peak_pending_atom_triggers, 4);
        assert_eq!(summary.euf.final_active_disequalities, 2);
    }
}
