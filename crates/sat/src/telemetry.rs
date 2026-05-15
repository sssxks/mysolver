//! Low-overhead solver telemetry backed by thread-local counters.
//!
//! The hot solver paths record only counter bumps into thread-local [`Cell`]s.
//! A background timer thread requests periodic flushes, and the solving thread
//! serializes one JSON line sample whenever it next reaches a safe checkpoint.

use std::cell::{Cell, RefCell};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

/// Default interval between periodic telemetry samples.
pub const DEFAULT_SAMPLE_PERIOD: Duration = Duration::from_secs(1);

/// Periodic sampling request shared between the timer thread and the solver thread.
static SAMPLE_TICK: AtomicBool = AtomicBool::new(false);
/// Cooperative stop flag used to shut down the timer thread.
static SAMPLE_STOP: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Thread-local counter storage for the solver hot path.
    static COUNTERS: CounterCells = const { CounterCells::new() };
    /// Per-thread telemetry session state that owns the JSONL output writer.
    static SESSION: RefCell<Option<LocalSession>> = const { RefCell::new(None) };
}

/// Counter metrics accumulated between flushed samples.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct SolverTelemetryCounters {
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
pub struct SolverTelemetryGauges {
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
pub struct SolverTelemetrySample {
    /// Seconds elapsed since the telemetry session started.
    pub elapsed_secs: f64,
    /// Counter deltas accumulated since the previous sample.
    pub counters: SolverTelemetryCounters,
    /// Point-in-time gauges captured at the sample boundary.
    pub gauges: SolverTelemetryGauges,
}

/// Aggregate telemetry derived from one case's emitted samples.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct SolverTelemetrySummary {
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

impl SolverTelemetrySummary {
    /// Aggregates one full sample stream into one compact summary.
    pub fn from_samples(samples: &[SolverTelemetrySample]) -> Option<Self> {
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

/// A guard that owns one telemetry JSONL writer and its timer thread.
#[derive(Debug)]
pub struct TelemetryRecorder {
    /// Background timer thread that requests periodic flushes.
    timer_thread: Option<JoinHandle<()>>,
}

impl TelemetryRecorder {
    /// Starts writing JSONL telemetry samples to `path`.
    pub fn start(path: &Path) -> io::Result<Self> {
        Self::with_period(path, DEFAULT_SAMPLE_PERIOD)
    }

    /// Starts writing JSONL telemetry samples to `path` using a custom period.
    pub fn with_period(path: &Path, period: Duration) -> io::Result<Self> {
        install_session(path)?;
        SAMPLE_STOP.store(false, Ordering::Relaxed);
        SAMPLE_TICK.store(false, Ordering::Relaxed);

        let timer_thread = thread::spawn(move || {
            while !SAMPLE_STOP.load(Ordering::Relaxed) {
                thread::sleep(period);
                if SAMPLE_STOP.load(Ordering::Relaxed) {
                    break;
                }
                SAMPLE_TICK.store(true, Ordering::Relaxed);
            }
        });

        Ok(Self {
            timer_thread: Some(timer_thread),
        })
    }

    /// Emits the final sample, stops the timer thread, and returns any write error.
    pub fn finish(mut self, gauges: SolverTelemetryGauges) -> io::Result<()> {
        emit_sample(gauges);
        self.shutdown();
        take_session_result()
    }

    /// Stops the timer thread without emitting any additional sample.
    fn shutdown(&mut self) {
        SAMPLE_STOP.store(true, Ordering::Relaxed);
        SAMPLE_TICK.store(false, Ordering::Relaxed);
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

/// Records one conflict event.
pub(crate) fn record_conflict() {
    COUNTERS.with(|counters| counters.bump(&counters.conflicts, 1));
}

/// Records one propagated assignment.
pub(crate) fn record_propagation() {
    COUNTERS.with(|counters| counters.bump(&counters.propagations, 1));
}

/// Records one branching decision.
pub(crate) fn record_decision() {
    COUNTERS.with(|counters| counters.bump(&counters.decisions, 1));
}

/// Records one restart.
pub(crate) fn record_restart() {
    COUNTERS.with(|counters| counters.bump(&counters.restarts, 1));
}

/// Records one learned-database reduction.
pub(crate) fn record_reduction() {
    COUNTERS.with(|counters| counters.bump(&counters.reductions, 1));
}

/// Records one learned clause insertion.
pub(crate) fn record_learnt_clause() {
    COUNTERS.with(|counters| counters.bump(&counters.learnt_clauses, 1));
}

/// Records `count` deleted clauses from a learned-database reduction.
pub(crate) fn record_deleted_clauses(count: usize) {
    COUNTERS.with(|counters| counters.bump(&counters.deleted_clauses, count as u64));
}

/// Emits one sample when the timer thread requested a flush.
pub(crate) fn maybe_emit_sample(gauges: SolverTelemetryGauges) {
    if !SAMPLE_TICK.swap(false, Ordering::Relaxed) {
        return;
    }

    emit_sample(gauges);
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
    Ok(())
}

/// Emits one JSONL sample to the active session, if any.
fn emit_sample(gauges: SolverTelemetryGauges) {
    let counters = COUNTERS.with(CounterCells::take);
    SESSION.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(session) = slot.as_mut() else {
            return;
        };
        let sample = SolverTelemetrySample {
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
}

/// Thread-local counter cells used by the solver hot path.
struct CounterCells {
    /// Conflict counter delta.
    conflicts: Cell<u64>,
    /// Propagation counter delta.
    propagations: Cell<u64>,
    /// Decision counter delta.
    decisions: Cell<u64>,
    /// Restart counter delta.
    restarts: Cell<u64>,
    /// Reduction counter delta.
    reductions: Cell<u64>,
    /// Learned-clause counter delta.
    learnt_clauses: Cell<u64>,
    /// Deleted-clause counter delta.
    deleted_clauses: Cell<u64>,
}

impl CounterCells {
    /// Creates one zeroed counter bundle.
    const fn new() -> Self {
        Self {
            conflicts: Cell::new(0),
            propagations: Cell::new(0),
            decisions: Cell::new(0),
            restarts: Cell::new(0),
            reductions: Cell::new(0),
            learnt_clauses: Cell::new(0),
            deleted_clauses: Cell::new(0),
        }
    }

    /// Increments one counter by `amount`.
    fn bump(&self, counter: &Cell<u64>, amount: u64) {
        counter.set(counter.get() + amount);
    }

    /// Resets all counters to zero.
    fn reset(&self) {
        self.conflicts.set(0);
        self.propagations.set(0);
        self.decisions.set(0);
        self.restarts.set(0);
        self.reductions.set(0);
        self.learnt_clauses.set(0);
        self.deleted_clauses.set(0);
    }

    /// Takes the current counter deltas and resets them to zero.
    fn take(&self) -> SolverTelemetryCounters {
        SolverTelemetryCounters {
            conflicts: self.conflicts.replace(0),
            propagations: self.propagations.replace(0),
            decisions: self.decisions.replace(0),
            restarts: self.restarts.replace(0),
            reductions: self.reductions.replace(0),
            learnt_clauses: self.learnt_clauses.replace(0),
            deleted_clauses: self.deleted_clauses.replace(0),
        }
    }
}

/// Per-thread telemetry state that owns the JSONL writer.
struct LocalSession {
    /// Session start instant used to compute elapsed seconds.
    started: Instant,
    /// Buffered writer for the telemetry JSONL file.
    writer: BufWriter<File>,
    /// First write error observed while emitting samples.
    write_error: Option<io::Error>,
}

impl LocalSession {
    /// Creates one writer-backed local session.
    fn new(file: File) -> Self {
        Self {
            started: Instant::now(),
            writer: BufWriter::new(file),
            write_error: None,
        }
    }

    /// Writes one sample unless a previous write error already occurred.
    fn write_sample(&mut self, sample: &SolverTelemetrySample) {
        if self.write_error.is_some() {
            return;
        }

        if let Err(error) = self.try_write_sample(sample) {
            self.write_error = Some(error);
        }
    }

    /// Serializes and flushes one sample line.
    fn try_write_sample(&mut self, sample: &SolverTelemetrySample) -> io::Result<()> {
        serde_json::to_writer(&mut self.writer, sample).map_err(io::Error::other)?;
        writeln!(self.writer)?;
        self.writer.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        SolverTelemetryCounters, SolverTelemetryGauges, SolverTelemetrySample,
        SolverTelemetrySummary,
    };

    /// Ensures telemetry aggregation combines counter totals and gauge peaks.
    #[test]
    fn summary_aggregates_samples() {
        let samples = [
            SolverTelemetrySample {
                elapsed_secs: 0.5,
                counters: SolverTelemetryCounters {
                    conflicts: 2,
                    propagations: 10,
                    decisions: 1,
                    restarts: 0,
                    reductions: 0,
                    learnt_clauses: 2,
                    deleted_clauses: 0,
                },
                gauges: SolverTelemetryGauges {
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
            SolverTelemetrySample {
                elapsed_secs: 1.0,
                counters: SolverTelemetryCounters {
                    conflicts: 5,
                    propagations: 12,
                    decisions: 3,
                    restarts: 1,
                    reductions: 1,
                    learnt_clauses: 4,
                    deleted_clauses: 2,
                },
                gauges: SolverTelemetryGauges {
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

        let summary = SolverTelemetrySummary::from_samples(&samples).expect("summary");
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
