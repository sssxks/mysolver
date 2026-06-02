use std::cell::{Cell, RefCell};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, Sender};
use std::thread::{self, JoinHandle};
use std::time::Instant;

use crate::{Counters, DEFAULT_SAMPLE_PERIOD, EufCounters, Gauges, SatCounters};

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

    /// Starts writing JSONL telemetry samples to `path` using a custom period.
    pub fn with_period(path: &Path, period: std::time::Duration) -> io::Result<Self> {
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

/// Returns the current SAT irredundant-clause gauge.
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

/// Accepts a published gauge snapshot for API compatibility with the atomic backend.
#[inline(always)]
pub fn publish_gauges(_gauges: Gauges) {}

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
        let sample = crate::Sample {
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
    fn write_sample(&mut self, sample: &crate::Sample) {
        if self.write_error.is_some() {
            return;
        }
        if let Err(error) = serde_json::to_writer(&mut self.writer, sample) {
            self.write_error = Some(io::Error::other(error));
            return;
        }
        if let Err(error) = self.writer.write_all(b"\n") {
            self.write_error = Some(error);
            return;
        }
        if let Err(error) = self.writer.flush() {
            self.write_error = Some(error);
        }
    }
}
