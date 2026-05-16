//! Telemetry implementation that records solver instrumentation.

use std::cell::{Cell, RefCell};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, Sender};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use super::{Counters, Gauges, Sample};

/// Periodic sampling request shared between the timer thread and the solver thread.
static SAMPLE_TICK: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Thread-local counter storage for the solver hot path.
    static COUNTERS: CounterCells = const { CounterCells::new() };
    /// Thread-local current-value gauges maintained incrementally on the solver thread.
    static GAUGES: GaugeCells = const { GaugeCells::new() };
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
        Self::with_period(path, super::DEFAULT_SAMPLE_PERIOD)
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

/// Records one conflict event.
#[inline(always)]
pub(crate) fn record_conflict() {
    COUNTERS.with(|counters| counters.bump(&counters.conflicts, 1));
}

/// Records one propagated assignment.
#[inline(always)]
pub(crate) fn record_propagation() {
    COUNTERS.with(|counters| counters.bump(&counters.propagations, 1));
}

/// Records one branching decision.
#[inline(always)]
pub(crate) fn record_decision() {
    COUNTERS.with(|counters| counters.bump(&counters.decisions, 1));
}

/// Records one restart.
#[inline(always)]
pub(crate) fn record_restart() {
    COUNTERS.with(|counters| counters.bump(&counters.restarts, 1));
}

/// Records one learned-database reduction.
#[inline(always)]
pub(crate) fn record_reduction() {
    COUNTERS.with(|counters| counters.bump(&counters.reductions, 1));
}

/// Records one learned clause insertion.
#[inline(always)]
pub(crate) fn record_learnt_clause() {
    COUNTERS.with(|counters| counters.bump(&counters.learnt_clauses, 1));
}

/// Records `count` deleted clauses from a learned-database reduction.
#[inline(always)]
pub(crate) fn record_deleted_clauses(count: usize) {
    COUNTERS.with(|counters| counters.bump(&counters.deleted_clauses, count as u64));
}

/// Initializes the current-value gauges for one solver run.
#[inline(always)]
pub(crate) fn initialize_solver_gauges(live_irredundant_clauses: usize, watcher_entries: usize) {
    GAUGES.with(|gauges| {
        gauges
            .live_irredundant_clauses
            .set(live_irredundant_clauses as u64);
        gauges.watcher_entries.set(watcher_entries as u64);
    });
}

/// Increments the watcher-entry gauge by `count`.
#[inline(always)]
pub(crate) fn record_added_watchers(count: usize) {
    GAUGES.with(|gauges| gauges.bump(&gauges.watcher_entries, count as u64));
}

/// Decrements the watcher-entry gauge by `count`.
#[inline(always)]
pub(crate) fn record_removed_watchers(count: usize) {
    GAUGES.with(|gauges| gauges.subtract(&gauges.watcher_entries, count as u64));
}

/// Returns the current irredundant long-clause count gauge.
#[inline(always)]
pub(crate) fn live_irredundant_clauses() -> u64 {
    GAUGES.with(|gauges| gauges.live_irredundant_clauses.get())
}

/// Returns the current watcher-entry gauge.
#[inline(always)]
pub(crate) fn watcher_entries() -> u64 {
    GAUGES.with(|gauges| gauges.watcher_entries.get())
}

/// Emits one sample when the timer thread requested a flush.
#[inline(always)]
pub(crate) fn maybe_emit_sample<F: FnOnce() -> Gauges>(gauges: F) {
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
    GAUGES.with(GaugeCells::reset);
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
    GAUGES.with(GaugeCells::reset);
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
    fn take(&self) -> Counters {
        Counters {
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

/// Thread-local gauges that reflect the solver's current structural state.
struct GaugeCells {
    /// Number of live irredundant long clauses for the current solver input.
    live_irredundant_clauses: Cell<u64>,
    /// Number of watcher entries currently present across all watch lists.
    watcher_entries: Cell<u64>,
}

impl GaugeCells {
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
        gauge.set(current.saturating_sub(amount));
    }

    /// Resets all gauges to zero.
    fn reset(&self) {
        self.live_irredundant_clauses.set(0);
        self.watcher_entries.set(0);
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
    fn write_sample(&mut self, sample: &Sample) {
        if self.write_error.is_some() {
            return;
        }

        if let Err(error) = self.try_write_sample(sample) {
            self.write_error = Some(error);
        }
    }

    /// Serializes and flushes one sample line.
    fn try_write_sample(&mut self, sample: &Sample) -> io::Result<()> {
        serde_json::to_writer(&mut self.writer, sample).map_err(io::Error::other)?;
        writeln!(self.writer)?;
        self.writer.flush()
    }
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    use super::{Gauges, TelemetryRecorder};
    use crate::telemetry::{Counters, Sample, Summary};

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

    /// Ensures finalizing telemetry does not block until the next sample period.
    #[test]
    fn finish_interrupts_timer_thread_promptly() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time before unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "sat-telemetry-finish-interrupts-{}-{unique}.jsonl",
            std::process::id()
        ));
        let recorder =
            TelemetryRecorder::with_period(&path, Duration::from_millis(300)).expect("recorder");

        // Give the timer thread time to enter its blocking wait state.
        thread::sleep(Duration::from_millis(50));

        let started = Instant::now();
        recorder.finish(Gauges::default()).expect("finish");
        let elapsed = started.elapsed();
        let _ = std::fs::remove_file(&path);

        assert!(
            elapsed < Duration::from_millis(200),
            "telemetry finalization took {elapsed:?}",
        );
    }
}
