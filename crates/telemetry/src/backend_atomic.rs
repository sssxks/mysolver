use std::cell::{Cell, RefCell};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, Sender};
use std::thread::{self, JoinHandle};
use std::time::Instant;

use crate::{
    Counters, DEFAULT_SAMPLE_PERIOD, EufCounters, EufGauges, Gauges, Sample, SatCounters, SatGauges,
};

thread_local! {
    /// The active telemetry session for the current solver thread, when any.
    static SESSION: RefCell<Option<Arc<SessionCore>>> = const { RefCell::new(None) };
    /// Thread-local current-value SAT gauges mirrored for solver-local reads and tests.
    static SAT_GAUGES: SatGaugeCells = const { SatGaugeCells::new() };
}

/// A guard that owns one telemetry JSONL writer and its timer thread.
#[derive(Debug)]
pub struct TelemetryRecorder {
    /// Control channel used to stop the timer thread or request the final sample.
    control_sender: Option<Sender<TimerCommand>>,
    /// Background timer thread that snapshots atomics into the JSONL stream.
    timer_thread: Option<JoinHandle<io::Result<()>>>,
}

impl TelemetryRecorder {
    /// Starts writing JSONL telemetry samples to `path`.
    pub fn start(path: &Path) -> io::Result<Self> {
        Self::with_period(path, DEFAULT_SAMPLE_PERIOD)
    }

    /// Starts writing JSONL telemetry samples to `path` using a custom period.
    pub fn with_period(path: &Path, period: std::time::Duration) -> io::Result<Self> {
        let writer = BufWriter::new(File::create(path)?);
        let core = Arc::new(SessionCore::default());
        install_session(Arc::clone(&core))?;
        let (control_sender, control_receiver) = mpsc::channel();

        let timer_thread =
            thread::spawn(move || run_timer_thread(core, writer, period, control_receiver));

        Ok(Self {
            control_sender: Some(control_sender),
            timer_thread: Some(timer_thread),
        })
    }

    /// Emits the final sample, stops the timer thread, and returns any write error.
    pub fn finish(mut self, gauges: Gauges) -> io::Result<()> {
        if let Some(sender) = self.control_sender.take() {
            let _ = sender.send(TimerCommand::Finish { gauges });
        }
        let result = join_timer_thread(self.timer_thread.take());
        clear_session();
        result
    }
}

impl Drop for TelemetryRecorder {
    fn drop(&mut self) {
        if let Some(sender) = self.control_sender.take() {
            let _ = sender.send(TimerCommand::Stop);
        }
        let _ = join_timer_thread(self.timer_thread.take());
        clear_session();
    }
}

/// Records one SAT conflict event.
#[inline(always)]
pub fn record_sat_conflict() {
    with_active_session(|core| {
        core.counters.sat.conflicts.fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one SAT propagated assignment.
#[inline(always)]
pub fn record_sat_propagation() {
    with_active_session(|core| {
        core.counters
            .sat
            .propagations
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one SAT branching decision.
#[inline(always)]
pub fn record_sat_decision() {
    with_active_session(|core| {
        core.counters.sat.decisions.fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one SAT restart.
#[inline(always)]
pub fn record_sat_restart() {
    with_active_session(|core| {
        core.counters.sat.restarts.fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one SAT learned-database reduction.
#[inline(always)]
pub fn record_sat_reduction() {
    with_active_session(|core| {
        core.counters.sat.reductions.fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one SAT learned clause insertion.
#[inline(always)]
pub fn record_sat_learnt_clause() {
    with_active_session(|core| {
        core.counters
            .sat
            .learnt_clauses
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Records `count` SAT clause deletions from a learned-database reduction.
#[inline(always)]
pub fn record_sat_deleted_clauses(count: usize) {
    with_active_session(|core| {
        core.counters
            .sat
            .deleted_clauses
            .fetch_add(count as u64, Ordering::Relaxed);
    });
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
    with_active_session(|core| {
        core.gauges
            .sat
            .live_irredundant_clauses
            .store(live_irredundant_clauses as u64, Ordering::Relaxed);
        core.gauges
            .sat
            .watcher_entries
            .store(watcher_entries as u64, Ordering::Relaxed);
    });
}

/// Increments the SAT watcher-entry gauge by `count`.
#[inline(always)]
pub fn record_sat_added_watchers(count: usize) {
    SAT_GAUGES.with(|gauges| gauges.bump(&gauges.watcher_entries, count as u64));
    with_active_session(|core| {
        core.gauges
            .sat
            .watcher_entries
            .fetch_add(count as u64, Ordering::Relaxed);
    });
}

/// Decrements the SAT watcher-entry gauge by `count`.
#[inline(always)]
pub fn record_sat_removed_watchers(count: usize) {
    SAT_GAUGES.with(|gauges| gauges.subtract(&gauges.watcher_entries, count as u64));
    with_active_session(|core| {
        core.gauges
            .sat
            .watcher_entries
            .fetch_sub(count as u64, Ordering::Relaxed);
    });
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
    with_active_session(|core| {
        core.counters
            .euf
            .input_equalities
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one EUF input disequality assignment.
#[inline(always)]
pub fn record_euf_input_disequality() {
    with_active_session(|core| {
        core.counters
            .euf
            .input_disequalities
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one congruence-driven EUF merge.
#[inline(always)]
pub fn record_euf_congruence_merge() {
    with_active_session(|core| {
        core.counters
            .euf
            .congruence_merges
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one EUF theory propagation clause.
#[inline(always)]
pub fn record_euf_theory_propagation() {
    with_active_session(|core| {
        core.counters
            .euf
            .theory_propagations
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Records one EUF theory conflict clause.
#[inline(always)]
pub fn record_euf_theory_conflict() {
    with_active_session(|core| {
        core.counters
            .euf
            .theory_conflicts
            .fetch_add(1, Ordering::Relaxed);
    });
}

/// Publishes one fresh gauge snapshot when the timer thread requested a refresh.
#[inline(always)]
pub fn maybe_emit_sample<F: FnOnce() -> Gauges>(gauges: F) {
    with_active_session(|core| {
        if core
            .gauge_refresh_requested
            .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            core.publish_gauges(gauges());
        }
    });
}

/// Publishes one gauge snapshot unconditionally for future timer-thread samples.
#[inline(always)]
pub fn publish_gauges(gauges: Gauges) {
    with_active_session(|core| core.publish_gauges(gauges));
}

/// Installs the active session for the solver thread.
fn install_session(core: Arc<SessionCore>) -> io::Result<()> {
    SESSION.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "telemetry recorder already installed on this thread",
            ));
        }
        *slot = Some(core);
        Ok(())
    })?;
    SAT_GAUGES.with(SatGaugeCells::reset);
    Ok(())
}

/// Runs the periodic writer loop on the timer thread.
fn run_timer_thread(
    core: Arc<SessionCore>,
    writer: BufWriter<File>,
    period: std::time::Duration,
    control_receiver: mpsc::Receiver<TimerCommand>,
) -> io::Result<()> {
    let mut session = LocalSession::new(writer);
    let mut previous_counters = Counters::default();

    loop {
        match control_receiver.recv_timeout(period) {
            Ok(TimerCommand::Finish { gauges }) => {
                core.publish_gauges(gauges);
                session.write_sample(core.snapshot_sample(&mut previous_counters));
                return session.finish();
            }
            Ok(TimerCommand::Stop) | Err(RecvTimeoutError::Disconnected) => {
                return session.finish();
            }
            Err(RecvTimeoutError::Timeout) => {
                core.gauge_refresh_requested.store(true, Ordering::Relaxed);
                session.write_sample(core.snapshot_sample(&mut previous_counters));
            }
        }
    }
}

/// Waits for the timer thread to terminate and converts thread panics into I/O errors.
fn join_timer_thread(handle: Option<JoinHandle<io::Result<()>>>) -> io::Result<()> {
    let Some(handle) = handle else {
        return Ok(());
    };
    match handle.join() {
        Ok(result) => result,
        Err(_) => Err(io::Error::other("telemetry timer thread panicked")),
    }
}

/// Removes the active per-thread session.
fn clear_session() {
    SESSION.with(|slot| {
        let _ = slot.borrow_mut().take();
    });
    SAT_GAUGES.with(SatGaugeCells::reset);
}

/// Executes one closure with the active session, if telemetry is currently enabled.
#[inline(always)]
fn with_active_session(f: impl FnOnce(&SessionCore)) {
    SESSION.with(|slot| {
        let slot = slot.borrow();
        let Some(core) = slot.as_ref() else {
            return;
        };
        f(core);
    });
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

/// One control command sent from the solver thread to the timer thread.
#[allow(clippy::missing_docs_in_private_items)]
enum TimerCommand {
    /// Publish these final gauges, emit one closing sample, then stop.
    Finish { gauges: Gauges },
    /// Stop without emitting any additional sample.
    Stop,
}

/// Atomically readable telemetry state shared between the solver and timer threads.
#[derive(Default)]
struct SessionCore {
    /// Cumulative SAT and EUF counters.
    counters: AtomicCounters,
    /// The latest published gauge snapshot.
    gauges: AtomicGauges,
    /// Whether the next safe solver checkpoint should refresh gauges.
    gauge_refresh_requested: AtomicBool,
}

impl SessionCore {
    /// Stores one full gauge snapshot for future timer-thread samples.
    fn publish_gauges(&self, gauges: Gauges) {
        self.gauges.store(gauges);
    }

    /// Loads one full sample and advances the caller's counter baseline.
    fn snapshot_sample(&self, previous_counters: &mut Counters) -> Sample {
        let current_counters = self.counters.load();
        let sample = Sample {
            elapsed_secs: 0.0,
            counters: subtract_counters(current_counters, *previous_counters),
            gauges: self.gauges.load(),
        };
        *previous_counters = current_counters;
        sample
    }
}

/// Cumulative SAT and EUF counters stored atomically.
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Default)]
struct AtomicCounters {
    sat: AtomicSatCounters,
    euf: AtomicEufCounters,
}

impl AtomicCounters {
    /// Loads one self-consistent cumulative counter snapshot.
    fn load(&self) -> Counters {
        Counters {
            sat: SatCounters {
                conflicts: self.sat.conflicts.load(Ordering::Relaxed),
                propagations: self.sat.propagations.load(Ordering::Relaxed),
                decisions: self.sat.decisions.load(Ordering::Relaxed),
                restarts: self.sat.restarts.load(Ordering::Relaxed),
                reductions: self.sat.reductions.load(Ordering::Relaxed),
                learnt_clauses: self.sat.learnt_clauses.load(Ordering::Relaxed),
                deleted_clauses: self.sat.deleted_clauses.load(Ordering::Relaxed),
            },
            euf: EufCounters {
                input_equalities: self.euf.input_equalities.load(Ordering::Relaxed),
                input_disequalities: self.euf.input_disequalities.load(Ordering::Relaxed),
                congruence_merges: self.euf.congruence_merges.load(Ordering::Relaxed),
                theory_propagations: self.euf.theory_propagations.load(Ordering::Relaxed),
                theory_conflicts: self.euf.theory_conflicts.load(Ordering::Relaxed),
            },
        }
    }
}

/// Atomically readable SAT cumulative counters.
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Default)]
struct AtomicSatCounters {
    conflicts: AtomicU64,
    propagations: AtomicU64,
    decisions: AtomicU64,
    restarts: AtomicU64,
    reductions: AtomicU64,
    learnt_clauses: AtomicU64,
    deleted_clauses: AtomicU64,
}

/// Atomically readable EUF cumulative counters.
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Default)]
struct AtomicEufCounters {
    input_equalities: AtomicU64,
    input_disequalities: AtomicU64,
    congruence_merges: AtomicU64,
    theory_propagations: AtomicU64,
    theory_conflicts: AtomicU64,
}

/// Atomically readable SAT and EUF gauges.
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Default)]
struct AtomicGauges {
    sat: AtomicSatGauges,
    euf: AtomicEufGauges,
}

impl AtomicGauges {
    /// Stores one full gauge snapshot.
    fn store(&self, gauges: Gauges) {
        self.sat.store(gauges.sat);
        self.euf.store(gauges.euf);
    }

    /// Loads one full gauge snapshot.
    fn load(&self) -> Gauges {
        Gauges {
            sat: self.sat.load(),
            euf: self.euf.load(),
        }
    }
}

/// Atomically readable SAT gauges.
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Default)]
struct AtomicSatGauges {
    decision_level: AtomicU64,
    assigned_vars: AtomicU64,
    trail_len: AtomicU64,
    pending_propagations: AtomicU64,
    live_irredundant_clauses: AtomicU64,
    live_learnt_clauses: AtomicU64,
    watcher_entries: AtomicU64,
    clause_words: AtomicU64,
    wasted_clause_words: AtomicU64,
}

impl AtomicSatGauges {
    /// Stores one SAT gauge snapshot.
    fn store(&self, gauges: SatGauges) {
        self.decision_level
            .store(gauges.decision_level, Ordering::Relaxed);
        self.assigned_vars
            .store(gauges.assigned_vars, Ordering::Relaxed);
        self.trail_len.store(gauges.trail_len, Ordering::Relaxed);
        self.pending_propagations
            .store(gauges.pending_propagations, Ordering::Relaxed);
        self.live_irredundant_clauses
            .store(gauges.live_irredundant_clauses, Ordering::Relaxed);
        self.live_learnt_clauses
            .store(gauges.live_learnt_clauses, Ordering::Relaxed);
        self.watcher_entries
            .store(gauges.watcher_entries, Ordering::Relaxed);
        self.clause_words
            .store(gauges.clause_words, Ordering::Relaxed);
        self.wasted_clause_words
            .store(gauges.wasted_clause_words, Ordering::Relaxed);
    }

    /// Loads one SAT gauge snapshot.
    fn load(&self) -> SatGauges {
        SatGauges {
            decision_level: self.decision_level.load(Ordering::Relaxed),
            assigned_vars: self.assigned_vars.load(Ordering::Relaxed),
            trail_len: self.trail_len.load(Ordering::Relaxed),
            pending_propagations: self.pending_propagations.load(Ordering::Relaxed),
            live_irredundant_clauses: self.live_irredundant_clauses.load(Ordering::Relaxed),
            live_learnt_clauses: self.live_learnt_clauses.load(Ordering::Relaxed),
            watcher_entries: self.watcher_entries.load(Ordering::Relaxed),
            clause_words: self.clause_words.load(Ordering::Relaxed),
            wasted_clause_words: self.wasted_clause_words.load(Ordering::Relaxed),
        }
    }
}

/// Atomically readable EUF gauges.
#[allow(clippy::missing_docs_in_private_items)]
#[derive(Default)]
struct AtomicEufGauges {
    registry_terms: AtomicU64,
    registry_atoms: AtomicU64,
    pending_assignments: AtomicU64,
    assigned_atoms: AtomicU64,
    pending_merges: AtomicU64,
    pending_repairs: AtomicU64,
    pending_atom_triggers: AtomicU64,
    pending_theory_clauses: AtomicU64,
    active_disequalities: AtomicU64,
    congruence_table_entries: AtomicU64,
}

impl AtomicEufGauges {
    /// Stores one EUF gauge snapshot.
    fn store(&self, gauges: EufGauges) {
        self.registry_terms
            .store(gauges.registry_terms, Ordering::Relaxed);
        self.registry_atoms
            .store(gauges.registry_atoms, Ordering::Relaxed);
        self.pending_assignments
            .store(gauges.pending_assignments, Ordering::Relaxed);
        self.assigned_atoms
            .store(gauges.assigned_atoms, Ordering::Relaxed);
        self.pending_merges
            .store(gauges.pending_merges, Ordering::Relaxed);
        self.pending_repairs
            .store(gauges.pending_repairs, Ordering::Relaxed);
        self.pending_atom_triggers
            .store(gauges.pending_atom_triggers, Ordering::Relaxed);
        self.pending_theory_clauses
            .store(gauges.pending_theory_clauses, Ordering::Relaxed);
        self.active_disequalities
            .store(gauges.active_disequalities, Ordering::Relaxed);
        self.congruence_table_entries
            .store(gauges.congruence_table_entries, Ordering::Relaxed);
    }

    /// Loads one EUF gauge snapshot.
    fn load(&self) -> EufGauges {
        EufGauges {
            registry_terms: self.registry_terms.load(Ordering::Relaxed),
            registry_atoms: self.registry_atoms.load(Ordering::Relaxed),
            pending_assignments: self.pending_assignments.load(Ordering::Relaxed),
            assigned_atoms: self.assigned_atoms.load(Ordering::Relaxed),
            pending_merges: self.pending_merges.load(Ordering::Relaxed),
            pending_repairs: self.pending_repairs.load(Ordering::Relaxed),
            pending_atom_triggers: self.pending_atom_triggers.load(Ordering::Relaxed),
            pending_theory_clauses: self.pending_theory_clauses.load(Ordering::Relaxed),
            active_disequalities: self.active_disequalities.load(Ordering::Relaxed),
            congruence_table_entries: self.congruence_table_entries.load(Ordering::Relaxed),
        }
    }
}

/// Timer-thread state that owns the JSONL writer.
struct LocalSession {
    /// Time at which sampling started.
    started: Instant,
    /// Buffered writer for the telemetry JSONL file.
    writer: BufWriter<File>,
    /// The first persistent write error observed while emitting samples.
    write_error: Option<io::Error>,
}

impl LocalSession {
    /// Creates one fresh local session around `writer`.
    fn new(writer: BufWriter<File>) -> Self {
        Self {
            started: Instant::now(),
            writer,
            write_error: None,
        }
    }

    /// Attempts to append one JSONL sample, remembering only the first error.
    fn write_sample(&mut self, mut sample: Sample) {
        if self.write_error.is_some() {
            return;
        }
        sample.elapsed_secs = self.started.elapsed().as_secs_f64();
        if let Err(error) = serde_json::to_writer(&mut self.writer, &sample) {
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

    /// Flushes the writer and returns the first recorded write error, if any.
    fn finish(&mut self) -> io::Result<()> {
        self.writer.flush()?;
        match self.write_error.take() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

/// Computes one counter delta between two cumulative snapshots.
fn subtract_counters(current: Counters, previous: Counters) -> Counters {
    Counters {
        sat: SatCounters {
            conflicts: current.sat.conflicts.saturating_sub(previous.sat.conflicts),
            propagations: current
                .sat
                .propagations
                .saturating_sub(previous.sat.propagations),
            decisions: current.sat.decisions.saturating_sub(previous.sat.decisions),
            restarts: current.sat.restarts.saturating_sub(previous.sat.restarts),
            reductions: current
                .sat
                .reductions
                .saturating_sub(previous.sat.reductions),
            learnt_clauses: current
                .sat
                .learnt_clauses
                .saturating_sub(previous.sat.learnt_clauses),
            deleted_clauses: current
                .sat
                .deleted_clauses
                .saturating_sub(previous.sat.deleted_clauses),
        },
        euf: EufCounters {
            input_equalities: current
                .euf
                .input_equalities
                .saturating_sub(previous.euf.input_equalities),
            input_disequalities: current
                .euf
                .input_disequalities
                .saturating_sub(previous.euf.input_disequalities),
            congruence_merges: current
                .euf
                .congruence_merges
                .saturating_sub(previous.euf.congruence_merges),
            theory_propagations: current
                .euf
                .theory_propagations
                .saturating_sub(previous.euf.theory_propagations),
            theory_conflicts: current
                .euf
                .theory_conflicts
                .saturating_sub(previous.euf.theory_conflicts),
        },
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::{Gauges, TelemetryRecorder, record_sat_conflict};

    /// Ensures periodic samples are emitted even if the solver never reaches a checkpoint.
    #[test]
    fn recorder_emits_periodic_samples_without_checkpoint_yields() {
        let path = unique_temp_path("telemetry-periodic");
        let recorder = TelemetryRecorder::with_period(&path, std::time::Duration::from_millis(10))
            .expect("start recorder");
        record_sat_conflict();
        std::thread::sleep(std::time::Duration::from_millis(30));
        recorder.finish(Gauges::default()).expect("finish recorder");

        let payload = fs::read_to_string(&path).expect("read telemetry");
        assert!(
            payload.lines().any(|line| !line.trim().is_empty()),
            "expected at least one periodic sample"
        );
        let _ = fs::remove_file(path);
    }

    /// Builds one unique temporary path for telemetry tests.
    fn unique_temp_path(prefix: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        std::env::temp_dir().join(format!("{prefix}-{nanos}.jsonl"))
    }
}
