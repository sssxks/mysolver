#![warn(missing_docs, clippy::missing_docs_in_private_items)]
//! Demo solver that emits periodic JSON metrics on stderr.

use observability_exp::StatsSample;
use std::cell::Cell;
use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};

/// Flag set by the timer thread to request a metrics flush from the hot loop.
static TICK: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Per-thread counters so the hot path only touches thread-local cells.
    static STATS: Stats = const {
        Stats {
            steps: Cell::new(0),
            conflicts: Cell::new(0),
            propagations: Cell::new(0),
            decisions: Cell::new(0),
        }
    };
}

/// Mutable counters accumulated between emitted samples.
struct Stats {
    /// Number of steps executed since the last flush.
    steps: Cell<u64>,
    /// Number of conflicts observed since the last flush.
    conflicts: Cell<u64>,
    /// Number of propagations observed since the last flush.
    propagations: Cell<u64>,
    /// Number of decisions observed since the last flush.
    decisions: Cell<u64>,
}

/// Tiny stateful solver model used only to drive the metrics experiment.
struct Solver {
    /// Remaining number of steps before the solver reports completion.
    remaining_steps: u64,
    /// Linear-congruential PRNG state used to generate synthetic events.
    rng: u64,
}

impl Solver {
    /// Total number of loop iterations executed by the demo solver.
    const TOTAL_STEPS: u64 = 2_000_000_000;

    /// Creates a new solver with a fixed pseudo-random seed.
    fn new() -> Self {
        Self {
            remaining_steps: Self::TOTAL_STEPS,
            rng: 0x1234_5678_9abc_def0,
        }
    }

    /// Returns whether all scheduled work has been consumed.
    fn done(&self) -> bool {
        self.remaining_steps == 0
    }

    /// Executes one synthetic solver step and updates the thread-local counters.
    fn step(&mut self) {
        self.remaining_steps -= 1;
        self.rng = self
            .rng
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);

        inc_steps();

        if self.rng & 0xff == 0 {
            inc_conflicts();
        }

        if self.rng & 0x3f == 0 {
            inc_decisions();
        }

        inc_propagations(1 + (self.rng & 7));
    }
}

/// Increments the step counter by one.
fn inc_steps() {
    STATS.with(|s| s.steps.set(s.steps.get() + 1));
}

/// Increments the conflict counter by one.
fn inc_conflicts() {
    STATS.with(|s| s.conflicts.set(s.conflicts.get() + 1));
}

/// Increments the propagation counter by the provided amount.
fn inc_propagations(n: u64) {
    STATS.with(|s| s.propagations.set(s.propagations.get() + n));
}

/// Increments the decision counter by one.
fn inc_decisions() {
    STATS.with(|s| s.decisions.set(s.decisions.get() + 1));
}

/// Resets the current counters and packages them as a transport sample.
fn take_stats(t: f64) -> StatsSample {
    STATS.with(|s| StatsSample {
        t,
        steps: s.steps.replace(0),
        conflicts: s.conflicts.replace(0),
        propagations: s.propagations.replace(0),
        decisions: s.decisions.replace(0),
    })
}

/// Starts a background thread that periodically requests a stats flush.
fn spawn_tick_thread(period: Duration) {
    let _ = thread::spawn(move || {
        loop {
            thread::sleep(period);
            TICK.store(true, Ordering::Relaxed);
        }
    });
}

/// Writes one JSONL sample to stderr.
fn emit_stats_line(sample: &StatsSample) -> io::Result<()> {
    let mut stderr = io::stderr().lock();
    serde_json::to_writer(&mut stderr, sample)?;
    writeln!(stderr)
}

/// Runs the demo solver until completion.
fn main() -> io::Result<()> {
    spawn_tick_thread(Duration::from_secs(1));

    let started = Instant::now();
    let mut solver = Solver::new();

    while !solver.done() {
        solver.step();

        if TICK.load(Ordering::Relaxed) {
            TICK.store(false, Ordering::Relaxed);
            let sample = take_stats(started.elapsed().as_secs_f64());
            emit_stats_line(&sample)?;
        }
    }

    let sample = take_stats(started.elapsed().as_secs_f64());
    emit_stats_line(&sample)?;

    println!("SAT");
    Ok(())
}
