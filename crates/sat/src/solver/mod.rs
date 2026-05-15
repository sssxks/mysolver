/// Clause insertion and clause-database update helpers.
mod add;
/// First-UIP conflict analysis.
mod analyze;
/// Watched-literal propagation.
mod propagate;
/// Branching heuristics, backtracking, and database reduction.
mod search;

use crate::clause_db::{ClauseArena, ClauseId};
use crate::heap::VarHeap;
use crate::telemetry::{self, SolverTelemetryGauges};
use crate::{Lit, Var};

use self::propagate::Watcher;

/// A three-valued boolean used for partial assignments.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum LBool {
    /// The value is assigned to false.
    False,
    /// The value is currently unassigned.
    Undef,
    /// The value is assigned to true.
    True,
}

/// The reason why a variable assignment was enqueued.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Reason {
    /// The assignment was a decision or top-level unit without a stored antecedent.
    None,
    /// The assignment came from a binary clause represented by its two literals.
    Binary(Lit, Lit),
    /// The assignment came from a long clause stored in the clause arena.
    Clause(ClauseId),
}

/// The outcome of a SAT solve attempt.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SatResult {
    /// The formula is satisfiable.
    Sat,
    /// The formula is unsatisfiable.
    Unsat,
}

/// A CDCL SAT solver over CNF formulas.
#[derive(Debug)]
pub struct Solver {
    /// Whether the clause database is still known to be consistent.
    ok: bool,
    /// The number of variables allocated in the solver.
    nvars: usize,

    /// Current assignment for each variable.
    assigns: Vec<LBool>,
    /// Decision level at which each variable was assigned.
    level: Vec<usize>,
    /// Antecedent reason for each assignment, eagerly maintained [`ClauseId`] liveness.
    reason: Vec<Reason>,
    /// Saved branching polarity for phase saving.
    phase: Vec<bool>,
    /// Count of variables that are currently assigned.
    assigned_count: usize,

    /// Assignment trail in chronological order.
    trail: Vec<Lit>,
    /// Trail indices that start each decision level.
    trail_lim: Vec<usize>,
    /// Read cursor into `trail` for propagation.
    qhead: usize,

    /// Watch lists indexed by packed literal, may contain invalid [`ClauseId`]s.
    watches: Vec<Vec<Watcher>>,
    /// Active learned clauses, eagerly maintained [`ClauseId`] liveness.
    learnts: Vec<ClauseId>,
    /// Arena storing all long clauses.
    clauses: ClauseArena,

    /// VSIDS activity per variable.
    var_activity: Vec<f64>,
    /// Current increment added when bumping variable activity.
    var_inc: f64,
    /// Multiplicative decay factor for variable activity.
    var_decay: f64,
    /// Heap of unassigned decision candidates.
    order: VarHeap,

    /// Current increment added when bumping clause activity.
    clause_inc: f32,
    /// Multiplicative decay factor for clause activity.
    clause_decay: f32,

    /// Temporary marks used during conflict analysis.
    seen: Vec<bool>,
    /// Variables marked during conflict analysis for later cleanup.
    analyze_stack: Vec<Var>,
    /// Number of conflicts seen during the current search.
    conflicts: usize,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Creates an empty solver with no variables or clauses.
    pub fn new() -> Self {
        Self {
            ok: true,
            nvars: 0,
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            phase: Vec::new(),
            assigned_count: 0,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            watches: Vec::new(),
            clauses: ClauseArena::new(),
            learnts: Vec::new(),
            var_activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            order: VarHeap::new(),
            clause_inc: 1.0,
            clause_decay: 0.999,
            seen: Vec::new(),
            analyze_stack: Vec::new(),
            conflicts: 0,
        }
    }

    /// Creates a solver preallocated with `n` variables.
    pub fn with_vars(n: usize) -> Self {
        let mut s = Self::new();
        for _ in 0..n {
            s.new_var();
        }
        s
    }

    /// Adds a fresh variable and returns its identifier.
    pub fn new_var(&mut self) -> Var {
        let v = Var::from_index(self.nvars);
        self.nvars += 1;
        self.assigns.push(LBool::Undef);
        self.level.push(0);
        self.reason.push(Reason::None);
        self.phase.push(true);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.var_activity.push(0.0);
        self.seen.push(false);
        self.order.new_var();
        self.order.insert(v, &self.var_activity);
        v
    }

    /// Returns the number of variables currently known to the solver.
    pub fn num_vars(&self) -> usize {
        self.nvars
    }

    /// Returns the current decision level.
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    /// Returns the current truth value of `lit`, if assigned.
    ///
    /// The return value is `Some(true)` when `lit` is satisfied, `Some(false)` when
    /// `lit` is falsified, and `None` when its variable is unassigned.
    pub fn value_lit_public(&self, lit: Lit) -> Option<bool> {
        match self.value_lit(lit) {
            LBool::True => Some(true),
            LBool::False => Some(false),
            LBool::Undef => None,
        }
    }

    /// Returns a complete model when the solver currently holds one.
    ///
    /// The model is indexed by variable and contains the underlying variable value,
    /// not literal satisfaction.
    pub fn model(&self) -> Option<Vec<bool>> {
        if !self.ok || self.assigned_count != self.nvars {
            return None;
        }
        Some(self.assigns.iter().map(|v| *v == LBool::True).collect())
    }

    /// Captures the current solver gauges for one telemetry sample boundary.
    pub fn telemetry_gauges(&self) -> SolverTelemetryGauges {
        let (live_irredundant_clauses, live_learnt_clauses) = self.clauses.live_clause_counts();
        let watcher_entries = self.watches.iter().map(Vec::len).sum::<usize>();

        SolverTelemetryGauges {
            decision_level: self.decision_level() as u64,
            assigned_vars: self.assigned_count as u64,
            trail_len: self.trail.len() as u64,
            pending_propagations: self.trail.len().saturating_sub(self.qhead) as u64,
            live_irredundant_clauses: live_irredundant_clauses as u64,
            live_learnt_clauses: live_learnt_clauses as u64,
            watcher_entries: watcher_entries as u64,
            clause_words: self.clauses.word_count() as u64,
            wasted_clause_words: self.clauses.wasted_word_count() as u64,
        }
    }

    /// Searches for a satisfying assignment for the current formula.
    pub fn solve(&mut self) -> SatResult {
        if !self.ok {
            return SatResult::Unsat;
        }

        let mut restart_conflicts = 0usize;
        let mut restart_limit = 100usize;
        let mut next_reduce = 2_000usize;
        // buffer across iterations to avoid repeated allocations during self.analyze()
        let mut learnt = Vec::with_capacity(16);

        loop {
            if let Some(conflict) = self.propagate() {
                telemetry::record_conflict();
                self.conflicts += 1;
                restart_conflicts += 1;

                if self.decision_level() == 0 {
                    self.ok = false;
                    self.maybe_emit_telemetry_sample();
                    return SatResult::Unsat;
                }

                let backtrack_level = self.analyze(conflict, &mut learnt);
                self.cancel_until(backtrack_level);
                self.add_learnt_clause(&learnt);
                self.var_decay_activity();
                self.clause_decay_activity();

                if self.conflicts >= next_reduce {
                    self.reduce_db();
                    next_reduce += 2_000;
                }

                self.maybe_emit_telemetry_sample();
                continue;
            }

            if self.assigned_count == self.nvars {
                self.maybe_emit_telemetry_sample();
                return SatResult::Sat;
            }

            if restart_conflicts >= restart_limit {
                telemetry::record_restart();
                self.cancel_until(0);
                restart_conflicts = 0;
                restart_limit = ((restart_limit as f64) * 1.5) as usize + 1;
                self.maybe_emit_telemetry_sample();
                continue;
            }

            let Some(next) = self.pick_branch_lit() else {
                self.maybe_emit_telemetry_sample();
                return SatResult::Sat;
            };
            self.new_decision_level();
            telemetry::record_decision();
            let _ = self.enqueue(next, Reason::None);
            self.maybe_emit_telemetry_sample();
        }
    }

    /// Emits one periodic telemetry sample when the timer thread requested it.
    fn maybe_emit_telemetry_sample(&self) {
        telemetry::maybe_emit_sample(self.telemetry_gauges());
    }
}
