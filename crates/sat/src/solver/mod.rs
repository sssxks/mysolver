/// Clause insertion and clause-database update helpers.
mod add;
/// First-UIP conflict analysis.
mod analyze;
/// Watched-literal propagation.
mod propagate;
/// Branching heuristics, backtracking, and database reduction.
mod search;

use std::ops::Range;

use crate::clause_db::{ClauseArena, ClauseId};
use crate::heap::VarHeap;
use crate::telemetry;
#[cfg(feature = "telemetry")]
use crate::telemetry::Gauges;
use crate::{AssertionLevel, Lit, Var};

use self::add::ClassifiedTheoryClause;
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
    Binary {
        /// The literal that was false when the reason clause became unit.
        false_lit: Lit,
        /// The propagated literal.
        other: Lit,
        /// User scope in which this binary clause exists.
        assertion_level: AssertionLevel,
    },
    /// The assignment came from a long clause stored in the clause arena.
    Clause(ClauseId),
    /// The assignment came from one unit theory clause kept only as an
    /// implication-graph reason.
    Theory(usize),
}

/// One transient theory reason stored in a shared literal arena.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct TheoryReason {
    /// Start offset in `Solver::theory_reason_lits`.
    start: u32,
    /// Number of literals in this reason clause.
    len: u32,
    /// User scope carried by the theory explanation.
    assertion_level: AssertionLevel,
}

impl TheoryReason {
    /// Returns the literal range backing this transient reason.
    #[inline(always)]
    fn range(self) -> Range<usize> {
        let start = self.start as usize;
        let len = self.len as usize;
        start..start + len
    }
}

/// The outcome of a SAT solve attempt.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SatResult {
    /// The formula is satisfiable.
    Sat,
    /// The formula is unsatisfiable.
    Unsat,
}

/// The outcome of attempting to insert one clause into the SAT database.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AddClauseResult {
    /// The clause was already satisfied or tautological and was ignored.
    Satisfied,
    /// The clause was added successfully.
    Added,
    /// The clause made the current user scope immediately inconsistent.
    Inconsistent,
}

/// Why one `pop()` request failed.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum PopError {
    /// The requested pop depth exceeds the current assertion stack depth.
    Underflow,
}

/// Classification used only for theory-clause metrics and debugging.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TheoryClauseKind {
    /// Clause originating from frontend input.
    Input,
    /// General theory lemma.
    Lemma,
    /// Clause explaining a theory propagation.
    PropagationExplanation,
    /// Clause explaining a theory conflict.
    ConflictExplanation,
}

/// One theory clause waiting to be inserted into SAT.
#[derive(Clone, Debug)]
pub struct TheoryClause {
    /// Fully explained clause over SAT literals.
    pub lits: Box<[Lit]>,
    /// User level where this clause must remain valid.
    pub assertion_level: AssertionLevel,
    /// Classification used only for metrics and debugging.
    pub kind: TheoryClauseKind,
}

/// One theory explanation clause that is already conflicting under the current
/// SAT trail and therefore must enter CDCL conflict analysis directly.
#[derive(Clone, Debug)]
struct TheoryConflict {
    /// Falsified theory-clause literals under the current trail.
    lits: Box<[Lit]>,
    /// User scope carried by the theory explanation.
    assertion_level: AssertionLevel,
}

/// One conflict source waiting for root-level handling or first-UIP analysis.
#[derive(Clone, Debug)]
enum SearchConflict {
    /// Conflict emitted directly by a theory callback.
    Theory(TheoryConflict),
    /// Conflict found by watched-literal propagation.
    Propagation(propagate::Conflict),
}

/// SAT and user-scope coordinates for one search conflict.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct SearchConflictScope {
    /// Highest SAT decision level occurring in the conflict clause.
    decision_level: usize,
    /// User assertion level where a root-level conflict remains visible.
    assertion_level: AssertionLevel,
}

/// The minimal CDCL(T) callback surface consumed by the SAT engine.
pub trait Theory {
    /// Called once at the start of each SAT search.
    fn notify_search_start(&mut self);

    /// Called immediately after the SAT solver opens a new CDCL decision level.
    fn notify_new_decision_level(&mut self);

    /// Called for one new assignment on the SAT trail.
    fn notify_assignment(&mut self, lit: Lit);

    /// Called after the SAT solver backtracks to one CDCL decision level.
    fn notify_backtrack(&mut self, level: usize);

    /// Drains any theory clauses that became available during propagation.
    fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>);

    /// Performs one final theory check after Boolean propagation reaches fixpoint.
    fn final_check(&mut self, out: &mut Vec<TheoryClause>);

    /// Returns whether the theory still has pending work to flush into SAT.
    fn has_pending_work(&self) -> bool;

    /// Emits one telemetry sample when SAT reaches a safe checkpoint.
    #[cfg(feature = "telemetry")]
    fn maybe_emit_telemetry_sample(&self, sat_gauges: Gauges) {
        telemetry::maybe_emit_sample(|| telemetry::CombinedGauges {
            sat: sat_gauges,
            euf: telemetry::EufGauges::default(),
        });
    }
}

/// One pushed user-level assertion frame.
#[derive(Clone, Debug)]
pub(crate) struct UserFrame {
    /// Level represented by this frame.
    level: AssertionLevel,
    /// Number of variables allocated before this frame was pushed.
    vars_base: usize,
}

/// Summary of one first-UIP conflict analysis.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct AnalyzeSummary {
    /// Decision level to keep when backtracking before asserting the learned clause.
    backtrack_level: usize,
    /// User-level scope required for the learned clause to remain sound.
    assertion_level: AssertionLevel,
    /// Number of distinct decision levels present in the minimized learned clause.
    lbd: u32,
}

/// A CDCL SAT solver over CNF formulas.
#[derive(Debug)]
pub struct Solver {
    /// The shallowest user scope currently known to be immediately inconsistent.
    inconsistent_assertion_level: Option<AssertionLevel>,
    /// Current user assertion level.
    assertion_level: AssertionLevel,
    /// Stack of pushed user frames above root.
    user_frames: Vec<UserFrame>,
    /// The number of variables currently allocated and in scope.
    nvars: usize,

    /// Current assignment for each variable.
    assigns: Vec<LBool>,
    /// Decision level at which each variable was assigned.
    sat_level: Vec<usize>,
    /// User assertion level at which each variable was assigned.
    user_level: Vec<AssertionLevel>,
    /// Antecedent reason for each assignment, eagerly maintained [`ClauseId`] liveness.
    reason: Vec<Reason>,
    /// User assertion level where each variable was introduced.
    intro_level: Vec<AssertionLevel>,
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
    /// Read cursor into `trail` for theory notifications.
    theory_qhead: usize,

    /// Watch lists indexed by packed literal, may contain invalid [`ClauseId`]s.
    watches: Vec<Vec<Watcher>>,
    /// Active learned clauses, eagerly maintained [`ClauseId`] liveness.
    learnts: Vec<ClauseId>,
    /// Arena storing all long clauses.
    clauses: ClauseArena,
    /// Transient theory clauses used as reasons for unit theory propagations.
    theory_reason_lits: Vec<Lit>,
    /// Ranges into `theory_reason_lits`.
    theory_reasons: Vec<TheoryReason>,

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
    /// Memoized redundancy states used while minimizing learned clauses.
    minimize_cache: Vec<u8>,
    /// Variables whose redundancy cache entries must be cleared after one analysis.
    minimize_touched: Vec<Var>,
    /// Epoch-stamped decision levels used while counting clause LBD values.
    lbd_levels: Vec<u32>,
    /// Current epoch value stored in [`Self::lbd_levels`].
    lbd_epoch: u32,
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
            inconsistent_assertion_level: None,
            assertion_level: AssertionLevel::ROOT,
            user_frames: Vec::new(),
            nvars: 0,
            assigns: Vec::new(),
            sat_level: Vec::new(),
            user_level: Vec::new(),
            reason: Vec::new(),
            intro_level: Vec::new(),
            phase: Vec::new(),
            assigned_count: 0,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            theory_qhead: 0,
            watches: Vec::new(),
            clauses: ClauseArena::new(),
            learnts: Vec::new(),
            theory_reason_lits: Vec::new(),
            theory_reasons: Vec::new(),
            var_activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            order: VarHeap::new(),
            clause_inc: 1.0,
            clause_decay: 0.999,
            seen: Vec::new(),
            analyze_stack: Vec::new(),
            minimize_cache: Vec::new(),
            minimize_touched: Vec::new(),
            lbd_levels: Vec::new(),
            lbd_epoch: 0,
            conflicts: 0,
        }
    }

    /// Creates a solver preallocated with `n` variables.
    pub(crate) fn with_vars(n: usize) -> Self {
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
        self.sat_level.push(0);
        self.user_level.push(AssertionLevel::ROOT);
        self.reason.push(Reason::None);
        self.intro_level.push(self.assertion_level);
        self.phase.push(true);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.var_activity.push(0.0);
        self.seen.push(false);
        self.minimize_cache.push(0);
        self.order.new_var();
        self.order.insert(v, &self.var_activity);
        v
    }

    /// Returns the number of variables currently known to the solver.
    #[cfg(test)]
    pub(crate) fn num_vars(&self) -> usize {
        self.nvars
    }

    /// Returns the current decision level.
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    /// Returns whether a remembered inconsistency is active in the current user scope.
    #[inline(always)]
    fn not_ok(&self) -> bool {
        self.inconsistent_assertion_level
            .is_some_and(|level| level <= self.assertion_level)
    }

    /// Returns the current user assertion level.
    #[cfg(test)]
    pub(crate) fn current_assertion_level(&self) -> AssertionLevel {
        self.assertion_level
    }

    /// Returns the current truth value of `lit`, if assigned.
    ///
    /// The return value is `Some(true)` when `lit` is satisfied, `Some(false)` when
    /// `lit` is falsified, and `None` when its variable is unassigned.
    #[cfg(test)]
    pub(crate) fn value_lit_public(&self, lit: Lit) -> Option<bool> {
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
    #[cfg(test)]
    pub(crate) fn model(&self) -> Option<Vec<bool>> {
        if self.not_ok() || self.assigned_count != self.nvars {
            return None;
        }
        Some(self.assigns.iter().map(|v| *v == LBool::True).collect())
    }

    /// Captures the current solver gauges for one telemetry sample boundary.
    #[cfg(feature = "telemetry")]
    pub fn telemetry_gauges(&self) -> Gauges {
        Gauges {
            decision_level: self.decision_level() as u64,
            assigned_vars: self.assigned_count as u64,
            trail_len: self.trail.len() as u64,
            pending_propagations: self.trail.len().saturating_sub(self.qhead) as u64,
            // Irredundant long clauses are input-defined in this solver: they are
            // added during parsing and never deleted during search.
            live_irredundant_clauses: telemetry::live_irredundant_clauses(),
            // `self.learnts` tracks only live learned long clauses after reductions.
            live_learnt_clauses: self.learnts.len() as u64,
            watcher_entries: telemetry::watcher_entries(),
            clause_words: self.clauses.word_count() as u64,
            wasted_clause_words: self.clauses.wasted_word_count() as u64,
        }
    }

    /// Searches for a satisfying assignment for the current formula.
    #[cfg(test)]
    pub(crate) fn solve(&mut self) -> SatResult {
        self.solve_with_assumptions(&[], &mut NullTheory)
    }

    /// Searches for a satisfying assignment under one transient assumption set.
    pub fn solve_with_assumptions<T: Theory>(
        &mut self,
        assumptions: &[Lit],
        theory: &mut T,
    ) -> SatResult {
        self.reset_search();

        let (live_irredundant_clauses, _) = self.clauses.live_clause_counts();
        let watcher_entries = self.watches.iter().map(Vec::len).sum::<usize>();
        telemetry::initialize_solver_gauges(live_irredundant_clauses, watcher_entries);

        if self.not_ok() {
            return SatResult::Unsat;
        }

        theory.notify_search_start();

        let mut restart_conflicts = 0usize;
        let mut restart_limit = 100usize;
        let mut next_reduce = 2_000usize;
        let mut assumption_cursor = 0usize;
        // buffer across iterations to avoid repeated allocations during self.analyze()
        let mut learnt = Vec::with_capacity(16);
        let mut theory_clauses = Vec::new();

        loop {
            self.notify_theory_assignments(theory);
            if let Some(conflict) = self.flush_theory_clauses(theory, false, &mut theory_clauses) {
                if let Some(result) = self.handle_search_conflict(
                    SearchConflict::Theory(conflict),
                    theory,
                    &mut learnt,
                    &mut restart_conflicts,
                    &mut next_reduce,
                ) {
                    return result;
                }
                continue;
            }

            if let Some(conflict) = self.propagate() {
                if let Some(result) = self.handle_search_conflict(
                    SearchConflict::Propagation(conflict),
                    theory,
                    &mut learnt,
                    &mut restart_conflicts,
                    &mut next_reduce,
                ) {
                    return result;
                }
                continue;
            }

            self.notify_theory_assignments(theory);
            if let Some(conflict) = self.flush_theory_clauses(theory, true, &mut theory_clauses) {
                if let Some(result) = self.handle_search_conflict(
                    SearchConflict::Theory(conflict),
                    theory,
                    &mut learnt,
                    &mut restart_conflicts,
                    &mut next_reduce,
                ) {
                    return result;
                }
                continue;
            }

            if let Some(&assumption) = assumptions.get(assumption_cursor) {
                match self.value_lit(assumption) {
                    LBool::True => {
                        assumption_cursor += 1;
                        continue;
                    }
                    LBool::False => {
                        self.maybe_emit_telemetry_sample(theory);
                        return SatResult::Unsat;
                    }
                    LBool::Undef => {
                        self.new_decision_level();
                        theory.notify_new_decision_level();
                        telemetry::record_decision();
                        let _ = self.enqueue(assumption, Reason::None);
                        assumption_cursor += 1;
                        self.maybe_emit_telemetry_sample(theory);
                        continue;
                    }
                }
            }

            if self.assigned_count == self.nvars {
                self.maybe_emit_telemetry_sample(theory);
                return SatResult::Sat;
            }

            if restart_conflicts >= restart_limit {
                telemetry::record_restart();
                self.cancel_until(0);
                theory.notify_backtrack(0);
                restart_conflicts = 0;
                restart_limit = ((restart_limit as f64) * 1.5) as usize + 1;
                self.maybe_emit_telemetry_sample(theory);
                continue;
            }

            let Some(next) = self.pick_branch_lit() else {
                self.maybe_emit_telemetry_sample(theory);
                return SatResult::Sat;
            };
            self.new_decision_level();
            theory.notify_new_decision_level();
            telemetry::record_decision();
            let _ = self.enqueue(next, Reason::None);
            self.maybe_emit_telemetry_sample(theory);
        }
    }

    /// Starts one new user assertion frame.
    pub fn push(&mut self) {
        self.reset_search();
        debug_assert_eq!(self.decision_level(), 0);
        let new_level = self.assertion_level.next();
        self.user_frames.push(UserFrame {
            level: new_level,
            vars_base: self.nvars,
        });
        self.assertion_level = new_level;
    }

    /// Pops `n` user assertion frames.
    pub fn pop(&mut self, n: usize) -> Result<(), PopError> {
        self.reset_search();
        let target_depth = self
            .assertion_level
            .index()
            .checked_sub(n)
            .ok_or(PopError::Underflow)?;
        self.pop_to_assertion_level(AssertionLevel::from_index(target_depth))
    }

    /// Emits one periodic telemetry sample when the timer thread requested it.
    #[cfg(feature = "telemetry")]
    fn maybe_emit_telemetry_sample<T: Theory>(&self, theory: &T) {
        theory.maybe_emit_telemetry_sample(self.telemetry_gauges());
    }

    /// Compiles to a no-op when solver telemetry instrumentation is disabled.
    #[cfg(not(feature = "telemetry"))]
    #[inline(always)]
    fn maybe_emit_telemetry_sample<T: Theory>(&self, _theory: &T) {}

    /// Notifies one theory about every SAT assignment not yet reported this search.
    fn notify_theory_assignments<T: Theory>(&mut self, theory: &mut T) {
        while self.theory_qhead < self.trail.len() {
            let lit = self.trail[self.theory_qhead];
            self.theory_qhead += 1;
            theory.notify_assignment(lit);
        }
    }

    /// Flushes theory clauses back into SAT.
    fn flush_theory_clauses<T: Theory>(
        &mut self,
        theory: &mut T,
        final_check: bool,
        out: &mut Vec<TheoryClause>,
    ) -> Option<TheoryConflict> {
        out.clear();
        if final_check {
            theory.final_check(out);
        } else if theory.has_pending_work() {
            theory.drain_clauses(out);
        }

        for clause in out.drain(..) {
            match self.classify_theory_clause(&clause) {
                ClassifiedTheoryClause::Satisfied => {}
                ClassifiedTheoryClause::Conflict {
                    lits,
                    assertion_level,
                } => {
                    return Some(TheoryConflict {
                        lits: lits.into_boxed_slice(),
                        assertion_level,
                    });
                }
                ClassifiedTheoryClause::Unit {
                    lits,
                    unit_index,
                    assertion_level,
                } => {
                    let _ = self.insert_unit_theory_clause(lits, unit_index, assertion_level);
                }
                ClassifiedTheoryClause::Watch {
                    lits,
                    first,
                    second,
                    assertion_level,
                } => {
                    let _ =
                        self.insert_watched_theory_clause(lits, first, second, assertion_level);
                }
            }
        }
        None
    }

    /// Handles one conflict through either root-level UNSAT or first-UIP learning.
    fn handle_search_conflict<T: Theory>(
        &mut self,
        conflict: SearchConflict,
        theory: &mut T,
        learnt: &mut Vec<Lit>,
        restart_conflicts: &mut usize,
        next_reduce: &mut usize,
    ) -> Option<SatResult> {
        telemetry::record_conflict();
        self.conflicts += 1;
        *restart_conflicts += 1;

        let conflict_scope = self.search_conflict_scope(&conflict);
        if conflict_scope.decision_level == 0 {
            self.inconsistent_assertion_level = Some(conflict_scope.assertion_level);
            self.maybe_emit_telemetry_sample(theory);
            return Some(SatResult::Unsat);
        }

        if conflict_scope.decision_level < self.decision_level() {
            self.cancel_until(conflict_scope.decision_level);
            theory.notify_backtrack(conflict_scope.decision_level);
        }

        let summary = match conflict {
            SearchConflict::Theory(conflict) => {
                self.analyze_theory_clause(&conflict.lits, conflict.assertion_level, learnt)
            }
            SearchConflict::Propagation(conflict) => self.analyze(conflict, learnt),
        };

        self.cancel_until(summary.backtrack_level);
        theory.notify_backtrack(summary.backtrack_level);
        self.add_learnt_clause(learnt, summary.lbd, summary.assertion_level);
        self.var_decay_activity();
        self.clause_decay_activity();

        if self.conflicts >= *next_reduce {
            self.reduce_db();
            *next_reduce += 2_000;
        }

        self.maybe_emit_telemetry_sample(theory);
        None
    }

    /// Returns the SAT decision and user assertion coordinates for one conflict.
    fn search_conflict_scope(&self, conflict: &SearchConflict) -> SearchConflictScope {
        match conflict {
            SearchConflict::Theory(conflict) => self.theory_conflict_scope(conflict),
            SearchConflict::Propagation(conflict) => self.propagation_conflict_scope(*conflict),
        }
    }

    /// Returns the SAT decision and user assertion coordinates for one theory conflict.
    fn theory_conflict_scope(&self, conflict: &TheoryConflict) -> SearchConflictScope {
        let decision_level = conflict
            .lits
            .iter()
            .map(|lit| self.sat_level[lit.var().index()])
            .max()
            .unwrap_or(0);
        SearchConflictScope {
            decision_level,
            assertion_level: conflict.assertion_level,
        }
    }

    /// Returns the SAT decision and user assertion coordinates for one propagation conflict.
    fn propagation_conflict_scope(&self, conflict: propagate::Conflict) -> SearchConflictScope {
        match conflict {
            propagate::Conflict::Binary {
                false_lit,
                other,
                assertion_level,
            } => SearchConflictScope {
                decision_level: self.sat_level[false_lit.var().index()]
                    .max(self.sat_level[other.var().index()]),
                assertion_level,
            },
            propagate::Conflict::Clause(cid) => {
                let header = self.clauses.header(cid);
                let len = header.len();
                let mut level = 0;
                for i in 0..len {
                    let lit = self.clauses.clause(cid).lit(i);
                    level = level.max(self.sat_level[lit.var().index()]);
                }
                SearchConflictScope {
                    decision_level: level,
                    assertion_level: header.assertion_level(),
                }
            }
        }
    }
}

/// Trivial theory adapter used by plain SAT solving.
#[derive(Debug, Default)]
pub struct NullTheory;

impl Theory for NullTheory {
    fn notify_search_start(&mut self) {}

    fn notify_new_decision_level(&mut self) {}

    fn notify_assignment(&mut self, _lit: Lit) {}

    fn notify_backtrack(&mut self, _level: usize) {}

    fn drain_clauses(&mut self, _out: &mut Vec<TheoryClause>) {}

    fn final_check(&mut self, _out: &mut Vec<TheoryClause>) {}

    fn has_pending_work(&self) -> bool {
        false
    }
}
