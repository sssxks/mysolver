//! Boolean plus EUF backend for already-lowered solver problems.
//!
//! This crate intentionally stays below SMT-LIB command handling and symbol
//! interning. Callers are expected to lower surface syntax into:
//!
//! - boolean clauses over [`Lit`] values,
//! - guarded theory atoms keyed by [`TheoryKey`], and
//! - one shared [`EufSolver`] term universe.
//!
//! The backend then runs CDCL(T) over that lowered problem and returns a
//! [`SatResult`].

use std::fmt;

pub use euf_core::{CheckBudget, Fuel};

use euf_core::{EufCheckOutcome, EufSolver, TermId, TheoryAtom};

/// SMT-LIB satisfiability result produced by the backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    /// The asserted formulas are satisfiable.
    Sat,
    /// The asserted formulas are inconsistent.
    Unsat,
    /// The solver could not determine satisfiability for the input fragment.
    Unknown,
    /// The solver stopped because the caller-provided budget ran out.
    Interrupted,
}

impl SatResult {
    /// Returns the canonical SMT-LIB spelling of this result.
    ///
    /// SMT-LIB has no dedicated token for interruptions, so [`SatResult::Interrupted`]
    /// is reported as `"unknown"` at that boundary.
    pub fn as_smtlib(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
            Self::Interrupted => "unknown",
        }
    }
}

impl fmt::Display for SatResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interrupted => f.write_str("interrupted"),
            _ => f.write_str(self.as_smtlib()),
        }
    }
}

/// Stable SAT variable identity inside one lowered problem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoolVar(u32);

impl BoolVar {
    /// Builds one non-zero SAT variable index.
    pub fn new(index: u32) -> Option<Self> {
        (index != 0).then_some(Self(index))
    }

    /// Returns the dense one-based index backing this variable.
    pub fn index(self) -> u32 {
        self.0
    }

    /// Returns the positive-polarity literal referencing this variable.
    pub fn positive(self) -> Lit {
        Lit {
            var: self,
            positive: true,
        }
    }
}

use std::ops::Not;

/// DIMACS-style signed literal referencing one [`BoolVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit {
    /// SAT variable identity this literal watches.
    var: BoolVar,
    /// When false, denotes negation relative to [`Self::var`]'s satisfying assignment bit.
    positive: bool,
}

impl Lit {
    /// Builds a literal from one variable plus polarity.
    pub fn new(var: BoolVar, positive: bool) -> Self {
        Self { var, positive }
    }

    /// Returns the underlying SAT variable.
    pub fn var(self) -> BoolVar {
        self.var
    }

    /// Returns whether this literal uses positive polarity.
    pub fn is_positive(self) -> bool {
        self.positive
    }

    /// Returns the dense watch-list slot for this literal.
    fn watch_index(self) -> usize {
        (self.var.0 as usize) * 2 + usize::from(!self.positive)
    }
}

impl Not for Lit {
    type Output = Self;

    /// Negates polarity while keeping the same underlying [`BoolVar`].
    fn not(self) -> Self::Output {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

/// Canonical EUF polarity carried by guarded SAT literals bridging into [`TheoryAtom`] checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TheoryRelation {
    /// SAT truth forces EUF equality of the keyed terms.
    Eq,
    /// SAT truth interprets EUF inequality between the keyed terms.
    Diseq,
}

/// Normalized unordered pair of [`TermId`] values plus [`TheoryRelation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TheoryKey {
    /// Whether guarding literal truth means equality versus disequality semantics.
    relation: TheoryRelation,
    /// Smaller [`TermId`] after canonical ordering.
    left: TermId,
    /// Larger [`TermId`] twin for stable hashing keyed EUF lookups.
    right: TermId,
}

impl TheoryKey {
    /// Builds a stable key swapping endpoints when necessary so hashing deduplicates symmetrical pairs.
    pub fn new(relation: TheoryRelation, left: TermId, right: TermId) -> Self {
        if left <= right {
            Self {
                relation,
                left,
                right,
            }
        } else {
            Self {
                relation,
                left: right,
                right: left,
            }
        }
    }

    /// Projects this key's guarded relation onto one concrete theory atom under `value`.
    fn atom_for_assignment(self, value: bool) -> TheoryAtom {
        match (self.relation, value) {
            (TheoryRelation::Eq, true) | (TheoryRelation::Diseq, false) => {
                TheoryAtom::Eq(self.left, self.right)
            }
            (TheoryRelation::Eq, false) | (TheoryRelation::Diseq, true) => {
                TheoryAtom::Diseq(self.left, self.right)
            }
        }
    }
}

/// Solves one already-lowered boolean-plus-EUF problem under `budget`.
///
/// `next_bool_var` must be the first unallocated variable id, with all used
/// variables lying in `1..next_bool_var`.
pub fn solve_with_budget<B: CheckBudget>(
    next_bool_var: u32,
    clauses: Vec<Box<[Lit]>>,
    theory_atoms: Vec<(BoolVar, TheoryKey)>,
    euf: EufSolver,
    budget: &mut B,
) -> SatResult {
    Cdcl::new(next_bool_var, clauses, theory_atoms, euf).solve(budget)
}

/// Sentinel budget used to preserve the unbounded entrypoint.
struct UnlimitedBudget;

impl CheckBudget for UnlimitedBudget {
    fn checkpoint(&mut self) -> bool {
        true
    }
}

/// Clause storage paired with two watched literal positions.
#[derive(Debug)]
struct Clause {
    /// Literals belonging to the clause.
    lits: Box<[Lit]>,
    /// Indices of the watched literals inside [`Self::lits`].
    watches: [usize; 2],
}

impl Clause {
    /// Builds one watched clause, defaulting to the first two literals when available.
    fn new(lits: Box<[Lit]>) -> Self {
        let second_watch = usize::from(lits.len() > 1);
        Self {
            lits,
            watches: [0, second_watch],
        }
    }
}

/// Assignment metadata stored per variable during CDCL search.
#[derive(Clone, Copy, Debug)]
struct AssignmentEntry {
    /// Chosen boolean value for the variable.
    value: bool,
    /// Decision level where the value became fixed.
    level: usize,
    /// Clause that implied the assignment, or `None` for decisions.
    reason: Option<usize>,
}

/// CDCL(T) search state with watched literals, clause learning, and eager EUF checks.
struct Cdcl {
    /// Boolean clauses guarding both pure props and bridged EUF predicates.
    clauses: Vec<Clause>,
    /// Clauses currently watching each literal polarity.
    watchlists: Vec<Vec<usize>>,
    /// Map from bridging SAT literals to their canonical [`TheoryKey`] metadata pairs.
    theory_atoms: Vec<(BoolVar, TheoryKey)>,
    /// Shared congruence oracle evaluating partial EUF interpretations.
    euf: EufSolver,
    /// Current assignment metadata indexed by dense [`BoolVar`] slot.
    assignments: Vec<Option<AssignmentEntry>>,
    /// Propagation trail in assignment order.
    trail: Vec<Lit>,
    /// Decision-level boundaries inside [`Self::trail`].
    trail_limits: Vec<usize>,
    /// Next trail position whose implications still need propagation.
    propagate_head: usize,
    /// Occurrence-based branching score for each boolean variable.
    variable_scores: Vec<u32>,
    /// Preferred phase for each variable, derived from clause polarity counts.
    preferred_phase: Vec<bool>,
    /// Scratch bitmap reused by conflict analysis to avoid repeated allocation.
    seen: Vec<bool>,
    /// Conflicts observed since the last restart.
    conflict_count: u64,
    /// Threshold triggering the next restart.
    restart_limit: u64,
    /// Sticky contradiction detected while loading clauses.
    has_empty_clause: bool,
}

impl Cdcl {
    /// Prepares a solver reserving one slot per boolean variable (index zero stays unused).
    fn new(
        next_bool_var: u32,
        clauses: Vec<Box<[Lit]>>,
        theory_atoms: Vec<(BoolVar, TheoryKey)>,
        euf: EufSolver,
    ) -> Self {
        let variable_count = next_bool_var as usize;
        let mut solver = Self {
            clauses: Vec::with_capacity(clauses.len()),
            watchlists: vec![Vec::new(); variable_count.saturating_mul(2)],
            theory_atoms,
            euf,
            assignments: vec![None; variable_count],
            trail: Vec::new(),
            trail_limits: Vec::new(),
            propagate_head: 0,
            variable_scores: vec![0; variable_count],
            preferred_phase: vec![false; variable_count],
            seen: vec![false; variable_count],
            conflict_count: 0,
            restart_limit: 128,
            has_empty_clause: false,
        };
        let mut polarity_balance = vec![0i32; variable_count];

        for lits in clauses {
            if lits.is_empty() {
                solver.has_empty_clause = true;
                continue;
            }
            for &lit in &lits {
                let index = lit.var.0 as usize;
                polarity_balance[index] += if lit.positive { 1 } else { -1 };
            }
            let clause_index = solver.add_clause(lits);
            if solver.clauses[clause_index].lits.len() == 1
                && !solver.enqueue(solver.clauses[clause_index].lits[0], Some(clause_index))
            {
                solver.has_empty_clause = true;
                break;
            }
        }

        for (index, balance) in polarity_balance.into_iter().enumerate().skip(1) {
            solver.preferred_phase[index] = balance > 0;
        }

        solver
    }

    /// Registers a clause, wires its watches, and returns the stable clause index.
    fn add_clause(&mut self, lits: Box<[Lit]>) -> usize {
        let clause_index = self.clauses.len();
        let clause = Clause::new(lits);
        if let Some(&first) = clause.lits.first() {
            self.watchlists[first.watch_index()].push(clause_index);
        }
        if clause.lits.len() > 1 {
            let second = clause.lits[clause.watches[1]];
            self.watchlists[second.watch_index()].push(clause_index);
        }
        for &lit in &clause.lits {
            let index = lit.var.0 as usize;
            self.variable_scores[index] = self.variable_scores[index].saturating_add(1);
        }
        self.clauses.push(clause);
        clause_index
    }

    /// Returns the current boolean value of `lit`, if its variable has been assigned already.
    fn lit_value(&self, lit: Lit) -> Option<bool> {
        self.assignments[lit.var.0 as usize].map(|entry| entry.value == lit.positive)
    }

    /// Returns the current decision level.
    fn decision_level(&self) -> usize {
        self.trail_limits.len()
    }

    /// Opens one fresh decision level above the current trail.
    fn new_decision_level(&mut self) {
        self.trail_limits.push(self.trail.len());
    }

    /// Records `lit` on the trail together with its reason, rejecting contradictory assignments.
    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        let level = self.decision_level();
        let slot = &mut self.assignments[lit.var.0 as usize];
        match *slot {
            Some(entry) => entry.value == lit.positive,
            None => {
                *slot = Some(AssignmentEntry {
                    value: lit.positive,
                    level,
                    reason,
                });
                self.trail.push(lit);
                true
            }
        }
    }

    /// Solves the accumulated clause set using a standard CDCL loop with theory conflict learning.
    fn solve<B: CheckBudget>(&mut self, budget: &mut B) -> SatResult {
        if self.has_empty_clause {
            return SatResult::Unsat;
        }

        loop {
            if !budget.checkpoint() {
                return SatResult::Interrupted;
            }

            let conflict = match self.propagate(budget) {
                Some(conflict) => conflict,
                None => return SatResult::Interrupted,
            };
            if let Some(conflict) = conflict {
                match self.handle_conflict(conflict) {
                    ConflictOutcome::Unsat => return SatResult::Unsat,
                    ConflictOutcome::Continue => continue,
                }
            }

            let theory_conflict = match self.theory_conflict(budget) {
                Some(conflict) => conflict,
                None => return SatResult::Interrupted,
            };
            if let Some(conflict) = theory_conflict {
                match self.handle_conflict(conflict) {
                    ConflictOutcome::Unsat => return SatResult::Unsat,
                    ConflictOutcome::Continue => continue,
                }
            }

            let all_satisfied = match self.all_clauses_satisfied(budget) {
                Some(value) => value,
                None => return SatResult::Interrupted,
            };
            if all_satisfied {
                return SatResult::Sat;
            }

            if self.conflict_count >= self.restart_limit && self.decision_level() > 0 {
                self.backtrack(0);
                self.conflict_count = 0;
                self.restart_limit = self.restart_limit.saturating_mul(2);
                continue;
            }

            let Some(branch_lit) = (match self.choose_branch_literal(budget) {
                Some(lit) => lit,
                None => return SatResult::Interrupted,
            }) else {
                return SatResult::Sat;
            };

            self.new_decision_level();
            if !self.enqueue(branch_lit, None) {
                return SatResult::Unsat;
            }
        }
    }

    /// Runs watched-literal propagation until fixpoint or a falsified clause is found.
    fn propagate<B: CheckBudget>(&mut self, budget: &mut B) -> Option<Option<Box<[Lit]>>> {
        while self.propagate_head < self.trail.len() {
            if !budget.checkpoint() {
                return None;
            }
            let assigned = self.trail[self.propagate_head];
            self.propagate_head += 1;
            let watched_false = assigned.not().watch_index();
            let watched_clauses = std::mem::take(&mut self.watchlists[watched_false]);
            let mut still_watching = Vec::with_capacity(watched_clauses.len());
            let mut cursor = 0usize;

            while cursor < watched_clauses.len() {
                if !budget.checkpoint() {
                    still_watching.extend_from_slice(&watched_clauses[cursor..]);
                    self.watchlists[watched_false] = still_watching;
                    return None;
                }

                let clause_index = watched_clauses[cursor];
                cursor += 1;

                let clause_watches = self.clauses[clause_index].watches;
                let false_watch_slot =
                    if self.clauses[clause_index].lits[clause_watches[0]] == assigned.not() {
                        0
                    } else {
                        1
                    };
                let other_watch_slot = 1 - false_watch_slot;
                let other_watch_index = clause_watches[other_watch_slot];
                let other_watch_lit = self.clauses[clause_index].lits[other_watch_index];

                if self.lit_value(other_watch_lit) == Some(true) {
                    still_watching.push(clause_index);
                    continue;
                }

                let replacement = {
                    let clause = &self.clauses[clause_index];
                    let mut replacement = None;
                    for candidate_index in 0..clause.lits.len() {
                        if !budget.checkpoint() {
                            still_watching.push(clause_index);
                            still_watching.extend_from_slice(&watched_clauses[cursor..]);
                            self.watchlists[watched_false] = still_watching;
                            return None;
                        }
                        if candidate_index == clause.watches[0]
                            || candidate_index == clause.watches[1]
                        {
                            continue;
                        }
                        let candidate = clause.lits[candidate_index];
                        if self.lit_value(candidate) != Some(false) {
                            replacement = Some(candidate_index);
                            break;
                        }
                    }
                    replacement
                };

                if let Some(replacement) = replacement {
                    self.clauses[clause_index].watches[false_watch_slot] = replacement;
                    let new_watch = self.clauses[clause_index].lits[replacement];
                    self.watchlists[new_watch.watch_index()].push(clause_index);
                    continue;
                }

                match self.lit_value(other_watch_lit) {
                    Some(false) => {
                        still_watching.push(clause_index);
                        still_watching.extend_from_slice(&watched_clauses[cursor..]);
                        self.watchlists[watched_false] = still_watching;
                        return Some(Some(self.clauses[clause_index].lits.clone()));
                    }
                    Some(true) => still_watching.push(clause_index),
                    None => {
                        if !self.enqueue(other_watch_lit, Some(clause_index)) {
                            still_watching.push(clause_index);
                            still_watching.extend_from_slice(&watched_clauses[cursor..]);
                            self.watchlists[watched_false] = still_watching;
                            return Some(Some(self.clauses[clause_index].lits.clone()));
                        }
                        still_watching.push(clause_index);
                    }
                }
            }

            self.watchlists[watched_false] = still_watching;
        }

        Some(None)
    }

    /// Returns one blocking clause when the currently assigned theory literals are inconsistent.
    fn theory_conflict<B: CheckBudget>(&self, budget: &mut B) -> Option<Option<Box<[Lit]>>> {
        let mut assigned_atoms = Vec::with_capacity(self.theory_atoms.len());
        for (var, key) in &self.theory_atoms {
            if !budget.checkpoint() {
                return None;
            }
            if let Some(entry) = self.assignments[var.0 as usize] {
                assigned_atoms.push((
                    Lit {
                        var: *var,
                        positive: entry.value,
                    }
                    .not(),
                    key.atom_for_assignment(entry.value),
                ));
            }
        }
        let atoms = assigned_atoms
            .iter()
            .map(|(_, atom)| atom.clone())
            .collect::<Vec<_>>();
        match self.euf.check_with_budget(&atoms, budget) {
            EufCheckOutcome::Consistent => Some(None),
            EufCheckOutcome::Conflict(conflict) => Some(Some(
                self.minimize_theory_conflict(
                    &self.conflict_relevant_atoms(&assigned_atoms, conflict.left, conflict.right),
                    budget,
                )?
                .into_boxed_slice(),
            )),
            EufCheckOutcome::Interrupted => None,
        }
    }

    /// Narrows theory-conflict minimization to atoms that touch the conflicting term cone.
    fn conflict_relevant_atoms(
        &self,
        assigned_atoms: &[(Lit, TheoryAtom)],
        left: TermId,
        right: TermId,
    ) -> Vec<(Lit, TheoryAtom)> {
        let mut relevant_terms = vec![false; self.euf.terms().len()];
        let mut stack = vec![left, right];

        while let Some(term) = stack.pop() {
            let index = term.index();
            if relevant_terms.get(index).copied().unwrap_or(true) {
                continue;
            }
            relevant_terms[index] = true;
            if let Some(term) = self.euf.terms().get(index) {
                stack.extend(term.args().iter().copied());
            }
        }

        let filtered = assigned_atoms
            .iter()
            .filter(|(_, atom)| match atom {
                TheoryAtom::Eq(left, right) | TheoryAtom::Diseq(left, right) => {
                    relevant_terms[left.index()] || relevant_terms[right.index()]
                }
            })
            .cloned()
            .collect::<Vec<_>>();

        if filtered.is_empty() {
            assigned_atoms.to_vec()
        } else {
            filtered
        }
    }

    /// Greedily shrinks one theory conflict into a much smaller learned blocking clause.
    fn minimize_theory_conflict<B: CheckBudget>(
        &self,
        assigned_atoms: &[(Lit, TheoryAtom)],
        budget: &mut B,
    ) -> Option<Vec<Lit>> {
        let current_level = self.decision_level();
        let mut kept = assigned_atoms.to_vec();
        let mut current_level_count = kept
            .iter()
            .filter(|(lit, _)| {
                self.assignments[lit.var.0 as usize]
                    .is_some_and(|entry| entry.level == current_level)
            })
            .count();
        let mut order = (0..kept.len()).collect::<Vec<_>>();
        order.sort_unstable_by_key(|&index| {
            self.assignments[kept[index].0.var.0 as usize]
                .map(|entry| usize::from(entry.level == current_level))
                .unwrap_or(0)
        });
        let mut order_index = 0usize;

        while order_index < order.len() {
            if !budget.checkpoint() {
                return None;
            }
            let index = order[order_index];
            if index >= kept.len() {
                order_index += 1;
                continue;
            }
            let removing_current_level = self.assignments[kept[index].0.var.0 as usize]
                .is_some_and(|entry| entry.level == current_level);
            if removing_current_level && current_level_count <= 1 {
                order_index += 1;
                continue;
            }
            let trial_atoms = kept
                .iter()
                .enumerate()
                .filter_map(|(trial_index, (_, atom))| {
                    (trial_index != index).then_some(atom.clone())
                })
                .collect::<Vec<_>>();
            let redundant = match self.euf.check_with_budget(&trial_atoms, budget) {
                EufCheckOutcome::Consistent => false,
                EufCheckOutcome::Conflict(_) => true,
                EufCheckOutcome::Interrupted => return None,
            };
            if redundant {
                if removing_current_level {
                    current_level_count -= 1;
                }
                kept.remove(index);
                for later in &mut order[(order_index + 1)..] {
                    if *later > index {
                        *later -= 1;
                    }
                }
            } else {
                order_index += 1;
            }
        }

        Some(kept.into_iter().map(|(lit, _)| lit).collect())
    }

    /// Learns from `conflict_clause`, backtracks non-chronologically, and enqueues the asserting literal.
    fn handle_conflict(&mut self, conflict_clause: Box<[Lit]>) -> ConflictOutcome {
        let current_level = self.decision_level();
        if current_level == 0 {
            return ConflictOutcome::Unsat;
        }

        let (learned_clause, backtrack_level) = self.analyze_conflict(&conflict_clause);
        self.bump_clause_activity(&learned_clause);
        self.backtrack(backtrack_level);
        if learned_clause.is_empty() {
            self.has_empty_clause = true;
            return ConflictOutcome::Unsat;
        }

        let clause_index = self.add_clause(learned_clause.clone().into_boxed_slice());
        let asserting_lit = self.clauses[clause_index].lits[0];
        if !self.enqueue(asserting_lit, Some(clause_index)) {
            self.has_empty_clause = true;
            return ConflictOutcome::Unsat;
        }

        self.conflict_count = self.conflict_count.saturating_add(1);
        ConflictOutcome::Continue
    }

    /// Performs first-UIP conflict analysis and returns `(learned_clause, backtrack_level)`.
    fn analyze_conflict(&mut self, conflict_clause: &[Lit]) -> (Vec<Lit>, usize) {
        for seen in &mut self.seen {
            *seen = false;
        }

        let current_level = self.decision_level();
        let mut learned = Vec::new();
        let mut pending_current_level = 0usize;
        let mut trail_index = self.trail.len();
        let mut clause = conflict_clause.to_vec();

        loop {
            for &lit in &clause {
                let var_index = lit.var.0 as usize;
                let Some(entry) = self.assignments[var_index] else {
                    continue;
                };
                if self.seen[var_index] || entry.level == 0 {
                    continue;
                }
                self.seen[var_index] = true;
                if entry.level == current_level {
                    pending_current_level += 1;
                } else {
                    learned.push(lit);
                }
            }
            if pending_current_level == 0 {
                return self.decision_cube_clause();
            }

            let pivot = loop {
                trail_index -= 1;
                let lit = self.trail[trail_index];
                if self.seen[lit.var.0 as usize] {
                    break lit;
                }
            };
            let pivot_index = pivot.var.0 as usize;
            self.seen[pivot_index] = false;
            pending_current_level -= 1;

            if pending_current_level == 0 {
                learned.insert(0, pivot.not());
                break;
            }

            let Some(reason) = self.assignments[pivot_index]
                .expect("pivot variable must stay assigned during analysis")
                .reason
            else {
                return self.decision_cube_clause();
            };
            clause.clear();
            clause.extend(
                self.clauses[reason]
                    .lits
                    .iter()
                    .copied()
                    .filter(|lit| lit.var != pivot.var),
            );
        }

        let backtrack_level = learned
            .iter()
            .skip(1)
            .filter_map(|lit| self.assignments[lit.var.0 as usize].map(|entry| entry.level))
            .max()
            .unwrap_or(0);

        (learned, backtrack_level)
    }

    /// Falls back to a sound but weaker learned clause blocking the current decision cube.
    fn decision_cube_clause(&self) -> (Vec<Lit>, usize) {
        let current_level = self.decision_level();
        let mut learned = Vec::with_capacity(current_level);
        if current_level == 0 {
            return (learned, 0);
        }

        let current_decision = self.trail[self.trail_limits[current_level - 1]].not();
        learned.push(current_decision);
        for level in (0..(current_level - 1)).rev() {
            let decision = self.trail[self.trail_limits[level]].not();
            learned.push(decision);
        }

        let backtrack_level = learned
            .iter()
            .skip(1)
            .filter_map(|lit| self.assignments[lit.var.0 as usize].map(|entry| entry.level))
            .max()
            .unwrap_or(0);

        (learned, backtrack_level)
    }

    /// Backtracks to `level`, removing every assignment from later decision levels.
    fn backtrack(&mut self, level: usize) {
        let trail_len = self
            .trail_limits
            .get(level)
            .copied()
            .unwrap_or(self.trail.len());
        while self.trail.len() > trail_len {
            if let Some(lit) = self.trail.pop() {
                self.assignments[lit.var.0 as usize] = None;
            }
        }
        self.trail_limits.truncate(level);
        self.propagate_head = self.propagate_head.min(trail_len);
    }

    /// Bumps branching activity for literals that survived conflict analysis.
    fn bump_clause_activity(&mut self, clause: &[Lit]) {
        for &lit in clause {
            let index = lit.var.0 as usize;
            self.variable_scores[index] = self.variable_scores[index].saturating_add(8);
            self.preferred_phase[index] = lit.positive;
        }
    }

    /// Returns true when every clause is already satisfied by the current partial assignment.
    fn all_clauses_satisfied<B: CheckBudget>(&self, budget: &mut B) -> Option<bool> {
        for clause in &self.clauses {
            if !budget.checkpoint() {
                return None;
            }
            let mut satisfied = false;
            for &lit in &clause.lits {
                if !budget.checkpoint() {
                    return None;
                }
                if self.lit_value(lit) == Some(true) {
                    satisfied = true;
                    break;
                }
            }
            if !satisfied {
                return Some(false);
            }
        }
        Some(true)
    }

    /// Chooses the highest-activity still-unassigned variable and applies its preferred phase.
    fn choose_branch_literal<B: CheckBudget>(&self, budget: &mut B) -> Option<Option<Lit>> {
        let mut best_var = None;

        for index in 1..self.assignments.len() {
            if !budget.checkpoint() {
                return None;
            }
            if self.assignments[index].is_some() {
                continue;
            }
            let replace = match best_var {
                Some(current) => self.variable_preferred_over(index, current),
                None => true,
            };
            if replace {
                best_var = Some(index);
            }
        }

        Some(best_var.map(|index| Lit {
            var: BoolVar(index as u32),
            positive: self.preferred_phase[index],
        }))
    }

    /// Returns true when `candidate_index` should be chosen ahead of `current_index`.
    fn variable_preferred_over(&self, candidate_index: usize, current_index: usize) -> bool {
        let candidate_score = self.variable_scores[candidate_index];
        let current_score = self.variable_scores[current_index];
        if candidate_score != current_score {
            return candidate_score > current_score;
        }

        candidate_index < current_index
    }
}

/// Result of processing one conflict inside the CDCL main loop.
enum ConflictOutcome {
    /// The search learned a clause and should continue.
    Continue,
    /// The conflict happened at decision level zero and proves unsatisfiability.
    Unsat,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interrupted_formats_distinctly_from_unknown() {
        assert_eq!(SatResult::Interrupted.to_string(), "interrupted");
        assert_eq!(SatResult::Interrupted.as_smtlib(), "unknown");
    }
}
