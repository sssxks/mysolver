//! Equality with uninterpreted functions over caller-assigned symbol and term identifiers.
//!
//! This crate provides a minimal congruence-closure checker for the solver
//! layer. Callers own any surface-level symbol tables, allocate opaque
//! [`FunId`] handles inside [`EufSolver`], intern terms once, then ask whether a
//! set of equality and disequality atoms is theory-consistent.

use std::collections::HashMap;
use std::fmt;

/// Cooperative budget checked by long-running search loops.
pub trait CheckBudget {
    /// Consumes one unit of budget and returns `false` when the caller must stop.
    fn checkpoint(&mut self) -> bool;
}

/// Deterministic work budget counted in abstract solver steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fuel {
    /// Remaining checkpoint count before the next checkpoint interrupts the run.
    remaining: u64,
}

impl Fuel {
    /// Creates a budget that allows exactly `remaining` successful checkpoints.
    pub fn new(remaining: u64) -> Self {
        Self { remaining }
    }

    /// Returns the number of checkpoints still available.
    pub fn remaining(self) -> u64 {
        self.remaining
    }
}

impl CheckBudget for Fuel {
    fn checkpoint(&mut self) -> bool {
        if self.remaining == 0 {
            return false;
        }
        self.remaining -= 1;
        true
    }
}

/// Outcome of a budget-aware EUF consistency check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EufCheckOutcome {
    /// The atom set is jointly consistent.
    Consistent,
    /// The atom set implies a concrete theory contradiction.
    Conflict(TheoryConflict),
    /// The caller-provided budget was exhausted before the check finished.
    Interrupted,
}

/// Stable identifier for one interned term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(u32);

impl TermId {
    /// Returns the internal dense index backing this term identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Stable identifier for one interned function symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunId(u32);

impl FunId {
    /// Returns the internal dense index backing this function identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// One interned EUF term represented as a function symbol plus argument terms.
///
/// Constants are encoded as nullary applications whose [`Self::args`] slice is empty.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    /// Applied function symbol.
    fun: FunId,
    /// Argument term identifiers in call order.
    args: Box<[TermId]>,
}

impl Term {
    /// Returns the function symbol applied by this term.
    pub fn fun(&self) -> FunId {
        self.fun
    }

    /// Returns the argument terms in application order.
    pub fn args(&self) -> &[TermId] {
        &self.args
    }
}

/// One theory atom to check under EUF.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryAtom {
    /// Equality constraint.
    Eq(TermId, TermId),
    /// Disequality constraint.
    Diseq(TermId, TermId),
}

/// Human-readable explanation for a theory conclusion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Explanation {
    /// Textual reason attached to the explanation.
    pub reason: Box<str>,
}

/// Inconsistency discovered by the EUF checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryConflict {
    /// Left side of the conflicting disequality.
    pub left: TermId,
    /// Right side of the conflicting disequality.
    pub right: TermId,
    /// Explanation for why the conflict is implied.
    pub explanation: Explanation,
}

impl fmt::Display for TheoryConflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "conflicting disequality between terms {:?} and {:?}: {}",
            self.left, self.right, self.explanation.reason
        )
    }
}

impl std::error::Error for TheoryConflict {}

/// Congruence-closure state for caller-interned EUF terms.
#[derive(Debug, Clone, Default)]
pub struct EufSolver {
    /// Next unallocated function-symbol identity.
    next_fun: u32,
    /// Interned [`Term`] values in ascending [`TermId`] order.
    terms: Vec<Term>,
}

impl EufSolver {
    /// Creates an empty EUF solver with no allocated symbols or interned terms.
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocates one fresh uninterpreted function symbol identity.
    ///
    /// The caller is responsible for mapping any higher-level symbol namespace
    /// onto this opaque handle.
    pub fn alloc_fun(&mut self) -> FunId {
        let id = FunId(self.next_fun);
        self.next_fun = self.next_fun.wrapping_add(1);
        debug_assert!(self.next_fun != 0, "function id space exhausted");
        id
    }

    /// Interns a term given its already-resolved function symbol and arguments.
    pub fn intern_term(&mut self, fun: FunId, args: Box<[TermId]>) -> TermId {
        let EufSolver { next_fun, terms } = self;
        debug_assert!(fun.0 < *next_fun, "term uses an unallocated function id");
        let term = Term { fun, args };
        debug_assert!(u32::try_from(terms.len()).is_ok());
        let id = TermId(terms.len() as u32);
        terms.push(term);
        id
    }

    /// Returns the term arena in insertion order.
    pub fn terms(&self) -> &[Term] {
        &self.terms
    }

    /// Checks whether the given atoms are jointly consistent in EUF.
    pub fn check(&self, atoms: &[TheoryAtom]) -> Result<(), TheoryConflict> {
        let mut budget = UnlimitedBudget;
        match self.check_with_budget(atoms, &mut budget) {
            EufCheckOutcome::Consistent => Ok(()),
            EufCheckOutcome::Conflict(conflict) => Err(conflict),
            EufCheckOutcome::Interrupted => unreachable!("unlimited budget cannot interrupt"),
        }
    }

    /// Checks whether the given atoms are jointly consistent in EUF under `budget`.
    pub fn check_with_budget<B: CheckBudget>(
        &self,
        atoms: &[TheoryAtom],
        budget: &mut B,
    ) -> EufCheckOutcome {
        let relevant_terms = self.relevant_terms(atoms, budget);
        let Some(relevant_terms) = relevant_terms else {
            return EufCheckOutcome::Interrupted;
        };
        let mut cc = Congruence::new(self.terms.len());
        for atom in atoms {
            if !budget.checkpoint() {
                return EufCheckOutcome::Interrupted;
            }
            if let TheoryAtom::Eq(left, right) = *atom {
                cc.union(left.index(), right.index());
            }
        }
        if !self.close_congruence(&mut cc, &relevant_terms, budget) {
            return EufCheckOutcome::Interrupted;
        }
        for atom in atoms {
            if !budget.checkpoint() {
                return EufCheckOutcome::Interrupted;
            }
            if let TheoryAtom::Diseq(left, right) = *atom
                && cc.find(left.index()) == cc.find(right.index())
            {
                return EufCheckOutcome::Conflict(TheoryConflict {
                    left,
                    right,
                    explanation: Explanation {
                        reason: "equality closure implies both sides are equal".into(),
                    },
                });
            }
        }
        EufCheckOutcome::Consistent
    }

    /// Collects the terms that can matter to the current atom set.
    ///
    /// Only atom endpoints and their recursive subterms can participate in a proof about
    /// those atoms. Unmentioned terms are ignored so guard-heavy incremental benchmarks do
    /// not pay congruence-closure cost for dormant formula regions.
    fn relevant_terms<B: CheckBudget>(
        &self,
        atoms: &[TheoryAtom],
        budget: &mut B,
    ) -> Option<Vec<usize>> {
        let mut seen = vec![false; self.terms.len()];
        let mut stack = Vec::new();

        for atom in atoms {
            if !budget.checkpoint() {
                return None;
            }
            let (left, right) = match *atom {
                TheoryAtom::Eq(left, right) | TheoryAtom::Diseq(left, right) => (left, right),
            };
            stack.push(left.index());
            stack.push(right.index());
        }

        while let Some(index) = stack.pop() {
            if !budget.checkpoint() {
                return None;
            }
            if seen.get(index).copied().unwrap_or(true) {
                continue;
            }
            seen[index] = true;
            if let Some(term) = self.terms.get(index) {
                for arg in term.args().iter().rev() {
                    stack.push(arg.index());
                }
            }
        }

        Some(
            seen.into_iter()
                .enumerate()
                .filter_map(|(index, used)| used.then_some(index))
                .collect(),
        )
    }

    /// Repeats signature bucketing until congruence-derived equalities stabilize in `cc`.
    fn close_congruence<B: CheckBudget>(
        &self,
        cc: &mut Congruence,
        relevant_terms: &[usize],
        budget: &mut B,
    ) -> bool {
        loop {
            if !budget.checkpoint() {
                return false;
            }
            let mut changed = false;
            let mut signatures = HashMap::<(FunId, Box<[usize]>), usize>::new();

            for &term_index in relevant_terms {
                if !budget.checkpoint() {
                    return false;
                }
                let term = &self.terms[term_index];
                let mut canonical_args = Vec::with_capacity(term.args().len());
                for arg in term.args().iter() {
                    if !budget.checkpoint() {
                        return false;
                    }
                    canonical_args.push(cc.find(arg.index()));
                }
                let signature = (term.fun(), canonical_args.into_boxed_slice());
                if let Some(&other_term) = signatures.get(&signature) {
                    changed |= cc.union(term_index, other_term);
                } else {
                    signatures.insert(signature, term_index);
                }
            }
            if !changed {
                return true;
            }
        }
    }
}

/// Disjoint-set union data for merging term indices under equality.
#[derive(Debug, Clone)]
struct Congruence {
    /// Parent pointers to the representative for each element index.
    parent: Vec<usize>,
    /// Union-by-rank metadata to keep paths shallow.
    rank: Vec<u8>,
}

impl Congruence {
    /// Builds `size` singleton sets labeled `0..size`.
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
            rank: vec![0; size],
        }
    }

    /// Returns the representative for `value` with path compression.
    fn find(&mut self, value: usize) -> usize {
        let parent = self.parent[value];
        if parent == value {
            value
        } else {
            let root = self.find(parent);
            self.parent[value] = root;
            root
        }
    }

    /// Merges the sets containing `left` and `right`; returns false if already merged.
    fn union(&mut self, left: usize, right: usize) -> bool {
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            return false;
        }
        match self.rank[left_root].cmp(&self.rank[right_root]) {
            std::cmp::Ordering::Less => self.parent[left_root] = right_root,
            std::cmp::Ordering::Greater => self.parent[right_root] = left_root,
            std::cmp::Ordering::Equal => {
                self.parent[right_root] = left_root;
                self.rank[left_root] += 1;
            }
        }
        true
    }
}

/// Sentinel budget for callers that intentionally want an unbounded search.
struct UnlimitedBudget;

impl CheckBudget for UnlimitedBudget {
    fn checkpoint(&mut self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closes_congruence() {
        let mut euf = EufSolver::new();
        let a_fun = euf.alloc_fun();
        let b_fun = euf.alloc_fun();
        let f_fun = euf.alloc_fun();
        let a = euf.intern_term(a_fun, Box::default());
        let b = euf.intern_term(b_fun, Box::default());
        let fa = euf.intern_term(f_fun, Box::new([a]));
        let fb = euf.intern_term(f_fun, Box::new([b]));
        let atoms = [TheoryAtom::Eq(a, b), TheoryAtom::Diseq(fa, fb)];
        assert!(euf.check(&atoms).is_err());
    }

    #[test]
    fn interrupts_when_fuel_runs_out() {
        let mut euf = EufSolver::new();
        let a_fun = euf.alloc_fun();
        let b_fun = euf.alloc_fun();
        let a = euf.intern_term(a_fun, Box::default());
        let b = euf.intern_term(b_fun, Box::default());
        let atoms = [TheoryAtom::Eq(a, b)];
        let mut fuel = Fuel::new(0);
        assert_eq!(
            euf.check_with_budget(&atoms, &mut fuel),
            EufCheckOutcome::Interrupted
        );
    }

    #[test]
    fn stores_terms_as_function_applications() {
        let mut euf = EufSolver::new();
        let a_fun = euf.alloc_fun();
        let f_fun = euf.alloc_fun();
        let a = euf.intern_term(a_fun, Box::default());
        let nullary_a = euf.intern_term(a_fun, Box::default());
        let fa = euf.intern_term(f_fun, Box::new([a]));

        let const_term = &euf.terms()[a.index()];
        let nullary_term = &euf.terms()[nullary_a.index()];
        let app_term = &euf.terms()[fa.index()];

        assert_eq!(const_term.args(), &[]);
        assert_eq!(nullary_term.args(), &[]);
        assert_eq!(app_term.args(), &[a]);
        assert_eq!(const_term.fun(), nullary_term.fun());
        assert_eq!(app_term.fun(), f_fun);
    }
}
