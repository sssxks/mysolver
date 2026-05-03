//! Equality with uninterpreted functions over interned term identifiers.
//!
//! This crate provides a minimal congruence-closure checker for the solver
//! layer. Clients intern terms once, then ask whether a set of equality and
//! disequality atoms is theory-consistent.

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

/// Shape of one interned term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    /// Named constant symbol.
    Const(Box<str>),
    /// Uninterpreted function application.
    App {
        /// Function symbol name.
        fun: Box<str>,
        /// Argument term identifiers in call order.
        args: Box<[TermId]>,
    },
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

/// Congruence-closure state for interned EUF terms.
#[derive(Debug, Clone, Default)]
pub struct EufSolver {
    /// Interned [`TermKind`] values in ascending [`TermId`] order.
    terms: Vec<TermKind>,
}

impl EufSolver {
    /// Creates an empty EUF solver with no interned terms.
    pub fn new() -> Self {
        Self::default()
    }

    /// Interns a constant symbol and returns its stable identifier.
    pub fn intern_const(&mut self, name: impl Into<Box<str>>) -> TermId {
        self.push_term(TermKind::Const(name.into()))
    }

    /// Interns an uninterpreted function application and returns its identifier.
    pub fn intern_app(&mut self, fun: impl Into<Box<str>>, args: Box<[TermId]>) -> TermId {
        self.push_term(TermKind::App {
            fun: fun.into(),
            args,
        })
    }

    /// Returns the term arena in insertion order.
    pub fn terms(&self) -> &[TermKind] {
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

    /// Appends `kind`, assigns the next dense [`TermId`], and returns it.
    fn push_term(&mut self, kind: TermKind) -> TermId {
        debug_assert!(u32::try_from(self.terms.len()).is_ok());
        let id = TermId(self.terms.len() as u32);
        self.terms.push(kind);
        id
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
            if let Some(TermKind::App { args, .. }) = self.terms.get(index) {
                for arg in args.iter().rev() {
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
            let mut signatures = HashMap::<(&str, Box<[usize]>), usize>::new();

            for &term_index in relevant_terms {
                if !budget.checkpoint() {
                    return false;
                }
                let TermKind::App { fun, args } = &self.terms[term_index] else {
                    continue;
                };
                let mut canonical_args = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    if !budget.checkpoint() {
                        return false;
                    }
                    canonical_args.push(cc.find(arg.index()));
                }
                let signature = (fun.as_ref(), canonical_args.into_boxed_slice());
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
        let a = euf.intern_const("a");
        let b = euf.intern_const("b");
        let fa = euf.intern_app("f", Box::new([a]));
        let fb = euf.intern_app("f", Box::new([b]));
        let atoms = [TheoryAtom::Eq(a, b), TheoryAtom::Diseq(fa, fb)];
        assert!(euf.check(&atoms).is_err());
    }

    #[test]
    fn interrupts_when_fuel_runs_out() {
        let mut euf = EufSolver::new();
        let a = euf.intern_const("a");
        let b = euf.intern_const("b");
        let atoms = [TheoryAtom::Eq(a, b)];
        let mut fuel = Fuel::new(0);
        assert_eq!(
            euf.check_with_budget(&atoms, &mut fuel),
            EufCheckOutcome::Interrupted
        );
    }
}
