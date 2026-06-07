use std::cmp::max;

use crate::clause_db::Clause;
use crate::telemetry;
use crate::{Level, Literal};

use super::propagate::Watcher;
use super::{Reason, Solver, TheoryClause, TheoryClauseKind, TruthValue};
use crate::Scope;

/// Drop false literals during ordinary clause normalization.
const DROP_FALSE: bool = false;

/// Keep false literals so theory clauses can become full implication-graph reasons.
const KEEP_FALSE: bool = true;

impl Solver {
    /// Adds a CNF clause to the database.
    ///
    /// Tautological and already-satisfied clauses are ignored. Empty or
    /// conflicting clauses mark the current scope inconsistent.
    pub fn add_clause(&mut self, lits: &[Literal]) {
        self.reset_search();
        self.add_scoped_clause(lits, self.input_clause_scope(lits));
    }

    /// Adds one input clause carrying an explicit scope level.
    fn add_scoped_clause(&mut self, lits: &[Literal], scope: Scope) {
        if self.not_ok() {
            return;
        }
        let Some(ps) = self.normalize_clause::<DROP_FALSE>(lits) else {
            return;
        };
        match ps.len() {
            0 => {
                self.inconsistent_scope = Some(scope);
            }
            1 => {
                if !self.enqueue(ps[0], Reason::None) {
                    self.inconsistent_scope = Some(scope);
                }
            }
            2 => {
                self.attach_binary(ps[0], ps[1], scope);
            }
            _ => {
                self.attach_irredundant_long(&ps, scope);
            }
        }
    }

    /// Classifies one SAT-facing theory clause after reason-preserving normalization.
    pub(crate) fn classify_theory_clause(&self, clause: &TheoryClause) -> ClassifiedTheoryClause {
        let scope = self.theory_clause_scope(clause);
        let Some(lits) = self.normalize_clause::<KEEP_FALSE>(&clause.lits) else {
            return ClassifiedTheoryClause::Satisfied;
        };

        let mut first = None;
        let mut second = None;
        for (index, &lit) in lits.iter().enumerate() {
            if self.value_lit(lit) == TruthValue::False {
                continue;
            }
            if first.is_none() {
                first = Some(index);
            } else {
                second = Some(index);
                break;
            }
        }

        match (first, second) {
            (None, _) => ClassifiedTheoryClause::Conflict { lits, scope },
            (Some(unit_index), None) => ClassifiedTheoryClause::Unit {
                lits,
                unit_index,
                scope,
            },
            (Some(first), Some(second)) => ClassifiedTheoryClause::Watch {
                lits,
                first,
                second,
                scope,
            },
        }
    }

    /// Inserts one currently unit theory clause and keeps its full reason when needed.
    pub(crate) fn insert_unit_theory_clause(
        &mut self,
        mut lits: Vec<Literal>,
        unit_index: usize,
        scope: Scope,
    ) {
        if self.not_ok() {
            return;
        }
        lits.swap(0, unit_index);

        let reason = if lits.len() == 1 || self.unit_theory_reason_is_root_level(&lits) {
            Reason::None
        } else {
            Reason::Theory(self.push_theory_reason(&lits, scope))
        };
        if !self.enqueue(lits[0], reason) {
            self.inconsistent_scope = Some(scope);
        }
    }

    /// Inserts one theory clause with at least two currently live literals.
    pub(crate) fn insert_watched_theory_clause(
        &mut self,
        mut lits: Vec<Literal>,
        first: usize,
        second: usize,
        scope: Scope,
    ) {
        if self.not_ok() {
            return;
        }
        move_two_indices_to_front(&mut lits, first, second);
        match lits.len() {
            2 => self.attach_binary(lits[0], lits[1], scope),
            _ => {
                self.attach_irredundant_long(&lits, scope);
            }
        }
    }

    /// Normalizes one clause under the current assignment.
    ///
    /// The returned clause is sorted and duplicate-free. Tautological clauses and
    /// clauses already satisfied by the current assignment return `None`.
    fn normalize_clause<const KEEP_FALSE_LITERALS: bool>(
        &self,
        lits: &[Literal],
    ) -> Option<Vec<Literal>> {
        let mut ps = Vec::with_capacity(lits.len());
        for &lit in lits {
            match self.value_lit(lit) {
                TruthValue::True => return None,
                TruthValue::False => {
                    if KEEP_FALSE_LITERALS {
                        ps.push(lit);
                    }
                }
                TruthValue::Unknown => ps.push(lit),
            }
        }

        ps.sort_unstable_by_key(|lit| lit.index());

        let mut out = Vec::with_capacity(ps.len());
        let mut prev: Option<Literal> = None;
        for lit in ps {
            if prev == Some(lit) {
                continue;
            }
            if let Some(p) = prev
                && p.var() == lit.var()
                && p.is_negated() != lit.is_negated()
            {
                return None;
            }
            out.push(lit);
            prev = Some(lit);
        }
        Some(out)
    }

    /// Attaches a binary clause to both of its watch lists.
    fn attach_binary(&mut self, a: Literal, b: Literal, scope: Scope) {
        self.watches[a.index()].push(Watcher::Binary { other: b, scope });
        self.watches[b.index()].push(Watcher::Binary { other: a, scope });
        telemetry::record_added_watchers(2);
    }

    /// Stores and watches one irredundant long clause.
    fn attach_irredundant_long(&mut self, lits: &[Literal], scope: Scope) -> Clause {
        debug_assert!(lits.len() >= 3);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self.clauses.alloc_irredundant(lits, scope);
        self.watches[w0.index()].push(Watcher::Long {
            clause: cid,
            blocker: w1,
        });
        self.watches[w1.index()].push(Watcher::Long {
            clause: cid,
            blocker: w0,
        });
        telemetry::record_added_watchers(2);
        cid
    }

    /// Stores and watches one learned long clause together with its initial LBD.
    pub(crate) fn attach_learnt_long(
        &mut self,
        lits: &[Literal],
        lbd: u32,
        scope: Scope,
    ) -> Clause {
        debug_assert!(lits.len() >= 3);
        debug_assert!(lbd > 0);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self.clauses.alloc_learnt(lits, self.clause_inc, lbd, scope);
        self.watches[w0.index()].push(Watcher::Long {
            clause: cid,
            blocker: w1,
        });
        self.watches[w1.index()].push(Watcher::Long {
            clause: cid,
            blocker: w0,
        });
        telemetry::record_added_watchers(2);
        self.learnts.push(cid);
        cid
    }

    /// Inserts a learned clause and enqueues its asserting literal.
    ///
    /// The caller must provide `lits` in asserting order as produced by
    /// [`Self::analyze`]: `lits[0]` is the asserting literal and, when `lits.len() > 1`,
    /// `lits[1]` is the literal with the highest remaining level.
    pub(crate) fn add_learnt_clause(&mut self, lits: &[Literal], lbd: u32, scope: Scope) {
        debug_assert!(!lits.is_empty());
        debug_assert!(lbd > 0);
        telemetry::record_learnt_clause();

        match lits.len() {
            1 => {
                let _ = self.enqueue(lits[0], Reason::None);
            }
            2 => {
                self.attach_binary(lits[0], lits[1], scope);
                let _ = self.enqueue(
                    lits[0],
                    Reason::Binary {
                        false_lit: lits[1],
                        other: lits[0],
                        scope,
                    },
                );
            }
            _ => {
                let cid = self.attach_learnt_long(lits, lbd, scope);
                let _ = self.enqueue(lits[0], Reason::Clause(cid));
            }
        }
    }

    /// Computes the scope required for one frontend or input clause.
    fn input_clause_scope(&self, lits: &[Literal]) -> Scope {
        lits.iter()
            .map(|lit| self.variable_scope[lit.var().index()])
            .max()
            .unwrap_or(self.current_scope)
            .max(self.current_scope)
    }

    /// Computes the scope required by one SAT-facing theory clause.
    fn theory_clause_scope(&self, clause: &TheoryClause) -> Scope {
        match clause.kind {
            TheoryClauseKind::Input | TheoryClauseKind::Lemma => clause.scope,
            TheoryClauseKind::PropagationExplanation | TheoryClauseKind::ConflictExplanation => {
                // regression test `empty_theory_conflict_preserves_declared_scope` in crates/sat/src/lib.rs
                let a = {
                    clause
                        .lits
                        .iter()
                        .map(|lit| self.variable_scope[lit.var().index()])
                        .max()
                        .unwrap_or(Scope::ROOT)
                };
                max(a, clause.scope)
            }
        }
    }

    /// Stores one transient theory reason and returns its stable id.
    fn push_theory_reason(&mut self, lits: &[Literal], scope: Scope) -> usize {
        let start = u32::try_from(self.theory_reason_lits.len())
            .expect("theory reason literal arena exhausted u32 offsets");
        let len = u32::try_from(lits.len()).expect("theory reason length exceeds u32::MAX");
        let id = self.theory_reasons.len();
        self.theory_reason_lits.extend_from_slice(lits);
        self.theory_reasons
            .push(super::TheoryReason { start, len, scope });
        id
    }

    /// Returns whether one currently unit theory clause depends only on root
    /// assignments and therefore needs no stored implication-graph reason.
    fn unit_theory_reason_is_root_level(&self, lits: &[Literal]) -> bool {
        debug_assert!(!lits.is_empty());
        lits[1..]
            .iter()
            .all(|lit| self.level[lit.var().index()] == Level::ROOT)
    }
}

/// The current SAT-trail state of one normalized theory clause.
///
/// Semantically, this is either a satisfied clause, a currently conflicting
/// clause, a unit clause ready to propagate, or a clause ready for watching.
pub(crate) enum ClassifiedTheoryClause {
    /// The clause is already satisfied or tautological under the current trail.
    Satisfied,
    /// Every normalized literal is currently false.
    Conflict {
        /// Normalized falsified literals retained for conflict analysis.
        lits: Vec<Literal>,
        /// Scope where the conflict must remain visible.
        scope: Scope,
    },
    /// Exactly one normalized literal is currently not false.
    Unit {
        /// Normalized clause literals retained as a propagation reason.
        lits: Vec<Literal>,
        /// Index of the literal to enqueue.
        unit_index: usize,
        /// Scope where this theory clause remains valid.
        scope: Scope,
    },
    /// At least two literals are not currently false.
    Watch {
        /// Normalized clause literals retained for future reasons.
        lits: Vec<Literal>,
        /// Index of the first live literal.
        first: usize,
        /// Index of the second live literal.
        second: usize,
        /// Scope where this theory clause remains valid.
        scope: Scope,
    },
}

/// Moves two known-distinct indices to the first two positions.
fn move_two_indices_to_front<T>(slice: &mut [T], first: usize, second: usize) {
    debug_assert_ne!(first, second);

    slice.swap(0, first);
    let second = if second == 0 { first } else { second };
    slice.swap(1, second);
}
