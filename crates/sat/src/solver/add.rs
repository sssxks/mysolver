use crate::Lit;
use crate::clause_db::ClauseId;
use crate::telemetry;

use super::propagate::Watcher;
use super::{AddClauseResult, ClauseOrigin, Reason, Solver, TheoryClause, TheoryClauseKind};
use crate::AssertionLevel;

impl Solver {
    /// Adds a CNF clause to the database.
    ///
    /// The method returns `false` when the clause makes the formula immediately
    /// inconsistent; otherwise it returns `true`. Tautological and already-satisfied
    /// clauses are ignored.
    pub fn add_clause(&mut self, lits: &[Lit]) -> AddClauseResult {
        self.reset_search();
        self.add_scoped_clause(
            lits,
            self.current_clause_assertion_level(lits),
            ClauseOrigin::Input,
        )
    }

    /// Adds one clause carrying an explicit user-scope level and origin.
    fn add_scoped_clause(
        &mut self,
        lits: &[Lit],
        assertion_level: AssertionLevel,
        origin: ClauseOrigin,
    ) -> AddClauseResult {
        if !self.ok {
            if self
                .inconsistent_assertion_level
                .is_some_and(|level| level <= self.assertion_level)
            {
                return AddClauseResult::Inconsistent;
            }
            self.ok = true;
        }
        let Some(ps) = self.prepare_clause(lits) else {
            return AddClauseResult::Satisfied;
        };
        match ps.len() {
            0 => {
                self.ok = false;
                self.inconsistent_assertion_level = Some(assertion_level);
                AddClauseResult::Inconsistent
            }
            1 => {
                if !self.enqueue(ps[0], Reason::None) {
                    self.ok = false;
                    self.inconsistent_assertion_level = Some(assertion_level);
                    return AddClauseResult::Inconsistent;
                }
                AddClauseResult::Added
            }
            2 => {
                self.attach_binary(ps[0], ps[1], assertion_level);
                AddClauseResult::Added
            }
            _ => {
                match origin {
                    ClauseOrigin::Input | ClauseOrigin::Theory => {
                        self.attach_irredundant_long(&ps, assertion_level);
                    }
                    ClauseOrigin::Learnt => {
                        unreachable!("learned long clauses use add_learnt_clause")
                    }
                }
                AddClauseResult::Added
            }
        }
    }

    /// Adds one theory clause without discarding falsified literals needed as
    /// propagation reasons under the current trail.
    fn add_scoped_theory_clause(
        &mut self,
        lits: &[Lit],
        assertion_level: AssertionLevel,
    ) -> AddClauseResult {
        if !self.ok {
            if self
                .inconsistent_assertion_level
                .is_some_and(|level| level <= self.assertion_level)
            {
                return AddClauseResult::Inconsistent;
            }
            self.ok = true;
        }
        let Some(mut ps) = self.prepare_reason_clause(lits) else {
            return AddClauseResult::Satisfied;
        };

        let live_count = ps
            .iter()
            .filter(|&&lit| self.value_lit(lit) != super::LBool::False)
            .count();
        match live_count {
            0 => {
                self.ok = false;
                self.inconsistent_assertion_level = Some(assertion_level);
                AddClauseResult::Inconsistent
            }
            1 => {
                let unit_index = ps
                    .iter()
                    .position(|&lit| self.value_lit(lit) == super::LBool::Undef)
                    .expect("one live literal in an unsatisfied clause must be unassigned");
                ps.swap(0, unit_index);
                match ps.len() {
                    1 => {
                        if !self.enqueue(ps[0], Reason::None) {
                            self.ok = false;
                            self.inconsistent_assertion_level = Some(assertion_level);
                            return AddClauseResult::Inconsistent;
                        }
                    }
                    _ => {
                        let reason = if self.unit_theory_reason_is_root_level(&ps) {
                            Reason::None
                        } else {
                            Reason::Theory(self.push_theory_reason(&ps, assertion_level))
                        };
                        if !self.enqueue(ps[0], reason) {
                            self.ok = false;
                            self.inconsistent_assertion_level = Some(assertion_level);
                            return AddClauseResult::Inconsistent;
                        }
                    }
                }
                AddClauseResult::Added
            }
            _ => {
                move_two_live_literals_to_front(&mut ps, |lit| {
                    self.value_lit(lit) != super::LBool::False
                });
                match ps.len() {
                    0 | 1 => unreachable!("live count is at least two"),
                    2 => self.attach_binary(ps[0], ps[1], assertion_level),
                    _ => {
                        self.attach_irredundant_long(&ps, assertion_level);
                    }
                }
                AddClauseResult::Added
            }
        }
    }

    /// Normalizes a clause under the current assignment.
    ///
    /// Satisfied clauses return `None`. Otherwise the result is sorted, duplicate-free,
    /// and stripped of literals already known to be false. Tautologies also return
    /// `None`.
    pub(crate) fn prepare_clause(&self, lits: &[Lit]) -> Option<Vec<Lit>> {
        let mut ps = Vec::with_capacity(lits.len());
        for &lit in lits {
            match self.value_lit(lit) {
                super::LBool::True => return None,
                super::LBool::False => {}
                super::LBool::Undef => ps.push(lit),
            }
        }

        ps.sort_unstable_by_key(|lit| lit.index());

        let mut out = Vec::with_capacity(ps.len());
        let mut prev: Option<Lit> = None;
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

    /// Normalizes a clause while preserving currently falsified literals for use
    /// as an implication-graph reason.
    fn prepare_reason_clause(&self, lits: &[Lit]) -> Option<Vec<Lit>> {
        let mut ps = Vec::with_capacity(lits.len());
        for &lit in lits {
            if self.value_lit(lit) == super::LBool::True {
                return None;
            }
            ps.push(lit);
        }

        ps.sort_unstable_by_key(|lit| lit.index());

        let mut out = Vec::with_capacity(ps.len());
        let mut prev: Option<Lit> = None;
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
    fn attach_binary(&mut self, a: Lit, b: Lit, assertion_level: AssertionLevel) {
        self.watches[a.index()].push(Watcher::Binary {
            other: b,
            assertion_level,
        });
        self.watches[b.index()].push(Watcher::Binary {
            other: a,
            assertion_level,
        });
        telemetry::record_added_watchers(2);
    }

    /// Stores and watches one irredundant long clause.
    fn attach_irredundant_long(
        &mut self,
        lits: &[Lit],
        assertion_level: AssertionLevel,
    ) -> ClauseId {
        debug_assert!(lits.len() >= 3);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self.clauses.alloc_irredundant(lits, assertion_level);
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
        lits: &[Lit],
        lbd: u32,
        assertion_level: AssertionLevel,
    ) -> ClauseId {
        debug_assert!(lits.len() >= 3);
        debug_assert!(lbd > 0);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self
            .clauses
            .alloc_learnt(lits, self.clause_inc, lbd, assertion_level);
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
    /// `lits[1]` is the literal with the highest remaining decision level.
    pub(crate) fn add_learnt_clause(
        &mut self,
        lits: &[Lit],
        lbd: u32,
        assertion_level: AssertionLevel,
    ) {
        debug_assert!(!lits.is_empty());
        debug_assert!(lbd > 0);
        telemetry::record_learnt_clause();

        match lits.len() {
            1 => {
                let _ = self.enqueue(lits[0], Reason::None);
            }
            2 => {
                self.attach_binary(lits[0], lits[1], assertion_level);
                let _ = self.enqueue(
                    lits[0],
                    Reason::Binary {
                        false_lit: lits[1],
                        other: lits[0],
                        assertion_level,
                    },
                );
            }
            _ => {
                let cid = self.attach_learnt_long(lits, lbd, assertion_level);
                let _ = self.enqueue(lits[0], Reason::Clause(cid));
            }
        }
    }

    /// Computes the scope required for one frontend or input clause.
    fn current_clause_assertion_level(&self, lits: &[Lit]) -> AssertionLevel {
        lits.iter()
            .map(|lit| self.intro_level[lit.var().index()])
            .max()
            .unwrap_or(self.assertion_level)
            .max(self.assertion_level)
    }

    /// Computes the scope required for one theory explanation clause.
    fn explanation_assertion_level(&self, lits: &[Lit]) -> AssertionLevel {
        lits.iter()
            .map(|lit| self.intro_level[lit.var().index()])
            .max()
            .unwrap_or(AssertionLevel::ROOT)
    }

    /// Computes the scope required by one SAT-facing theory clause.
    pub(crate) fn theory_clause_assertion_level(&self, clause: &TheoryClause) -> AssertionLevel {
        match clause.kind {
            TheoryClauseKind::Input | TheoryClauseKind::Lemma => clause.assertion_level,
            TheoryClauseKind::PropagationExplanation | TheoryClauseKind::ConflictExplanation => {
                self.explanation_assertion_level(&clause.lits)
            }
        }
    }

    /// Inserts one theory clause through the ordinary scoped-clause path.
    pub(crate) fn add_theory_clause(&mut self, clause: TheoryClause) -> AddClauseResult {
        let assertion_level = self.theory_clause_assertion_level(&clause);
        self.add_scoped_theory_clause(&clause.lits, assertion_level)
    }

    /// Stores one transient theory reason and returns its stable id.
    fn push_theory_reason(&mut self, lits: &[Lit], assertion_level: AssertionLevel) -> usize {
        let start = u32::try_from(self.theory_reason_lits.len())
            .expect("theory reason literal arena exhausted u32 offsets");
        let len = u32::try_from(lits.len()).expect("theory reason length exceeds u32::MAX");
        let id = self.theory_reasons.len();
        self.theory_reason_lits.extend_from_slice(lits);
        self.theory_reasons.push(super::TheoryReason {
            start,
            len,
            assertion_level,
        });
        id
    }

    /// Returns whether one currently unit theory clause depends only on root
    /// assignments and therefore needs no stored implication-graph reason.
    fn unit_theory_reason_is_root_level(&self, lits: &[Lit]) -> bool {
        debug_assert!(!lits.is_empty());
        lits[1..]
            .iter()
            .all(|lit| self.sat_level[lit.var().index()] == 0)
    }
}

/// Moves two literals satisfying `is_live` to the first two positions.
fn move_two_live_literals_to_front(ps: &mut [Lit], is_live: impl Fn(Lit) -> bool) {
    let first = ps
        .iter()
        .position(|&lit| is_live(lit))
        .expect("caller guarantees at least two live literals");
    ps.swap(0, first);
    let second = ps[1..]
        .iter()
        .position(|&lit| is_live(lit))
        .expect("caller guarantees at least two live literals after the first")
        + 1;
    ps.swap(1, second);
}
