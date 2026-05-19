use crate::Lit;
use crate::clause_db::ClauseId;
use crate::telemetry;

use super::propagate::Watcher;
use super::{Reason, Solver};

impl Solver {
    /// Adds a CNF clause to the database.
    ///
    /// The method returns `false` when the clause makes the formula immediately
    /// inconsistent; otherwise it returns `true`. Tautological and already-satisfied
    /// clauses are ignored.
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if !self.ok {
            return false;
        }
        let Some(ps) = self.prepare_clause(lits) else {
            return true;
        };
        match ps.len() {
            0 => {
                self.ok = false;
                false
            }
            1 => {
                if !self.enqueue(ps[0], Reason::None) {
                    self.ok = false;
                    return false;
                }
                true
            }
            2 => {
                self.attach_binary(ps[0], ps[1]);
                true
            }
            _ => {
                self.attach_irredundant_long(&ps);
                true
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

    /// Attaches a binary clause to both of its watch lists.
    pub(crate) fn attach_binary(&mut self, a: Lit, b: Lit) {
        self.watches[a.index()].push(Watcher::Binary { other: b });
        self.watches[b.index()].push(Watcher::Binary { other: a });
        telemetry::record_added_watchers(2);
    }

    /// Stores and watches one irredundant long clause.
    pub(crate) fn attach_irredundant_long(&mut self, lits: &[Lit]) -> ClauseId {
        debug_assert!(lits.len() >= 3);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self.clauses.alloc(lits, false, 0.0, 0);
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
    pub(crate) fn attach_learnt_long(&mut self, lits: &[Lit], lbd: u32) -> ClauseId {
        debug_assert!(lits.len() >= 3);
        debug_assert!(lbd > 0);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self.clauses.alloc(lits, true, self.clause_inc, lbd);
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
    pub(crate) fn add_learnt_clause(&mut self, lits: &[Lit], lbd: u32) {
        debug_assert!(!lits.is_empty());
        debug_assert!(lbd > 0);
        telemetry::record_learnt_clause();

        match lits.len() {
            1 => {
                let _ = self.enqueue(lits[0], Reason::None);
            }
            2 => {
                self.attach_binary(lits[0], lits[1]);
                let _ = self.enqueue(lits[0], Reason::Binary(lits[0], lits[1]));
            }
            _ => {
                let cid = self.attach_learnt_long(lits, lbd);
                let _ = self.enqueue(lits[0], Reason::Clause(cid));
            }
        }
    }
}
