use std::mem;

use crate::Lit;
use crate::clause_db::ClauseId;

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
        let Some(mut ps) = self.prepare_clause(lits) else {
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
                self.attach_long(mem::take(&mut ps), false);
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
    }

    /// Stores and watches a long clause, optionally marking it as learned.
    pub(crate) fn attach_long(&mut self, lits: Vec<Lit>, learnt: bool) -> ClauseId {
        debug_assert!(lits.len() >= 3);
        let w0 = lits[0];
        let w1 = lits[1];
        let activity = if learnt { self.clause_inc } else { 0.0 };
        let cid = self.clauses.alloc(&lits, learnt, activity);
        self.watches[w0.index()].push(Watcher::Long {
            clause: cid,
            blocker: w1,
        });
        self.watches[w1.index()].push(Watcher::Long {
            clause: cid,
            blocker: w0,
        });
        if learnt {
            self.learnts.push(cid);
        }
        cid
    }

    /// Inserts a learned clause and enqueues its asserting literal.
    pub(crate) fn add_learnt_clause(&mut self, mut lits: Vec<Lit>) {
        debug_assert!(!lits.is_empty());
        if lits.len() > 1 {
            let mut max_i = 1;
            for i in 2..lits.len() {
                if self.level[lits[i].var().index()] > self.level[lits[max_i].var().index()] {
                    max_i = i;
                }
            }
            lits.swap(1, max_i);
        }

        match lits.len() {
            1 => {
                let _ = self.enqueue(lits[0], Reason::None);
            }
            2 => {
                self.attach_binary(lits[0], lits[1]);
                let _ = self.enqueue(lits[0], Reason::Binary(lits[0], lits[1]));
            }
            _ => {
                let cid = self.attach_long(lits, true);
                let lit = self.clauses.clause(cid).lit(0);
                let _ = self.enqueue(lit, Reason::Clause(cid));
            }
        }
    }
}
