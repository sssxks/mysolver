use std::cmp::Ordering;

use crate::clause_db::ClauseId;
use crate::{Lit, Var};

use super::{LBool, Reason, Solver};

impl Solver {
    /// Starts a new decision level at the current trail position.
    pub(crate) fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    /// Backtracks to `level`, undoing assignments above it.
    pub(crate) fn cancel_until(&mut self, level: usize) {
        if self.decision_level() <= level {
            return;
        }
        let keep = self.trail_lim[level];
        for i in (keep..self.trail.len()).rev() {
            let lit = self.trail[i];
            let v = lit.var();
            let vi = v.index();
            self.assigns[vi] = LBool::Undef;
            self.reason[vi] = Reason::None;
            self.level[vi] = 0;
            self.assigned_count -= 1;
            self.order.insert(v, &self.var_activity);
        }
        self.trail.truncate(keep);
        self.trail_lim.truncate(level);
        self.qhead = self.trail.len();
    }

    /// Picks the next unassigned branching literal according to activity and phase.
    pub(crate) fn pick_branch_lit(&mut self) -> Option<Lit> {
        while let Some(v) = self.order.pop_max(&self.var_activity) {
            if self.assigns[v.index()] == LBool::Undef {
                return Some(Lit::new(v, !self.phase[v.index()]));
            }
        }
        None
    }

    /// Increases the activity score of `v` and updates heap order.
    pub(crate) fn bump_var_activity(&mut self, v: Var) {
        let vi = v.index();
        self.var_activity[vi] += self.var_inc;
        if self.var_activity[vi] > 1e100 {
            for a in &mut self.var_activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.order.increase(v, &self.var_activity);
    }

    /// Applies variable activity decay for future bumps.
    pub(crate) fn var_decay_activity(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    /// Increases the activity score of a learned clause.
    pub(crate) fn bump_clause_activity(&mut self, cid: ClauseId) {
        let new_activity = {
            let header = self.clauses.header_mut(cid);
            if !header.is_learnt() || header.is_deleted() {
                return;
            }
            let new_activity = header.activity() + self.clause_inc;
            header.set_activity(new_activity);
            new_activity
        };

        if new_activity > 1e20 {
            self.clauses.scale_activities(1e-20);
            self.clause_inc *= 1e-20;
        }
    }

    /// Applies clause activity decay for future bumps.
    pub(crate) fn clause_decay_activity(&mut self) {
        self.clause_inc *= 1.0 / self.clause_decay;
    }

    /// Deletes the least useful half of removable learned clauses.
    pub(crate) fn reduce_db(&mut self) {
        if self.learnts.len() < 128 {
            return;
        }

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reason {
            if let Reason::Clause(cid) = reason {
                locked[cid.index()] = true;
            }
        }

        let mut candidates: Vec<ClauseId> = self
            .learnts
            .iter()
            .copied()
            .filter(|&cid| {
                let header = self.clauses.header(cid);
                !header.is_deleted() && header.len() > 2 && !locked[cid.index()]
            })
            .collect();

        candidates.sort_by(|&a, &b| {
            self.clauses
                .header(a)
                .activity()
                .partial_cmp(&self.clauses.header(b).activity())
                .unwrap_or(Ordering::Equal)
        });

        let remove = candidates.len() / 2;
        for cid in candidates.into_iter().take(remove) {
            self.clauses.header_mut(cid).set_deleted(true);
        }

        self.learnts
            .retain(|&cid| !self.clauses.header(cid).is_deleted());
    }
}
