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
            if !header.is_learnt() {
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

    /// Removes one long clause and recycles its database slot.
    ///
    /// Stale long-clause watchers are cleaned up lazily the next time their watched
    /// literal becomes false.
    fn delete_clause(&mut self, cid: ClauseId) {
        if !self.clauses.is_live(cid) {
            return;
        }

        self.clauses.delete(cid);
    }

    /// Deletes the least useful half of removable learned clauses.
    pub(crate) fn reduce_db(&mut self) {
        if self.learnts.len() < 128 {
            return;
        }

        let mut locked = vec![false; self.clauses.slot_count()];
        for &reason in &self.reason {
            if let Reason::Clause(cid) = reason {
                let slot = self.clauses.live_slot(cid);
                locked[slot] = true;
            }
        }

        let mut learnts = std::mem::take(&mut self.learnts);
        let mut removable = 0;
        let mut locked_start = learnts.len();
        while removable < locked_start {
            if locked[self.clauses.live_slot(learnts[removable])] {
                locked_start -= 1;
                learnts.swap(removable, locked_start);
            } else {
                removable += 1;
            }
        }

        let remove = removable / 2;
        if remove >= 2 {
            // `select_nth_unstable_by` requires a non-empty slice and does not help
            // when there is only one removable clause because `remove` stays zero.
            learnts[..removable].select_nth_unstable_by(remove, |&a, &b| {
                self.clauses
                    .header(a)
                    .activity()
                    .total_cmp(&self.clauses.header(b).activity())
            });

            for &cid in &learnts[..remove] {
                self.delete_clause(cid);
            }
        }

        learnts.retain(|&cid| self.clauses.is_live(cid));
        self.learnts = learnts;
    }
}

#[cfg(test)]
mod tests {
    use super::{Reason, Solver};
    use crate::{Lit, Var};

    fn lit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), false)
    }

    fn nlit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), true)
    }

    fn long_watch_count(solver: &Solver, watched: Lit, cid: crate::clause_db::ClauseId) -> usize {
        solver.watches[watched.index()]
            .iter()
            .filter(|watcher| {
                matches!(
                    watcher,
                    super::super::propagate::Watcher::Long { clause, .. } if *clause == cid
                )
            })
            .count()
    }

    #[test]
    fn delete_clause_leaves_stale_watchers_for_lazy_cleanup() {
        let mut solver = Solver::with_vars(5);
        let dead = solver.attach_long(&[lit(0), lit(1), lit(2)], true);
        solver.delete_clause(dead);
        let replacement = solver.attach_long(&[lit(0), lit(3), lit(4)], true);

        assert_eq!(dead.slot(), replacement.slot());
        assert_ne!(dead, replacement);
        assert_eq!(long_watch_count(&solver, lit(0), dead), 1);
        assert_eq!(long_watch_count(&solver, lit(1), dead), 1);
        assert_eq!(long_watch_count(&solver, lit(0), replacement), 1);

        assert!(solver.enqueue(nlit(0), Reason::None));
        assert!(solver.propagate().is_none());

        assert_eq!(long_watch_count(&solver, lit(0), dead), 0);
        assert_eq!(long_watch_count(&solver, lit(1), dead), 1);
        assert!(solver.clauses.is_live(replacement));
    }
}
