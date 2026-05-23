use crate::clause_db::ClauseId;
use crate::telemetry;
use crate::{Lit, Var};

use super::{LBool, PopError, Reason, Solver};
use crate::AssertionLevel;

/// Learned clauses at or below this LBD stay in the protected core.
const CORE_LBD_CUTOFF: u32 = 2;

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
            self.sat_level[vi] = 0;
            self.user_level[vi] = AssertionLevel::ROOT;
            self.assigned_count -= 1;
            self.order.insert(v, &self.var_activity);
        }
        self.trail.truncate(keep);
        self.trail_lim.truncate(level);
        self.qhead = self.trail.len();
        self.theory_qhead = self.theory_qhead.min(self.trail.len());
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
        if !self.clauses.header(cid).is_learnt() {
            return;
        }

        let new_activity = self.clauses.activity(cid) + self.clause_inc;
        self.clauses.set_activity(cid, new_activity);

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

    /// Deletes every long clause that left scope after one user-level pop.
    pub(crate) fn delete_long_clauses_above_level(&mut self, level: AssertionLevel) {
        for cid in self.clauses.live_clauses_above_level(level) {
            self.delete_clause(cid);
        }
        self.learnts.retain(|&cid| self.clauses.is_live(cid));
    }

    /// Shrinks every variable-indexed array back to the live frame boundary.
    pub(crate) fn shrink_vars_to_frame_boundary(&mut self, new_level: AssertionLevel) {
        let vars_base = self.user_frames.last().map_or(0, |frame| {
            debug_assert_eq!(frame.level, new_level);
            frame.vars_base
        });
        self.truncate_vars(vars_base);
    }

    /// Resets transient CDCL search state while preserving root-level assignments.
    pub(crate) fn reset_search(&mut self) {
        self.cancel_until(0);
        self.theory_qhead = 0;
    }

    /// Pops back to one user assertion level.
    pub(crate) fn pop_to_assertion_level(
        &mut self,
        new_level: AssertionLevel,
    ) -> Result<(), PopError> {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert!(new_level <= self.assertion_level);

        self.assertion_level = new_level;
        if self
            .inconsistent_assertion_level
            .is_some_and(|level| level > new_level)
        {
            self.inconsistent_assertion_level = None;
            self.ok = true;
        }
        while self
            .user_frames
            .last()
            .is_some_and(|frame| frame.level > new_level)
        {
            self.user_frames.pop();
        }
        while self
            .trail
            .last()
            .is_some_and(|&lit| self.user_level[lit.var().index()] > new_level)
        {
            let lit = self.trail.pop().expect("checked above");
            let vi = lit.var().index();
            self.assigns[vi] = LBool::Undef;
            self.sat_level[vi] = 0;
            self.user_level[vi] = AssertionLevel::ROOT;
            self.reason[vi] = Reason::None;
            self.assigned_count -= 1;
        }
        self.qhead = self.trail.len();
        self.theory_qhead = self.theory_qhead.min(self.trail.len());

        self.delete_long_clauses_above_level(new_level);
        for watchers in &mut self.watches {
            watchers.retain(|watcher| match watcher {
                super::propagate::Watcher::Binary {
                    assertion_level, ..
                } => *assertion_level <= new_level,
                super::propagate::Watcher::Long { clause, .. } => {
                    self.clauses.is_live(*clause)
                        && self.clauses.header(*clause).assertion_level() <= new_level
                }
            });
        }

        self.shrink_vars_to_frame_boundary(new_level);
        Ok(())
    }

    /// Truncates every variable-indexed structure to `new_nvars` and rebuilds the heap.
    fn truncate_vars(&mut self, new_nvars: usize) {
        if new_nvars >= self.nvars {
            return;
        }
        self.nvars = new_nvars;
        self.assigns.truncate(new_nvars);
        self.sat_level.truncate(new_nvars);
        self.user_level.truncate(new_nvars);
        self.reason.truncate(new_nvars);
        self.intro_level.truncate(new_nvars);
        self.phase.truncate(new_nvars);
        self.var_activity.truncate(new_nvars);
        self.seen.truncate(new_nvars);
        self.minimize_cache.truncate(new_nvars);
        self.watches.truncate(new_nvars * 2);
        self.rebuild_order_heap();
    }

    /// Rebuilds the decision heap from the current assignment state.
    fn rebuild_order_heap(&mut self) {
        let mut order = crate::heap::VarHeap::new();
        for _ in 0..self.nvars {
            order.new_var();
        }
        for vi in 0..self.nvars {
            if self.assigns[vi] == LBool::Undef {
                order.insert(crate::Var::from_index(vi), &self.var_activity);
            }
        }
        self.order = order;
    }

    /// Deletes the least useful half of removable learned clauses.
    pub(crate) fn reduce_db(&mut self) {
        if self.learnts.len() < 128 {
            return;
        }
        telemetry::record_reduction();

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
            let cid = learnts[removable];
            let protected =
                locked[self.clauses.live_slot(cid)] || self.clauses.lbd(cid) <= CORE_LBD_CUTOFF;
            if protected {
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
                self.clauses.lbd(b).cmp(&self.clauses.lbd(a)).then_with(|| {
                    self.clauses
                        .activity(a)
                        .total_cmp(&self.clauses.activity(b))
                })
            });

            for &cid in &learnts[..remove] {
                self.delete_clause(cid);
            }
            telemetry::record_deleted_clauses(remove);
        }

        learnts.retain(|&cid| self.clauses.is_live(cid));
        self.learnts = learnts;
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "telemetry")]
    use super::CORE_LBD_CUTOFF;
    #[cfg(feature = "telemetry")]
    use super::Reason;
    #[cfg(feature = "telemetry")]
    use super::Solver;
    #[cfg(feature = "telemetry")]
    use crate::AssertionLevel;
    #[cfg(feature = "telemetry")]
    use crate::telemetry;
    #[cfg(feature = "telemetry")]
    use crate::{Lit, Var};

    #[cfg(feature = "telemetry")]
    fn lit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), false)
    }

    #[cfg(feature = "telemetry")]
    fn nlit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), true)
    }

    #[cfg(feature = "telemetry")]
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

    #[cfg(feature = "telemetry")]
    #[test]
    fn delete_clause_leaves_stale_watchers_for_lazy_cleanup() {
        let mut solver = Solver::with_vars(5);
        telemetry::initialize_solver_gauges(0, 0);
        let dead = solver.attach_learnt_long(&[lit(0), lit(1), lit(2)], 4, AssertionLevel::ROOT);
        solver.delete_clause(dead);
        let replacement =
            solver.attach_learnt_long(&[lit(0), lit(3), lit(4)], 3, AssertionLevel::ROOT);

        assert_eq!(dead.slot(), replacement.slot());
        assert_ne!(dead, replacement);
        assert_eq!(long_watch_count(&solver, lit(0), dead), 1);
        assert_eq!(long_watch_count(&solver, lit(1), dead), 1);
        assert_eq!(long_watch_count(&solver, lit(0), replacement), 1);
        assert_eq!(telemetry::watcher_entries(), 4);

        assert!(solver.enqueue(nlit(0), Reason::None));
        assert!(solver.propagate().is_none());

        assert_eq!(long_watch_count(&solver, lit(0), dead), 0);
        assert_eq!(long_watch_count(&solver, lit(1), dead), 1);
        assert!(solver.clauses.is_live(replacement));
        assert_eq!(telemetry::watcher_entries(), 3);
    }

    #[cfg(feature = "telemetry")]
    #[test]
    fn reduce_db_keeps_low_lbd_core_clauses() {
        let mut solver = Solver::with_vars(3 * 128);
        telemetry::initialize_solver_gauges(0, 0);

        let core = solver.attach_learnt_long(
            &[lit(0), lit(1), lit(2)],
            CORE_LBD_CUTOFF,
            AssertionLevel::ROOT,
        );
        solver.clauses.set_activity(core, 0.01);

        for clause_idx in 1..128usize {
            let base = clause_idx * 3;
            let cid = solver.attach_learnt_long(
                &[lit(base), lit(base + 1), lit(base + 2)],
                CORE_LBD_CUTOFF + 4,
                AssertionLevel::ROOT,
            );
            solver.clauses.set_activity(cid, 100.0 + clause_idx as f32);
        }

        solver.reduce_db();

        assert!(solver.clauses.is_live(core));
        assert!(
            solver
                .learnts
                .iter()
                .all(|&cid| solver.clauses.is_live(cid))
        );
        assert!(solver.learnts.len() < 128);
    }
}
