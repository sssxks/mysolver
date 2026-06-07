use crate::clause_db::ClauseId;
use crate::telemetry;
use crate::{Level, Literal, Var};

use super::{PopError, Reason, Solver, TruthValue};
use crate::Scope;

/// Learned clauses at or below this LBD stay in the protected core.
const CORE_LBD_CUTOFF: u32 = 2;

impl Solver {
    /// Starts a new level at the current trail position.
    pub(crate) fn new_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    /// Backtracks to `level`, undoing assignments above it.
    pub(crate) fn cancel_until(&mut self, level: Level) {
        if self.level() <= level {
            if level == Level::ROOT {
                self.theory_reason_lits.clear();
                self.theory_reasons.clear();
            }
            return;
        }
        let keep = self.trail_lim[level.index()];
        for i in (keep..self.trail.len()).rev() {
            let lit = self.trail[i];
            let v = lit.var();
            let vi = v.index();
            self.assigns[vi] = TruthValue::Unknown;
            self.reason[vi] = Reason::None;
            self.level[vi] = Level::ROOT;
            self.assignment_scope[vi] = Scope::ROOT;
            self.assigned_count -= 1;
            self.order.insert(v, &self.var_activity);
        }
        self.trail.truncate(keep);
        self.trail_lim.truncate(level.index());
        self.qhead = self.trail.len();
        self.theory_qhead = self.theory_qhead.min(self.trail.len());
        if level == Level::ROOT {
            self.theory_reason_lits.clear();
            self.theory_reasons.clear();
        }
    }

    /// Picks the next unassigned branching literal according to activity and phase.
    pub(crate) fn pick_branch_lit(&mut self) -> Option<Literal> {
        while let Some(v) = self.order.pop_max(&self.var_activity) {
            if self.assigns[v.index()] == TruthValue::Unknown {
                return Some(Literal::new(v, !self.phase[v.index()]));
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

    /// Deletes every long clause that left scope after one pop.
    fn delete_long_clauses_above_scope(&mut self, scope: Scope) {
        for cid in self.clauses.live_clauses_above_scope(scope) {
            self.delete_clause(cid);
        }
        self.learnts.retain(|&cid| self.clauses.is_live(cid));
    }

    /// Shrinks every variable-indexed array back to the live frame boundary.
    fn shrink_vars_to_frame_boundary(&mut self, new_scope: Scope) {
        let vars_base = self.scope_frames.last().map_or(0, |frame| {
            debug_assert_eq!(frame.scope, new_scope);
            frame.vars_base
        });
        self.truncate_vars(vars_base);
    }

    /// Resets transient CDCL search state while preserving root-level assignments.
    pub(crate) fn reset_search(&mut self) {
        self.cancel_until(Level::ROOT);
        self.theory_qhead = 0;
    }

    /// Pops back to one assertion-stack scope.
    pub(crate) fn pop_to_scope(&mut self, new_scope: Scope) -> Result<(), PopError> {
        debug_assert_eq!(self.level(), Level::ROOT);
        debug_assert!(new_scope <= self.current_scope);

        self.current_scope = new_scope;
        if self
            .inconsistent_scope
            .is_some_and(|scope| scope > new_scope)
        {
            self.inconsistent_scope = None;
        }
        while self
            .scope_frames
            .last()
            .is_some_and(|frame| frame.scope > new_scope)
        {
            self.scope_frames.pop();
        }
        while self
            .trail
            .last()
            .is_some_and(|&lit| self.assignment_scope[lit.var().index()] > new_scope)
        {
            let lit = self.trail.pop().expect("checked above");
            let vi = lit.var().index();
            self.assigns[vi] = TruthValue::Unknown;
            self.level[vi] = Level::ROOT;
            self.assignment_scope[vi] = Scope::ROOT;
            self.reason[vi] = Reason::None;
            self.assigned_count -= 1;
        }
        self.qhead = self.trail.len();
        self.theory_qhead = self.theory_qhead.min(self.trail.len());

        self.delete_long_clauses_above_scope(new_scope);
        for watchers in &mut self.watches {
            watchers.retain(|watcher| match watcher {
                super::propagate::Watcher::Binary { scope, .. } => *scope <= new_scope,
                super::propagate::Watcher::Long { clause, .. } => {
                    self.clauses.is_live(*clause)
                        && self.clauses.header(*clause).scope() <= new_scope
                }
            });
        }

        self.shrink_vars_to_frame_boundary(new_scope);
        Ok(())
    }

    /// Truncates every variable-indexed structure to `new_nvars` and rebuilds the heap.
    fn truncate_vars(&mut self, new_nvars: usize) {
        if new_nvars >= self.nvars {
            return;
        }
        self.nvars = new_nvars;
        self.assigns.truncate(new_nvars);
        self.level.truncate(new_nvars);
        self.assignment_scope.truncate(new_nvars);
        self.reason.truncate(new_nvars);
        self.variable_scope.truncate(new_nvars);
        self.phase.truncate(new_nvars);
        self.var_activity.truncate(new_nvars);
        self.seen.truncate(new_nvars);
        self.minimize_cache.truncate(new_nvars);
        self.minimize_scope_cache.truncate(new_nvars);
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
            if self.assigns[vi] == TruthValue::Unknown {
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
    use crate::Scope;
    #[cfg(feature = "telemetry")]
    use crate::clause_db::ClauseId;
    #[cfg(feature = "telemetry")]
    use crate::telemetry;
    #[cfg(feature = "telemetry")]
    use crate::{Literal, Var};

    #[cfg(feature = "telemetry")]
    fn lit(index: usize) -> Literal {
        Literal::new(Var::from_index(index), false)
    }

    #[cfg(feature = "telemetry")]
    fn nlit(index: usize) -> Literal {
        Literal::new(Var::from_index(index), true)
    }

    #[cfg(feature = "telemetry")]
    fn long_watch_count(solver: &Solver, watched: Literal, cid: ClauseId) -> usize {
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
        let dead = solver.attach_learnt_long(&[lit(0), lit(1), lit(2)], 4, Scope::ROOT);
        solver.delete_clause(dead);
        let replacement = solver.attach_learnt_long(&[lit(0), lit(3), lit(4)], 3, Scope::ROOT);

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

        let core =
            solver.attach_learnt_long(&[lit(0), lit(1), lit(2)], CORE_LBD_CUTOFF, Scope::ROOT);
        solver.clauses.set_activity(core, 0.01);

        for clause_idx in 1..128usize {
            let base = clause_idx * 3;
            let cid = solver.attach_learnt_long(
                &[lit(base), lit(base + 1), lit(base + 2)],
                CORE_LBD_CUTOFF + 4,
                Scope::ROOT,
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
