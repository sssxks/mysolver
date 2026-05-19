use crate::Lit;
use crate::clause_db::ClauseId;

use super::propagate::Conflict;
use super::{AnalyzeSummary, Reason, Solver};
use crate::Var;

/// A clause-like source used during conflict analysis.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum AnalyzeSource {
    /// Treat a binary clause as an analysis source.
    Binary(Lit, Lit),
    /// Treat a long clause as an analysis source.
    Clause(ClauseId),
}

impl Solver {
    /// Performs first-UIP conflict analysis into a reusable learned-clause buffer.
    ///
    /// The caller-provided `learnt` buffer is cleared and then populated in asserting
    /// order: slot 0 is the asserting literal, and slot 1, when present, is the
    /// literal with the highest remaining decision level. The returned value is the
    /// backtrack level induced by that second watched position.
    pub(crate) fn analyze(&mut self, conflict: Conflict, learnt: &mut Vec<Lit>) -> AnalyzeSummary {
        let current_level = self.decision_level();
        learnt.clear();
        learnt.push(Lit::from_raw(0));

        let mut path_count = 0usize;
        let mut trail_idx = self.trail.len();
        let mut source = self.conflict_source(conflict);
        let mut resolved: Option<Var> = None;

        loop {
            match source {
                AnalyzeSource::Binary(a, b) => {
                    self.analyze_lit(a, resolved, current_level, &mut path_count, learnt);
                    self.analyze_lit(b, resolved, current_level, &mut path_count, learnt);
                }
                AnalyzeSource::Clause(cid) => {
                    self.note_clause_analysis(cid);
                    let len = self.clauses.header(cid).len();
                    for i in 0..len {
                        let q = self.clauses.clause(cid).lit(i);
                        self.analyze_lit(q, resolved, current_level, &mut path_count, learnt);
                    }
                }
            }

            let p = loop {
                trail_idx -= 1;
                let p = self.trail[trail_idx];
                if self.seen[p.var().index()] {
                    break p;
                }
            };

            let pv = p.var();
            self.seen[pv.index()] = false;
            path_count -= 1;

            if path_count == 0 {
                learnt[0] = !p;
                break;
            }

            resolved = Some(pv);
            source = match self.reason[pv.index()] {
                Reason::Binary(a, b) => AnalyzeSource::Binary(a, b),
                Reason::Clause(cid) => AnalyzeSource::Clause(cid),
                Reason::None => {
                    learnt[0] = !p;
                    break;
                }
            };
        }

        for v in self.analyze_stack.drain(..) {
            self.seen[v.index()] = false;
        }

        self.minimize_learnt_clause(learnt);
        let lbd = self.learnt_clause_lbd(learnt);

        let mut backtrack_level = 0usize;
        if learnt.len() > 1 {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[learnt[i].var().index()] > self.level[learnt[max_i].var().index()] {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            backtrack_level = self.level[learnt[1].var().index()];
        }

        AnalyzeSummary {
            backtrack_level,
            lbd,
        }
    }

    /// Accounts for one clause touched during conflict analysis.
    fn note_clause_analysis(&mut self, cid: ClauseId) {
        self.bump_clause_activity(cid);

        if !self.clauses.header(cid).is_learnt() {
            return;
        }

        let lbd = self.clause_lbd(cid);
        if lbd < self.clauses.lbd(cid) {
            self.clauses.set_lbd(cid, lbd);
        }
    }

    /// Removes learned literals whose reasons are already implied by the rest.
    fn minimize_learnt_clause(&mut self, learnt: &mut Vec<Lit>) {
        if learnt.len() <= 2 {
            return;
        }

        self.analyze_stack.clear();
        for &lit in learnt.iter() {
            let v = lit.var();
            let vi = v.index();
            if self.seen[vi] {
                continue;
            }
            self.seen[vi] = true;
            self.analyze_stack.push(v);
        }

        let mut out = 1usize;
        for i in 1..learnt.len() {
            let lit = learnt[i];
            if !self.literal_is_redundant(lit.var()) {
                learnt[out] = lit;
                out += 1;
            }
        }

        for v in self.analyze_stack.drain(..) {
            self.seen[v.index()] = false;
        }
        for v in self.minimize_touched.drain(..) {
            self.minimize_cache[v.index()] = 0;
        }

        learnt.truncate(out);
    }

    /// Returns whether one learned literal can be dropped without changing entailment.
    fn literal_is_redundant(&mut self, var: Var) -> bool {
        let vi = var.index();
        match self.minimize_cache[vi] {
            1 => return true,
            2 => return false,
            3 => return true,
            _ => {}
        }

        let ok = match self.reason[vi] {
            Reason::None => false,
            Reason::Binary(a, b) => {
                self.set_minimize_cache(var, 3);
                self.reason_literal_is_redundant(var, a) && self.reason_literal_is_redundant(var, b)
            }
            Reason::Clause(cid) => {
                self.set_minimize_cache(var, 3);
                let len = self.clauses.header(cid).len();
                let mut ok = true;
                for i in 0..len {
                    let q = self.clauses.clause(cid).lit(i);
                    if !self.reason_literal_is_redundant(var, q) {
                        ok = false;
                        break;
                    }
                }
                ok
            }
        };

        self.set_minimize_cache(var, if ok { 1 } else { 2 });
        ok
    }

    /// Tracks one redundancy memoization state for later cleanup.
    fn set_minimize_cache(&mut self, var: Var, state: u8) {
        let vi = var.index();
        if self.minimize_cache[vi] == 0 {
            self.minimize_touched.push(var);
        }
        self.minimize_cache[vi] = state;
    }

    /// Returns whether one antecedent literal is already covered by the learned clause.
    fn reason_literal_is_redundant(&mut self, current: Var, lit: Lit) -> bool {
        let antecedent = lit.var();
        if antecedent == current {
            return true;
        }

        let antecedent_index = antecedent.index();
        if self.level[antecedent_index] == 0 || self.seen[antecedent_index] {
            return true;
        }

        self.literal_is_redundant(antecedent)
    }

    /// Counts distinct decision levels in one minimized learned clause.
    fn learnt_clause_lbd(&mut self, learnt: &[Lit]) -> u32 {
        let epoch = self.next_lbd_epoch();
        let mut count = 0u32;

        for &lit in learnt {
            self.note_clause_level(epoch, self.level[lit.var().index()], &mut count);
        }

        count.max(1)
    }

    /// Counts distinct decision levels in one live clause currently stored in the arena.
    fn clause_lbd(&mut self, cid: ClauseId) -> u32 {
        let epoch = self.next_lbd_epoch();
        let mut count = 0u32;
        let len = self.clauses.header(cid).len();

        for i in 0..len {
            let lit = self.clauses.clause(cid).lit(i);
            self.note_clause_level(epoch, self.level[lit.var().index()], &mut count);
        }

        count.max(1)
    }

    /// Advances the per-analysis LBD epoch, clearing old stamps on overflow.
    fn next_lbd_epoch(&mut self) -> u32 {
        if self.lbd_epoch == u32::MAX {
            self.lbd_levels.fill(0);
            self.lbd_epoch = 1;
        } else {
            self.lbd_epoch += 1;
        }
        self.lbd_epoch
    }

    /// Records one decision level into the current LBD counter.
    fn note_clause_level(&mut self, epoch: u32, level: usize, count: &mut u32) {
        if level >= self.lbd_levels.len() {
            self.lbd_levels.resize(level + 1, 0);
        }
        if self.lbd_levels[level] != epoch {
            self.lbd_levels[level] = epoch;
            *count += 1;
        }
    }

    /// Converts a propagated conflict into a clause-like analysis source.
    fn conflict_source(&self, conflict: Conflict) -> AnalyzeSource {
        match conflict {
            Conflict::Binary(a, b) => AnalyzeSource::Binary(a, b),
            Conflict::Clause(cid) => AnalyzeSource::Clause(cid),
        }
    }

    /// Marks one analysis literal and records its contribution to the learned clause.
    fn analyze_lit(
        &mut self,
        q: Lit,
        resolved: Option<Var>,
        current_level: usize,
        path_count: &mut usize,
        learnt: &mut Vec<Lit>,
    ) {
        let v = q.var();
        if resolved == Some(v) {
            return;
        }
        let vi = v.index();
        if !self.seen[vi] && self.level[vi] > 0 {
            self.seen[vi] = true;
            self.analyze_stack.push(v);
            self.bump_var_activity(v);
            if self.level[vi] == current_level {
                *path_count += 1;
            } else {
                learnt.push(q);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Solver;
    use crate::{Lit, Var};

    fn lit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), false)
    }

    fn nlit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), true)
    }

    #[test]
    fn analyze_reports_distinct_decision_levels_as_lbd() {
        let mut solver = Solver::with_vars(7);

        assert!(solver.add_clause(&[nlit(0), lit(1)]));
        assert!(solver.add_clause(&[nlit(2), lit(3)]));
        assert!(solver.add_clause(&[nlit(4), lit(5)]));
        assert!(solver.add_clause(&[nlit(4), lit(6)]));
        assert!(solver.add_clause(&[nlit(1), nlit(3), nlit(5), nlit(6)]));

        solver.new_decision_level();
        assert!(solver.enqueue(lit(0), super::Reason::None));
        assert!(solver.propagate().is_none());

        solver.new_decision_level();
        assert!(solver.enqueue(lit(2), super::Reason::None));
        assert!(solver.propagate().is_none());

        solver.new_decision_level();
        assert!(solver.enqueue(lit(4), super::Reason::None));
        let conflict = solver.propagate().expect("expected long-clause conflict");

        let mut learnt = Vec::new();
        let summary = solver.analyze(conflict, &mut learnt);

        assert_eq!(summary.lbd, 3);
        assert_eq!(summary.backtrack_level, 2);
        assert_eq!(learnt[0], nlit(4));
        assert_eq!(learnt[1], nlit(3));
        assert!(learnt.contains(&nlit(1)));
    }
}
