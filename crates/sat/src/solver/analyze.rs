use crate::{Level, Lit};
use crate::Var;
use crate::clause_db::ClauseId;

use super::propagate::Conflict;
use super::{AnalyzeSummary, Reason, Solver};
use crate::Scope;

/// A clause-like source used during conflict analysis.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum AnalyzeSource<'a> {
    /// Treat an inline binary clause as an analysis source.
    Binary {
        /// The literal that was false when the clause became active.
        false_lit: Lit,
        /// The propagated or conflicting counterpart literal.
        other: Lit,
        /// Scope in which this binary clause exists.
        scope: Scope,
    },
    /// Treat a long clause as an analysis source.
    Clause(ClauseId),
    /// Treat one unstored theory explanation clause as an analysis source.
    TheoryClause {
        /// The falsified theory clause literals.
        lits: &'a [Lit],
        /// Scope carried by the theory explanation.
        scope: Scope,
    },
    /// Treat one transient theory reason stored by the solver as an analysis
    /// source.
    TheoryReason(usize),
}

impl Solver {
    /// Performs first-UIP conflict analysis into a reusable learned-clause buffer.
    ///
    /// The caller-provided `learnt` buffer is cleared and then populated in asserting
    /// order: slot 0 is the asserting literal, and slot 1, when present, is the
    /// literal with the highest remaining level.
    pub(crate) fn analyze(&mut self, conflict: Conflict, learnt: &mut Vec<Lit>) -> AnalyzeSummary {
        self.analyze_from_source(self.conflict_source(conflict), learnt)
    }

    /// Performs first-UIP conflict analysis starting from one theory clause that
    /// is already falsified under the current assignment.
    pub(crate) fn analyze_theory_clause(
        &mut self,
        lits: &[Lit],
        scope: Scope,
        learnt: &mut Vec<Lit>,
    ) -> AnalyzeSummary {
        self.analyze_from_source(AnalyzeSource::TheoryClause { lits, scope }, learnt)
    }

    /// Shared first-UIP conflict analysis entry point for propagator and theory sources.
    fn analyze_from_source(
        &mut self,
        mut source: AnalyzeSource<'_>,
        learnt: &mut Vec<Lit>,
    ) -> AnalyzeSummary {
        let current_level = self.level();
        let mut required_scope = Scope::ROOT;
        learnt.clear();
        learnt.push(Lit::from_raw(0));

        let mut path_count = 0usize;
        let mut trail_idx = self.trail.len();
        let mut resolved: Option<Var> = None;

        loop {
            match source {
                AnalyzeSource::Binary {
                    false_lit,
                    other,
                    scope,
                } => {
                    required_scope = required_scope.max(scope);
                    self.analyze_lit(
                        false_lit,
                        resolved,
                        current_level,
                        &mut path_count,
                        &mut required_scope,
                        learnt,
                    );
                    self.analyze_lit(
                        other,
                        resolved,
                        current_level,
                        &mut path_count,
                        &mut required_scope,
                        learnt,
                    );
                }
                AnalyzeSource::Clause(cid) => {
                    self.note_clause_analysis(cid);
                    required_scope = required_scope.max(self.clauses.header(cid).scope());
                    let len = self.clauses.header(cid).len();
                    for i in 0..len {
                        let q = self.clauses.clause(cid).lit(i);
                        self.analyze_lit(
                            q,
                            resolved,
                            current_level,
                            &mut path_count,
                            &mut required_scope,
                            learnt,
                        );
                    }
                }
                AnalyzeSource::TheoryClause { lits, scope } => {
                    required_scope = required_scope.max(scope);
                    for &q in lits {
                        self.analyze_lit(
                            q,
                            resolved,
                            current_level,
                            &mut path_count,
                            &mut required_scope,
                            learnt,
                        );
                    }
                }
                AnalyzeSource::TheoryReason(id) => {
                    let reason = self.theory_reasons[id];
                    required_scope = required_scope.max(reason.scope);
                    for i in reason.range() {
                        let q = self.theory_reason_lits[i];
                        self.analyze_lit(
                            q,
                            resolved,
                            current_level,
                            &mut path_count,
                            &mut required_scope,
                            learnt,
                        );
                    }
                }
            }

            let p = loop {
                if trail_idx == 0 {
                    panic!(
                        "conflict analysis ran out of earlier marked literals; reason sources must precede propagated literals on the trail"
                    );
                }
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
                Reason::Binary {
                    false_lit,
                    other,
                    scope,
                } => AnalyzeSource::Binary {
                    false_lit,
                    other,
                    scope,
                },
                Reason::Clause(cid) => AnalyzeSource::Clause(cid),
                Reason::Theory(id) => AnalyzeSource::TheoryReason(id),
                Reason::None => {
                    learnt[0] = !p;
                    break;
                }
            };
        }

        for v in self.analyze_stack.drain(..) {
            self.seen[v.index()] = false;
        }

        self.minimize_learnt_clause(learnt, &mut required_scope);
        let lbd = self.learnt_clause_lbd(learnt);

        let mut backtrack_level = Level::ROOT;
        if learnt.len() > 1 {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[learnt[i].var().index()]
                    > self.level[learnt[max_i].var().index()]
                {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            backtrack_level = self.level[learnt[1].var().index()];
        }

        AnalyzeSummary {
            backtrack_level,
            scope: required_scope,
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
    fn minimize_learnt_clause(&mut self, learnt: &mut Vec<Lit>, required_scope: &mut Scope) {
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
            let (redundant, scope) = self.literal_is_redundant(lit.var());
            if redundant {
                *required_scope = (*required_scope).max(scope);
            } else {
                learnt[out] = lit;
                out += 1;
            }
        }

        for v in self.analyze_stack.drain(..) {
            self.seen[v.index()] = false;
        }
        for v in self.minimize_touched.drain(..) {
            self.minimize_cache[v.index()] = 0;
            self.minimize_scope_cache[v.index()] = Scope::ROOT;
        }

        learnt.truncate(out);
    }

    /// Returns whether one learned literal can be dropped without changing entailment.
    fn literal_is_redundant(&mut self, var: Var) -> (bool, Scope) {
        let vi = var.index();
        match self.minimize_cache[vi] {
            1 => return (true, self.minimize_scope_cache[vi]),
            2 => return (false, Scope::ROOT),
            3 => return (true, Scope::ROOT),
            _ => {}
        }

        let (ok, scope) = match self.reason[vi] {
            Reason::None => (false, Scope::ROOT),
            Reason::Binary {
                false_lit,
                other,
                scope,
            } => {
                self.set_minimize_cache(var, 3);
                let mut scope = scope;
                let false_lit_ok = self.reason_literal_is_redundant(var, false_lit, &mut scope);
                let other_ok = self.reason_literal_is_redundant(var, other, &mut scope);
                (false_lit_ok && other_ok, scope)
            }
            Reason::Clause(cid) => {
                self.set_minimize_cache(var, 3);
                let header = self.clauses.header(cid);
                let len = header.len();
                let mut scope = header.scope();
                let mut ok = true;
                for i in 0..len {
                    let q = self.clauses.clause(cid).lit(i);
                    if !self.reason_literal_is_redundant(var, q, &mut scope) {
                        ok = false;
                        break;
                    }
                }
                (ok, scope)
            }
            Reason::Theory(id) => {
                self.set_minimize_cache(var, 3);
                let reason = self.theory_reasons[id];
                let mut scope = reason.scope;
                let mut ok = true;
                for i in reason.range() {
                    let q = self.theory_reason_lits[i];
                    if !self.reason_literal_is_redundant(var, q, &mut scope) {
                        ok = false;
                        break;
                    }
                }
                (ok, scope)
            }
        };

        self.set_minimize_cache(var, if ok { 1 } else { 2 });
        self.minimize_scope_cache[vi] = if ok { scope } else { Scope::ROOT };
        (ok, scope)
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
    fn reason_literal_is_redundant(&mut self, current: Var, lit: Lit, scope: &mut Scope) -> bool {
        let antecedent = lit.var();
        if antecedent == current {
            return true;
        }

        let antecedent_index = antecedent.index();
        if self.level[antecedent_index] == Level::ROOT {
            *scope = (*scope).max(self.assignment_scope[antecedent_index]);
            return true;
        }

        if self.seen[antecedent_index] {
            return true;
        }

        let (redundant, antecedent_scope) = self.literal_is_redundant(antecedent);
        if redundant {
            *scope = (*scope).max(antecedent_scope);
        }
        redundant
    }

    /// Counts distinct levels in one minimized learned clause.
    fn learnt_clause_lbd(&mut self, learnt: &[Lit]) -> u32 {
        let epoch = self.next_lbd_epoch();
        let mut count = 0u32;

        for &lit in learnt {
            self.note_clause_level(epoch, self.level[lit.var().index()], &mut count);
        }

        count.max(1)
    }

    /// Counts distinct levels in one live clause currently stored in the arena.
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

    /// Records one level into the current LBD counter.
    fn note_clause_level(&mut self, epoch: u32, level: Level, count: &mut u32) {
        let index = level.index();
        if index >= self.lbd_levels.len() {
            self.lbd_levels.resize(index + 1, 0);
        }
        if self.lbd_levels[index] != epoch {
            self.lbd_levels[index] = epoch;
            *count += 1;
        }
    }

    /// Converts a propagated conflict into a clause-like analysis source.
    fn conflict_source(&self, conflict: Conflict) -> AnalyzeSource<'static> {
        match conflict {
            Conflict::Binary {
                false_lit,
                other,
                scope,
            } => AnalyzeSource::Binary {
                false_lit,
                other,
                scope,
            },
            Conflict::Clause(cid) => AnalyzeSource::Clause(cid),
        }
    }

    /// Marks one analysis literal and records its contribution to the learned clause.
    fn analyze_lit(
        &mut self,
        q: Lit,
        resolved: Option<Var>,
        current_level: Level,
        path_count: &mut usize,
        required_scope: &mut Scope,
        learnt: &mut Vec<Lit>,
    ) {
        let v = q.var();
        if resolved == Some(v) {
            return;
        }
        let vi = v.index();
        if self.level[vi] == Level::ROOT {
            *required_scope = (*required_scope).max(self.assignment_scope[vi]);
        }
        if !self.seen[vi] && self.level[vi] > Level::ROOT {
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
    use crate::{AddClauseResult, Level, Lit, Scope, TheoryClause, TheoryClauseKind, Var};

    fn lit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), false)
    }

    fn nlit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), true)
    }

    #[test]
    fn unit_theory_propagation_keeps_its_reason_clause() {
        let mut solver = Solver::with_vars(3);
        let premise = lit(0);
        let left = lit(1);
        let right = lit(2);

        solver.new_level();
        assert!(solver.enqueue(premise, super::Reason::None));

        for propagated in [left, right] {
            let clause = TheoryClause {
                lits: Box::from([!premise, propagated]),
                scope: Scope::ROOT,
                kind: TheoryClauseKind::PropagationExplanation,
            };
            let crate::solver::add::ClassifiedTheoryClause::Unit {
                lits,
                unit_index,
                scope,
            } = solver.classify_theory_clause(&clause)
            else {
                panic!("premise should make the theory explanation unit");
            };
            assert_eq!(
                solver.insert_unit_theory_clause(lits, unit_index, scope),
                AddClauseResult::Added
            );
            assert!(
                matches!(
                    solver.reason[propagated.var().index()],
                    super::Reason::Theory(_)
                ),
                "non-root theory propagation must retain its explanation as the assignment reason"
            );
        }

        let mut learnt = Vec::new();
        let summary = solver.analyze_theory_clause(&[!left, !right], Scope::ROOT, &mut learnt);

        assert_eq!(learnt, [!premise]);
        assert_eq!(summary.backtrack_level, Level::ROOT);
        assert_eq!(summary.scope, Scope::ROOT);
    }

    #[test]
    fn analyze_reports_distinct_levels_as_lbd() {
        let mut solver = Solver::with_vars(7);

        assert_eq!(
            solver.add_clause(&[nlit(0), lit(1)]),
            AddClauseResult::Added
        );
        assert_eq!(
            solver.add_clause(&[nlit(2), lit(3)]),
            AddClauseResult::Added
        );
        assert_eq!(
            solver.add_clause(&[nlit(4), lit(5)]),
            AddClauseResult::Added
        );
        assert_eq!(
            solver.add_clause(&[nlit(4), lit(6)]),
            AddClauseResult::Added
        );
        assert_eq!(
            solver.add_clause(&[nlit(1), nlit(3), nlit(5), nlit(6)]),
            AddClauseResult::Added
        );

        solver.new_level();
        assert!(solver.enqueue(lit(0), super::Reason::None));
        assert!(solver.propagate().is_none());

        solver.new_level();
        assert!(solver.enqueue(lit(2), super::Reason::None));
        assert!(solver.propagate().is_none());

        solver.new_level();
        assert!(solver.enqueue(lit(4), super::Reason::None));
        let conflict = solver.propagate().expect("expected long-clause conflict");

        let mut learnt = Vec::new();
        let summary = solver.analyze(conflict, &mut learnt);

        assert_eq!(summary.lbd, 3);
        assert_eq!(summary.backtrack_level, Level::from_index(2));
        assert_eq!(learnt[0], nlit(4));
        assert_eq!(learnt[1], nlit(3));
        assert!(learnt.contains(&nlit(1)));
    }
}
