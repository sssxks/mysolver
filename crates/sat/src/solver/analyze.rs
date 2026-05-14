use crate::Lit;
use crate::clause_db::ClauseId;

use super::propagate::Conflict;
use super::{Reason, Solver};
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
    pub(crate) fn analyze(&mut self, conflict: Conflict, learnt: &mut Vec<Lit>) -> usize {
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
                    self.bump_clause_activity(cid);
                    let len = self.clauses.expect_live_header(cid).len();
                    for i in 0..len {
                        let q = self.clauses.expect_live_clause(cid).lit(i);
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

        backtrack_level
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
