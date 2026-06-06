//! A small conflict-driven clause learning SAT solver.
//!
//! The crate exposes a [`Solver`] for programmatic construction of CNF formulas and
//! a [`parse_dimacs`] helper for loading formulas from DIMACS CNF text.

/// Internal long-clause storage primitives.
mod clause_db;
/// DIMACS CNF parsing.
mod dimacs;
/// Variable-activity heap utilities.
mod heap;
/// CDCL solver state and search algorithms.
mod solver;
/// Low-overhead telemetry adapters shared with the standalone telemetry crate.
pub mod telemetry;
/// Core SAT value types.
mod types;

pub use dimacs::parse_dimacs;
pub use solver::{
    AddClauseResult, NullTheory, PopError, SatResult, Solver, Theory, TheoryClause,
    TheoryClauseKind,
};
pub use types::{AssertionLevel, Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct NoopTheory;

    impl Theory for NoopTheory {
        fn notify_search_start(&mut self) {}

        fn notify_new_decision_level(&mut self) {}

        fn notify_assignment(&mut self, _lit: Lit) {}

        fn notify_backtrack(&mut self, _level: usize) {}

        fn drain_clauses(&mut self, _out: &mut Vec<TheoryClause>) {}

        fn final_check(&mut self, _out: &mut Vec<TheoryClause>) {}

        fn has_pending_work(&self) -> bool {
            false
        }
    }

    struct ImplicationConflictTheory {
        premise: Lit,
        propagated: Lit,
        saw_premise: bool,
        emitted_implication: bool,
        emitted_conflict: bool,
    }

    impl Theory for ImplicationConflictTheory {
        fn notify_search_start(&mut self) {
            self.saw_premise = false;
            self.emitted_implication = false;
            self.emitted_conflict = false;
        }

        fn notify_new_decision_level(&mut self) {}

        fn notify_assignment(&mut self, lit: Lit) {
            if lit == self.premise {
                self.saw_premise = true;
            }
        }

        fn notify_backtrack(&mut self, level: usize) {
            if level == 0 {
                self.saw_premise = false;
                self.emitted_implication = false;
                self.emitted_conflict = false;
            }
        }

        fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>) {
            if self.saw_premise && !self.emitted_implication {
                self.emitted_implication = true;
                out.push(TheoryClause {
                    lits: Box::from([!self.premise, self.propagated]),
                    assertion_level: AssertionLevel::ROOT,
                    kind: TheoryClauseKind::PropagationExplanation,
                });
            }
        }

        fn final_check(&mut self, out: &mut Vec<TheoryClause>) {
            if self.saw_premise && self.emitted_implication && !self.emitted_conflict {
                self.emitted_conflict = true;
                out.push(TheoryClause {
                    lits: Box::from([!self.propagated]),
                    assertion_level: AssertionLevel::ROOT,
                    kind: TheoryClauseKind::ConflictExplanation,
                });
            }
        }

        fn has_pending_work(&self) -> bool {
            self.saw_premise && !self.emitted_implication
        }
    }

    struct EmptyScopedConflictTheory {
        assertion_level: AssertionLevel,
        emitted: bool,
    }

    impl Theory for EmptyScopedConflictTheory {
        fn notify_search_start(&mut self) {}

        fn notify_new_decision_level(&mut self) {}

        fn notify_assignment(&mut self, _lit: Lit) {}

        fn notify_backtrack(&mut self, _level: usize) {}

        fn drain_clauses(&mut self, _out: &mut Vec<TheoryClause>) {}

        fn final_check(&mut self, out: &mut Vec<TheoryClause>) {
            if self.emitted {
                return;
            }
            self.emitted = true;
            out.push(TheoryClause {
                lits: Box::from([]),
                assertion_level: self.assertion_level,
                kind: TheoryClauseKind::ConflictExplanation,
            });
        }

        fn has_pending_work(&self) -> bool {
            false
        }
    }

    fn lit(v: Var) -> Lit {
        Lit::new(v, false)
    }

    fn nlit(v: Var) -> Lit {
        Lit::new(v, true)
    }

    #[test]
    fn unit_sat() {
        let mut s = Solver::new();
        let x = s.new_var();
        assert_eq!(s.add_clause(&[lit(x)]), AddClauseResult::Added);
        assert_eq!(s.solve(), SatResult::Sat);
        assert_eq!(s.value_lit_public(lit(x)), Some(true));
    }

    #[test]
    fn direct_unsat() {
        let mut s = Solver::new();
        let x = s.new_var();
        assert_eq!(s.add_clause(&[lit(x)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(x)]), AddClauseResult::Inconsistent);
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn xor_unsat() {
        let mut s = Solver::new();
        let a = s.new_var();
        let b = s.new_var();
        assert_eq!(s.add_clause(&[lit(a), lit(b)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(a), lit(b)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[lit(a), nlit(b)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(a), nlit(b)]), AddClauseResult::Added);
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn dimacs_sat() {
        let input = "p cnf 3 2\n1 -2 0\n2 3 0\n";
        let mut s = parse_dimacs(input).unwrap();
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn dimacs_accepts_satlib_end_marker() {
        let input = "p cnf 1 1\n1 0\n%\n0\n";
        let mut s = parse_dimacs(input).unwrap();
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn push_pop_shrinks_scoped_variables() {
        let mut s = Solver::new();
        s.push();
        let x = s.new_var();
        assert_eq!(s.current_assertion_level(), AssertionLevel::ROOT.next());
        assert_eq!(s.add_clause(&[lit(x)]), AddClauseResult::Added);
        assert_eq!(s.value_lit_public(lit(x)), Some(true));

        s.pop(1).expect("frame should exist");

        assert_eq!(s.current_assertion_level(), AssertionLevel::ROOT);
        assert_eq!(s.num_vars(), 0);
    }

    #[test]
    fn solve_with_assumptions_detects_conflicting_assumption() {
        let mut s = Solver::new();
        let x = s.new_var();
        assert_eq!(s.add_clause(&[lit(x)]), AddClauseResult::Added);

        let mut theory = NoopTheory;
        assert_eq!(
            s.solve_with_assumptions(&[nlit(x)], &mut theory),
            SatResult::Unsat
        );
    }

    #[test]
    fn add_clause_after_sat_resets_stale_search_assignment() {
        let mut s = Solver::new();
        let x = s.new_var();
        let y = s.new_var();
        assert_eq!(s.add_clause(&[lit(x), lit(y)]), AddClauseResult::Added);
        assert_eq!(s.solve(), SatResult::Sat);

        let model = s.model().expect("sat solve should expose one model");
        let opposite_x = if model[x.index()] { nlit(x) } else { lit(x) };

        assert_eq!(s.add_clause(&[opposite_x]), AddClauseResult::Added);
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn unit_theory_propagation_keeps_its_reason_clause() {
        let mut s = Solver::new();
        let premise = lit(s.new_var());
        let propagated = lit(s.new_var());
        let mut theory = ImplicationConflictTheory {
            premise,
            propagated,
            saw_premise: false,
            emitted_implication: false,
            emitted_conflict: false,
        };

        assert_eq!(s.solve_with_assumptions(&[], &mut theory), SatResult::Sat);
        assert_eq!(s.value_lit_public(premise), Some(false));
    }

    #[test]
    fn empty_theory_conflict_preserves_declared_scope() {
        let mut s = Solver::new();
        s.push();
        let scoped_level = s.current_assertion_level();
        let mut conflict_theory = EmptyScopedConflictTheory {
            assertion_level: scoped_level,
            emitted: false,
        };

        assert_eq!(
            s.solve_with_assumptions(&[], &mut conflict_theory),
            SatResult::Unsat
        );

        s.pop(1).expect("scoped conflict frame should exist");

        let mut noop = NoopTheory;
        assert_eq!(s.solve_with_assumptions(&[], &mut noop), SatResult::Sat);
    }

    #[test]
    fn root_long_propagation_conflict_survives_deeper_pop() {
        let mut s = Solver::new();
        let a = s.new_var();
        let b = s.new_var();
        let c = s.new_var();
        assert_eq!(
            s.add_clause(&[lit(a), lit(b), lit(c)]),
            AddClauseResult::Added
        );
        assert_eq!(s.add_clause(&[nlit(a)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(b)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(c)]), AddClauseResult::Added);

        s.push();
        let mut noop = NoopTheory;
        assert_eq!(s.solve_with_assumptions(&[], &mut noop), SatResult::Unsat);

        s.pop(1).expect("unrelated deeper frame should exist");

        assert_eq!(s.solve_with_assumptions(&[], &mut noop), SatResult::Unsat);
    }

    #[test]
    fn scoped_root_assignments_do_not_make_root_clause_globally_unsat() {
        let mut s = Solver::new();
        let a = s.new_var();
        let b = s.new_var();
        let c = s.new_var();
        assert_eq!(
            s.add_clause(&[lit(a), lit(b), lit(c)]),
            AddClauseResult::Added
        );

        s.push();
        assert_eq!(s.add_clause(&[nlit(a)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(b)]), AddClauseResult::Added);
        assert_eq!(s.add_clause(&[nlit(c)]), AddClauseResult::Added);

        let mut noop = NoopTheory;
        assert_eq!(s.solve_with_assumptions(&[], &mut noop), SatResult::Unsat);

        s.pop(1).expect("scoped unit frame should exist");

        assert_eq!(s.solve_with_assumptions(&[], &mut noop), SatResult::Sat);
    }

    #[test]
    fn scoped_root_theory_premise_does_not_make_root_globally_unsat() {
        let mut s = Solver::new();
        let premise = lit(s.new_var());
        let propagated = lit(s.new_var());
        s.push();
        assert_eq!(s.add_clause(&[premise]), AddClauseResult::Added);
        let mut theory = ImplicationConflictTheory {
            premise,
            propagated,
            saw_premise: false,
            emitted_implication: false,
            emitted_conflict: false,
        };

        assert_eq!(s.solve_with_assumptions(&[], &mut theory), SatResult::Unsat);

        s.pop(1).expect("scoped premise frame should exist");

        assert_eq!(s.solve_with_assumptions(&[], &mut theory), SatResult::Sat);
    }
}
