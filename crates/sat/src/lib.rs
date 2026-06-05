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

pub(crate) use dimacs::parse_dimacs;
pub use solver::{
    AddClauseResult, PopError, SatResult, Solver, Theory, TheoryClause, TheoryClauseKind,
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
}
