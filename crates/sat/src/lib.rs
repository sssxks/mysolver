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
/// Core SAT value types.
mod types;

pub use dimacs::parse_dimacs;
pub use solver::{SatResult, Solver};
pub use types::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(s.add_clause(&[lit(x)]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert_eq!(s.value_lit_public(lit(x)), Some(true));
    }

    #[test]
    fn direct_unsat() {
        let mut s = Solver::new();
        let x = s.new_var();
        assert!(s.add_clause(&[lit(x)]));
        assert!(!s.add_clause(&[nlit(x)]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn xor_unsat() {
        let mut s = Solver::new();
        let a = s.new_var();
        let b = s.new_var();
        assert!(s.add_clause(&[lit(a), lit(b)]));
        assert!(s.add_clause(&[nlit(a), lit(b)]));
        assert!(s.add_clause(&[lit(a), nlit(b)]));
        assert!(s.add_clause(&[nlit(a), nlit(b)]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn dimacs_sat() {
        let input = "p cnf 3 2\n1 -2 0\n2 3 0\n";
        let mut s = parse_dimacs(input).unwrap();
        assert_eq!(s.solve(), SatResult::Sat);
    }
}
