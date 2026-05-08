use std::mem;

use crate::{Lit, Solver};

/// Parses a DIMACS CNF document into a [`Solver`].
///
/// The returned solver already contains the declared variables and clauses but does
/// not run search automatically.
pub fn parse_dimacs(input: &str) -> Result<Solver, String> {
    let mut declared_vars: Option<usize> = None;
    let mut declared_clauses: Option<usize> = None;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut current: Vec<Lit> = Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(format!("bad problem line: {line}"));
            }
            declared_vars = Some(
                parts[2]
                    .parse()
                    .map_err(|_| format!("bad var count: {}", parts[2]))?,
            );
            declared_clauses = Some(
                parts[3]
                    .parse()
                    .map_err(|_| format!("bad clause count: {}", parts[3]))?,
            );
            continue;
        }

        for tok in line.split_whitespace() {
            let x: i32 = tok
                .parse()
                .map_err(|_| format!("bad integer token: {tok}"))?;
            if x == 0 {
                clauses.push(mem::take(&mut current));
            } else {
                current.push(Lit::from_dimacs(x));
            }
        }
    }

    if !current.is_empty() {
        return Err("last clause is missing trailing 0".to_string());
    }

    let nvars = declared_vars.ok_or_else(|| "missing p cnf line".to_string())?;
    if let Some(nclauses) = declared_clauses
        && nclauses != clauses.len()
    {
        return Err(format!(
            "declared {nclauses} clauses, parsed {}",
            clauses.len()
        ));
    }

    let mut solver = Solver::with_vars(nvars);
    for clause in clauses {
        for lit in &clause {
            if lit.var().index() >= nvars {
                return Err(format!(
                    "literal uses variable {} beyond declared {nvars}",
                    lit.var().index() + 1
                ));
            }
        }
        solver.add_clause(&clause);
    }
    Ok(solver)
}
