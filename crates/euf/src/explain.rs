//! Equality and theory-clause explanation support.

// TODO this module is poorly implemented, needs investigation. performance very bad.

use std::collections::VecDeque;

use sat::{AssertionLevel, Lit, TheoryClause, TheoryClauseKind};

use crate::types::{TermId, TermRef};
use crate::registry::Registry;
use crate::search_state::{DisequalityEntry, MergeReason, SearchState};

impl SearchState {
    /// Explains why `lhs == rhs` currently holds as a multiset of input literals.
    pub fn explain_equality(
        &self,
        registry: &Registry,
        lhs: TermId,
        rhs: TermId,
        out: &mut Vec<Lit>,
    ) {
        out.clear();
        self.collect_equality_explanation(registry, lhs, rhs, out);
    }

    /// Recursively appends one equality explanation without discarding already
    /// collected premises from the caller.
    fn collect_equality_explanation(
        &self,
        registry: &Registry,
        lhs: TermId,
        rhs: TermId,
        out: &mut Vec<Lit>,
    ) {
        if lhs == rhs {
            return;
        }
        let mut parents = vec![None; registry.num_terms()];
        let mut queue = VecDeque::new();
        queue.push_back(lhs);
        parents[lhs.index()] = Some(usize::MAX);

        while let Some(current) = queue.pop_front() {
            if current == rhs {
                break;
            }
            for (edge_index, edge) in self.merge_edges.iter().enumerate() {
                let next = if edge.lhs == current {
                    edge.rhs
                } else if edge.rhs == current {
                    edge.lhs
                } else {
                    continue;
                };
                if parents[next.index()].is_none() {
                    parents[next.index()] = Some(edge_index);
                    queue.push_back(next);
                }
            }
        }

        let mut path_edges = Vec::new();
        let mut current = rhs;
        while current != lhs {
            let edge_index = parents[current.index()].expect("missing equality explanation path");
            let edge = self.merge_edges[edge_index];
            path_edges.push(edge);
            current = if edge.lhs == current {
                edge.rhs
            } else {
                edge.lhs
            };
        }
        path_edges.reverse();

        for edge in path_edges {
            match edge.reason {
                MergeReason::InputEq { reason_lit } => out.push(reason_lit),
                MergeReason::Congruence {
                    left_parent,
                    right_parent,
                } => {
                    let (
                        TermRef::App {
                            args: left_args, ..
                        },
                        TermRef::App {
                            args: right_args, ..
                        },
                    ) = (
                        registry.term_ref(left_parent),
                        registry.term_ref(right_parent),
                    )
                    else {
                        continue;
                    };
                    for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
                        if self.find(left_arg) == self.find(right_arg) {
                            self.collect_equality_explanation(registry, left_arg, right_arg, out);
                        }
                    }
                }
            }
        }
    }

    /// Explains one disequality conflict as its supporting input literals.
    pub fn explain_conflict(
        &self,
        registry: &Registry,
        diseq: DisequalityEntry,
        out: &mut Vec<Lit>,
    ) {
        out.clear();
        self.collect_equality_explanation(registry, diseq.lhs, diseq.rhs, out);
        out.push(diseq.reason_lit);
    }
}

/// One recursive equality explanation node.
#[derive(Clone, Debug)]
pub enum EqualityExplanation {
    /// One asserted equality literal.
    InputLiteral(Lit),
    /// One congruence step between two parent applications.
    Congruence {
        /// Left parent application.
        left_parent: TermId,
        /// Right parent application.
        right_parent: TermId,
        /// Child pairs that were recursively equal.
        child_pairs: Box<[(TermId, TermId)]>,
    },
}

/// One clause explanation reconstructed by the theory.
#[derive(Clone, Debug)]
pub struct ExplanationClause {
    /// Propagated literal, when this is one propagation rather than one conflict.
    propagated: Option<Lit>,
    /// Premise literals whose negation form the explanation antecedent.
    premises: Box<[Lit]>,
}

impl ExplanationClause {
    /// Converts this explanation into one SAT theory clause.
    pub fn to_theory_clause(&self, solver: &sat::Solver, kind: TheoryClauseKind) -> TheoryClause {
        let mut lits =
            Vec::with_capacity(self.premises.len() + usize::from(self.propagated.is_some()));
        for &premise in &*self.premises {
            lits.push(!premise);
        }
        if let Some(propagated) = self.propagated {
            lits.push(propagated);
        }
        let assertion_level = lits
            .iter()
            .map(|lit| solver.intro_level_of(lit.var()))
            .max()
            .unwrap_or(AssertionLevel::ROOT);
        TheoryClause {
            lits: lits.into_boxed_slice(),
            assertion_level,
            kind,
        }
    }
}
