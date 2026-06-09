//! Equality and theory-clause explanation support.

use sat::Literal;

use crate::registry::Registry;
use crate::search_state::{
    DirectedEdge, DisequalityEntry, ExplainVisit, MergeEdge, MergeReason, SearchState,
};
use crate::types::Term;

impl SearchState {
    /// Explains why `lhs == rhs` currently holds as a multiset of input literals.
    pub(crate) fn explain_equality(
        &mut self,
        registry: &Registry,
        lhs: Term,
        rhs: Term,
        out: &mut Vec<Literal>,
    ) {
        out.clear();
        self.explain_cache.clear();
        self.collect_equality_explanation(registry, lhs, rhs, out);
    }

    /// Recursively appends one equality explanation without discarding already
    /// collected premises from the caller.
    fn collect_equality_explanation(
        &mut self,
        registry: &Registry,
        lhs: Term,
        rhs: Term,
        out: &mut Vec<Literal>,
    ) {
        if lhs == rhs {
            return;
        }

        let key = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
        if !self.explain_cache.insert(key) {
            return;
        }

        let mut path_edges = match self.find_equality_explanation_path(registry, lhs, rhs) {
            Some(path_edges) => path_edges,
            None => panic!("missing equality explanation path"),
        };
        path_edges.reverse();

        for edge in path_edges {
            match edge.reason {
                MergeReason::InputEq { reason_lit } => out.push(reason_lit),
                MergeReason::Congruence {
                    left_parent,
                    right_parent,
                } => {
                    let left_args = registry.term_ref(left_parent).args;
                    let right_args = registry.term_ref(right_parent).args;
                    for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
                        if self.find(left_arg) == self.find(right_arg) {
                            self.collect_equality_explanation(registry, left_arg, right_arg, out);
                        }
                    }
                }
            }
        }
    }

    /// Finds one active proof-graph path from `lhs` to `rhs`.
    fn find_equality_explanation_path(
        &mut self,
        registry: &Registry,
        lhs: Term,
        rhs: Term,
    ) -> Option<Vec<MergeEdge>> {
        self.prepare_explanation_bfs(registry.num_terms());

        let epoch = self.explain_epoch;
        self.explain_queue.clear();
        self.explain_queue.push(lhs);
        self.explain_visits[lhs.index()] = ExplainVisit {
            epoch,
            parent_edge: DirectedEdge::NONE,
        };

        let mut qhead = 0;
        let mut found = lhs == rhs;
        while qhead < self.explain_queue.len() && !found {
            let current = self.explain_queue[qhead];
            qhead += 1;

            let mut directed = self.graph_heads[current.index()];
            while !directed.is_none() {
                let edge = self.edges[directed.edge_index()];
                let next = edge.target(directed);
                if self.explain_visits[next.index()].epoch != epoch {
                    self.explain_visits[next.index()] = ExplainVisit {
                        epoch,
                        parent_edge: directed,
                    };
                    if next == rhs {
                        found = true;
                        break;
                    }
                    self.explain_queue.push(next);
                }
                directed = edge.next(directed);
            }
        }

        if !found {
            return None;
        }

        let mut path_edges = Vec::new();
        let mut current = rhs;
        while current != lhs {
            let parent_edge = self.explain_visits[current.index()].parent_edge;
            if parent_edge.is_none() {
                return None;
            }
            let edge = self.edges[parent_edge.edge_index()];
            path_edges.push(edge);
            current = edge.other_endpoint(current);
        }

        Some(path_edges)
    }

    /// Starts a new BFS epoch and grows scratch storage to the current term count.
    fn prepare_explanation_bfs(&mut self, num_terms: usize) {
        self.explain_visits.resize(
            num_terms,
            ExplainVisit {
                epoch: 0,
                parent_edge: DirectedEdge::NONE,
            },
        );

        if self.explain_epoch == u32::MAX {
            for visit in &mut self.explain_visits {
                visit.epoch = 0;
            }
            self.explain_epoch = 1;
            return;
        }

        self.explain_epoch += 1;
    }

    /// Explains one disequality conflict as its supporting input literals.
    pub(crate) fn explain_conflict(
        &mut self,
        registry: &Registry,
        diseq: DisequalityEntry,
        out: &mut Vec<Literal>,
    ) {
        out.clear();
        self.explain_cache.clear();
        self.collect_equality_explanation(registry, diseq.lhs, diseq.rhs, out);
        out.push(diseq.reason_lit);
    }
}
