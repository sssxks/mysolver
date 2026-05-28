//! Equality and theory-clause explanation support.

use sat::Lit;

use crate::registry::Registry;
use crate::search_state::{DisequalityEntry, MergeReason, SearchState};
use crate::types::{ProofEdgeId, TermId};

impl SearchState {
    /// Explains why `lhs == rhs` currently holds as a deduplicated premise set.
    pub fn explain_equality(
        &mut self,
        registry: &Registry,
        lhs: TermId,
        rhs: TermId,
        out: &mut Vec<Lit>,
    ) {
        self.begin_explanation_query(out);
        self.collect_equality_explanation(registry, lhs, rhs, out);
    }

    /// Explains one disequality conflict as its supporting input literals.
    pub fn explain_conflict(
        &mut self,
        registry: &Registry,
        diseq: DisequalityEntry,
        out: &mut Vec<Lit>,
    ) {
        self.begin_explanation_query(out);
        self.collect_equality_explanation(registry, diseq.lhs, diseq.rhs, out);
        self.push_explanation_lit(diseq.reason_lit, out);
    }

    /// Clears query-local scratch for one new top-level explanation.
    fn begin_explanation_query(&mut self, out: &mut Vec<Lit>) {
        out.clear();
        self.explain_pair_cache.clear();
        self.explain_output_seen.clear();
        self.explain_path_scratch.clear();
        self.bump_explain_epoch();
    }

    /// Advances the explanation-visit epoch, clearing the stamp buffer on wraparound.
    fn bump_explain_epoch(&mut self) {
        if self.explain_epoch == u32::MAX {
            self.explain_seen_stamp.fill(0);
            self.explain_epoch = 1;
            return;
        }
        self.explain_epoch += 1;
    }

    /// Recursively appends one equality explanation without discarding already
    /// collected premises from the caller.
    fn collect_equality_explanation(
        &mut self,
        registry: &Registry,
        lhs: TermId,
        rhs: TermId,
        out: &mut Vec<Lit>,
    ) {
        if lhs == rhs {
            return;
        }
        let pair = canonical_pair(lhs, rhs);
        if !self.explain_pair_cache.insert(pair) {
            return;
        }
        self.fill_explanation_path(lhs, rhs);
        let path: Vec<ProofEdgeId> = self.explain_path_scratch.iter().rev().copied().collect();
        for edge_id in path {
            let edge = self.proof_edges[edge_id.index()];
            match edge.reason {
                MergeReason::InputEq { reason_lit } => {
                    self.push_explanation_lit(reason_lit, out);
                }
                MergeReason::Congruence {
                    left_parent,
                    right_parent,
                } => {
                    let left_args = registry.term_ref(left_parent).args;
                    let right_args = registry.term_ref(right_parent).args;
                    for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
                        self.collect_equality_explanation(registry, left_arg, right_arg, out);
                    }
                }
            }
        }
    }

    /// Records one explanation premise at most once for the current query.
    fn push_explanation_lit(&mut self, lit: Lit, out: &mut Vec<Lit>) {
        if self.explain_output_seen.insert(lit) {
            out.push(lit);
        }
    }

    /// Reconstructs one explanation path from `lhs` to `rhs` into `explain_path_scratch`.
    fn fill_explanation_path(&mut self, lhs: TermId, rhs: TermId) {
        self.run_explanation_bfs(lhs, rhs);
        self.explain_path_scratch.clear();
        let mut current = rhs;
        while current != lhs {
            let edge_id =
                self.explain_pred_edge[current.index()].expect("missing equality explanation path");
            self.explain_path_scratch.push(edge_id);
            current = self.proof_edge_source(edge_id);
        }
    }

    /// Runs one allocation-free BFS over the active explanation graph.
    fn run_explanation_bfs(&mut self, lhs: TermId, rhs: TermId) {
        self.explain_queue.clear();
        self.explain_queue_head = 0;
        self.explain_queue.push(lhs);
        self.explain_seen_stamp[lhs.index()] = self.explain_epoch;
        self.explain_pred_edge[lhs.index()] = None;

        while self.explain_queue_head < self.explain_queue.len() {
            let current = self.explain_queue[self.explain_queue_head];
            self.explain_queue_head += 1;
            let mut edge_id = self.proof_edge_head[current.index()];
            while let Some(current_edge) = edge_id {
                let edge = self.proof_edges[current_edge.index()];
                let next = edge.to;
                if self.explain_seen_stamp[next.index()] != self.explain_epoch {
                    self.explain_seen_stamp[next.index()] = self.explain_epoch;
                    self.explain_pred_edge[next.index()] = Some(current_edge);
                    if next == rhs {
                        return;
                    }
                    self.explain_queue.push(next);
                }
                edge_id = edge.next;
            }
        }

        panic!("missing equality explanation path");
    }

    /// Returns the source endpoint of one directed proof edge.
    fn proof_edge_source(&self, edge_id: ProofEdgeId) -> TermId {
        self.proof_edges[edge_id.reverse().index()].to
    }
}

/// Returns one canonical unordered key for an equality pair.
fn canonical_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
    if lhs.index() <= rhs.index() {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}
