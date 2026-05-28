//! Search-local congruence-closure state and rollback bookkeeping.

use std::collections::VecDeque;
use std::ptr::NonNull;

use bumpalo::Bump;
use hashbrown::{HashMap, HashSet};
use sat::{Lit, TheoryClause};

use crate::arena::{ArenaSlice, make_hash};
use crate::registry::Registry;
use crate::types::{EClassId, ProofEdgeId, SymbolId, TermId, TheoryAtomId};

/// One input equality waiting to merge.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeInput {
    /// Left term.
    pub(crate) lhs: TermId,
    /// Right term.
    pub(crate) rhs: TermId,
    /// Assigned SAT literal justifying this merge.
    pub(crate) reason_lit: Lit,
}

/// One input disequality waiting to become active.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DiseqInput {
    /// Left term.
    pub(crate) lhs: TermId,
    /// Right term.
    pub(crate) rhs: TermId,
    /// Assigned SAT literal justifying this disequality.
    pub(crate) reason_lit: Lit,
}

/// Borrowed congruence signature used for allocation-free probing.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSigRef<'a> {
    /// Function symbol.
    pub(crate) fun: SymbolId,
    /// Current class representatives of the arguments.
    pub(crate) arg_reps: &'a [EClassId],
}

/// Owned congruence signature stored in the search-local table.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSig {
    /// Function symbol.
    fun: SymbolId,
    /// Current class representatives of the arguments.
    arg_reps: ArenaSlice<EClassId>,
}

impl CongruenceSig {
    /// Returns whether this stored signature matches one borrowed probe.
    fn matches_ref(&self, sig: CongruenceSigRef<'_>) -> bool {
        // SAFETY: `arg_reps` points into live search-local bump storage.
        unsafe { self.fun == sig.fun && self.arg_reps.as_slice() == sig.arg_reps }
    }
}

/// Reason why two terms became equal.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum MergeReason {
    /// One asserted equality literal.
    InputEq {
        /// The asserted equality literal.
        reason_lit: Lit,
    },
    /// Congruence closure of two application parents.
    Congruence {
        /// Left parent application.
        left_parent: TermId,
        /// Right parent application.
        right_parent: TermId,
    },
}

/// One active directed edge in the equality explanation graph.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct ProofEdge {
    /// Target endpoint.
    pub(crate) to: TermId,
    /// Next incident edge for the source endpoint.
    pub(crate) next: Option<ProofEdgeId>,
    /// Justification for this equality edge.
    pub(crate) reason: MergeReason,
}

/// One active disequality fact.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DisequalityEntry {
    /// Left endpoint.
    pub(crate) lhs: TermId,
    /// Right endpoint.
    pub(crate) rhs: TermId,
    /// SAT literal asserting disequality.
    pub(crate) reason_lit: Lit,
}

/// One SAT-decision-level rollback marker.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct SatLevelMarker {
    /// Undo-log length at level entry.
    pub(crate) undo_len: usize,
    /// Congruence-insert log length at level entry.
    pub(crate) congruence_insert_len: usize,
    /// Explanation-edge length at level entry.
    pub(crate) proof_edges_len: usize,
    /// Active-disequality length at level entry.
    pub(crate) active_disequalities_len: usize,
    /// Pending-merge queue length at level entry.
    pub(crate) pending_merges_len: usize,
    /// Pending-repair queue length at level entry.
    pub(crate) pending_repairs_len: usize,
    /// Pending-atom-trigger queue length at level entry.
    pub(crate) pending_atom_triggers_len: usize,
    /// Pending-clause queue length at level entry.
    pub(crate) pending_clauses_len: usize,
}

/// One reversible mutation record.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Undo {
    /// Parent pointer change.
    Parent {
        /// Node updated in `parent`.
        node: TermId,
        /// Previous parent value.
        old_parent: EClassId,
    },
    /// Rank update for a surviving root.
    Rank {
        /// Root updated in `rank`.
        root: EClassId,
        /// Previous rank value.
        old_rank: u32,
    },
    /// Circular class-membership successor change.
    ClassNext {
        /// Node updated in `next_in_class`.
        node: TermId,
        /// Previous successor value.
        old_next: TermId,
    },
}

/// Search-local equality engine state.
#[derive(Debug, Default)]
pub struct SearchState {
    /// Union-find representative for each term.
    parent: Vec<EClassId>,
    /// Rank heuristic for each representative.
    rank: Vec<u32>,
    /// Successor link for each term in one circular class-membership list.
    pub(crate) next: Vec<TermId>,

    /// Search-lifetime arena for owned congruence signatures.
    ///
    /// Currently, this is implemented as search-lifetime bump arena for
    /// simplicity. SAT backtracking removes congruence-table entries via
    /// `signature_log`, but does not reclaim per-signature payload.
    /// That keeps `CongruenceSig` as one simple hashable slice handle.
    signature_storage: Bump,
    /// Congruence table keyed by function symbol and current representative arguments.
    pub(crate) signatures: HashMap<CongruenceSig, TermId>,
    /// Congruence-table insertions in insertion order for SAT-level rollback.
    pub(crate) signature_log: Vec<CongruenceSig>,
    /// Scratch buffer used while building borrowed congruence signatures.
    signature_scratch: Vec<EClassId>,

    /// Pending input merges still to process.
    pub(crate) pending_merges: VecDeque<MergeInput>,
    /// Parent applications that must be reconsidered.
    pub(crate) pending_repairs: VecDeque<TermId>,
    /// Theory atoms affected by recent class changes.
    pub(crate) pending_atom_triggers: Vec<TheoryAtomId>,
    /// Read cursor into `pending_atom_triggers`.
    pub(crate) pending_atom_qhead: usize,
    /// Per-atom queue-membership bit.
    pub(crate) atom_is_enqueued: Vec<bool>,
    /// Pending theory clauses ready to return to SAT.
    pub(crate) pending_clauses: Vec<TheoryClause>,
    /// Currently active disequalities.
    pub(crate) active_disequalities: Vec<DisequalityEntry>,

    /// Per-term adjacency-list heads into `proof_edges`.
    pub(crate) proof_edge_head: Vec<Option<ProofEdgeId>>,
    /// Active equality explanation graph as directed adjacency entries.
    pub(crate) proof_edges: Vec<ProofEdge>,
    /// Search-local visitation stamps for one explanation BFS.
    pub(crate) explain_seen_stamp: Vec<u32>,
    /// Predecessor edge for each term visited in the current explanation BFS.
    pub(crate) explain_pred_edge: Vec<Option<ProofEdgeId>>,
    /// Allocation-free BFS queue reused across explanation queries.
    pub(crate) explain_queue: Vec<TermId>,
    /// Read cursor into `explain_queue`.
    pub(crate) explain_queue_head: usize,
    /// Monotonic epoch used by `explain_seen_stamp`.
    pub(crate) explain_epoch: u32,
    /// Pair cache for one top-level explanation query.
    pub(crate) explain_pair_cache: HashSet<(TermId, TermId)>,
    /// Premise deduplication for one top-level explanation query.
    pub(crate) explain_output_seen: HashSet<Lit>,
    /// Scratch path used while reconstructing one explanation chain.
    pub(crate) explain_path_scratch: Vec<ProofEdgeId>,

    /// Reversible mutation log.
    pub(crate) undo_log: Vec<Undo>,
    /// One marker per open SAT decision level.
    level_markers: Vec<SatLevelMarker>,
}

impl SearchState {
    /// Finds one current class representative using an arbitrary parent slice.
    fn find_in_parent(parent: &[EClassId], term: TermId) -> EClassId {
        let mut current = EClassId::from_index(term.index());
        while parent[current.index()] != current {
            current = parent[current.index()];
        }
        current
    }

    /// Reinitializes the search-local state for one new top-level SAT search.
    pub fn reset_for_registry(&mut self, registry: &Registry) {
        let nterms = registry.num_terms();
        self.parent.clear();
        self.rank.clear();
        self.next.clear();
        self.proof_edge_head.clear();
        self.signature_storage.reset();

        for index in 0..nterms {
            let term = TermId::from_index(index);
            let rep = EClassId::from_index(index);
            self.parent.push(rep);
            self.rank.push(0);
            self.next.push(term);
            self.proof_edge_head.push(None);
        }

        self.signatures.clear();
        self.signature_scratch.clear();
        self.pending_merges.clear();
        self.pending_repairs.clear();
        self.pending_atom_triggers.clear();
        self.pending_atom_qhead = 0;
        self.atom_is_enqueued.clear();
        self.atom_is_enqueued.resize(registry.num_atoms(), false);
        self.pending_clauses.clear();
        self.active_disequalities.clear();
        self.proof_edges.clear();
        self.explain_seen_stamp.clear();
        self.explain_seen_stamp.resize(nterms, 0);
        self.explain_pred_edge.clear();
        self.explain_pred_edge.resize(nterms, None);
        self.explain_queue.clear();
        self.explain_queue_head = 0;
        self.explain_epoch = 0;
        self.explain_pair_cache.clear();
        self.explain_output_seen.clear();
        self.explain_path_scratch.clear();
        self.signature_log.clear();
        self.undo_log.clear();
        self.level_markers.clear();
    }

    /// Pushes one rollback marker aligned with a new SAT decision level.
    pub fn push_sat_level(&mut self) {
        self.level_markers.push(SatLevelMarker {
            undo_len: self.undo_log.len(),
            congruence_insert_len: self.signature_log.len(),
            proof_edges_len: self.proof_edges.len(),
            active_disequalities_len: self.active_disequalities.len(),
            pending_merges_len: self.pending_merges.len(),
            pending_repairs_len: self.pending_repairs.len(),
            pending_atom_triggers_len: self.pending_atom_triggers.len(),
            pending_clauses_len: self.pending_clauses.len(),
        });
    }

    /// Pops search-local state back to `new_level`.
    pub fn pop_sat_levels(&mut self, new_level: usize) {
        while self.level_markers.len() > new_level {
            let marker = self.level_markers.pop().expect("checked above");
            self.pending_clauses.truncate(marker.pending_clauses_len);
            for &atom in &self.pending_atom_triggers[marker.pending_atom_triggers_len..] {
                self.atom_is_enqueued[atom.index()] = false;
            }
            self.pending_atom_triggers
                .truncate(marker.pending_atom_triggers_len);
            self.pending_atom_qhead = self
                .pending_atom_qhead
                .min(self.pending_atom_triggers.len());
            self.pending_repairs.truncate(marker.pending_repairs_len);
            self.pending_merges.truncate(marker.pending_merges_len);
            self.active_disequalities
                .truncate(marker.active_disequalities_len);
            self.rollback_proof_edges_to(marker.proof_edges_len);
            while self.signature_log.len() > marker.congruence_insert_len {
                let key = self
                    .signature_log
                    .pop()
                    .expect("checked congruence insert suffix above");
                self.signatures.remove(&key);
            }
            self.rollback_to(marker.undo_len);
        }
    }

    /// Finds the current class representative of `term`.
    pub fn find(&self, term: TermId) -> EClassId {
        let mut current = EClassId::from_index(term.index());
        while self.parent[current.index()] != current {
            current = self.parent[current.index()];
        }
        current
    }

    /// Merges two distinct roots and returns the surviving root.
    pub fn union_roots(&mut self, lhs_root: EClassId, rhs_root: EClassId) -> EClassId {
        debug_assert_ne!(lhs_root, rhs_root);
        let (survivor, absorbed) = if self.rank[lhs_root.index()] < self.rank[rhs_root.index()] {
            (rhs_root, lhs_root)
        } else {
            (lhs_root, rhs_root)
        };

        self.undo_log.push(Undo::Parent {
            node: TermId::from_index(absorbed.index()),
            old_parent: self.parent[absorbed.index()],
        });
        self.parent[absorbed.index()] = survivor;

        if self.rank[lhs_root.index()] == self.rank[rhs_root.index()] {
            self.undo_log.push(Undo::Rank {
                root: survivor,
                old_rank: self.rank[survivor.index()],
            });
            self.rank[survivor.index()] += 1;
        }

        let survivor_node = TermId::from_index(survivor.index());
        let absorbed_node = TermId::from_index(absorbed.index());
        self.undo_log.push(Undo::ClassNext {
            node: survivor_node,
            old_next: self.next[survivor_node.index()],
        });
        self.undo_log.push(Undo::ClassNext {
            node: absorbed_node,
            old_next: self.next[absorbed_node.index()],
        });
        let survivor_next = self.next[survivor_node.index()];
        self.next[survivor_node.index()] = self.next[absorbed_node.index()];
        self.next[absorbed_node.index()] = survivor_next;

        survivor
    }

    /// Fills `congruence_sig_scratch` with the current signature of `parent`.
    pub(crate) fn fill_congruence_sig_scratch(
        &mut self,
        registry: &Registry,
        parent: TermId,
    ) -> Option<SymbolId> {
        let term = registry.term_ref(parent);
        let union_find_parent = &self.parent;
        self.signature_scratch.clear();
        for &arg in term.args {
            self.signature_scratch
                .push(Self::find_in_parent(union_find_parent, arg));
        }
        Some(term.fun)
    }

    /// Finds one existing congruence-table owner for the current scratch signature.
    fn find_congruent_parent_for_current_sig(&self, fun: SymbolId) -> Option<TermId> {
        let sig = CongruenceSigRef {
            fun,
            arg_reps: &self.signature_scratch,
        };
        let hash = make_hash(self.signatures.hasher(), &sig);
        self.signatures
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(sig))
            .map(|(_, &owner)| owner)
    }

    /// Materializes one owned congruence signature from the current scratch buffer.
    pub(crate) fn own_current_congruence_sig(&self, fun: SymbolId) -> CongruenceSig {
        let sig = CongruenceSigRef {
            fun,
            arg_reps: &self.signature_scratch,
        };
        self.own_congruence_sig(sig)
    }

    /// Finds one existing congruence-table owner for `parent`, if any.
    pub(crate) fn find_congruent_parent(
        &mut self,
        registry: &Registry,
        parent: TermId,
    ) -> Option<TermId> {
        let fun = self.fill_congruence_sig_scratch(registry, parent)?;
        self.find_congruent_parent_for_current_sig(fun)
    }

    /// Enqueues one atom trigger at most once.
    pub fn enqueue_atom_trigger(&mut self, atom: TheoryAtomId) {
        if self.atom_is_enqueued[atom.index()] {
            return;
        }
        self.atom_is_enqueued[atom.index()] = true;
        self.pending_atom_triggers.push(atom);
    }

    /// Enqueues one input equality merge.
    pub fn enqueue_input_equality(&mut self, input: MergeInput) {
        self.pending_merges.push_back(input);
    }

    /// Activates one input disequality.
    pub fn enqueue_input_disequality(&mut self, input: DiseqInput) {
        self.active_disequalities.push(DisequalityEntry {
            lhs: input.lhs,
            rhs: input.rhs,
            reason_lit: input.reason_lit,
        });
    }

    /// Appends one undirected proof edge as two directed adjacency entries.
    pub fn add_proof_edge(&mut self, lhs: TermId, rhs: TermId, reason: MergeReason) {
        let lhs_head = self.proof_edge_head[lhs.index()];
        let rhs_head = self.proof_edge_head[rhs.index()];
        let forward = ProofEdgeId::from_index(self.proof_edges.len());
        let reverse = ProofEdgeId::from_index(self.proof_edges.len() + 1);
        self.proof_edges.push(ProofEdge {
            to: rhs,
            next: lhs_head,
            reason,
        });
        self.proof_edges.push(ProofEdge {
            to: lhs,
            next: rhs_head,
            reason,
        });
        self.proof_edge_head[lhs.index()] = Some(forward);
        self.proof_edge_head[rhs.index()] = Some(reverse);
    }

    /// Rolls back all reversible mutations down to `undo_len`.
    pub fn rollback_to(&mut self, undo_len: usize) {
        while self.undo_log.len() > undo_len {
            match self.undo_log.pop().expect("checked above") {
                Undo::Parent { node, old_parent } => {
                    self.parent[node.index()] = old_parent;
                }
                Undo::Rank { root, old_rank } => {
                    self.rank[root.index()] = old_rank;
                }
                Undo::ClassNext { node, old_next } => {
                    self.next[node.index()] = old_next;
                }
            }
        }
    }

    /// Stores one owned congruence signature inside the search-local bump arena.
    fn own_congruence_sig(&self, sig: CongruenceSigRef<'_>) -> CongruenceSig {
        CongruenceSig {
            fun: sig.fun,
            arg_reps: ArenaSlice::from_raw(NonNull::from(
                self.signature_storage.alloc_slice_copy(sig.arg_reps),
            )),
        }
    }

    /// Rolls back the explanation graph to the requested edge prefix length.
    fn rollback_proof_edges_to(&mut self, proof_edges_len: usize) {
        while self.proof_edges.len() > proof_edges_len {
            let reverse_index = self.proof_edges.len() - 1;
            let forward_index = reverse_index - 1;
            let forward = self.proof_edges[forward_index];
            let reverse = self.proof_edges[reverse_index];
            let forward_id = ProofEdgeId::from_index(forward_index);
            let reverse_id = ProofEdgeId::from_index(reverse_index);
            let forward_source = reverse.to;
            let reverse_source = forward.to;
            debug_assert_eq!(
                self.proof_edge_head[forward_source.index()],
                Some(forward_id)
            );
            debug_assert_eq!(
                self.proof_edge_head[reverse_source.index()],
                Some(reverse_id)
            );
            self.proof_edge_head[forward_source.index()] = forward.next;
            self.proof_edge_head[reverse_source.index()] = reverse.next;
            self.proof_edges.truncate(forward_index);
        }
    }
}
