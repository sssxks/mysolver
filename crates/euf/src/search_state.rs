//! Search-local congruence-closure state and rollback bookkeeping.

use std::collections::VecDeque;
use std::ptr::NonNull;

use bumpalo::Bump;
use hashbrown::{HashMap, HashSet};
use sat::{Literal, TheoryClause};

use crate::arena::{ArenaSlice, make_hash};
use crate::registry::Registry;
use crate::types::{EClass, Symbol, Term, TheoryAtom};

/// One input equality waiting to merge.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeInput {
    /// Left term.
    pub(crate) lhs: Term,
    /// Right term.
    pub(crate) rhs: Term,
    /// Assigned SAT literal justifying this merge.
    pub(crate) reason_lit: Literal,
}

/// One input disequality waiting to become active.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DiseqInput {
    /// Left term.
    pub(crate) lhs: Term,
    /// Right term.
    pub(crate) rhs: Term,
    /// Assigned SAT literal justifying this disequality.
    pub(crate) reason_lit: Literal,
}

/// Borrowed congruence signature used for allocation-free probing.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSigRef<'a> {
    /// Function symbol.
    fun: Symbol,
    /// Current class representatives of the arguments.
    arg_reps: &'a [EClass],
}

/// Owned congruence signature stored in the search-local table.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSig {
    /// Function symbol.
    fun: Symbol,
    /// Current class representatives of the arguments.
    arg_reps: ArenaSlice<EClass>,
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
        reason_lit: Literal,
    },
    /// Congruence closure of two application parents.
    Congruence {
        /// Left parent application.
        left_parent: Term,
        /// Right parent application.
        right_parent: Term,
    },
}

/// One active edge in the equality proof graph.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeEdge {
    /// Left endpoint.
    lhs: Term,
    /// Right endpoint.
    rhs: Term,
    /// Previous adjacency-list head for the `lhs -> rhs` orientation.
    next_lhs: DirectedEdge,
    /// Previous adjacency-list head for the `rhs -> lhs` orientation.
    next_rhs: DirectedEdge,
    /// Justification for this equality edge.
    pub(crate) reason: MergeReason,
}

impl MergeEdge {
    /// Returns the endpoint opposite `term` on this undirected merge edge.
    #[inline(always)]
    pub(crate) fn other_endpoint(self, term: Term) -> Term {
        if self.lhs == term {
            return self.rhs;
        }
        debug_assert_eq!(self.rhs, term);
        self.lhs
    }

    /// Returns the target endpoint for one directed orientation of this edge.
    #[inline(always)]
    pub(crate) fn target(self, directed: DirectedEdge) -> Term {
        if directed.is_rhs_to_lhs() {
            return self.lhs;
        }
        self.rhs
    }

    /// Returns the next edge in the source endpoint adjacency list.
    #[inline(always)]
    pub(crate) fn next(self, directed: DirectedEdge) -> DirectedEdge {
        if directed.is_rhs_to_lhs() {
            return self.next_rhs;
        }
        self.next_lhs
    }
}

/// Handle for one directed orientation of a merge edge.
///
/// Semantically, this is `(SearchState::edges index × Direction) + None`.
///
/// # Encoding
///
/// - `lhs -> rhs` is encoded as `edge.index() * 2`.
/// - `rhs -> lhs` is encoded as `edge.index() * 2 + 1`.
/// - `u32::MAX` is reserved as the null adjacency-list terminator.
/// - Invariants: live raw handles are strictly smaller than `u32::MAX`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct DirectedEdge(u32);

impl DirectedEdge {
    /// Sentinel for the end of one adjacency list.
    pub(crate) const NONE: Self = Self(u32::MAX);

    /// Creates the `lhs -> rhs` orientation for one merge edge.
    #[inline(always)]
    fn lhs_to_rhs(edge_index: usize) -> Self {
        Self::from_edge_index_and_direction(edge_index, false)
    }

    /// Creates the `rhs -> lhs` orientation for one merge edge.
    #[inline(always)]
    fn rhs_to_lhs(edge_index: usize) -> Self {
        Self::from_edge_index_and_direction(edge_index, true)
    }

    /// Creates one directed edge handle from an edge index and orientation bit.
    #[inline(always)]
    fn from_edge_index_and_direction(edge_index: usize, rhs_to_lhs: bool) -> Self {
        let raw = edge_index
            .checked_mul(2)
            .and_then(|raw| raw.checked_add(usize::from(rhs_to_lhs)))
            .expect("directed merge edge handle space exhausted");
        assert!(
            raw < u32::MAX as usize,
            "directed merge edge handle space exhausted"
        );
        Self(raw as u32)
    }

    /// Returns the zero-based merge edge index named by this orientation.
    #[inline(always)]
    pub(crate) fn edge_index(self) -> usize {
        debug_assert_ne!(self, Self::NONE);
        (self.0 >> 1) as usize
    }

    /// Returns whether this orientation is `rhs -> lhs`.
    #[inline(always)]
    fn is_rhs_to_lhs(self) -> bool {
        debug_assert_ne!(self, Self::NONE);
        self.0 & 1 == 1
    }

    /// Returns whether this is the sentinel value.
    #[inline(always)]
    pub(crate) fn is_none(self) -> bool {
        self == Self::NONE
    }
}

impl Default for DirectedEdge {
    fn default() -> Self {
        Self::NONE
    }
}

/// One visited-node record for an explanation BFS.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub(crate) struct ExplainVisit {
    /// BFS epoch in which this record is live.
    pub(crate) epoch: u32,
    /// Incoming directed edge on the discovered BFS tree.
    pub(crate) parent_edge: DirectedEdge,
}

/// One active disequality fact.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DisequalityEntry {
    /// Left endpoint.
    pub(crate) lhs: Term,
    /// Right endpoint.
    pub(crate) rhs: Term,
    /// SAT literal asserting disequality.
    pub(crate) reason_lit: Literal,
}

/// The result of merging two distinct equality classes.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct ClassMerge {
    /// Representative that remains live after the merge.
    pub(crate) survivor: EClass,
    /// Representative whose class was absorbed.
    pub(crate) absorbed: EClass,
    /// Violated active disequality found while scanning the absorbed class.
    ///
    /// The caller must add the merge's proof edge before explaining this conflict.
    pub(crate) disequality_conflict: Option<DisequalityEntry>,
}

/// One SAT level rollback marker.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct LevelMarker {
    /// Undo-log length at level entry.
    undo_len: usize,
    /// Congruence-insert log length at level entry.
    congruence_insert_len: usize,
    /// Merge-edge length at level entry.
    merge_edges_len: usize,
    /// Active-disequality length at level entry.
    active_disequalities_len: usize,
    /// Disequality incidence-log length at level entry.
    disequality_incident_log_len: usize,
    /// Pending-merge queue length at level entry.
    pending_merges_len: usize,
    /// Pending-repair queue length at level entry.
    pending_repairs_len: usize,
    /// Pending-atom-trigger queue length at level entry.
    pending_atom_triggers_len: usize,
    /// Pending-clause queue length at level entry.
    pending_clauses_len: usize,
    /// Search-local atom-assignment trail length at level entry.
    atom_trail_len: usize,
}

/// One reversible mutation record.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Undo {
    /// Parent pointer change.
    Parent {
        /// Node updated in `parent`.
        node: Term,
        /// Previous parent value.
        old_parent: EClass,
    },
    /// Class-size update for a surviving root.
    ClassSize {
        /// Root updated in `class_size`.
        root: EClass,
        /// Previous class size.
        old_size: u32,
    },
    /// Circular class-membership successor change.
    ClassNext {
        /// Node updated in `next_in_class`.
        node: Term,
        /// Previous successor value.
        old_next: Term,
    },
}

/// Search-local equality engine state.
#[derive(Debug, Default)]
pub struct SearchState {
    /// Union-find representative for each term.
    parent: Vec<EClass>,
    /// Number of terms in each current representative class.
    class_size: Vec<u32>,
    /// Successor link for each term in one circular class-membership list.
    next: Vec<Term>,

    /// Search-lifetime arena for owned congruence signatures.
    ///
    /// Currently, this is implemented as search-lifetime bump arena for
    /// simplicity. SAT backtracking removes congruence-table entries via
    /// `congruence_insert_log`, but does not reclaim per-signature payload.
    /// That keeps `CongruenceSig` as one simple hashable slice handle.
    signature_storage: Bump,
    /// Congruence table keyed by function symbol and current representative arguments.
    pub(crate) signatures: HashMap<CongruenceSig, Term>,
    /// Congruence-table insertions in insertion order for SAT-level rollback.
    pub(crate) signature_log: Vec<CongruenceSig>,
    /// Scratch buffer used while building borrowed congruence signatures.
    signature_scratch: Vec<EClass>,

    /// Pending input merges still to process.
    pub(crate) pending_merges: VecDeque<MergeInput>,
    /// Assigned theory literals not yet processed by EUF.
    pending_assignments: VecDeque<Literal>,
    /// Parent applications that must be reconsidered.
    pub(crate) pending_repairs: VecDeque<Term>,
    /// Theory atoms affected by recent class changes.
    pub(crate) pending_atom_triggers: Vec<TheoryAtom>,
    /// Read cursor into `pending_atom_triggers`.
    pub(crate) pending_atom_qhead: usize,
    /// Per-atom queue-membership bit.
    pub(crate) atom_is_enqueued: Vec<bool>,
    /// Current search-local Boolean value for each theory atom.
    atom_value: Vec<Option<bool>>,
    /// Search-local assigned atom trail for SAT-level rollback.
    atom_trail: Vec<TheoryAtom>,
    /// Pending theory clauses ready to return to SAT.
    pub(crate) pending_clauses: Vec<TheoryClause>,
    /// Currently active disequalities.
    pub(crate) active_disequalities: Vec<DisequalityEntry>,
    /// Active disequality indexes incident to each term.
    term_disequalities: Vec<Vec<usize>>,
    /// Rollback log for entries appended to `term_disequalities`.
    disequality_incident_log: Vec<(Term, usize)>,

    /// Active equality-proof graph.
    pub(crate) edges: Vec<MergeEdge>,
    /// Per-term head of the directed equality-proof adjacency list.
    pub(crate) graph_heads: Vec<DirectedEdge>,

    /// Reusable visited records for equality explanation BFS.
    pub(crate) explain_visits: Vec<ExplainVisit>,
    /// Current nonzero BFS epoch.
    pub(crate) explain_epoch: u32,
    /// Reusable FIFO storage for equality explanation BFS.
    pub(crate) explain_queue: Vec<Term>,
    /// Pair cache for one recursive equality explanation.
    pub(crate) explain_cache: HashSet<(Term, Term)>,

    /// Reversible mutation log.
    undo_log: Vec<Undo>,
    /// One marker per open SAT level.
    level_markers: Vec<LevelMarker>,
}

impl SearchState {
    /// Finds one current class representative using an arbitrary parent slice.
    fn find_in_parent(parent: &[EClass], term: Term) -> EClass {
        let mut current = EClass::from_index(term.index());
        while parent[current.index()] != current {
            current = parent[current.index()];
        }
        current
    }

    /// Reinitializes the search-local state for one new top-level SAT search.
    pub(crate) fn reset_for_registry(&mut self, registry: &Registry) {
        let nterms = registry.num_terms();
        self.parent.clear();
        self.class_size.clear();
        self.next.clear();
        self.signature_storage.reset();

        for index in 0..nterms {
            let term = Term::from_index(index);
            let rep = EClass::from_index(index);
            self.parent.push(rep);
            self.class_size.push(1);
            self.next.push(term);
        }

        self.signatures.clear();
        self.signature_scratch.clear();
        self.signature_log.clear();
        self.initialize_congruence_table(registry);
        self.pending_merges.clear();
        self.pending_assignments.clear();
        self.pending_repairs.clear();
        self.pending_atom_triggers.clear();
        self.pending_atom_qhead = 0;
        self.atom_is_enqueued.clear();
        self.atom_is_enqueued.resize(registry.num_atoms(), false);
        self.atom_value.clear();
        self.atom_value.resize(registry.num_atoms(), None);
        self.atom_trail.clear();
        self.pending_clauses.clear();
        self.active_disequalities.clear();
        self.term_disequalities.clear();
        self.term_disequalities.resize(nterms, Vec::new());
        self.disequality_incident_log.clear();
        self.edges.clear();
        self.graph_heads.clear();
        self.graph_heads.resize(nterms, DirectedEdge::NONE);
        self.explain_visits.clear();
        self.explain_epoch = 0;
        self.explain_queue.clear();
        self.explain_cache.clear();
        self.undo_log.clear();
        self.level_markers.clear();
    }

    /// Pushes one rollback marker aligned with a new SAT level.
    pub(crate) fn push_level(&mut self) {
        self.level_markers.push(LevelMarker {
            undo_len: self.undo_log.len(),
            congruence_insert_len: self.signature_log.len(),
            merge_edges_len: self.edges.len(),
            active_disequalities_len: self.active_disequalities.len(),
            disequality_incident_log_len: self.disequality_incident_log.len(),
            pending_merges_len: self.pending_merges.len(),
            pending_repairs_len: self.pending_repairs.len(),
            pending_atom_triggers_len: self.pending_atom_triggers.len(),
            pending_clauses_len: self.pending_clauses.len(),
            atom_trail_len: self.atom_trail.len(),
        });
    }

    /// Pops search-local state back to `new_level`.
    pub(crate) fn pop_levels(&mut self, new_level: sat::Level) {
        while self.level_markers.len() > new_level.index() {
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
            while self.atom_trail.len() > marker.atom_trail_len {
                let atom = self
                    .atom_trail
                    .pop()
                    .expect("checked atom trail suffix above");
                self.atom_value[atom.index()] = None;
            }
            self.active_disequalities
                .truncate(marker.active_disequalities_len);
            while self.disequality_incident_log.len() > marker.disequality_incident_log_len {
                let Some((term, diseq_index)) = self.disequality_incident_log.pop() else {
                    panic!("checked disequality incidence suffix above");
                };
                let Some(last) = self.term_disequalities[term.index()].pop() else {
                    panic!("disequality incidence list must contain logged suffix");
                };
                assert_eq!(
                    last, diseq_index,
                    "disequality incidence rollback must be stack-like"
                );
            }
            self.truncate_merge_edges(marker.merge_edges_len);
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
    pub(crate) fn find(&self, term: Term) -> EClass {
        let mut current = EClass::from_index(term.index());
        while self.parent[current.index()] != current {
            current = self.parent[current.index()];
        }
        current
    }

    /// Merges two distinct roots and enqueues work for the absorbed class.
    pub(crate) fn union_roots(
        &mut self,
        registry: &Registry,
        lhs_root: EClass,
        rhs_root: EClass,
    ) -> ClassMerge {
        debug_assert_ne!(lhs_root, rhs_root);
        let (survivor, absorbed) =
            if self.class_size[lhs_root.index()] < self.class_size[rhs_root.index()] {
                (rhs_root, lhs_root)
            } else {
                (lhs_root, rhs_root)
            };

        self.undo_log.push(Undo::Parent {
            node: Term::from_index(absorbed.index()),
            old_parent: self.parent[absorbed.index()],
        });
        self.parent[absorbed.index()] = survivor;

        self.undo_log.push(Undo::ClassSize {
            root: survivor,
            old_size: self.class_size[survivor.index()],
        });
        self.class_size[survivor.index()] += self.class_size[absorbed.index()];

        let absorbed_start = Term::from_index(absorbed.index());
        let mut term = absorbed_start;
        let mut disequality_conflict = None;
        loop {
            for &parent in registry.parent_apps(term) {
                self.pending_repairs.push_back(parent);
            }
            for &atom in registry.term_atoms(term) {
                self.enqueue_atom_trigger(atom);
            }
            if disequality_conflict.is_none() {
                disequality_conflict = self.incident_disequality_conflict(term);
            }

            term = self.next[term.index()];
            if term == absorbed_start {
                break;
            }
        }

        let survivor_node = Term::from_index(survivor.index());
        let absorbed_node = Term::from_index(absorbed.index());
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

        ClassMerge {
            survivor,
            absorbed,
            disequality_conflict,
        }
    }

    /// Initializes the congruence table for every registered application term.
    fn initialize_congruence_table(&mut self, registry: &Registry) {
        for index in 0..registry.num_terms() {
            let parent = Term::from_index(index);
            if registry.term_ref(parent).args.is_empty() {
                continue;
            }
            let Some(fun) = self.fill_congruence_sig_scratch(registry, parent) else {
                continue;
            };
            debug_assert!(
                self.find_congruent_parent_for_current_sig(fun).is_none(),
                "canonical registry must not contain duplicate initial application signatures",
            );
            let owned = self.own_current_congruence_sig(fun);
            self.signature_log.push(owned.clone());
            self.signatures.insert(owned, parent);
        }
    }

    /// Fills `congruence_sig_scratch` with the current signature of `parent`.
    pub(crate) fn fill_congruence_sig_scratch(
        &mut self,
        registry: &Registry,
        parent: Term,
    ) -> Option<Symbol> {
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
    fn find_congruent_parent_for_current_sig(&self, fun: Symbol) -> Option<Term> {
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
    pub(crate) fn own_current_congruence_sig(&self, fun: Symbol) -> CongruenceSig {
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
        parent: Term,
    ) -> Option<Term> {
        let fun = self.fill_congruence_sig_scratch(registry, parent)?;
        self.find_congruent_parent_for_current_sig(fun)
    }

    /// Enqueues one atom trigger at most once.
    fn enqueue_atom_trigger(&mut self, atom: TheoryAtom) {
        if self.atom_is_enqueued[atom.index()] {
            return;
        }
        self.atom_is_enqueued[atom.index()] = true;
        self.pending_atom_triggers.push(atom);
    }

    /// Finds one violated active disequality incident to `term`.
    fn incident_disequality_conflict(&self, term: Term) -> Option<DisequalityEntry> {
        for &diseq_index in &self.term_disequalities[term.index()] {
            let Some(&diseq) = self.active_disequalities.get(diseq_index) else {
                panic!("active disequality incidence index must name a live entry");
            };
            if self.find(diseq.lhs) == self.find(diseq.rhs) {
                return Some(diseq);
            }
        }
        None
    }

    /// Enqueues one input equality merge.
    pub(crate) fn enqueue_input_equality(&mut self, input: MergeInput) {
        self.pending_merges.push_back(input);
    }

    /// Enqueues one SAT assignment whose variable is bound to a theory atom.
    pub(crate) fn enqueue_pending_assignment(&mut self, lit: Literal) {
        self.pending_assignments.push_back(lit);
    }

    /// Pops the oldest unprocessed SAT assignment.
    pub(crate) fn pop_pending_assignment(&mut self) -> Option<Literal> {
        self.pending_assignments.pop_front()
    }

    /// Records one processed theory-atom assignment.
    pub(crate) fn assign_theory_atom(&mut self, atom: TheoryAtom, value: bool) {
        if self.atom_value.len() <= atom.index() {
            self.atom_value.resize(atom.index() + 1, None);
        }
        self.atom_value[atom.index()] = Some(value);
        self.atom_trail.push(atom);
    }

    /// Returns the current search-local value of one theory atom.
    pub(crate) fn atom_value(&self, atom: TheoryAtom) -> Option<bool> {
        self.atom_value.get(atom.index()).copied().flatten()
    }

    /// Returns the number of SAT assignments waiting for EUF processing.
    pub(crate) fn pending_assignment_count(&self) -> usize {
        self.pending_assignments.len()
    }

    /// Returns the number of currently assigned theory atoms.
    pub(crate) fn assigned_atom_count(&self) -> usize {
        self.atom_trail.len()
    }

    /// Returns whether any search-local work remains.
    pub(crate) fn has_pending_work(&self) -> bool {
        !self.pending_assignments.is_empty()
            || !self.pending_clauses.is_empty()
            || !self.pending_merges.is_empty()
            || !self.pending_repairs.is_empty()
            || self.pending_atom_qhead < self.pending_atom_triggers.len()
    }

    /// Activates one input disequality.
    pub(crate) fn enqueue_input_disequality(&mut self, input: DiseqInput) -> DisequalityEntry {
        let entry = DisequalityEntry {
            lhs: input.lhs,
            rhs: input.rhs,
            reason_lit: input.reason_lit,
        };
        let diseq_index = self.active_disequalities.len();
        self.active_disequalities.push(entry);
        self.term_disequalities[input.lhs.index()].push(diseq_index);
        self.disequality_incident_log.push((input.lhs, diseq_index));
        if input.lhs != input.rhs {
            self.term_disequalities[input.rhs.index()].push(diseq_index);
            self.disequality_incident_log.push((input.rhs, diseq_index));
        }
        entry
    }

    /// Rolls back all reversible mutations down to `undo_len`.
    fn rollback_to(&mut self, undo_len: usize) {
        while self.undo_log.len() > undo_len {
            match self.undo_log.pop().expect("checked above") {
                Undo::Parent { node, old_parent } => {
                    self.parent[node.index()] = old_parent;
                }
                Undo::ClassSize { root, old_size } => {
                    self.class_size[root.index()] = old_size;
                }
                Undo::ClassNext { node, old_next } => {
                    self.next[node.index()] = old_next;
                }
            }
        }
    }

    /// Appends one undirected merge edge and its two directed adjacency entries.
    #[inline(always)]
    pub(crate) fn push_merge_edge(&mut self, lhs: Term, rhs: Term, reason: MergeReason) {
        let edge_index = self.edges.len();
        let lhs_directed = DirectedEdge::lhs_to_rhs(edge_index);
        let rhs_directed = DirectedEdge::rhs_to_lhs(edge_index);
        let lhs_head = self.graph_heads[lhs.index()];
        let rhs_head = self.graph_heads[rhs.index()];
        self.edges.push(MergeEdge {
            lhs,
            rhs,
            next_lhs: lhs_head,
            next_rhs: rhs_head,
            reason,
        });
        self.graph_heads[lhs.index()] = lhs_directed;
        self.graph_heads[rhs.index()] = rhs_directed;
    }

    /// Truncates merge edges while maintaining adjacency-list heads.
    fn truncate_merge_edges(&mut self, keep_len: usize) {
        while self.edges.len() > keep_len {
            let edge_index = self.edges.len() - 1;
            let edge = self.edges[edge_index];
            let lhs_directed = DirectedEdge::lhs_to_rhs(edge_index);
            let rhs_directed = DirectedEdge::rhs_to_lhs(edge_index);
            debug_assert_eq!(self.graph_heads[edge.lhs.index()], lhs_directed);
            debug_assert_eq!(self.graph_heads[edge.rhs.index()], rhs_directed);

            self.graph_heads[edge.lhs.index()] = edge.next_lhs;
            self.graph_heads[edge.rhs.index()] = edge.next_rhs;
            self.edges.pop();
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
}
