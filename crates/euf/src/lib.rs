//! Equality with uninterpreted functions as one SAT theory module.
//!
//! This crate follows the layering in `docs/incremental-qf-uf-design.md`:
//!
//! - permanent term and atom registry,
//! - search-local congruence-closure state,
//! - SAT-facing theory interface implemented by [`EufTheory`].

use std::collections::VecDeque;
use std::hash::{BuildHasher, Hash, Hasher};
use std::marker::PhantomData;
use std::ptr::NonNull;

use bumpalo::Bump;
use hashbrown::HashMap;
use sat::{AssertionLevel, Lit, Theory, TheoryClause, TheoryClauseKind, Var};

/// One uninterpreted or built-in sort identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct SortId(u32);

impl SortId {
    /// Returns the zero-based index named by this identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one sort identifier from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One function symbol identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct SymbolId(u32);

impl SymbolId {
    /// Returns the zero-based index named by this identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one symbol identifier from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One canonical term identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct TermId(u32);

impl TermId {
    /// Returns the zero-based index named by this identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one term identifier from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One canonical theory atom identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct TheoryAtomId(u32);

impl TheoryAtomId {
    /// Returns the zero-based index named by this identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one atom identifier from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One current equivalence-class representative identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct EClassId(u32);

impl EClassId {
    /// Returns the zero-based index named by this identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one class identifier from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One permanently allocated string payload inside one bump arena.
#[derive(Debug)]
pub struct ArenaStr {
    /// Raw fat pointer to bump-owned string data.
    raw: NonNull<str>,
}

impl ArenaStr {
    /// Reborrows the stored string.
    ///
    /// # Safety
    ///
    /// The owner of this handle must guarantee that `raw` still points to one live
    /// `str` allocation for the duration of the returned borrow.
    unsafe fn as_str<'a>(&self) -> &'a str {
        // SAFETY: callers uphold the arena-liveness invariant.
        unsafe { self.raw.as_ref() }
    }
}

impl Copy for ArenaStr {}

impl Clone for ArenaStr {
    fn clone(&self) -> Self {
        *self
    }
}

impl PartialEq for ArenaStr {
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_str() == other.as_str() }
    }
}

impl Eq for ArenaStr {}

impl Hash for ArenaStr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_str().hash(state) }
    }
}

/// One permanently allocated slice payload inside one bump arena.
#[derive(Debug)]
pub struct ArenaSlice<T> {
    /// Raw fat pointer to bump-owned slice data.
    raw: NonNull<[T]>,
    /// Marker preserving the element type.
    marker: PhantomData<T>,
}

impl<T> ArenaSlice<T> {
    /// Reborrows the stored slice.
    ///
    /// # Safety
    ///
    /// The owner of this handle must guarantee that `raw` still points to one live
    /// `[T]` allocation for the duration of the returned borrow.
    unsafe fn as_slice<'a>(&self) -> &'a [T] {
        // SAFETY: callers uphold the arena-liveness invariant.
        unsafe { self.raw.as_ref() }
    }
}

impl<T> Copy for ArenaSlice<T> {}

impl<T> Clone for ArenaSlice<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: PartialEq> PartialEq for ArenaSlice<T> {
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_slice() == other.as_slice() }
    }
}

impl<T: Eq> Eq for ArenaSlice<T> {}

impl<T: Hash> Hash for ArenaSlice<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_slice().hash(state) }
    }
}

/// Hashes one borrowed probe key with the same build-hasher used by one table.
fn make_hash<S: BuildHasher, T: Hash>(hasher: &S, value: &T) -> u64 {
    hasher.hash_one(value)
}

/// One canonical sort object.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Sort {
    /// The SMT-LIB built-in `Bool` sort.
    Bool,
    /// One uninterpreted sort with a declared name.
    Uninterpreted {
        /// Declared sort name.
        name: ArenaStr,
    },
}

impl Sort {
    /// Returns whether this stored sort matches one borrowed probe.
    fn matches_ref(&self, sort: SortRef<'_>) -> bool {
        match (self, sort) {
            (Self::Bool, SortRef::Bool) => true,
            (Self::Uninterpreted { name }, SortRef::Uninterpreted { name: query }) => {
                // SAFETY: `name` points into live registry storage.
                unsafe { name.as_str() == query }
            }
            _ => false,
        }
    }
}

/// One canonical function symbol object.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Symbol {
    /// Declared symbol name.
    name: ArenaStr,
    /// Declared argument sorts.
    arg_sorts: ArenaSlice<SortId>,
    /// Declared result sort.
    result_sort: SortId,
}

impl Symbol {
    /// Returns whether this stored symbol matches one borrowed probe.
    fn matches_ref(&self, symbol: SymbolRef<'_>) -> bool {
        // SAFETY: both arena-backed payload handles point into live registry storage.
        unsafe {
            self.name.as_str() == symbol.name
                && self.arg_sorts.as_slice() == symbol.arg_sorts
                && self.result_sort == symbol.result_sort
        }
    }
}

/// One canonical term object.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Term {
    /// One nullary application represented by its symbol.
    Const(SymbolId),
    /// One n-ary application node.
    App {
        /// The applied symbol.
        fun: SymbolId,
        /// Canonical child terms.
        args: ArenaSlice<TermId>,
    },
}

impl Term {
    /// Returns whether this stored term matches one borrowed probe.
    fn matches_ref(&self, term: TermRef<'_>) -> bool {
        match (self, term) {
            (Self::Const(symbol), TermRef::Const(query)) => *symbol == query,
            (
                Self::App { fun, args },
                TermRef::App {
                    fun: query_fun,
                    args: query_args,
                },
            ) => {
                // SAFETY: `args` points into live registry storage.
                unsafe { *fun == query_fun && args.as_slice() == query_args }
            }
            _ => false,
        }
    }
}

/// One canonical theory atom object.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Atom {
    /// Equality between two terms.
    Eq(TermId, TermId),
}

impl Atom {
    /// Returns whether this stored atom matches one borrowed probe.
    fn matches_ref(&self, atom: AtomRef) -> bool {
        match (*self, atom) {
            (Self::Eq(lhs, rhs), AtomRef::Eq(query_lhs, query_rhs)) => {
                lhs == query_lhs && rhs == query_rhs
            }
        }
    }
}

/// Borrowed query view for one sort.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum SortRef<'a> {
    /// The built-in Boolean sort.
    Bool,
    /// One uninterpreted sort named by `name`.
    Uninterpreted {
        /// Borrowed sort name.
        name: &'a str,
    },
}

/// Borrowed query view for one function symbol.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct SymbolRef<'a> {
    /// Symbol name.
    pub name: &'a str,
    /// Borrowed argument-sort slice.
    pub arg_sorts: &'a [SortId],
    /// Result sort.
    pub result_sort: SortId,
}

/// Borrowed query view for one term.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum TermRef<'a> {
    /// One nullary application.
    Const(SymbolId),
    /// One n-ary application.
    App {
        /// The applied symbol.
        fun: SymbolId,
        /// Borrowed child-term slice.
        args: &'a [TermId],
    },
}

/// Borrowed query view for one theory atom.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum AtomRef {
    /// Equality between two terms.
    Eq(TermId, TermId),
}

/// Solver-lifetime storage for permanent registry payloads.
#[derive(Debug, Default)]
pub struct RegistryStorage {
    /// Append-only allocator for names and argument slices.
    bump: Bump,
}

impl RegistryStorage {
    /// Allocates one owned string inside the bump arena.
    fn alloc_str(&self, text: &str) -> ArenaStr {
        ArenaStr {
            raw: NonNull::from(self.bump.alloc_str(text)),
        }
    }

    /// Allocates one copied slice inside the bump arena.
    fn alloc_slice<T: Copy>(&self, slice: &[T]) -> ArenaSlice<T> {
        ArenaSlice {
            raw: NonNull::from(self.bump.alloc_slice_copy(slice)),
            marker: PhantomData,
        }
    }
}

/// One canonical interner table.
#[derive(Debug)]
pub struct Interner<Id, T> {
    /// Stored canonical values in insertion order.
    values: Vec<T>,
    /// Fast lookup by stored value.
    index: HashMap<T, Id>,
}

impl<Id, T> Default for Interner<Id, T> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            index: HashMap::new(),
        }
    }
}

/// Internal helper for interner identifier construction.
pub trait InternId: Copy {
    /// Creates one identifier from a zero-based insertion index.
    fn from_index(index: usize) -> Self;
}

impl InternId for SortId {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl InternId for SymbolId {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl InternId for TermId {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl InternId for TheoryAtomId {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl<Id: InternId + Eq + Hash, T: Clone + Eq + Hash> Interner<Id, T> {
    /// Interns `value`, returning the existing identifier when present.
    fn intern(&mut self, value: T) -> Id {
        if let Some(&id) = self.index.get(&value) {
            return id;
        }
        let id = Id::from_index(self.values.len());
        self.values.push(value.clone());
        self.index.insert(value, id);
        id
    }

    /// Returns the value named by `id`.
    fn get(&self, index: usize) -> &T {
        &self.values[index]
    }

    /// Returns the number of interned values.
    fn len(&self) -> usize {
        self.values.len()
    }
}

/// Permanent registry of canonical terms, symbols, sorts, and atoms.
#[derive(Debug, Default)]
pub struct Registry {
    /// Solver-lifetime payload storage.
    storage: RegistryStorage,
    /// Canonical sort table.
    sorts: Interner<SortId, Sort>,
    /// Canonical symbol table.
    symbols: Interner<SymbolId, Symbol>,
    /// Canonical term table.
    terms: Interner<TermId, Term>,
    /// Canonical atom table.
    atoms: Interner<TheoryAtomId, Atom>,
    /// Derived sort for each interned term.
    term_sort: Vec<SortId>,
    /// Permanent atom incidence lists.
    term_atoms: Vec<Vec<TheoryAtomId>>,
    /// Permanent structural parent use-lists.
    parent_apps: Vec<Vec<TermId>>,
    /// Lazily created Boolean sort.
    bool_sort: Option<SortId>,
    /// Lazily created canonical true term.
    true_term: Option<TermId>,
}

impl Registry {
    /// Interns one sort.
    pub fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId {
        if let Some(id) = self.find_sort(sort) {
            return id;
        }
        let owned = match sort {
            SortRef::Bool => Sort::Bool,
            SortRef::Uninterpreted { name } => Sort::Uninterpreted {
                name: self.storage.alloc_str(name),
            },
        };
        let id = self.sorts.intern(owned);
        if matches!(sort, SortRef::Bool) {
            self.bool_sort = Some(id);
        }
        id
    }

    /// Interns one symbol.
    pub fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId {
        if let Some(id) = self.find_symbol(symbol) {
            return id;
        }
        let owned = Symbol {
            name: self.storage.alloc_str(symbol.name),
            arg_sorts: self.storage.alloc_slice(symbol.arg_sorts),
            result_sort: symbol.result_sort,
        };
        self.symbols.intern(owned)
    }

    /// Interns one term together with its already-known sort.
    pub fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        if let Some(id) = self.find_term(term) {
            return id;
        }
        let owned = match term {
            TermRef::Const(symbol) => Term::Const(symbol),
            TermRef::App { fun, args } => Term::App {
                fun,
                args: self.storage.alloc_slice(args),
            },
        };
        let id = self.terms.intern(owned);
        self.term_sort.push(sort);
        self.term_atoms.push(Vec::new());
        self.parent_apps.push(Vec::new());

        if let TermRef::App { args, .. } = term {
            for &arg in args {
                self.parent_apps[arg.index()].push(id);
            }
        }

        id
    }

    /// Interns one theory atom.
    pub fn intern_atom(&mut self, atom: AtomRef) -> TheoryAtomId {
        let normalized = match atom {
            AtomRef::Eq(lhs, rhs) if rhs < lhs => Atom::Eq(rhs, lhs),
            AtomRef::Eq(lhs, rhs) => Atom::Eq(lhs, rhs),
        };
        if let Some(id) = self.find_atom(match normalized {
            Atom::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        }) {
            return id;
        }
        let id = self.atoms.intern(normalized);
        let Atom::Eq(lhs, rhs) = normalized;
        self.term_atoms[lhs.index()].push(id);
        if lhs != rhs {
            self.term_atoms[rhs.index()].push(id);
        }
        id
    }

    /// Finds one previously interned sort.
    pub fn find_sort(&self, sort: SortRef<'_>) -> Option<SortId> {
        let hash = make_hash(self.sorts.index.hasher(), &sort);
        self.sorts
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(sort))
            .map(|(_, &id)| id)
    }

    /// Finds one previously interned symbol.
    pub fn find_symbol(&self, symbol: SymbolRef<'_>) -> Option<SymbolId> {
        let hash = make_hash(self.symbols.index.hasher(), &symbol);
        self.symbols
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(symbol))
            .map(|(_, &id)| id)
    }

    /// Finds one previously interned term.
    pub fn find_term(&self, term: TermRef<'_>) -> Option<TermId> {
        let hash = make_hash(self.terms.index.hasher(), &term);
        self.terms
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(term))
            .map(|(_, &id)| id)
    }

    /// Finds one previously interned atom.
    pub fn find_atom(&self, atom: AtomRef) -> Option<TheoryAtomId> {
        let atom = match atom {
            AtomRef::Eq(lhs, rhs) if rhs < lhs => AtomRef::Eq(rhs, lhs),
            other => other,
        };
        let hash = make_hash(self.atoms.index.hasher(), &atom);
        self.atoms
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(atom))
            .map(|(_, &id)| id)
    }

    /// Returns one borrowed view over the canonical sort named by `id`.
    pub fn sort_ref(&self, id: SortId) -> SortRef<'_> {
        match self.sorts.get(id.index()) {
            Sort::Bool => SortRef::Bool,
            Sort::Uninterpreted { name } => {
                // SAFETY: `name` points into `self.storage`.
                SortRef::Uninterpreted {
                    name: unsafe { name.as_str() },
                }
            }
        }
    }

    /// Returns one borrowed view over the canonical symbol named by `id`.
    pub fn symbol_ref(&self, id: SymbolId) -> SymbolRef<'_> {
        let symbol = self.symbols.get(id.index());
        SymbolRef {
            // SAFETY: every handle stored in this registry points into `self.storage`.
            name: unsafe { symbol.name.as_str() },
            // SAFETY: every handle stored in this registry points into `self.storage`.
            arg_sorts: unsafe { symbol.arg_sorts.as_slice() },
            result_sort: symbol.result_sort,
        }
    }

    /// Returns one borrowed view over the canonical term named by `id`.
    pub fn term_ref(&self, id: TermId) -> TermRef<'_> {
        match self.terms.get(id.index()) {
            Term::Const(symbol) => TermRef::Const(*symbol),
            Term::App { fun, args } => TermRef::App {
                fun: *fun,
                // SAFETY: every handle stored in this registry points into `self.storage`.
                args: unsafe { args.as_slice() },
            },
        }
    }

    /// Returns one borrowed view over the canonical atom named by `id`.
    pub fn atom_ref(&self, id: TheoryAtomId) -> AtomRef {
        match *self.atoms.get(id.index()) {
            Atom::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        }
    }

    /// Returns the number of canonical terms.
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Returns the number of canonical atoms.
    pub fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    /// Returns the sort of one interned term.
    pub fn term_sort(&self, id: TermId) -> SortId {
        self.term_sort[id.index()]
    }

    /// Returns the permanent incidence list for `id`.
    pub fn term_atoms(&self, id: TermId) -> &[TheoryAtomId] {
        &self.term_atoms[id.index()]
    }

    /// Returns the permanent structural parent list for `id`.
    pub fn parent_apps(&self, id: TermId) -> &[TermId] {
        &self.parent_apps[id.index()]
    }

    /// Returns the canonical Boolean sort, creating it on demand.
    pub fn bool_sort(&mut self) -> SortId {
        if let Some(sort) = self.bool_sort {
            return sort;
        }
        self.intern_sort(SortRef::Bool)
    }

    /// Returns the canonical Boolean true term, creating it on demand.
    pub fn true_term(&mut self) -> TermId {
        if let Some(term) = self.true_term {
            return term;
        }
        let bool_sort = self.bool_sort();
        let symbol = self.intern_symbol(SymbolRef {
            name: "true",
            arg_sorts: &[],
            result_sort: bool_sort,
        });
        let term = self.intern_term(TermRef::Const(symbol), bool_sort);
        self.true_term = Some(term);
        term
    }
}

/// One input equality waiting to merge.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeInput {
    /// Left term.
    lhs: TermId,
    /// Right term.
    rhs: TermId,
    /// Assigned SAT literal justifying this merge.
    reason_lit: Lit,
}

/// One input disequality waiting to become active.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DiseqInput {
    /// Left term.
    lhs: TermId,
    /// Right term.
    rhs: TermId,
    /// Assigned SAT literal justifying this disequality.
    reason_lit: Lit,
}

/// Borrowed congruence signature used for allocation-free probing.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSigRef<'a> {
    /// Function symbol.
    fun: SymbolId,
    /// Current class representatives of the arguments.
    arg_reps: &'a [EClassId],
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

/// One active edge in the equality proof graph.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeEdge {
    /// Left endpoint.
    lhs: TermId,
    /// Right endpoint.
    rhs: TermId,
    /// Justification for this equality edge.
    reason: MergeReason,
}

/// One active disequality fact.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DisequalityEntry {
    /// Left endpoint.
    lhs: TermId,
    /// Right endpoint.
    rhs: TermId,
    /// SAT literal asserting disequality.
    reason_lit: Lit,
}

/// One SAT-decision-level rollback marker.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct SatLevelMarker {
    /// Undo-log length at level entry.
    undo_len: usize,
    /// Merge-edge length at level entry.
    merge_edges_len: usize,
    /// Active-disequality length at level entry.
    active_disequalities_len: usize,
    /// Pending-merge queue length at level entry.
    pending_merges_len: usize,
    /// Pending-repair queue length at level entry.
    pending_repairs_len: usize,
    /// Pending-atom-trigger queue length at level entry.
    pending_atom_triggers_len: usize,
    /// Pending-clause queue length at level entry.
    pending_clauses_len: usize,
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
    /// Class-head pointer update.
    ClassHead {
        /// Root updated in `class_head`.
        root: EClassId,
        /// Previous head value.
        old_head: TermId,
    },
    /// Class-tail pointer update.
    ClassTail {
        /// Root updated in `class_tail`.
        root: EClassId,
        /// Previous tail value.
        old_tail: TermId,
    },
    /// Linked-list successor change.
    ClassNext {
        /// Node updated in `next_in_class`.
        node: TermId,
        /// Previous successor value.
        old_next: Option<TermId>,
    },
    /// Congruence-table insertion to remove on rollback.
    CongruenceInsert {
        /// Inserted owned key.
        key: CongruenceSig,
    },
}

/// Search-local equality engine state.
#[derive(Debug, Default)]
pub struct SearchState {
    /// Search-lifetime arena for owned congruence signatures.
    congruence_storage: Bump,
    /// Union-find representative for each term.
    parent: Vec<EClassId>,
    /// Rank heuristic for each representative.
    rank: Vec<u32>,
    /// Head of each class-membership linked list.
    class_head: Vec<TermId>,
    /// Tail of each class-membership linked list.
    class_tail: Vec<TermId>,
    /// Successor link for each term in one class-membership list.
    next_in_class: Vec<Option<TermId>>,
    /// Congruence table keyed by function symbol and current representative arguments.
    congruence_table: HashMap<CongruenceSig, TermId>,
    /// Scratch buffer used while building borrowed congruence signatures.
    congruence_sig_scratch: Vec<EClassId>,
    /// Pending input merges still to process.
    pending_merges: VecDeque<MergeInput>,
    /// Parent applications that must be reconsidered.
    pending_repairs: VecDeque<TermId>,
    /// Theory atoms affected by recent class changes.
    pending_atom_triggers: Vec<TheoryAtomId>,
    /// Read cursor into `pending_atom_triggers`.
    pending_atom_qhead: usize,
    /// Per-atom queue-membership bit.
    atom_is_enqueued: Vec<bool>,
    /// Pending theory clauses ready to return to SAT.
    pending_clauses: Vec<TheoryClause>,
    /// Currently active disequalities.
    active_disequalities: Vec<DisequalityEntry>,
    /// Active equality-proof graph.
    merge_edges: Vec<MergeEdge>,
    /// Reversible mutation log.
    undo_log: Vec<Undo>,
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
        self.class_head.clear();
        self.class_tail.clear();
        self.next_in_class.clear();
        self.congruence_storage.reset();

        for index in 0..nterms {
            let term = TermId::from_index(index);
            let rep = EClassId::from_index(index);
            self.parent.push(rep);
            self.rank.push(0);
            self.class_head.push(term);
            self.class_tail.push(term);
            self.next_in_class.push(None);
        }

        self.congruence_table.clear();
        self.congruence_sig_scratch.clear();
        self.pending_merges.clear();
        self.pending_repairs.clear();
        self.pending_atom_triggers.clear();
        self.pending_atom_qhead = 0;
        self.atom_is_enqueued.clear();
        self.atom_is_enqueued.resize(registry.num_atoms(), false);
        self.pending_clauses.clear();
        self.active_disequalities.clear();
        self.merge_edges.clear();
        self.undo_log.clear();
        self.level_markers.clear();
    }

    /// Pushes one rollback marker aligned with a new SAT decision level.
    pub fn push_sat_level(&mut self) {
        self.level_markers.push(SatLevelMarker {
            undo_len: self.undo_log.len(),
            merge_edges_len: self.merge_edges.len(),
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
            self.merge_edges.truncate(marker.merge_edges_len);
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

        self.undo_log.push(Undo::ClassTail {
            root: survivor,
            old_tail: self.class_tail[survivor.index()],
        });
        self.undo_log.push(Undo::ClassNext {
            node: self.class_tail[survivor.index()],
            old_next: self.next_in_class[self.class_tail[survivor.index()].index()],
        });
        self.next_in_class[self.class_tail[survivor.index()].index()] =
            Some(self.class_head[absorbed.index()]);
        self.class_tail[survivor.index()] = self.class_tail[absorbed.index()];

        survivor
    }

    /// Builds one borrowed congruence signature for `parent`.
    pub fn make_congruence_sig<'a>(
        &'a mut self,
        registry: &Registry,
        parent: TermId,
    ) -> CongruenceSigRef<'a> {
        let Some(fun) = self.fill_congruence_sig_scratch(registry, parent) else {
            panic!("congruence signatures require application terms");
        };
        CongruenceSigRef {
            fun,
            arg_reps: &self.congruence_sig_scratch,
        }
    }

    /// Fills `congruence_sig_scratch` with the current signature of `parent`.
    fn fill_congruence_sig_scratch(
        &mut self,
        registry: &Registry,
        parent: TermId,
    ) -> Option<SymbolId> {
        let TermRef::App { fun, args } = registry.term_ref(parent) else {
            return None;
        };
        let union_find_parent = &self.parent;
        self.congruence_sig_scratch.clear();
        for &arg in args {
            self.congruence_sig_scratch
                .push(Self::find_in_parent(union_find_parent, arg));
        }
        Some(fun)
    }

    /// Finds one existing congruence-table owner for the current scratch signature.
    fn find_congruent_parent_for_current_sig(&self, fun: SymbolId) -> Option<TermId> {
        let sig = CongruenceSigRef {
            fun,
            arg_reps: &self.congruence_sig_scratch,
        };
        let hash = make_hash(self.congruence_table.hasher(), &sig);
        self.congruence_table
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(sig))
            .map(|(_, &owner)| owner)
    }

    /// Materializes one owned congruence signature from the current scratch buffer.
    fn own_current_congruence_sig(&self, fun: SymbolId) -> CongruenceSig {
        let sig = CongruenceSigRef {
            fun,
            arg_reps: &self.congruence_sig_scratch,
        };
        self.own_congruence_sig(sig)
    }

    /// Finds one existing congruence-table owner for `parent`, if any.
    fn find_congruent_parent(&mut self, registry: &Registry, parent: TermId) -> Option<TermId> {
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
                Undo::ClassHead { root, old_head } => {
                    self.class_head[root.index()] = old_head;
                }
                Undo::ClassTail { root, old_tail } => {
                    self.class_tail[root.index()] = old_tail;
                }
                Undo::ClassNext { node, old_next } => {
                    self.next_in_class[node.index()] = old_next;
                }
                Undo::CongruenceInsert { key } => {
                    self.congruence_table.remove(&key);
                }
            }
        }
    }

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

    /// Constructs one propagation explanation clause from already collected premises.
    pub fn explain_propagation(&self, propagated: Lit, support: &[Lit]) -> ExplanationClause {
        ExplanationClause {
            propagated: Some(propagated),
            premises: support.to_vec().into_boxed_slice(),
        }
    }

    /// Stores one owned congruence signature inside the search-local bump arena.
    fn own_congruence_sig(&self, sig: CongruenceSigRef<'_>) -> CongruenceSig {
        CongruenceSig {
            fun: sig.fun,
            arg_reps: ArenaSlice {
                raw: NonNull::from(self.congruence_storage.alloc_slice_copy(sig.arg_reps)),
                marker: PhantomData,
            },
        }
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

/// Kind of theory atom represented by one SAT literal.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AtomLiteralKind {
    /// Equality atom over two term endpoints.
    Eq {
        /// Left endpoint.
        lhs: TermId,
        /// Right endpoint.
        rhs: TermId,
        /// Whether the literal is positive.
        positive: bool,
    },
}

/// The EUF theory module exposed to the SAT engine.
#[derive(Debug, Default)]
pub struct EufTheory {
    /// Permanent canonical registry.
    registry: Registry,
    /// Search-local congruence closure state.
    search: SearchState,
    /// Forward map from theory atoms to SAT variables.
    theory_atom_to_var: Vec<Var>,
    /// Reverse map from SAT variables to theory atoms.
    var_to_theory_atom: Vec<Option<TheoryAtomId>>,
    /// Queue of assigned theory literals not yet processed by EUF.
    pending_assignments: VecDeque<Lit>,
    /// Search-local atom assignment cache.
    atom_value: Vec<Option<bool>>,
    /// Search-local assigned atom trail.
    atom_trail: Vec<TheoryAtomId>,
    /// Search-local decision-level starts for `atom_trail`.
    atom_trail_lim: Vec<usize>,
}

impl EufTheory {
    /// Creates one empty theory object.
    pub fn new() -> Self {
        Self::default()
    }

    /// Interns one sort.
    pub fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId {
        self.registry.intern_sort(sort)
    }

    /// Interns one symbol.
    pub fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId {
        self.registry.intern_symbol(symbol)
    }

    /// Interns one term.
    pub fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        self.registry.intern_term(term, sort)
    }

    /// Interns one equality atom and binds it to `sat_var`.
    pub fn intern_equality_atom(&mut self, lhs: TermId, rhs: TermId, sat_var: Var) -> TheoryAtomId {
        let atom = self.registry.intern_atom(AtomRef::Eq(lhs, rhs));
        if self.theory_atom_to_var.len() <= atom.index() {
            self.theory_atom_to_var.resize(atom.index() + 1, sat_var);
        }
        let existing = self.theory_atom_to_var[atom.index()];
        assert_eq!(
            existing, sat_var,
            "canonical theory atom cannot be bound to multiple SAT variables",
        );

        if self.var_to_theory_atom.len() <= sat_var.index() {
            self.var_to_theory_atom.resize(sat_var.index() + 1, None);
        }
        match self.var_to_theory_atom[sat_var.index()] {
            Some(existing_atom) => assert_eq!(existing_atom, atom),
            None => self.var_to_theory_atom[sat_var.index()] = Some(atom),
        }
        atom
    }

    /// Returns the canonical atom, if any, bound to `var`.
    pub fn theory_atom_for_var(&self, var: Var) -> Option<TheoryAtomId> {
        self.var_to_theory_atom.get(var.index()).copied().flatten()
    }

    /// Decodes one SAT literal as one EUF atom literal, if applicable.
    pub fn atom_literal_kind(&self, lit: Lit) -> Option<AtomLiteralKind> {
        let atom = self.theory_atom_for_var(lit.var())?;
        match self.registry.atom_ref(atom) {
            AtomRef::Eq(lhs, rhs) => Some(AtomLiteralKind::Eq {
                lhs,
                rhs,
                positive: !lit.is_negated(),
            }),
        }
    }

    /// Processes all theory assignments currently buffered from SAT.
    fn process_pending_assignments(&mut self) {
        while let Some(lit) = self.pending_assignments.pop_front() {
            let Some(atom) = self.theory_atom_for_var(lit.var()) else {
                continue;
            };
            let value = !lit.is_negated();
            if self.atom_value.len() <= atom.index() {
                self.atom_value.resize(atom.index() + 1, None);
            }
            self.atom_value[atom.index()] = Some(value);
            self.atom_trail.push(atom);

            match self.atom_literal_kind(lit) {
                Some(AtomLiteralKind::Eq {
                    lhs,
                    rhs,
                    positive: true,
                }) => {
                    self.search.enqueue_input_equality(MergeInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                    self.saturate();
                }
                Some(AtomLiteralKind::Eq {
                    lhs,
                    rhs,
                    positive: false,
                }) => {
                    self.search.enqueue_input_disequality(DiseqInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                    self.check_active_disequalities();
                }
                None => {}
            }
        }
    }

    /// Saturates the current congruence state.
    fn saturate(&mut self) {
        loop {
            while let Some(input) = self.search.pending_merges.pop_front() {
                self.merge_input(input);
                self.repair_congruence();
                self.check_active_disequalities();
            }

            self.process_pending_atom_triggers();

            if self.search.pending_merges.is_empty()
                && self.search.pending_repairs.is_empty()
                && self.search.pending_atom_qhead == self.search.pending_atom_triggers.len()
            {
                return;
            }
        }
    }

    /// Applies one input equality merge.
    fn merge_input(&mut self, input: MergeInput) {
        let lhs_root = self.search.find(input.lhs);
        let rhs_root = self.search.find(input.rhs);
        if lhs_root == rhs_root {
            return;
        }
        let merged_root = self.search.union_roots(lhs_root, rhs_root);
        self.search.merge_edges.push(MergeEdge {
            lhs: input.lhs,
            rhs: input.rhs,
            reason: MergeReason::InputEq {
                reason_lit: input.reason_lit,
            },
        });
        self.enqueue_repairs_for_class(merged_root);
        self.enqueue_atom_triggers_for_class(merged_root);
    }

    /// Applies one congruence-driven merge.
    fn merge_due_to_congruence(&mut self, lhs_parent: TermId, rhs_parent: TermId) {
        let lhs_root = self.search.find(lhs_parent);
        let rhs_root = self.search.find(rhs_parent);
        if lhs_root == rhs_root {
            return;
        }
        let merged_root = self.search.union_roots(lhs_root, rhs_root);
        self.search.merge_edges.push(MergeEdge {
            lhs: lhs_parent,
            rhs: rhs_parent,
            reason: MergeReason::Congruence {
                left_parent: lhs_parent,
                right_parent: rhs_parent,
            },
        });
        self.enqueue_repairs_for_class(merged_root);
        self.enqueue_atom_triggers_for_class(merged_root);
    }

    /// Repairs congruence closure after recent merges.
    fn repair_congruence(&mut self) {
        while let Some(parent) = self.search.pending_repairs.pop_front() {
            self.repair_parent_app(parent);
        }
    }

    /// Enqueues parent applications of one changed class.
    fn enqueue_repairs_for_class(&mut self, root: EClassId) {
        let mut current = Some(self.search.class_head[root.index()]);
        while let Some(term) = current {
            for &parent in self.registry.parent_apps(term) {
                self.search.pending_repairs.push_back(parent);
            }
            current = self.search.next_in_class[term.index()];
        }
    }

    /// Enqueues atom triggers attached to one changed class.
    fn enqueue_atom_triggers_for_class(&mut self, root: EClassId) {
        let mut current = Some(self.search.class_head[root.index()]);
        while let Some(term) = current {
            for &atom in self.registry.term_atoms(term) {
                self.search.enqueue_atom_trigger(atom);
            }
            current = self.search.next_in_class[term.index()];
        }
    }

    /// Rechecks one parent application under current child representatives.
    fn repair_parent_app(&mut self, parent: TermId) {
        let existing = match self.registry.term_ref(parent) {
            TermRef::Const(_) => return,
            TermRef::App { .. } => self.search.find_congruent_parent(&self.registry, parent),
        };

        if let Some(existing) = existing {
            if self.search.find(existing) != self.search.find(parent) {
                self.merge_due_to_congruence(existing, parent);
            }
            return;
        }

        let Some(fun) = self
            .search
            .fill_congruence_sig_scratch(&self.registry, parent)
        else {
            return;
        };
        let owned = self.search.own_current_congruence_sig(fun);
        self.search
            .undo_log
            .push(Undo::CongruenceInsert { key: owned.clone() });
        self.search.congruence_table.insert(owned, parent);
    }

    /// Emits conflicts for any active disequality that is now violated.
    fn check_active_disequalities(&mut self) {
        let mut explanation = Vec::new();
        for &diseq in &self.search.active_disequalities {
            if self.search.find(diseq.lhs) != self.search.find(diseq.rhs) {
                continue;
            }
            self.search
                .explain_conflict(&self.registry, diseq, &mut explanation);
            self.search.pending_clauses.push(self.build_theory_clause(
                &explanation,
                None,
                TheoryClauseKind::ConflictExplanation,
            ));
            break;
        }
    }

    /// Processes every affected atom trigger.
    fn process_pending_atom_triggers(&mut self) {
        while self.search.pending_atom_qhead < self.search.pending_atom_triggers.len() {
            let atom = self.search.pending_atom_triggers[self.search.pending_atom_qhead];
            self.search.pending_atom_qhead += 1;
            self.search.atom_is_enqueued[atom.index()] = false;
            self.evaluate_atom_trigger(atom);
        }
    }

    /// Re-evaluates one registered atom under current equality classes.
    fn evaluate_atom_trigger(&mut self, atom: TheoryAtomId) {
        let AtomRef::Eq(lhs, rhs) = self.registry.atom_ref(atom);
        let Some(&sat_var) = self.theory_atom_to_var.get(atom.index()) else {
            return;
        };
        let lit = Lit::new(sat_var, false);
        let equal_now = self.search.find(lhs) == self.search.find(rhs);
        let current_value = self.atom_value.get(atom.index()).copied().flatten();

        if equal_now && current_value.is_none() {
            let mut support = Vec::new();
            self.search
                .explain_equality(&self.registry, lhs, rhs, &mut support);
            self.search.pending_clauses.push(self.build_theory_clause(
                &support,
                Some(lit),
                TheoryClauseKind::PropagationExplanation,
            ));
        }

        if equal_now && current_value == Some(false) {
            let diseq = DisequalityEntry {
                lhs,
                rhs,
                reason_lit: !lit,
            };
            let mut support = Vec::new();
            self.search
                .explain_conflict(&self.registry, diseq, &mut support);
            self.search.pending_clauses.push(self.build_theory_clause(
                &support,
                None,
                TheoryClauseKind::ConflictExplanation,
            ));
        }
    }

    /// Builds one SAT-facing theory clause from already explained premise literals.
    fn build_theory_clause(
        &self,
        premises: &[Lit],
        propagated: Option<Lit>,
        kind: TheoryClauseKind,
    ) -> TheoryClause {
        let mut lits = Vec::with_capacity(premises.len() + usize::from(propagated.is_some()));
        for &premise in premises {
            lits.push(!premise);
        }
        if let Some(propagated) = propagated {
            lits.push(propagated);
        }
        TheoryClause {
            lits: lits.into_boxed_slice(),
            assertion_level: AssertionLevel::ROOT,
            kind,
        }
    }
}

impl Theory for EufTheory {
    fn notify_search_start(&mut self) {
        self.search.reset_for_registry(&self.registry);
        self.pending_assignments.clear();
        self.atom_value.clear();
        self.atom_value.resize(self.registry.num_atoms(), None);
        self.atom_trail.clear();
        self.atom_trail_lim.clear();
    }

    fn notify_new_decision_level(&mut self) {
        self.search.push_sat_level();
        self.atom_trail_lim.push(self.atom_trail.len());
    }

    fn notify_assignment(&mut self, lit: Lit) {
        if self.theory_atom_for_var(lit.var()).is_some() {
            self.pending_assignments.push_back(lit);
        }
    }

    fn notify_backtrack(&mut self, level: usize) {
        self.search.pop_sat_levels(level);
        while self.atom_trail_lim.len() > level {
            let keep = self.atom_trail_lim.pop().expect("checked above");
            while self.atom_trail.len() > keep {
                let atom = self.atom_trail.pop().expect("checked above");
                self.atom_value[atom.index()] = None;
            }
        }
    }

    fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>) {
        self.process_pending_assignments();
        self.saturate();
        out.append(&mut self.search.pending_clauses);
    }

    fn final_check(&mut self, out: &mut Vec<TheoryClause>) {
        self.process_pending_assignments();
        self.saturate();
        out.append(&mut self.search.pending_clauses);
    }

    fn has_pending_work(&self) -> bool {
        !self.pending_assignments.is_empty()
            || !self.search.pending_clauses.is_empty()
            || !self.search.pending_merges.is_empty()
            || !self.search.pending_repairs.is_empty()
            || self.search.pending_atom_qhead < self.search.pending_atom_triggers.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bool_lit(var: Var) -> Lit {
        Lit::new(var, false)
    }

    fn neg_bool_lit(var: Var) -> Lit {
        Lit::new(var, true)
    }

    #[test]
    fn registry_interns_terms_and_atoms_canonically() {
        let mut theory = EufTheory::new();
        let mut sat = sat::Solver::new();
        let bool_sort = theory.intern_sort(SortRef::Bool);
        let u_sort = theory.intern_sort(SortRef::Uninterpreted { name: "U" });
        let f = theory.intern_symbol(SymbolRef {
            name: "f",
            arg_sorts: &[u_sort],
            result_sort: u_sort,
        });
        let a_sym = theory.intern_symbol(SymbolRef {
            name: "a",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let a = theory.intern_term(TermRef::Const(a_sym), u_sort);
        let fa = theory.intern_term(TermRef::App { fun: f, args: &[a] }, u_sort);

        assert_eq!(theory.registry.term_sort(fa), u_sort);
        assert_eq!(theory.registry.bool_sort(), bool_sort);

        let sat_var = sat.new_var();
        let atom = theory.intern_equality_atom(fa, a, sat_var);
        assert_eq!(theory.theory_atom_for_var(sat_var), Some(atom));
    }

    #[test]
    fn theory_reports_conflict_for_negative_congruence_atom() {
        let mut sat = sat::Solver::new();
        let mut theory = EufTheory::new();
        let u_sort = theory.intern_sort(SortRef::Uninterpreted { name: "U" });
        let f = theory.intern_symbol(SymbolRef {
            name: "f",
            arg_sorts: &[u_sort],
            result_sort: u_sort,
        });
        let a_sym = theory.intern_symbol(SymbolRef {
            name: "a",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let b_sym = theory.intern_symbol(SymbolRef {
            name: "b",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let a = theory.intern_term(TermRef::Const(a_sym), u_sort);
        let b = theory.intern_term(TermRef::Const(b_sym), u_sort);
        let fa = theory.intern_term(TermRef::App { fun: f, args: &[a] }, u_sort);
        let fb = theory.intern_term(TermRef::App { fun: f, args: &[b] }, u_sort);

        let ab_var = sat.new_var();
        let fafb_var = sat.new_var();
        let ab = bool_lit(ab_var);
        let not_fafb = neg_bool_lit(fafb_var);
        theory.intern_equality_atom(a, b, ab_var);
        theory.intern_equality_atom(fa, fb, fafb_var);

        let _ = sat.add_clause(&[ab]);
        let _ = sat.add_clause(&[not_fafb]);

        assert_eq!(
            sat.solve_with_assumptions(&[], &mut theory),
            sat::SatResult::Unsat
        );
    }
}
