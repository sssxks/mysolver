//! Private canonical objects stored by the permanent registry.
//!
//! These types are intentionally confined to the `registry` module. Each object may
//! carry arena-backed handles with no lifetime parameter, so safe helper methods such
//! as `matches_ref()` rely on the module invariant that every embedded handle points
//! into one live [`crate::arena::RegistryStorage`] owned by the enclosing
//! [`super::Registry`].

use crate::arena::{ArenaSlice, ArenaStr, MatchesRef};
use crate::types::{AtomRef, Sort, SortRef, Symbol, SymbolRef, Term, TermRef};

/// One canonical sort object stored in the permanent registry.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(super) enum SortEntry {
    /// The SMT-LIB built-in `Bool` sort.
    Bool,
    /// One uninterpreted sort with a declared name.
    Uninterpreted {
        /// Declared sort name stored in registry arena memory.
        name: ArenaStr,
    },
}

impl MatchesRef for SortEntry {
    type Query<'a> = SortRef<'a>;

    /// Returns whether this stored sort matches one borrowed probe.
    ///
    /// This method is safe because the `registry` module does not expose constructors
    /// for canonical stored objects. Every `ArenaStr` embedded here therefore comes
    /// from the live registry arena owned by the surrounding [`super::Registry`].
    fn matches_ref(&self, sort: Self::Query<'_>) -> bool {
        match (self, sort) {
            (Self::Bool, SortRef::Bool) => true,
            (Self::Uninterpreted { name }, SortRef::Uninterpreted { name: query }) => {
                // SAFETY: `SortEntry` values are registry-private, so `name` can only point
                // into the live arena owned by the enclosing registry.
                unsafe { name.as_str() == query }
            }
            _ => false,
        }
    }
}

/// One canonical function symbol object stored in the permanent registry.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(super) struct SymbolEntry {
    /// Declared symbol name stored in registry arena memory.
    pub(super) name: ArenaStr,
    /// Declared argument sorts stored in registry arena memory.
    pub(super) arg_sorts: ArenaSlice<Sort>,
    /// Declared result sort.
    pub(super) result_sort: Sort,
}

impl MatchesRef for SymbolEntry {
    type Query<'a> = SymbolRef<'a>;

    /// Returns whether this stored symbol matches one borrowed probe.
    ///
    /// This method is safe for the same reason as `SortEntry`'s borrowed-match logic:
    /// registry privacy prevents outside code from constructing `SymbolEntry` values that
    /// carry dangling arena handles.
    fn matches_ref(&self, symbol: Self::Query<'_>) -> bool {
        // SAFETY: `SymbolEntry` values are registry-private, so both handles can only
        // point into the live arena owned by the enclosing registry.
        unsafe {
            self.name.as_str() == symbol.name
                && self.arg_sorts.as_slice() == symbol.arg_sorts
                && self.result_sort == symbol.result_sort
        }
    }
}

/// One canonical term object stored in the permanent registry.
///
/// Semantically, a term is one application in `Symbol × Term*`.
///
/// # Encoding
///
/// - `(fun, args)` is stored directly in the two fields below.
/// - Nullary applications use one empty arena slice; there is no distinct constant
///   encoding.
/// - The enclosing registry guarantees that `args.len()` and each child term sort
///   match the declared signature of `fun`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(super) struct TermEntry {
    /// The applied symbol.
    pub(super) fun: Symbol,
    /// Canonical child terms stored in registry arena memory.
    pub(super) args: ArenaSlice<Term>,
}

impl MatchesRef for TermEntry {
    type Query<'a> = TermRef<'a>;

    /// Returns whether this stored term matches one borrowed probe.
    ///
    /// This method is safe because `TermEntry` values remain private to `registry`, so the
    /// embedded arena slice can only originate from the surrounding live registry
    /// storage.
    fn matches_ref(&self, term: Self::Query<'_>) -> bool {
        // SAFETY: `TermEntry` values are registry-private, so `args` can only point into
        // the live arena owned by the enclosing registry.
        unsafe { self.fun == term.fun && self.args.as_slice() == term.args }
    }
}

/// One canonical theory atom object stored in the permanent registry.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) enum AtomEntry {
    /// Equality between two terms.
    Eq(Term, Term),
}

impl MatchesRef for AtomEntry {
    type Query<'a> = AtomRef;

    /// Returns whether this stored atom matches one borrowed probe.
    fn matches_ref(&self, atom: Self::Query<'_>) -> bool {
        match (*self, atom) {
            (Self::Eq(lhs, rhs), AtomRef::Eq(query_lhs, query_rhs)) => {
                lhs == query_lhs && rhs == query_rhs
            }
        }
    }
}
