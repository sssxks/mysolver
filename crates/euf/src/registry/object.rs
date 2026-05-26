//! Private canonical objects stored by the permanent registry.
//!
//! These types are intentionally confined to the `registry` module. Each object may
//! carry arena-backed handles with no lifetime parameter, so safe helper methods such
//! as `matches_ref()` rely on the module invariant that every embedded handle points
//! into one live [`crate::arena::RegistryStorage`] owned by the enclosing
//! [`super::Registry`].

use crate::arena::{ArenaSlice, ArenaStr};
use crate::ids::{AtomRef, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef};

/// One canonical sort object stored in the permanent registry.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(super) enum Sort {
    /// The SMT-LIB built-in `Bool` sort.
    Bool,
    /// One uninterpreted sort with a declared name.
    Uninterpreted {
        /// Declared sort name stored in registry arena memory.
        name: ArenaStr,
    },
}

impl Sort {
    /// Returns whether this stored sort matches one borrowed probe.
    ///
    /// This method is safe because the `registry` module does not expose constructors
    /// for canonical stored objects. Every `ArenaStr` embedded here therefore comes
    /// from the live registry arena owned by the surrounding [`super::Registry`].
    pub(crate) fn matches_ref(&self, sort: SortRef<'_>) -> bool {
        match (self, sort) {
            (Self::Bool, SortRef::Bool) => true,
            (Self::Uninterpreted { name }, SortRef::Uninterpreted { name: query }) => {
                // SAFETY: `Sort` values are registry-private, so `name` can only point
                // into the live arena owned by the enclosing registry.
                unsafe { name.as_str() == query }
            }
            _ => false,
        }
    }
}

/// One canonical function symbol object stored in the permanent registry.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(super) struct Symbol {
    /// Declared symbol name stored in registry arena memory.
    pub(super) name: ArenaStr,
    /// Declared argument sorts stored in registry arena memory.
    pub(super) arg_sorts: ArenaSlice<SortId>,
    /// Declared result sort.
    pub(super) result_sort: SortId,
}

impl Symbol {
    /// Returns whether this stored symbol matches one borrowed probe.
    ///
    /// This method is safe for the same reason as [`Sort::matches_ref`]: registry
    /// privacy prevents outside code from constructing `Symbol` values that carry
    /// dangling arena handles.
    pub(crate) fn matches_ref(&self, symbol: SymbolRef<'_>) -> bool {
        // SAFETY: `Symbol` values are registry-private, so both handles can only
        // point into the live arena owned by the enclosing registry.
        unsafe {
            self.name.as_str() == symbol.name
                && self.arg_sorts.as_slice() == symbol.arg_sorts
                && self.result_sort == symbol.result_sort
        }
    }
}

/// One canonical term object stored in the permanent registry.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(super) enum Term {
    /// One nullary application represented by its symbol.
    Const(SymbolId),
    /// One n-ary application node.
    App {
        /// The applied symbol.
        fun: SymbolId,
        /// Canonical child terms stored in registry arena memory.
        args: ArenaSlice<TermId>,
    },
}

impl Term {
    /// Returns whether this stored term matches one borrowed probe.
    ///
    /// This method is safe because `Term` values remain private to `registry`, so the
    /// embedded arena slice can only originate from the surrounding live registry
    /// storage.
    pub(crate) fn matches_ref(&self, term: TermRef<'_>) -> bool {
        match (self, term) {
            (Self::Const(symbol), TermRef::Const(query)) => *symbol == query,
            (
                Self::App { fun, args },
                TermRef::App {
                    fun: query_fun,
                    args: query_args,
                },
            ) => {
                // SAFETY: `Term` values are registry-private, so `args` can only point
                // into the live arena owned by the enclosing registry.
                unsafe { *fun == query_fun && args.as_slice() == query_args }
            }
            _ => false,
        }
    }
}

/// One canonical theory atom object stored in the permanent registry.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) enum Atom {
    /// Equality between two terms.
    Eq(TermId, TermId),
}

impl Atom {
    /// Returns whether this stored atom matches one borrowed probe.
    pub(crate) fn matches_ref(&self, atom: AtomRef) -> bool {
        match (*self, atom) {
            (Self::Eq(lhs, rhs), AtomRef::Eq(query_lhs, query_rhs)) => {
                lhs == query_lhs && rhs == query_rhs
            }
        }
    }
}
