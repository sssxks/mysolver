//! Identifier newtypes and canonical EUF objects.

use crate::arena::{ArenaSlice, ArenaStr, InternId};

/// One uninterpreted or built-in sort identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct SortId(u32);

impl SortId {
    /// Returns the zero-based index named by this identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one sort identifier from a zero-based index.
    pub(crate) fn from_index(index: usize) -> Self {
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
    pub(crate) fn from_index(index: usize) -> Self {
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
    pub(crate) fn from_index(index: usize) -> Self {
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
    pub(crate) fn from_index(index: usize) -> Self {
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
    pub(crate) fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
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
    pub(crate) fn matches_ref(&self, sort: SortRef<'_>) -> bool {
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
    pub(crate) name: ArenaStr,
    /// Declared argument sorts.
    pub(crate) arg_sorts: ArenaSlice<SortId>,
    /// Declared result sort.
    pub(crate) result_sort: SortId,
}

impl Symbol {
    /// Returns whether this stored symbol matches one borrowed probe.
    pub(crate) fn matches_ref(&self, symbol: SymbolRef<'_>) -> bool {
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
    pub(crate) fn matches_ref(&self, atom: AtomRef) -> bool {
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
