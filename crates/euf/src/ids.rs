//! Identifier newtypes and borrowed EUF query views.

use crate::arena::InternId;

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
