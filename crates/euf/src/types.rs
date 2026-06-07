//! Handle newtypes and borrowed EUF query views.

use crate::arena::InternKey;

/// One uninterpreted or built-in sort handle.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct Sort(u32);

impl Sort {
    /// Creates one sort handle from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One function symbol handle.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct Symbol(u32);

impl Symbol {
    /// Returns the zero-based index named by this handle.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one symbol handle from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One canonical term handle.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct Term(u32);

impl Term {
    /// Returns the zero-based index named by this handle.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one term handle from a zero-based index.
    pub(crate) fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One canonical theory atom handle.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct TheoryAtom(u32);

impl TheoryAtom {
    /// Returns the zero-based index named by this handle.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one atom handle from a zero-based index.
    fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

/// One current equivalence-class representative handle.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct EClass(u32);

impl EClass {
    /// Returns the zero-based index named by this handle.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates one class handle from a zero-based index.
    pub(crate) fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }
}

impl InternKey for Sort {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl InternKey for Symbol {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl InternKey for Term {
    fn from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl InternKey for TheoryAtom {
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
    pub arg_sorts: &'a [Sort],
    /// Result sort.
    pub result_sort: Sort,
}

/// Borrowed query view for one canonical EUF term.
///
/// Semantically, a term is one application in `Symbol × Vec<Term>`.
///
/// # Encoding
///
/// - `(fun, args)` is encoded directly as `Self { fun, args }`.
/// - Nullary symbols use `args = &[]`; there is no separate constant variant.
/// - Callers must only intern terms whose argument count and argument sorts match the
///   declared signature of `fun`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct TermRef<'a> {
    /// The applied symbol.
    pub fun: Symbol,
    /// Borrowed child-term slice.
    pub args: &'a [Term],
}

impl<'a> TermRef<'a> {
    /// Returns one borrowed nullary application view.
    pub fn nullary(fun: Symbol) -> Self {
        Self { fun, args: &[] }
    }
}

/// Borrowed query view for one theory atom.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum AtomRef {
    /// Equality between two terms.
    Eq(Term, Term),
}

/// Kind of theory atom represented by one SAT literal.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AtomLiteralKind {
    /// Equality atom over two term endpoints.
    Eq {
        /// Left endpoint.
        lhs: Term,
        /// Right endpoint.
        rhs: Term,
        /// Whether the literal is positive.
        positive: bool,
    },
}
