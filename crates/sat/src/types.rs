use std::ops::Not;

/// SMT assertion-stack scope created by `push` and `pop`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct Scope(u32);

impl Scope {
    /// The root scope.
    pub const ROOT: Self = Self(0);

    /// Returns the zero-based scope depth.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates a scope from one zero-based depth.
    pub(crate) fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }

    /// Returns the next deeper scope.
    pub(crate) fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

/// A zero-based propositional variable identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Var(u32);

impl Var {
    /// Creates a variable from a zero-based index known to fit in the encoding.
    pub(crate) fn from_index(index: usize) -> Self {
        debug_assert!(u32::try_from(index).is_ok());
        Self(index as u32)
    }

    /// Returns the zero-based index of this variable.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A propositional literal encoded as `var << 1 | negated`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Lit(u32);

impl Lit {
    /// Creates a literal from a variable and its sign.
    pub fn new(var: Var, negated: bool) -> Self {
        Self(((var.index() as u32) << 1) | negated as u32)
    }

    /// Returns the underlying variable.
    pub fn var(self) -> Var {
        Var::from_index((self.0 >> 1) as usize)
    }

    /// Returns whether the literal is negated.
    pub fn is_negated(self) -> bool {
        (self.0 & 1) != 0
    }

    /// Returns the zero-based packed literal index.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates a literal from a packed internal representation.
    pub(crate) fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Converts a non-zero DIMACS integer into a literal.
    ///
    /// Positive integers map to positive literals and negative integers map to
    /// negated literals.
    ///
    /// # Panics
    ///
    /// Panics if `x == 0`, because `0` is the DIMACS clause terminator rather than
    /// a literal.
    pub(crate) fn from_dimacs(x: i32) -> Self {
        assert!(x != 0);
        let v = Var::from_index((x.unsigned_abs() - 1) as usize);
        Lit::new(v, x < 0)
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit::from_raw(self.0 ^ 1)
    }
}
