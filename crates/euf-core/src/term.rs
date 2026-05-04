/// Stable identifier for one interned term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(u32);

impl TermId {
    /// Returns the internal dense index backing this term identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Stable identifier for one interned function symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunId(u32);

impl FunId {
    /// Returns the internal dense index backing this function identifier.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// One interned EUF term represented as a function symbol plus argument terms.
///
/// Constants are encoded as nullary applications whose [`Self::args`] slice is empty.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    /// Applied function symbol.
    fun: FunId,
    /// Argument term identifiers in call order.
    args: Box<[TermId]>,
}

impl Term {
    /// Returns the function symbol applied by this term.
    pub fn fun(&self) -> FunId {
        self.fun
    }

    /// Returns the argument terms in application order.
    pub fn args(&self) -> &[TermId] {
        &self.args
    }
}

/// One theory atom to check under EUF.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryAtom {
    /// Equality constraint.
    Eq(TermId, TermId),
    /// Disequality constraint.
    Diseq(TermId, TermId),
}
