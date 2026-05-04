/// Outcome of a budget-aware EUF consistency check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EufCheckOutcome {
    /// The atom set is jointly consistent.
    Consistent,
    /// The atom set implies a concrete theory contradiction.
    Conflict(TheoryConflict),
    /// The caller-provided budget was exhausted before the check finished.
    Interrupted,
}

/// Inconsistency discovered by the EUF checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryConflict {
    /// Left side of the conflicting disequality.
    pub left: TermId,
    /// Right side of the conflicting disequality.
    pub right: TermId,
}
