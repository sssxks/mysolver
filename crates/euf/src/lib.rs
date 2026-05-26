//! Equality with uninterpreted functions as one SAT theory module.
//!
//! This crate follows the layering in `docs/incremental-qf-uf-design.md`:
//!
//! - permanent term and atom registry,
//! - search-local congruence-closure state,
//! - SAT-facing theory interface implemented by [`EufTheory`].

/// Arena-backed storage handles and interning helpers.
mod arena;
/// Identifier newtypes and canonical EUF objects.
mod ids;
/// Permanent registry of canonical terms, sorts, symbols, and atoms.
mod registry;

/// Equality and theory-clause explanation support.
mod explain;
/// Search-local congruence-closure state and rollback bookkeeping.
mod search_state;
/// SAT-facing EUF theory integration.
mod theory;

pub use arena::{ArenaSlice, ArenaStr, InternId, Interner, RegistryStorage};
pub use explain::{EqualityExplanation, ExplanationClause};
pub use ids::{
    Atom, AtomRef, EClassId, Sort, SortId, SortRef, Symbol, SymbolId, SymbolRef, Term, TermId,
    TermRef, TheoryAtomId,
};
pub use registry::Registry;
pub use search_state::{
    CongruenceSig, CongruenceSigRef, DiseqInput, DisequalityEntry, MergeEdge, MergeInput,
    MergeReason, SatLevelMarker, SearchState, Undo,
};
pub use theory::{AtomLiteralKind, EufTheory};
