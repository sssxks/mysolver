//! Equality with uninterpreted functions as one SAT theory module.
//!
//! This crate follows the layering in `docs/incremental-qf-uf-design.md`:
//!
//! - permanent term and atom registry,
//! - search-local congruence-closure state,
//! - SAT-facing theory interface implemented by [`EufTheory`].

/// Arena-backed storage handles and interning helpers.
mod arena;
/// Permanent registry of canonical terms, sorts, symbols, and atoms.
mod registry;
/// EUF-local telemetry adapters.
mod telemetry;
/// Identifier newtypes and canonical EUF objects.
mod types;

/// Equality and theory-clause explanation support.
mod explain;
/// Search-local congruence-closure state and rollback bookkeeping.
mod search_state;
/// SAT-facing EUF theory integration.
mod theory;

pub use registry::Registry;
pub use search_state::{
    CongruenceSig, CongruenceSigRef, DiseqInput, DisequalityEntry, MergeEdge, MergeInput,
    MergeReason, SatLevelMarker, SearchState, Undo,
};
pub use theory::EufTheory;
pub use types::{
    AtomLiteralKind, AtomRef, EClassId, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef,
    TheoryAtomId,
};
