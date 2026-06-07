//! Theory interface consumed by the CDCL SAT engine.
//!
//! The types in this module are the public CDCL(T) boundary. A theory module
//! observes SAT trail changes through [`Theory`] callbacks and returns fully
//! explained clauses over SAT [`Literal`]s when it finds propagations, lemmas, or
//! conflicts.

#[cfg(feature = "telemetry")]
use crate::telemetry;
#[cfg(feature = "telemetry")]
use crate::telemetry::Gauges;
use crate::{Level, Literal, Scope};

/// Classification used only for theory-clause metrics and debugging.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TheoryClauseKind {
    /// Clause originating from frontend input.
    Input,
    /// General theory lemma.
    Lemma,
    /// Clause explaining a theory propagation.
    PropagationExplanation,
    /// Clause explaining a theory conflict.
    ConflictExplanation,
}

/// One theory clause waiting to be inserted into SAT.
///
/// Semantically, a theory clause is `Literal* × Scope × TheoryClauseKind`.
///
/// where:
/// - `Literal*` is a finite disjunction of SAT literals,
/// - `Scope` is the shallowest assertion-stack scope where the clause remains
///   justified,
/// - `TheoryClauseKind` records why the theory produced the clause.
///
/// # Encoding
///
/// - `Literal*` -> [`Self::lits`] as a boxed slice.
/// - `Scope` -> [`Self::scope`].
/// - `TheoryClauseKind` -> [`Self::kind`].
/// - Invariants: literals must refer to variables currently known to the SAT
///   solver at the synchronization point where the clause is drained.
///
/// The SAT solver normalizes clauses before insertion. Theory producers do not
/// need to sort or deduplicate literals, but they must report a sound scope.
#[derive(Clone, Debug)]
pub struct TheoryClause {
    /// Fully explained clause over SAT literals.
    pub lits: Box<[Literal]>,
    /// Shallowest scope where this clause is valid.
    ///
    /// The theory producer must set this to at least the deepest `push()` frame
    /// that any non-literal dependency of the clause relies on. For input clauses
    /// and general theory lemmas, SAT uses this field as the clause scope. For
    /// propagation and conflict explanations, SAT also raises the stored scope to
    /// cover variables appearing in `lits`, but empty explanations and dependencies
    /// not represented by literals still rely on this value. Under-reporting this
    /// scope is unsound because learned clauses may survive a `pop()` that removes
    /// their justification; over-reporting is sound but prevents reuse in shallower
    /// scopes.
    pub scope: Scope,
    /// Classification used only for metrics and debugging.
    pub kind: TheoryClauseKind,
}

/// The minimal CDCL(T) callback surface consumed by the SAT engine.
pub trait Theory {
    /// Called once at the start of each SAT search.
    fn notify_search_start(&mut self);

    /// Called immediately after the SAT solver opens a new CDCL level.
    fn notify_new_level(&mut self);

    /// Called for one new assignment on the SAT trail.
    fn notify_assignment(&mut self, lit: Literal);

    /// Called after the SAT solver backtracks to one CDCL level.
    fn notify_backtrack(&mut self, level: Level);

    /// Checks pending theory work and drains any clauses that became available.
    fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>);

    /// Returns whether the theory still has pending work to flush into SAT.
    fn has_pending_work(&self) -> bool;

    /// Emits one telemetry sample when SAT reaches a safe checkpoint.
    #[cfg(feature = "telemetry")]
    fn maybe_emit_telemetry_sample(&self, sat_gauges: Gauges) {
        telemetry::maybe_emit_sample(|| telemetry::CombinedGauges {
            sat: sat_gauges,
            euf: telemetry::EufGauges::default(),
        });
    }
}

/// Trivial theory adapter used by plain SAT solving.
#[derive(Debug, Default)]
pub struct NullTheory;

impl Theory for NullTheory {
    fn notify_search_start(&mut self) {}

    fn notify_new_level(&mut self) {}

    fn notify_assignment(&mut self, _lit: Literal) {}

    fn notify_backtrack(&mut self, _level: Level) {}

    fn drain_clauses(&mut self, _out: &mut Vec<TheoryClause>) {}

    fn has_pending_work(&self) -> bool {
        false
    }
}
