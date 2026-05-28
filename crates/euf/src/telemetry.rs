//! EUF-local telemetry adapters.

use sat::telemetry::Gauges as SatGauges;

#[cfg(feature = "telemetry")]
pub(crate) use telemetry::EufGauges as Gauges;

#[cfg(not(feature = "telemetry"))]
/// Placeholder EUF gauge type used when telemetry instrumentation is disabled.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Gauges;

/// Records one asserted input equality.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_input_equality() {
    telemetry::record_euf_input_equality();
}

/// Records one asserted input equality.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_input_equality() {}

/// Records one asserted input disequality.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_input_disequality() {
    telemetry::record_euf_input_disequality();
}

/// Records one asserted input disequality.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_input_disequality() {}

/// Records one congruence-driven merge.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_congruence_merge() {
    telemetry::record_euf_congruence_merge();
}

/// Records one congruence-driven merge.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_congruence_merge() {}

/// Records one theory propagation clause.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_theory_propagation() {
    telemetry::record_euf_theory_propagation();
}

/// Records one theory propagation clause.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_theory_propagation() {}

/// Records one theory conflict clause.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn record_theory_conflict() {
    telemetry::record_euf_theory_conflict();
}

/// Records one theory conflict clause.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn record_theory_conflict() {}

/// Emits one combined SAT+EUF sample.
#[cfg(feature = "telemetry")]
#[inline(always)]
pub(crate) fn maybe_emit_sample(sat: SatGauges, euf: Gauges) {
    telemetry::maybe_emit_sample(|| telemetry::Gauges { sat, euf });
}

/// Emits one combined SAT+EUF sample.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
pub(crate) fn maybe_emit_sample(_sat: SatGauges, _euf: Gauges) {}
