//! Compile-time coverage for generated `bitsum` APIs and diagnostics.

/// Verifies `bitsum` expansion behavior that only appears at compile time.
#[test]
fn ui() {
    let cases = trybuild::TestCases::new();
    cases.pass("tests/ui/pass/*.rs");
    cases.compile_fail("tests/ui/fail/*.rs");
}
