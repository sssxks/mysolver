//! Incremental SMT-LIB driver for QF-UF over the local `sat` and `euf` crates.

/// The incremental QF-UF solver driver.
mod driver;
/// SMT-LIB tokenizer and command parser.
mod parser;
/// Shared AST and lowering types.
mod types;

use crate::driver::Driver;
use crate::parser::parse_commands;

/// Runs the solver over one complete SMT-LIB input string and returns the textual
/// responses produced by query commands.
pub fn run_script(input: &str) -> Result<String, String> {
    let mut driver = Driver::new();
    run_script_with_driver(&mut driver, input)
}

/// Runs the solver over one complete SMT-LIB input string, recording periodic
/// telemetry samples to the given path. Returns the textual responses.
#[cfg(feature = "telemetry")]
pub fn run_script_with_telemetry(
    input: &str,
    telemetry_path: &std::path::Path,
) -> Result<String, String> {
    use telemetry::TelemetryRecorder;

    let mut driver = Driver::new();
    let recorder = TelemetryRecorder::start(telemetry_path)
        .map_err(|error| format!("failed to start telemetry recorder: {error}"))?;
    let result = run_script_with_driver(&mut driver, input);
    finish_telemetry(recorder, driver.telemetry_gauges(), result)
}

/// Runs the script using one preallocated driver.
fn run_script_with_driver(driver: &mut Driver, input: &str) -> Result<String, String> {
    let commands = parse_commands(input)?;
    let mut output = String::new();

    for command in commands {
        if let Some(line) = driver.execute(command)? {
            output.push_str(&line);
            output.push('\n');
        }
        maybe_emit_progress_sample(driver);
    }

    Ok(output)
}

/// Emits one telemetry sample at a command boundary when a timer tick is pending.
#[cfg(feature = "telemetry")]
#[inline(always)]
fn maybe_emit_progress_sample(driver: &Driver) {
    telemetry::maybe_emit_sample(|| driver.telemetry_gauges());
}

/// Compiles to a no-op when telemetry instrumentation is disabled.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
fn maybe_emit_progress_sample(_driver: &Driver) {}

/// Finalizes the telemetry recorder and merges any recorder error with the solver result.
#[cfg(feature = "telemetry")]
fn finish_telemetry(
    recorder: telemetry::TelemetryRecorder,
    gauges: telemetry::Gauges,
    result: Result<String, String>,
) -> Result<String, String> {
    let finish_result = recorder
        .finish(gauges)
        .map_err(|error| format!("failed to finalize telemetry recorder: {error}"));
    match (result, finish_result) {
        (Ok(output), Ok(())) => Ok(output),
        (Ok(_), Err(error)) => Err(error),
        (Err(error), Ok(())) => Err(error),
        (Err(error), Err(finish_error)) => Err(format!("{error}; {finish_error}")),
    }
}

#[cfg(test)]
mod tests {
    use super::run_script;

    #[test]
    fn solves_simple_unsat_euf_script() {
        let input = r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun f (U) U)
            (assert (= a b))
            (assert (not (= (f a) (f b))))
            (check-sat)
            (exit)
        "#;
        assert_eq!(run_script(input).expect("script should run"), "unsat\n");
    }

    #[test]
    fn supports_push_pop_and_multiple_queries() {
        let input = r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (assert (= a b))
            (check-sat)
            (push 1)
            (assert (not (= a b)))
            (check-sat)
            (pop 1)
            (check-sat)
            (exit)
        "#;
        assert_eq!(
            run_script(input).expect("script should run"),
            "sat\nunsat\nsat\n"
        );
    }

    #[test]
    fn supports_asserting_more_constraints_after_sat() {
        let input = r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun c () U)
            (assert (or (= a b) (= a c)))
            (check-sat)
            (assert (not (= a b)))
            (check-sat)
            (exit)
        "#;
        assert_eq!(run_script(input).expect("script should run"), "sat\nsat\n");
    }

    #[test]
    fn rejects_bare_non_nullary_function_symbols() {
        let input = r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-const a U)
            (declare-fun f (U) U)
            (assert (= f (f a)))
            (check-sat)
            (exit)
        "#;
        assert_eq!(
            run_script(input),
            Err("symbol `f` expects 1 arguments".to_owned())
        );
    }

    #[test]
    fn rejects_wrong_application_arity() {
        let input = r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-const a U)
            (assert (= a (a a)))
            (check-sat)
            (exit)
        "#;
        assert_eq!(
            run_script(input),
            Err("symbol `a` expects 0 arguments, got 1".to_owned())
        );
    }

    #[test]
    fn treats_nullary_application_lists_as_the_same_term() {
        let input = r#"
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-const a U)
            (assert (not (= a (a))))
            (check-sat)
            (exit)
        "#;
        assert_eq!(run_script(input).expect("script should run"), "unsat\n");
    }
}
