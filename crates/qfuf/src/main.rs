//! Binary entrypoint for the incremental QF-UF solver.

/// Runs the QF-UF solver over stdin/stdout.
fn main() -> std::process::ExitCode {
    match qfuf::run_stdio() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::from(2)
        }
    }
}
