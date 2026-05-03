//! Command-line entrypoint that reads SMT-LIB from stdin and prints solver
//! results for each `check-sat`.

use std::io::Read;
use std::sync::Arc;

use lower::{Solver, SolverEvent};
use smtlib_lexer::parse_many;
use smtlib_syntax::Command;

fn main() {
    let mut input = String::new();
    if let Err(error) = std::io::stdin().read_to_string(&mut input) {
        eprintln!("failed to read stdin: {error}");
        std::process::exit(1);
    }

    let exprs = match parse_many(&input) {
        Ok(exprs) => exprs,
        Err(error) => {
            eprintln!("parse error: {error}");
            println!("unsupported");
            std::process::exit(1);
        }
    };

    let source = Arc::<str>::from(input);
    let mut solver = Solver::new();
    for expr in exprs {
        let command = match Command::from_sexpr(&source, expr) {
            Ok(command) => command,
            Err(error) => {
                eprintln!("command error: {error}");
                println!("unsupported");
                std::process::exit(1);
            }
        };
        let event = match solver.handle_command(command) {
            Ok(event) => event,
            Err(error) => {
                eprintln!("solver error: {error}");
                println!("unsupported");
                std::process::exit(1);
            }
        };
        match event {
            SolverEvent::None => {}
            SolverEvent::CheckSat(result) => println!("{}", result.as_smtlib()),
            SolverEvent::Exit => break,
        }
    }
}
