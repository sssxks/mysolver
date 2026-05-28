use crate::types::{Command, SExpr};

/// Parses a complete SMT-LIB input string into commands.
pub(crate) fn parse_commands(input: &str) -> Result<Vec<Command>, String> {
    let tokens = tokenize(input);
    let (exprs, next) = parse_many(&tokens, 0)?;
    if next != tokens.len() {
        return Err("trailing tokens after parse".to_owned());
    }
    exprs.into_iter().map(command_from_sexpr).collect()
}

/// Tokenizes one SMT-LIB input string into atoms and parentheses.
fn tokenize(input: &str) -> Vec<Box<str>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == ';' {
            while let Some(next) = chars.peek() {
                if *next == '\n' {
                    break;
                }
                chars.next();
            }
            continue;
        }
        match ch {
            '(' | ')' => {
                if !current.is_empty() {
                    tokens.push(current.clone().into_boxed_str());
                    current.clear();
                    maybe_emit_parse_progress_sample(tokens.len());
                }
                tokens.push(ch.to_string().into_boxed_str());
                maybe_emit_parse_progress_sample(tokens.len());
            }
            ch if ch.is_whitespace() => {
                if !current.is_empty() {
                    tokens.push(current.clone().into_boxed_str());
                    current.clear();
                    maybe_emit_parse_progress_sample(tokens.len());
                }
            }
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        tokens.push(current.into_boxed_str());
        maybe_emit_parse_progress_sample(tokens.len());
    }
    tokens
}

/// Parses as many S-expressions as possible starting at `start`.
fn parse_many(tokens: &[Box<str>], mut start: usize) -> Result<(Vec<SExpr>, usize), String> {
    let mut exprs = Vec::new();
    while start < tokens.len() {
        if tokens[start].as_ref() == ")" {
            break;
        }
        let (expr, next) = parse_one(tokens, start)?;
        exprs.push(expr);
        maybe_emit_parse_progress_sample(exprs.len());
        start = next;
    }
    Ok((exprs, start))
}

/// Parses one S-expression starting at `start`.
fn parse_one(tokens: &[Box<str>], start: usize) -> Result<(SExpr, usize), String> {
    let token = tokens
        .get(start)
        .ok_or_else(|| "unexpected end of input".to_owned())?;
    if token.as_ref() == "(" {
        let (items, next) = parse_many(tokens, start + 1)?;
        if tokens.get(next).map(|token| token.as_ref()) != Some(")") {
            return Err("missing closing `)`".to_owned());
        }
        return Ok((SExpr::List(items), next + 1));
    }
    if token.as_ref() == ")" {
        return Err("unexpected `)`".to_owned());
    }
    Ok((SExpr::Atom(token.clone()), start + 1))
}

/// Converts one top-level S-expression into one supported command.
fn command_from_sexpr(expr: SExpr) -> Result<Command, String> {
    let SExpr::List(items) = expr else {
        return Err("top-level form must be a list".to_owned());
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return Err("top-level form requires an atom head".to_owned());
    };

    match head.as_ref() {
        "set-logic" => {
            let [_, SExpr::Atom(logic)] = items.as_slice() else {
                return Err("malformed set-logic".to_owned());
            };
            Ok(Command::SetLogic(logic.clone()))
        }
        "set-info" => Ok(Command::SetInfo),
        "declare-sort" => {
            let [_, SExpr::Atom(name), SExpr::Atom(arity)] = items.as_slice() else {
                return Err("malformed declare-sort".to_owned());
            };
            if arity.as_ref() != "0" {
                return Err("only zero-arity declare-sort is supported".to_owned());
            }
            Ok(Command::DeclareSort { name: name.clone() })
        }
        "declare-fun" => {
            let [_, SExpr::Atom(name), SExpr::List(args), SExpr::Atom(result)] = items.as_slice()
            else {
                return Err("malformed declare-fun".to_owned());
            };
            let args = args
                .iter()
                .map(|arg| match arg {
                    SExpr::Atom(atom) => Ok(atom.clone()),
                    _ => Err("function sort arguments must be atoms".to_owned()),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Command::DeclareFun {
                name: name.clone(),
                args,
                result: result.clone(),
            })
        }
        "declare-const" => {
            let [_, SExpr::Atom(name), SExpr::Atom(sort)] = items.as_slice() else {
                return Err("malformed declare-const".to_owned());
            };
            Ok(Command::DeclareConst {
                name: name.clone(),
                sort: sort.clone(),
            })
        }
        "assert" => {
            let [_, expr] = items.as_slice() else {
                return Err("malformed assert".to_owned());
            };
            Ok(Command::Assert(expr.clone()))
        }
        "push" => {
            let [_, SExpr::Atom(levels)] = items.as_slice() else {
                return Err("malformed push".to_owned());
            };
            let levels = levels
                .parse::<u32>()
                .map_err(|error| format!("invalid push level: {error}"))?;
            Ok(Command::Push(levels))
        }
        "pop" => {
            let [_, SExpr::Atom(levels)] = items.as_slice() else {
                return Err("malformed pop".to_owned());
            };
            let levels = levels
                .parse::<u32>()
                .map_err(|error| format!("invalid pop level: {error}"))?;
            Ok(Command::Pop(levels))
        }
        "check-sat" => Ok(Command::CheckSat),
        "exit" => Ok(Command::Exit),
        other => Err(format!("unsupported command: {other}")),
    }
}

/// Emits one default telemetry sample while the front-end parser is still working.
#[cfg(feature = "telemetry")]
#[inline(always)]
fn maybe_emit_parse_progress_sample(progress: usize) {
    if progress & 1023 == 0 {
        telemetry::maybe_emit_sample(telemetry::Gauges::default);
    }
}

/// Compiles to a no-op when telemetry instrumentation is disabled.
#[cfg(not(feature = "telemetry"))]
#[inline(always)]
fn maybe_emit_parse_progress_sample(_progress: usize) {}
