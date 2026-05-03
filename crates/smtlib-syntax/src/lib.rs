//! Syntax-level SMT-LIB command model for the subset currently used by the
//! solver and benchmark harnesses.
//!
//! The parser intentionally preserves a small amount of benchmark metadata. In
//! particular, `set-info :status ...` is parsed into [`SetInfo::expected_status`]
//! so tests can compare benchmark expectations against the solver's actual
//! result, while execution layers remain free to ignore it.

use std::fmt;

use smtlib_lexer::{SExpr, Span};

/// Interned symbol name from the SMT-LIB surface syntax.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(Box<str>);

impl Symbol {
    /// Creates a symbol from owned text.
    pub fn new(text: impl Into<Box<str>>) -> Self {
        Self(text.into())
    }

    /// Returns the symbol text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// SMT-LIB keyword such as `:status`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Keyword(Box<str>);

impl Keyword {
    /// Creates a keyword from owned text.
    pub fn new(text: impl Into<Box<str>>) -> Self {
        Self(text.into())
    }

    /// Returns the keyword text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Parsed SMT-LIB command in the currently supported subset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// `(set-logic ...)`.
    SetLogic(SetLogic),
    /// `(set-info ...)`.
    SetInfo(SetInfo),
    /// `(declare-sort ...)`.
    DeclareSort(DeclareSort),
    /// `(declare-fun ...)`.
    DeclareFun(DeclareFun),
    /// `(define-fun ...)`.
    DefineFun(DefineFun),
    /// `(assert ...)`.
    Assert(TermExpr),
    /// `(push n)`.
    Push(u32),
    /// `(pop n)`.
    Pop(u32),
    /// `(check-sat)`.
    CheckSat,
    /// `(exit)`.
    Exit,
}

/// Parsed `set-logic` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetLogic {
    /// Logic name, such as `QF_UF`.
    pub logic: Symbol,
}

/// Parsed `set-info` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetInfo {
    /// Original SMT-LIB keyword, such as `:status`.
    pub keyword: Keyword,
    /// Atom-valued payload when the current subset can represent it directly.
    pub value: Option<Box<str>>,
    /// Parsed benchmark expectation for `set-info :status ...`.
    ///
    /// This field is metadata. It exists so harnesses can validate a benchmark's
    /// declared expectation against a real `check-sat` result; it must not be
    /// interpreted as permission for the solver to short-circuit solving.
    pub expected_status: Option<ExpectedStatus>,
}

/// Benchmark expectation extracted from `set-info :status`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedStatus {
    /// The benchmark declares the following `check-sat` as satisfiable.
    Sat,
    /// The benchmark declares the following `check-sat` as unsatisfiable.
    Unsat,
    /// The benchmark declares the following `check-sat` as unknown.
    Unknown,
}

/// Parsed `declare-sort` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclareSort {
    /// Sort name.
    pub name: Symbol,
    /// Arity for parametric sorts.
    pub arity: u32,
}

/// Parsed `declare-fun` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclareFun {
    /// Function symbol name.
    pub name: Symbol,
    /// Argument sorts in declaration order.
    pub args: Box<[SortExpr]>,
    /// Result sort.
    pub result: SortExpr,
}

/// Parsed `define-fun` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineFun {
    /// Function symbol name.
    pub name: Symbol,
    /// Binders in declaration order.
    pub binders: Box<[Binder]>,
    /// Result sort.
    pub result: SortExpr,
    /// Function body expression.
    pub body: TermExpr,
}

/// One `define-fun` binder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binder {
    /// Binder name.
    pub name: Symbol,
    /// Binder sort.
    pub sort: SortExpr,
}

/// Sort expression in the currently supported SMT-LIB subset.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SortExpr {
    /// Non-parametric sort reference.
    Simple(Symbol),
}

/// Term expression preserved as a syntax tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermExpr {
    /// Parsed S-expression tree backing this logical term surface form.
    expr: SExpr,
}

impl TermExpr {
    /// Wraps a parsed S-expression as a term.
    pub fn new(expr: SExpr) -> Self {
        Self { expr }
    }

    /// Returns the underlying syntax tree.
    pub fn sexpr(&self) -> &SExpr {
        &self.expr
    }
}

/// Failure while converting an S-expression into a [`Command`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommandError {
    /// Span of the offending syntax.
    pub span: Span,
    /// Human-readable error description.
    pub message: Box<str>,
}

impl CommandError {
    /// Describes a malformed command substring at `span`.
    fn new(span: Span, message: impl Into<Box<str>>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }
}

impl fmt::Display for CommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at bytes {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for CommandError {}

impl Command {
    /// Parses one SMT-LIB command from a pre-parsed S-expression.
    pub fn from_sexpr(expr: SExpr) -> Result<Self, CommandError> {
        let span = expr.span();
        let items = expr
            .as_list()
            .ok_or_else(|| CommandError::new(span, "command must be a list"))?;
        let head = atom_at(items, 0, "command name")?;
        match head {
            "set-logic" => Ok(Self::SetLogic(SetLogic {
                logic: Symbol::new(atom_at(items, 1, "logic")?),
            })),
            "set-info" => parse_set_info(items),
            "declare-sort" => Ok(Self::DeclareSort(DeclareSort {
                name: Symbol::new(atom_at(items, 1, "sort name")?),
                arity: parse_u32(atom_at(items, 2, "sort arity")?, items[2].span())?,
            })),
            "declare-fun" => parse_declare_fun(items),
            "define-fun" => parse_define_fun(items),
            "assert" => {
                let term = items
                    .get(1)
                    .ok_or_else(|| CommandError::new(span, "assert missing term"))?;
                Ok(Self::Assert(TermExpr::new(term.clone())))
            }
            "push" => Ok(Self::Push(parse_optional_count(items, 1)?)),
            "pop" => Ok(Self::Pop(parse_optional_count(items, 1)?)),
            "check-sat" => Ok(Self::CheckSat),
            "exit" => Ok(Self::Exit),
            other => Err(CommandError::new(
                span,
                format!("unsupported command `{other}`"),
            )),
        }
    }
}

/// Interprets `(set-info ...)` into [`Command::SetInfo`], validating `:status` values.
fn parse_set_info(items: &[SExpr]) -> Result<Command, CommandError> {
    let span = items[0].span();
    let keyword = Keyword::new(atom_at(items, 1, "info keyword")?);
    let value = items.get(2).and_then(SExpr::as_atom).map(Into::into);
    let expected_status = if keyword.as_str() == ":status" {
        match value.as_deref() {
            Some("sat") => Some(ExpectedStatus::Sat),
            Some("unsat") => Some(ExpectedStatus::Unsat),
            Some("unknown") => Some(ExpectedStatus::Unknown),
            Some(other) => {
                return Err(CommandError::new(
                    items[2].span(),
                    format!("unsupported status `{other}`"),
                ));
            }
            None => return Err(CommandError::new(span, "status info missing value")),
        }
    } else {
        None
    };
    Ok(Command::SetInfo(SetInfo {
        keyword,
        value,
        expected_status,
    }))
}

/// Builds [`Command::DeclareFun`] after parsing argument-sort list and result sort.
fn parse_declare_fun(items: &[SExpr]) -> Result<Command, CommandError> {
    let name = Symbol::new(atom_at(items, 1, "function name")?);
    let arg_items = items
        .get(2)
        .and_then(SExpr::as_list)
        .ok_or_else(|| CommandError::new(items[0].span(), "declare-fun missing argument sorts"))?;
    let args = arg_items
        .iter()
        .map(parse_sort)
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let result =
        parse_sort(items.get(3).ok_or_else(|| {
            CommandError::new(items[0].span(), "declare-fun missing result sort")
        })?)?;
    Ok(Command::DeclareFun(DeclareFun { name, args, result }))
}

/// Builds [`Command::DefineFun`] after parsing binder list, result sort, and body.
fn parse_define_fun(items: &[SExpr]) -> Result<Command, CommandError> {
    let name = Symbol::new(atom_at(items, 1, "function name")?);
    let binder_items = items
        .get(2)
        .and_then(SExpr::as_list)
        .ok_or_else(|| CommandError::new(items[0].span(), "define-fun missing binders"))?;
    let binders = binder_items
        .iter()
        .map(parse_binder)
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let result =
        parse_sort(items.get(3).ok_or_else(|| {
            CommandError::new(items[0].span(), "define-fun missing result sort")
        })?)?;
    let body = items
        .get(4)
        .ok_or_else(|| CommandError::new(items[0].span(), "define-fun missing body"))?;
    Ok(Command::DefineFun(DefineFun {
        name,
        binders,
        result,
        body: TermExpr::new(body.clone()),
    }))
}

/// Parses `(name sort)` binder pairs nested inside `(define-fun ...)`.
fn parse_binder(expr: &SExpr) -> Result<Binder, CommandError> {
    let items = expr
        .as_list()
        .ok_or_else(|| CommandError::new(expr.span(), "binder must be a list"))?;
    Ok(Binder {
        name: Symbol::new(atom_at(items, 0, "binder name")?),
        sort: parse_sort(
            items
                .get(1)
                .ok_or_else(|| CommandError::new(expr.span(), "binder missing sort"))?,
        )?,
    })
}

/// Maps a lone symbol sort reference into [`SortExpr`]; rejects functor sorts here.
fn parse_sort(expr: &SExpr) -> Result<SortExpr, CommandError> {
    match expr {
        SExpr::Atom { text, .. } => Ok(SortExpr::Simple(Symbol::new(text.clone()))),
        SExpr::List { .. } => Err(CommandError::new(
            expr.span(),
            "parametric sorts are not in the observed subset",
        )),
    }
}

/// Returns the atomic string payload at `index` inside `items` or fails with [`CommandError`].
fn atom_at<'a>(items: &'a [SExpr], index: usize, what: &str) -> Result<&'a str, CommandError> {
    let expr = items
        .get(index)
        .ok_or_else(|| CommandError::new(items[0].span(), format!("missing {what}")))?;
    expr.as_atom()
        .ok_or_else(|| CommandError::new(expr.span(), format!("{what} must be an atom")))
}

/// Reads an optional repeating command count atom, defaulting to `1` when absent.
fn parse_optional_count(items: &[SExpr], index: usize) -> Result<u32, CommandError> {
    match items.get(index) {
        Some(expr) => parse_u32(
            expr.as_atom()
                .ok_or_else(|| CommandError::new(expr.span(), "count must be an atom"))?,
            expr.span(),
        ),
        None => Ok(1),
    }
}

/// Parses `text` as an unsigned decimal `u32` or returns an error at `span`.
fn parse_u32(text: &str, span: Span) -> Result<u32, CommandError> {
    text.parse()
        .map_err(|_| CommandError::new(span, format!("expected unsigned integer, got `{text}`")))
}

#[cfg(test)]
mod tests {
    use smtlib_lexer::parse_many;

    use super::*;

    #[test]
    fn parses_expected_status() {
        let exprs = parse_many("(set-info :status unsat)").expect("valid sexpr");
        let command = Command::from_sexpr(exprs[0].clone()).expect("valid command");
        assert!(matches!(
            command,
            Command::SetInfo(SetInfo {
                expected_status: Some(ExpectedStatus::Unsat),
                ..
            })
        ));
    }
}
