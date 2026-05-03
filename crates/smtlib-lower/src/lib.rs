//! Lowering from parsed SMT-LIB commands into reviewable, solver-oriented IDs.
//!
//! The lowering layer resolves declarations into stable numeric identifiers while
//! preserving original commands that still matter to later phases. Benchmark
//! metadata such as `set-info :status` is kept as plain [`SetInfo`] instead of
//! being promoted into solver behavior.

use std::collections::HashMap;
use std::fmt;

use smtlib_syntax::{Command, DeclareFun, DeclareSort, DefineFun, SetInfo, SortExpr, Symbol};

/// Stable identifier for one declared uninterpreted sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SortId(pub u32);

/// Stable identifier for one declared function symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunId(pub u32);

/// Stable identifier for one lowered term node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u32);

/// Stable identifier for one lowered boolean formula node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FormulaId(pub u32);

/// Stable identifier for one lowered SAT literal variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoolVar(pub u32);

/// Stable identifier for one lowered push/pop frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameId(pub u32);

/// Lowered sort model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    /// Built-in boolean sort.
    Bool,
    /// User-declared uninterpreted sort.
    Uninterpreted(SortId),
}

/// Lowered term model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Nullary function or constant symbol.
    Const(FunId),
    /// Function application.
    App(AppTerm),
    /// If-then-else over terms.
    Ite(TermIte),
}

/// Lowered function application term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppTerm {
    /// Applied function symbol.
    pub fun: FunId,
    /// Lowered argument terms.
    pub args: Box<[TermId]>,
}

/// Lowered term-valued if-then-else.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermIte {
    /// Boolean condition.
    pub cond: FormulaId,
    /// Branch used when the condition is true.
    pub then_term: TermId,
    /// Branch used when the condition is false.
    pub else_term: TermId,
}

/// Lowered boolean formula model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    /// Constant `true`.
    True,
    /// Constant `false`.
    False,
    /// Atomic boolean predicate.
    Atom(BoolAtom),
    /// Negation.
    Not(FormulaId),
    /// Conjunction.
    And(Box<[FormulaId]>),
    /// Disjunction.
    Or(Box<[FormulaId]>),
    /// Boolean if-then-else.
    Ite(BoolIte),
}

/// Lowered boolean atom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolAtom {
    /// Equality between two lowered terms.
    Eq(TermId, TermId),
    /// Predicate application returning `Bool`.
    PredApp(FunId, Box<[TermId]>),
}

/// Lowered boolean if-then-else.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolIte {
    /// Boolean condition.
    pub cond: FormulaId,
    /// Branch used when the condition is true.
    pub then_formula: FormulaId,
    /// Branch used when the condition is false.
    pub else_formula: FormulaId,
}

/// Sort declaration after assigning a stable ID.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclaredSort {
    /// Stable sort identifier.
    pub id: SortId,
    /// Original sort name.
    pub name: Symbol,
    /// Declared sort arity.
    pub arity: u32,
}

/// Function declaration after assigning a stable ID.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclaredFun {
    /// Stable function identifier.
    pub id: FunId,
    /// Original function name.
    pub name: Symbol,
    /// Declared argument sorts.
    pub args: Box<[SortExpr]>,
    /// Declared result sort.
    pub result: SortExpr,
}

/// Command after declaration names are lowered into stable IDs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweredCommand {
    /// Changes the active logic.
    SetLogic(Symbol),
    /// Preserves uninterpreted `set-info` metadata.
    SetInfo(SetInfo),
    /// Declares a fresh uninterpreted sort.
    DeclareSort(DeclaredSort),
    /// Declares a fresh function symbol.
    DeclareFun(DeclaredFun),
    /// Preserves a function definition for later consumers.
    DefineFun(DefineFun),
    /// Records one asserted top-level formula.
    Assert,
    /// Pushes the assertion stack by the given amount.
    Push(u32),
    /// Pops the assertion stack by the given amount.
    Pop(u32),
    /// Requests satisfiability checking.
    CheckSat,
    /// Requests termination.
    Exit,
}

/// Failure raised while lowering parsed commands.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LowerError(Box<str>);

impl LowerError {
    /// Wraps a descriptive lowering failure message.
    fn new(message: impl Into<Box<str>>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for LowerError {}

/// Mutable lowering state tracking already declared names.
#[derive(Debug, Default)]
pub struct LoweringContext {
    /// Maps declared sort names to their assigned [`DeclaredSort`] records.
    sorts: HashMap<Symbol, DeclaredSort>,
    /// Maps declared function names to their assigned [`DeclaredFun`] records.
    funs: HashMap<Symbol, DeclaredFun>,
}

impl LoweringContext {
    /// Creates an empty lowering context.
    pub fn new() -> Self {
        Self::default()
    }

    /// Lowers one parsed command into the current command-level IR.
    pub fn lower_command(&mut self, command: Command) -> Result<LoweredCommand, LowerError> {
        match command {
            Command::SetLogic(set_logic) => Ok(LoweredCommand::SetLogic(set_logic.logic)),
            Command::SetInfo(set_info) => Ok(LoweredCommand::SetInfo(set_info)),
            Command::DeclareSort(declare_sort) => self.declare_sort(declare_sort),
            Command::DeclareFun(declare_fun) => self.declare_fun(declare_fun),
            Command::DefineFun(define_fun) => Ok(LoweredCommand::DefineFun(define_fun)),
            Command::Assert(_) => Ok(LoweredCommand::Assert),
            Command::Push(amount) => Ok(LoweredCommand::Push(amount)),
            Command::Pop(amount) => Ok(LoweredCommand::Pop(amount)),
            Command::CheckSat => Ok(LoweredCommand::CheckSat),
            Command::Exit => Ok(LoweredCommand::Exit),
        }
    }

    /// Allocates the next [`SortId`] unless `declare_sort.name` clashes with an earlier declaration.
    fn declare_sort(&mut self, declare_sort: DeclareSort) -> Result<LoweredCommand, LowerError> {
        if self.sorts.contains_key(&declare_sort.name) {
            return Err(LowerError::new(format!(
                "sort `{}` already declared",
                declare_sort.name.as_str()
            )));
        }
        let id = SortId(
            self.sorts
                .len()
                .try_into()
                .map_err(|_| LowerError::new("too many declared sorts for u32-backed SortId"))?,
        );
        let declared = DeclaredSort {
            id,
            name: declare_sort.name.clone(),
            arity: declare_sort.arity,
        };
        self.sorts.insert(declare_sort.name, declared.clone());
        Ok(LoweredCommand::DeclareSort(declared))
    }

    /// Allocates the next [`FunId`] unless `declare_fun.name` clashes with an earlier declaration.
    fn declare_fun(&mut self, declare_fun: DeclareFun) -> Result<LoweredCommand, LowerError> {
        if self.funs.contains_key(&declare_fun.name) {
            return Err(LowerError::new(format!(
                "function `{}` already declared",
                declare_fun.name.as_str()
            )));
        }
        let id =
            FunId(self.funs.len().try_into().map_err(|_| {
                LowerError::new("too many declared functions for u32-backed FunId")
            })?);
        let declared = DeclaredFun {
            id,
            name: declare_fun.name.clone(),
            args: declare_fun.args,
            result: declare_fun.result,
        };
        self.funs.insert(declare_fun.name, declared.clone());
        Ok(LoweredCommand::DeclareFun(declared))
    }
}

#[cfg(test)]
mod tests {
    use smtlib_lexer::parse_many;
    use smtlib_syntax::{Command, ExpectedStatus};

    use super::*;

    #[test]
    fn preserves_status_metadata_as_set_info() {
        let exprs = parse_many("(set-info :status unsat)").expect("valid sexpr");
        let command = Command::from_sexpr(exprs[0].clone()).expect("valid command");
        let lowered = LoweringContext::new()
            .lower_command(command)
            .expect("lowering succeeds");

        assert!(matches!(
            lowered,
            LoweredCommand::SetInfo(SetInfo {
                expected_status: Some(ExpectedStatus::Unsat),
                ..
            })
        ));
    }
}
