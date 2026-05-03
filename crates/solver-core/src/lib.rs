//! Incremental SMT-LIB command execution for the current QF_UF-focused solver.
//!
//! This crate owns the command-level state machine that sits above the EUF checker:
//! asserted formulas, zero-arity definitions, and push/pop frames. The solver
//! consumes parsed [`Command`] values and produces observable events such as
//! [`SolverEvent::CheckSat`].
//!
//! `set-info :status ...` is intentionally treated as benchmark metadata only.
//! The parser preserves it for test harnesses, but the solver never uses that
//! annotation to influence the actual satisfiability result.

use std::collections::HashMap;
use std::fmt;

pub use euf_core::{CheckBudget, Fuel};

use euf_core::{EufCheckOutcome, EufSolver, TermId, TermKind, TheoryAtom};
use smtlib_lexer::SExpr;
use smtlib_syntax::{Command, DefineFun, ExpectedStatus, Symbol, TermExpr};

/// SMT-LIB satisfiability result produced by the solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    /// The asserted formulas are satisfiable.
    Sat,
    /// The asserted formulas are inconsistent.
    Unsat,
    /// The solver could not determine satisfiability for the input fragment.
    Unknown,
    /// The solver stopped because the caller-provided budget ran out.
    Interrupted,
}

impl SatResult {
    /// Returns the canonical SMT-LIB spelling of this result.
    ///
    /// SMT-LIB has no dedicated token for interruptions, so [`SatResult::Interrupted`]
    /// is reported as `"unknown"` at that boundary.
    pub fn as_smtlib(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
            Self::Interrupted => "unknown",
        }
    }
}

impl fmt::Display for SatResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interrupted => f.write_str("interrupted"),
            _ => f.write_str(self.as_smtlib()),
        }
    }
}

impl From<ExpectedStatus> for SatResult {
    fn from(value: ExpectedStatus) -> Self {
        match value {
            ExpectedStatus::Sat => Self::Sat,
            ExpectedStatus::Unsat => Self::Unsat,
            ExpectedStatus::Unknown => Self::Unknown,
        }
    }
}

/// Result payload emitted by a `check-sat` command.
pub type CheckSatResult = SatResult;

/// Stable identifier for one push/pop frame in the solver stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameId(pub u32);

/// Stable identifier for one asserted top-level formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AssertedFormulaId(pub u32);

/// Reserved identifier for a future activation-literal based frame encoding.
///
/// The current solver still stores assertions structurally per frame, but the
/// identifier remains part of the public model because stack frames already
/// expose it and downstream tooling may want to correlate with that shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ActivationLiteral(pub u32);

/// One top-level asserted formula recorded by the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssertedFormula {
    /// Monotonic identifier assigned when the formula enters the assertion stack.
    pub id: AssertedFormulaId,
    /// Original SMT-LIB term as parsed by `smtlib-syntax`.
    pub formula: TermExpr,
}

/// Snapshot of one incremental frame.
///
/// Frames let the solver restore the assertion stack to an earlier prefix during
/// `pop`. They currently capture only the assertion length plus externally
/// visible identifiers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Frame {
    /// Monotonic frame identifier.
    pub id: FrameId,
    /// Reserved activation-literal identifier associated with this frame.
    pub activation: ActivationLiteral,
    /// Number of asserted formulas retained when this frame was pushed (`pop` restores to this prefix).
    asserted_len: usize,
}

/// Observable effect of handling one SMT-LIB command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverEvent {
    /// The command updated internal state without producing user-visible output.
    None,
    /// The command produced a satisfiability result.
    CheckSat(CheckSatResult),
    /// The command requested termination.
    Exit,
}

/// Error raised while executing a parsed command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverError(Box<str>);

impl SolverError {
    /// Wraps a descriptive solver-stage failure suitable for callers and logging.
    fn new(message: impl Into<Box<str>>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for SolverError {}

/// Incremental solver state for the supported SMT-LIB subset.
#[derive(Debug, Default)]
pub struct Solver {
    /// Top-level asserted formulas in stack order across all active frames.
    assertions: Vec<AssertedFormula>,
    /// Frames recorded by `(push)`, newest last; [`Frame::asserted_len`] trims on `(pop)`.
    frames: Vec<Frame>,
    /// Zero-arity `define-fun` bodies keyed by declared symbol names.
    definitions: HashMap<Symbol, TermExpr>,
    /// Next monotonic [`FrameId`] counter for newly pushed scopes.
    next_frame: u32,
    /// Next reserved [`ActivationLiteral`] counter paired with frames.
    next_activation: u32,
}

impl Solver {
    /// Creates an empty solver with no declarations, assertions, or frames.
    pub fn new() -> Self {
        Self::default()
    }

    /// Applies one parsed SMT-LIB command to the incremental solver state.
    ///
    /// `set-info` commands are accepted as metadata and ignored by the solving
    /// engine. In particular, benchmark annotations such as `:status` never
    /// override the real `check-sat` result.
    pub fn handle_command(&mut self, command: Command) -> Result<SolverEvent, SolverError> {
        let mut budget = UnlimitedBudget;
        self.handle_command_with_budget(command, &mut budget)
    }

    /// Applies one parsed SMT-LIB command to the incremental solver state under `budget`.
    ///
    /// The supplied budget is consumed only by work that can grow with input size.
    /// Metadata updates and stack bookkeeping still remain effectively free.
    pub fn handle_command_with_budget<B: CheckBudget>(
        &mut self,
        command: Command,
        budget: &mut B,
    ) -> Result<SolverEvent, SolverError> {
        match command {
            Command::SetLogic(_) | Command::DeclareSort(_) => Ok(SolverEvent::None),
            Command::SetInfo(_) => Ok(SolverEvent::None),
            Command::DeclareFun(_) => Ok(SolverEvent::None),
            Command::DefineFun(define_fun) => {
                self.define_fun(define_fun)?;
                Ok(SolverEvent::None)
            }
            Command::Assert(term) => {
                self.assert_formula(term)?;
                Ok(SolverEvent::None)
            }
            Command::Push(amount) => {
                self.push(amount)?;
                Ok(SolverEvent::None)
            }
            Command::Pop(amount) => {
                self.pop(amount)?;
                Ok(SolverEvent::None)
            }
            Command::CheckSat => Ok(SolverEvent::CheckSat(self.check_sat_with_budget(budget))),
            Command::Exit => Ok(SolverEvent::Exit),
        }
    }

    /// Solves the current assertion stack.
    ///
    /// The result depends only on the asserted formulas and definitions currently
    /// in scope. Benchmark metadata such as `set-info :status` is deliberately
    /// excluded from this computation.
    pub fn check_sat(&self) -> CheckSatResult {
        let mut budget = UnlimitedBudget;
        self.check_sat_with_budget(&mut budget)
    }

    /// Solves the current assertion stack under `budget`.
    ///
    /// Returning [`SatResult::Interrupted`] preserves the distinction between
    /// semantic incompleteness and caller-imposed resource limits.
    pub fn check_sat_with_budget<B: CheckBudget>(&self, budget: &mut B) -> CheckSatResult {
        let mut budget = SearchBudget::new(budget);
        let mut checker = SatEufCheck::new(&self.definitions);
        for asserted in &self.assertions {
            if !budget.checkpoint() {
                return SatResult::Interrupted;
            }
            if checker.assert_formula(asserted.formula.sexpr()).is_err() {
                return SatResult::Unknown;
            }
        }
        checker.check_with_budget(&mut budget)
    }

    /// Stores `define_fun` when arity is zero; otherwise returns an explanatory error.
    fn define_fun(&mut self, define_fun: DefineFun) -> Result<(), SolverError> {
        if !define_fun.binders.is_empty() {
            return Err(SolverError::new(format!(
                "define-fun `{}` has arity {}; only arity-0 definitions are supported in this path",
                define_fun.name.as_str(),
                define_fun.binders.len()
            )));
        }
        self.definitions.insert(define_fun.name, define_fun.body);
        Ok(())
    }

    /// Assigns [`AssertedFormulaId`] and pushes `formula` onto the assertion stack.
    fn assert_formula(&mut self, formula: TermExpr) -> Result<(), SolverError> {
        let id = AssertedFormulaId(
            self.assertions
                .len()
                .try_into()
                .map_err(|_| SolverError::new("too many asserted formulas for u32 id"))?,
        );
        self.assertions.push(AssertedFormula { id, formula });
        Ok(())
    }

    /// Records `amount` fresh frames pinning the current assertion prefix length before growth continues.
    fn push(&mut self, amount: u32) -> Result<(), SolverError> {
        for _ in 0..amount {
            let frame = Frame {
                id: FrameId(self.next_frame),
                activation: ActivationLiteral(self.next_activation),
                asserted_len: self.assertions.len(),
            };
            self.next_frame = self
                .next_frame
                .checked_add(1)
                .ok_or_else(|| SolverError::new("frame id overflow"))?;
            self.next_activation = self
                .next_activation
                .checked_add(1)
                .ok_or_else(|| SolverError::new("activation literal overflow"))?;
            self.frames.push(frame);
        }
        Ok(())
    }

    /// Reverts the newest `amount` pushes, truncating assertions to each popped frame boundary.
    fn pop(&mut self, amount: u32) -> Result<(), SolverError> {
        for _ in 0..amount {
            let frame = self
                .frames
                .pop()
                .ok_or_else(|| SolverError::new("pop beyond current assertion stack"))?;
            self.assertions.truncate(frame.asserted_len);
        }
        Ok(())
    }
}

/// Sentinel budget used to preserve the legacy unbounded API.
struct UnlimitedBudget;

impl CheckBudget for UnlimitedBudget {
    fn checkpoint(&mut self) -> bool {
        true
    }
}

/// Batches fine-grained solver checkpoints into coarser externally visible fuel consumption.
///
/// Archive fixtures execute many tiny internal loops. Charging one fuel unit for every one of
/// those steps interrupts otherwise tractable searches much earlier than intended. This adapter
/// keeps the interruption API while amortizing the hot-path accounting cost.
struct SearchBudget<'a, B> {
    /// Underlying caller-provided budget.
    inner: &'a mut B,
    /// Remaining internal steps covered by the current charged checkpoint.
    remaining: u16,
}

impl<'a, B> SearchBudget<'a, B> {
    /// Number of internal checkpoints grouped into one external budget unit.
    const QUANTUM: u16 = 1024;

    /// Creates a batching wrapper around `inner`.
    fn new(inner: &'a mut B) -> Self {
        Self {
            inner,
            remaining: 0,
        }
    }
}

impl<B: CheckBudget> CheckBudget for SearchBudget<'_, B> {
    fn checkpoint(&mut self) -> bool {
        if self.remaining == 0 {
            if !self.inner.checkpoint() {
                return false;
            }
            self.remaining = Self::QUANTUM;
        }
        self.remaining -= 1;
        true
    }
}

/// One-shot SAT+EUF checker built from solver definitions and asserted formulas.
struct SatEufCheck<'a> {
    /// Zero-arity definitional expansions available while lowering formulas.
    definitions: &'a HashMap<Symbol, TermExpr>,
    /// Backend congruence solver sharing interned term ids.
    euf: EufSolver,
    /// Structural EUF [`TermKind`] cache mapping to reusable [`TermId`] handles.
    terms: HashMap<TermKind, TermId>,
    /// Boolean atom names mapped onto dedicated DIMACS-style literals.
    bool_symbols: HashMap<Box<str>, BoolVar>,
    /// Stable literal-to-theory tuples emitted for later EUF reconciliation.
    theory_atoms: Vec<(BoolVar, TheoryKey)>,
    /// Dedup lookup so identical theory literals reuse one [`BoolVar`].
    theory_vars: HashMap<TheoryKey, BoolVar>,
    /// CNF clauses over [`Lit`] literals once boolean structure is flattened.
    clauses: Vec<Box<[Lit]>>,
    /// Next unallocated boolean variable counter (dense index ordering).
    next_bool_var: u32,
    /// Next synthetic term proxy used to materialize term-valued `(ite)` nodes.
    next_term_proxy: u32,
}

impl<'a> SatEufCheck<'a> {
    /// Seeds an empty checker referencing `definitions` for macro expansion lookups.
    fn new(definitions: &'a HashMap<Symbol, TermExpr>) -> Self {
        Self {
            definitions,
            euf: EufSolver::new(),
            terms: HashMap::new(),
            bool_symbols: HashMap::new(),
            theory_atoms: Vec::new(),
            theory_vars: HashMap::new(),
            clauses: Vec::new(),
            next_bool_var: 1,
            next_term_proxy: 0,
        }
    }

    /// Parses `expr`, maps it through `self`, then encodes top-level satisfaction as clauses.
    fn assert_formula(&mut self, expr: &SExpr) -> Result<(), SolverError> {
        let mut env = HashMap::new();
        let value = self.formula(expr, &mut env)?;
        self.assert_value(value);
        Ok(())
    }

    /// Builds the DIMACS+EUF handshake from accumulated structure and invokes DPLL.
    fn check_with_budget<B: CheckBudget>(self, budget: &mut B) -> SatResult {
        let mut dpll = Dpll::new(
            self.next_bool_var,
            self.clauses,
            self.theory_atoms,
            self.euf,
        );
        dpll.solve(budget)
    }

    /// Recursive boolean lowering for atoms, connectors, equality, `(ite)`, `(let)`, and definitions.
    fn formula(
        &mut self,
        expr: &SExpr,
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        if let Some(atom) = expr.as_atom() {
            if let Some(bound) = env.get(atom) {
                return self.formula(&bound.clone(), env);
            }
            if let Some(definition) = self.definitions.get(&Symbol::new(atom)) {
                return self.formula(definition.sexpr(), env);
            }
            return Ok(match atom {
                "true" => BoolValue::Const(true),
                "false" => BoolValue::Const(false),
                _ => BoolValue::Lit(self.bool_symbol(atom.into()).positive()),
            });
        }

        let items = expr
            .as_list()
            .ok_or_else(|| SolverError::new("formula must be an atom or list"))?;
        let head = items
            .first()
            .and_then(SExpr::as_atom)
            .ok_or_else(|| SolverError::new("formula list must start with an atom"))?;

        match head {
            "and" => self.formula_and(&items[1..], env),
            "or" => self.formula_or(&items[1..], env),
            "not" if items.len() == 2 => Ok(self.formula(&items[1], env)?.not()),
            "=>" if items.len() == 3 => {
                let premise = self.formula(&items[1], env)?.not();
                let conclusion = self.formula(&items[2], env)?;
                self.or_values([premise, conclusion])
            }
            "=" => self.formula_equal(&items[1..], env),
            "distinct" => self.formula_distinct(&items[1..], env),
            "ite" if items.len() == 4 => {
                let cond = self.formula(&items[1], env)?;
                let then_value = self.formula(&items[2], env)?;
                let else_value = self.formula(&items[3], env)?;
                let left = self.and_values([cond, then_value])?;
                let right = self.and_values([cond.not(), else_value])?;
                self.or_values([left, right])
            }
            "let" if items.len() == 3 => self.formula_let(&items[1], &items[2], env),
            _ => Err(SolverError::new(format!(
                "unsupported formula shape headed by `{head}`"
            ))),
        }
    }

    /// Builds the conjunction semantics for `"and"` with constant folding shortcuts.
    fn formula_and(
        &mut self,
        args: &[SExpr],
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        let values = args
            .iter()
            .map(|arg| self.formula(arg, env))
            .collect::<Result<Vec<_>, _>>()?;
        self.and_values(values)
    }

    /// Builds the disjunction semantics for `"or"` with constant folding shortcuts.
    fn formula_or(
        &mut self,
        args: &[SExpr],
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        let values = args
            .iter()
            .map(|arg| self.formula(arg, env))
            .collect::<Result<Vec<_>, _>>()?;
        self.or_values(values)
    }

    /// Handles `"="` chains for pure booleans versus EUF terms.
    fn formula_equal(
        &mut self,
        args: &[SExpr],
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        if args.len() < 2 {
            return Ok(BoolValue::Const(true));
        }
        let term_values = args
            .iter()
            .map(|arg| self.term_value(arg, env))
            .collect::<Result<Vec<_>, _>>()?;
        if term_values.iter().all(Option::is_some) {
            let terms = term_values
                .into_iter()
                .flatten()
                .map(|value| self.materialize_term_value(value))
                .collect::<Result<Vec<_>, _>>()?;
            self.chain_term_relation(terms, TheoryRelation::Eq)
        } else {
            let values = args
                .iter()
                .map(|arg| self.formula(arg, env))
                .collect::<Result<Vec<_>, _>>()?;
            self.chain_equivalence(values)
        }
    }

    /// Expands pairwise disequalities into conjoined [`TheoryRelation::Diseq`] guarded literals.
    fn formula_distinct(
        &mut self,
        args: &[SExpr],
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        if args.len() < 2 {
            return Ok(BoolValue::Const(true));
        }
        let terms = args
            .iter()
            .map(|arg| self.term_value(arg, env))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| SolverError::new("distinct contains a non-term argument"))?;
        let mut values = Vec::new();
        for left in 0..terms.len() {
            for right in (left + 1)..terms.len() {
                let left_term = self.materialize_term_value(terms[left].clone())?;
                let right_term = self.materialize_term_value(terms[right].clone())?;
                values.push(self.theory_atom(TheoryKey::new(
                    TheoryRelation::Diseq,
                    left_term,
                    right_term,
                )));
            }
        }
        self.and_values(values)
    }

    /// Applies temporary symbol bindings inside `bindings_expr`, evaluates `body`, then restores `env`.
    fn formula_let(
        &mut self,
        bindings_expr: &SExpr,
        body: &SExpr,
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        let bindings = bindings_expr
            .as_list()
            .ok_or_else(|| SolverError::new("let bindings must be a list"))?;
        let mut inserted = Vec::new();
        for binding in bindings {
            let pair = binding
                .as_list()
                .ok_or_else(|| SolverError::new("let binding must be a list"))?;
            if pair.len() != 2 {
                return Err(SolverError::new("let binding must contain name and value"));
            }
            let name = pair[0]
                .as_atom()
                .ok_or_else(|| SolverError::new("let binding name must be an atom"))?;
            let previous = env.insert(name.into(), pair[1].clone());
            inserted.push((Box::<str>::from(name), previous));
        }
        let result = self.formula(body, env);
        for (name, previous) in inserted.into_iter().rev() {
            match previous {
                Some(value) => {
                    env.insert(name, value);
                }
                None => {
                    env.remove(&name);
                }
            }
        }
        result
    }

    /// Converts `expr` to a term-valued lowering result when it denotes EUF structure.
    fn term_value(
        &mut self,
        expr: &SExpr,
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<Option<TermValue>, SolverError> {
        if let Some(atom) = expr.as_atom() {
            if atom == "true" || atom == "false" {
                return Ok(None);
            }
            if let Some(bound) = env.get(atom) {
                return self.term_value(&bound.clone(), env);
            }
            if let Some(definition) = self.definitions.get(&Symbol::new(atom)) {
                return self.term_value(definition.sexpr(), env);
            }
            return Ok(Some(TermValue::Term(
                self.intern(TermKind::Const(atom.into())),
            )));
        }

        let items = expr
            .as_list()
            .ok_or_else(|| SolverError::new("term must be an atom or list"))?;
        let head = items
            .first()
            .and_then(SExpr::as_atom)
            .ok_or_else(|| SolverError::new("term list must start with an atom"))?;
        if head == "let" && items.len() == 3 {
            return self.term_value_let(&items[1], &items[2], env);
        }
        if head == "ite" && items.len() == 4 {
            let cond = self.formula(&items[1], env)?;
            let then_branch = self
                .term_value(&items[2], env)?
                .ok_or_else(|| SolverError::new("term ite then-branch is not a term"))?;
            let else_branch = self
                .term_value(&items[3], env)?
                .ok_or_else(|| SolverError::new("term ite else-branch is not a term"))?;
            return Ok(Some(TermValue::Ite {
                cond,
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            }));
        }
        if matches!(head, "and" | "or" | "not" | "=>" | "=" | "distinct") {
            return Ok(None);
        }
        let args = items[1..]
            .iter()
            .map(|arg| self.term_value(arg, env))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| SolverError::new("function application contains a non-term argument"))?;
        let args = args
            .into_iter()
            .map(|arg| self.materialize_term_value(arg))
            .collect::<Result<Vec<_>, _>>()?
            .into_boxed_slice();
        Ok(Some(TermValue::Term(self.intern(TermKind::App {
            fun: head.into(),
            args,
        }))))
    }

    /// `let`-binder aware variant of [`Self::term_value`] sharing the rollback discipline of formula lets.
    fn term_value_let(
        &mut self,
        bindings_expr: &SExpr,
        body: &SExpr,
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<Option<TermValue>, SolverError> {
        let bindings = bindings_expr
            .as_list()
            .ok_or_else(|| SolverError::new("let bindings must be a list"))?;
        let mut inserted = Vec::new();
        for binding in bindings {
            let pair = binding
                .as_list()
                .ok_or_else(|| SolverError::new("let binding must be a list"))?;
            if pair.len() != 2 {
                return Err(SolverError::new("let binding must contain name and value"));
            }
            let name = pair[0]
                .as_atom()
                .ok_or_else(|| SolverError::new("let binding name must be an atom"))?;
            let previous = env.insert(name.into(), pair[1].clone());
            inserted.push((Box::<str>::from(name), previous));
        }
        let result = self.term_value(body, env);
        for (name, previous) in inserted.into_iter().rev() {
            match previous {
                Some(value) => {
                    env.insert(name, value);
                }
                None => {
                    env.remove(&name);
                }
            }
        }
        result
    }

    /// Dedup-inserts structural `kind` into `euf`, caching the canonical [`TermId`] when possible.
    fn intern(&mut self, kind: TermKind) -> TermId {
        if let Some(id) = self.terms.get(&kind) {
            return *id;
        }
        let id = match &kind {
            TermKind::Const(name) => self.euf.intern_const(name.clone()),
            TermKind::App { fun, args } => self.euf.intern_app(fun.clone(), args.clone()),
        };
        self.terms.insert(kind, id);
        id
    }

    /// Encodes pairwise boolean equality via bidirectional implication clauses over literals.
    fn chain_equivalence(&mut self, values: Vec<BoolValue>) -> Result<BoolValue, SolverError> {
        let mut pairs = Vec::new();
        for pair in values.windows(2) {
            pairs.push(self.equivalence(pair[0], pair[1])?);
        }
        self.and_values(pairs)
    }

    /// Conjoins adjacent theory relations encoded as guarded literals.
    fn chain_term_relation(
        &mut self,
        terms: Vec<TermId>,
        relation: TheoryRelation,
    ) -> Result<BoolValue, SolverError> {
        let mut values = Vec::new();
        for pair in terms.windows(2) {
            values.push(self.theory_atom(TheoryKey::new(relation, pair[0], pair[1])));
        }
        self.and_values(values)
    }

    /// Materializes a term-valued `(ite)` into a fresh proxy term plus guarded equalities.
    fn materialize_term_value(&mut self, value: TermValue) -> Result<TermId, SolverError> {
        match value {
            TermValue::Term(term) => Ok(term),
            TermValue::Ite {
                cond,
                then_branch,
                else_branch,
            } => {
                let then_term = self.materialize_term_value(*then_branch)?;
                let else_term = self.materialize_term_value(*else_branch)?;
                if then_term == else_term {
                    return Ok(then_term);
                }

                let proxy_name = format!("$term_ite${}", self.next_term_proxy);
                self.next_term_proxy = self.next_term_proxy.saturating_add(1);
                let proxy = self.intern(TermKind::Const(proxy_name.into_boxed_str()));

                let then_equal =
                    self.theory_atom(TheoryKey::new(TheoryRelation::Eq, proxy, then_term));
                let then_guard = self.or_values([
                    cond.not(),
                    then_equal,
                ])?;
                let else_equal =
                    self.theory_atom(TheoryKey::new(TheoryRelation::Eq, proxy, else_term));
                let else_guard = self.or_values([
                    cond,
                    else_equal,
                ])?;
                self.assert_value(then_guard);
                self.assert_value(else_guard);
                Ok(proxy)
            }
        }
    }

    /// Materializes `(left ≡ right)` via `(!left ∨ right) ∧ (!right ∨ left)` over SAT literals when needed.
    fn equivalence(&mut self, left: BoolValue, right: BoolValue) -> Result<BoolValue, SolverError> {
        let forward = self.or_values([left.not(), right])?;
        let backward = self.or_values([right.not(), left])?;
        self.and_values([forward, backward])
    }

    /// Conjuncts iterator values, short-circuiting on constants and inserting Tseitin helpers when ambiguous.
    fn and_values<I>(&mut self, values: I) -> Result<BoolValue, SolverError>
    where
        I: IntoIterator<Item = BoolValue>,
    {
        let values = values
            .into_iter()
            .filter(|value| *value != BoolValue::Const(true))
            .collect::<Vec<_>>();
        if values.contains(&BoolValue::Const(false)) {
            return Ok(BoolValue::Const(false));
        }
        if values.is_empty() {
            return Ok(BoolValue::Const(true));
        }
        if values.len() == 1 {
            return Ok(values[0]);
        }
        let result = self.fresh_bool().positive();
        let mut defining_clause = Vec::with_capacity(values.len() + 1);
        defining_clause.push(result);
        for value in values {
            let lit = value
                .as_lit()
                .ok_or_else(|| SolverError::new("non-literal value after constant filtering"))?;
            self.add_clause(Box::new([result.not(), lit]));
            defining_clause.push(lit.not());
        }
        self.add_clause(defining_clause.into_boxed_slice());
        Ok(BoolValue::Lit(result))
    }

    /// Disjoins iterator values, short-circuiting on constants and inserting Tseitin helpers when ambiguous.
    fn or_values<I>(&mut self, values: I) -> Result<BoolValue, SolverError>
    where
        I: IntoIterator<Item = BoolValue>,
    {
        let values = values
            .into_iter()
            .filter(|value| *value != BoolValue::Const(false))
            .collect::<Vec<_>>();
        if values.contains(&BoolValue::Const(true)) {
            return Ok(BoolValue::Const(true));
        }
        if values.is_empty() {
            return Ok(BoolValue::Const(false));
        }
        if values.len() == 1 {
            return Ok(values[0]);
        }
        let result = self.fresh_bool().positive();
        let mut forward_clause = Vec::with_capacity(values.len() + 1);
        forward_clause.push(result.not());
        for value in values {
            let lit = value
                .as_lit()
                .ok_or_else(|| SolverError::new("non-literal value after constant filtering"))?;
            self.add_clause(Box::new([lit.not(), result]));
            forward_clause.push(lit);
        }
        self.add_clause(forward_clause.into_boxed_slice());
        Ok(BoolValue::Lit(result))
    }

    /// Reuses or allocates a SAT literal guarding the polarity of `key` inside the checker.
    fn theory_atom(&mut self, key: TheoryKey) -> BoolValue {
        if let Some(var) = self.theory_vars.get(&key) {
            return BoolValue::Lit(var.positive());
        }
        let var = self.fresh_bool();
        self.theory_vars.insert(key, var);
        self.theory_atoms.push((var, key));
        BoolValue::Lit(var.positive())
    }

    /// Finds or allocates the [`BoolVar`] backing proposition `name` for pure boolean literals.
    fn bool_symbol(&mut self, name: Box<str>) -> BoolVar {
        if let Some(var) = self.bool_symbols.get(&name) {
            *var
        } else {
            let var = self.fresh_bool();
            self.bool_symbols.insert(name, var);
            var
        }
    }

    /// Increments [`Self::next_bool_var`] and returns the freshly minted auxiliary variable wrapper.
    fn fresh_bool(&mut self) -> BoolVar {
        let var = BoolVar(self.next_bool_var);
        debug_assert!(self.next_bool_var < u32::MAX);
        self.next_bool_var = self.next_bool_var.saturating_add(1);
        var
    }

    /// Encodes a top-level tautology expectation as unit or empty conflicting clauses when needed.
    fn assert_value(&mut self, value: BoolValue) {
        match value {
            BoolValue::Const(true) => {}
            BoolValue::Const(false) => self.add_clause(Box::new([])),
            BoolValue::Lit(lit) => self.add_clause(Box::new([lit])),
        }
    }

    /// Appends `clause` to the DIMACS accumulator feeding DPLL+EUF reconciliation.
    fn add_clause(&mut self, clause: Box<[Lit]>) {
        self.clauses.push(clause);
    }
}

/// Wrapper over a dense `u32` index into the SAT assignment vector (`0` stays unused).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct BoolVar(u32);

impl BoolVar {
    /// Returns the positive-polarity [`Lit`] referencing this SAT variable slot.
    fn positive(self) -> Lit {
        Lit {
            var: self,
            positive: true,
        }
    }
}

/// DIMACS-style signed literal referencing [`BoolVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Lit {
    /// SAT variable identity this literal watches.
    var: BoolVar,
    /// When false, denotes negation relative to [`Self::var`]'s satisfying assignment bit.
    positive: bool,
}

impl Lit {
    /// Negates polarity while keeping the same underlying [`BoolVar`].
    fn not(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }

    /// Returns the dense watch-list slot for this literal.
    fn watch_index(self) -> usize {
        (self.var.0 as usize) * 2 + usize::from(!self.positive)
    }
}

/// Either a deterministic boolean shortcut or an encoded SAT literal from Tseitinization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoolValue {
    /// Compile-time definite truth value skipping clause emission.
    Const(bool),
    /// Lazy literal whose satisfaction still depends on the SAT backbone.
    Lit(Lit),
}

impl BoolValue {
    /// Applies De Morgan-compatible negation directly on constants or [`Lit`] nodes.
    fn not(self) -> Self {
        match self {
            Self::Const(value) => Self::Const(!value),
            Self::Lit(lit) => Self::Lit(lit.not()),
        }
    }

    /// Yields [`BoolValue::Lit`] payload when lowering still tracks a DIMACS literal.
    fn as_lit(self) -> Option<Lit> {
        match self {
            Self::Const(_) => None,
            Self::Lit(lit) => Some(lit),
        }
    }
}

/// EUF term expression that may still branch on a boolean condition via `(ite)`.
#[derive(Debug, Clone)]
enum TermValue {
    /// Plain interned EUF term.
    Term(TermId),
    /// Term-level if-then-else waiting to be lowered into guarded equalities.
    Ite {
        /// Boolean selector choosing the active branch.
        cond: BoolValue,
        /// Term produced when `cond` is true.
        then_branch: Box<TermValue>,
        /// Term produced when `cond` is false.
        else_branch: Box<TermValue>,
    },
}

/// Canonical EUF polarity carried by guarded SAT literals bridging into [`TheoryAtom`] checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TheoryRelation {
    /// SAT truth forces EUF equality of the keyed terms.
    Eq,
    /// SAT truth interprets EUF inequality between the keyed terms (pairwise distinct path).
    Diseq,
}

/// Normalized unordered pair of [`TermId`] values plus [`TheoryRelation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TheoryKey {
    /// Whether guarding literal truth means equality versus disequality semantics.
    relation: TheoryRelation,
    /// Smaller [`TermId`] after canonical ordering (might equal `right` when only one symbolic term matters).
    left: TermId,
    /// Larger [`TermId`] twin for stable hashing keyed EUF lookups.
    right: TermId,
}

impl TheoryKey {
    /// Builds a stable key swapping endpoints when necessary so hashing deduplicates symmetrical pairs.
    fn new(relation: TheoryRelation, left: TermId, right: TermId) -> Self {
        if left <= right {
            Self {
                relation,
                left,
                right,
            }
        } else {
            Self {
                relation,
                left: right,
                right: left,
            }
        }
    }

    /// Projects this literal's guarded [`TheoryRelation`] onto concrete [`TheoryAtom`] facts once SAT assigns polarity.
    fn atom_for_assignment(self, value: bool) -> TheoryAtom {
        match (self.relation, value) {
            (TheoryRelation::Eq, true) | (TheoryRelation::Diseq, false) => {
                TheoryAtom::Eq(self.left, self.right)
            }
            (TheoryRelation::Eq, false) | (TheoryRelation::Diseq, true) => {
                TheoryAtom::Diseq(self.left, self.right)
            }
        }
    }
}

/// Clause storage paired with two watched literal positions.
#[derive(Debug)]
struct Clause {
    /// Literals belonging to the clause.
    lits: Box<[Lit]>,
    /// Indices of the watched literals inside [`Self::lits`].
    watches: [usize; 2],
}

impl Clause {
    /// Builds one watched clause, defaulting to the first two literals when available.
    fn new(lits: Box<[Lit]>) -> Self {
        let second_watch = usize::from(lits.len() > 1);
        Self {
            lits,
            watches: [0, second_watch],
        }
    }
}

/// Assignment metadata stored per variable during CDCL search.
#[derive(Clone, Copy, Debug)]
struct AssignmentEntry {
    /// Chosen boolean value for the variable.
    value: bool,
    /// Decision level where the value became fixed.
    level: usize,
    /// Clause that implied the assignment, or `None` for decisions.
    reason: Option<usize>,
}

/// CDCL(T) search state with watched literals, clause learning, and eager EUF checks.
struct Dpll {
    /// Boolean clauses guarding both pure props and bridged EUF predicates.
    clauses: Vec<Clause>,
    /// Clauses currently watching each literal polarity.
    watchlists: Vec<Vec<usize>>,
    /// Map from bridging SAT literals to their canonical [`TheoryKey`] metadata pairs.
    theory_atoms: Vec<(BoolVar, TheoryKey)>,
    /// Shared congruence oracle evaluating partial EUF interpretations.
    euf: EufSolver,
    /// Current assignment metadata indexed by dense [`BoolVar`] slot.
    assignments: Vec<Option<AssignmentEntry>>,
    /// Propagation trail in assignment order.
    trail: Vec<Lit>,
    /// Decision-level boundaries inside [`Self::trail`].
    trail_limits: Vec<usize>,
    /// Next trail position whose implications still need propagation.
    propagate_head: usize,
    /// Occurrence-based branching score for each boolean variable.
    variable_scores: Vec<u32>,
    /// Preferred phase for each variable, derived from clause polarity counts.
    preferred_phase: Vec<bool>,
    /// Scratch bitmap reused by conflict analysis to avoid repeated allocation.
    seen: Vec<bool>,
    /// Conflicts observed since the last restart.
    conflict_count: u64,
    /// Threshold triggering the next restart.
    restart_limit: u64,
    /// Sticky contradiction detected while loading clauses.
    has_empty_clause: bool,
}

impl Dpll {
    /// Prepares a solver reserving one slot per boolean variable (index zero stays unused).
    fn new(
        next_bool_var: u32,
        clauses: Vec<Box<[Lit]>>,
        theory_atoms: Vec<(BoolVar, TheoryKey)>,
        euf: EufSolver,
    ) -> Self {
        let variable_count = next_bool_var as usize;
        let mut solver = Self {
            clauses: Vec::with_capacity(clauses.len()),
            watchlists: vec![Vec::new(); variable_count.saturating_mul(2)],
            theory_atoms,
            euf,
            assignments: vec![None; variable_count],
            trail: Vec::new(),
            trail_limits: Vec::new(),
            propagate_head: 0,
            variable_scores: vec![0; variable_count],
            preferred_phase: vec![false; variable_count],
            seen: vec![false; variable_count],
            conflict_count: 0,
            restart_limit: 128,
            has_empty_clause: false,
        };
        let mut polarity_balance = vec![0i32; variable_count];

        for lits in clauses {
            if lits.is_empty() {
                solver.has_empty_clause = true;
                continue;
            }
            for &lit in &lits {
                let index = lit.var.0 as usize;
                polarity_balance[index] += if lit.positive { 1 } else { -1 };
            }
            let clause_index = solver.add_clause(lits);
            if solver.clauses[clause_index].lits.len() == 1
                && !solver.enqueue(solver.clauses[clause_index].lits[0], Some(clause_index))
            {
                solver.has_empty_clause = true;
                break;
            }
        }

        for (index, balance) in polarity_balance.into_iter().enumerate().skip(1) {
            solver.preferred_phase[index] = balance > 0;
        }

        solver
    }

    /// Registers a clause, wires its watches, and returns the stable clause index.
    fn add_clause(&mut self, lits: Box<[Lit]>) -> usize {
        let clause_index = self.clauses.len();
        let clause = Clause::new(lits);
        if let Some(&first) = clause.lits.first() {
            self.watchlists[first.watch_index()].push(clause_index);
        }
        if clause.lits.len() > 1 {
            let second = clause.lits[clause.watches[1]];
            self.watchlists[second.watch_index()].push(clause_index);
        }
        for &lit in &clause.lits {
            let index = lit.var.0 as usize;
            self.variable_scores[index] = self.variable_scores[index].saturating_add(1);
        }
        self.clauses.push(clause);
        clause_index
    }

    /// Returns the current boolean value of `lit`, if its variable has been assigned already.
    fn lit_value(&self, lit: Lit) -> Option<bool> {
        self.assignments[lit.var.0 as usize].map(|entry| entry.value == lit.positive)
    }

    /// Returns the current decision level.
    fn decision_level(&self) -> usize {
        self.trail_limits.len()
    }

    /// Opens one fresh decision level above the current trail.
    fn new_decision_level(&mut self) {
        self.trail_limits.push(self.trail.len());
    }

    /// Records `lit` on the trail together with its reason, rejecting contradictory assignments.
    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        let level = self.decision_level();
        let slot = &mut self.assignments[lit.var.0 as usize];
        match *slot {
            Some(entry) => entry.value == lit.positive,
            None => {
                *slot = Some(AssignmentEntry {
                    value: lit.positive,
                    level,
                    reason,
                });
                self.trail.push(lit);
                true
            }
        }
    }

    /// Solves the accumulated clause set using a standard CDCL loop with theory conflict learning.
    fn solve<B: CheckBudget>(&mut self, budget: &mut B) -> SatResult {
        if self.has_empty_clause {
            return SatResult::Unsat;
        }

        loop {
            if !budget.checkpoint() {
                return SatResult::Interrupted;
            }

            let conflict = match self.propagate(budget) {
                Some(conflict) => conflict,
                None => return SatResult::Interrupted,
            };
            if let Some(conflict) = conflict {
                match self.handle_conflict(conflict) {
                    ConflictOutcome::Unsat => return SatResult::Unsat,
                    ConflictOutcome::Continue => continue,
                }
            }

            let theory_conflict = match self.theory_conflict(budget) {
                Some(conflict) => conflict,
                None => return SatResult::Interrupted,
            };
            if let Some(conflict) = theory_conflict {
                match self.handle_conflict(conflict) {
                    ConflictOutcome::Unsat => return SatResult::Unsat,
                    ConflictOutcome::Continue => continue,
                }
            }

            let all_satisfied = match self.all_clauses_satisfied(budget) {
                Some(value) => value,
                None => return SatResult::Interrupted,
            };
            if all_satisfied {
                return SatResult::Sat;
            }

            if self.conflict_count >= self.restart_limit && self.decision_level() > 0 {
                self.backtrack(0);
                self.conflict_count = 0;
                self.restart_limit = self.restart_limit.saturating_mul(2);
                continue;
            }

            let Some(branch_lit) = (match self.choose_branch_literal(budget) {
                Some(lit) => lit,
                None => return SatResult::Interrupted,
            }) else {
                return SatResult::Sat;
            };

            self.new_decision_level();
            if !self.enqueue(branch_lit, None) {
                return SatResult::Unsat;
            }
        }
    }

    /// Runs watched-literal propagation until fixpoint or a falsified clause is found.
    fn propagate<B: CheckBudget>(&mut self, budget: &mut B) -> Option<Option<Box<[Lit]>>> {
        while self.propagate_head < self.trail.len() {
            if !budget.checkpoint() {
                return None;
            }
            let assigned = self.trail[self.propagate_head];
            self.propagate_head += 1;
            let watched_false = assigned.not().watch_index();
            let watched_clauses = std::mem::take(&mut self.watchlists[watched_false]);
            let mut still_watching = Vec::with_capacity(watched_clauses.len());
            let mut cursor = 0usize;

            while cursor < watched_clauses.len() {
                if !budget.checkpoint() {
                    still_watching.extend_from_slice(&watched_clauses[cursor..]);
                    self.watchlists[watched_false] = still_watching;
                    return None;
                }

                let clause_index = watched_clauses[cursor];
                cursor += 1;

                let clause_watches = self.clauses[clause_index].watches;
                let false_watch_slot =
                    if self.clauses[clause_index].lits[clause_watches[0]] == assigned.not() {
                        0
                    } else {
                        1
                    };
                let other_watch_slot = 1 - false_watch_slot;
                let other_watch_index = clause_watches[other_watch_slot];
                let other_watch_lit = self.clauses[clause_index].lits[other_watch_index];

                if self.lit_value(other_watch_lit) == Some(true) {
                    still_watching.push(clause_index);
                    continue;
                }

                let replacement = {
                    let clause = &self.clauses[clause_index];
                    let mut replacement = None;
                    for candidate_index in 0..clause.lits.len() {
                        if !budget.checkpoint() {
                            still_watching.push(clause_index);
                            still_watching.extend_from_slice(&watched_clauses[cursor..]);
                            self.watchlists[watched_false] = still_watching;
                            return None;
                        }
                        if candidate_index == clause.watches[0] || candidate_index == clause.watches[1]
                        {
                            continue;
                        }
                        let candidate = clause.lits[candidate_index];
                        if self.lit_value(candidate) != Some(false) {
                            replacement = Some(candidate_index);
                            break;
                        }
                    }
                    replacement
                };

                if let Some(replacement) = replacement {
                    self.clauses[clause_index].watches[false_watch_slot] = replacement;
                    let new_watch = self.clauses[clause_index].lits[replacement];
                    self.watchlists[new_watch.watch_index()].push(clause_index);
                    continue;
                }

                match self.lit_value(other_watch_lit) {
                    Some(false) => {
                        still_watching.push(clause_index);
                        still_watching.extend_from_slice(&watched_clauses[cursor..]);
                        self.watchlists[watched_false] = still_watching;
                        return Some(Some(self.clauses[clause_index].lits.clone()));
                    }
                    Some(true) => still_watching.push(clause_index),
                    None => {
                        if !self.enqueue(other_watch_lit, Some(clause_index)) {
                            still_watching.push(clause_index);
                            still_watching.extend_from_slice(&watched_clauses[cursor..]);
                            self.watchlists[watched_false] = still_watching;
                            return Some(Some(self.clauses[clause_index].lits.clone()));
                        }
                        still_watching.push(clause_index);
                    }
                }
            }

            self.watchlists[watched_false] = still_watching;
        }

        Some(None)
    }

    /// Returns one blocking clause when the currently assigned theory literals are inconsistent.
    fn theory_conflict<B: CheckBudget>(&self, budget: &mut B) -> Option<Option<Box<[Lit]>>> {
        let mut assigned_atoms = Vec::with_capacity(self.theory_atoms.len());
        for (var, key) in &self.theory_atoms {
            if !budget.checkpoint() {
                return None;
            }
            if let Some(entry) = self.assignments[var.0 as usize] {
                assigned_atoms.push((
                    Lit {
                        var: *var,
                        positive: entry.value,
                    }
                    .not(),
                    key.atom_for_assignment(entry.value),
                ));
            }
        }
        let atoms = assigned_atoms
            .iter()
            .map(|(_, atom)| atom.clone())
            .collect::<Vec<_>>();
        match self.euf.check_with_budget(&atoms, budget) {
            EufCheckOutcome::Consistent => Some(None),
            EufCheckOutcome::Conflict(conflict) => Some(Some(
                self.minimize_theory_conflict(
                    &self.conflict_relevant_atoms(&assigned_atoms, conflict.left, conflict.right),
                    budget,
                )?
                    .into_boxed_slice(),
            )),
            EufCheckOutcome::Interrupted => None,
        }
    }

    /// Narrows theory-conflict minimization to atoms that touch the conflicting term cone.
    ///
    /// Equalities outside the recursive subterm closure of the final disequality endpoints cannot
    /// help prove that particular conflict in the current EUF encoding, so dropping them up front
    /// both speeds up shrinking and produces tighter learned clauses.
    fn conflict_relevant_atoms(
        &self,
        assigned_atoms: &[(Lit, TheoryAtom)],
        left: TermId,
        right: TermId,
    ) -> Vec<(Lit, TheoryAtom)> {
        let mut relevant_terms = vec![false; self.euf.terms().len()];
        let mut stack = vec![left, right];

        while let Some(term) = stack.pop() {
            let index = term.index();
            if relevant_terms.get(index).copied().unwrap_or(true) {
                continue;
            }
            relevant_terms[index] = true;
            if let Some(TermKind::App { args, .. }) = self.euf.terms().get(index) {
                stack.extend(args.iter().copied());
            }
        }

        let filtered = assigned_atoms
            .iter()
            .filter(|(_, atom)| match atom {
                TheoryAtom::Eq(left, right) | TheoryAtom::Diseq(left, right) => {
                    relevant_terms[left.index()] || relevant_terms[right.index()]
                }
            })
            .cloned()
            .collect::<Vec<_>>();

        if filtered.is_empty() {
            assigned_atoms.to_vec()
        } else {
            filtered
        }
    }

    /// Greedily shrinks one theory conflict into a much smaller learned blocking clause.
    ///
    /// The starting point is the full set of currently assigned theory literals. Each pass tries
    /// to delete one literal and keeps the deletion only if EUF still reports a conflict. This is
    /// not a minimum unsat core algorithm, but even a single shrinking pass materially improves
    /// learned clause quality compared to blocking every active theory literal.
    fn minimize_theory_conflict<B: CheckBudget>(
        &self,
        assigned_atoms: &[(Lit, TheoryAtom)],
        budget: &mut B,
    ) -> Option<Vec<Lit>> {
        let current_level = self.decision_level();
        let mut kept = assigned_atoms.to_vec();
        let mut current_level_count = kept
            .iter()
            .filter(|(lit, _)| {
                self.assignments[lit.var.0 as usize]
                    .is_some_and(|entry| entry.level == current_level)
            })
            .count();
        let mut order = (0..kept.len()).collect::<Vec<_>>();
        order.sort_unstable_by_key(|&index| {
            self.assignments[kept[index].0.var.0 as usize]
                .map(|entry| usize::from(entry.level == current_level))
                .unwrap_or(0)
        });
        let mut order_index = 0usize;

        while order_index < order.len() {
            if !budget.checkpoint() {
                return None;
            }
            let index = order[order_index];
            if index >= kept.len() {
                order_index += 1;
                continue;
            }
            let removing_current_level = self.assignments[kept[index].0.var.0 as usize]
                .is_some_and(|entry| entry.level == current_level);
            if removing_current_level && current_level_count <= 1 {
                order_index += 1;
                continue;
            }
            let trial_atoms = kept
                .iter()
                .enumerate()
                .filter_map(|(trial_index, (_, atom))| {
                    (trial_index != index).then_some(atom.clone())
                })
                .collect::<Vec<_>>();
            let redundant = match self.euf.check_with_budget(&trial_atoms, budget) {
                EufCheckOutcome::Consistent => false,
                EufCheckOutcome::Conflict(_) => true,
                EufCheckOutcome::Interrupted => return None,
            };
            if redundant {
                if removing_current_level {
                    current_level_count -= 1;
                }
                kept.remove(index);
                for later in &mut order[(order_index + 1)..] {
                    if *later > index {
                        *later -= 1;
                    }
                }
            } else {
                order_index += 1;
            }
        }

        Some(kept.into_iter().map(|(lit, _)| lit).collect())
    }

    /// Learns from `conflict_clause`, backtracks non-chronologically, and enqueues the asserting literal.
    fn handle_conflict(&mut self, conflict_clause: Box<[Lit]>) -> ConflictOutcome {
        let current_level = self.decision_level();
        if current_level == 0 {
            return ConflictOutcome::Unsat;
        }

        let (learned_clause, backtrack_level) = self.analyze_conflict(&conflict_clause);
        self.bump_clause_activity(&learned_clause);
        self.backtrack(backtrack_level);
        if learned_clause.is_empty() {
            self.has_empty_clause = true;
            return ConflictOutcome::Unsat;
        }

        let clause_index = self.add_clause(learned_clause.clone().into_boxed_slice());
        let asserting_lit = self.clauses[clause_index].lits[0];
        if !self.enqueue(asserting_lit, Some(clause_index)) {
            self.has_empty_clause = true;
            return ConflictOutcome::Unsat;
        }

        self.conflict_count = self.conflict_count.saturating_add(1);
        ConflictOutcome::Continue
    }

    /// Performs first-UIP conflict analysis and returns `(learned_clause, backtrack_level)`.
    fn analyze_conflict(&mut self, conflict_clause: &[Lit]) -> (Vec<Lit>, usize) {
        for seen in &mut self.seen {
            *seen = false;
        }

        let current_level = self.decision_level();
        let mut learned = Vec::new();
        let mut pending_current_level = 0usize;
        let mut trail_index = self.trail.len();
        let mut clause = conflict_clause.to_vec();

        loop {
            for &lit in &clause {
                let var_index = lit.var.0 as usize;
                let Some(entry) = self.assignments[var_index] else {
                    continue;
                };
                if self.seen[var_index] || entry.level == 0 {
                    continue;
                }
                self.seen[var_index] = true;
                if entry.level == current_level {
                    pending_current_level += 1;
                } else {
                    learned.push(lit);
                }
            }
            if pending_current_level == 0 {
                return self.decision_cube_clause();
            }

            let pivot = loop {
                trail_index -= 1;
                let lit = self.trail[trail_index];
                if self.seen[lit.var.0 as usize] {
                    break lit;
                }
            };
            let pivot_index = pivot.var.0 as usize;
            self.seen[pivot_index] = false;
            pending_current_level -= 1;

            if pending_current_level == 0 {
                learned.insert(0, pivot.not());
                break;
            }

            let Some(reason) = self.assignments[pivot_index]
                .expect("pivot variable must stay assigned during analysis")
                .reason
            else {
                return self.decision_cube_clause();
            };
            clause.clear();
            clause.extend(
                self.clauses[reason]
                    .lits
                    .iter()
                    .copied()
                    .filter(|lit| lit.var != pivot.var),
            );
        }

        let backtrack_level = learned
            .iter()
            .skip(1)
            .filter_map(|lit| self.assignments[lit.var.0 as usize].map(|entry| entry.level))
            .max()
            .unwrap_or(0);

        (learned, backtrack_level)
    }

    /// Falls back to a sound but weaker learned clause blocking the current decision cube.
    ///
    /// This path is used only when first-UIP analysis encounters a decision literal before the
    /// pending current-level count collapses as expected. The resulting clause says: "not all of
    /// these decisions together again", which remains valid even though it is less precise than a
    /// normal implication-graph explanation.
    fn decision_cube_clause(&self) -> (Vec<Lit>, usize) {
        let current_level = self.decision_level();
        let mut learned = Vec::with_capacity(current_level);
        if current_level == 0 {
            return (learned, 0);
        }

        let current_decision = self.trail[self.trail_limits[current_level - 1]].not();
        learned.push(current_decision);
        for level in (0..(current_level - 1)).rev() {
            let decision = self.trail[self.trail_limits[level]].not();
            learned.push(decision);
        }

        let backtrack_level = learned
            .iter()
            .skip(1)
            .filter_map(|lit| self.assignments[lit.var.0 as usize].map(|entry| entry.level))
            .max()
            .unwrap_or(0);

        (learned, backtrack_level)
    }

    /// Backtracks to `level`, removing every assignment from later decision levels.
    fn backtrack(&mut self, level: usize) {
        let trail_len = self.trail_limits.get(level).copied().unwrap_or(self.trail.len());
        while self.trail.len() > trail_len {
            if let Some(lit) = self.trail.pop() {
                self.assignments[lit.var.0 as usize] = None;
            }
        }
        self.trail_limits.truncate(level);
        self.propagate_head = self.propagate_head.min(trail_len);
    }

    /// Bumps branching activity for literals that survived conflict analysis.
    fn bump_clause_activity(&mut self, clause: &[Lit]) {
        for &lit in clause {
            let index = lit.var.0 as usize;
            self.variable_scores[index] = self.variable_scores[index].saturating_add(8);
            self.preferred_phase[index] = lit.positive;
        }
    }

    /// Returns true when every clause is already satisfied by the current partial assignment.
    fn all_clauses_satisfied<B: CheckBudget>(&self, budget: &mut B) -> Option<bool> {
        for clause in &self.clauses {
            if !budget.checkpoint() {
                return None;
            }
            let mut satisfied = false;
            for &lit in &clause.lits {
                if !budget.checkpoint() {
                    return None;
                }
                if self.lit_value(lit) == Some(true) {
                    satisfied = true;
                    break;
                }
            }
            if !satisfied {
                return Some(false);
            }
        }
        Some(true)
    }

    /// Chooses the highest-activity still-unassigned variable and applies its preferred phase.
    fn choose_branch_literal<B: CheckBudget>(&self, budget: &mut B) -> Option<Option<Lit>> {
        let mut best_var = None;

        for index in 1..self.assignments.len() {
            if !budget.checkpoint() {
                return None;
            }
            if self.assignments[index].is_some() {
                continue;
            }
            let replace = match best_var {
                Some(current) => self.variable_preferred_over(index, current),
                None => true,
            };
            if replace {
                best_var = Some(index);
            }
        }

        Some(best_var.map(|index| Lit {
            var: BoolVar(index as u32),
            positive: self.preferred_phase[index],
        }))
    }

    /// Returns true when `candidate_index` should be chosen ahead of `current_index`.
    fn variable_preferred_over(&self, candidate_index: usize, current_index: usize) -> bool {
        let candidate_score = self.variable_scores[candidate_index];
        let current_score = self.variable_scores[current_index];
        if candidate_score != current_score {
            return candidate_score > current_score;
        }

        candidate_index < current_index
    }
}

/// Result of processing one conflict inside the CDCL main loop.
enum ConflictOutcome {
    /// The search learned a clause and should continue.
    Continue,
    /// The conflict happened at decision level zero and proves unsatisfiability.
    Unsat,
}

#[cfg(test)]
mod tests {
    use smtlib_lexer::parse_many;
    use smtlib_syntax::Command;

    use super::*;

    fn run(input: &str) -> SatResult {
        let mut solver = Solver::new();
        for expr in parse_many(input).expect("valid sexpr") {
            let command = Command::from_sexpr(expr).expect("valid command");
            if let SolverEvent::CheckSat(result) =
                solver.handle_command(command).expect("command succeeds")
            {
                return result;
            }
        }
        SatResult::Unknown
    }

    fn run_with_fuel(input: &str, fuel: &mut Fuel) -> SatResult {
        let mut solver = Solver::new();
        for expr in parse_many(input).expect("valid sexpr") {
            let command = Command::from_sexpr(expr).expect("valid command");
            if let SolverEvent::CheckSat(result) = solver
                .handle_command_with_budget(command, fuel)
                .expect("command succeeds")
            {
                return result;
            }
        }
        SatResult::Unknown
    }

    #[test]
    fn detects_direct_euf_conflict() {
        assert_eq!(
            run("(assert (= a b)) (assert (distinct (f a) (f b))) (check-sat)"),
            SatResult::Unsat
        );
    }

    #[test]
    fn supports_push_pop() {
        let input = "(assert (= a b)) (push 1) (assert (distinct a b)) (pop 1) (check-sat)";
        assert_eq!(run(input), SatResult::Sat);
    }

    #[test]
    fn solves_implication_conflict_without_status_hint() {
        assert_eq!(
            run("(assert (=> p false)) (assert p) (check-sat)"),
            SatResult::Unsat
        );
    }

    #[test]
    fn solves_boolean_equality_to_theory_atom() {
        assert_eq!(
            run("(assert (= flag (= a b))) (assert flag) (assert (distinct a b)) (check-sat)"),
            SatResult::Unsat
        );
    }

    #[test]
    fn solves_boolean_ite_with_theory_branches() {
        assert_eq!(
            run(
                "(assert (ite p (= a b) (distinct a b))) (assert p) (assert (distinct a b)) (check-sat)"
            ),
            SatResult::Unsat
        );
    }

    #[test]
    fn solves_negated_equality_as_disequality() {
        assert_eq!(
            run("(assert (not (= a b))) (assert (= (f a) (f b))) (check-sat)"),
            SatResult::Sat
        );
        assert_eq!(
            run("(assert (not (= a b))) (assert (= a b)) (check-sat)"),
            SatResult::Unsat
        );
    }

    #[test]
    fn status_hint_is_metadata_only() {
        assert_eq!(
            run("(assert false) (set-info :status sat) (check-sat)"),
            SatResult::Unsat
        );
    }

    #[test]
    fn check_sat_returns_interrupted_when_fuel_is_exhausted() {
        let mut fuel = Fuel::new(0);
        assert_eq!(
            run_with_fuel("(assert (= a b)) (check-sat)", &mut fuel),
            SatResult::Interrupted
        );
    }

    #[test]
    fn interrupted_result_formats_distinctly_from_unknown() {
        assert_eq!(SatResult::Interrupted.to_string(), "interrupted");
        assert_eq!(SatResult::Interrupted.as_smtlib(), "unknown");
    }
}
