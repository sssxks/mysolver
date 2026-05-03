//! Incremental SMT-LIB command lowering for the current QF_UF-focused solver.
//!
//! This crate owns the command-level state machine that sits above the boolean
//! plus EUF backend in [`solver_core`]: asserted formulas, zero-arity
//! definitions, push/pop frames, and the persistent semantic IR used to avoid
//! rebuilding the SMT-LIB view of the world on every `check-sat`.
//!
//! `set-info :status ...` is intentionally treated as benchmark metadata only.
//! The parser preserves it for test harnesses, but the lowering stage never
//! uses that annotation to influence the actual satisfiability result.

use std::collections::HashMap;
use std::fmt;

use euf_core::{EufSolver, FunId, TermId};
use smtlib_lexer::SExpr;
use smtlib_syntax::{Command, DefineFun, SortExpr};
use solver_core::{BoolVar, Lit, TheoryKey, TheoryRelation};
pub use solver_core::{CheckBudget, Fuel, SatResult};

/// Result payload emitted by a `check-sat` command.
pub type CheckSatResult = SatResult;

/// Stable identifier for one push/pop frame in the solver stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameId(pub u32);

/// Stable identifier for one asserted top-level formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AssertedFormulaId(pub u32);

/// Stable identifier for one frame-scoped activation literal above the backend.
///
/// Each pushed frame receives one activation id. Assertions recorded while that
/// frame is current are guarded by the corresponding backend boolean variable
/// and `check-sat` enables the currently active frames through assumptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ActivationLiteral(pub u32);

/// Stable identifier for one persistent lowered formula node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LowerFormulaId(u32);

/// One top-level asserted formula recorded by the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssertedFormula {
    /// Monotonic identifier assigned when the formula enters the assertion stack.
    pub id: AssertedFormulaId,
    /// Persistent lowered formula held across repeated `check-sat` calls.
    pub formula: LowerFormulaId,
    /// Activation guard controlling whether the assertion is currently in scope.
    activation: Option<ActivationLiteral>,
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
#[derive(Debug)]
pub struct Solver<'src> {
    /// Original SMT-LIB source text backing every stored S-expression span.
    source: &'src str,
    /// Top-level asserted formulas in stack order across all active frames.
    assertions: Vec<AssertedFormula>,
    /// Frames recorded by `(push)`, newest last; [`Frame::asserted_len`] trims on `(pop)`.
    frames: Vec<Frame>,
    /// Zero-arity `define-fun` bodies keyed by declared symbol names after validation and lowering.
    definitions: DefinitionTable,
    /// Persistent semantic lowering context reused across repeated checks.
    lower: LowerContext,
    /// Persistent backend state reused across repeated `check-sat` calls.
    backend: IncrementalBackend,
    /// Next monotonic [`FrameId`] counter for newly pushed scopes.
    next_frame: u32,
    /// Next reserved [`ActivationLiteral`] counter paired with frames.
    next_activation: u32,
    /// Next monotonic [`AssertedFormulaId`] assigned to newly asserted formulas.
    next_asserted_formula: u32,
}

impl<'src> Solver<'src> {
    /// Creates an empty solver with no declarations, assertions, or frames.
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            backend: IncrementalBackend::new(),
            assertions: Vec::new(),
            frames: Vec::new(),
            definitions: DefinitionTable::new(),
            lower: LowerContext::new(),
            next_frame: 0,
            next_activation: 0,
            next_asserted_formula: 0,
        }
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
    pub fn check_sat(&mut self) -> CheckSatResult {
        let mut budget = UnlimitedBudget;
        self.check_sat_with_budget(&mut budget)
    }

    /// Solves the current assertion stack under `budget`.
    ///
    /// Returning [`SatResult::Interrupted`] preserves the distinction between
    /// semantic incompleteness and caller-imposed resource limits.
    pub fn check_sat_with_budget<B: CheckBudget>(&mut self, budget: &mut B) -> CheckSatResult {
        let mut budget = SearchBudget::new(budget);
        self.backend.check_with_budget(&self.frames, &mut budget)
    }

    /// Stores a zero-arity lowered definition; other arities remain unsupported.
    fn define_fun(&mut self, define_fun: DefineFun) -> Result<(), SolverError> {
        if !define_fun.binders.is_empty() {
            return Err(SolverError::new(format!(
                "define-fun `{}` has arity {}; only arity-0 definitions are supported in this path",
                define_fun.name.as_str(),
                define_fun.binders.len()
            )));
        }
        let mut active_definitions = vec![define_fun.name.as_str().into()];
        let value = if is_bool_sort(&define_fun.result) {
            LoweredDefinitionValue::Formula(self.lower_formula(
                &define_fun.body,
                &mut HashMap::new(),
                &mut active_definitions,
            )?)
        } else {
            let term = self
                .lower_maybe_term(
                    &define_fun.body,
                    &mut HashMap::new(),
                    &mut active_definitions,
                )?
                .ok_or_else(|| {
                    SolverError::new(format!(
                        "define-fun `{}` body does not lower to a term",
                        define_fun.name.as_str()
                    ))
                })?;
            LoweredDefinitionValue::Term(term)
        };
        self.definitions
            .insert(define_fun.name.as_str().into(), value);
        Ok(())
    }

    /// Assigns [`AssertedFormulaId`] and pushes the lowered formula onto the assertion stack.
    fn assert_formula(&mut self, formula: SExpr) -> Result<(), SolverError> {
        let lowered = self.lower_formula(&formula, &mut HashMap::new(), &mut Vec::new())?;
        let activation = self.frames.last().map(|frame| frame.activation);
        self.backend
            .assert_formula(&self.lower, lowered, activation)?;
        let id = AssertedFormulaId(self.next_asserted_formula);
        self.next_asserted_formula = self
            .next_asserted_formula
            .checked_add(1)
            .ok_or_else(|| SolverError::new("asserted formula id overflow"))?;
        self.assertions.push(AssertedFormula {
            id,
            formula: lowered,
            activation,
        });
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

    /// Lowers one expression in boolean position into persistent semantic IR.
    fn lower_formula(
        &mut self,
        expr: &SExpr,
        env: &mut LetEnv,
        active_definitions: &mut Vec<Box<str>>,
    ) -> Result<LowerFormulaId, SolverError> {
        if let Some(atom) = expr.as_atom(self.source) {
            let atom = atom.as_ref();
            if let Some(bound) = env.get(atom).cloned() {
                return self.lower_formula(&bound, env, active_definitions);
            }
            if active_definitions.iter().any(|name| name.as_ref() == atom) {
                return Err(SolverError::new(format!(
                    "cyclic define-fun reference involving `{atom}`"
                )));
            }
            if let Some(definition) = self.definitions.get(atom) {
                return match definition {
                    LoweredDefinitionValue::Formula(formula) => Ok(formula),
                    LoweredDefinitionValue::Term(_) => Err(SolverError::new(format!(
                        "symbol `{atom}` denotes a term definition, not a formula"
                    ))),
                };
            }
            return match atom {
                "true" => self.lower.formula_true(),
                "false" => self.lower.formula_false(),
                _ => {
                    let symbol = self.bool_symbol(atom.into())?;
                    self.lower.intern_formula(FormulaNode::BoolSymbol(symbol))
                }
            };
        }

        let items = expr
            .as_list()
            .ok_or_else(|| SolverError::new("formula must be an atom or list"))?;
        let head = items
            .first()
            .and_then(|expr| expr.as_atom(self.source))
            .ok_or_else(|| SolverError::new("formula list must start with an atom"))?;

        match head.as_ref() {
            "and" => {
                let formulas = items[1..]
                    .iter()
                    .map(|arg| self.lower_formula(arg, env, active_definitions))
                    .collect::<Result<Vec<_>, _>>()?;
                self.lower.and_formula(formulas)
            }
            "or" => {
                let formulas = items[1..]
                    .iter()
                    .map(|arg| self.lower_formula(arg, env, active_definitions))
                    .collect::<Result<Vec<_>, _>>()?;
                self.lower.or_formula(formulas)
            }
            "not" if items.len() == 2 => {
                let inner = self.lower_formula(&items[1], env, active_definitions)?;
                self.lower.intern_formula(FormulaNode::Not(inner))
            }
            "=>" if items.len() == 3 => {
                let premise = self.lower_formula(&items[1], env, active_definitions)?;
                let conclusion = self.lower_formula(&items[2], env, active_definitions)?;
                self.lower
                    .intern_formula(FormulaNode::Implies(premise, conclusion))
            }
            "=" => self.lower_formula_equal(&items[1..], env, active_definitions),
            "distinct" => self.lower_formula_distinct(&items[1..], env, active_definitions),
            "ite" if items.len() == 4 => {
                let cond = self.lower_formula(&items[1], env, active_definitions)?;
                let then_branch = self.lower_formula(&items[2], env, active_definitions)?;
                let else_branch = self.lower_formula(&items[3], env, active_definitions)?;
                self.lower.formula_ite(cond, then_branch, else_branch)
            }
            "let" if items.len() == 3 => {
                self.lower_formula_let(&items[1], &items[2], env, active_definitions)
            }
            _ => Err(SolverError::new(format!(
                "unsupported formula shape headed by `{head}`"
            ))),
        }
    }

    /// Handles `"="` chains for pure booleans versus EUF terms.
    fn lower_formula_equal(
        &mut self,
        args: &[SExpr],
        env: &mut LetEnv,
        active_definitions: &mut Vec<Box<str>>,
    ) -> Result<LowerFormulaId, SolverError> {
        if args.len() < 2 {
            return self.lower.formula_true();
        }
        let term_values = args
            .iter()
            .map(|arg| self.lower_maybe_term(arg, env, active_definitions))
            .collect::<Result<Vec<_>, _>>()?;
        if term_values.iter().all(Option::is_some) {
            let terms = term_values.into_iter().flatten().collect::<Vec<_>>();
            return self.lower.term_eq(terms);
        }
        let formulas = args
            .iter()
            .map(|arg| self.lower_formula(arg, env, active_definitions))
            .collect::<Result<Vec<_>, _>>()?;
        self.lower.bool_eq(formulas)
    }

    /// Expands pairwise disequalities into one persistent `distinct` formula node.
    fn lower_formula_distinct(
        &mut self,
        args: &[SExpr],
        env: &mut LetEnv,
        active_definitions: &mut Vec<Box<str>>,
    ) -> Result<LowerFormulaId, SolverError> {
        if args.len() < 2 {
            return self.lower.formula_true();
        }
        let terms = args
            .iter()
            .map(|arg| self.lower_maybe_term(arg, env, active_definitions))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| SolverError::new("distinct contains a non-term argument"))?;
        self.lower.distinct(terms)
    }

    /// Applies temporary symbol bindings inside `bindings_expr`, evaluates `body`, then restores `env`.
    fn lower_formula_let(
        &mut self,
        bindings_expr: &SExpr,
        body: &SExpr,
        env: &mut LetEnv,
        active_definitions: &mut Vec<Box<str>>,
    ) -> Result<LowerFormulaId, SolverError> {
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
                .as_atom(self.source)
                .ok_or_else(|| SolverError::new("let binding name must be an atom"))?;
            let previous = env.insert(name.clone().into_owned().into_boxed_str(), pair[1].clone());
            inserted.push((name.into_owned().into_boxed_str(), previous));
        }
        let result = self.lower_formula(body, env, active_definitions);
        rollback_let_env(env, inserted);
        result
    }

    /// Converts `expr` to a term-valued lowering result when it denotes EUF structure.
    fn lower_maybe_term(
        &mut self,
        expr: &SExpr,
        env: &mut LetEnv,
        active_definitions: &mut Vec<Box<str>>,
    ) -> Result<Option<TermId>, SolverError> {
        if let Some(atom) = expr.as_atom(self.source) {
            let atom = atom.as_ref();
            if atom == "true" || atom == "false" {
                return Ok(None);
            }
            if let Some(bound) = env.get(atom).cloned() {
                return self.lower_maybe_term(&bound, env, active_definitions);
            }
            if active_definitions.iter().any(|name| name.as_ref() == atom) {
                return Err(SolverError::new(format!(
                    "cyclic define-fun reference involving `{atom}`"
                )));
            }
            if let Some(definition) = self.definitions.get(atom) {
                return Ok(match definition {
                    LoweredDefinitionValue::Formula(_) => None,
                    LoweredDefinitionValue::Term(term) => Some(term),
                });
            }
            let fun = self.fun_symbol(atom.into());
            return self.intern_term_node(TermNode::Const(fun)).map(Some);
        }

        let items = expr
            .as_list()
            .ok_or_else(|| SolverError::new("term must be an atom or list"))?;
        let head = items
            .first()
            .and_then(|expr| expr.as_atom(self.source))
            .ok_or_else(|| SolverError::new("term list must start with an atom"))?;
        if head.as_ref() == "let" && items.len() == 3 {
            return self.lower_term_let(&items[1], &items[2], env, active_definitions);
        }
        if head.as_ref() == "ite" && items.len() == 4 {
            let cond = self.lower_formula(&items[1], env, active_definitions)?;
            let then_branch = self
                .lower_maybe_term(&items[2], env, active_definitions)?
                .ok_or_else(|| SolverError::new("term ite then-branch is not a term"))?;
            let else_branch = self
                .lower_maybe_term(&items[3], env, active_definitions)?
                .ok_or_else(|| SolverError::new("term ite else-branch is not a term"))?;
            return if then_branch == else_branch {
                Ok(Some(then_branch))
            } else {
                self.intern_term_node(TermNode::TermIte {
                    cond,
                    then_branch,
                    else_branch,
                })
                .map(Some)
            };
        }
        if matches!(
            head.as_ref(),
            "and" | "or" | "not" | "=>" | "=" | "distinct"
        ) {
            return Ok(None);
        }
        let args = items[1..]
            .iter()
            .map(|arg| self.lower_maybe_term(arg, env, active_definitions))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| SolverError::new("function application contains a non-term argument"))?;
        let fun = self.fun_symbol(head.into_owned().into_boxed_str());
        self.intern_term_node(TermNode::App {
                fun,
                args: args.into_boxed_slice(),
            })
            .map(Some)
    }

    /// `let`-binder aware variant of [`Self::lower_maybe_term`] sharing the rollback discipline of formula lets.
    fn lower_term_let(
        &mut self,
        bindings_expr: &SExpr,
        body: &SExpr,
        env: &mut LetEnv,
        active_definitions: &mut Vec<Box<str>>,
    ) -> Result<Option<TermId>, SolverError> {
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
                .as_atom(self.source)
                .ok_or_else(|| SolverError::new("let binding name must be an atom"))?;
            let previous = env.insert(name.clone().into_owned().into_boxed_str(), pair[1].clone());
            inserted.push((name.into_owned().into_boxed_str(), previous));
        }
        let result = self.lower_maybe_term(body, env, active_definitions);
        rollback_let_env(env, inserted);
        result
    }

    /// Reuses or allocates one backend-stable SAT variable for `name`.
    fn bool_symbol(&mut self, name: Box<str>) -> Result<BoolVar, SolverError> {
        if let Some(var) = self.lower.bool_symbols.get(&name) {
            return Ok(*var);
        }
        let var = self.backend.fresh_bool()?;
        self.lower.bool_symbols.insert(name, var);
        Ok(var)
    }

    /// Reuses or allocates one backend-stable EUF function symbol for `name`.
    fn fun_symbol(&mut self, name: Box<str>) -> FunId {
        if let Some(fun) = self.lower.fun_symbols.get(&name) {
            return *fun;
        }
        let fun = self.backend.euf.alloc_fun();
        self.lower.fun_symbols.insert(name, fun);
        fun
    }

    /// Deduplicates one lowered term node and materializes its backend `TermId` once overall.
    fn intern_term_node(&mut self, node: TermNode) -> Result<TermId, SolverError> {
        if let Some(id) = self.lower.term_intern.get(&node) {
            return Ok(*id);
        }
        let id = match &node {
            TermNode::Const(fun) => self.backend.euf.intern_term(*fun, Box::default()),
            TermNode::App { fun, args } => self.backend.euf.intern_term(*fun, args.clone()),
            TermNode::TermIte {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond = self.backend.formula(&self.lower, *cond)?;
                let proxy_fun = self.backend.euf.alloc_fun();
                let proxy = self.backend.euf.intern_term(proxy_fun, Box::default());

                let then_equal = self.backend.theory_atom(TheoryKey::new(
                    TheoryRelation::Eq,
                    proxy,
                    *then_branch,
                ))?;
                let then_guard = self.backend.or_values([cond.not(), then_equal])?;
                let else_equal = self.backend.theory_atom(TheoryKey::new(
                    TheoryRelation::Eq,
                    proxy,
                    *else_branch,
                ))?;
                let else_guard = self.backend.or_values([cond, else_equal])?;
                self.backend.assert_value(then_guard, None)?;
                self.backend.assert_value(else_guard, None)?;
                proxy
            }
        };
        self.lower.term_intern.insert(node, id);
        Ok(id)
    }
}

/// Restores the `let` environment to the state it had before the current binder scope.
fn rollback_let_env(env: &mut LetEnv, inserted: Vec<(Box<str>, Option<SExpr>)>) {
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
}

/// Returns whether a parsed sort denotes SMT-LIB `Bool`.
fn is_bool_sort(sort: &SortExpr) -> bool {
    matches!(sort, SortExpr::Simple(symbol) if symbol.as_str() == "Bool")
}

/// Temporary `let` binding environment used only while lowering one top-level expression.
type LetEnv = HashMap<Box<str>, SExpr>;

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

/// One validated zero-arity definition stored above the backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoweredDefinitionValue {
    /// Definition that expands to a boolean formula.
    Formula(LowerFormulaId),
    /// Definition that expands to a EUF term.
    Term(TermId),
}

/// Map of surface definition names to already-lowered semantic ids.
#[derive(Debug)]
struct DefinitionTable {
    /// Validated zero-arity definitions keyed by surface symbol text.
    entries: HashMap<Box<str>, LoweredDefinitionValue>,
}

impl DefinitionTable {
    /// Creates an empty table with no surface definitions in scope.
    fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Replaces the lowered value associated with `name`.
    fn insert(&mut self, name: Box<str>, value: LoweredDefinitionValue) {
        self.entries.insert(name, value);
    }

    /// Retrieves a lowered definition by surface symbol name.
    fn get(&self, name: &str) -> Option<LoweredDefinitionValue> {
        self.entries.get(name).copied()
    }
}

/// Persistent semantic lowering context shared by all future backend builds.
#[derive(Debug)]
struct LowerContext {
    /// Stable boolean symbol table keyed directly by backend SAT variables.
    bool_symbols: HashMap<Box<str>, BoolVar>,
    /// Stable uninterpreted function symbol table keyed directly by backend `FunId`s.
    fun_symbols: HashMap<Box<str>, FunId>,
    /// Persistent formula arena indexed by [`LowerFormulaId`].
    formulas: Vec<FormulaNode>,
    /// Hash-consing table deduplicating semantically identical formula nodes.
    formula_intern: HashMap<FormulaNode, LowerFormulaId>,
    /// Hash-consing table deduplicating semantically identical term nodes to one backend `TermId`.
    term_intern: HashMap<TermNode, TermId>,
}

impl LowerContext {
    /// Creates an empty context with no symbols, formulas, or interned backend terms.
    fn new() -> Self {
        Self {
            bool_symbols: HashMap::new(),
            fun_symbols: HashMap::new(),
            formulas: Vec::new(),
            formula_intern: HashMap::new(),
            term_intern: HashMap::new(),
        }
    }

    /// Returns the canonical persistent `true` node.
    fn formula_true(&mut self) -> Result<LowerFormulaId, SolverError> {
        self.intern_formula(FormulaNode::True)
    }

    /// Returns the canonical persistent `false` node.
    fn formula_false(&mut self) -> Result<LowerFormulaId, SolverError> {
        self.intern_formula(FormulaNode::False)
    }

    /// Returns one persistent conjunction node with identity simplifications.
    fn and_formula(
        &mut self,
        formulas: Vec<LowerFormulaId>,
    ) -> Result<LowerFormulaId, SolverError> {
        match formulas.as_slice() {
            [] => self.formula_true(),
            [single] => Ok(*single),
            _ => self.intern_formula(FormulaNode::And(formulas.into_boxed_slice())),
        }
    }

    /// Returns one persistent disjunction node with identity simplifications.
    fn or_formula(&mut self, formulas: Vec<LowerFormulaId>) -> Result<LowerFormulaId, SolverError> {
        match formulas.as_slice() {
            [] => self.formula_false(),
            [single] => Ok(*single),
            _ => self.intern_formula(FormulaNode::Or(formulas.into_boxed_slice())),
        }
    }

    /// Returns one persistent boolean equivalence chain.
    fn bool_eq(&mut self, formulas: Vec<LowerFormulaId>) -> Result<LowerFormulaId, SolverError> {
        match formulas.as_slice() {
            [] | [_] => self.formula_true(),
            _ => self.intern_formula(FormulaNode::BoolEq(formulas.into_boxed_slice())),
        }
    }

    /// Returns one persistent term equality chain.
    fn term_eq(&mut self, terms: Vec<TermId>) -> Result<LowerFormulaId, SolverError> {
        match terms.as_slice() {
            [] | [_] => self.formula_true(),
            _ => self.intern_formula(FormulaNode::TermEq(terms.into_boxed_slice())),
        }
    }

    /// Returns one persistent pairwise disequality formula.
    fn distinct(&mut self, terms: Vec<TermId>) -> Result<LowerFormulaId, SolverError> {
        match terms.as_slice() {
            [] | [_] => self.formula_true(),
            _ => self.intern_formula(FormulaNode::Distinct(terms.into_boxed_slice())),
        }
    }

    /// Returns one persistent formula-valued `(ite)` with trivial branch elimination.
    fn formula_ite(
        &mut self,
        cond: LowerFormulaId,
        then_branch: LowerFormulaId,
        else_branch: LowerFormulaId,
    ) -> Result<LowerFormulaId, SolverError> {
        if then_branch == else_branch {
            return Ok(then_branch);
        }
        self.intern_formula(FormulaNode::FormulaIte {
            cond,
            then_branch,
            else_branch,
        })
    }

    /// Deduplicates `node` and returns its stable formula id.
    fn intern_formula(&mut self, node: FormulaNode) -> Result<LowerFormulaId, SolverError> {
        if let Some(id) = self.formula_intern.get(&node) {
            return Ok(*id);
        }
        let index = u32::try_from(self.formulas.len())
            .map_err(|_| SolverError::new("too many lowered formulas"))?;
        let id = LowerFormulaId(index);
        self.formulas.push(node.clone());
        self.formula_intern.insert(node, id);
        Ok(id)
    }

    /// Returns the formula node addressed by `id`.
    fn formula(&self, id: LowerFormulaId) -> &FormulaNode {
        &self.formulas[id.0 as usize]
    }
}

/// Persistent boolean formula IR stored above the backend.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FormulaNode {
    /// Constant truth.
    True,
    /// Constant falsity.
    False,
    /// Surface boolean symbol used directly in formula position.
    BoolSymbol(BoolVar),
    /// Boolean negation.
    Not(LowerFormulaId),
    /// Conjunction of one or more child formulas.
    And(Box<[LowerFormulaId]>),
    /// Disjunction of one or more child formulas.
    Or(Box<[LowerFormulaId]>),
    /// Binary implication.
    Implies(LowerFormulaId, LowerFormulaId),
    /// Chained boolean equality.
    BoolEq(Box<[LowerFormulaId]>),
    /// Chained term equality.
    TermEq(Box<[TermId]>),
    /// Pairwise term disequality.
    Distinct(Box<[TermId]>),
    /// Formula-valued conditional.
    FormulaIte {
        /// Guard deciding which branch is active.
        cond: LowerFormulaId,
        /// Branch chosen when `cond` is true.
        then_branch: LowerFormulaId,
        /// Branch chosen when `cond` is false.
        else_branch: LowerFormulaId,
    },
}

/// Persistent EUF term IR stored above the backend.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TermNode {
    /// Nullary uninterpreted symbol.
    Const(FunId),
    /// Uninterpreted function application.
    App {
        /// Applied function symbol.
        fun: FunId,
        /// Backend term arguments in call order.
        args: Box<[TermId]>,
    },
    /// Term-valued conditional lowered once into guarded proxy equalities.
    TermIte {
        /// Guard deciding which branch is active.
        cond: LowerFormulaId,
        /// Branch chosen when `cond` is true.
        then_branch: TermId,
        /// Branch chosen when `cond` is false.
        else_branch: TermId,
    },
}

/// Persistent SAT+EUF backend reused across repeated `check-sat` calls.
#[derive(Debug)]
struct IncrementalBackend {
    /// Backend congruence solver sharing interned term ids.
    euf: EufSolver,
    /// Persistent CDCL(T) clause database and learned-state owner.
    sat: solver_core::IncrementalSolver,
    /// Cached formula encodings so repeated IR nodes are Tseitinized once overall.
    formula_cache: HashMap<LowerFormulaId, BoolValue>,
    /// Dedup lookup so identical theory literals reuse one `BoolVar`.
    theory_vars: HashMap<TheoryKey, BoolVar>,
    /// Activation variable assigned to each frame that has emitted guarded clauses.
    activation_vars: HashMap<ActivationLiteral, BoolVar>,
}

impl IncrementalBackend {
    /// Creates an empty persistent backend with no clauses, variables, or theory atoms.
    fn new() -> Self {
        Self {
            euf: EufSolver::new(),
            sat: solver_core::IncrementalSolver::new(),
            formula_cache: HashMap::new(),
            theory_vars: HashMap::new(),
            activation_vars: HashMap::new(),
        }
    }
    /// Lowers one persistent top-level formula into permanent backend clauses.
    fn assert_formula(
        &mut self,
        lower: &LowerContext,
        formula: LowerFormulaId,
        activation: Option<ActivationLiteral>,
    ) -> Result<(), SolverError> {
        let value = self.formula(lower, formula)?;
        self.assert_value(value, activation)?;
        Ok(())
    }

    /// Solves the currently active frame prefix by asserting those frame activations as assumptions.
    fn check_with_budget<B: CheckBudget>(&mut self, frames: &[Frame], budget: &mut B) -> SatResult {
        let assumptions = frames
            .iter()
            .filter_map(|frame| {
                self.activation_vars
                    .get(&frame.activation)
                    .copied()
                    .map(BoolVar::positive)
            })
            .collect::<Vec<_>>();
        self.sat
            .solve_with_assumptions_and_budget(&self.euf, &assumptions, budget)
    }

    /// Materializes one persistent formula node into clauses and theory guards.
    fn formula(
        &mut self,
        lower: &LowerContext,
        formula: LowerFormulaId,
    ) -> Result<BoolValue, SolverError> {
        if let Some(value) = self.formula_cache.get(&formula) {
            return Ok(*value);
        }
        let node = lower.formula(formula).clone();
        let value = match node {
            FormulaNode::True => BoolValue::Const(true),
            FormulaNode::False => BoolValue::Const(false),
            FormulaNode::BoolSymbol(symbol) => BoolValue::Lit(symbol.positive()),
            FormulaNode::Not(inner) => self.formula(lower, inner)?.not(),
            FormulaNode::And(args) => {
                let values = args
                    .iter()
                    .map(|arg| self.formula(lower, *arg))
                    .collect::<Result<Vec<_>, _>>()?;
                self.and_values(values)?
            }
            FormulaNode::Or(args) => {
                let values = args
                    .iter()
                    .map(|arg| self.formula(lower, *arg))
                    .collect::<Result<Vec<_>, _>>()?;
                self.or_values(values)?
            }
            FormulaNode::Implies(premise, conclusion) => {
                let premise = self.formula(lower, premise)?.not();
                let conclusion = self.formula(lower, conclusion)?;
                self.or_values([premise, conclusion])?
            }
            FormulaNode::BoolEq(args) => {
                let values = args
                    .iter()
                    .map(|arg| self.formula(lower, *arg))
                    .collect::<Result<Vec<_>, _>>()?;
                self.chain_equivalence(values)?
            }
            FormulaNode::TermEq(args) => {
                self.chain_term_relation(args.into_vec(), TheoryRelation::Eq)?
            }
            FormulaNode::Distinct(args) => {
                let terms = args.into_vec();
                let mut values = Vec::new();
                for left in 0..terms.len() {
                    for right in (left + 1)..terms.len() {
                        values.push(self.theory_atom(TheoryKey::new(
                            TheoryRelation::Diseq,
                            terms[left],
                            terms[right],
                        ))?);
                    }
                }
                self.and_values(values)?
            }
            FormulaNode::FormulaIte {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond = self.formula(lower, cond)?;
                let then_value = self.formula(lower, then_branch)?;
                let else_value = self.formula(lower, else_branch)?;
                let left = self.and_values([cond, then_value])?;
                let right = self.and_values([cond.not(), else_value])?;
                self.or_values([left, right])?
            }
        };
        self.formula_cache.insert(formula, value);
        Ok(value)
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
            values.push(self.theory_atom(TheoryKey::new(relation, pair[0], pair[1]))?);
        }
        self.and_values(values)
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
        let result = self.fresh_bool()?.positive();
        let mut defining_clause = Vec::with_capacity(values.len() + 1);
        defining_clause.push(result);
        for value in values {
            let lit = value
                .as_lit()
                .ok_or_else(|| SolverError::new("non-literal value after constant filtering"))?;
            self.add_clause(Box::new([!result, lit]));
            defining_clause.push(!lit);
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
        let result = self.fresh_bool()?.positive();
        let mut forward_clause = Vec::with_capacity(values.len() + 1);
        forward_clause.push(!result);
        for value in values {
            let lit = value
                .as_lit()
                .ok_or_else(|| SolverError::new("non-literal value after constant filtering"))?;
            self.add_clause(Box::new([!lit, result]));
            forward_clause.push(lit);
        }
        self.add_clause(forward_clause.into_boxed_slice());
        Ok(BoolValue::Lit(result))
    }

    /// Reuses or allocates a SAT literal guarding the polarity of `key` inside the builder.
    fn theory_atom(&mut self, key: TheoryKey) -> Result<BoolValue, SolverError> {
        if let Some(var) = self.theory_vars.get(&key) {
            return Ok(BoolValue::Lit(var.positive()));
        }
        let var = self.fresh_bool()?;
        self.theory_vars.insert(key, var);
        self.sat.add_theory_atom(var, key);
        Ok(BoolValue::Lit(var.positive()))
    }

    /// Returns one fresh backend-local boolean variable.
    fn fresh_bool(&mut self) -> Result<BoolVar, SolverError> {
        self.sat
            .alloc_bool_var()
            .ok_or_else(|| SolverError::new("boolean variable overflow"))
    }

    /// Reuses or allocates the SAT variable enabling one frame's guarded assertions.
    fn activation_var(&mut self, activation: ActivationLiteral) -> Result<BoolVar, SolverError> {
        if let Some(var) = self.activation_vars.get(&activation) {
            return Ok(*var);
        }
        let var = self.fresh_bool()?;
        self.activation_vars.insert(activation, var);
        Ok(var)
    }

    /// Encodes a top-level assertion, optionally guarded by one frame activation literal.
    fn assert_value(
        &mut self,
        value: BoolValue,
        activation: Option<ActivationLiteral>,
    ) -> Result<(), SolverError> {
        let clause: Box<[Lit]> = match (activation, value) {
            (_, BoolValue::Const(true)) => return Ok(()),
            (None, BoolValue::Const(false)) => Vec::new().into_boxed_slice(),
            (None, BoolValue::Lit(lit)) => vec![lit].into_boxed_slice(),
            (Some(activation), BoolValue::Const(false)) => {
                vec![!self.activation_var(activation)?.positive()].into_boxed_slice()
            }
            (Some(activation), BoolValue::Lit(lit)) => {
                let guard = self.activation_var(activation)?.positive();
                vec![!guard, lit].into_boxed_slice()
            }
        };
        self.add_clause(clause);
        Ok(())
    }

    /// Appends `clause` to the persistent SAT database.
    fn add_clause(&mut self, clause: Box<[Lit]>) {
        self.sat.add_clause(clause);
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
            Self::Lit(lit) => Self::Lit(!lit),
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

#[cfg(test)]
mod tests {
    use smtlib_lexer::parse_many;
    use smtlib_syntax::Command;

    use super::*;

    fn run(input: &str) -> SatResult {
        let source = input;
        let mut solver = Solver::new(source);
        for expr in parse_many(source).expect("valid sexpr") {
            let command = Command::from_sexpr(source, expr).expect("valid command");
            if let SolverEvent::CheckSat(result) =
                solver.handle_command(command).expect("command succeeds")
            {
                return result;
            }
        }
        SatResult::Unknown
    }

    fn run_all_checks(input: &str) -> Vec<SatResult> {
        let source = input;
        let mut solver = Solver::new(source);
        let mut results = Vec::new();
        for expr in parse_many(source).expect("valid sexpr") {
            let command = Command::from_sexpr(source, expr).expect("valid command");
            if let SolverEvent::CheckSat(result) =
                solver.handle_command(command).expect("command succeeds")
            {
                results.push(result);
            }
        }
        results
    }

    fn run_with_fuel(input: &str, fuel: &mut Fuel) -> SatResult {
        let source = input;
        let mut solver = Solver::new(source);
        for expr in parse_many(source).expect("valid sexpr") {
            let command = Command::from_sexpr(source, expr).expect("valid command");
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
    fn repeated_check_sat_reuses_lowered_assertions() {
        assert_eq!(
            run_all_checks(
                "(define-fun same () Bool (= a b)) \
                 (assert same) \
                 (check-sat) \
                 (assert (distinct a b)) \
                 (check-sat)"
            ),
            vec![SatResult::Sat, SatResult::Unsat]
        );
    }

    #[test]
    fn repeated_check_sat_tracks_nested_frame_activation() {
        assert_eq!(
            run_all_checks(
                "(push 1) \
                 (assert p) \
                 (push 1) \
                 (assert (not p)) \
                 (check-sat) \
                 (pop 1) \
                 (check-sat) \
                 (pop 1) \
                 (check-sat)"
            ),
            vec![SatResult::Unsat, SatResult::Sat, SatResult::Sat]
        );
    }

    #[test]
    fn popped_frame_assertions_stay_dormant_after_later_checks() {
        assert_eq!(
            run_all_checks(
                "(assert (= a b)) \
                 (push 1) \
                 (assert (distinct a b)) \
                 (check-sat) \
                 (pop 1) \
                 (check-sat) \
                 (check-sat)"
            ),
            vec![SatResult::Unsat, SatResult::Sat, SatResult::Sat]
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
    fn recursive_define_fun_is_rejected() {
        let source = "(define-fun self () Bool self)";
        let expr = parse_many(source)
            .expect("valid sexpr")
            .into_vec()
            .remove(0);
        let command = Command::from_sexpr(source, expr).expect("valid command");
        let mut solver = Solver::new(source);
        let error = solver
            .handle_command(command)
            .expect_err("recursive definition must fail");
        assert!(
            error
                .to_string()
                .contains("cyclic define-fun reference involving `self`")
        );
    }
}
