//! Incremental SMT-LIB command lowering for the current QF_UF-focused solver.
//!
//! This crate owns the command-level state machine that sits above the boolean
//! plus EUF backend in [`solver_core`]: asserted formulas, zero-arity
//! definitions, and push/pop frames. The lowering step consumes parsed
//! [`Command`] values and produces observable events such as
//! [`SolverEvent::CheckSat`].
//!
//! `set-info :status ...` is intentionally treated as benchmark metadata only.
//! The parser preserves it for test harnesses, but the lowering stage never
//! uses that annotation to influence the actual satisfiability result.

use std::collections::HashMap;
use std::fmt;

use euf_core::{EufSolver, FunId, TermId};
use smtlib_lexer::SExpr;
use smtlib_syntax::{Command, DefineFun, Symbol};
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

/// Reserved identifier for a future activation-literal based frame encoding.
///
/// The current solver still stores assertions structurally per frame, but the
/// identifier remains part of the public model because stack frames already
/// expose it and downstream tooling may want to correlate with that shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ActivationLiteral(pub u32);

/// Structural EUF term key used to deduplicate lowering results before interning into [`EufSolver`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum EufTermKey {
    /// Nullary uninterpreted symbol allocated by the lowering layer.
    Const(FunId),
    /// Uninterpreted function application.
    App {
        /// Function symbol identity allocated by the lowering layer.
        fun: FunId,
        /// Argument term identifiers in call order.
        args: Box<[TermId]>,
    },
}

/// One top-level asserted formula recorded by the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssertedFormula {
    /// Monotonic identifier assigned when the formula enters the assertion stack.
    pub id: AssertedFormulaId,
    /// Original SMT-LIB term as parsed by `smtlib-syntax`.
    pub formula: SExpr,
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
pub struct Solver<'src> {
    /// Original SMT-LIB source text backing every stored S-expression span.
    source: &'src str,
    /// Top-level asserted formulas in stack order across all active frames.
    assertions: Vec<AssertedFormula>,
    /// Frames recorded by `(push)`, newest last; [`Frame::asserted_len`] trims on `(pop)`.
    frames: Vec<Frame>,
    /// Zero-arity `define-fun` bodies keyed by declared symbol names.
    definitions: HashMap<Symbol, SExpr>,
    /// Next monotonic [`FrameId`] counter for newly pushed scopes.
    next_frame: u32,
    /// Next reserved [`ActivationLiteral`] counter paired with frames.
    next_activation: u32,
}

impl<'src> Solver<'src> {
    /// Creates an empty solver with no declarations, assertions, or frames.
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            ..Self::default()
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
        let mut checker = SatEufCheck::new(self.source, &self.definitions);
        for asserted in &self.assertions {
            if !budget.checkpoint() {
                return SatResult::Interrupted;
            }
            if checker.assert_formula(&asserted.formula).is_err() {
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
    fn assert_formula(&mut self, formula: SExpr) -> Result<(), SolverError> {
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
struct SatEufCheck<'src> {
    /// Original SMT-LIB source text used to decode atoms from stored spans.
    source: &'src str,
    /// Zero-arity definitional expansions available while lowering formulas.
    definitions: &'src HashMap<Symbol, SExpr>,
    /// Backend congruence solver sharing interned term ids.
    euf: EufSolver,
    /// Surface-level uninterpreted symbol table owned by lowering rather than the EUF core.
    fun_symbols: HashMap<Box<str>, FunId>,
    /// Structural EUF term cache mapping to reusable [`TermId`] handles.
    terms: HashMap<EufTermKey, TermId>,
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

impl<'src> SatEufCheck<'src> {
    /// Seeds an empty checker referencing `definitions` for macro expansion lookups.
    fn new(source: &'src str, definitions: &'src HashMap<Symbol, SExpr>) -> Self {
        Self {
            source,
            definitions,
            euf: EufSolver::new(),
            fun_symbols: HashMap::new(),
            terms: HashMap::new(),
            bool_symbols: HashMap::new(),
            theory_atoms: Vec::new(),
            theory_vars: HashMap::new(),
            clauses: Vec::new(),
            next_bool_var: 1,
            next_term_proxy: 0,
        }
    }

    /// Parses `formula`, maps it through `self`, then encodes top-level satisfaction as clauses.
    fn assert_formula(&mut self, formula: &SExpr) -> Result<(), SolverError> {
        let mut env = HashMap::new();
        let value = self.formula(formula, &mut env)?;
        self.assert_value(value);
        Ok(())
    }

    /// Builds the DIMACS+EUF handshake from accumulated structure and invokes CDCL(T).
    fn check_with_budget<B: CheckBudget>(self, budget: &mut B) -> SatResult {
        solver_core::solve_with_budget(
            self.next_bool_var,
            self.clauses,
            self.theory_atoms,
            self.euf,
            budget,
        )
    }

    /// Recursive boolean lowering for atoms, connectors, equality, `(ite)`, `(let)`, and definitions.
    fn formula(
        &mut self,
        expr: &SExpr,
        env: &mut HashMap<Box<str>, SExpr>,
    ) -> Result<BoolValue, SolverError> {
        if let Some(atom) = expr.as_atom(self.source) {
            let atom = atom.as_ref();
            if let Some(bound) = env.get(atom).cloned() {
                return self.formula(&bound, env);
            }
            if let Some(definition) = self.definitions.get(&Symbol::new(atom)) {
                return self.formula(definition, env);
            }
            return Ok(match atom {
                "true" => BoolValue::Const(true),
                "false" => BoolValue::Const(false),
                _ => BoolValue::Lit(self.bool_symbol(atom.into())?.positive()),
            });
        }

        let items = expr
            .as_list()
            .ok_or_else(|| SolverError::new("formula must be an atom or list"))?;
        let head = items
            .first()
            .and_then(|expr| expr.as_atom(self.source))
            .ok_or_else(|| SolverError::new("formula list must start with an atom"))?;

        match head.as_ref() {
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
                ))?);
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
                .as_atom(self.source)
                .ok_or_else(|| SolverError::new("let binding name must be an atom"))?;
            let previous = env.insert(name.clone().into_owned().into_boxed_str(), pair[1].clone());
            inserted.push((name.into_owned().into_boxed_str(), previous));
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
        if let Some(atom) = expr.as_atom(self.source) {
            let atom = atom.as_ref();
            if atom == "true" || atom == "false" {
                return Ok(None);
            }
            if let Some(bound) = env.get(atom).cloned() {
                return self.term_value(&bound, env);
            }
            if let Some(definition) = self.definitions.get(&Symbol::new(atom)) {
                return self.term_value(definition, env);
            }
            let fun = self.fun_symbol(atom.into());
            return Ok(Some(TermValue::Term(self.intern(EufTermKey::Const(fun)))));
        }

        let items = expr
            .as_list()
            .ok_or_else(|| SolverError::new("term must be an atom or list"))?;
        let head = items
            .first()
            .and_then(|expr| expr.as_atom(self.source))
            .ok_or_else(|| SolverError::new("term list must start with an atom"))?;
        if head.as_ref() == "let" && items.len() == 3 {
            return self.term_value_let(&items[1], &items[2], env);
        }
        if head.as_ref() == "ite" && items.len() == 4 {
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
        if matches!(
            head.as_ref(),
            "and" | "or" | "not" | "=>" | "=" | "distinct"
        ) {
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
        let fun = self.fun_symbol(head.into_owned().into_boxed_str());
        Ok(Some(TermValue::Term(
            self.intern(EufTermKey::App { fun, args }),
        )))
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
                .as_atom(self.source)
                .ok_or_else(|| SolverError::new("let binding name must be an atom"))?;
            let previous = env.insert(name.clone().into_owned().into_boxed_str(), pair[1].clone());
            inserted.push((name.into_owned().into_boxed_str(), previous));
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
    fn intern(&mut self, kind: EufTermKey) -> TermId {
        if let Some(id) = self.terms.get(&kind) {
            return *id;
        }
        let id = match &kind {
            EufTermKey::Const(fun) => self.euf.intern_term(*fun, Box::default()),
            EufTermKey::App { fun, args } => self.euf.intern_term(*fun, args.clone()),
        };
        self.terms.insert(kind, id);
        id
    }

    /// Finds or allocates one EUF function-symbol identity for `name`.
    ///
    /// Constants and function applications intentionally share this namespace so
    /// a nullary surface symbol reuses the same underlying uninterpreted symbol.
    fn fun_symbol(&mut self, name: Box<str>) -> FunId {
        if let Some(fun) = self.fun_symbols.get(&name) {
            *fun
        } else {
            let fun = self.euf.alloc_fun();
            self.fun_symbols.insert(name, fun);
            fun
        }
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
                self.next_term_proxy = self
                    .next_term_proxy
                    .checked_add(1)
                    .ok_or_else(|| SolverError::new("term ite proxy overflow"))?;
                let proxy_fun = self.fun_symbol(proxy_name.into_boxed_str());
                let proxy = self.intern(EufTermKey::Const(proxy_fun));

                let then_equal =
                    self.theory_atom(TheoryKey::new(TheoryRelation::Eq, proxy, then_term))?;
                let then_guard = self.or_values([cond.not(), then_equal])?;
                let else_equal =
                    self.theory_atom(TheoryKey::new(TheoryRelation::Eq, proxy, else_term))?;
                let else_guard = self.or_values([cond, else_equal])?;
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

    /// Reuses or allocates a SAT literal guarding the polarity of `key` inside the checker.
    fn theory_atom(&mut self, key: TheoryKey) -> Result<BoolValue, SolverError> {
        if let Some(var) = self.theory_vars.get(&key) {
            return Ok(BoolValue::Lit(var.positive()));
        }
        let var = self.fresh_bool()?;
        self.theory_vars.insert(key, var);
        self.theory_atoms.push((var, key));
        Ok(BoolValue::Lit(var.positive()))
    }

    /// Finds or allocates the [`BoolVar`] backing proposition `name` for pure boolean literals.
    fn bool_symbol(&mut self, name: Box<str>) -> Result<BoolVar, SolverError> {
        if let Some(var) = self.bool_symbols.get(&name) {
            Ok(*var)
        } else {
            let var = self.fresh_bool()?;
            self.bool_symbols.insert(name, var);
            Ok(var)
        }
    }

    /// Increments [`Self::next_bool_var`] and returns the freshly minted auxiliary variable wrapper.
    fn fresh_bool(&mut self) -> Result<BoolVar, SolverError> {
        let var = BoolVar::new(self.next_bool_var)
            .ok_or_else(|| SolverError::new("boolean variable ids start at 1"))?;
        self.next_bool_var = self
            .next_bool_var
            .checked_add(1)
            .ok_or_else(|| SolverError::new("boolean variable overflow"))?;
        Ok(var)
    }

    /// Encodes a top-level tautology expectation as unit or empty conflicting clauses when needed.
    fn assert_value(&mut self, value: BoolValue) {
        match value {
            BoolValue::Const(true) => {}
            BoolValue::Const(false) => self.add_clause(Box::new([])),
            BoolValue::Lit(lit) => self.add_clause(Box::new([lit])),
        }
    }

    /// Appends `clause` to the DIMACS accumulator feeding CDCL(T).
    fn add_clause(&mut self, clause: Box<[Lit]>) {
        self.clauses.push(clause);
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
    fn check_sat_returns_interrupted_when_fuel_is_exhausted() {
        let mut fuel = Fuel::new(0);
        assert_eq!(
            run_with_fuel("(assert (= a b)) (check-sat)", &mut fuel),
            SatResult::Interrupted
        );
    }
}
