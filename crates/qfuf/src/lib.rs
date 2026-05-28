//! Incremental SMT-LIB driver for QF-UF over the local `sat` and `euf` crates.

use std::collections::{HashMap, HashSet};
use std::io::{self, Write};

use euf::{EufTheory, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef};
#[cfg(feature = "telemetry")]
use telemetry::{Gauges, TelemetryRecorder};
use sat::{AddClauseResult, Lit, SatResult, Solver};

/// Runs the solver over one complete SMT-LIB input string and returns the textual
/// responses produced by query commands.
pub fn run_script(input: &str) -> Result<String, String> {
    let mut driver = Driver::new();
    #[cfg(feature = "telemetry")]
    let recorder = start_telemetry_recorder_from_env()?;
    let result = run_script_with_driver(&mut driver, input);
    #[cfg(feature = "telemetry")]
    return finalize_telemetry_result(recorder, driver.telemetry_gauges(), result);
    #[cfg(not(feature = "telemetry"))]
    result
}

/// Runs the solver over stdin and writes responses to stdout.
pub fn run_stdio() -> Result<(), String> {
    let input = io::read_to_string(io::stdin())
        .map_err(|error| format!("failed to read stdin: {error}"))?;
    let output = run_script(&input)?;
    let mut stdout = io::stdout().lock();
    stdout
        .write_all(output.as_bytes())
        .map_err(|error| format!("failed to write stdout: {error}"))?;
    stdout
        .flush()
        .map_err(|error| format!("failed to flush stdout: {error}"))
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
    }

    Ok(output)
}

/// Starts the optional telemetry recorder configured through the environment.
#[cfg(feature = "telemetry")]
fn start_telemetry_recorder_from_env() -> Result<Option<TelemetryRecorder>, String> {
    TelemetryRecorder::start_from_env()
        .map_err(|error| format!("failed to start telemetry recorder from env: {error}"))
}

/// Finalizes the optional telemetry recorder without losing the primary solver result.
#[cfg(feature = "telemetry")]
fn finalize_telemetry_result(
    recorder: Option<TelemetryRecorder>,
    gauges: Gauges,
    result: Result<String, String>,
) -> Result<String, String> {
    let finish_result = recorder
        .map(|recorder| {
            recorder
                .finish(gauges)
                .map_err(|error| format!("failed to finalize telemetry recorder: {error}"))
        })
        .transpose()
        .map(|_| ());
    match (result, finish_result) {
        (Ok(output), Ok(())) => Ok(output),
        (Ok(_), Err(error)) => Err(error),
        (Err(error), Ok(())) => Err(error),
        (Err(error), Err(finish_error)) => Err(format!("{error}; {finish_error}")),
    }
}

/// One parsed S-expression.
#[derive(Clone, Debug, Eq, PartialEq)]
enum SExpr {
    /// One atom token.
    Atom(Box<str>),
    /// One list form.
    List(Vec<SExpr>),
}

/// One supported SMT-LIB command.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Command {
    /// `(set-logic ...)`
    SetLogic(Box<str>),
    /// `(set-info ...)`
    SetInfo,
    /// `(declare-sort name 0)`
    DeclareSort {
        /// Declared sort name.
        name: Box<str>,
    },
    /// `(declare-fun name (args...) result)`
    DeclareFun {
        /// Declared function name.
        name: Box<str>,
        /// Declared argument sort names.
        args: Vec<Box<str>>,
        /// Declared result sort name.
        result: Box<str>,
    },
    /// `(declare-const name sort)`
    DeclareConst {
        /// Declared constant name.
        name: Box<str>,
        /// Declared constant sort name.
        sort: Box<str>,
    },
    /// `(assert expr)`
    Assert(SExpr),
    /// `(push 1)`
    Push(u32),
    /// `(pop 1)`
    Pop(u32),
    /// `(check-sat)`
    CheckSat,
    /// `(exit)`
    Exit,
}

/// One declared function symbol.
#[derive(Copy, Clone, Debug)]
struct FunDecl {
    /// Canonical symbol identifier.
    symbol: SymbolId,
    /// Declared argument count.
    arity: u32,
    /// Result sort.
    result_sort: SortId,
}

/// One lowered Boolean subexpression.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum BoolView {
    /// Constant true.
    True,
    /// Constant false.
    False,
    /// Existing SAT literal.
    Lit(Lit),
}

/// One local `let` binding visible while lowering one expression subtree.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LocalBinding {
    /// One Boolean binding cached as a SAT-level Boolean view.
    Bool(BoolView),
    /// One term binding cached as a canonical term and its sort.
    Term {
        /// Canonical term identifier.
        term: TermId,
        /// Sort of the cached term.
        sort: SortId,
    },
}

/// One interactive SMT driver instance.
#[derive(Debug, Default)]
struct Driver {
    /// Incremental SAT engine.
    sat: Solver,
    /// EUF theory module.
    euf: EufTheory,
    /// Declared sort environment.
    sorts: HashMap<Box<str>, SortId>,
    /// Declared function environment.
    funs: HashMap<Box<str>, FunDecl>,
    /// Reuse map for canonical equality atoms.
    eq_lits: HashMap<(TermId, TermId), Lit>,
    /// Cached sort of each term interned through this driver.
    term_sorts: HashMap<TermId, SortId>,
    /// Bool-sorted terms that already have two-valued domain clauses attached.
    bool_terms_constrained: HashSet<TermId>,
    /// Cached Boolean sort id.
    bool_sort: Option<SortId>,
    /// Cached canonical true term.
    true_term: Option<TermId>,
    /// Cached canonical false term.
    false_term: Option<TermId>,
    /// Whether the root clause `true != false` has already been asserted.
    bool_constants_separated: bool,
    /// Lexically scoped `let` bindings used while lowering one expression.
    let_scopes: Vec<HashMap<Box<str>, LocalBinding>>,
    /// Monotonic counter for internally introduced fresh constants.
    fresh_const_counter: u64,
}

impl Driver {
    /// Creates one empty QF-UF driver.
    fn new() -> Self {
        Self::default()
    }

    /// Captures the current combined SAT+EUF gauges for one telemetry sample boundary.
    #[cfg(feature = "telemetry")]
    fn telemetry_gauges(&self) -> Gauges {
        Gauges {
            sat: self.sat.telemetry_gauges(),
            euf: self.euf.telemetry_gauges(),
        }
    }

    /// Executes one parsed command and optionally returns one output line.
    fn execute(&mut self, command: Command) -> Result<Option<String>, String> {
        match command {
            Command::SetLogic(logic) => {
                if logic.as_ref() != "QF_UF" {
                    return Err(format!("unsupported logic: {logic}"));
                }
                Ok(None)
            }
            Command::SetInfo => Ok(None),
            Command::DeclareSort { name } => {
                let sort = self.euf.intern_sort(SortRef::Uninterpreted { name: &name });
                self.sorts.insert(name, sort);
                Ok(None)
            }
            Command::DeclareFun { name, args, result } => {
                let arg_sorts = args
                    .iter()
                    .map(|arg| self.resolve_sort(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let arity = u32::try_from(arg_sorts.len())
                    .map_err(|_| "function arity exceeds u32".to_owned())?;
                let result_sort = self.resolve_sort(&result)?;
                let symbol = self.euf.intern_symbol(SymbolRef {
                    name: &name,
                    arg_sorts: &arg_sorts,
                    result_sort,
                });
                self.funs.insert(
                    name,
                    FunDecl {
                        symbol,
                        arity,
                        result_sort,
                    },
                );
                Ok(None)
            }
            Command::DeclareConst { name, sort } => self.execute(Command::DeclareFun {
                name,
                args: Vec::new(),
                result: sort,
            }),
            Command::Assert(expr) => {
                let view = self.lower_formula(&expr)?;
                self.assert_bool_view(view)?;
                Ok(None)
            }
            Command::Push(levels) => {
                for _ in 0..levels {
                    self.sat.push();
                }
                Ok(None)
            }
            Command::Pop(levels) => {
                self.sat
                    .pop(levels as usize)
                    .map_err(|error| format!("pop failed: {error:?}"))?;
                Ok(None)
            }
            Command::CheckSat => Ok(Some(
                match self.sat.solve_with_assumptions(&[], &mut self.euf) {
                    SatResult::Sat => "sat".to_owned(),
                    SatResult::Unsat => "unsat".to_owned(),
                },
            )),
            Command::Exit => Ok(None),
        }
    }

    /// Resolves one sort name into one canonical sort identifier.
    fn resolve_sort(&mut self, name: &str) -> Result<SortId, String> {
        if name == "Bool" {
            let sort = self.euf.intern_sort(SortRef::Bool);
            self.bool_sort = Some(sort);
            return Ok(sort);
        }
        self.sorts
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown sort: {name}"))
    }

    /// Asserts one lowered Boolean view into SAT.
    /// Asserts one lowered Boolean view into SAT.
    fn assert_bool_view(&mut self, view: BoolView) -> Result<(), String> {
        match view {
            BoolView::True => Ok(()),
            BoolView::False => accept_add_result(self.sat.add_clause(&[])),
            BoolView::Lit(lit) => accept_add_result(self.sat.add_clause(&[lit])),
        }
    }

    /// Looks up one lexically scoped `let` binding by name.
    fn lookup_local_binding(&self, name: &str) -> Option<LocalBinding> {
        self.let_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    /// Pushes one new lexical binding scope for nested `let` lowering.
    fn push_let_scope(&mut self, scope: HashMap<Box<str>, LocalBinding>) {
        self.let_scopes.push(scope);
    }

    /// Pops the most recent lexical binding scope.
    fn pop_let_scope(&mut self) {
        self.let_scopes.pop().expect("let scope stack underflow");
    }

    /// Evaluates one `let` binding list in the outer scope, then lowers `body`
    /// inside a newly pushed lexical scope.
    fn with_let_bindings<T>(
        &mut self,
        bindings: &[SExpr],
        body: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let mut scope = HashMap::with_capacity(bindings.len());
        for binding in bindings {
            let SExpr::List(items) = binding else {
                return Err("let binding must be a pair".to_owned());
            };
            let [SExpr::Atom(name), value] = items.as_slice() else {
                return Err("let binding must be `(name value)`".to_owned());
            };
            let binding_value = if self.is_boolean_expr(value)? {
                LocalBinding::Bool(self.lower_formula(value)?)
            } else {
                let term = self.lower_term(value)?;
                LocalBinding::Term {
                    term,
                    sort: self.term_sort(term)?,
                }
            };
            scope.insert(name.clone(), binding_value);
        }
        self.push_let_scope(scope);
        let result = body(self);
        self.pop_let_scope();
        result
    }

    /// Lowers one formula-position expression into a Boolean view.
    fn lower_formula(&mut self, expr: &SExpr) -> Result<BoolView, String> {
        match expr {
            SExpr::Atom(atom) if atom.as_ref() == "true" => Ok(BoolView::True),
            SExpr::Atom(atom) if atom.as_ref() == "false" => Ok(BoolView::False),
            SExpr::Atom(atom) => match self.lookup_local_binding(atom) {
                Some(LocalBinding::Bool(view)) => Ok(view),
                Some(LocalBinding::Term { term, sort }) => {
                    if sort != self.bool_sort() {
                        return Err("non-Boolean term used as formula".to_owned());
                    }
                    Ok(BoolView::Lit(self.bool_term_literal(term)))
                }
                None => {
                    let term = self.lower_term(expr)?;
                    let bool_sort = self.bool_sort();
                    if self.term_sort(term)? != bool_sort {
                        return Err("non-Boolean term used as formula".to_owned());
                    }
                    Ok(BoolView::Lit(self.bool_term_literal(term)))
                }
            },
            SExpr::List(items) => {
                if let Some(SExpr::Atom(head)) = items.first() {
                    match head.as_ref() {
                        "let" => {
                            let [_, SExpr::List(bindings), body] = items.as_slice() else {
                                return Err("malformed let".to_owned());
                            };
                            return self
                                .with_let_bindings(bindings, |this| this.lower_formula(body));
                        }
                        "ite" => {
                            let [_, cond, then_branch, else_branch] = items.as_slice() else {
                                return Err("`ite` expects exactly three arguments".to_owned());
                            };
                            return self.lower_bool_ite(cond, then_branch, else_branch);
                        }
                        _ => {}
                    }
                }

                if let Some(view) = self.try_lower_connective(expr)? {
                    return Ok(view);
                }

                if let Some(SExpr::Atom(head)) = items.first()
                    && head.as_ref() == "="
                {
                    return self.lower_equality_formula(&items[1..]);
                }

                let term = self.lower_term(expr)?;
                let bool_sort = self.bool_sort();
                if self.term_sort(term)? != bool_sort {
                    return Err("non-Boolean term used as formula".to_owned());
                }
                Ok(BoolView::Lit(self.bool_term_literal(term)))
            }
        }
    }

    /// Attempts to lower one built-in Boolean connective.
    fn try_lower_connective(&mut self, expr: &SExpr) -> Result<Option<BoolView>, String> {
        let SExpr::List(items) = expr else {
            return Ok(None);
        };
        let Some(SExpr::Atom(head)) = items.first() else {
            return Ok(None);
        };

        let args = &items[1..];
        match head.as_ref() {
            "not" => {
                let [arg] = args else {
                    return Err("`not` expects exactly one argument".to_owned());
                };
                Ok(Some(negate_view(self.lower_formula(arg)?)))
            }
            "and" => Ok(Some(self.lower_nary_and(args)?)),
            "or" => Ok(Some(self.lower_nary_or(args)?)),
            "distinct" => Ok(Some(self.lower_distinct_formula(args)?)),
            "=>" => {
                let [lhs, rhs] = args else {
                    return Err("`=>` expects exactly two arguments".to_owned());
                };
                let lhs = self.lower_formula(lhs)?;
                let rhs = self.lower_formula(rhs)?;
                Ok(Some(self.lower_or_from_views(&[negate_view(lhs), rhs])?))
            }
            "xor" => {
                let [lhs, rhs] = args else {
                    return Err("`xor` expects exactly two arguments".to_owned());
                };
                let lhs = self.lower_formula(lhs)?;
                let rhs = self.lower_formula(rhs)?;
                Ok(Some(self.lower_xor(lhs, rhs)?))
            }
            _ => Ok(None),
        }
    }

    /// Lowers one equality formula.
    fn lower_equality_formula(&mut self, args: &[SExpr]) -> Result<BoolView, String> {
        let [lhs, rhs] = args else {
            return Err("`=` expects exactly two arguments".to_owned());
        };
        if self.is_boolean_expr(lhs)? || self.is_boolean_expr(rhs)? {
            let lhs = self.lower_formula(lhs)?;
            let rhs = self.lower_formula(rhs)?;
            return self.lower_bool_equiv(lhs, rhs);
        }
        let lhs = self.lower_term(lhs)?;
        let rhs = self.lower_term(rhs)?;
        Ok(BoolView::Lit(self.equality_literal(lhs, rhs)))
    }

    /// Lowers one n-ary `distinct` formula by expanding to pairwise disequalities.
    fn lower_distinct_formula(&mut self, args: &[SExpr]) -> Result<BoolView, String> {
        if args.len() <= 1 {
            return Ok(BoolView::True);
        }

        let mut pairwise = Vec::new();
        for left_index in 0..args.len() {
            for right_index in left_index + 1..args.len() {
                let equal = self.lower_equality_formula(&[
                    args[left_index].clone(),
                    args[right_index].clone(),
                ])?;
                pairwise.push(negate_view(equal));
            }
        }
        self.lower_and_from_views(&pairwise)
    }

    /// Lowers one Boolean-valued `ite`.
    fn lower_bool_ite(
        &mut self,
        cond: &SExpr,
        then_branch: &SExpr,
        else_branch: &SExpr,
    ) -> Result<BoolView, String> {
        let cond = self.lower_formula(cond)?;
        let then_branch = self.lower_formula(then_branch)?;
        let else_branch = self.lower_formula(else_branch)?;
        match cond {
            BoolView::True => Ok(then_branch),
            BoolView::False => Ok(else_branch),
            _ if then_branch == else_branch => Ok(then_branch),
            _ => {
                let when_true = self.lower_and_from_views(&[cond, then_branch])?;
                let when_false = self.lower_and_from_views(&[negate_view(cond), else_branch])?;
                self.lower_or_from_views(&[when_true, when_false])
            }
        }
    }

    /// Returns whether `expr` is known to denote a Boolean expression.
    fn is_boolean_expr(&mut self, expr: &SExpr) -> Result<bool, String> {
        match expr {
            SExpr::Atom(atom) if atom.as_ref() == "true" || atom.as_ref() == "false" => Ok(true),
            SExpr::Atom(atom) => Ok(match self.lookup_local_binding(atom) {
                Some(LocalBinding::Bool(_)) => true,
                Some(LocalBinding::Term { sort, .. }) => sort == self.bool_sort(),
                None => false,
            }),
            SExpr::List(items)
                if matches!(
                    items.first(),
                    Some(SExpr::Atom(head))
                        if matches!(
                            head.as_ref(),
                            "not" | "and" | "or" | "=>" | "xor" | "=" | "distinct"
                        )
                ) =>
            {
                Ok(true)
            }
            SExpr::List(items) if matches!(items.first(), Some(SExpr::Atom(head)) if head.as_ref() == "let") =>
            {
                let [_, SExpr::List(bindings), body] = items.as_slice() else {
                    return Err("malformed let".to_owned());
                };
                self.with_let_bindings(bindings, |this| this.is_boolean_expr(body))
            }
            SExpr::List(items) if matches!(items.first(), Some(SExpr::Atom(head)) if head.as_ref() == "ite") =>
            {
                let [_, _, then_branch, else_branch] = items.as_slice() else {
                    return Err("`ite` expects exactly three arguments".to_owned());
                };
                Ok(self.is_boolean_expr(then_branch)? && self.is_boolean_expr(else_branch)?)
            }
            _ => {
                let term = self.lower_term(expr)?;
                let bool_sort = self.bool_sort();
                Ok(self.term_sort(term)? == bool_sort)
            }
        }
    }

    /// Lowers one term-position expression.
    fn lower_term(&mut self, expr: &SExpr) -> Result<TermId, String> {
        match expr {
            SExpr::Atom(atom) if atom.as_ref() == "true" => self.true_term(),
            SExpr::Atom(atom) if atom.as_ref() == "false" => self.false_term(),
            SExpr::Atom(atom) => {
                if let Some(binding) = self.lookup_local_binding(atom) {
                    return match binding {
                        LocalBinding::Bool(view) => self.bool_view_term(view),
                        LocalBinding::Term { term, .. } => Ok(term),
                    };
                }
                let decl = *self
                    .funs
                    .get(atom.as_ref())
                    .ok_or_else(|| format!("unknown symbol: {atom}"))?;
                if decl.arity != 0 {
                    return Err(format!("symbol `{atom}` expects {} arguments", decl.arity));
                }
                Ok(self.intern_term(TermRef::nullary(decl.symbol), decl.result_sort))
            }
            SExpr::List(items) => {
                if let Some(SExpr::Atom(head)) = items.first() {
                    match head.as_ref() {
                        "let" => {
                            let [_, SExpr::List(bindings), body] = items.as_slice() else {
                                return Err("malformed let".to_owned());
                            };
                            return self.with_let_bindings(bindings, |this| this.lower_term(body));
                        }
                        "ite" => {
                            let [_, cond, then_branch, else_branch] = items.as_slice() else {
                                return Err("`ite` expects exactly three arguments".to_owned());
                            };
                            return self.lower_term_ite(cond, then_branch, else_branch);
                        }
                        "not" | "and" | "or" | "=>" | "xor" | "=" | "distinct" => {
                            let view = self.lower_formula(expr)?;
                            return self.bool_view_term(view);
                        }
                        _ => {}
                    }
                }

                let Some(SExpr::Atom(head)) = items.first() else {
                    return Err("application head must be an atom".to_owned());
                };
                let decl = *self
                    .funs
                    .get(head.as_ref())
                    .ok_or_else(|| format!("unknown symbol: {head}"))?;
                let actual_arity = items.len() - 1;
                if actual_arity != decl.arity as usize {
                    return Err(format!(
                        "symbol `{head}` expects {} arguments, got {actual_arity}",
                        decl.arity
                    ));
                }
                let args = items[1..]
                    .iter()
                    .map(|arg| self.lower_term(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.intern_term(
                    TermRef {
                        fun: decl.symbol,
                        args: &args,
                    },
                    decl.result_sort,
                ))
            }
        }
    }

    /// Lowers one term-valued `ite`, introducing one fresh constant when the
    /// chosen branch depends on SAT.
    fn lower_term_ite(
        &mut self,
        cond: &SExpr,
        then_branch: &SExpr,
        else_branch: &SExpr,
    ) -> Result<TermId, String> {
        let cond = self.lower_formula(cond)?;
        let then_term = self.lower_term(then_branch)?;
        let else_term = self.lower_term(else_branch)?;
        let then_sort = self.term_sort(then_term)?;
        let else_sort = self.term_sort(else_term)?;
        if then_sort != else_sort {
            return Err("`ite` branches must have the same sort".to_owned());
        }

        match cond {
            BoolView::True => Ok(then_term),
            BoolView::False => Ok(else_term),
            _ if then_term == else_term => Ok(then_term),
            BoolView::Lit(cond_lit) => {
                let fresh_term = self.fresh_const_term(then_sort);
                let then_eq = self.equality_literal(fresh_term, then_term);
                let else_eq = self.equality_literal(fresh_term, else_term);
                accept_add_result(self.sat.add_clause(&[!cond_lit, then_eq]))?;
                accept_add_result(self.sat.add_clause(&[cond_lit, else_eq]))?;
                Ok(fresh_term)
            }
        }
    }

    /// Returns one SAT literal representing the equality atom `lhs = rhs`.
    fn equality_literal(&mut self, lhs: TermId, rhs: TermId) -> Lit {
        let key = if rhs < lhs { (rhs, lhs) } else { (lhs, rhs) };
        if let Some(&lit) = self.eq_lits.get(&key) {
            return lit;
        }
        let var = self.sat.new_var();
        let lit = Lit::new(var, false);
        let _ = self.euf.intern_equality_atom(key.0, key.1, var);
        self.eq_lits.insert(key, lit);
        lit
    }

    /// Returns one SAT literal representing the Boolean term `term = true`.
    fn bool_term_literal(&mut self, term: TermId) -> Lit {
        let true_term = self.true_term().expect("true term must be available");
        self.equality_literal(term, true_term)
    }

    /// Reifies one Boolean view into one Bool-sorted term.
    fn bool_view_term(&mut self, view: BoolView) -> Result<TermId, String> {
        match view {
            BoolView::True => self.true_term(),
            BoolView::False => self.false_term(),
            BoolView::Lit(lit) => {
                let bool_sort = self.bool_sort();
                let fresh = self.fresh_const_term(bool_sort);
                let true_term = self.true_term()?;
                let false_term = self.false_term()?;
                let true_eq = self.equality_literal(fresh, true_term);
                let false_eq = self.equality_literal(fresh, false_term);
                accept_add_result(self.sat.add_clause(&[!lit, true_eq]))?;
                accept_add_result(self.sat.add_clause(&[lit, false_eq]))?;
                Ok(fresh)
            }
        }
    }

    /// Interns one term without adding any extra Boolean-domain constraints.
    fn intern_term_unchecked(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        let term_id = self.euf.intern_term(term, sort);
        self.term_sorts.insert(term_id, sort);
        term_id
    }

    /// Interns one term and records its sort locally.
    fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        let term_id = self.intern_term_unchecked(term, sort);
        if Some(sort) == self.bool_sort
            && self.true_term != Some(term_id)
            && self.false_term != Some(term_id)
        {
            self.enforce_bool_term_domain(term_id);
        }
        term_id
    }

    /// Returns the sort of one previously interned term.
    fn term_sort(&self, term: TermId) -> Result<SortId, String> {
        self.term_sorts
            .get(&term)
            .copied()
            .ok_or_else(|| "driver lost track of term sort".to_owned())
    }

    /// Returns the canonical Boolean sort.
    fn bool_sort(&mut self) -> SortId {
        if let Some(sort) = self.bool_sort {
            return sort;
        }
        let sort = self.euf.intern_sort(SortRef::Bool);
        self.bool_sort = Some(sort);
        sort
    }

    /// Returns the canonical true term.
    fn true_term(&mut self) -> Result<TermId, String> {
        if let Some(term) = self.true_term {
            return Ok(term);
        }
        let bool_sort = self.bool_sort();
        let symbol = self.euf.intern_symbol(SymbolRef {
            name: "true",
            arg_sorts: &[],
            result_sort: bool_sort,
        });
        let term = self.intern_term_unchecked(TermRef::nullary(symbol), bool_sort);
        self.true_term = Some(term);
        self.ensure_bool_constants_distinct();
        Ok(term)
    }

    /// Returns the canonical false term.
    fn false_term(&mut self) -> Result<TermId, String> {
        if let Some(term) = self.false_term {
            return Ok(term);
        }
        let bool_sort = self.bool_sort();
        let symbol = self.euf.intern_symbol(SymbolRef {
            name: "false",
            arg_sorts: &[],
            result_sort: bool_sort,
        });
        let term = self.intern_term_unchecked(TermRef::nullary(symbol), bool_sort);
        self.false_term = Some(term);
        self.ensure_bool_constants_distinct();
        Ok(term)
    }

    /// Interns one fresh solver-internal constant term of the requested sort.
    fn fresh_const_term(&mut self, sort: SortId) -> TermId {
        let name = format!("|@qfuf.{}|", self.fresh_const_counter);
        self.fresh_const_counter += 1;
        let symbol = self.euf.intern_symbol(SymbolRef {
            name: &name,
            arg_sorts: &[],
            result_sort: sort,
        });
        self.intern_term(TermRef::nullary(symbol), sort)
    }

    /// Asserts the root disequality between the canonical Boolean constants.
    fn ensure_bool_constants_distinct(&mut self) {
        if self.bool_constants_separated {
            return;
        }
        let Some(true_term) = self.true_term else {
            return;
        };
        let Some(false_term) = self.false_term else {
            return;
        };
        let eq_lit = self.equality_literal(true_term, false_term);
        let _ = accept_add_result(self.sat.add_clause(&[!eq_lit]));
        self.bool_constants_separated = true;
    }

    /// Adds the two-valued Boolean-domain clauses for one Bool-sorted term.
    fn enforce_bool_term_domain(&mut self, term: TermId) {
        if !self.bool_terms_constrained.insert(term) {
            return;
        }
        self.ensure_bool_constants_distinct();
        let true_lit = self.bool_term_literal(term);
        let false_term = self.false_term().expect("false term must be available");
        let false_lit = self.equality_literal(term, false_term);
        let _ = accept_add_result(self.sat.add_clause(&[true_lit, false_lit]));
        let _ = accept_add_result(self.sat.add_clause(&[!true_lit, !false_lit]));
    }

    /// Lowers one n-ary conjunction.
    fn lower_nary_and(&mut self, args: &[SExpr]) -> Result<BoolView, String> {
        let mut views = Vec::with_capacity(args.len());
        for arg in args {
            views.push(self.lower_formula(arg)?);
        }
        if views.is_empty() {
            return Ok(BoolView::True);
        }
        self.lower_and_from_views(&views)
    }

    /// Lowers one conjunction from already lowered Boolean views.
    fn lower_and_from_views(&mut self, views: &[BoolView]) -> Result<BoolView, String> {
        let mut filtered = Vec::with_capacity(views.len());
        for &view in views {
            if view == BoolView::False {
                return Ok(BoolView::False);
            }
            if view != BoolView::True {
                filtered.push(view);
            }
        }
        if filtered.is_empty() {
            return Ok(BoolView::True);
        }
        if filtered.len() == 1 {
            return Ok(filtered[0]);
        }
        let lit = self.new_tseitin_lit();
        for &view in &filtered {
            if let BoolView::Lit(arg_lit) = view {
                accept_add_result(self.sat.add_clause(&[!lit, arg_lit]))?;
            }
        }
        let mut support = Vec::with_capacity(filtered.len() + 1);
        support.push(lit);
        for &view in &filtered {
            if let BoolView::Lit(arg_lit) = view {
                support.push(!arg_lit);
            }
        }
        accept_add_result(self.sat.add_clause(&support))?;
        Ok(BoolView::Lit(lit))
    }

    /// Lowers one n-ary disjunction.
    fn lower_nary_or(&mut self, args: &[SExpr]) -> Result<BoolView, String> {
        let mut views = Vec::with_capacity(args.len());
        for arg in args {
            views.push(self.lower_formula(arg)?);
        }
        if views.is_empty() {
            return Ok(BoolView::False);
        }
        self.lower_or_from_views(&views)
    }

    /// Lowers one disjunction from already lowered Boolean views.
    fn lower_or_from_views(&mut self, views: &[BoolView]) -> Result<BoolView, String> {
        let mut filtered = Vec::with_capacity(views.len());
        for &view in views {
            if view == BoolView::True {
                return Ok(BoolView::True);
            }
            if view != BoolView::False {
                filtered.push(view);
            }
        }
        if filtered.is_empty() {
            return Ok(BoolView::False);
        }
        if filtered.len() == 1 {
            return Ok(filtered[0]);
        }
        let lit = self.new_tseitin_lit();
        for &view in &filtered {
            if let BoolView::Lit(arg_lit) = view {
                accept_add_result(self.sat.add_clause(&[lit, !arg_lit]))?;
            }
        }
        let mut support = Vec::with_capacity(filtered.len() + 1);
        support.push(!lit);
        for &view in &filtered {
            if let BoolView::Lit(arg_lit) = view {
                support.push(arg_lit);
            }
        }
        accept_add_result(self.sat.add_clause(&support))?;
        Ok(BoolView::Lit(lit))
    }

    /// Lowers Boolean equivalence.
    fn lower_bool_equiv(&mut self, lhs: BoolView, rhs: BoolView) -> Result<BoolView, String> {
        self.lower_xor(lhs, rhs).map(negate_view)
    }

    /// Lowers Boolean xor.
    fn lower_xor(&mut self, lhs: BoolView, rhs: BoolView) -> Result<BoolView, String> {
        match (lhs, rhs) {
            (BoolView::True, view) | (view, BoolView::True) => Ok(negate_view(view)),
            (BoolView::False, view) | (view, BoolView::False) => Ok(view),
            (BoolView::Lit(lhs), BoolView::Lit(rhs)) => {
                let lit = self.new_tseitin_lit();
                accept_add_result(self.sat.add_clause(&[!lhs, !rhs, !lit]))?;
                accept_add_result(self.sat.add_clause(&[lhs, rhs, !lit]))?;
                accept_add_result(self.sat.add_clause(&[lhs, !rhs, lit]))?;
                accept_add_result(self.sat.add_clause(&[!lhs, rhs, lit]))?;
                Ok(BoolView::Lit(lit))
            }
        }
    }

    /// Allocates one fresh Tseitin literal.
    fn new_tseitin_lit(&mut self) -> Lit {
        Lit::new(self.sat.new_var(), false)
    }
}

/// Parses a complete SMT-LIB input string into commands.
fn parse_commands(input: &str) -> Result<Vec<Command>, String> {
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
                }
                tokens.push(ch.to_string().into_boxed_str());
            }
            ch if ch.is_whitespace() => {
                if !current.is_empty() {
                    tokens.push(current.clone().into_boxed_str());
                    current.clear();
                }
            }
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        tokens.push(current.into_boxed_str());
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

/// Accepts one clause-insertion result from the SAT core.
fn accept_add_result(result: AddClauseResult) -> Result<(), String> {
    match result {
        AddClauseResult::Added | AddClauseResult::Satisfied => Ok(()),
        AddClauseResult::Inconsistent => Ok(()),
    }
}

/// Negates one lowered Boolean view.
fn negate_view(view: BoolView) -> BoolView {
    match view {
        BoolView::True => BoolView::False,
        BoolView::False => BoolView::True,
        BoolView::Lit(lit) => BoolView::Lit(!lit),
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
