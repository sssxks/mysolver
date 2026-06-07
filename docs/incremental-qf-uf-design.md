# Incremental QF-UF Solver Design

## Context

This repository currently has three disconnected pieces:

- `sat` is a single-shot CDCL solver over a persistent CNF database.
- `euf` is a prototype that mixes Boolean reasoning and equality reasoning inside one crate.
- `sat-harness` assumes one input file produces one final outcome.

That shape is sufficient for DIMACS SAT, but it is not the right shape for incremental SMT over QF-UF. The target benchmark family is the SMT-LIB 2025 incremental release, where one benchmark file is a command trace containing multiple `check-sat` calls, typically separated by `push 1` and `pop 1`, and each `check-sat` has its own expected status. The SMT-LIB benchmark-submission repository states that incremental benchmarks have more than one `check-sat`, and that each `check-sat` should have a corresponding `set-info :status` immediately above it. SMT-COMP 2025 further states that the incremental track is executed as an online interaction over stdin/stdout, with the benchmark trace fed command by command. Sources:

- SMT-LIB benchmark submission rules: <https://github.com/SMT-LIB/benchmark-submission>
- SMT-COMP 2025 rules: <https://smt-comp.github.io/2025/rules.pdf>
- SMT-LIB 2025 incremental benchmark release: <https://zenodo.org/records/15493096>

The design below follows the same coarse layering used by `cvc5`:

- an SMT command driver at the top,
- a propositional engine in the middle,
- one or more theory solvers underneath,
- strict separation between incremental scopes and SAT search backtracking.

## Baseline Constraints In This Repository

### `sat`

The current `sat::Solver` owns the whole search loop internally. It can:

- create variables,
- add clauses permanently,
- run `solve()`,
- keep learned clauses across the run.

It cannot currently represent:

- scoped `push` and `pop`,
- solving under assumptions,
- callbacks into a theory solver,
- repeated `check-sat` with preserved clause database but fresh search state.

### `euf`

The current `euf` crate is not yet a theory module. It is a self-contained experiment with:

- its own Boolean variable type,
- its own clause database,
- its own unit propagation path.

That is the opposite of what a DPLL(T) architecture needs. In the target architecture, EUF must stop being “a solver that happens to know equality” and become “a theory engine that consumes Boolean assignments from SAT and returns explained theory consequences”.

### `sat-harness`

The current harness data model assumes:

- one discovered file,
- one solver run,
- one final outcome category,
- optionally one oracle answer for the whole file.

That assumption is incompatible with incremental SMT-LIB traces, where:

- one file contains multiple queries,
- each query has its own expected answer,
- comparison needs to reason about per-query outcome sequences, not just one case-level category.

## Recommended Top-Level Architecture

The recommended architecture is four layers.

### Layer 1: SMT-LIB Driver

Responsibility:

- parse incremental SMT-LIB commands,
- maintain the assertion stack,
- lower Boolean structure into SAT,
- register theory atoms with EUF,
- call `check_sat` repeatedly,
- print SMT-LIB-compliant responses.

This layer should be a separate crate or binary-oriented module, not stuffed into `sat` or `euf`. A good end state is a new top-level solver crate, for example `crates/qfuf` or `crates/smt`, that depends on `sat` and `euf`.

### Layer 2: SAT Engine

Responsibility:

- own CNF variables and clauses,
- do CDCL,
- support incremental assertion frames,
- notify registered theories about relevant assignments,
- absorb theory-generated explanation clauses.

This layer should remain theory-agnostic. It should know that a theory exists, but it should not know anything specific about EUF terms, congruence, or e-graphs.

### Layer 3: EUF Theory Engine

Responsibility:

- own the term DAG, atom registry, and equality engine,
- receive SAT assignments to theory atoms,
- maintain congruence closure under current SAT search assumptions,
- detect theory conflicts,
- derive theory propagations,
- explain every conflict and propagation as a clause over SAT literals.

### Layer 4: Benchmark Harness

Responsibility:

- discover SMT benchmark files,
- execute the solver as an interactive subprocess,
- feed the command trace incrementally,
- collect per-query outputs,
- summarize case-level and run-level results.

This layer should not call internal Rust APIs directly for the incremental benchmark path. The benchmark itself is defined as an interaction protocol, so the harness should exercise the actual solver boundary: stdin/stdout.

## The Most Important Separation: Two Different Kinds Of Backtracking

This is the part most likely to go wrong if the design stays implicit.

There are two unrelated notions of “scope”:

1. SMT assertion scopes.
   These come from SMT-LIB `assert`, `push`, and `pop`. They must survive across multiple `check-sat` calls until popped by the caller.
2. SAT search scopes.
   These come from CDCL decision levels during one `check-sat`. They are temporary and must be discarded at the end of the search.

These two scopes must not be represented by the same stack.

`cvc5` solves this by separating assertion-stack context from SAT context. This repository should do the same conceptually, even if the Rust implementation is lighter-weight.

## SAT Incrementality Design

### Choice

For SMT-LIB incrementality, prefer **native SAT `push` and `pop`** over encoding scope frames with activation literals.

Keep a separate **assumptions API** as well, but use it for transient per-check assumptions such as future `check-sat-assuming`, not as the primary encoding of the SMT-LIB assertion stack.

### Why Native `push`/`pop`

Activation literals are easy to prototype and fit IPASIR-style APIs well, but they add overhead to every incremental query. For a workload dominated by many `push/assert/check-sat/pop` cycles, that overhead is a real performance concern. The cvc5 experience with its newer CDCL(T) backends reflects that tradeoff; their older incremental MiniSat integration instead used native scoped clauses and variables.

Native `push`/`pop` means the SAT engine itself becomes responsible for:

- tracking the current scope,
- removing clauses and variables that leave scope on `pop`,
- preserving only those learned facts that remain valid below the new scope.

This is more implementation work inside `sat`, but it avoids baking scope-frame control literals into every scoped clause.

### Core Consequence

Once native `push`/`pop` is chosen, the most important SAT-design question is no longer “how do we encode frames?”, but instead:

- how clause scope is represented,
- how `pop` removes out-of-scope clauses and assignments,
- how learned clause scope is computed during conflict analysis.

### SAT Public API Shape

The `sat` crate should expose an incremental API roughly shaped like this:

- `new_var() -> Var`
- `add_clause(&[Lit]) -> AddClauseResult`
- `push()`
- `pop(n: usize)`
- `current_scope() -> Scope`
- `add_scoped_clause(&[Lit]) -> AddClauseResult`
- `solve_with_assumptions(&[Lit], theory: &mut impl Theory) -> SatResult`
- `reset_search()`

The important semantic split is:

- scope is native solver state,
- assumptions are transient per-check state,
- some clauses and variables may be removed on `pop`,
- the search trail is per-check,
- CDCL decision levels remain strictly separate from scopes.

### SAT Internal State

Persistent state:

- variable table,
- clause arena,
- watch lists,
- variable activities,
- learned clauses,
- scope frame stack,
- per-frame variable and clause boundaries or equivalent rollback metadata.

Per-check search state:

- assignments,
- assignment levels,
- reason table,
- trail,
- propagation head,
- temporary analysis buffers,
- theory notification cursor.

The current solver already has most of the per-check state. The design change is that this state becomes explicitly resettable between `check-sat` calls, while clauses and heuristics remain persistent.

### Scope Metadata

Following the old cvc5 MiniSat integration, scope should be represented on the objects that survive across `check-sat` calls:

- long clauses carry a `clause.level`,
- variables carry at least an `variable_scope`,
- assigned variables should also record the `assignment_scope` of their current assignment,
- learned clauses carry the maximum scope dependency discovered by conflict analysis.

This metadata is what makes native `pop` sound.

### Inline Binary Clauses

The current `sat` crate stores binary clauses inline in the watchlists instead of allocating them in the long-clause arena. That is acceptable for the current design target, but only if scope metadata is carried on the inline binary representation as well.

The minimum sound design is:

- `Watcher::Binary` carries `other: Lit` and `scope`,
- `Reason::Binary` carries the same `scope`,
- `pop()` removes inline binary watchers whose `scope` is above the new current scope,
- `analyze()` incorporates the binary reason's `scope` when computing the learned clause scope.

No binary-clause identity is required for soundness under this plan. The tradeoff is simply that `pop()` must scan the watchlists and filter stale inline binary entries. This is acceptable because `pop()` is low-frequency compared with Boolean propagation.

### Variable Lifetime On `pop`

`pop()` must not only remove stale clauses; it must also ensure that variables introduced in higher scope frames cannot participate in later searches.

The recommended and default strategy is:

- record `vars_base` when each scope frame is pushed,
- on `pop`, shrink the variable arrays back to the restored frame boundary.

This avoids reusing `variable_scope` as a proxy for variable liveness across unrelated frames of the same depth. In particular, it avoids the ambiguity in sequences such as `push(); ...; pop(); push();`, where the second push returns to the same depth but must not make variables from the first frame visible again.

Under this design:

- `variable_scope` is used for clause-scope computation,
- variable liveness is determined by array membership after shrink,
- popped variables simply stop existing in the SAT core.

### `variable_scope` vs `assignment_scope`

The two fields serve different purposes and should not be conflated.

- `variable_scope`
  - the scope where a SAT variable was created,
  - immutable after allocation,
  - used for clause-scope computation.
- `assignment_scope`
  - the scope where the variable's current assignment was produced,
  - changes as the solver backtracks and re-propagates,
  - used to decide which trail assignments must be removed on `pop()`.

Example:

1. `push()` to level 1.
2. Create variable `t`.
3. `push()` to level 2.
4. First propagate `t = true`.

At that point:

- `variable_scope(t) = 1`
- `assignment_scope(t) = 2`

The variable exists because it was introduced at level 1, but its current assignment must still be removed when popping from level 2 back to level 1.

Under the recommended shrink-on-pop design:

- `variable_scope` does not decide whether a variable is still alive,
- variable liveness comes from shrinking the arrays back to `vars_base`,
- `variable_scope` remains useful because theory clauses and learned clauses must still know how deep their referenced variables were introduced.

### SAT  Sketch

The following pseudocode is the recommended direction for the current `sat` crate. It is intentionally close to the existing code layout in `crates/sat/src/solver`.

```rust
/// SMT assertion-stack scope created by SMT-LIB `push` / `pop`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Default)]
pub struct Scope(u32);

impl Scope {
    pub const ROOT: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

/// Why one variable currently has its assignment.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Reason {
    /// Decision or top-level unit without a stored antecedent.
    None,
    /// Inline binary clause.
    Binary {
        /// The literal that was false when this reason fired.
        false_lit: Lit,
        /// The propagated literal.
        other: Lit,
        /// Scope in which this binary clause exists.
        scope: Scope,
    },
    /// Long clause stored in the clause arena.
    Clause(ClauseId),
}

/// One pushed assertion-stack scope frame.
#[derive(Clone, Debug)]
pub(crate) struct ScopeFrame {
    /// Scope represented by this frame.
    scope: Scope,
    /// Number of variables allocated before the frame was pushed.
    vars_base: usize,
}

/// A watched-literal entry.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Watcher {
    Binary {
        other: Lit,
        scope: Scope,
    },
    Long {
        clause: ClauseId,
        blocker: Lit,
    },
}

/// A conflict discovered during propagation.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Conflict {
    Binary {
        false_lit: Lit,
        other: Lit,
        scope: Scope,
    },
    Clause(ClauseId),
}

/// One theory clause waiting to be inserted into SAT.
#[derive(Clone, Debug)]
pub struct TheoryClause {
    /// Fully explained clause over SAT literals.
    lits: Box<[Lit]>,
    /// Scope where this clause must remain valid.
    scope: Scope,
    /// Classification used only for metrics and debugging.
    kind: TheoryClauseKind,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TheoryClauseKind {
    Input,
    Lemma,
    PropagationExplanation,
    ConflictExplanation,
}

/// Incremental SAT solver state.
#[derive(Debug)]
pub struct Solver {
    /// The shallowest scope currently known to be immediately inconsistent.
    inconsistent_scope: Option<Scope>,

    /// Current assertion-stack scope.
    current_scope: Scope,
    /// Stack of pushed scope frames above root.
    scope_frames: Vec<ScopeFrame>,

    /// Number of variables currently allocated and in scope.
    nvars: usize,
    /// Current truth value for each variable.
    assigns: Vec<TruthValue>,
    /// CDCL decision level of each current assignment.
    sat_level: Vec<usize>,
    /// Scope of each current assignment.
    assignment_scope: Vec<Scope>,
    /// Antecedent reason for each current assignment.
    reason: Vec<Reason>,
    /// Scope where each variable was introduced.
    variable_scope: Vec<Scope>,

    /// CDCL trail.
    trail: Vec<Lit>,
    /// Start index of each CDCL decision level.
    trail_lim: Vec<usize>,
    /// Boolean propagation cursor.
    qhead: usize,

    /// Watch lists indexed by packed literal.
    watches: Vec<Vec<Watcher>>,

    /// Long learned clauses that are still live.
    learnts: Vec<ClauseId>,
    /// Long clause arena. Long clauses must carry their own scope.
    clauses: ClauseArena,

    /// VSIDS data and branching heap.
    var_activity: Vec<f64>,
    var_inc: f64,
    var_decay: f64,
    order: VarHeap,

    /// Long-clause activity data.
    clause_inc: f32,
    clause_decay: f32,

    /// Conflict-analysis scratch state.
    seen: Vec<bool>,
    analyze_stack: Vec<Var>,
    minimize_cache: Vec<u8>,
    minimize_touched: Vec<Var>,
    lbd_levels: Vec<u32>,
    lbd_epoch: u32,
}
```

The current `ClauseArena` should be extended conceptually so that each long clause header carries:

```rust
pub(crate) struct ClauseHeader {
    len: u32,
    learnt: bool,
    activity: f32,
    lbd: u32,
    scope: Scope,
    deleted: bool,
}
```

Only the additional `scope` field is required by native `push`/`pop`. The other fields already exist today in some form.

### SAT API Sketch

The recommended public and internal APIs are:

```rust
impl Solver {
    pub fn new() -> Self;
    pub fn new_var(&mut self) -> Var;

    pub fn push(&mut self);
    pub fn pop(&mut self, n: usize) -> Result<(), PopError>;
    pub fn current_scope(&self) -> Scope;

    pub fn add_clause(&mut self, lits: &[Lit]) -> bool;
    pub fn solve(&mut self) -> SatResult;
    pub fn solve_with_assumptions<T: Theory>(
        &mut self,
        assumptions: &[Lit],
        theory: &mut T,
    ) -> SatResult;

    pub(crate) fn add_scoped_clause(
        &mut self,
        lits: &[Lit],
        scope: Scope,
        origin: ClauseOrigin,
    ) -> AddClauseResult;

    pub(crate) fn pop_to_scope(
        &mut self,
        new_scope: Scope,
    ) -> Result<(), PopError>;

    pub(crate) fn reset_search(&mut self);
}
```

And the clause origin classification:

```rust
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum ClauseOrigin {
    Input,
    Theory,
    Learnt,
}
```

### Core Invariants

The SAT core should maintain these invariants at all times:

```rust
/// Every assigned variable has a scoped assignment that is still in scope.
assert!(solver.assigns[v.index()] == TruthValue::Unassigned
    || solver.assignment_scope[v.index()] <= solver.current_scope);

/// Every allocated variable was introduced in a frame that still exists.
assert!(solver.variable_scope[v.index()] <= solver.current_scope);

/// Every inline binary watcher still present in a watchlist is in scope.
assert!(matches!(watcher, Watcher::Binary { scope, .. } if scope <= solver.current_scope));

/// Every live long clause still present in the clause arena is in scope.
assert!(solver.clauses.header(cid).scope <= solver.current_scope);

/// Every reason references an antecedent that is still valid at the current scope.
assert!(match solver.reason[v.index()] {
    Reason::None => true,
    Reason::Binary { scope, .. } => scope <= solver.current_scope,
    Reason::Clause(cid) => solver.clauses.header(cid).scope <= solver.current_scope,
});
```

The exact `assert!` syntax above is only schematic. The important part is the invariant itself.

### `push()` Sketch

```rust
impl Solver {
    pub fn push(&mut self) {
        debug_assert_eq!(self.decision_level(), 0);

        let new_scope = self.current_scope.next();
        self.scope_frames.push(ScopeFrame {
            scope: new_scope,
            vars_base: self.nvars,
        });
        self.current_scope = new_scope;
    }
}
```

### `pop()` Sketch

```rust
impl Solver {
    pub fn pop(&mut self, n: usize) -> Result<(), PopError> {
        let target_depth = self
            .current_scope
            .index()
            .checked_sub(n)
            .ok_or(PopError::Underflow)?;
        self.pop_to_scope(Scope(target_depth as u32))
    }

    pub(crate) fn pop_to_scope(
        &mut self,
        new_scope: Scope,
    ) -> Result<(), PopError> {
        debug_assert_eq!(self.decision_level(), 0);
        debug_assert!(new_scope <= self.current_scope);

        self.current_scope = new_scope;

        // 1. Drop scope-frame records.
        while self
            .scope_frames
            .last()
            .is_some_and(|frame| frame.scope > new_scope)
        {
            self.scope_frames.pop();
        }

        // 2. Unassign variables whose current assignment was made above new_scope.
        while self
            .trail
            .last()
            .is_some_and(|&lit| self.assignment_scope[lit.var().index()] > new_scope)
        {
            let lit = self.trail.pop().unwrap();
            let vi = lit.var().index();
            self.assigns[vi] = TruthValue::Unassigned;
            self.sat_level[vi] = 0;
            self.assignment_scope[vi] = Scope::ROOT;
            self.reason[vi] = Reason::None;
        }
        self.qhead = self.trail.len();

        // 3. Delete long clauses whose scope is deeper than the restored scope.
        self.delete_long_clauses_above_scope(new_scope);

        // 4. Remove stale watchers by scanning each watchlist.
        for watchers in &mut self.watches {
            watchers.retain(|watcher| match watcher {
                Watcher::Binary { scope, .. } => *scope <= new_scope,
                Watcher::Long { clause, .. } => {
                    self.clauses.is_live(*clause)
                        && self.clauses.header(*clause).scope <= new_scope
                }
            });
        }

        // 5. Shrink variables back to the restored frame boundary.
        self.shrink_vars_to_frame_boundary(new_scope);

        Ok(())
    }
}
```

The above pseudocode assumes eager watchlist cleanup. That is recommended for inline binary clauses because it keeps later propagation code simple. For long clauses, deletion must happen before watchlist filtering so that the retain pass sees the final `is_live()` state of each clause.

### Clause Attachment Sketch

```rust
impl Solver {
    fn attach_binary(
        &mut self,
        a: Lit,
        b: Lit,
        scope: Scope,
    ) {
        self.watches[a.index()].push(Watcher::Binary {
            other: b,
            scope,
        });
        self.watches[b.index()].push(Watcher::Binary {
            other: a,
            scope,
        });
    }

    fn attach_irredundant_long(
        &mut self,
        lits: &[Lit],
        scope: Scope,
    ) -> ClauseId {
        let cid = self.clauses.alloc_irredundant(lits, scope);
        let w0 = lits[0];
        let w1 = lits[1];
        self.watches[w0.index()].push(Watcher::Long {
            clause: cid,
            blocker: w1,
        });
        self.watches[w1.index()].push(Watcher::Long {
            clause: cid,
            blocker: w0,
        });
        cid
    }

    fn attach_learnt_long(
        &mut self,
        lits: &[Lit],
        lbd: u32,
        scope: Scope,
    ) -> ClauseId {
        let cid = self.clauses.alloc_learnt(lits, self.clause_inc, lbd, scope);
        // Watch attachment same as above.
        cid
    }
}
```

### Clause-Level Computation Sketch

The solver should compute scopes as follows:

```rust
impl Solver {
    fn input_clause_scope(&self, lits: &[Lit]) -> Scope {
        lits.iter()
            .map(|lit| self.variable_scope[lit.var().index()])
            .max()
            .unwrap_or(self.current_scope)
            .max(self.current_scope)
    }

    fn explanation_scope(&self, lits: &[Lit]) -> Scope {
        lits.iter()
            .map(|lit| self.variable_scope[lit.var().index()])
            .max()
            .unwrap_or(Scope::ROOT)
    }
}
```

The rule is:

- input clauses are scoped to the current scope and any deeper `variable_scope` they mention,
- in the recommended shrink-on-pop design, such deeper `variable_scope`s can only come from variables introduced in the current frame,
- theory explanation clauses are scoped to the maximum `variable_scope` of their explanation literals,
- learned clauses are scoped to the maximum scope seen among the reasons used by conflict analysis.

### Conflict-Analysis Sketch

The analysis return type should be extended so that learned clauses carry both SAT and scope backtracking information:

```rust
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct AnalyzeSummary {
    /// CDCL backtrack level before asserting the learned clause.
    backtrack_level: usize,
    /// Scope required for the learned clause to remain sound.
    scope: Scope,
    /// Number of distinct CDCL levels in the learned clause.
    lbd: u32,
}
```

Then `analyze()` conceptually becomes:

```rust
impl Solver {
    pub(crate) fn analyze(
        &mut self,
        conflict: Conflict,
        learnt: &mut Vec<Lit>,
    ) -> AnalyzeSummary {
        let mut required_scope = Scope::ROOT;

        // Existing first-UIP traversal remains in place.
        // The additional work is:
        // - if resolving a long clause reason, update with clause.scope
        // - if resolving a binary reason, update with reason.scope
        // - if a literal from level 0 remains relevant, update with its scope provenance

        AnalyzeSummary {
            backtrack_level,
            scope: required_scope,
            lbd,
        }
    }
}
```

The exact implementation can continue to follow the current first-UIP code. The important structural change is that scope dependency is computed in parallel with ordinary CDCL analysis.

### Theory Trait Sketch

The SAT/theory boundary should expose scope-aware theory clauses:

```rust
pub trait Theory {
    fn notify_search_start(&mut self);
    fn notify_new_decision_level(&mut self);
    fn notify_assignment(&mut self, lit: Lit);
    fn notify_backtrack(&mut self, level: usize);
    fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>);
    fn final_check(&mut self, out: &mut Vec<TheoryClause>);
    fn has_pending_work(&self) -> bool;
}
```

And SAT should ingest them through:

```rust
impl Solver {
    fn add_theory_clause(&mut self, clause: TheoryClause) -> AddClauseResult {
        self.add_scoped_clause(&clause.lits, clause.scope, ClauseOrigin::Theory)
    }
}
```

This keeps all scope computation inside SAT, while requiring the theory to provide enough provenance to compute a correct clause level.

## SAT/Theory Integration Design

### Choice

Theory consequences should be communicated to SAT as **explained clauses**, not as direct mutations of SAT reason state.

### Why Clause-Based Integration

This keeps the SAT core simple.

If EUF directly enqueues literals inside SAT, then SAT conflict analysis must understand “theory reasons” as a separate kind of antecedent. That is workable, but it spreads theory-specific logic into the CDCL internals.

Clause-based integration is cleaner:

- EUF observes the current assignment,
- EUF derives a theory lemma or propagation explanation,
- EUF returns a clause over existing SAT literals,
- SAT inserts that clause and continues with ordinary BCP and ordinary conflict analysis.

This mirrors the `prop engine` plus `theory output channel` structure in `cvc5`.

### Theory Trait

The SAT crate should depend only on a small trait, conceptually like:

- `notify_search_start()`
- `notify_new_decision_level()`
- `notify_assignment(lit: Lit)`
- `notify_backtrack(level: usize)`
- `drain_clauses(out: &mut Vec<TheoryClause>)`
- `final_check(out: &mut Vec<TheoryClause>)`
- `has_pending_work() -> bool`

Where `TheoryClause` is:

- a clause over SAT literals,
- optionally tagged as `input`, `lemma`, or `propagation-explanation` for metrics only.

SAT responsibilities:

- maintain a mapping from SAT literals to “is this a theory atom?”,
- call `notify_new_decision_level()` exactly when CDCL enters a new decision level,
- notify the theory only for literals that correspond to theory atoms,
- call `notify_backtrack(level)` after backtracking to SAT decision level `level`,
- add theory clauses through the same clause-ingestion path used by learned clauses,
- assign each theory clause a sound scope.

Theory responsibilities:

- every returned clause must already be fully explained in SAT literals,
- every propagated theory fact must have a clause that becomes unit under the current assignment,
- every conflict must have a clause falsified under the current assignment.

For native `push`/`pop`, the theory boundary must preserve enough provenance for SAT to assign a scope to every returned clause. In practice, the scope should be the maximum `variable_scope` of the literals appearing in the explanation.

## EUF Design

The `euf` crate should be split mentally into three subcomponents.

1. Permanent Term And Atom Registry

This part survives across all `check-sat` calls.

2. Search-Local Equality Engine

This part is reset at the beginning of each `check-sat` and backtracks with SAT decision levels during the search.

3. Explanation Engine

This is the part that turns “theory knows something” into “SAT gets a clause”.

## Theory Atom Modeling

For QF-UF, the theory should register only atoms that SAT can mention in clauses.

Recommended atom normalization:

- equality atom: `Eq(TermId, TermId)` with sorted endpoints for commutativity,
- Boolean term atom: `Eq(term_bool, term_true)`.

Recommended atom-to-SAT mapping:

- `theory_atom_to_var: Vec<Var>`
- `var_to_theory_atom: Vec<Option<TheoryAtomId>>`

This mapping belongs at the SAT/theory boundary, not inside the pure term registry.

Recommended atom-trigger discipline:

- each canonical equality atom is permanently indexed by both endpoint terms,
- class merges do **not** scan all atoms,
- instead, when a class changes, EUF revisits only atoms attached to terms in the affected classes,
- if an atom becomes true, false, or unit-propagating under the current equality state, EUF emits the corresponding explained clause.

This is the same high-level direction as cvc5's equality-trigger mechanism: class merges drive trigger firing. The recommended first implementation below uses permanent term-to-atom incidence lists plus a search-local affected-atom queue, which is simpler to integrate with the current Rust design than cvc5's internal trigger chains while preserving the same merge-triggered behavior.

### EUF Code Sketch

The following pseudocode is the recommended direction for `crates/euf`. It deliberately separates:

- permanent solver-lifetime registries,
- per-`check-sat` search state,
- explanation data needed to return clauses to SAT.

```rust
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct SortId(u32);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct SymbolId(u32);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct TermId(u32);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct TheoryAtomId(u32);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct EClassId(u32);
```

#### Permanent Registry Sketch

The permanent registry is append-only across the whole solver lifetime.

```rust
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct ArenaStr {
    raw: NonNull<str>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct ArenaSlice<T> {
    raw: NonNull<[T]>,
    marker: PhantomData<T>,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Sort {
    Bool,
    Uninterpreted { name: ArenaStr },
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Symbol {
    name: ArenaStr,
    arg_sorts: ArenaSlice<SortId>,
    result_sort: SortId,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Term {
    Const(SymbolId),
    App { fun: SymbolId, args: ArenaSlice<TermId> },
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Atom {
    Eq(TermId, TermId),
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum SortRef<'a> {
    Bool,
    Uninterpreted { name: &'a str },
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct SymbolRef<'a> {
    name: &'a str,
    arg_sorts: &'a [SortId],
    result_sort: SortId,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum TermRef<'a> {
    Const(SymbolId),
    App { fun: SymbolId, args: &'a [TermId] },
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum AtomRef {
    Eq(TermId, TermId),
}

#[derive(Debug, Default)]
pub struct RegistryStorage {
    bump: Bump,
}

#[derive(Debug, Default)]
pub struct Interner<Id, T> {
    values: Vec<T>,
    index: HashMap<T, Id>,
}

#[derive(Debug, Default)]
pub struct Registry {
    storage: RegistryStorage,

    sorts: Interner<SortId, Sort>,
    symbols: Interner<SymbolId, Symbol>,
    terms: Interner<TermId, Term>,
    atoms: Interner<TheoryAtomId, Atom>,

    /// Sort of each interned term. This is derived metadata, not term identity.
    term_sort: Vec<SortId>,
    /// Permanent atom incidence lists.
    /// `term_atoms[t]` contains every canonical equality atom that mentions `t`.
    term_atoms: Vec<Vec<TheoryAtomId>>,

    /// Permanent structural use-lists for congruence repair.
    /// `parent_apps[t]` contains every application term that mentions `t` as an argument.
    parent_apps: Vec<Vec<TermId>>,

    bool_sort: Option<SortId>,
    true_term: Option<TermId>,
}
```

The registry API should be shaped roughly like:

```rust
impl Registry {
    pub fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId;
    pub fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId;
    pub fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId;
    pub fn intern_atom(&mut self, atom: AtomRef) -> TheoryAtomId;

    pub fn find_sort(&self, sort: SortRef<'_>) -> Option<SortId>;
    pub fn find_symbol(&self, symbol: SymbolRef<'_>) -> Option<SymbolId>;
    pub fn find_term(&self, term: TermRef<'_>) -> Option<TermId>;
    pub fn find_atom(&self, atom: AtomRef) -> Option<TheoryAtomId>;

    pub fn sort_ref(&self, id: SortId) -> SortRef<'_>;
    pub fn symbol_ref(&self, id: SymbolId) -> SymbolRef<'_>;
    pub fn term_ref(&self, id: TermId) -> TermRef<'_>;
    pub fn atom_ref(&self, id: TheoryAtomId) -> AtomRef;
    pub fn num_terms(&self) -> usize;
    pub fn num_atoms(&self) -> usize;
    pub fn term_sort(&self, id: TermId) -> SortId;
    pub fn term_atoms(&self, id: TermId) -> &[TheoryAtomId];
    pub fn parent_apps(&self, id: TermId) -> &[TermId];
    pub fn bool_sort(&mut self) -> SortId;
    pub fn true_term(&mut self) -> TermId;
}
```

The intended storage discipline is:

- nominal object types are `Sort`, `Symbol`, `Term`, and `Atom`,
- there is no separate `Key`/`Data` modeling layer,
- non-identity metadata such as `term_sort` lives in side tables,
- permanent incidence data such as `term_atoms` and `parent_apps` also lives in side tables,
- variable-length permanent payloads such as names and argument lists are copied into `storage.bump` exactly once on interning.

`ArenaStr` and `ArenaSlice<T>` are internal storage handles, not public lifetime-erased references. Safe dereferencing of those handles should be confined to `Registry` methods that tie the returned borrow to `&self`. For that reason, public read access should usually happen through borrowed view constructors such as `sort_ref`, `symbol_ref`, and `term_ref`, rather than by exposing the raw stored object directly.

The intended lookup discipline is:

- `find_*()` and `intern_*()` accept borrowed query shapes such as `&str`, `&[SortId]`, and `&[TermId]`,
- lookup must not allocate temporary boxed keys,
- on an interner miss, the registry copies the borrowed payload into `storage.bump`, constructs the nominal object, and inserts it.

The `Interner<Id, T>` sketch above is schematic. The important requirement is allocation-free borrowed probing, not the exact internal `HashMap` API shape. In practice this likely means using raw-entry or equivalent borrowed-key lookup so that probing `SymbolRef<'_>` or `TermRef<'_>` does not first materialize an owned `Symbol` or `Term`.

For example:

- `intern_symbol(SymbolRef { name, arg_sorts, result_sort })`
  probes the symbol interner with `name: &str` and `arg_sorts: &[SortId]` directly,
- only if the symbol is missing does it copy `name` and `arg_sorts` into the bump arena,
- the resulting `Symbol` then becomes both the canonical stored object and the interner key.

When interning `TermRef::App { fun, args }`, the registry should also append the new parent term ID to `parent_apps[arg]` for each child argument. This relation is structural and solver-lifetime permanent, so it should not live in the backtrackable search state.

When interning a canonical equality atom `Atom::Eq(lhs, rhs)`, the registry should append that `TheoryAtomId` to `term_atoms[lhs]` and `term_atoms[rhs]`. If `lhs == rhs`, it should append only once. This relation is also permanent and does not backtrack with SAT search.

The theory-atom to SAT-variable mapping is intentionally **not** part of `Registry`. It belongs to the SAT/theory boundary owned by `EufTheory`, because the same canonical atom identity is theory-side structure while the attached SAT variable is frontend/lowering metadata.

#### Search-Local Congruence State Sketch

This state is rebuilt at the beginning of each top-level `check-sat` and then backtracks with SAT decision levels during that search.

During one top-level `check-sat`, the permanent registry is assumed to be shape-stable:

- no new sorts,
- no new symbols,
- no new terms,
- no new theory atoms.

All lowering and theory-atom registration for the currently active SMT-LIB assertion stack should happen before SAT enters CDCL search. This is required because `SearchState` sizes its union-find arrays and enqueue bitmaps from `registry.num_terms()` / `registry.num_atoms()` at search start.

```rust
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeInput {
    lhs: TermId,
    rhs: TermId,
    reason_lit: Lit,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DiseqInput {
    lhs: TermId,
    rhs: TermId,
    reason_lit: Lit,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSigRef<'a> {
    fun: SymbolId,
    arg_reps: &'a [EClassId],
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CongruenceSig {
    fun: SymbolId,
    arg_reps: ArenaSlice<EClassId>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum MergeReason {
    InputEq { reason_lit: Lit },
    Congruence {
        left_parent: TermId,
        right_parent: TermId,
    },
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct MergeEdge {
    lhs: TermId,
    rhs: TermId,
    reason: MergeReason,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DisequalityEntry {
    lhs: TermId,
    rhs: TermId,
    reason_lit: Lit,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct LevelMarker {
    undo_len: usize,
    merge_edges_len: usize,
    active_disequalities_len: usize,
    pending_merges_len: usize,
    pending_repairs_len: usize,
    pending_atom_triggers_len: usize,
    pending_clauses_len: usize,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Undo {
    Parent { node: TermId, old_parent: EClassId },
    Rank { root: EClassId, old_rank: u32 },
    ClassHead { root: EClassId, old_head: TermId },
    ClassTail { root: EClassId, old_tail: TermId },
    ClassNext { node: TermId, old_next: Option<TermId> },
    CongruenceInsert { key: CongruenceSig },
}

#[derive(Clone, Debug, Default)]
pub struct SearchState {
    /// Search-lifetime arena for owned congruence signatures.
    congruence_storage: Bump,
    /// Union-find representative for each term.
    parent: Vec<EClassId>,
    /// Rank or size heuristic for each representative.
    rank: Vec<u32>,
    /// Linked membership list for each equivalence class.
    class_head: Vec<TermId>,
    class_tail: Vec<TermId>,
    next_in_class: Vec<Option<TermId>>,

    /// Congruence table keyed by function symbol and representative arguments.
    congruence_table: HashMap<CongruenceSig, TermId>,
    /// Scratch buffer used to build borrowed congruence signatures without allocation.
    congruence_sig_scratch: Vec<EClassId>,

    /// Pending merges still to process.
    pending_merges: VecDeque<MergeInput>,
    /// Parent applications that must be reconsidered after some merge.
    pending_repairs: VecDeque<TermId>,
    /// Theory atoms affected by recent class changes.
    pending_atom_triggers: Vec<TheoryAtomId>,
    pending_atom_qhead: usize,
    atom_is_enqueued: Vec<bool>,
    /// Pending theory clauses to return to SAT.
    pending_clauses: Vec<TheoryClause>,

    /// Disequalities that must hold in the current search state.
    active_disequalities: Vec<DisequalityEntry>,
    /// Explanation edges used to reconstruct equality proofs.
    /// The active prefix of this vector is the current proof graph.
    merge_edges: Vec<MergeEdge>,

    /// SAT level rollback support.
    undo_log: Vec<Undo>,
    level_markers: Vec<LevelMarker>,
}
```

The initialization pattern should be:

```rust
impl SearchState {
    pub fn reset_for_registry(&mut self, registry: &Registry) {
        let nterms = registry.num_terms();
        self.parent.clear();
        self.rank.clear();
        self.class_head.clear();
        self.class_tail.clear();
        self.next_in_class.clear();
        self.congruence_storage.reset();

        for i in 0..nterms {
            let term = TermId(i as u32);
            let rep = EClassId(i as u32);
            self.parent.push(rep);
            self.rank.push(0);
            self.class_head.push(term);
            self.class_tail.push(term);
            self.next_in_class.push(None);
        }

        self.congruence_table.clear();
        self.congruence_sig_scratch.clear();
        self.pending_merges.clear();
        self.pending_repairs.clear();
        self.pending_atom_triggers.clear();
        self.pending_atom_qhead = 0;
        self.atom_is_enqueued.clear();
        self.atom_is_enqueued.resize(registry.num_atoms(), false);
        self.pending_clauses.clear();
        self.active_disequalities.clear();
        self.merge_edges.clear();
        self.undo_log.clear();
        self.level_markers.clear();
    }

    pub fn push_level(&mut self) {
        self.level_markers.push(LevelMarker {
            undo_len: self.undo_log.len(),
            merge_edges_len: self.merge_edges.len(),
            active_disequalities_len: self.active_disequalities.len(),
            pending_merges_len: self.pending_merges.len(),
            pending_repairs_len: self.pending_repairs.len(),
            pending_atom_triggers_len: self.pending_atom_triggers.len(),
            pending_clauses_len: self.pending_clauses.len(),
        });
    }

    pub fn pop_levels(&mut self, new_level: sat::Level) {
        while self.level_markers.len() > new_level.index() {
            let marker = self.level_markers.pop().unwrap();
            self.pending_clauses.truncate(marker.pending_clauses_len);
            for &atom in &self.pending_atom_triggers[marker.pending_atom_triggers_len..] {
                self.atom_is_enqueued[atom.index()] = false;
            }
            self.pending_atom_triggers
                .truncate(marker.pending_atom_triggers_len);
            self.pending_atom_qhead = self.pending_atom_qhead.min(self.pending_atom_triggers.len());
            self.pending_repairs.truncate(marker.pending_repairs_len);
            self.pending_merges.truncate(marker.pending_merges_len);
            self.active_disequalities
                .truncate(marker.active_disequalities_len);
            self.merge_edges.truncate(marker.merge_edges_len);
            self.rollback_to(marker.undo_len);
        }
    }
}
```

`level_markers.len()` should always equal the current SAT level. Root level `0` has no marker. SAT must therefore call `notify_new_level()` exactly when it creates a new CDCL level, and `notify_backtrack(level)` with the target SAT level after analysis.

The intended rollback split is:

- `undo_log` handles in-place mutations of union-find, class membership, and congruence-table ownership,
- `LevelMarker` truncation handles append-only vectors and queues.

That keeps the undo records small and avoids encoding every queue push as its own `Undo` variant.

The first implementation should expose helpers roughly like:

```rust
impl SearchState {
    pub fn find(&self, term: TermId) -> EClassId;
    pub fn union_roots(
        &mut self,
        lhs_root: EClassId,
        rhs_root: EClassId,
    ) -> EClassId;
    pub fn make_congruence_sig<'a>(
        &'a mut self,
        registry: &Registry,
        parent: TermId,
    ) -> CongruenceSigRef<'a>;
    pub fn enqueue_atom_trigger(&mut self, atom: TheoryAtomId);
    pub fn enqueue_input_equality(&mut self, input: MergeInput);
    pub fn enqueue_input_disequality(&mut self, input: DiseqInput);
    pub fn rollback_to(&mut self, undo_len: usize);
}
```

`union_roots` should splice the smaller class list into the larger class list, record enough undo entries to restore `parent`, `rank`, `class_head`, `class_tail`, and the one `next_in_class` pointer modified by the splice, and then return the surviving root.

The first rollback-capable implementation should use union-by-rank or union-by-size **without ordinary path compression**. A reversible `find()` is much easier to keep sound if it is read-only. If profiling later shows that `find()` dominates runtime, reversible path compression can be added as a separate optimization.

For congruence lookup, the same no-allocation probe rule applies as in the permanent registry:

- `CongruenceSigRef<'_>` is the borrowed query shape,
- `CongruenceSig` is the stored owned shape,
- probing `congruence_table` should reuse `congruence_sig_scratch` instead of allocating a temporary boxed slice for every repair step,
- only a successful insertion into `congruence_table` should materialize an owned `CongruenceSig`,
- the owned `CongruenceSig` should copy its argument representatives into `congruence_storage`, not into a per-signature heap allocation,
- `congruence_storage` is reset once per top-level `check-sat`, not on SAT backtrack.

#### Congruence Repair And Propagation Sketch

The reversible core is easier to keep sound if congruence repair is explicit.

```rust
impl EufTheory {
    fn saturate(&mut self) {
        loop {
            while let Some(input) = self.search.pending_merges.pop_front() {
                self.merge_input(input);
                self.repair_congruence();
                self.check_active_disequalities();
            }

            self.process_pending_atom_triggers();

            if self.search.pending_merges.is_empty()
                && self.search.pending_repairs.is_empty()
                && self.search.pending_atom_qhead == self.search.pending_atom_triggers.len()
            {
                return;
            }
        }
    }

    fn merge_input(&mut self, input: MergeInput);
    fn merge_due_to_congruence(
        &mut self,
        lhs_parent: TermId,
        rhs_parent: TermId,
    );
    fn repair_congruence(&mut self);
    fn enqueue_repairs_for_class(&mut self, root: EClassId);
    fn enqueue_atom_triggers_for_class(&mut self, root: EClassId);
    fn repair_parent_app(&mut self, parent: TermId);
    fn check_active_disequalities(&mut self);
    fn process_pending_atom_triggers(&mut self);
    fn evaluate_atom_trigger(&mut self, atom: TheoryAtomId);
}
```

Recommended semantics:

- `merge_input` merges two terms justified by an asserted equality SAT literal and, for every class that changed, enqueues both congruence repairs and affected atom triggers.
- `merge_due_to_congruence` merges two application terms justified by `MergeReason::Congruence` and schedules the same follow-up work.
- `enqueue_repairs_for_class` iterates the linked-list members of the merged class, looks up structural users from `registry.parent_apps(term)`, and pushes those parent applications into `pending_repairs`.
- `enqueue_atom_triggers_for_class` iterates the linked-list members of the merged class, looks up incident atoms from `registry.term_atoms(term)`, and enqueues each affected atom at most once.
- `repair_parent_app` recomputes the borrowed congruence signature for that application from current child representatives; if another owner with the same signature already exists, the two parent terms become a new congruence merge.
- `check_active_disequalities` emits a conflict clause as soon as some asserted disequality now has equal endpoints.
- `process_pending_atom_triggers` drains the affected-atom queue. For each canonical equality atom `(= s t)`, it compares the current class representatives of `s` and `t` and then:
  - clears `atom_is_enqueued[atom]` when the atom is dequeued,
  - emits the unit propagation clause for the positive literal if the atom became true and its SAT variable is unassigned,
  - emits the conflict clause if the atom is assigned false but `s` and `t` are now equal,
  - otherwise does nothing.

This merge-triggered atom propagation is the recommended design because:

- it follows the same high-level mechanism as cvc5's equality triggers,
- it avoids whole-registry scans after every merge,
- it reuses permanent incidence data and low-frequency SAT-level rollback,
- it does not require a second congruence-style watch structure for atoms.

#### Explanation And Output Sketch

The search state should reconstruct clauses over SAT literals only. EUF should never return a raw internal reason to SAT.

```rust
#[derive(Clone, Debug)]
pub enum EqualityExplanation {
    InputLiteral(Lit),
    Congruence {
        left_parent: TermId,
        right_parent: TermId,
        child_pairs: Box<[(TermId, TermId)]>,
    },
}

#[derive(Clone, Debug)]
pub struct ExplanationClause {
    propagated: Option<Lit>,
    premises: Box<[Lit]>,
}

impl ExplanationClause {
    pub fn to_theory_clause(
        &self,
        solver: &sat::Solver,
        kind: TheoryClauseKind,
    ) -> TheoryClause {
        let mut lits = Vec::with_capacity(self.premises.len() + usize::from(self.propagated.is_some()));
        for &premise in &*self.premises {
            lits.push(!premise);
        }
        if let Some(prop) = self.propagated {
            lits.push(prop);
        }
        let scope = lits
            .iter()
            .map(|lit| solver.variable_scope_of(lit.var()))
            .max()
            .unwrap_or(Scope::ROOT);
        TheoryClause {
            lits: lits.into_boxed_slice(),
            scope,
            kind,
        }
    }
}
```

The recursive explanation helpers should look conceptually like:

```rust
impl SearchState {
    pub fn explain_equality(
        &self,
        registry: &Registry,
        lhs: TermId,
        rhs: TermId,
        out: &mut Vec<Lit>,
    );

    pub fn explain_conflict(
        &self,
        registry: &Registry,
        diseq: DisequalityEntry,
        out: &mut Vec<Lit>,
    );

    pub fn explain_propagation(
        &self,
        propagated: Lit,
        support: &[Lit],
    ) -> ExplanationClause;
}
```

The expected semantics are:

- equality explanation walks the active prefix of `merge_edges` as an undirected proof graph until it reaches asserted equalities,
- conflict explanation returns the SAT literals that jointly imply an impossible disequality,
- propagation explanation returns a clause of the form `(!p1 OR !p2 OR ... OR q)`.

For the first implementation, it is acceptable for `explain_equality` to run a local graph search over the active `merge_edges` prefix instead of maintaining a more elaborate proof forest. The representation should optimize for rollback clarity first; if explanation cost later shows up in profiles, the proof graph can be specialized without changing the SAT/theory interface.

#### EUF Solver Object Sketch

The actual `euf` crate should combine permanent registry and search-local state, plus the SAT-facing atom map.

```rust
#[derive(Debug, Default)]
pub struct EufTheory {
    registry: Registry,
    search: SearchState,

    theory_atom_to_var: Vec<Var>,
    var_to_theory_atom: Vec<Option<TheoryAtomId>>,

    /// Queue of assigned theory literals not yet processed by EUF.
    pending_assignments: VecDeque<Lit>,
}
```

The frontend-facing API should be roughly:

```rust
impl EufTheory {
    pub fn new() -> Self;

    pub fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId;
    pub fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId;
    pub fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId;

    pub fn intern_equality_atom(&mut self, lhs: TermId, rhs: TermId, sat_var: Var) -> TheoryAtomId;
    pub fn theory_atom_for_var(&self, var: Var) -> Option<TheoryAtomId>;

    pub fn atom_literal_kind(&self, lit: Lit) -> Option<AtomLiteralKind>;
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AtomLiteralKind {
    Eq { lhs: TermId, rhs: TermId, positive: bool },
}
```

`intern_equality_atom(lhs, rhs, sat_var)` should:

- normalize the atom as `Atom::Eq(min(lhs, rhs), max(lhs, rhs))`,
- intern that canonical atom in `registry`,
- install or verify the SAT/theory boundary mapping in `theory_atom_to_var` and `var_to_theory_atom`,
- reject or treat as a frontend bug any attempt to bind the same canonical theory atom to two different SAT variables.

#### `Theory` Trait Implementation Sketch

`euf` should implement the SAT-side theory trait approximately like this:

```rust
impl Theory for EufTheory {
    fn notify_search_start(&mut self) {
        self.search.reset_for_registry(&self.registry);
        self.pending_assignments.clear();
    }

    fn notify_new_decision_level(&mut self) {
        self.search.push_sat_level();
    }

    fn notify_assignment(&mut self, lit: Lit) {
        if self.theory_atom_for_var(lit.var()).is_some() {
            self.pending_assignments.push_back(lit);
        }
    }

    fn notify_backtrack(&mut self, level: usize) {
        self.search.pop_sat_levels(level);
    }

    fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>) {
        self.process_pending_assignments();
        self.saturate();
        out.append(&mut self.search.pending_clauses);
    }

    fn final_check(&mut self, out: &mut Vec<TheoryClause>) {
        self.process_pending_assignments();
        self.saturate();
        out.append(&mut self.search.pending_clauses);
    }

    fn has_pending_work(&self) -> bool {
        !self.pending_assignments.is_empty()
            || !self.search.pending_clauses.is_empty()
            || !self.search.pending_merges.is_empty()
            || !self.search.pending_repairs.is_empty()
            || self.search.pending_atom_qhead < self.search.pending_atom_triggers.len()
    }
}
```

And the main internal work loop should be:

```rust
impl EufTheory {
    fn process_pending_assignments(&mut self) {
        while let Some(lit) = self.pending_assignments.pop_front() {
            match self.atom_literal_kind(lit) {
                Some(AtomLiteralKind::Eq { lhs, rhs, positive: true }) => {
                    self.search.pending_merges.push_back(MergeInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                    self.saturate();
                }
                Some(AtomLiteralKind::Eq { lhs, rhs, positive: false }) => {
                    self.search
                        .enqueue_input_disequality(DiseqInput { lhs, rhs, reason_lit: lit });
                    self.check_active_disequalities();
                }
                None => {}
            }
        }
    }
}
```

#### EUF Invariants

The EUF core should maintain these invariants:

```rust
/// Every registered term belongs to exactly one current equivalence class.
assert_eq!(search.parent.len(), registry.num_terms());

/// Registry shape is frozen during one top-level search.
assert_eq!(search.atom_is_enqueued.len(), registry.num_atoms());

/// Structural parent-use lists are permanent registry data, not search-local rollback data.
assert_eq!(registry.parent_apps.len(), registry.num_terms());

/// The boundary map from theory atoms to SAT variables is total over interned atoms.
assert_eq!(theory_atom_to_var.len(), registry.num_atoms());

/// Every SAT variable mapped as a theory atom points to a valid atom.
assert!(var_to_theory_atom[var.index()]
    .is_none_or(|atom| atom.index() < registry.num_atoms()));

/// The forward and reverse SAT/theory atom maps are consistent.
assert!(var_to_theory_atom.iter().enumerate().all(|(vi, mapped)| {
    mapped.is_none_or(|atom| theory_atom_to_var[atom.index()].index() == vi)
}));

/// Every pending merge is justified by one currently assigned SAT literal.
assert!(search.pending_merges.iter().all(|m| m.reason_lit.var().index() < sat.num_vars()));

/// The pending atom-trigger queue indices stay in range.
assert!(search.pending_atom_qhead <= search.pending_atom_triggers.len());

/// Every term appears in exactly one linked class-membership list.
assert_eq!(search.next_in_class.len(), registry.num_terms());

/// Every theory clause returned to SAT is already fully explained in SAT literals.
assert!(search.pending_clauses.iter().all(|clause| !clause.lits.is_empty()));
```

Again, the syntax above is schematic. The important part is the invariant, not the exact code.

## Frontend Lowering Design

The SMT-LIB driver needs a Boolean lowering layer between parser and SAT.

### Commands That Must Be Supported For The Benchmark

For the incremental QF-UF benchmark target, the driver should support at least:

- `set-logic`
- `set-info`
- `declare-sort`
- `declare-fun`
- `declare-const`
- `assert`
- `push`
- `pop`
- `check-sat`
- `exit`

Other commands can remain unsupported initially if the benchmark set does not require them.

### Formula Lowering

Separate the frontend representation into:

- term DAG for non-Boolean and Boolean theory terms,
- propositional structure for connectives.

Recommended lowering path:

1. parse SMT-LIB term/formula AST,
2. intern all theory terms in the permanent `euf` registry,
3. convert every theory atom to one SAT literal,
4. Tseitin-lower Boolean structure to CNF inside `sat`.

Recommended Boolean lowering data:

- `BoolView`
  - constant `true` or `false`,
  - existing SAT literal,
  - newly created Tseitin literal
- `AssertFrame`
  - current scope frame id,
  - vector of asserted root literals or clauses

This keeps EUF focused only on equalities, not on parsing or CNF encoding.

## Incremental Check Lifecycle

One `check-sat` should conceptually do this:

1. SAT resets per-check search state.
2. SAT starts from the currently active native assertion stack.
3. EUF resets search-local state.
4. SAT starts CDCL.
5. Boolean propagation runs.
6. Newly assigned theory literals are pushed into EUF.
7. EUF saturates congruence closure and returns any explained clauses.
8. SAT adds those clauses and continues.
9. On `SAT`, SAT asks EUF for `final_check`.
10. If `final_check` emits more clauses, continue searching.
11. Otherwise return `sat`.

The important point is that EUF is not replayed from scratch for every propagation step. It is reset once per top-level `check-sat`, and then it backtracks with SAT decision levels during that search.

If `solve_with_assumptions()` is used, those assumptions are an extra transient layer on top of the native assertion stack, not the representation of the stack itself.

## Harness Redesign

The package should be renamed from `sat-harness` to `my-harness`, but the more important change is the data model.

### Why The Current Model Is Wrong For Incremental SMT

One case no longer has one semantic result.

Instead, one case now has:

- one command trace,
- zero or more non-query commands,
- `n` query commands,
- one expected result per query,
- one actual response per query.

The harness therefore needs to store both:

- query-level outcomes,
- a derived case-level summary.

### Recommended Case Model

Recommended persistent metadata:

- `CaseRecord`
  - stable path key,
  - bytes,
  - logic,
  - query count if precomputed

Recommended expected-answer model:

- `ExpectedQueryResult`
  - query index,
  - expected: `sat | unsat | unknown`

Recommended runtime result model:

- `QueryOutcome`
  - query index,
  - expected,
  - actual,
  - elapsed since case start or per-query delta,
  - category

- `CaseOutcome`
  - case metadata,
  - aggregate category,
  - total elapsed,
  - `queries: Vec<QueryOutcome>`,
  - optional detail,
  - optional telemetry

Case aggregate category should be derived mechanically:

- `Pass` if all queries match,
- `WrongAnswer` if any query mismatches,
- `Timeout` if the interactive run times out before all queries finish,
- other infrastructure categories as needed.

### Recommended Harness Execution Model

For incremental SMT, the child process should:

- spawn the actual solver binary,
- stream the benchmark file command by command to stdin,
- read one response per command from stdout,
- validate `success` on non-query commands if desired,
- record `sat | unsat | unknown` on each `check-sat`.

This matches the competition model much better than “load file, call library function once”.

### Recommended Comparison Semantics

The comparison subcommand should stop pretending that exact elapsed times are part of semantic equality.

For incremental SMT runs, the semantic comparison should be:

- same discovered cases,
- same number of queries per case,
- same category per query,
- same actual answer per query,
- optionally same aggregate category per case.

Elapsed time differences should be reported as metrics, not treated as mismatches.

## Recommended Package Boundaries

A clean package split is:

- `sat`
  - incremental CDCL core,
  - theory trait,
  - clause database,
  - native `push`/`pop`,
  - optional assumptions API
- `euf`
  - term registry,
  - equality engine,
  - explanation engine,
  - implementation of the theory trait
- `qfuf` or `smt`
  - SMT-LIB parser integration,
  - symbol tables,
  - lowering to SAT plus EUF,
  - solver binary
- `my-harness`
  - benchmark discovery,
  - interactive case runner,
  - saved result format,
  - comparison UI

This is more maintainable than making `euf` parse SMT-LIB directly or making `sat` own uninterpreted-function terms.

## Key Design Decisions And Alternatives

### Decision 1: Activation Literals For Scope Frames

Recommended:

- use native SAT `push`/`pop` for SMT-LIB scopes, and keep assumptions only as a separate transient API.

Alternative:

- encode scope frames via activation literals and assumptions.

Why not the alternative:

- it adds control literals to every scoped clause,
- it can hurt incremental performance on workloads with many `check-sat` calls,
- it is not the architecture we want to optimize around for the target benchmark class.

### Decision 2: Theory Returns Clauses, Not Raw SAT Reasons

Recommended:

- EUF produces explained clauses.

Alternative:

- EUF directly enqueues literals with opaque theory reasons.

Why not the alternative:

- conflict analysis in `sat` becomes more coupled to theory internals,
- the SAT reason model gets more complicated immediately,
- testing the boundary becomes harder.

### Decision 3: Harness Talks To The Solver Process

Recommended:

- `my-harness` runs the real solver over stdin/stdout.

Alternative:

- harness links directly to an internal Rust solver API.

Why not the alternative:

- it misses protocol bugs,
- it does not match SMT-COMP incremental execution semantics,
- it gives less confidence that the final binary can really run the benchmark.

## Minimal Command Subset For “Can Run Incremental QF-UF Benchmark”

The solver should be considered benchmark-runnable once it can correctly process benchmark traces using:

- declarations of uninterpreted sorts and functions,
- Boolean connectives,
- equalities between QF-UF terms,
- `assert`,
- `push 1`,
- `pop 1`,
- repeated `check-sat`,
- `exit`.

Model production, unsat cores, and general SMT-LIB command coverage are separate concerns and should not be folded into this design target.

## Summary

The central refactor is not “teach EUF a bit of incrementality”. The central refactor is:

- make `sat` the only Boolean search engine,
- make `euf` a pure theory module with explained consequences,
- introduce a real SMT driver above them,
- model one benchmark file as a multi-query interaction instead of a single result,
- make native SAT `push`/`pop` the mechanism that represents SMT-LIB scopes.

If those four points are done with the boundaries described above, the repository shape becomes compatible with incremental QF-UF benchmarking and remains extensible to additional theories later.
