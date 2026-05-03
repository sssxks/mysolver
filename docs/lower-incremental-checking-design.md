# `lower` Incremental Checking Refactor Draft

## Background

The current `lower` crate keeps incremental SMT-LIB command state, but it does
not keep incremental lowered solver state across `check-sat` calls.

Today the lifecycle is:

1. Parse SMT-LIB into `SExpr`.
2. Convert `SExpr` into `Command`.
3. Store top-level assertions and zero-arity definitions inside `Solver`.
4. On every `check-sat`, construct a fresh `SatEufCheck`.
5. Replay every active assertion through lowering again.
6. Hand one fully rebuilt SAT+EUF problem to `solver-core`.

This means repeated `check-sat` calls on an incremental benchmark only share:

- parsed `SExpr` trees,
- top-level assertion stack structure,
- top-level zero-arity definitions,
- frame bookkeeping.

They do **not** share:

- symbol resolution for boolean names and uninterpreted function names,
- term interning,
- theory atom deduplication,
- CNF lowering results,
- SAT variable numbering,
- EUF solver term universe,
- any `solver-core` search state.

That is enough to explain the current performance shape on incremental inputs:
the command layer is incremental, but the lowered problem is rebuilt from
scratch for every `check-sat`.

## Problem Statement

We need a design that improves reuse across repeated `check-sat` calls without
forcing a high-risk rewrite of the solver stack all at once.

There are two distinct opportunities:

1. Reuse **surface-to-IR lowering work** across `check-sat`.
2. Reuse **backend SAT/EUF problem state** across `check-sat`.

These should be treated as separate refactors.

## Goals

- Stop repeating `SExpr`-level symbol and term reconstruction on every
  `check-sat`.
- Preserve the current external SMT-LIB behavior while the refactor lands.
- Keep `push` / `pop` semantics explicit instead of hiding them behind
  ad-hoc caches.
- Make a later true incremental SAT/EUF backend possible without discarding the
  first refactor.
- Keep unsupported syntax and current error behavior understandable.

## Non-Goals

- Do not make `solver-core` incremental in the first phase.
- Do not preserve CDCL search state in the first phase.
- Do not introduce aggressive speculative caching tied directly to `SExpr`
  pointer identity.
- Do not optimize for unsupported SMT-LIB features before the representation is
  cleaned up.

## Current Constraints

### `lower` owns surface symbol handling

`euf-core` explicitly expects callers to own surface symbol tables and to intern
terms into a specific `EufSolver` instance. That means `FunId` and `TermId` are
instance-local backend ids, not stable ids that can be lifted into `Solver`
    state.

### `solver-core` is one-shot

`solver-core::solve_with_budget(...)` consumes one fully lowered SAT+EUF
problem. The interface does not currently expose:

- assumptions,
- incremental clause addition,
- reversible stack scopes,
- persistent learned clauses,
- persistent theory state.

### Frame activation is not implemented yet

`ActivationLiteral` exists only as a reserved identifier. The current `pop`
semantics are structural truncation of the assertion list, not logical
deactivation inside a persistent backend.

## Proposed Architecture

Split the current `SatEufCheck` responsibilities into two layers:

1. A **persistent semantic lowering layer** owned by `Solver`.
2. A **per-check backend build layer** that maps persistent IR into one
   backend problem instance.

This gives a clean boundary:

- persistent ids live above the backend,
- backend-local ids stay backend-local,
- the first refactor already removes repeated syntax walking and symbol
  reconstruction,
- the second refactor can later replace the per-check backend build layer with a
  true incremental backend session.

## Phase 1: Persistent Lowered IR

### Summary

Move `SExpr` to semantic IR lowering out of the `check-sat` hot path.

Instead of storing only original `SExpr` in `Solver`, lower top-level
definitions and assertions once into a stable, backend-agnostic IR.

Each `check-sat` still builds a fresh SAT+EUF problem, but it builds it from
already-resolved IR rather than reinterpreting SMT-LIB syntax.

### Target Outcome

After phase 1:

- `assert` lowers once,
- `define-fun` lowers once,
- repeated `check-sat` does not recurse through `SExpr`,
- repeated `check-sat` does not rebuild surface symbol tables from raw names,
- `solver-core` and `euf-core` interfaces stay unchanged.

### New Persistent Context

Add a persistent lowering context inside `Solver`, conceptually:

```rust
struct Solver<'src> {
    source: &'src str,
    frames: Vec<Frame>,
    assertions: Vec<AssertedFormula>,
    definitions: DefinitionTable,
    lower: LowerContext,
    next_frame: u32,
    next_activation: u32,
}
```

Suggested responsibilities:

- `DefinitionTable`
  - stores validated zero-arity definitions,
  - maps surface symbol name to persistent lowered value or term/formula body.
- `LowerContext`
  - owns stable symbol interning above the backend,
  - owns persistent lowered node arenas,
  - provides APIs to lower new top-level forms once.

### Persistent Id Types

Introduce ids that are **not** tied to one `EufSolver` or one SAT instance:

```rust
struct LowerBoolSymbolId(u32);
struct LowerFunSymbolId(u32);
struct LowerTermId(u32);
struct LowerFormulaId(u32);
struct LowerDefinitionId(u32);
```

These ids identify semantic objects inside `lower`, not backend objects.

### Proposed IR Shape

The exact representation can vary, but it should distinguish boolean formulas
from term expressions at the type level.

Suggested shape:

```rust
enum FormulaNode {
    True,
    False,
    BoolSymbol(LowerBoolSymbolId),
    Not(LowerFormulaId),
    And(Box<[LowerFormulaId]>),
    Or(Box<[LowerFormulaId]>),
    Implies(LowerFormulaId, LowerFormulaId),
    BoolEq(Box<[LowerFormulaId]>),
    TermEq(Box<[LowerTermId]>),
    Distinct(Box<[LowerTermId]>),
    FormulaIte {
        cond: LowerFormulaId,
        then_branch: LowerFormulaId,
        else_branch: LowerFormulaId,
    },
}

enum TermNode {
    Const(LowerFunSymbolId),
    App {
        fun: LowerFunSymbolId,
        args: Box<[LowerTermId]>,
    },
    TermIte {
        cond: LowerFormulaId,
        then_branch: LowerTermId,
        else_branch: LowerTermId,
    },
}
```

This is intentionally close to the semantics already implemented in
`SatEufCheck`, but no longer tied to backend-local ids.

### Lowering Rules

Lowering from `SExpr` into persistent IR should:

- resolve surface boolean symbols into persistent `LowerBoolSymbolId`,
- resolve uninterpreted function names into persistent `LowerFunSymbolId`,
- recursively expand supported zero-arity definitions,
- type-discriminate formula versus term positions during lowering,
- intern repeated semantic nodes when profitable,
- reject unsupported shapes at lowering time rather than at `check-sat` time.

This moves failures earlier and makes `check-sat` a build-and-solve step instead
of a parse-like step.

### Assertion Storage

Replace:

```rust
pub struct AssertedFormula {
    pub id: AssertedFormulaId,
    pub formula: SExpr,
}
```

with something conceptually like:

```rust
pub struct AssertedFormula {
    pub id: AssertedFormulaId,
    pub formula: LowerFormulaId,
}
```

Optionally keep the original `SExpr` only for diagnostics if needed:

```rust
pub struct AssertedFormula {
    pub id: AssertedFormulaId,
    pub formula: LowerFormulaId,
    original: SExpr,
}
```

If diagnostics do not require the original tree, prefer dropping it to reduce
memory retention.

### Backend Build Context

Each `check-sat` creates a fresh builder that maps persistent ids into
backend-local ids:

```rust
struct BackendBuildCtx<'a> {
    lower: &'a LowerContext,
    euf: EufSolver,
    fun_map: HashMap<LowerFunSymbolId, FunId>,
    term_map: HashMap<LowerTermId, TermId>,
    bool_map: HashMap<LowerBoolSymbolId, BoolVar>,
    theory_vars: HashMap<TheoryKey, BoolVar>,
    theory_atoms: Vec<(BoolVar, TheoryKey)>,
    clauses: Vec<Box<[Lit]>>,
    next_bool_var: u32,
    next_term_proxy: u32,
}
```

This is the spiritual replacement for today’s `SatEufCheck`, but it operates on
already-lowered semantic ids instead of raw `SExpr`.

### Why Phase 1 Is Worth Doing

This phase does **not** solve everything, but it removes the part that is
currently most obviously repeated and easiest to separate:

- no repeated string-based symbol lookup from syntax trees,
- no repeated traversal of unchanged assertion trees,
- no repeated recursive definition expansion from syntax,
- no repeated formula/term shape discrimination from syntax.

It also creates the representation needed for later incremental backend work.

## Phase 2: True Incremental Backend

### Summary

Once phase 1 is stable, replace “build a fresh backend problem every
`check-sat`” with a persistent backend session.

At that point `ActivationLiteral` becomes real rather than reserved.

### Target Outcome

After phase 2:

- new assertions are lowered once and added once,
- `check-sat` reuses one SAT clause database and one EUF term universe,
- `push` / `pop` become activation-scoped rather than replay-scoped,
- repeated `check-sat` can reuse learned clauses and backend-local ids where
  sound,
- the system behaves like an actual incremental SMT solver rather than a
  command-level incremental wrapper around one-shot solving.

### Backend Session Shape

Conceptually:

```rust
struct IncrementalBackend {
    euf: PersistentEufState,
    sat: PersistentSatState,
    activation_vars: HashMap<ActivationLiteral, BoolVar>,
    asserted_units: Vec<BackendAssertionHandle>,
}
```

This likely requires `solver-core` changes. The exact API might become:

```rust
impl IncrementalBackend {
    fn add_clause(&mut self, clause: Box<[Lit]>);
    fn add_theory_atom(&mut self, lit: BoolVar, atom: TheoryKey);
    fn solve_with_assumptions<B: CheckBudget>(
        &mut self,
        assumptions: &[Lit],
        budget: &mut B,
    ) -> SatResult;
}
```

### Frame Encoding

Use one activation literal per pushed frame.

Suggested policy:

- assertions added at base level are unconditional,
- assertions added under frame `F` are guarded by `act(F)`,
- if nested frames exist, assertions are guarded by the conjunction of active
  frame literals in scope,
- `check-sat` calls the backend with active frame assumptions,
- `pop` removes assumptions from future calls rather than deleting clauses.

There are two common ways to encode nested frames:

1. Guard each assertion with all active frame literals.
2. Make frame activations imply parent activations, then guard each assertion
   only with the current frame literal.

The second is cleaner if the backend already supports clause addition well:

- add clause `(!act(child) ∨ act(parent))`,
- guard a frame-local assertion with `(!act(frame) ∨ ...)`.

### What Must Change in `solver-core`

`solver-core` currently solves a fully built problem in one call. To support
true incrementality it will likely need:

- persistent clause storage,
- persistent watch lists,
- persistent variable allocation,
- an assumptions API,
- a strategy for solver state reset between checks,
- a policy for retaining or dropping learned clauses across scoped checks.

The smallest useful step is:

- persistent clause database,
- assumptions-based solving,
- no attempt to preserve advanced heuristics initially.

That still provides structural reuse without overcommitting early.

### What Must Change in `euf-core`

Possibly less than `solver-core`, depending on how theory propagation is
structured. We mainly need:

- one persistent term universe,
- stable mapping from persistent lower ids to backend term ids,
- theory checks that can be rerun against different active theory literals.

If `euf-core` already treats the term universe separately from equality
assumptions, it may be possible to preserve term interning before preserving
full congruence state.

## Recommended Implementation Plan

### Step 1: Introduce persistent ids and IR

- add `LowerContext`,
- add formula and term node arenas,
- add persistent symbol interning,
- keep current external `Solver` API intact.

### Step 2: Lower definitions on insertion

- replace `HashMap<Symbol, SExpr>` with validated lowered definitions,
- fail early on unsupported definition bodies,
- keep zero-arity-only policy for now.

### Step 3: Lower assertions on insertion

- replace stored asserted `SExpr` with stored `LowerFormulaId`,
- keep `push` / `pop` as current structural truncation,
- keep current `ActivationLiteral` placeholder untouched for now.

### Step 4: Rebuild `SatEufCheck` into a backend builder

- remove syntax walking from the `check-sat` path,
- build one-shot backend state from persistent IR,
- preserve existing solver behavior and tests.

### Step 5: Measure

- compare repeated `check-sat` runs on incremental benchmarks before and after,
- specifically track time spent in:
  - top-level assertion replay,
  - definition expansion,
  - symbol interning,
  - term interning,
  - SAT solving.

This measurement should determine whether phase 2 is worth doing immediately.

### Step 6: Add true incremental backend only if phase 1 is not enough

- expose assumptions or scoped activation support in `solver-core`,
- thread activation literals through clause generation,
- make `pop` a logical deactivation instead of a structural replay boundary.

## Data Ownership After Phase 1

The ownership model should become:

- `Solver`
  - owns command-level stack state,
  - owns persistent lowered IR,
  - owns stable semantic symbol ids.
- `BackendBuildCtx`
  - owns one backend-local SAT/EUF problem instance,
  - owns only per-check ids and clauses.
- `solver-core`
  - remains one-shot and unaware of SMT-LIB syntax.
- `euf-core`
  - remains backend-level and unaware of surface symbols.

This separation is the main architectural cleanup.

## Expected Benefits

### Phase 1

- clear reduction in repeated lowering work,
- simpler cost model for repeated `check-sat`,
- earlier rejection of unsupported forms,
- better foundation for profiling and later backend refactors.

### Phase 2

- reuse of SAT and EUF problem structure,
- lower repeated `check-sat` latency on scoped incremental benchmarks,
- a real use for `ActivationLiteral`,
- solver behavior that better matches SMT-LIB incremental workflows.

## Risks

### Phase 1 Risks

- introducing a typed IR may expose latent ambiguity in current formula-versus-
  term discrimination,
- storing both original `SExpr` and IR may temporarily increase memory use,
- definition lowering needs cycle policy and clear error reporting.

### Phase 2 Risks

- incremental CDCL state handling is substantially more complex than phase 1,
- assumptions and learned clause retention can easily produce subtle soundness
  bugs if scope handling is weak,
- persistent theory state may require more invasive redesign than expected.

## Open Questions

- Should original `SExpr` trees be retained for diagnostics after lowering, or
  should diagnostics switch to symbol/span-based reporting?
- Should phase 1 intern full semantic nodes aggressively, or only intern symbols
  and lower nodes straightforwardly first?
- Do we want one shared “value” IR that can represent both terms and formulas,
  or do we want strict separation between `FormulaNode` and `TermNode`?
  Strict separation is safer.
- Do zero-arity definitions expand eagerly into IR, or should they remain named
  references until backend build time?
  Eager lowering is simpler and exposes unsupported shapes earlier.
- After phase 1, is replaying all active assertions still a meaningful enough
  cost to justify phase 2 immediately?

## Recommendation

Implement phase 1 first.

It has the best cost-to-risk ratio:

- it directly addresses the confirmed repeated lowering issue,
- it keeps solver semantics stable,
- it creates the correct architecture for true incrementality later,
- it avoids prematurely entangling a representation refactor with a backend
  solver rewrite.

Only start phase 2 after phase 1 lands and profiling shows that backend rebuild
still dominates real incremental workloads.

## Current Status In Tree

The current code base has already implemented most of phase 1 in
`crates/lower/src/lib.rs`.

What is now true in the checked-in implementation:

- `Solver` stores `AssertedFormula { id, formula: LowerFormulaId }` instead of
  storing raw asserted `SExpr` trees.
- `define-fun` lowers once at insertion time into `DefinitionTable`, split into
  `LoweredDefinitionValue::Formula` and `LoweredDefinitionValue::Term`.
- `LowerContext` owns persistent symbol tables plus persistent formula and term
  arenas.
- both formula nodes and term nodes are hash-consed, so repeated semantic
  structure lowers to the same persistent ids.
- `check-sat` now builds a fresh `BackendBuildCtx` from persistent IR instead of
  recursively re-reading SMT-LIB syntax.
- backend-local SAT literals, EUF term ids, and theory atoms are still rebuilt
  per check, as intended for phase 1.

This means the document above should now be read partly as design rationale for
the current implementation, not only as a proposal for future work.

## Phase 1 As Implemented

The landed representation differs from the earlier sketch in a few useful ways.

### Typed persistent IR is real

The implementation uses the exact separation this document argued for:

- `FormulaNode`
  - `True`
  - `False`
  - `BoolSymbol`
  - `Not`
  - `And`
  - `Or`
  - `Implies`
  - `BoolEq`
  - `TermEq`
  - `Distinct`
  - `FormulaIte`
- `TermNode`
  - `Const`
  - `App`
  - `TermIte`

That separation was the correct choice. It keeps lowering failures local and
avoids a large class of "figure out later whether this value is boolean or term"
logic inside `check-sat`.

### Hash-consing moved into the persistent layer

The current `LowerContext` does not only intern surface symbols. It also interns
full semantic nodes:

- `formula_intern: HashMap<FormulaNode, LowerFormulaId>`
- `term_intern: HashMap<TermNode, LowerTermId>`

This is stronger than the minimal phase 1 design. It means repeated assertion
subtrees can collapse before backend building even starts.

That is a good tradeoff for this code base because:

- the supported language fragment is still small,
- the IR node types are compact and deterministic,
- semantic deduplication simplifies later profiling,
- later persistent-backend work can reuse these ids directly.

### Backend building already has its own internal cache boundary

The per-check builder has one more useful layer than the high-level design
initially spelled out:

- persistent `LowerFormulaId` and `LowerTermId` live in `Solver`,
- per-check backend ids live in `BackendBuildCtx`,
- within one check, `formula_cache` avoids repeated Tseitinization of the same
  lowered formula node.

That cache boundary matters. Even before phase 2, the architecture is already:

1. lower once into persistent semantic ids,
2. encode each persistent formula at most once per check,
3. solve one backend problem.

This is a clean layering and should be preserved.

### Term `ite` lowering is already normalized through proxy equalities

The implemented builder lowers `TermIte` by:

1. materializing both branches,
2. allocating a fresh proxy term when the branches differ,
3. asserting guarded equalities from the proxy to the chosen branch.

That is an important design decision because it means the persistent IR can stay
close to source semantics while the backend encoding remains purely SAT + EUF.
Phase 2 should keep this encoding strategy unless the backend grows first-class
support for conditional terms, which is unlikely to be worth it.

## Deliberate Gaps That Still Remain

Even after phase 1 landed, the main non-incremental boundaries are still very
clear.

### `check-sat` still rebuilds all backend-local state

Every `check-sat` still constructs:

- a fresh `EufSolver`,
- a fresh SAT variable numbering,
- a fresh theory-atom table,
- a fresh clause vector,
- a fresh Tseitin encoding.

So repeated checks no longer re-lower syntax, but they still re-encode the full
active problem into backend form.

### `push` / `pop` are now activation-scoped

Phase 2 makes frame activations semantically real.

The current implementation keeps the user-visible assertion stack for command
bookkeeping, but backend scoping is no longer implemented by replay or rebuild.

What is now true in tree:

- each pushed frame still receives one stable `ActivationLiteral`,
- assertions record the activation literal of the frame they were created in,
- base-level assertions are emitted as unconditional clauses,
- frame-local assertions are emitted once as guarded clauses `(!act(frame) ∨ body)`,
- `check-sat` enables only the currently active frame literals through SAT assumptions,
- `pop` deactivates future checks logically instead of deleting backend clauses.

This is the core semantic shift of phase 2: popped assertions remain stored in
the backend, but they are dormant unless their frame is active again, which
cannot happen under SMT-LIB stack discipline after that frame has been popped.

### Definitions are still an early-lowering convenience, not a general scope model

The current implementation lowers zero-arity `define-fun` bodies eagerly and
stores the lowered result by symbol name.

That is enough for the supported fragment, but it also means:

- the design is still centered on current QF_UF support,
- broader SMT-LIB definition scoping rules are not modeled yet,
- later feature growth should revisit definition ownership explicitly rather
  than stretching the current table too far.

## Phase 2 As Implemented

The landed phase-2 implementation follows the same architectural split, but
the interfaces are now concrete rather than aspirational.

### `solver-core` now has transient assumptions plus persistent clause state

The backend layer now exposes both:

- a one-shot `solve_with_assumptions_and_budget(...)` entrypoint, and
- a persistent `IncrementalSolver` that keeps clauses, watch lists, variable
  scores, theory-atom registrations, and learned clauses across solves.

Repeated `solve` calls:

- backtrack to decision level zero before each call,
- apply assumptions as temporary decisions,
- preserve learned clauses when they are sound to keep,
- keep root-level permanent consequences available for future calls.

This gives `lower` the exact primitive it needs for frame activation.

### `lower` now owns one persistent backend session

`IncrementalBackend` in `crates/lower/src/lib.rs` is now the phase-2
counterpart to the old one-shot builder.

Its long-lived state includes:

```rust
struct IncrementalBackend {
    euf: EufSolver,
    sat: solver_core::IncrementalSolver,
    fun_map: HashMap<LowerFunSymbolId, FunId>,
    term_map: HashMap<LowerTermId, TermId>,
    bool_map: HashMap<LowerBoolSymbolId, BoolVar>,
    formula_cache: HashMap<LowerFormulaId, BoolValue>,
    theory_vars: HashMap<TheoryKey, BoolVar>,
    activation_vars: HashMap<ActivationLiteral, BoolVar>,
}
```

That means repeated `check-sat` now reuses:

- backend-local SAT variable numbering,
- backend-local EUF function ids,
- backend-local EUF term ids,
- lowered-formula Tseitin literals,
- theory-atom guard variables,
- the full SAT clause database,
- learned SAT clauses that survive the previous solve.

### Assertion insertion is now the real backend insertion point

After phase 2:

- `assert` still lowers once into persistent semantic IR,
- the lowered formula is immediately materialized into the persistent backend,
- later `check-sat` no longer rebuilds clause vectors, theory atoms, or the EUF
  term universe for already-inserted assertions,
- `check-sat` now primarily means “solve current backend under active frame
  assumptions”.

This is the intended end state for the current incremental command model.

## Ownership Model After Phase 2

The ownership split is now:

- `Solver`
  - owns the SMT-LIB command stack,
  - owns persistent IR,
  - decides which assertions are logically active.
- `IncrementalBackend`
  - owns backend-local SAT and EUF ids,
  - owns the growing clause database,
  - owns activation-literal variables,
  - owns the cached mapping from lowered ids to backend ids.

The key rule should remain:

- `Lower*Id` values are stable and backend-agnostic,
- `BoolVar`, `FunId`, and `TermId` remain backend-local,
- only the incremental backend may remember the mapping between them.

That keeps the layering explicit and avoids leaking backend instance identity
back into the command layer.

## Recommended Immediate Follow-Up

Phase 2 removes the large structural rebuild cost, so the next work should be
observability and backend-quality tuning rather than another architectural
split.

Recommended order now:

1. add timing or counters to split repeated `check-sat` cost into:
   SAT search, EUF checking, and assertion insertion,
2. measure whether retained learned clauses help materially on target
   incremental benchmarks,
3. inspect whether assumption-heavy solves need stronger conflict retention or
   assumption-core reporting,
4. revisit definition scoping only when the supported SMT-LIB fragment grows
   beyond the current zero-arity policy.
