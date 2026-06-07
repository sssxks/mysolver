# Incremental QF-UF Implementation Differences

This document tracks differences between the implementation and
`docs/incremental-qf-uf-design.md` that are currently intentional because the
design leaves a gap that code must resolve.

## Current Differences

### `EufTheory` stores a search-local atom assignment cache

The design document models the SAT/theory boundary with:

- `notify_assignment(lit)`,
- `notify_backtrack(level)`,
- queueing of pending theory literals.

That is enough to observe new assignments, but it is not enough by itself for
`evaluate_atom_trigger()` to answer whether a theory atom is currently:

- assigned true,
- assigned false,
- or still unassigned.

Current implementation choice:

- `EufTheory` additionally keeps:
  - `atom_value: Vec<Option<bool>>`
  - `atom_trail: Vec<TheoryAtom>`
  - `atom_trail_lim: Vec<usize>`

These fields are updated by `notify_assignment()` / `notify_backtrack()` and are
used by trigger evaluation to distinguish propagation from conflict.

Why this is a design gap:

- the design explicitly questioned whether EUF should read SAT assignment state
  directly or keep a cache,
- but the pseudocode did not include a concrete cache structure,
- while the current `Theory` trait also does not expose direct read access to
  SAT assignments.

What would remove this difference:

- either make the cache part of the documented design,
- or extend the SAT/theory API with a direct way for EUF to query current atom
  assignment state.
