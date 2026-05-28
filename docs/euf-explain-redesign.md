# EUF Explain Redesign

## Context

`crates/euf/src/explain.rs` currently explains one equality by:

- allocating a fresh `parents: Vec<Option<usize>>` sized to all terms,
- running a BFS that, for each popped node, linearly scans the entire active
  `edges` vector,
- recursively repeating the same procedure for congruence justifications.

This design is simple, but it has the wrong asymptotic shape for a hot path.
The current `profile.json.gz` in the repository shows
`SearchState::collect_equality_explanation` dominating self time.

The important observation from cvc5 is not its proof object layer. The useful
part to copy is the equality-graph representation used for explanation:

- every merge inserts an undirected proof edge into a per-node adjacency list,
- backtracking truncates the edge storage,
- explanation BFS walks only incident edges,
- recursive sub-explanations share one per-query cache.

This document describes a redesign that copies that part and leaves proof
production out of scope.

## Goal

Reduce explanation cost from "repeated full scans of all active merge edges" to
"walk the relevant explanation subgraph only", while preserving:

- current SAT/theory interface,
- SAT-level rollback behavior,
- current explanation semantics,
- current congruence-based recursive justification model.

## Non-Goals

- Do not introduce proof objects like cvc5's `EqProof`.
- Do not try to minimize explanations.
- Do not add redundant equality edges for shortest explanations.
- Do not redesign congruence closure itself.
- Do not change the theory clause API between `euf` and `sat`.

## Current Problem

Today the explanation path has three coupled costs:

1. Global edge scans.
   `collect_equality_explanation()` scans every active edge for every BFS pop.

2. Per-call allocation and growth.
   Each explanation allocates a fresh `parents` vector and a fresh queue.

3. Recursive recomputation.
   Congruence edges recursively explain argument equalities without a cache, so
   one query can recompute the same pair multiple times.

The result is a cost shape closer to:

- one explanation query: `O(number_of_visited_nodes * active_edges)`,
- recursive explanation: repeated copies of the above.

That is the wrong side of the performance boundary for theory propagation and
conflict explanation.

## Recommended Design

Replace the current `edges: Vec<MergeEdge>` proof graph with a rollback-friendly
adjacency-list representation.

The redesign has three pieces:

1. Proof-edge storage:
   store every active equality justification as two directed adjacency entries.

2. Search-local explanation scratch:
   keep reusable BFS state and per-query memoization inside `SearchState`.

3. Query-local explanation driver:
   one `explain_equality()` call owns the cache, scratch reset, path recovery,
   duplicate suppression, and recursive descent over congruence edges.

## Complexity Contract

| Operation | Frequency | Complexity | Data structure | Forbidden Impl |
| - | - | - | - | - |
| Add one proof edge for an input equality or congruence merge | high | `O(1)` | head-insert adjacency list in `Vec<ProofEdge>` | appending only to a flat edge list with no incident index |
| Roll back proof edges to a SAT level | high | `O(number_of_edges_popped)` | truncate `Vec<ProofEdge>` and restore per-node heads | scanning all surviving edges to rebuild adjacency |
| BFS frontier expansion during one explanation query | high | `O(sum of visited out-degrees)` | per-node adjacency walk | scanning all active edges for every popped node |
| Recover one path after BFS | high | `O(path_length)` | predecessor edge array | re-running search to reconstruct the path |
| Re-explain one previously seen pair during the same top-level query | medium | amortized `O(1)` skip | query-local pair cache | recursively recomputing the same pair |
| Emit final SAT premises for one explanation | high | `O(number_of_premises)` | flat `Vec<Lit>` plus seen set | repeated linear duplicate checks on large outputs |

## Data Model

### Existing semantic model

Semantically, the explanation state is:

- a set of active terms,
- a set of active justified equalities between terms,
- a rollback boundary per SAT level,
- enough information to recover a conjunction of input literals that implies
  one requested equality or conflict.

The current encoding stores active justified equalities as a flat list of
undirected edges. The redesign changes only the encoding, not the semantics.

### New search-local types

The implementation should introduce newtypes instead of raw `usize` indexes.

Suggested sketch:

```rust
pub struct ProofEdgeId(u32);

pub struct ExplainStamp(u32);
```

Suggested edge payload:

```rust
pub struct ProofEdge {
    to: TermId,
    next: Option<ProofEdgeId>,
    reason: MergeReason,
}
```

Suggested `SearchState` additions:

```rust
proof_edge_head: Vec<Option<ProofEdgeId>>,
proof_edges: Vec<ProofEdge>,

explain_seen_stamp: Vec<u32>,
explain_pred_edge: Vec<Option<ProofEdgeId>>,
explain_queue: Vec<TermId>,
explain_queue_head: usize,
explain_epoch: u32,

explain_pair_cache: hashbrown::HashSet<(TermId, TermId)>,
explain_output_seen: hashbrown::HashSet<Lit>,
path_scratch: Vec<ProofEdgeId>,
```

Notes:

- `proof_edge_head[t]` is the head of `t`'s incident adjacency list.
- Each undirected merge inserts two directed `ProofEdge`s.
- `proof_edges.len()` is always even.
- `proof_edges[i ^ 1]` is the reverse direction of `proof_edges[i]`.
- `explain_seen_stamp` avoids clearing a `Vec<bool>` or `Vec<Option<_>>` on
  every query.
- `explain_pair_cache` is per top-level explanation query, not persistent
  across SAT search.
- `explain_output_seen` deduplicates premises before building the theory clause.

## Encoding Invariants

- `proof_edge_head.len() == registry.num_terms()`.
- Every active proof edge is reachable from exactly one node head and has a
  reverse edge at `id ^ 1`.
- If a proof edge `e` is active, then its reverse edge is also active.
- `proof_edges` contains only edges from the active SAT-level prefix.
- On rollback, all heads referring to popped edges are restored to the
  previous `next` pointer value before truncation.
- `MergeReason::InputEq` stores one SAT literal that may appear directly in the
  final explanation.
- `MergeReason::Congruence` stores the two parent terms whose argument
  equalities justify the merge.
- One top-level explanation query must not recursively expand the same
  canonicalized pair twice.

## SAT-Level Rollback

The current rollback marker already stores `merge_edges_len`. Replace that with
`proof_edges_len`.

On push:

- save `proof_edges.len()`.

On pop to marker:

1. Walk edge ids from `proof_edges.len() - 2` down to `marker.proof_edges_len`
   in reverse insertion order.
2. For each directed pair `(fwd, rev)`:
   - restore the source endpoint head of `fwd` to `proof_edges[fwd].next`,
   - restore the source endpoint head of `rev` to `proof_edges[rev].next`,
   - then truncate `proof_edges`.

Because each reverse edge stores the opposite endpoint in its `to` field, the
source endpoints can be recovered without storing them twice:

- source(`fwd`) = `proof_edges[rev].to`,
- source(`rev`) = `proof_edges[fwd].to`.

Because insertion is always head insertion, rollback never needs to inspect
surviving edges.

This is the main cvc5 idea worth copying: insertion and rollback are both local
pointer rewrites plus truncation.

## Query Algorithm

### Top-level flow

`explain_equality(lhs, rhs, out)` should:

1. clear `out`,
2. increment the explanation epoch,
3. clear the pair cache,
4. clear the output-seen set,
5. call `collect_pair(lhs, rhs, out)`.

`explain_conflict(diseq, out)` should:

1. run the same top-level setup,
2. collect the equality explanation for `(diseq.lhs, diseq.rhs)`,
3. append `diseq.reason_lit` once if not already present.

### Pair collection

`collect_pair(lhs, rhs, out)` should:

1. return immediately if `lhs == rhs`,
2. canonicalize the pair by term index order,
3. return if that pair is already in `explain_pair_cache`,
4. BFS from `lhs` to `rhs` using only `proof_edge_head` and `proof_edges`,
5. reconstruct the found path into `path_scratch`,
6. walk the path in order:
   - `InputEq { reason_lit }`: add `reason_lit` if unseen,
   - `Congruence { left_parent, right_parent }`: for each argument pair,
     recurse on `(left_arg, right_arg)`.

Canonicalization is important even though explanations are symmetric in the
current Rust design. It avoids re-explaining `(a, b)` and `(b, a)` separately
inside one top-level query.

### BFS details

The BFS should be allocation-free after `reset_for_registry()`:

- `explain_queue.clear()`,
- `explain_queue_head = 0`,
- push `lhs`,
- stamp `lhs` with the current epoch,
- while `explain_queue_head < explain_queue.len()`:
  - pop `current`,
  - iterate `edge_id = proof_edge_head[current]`,
  - follow `next` pointers through incident edges only,
  - when first visiting `next_term`, record `pred_edge[next_term] = edge_id`,
    stamp it, and push it,
  - stop once `rhs` is discovered.

Path reconstruction walks `pred_edge` from `rhs` back to `lhs`.

## Why This Is Enough

This redesign fixes the current hotspot without changing the theory boundary.

It preserves:

- the existing `MergeReason` enum,
- recursive congruence explanation,
- the current propagation and conflict building code,
- rollback aligned with SAT decision levels.

It removes the expensive parts:

- no full scan of all active proof edges during BFS,
- no per-call `parents = vec![..num_terms..]`,
- no repeated pair expansion inside one top-level explanation,
- no repeated duplicate literals in the final clause.

## Why Not Copy More From cvc5

### Not now: proof objects

cvc5 can optionally build `EqProof` objects while explaining. We do not need
that to solve the current performance problem.

Adding proof objects now would:

- complicate the API,
- increase memory pressure,
- make rollback reasoning harder,
- solve a problem we do not currently have.

### Not now: shortest explanations

Recent cvc5 work on shorter congruence-closure proofs keeps redundant equality
edges and searches for shorter weighted paths. That targets proof size, not the
main hotspot we have today.

It would also change the proof graph from a tree-shaped merge history to a more
general graph where:

- there can be many competing explanation paths,
- edge weights may need recomputation,
- query behavior becomes more complex under backtracking.

That is a valid future direction, but it is not the first move.

## Migration Plan

1. Introduce the new proof-edge storage next to the current `edges` storage.
   Keep behavior unchanged while validating insertion and rollback.

2. Switch explanation BFS to the adjacency representation.
   Keep recursive congruence explanation unchanged.

3. Add query-local pair memoization and output deduplication.

4. Delete the old flat `edges` traversal implementation.

5. Re-profile on the same benchmark and compare:
   - self samples in explanation,
   - number of allocations during explanation,
   - total solver time.

## Expected Outcome

After this redesign, explanation cost should scale with the part of the proof
graph actually touched by the query, not with the full active merge history.

The expected qualitative result is:

- `collect_equality_explanation` stops dominating self time,
- propagation and conflict explanation become proportional to local proof size,
- SAT search can afford more theory explanations before EUF becomes the main
  bottleneck again.

## Open Questions

- Whether `explain_pair_cache` should store ordered or canonicalized unordered
  pairs. Current recommendation: canonicalized unordered pairs.
- Whether `explain_output_seen` should be a hash set or a stamp table keyed by
  SAT variable plus polarity. Current recommendation: start with a hash set and
  only specialize if it shows up in profiles.
- Whether to keep a separate `path_scratch` or reuse part of the queue buffer.
  Current recommendation: keep it separate for simpler reasoning.

## Rejected Alternatives

### Keep the flat edge list and add only memoization

Rejected because the dominant cost is the global scan inside BFS. Memoization
helps recursive overlap, but it does not fix the wrong primary complexity term.

### Maintain one explanation parent forest instead of an adjacency graph

Rejected as the first step because it is more invasive and less obviously
compatible with current congruence-driven recursive justification. It may still
be a good second-stage optimization if adjacency-list BFS remains visible.

### Cache complete explanations across SAT states

Rejected because SAT backtracking changes the active proof-edge prefix. Any
cross-query persistent cache would need complicated invalidation logic and would
be easy to make unsound.
