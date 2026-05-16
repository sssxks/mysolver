# `engine_unsat_1.0` Solver Attempts

Date: 2026-05-17

Commands used:

```bash
cargo run -p sat-harness --release -q -- run test/fixture/sat/cases/satlib/engine_unsat_1.0 --all --jobs 4
cargo run -p sat-harness --release -q -- run test/fixture/sat/cases/satlib/engine_unsat_1.0/engine_5.cnf.gz --all --jobs 1 --timeout 120s
cargo run -p sat-harness --release -q -- run test/fixture/sat/cases/satlib/engine_unsat_1.0/engine_6.cnf.gz --all --jobs 1 --timeout 120s
timeout 35s /tmp/minisat/build/release/bin/minisat test/fixture/sat/cases/satlib/engine_unsat_1.0/engine_5.cnf.gz /tmp/engine5.out
timeout 35s /tmp/minisat/build/release/bin/minisat test/fixture/sat/cases/satlib/engine_unsat_1.0/engine_6.cnf.gz /tmp/engine6.out
```

## Baseline

Initial solver result on `engine_unsat_1.0`:

- Pass `4/10`
- Passed cases:
  - `engine_4.cnf.gz` in `2.73s`
  - `engine_4_nd.cnf.gz` in `10.84s`
  - `engine_5_case1.cnf.gz` in `1.12s`
  - `engine_5_nd_case1.cnf.gz` in `9.59s`
- Timed out:
  - `engine_5.cnf.gz`
  - `engine_5_nd.cnf.gz`
  - `engine_6.cnf.gz`
  - `engine_6_case1.cnf.gz`
  - `engine_6_nd.cnf.gz`
  - `engine_6_nd_case1.cnf.gz`

Longer single-case runs showed that baseline search quality was the main limiter, not just a small constant-factor issue:

- `engine_5.cnf.gz` still timed out at `120s`
- `engine_6.cnf.gz` still timed out at `120s`

External reference using a locally built `minisat` was also unable to finish the hard cases in `35s`:

- `engine_5.cnf.gz`: `INDETERMINATE` after `34.79s`
- `engine_6.cnf.gz`: `INDETERMINATE` after `34.84s`

That made `5/10` or better a realistic target, rather than expecting all `engine_5/6` cases to fall quickly.

## Attempt 1: Luby Restarts

Change:

- Replaced the geometric restart growth with a Minisat-style Luby schedule.

Result:

- Rejected.
- Full-suite result regressed from `4/10` to `3/10`.
- Restart count exploded into the hundreds on easier cases and previously passing instances slowed down substantially.

## Attempt 2: Learned-Clause Minimization

Change:

- Added recursive learned-clause minimization after first-UIP analysis.
- Memoized redundancy checks inside one conflict analysis to keep the minimization pass cheap enough.

Result:

- Kept as part of the final solution.
- Solved count stayed at `4/10`, but passed cases became materially faster:
  - `engine_4.cnf.gz`: `2.73s -> 1.86s`
  - `engine_5_nd_case1.cnf.gz`: `9.59s -> 6.21s`
- This improved clause quality enough to justify keeping it even before it increased solved count on its own.

## Attempt 3: Keep Short Learned Clauses During Reduction

Change:

- Protected learned long clauses of length `<= 6` from reduction.
- Kept the existing activity-based reduction order, with clause length as a tie-breaker.

Result:

- Kept as part of the final solution.
- Full-suite result improved from `4/10` to `5/10`.
- Newly solved case:
  - `engine_6_case1.cnf.gz` in `13.52s`
- Remaining passing cases also improved:
  - `engine_4.cnf.gz`: `2.73s -> 1.40s`
  - `engine_4_nd.cnf.gz`: `10.84s -> 7.79s`
  - `engine_5_case1.cnf.gz`: `1.12s -> 1.07s`
  - `engine_5_nd_case1.cnf.gz`: `9.59s -> 4.77s`

## Attempt 4: Prefer Deleting Longer Clauses Before Low-Activity Ones

Change:

- Changed learned-clause reduction to prioritize deleting longer clauses before considering activity.

Result:

- Rejected.
- Targeted reruns on the blocking cases got worse:
  - `engine_5.cnf.gz`: still timed out, with more conflicts and propagations than Attempt 3
  - `engine_5_nd.cnf.gz`: still timed out, with more conflicts and propagations than Attempt 3

## Final Result

Final retained changes:

- Recursive learned-clause minimization in conflict analysis.
- Reduction policy that protects short learned clauses up to length `6`.

Final solver result on `engine_unsat_1.0`:

- Pass `5/10`
- Passed cases:
  - `engine_4.cnf.gz` in `1.40s`
  - `engine_4_nd.cnf.gz` in `7.79s`
  - `engine_5_case1.cnf.gz` in `1.07s`
  - `engine_5_nd_case1.cnf.gz` in `4.77s`
  - `engine_6_case1.cnf.gz` in `13.52s`
- Timed out:
  - `engine_5.cnf.gz`
  - `engine_5_nd.cnf.gz`
  - `engine_6.cnf.gz`
  - `engine_6_nd.cnf.gz`
  - `engine_6_nd_case1.cnf.gz`
