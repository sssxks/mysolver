# do not run `just --unstable --fmt --check`, which insists single line instead of backslash

set no-exit-message := true

# Runs the harness with shared flags.
harness-run *args="":
    @cargo run -p sat-harness --release -q -- run {{ args }}

# Fetches SAT benchmarks.
sat-bench-fetch *args="":
    @./scripts/fetch_sat_benchmarks.py {{ args }}

# Fetches SMT-LIB benchmarks.
smt-bench-fetch *args="":
    @./scripts/fetch_smt_benchmarks.py {{ args }}

# Tests and benchmarks our SAT solver, default to hard subset.
bench preset="hard" *extra:\
  (sat-bench-fetch "--quiet") \
  (harness-run \
    if preset == "full" {\
         "" \
    } else if preset == "hard" {\
        "test/fixture/sat/cases/satlib/engine_unsat_1.0" \
    } else {\
        error("unknown bench preset: " + preset) \
    } extra\
  )\

# Compares harness results before and after the current local changes.
compare argument="hard" *extra:
    @./scripts/bench_compare_stash.py --preset {{ argument }} {{ extra }}

# Run this recipe via `perf record` or `samply record`
perf:
    @cargo run -p my-harness --profile perf -q -- run "test/fixture/sat/cases/satlib/engine_unsat_1.0" --all
