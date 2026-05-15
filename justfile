# do not run `just --unstable --fmt --check`, which insists single line instead of backslash

set no-exit-message := true

# Runs the SAT harness with shared flags.
sat-harness-run *args="":
    @cargo run -p sat-harness --release -q -- run {{ args }}

# Fetches SAT benchmarks.
sat-bench-fetch *args="":
    @./scripts/fetch_sat_benchmarks.py {{ args }}

# Tests and benchmarks our SAT solver, default to hard subset.
bench argument="hard" *extra:\
  (sat-bench-fetch "--quiet") \
  (sat-harness-run \
    if argument == "full" {\
         "" \
    } else if argument == "hard" {\
        "test/fixture/sat/cases/satlib/engine_unsat_1.0" \
    } else {\
        error("unknown bench preset: " + argument) \
    } extra\
  )\

# Compares harness results before and after the current local changes.
compare argument="hard" *extra:
    @./scripts/bench_compare_stash.py --preset {{ argument }} {{ extra }}
