# do not run `just --unstable --fmt --check`, which insists single line instead of backslash
set no-exit-message := true

# Runs the SAT harness with shared flags.
_sat-harness-run *args="":
    @cargo run -p sat-harness --release -q -- run {{ args }}

# Tests and benchmarks our SAT solver, default to hard subset.
bench argument="hard" *extra:\
  (sat-bench-fetch "--quiet") \
  (_sat-harness-run extra \
    if argument == "full" {\
         "" \
    } else if argument == "hard" {\
        "test/fixture/sat/cases/satlib/engine_unsat_1.0" \
    } else {\
        error("unknown bench preset: " + argument) \
    }\
  )\

sat-bench-fetch *args="":
    @./scripts/fetch_sat_benchmarks.sh {{ args }}
