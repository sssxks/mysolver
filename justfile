# do not run `just --unstable --fmt --check`, which insists single line instead of backslash

set no-exit-message := true

# Runs the harness with shared flags.
harness-run *args="":
    @cargo run -p my-harness --release -q -- run {{ args }}

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

# recipe for perf recording. e.g. run with `timeout ...`, `cargo run ...`. use `--profile perf` to build the harness with perf instrumentation.
perf *args="":
    samply record --unstable-presymbolicate -- {{ args }}

@dead-pub:
    # cargo install has to update index, causing a little lag even when installed, seems not very ideal.
    cargo install cargo-workspace-unused-pub -q
    # rustup is fine.
    rustup component add rust-analyzer > /dev/null 2>&1
    # also the `cargo-workspace-unused-pub` tool is poorly implemented, quite slow.
    -RUST_LOG=off cargo workspace-unused-pub
    rm -f index.scip
    