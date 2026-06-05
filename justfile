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
bench *extra:\
  (sat-bench-fetch "--quiet") \
  (harness-run extra)

# recipe for perf recording. e.g. run with `just bench`, `timeout ...`, `cargo run ...`.
perf *args="":
    samply record --unstable-presymbolicate -- {{ args }}

# This project currently doesn't use nightly feature, so 1.95.0 hawk works; update after hawk supports nightly.
# due to https://github.com/astral-sh/hawk/issues/74, we need to clear `.rustc_info.json` first.
# `hawk` is aggressive, do not run after each change. instead, audit pub surface with `hawk` when user required.
hawk *extra:
    @rm -f target/.rustc_info.json
    @cargo +1.95.0 hawk {{ extra }}