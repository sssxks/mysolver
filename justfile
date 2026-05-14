set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

perf:

sat-bench:
    cargo run --bin sat-harness -- run

sat-bench-fetch:
    ./scripts/fetch_sat_benchmarks.sh
