set no-exit-message

bench argument="hard" *extra:
    @if [ "{{argument}}" = "simple" ]; then cargo run -p sat-harness --release -q -- run {{extra}}; elif [ "{{argument}}" = "hard" ]; then cargo run -p sat-harness --release -q -- run {{extra}} test/fixture/sat/cases/satlib/engine_unsat_1.0; else echo "unknown bench preset: {{argument}}" >&2; exit 1; fi

sat-bench-fetch:
    @./scripts/fetch_sat_benchmarks.sh
