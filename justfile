set no-exit-message

bench argument="hard":
    @if [ "{{argument}}" = "simple" ]; then cargo run -p sat-harness -q -- run; elif [ "{{argument}}" = "hard" ]; then cargo run -p sat-harness -q -- run test/fixture/sat/cases/satlib/engine_unsat_1.0; else echo "unknown bench preset: {{argument}}" >&2; exit 1; fi

sat-bench-fetch:
    @./scripts/fetch_sat_benchmarks.sh
