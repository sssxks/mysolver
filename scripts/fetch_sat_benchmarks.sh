#!/usr/bin/env bash
set -euo pipefail

profile="smoke"
dest="test/fixture/sat"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --profile)
            profile="$2"
            shift 2
            ;;
        --dest)
            dest="$2"
            shift 2
            ;;
        *)
            echo "unknown argument: $1" >&2
            exit 2
            ;;
    esac
done

case "$profile" in
    smoke|core|full)
        ;;
    *)
        echo "unsupported profile: $profile" >&2
        exit 2
        ;;
esac

archives_dir="$dest/upstream"
cases_dir="$dest/cases"
manifest_path="$dest/expectations.tsv"

mkdir -p "$archives_dir" "$cases_dir/satlib" "$cases_dir/vlsat"

download_file() {
    local url="$1"
    local out="$2"

    if [[ -f "$out" ]]; then
        printf 'cached  %s\n' "$out"
        return
    fi

    printf 'fetch   %s\n' "$url"
    curl --fail --location --progress-bar --output "$out" "$url"
}

extract_tarball() {
    local archive="$1"
    local out_dir="$2"

    if [[ -d "$out_dir" ]] && find "$out_dir" -mindepth 1 -print -quit >/dev/null; then
        printf 'ready   %s\n' "$out_dir"
        return
    fi

    mkdir -p "$out_dir"
    printf 'extract %s\n' "$archive"
    tar -xzf "$archive" -C "$out_dir"
}

write_manifest() {
    cat >"$manifest_path" <<'EOF'
# prefix	expected	source
cases/satlib/uf20-91/	sat	SATLIB RND3SAT uf20-91
cases/satlib/uuf50-218/	unsat	SATLIB RND3SAT uuf50-218
cases/satlib/uf100-430/	sat	SATLIB RND3SAT uf100-430
cases/satlib/engine_unsat_1.0/	unsat	SATLIB I-Velev03 engine_unsat_1.0
cases/vlsat/vlsat1_9588_392364.cnf.bz2	sat	CADP VLSAT-1 vlsat1_9588_392364
cases/vlsat/vlsat1_15498_838393.cnf.bz2	sat	CADP VLSAT-1 vlsat1_15498_838393
EOF

    if [[ "$profile" == "core" || "$profile" == "full" ]]; then
        cat >>"$manifest_path" <<'EOF'
cases/satlib/uuf100-430/	unsat	SATLIB RND3SAT uuf100-430
cases/satlib/vliw_unsat_3.0/	unsat	SATLIB I-Velev03 vliw_unsat_3.0
EOF
    fi

    if [[ "$profile" == "full" ]]; then
        cat >>"$manifest_path" <<'EOF'
cases/satlib/pipe_sat_1.0/	sat	SATLIB I-Velev03 pipe_sat_1.0
cases/satlib/pipe_unsat_1.0/	unsat	SATLIB I-Velev03 pipe_unsat_1.0
EOF
    fi
}

fetch_random_suite() {
    local suite="$1"
    local url="https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/${suite}.tar.gz"
    local archive="$archives_dir/${suite}.tar.gz"
    local out_dir="$cases_dir/satlib/${suite}"
    download_file "$url" "$archive"
    extract_tarball "$archive" "$out_dir"
}

fetch_velev_suite() {
    local suite="$1"
    local url="https://www.cs.ubc.ca/~hoos/SATLIB/I-Velev03/${suite}.tar.gz"
    local archive="$archives_dir/${suite}.tar.gz"
    local out_dir="$cases_dir/satlib/${suite}"
    download_file "$url" "$archive"
    extract_tarball "$archive" "$out_dir"
}

fetch_vlsat_case() {
    local case_name="$1"
    local url="https://cadp.inria.fr/ftp/benchmarks/vlsat/${case_name}.cnf.bz2"
    local out="$cases_dir/vlsat/${case_name}.cnf.bz2"
    download_file "$url" "$out"
}

fetch_random_suite "uf20-91"
fetch_random_suite "uuf50-218"
fetch_random_suite "uf100-430"
fetch_velev_suite "engine_unsat_1.0"
fetch_vlsat_case "vlsat1_9588_392364"
fetch_vlsat_case "vlsat1_15498_838393"

if [[ "$profile" == "core" || "$profile" == "full" ]]; then
    fetch_random_suite "uuf100-430"
    fetch_velev_suite "vliw_unsat_3.0"
fi

if [[ "$profile" == "full" ]]; then
    fetch_velev_suite "pipe_sat_1.0"
    fetch_velev_suite "pipe_unsat_1.0"
fi

write_manifest

printf '\nbenchmarks ready under %s\n' "$dest"
