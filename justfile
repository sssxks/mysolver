set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

perf subset="4" seed="1" filter="" output="target/flamegraph/qf-uf-archive-random-subset.svg":
    mkdir -p "$(dirname "{{ output }}")"
    {{ if filter != "" { "QF_UF_FILTER='" + filter + "' " } else { "" } }}CARGO_PROFILE_RELEASE_DEBUG=true QF_UF_RANDOM_SUBSET="{{ subset }}" QF_UF_RANDOM_SEED="{{ seed }}" cargo flamegraph --package lower --test qf_uf --output "{{ output }}" -- qf_uf_archive_random_subset --exact --nocapture
