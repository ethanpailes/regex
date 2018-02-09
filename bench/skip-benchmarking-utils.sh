bench_feature () {
    local _feature=${1}
    local _filter=${2}
    echo ">>> RUNNING WITH FEATURE: ${_feature}"

    cargo bench --bench bench --features ${_feature} ${_filter} | tee ${_feature}.bench
}

diff_features () {
    local _feature_1=${1}
    local _feature_2=${2}

    echo ""
    echo ">>> SPEEDUP: ${_feature_1} ==> ${_feature_2} "
    echo ""

    cargo benchcmp ${_feature_1}.bench ${_feature_2}.bench
}
