#!/bin/sh

set -euo pipefail
IFS=$'\n\t'

if [ -z ${1+x} ]; then
    FILTER=cap_
else
    FILTER=$1
fi

source ./skip-benchmarking-utils.sh

bench_feature captures-baseline-pike ${FILTER}
bench_feature captures-baseline-backtrack ${FILTER}

bench_feature captures-skip-pike-none ${FILTER}
# bench_feature captures-skip-pike-ds ${FILTER}
# bench_feature captures-skip-pike-es ${FILTER}
# bench_feature captures-skip-pike-sl ${FILTER}
# bench_feature captures-skip-pike-ds-es ${FILTER}
# bench_feature captures-skip-pike-ds-sl ${FILTER}
# bench_feature captures-skip-pike-es-sl ${FILTER}
# bench_feature captures-skip-pike-ds-es-sl ${FILTER}

bench_feature captures-skip-backtrack-none ${FILTER}
bench_feature captures-skip-backtrack-ds ${FILTER}
bench_feature captures-skip-backtrack-es ${FILTER}
bench_feature captures-skip-backtrack-sl ${FILTER}
bench_feature captures-skip-backtrack-ds-es ${FILTER}
bench_feature captures-skip-backtrack-ds-sl ${FILTER}
bench_feature captures-skip-backtrack-es-sl ${FILTER}
bench_feature captures-skip-backtrack-ds-es-sl ${FILTER}
