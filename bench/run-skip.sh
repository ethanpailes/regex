#!/bin/sh

set -euo pipefail
IFS=$'\n\t'

if [ -z ${1+x} ]; then
    FILTER=cap_
else
    FILTER=$1
fi

cargo bench --bench bench --features captures-baseline-pike ${FILTER} \
    | tee baseline-pike.bench

cargo bench --bench bench --features captures-baseline-backtrack ${FILTER} \
    | tee baseline-backtrack.bench

cargo bench --bench bench --features captures-skip-pike ${FILTER} \
    | tee skip-pike.bench

cargo bench --bench bench --features captures-skip-backtrack ${FILTER} \
    | tee skip-backtrack.bench

echo ""
echo "==================== SKIP PIKE SPEEDUP ======================="
echo ""

cargo benchcmp baseline-pike.bench skip-pike.bench

echo ""

echo ""
echo "================== SKIP BACKTRACK SPEEDUP ======================="
echo ""

cargo benchcmp baseline-backtrack.bench skip-backtrack.bench

echo ""

echo ""
echo "============== SKIP BACKTRACK SPEEDUP OVER PIKE =================="
echo ""

cargo benchcmp skip-pike.bench skip-backtrack.bench
