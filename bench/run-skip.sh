#!/bin/sh

cargo bench --bench bench --features captures-baseline cap_ \
    | tee baseline.bench

cargo bench --bench bench --features captures-skip-pike cap_ \
    | tee skip-pike.bench

cargo bench --bench bench --features captures-skip-backtrack cap_ \
    | tee skip-backtrack.bench

echo ""
echo "==================== SKIP PIKE SPEEDUP ======================="
echo ""

cargo benchcmp baseline.bench skip-pike.bench

echo ""

echo ""
echo "================== SKIP BACKTRACK SPEEDUP ======================="
echo ""

cargo benchcmp baseline.bench skip-backtrack.bench

echo ""

echo ""
echo "============== SKIP BACKTRACK SPEEDUP OVER PIKE =================="
echo ""

cargo benchcmp skip-pike.bench skip-backtrack.bench
