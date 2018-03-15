#!/bin/sh

set -euo pipefail
IFS=$'\n\t'

source ./skip-benchmarking-utils.sh

FEATURES=(
  "captures-baseline-backtrack"
  "captures-skip-backtrack-none"
)

SCALING_FACTORS=(
  "10"
  "1000"
  "2000"
  "3000"
  "4000"
  "5000"
  "6000"
  "7000"
  "8000"
  "9000"
  "10000"
  "11000"
  "12000"
  "13000"
  "14000"
  "15000"
)

if [ -z ${1+x} ]; then
    FILTER=cap_
else
    if [[ x$1 == "x--no-regen" ]]; then
      python3 graph-sfs.py ${SCALING_FACTORS[@]}
      exit 0
    else
      FILTER=$1
    fi
fi

echo "GENERATING THE RAW BENCHMARK DATA"
for feature in ${FEATURES[@]}
do
  for scaling_factor in ${SCALING_FACTORS[@]}
  do
    echo ">>> scaling_factor=${scaling_factor}"

    SKIP_RE_BENCH_SCALE=${scaling_factor} \
      cargo bench --bench bench --features ${feature} ${FILTER} |\
      tee ${scaling_factor}-${feature}.bench
  done
done

echo "POST BENCHMARK DATA MUNGING"
for scaling_factor in ${SCALING_FACTORS[@]}
do
  echo ">>> scaling_factor=${scaling_factor}"
  echo -n "converting the results to csv format...  "
  for feature in ${FEATURES[@]}
  do
    csv_file="${scaling_factor}-${feature}.bench.csv"

    echo "scaling_factor,test_name,${feature}_time,${feature}_error" > ${csv_file}

    cat ${scaling_factor}-${feature}.bench | \
      rg "^test ([a-zA-Z:_]+) +... bench: +([0-9,]+) ns/iter \(\+/\- ([0-9,]+)\).*$"\
         --replace "${scaling_factor},\$1,\"\$2\",\"\$3\"" >> \
      ${csv_file}
  done
  echo "[ OK ]"

  # I realized that this is bad relational thinking after I wrote the
  # script. I really should have just put the feature in a column.
  # Sorry :(.
  echo -n "joining the csv files...  "
  rollup_csv_file=${scaling_factor}.bench.csv
  cp ${scaling_factor}-${FEATURES[0]}.bench.csv ${rollup_csv_file}
  for feature in ${FEATURES[@]:1}
  do
    csv_file="${scaling_factor}-${feature}.bench.csv"

    xsv join test_name,scaling_factor ${rollup_csv_file} \
        test_name,scaling_factor ${csv_file} |\
      xsv select '!test_name[1],scaling_factor[1]' > tmp.bench.csv
    mv tmp.bench.csv ${rollup_csv_file}
  done
  echo "[ OK ]"

done

python3 graph-sfs.py ${SCALING_FACTORS[@]}
