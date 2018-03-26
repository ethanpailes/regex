#!/bin/sh

set -euo pipefail
IFS=$'\n\t'

source ./skip-benchmarking-utils.sh

if ! [ -z ${1+x} ] ; then
  if [[ "x--no-regen" == x$1 ]] ; then
    NO_REGEN=yes
  fi
fi

RESOURCE_DIR=$HOME/repos/lazy-regex/evaluation/resources

A_BIG_SKIP_FEATURES=(
  "captures-baseline-backtrack"
  "captures-skip-backtrack-ds-es-sl"
  "captures-skip-backtrack-ds-es"
  "captures-skip-pike-ds-es-sl"
)

LEADING_DOTSTAR_FEATURES=(
  "captures-baseline-backtrack"
  "captures-skip-backtrack-ds-es-sl"
  "captures-skip-pike-ds-es-sl"
  "captures-skip-backtrack-es-sl"
)

DOTSTAR_BOUNCE=(
  "captures-baseline-backtrack"
  "captures-skip-backtrack-ds-es-sl"
  "captures-skip-backtrack-es-sl"
)

LEADING_NONCONTAINING_ESTAR=(
  "captures-baseline-backtrack"
  "captures-skip-backtrack-ds-es-sl"
  "captures-skip-pike-ds-es-sl"
  "captures-skip-backtrack-ds-sl"
)

PATHOLOGICAL=(
  "captures-baseline-backtrack"
  "captures-baseline-pike"
  "captures-skip-backtrack-ds-es-sl"
)

JUSTTWO_BRANCH=(
  "captures-baseline-backtrack"
  "captures-baseline-pike"
  "captures-skip-backtrack-ds-es-sl"
  "captures-skip-pike-ds-es-sl"
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

csv_file="bench.csv"

function gen_data_points() {
  FILTER=$1
  shift
  FEATURES=($@)

  if [ -z ${NO_REGEN+x} ]; then
    echo "GENERATING THE RAW BENCHMARK DATA"
    for feature in ${FEATURES[@]}
    do
      for scaling_factor in ${SCALING_FACTORS[@]}
      do
        echo ">>> scaling_factor=${scaling_factor} feature=${feature}"

        set +e
        SKIP_RE_BENCH_SCALE=${scaling_factor} \
          cargo bench --bench bench --features ${feature} ${FILTER} |\
          tee ${scaling_factor}-${feature}.bench
        set -e
      done
    done
  fi 

  echo "POST BENCHMARK DATA MUNGING"
  echo "converting the results to csv format...  "
  for scaling_factor in ${SCALING_FACTORS[@]}
  do
    echo ">>> scaling_factor=${scaling_factor}"
    for feature in ${FEATURES[@]}
    do
      echo "    > feature=${feature}"

      $(cat ${scaling_factor}-${feature}.bench | \
        rg "^test ([a-zA-Z:_]+) +... bench: +([0-9,]+) ns/iter \(\+/\- ([0-9,]+)\).*$"\
           --replace "${scaling_factor},${feature},\$1,\"\$2\",\"\$3\"" >> \
        ${csv_file} || true)
    done
  done
  echo "    [ OK ]"

}

# write the csv headers
echo "scaling_factor,feature,test_name,time,error" > ${csv_file}

gen_data_points cap_a_big_skip ${A_BIG_SKIP_FEATURES[@]}
gen_data_points cap_leading_dotstar ${LEADING_DOTSTAR_FEATURES[@]}
gen_data_points cap_leading_noncontaining_estar ${LEADING_NONCONTAINING_ESTAR[@]}
gen_data_points cap_dotstar_bounce ${DOTSTAR_BOUNCE[@]}
gen_data_points cap_justtwo_branch ${JUSTTWO_BRANCH[@]}

# split the benchmark data up by test
tests=$(xsv select test_name ${csv_file} | tail -n +2 | awk '!a[$0]++')
for t in ${tests[@]}
do
  xsv search -s test_name "${t}" ${csv_file} > ${t}.csv
done

python3 graph-sfs.py ${tests[@]}
cp *.png ${RESOURCE_DIR}
