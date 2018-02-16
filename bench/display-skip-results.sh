#!/bin/sh

set -euo pipefail
IFS=$'\n\t'

source ./skip-benchmarking-utils.sh

diff_features captures-baseline-pike captures-skip-pike-none
# diff_features captures-baseline-pike captures-skip-pike-ds
# diff_features captures-baseline-pike captures-skip-pike-es
# diff_features captures-baseline-pike captures-skip-pike-sl
# diff_features captures-baseline-pike captures-skip-pike-ds-es
# diff_features captures-baseline-pike captures-skip-pike-ds-sl
# diff_features captures-baseline-pike captures-skip-pike-es-sl
# diff_features captures-baseline-pike captures-skip-pike-ds-es-sl

diff_features captures-baseline-backtrack captures-skip-backtrack-none
diff_features captures-baseline-backtrack captures-skip-backtrack-ds
diff_features captures-baseline-backtrack captures-skip-backtrack-es
diff_features captures-baseline-backtrack captures-skip-backtrack-sl
diff_features captures-baseline-backtrack captures-skip-backtrack-ds-es
diff_features captures-baseline-backtrack captures-skip-backtrack-ds-sl
diff_features captures-baseline-backtrack captures-skip-backtrack-es-sl
diff_features captures-baseline-backtrack captures-skip-backtrack-ds-es-sl

diff_features captures-baseline-backtrack captures-skip-backtrack-validation
