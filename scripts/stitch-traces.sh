#!/bin/bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

function stitch_traces {
  if [ "${1}" ]; then
    eval "declare -A USER_VARS="${1#*=}

    USER_VAR_STR=""
    for VAR in "${!USER_VARS[@]}"; do
      USER_VAR_STR="$USER_VAR_STR,$VAR=(w32 ${USER_VARS[$VAR]})"
    done

    USER_VAR_STR="$(echo "$USER_VAR_STR" | sed -e 's/^,//')"

    parallel "echo -n \$(basename {} .call_path)' '; \
              $SCRIPT_DIR/../build/bin/stitch-perf-contract \
                  -use-forked-solver=false \
                  -contract $SCRIPT_DIR/../../vigor/perf-contracts/perf-contracts.so \
                  --user-vars \"$USER_VAR_STR\" \
                  {} 2>/dev/null" ::: traces/*.call_path > traces/stateful-perf.txt
  else
    parallel "echo -n \$(basename {} .call_path)' '; \
              $SCRIPT_DIR/../build/bin/stitch-perf-contract \
                  -use-forked-solver=false \
                  -contract $SCRIPT_DIR/../../vigor/perf-contracts/perf-contracts.so \
                  {} 2>/dev/null" ::: traces/*.call_path > traces/stateful-perf.txt
  fi

  awk '
  {
    if ($2 < 0 || totals[$1] < 0) {
      totals[$1] = -1;
    } else {
      totals[$1] += $2;
    }
  }

  END {
    for (trace in totals) {
      print totals[trace];
    }
  }' traces/stateful-perf.txt traces/stateless-perf.txt \
    | sort -n | tail -n 1
}


declare -A USER_VARS=()

while [ "${1:-}" ]; do
  USER_VARS[$1]=$2
  shift 2
done

if [ ${#USER_VARS[@]} -gt 0 ]; then
  BASELINE_PERF=$(stitch_traces "$(declare -p USER_VARS)")
  echo $BASELINE_PERF

  for VAR in "${!USER_VARS[@]}"; do
    USER_VARS_STR=$(declare -p USER_VARS)
    eval "declare -A USER_VARS_VARIANT="${USER_VARS_STR#*=}
    USER_VARS_VARIANT["$VAR"]=$((${USER_VARS[$VAR]} + 1))

    VARIANT_PERF=$(stitch_traces "$(declare -p USER_VARS_VARIANT)")
    echo "$(($VARIANT_PERF - $BASELINE_PERF))/$VAR"
  done
else
  stitch_traces ""
fi
