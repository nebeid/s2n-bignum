#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
reps=${1:-160}
processes=${2:-7}
core=${3:-3}
host=$(hostname)

for layout in entry-first hybrid-first; do
  out="results/entry-compare-$layout-$host.log"
  : > "$out"
  {
    echo "# date=$(date -u +%FT%TZ)"
    echo "# host=$host"
    echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
    echo "# layout=$layout reps=$reps processes=$processes pinned_cpu=$core"
    cat results/entry-compare-objects.csv
  } >> "$out"
  for process in $(seq 1 "$processes"); do
    taskset -c "$core" "./bench-$layout" "$reps" "$process" \
      entry shared-helper >> "$out"
  done
  echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
  echo "$out"
done
