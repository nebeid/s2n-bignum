#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
reps=${1:-160}
processes=${2:-7}
core=${3:-3}
host=$(hostname)
out="results/pr-compare-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
  echo "# reps=$reps processes=$processes pinned_cpu=$core"
  cat results/pr-equivalence.txt
  cat results/objects.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  taskset -c "$core" ./bench-dec-pr "$reps" "$process" \
    pr-t4 local-t4 t4p8 john-basic john-mem2 >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
