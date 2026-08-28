#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
reps=${1:-160}
processes=${2:-7}
core=${3:-3}
host=$(hostname)
out="results/selected-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
  echo "# reps=$reps processes=$processes pinned_cpu=$core"
  cat results/selected-objects.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  taskset -c "$core" ./bench-selected-enc "$reps" "$process" \
    enc-8x enc-4x-late-tag >> "$out"
  taskset -c "$core" ./bench-selected-dec "$reps" "$process" \
    dec-8x dec-4x-basic dec-4x-fast-tail >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
echo "$out"
