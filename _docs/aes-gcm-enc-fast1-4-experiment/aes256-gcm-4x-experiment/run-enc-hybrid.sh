#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
reps=${1:-160}
processes=${2:-7}
core=${3:-3}
host=$(hostname)
out="results/hybrid-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
  echo "# reps=$reps processes=$processes pinned_cpu=$core"
  cat results/hybrid-objects.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  taskset -c "$core" ./bench-enc-hybrid "$reps" "$process" \
    enc-8x enc-4x-hybrid enc-4x-fast-tail enc-4x-late-tag >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
echo "$out"
