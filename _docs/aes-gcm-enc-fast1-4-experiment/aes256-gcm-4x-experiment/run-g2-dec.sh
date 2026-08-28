#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
reps=${1:-200}
processes=${2:-9}
core=${3:-3}
label=${4:-fasttail}
host=$(hostname)
out="results/g2-dec-$label-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
  echo "# reps=$reps processes=$processes pinned_cpu=$core"
} >> "$out"
for process in $(seq 1 "$processes"); do
  taskset -c "$core" ./bench-g2-dec "$reps" "$process" \
    dec-basic dec-fasttail dec-mem2 >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
