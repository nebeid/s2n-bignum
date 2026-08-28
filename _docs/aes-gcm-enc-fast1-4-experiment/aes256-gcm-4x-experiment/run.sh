#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
reps=${1:-160}
processes=${2:-7}
core=${3:-3}
host=$(hostname)
out="results/raw-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
  echo "# reps=$reps processes=$processes pinned_cpu=$core"
  cat results/objects.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  taskset -c "$core" ./bench-enc "$reps" "$process" \
    enc-x8 enc-basic enc-dual enc-fasttail enc-reload enc-mem2 \
    enc-mem2tail enc-scalarrk >> "$out"
  taskset -c "$core" ./bench-dec "$reps" "$process" \
    dec-x8 dec-basic dec-mem2 >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
