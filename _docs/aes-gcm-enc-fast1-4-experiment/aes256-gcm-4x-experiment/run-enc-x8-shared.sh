#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mode=${1:?usage: run-enc-x8-shared.sh small|large [reps] [processes] [core]}
reps=${2:-160}
processes=${3:-7}
core=${4:-3}
labels=(enc-8x-compact-fast1-4 enc-8x-shared-fused enc-8x-baseline)

case "$mode" in
  small) size_env= ;;
  large) size_env=LARGE_SIZES=1 ;;
  *)
    echo "unknown mode: $mode" >&2
    exit 64
    ;;
esac

host=$(hostname)
out="results/x8-shared-$mode-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,\"\",$2);print $2}')"
  echo "# mode=$mode reps=$reps processes=$processes pinned_cpu=$core"
  cat results/x8-enc-shared-objects.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  env $size_env taskset -c "$core" ./bench-enc-x8-shared \
    "$reps" "$process" "${labels[@]}" >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
echo "$out"
