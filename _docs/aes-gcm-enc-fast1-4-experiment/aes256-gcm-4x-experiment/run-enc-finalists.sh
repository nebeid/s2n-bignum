#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mode=${1:?usage: run-enc-finalists.sh small|large [reps] [processes] [core]}
reps=${2:-160}
processes=${3:-7}
core=${4:-3}

case "$mode" in
  small) size_env= ;;
  large) size_env=LARGE_SIZES=1 ;;
  *)
    echo "unknown mode: $mode" >&2
    exit 64
    ;;
esac

host=$(hostname)
for layout in 4x-first 8x-first; do
  binary="./bench-enc-finalists-$layout"
  case "$layout" in
    4x-first) labels=(enc-4x-shared enc-8x-final enc-8x-compact) ;;
    8x-first) labels=(enc-8x-final enc-4x-shared enc-8x-compact) ;;
  esac
  out="results/finalists-$mode-$layout-$host.log"
  : > "$out"
  {
    echo "# date=$(date -u +%FT%TZ)"
    echo "# host=$host"
    echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
    echo "# mode=$mode layout=$layout reps=$reps processes=$processes pinned_cpu=$core"
    cat results/finalists-objects.csv
  } >> "$out"

  for process in $(seq 1 "$processes"); do
    env $size_env taskset -c "$core" "$binary" \
      "$reps" "$process" "${labels[@]}" >> "$out"
  done
  echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
  echo "$out"
done
