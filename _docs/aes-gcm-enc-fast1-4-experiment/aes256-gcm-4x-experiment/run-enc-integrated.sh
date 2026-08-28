#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
profile=${1:?usage: run-enc-integrated.sh g2|all small|large [reps] [processes] [core]}
mode=${2:?usage: run-enc-integrated.sh g2|all small|large [reps] [processes] [core]}
reps=${3:-160}
processes=${4:-7}
core=${5:-3}

case "$profile" in
  g2)
    binary=./bench-enc-integrated-g2
    labels=(enc-4x-integrated enc-4x-fast-tail enc-4x-late-tag)
    ;;
  all)
    binary=./bench-enc-integrated
    labels=(enc-8x enc-4x-integrated enc-4x-fast-tail enc-4x-late-tag)
    ;;
  *)
    echo "unknown profile: $profile" >&2
    exit 64
    ;;
esac

case "$mode" in
  small) size_env= ;;
  large) size_env=LARGE_SIZES=1 ;;
  *)
    echo "unknown mode: $mode" >&2
    exit 64
    ;;
esac

host=$(hostname)
out="results/integrated-$mode-$host.log"
: > "$out"
{
  echo "# date=$(date -u +%FT%TZ)"
  echo "# host=$host"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2}')"
  echo "# profile=$profile mode=$mode reps=$reps processes=$processes pinned_cpu=$core"
  cat results/integrated-objects.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  env $size_env taskset -c "$core" "$binary" "$reps" "$process" \
    "${labels[@]}" >> "$out"
done
echo "DONE: $(grep -c '^# SELFCHECK OK' "$out") correctness gates" >> "$out"
echo "$out"
