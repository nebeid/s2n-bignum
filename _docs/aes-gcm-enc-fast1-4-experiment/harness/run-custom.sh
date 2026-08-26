#!/bin/bash
set -euo pipefail

root=${1:-/tmp/enc-fast1-4}
rounds=${2:-160}
processes=${3:-5}
core=${4:-3}
cd "$root"

out="results/custom-$(hostname).log"
: > "$out"
{
  echo "# host=$(hostname)"
  echo "# model=$(lscpu | awk -F: '/Model name/{gsub(/^ +/,\"\",$2); print $2}')"
  echo "# rounds=$rounds processes=$processes pinned_cpu=$core"
  echo "# date=$(date -u +%FT%TZ)"
  cat results/code-size.csv
} >> "$out"

for process in $(seq 1 "$processes"); do
  echo "# process=$process" >> "$out"
  taskset -c "$core" ./custom-bench "$rounds" >> "$out"
done
