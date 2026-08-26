#!/bin/bash
set -euo pipefail

root=${1:-/tmp/intree-enc-fast1-4}
rounds=${2:-10}
inner_reps=${3:-1000}
core=${4:-3}
cd "$root"
out="intree-$(hostname).log"
: > "$out"
{
  echo "# host=$(hostname)"
  echo "# rounds=$rounds inner_reps=$inner_reps pinned_cpu=$core"
  echo "# date=$(date -u +%FT%TZ)"
  sed 's/^/# /' columns.txt
} >> "$out"

order=(base compact full fullAA)
count=${#order[@]}
for round in $(seq 1 "$rounds"); do
  for k in $(seq 0 $((count - 1))); do
    label=${order[$(((k + round) % count))]}
    echo "ROUND $round $label" >> "$out"
    taskset -c "$core" "./benchmark-$label" "-$inner_reps" \
      aesv8_gcm_8x_enc_256_ >> "$out" 2>&1
  done
done
