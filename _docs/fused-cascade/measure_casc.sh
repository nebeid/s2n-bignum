#!/bin/bash
# measure_casc.sh <label> <core> <reps> <nproc>
# Kernel-level head-to-head, all variants objcopy'd to distinct symbols and
# linked into ONE binary, timed round-robin with the slot order rotated per rep.
#   base   our HEAD kernel            baseAA  the same object again = A/A floor
#   tuned  eight-body fused path (fused-small-path.patch)
#   casck  pure fall-through cascade, round keys hoisted (best W=1)
#   cw1..cw8  one generator, interleave width W = 1,2,4,8 (identical slot counts)
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
NAMES="base baseAA tuned casck cw1 cw2 cw4 cw8"
./build_bench.sh base base tuned casck cw1 cw2 cw4 cw8
taskset -c "$core" ./clk
for p in $(seq 1 "$np"); do
  echo "=== process $p"
  taskset -c "$core" ./bench "$reps" $NAMES
done | tee logs/cascw_$lbl.log
