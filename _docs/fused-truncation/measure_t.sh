#!/bin/bash
# measure_t.sh <label> <core> <reps> <nproc>
# 12 slots in ONE binary, round-robin, order rotated per rep, best-of-reps.
#   base     our HEAD kernel
#   baseAA   the same object a 2nd time   baseAB  a 3rd time  -> A/A floor, twice
#   dsp0     baseline + the 2 dispatch instructions, never-taken, NO fused
#            region: the pure-dispatch control
#   t2..t7   fused bodies for nblk <= C only; nblk > C on the existing path
#   t8       == the full eight-body variant (fused-small-path.patch)
#   cw4t     width-4 cascade for nblk <= 7 + existing path at nblk = 8
#
# Run THREE link orderings.  Every variant has a different .text size, so the
# link order decides each kernel's absolute address, and the baseline's small-
# length timing is known to be address-placement sensitive.  Permuting the order
# re-randomises placement, so a residual that survives all three orderings is a
# property of the code, not of where it landed.
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA baseAB dsp0 t2 t3 t4 t5 t6 t7 t8 cw4t"
O2="base cw4t t8 t7 t6 t5 t4 t3 t2 dsp0 baseAB baseAA"
O3="base t5 t8 baseAA t3 cw4t t7 dsp0 t2 baseAB t6 t4"
taskset -c "$core" ./clk
{
for oi in 1 2 3; do
  eval "O=\$O$oi"
  # baseAA / baseAB / dsp0 map onto real objects
  link=""
  for v in $O; do
    case $v in baseAA|baseAB) link="$link base" ;; *) link="$link $v" ;; esac
  done
  ./build_bench12.sh $link
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./bench12 "$reps" $O
  done
done
} | tee logs/trunc_$lbl.log
