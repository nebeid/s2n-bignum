#!/bin/bash
# measure_mx.sh <label> <core> <reps> <nproc> : 12 slots in ONE binary,
# round-robin, slot order rotated per rep, best-of-reps, 3 link orderings.
#   base            our HEAD kernel                     (always link slot 0)
#   baseAA          the same object again                -> A/A floor
#   dsp0  dsp0AA    baseline + the 2 never-taken dispatch instructions, twice
#                   -> the placement-matched reference for the 128 B column
#   m4s4  m4s4AA    widths 4,1,1,1,1, rotating keys, and its own placement floor
#   m4s4h           widths 4,1,1,1,1, hoisted round keys
#   s4  s4h         widths 1,1,1,1 (nblk = 8 dropped from the fused set)
#   t4p8            separate bodies {1,2,3,4,8}          -- the head-to-head
#   t4              separate bodies {1,2,3,4}
#   cw4             the published width-4 cascade        -- 4-wide tail reference
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA dsp0 dsp0AA m4s4 m4s4AA m4s4h s4 s4h t4p8 t4 cw4"
O2="base cw4 t4 t4p8 s4h s4 m4s4h m4s4AA m4s4 dsp0AA dsp0 baseAA"
O3="base m4s4h s4 baseAA t4p8 dsp0 cw4 m4s4 dsp0AA t4 s4h m4s4AA"
taskset -c "$core" ./clk
{
for oi in 1 2 3; do
  eval "O=\$O$oi"
  link=""
  for v in $O; do
    case $v in baseAA) link="$link base" ;;
               dsp0AA) link="$link dsp0" ;;
               m4s4AA) link="$link m4s4" ;;
               *)      link="$link $v" ;; esac
  done
  ./build_bench12.sh $link
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./bench12 "$reps" $O
  done
done
} | tee logs/mx_$lbl.log
