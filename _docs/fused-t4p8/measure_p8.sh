#!/bin/bash
# measure_p8.sh <label> <core> <reps> <nproc> <orderset:1|2>
# 12 slots in ONE binary, round-robin, slot order rotated per rep, best-of-reps.
#   base            our HEAD kernel                  (always link slot 0)
#   baseAA baseAB   the same object again, twice      -> A/A floor
#   dsp0  dsp0AA    baseline + the 2 never-taken dispatch instructions, twice
#                   -> the placement-matched reference for the 128 B column
#   t4 t5 t7 t8     contiguous truncations (bodies {1..C})
#   t4p8            bodies {1,2,3,4,8}, dispatch order "small"
#   t4p8AA          the same object again -> t4p8's own placement floor
#   t4p8b           bodies {1,2,3,4,8}, dispatch order "big"
#
# THREE link orderings per orderset (6 over the two), base pinned to slot 0
# exactly as in the truncation run so the tables are comparable: every variant
# has a different .text size, so the link order decides each kernel's absolute
# address and the baseline's small-length timing is address-placement sensitive.
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"; os="${5:-1}"
if [ "$os" = 1 ]; then
  O1="base baseAA baseAB dsp0 dsp0AA t4 t5 t7 t8 t4p8 t4p8AA t4p8b"
  O2="base t4p8b t4p8AA t4p8 t8 t7 t5 t4 dsp0AA dsp0 baseAB baseAA"
  O3="base t5 t4p8 baseAA t8 dsp0 t4p8b t4 dsp0AA baseAB t7 t4p8AA"
  OI="1 2 3"
else
  O4="base t8 t4 t4p8AA dsp0 t7 baseAB t4p8b t5 dsp0AA t4p8 baseAA"
  O5="base dsp0AA t7 t4p8b baseAB t4p8 t4 t8 baseAA t5 t4p8AA dsp0"
  O6="base t4p8AA t5 dsp0 t4p8b baseAA t8 dsp0AA t4 baseAB t4p8 t7"
  OI="4 5 6"
fi
taskset -c "$core" ./clk
{
for oi in $OI; do
  eval "O=\$O$oi"
  link=""
  for v in $O; do
    case $v in baseAA|baseAB) link="$link base" ;;
               dsp0AA)        link="$link dsp0" ;;
               t4p8AA)        link="$link t4p8" ;;
               *)             link="$link $v" ;; esac
  done
  ./build_bench12.sh $link
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./bench12 "$reps" $O
  done
done
} | tee logs/p8_$lbl.log
