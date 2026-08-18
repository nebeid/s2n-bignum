#!/bin/bash
# measure_g4.sh <label> <core> <reps> <nproc> : 12 slots in ONE binary,
# round-robin, slot order rotated per rep, best-of-reps, 3 link orderings.
#   base           our HEAD kernel                       (always link slot 0)
#   baseAA         the same object again                  -> A/A floor
#   dsp0 dsp0AA    baseline + the 2 never-taken dispatch instructions, twice
#                  -> the placement-matched reference for the 128 B column
#   g4  g4AA       THE STRUCTURE UNDER TEST, and its own placement floor
#   g4h            the same region with the round keys hoisted
#   a4             CONTROL: separate bodies, 4 blocks of AES, exact GHASH
#   g4p8           g4 + a dedicated 8-wide body 8
#   t4 t4p8        the published separate-body comparators
#   m4s4h          the published mixed-width shared region
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA dsp0 dsp0AA g4 g4AA g4h a4 g4p8 t4p8 t4 m4s4h"
O2="base m4s4h t4 t4p8 g4p8 a4 g4h g4AA g4 dsp0AA dsp0 baseAA"
O3="base g4h a4 baseAA t4p8 dsp0 m4s4h g4 dsp0AA t4 g4p8 g4AA"
taskset -c "$core" ./clk
{
for oi in 1 2 3; do
  eval "O=\$O$oi"
  link=""
  for v in $O; do
    case $v in baseAA) link="$link base" ;;
               dsp0AA) link="$link dsp0" ;;
               g4AA)   link="$link g4" ;;
               *)      link="$link $v" ;; esac
  done
  ./build_bench12g.sh $link
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./bench12g "$reps" $O
  done
done
} | tee logs/g4_$lbl.log
