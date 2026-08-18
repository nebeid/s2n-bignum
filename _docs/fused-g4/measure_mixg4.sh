#!/bin/bash
# measure_mixg4.sh <label> <core> <reps> <nproc> : mixed-length workload, the
# same 12 slots and 3 link orderings as measure_g4.sh.  Mixes A-D are
# bit-identical to the sequences in _docs/fused-t4p8.md and _docs/fused-mix4s4.md
# so the numbers are directly comparable with both reports.
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA dsp0 dsp0AA g4 g4AA g4h a4 g4p8 t4p8 t4 m4s4h"
O2="base m4s4h t4 t4p8 g4p8 a4 g4h g4AA g4 dsp0AA dsp0 baseAA"
O3="base g4h a4 baseAA t4p8 dsp0 m4s4h g4 dsp0AA t4 g4p8 g4AA"
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
  i=0; objs=""
  for v in $link; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/ms$i.o
    objs="$objs obj/ms$i.o"; i=$((i+1))
  done
  rm -f benchmixg4
  gcc -O2 -DNV=$i -o benchmixg4 bench_mix2.c $objs obj/awslchelp.o
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./benchmixg4 "$reps" $O
  done
done
} | tee logs/mixg4_$lbl.log
