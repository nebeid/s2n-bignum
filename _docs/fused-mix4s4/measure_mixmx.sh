#!/bin/bash
# measure_mixmx.sh <label> <core> <reps> <nproc> : mixed-length workload, the
# same 12 slots and the same 3 link orderings as measure_mx.sh.  Mixes A-E are
# bit-identical to the truncation / t4p8 runs' sequences, so the numbers are
# directly comparable; F and R1..R6 come along with bench_mix2.c.
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA dsp0 dsp0AA m4s4 m4s4AA m4s4h s4 s4h t4p8 t4 cw4"
O2="base cw4 t4 t4p8 s4h s4 m4s4h m4s4AA m4s4 dsp0AA dsp0 baseAA"
O3="base m4s4h s4 baseAA t4p8 dsp0 cw4 m4s4 dsp0AA t4 s4h m4s4AA"
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
  i=0; objs=""
  for v in $link; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/ms$i.o
    objs="$objs obj/ms$i.o"; i=$((i+1))
  done
  rm -f benchmixmx
  gcc -O2 -DNV=$i -o benchmixmx bench_mix2.c $objs obj/awslchelp.o
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./benchmixmx "$reps" $O
  done
done
} | tee logs/mixmx_$lbl.log
