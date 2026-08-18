#!/bin/bash
# measure_mixp8.sh <label> <core> <reps> <nproc> : mixed-length workload,
# same 12 slots and the same three link orderings as measure_p8.sh orderset 1.
# Mixes A-E are bit-identical to the truncation run's; F/R1..R6 are appended.
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA baseAB dsp0 dsp0AA t4 t5 t7 t8 t4p8 t4p8AA t4p8b"
O2="base t4p8b t4p8AA t4p8 t8 t7 t5 t4 dsp0AA dsp0 baseAB baseAA"
O3="base t5 t4p8 baseAA t8 dsp0 t4p8b t4 dsp0AA baseAB t7 t4p8AA"
{
for oi in 1 2 3; do
  eval "O=\$O$oi"
  link=""
  for v in $O; do
    case $v in baseAA|baseAB) link="$link base" ;;
               dsp0AA)        link="$link dsp0" ;;
               t4p8AA)        link="$link t4p8" ;;
               *)             link="$link $v" ;; esac
  done
  i=0; objs=""
  for v in $link; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/ps$i.o
    objs="$objs obj/ps$i.o"; i=$((i+1))
  done
  rm -f benchmixp8
  gcc -O2 -DNV=$i -o benchmixp8 bench_mix2.c $objs obj/awslchelp.o
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./benchmixp8 "$reps" $O
  done
done
} | tee logs/mixp8_$lbl.log
