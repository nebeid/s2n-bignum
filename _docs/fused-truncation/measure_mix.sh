#!/bin/bash
# measure_mix.sh <label> <core> <reps> <nproc> : mixed-length workload,
# same 12 slots and the same three link orderings as measure_t.sh.
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
O1="base baseAA baseAB dsp0 t2 t3 t4 t5 t6 t7 t8 cw4t"
O2="base cw4t t8 t7 t6 t5 t4 t3 t2 dsp0 baseAB baseAA"
O3="base t5 t8 baseAA t3 cw4t t7 dsp0 t2 baseAB t6 t4"
{
for oi in 1 2 3; do
  eval "O=\$O$oi"
  link=""
  for v in $O; do
    case $v in baseAA|baseAB) link="$link base" ;; *) link="$link $v" ;; esac
  done
  i=0; objs=""
  for v in $link; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/ms$i.o
    objs="$objs obj/ms$i.o"; i=$((i+1))
  done
  rm -f benchmix
  gcc -O2 -DNV=$i -o benchmix bench_mix.c $objs obj/awslchelp.o
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    taskset -c "$core" ./benchmix "$reps" $O
  done
done
} | tee logs/mix_$lbl.log
