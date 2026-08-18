#!/bin/bash
# mixaa.sh <reps> <nproc> : placement-noise controls for the MIXED-LENGTH bench.
# Four copies of the SAME variant in four different link slots: the spread is
# the placement floor for that variant in each mix.  Then t5/t8 interleaved in
# both orders, so the t5-vs-t8 gap is measured with each at both address ranks.
set -e
cd /tmp/fsp
reps="${1:-150}"; np="${2:-2}"
run () {
  local lbl="$1"; shift
  local i=0 objs=""
  for v in "$@"; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/ma$i.o
    objs="$objs obj/ma$i.o"; i=$((i+1))
  done
  rm -f benchma
  gcc -O2 -DNV=$# -o benchma bench_mix.c $objs obj/awslchelp.o
  echo "### $lbl : $*"
  local nm=""; i=0
  for v in "$@"; do nm="$nm ${v}_$i"; i=$((i+1)); done
  for p in $(seq 1 "$np"); do taskset -c 3 ./benchma "$reps" $nm; done
}
run AA-t8 t8 t8 t8 t8
run AA-t5 t5 t5 t5 t5
run AA-base base base base base
run t5t8 t5 t8 t5 t8
run t8t5 t8 t5 t8 t5
run t6t8 t6 t8 t6 t8
run t7t8 t7 t8 t7 t8
