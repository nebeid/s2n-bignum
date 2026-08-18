#!/bin/bash
# mixctl.sh <reps> <nproc> : SMALL-binary controls for the mixed-length result.
# 4 slots only, so the whole benchmark binary is small and cross-variant
# I-cache interaction cannot be blamed.  Slot order permuted between sets.
set -e
cd /tmp/fsp
reps="${1:-150}"; np="${2:-3}"
run () {
  local i=0 objs=""
  for v in "$@"; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/mc$i.o
    objs="$objs obj/mc$i.o"; i=$((i+1))
  done
  rm -f benchmc
  gcc -O2 -DNV=$# -o benchmc bench_mix.c $objs obj/awslchelp.o
  echo "### slots: $*"
  for p in $(seq 1 "$np"); do taskset -c 3 ./benchmc "$reps" "$@"; done
}
run base dsp0 t7 t8
run base t8 t7 dsp0
run base t5 t8 t7
run base t8 t5 t4
run base t6 t8 t7
run base t2 t8 t4
run base t8 t2 t3
