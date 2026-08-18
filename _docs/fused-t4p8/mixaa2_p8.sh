#!/bin/bash
# mixaa2_p8.sh <core> <reps> <nproc> : the dispatch-ORDER question.
# t4p8 (order "small": 2 tests, nblk>8 pays 4 instrs) vs t4p8b (order "big":
# nblk>8 pays 2 instrs, one of them a TAKEN branch).  Both orders of the pair,
# so placement cancels; plus t4p8b's own A/A floor.
set -e
cd /tmp/fsp
core="${1:-3}"; reps="${2:-150}"; np="${3:-2}"
run () {
  local lbl="$1"; shift
  local i=0 objs=""
  for v in "$@"; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/qa$i.o
    objs="$objs obj/qa$i.o"; i=$((i+1))
  done
  rm -f benchqa
  gcc -O2 -DNV=$# -o benchqa bench_mix2.c $objs obj/awslchelp.o
  echo "### $lbl : $*"
  local nm=""; i=0
  for v in "$@"; do nm="$nm ${v}_$i"; i=$((i+1)); done
  for p in $(seq 1 "$np"); do taskset -c "$core" ./benchqa "$reps" $nm; done
}
{
run AA-t4p8b t4p8b t4p8b t4p8b t4p8b
run p-t4p8-t4p8b t4p8 t4p8b t4p8 t4p8b
run p-t4p8b-t4p8 t4p8b t4p8 t4p8b t4p8
} | tee logs/mixaa2_p8_$(hostname -s).log
