#!/bin/bash
# mixaa_mx.sh <core> <reps> <nproc> : placement controls and PAIRED both-rank
# comparisons for the MIXED-LENGTH bench, in small 4-slot binaries.
#   AA-<v>   four copies of the SAME object -> that variant's placement floor
#   paired   two variants interleaved X Y X Y and again Y X Y X, so each appears
#            at two address ranks and placement cancels.  Pairs:
#              t4p8  vs m4s4h  -- separate bodies vs the shared mixed-width
#                                 region, same entry set: THE head-to-head
#              t4p8  vs m4s4   -- ditto, rotating keys
#              m4s4  vs m4s4h  -- what the round-key hoist is worth
#              t4    vs s4h    -- same, without nblk = 8 in the fused set
#              m4s4h vs s4h    -- does keeping nblk = 8 fused cost mixed traffic?
set -e
cd /tmp/fsp
core="${1:-3}"; reps="${2:-150}"; np="${3:-2}"
run () {
  local lbl="$1"; shift
  local i=0 objs=""
  for v in "$@"; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/ma$i.o
    objs="$objs obj/ma$i.o"; i=$((i+1))
  done
  rm -f benchma2
  gcc -O2 -DNV=$# -o benchma2 bench_mix2.c $objs obj/awslchelp.o
  echo "### $lbl : $*"
  local nm=""; i=0
  for v in "$@"; do nm="$nm ${v}_$i"; i=$((i+1)); done
  for p in $(seq 1 "$np"); do taskset -c "$core" ./benchma2 "$reps" $nm; done
}
{
run AA-base  base base base base
run AA-m4s4  m4s4 m4s4 m4s4 m4s4
run AA-m4s4h m4s4h m4s4h m4s4h m4s4h
run AA-t4p8  t4p8 t4p8 t4p8 t4p8
run AA-s4h   s4h s4h s4h s4h
run p-t4p8-m4s4h t4p8 m4s4h t4p8 m4s4h
run p-m4s4h-t4p8 m4s4h t4p8 m4s4h t4p8
run p-t4p8-m4s4  t4p8 m4s4 t4p8 m4s4
run p-m4s4-t4p8  m4s4 t4p8 m4s4 t4p8
run p-m4s4-m4s4h m4s4 m4s4h m4s4 m4s4h
run p-m4s4h-m4s4 m4s4h m4s4 m4s4h m4s4
run p-t4-s4h     t4 s4h t4 s4h
run p-s4h-t4     s4h t4 s4h t4
run p-m4s4h-s4h  m4s4h s4h m4s4h s4h
run p-s4h-m4s4h  s4h m4s4h s4h m4s4h
} | tee logs/mixaa_mx_$(hostname -s).log
