#!/bin/bash
# mixaa_g4.sh <core> <reps> <nproc> : placement controls and PAIRED both-rank
# comparisons for the MIXED-LENGTH bench, in small 4-slot binaries.
#   AA-<v>   four copies of the SAME object -> that variant's placement floor
#   paired   two variants interleaved X Y X Y and again Y X Y X, so each appears
#            at two address ranks and placement cancels.  Pairs:
#              g4  vs t4     -- one 4-block region vs four exact-n bodies
#              g4  vs a4     -- how much of the loss is the PREDICATION vs the
#                               discarded AES itself
#              a4  vs t4     -- the isolated cost of the DISCARDED BLOCKS
#              g4  vs g4h    -- what round-key hoisting is worth here
#              g4  vs t4p8   -- the head-to-head at the family level
#              g4  vs m4s4h  -- shared region vs shared region
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
  rm -f benchma4
  gcc -O2 -DNV=$# -o benchma4 bench_mix2.c $objs obj/awslchelp.o
  echo "### $lbl : $*"
  local nm=""; i=0
  for v in "$@"; do nm="$nm ${v}_$i"; i=$((i+1)); done
  for p in $(seq 1 "$np"); do taskset -c "$core" ./benchma4 "$reps" $nm; done
}
{
run AA-base base base base base
run AA-g4   g4 g4 g4 g4
run AA-t4   t4 t4 t4 t4
run p-g4-t4      g4 t4 g4 t4
run p-t4-g4      t4 g4 t4 g4
run p-g4-a4      g4 a4 g4 a4
run p-a4-g4      a4 g4 a4 g4
run p-a4-t4      a4 t4 a4 t4
run p-t4-a4      t4 a4 t4 a4
run p-g4-g4h     g4 g4h g4 g4h
run p-g4h-g4     g4h g4 g4h g4
run p-g4-t4p8    g4 t4p8 g4 t4p8
run p-t4p8-g4    t4p8 g4 t4p8 g4
run p-g4-m4s4h   g4 m4s4h g4 m4s4h
run p-m4s4h-g4   m4s4h g4 m4s4h g4
run p-g4p8-t4p8  g4p8 t4p8 g4p8 t4p8
run p-t4p8-g4p8  t4p8 g4p8 t4p8 g4p8
} | tee logs/mixaa_g4_$(hostname -s).log
