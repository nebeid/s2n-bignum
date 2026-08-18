#!/bin/bash
# mixaa_p8.sh <core> <reps> <nproc> : placement controls for the MIXED-LENGTH
# bench, small 4-slot binaries only.
#   AA-<v>   four copies of the SAME object in four link slots -> that variant's
#            placement floor in each mix
#   paired   two variants interleaved as X Y X Y and again as Y X Y X, so each is
#            measured at two address ranks and placement cancels.  Pairs:
#              t4  vs t4p8   -- does ADDING body 8 to t4 cost mixed traffic?
#                               (the new-mechanism question: body 8 present, the
#                                middle bodies absent)
#              t5  vs t4p8   -- the decision comparison
#              t8  vs t4p8   -- t4p8 has the big body but not 5,6,7
#              t7  vs t8     -- reproduction of the truncation run's finding
set -e
cd /tmp/fsp
core="${1:-3}"; reps="${2:-150}"; np="${3:-2}"
run () {
  local lbl="$1"; shift
  local i=0 objs=""
  for v in "$@"; do
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
            --keep-global-symbol=dec_s$i obj/$v.o obj/pa$i.o
    objs="$objs obj/pa$i.o"; i=$((i+1))
  done
  rm -f benchpa
  gcc -O2 -DNV=$# -o benchpa bench_mix2.c $objs obj/awslchelp.o
  echo "### $lbl : $*"
  local nm=""; i=0
  for v in "$@"; do nm="$nm ${v}_$i"; i=$((i+1)); done
  for p in $(seq 1 "$np"); do taskset -c "$core" ./benchpa "$reps" $nm; done
}
{
run AA-base base base base base
run AA-t4p8 t4p8 t4p8 t4p8 t4p8
run AA-t5   t5 t5 t5 t5
run AA-t8   t8 t8 t8 t8
run AA-t4   t4 t4 t4 t4
run p-t4-t4p8 t4 t4p8 t4 t4p8
run p-t4p8-t4 t4p8 t4 t4p8 t4
run p-t5-t4p8 t5 t4p8 t5 t4p8
run p-t4p8-t5 t4p8 t5 t4p8 t5
run p-t8-t4p8 t8 t4p8 t8 t4p8
run p-t4p8-t8 t4p8 t8 t4p8 t8
run p-t7-t8   t7 t8 t7 t8
run p-t8-t7   t8 t7 t8 t7
} | tee logs/mixaa_p8_$(hostname -s).log
