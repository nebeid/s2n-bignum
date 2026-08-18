#!/bin/bash
# measure_aux_g4.sh <label> <core> <reps> <nproc> : the DECOMPOSITION run.
#
# Eight slots, two link orderings.  All of these do FOUR blocks of AES; they
# differ only in how the exactly-nblk GHASH/store half is obtained:
#   t4    exact-n AES + exact-n GHASH, four separate bodies  (the reference)
#   a4    4-wide AES + exact-n GHASH, four separate bodies   -> the DISCARDED-AES
#                                                               cost, isolated
#   g4    ONE region, 4-wide AES + 4-lane GHASH + branch-free predication
#   g4i   the same with the masks materialised INLINE instead of precomputed
#   g4nm  DIAGNOSTIC, correct at nblk == 4 ONLY: g4 with the masks REMOVED
#         -> isolates what the predication costs
#   g4nn  DIAGNOSTIC, correct at nblk == 4 ONLY: g4nm with the clamped register
#         offsets and the counter-base shift removed too
#         -> isolates what the clamped ADDRESSING costs
#   cw4   the published width-4 cascade: the same 4-wide group reached through a
#         per-nblk stub, i.e. gen_cascW's idiom without any predication
# g4nm/g4nn are wrong for nblk != 4, so ALLOW_MISMATCH is set and ONLY their
# 64 B column is a valid measurement (their cost is nblk-independent by
# construction, which the table itself shows).
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="${3:-200}"; np="${4:-2}"
A1="base t4 a4 g4 g4i g4nm g4nn cw4"
A2="base cw4 g4nn g4nm g4i g4 a4 t4"
{
for oi in 1 2; do
  eval "O=\$A$oi"
  ./build_bench12g.sh $O
  for p in $(seq 1 "$np"); do
    echo "=== process order$oi.$p"
    ALLOW_MISMATCH=1 taskset -c "$core" ./bench12g "$reps" $O
  done
done
} | tee logs/aux_$lbl.log
