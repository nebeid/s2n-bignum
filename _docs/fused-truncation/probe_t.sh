#!/bin/bash
# probe_t.sh : liveness / dispatch-boundary probes for each truncation.
#
#   zapN    body N's block-0 GHASH products replaced by zero.  Body N is
#           reachable ONLY for nblk == N, so this MUST fail exactly nblk == N.
#   zapALL  EVERY retained body zapped.  This MUST fail exactly nblk = 1..C and
#           NOT at nblk = C+1..8 -- the direct test that the dispatch does not
#           route nblk > C into a fused body (or into the wrong one).
#
# For the W=4 hybrid: stub probes (exactly nblk == N) and section probes
# (H^J is used by every path with nblk >= J, so exactly nblk = J..7).
set -e
cd /tmp/fsp
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70
fails () {   # $1 = variant object basename
  ./build_bench12.sh base "$1" >/dev/null
  ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c 3 ./bench12 2 base "$1" \
    | sed -n 's/^SELFCHECK FAIL nblk=\([0-9]*\).*/\1/p' | sort -n | uniq | tr '\n' ',' \
    | sed 's/,$//'
}
echo "==== FAMILY 1: truncated eight-body ===="
for C in 2 3 4 5 6 7 8; do
  for N in $(seq 1 $C); do
    python3 gen_trunc.py src/base.S src/z${C}_$N.S $C $K $N >/dev/null
    ./mk.sh z${C}_$N
    echo "C=$C zap$N: fails at nblk={$(fails z${C}_$N)}   expected {$N}"
  done
  python3 gen_trunc.py src/base.S src/z${C}_all.S $C $K all >/dev/null
  ./mk.sh z${C}_all
  echo "C=$C zapALL: fails at nblk={$(fails z${C}_all)}   expected {1..$C}"
done
echo "==== FAMILY 2: W=4 cascade, nblk<=7 ===="
for N in 1 2 3 4 5 6 7; do
  python3 gen_cascWt.py src/base.S src/cz_$N.S 4 7 1.0 0.35 cwt $N 0 >/dev/null
  ./mk.sh cz_$N
  echo "cw4t stub-zap$N: fails at nblk={$(fails cz_$N)}   expected {$N}"
done
for J in 1 2 3 4 5 6 7; do
  python3 gen_cascWt.py src/base.S src/cs_$J.S 4 7 1.0 0.35 cwt 0 $J >/dev/null
  ./mk.sh cs_$J
  echo "cw4t sec-zap H^$J: fails at nblk={$(fails cs_$J)}   expected {$J..7}"
done
