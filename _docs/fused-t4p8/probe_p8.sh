#!/bin/bash
# probe_p8.sh : liveness / DISCONTIGUOUS-DISPATCH-boundary probes for t4p8.
#
#   zapN    body N's block-0 GHASH products replaced by zero.  Body N is
#           reachable ONLY for nblk == N, so this MUST fail exactly nblk == N.
#           Run for every retained body N in {1,2,3,4,8}.
#   zapALL  EVERY retained body zapped.  For t4p8 this MUST fail at exactly
#           {1,2,3,4,8} and NEVER at 5, 6, 7 (nor at 9+).  This is the direct
#           test of the discontiguous dispatch: a tree that routed nblk = 6 into
#           body 8 (or body 4) would show a failure at 6.
#
# Both dispatch orderings are probed, since the orderings differ exactly in the
# dispatch code the probe is testing.
set -e
cd /tmp/fsp
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70
CORE="${CORE:-3}"
fails () {   # $1 = variant object basename
  ./build_bench12.sh base "$1" >/dev/null
  ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c "$CORE" ./bench12 2 base "$1" \
    | sed -n 's/^SELFCHECK FAIL nblk=\([0-9]*\).*/\1/p' | sort -n | uniq | tr '\n' ',' \
    | sed 's/,$//'
}
for ord in small big; do
  case $ord in small) sfx="" ;; big) sfx="b" ;; esac
  echo "==== t4p8$sfx  (bodies {1,2,3,4,8}, dispatch order '$ord') ===="
  for N in 1 2 3 4 8; do
    python3 gen_set.py src/base.S src/p8z${sfx}_$N.S 1,2,3,4,8 $K $ord $N >/dev/null
    ./mk.sh p8z${sfx}_$N
    echo "  zap$N:   fails at nblk={$(fails p8z${sfx}_$N)}   expected {$N}"
  done
  python3 gen_set.py src/base.S src/p8z${sfx}_all.S 1,2,3,4,8 $K $ord all >/dev/null
  ./mk.sh p8z${sfx}_all
  echo "  zapALL: fails at nblk={$(fails p8z${sfx}_all)}   expected {1,2,3,4,8}"
done
