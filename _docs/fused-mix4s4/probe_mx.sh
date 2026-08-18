#!/bin/bash
# probe_mx.sh : liveness / mis-ENTRY probes for the mix4s4 fall-through region.
#
#   zapN    entry stub N's  acc <- Xi'*H^N  seed replaced by zero.  Stub N is
#           reached ONLY for nblk == N, so it must fail at EXACTLY nblk == N.
#   zapALL  every retained stub zapped.  For m4s4 this must fail at exactly
#           {1,2,3,4,8} and NEVER at 5,6,7 (nor >= 9) -- the direct test of the
#           discontiguous dispatch.  For s4: exactly {1,2,3,4}.
#   zsecP   the products of the block that uses H^P are zeroed.  That block sits
#           in the group containing power P, which runs for every entry >= the
#           group's own remaining count, so the expected failing set is fixed by
#           the fall-through structure:
#              m4s4: zsec1 {1,2,3,4,8}  zsec2 {2,3,4,8}  zsec3 {3,4,8}
#                    zsec4 {4,8}        zsec5 {8}        zsec8 {8}
#           This is the probe that catches the characteristic bug of a
#           fall-through region -- entering at .L_3 while the code assumes 4 live
#           keystream registers -- because such a bug moves the boundary.
set -e
cd /tmp/fsp
KSEC=1.0; K1=0.35
CORE="${CORE:-3}"
fails () {   # $1 = variant object basename
  ./build_bench12.sh base "$1" >/dev/null
  ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c "$CORE" ./bench12 2 base "$1" \
    | sed -n 's/^SELFCHECK FAIL nblk=\([0-9]*\).*/\1/p' | sort -n | uniq | tr '\n' ',' \
    | sed 's/,$//'
}
probe () {   # $1 name  $2 widths  $3 pfx  $4 keys
  local nm="$1" W="$2" P="$3" KY="$4"
  local ENT=; case "$W" in 4,1,1,1,1) ENT="1 2 3 4 8";; 1,1,1,1) ENT="1 2 3 4";; esac
  echo "==== $nm (widths $W, keys $KY) ===="
  for N in $ENT; do
    python3 gen_mix.py src/base.S src/${nm}z_$N.S $W $KSEC $K1 $P $KY $N >/dev/null
    ./mk.sh ${nm}z_$N
    echo "  zap$N:    fails at nblk={$(fails ${nm}z_$N)}   expected {$N}"
  done
  python3 gen_mix.py src/base.S src/${nm}z_all.S $W $KSEC $K1 $P $KY all >/dev/null
  ./mk.sh ${nm}z_all
  echo "  zapALL:  fails at nblk={$(fails ${nm}z_all)}   expected {$(echo $ENT | tr ' ' ',')}"
  for S in $ENT; do
    python3 gen_mix.py src/base.S src/${nm}s_$S.S $W $KSEC $K1 $P $KY 0 $S >/dev/null
    ./mk.sh ${nm}s_$S
    exp=; for e in $ENT; do [ "$e" -ge "$S" ] && exp="$exp,$e"; done
    echo "  zsec$S:   fails at nblk={$(fails ${nm}s_$S)}   expected {${exp#,}}"
  done
  if [ "$W" = "4,1,1,1,1" ]; then
    for S in 5 6 7; do
      python3 gen_mix.py src/base.S src/${nm}s_$S.S $W $KSEC $K1 $P $KY 0 $S >/dev/null
      ./mk.sh ${nm}s_$S
      echo "  zsec$S:   fails at nblk={$(fails ${nm}s_$S)}   expected {8}"
    done
  fi
}
probe m4s4  4,1,1,1,1 mx  rotate
probe m4s4h 4,1,1,1,1 mxh hoist
probe s4    1,1,1,1   s4  rotate
probe s4h   1,1,1,1   s4h hoist
