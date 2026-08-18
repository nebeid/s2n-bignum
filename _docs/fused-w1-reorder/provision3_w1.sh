#!/bin/bash
# provision3_w1.sh : round 3.  Round 2 showed ksec and `clump` are the SAME
# lever -- fewer, bigger bursts of GHASH product ops between the aese/aesmc
# pairs, as early as possible -- and that it is monotone up to clump = 4.  Round
# 3 pushes it to the limit (`pre`: every product op before AES round 0) and
# crosses it with ct=head.
set -e
cd /tmp/fsw
g () { python3 gen_w1.py src/base.S src/$1.S $2 "${@:3}" >/dev/null; }
g cl5  w3a k=1.0  K=0.35 clump=5
g cl6  w3b k=1.0  K=0.35 clump=6
g cl12 w3c k=1.0  K=0.35 clump=12
g d1   w3d k=0.35 K=0.35 clump=4
g d2   w3e k=0.50 K=0.35 clump=4
g d3   w3f k=0.35 K=0.35 clump=6
g d4   w3g k=0.35 K=0.35 clump=4 ct=head
g d5   w3h k=1.0  K=0.35 clump=4 ct=head
g pre1 w3i k=1.0  K=0.35 pre=1
g pre2 w3j k=1.0  K=0.35 pre=1 ct=head
g pre3 w3k k=1.0  K=0.25 pre=1 ct=head
g pre4 w3l k=1.0  K=0.50 pre=1 ct=head
g pre5 w3m k=1.0  K=0.35 pre=1 ct=head dsp=f4i sub=eq
g pre6 w3n k=1.0  K=0.35 pre=1 ct=head ptr=end
V3="cl5 cl6 cl12 d1 d2 d3 d4 d5 pre1 pre2 pre3 pre4 pre5 pre6"
for v in $V3; do ./mk.sh $v; done
echo "=== .text ==="
for v in $V3; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}'); printf "%-8s %s\n" "$v" "$t"
done
echo "=== md5 ==="; for v in $V3; do md5sum obj/$v.o; done
echo "=== slots / aese / adjacency ==="
for vp in "cl12 w3c" "d1 w3d" "pre2 w3j" "pre5 w3m"; do set -- $vp
  echo "---- $1"; python3 verify_mx.py src/$1.S $2 | grep -E 'adjacency|^ *[1-4] |MISMATCH'
done
echo "=== nblk>8 unchanged ==="
for v in $V3; do printf "%-8s " $v; python3 objcmp.py obj/base.o obj/$v.o | tail -1; done
echo "=== KAT ==="
for v in $V3; do printf "%-8s " $v; ./kat.sh $v | tail -2 | tr '\n' ' '; echo; done
echo "=== byte-compare, all 256 lengths ==="
./buildw.sh base cl5 cl6 cl12 d1 d2 d3 d4 d5 pre1 pre2 pre3 && SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./benchw 2 base cl5 cl6 cl12 d1 d2 d3 d4 d5 pre1 pre2 pre3
./buildw.sh base pre4 pre5 pre6 && SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./benchw 2 base pre4 pre5 pre6
