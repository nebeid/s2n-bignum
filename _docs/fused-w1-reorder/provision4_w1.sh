#!/bin/bash
# provision4_w1.sh : round 4.  Two more within-section orderings on top of the
# round-3 optimum `c3` (ksec 0.35, ct=head, clump=3):
#   ldh=1      every LOAD the section needs (ciphertext + the two H^p table
#              reads) hoisted to the very top of the section.  Loads take no
#              SIMD issue slot, so this is free in slot terms.
#   fold=late  the three accumulator eors (the only ops on the cross-section
#              GHASH chain) moved to the end of the section instead of being
#              interleaved with the AES rounds.  Non-terminal sections only.
set -e
cd /tmp/fsw
g () { python3 gen_w1.py src/base.S src/$1.S $2 "${@:3}" >/dev/null; }
B="k=0.35 K=0.35 ct=head clump=3"
g e1 w4a $B ldh=1
g e2 w4b $B fold=late
g e3 w4c $B ldh=1 fold=late
g e4 w4d k=0.45 K=0.35 ct=head clump=4 ldh=1
g e5 w4e k=0.35 K=0.30 ct=head clump=3 ldh=1
g e6 w4f k=0.35 K=0.35 ct=head clump=5 ldh=1
g e7 w4g k=0.35 K=0.35 ct=head clump=3 ldh=1 dsp=f4i sub=eq
g e8 w4h k=0.35 K=0.35 ct=head clump=3 ldh=1 ptr=end
V4="e1 e2 e3 e4 e5 e6 e7 e8"
for v in $V4; do ./mk.sh $v; done
echo "=== .text ==="
for v in $V4; do t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}'); printf "%-8s %s\n" "$v" "$t"; done
echo "=== md5 ==="; for v in $V4; do md5sum obj/$v.o; done
echo "=== slots / aese / adjacency ==="
for vp in "e1 w4a" "e3 w4c" "e7 w4g" "e8 w4h"; do set -- $vp
  echo "---- $1"; python3 verify_mx.py src/$1.S $2 | grep -E 'adjacency|^ *[1-4] |MISMATCH'; done
echo "=== nblk>8 unchanged ==="
for v in $V4; do printf "%-8s " $v; python3 objcmp.py obj/base.o obj/$v.o | tail -1; done
echo "=== KAT ==="
for v in $V4; do printf "%-8s " $v; ./kat.sh $v | tail -2 | tr '\n' ' '; echo; done
echo "=== byte-compare, all 256 lengths ==="
./buildw.sh base $V4 && SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./benchw 2 base $V4
