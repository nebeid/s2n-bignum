#!/bin/bash
# provision2_w1.sh : round 2.  Round 1 found three levers that move V1 at 48/64 B
# and they are all the same shape -- get the GHASH product ops EARLIER and
# CLUMPED, not spread over the 14 AES rounds:
#     ksec 1.0 -> 0.35   (-1.2 pt at 64 B)
#     ct=head            (-0.8 pt)
#     clump=3            (-0.7 pt)
# and two that are flat: the dispatch/taken-branch count and the address chain.
# Round 2 refines the ksec window and crosses the three winners.
set -e
cd /tmp/fsw
g () { python3 gen_w1.py src/base.S src/$1.S $2 "${@:3}" >/dev/null; }
g k20  w2a k=0.20 K=0.35
g k25  w2b k=0.25 K=0.35
g k30  w2c k=0.30 K=0.35
g k40  w2d k=0.40 K=0.35
g k45  w2e k=0.45 K=0.35
g c1   w2f k=0.35 K=0.35 ct=head
g c2   w2g k=0.35 K=0.35 clump=3
g c3   w2h k=0.35 K=0.35 ct=head clump=3
g c4   w2i k=0.25 K=0.35 ct=head clump=2
g c5   w2j k=0.35 K=0.35 ct=head clump=3 dsp=f4i sub=eq
g c6   w2k k=0.35 K=0.25 ct=head clump=3
g c7   w2l k=0.35 K=0.35 ct=head clump=4
g c8   w2m k=0.35 K=0.35 ct=head clump=3 ptr=end
g f4ie w2n k=1.0  K=0.35 dsp=f4i sub=eq
V2="k20 k25 k30 k40 k45 c1 c2 c3 c4 c5 c6 c7 c8 f4ie"
for v in $V2; do ./mk.sh $v; done
echo "=== .text ==="
for v in $V2; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  printf "%-8s %s\n" "$v" "$t"
done
echo "=== md5 ==="; for v in $V2; do md5sum obj/$v.o; done
echo "=== taken branches inside the region ==="
python3 branches_w1.py f4ie:w2n c5:w2j c3:w2h
echo "=== slots / aese / adjacency ==="
for vp in "c3 w2h" "c5 w2j" "c8 w2m" "k25 w2b"; do set -- $vp
  echo "---- $1"; python3 verify_mx.py src/$1.S $2 | grep -E 'adjacency|^ *[1-4] |MISMATCH'
done
echo "=== nblk>8 unchanged ==="
for v in $V2; do printf "%-8s " $v; python3 objcmp.py obj/base.o obj/$v.o | tail -1; done
echo "=== KAT ==="
for v in $V2; do printf "%-8s " $v; ./kat.sh $v | tail -2 | tr '\n' ' '; echo; done
echo "=== byte-compare, all 256 lengths (two 12-slot groups) ==="
./buildw.sh base k20 k25 k30 k40 k45 c1 c2 c3 c4 c5 c6 && SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./benchw 2 base k20 k25 k30 k40 k45 c1 c2 c3 c4 c5 c6
./buildw.sh base c7 c8 f4ie && SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./benchw 2 base c7 c8 f4ie
