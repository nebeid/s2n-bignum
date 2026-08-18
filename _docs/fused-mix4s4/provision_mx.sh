#!/bin/bash
# provision_mx.sh : generate + assemble everything the mix4s4 experiment needs.
#
#   m4s4    widths 4,1,1,1,1  keys rotate  -- THE STRUCTURE UNDER TEST
#   m4s4h   widths 4,1,1,1,1  keys hoist   -- same structure, round keys hoisted
#   s4      widths 1,1,1,1    keys rotate  -- the same thing without nblk = 8
#   s4h     widths 1,1,1,1    keys hoist
#   gc1     widths 1x8        keys rotate  -- SELF-CHECK: must be md5-identical
#                                             to gen_cascW.py's W=1 (cw1), i.e.
#                                             gen_mix.py is a strict extension
#   dsp0    pure-dispatch control (gen_trunc.py C=0)
#   t4 t4p8 the separate-body comparators (gen_trunc.py / gen_set.py)
#   cw4     the published width-4 cascade (gen_cascW.py W=4)
set -e
cd /tmp/fsp
mkdir -p obj logs src
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70     # eight-body per-n split points
KSEC=1.0; K1=0.35                             # published cascade split points

python3 gen_mix.py src/base.S src/m4s4.S  4,1,1,1,1 $KSEC $K1 mx  rotate >/dev/null
python3 gen_mix.py src/base.S src/m4s4h.S 4,1,1,1,1 $KSEC $K1 mxh hoist  >/dev/null
python3 gen_mix.py src/base.S src/s4.S    1,1,1,1   $KSEC $K1 s4  rotate >/dev/null
python3 gen_mix.py src/base.S src/s4h.S   1,1,1,1   $KSEC $K1 s4h hoist  >/dev/null
python3 gen_mix.py src/base.S src/gc1.S   1,1,1,1,1,1,1,1 $KSEC $K1 cw rotate >/dev/null
python3 gen_cascW.py src/base.S src/cw1.S 1 $KSEC $K1 cw >/dev/null
python3 gen_cascW.py src/base.S src/cw4.S 4 $KSEC $K1 cw >/dev/null
python3 gen_trunc.py src/base.S src/dsp0.S 0 $K >/dev/null
python3 gen_trunc.py src/base.S src/t4.S   4 $K >/dev/null
python3 gen_set.py   src/base.S src/t4p8.S 1,2,3,4,8 $K small >/dev/null

for v in m4s4 m4s4h s4 s4h gc1 cw1 cw4 dsp0 t4 t4p8; do ./mk.sh $v; done
[ -f obj/ref.o ] || ./mk.sh ref

echo "=== SELF-CHECK: gen_mix.py widths=1x8 rotate  ==  gen_cascW.py W=1 ==="
a=$(md5sum obj/gc1.o | cut -d' ' -f1); b=$(md5sum obj/cw1.o | cut -d' ' -f1)
[ "$a" = "$b" ] && echo "  gc1=$a cw1=$b  SAME" || echo "  gc1=$a cw1=$b  DIFFER"

echo "=== md5 ==="
md5sum obj/base.o obj/dsp0.o obj/t4.o obj/t4p8.o obj/cw4.o \
       obj/m4s4.o obj/m4s4h.o obj/s4.o obj/s4h.o

echo "=== .text sizes ==="
for v in base dsp0 t4 t4p8 cw1 cw4 m4s4 m4s4h s4 s4h; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  printf "%-6s %-6s x%.4f\n" "$v" "$t" "$(echo "$t/4968" | bc -l)"
done
