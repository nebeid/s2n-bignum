#!/bin/bash
# provision_g4.sh : generate + assemble everything the g4 experiment needs.
#
#   g4      ONE region, ONE entry, 4-wide group, ALWAYS 4 blocks of AES, keys
#           rotating through v26/v27/v28  -- THE STRUCTURE UNDER TEST
#   g4h     the same region with all 15 round keys hoisted into v1..v15
#   g4p8    g4 + gen.py's dedicated 8-wide body 8 (the secondary ask)
#   a4      CONTROL: four SEPARATE gen.py bodies for nblk = 1..4, each doing
#           4 blocks of AES and exactly nblk of GHASH.  Isolates the cost of the
#           discarded AES with NO predication -- the primary decomposition.
#   x4      SELF-CHECK: apply_a4 with n_aes = 1 must reproduce gen_trunc's t4
#           object bit for bit (so a4 is t4 + the one changed parameter)
#   dsp0    pure-dispatch control (gen_trunc.py C=0)
#   t4 t4p8 the published separate-body comparators
#   m4s4h   the published mixed-width shared region (gen_mix.py 4,1,1,1,1 hoist)
set -e
cd /tmp/fsp
mkdir -p obj logs src
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70     # gen.py's published per-n splits
K1="${G4K1:-0.30}"        # g4 GHASH/MODULO split point (swept: 0.20..0.60,
                          # 0.30 best by 0.5-2.9% on r8g; the family sweep was flat)
KSEC=1.0; MK1=0.35                            # published cascade splits

python3 gen_g4.py src/base.S src/g4.S    g4   $K1 >/dev/null
python3 gen_g4.py src/base.S src/g4i.S   g4i  $K1 >/dev/null
python3 gen_g4.py src/base.S src/g4h.S   g4h  $K1 >/dev/null
python3 gen_g4.py src/base.S src/g4nm.S  g4nm $K1 >/dev/null
python3 gen_g4.py src/base.S src/g4nn.S  g4nn $K1 >/dev/null
python3 gen_g4.py src/base.S src/g4p8.S  g4p8 $K1 >/dev/null
python3 gen_g4.py src/base.S src/a4.S    a4   $K 4 >/dev/null
python3 gen_g4.py src/base.S src/x4.S    a4   $K 1 >/dev/null
python3 gen_trunc.py src/base.S src/dsp0.S 0 $K >/dev/null
python3 gen_trunc.py src/base.S src/t4.S   4 $K >/dev/null
python3 gen_set.py   src/base.S src/t4p8.S 1,2,3,4,8 $K small >/dev/null
python3 gen_mix.py   src/base.S src/m4s4h.S 4,1,1,1,1 $KSEC $MK1 mxh hoist >/dev/null
python3 gen_cascW.py src/base.S src/cw4.S 4 $KSEC $MK1 cw >/dev/null

for v in g4 g4i g4h g4nm g4nn g4p8 a4 x4 dsp0 t4 t4p8 m4s4h cw4; do ./mk.sh $v; done
[ -f obj/ref.o ] || ./mk.sh ref

echo "=== SELF-CHECK 1: gen_g4.apply_a4 with n_aes=1  ==  gen_trunc.py t4 ==="
a=$(md5sum obj/x4.o | cut -d' ' -f1); b=$(md5sum obj/t4.o | cut -d' ' -f1)
[ "$a" = "$b" ] && echo "  x4=$a t4=$b  SAME" || echo "  x4=$a t4=$b  DIFFER"
echo "=== SELF-CHECK 2: published md5s ==="
echo "  base.o must be 114cedb51f36c584e50843d2838d871e"; md5sum obj/base.o
echo "  t4.o   must be c3f72ffe4679c67064f5439a1d97c712"; md5sum obj/t4.o
echo "  cw4.o  must be 51bbb39cc2c0d89fd3c94804c1ec62bc"; md5sum obj/cw4.o
echo "=== SELF-CHECK 3: g4p8's body 8 == t4p8's body 8 (gen.py body(8,8,0.70)) ==="
awk '/^\.L256_dec_fused_8:/{f=1} f&&/^\.L256_dec_ret:/{f=0} f' src/g4p8.S > /tmp/b8_g4p8.txt
awk '/^\.L256_dec_fused_8:/{f=1} f&&/^\.L256_dec_ret:/{f=0} f' src/t4p8.S > /tmp/b8_t4p8.txt
if diff -q /tmp/b8_g4p8.txt /tmp/b8_t4p8.txt >/dev/null; then
  echo "  body 8: IDENTICAL ($(wc -l < /tmp/b8_g4p8.txt) lines)"
else
  echo "  body 8: DIFFERS"; diff /tmp/b8_g4p8.txt /tmp/b8_t4p8.txt | head
fi

echo "=== md5 ==="
md5sum obj/base.o obj/dsp0.o obj/g4.o obj/g4i.o obj/g4h.o obj/g4p8.o obj/a4.o \
       obj/t4.o obj/t4p8.o obj/m4s4h.o obj/cw4.o

echo "=== .text sizes ==="
{ for v in base dsp0 g4 g4i g4h g4nm g4nn g4p8 a4 t4 t4p8 m4s4h cw4; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  printf "%-6s %-6s x%.4f\n" "$v" "$t" "$(echo "$t/4968" | bc -l)"
done; } | tee logs/text.txt
python3 verify_g4.py src/g4.S g4 | awk '/region total/{print $4}' > logs/slots.txt
echo "g4 region slots: $(cat logs/slots.txt)"
