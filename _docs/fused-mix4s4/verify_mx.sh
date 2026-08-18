#!/bin/bash
# verify_mx.sh : all non-timing checks for the mix4s4 variants.
#  1. .text size + frame check (80 bytes, and no other sp adjustment)
#  2. dispatch instructions actually emitted
#  3. normalised objdump: is the NOT-fused fall-through content unchanged?
#  4. aese/aesmc adjacency + per-nblk slot / aese accounting (14n, no dead AES)
#  5. in-process byte-compare, ALL whole-block lengths 1..256, all 12 slots
#  6. KAT 35/35 per variant, genuine relink
set -e
cd /tmp/fsp
V="dsp0 t4 t4p8 cw4 m4s4 m4s4h s4 s4h"

echo "############ 1. .text size and 80-byte frame"
for v in base $V; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  push=$(grep -c 'stp[[:space:]]*d8, d9, \[sp, #-80\]!' src/$v.S || true)
  pop=$(grep -c 'ldp[[:space:]]*d8, d9, \[sp\], #80' src/$v.S || true)
  other=$(grep -nE '(add|sub)[[:space:]]+sp,' src/$v.S | wc -l | tr -d ' ')
  spother=$(objdump -d obj/$v.o | grep -cE '\b(add|sub)\s+sp,' || true)
  printf "%-6s .text=%-6s push80=%s pop80=%s  src sp-adjust=%s  objdump sp add/sub=%s\n" \
     "$v" "$t" "$push" "$pop" "$other" "$spother"
done

echo
echo "############ 2. dispatch instructions actually emitted"
for v in t4 t4p8 m4s4 m4s4h s4; do
  echo "---- $v"
  grep -A8 'add[[:space:]]*x10, sp, #64' src/$v.S | grep -E 'FUSE|MIX|CASCW|cmp|b\.' || true
done

echo
echo "############ 3. fall-through path: normalised objdump vs baseline"
for v in $V; do
  echo "---- $v"
  python3 objcmp.py obj/base.o obj/$v.o | tail -5
done

echo
echo "############ 4. adjacency + per-nblk slots (aese must be exactly 14n)"
for vp in "m4s4 mx" "m4s4h mxh" "s4 s4" "s4h s4h"; do
  set -- $vp
  echo "---- $1 (label prefix $2)"
  python3 verify_mx.py src/$1.S $2
done
for v in t4 t4p8 cw4; do
  printf "%-6s " "$v"; python3 verify.py src/$v.S 2>/dev/null | grep -i "violation" | head -1
done

echo
echo "############ 5. in-process byte-compare (all 256 whole-block lengths, 12 slots)"
./build_bench12.sh base base dsp0 dsp0 m4s4 m4s4 m4s4h s4 s4h t4p8 t4 cw4
SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./bench12 2 \
   base baseAA dsp0 dsp0AA m4s4 m4s4AA m4s4h s4 s4h t4p8 t4 cw4

echo
echo "############ 6. KAT (differential, genuine relink) per variant"
for v in base $V; do
  printf "%-6s " "$v"
  ./kat.sh $v | tail -2 | tr '\n' ' '
  echo
done
