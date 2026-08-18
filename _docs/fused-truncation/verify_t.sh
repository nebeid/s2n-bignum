#!/bin/bash
# verify_t.sh : all non-timing checks for the truncation curve.
#  1. .text size + frame check (must be 80 bytes, and no other sp adjustment)
#  2. normalised objdump: is the nblk>C fall-through content unchanged?
#  3. aese/aesmc adjacency (verify.py) on the fused variants
#  4. in-process byte-compare, ALL whole-block lengths 1..256, every variant
#  5. KAT 35/35 per variant, genuine relink
set -e
cd /tmp/fsp
V8="t2 t3 t4 t5 t6 t7 t8 cw4t"

echo "############ 1. .text size and 80-byte frame"
for v in base tuned $V8; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  push=$(grep -c 'stp[[:space:]]*d8, d9, \[sp, #-80\]!' src/$v.S || true)
  pop=$(grep -c 'ldp[[:space:]]*d8, d9, \[sp\], #80' src/$v.S || true)
  other=$(grep -nE '(add|sub)[[:space:]]+sp,' src/$v.S | wc -l | tr -d ' ')
  spother=$(objdump -d obj/$v.o | grep -cE '\b(add|sub)\s+sp,' || true)
  printf "%-6s .text=%-6s push80=%s pop80=%s  src sp-adjust=%s  objdump sp add/sub=%s\n" \
     "$v" "$t" "$push" "$pop" "$other" "$spother"
done

echo
echo "############ 2. nblk>C fall-through path: normalised objdump vs baseline"
for v in tuned $V8; do
  echo "---- $v"
  python3 objcmp.py obj/base.o obj/$v.o | tail -6
done

echo
echo "############ 3. aese/aesmc adjacency"
for v in tuned t2 t3 t4 t5 t6 t7 t8; do
  printf "%-6s " "$v"; python3 verify.py src/$v.S 2>/dev/null | grep -i "violation" | head -1
done
printf "%-6s " "cw4t"; python3 verify_casck.py src/cw4t.S 2>/dev/null | grep -i "violation" | head -1 || true

echo
echo "############ 4. in-process byte-compare (all 256 whole-block lengths)"
./build_bench12.sh base tuned $V8
SELFCHECK_ONLY=1 taskset -c 3 ./bench12 2 base tuned $V8

echo
echo "############ 5. KAT (differential, genuine relink) per variant"
for v in base tuned $V8; do
  printf "%-6s " "$v"
  ./kat.sh $v | tail -2 | tr '\n' ' '
  echo
done
