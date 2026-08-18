#!/bin/bash
# verify_p8.sh : all non-timing checks for the t4p8 variant.
#  1. .text size + frame check (80 bytes, and no other sp adjustment)
#  2. normalised objdump: is the NOT-fused fall-through content unchanged?
#  3. aese/aesmc adjacency
#  4. in-process byte-compare, ALL whole-block lengths 1..256, all 12 slots
#  5. KAT 35/35 per variant, genuine relink
set -e
cd /tmp/fsp
V="dsp0 t4 t5 t7 t8 t4p8 t4p8b"

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
echo "############ 1b. dispatch instructions actually emitted"
for v in t4 t5 t8 t4p8 t4p8b; do
  echo "---- $v"
  grep -A6 'add[[:space:]]*x10, sp, #64' src/$v.S | grep -E 'FUSE|nofuse' || true
done

echo
echo "############ 2. fall-through path: normalised objdump vs baseline"
for v in $V; do
  echo "---- $v"
  python3 objcmp.py obj/base.o obj/$v.o | tail -6
done

echo
echo "############ 3. aese/aesmc adjacency"
for v in t4 t5 t7 t8 t4p8 t4p8b; do
  printf "%-6s " "$v"; python3 verify.py src/$v.S 2>/dev/null | grep -i "violation" | head -1
done

echo
echo "############ 4. in-process byte-compare (all 256 whole-block lengths, 12 slots)"
./build_bench12.sh base base base dsp0 dsp0 t4 t5 t7 t8 t4p8 t4p8 t4p8b
SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./bench12 2 \
   base baseAA baseAB dsp0 dsp0AA t4 t5 t7 t8 t4p8 t4p8AA t4p8b

echo
echo "############ 5. KAT (differential, genuine relink) per variant"
for v in base $V; do
  printf "%-6s " "$v"
  ./kat.sh $v | tail -2 | tr '\n' ' '
  echo
done
