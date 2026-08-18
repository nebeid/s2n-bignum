#!/bin/bash
# verify_g4.sh : every non-timing check for the g4 variants.
#  1. .text size + frame check (80 bytes, no other sp adjustment)
#  2. the dispatch instructions actually emitted
#  3. normalised objdump: is the nblk>8 fall-through content unchanged?
#  4. aese/aesmc adjacency + slot / aese / predication structure
#  5. in-process byte-compare, ALL 256 whole-block lengths, 12 slots, PLUS the
#     "nothing written past 16*nblk" check
#  6. KAT 35/35 per variant, genuine relink
set -e
cd /tmp/fsp
V="dsp0 g4 g4i g4h g4p8 a4 t4 t4p8 m4s4h cw4"

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
for v in g4 g4h g4p8 a4 t4 t4p8; do
  echo "---- $v"
  grep -A8 'add[[:space:]]*x10, sp, #64' src/$v.S | grep -E 'G4|A4|FUSE|cmp|b\.' || true
done

echo
echo "############ 3. nblk>8 fall-through: normalised objdump vs baseline"
for v in $V; do
  echo "---- $v"
  python3 objcmp.py obj/base.o obj/$v.o | tail -4
done

echo
echo "############ 4. adjacency + slots + predication structure"
for vp in "g4 g4" "g4i g4i" "g4h g4h" "g4p8 g4"; do
  set -- $vp
  echo "---- $1 (label prefix $2)"
  python3 verify_g4.py src/$1.S $2
done
echo "---- a4 (separate bodies; aese must be 56 in EVERY body: 4 blocks always)"
python3 verify.py src/a4.S 2>/dev/null | head -8
for v in t4 t4p8 m4s4h cw4; do
  printf "%-6s " "$v"; python3 verify.py src/$v.S 2>/dev/null | grep -i violation | head -1
done

echo
echo "############ 5. in-process byte-compare + no write past 16*nblk (12 slots)"
./build_bench12g.sh base base dsp0 dsp0 g4 g4 g4h a4 g4p8 t4p8 t4 m4s4h
SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./bench12g 2 \
   base baseAA dsp0 dsp0AA g4 g4AA g4h a4 g4p8 t4p8 t4 m4s4h

echo
echo "############ 6. KAT (differential, genuine relink) per variant"
for v in base $V; do
  printf "%-6s " "$v"
  ./kat.sh $v | tail -2 | tr '\n' ' '
  echo
done
