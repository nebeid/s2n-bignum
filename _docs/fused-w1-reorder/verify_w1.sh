#!/bin/bash
# verify_w1.sh : every non-timing check for the W=1 ordering variants.
#  1. .text size + 80-byte frame (and no other sp adjustment anywhere)
#  2. the dispatch instructions actually emitted, and the taken-branch count
#     on each entry path
#  3. normalised objdump: is the nblk>8 fall-through content unchanged?
#  4. aese/aesmc adjacency (whole file) + per-nblk slot / aese accounting
#  5. in-process byte-compare over ALL 256 whole-block lengths, 12 slots
#  6. KAT 35/35 per variant, genuine relink (binary deleted first)
set -e
cd /tmp/fsw
V="${W1V:-s4h w1 ka kb kc kd Ka Kb Kc Kd gs30 gs50 cl2 cl3 cl4 cthd ptre f4 f4i f4iE f4iH lbr lrev}"
declare -A PFX=( [s4h]=mxh [w1]=mxh [ka]=w1a [kb]=w1b [kc]=w1c [kd]=w1d [Ka]=w1e
                 [Kb]=w1f [Kc]=w1g [Kd]=w1h [gs30]=w1i [gs50]=w1j [cl2]=w1k
                 [cl3]=w1l [cl4]=w1m [cthd]=w1n [ptre]=w1o [f4]=w1p [f4i]=w1q
                 [f4iE]=w1r [f4iH]=w1s [lbr]=w1t [lrev]=w1u
                 [dctr]=w1v [dct]=w1w [dbot]=w1x )

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
echo "############ 2. dispatch actually emitted (at the entry anchor)"
for v in w1 f4i lrev; do
  echo "---- $v"; grep -A4 'add[[:space:]]*x10, sp, #64' src/$v.S | grep -E 'W1|cmp|b\.' || true
done
echo "---- taken branches inside the region on each entry path"
python3 branches_w1.py

echo
echo "############ 3. nblk>8 fall-through: normalised objdump vs baseline"
for v in $V; do
  printf "%-6s " "$v"; python3 objcmp.py obj/base.o obj/$v.o | tail -1
done

echo
echo "############ 4. adjacency + per-nblk slots / aese (must be 14n)"
for v in $V; do
  echo "---- $v (label prefix ${PFX[$v]})"
  python3 verify_mx.py src/$v.S "${PFX[$v]}" | grep -E 'adjacency|^ *[1-4] |entry set|MISMATCH'
done

echo
echo "############ 5. in-process byte-compare, all 256 whole-block lengths"
for grp in "base s4h w1 ka kb kc kd Ka Kb Kc Kd gs30" \
           "base gs50 cl2 cl3 cl4 cthd ptre f4 f4i f4iE f4iH lbr" \
           "base lrev s4h w1 f4i ptre"; do
  ./build6.sh $grp
  SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./bench6 2 $grp
done

echo
echo "############ 6. KAT (differential, genuine relink) per variant"
for v in base $V; do
  printf "%-6s " "$v"
  ./kat.sh $v | tail -2 | tr '\n' ' '
  echo
done
