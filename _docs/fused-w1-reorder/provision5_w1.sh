#!/bin/bash
# provision5_w1.sh : round 5 -- the `rejoin` change on top of the d5 ordering.
#   d5   the accepted ordering (ct=head, clump=4), THREE `ret` in the file
#   d5r  d5 + rejoin=1  : the fused `_done` becomes `b .L256_dec_frame_restore`
#   w1r  the SHIPPED ordering + rejoin=1, so the rejoin cost can be read off
#        independently of the reordering
set -e
cd /tmp/fsw
g () { python3 gen_w1.py src/$1.S src/$2.S $3 "${@:4}" >/dev/null; }
D5="k=1.0 K=0.35 ct=head clump=4"

# the FINAL design, one line:
python3 gen_w1.py src/base.S src/d5r.S w5r k=1.0 K=0.35 ct=head clump=4 rejoin=1
python3 gen_w1.py src/base.S src/w1r.S w5s k=1.0 K=0.35 rejoin=1 >/dev/null
# the control must STILL hold with rejoin=0
python3 gen_w1.py src/base.S src/w1chk2.S mxh k=1.0 K=0.35 >/dev/null
V5="d5r w1r w1chk2"
for v in $V5; do ./mk.sh $v; done

echo "=== CONTROL (rejoin=0 default unchanged): gen_w1 == gen_mix s4h ==="
a=$(md5sum obj/w1chk2.o|cut -d' ' -f1); b=$(md5sum obj/s4h.o|cut -d' ' -f1)
[ "$a" = "$b" ] && echo "  w1chk2=$a s4h=$b  SAME" || { echo "  DIFFER"; exit 1; }

echo "=== the label insertion is LABEL-ONLY (diff d5 -> d5r) ==="
diff src/d5.S src/d5r.S || true

echo "=== ONE-ret check ==="
for vp in "d5 w3h" "d5r w5r" "w1 mxh" "w1r w5s"; do set -- $vp
  echo "---- $1"; python3 onret_w1.py src/$1.S $2 src/base.S || true
done
echo "---- baseline for reference"
python3 - <<'PY'
import re
L=[l.split('//')[0].rstrip() for l in open('src/base.S')]
r=[i+1 for i,l in enumerate(L) if l.strip()=='ret']
print("   base.S has %d `ret`: lines %s"%(len(r),r))
PY

echo "=== .text ==="
for v in base w1 d5 $V5; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  n=$(objdump -d obj/$v.o | grep -cE '\sret$' || true)
  printf "%-8s .text=%-6s objdump ret=%s\n" "$v" "$t" "$n"
done
echo "=== md5 ==="; for v in $V5; do md5sum obj/$v.o; done
echo "=== frame: 80 B, no other sp adjustment ==="
for v in d5r w1r; do
  push=$(grep -c 'stp[[:space:]]*d8, d9, \[sp, #-80\]!' src/$v.S || true)
  pop=$(grep -c 'ldp[[:space:]]*d8, d9, \[sp\], #80' src/$v.S || true)
  other=$(grep -nE '(add|sub)[[:space:]]+sp,' src/$v.S | wc -l | tr -d ' ')
  spo=$(objdump -d obj/$v.o | grep -cE '\b(add|sub)\s+sp,' || true)
  printf "%-6s push80=%s pop80=%s src sp-adjust=%s objdump sp add/sub=%s\n" "$v" "$push" "$pop" "$other" "$spo"
done
echo "=== nblk>8 unchanged ==="
for v in d5r w1r; do printf "%-6s " $v; python3 objcmp.py obj/base.o obj/$v.o | tail -1; done
echo "=== slots / aese / adjacency ==="
for vp in "d5r w5r" "w1r w5s"; do set -- $vp
  echo "---- $1"; python3 verify_mx.py src/$1.S $2 | grep -E 'adjacency|^ *[1-4] |entry set|MISMATCH'; done
echo "=== taken branches inside the region ==="
python3 branches_w1.py d5:w3h d5r:w5r w1:mxh w1r:w5s
echo "=== KAT (genuine relink) ==="
for v in $V5; do printf "%-8s " $v; ./kat.sh $v | tail -2 | tr '\n' ' '; echo; done
echo "=== byte-compare, all 256 whole-block lengths ==="
./buildw.sh base baseAA w1 w1AA d5 d5AA d5r d5rAA w1r c3 d4 c5 \
  && SELFCHECK_ONLY=1 taskset -c "${CORE:-3}" ./benchw 2 base baseAA w1 w1AA d5 d5AA d5r d5rAA w1r c3 d4 c5
