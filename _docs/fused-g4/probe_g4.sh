#!/bin/bash
# probe_g4.sh : liveness / mis-entry / lane-mapping / memory-safety probes for
# the g4 single-entry region.
#
#  zlaneJ   lane J's GHASH products replaced by zero.  Lane J carries message
#           block J-(4-nblk) and is a DISCARDED lane when nblk < 4-J, so zapping
#           it must break EXACTLY the lengths for which the lane is real:
#              zlane0 {4}   zlane1 {3,4}   zlane2 {2,3,4}   zlane3 {1,2,3,4}
#           This is the direct test of the lane -> block mapping AND of the
#           zero-masking: if a discarded lane leaked into the accumulator, or if
#           the real blocks sat in the wrong lanes, the boundary would move.
#  zapall   every lane zapped: must fail at exactly {1,2,3,4} and NEVER at
#           5,6,7,8 or >8 -- the fall-back is genuinely untouched.
#  brk      `brk #0` at the region's single entry label: the process must DIE
#           for nblk = 1,2,3,4 and SURVIVE for 5,6,7,8 and >8.
#  guard    the real g4 objects run with in/out flush against a PROT_NONE page,
#           above and below, at every nblk 1..8: any unclamped lane address is a
#           hard SIGSEGV.
set -e
cd /tmp/fsp
K1="${G4K1:-0.35}"
CORE="${CORE:-3}"

fails () {   # $1 = variant object basename -> comma list of failing nblk
  ./build_bench12g.sh base "$1" >/dev/null
  ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c "$CORE" ./bench12g 2 base "$1" \
    | sed -n 's/^\(SELFCHECK FAIL\|TAILWRITE\) nblk=\([0-9]*\).*/\2/p' | sort -n | uniq \
    | tr '\n' ',' | sed 's/,$//'
}

for M in g4 g4h; do
  echo "==== $M : lane-mapping probes ===="
  for J in 0 1 2 3; do
    python3 gen_g4.py src/base.S src/${M}z_$J.S $M $K1 zlane$J >/dev/null
    ./mk.sh ${M}z_$J
    exp=$(seq $((4-J)) 4 | tr '\n' ',' | sed 's/,$//')
    echo "  zlane$J:  fails at nblk={$(fails ${M}z_$J)}   expected {$exp}"
  done
  python3 gen_g4.py src/base.S src/${M}z_all.S $M $K1 zapall >/dev/null
  ./mk.sh ${M}z_all
  echo "  zapall:  fails at nblk={$(fails ${M}z_all)}   expected {1,2,3,4}"
done

echo
echo "==== brk #0 liveness at the single entry (die = entered) ===="
python3 gen_g4.py src/base.S src/g4brk.S g4 $K1 brk >/dev/null
./mk.sh g4brk
objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s0 \
        --keep-global-symbol=dec_s0 obj/g4brk.o obj/bk0.o
gcc -O2 -o brkprobe_g4 brkprobe.c obj/bk0.o obj/awslchelp.o
for n in 1 2 3 4 5 6 7 8 9 16 64; do
  if taskset -c "$CORE" ./brkprobe_g4 $n plain >/dev/null 2>&1; then r="SURVIVED"; else r="TRAPPED "; fi
  exp=$([ "$n" -le 4 ] && echo TRAPPED || echo SURVIVED)
  printf "  nblk=%-3s %s  expected %s\n" "$n" "$r" "$exp"
done

echo
echo "==== guard-page memory safety of the clamped lane addresses ===="
for v in g4 g4h g4p8 a4 t4 base; do
  objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s0 \
          --keep-global-symbol=dec_s0 obj/$v.o obj/bk1.o
  gcc -O2 -o brkprobe_$v brkprobe.c obj/bk1.o obj/awslchelp.o
  for mode in guard guardlo; do
    ok=""; for n in 1 2 3 4 5 6 7 8; do
      taskset -c "$CORE" ./brkprobe_$v $n $mode >/dev/null 2>&1 && ok="$ok$n" || ok="$ok!$n"
    done
    printf "  %-6s %-8s survived nblk: %s\n" "$v" "$mode" "$ok"
  done
done
