#!/bin/bash
# probe_w1.sh : liveness / mis-entry / memory-safety probes.
#
#  brk #0 at section r    the process must DIE for every nblk in [r,4] and
#                         SURVIVE for nblk < r and for nblk = 5,6,7,8 and > 8.
#                         r=1 gives the "entry at nblk=1,2,3,4, non-entry at
#                         5..8" requirement directly; r=2,3,4 additionally pin
#                         the fall-through boundary.
#  zsecP                  section P's GHASH products zeroed: must break exactly
#                         nblk >= P (and never 5..8, never > 8).
#  zapN / zapall          the entry seed zeroed: must break exactly nblk = N /
#                         exactly {1,2,3,4}.
#  guard / guardlo        in/out buffers flush against a PROT_NONE page above /
#                         below: any out-of-range ciphertext load or plaintext
#                         store (the characteristic risk of the `ptr=end` static
#                         offsets) is a hard SIGSEGV.
set -e
cd /tmp/fsw
CORE="${CORE:-3}"
KSEC=1.0; MK1=0.35
declare -A KN=( [w1]="k=1.0 K=0.35"
                [f4i]="k=1.0 K=0.35 dsp=f4i"
                [ptre]="k=1.0 K=0.35 ptr=end"
                [c3]="k=0.35 K=0.35 ct=head clump=3"
                [c5]="k=0.35 K=0.35 ct=head clump=3 dsp=f4i sub=eq"
                [d5]="k=1.0 K=0.35 ct=head clump=4"
                [d4]="k=0.35 K=0.35 ct=head clump=4"
                [d5r]="k=1.0 K=0.35 ct=head clump=4 rejoin=1" )
declare -A PF=( [w1]=mxh [f4i]=w1q [ptre]=w1o [c3]=w2h [c5]=w2j [d5]=w3h [d4]=w3g [d5r]=w5r )
PROBEV="${PROBEV:-w1 f4i ptre}"

fails () {
  ./build6.sh base "$1" >/dev/null
  ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c "$CORE" ./bench6 2 base "$1" \
    | sed -n 's/^\(SELFCHECK FAIL\|TAILWRITE\) nblk=\([0-9]*\).*/\2/p' | sort -n | uniq \
    | tr '\n' ',' | sed 's/,$//'
}

for M in $PROBEV; do
  echo "==== $M : brk #0 liveness at each section entry ===="
  for r in 4 3 2 1; do
    python3 gen_w1.py src/base.S src/${M}brk$r.S ${PF[$M]}b \
        ${KN[$M]} brk=$r >/dev/null
    ./mk.sh ${M}brk$r
    objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s0 \
            --keep-global-symbol=dec_s0 obj/${M}brk$r.o obj/bk0.o
    gcc -O2 -o brkprobe_w1 brkprobe.c obj/bk0.o obj/awslchelp.o
    got=""; exp=""
    for n in 1 2 3 4 5 6 7 8 9 16 64; do
      taskset -c "$CORE" ./brkprobe_w1 $n plain >/dev/null 2>&1 && got="$got ." || got="$got $n"
      if [ "$n" -ge "$r" ] && [ "$n" -le 4 ]; then exp="$exp $n"; else exp="$exp ."; fi
    done
    echo "  brk@g$r trapped at nblk:$got"
    echo "         expected      :$exp"
  done
  echo "==== $M : section-product and seed zap probes ===="
  for P in 1 2 3 4; do
    python3 gen_w1.py src/base.S src/${M}zs$P.S ${PF[$M]}c \
        ${KN[$M]} zsec=$P >/dev/null
    ./mk.sh ${M}zs$P
    exp=$(seq $P 4 | tr '\n' ',' | sed 's/,$//')
    echo "  zsec$P: fails at nblk={$(fails ${M}zs$P)}   expected {$exp}"
  done
  for N in 1 2 3 4; do
    python3 gen_w1.py src/base.S src/${M}zp$N.S ${PF[$M]}d \
        ${KN[$M]} zap=$N >/dev/null
    ./mk.sh ${M}zp$N
    echo "  zap$N:  fails at nblk={$(fails ${M}zp$N)}   expected {$N}"
  done
  python3 gen_w1.py src/base.S src/${M}zpa.S ${PF[$M]}e \
      ${KN[$M]} zap=all >/dev/null
  ./mk.sh ${M}zpa
  echo "  zapall: fails at nblk={$(fails ${M}zpa)}   expected {1,2,3,4}"
done

echo
echo "==== guard-page memory safety (any out-of-range access = SIGSEGV) ===="
for v in base s4h w1 c3 d5 d5r w1r; do
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
