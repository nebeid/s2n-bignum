#!/bin/bash
# provision.sh : build everything needed on this host.
set -e
cd /tmp/pl
mkdir -p obj bin logs
chmod +x *.sh

# ---- aws-lc helper object (aes_hw_set_encrypt_key / aes_hw_encrypt / gcm_init_v8)
gcc -c -Iinclude -o obj/aesv8armx.o src/aesv8-armx.S  -march=armv8.2-a+crypto+sha3
gcc -c -Iinclude -o obj/ghashv8.o   src/ghashv8-armx.S -march=armv8.2-a+crypto+sha3
ld -r -o obj/awslchelp.o obj/aesv8armx.o obj/ghashv8.o

# ---- PHASE 1: the exact banked pcb4 build (A,B,C,D + 4 A/A duplicates)
for v in A B C D; do ./mk.sh $v; done
echo "=== assembled-object md5 (D must be 968b7a2f0e89093da5d1961d978e4f44) ==="
md5sum obj/A.o obj/B.o obj/C.o obj/D.o
./build.sh

# ---- PHASE 2/3 variant sources
# natural entry alignment (.align 4 as shipped), main-loop marker only
python3 gen_variant.py src/C.S src/cn.S
python3 gen_variant.py src/D.S src/dn.S
# entry forced to a 64-byte boundary, main loop shifted by 0..56 bytes of nops
for p in 0 8 16 24 32 40 48 56; do
  python3 gen_variant.py src/C.S src/ca$p.S --pad $p --entry-align 64
  python3 gen_variant.py src/D.S src/da$p.S --pad $p --entry-align 64
done
for v in cn dn ca0 ca8 ca16 ca24 ca32 ca40 ca48 ca56 \
                da0 da8 da16 da24 da32 da40 da48 da56; do ./mk.sh $v; done

# cn/dn must be code-identical to C/D apart from the (zero-byte) ml_mark symbol
echo "=== cn vs C, dn vs D  .text md5 (must match) ==="
for pair in "C cn" "D dn"; do
  set -- $pair
  a=$(objcopy -O binary --only-section=.text obj/$1.o /dev/stdout 2>/dev/null | md5sum | cut -d' ' -f1)
  b=$(objcopy -O binary --only-section=.text obj/$2.o /dev/stdout 2>/dev/null | md5sum | cut -d' ' -f1)
  [ "$a" = "$b" ] && echo "  $1 == $2  ($a)" || echo "  $1 != $2  MISMATCH ($a vs $b)"
done
# ca0 / da0 must also be code-identical to C / D (entry .balign changes only padding)
echo "=== ca0 vs C, da0 vs D  .text md5 ==="
for pair in "C ca0" "D da0"; do
  set -- $pair
  a=$(objcopy -O binary --only-section=.text obj/$1.o /dev/stdout 2>/dev/null | md5sum | cut -d' ' -f1)
  b=$(objcopy -O binary --only-section=.text obj/$2.o /dev/stdout 2>/dev/null | md5sum | cut -d' ' -f1)
  [ "$a" = "$b" ] && echo "  $1 == $2  ($a)" || echo "  $1 != $2  differs (expected: .balign pad)"
done

gcc -O2 -o clk clk.c

# ---- PHASE 2: 5 link-order permutations of 4xC + 4xD, natural alignment
./build2.sh P0    0 cn dn cn dn cn dn cn dn
./build2.sh P1    0 cn cn cn cn dn dn dn dn
./build2.sh P2    0 dn cn dn cn dn cn dn cn
./build2.sh P3    0 dn dn cn cn dn dn cn cn
./build2.sh P4    0 cn dn dn cn dn cn cn dn
# ---- PHASE 2: leading padding, P0 slot order
for n in 16 64 128 256 1024; do
  ./build2.sh PAD$n $n cn dn cn dn cn dn cn dn
done
# ---- PHASE 3: main-loop offset, function entry forced 64-byte aligned
./build2.sh A2X2  0 ca0 da0 ca8 da8 ca0 da0 ca8 da8
./build2.sh ACSW  0 ca0 ca8 ca16 ca24 ca32 ca40 ca48 ca56
./build2.sh ADSW  0 da0 da8 da16 da24 da32 da40 da48 da56
echo "PROVISION OK"
