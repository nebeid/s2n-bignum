#!/bin/bash
# awslc.sh <variant>
#   A : aws-lc as shipped (pristine; own fallback <256 B, own 8x kernel >=256 B)
#   B : our HEAD kernel substituted for aesv8_gcm_8x_dec_256, threshold -> 16
#   C : new generalised fused small path substituted, threshold -> 16
#
# Substitution: the aws-lc dec_256 8x kernel is renamed out of the way inside
# generated-src/linux-aarch64/.../aesv8-gcm-armv8-unroll8.S and our kernel is
# appended to that same file (labels prefixed so they cannot collide), so no
# CMake/source-list change is needed.
set -e
V="$1"
SRC=/tmp/awslc_src
DST=/tmp/awslc_$V
U=generated-src/linux-aarch64/crypto/fipsmodule/aesv8-gcm-armv8-unroll8.S
GCMC=crypto/fipsmodule/modes/gcm.c

rm -rf "$DST"
cp -a "$SRC" "$DST"
cd "$DST"

if [ "$V" != "A" ]; then
  # 1. threshold: both hw_gcm_encrypt and hw_gcm_decrypt sites
  n=$(grep -c 'len >= 256' $GCMC)
  [ "$n" = "2" ] || { echo "FATAL: expected 2 threshold sites, found $n"; exit 1; }
  sed -i 's/len >= 256/len >= 16/g' $GCMC
  grep -n 'len >= 16' $GCMC

  # 2. rename the shipped dec_256 8x kernel out of the way
  before=$(grep -c 'aesv8_gcm_8x_dec_256\b' $U)
  sed -i 's/\baesv8_gcm_8x_dec_256\b/aesv8_gcm_8x_dec_256_SHIPPED/g' $U
  echo "renamed $before references of the shipped dec_256"

  # 3. append our kernel under that name
  case "$V" in
    B) K=base ;;
    C) K=tuned ;;
    *) echo "unknown variant $V"; exit 1 ;;
  esac
  gcc -E -I/tmp/fsp/include -xassembler-with-cpp - < /tmp/fsp/src/$K.S | tr ';' '\n' \
    | grep -v '^#' \
    | sed -e 's/\.L256_dec_/.L256_decWB_/g' \
          -e 's/\baesv8_gcm_8x_dec_256_wb\b/aesv8_gcm_8x_dec_256/g' \
    > /tmp/wb_$V.s
  grep -c 'aesv8_gcm_8x_dec_256' /tmp/wb_$V.s
  { echo ""; echo "// ==== substituted s2n-bignum kernel ($K) ===="; cat /tmp/wb_$V.s; } >> $U
fi

mkdir -p build
cd build
cmake -GNinja -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF \
      -DDISABLE_GO=ON -DDISABLE_PERL=ON .. > /tmp/cmake_$V.log 2>&1
ninja bssl > /tmp/ninja_$V.log 2>&1 || { tail -30 /tmp/ninja_$V.log; exit 1; }
echo "built $DST/build/tool/bssl"
nm -C ../build/crypto/libcrypto.a 2>/dev/null | grep -c 'aesv8_gcm_8x_dec_256' || true
