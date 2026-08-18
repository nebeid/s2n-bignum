#!/bin/bash
# Set up /tmp/pfx on an aarch64 host: build base + expA objects, KAT, bench.
set -e
cd /tmp/pfx
mkdir -p src obj kat
cp pfx_pkg/aes-gcm/aesv8_gcm_8x_dec_256_wb.S src/base.S
cp pfx_pkg/aes-gcm/aesv8_gcm_8x_dec_256.S    src/ref.S
cp pfx_pkg/aes-gcm/aesv8_gcm_8x_enc_256.S    src/enc.S
cp -r pfx_pkg/include include
cp pfx_pkg/aes-gcm/kat/kat_wb_dec.c kat/

# expA variant
cp src/base.S src/expA.S
patch -s -p0 src/expA.S < pfx_pkg/expA-fused8-K80.patch
echo "expA patched OK"
echo "done setup.sh"
