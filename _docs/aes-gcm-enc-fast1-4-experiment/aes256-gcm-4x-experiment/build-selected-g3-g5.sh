#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march=armv8.2-a+crypto+sha3 -o "$object" -
}

assemble src/x8-enc.S obj/selected-x8-enc.o
assemble src/x8-dec.S obj/selected-x8-dec.o
assemble src/jenc-scalar_iv_mem_late_tag_scalar_rk.S obj/selected-enc-late-tag.o
assemble src/jdec-basic.S obj/selected-dec-basic.o
assemble src/jdec-fast_tail.S obj/selected-dec-fast-tail.o
assemble src/aesv8-armx.S obj/selected-aesv8armx.o
assemble src/ghashv8-armx.S obj/selected-ghashv8.o
ld -r -o obj/selected-helpers.o obj/selected-aesv8armx.o obj/selected-ghashv8.o

build_one() {
  local mode=$1
  shift
  local objects=() i=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$i" --keep-global-symbol="kernel$i" \
      "obj/$source.o" "obj/selected-$mode-slot$i.o"
    objects+=("obj/selected-$mode-slot$i.o")
    i=$((i + 1))
  done
  gcc -O2 -Wall -Wextra -std=c11 -DNV="$i" -o "bench-selected-$mode" \
    bench.c "${objects[@]}" obj/selected-helpers.o
}

build_one enc \
  selected-x8-enc:aesv8_gcm_8x_enc_256 \
  selected-enc-late-tag:aes_gcm_enc_kernel_slothy_base_256

build_one dec \
  selected-x8-dec:aesv8_gcm_8x_dec_256_wb \
  selected-dec-basic:aes_gcm_dec_kernel_slothy_base_256 \
  selected-dec-fast-tail:aes_gcm_dec_kernel_slothy_base_256

{
  echo "file,sha256,text_bytes"
  for f in obj/selected-{x8-enc,x8-dec,enc-late-tag,dec-basic,dec-fast-tail}.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/selected-objects.csv

SELFCHECK_ONLY=1 ./bench-selected-enc 3 0 enc-8x enc-4x-late-tag
SELFCHECK_ONLY=1 ./bench-selected-dec 3 0 dec-8x dec-4x-basic dec-4x-fast-tail
