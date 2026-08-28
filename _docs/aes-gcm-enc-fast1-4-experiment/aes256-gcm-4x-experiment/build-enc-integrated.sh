#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2 march=${3:-armv8.2-a+crypto}
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march="$march" -o "$object" -
}

assemble src/hanno-enc-integrated.S obj/integrated.o
assemble src/hanno-enc-fast-tail.S obj/integrated-fast-tail.o
assemble src/hanno-enc-large.S obj/integrated-late-tag.o
assemble src/x8-enc-compact.S obj/integrated-x8-enc.o armv8.2-a+crypto+sha3
assemble src/aesv8-armx.S obj/integrated-aesv8armx.o
assemble src/ghashv8-armx.S obj/integrated-ghashv8.o
ld -r -o obj/integrated-helpers.o \
  obj/integrated-aesv8armx.o obj/integrated-ghashv8.o

build_bench() {
  local output=$1
  shift
  local objects=() i=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$i" --keep-global-symbol="kernel$i" \
      "obj/$source.o" "obj/integrated-$output-slot$i.o"
    objects+=("obj/integrated-$output-slot$i.o")
    i=$((i + 1))
  done
  gcc -O2 -Wall -Wextra -std=c11 -DNV="$i" -o "$output" \
    bench-enc-integrated.c "${objects[@]}" obj/integrated-helpers.o
}

build_bench bench-enc-integrated \
  integrated-x8-enc:aesv8_gcm_8x_enc_256 \
  integrated:aes_gcm_enc_kernel_slothy_base_256 \
  integrated-fast-tail:aes_gcm_enc_kernel_slothy_base_256 \
  integrated-late-tag:aes_gcm_enc_kernel_slothy_base_256

build_bench bench-enc-integrated-g2 \
  integrated:aes_gcm_enc_kernel_slothy_base_256 \
  integrated-fast-tail:aes_gcm_enc_kernel_slothy_base_256 \
  integrated-late-tag:aes_gcm_enc_kernel_slothy_base_256

gcc -O2 -Wall -Wextra -std=c11 \
  -Daes_gcm_enc_kernel_hybrid_256=aes_gcm_enc_kernel_slothy_base_256 \
  -o kat-enc-integrated \
  kat-enc-hybrid.c obj/integrated.o obj/integrated-helpers.o

{
  echo "file,sha256,text_bytes"
  for f in obj/integrated{,-fast-tail,-late-tag,-x8-enc}.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/integrated-objects.csv

./kat-enc-integrated
SELFCHECK_ONLY=1 ./bench-enc-integrated-g2 3 0 \
  enc-4x-integrated enc-4x-fast-tail enc-4x-late-tag
if [[ ${G2_ONLY:-0} != 1 ]]; then
  SELFCHECK_ONLY=1 ./bench-enc-integrated 3 0 \
    enc-8x enc-4x-integrated enc-4x-fast-tail enc-4x-late-tag
fi
