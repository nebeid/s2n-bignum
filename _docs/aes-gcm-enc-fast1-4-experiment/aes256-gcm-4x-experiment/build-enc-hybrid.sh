#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

awk -f make-enc-short.awk src/hanno-enc-fast-tail.S > src/hanno-enc-short.S

assemble() {
  local source=$1 object=$2 march=${3:-armv8.2-a+crypto}
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march="$march" -o "$object" -
}

assemble src/hanno-enc-large.S obj/hybrid-late-tag.o
assemble src/hanno-enc-fast-tail.S obj/hybrid-fast-tail.o
assemble src/hanno-enc-short.S obj/hybrid-short-original.o
assemble src/hanno-enc-hybrid-wrapper.S obj/hybrid-wrapper.o
assemble src/x8-enc-compact.S obj/hybrid-x8-enc.o armv8.2-a+crypto+sha3
assemble src/aesv8-armx.S obj/hybrid-aesv8armx.o
assemble src/ghashv8-armx.S obj/hybrid-ghashv8.o
ld -r -o obj/hybrid-helpers.o obj/hybrid-aesv8armx.o obj/hybrid-ghashv8.o

rename_kernel() {
  local source=$1 object=$2 name=$3
  objcopy \
    --redefine-sym "aes_gcm_enc_kernel_slothy_base_256=$name" \
    --redefine-sym "_aes_gcm_enc_kernel_slothy_base_256=_$name" \
    "$source" "$object"
}

rename_kernel obj/hybrid-late-tag.o obj/hybrid-late-tag-renamed.o \
  aes_gcm_enc_kernel_late_tag_256
rename_kernel obj/hybrid-short-original.o obj/hybrid-short-renamed.o \
  aes_gcm_enc_kernel_short_256
ld -r -o obj/hanno-enc-hybrid.o \
  obj/hybrid-wrapper.o obj/hybrid-late-tag-renamed.o obj/hybrid-short-renamed.o

if nm -g obj/hybrid-x8-enc.o | grep -q ' aesv8_gcm_8x_enc_256_org$'; then
  x8_symbol=aesv8_gcm_8x_enc_256_org
else
  x8_symbol=aesv8_gcm_8x_enc_256
fi

build_bench() {
  local objects=() i=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$i" --keep-global-symbol="kernel$i" \
      "obj/$source.o" "obj/hybrid-slot$i.o"
    objects+=("obj/hybrid-slot$i.o")
    i=$((i + 1))
  done
  gcc -O2 -Wall -Wextra -std=c11 -DNV="$i" -o bench-enc-hybrid \
    bench-enc-hybrid.c "${objects[@]}" obj/hybrid-helpers.o
}

build_bench \
  "hybrid-x8-enc:$x8_symbol" \
  hanno-enc-hybrid:aes_gcm_enc_kernel_hybrid_256 \
  hybrid-fast-tail:aes_gcm_enc_kernel_slothy_base_256 \
  hybrid-late-tag:aes_gcm_enc_kernel_slothy_base_256

gcc -O2 -Wall -Wextra -std=c11 -o kat-enc-hybrid \
  kat-enc-hybrid.c obj/hanno-enc-hybrid.o obj/hybrid-helpers.o

{
  echo "file,sha256,text_bytes"
  for f in obj/hybrid-{x8-enc,fast-tail,late-tag}.o \
           obj/hybrid-short-original.o obj/hanno-enc-hybrid.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/hybrid-objects.csv

./kat-enc-hybrid
SELFCHECK_ONLY=1 ./bench-enc-hybrid 3 0 \
  enc-8x enc-4x-hybrid enc-4x-fast-tail enc-4x-late-tag
