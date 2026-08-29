#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

awk -f make-enc-short.awk src/hanno-enc-fast-tail.S > src/hanno-enc-short.S
awk -v name=aes_gcm_enc_short_body_256 -v short=1 \
  -f make-enc-entry-body.awk src/hanno-enc-short.S \
  > src/hanno-enc-entry-short.S
awk -v name=aes_gcm_enc_large_body_256 -v short=0 \
  -f make-enc-entry-body.awk src/hanno-enc-large.S \
  > src/hanno-enc-entry-large.S

assemble() {
  local source=$1 object=$2 march=${3:-armv8.2-a+crypto}
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march="$march" -o "$object" -
}

assemble src/hanno-enc-entry-wrapper.S obj/entry-wrapper.o
assemble src/hanno-enc-entry-short.S obj/entry-short.o
assemble src/hanno-enc-entry-large.S obj/entry-large.o
assemble src/hanno-enc-fast-tail.S obj/entry-fast-tail.o
assemble src/hanno-enc-large.S obj/entry-late-tag.o
assemble src/x8-enc-compact.S obj/entry-x8-enc.o armv8.2-a+crypto+sha3
assemble src/aesv8-armx.S obj/entry-aesv8armx.o
assemble src/ghashv8-armx.S obj/entry-ghashv8.o
ld -r -o obj/entry-helpers.o obj/entry-aesv8armx.o obj/entry-ghashv8.o
ld -r -o obj/hanno-enc-entry.o \
  obj/entry-wrapper.o obj/entry-large.o obj/entry-short.o

if nm -g obj/entry-x8-enc.o | grep -q ' aesv8_gcm_8x_enc_256_org$'; then
  x8_symbol=aesv8_gcm_8x_enc_256_org
else
  x8_symbol=aesv8_gcm_8x_enc_256
fi

build_bench() {
  local output=$1
  shift
  local objects=() i=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$i" --keep-global-symbol="kernel$i" \
      "obj/$source.o" "obj/entry-$output-slot$i.o"
    objects+=("obj/entry-$output-slot$i.o")
    i=$((i + 1))
  done
  gcc -O2 -Wall -Wextra -std=c11 -DNV="$i" -o "$output" \
    bench.c "${objects[@]}" obj/entry-helpers.o
}

build_bench bench-enc-entry \
  "entry-x8-enc:$x8_symbol" \
  hanno-enc-entry:aes_gcm_enc_kernel_entry_256 \
  entry-fast-tail:aes_gcm_enc_kernel_slothy_base_256 \
  entry-late-tag:aes_gcm_enc_kernel_slothy_base_256

build_bench bench-enc-entry-g2 \
  hanno-enc-entry:aes_gcm_enc_kernel_entry_256 \
  entry-fast-tail:aes_gcm_enc_kernel_slothy_base_256 \
  entry-late-tag:aes_gcm_enc_kernel_slothy_base_256

gcc -O2 -Wall -Wextra -std=c11 \
  -Daes_gcm_enc_kernel_hybrid_256=aes_gcm_enc_kernel_entry_256 \
  -o kat-enc-entry \
  kat-enc-hybrid.c obj/hanno-enc-entry.o obj/entry-helpers.o

{
  echo "file,sha256,text_bytes"
  for f in obj/hanno-enc-entry.o \
           obj/entry-{wrapper,short,large,fast-tail,late-tag,x8-enc}.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/entry-objects.csv

./kat-enc-entry
SELFCHECK_ONLY=1 ./bench-enc-entry-g2 3 0 \
  enc-4x-entry enc-4x-fast-tail enc-4x-late-tag
if [[ ${G2_ONLY:-0} != 1 ]]; then
  SELFCHECK_ONLY=1 ./bench-enc-entry 3 0 \
    enc-8x enc-4x-entry enc-4x-fast-tail enc-4x-late-tag
fi
