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
  local source=$1 object=$2 march=$3
  shift 3
  gcc -E "$@" -Isrc -I../src -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march="$march" -o "$object" -
}

assemble src/hanno-enc-entry-wrapper.S obj/finalists-entry-wrapper.o \
  armv8.2-a+crypto
assemble src/hanno-enc-entry-short.S obj/finalists-entry-short.o \
  armv8.2-a+crypto
assemble src/hanno-enc-entry-large.S obj/finalists-entry-large.o \
  armv8.2-a+crypto
ld -r -o obj/finalists-4x-entry.o \
  obj/finalists-entry-wrapper.o \
  obj/finalists-entry-large.o \
  obj/finalists-entry-short.o

assemble src/x8-enc-pareto-full.S obj/finalists-8x.o \
  armv8.2-a+crypto+sha3 \
  -DX8_PARETO_WIDTHS=4 -DX8_PARETO_SHARED_REDUCE=1
assemble src/x8-enc-compact.S obj/finalists-compact.o \
  armv8.2-a+crypto+sha3
assemble src/aesv8-armx.S obj/finalists-aesv8armx.o armv8.2-a+crypto
assemble src/ghashv8-armx.S obj/finalists-ghashv8.o armv8.2-a+crypto
ld -r -o obj/finalists-helpers.o \
  obj/finalists-aesv8armx.o obj/finalists-ghashv8.o

if nm -g obj/finalists-compact.o |
    grep -q ' aesv8_gcm_8x_enc_256_org$'; then
  compact_symbol=aesv8_gcm_8x_enc_256_org
else
  compact_symbol=aesv8_gcm_8x_enc_256
fi

build_bench() {
  local output=$1
  shift
  local objects=() slot=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$slot" \
      --keep-global-symbol="kernel$slot" \
      "obj/$source.o" "obj/$output-slot$slot.o"
    objects+=("obj/$output-slot$slot.o")
    slot=$((slot + 1))
  done
  gcc -O2 -Wall -Wextra -std=c11 -DNV=3 -o "$output" \
    bench-enc-integrated.c "${objects[@]}" obj/finalists-helpers.o
}

build_bench bench-enc-finalists-4x-first \
  finalists-4x-entry:aes_gcm_enc_kernel_entry_256 \
  finalists-8x:aesv8_gcm_8x_enc_256 \
  finalists-compact:"$compact_symbol"
build_bench bench-enc-finalists-8x-first \
  finalists-8x:aesv8_gcm_8x_enc_256 \
  finalists-4x-entry:aes_gcm_enc_kernel_entry_256 \
  finalists-compact:"$compact_symbol"

gcc -O2 -Wall -Wextra -std=c11 \
  -Daes_gcm_enc_kernel_hybrid_256=aes_gcm_enc_kernel_entry_256 \
  -o kat-enc-finalists-4x kat-enc-hybrid.c \
  obj/finalists-4x-entry.o obj/finalists-helpers.o
gcc -O2 -Wall -Wextra -std=c11 \
  -Daes_gcm_enc_kernel_hybrid_256=aesv8_gcm_8x_enc_256 \
  -o kat-enc-finalists-8x kat-enc-hybrid.c \
  obj/finalists-8x.o obj/finalists-helpers.o

{
  echo "file,sha256,text_bytes"
  for f in obj/finalists-{4x-entry,8x,compact}.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" \
      "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/finalists-objects.csv

./kat-enc-finalists-4x
./kat-enc-finalists-8x
SELFCHECK_ONLY=1 ./bench-enc-finalists-4x-first 3 0 \
  enc-4x-shared enc-8x-final enc-8x-compact
SELFCHECK_ONLY=1 ./bench-enc-finalists-8x-first 3 0 \
  enc-8x-final enc-4x-shared enc-8x-compact
