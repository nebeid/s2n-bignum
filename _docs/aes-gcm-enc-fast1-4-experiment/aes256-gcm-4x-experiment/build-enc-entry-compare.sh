#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march=armv8.2-a+crypto -o "$object" -
}

assemble src/hanno-enc-hybrid-wrapper.S obj/compare-hybrid-wrapper.o
assemble src/hanno-enc-short.S obj/compare-hybrid-short.o
assemble src/hanno-enc-large.S obj/compare-hybrid-large.o

objcopy \
  --redefine-sym \
  aes_gcm_enc_kernel_slothy_base_256=aes_gcm_enc_kernel_short_256 \
  --redefine-sym \
  _aes_gcm_enc_kernel_slothy_base_256=_aes_gcm_enc_kernel_short_256 \
  obj/compare-hybrid-short.o obj/compare-hybrid-short-renamed.o
objcopy \
  --redefine-sym \
  aes_gcm_enc_kernel_slothy_base_256=aes_gcm_enc_kernel_late_tag_256 \
  --redefine-sym \
  _aes_gcm_enc_kernel_slothy_base_256=_aes_gcm_enc_kernel_late_tag_256 \
  obj/compare-hybrid-large.o obj/compare-hybrid-large-renamed.o
ld -r -o obj/compare-hybrid.o \
  obj/compare-hybrid-wrapper.o \
  obj/compare-hybrid-large-renamed.o \
  obj/compare-hybrid-short-renamed.o

objcopy \
  --redefine-sym aes_gcm_enc_kernel_entry_256=kernel0 \
  --keep-global-symbol=kernel0 \
  obj/hanno-enc-entry.o obj/compare-entry-slot.o
objcopy \
  --redefine-sym aes_gcm_enc_kernel_hybrid_256=kernel1 \
  --keep-global-symbol=kernel1 \
  obj/compare-hybrid.o obj/compare-hybrid-slot.o

gcc -O2 -Wall -Wextra -std=c11 -DNV=2 -o bench-entry-first \
  bench.c obj/compare-entry-slot.o obj/compare-hybrid-slot.o \
  obj/entry-helpers.o
gcc -O2 -Wall -Wextra -std=c11 -DNV=2 -o bench-hybrid-first \
  bench.c obj/compare-hybrid-slot.o obj/compare-entry-slot.o \
  obj/entry-helpers.o

{
  echo "file,sha256,text_bytes"
  for f in obj/hanno-enc-entry.o obj/compare-hybrid.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/entry-compare-objects.csv

SELFCHECK_ONLY=1 ./bench-entry-first 3 0 entry shared-helper
SELFCHECK_ONLY=1 ./bench-hybrid-first 3 0 entry shared-helper
