#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2 march=${3:-armv8.2-a+crypto}
  gcc -E -Isrc -I../src -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march="$march" -o "$object" -
}

assemble src/x8-enc-shared-fused.S obj/x8-enc-shared-fused.o \
  armv8.2-a+crypto+sha3
assemble src/x8-enc-compact.S obj/x8-enc-compact.o \
  armv8.2-a+crypto+sha3
assemble ../src/baseline.S obj/x8-enc-baseline.o
assemble src/aesv8-armx.S obj/x8-enc-aesv8armx.o
assemble src/ghashv8-armx.S obj/x8-enc-ghashv8.o
ld -r -o obj/x8-enc-helpers.o \
  obj/x8-enc-aesv8armx.o obj/x8-enc-ghashv8.o

for item in \
  compact:x8-enc-compact \
  shared:x8-enc-shared-fused \
  baseline:x8-enc-baseline; do
  name=${item%%:*}
  source=${item#*:}
  case "$name" in
    compact) slot=0 ;;
    shared) slot=1 ;;
    baseline) slot=2 ;;
  esac
  objcopy --redefine-sym aesv8_gcm_8x_enc_256="kernel$slot" \
    --keep-global-symbol="kernel$slot" \
    "obj/$source.o" "obj/x8-enc-$name-bench.o"
done

gcc -O2 -Wall -Wextra -std=c11 -DNV=3 -o bench-enc-x8-shared \
  bench-enc-integrated.c \
  obj/x8-enc-compact-bench.o obj/x8-enc-shared-bench.o \
  obj/x8-enc-baseline-bench.o obj/x8-enc-helpers.o

gcc -O2 -Wall -Wextra -std=c11 \
  -Daes_gcm_enc_kernel_hybrid_256=aesv8_gcm_8x_enc_256 \
  -o kat-enc-x8-shared kat-enc-hybrid.c \
  obj/x8-enc-shared-fused.o obj/x8-enc-helpers.o

{
  echo "file,sha256,text_bytes"
  for f in obj/x8-enc-{baseline,shared-fused,compact}.o; do
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" \
      "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/x8-enc-shared-objects.csv

# The dispatch adds eight bytes before this range. Everything from the old
# body entry through the exact-8 drain must otherwise remain byte-identical.
objcopy --dump-section .text=obj/x8-enc-baseline.text obj/x8-enc-baseline.o
objcopy --dump-section .text=obj/x8-enc-shared.text obj/x8-enc-shared-fused.o
large_hex=$(nm -a obj/x8-enc-shared-fused.o |
  awk '$3=="L256_enc_large_path"{print $1}')
small_hex=$(nm -a obj/x8-enc-shared-fused.o |
  awk '$3=="L256_enc_w1_small"{print $1}')
large=$((16#$large_hex))
small=$((16#$small_hex))
baseline_start=$((large - 8))
length=$((small - large))
dd if=obj/x8-enc-baseline.text of=obj/x8-enc-baseline-large.text \
  bs=1 skip="$baseline_start" count="$length" status=none
dd if=obj/x8-enc-shared.text of=obj/x8-enc-shared-large.text \
  bs=1 skip="$large" count="$length" status=none
cmp obj/x8-enc-baseline-large.text obj/x8-enc-shared-large.text
echo "LARGE PATH BYTE-IDENTICAL: $length bytes"

./kat-enc-x8-shared
SELFCHECK_ONLY=1 ./bench-enc-x8-shared 3 0 \
  enc-8x-compact-fast1-4 enc-8x-shared-fused enc-8x-baseline
