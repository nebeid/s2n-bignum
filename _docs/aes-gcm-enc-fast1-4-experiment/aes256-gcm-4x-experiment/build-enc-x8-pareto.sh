#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2 march=$3
  shift 3
  gcc -E "$@" -Isrc -I../src -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march="$march" -o "$object" -
}

assemble src/x8-enc-compact.S obj/x8-pareto-compact.o \
  armv8.2-a+crypto+sha3
assemble src/aesv8-armx.S obj/x8-pareto-aesv8armx.o armv8.2-a+crypto
assemble src/ghashv8-armx.S obj/x8-pareto-ghashv8.o armv8.2-a+crypto
ld -r -o obj/x8-pareto-helpers.o \
  obj/x8-pareto-aesv8armx.o obj/x8-pareto-ghashv8.o

variants=(
  "w1-inline:1:0"
  "w2-inline:2:0"
  "w2-shared:2:1"
  "w3-inline:3:0"
  "w3-shared:3:1"
  "w4-inline:4:0"
  "w4-shared:4:1"
)

for item in "${variants[@]}"; do
  name=${item%%:*}
  rest=${item#*:}
  width=${rest%%:*}
  reduce=${rest##*:}
  assemble src/x8-enc-pareto-full.S "obj/x8-pareto-$name.o" \
    armv8.2-a+crypto+sha3 -DX8_PARETO_WIDTHS="$width" \
    -DX8_PARETO_SHARED_REDUCE="$reduce"
done

objects=(compact)
for item in "${variants[@]}"; do objects+=("${item%%:*}"); done
bench_objects=()
for slot in "${!objects[@]}"; do
  name=${objects[$slot]}
  objcopy --redefine-sym aesv8_gcm_8x_enc_256="kernel$slot" \
    --keep-global-symbol="kernel$slot" \
    "obj/x8-pareto-$name.o" "obj/x8-pareto-$name-bench.o"
  bench_objects+=("obj/x8-pareto-$name-bench.o")
done

gcc -O2 -Wall -Wextra -std=c11 -DNV=8 -o bench-enc-x8-pareto \
  bench-enc-integrated.c "${bench_objects[@]}" obj/x8-pareto-helpers.o

for mode in inline shared; do
  gcc -O2 -Wall -Wextra -std=c11 \
    -Daes_gcm_enc_kernel_hybrid_256=aesv8_gcm_8x_enc_256 \
    -o "kat-enc-x8-pareto-$mode" kat-enc-hybrid.c \
    "obj/x8-pareto-w4-$mode.o" obj/x8-pareto-helpers.o
done

{
  echo "file,sha256,text_bytes"
  for name in "${objects[@]}"; do
    f="obj/x8-pareto-$name.o"
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" \
      "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/x8-pareto-objects.csv

# The candidate's first live short drain marks
# the end of the byte-identical main loop and common-tail range in both objects.
objcopy --dump-section .text=obj/x8-pareto-compact.text \
  obj/x8-pareto-compact.o
objcopy --dump-section .text=obj/x8-pareto-candidate.text \
  obj/x8-pareto-w4-shared.o
symbol_offset() {
  nm -a "$1" | awk -v symbol="$2" '$3==symbol{print $1}'
}
compact_start=$((16#$(symbol_offset obj/x8-pareto-compact.o L256_enc_main_loop)))
compact_end=$((16#$(symbol_offset obj/x8-pareto-compact.o L256_enc_fast2_drain)))
candidate_start=$((16#$(symbol_offset obj/x8-pareto-w4-shared.o L256_enc_main_loop)))
candidate_end=$((16#$(symbol_offset obj/x8-pareto-w4-shared.o L256_enc_fast2_drain)))
compact_length=$((compact_end - compact_start))
candidate_length=$((candidate_end - candidate_start))
test "$compact_length" -eq "$candidate_length"
dd if=obj/x8-pareto-compact.text of=obj/x8-pareto-compact-main.text \
  bs=1 skip="$compact_start" count="$compact_length" status=none
dd if=obj/x8-pareto-candidate.text of=obj/x8-pareto-candidate-main.text \
  bs=1 skip="$candidate_start" count="$candidate_length" status=none
cmp obj/x8-pareto-compact-main.text obj/x8-pareto-candidate-main.text
echo "MAIN LOOP AND COMMON TAILS BYTE-IDENTICAL: $candidate_length bytes"

./kat-enc-x8-pareto-inline
./kat-enc-x8-pareto-shared
SELFCHECK_ONLY=1 ./bench-enc-x8-pareto 3 0 \
  enc-8x-compact-fast1-4 \
  enc-8x-w1-inline enc-8x-w2-inline enc-8x-w2-shared \
  enc-8x-w3-inline enc-8x-w3-shared \
  enc-8x-w4-inline enc-8x-w4-shared
