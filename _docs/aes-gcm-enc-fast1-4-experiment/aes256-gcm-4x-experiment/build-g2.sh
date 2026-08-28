#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march=armv8.2-a+crypto -o "$object" -
}

enc_sources=(
  basic dual_acc fast_tail reload_round_keys_partial scalar_iv_mem2_late_tag
  scalar_iv_mem2_late_tag_fast_tail scalar_iv_mem_late_tag_scalar_rk
)
dec_sources=(basic fast_tail scalar_iv_mem2_late_tag)
for v in "${enc_sources[@]}"; do assemble "src/jenc-$v.S" "obj/jenc-$v.o"; done
for v in "${dec_sources[@]}"; do assemble "src/jdec-$v.S" "obj/jdec-$v.o"; done
assemble src/aesv8-armx.S obj/aesv8armx.o
assemble src/ghashv8-armx.S obj/ghashv8.o
ld -r -o obj/helpers.o obj/aesv8armx.o obj/ghashv8.o

build_one() {
  local mode=$1 nv=$2
  shift 2
  local objects=() i=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$i" --keep-global-symbol="kernel$i" \
      "obj/$source.o" "obj/g2-$mode-slot$i.o"
    objects+=("obj/g2-$mode-slot$i.o")
    i=$((i + 1))
  done
  test "$i" -eq "$nv"
  gcc -O2 -Wall -Wextra -std=c11 -DNV="$nv" -o "bench-g2-$mode" \
    bench.c "${objects[@]}" obj/helpers.o
}

build_one enc 7 \
  jenc-basic:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-dual_acc:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-fast_tail:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-reload_round_keys_partial:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-scalar_iv_mem2_late_tag:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-scalar_iv_mem2_late_tag_fast_tail:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-scalar_iv_mem_late_tag_scalar_rk:aes_gcm_enc_kernel_slothy_base_256

build_one dec 3 \
  jdec-basic:aes_gcm_dec_kernel_slothy_base_256 \
  jdec-fast_tail:aes_gcm_dec_kernel_slothy_base_256 \
  jdec-scalar_iv_mem2_late_tag:aes_gcm_dec_kernel_slothy_base_256

if objdump -d obj/jenc-*.o obj/jdec-*.o | grep -Eq '(^|[[:space:]])eor3([[:space:]]|$)'; then
  echo "G2 GATE FAIL: EOR3 found" >&2
  exit 2
fi
echo "G2 INSTRUCTION GATE PASS: no EOR3"
SELFCHECK_ONLY=1 ./bench-g2-enc 3 0 basic dual fasttail reload mem2 mem2tail scalarrk
SELFCHECK_ONLY=1 ./bench-g2-dec 3 0 basic fasttail mem2
