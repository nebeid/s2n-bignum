#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p obj results

assemble() {
  local source=$1 object=$2
  gcc -E -Isrc -Iinclude -xassembler-with-cpp "$source" |
    tr ';' '\n' | as -march=armv8.2-a+crypto+sha3 -o "$object" -
}

assemble src/x8-enc.S obj/x8-enc.o
assemble src/x8-dec.S obj/x8-dec.o
if [[ -f src/pr-dec.S && -f src/t4p8-dec.S ]]; then
  assemble src/pr-dec.S obj/pr-dec.o
  assemble src/t4p8-dec.S obj/t4p8-dec.o
fi

enc_sources=(
  basic dual_acc fast_tail reload_round_keys_partial scalar_iv_mem2_late_tag
  scalar_iv_mem2_late_tag_fast_tail scalar_iv_mem_late_tag_scalar_rk
)
dec_sources=(basic scalar_iv_mem2_late_tag)
for v in "${enc_sources[@]}"; do assemble "src/jenc-$v.S" "obj/jenc-$v.o"; done
for v in "${dec_sources[@]}"; do assemble "src/jdec-$v.S" "obj/jdec-$v.o"; done

assemble src/aesv8-armx.S obj/aesv8armx.o
assemble src/ghashv8-armx.S obj/ghashv8.o
ld -r -o obj/helpers.o obj/aesv8armx.o obj/ghashv8.o

build_one() {
  local mode=$1 nv=$2 reference_symbol=$3
  shift 3
  local objects=() i=0 item source symbol
  for item in "$@"; do
    source=${item%%:*}
    symbol=${item#*:}
    objcopy --redefine-sym "$symbol=kernel$i" --keep-global-symbol="kernel$i" \
      "obj/$source.o" "obj/$mode-slot$i.o"
    objects+=("obj/$mode-slot$i.o")
    i=$((i + 1))
  done
  test "$i" -eq "$nv"
  gcc -O2 -Wall -Wextra -std=c11 -DNV="$nv" -o "bench-$mode" \
    bench.c "${objects[@]}" obj/helpers.o
}

build_one enc 8 aesv8_gcm_8x_enc_256 \
  x8-enc:aesv8_gcm_8x_enc_256 \
  jenc-basic:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-dual_acc:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-fast_tail:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-reload_round_keys_partial:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-scalar_iv_mem2_late_tag:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-scalar_iv_mem2_late_tag_fast_tail:aes_gcm_enc_kernel_slothy_base_256 \
  jenc-scalar_iv_mem_late_tag_scalar_rk:aes_gcm_enc_kernel_slothy_base_256

build_one dec 3 aesv8_gcm_8x_dec_256_wb \
  x8-dec:aesv8_gcm_8x_dec_256_wb \
  jdec-basic:aes_gcm_dec_kernel_slothy_base_256 \
  jdec-scalar_iv_mem2_late_tag:aes_gcm_dec_kernel_slothy_base_256

if [[ -f obj/pr-dec.o && -f obj/t4p8-dec.o ]]; then
  build_one dec-pr 5 aesv8_gcm_8x_dec_256_wb \
    pr-dec:aesv8_gcm_8x_dec_256_wb \
    x8-dec:aesv8_gcm_8x_dec_256_wb \
    t4p8-dec:aesv8_gcm_8x_dec_256_wb \
    jdec-basic:aes_gcm_dec_kernel_slothy_base_256 \
    jdec-scalar_iv_mem2_late_tag:aes_gcm_dec_kernel_slothy_base_256
fi

{
  echo "file,sha256,text_bytes"
  for f in obj/x8-{enc,dec}.o obj/pr-dec.o obj/t4p8-dec.o obj/j{enc,dec}-*.o; do
    [[ -f "$f" ]] || continue
    bytes=$(objdump -h "$f" | awk '$2==".text"{print strtonum("0x"$3)}')
    printf "%s,%s,%s\n" "${f#obj/}" "$(sha256sum "$f" | cut -d' ' -f1)" "$bytes"
  done
} > results/objects.csv

SELFCHECK_ONLY=1 ./bench-enc 3 0 x8 basic dual fasttail reload mem2 mem2tail scalarrk
SELFCHECK_ONLY=1 ./bench-dec 3 0 x8 basic mem2
if [[ -x ./bench-dec-pr ]]; then
  SELFCHECK_ONLY=1 ./bench-dec-pr 3 0 pr-t4 local-t4 t4p8 john-basic john-mem2
  objcopy -O binary --only-section=.text obj/pr-dec.o obj/pr-dec.text
  objcopy -O binary --only-section=.text obj/x8-dec.o obj/x8-dec.text
  if cmp -s obj/pr-dec.text obj/x8-dec.text; then
    echo "PR_T4_LOCAL_T4_TEXT_IDENTICAL=yes" | tee results/pr-equivalence.txt
  else
    echo "PR_T4_LOCAL_T4_TEXT_IDENTICAL=no" | tee results/pr-equivalence.txt
  fi
fi
