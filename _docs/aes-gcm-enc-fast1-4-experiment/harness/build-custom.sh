#!/bin/bash
set -euo pipefail

root=${1:-/tmp/enc-fast1-4}
cd "$root"
mkdir -p obj results

assemble() {
  local name=$1
  gcc -E -Isrc -xassembler-with-cpp "src/$name.S" |
    tr ';' '\n' | as -march=armv8.2-a+sha3 -o "obj/$name.o" -
}

for name in baseline compact-fast1-4 full-fast1-7 awslc-8x awslc-4x; do
  assemble "$name"
done

printf "variant,text_bytes\n" > results/code-size.csv
for name in baseline compact-fast1-4 full-fast1-7 awslc-8x awslc-4x; do
  bytes=$(objdump -h "obj/$name.o" | awk '$2==".text"{print strtonum("0x"$3)}')
  printf "%s,%s\n" "$name" "$bytes" >> results/code-size.csv
done

# Duplicate object mappings provide same-process A/A controls.
variants=(baseline baseline compact-fast1-4 compact-fast1-4 full-fast1-7 awslc-8x awslc-4x)
symbols=(aesv8_gcm_8x_enc_256 aesv8_gcm_8x_enc_256 aesv8_gcm_8x_enc_256
         aesv8_gcm_8x_enc_256 aesv8_gcm_8x_enc_256 aesv8_gcm_8x_enc_256_org
         aes_gcm_enc_kernel_4x)
objects=()
for i in "${!variants[@]}"; do
  objcopy --redefine-sym "${symbols[$i]}=enc_s$i" \
    --keep-global-symbol="enc_s$i" "obj/${variants[$i]}.o" "obj/slot$i.o"
  objects+=("obj/slot$i.o")
done

# aes-helper.o contains aws-lc's aes_hw_* and gcm_init_v8 routines.
gcc -O2 -Wall -Wextra -std=c11 -DNV=7 -o custom-bench \
  harness/bench.c "${objects[@]}" obj/aes-helper.o
SELFCHECK_ONLY=1 ./custom-bench
