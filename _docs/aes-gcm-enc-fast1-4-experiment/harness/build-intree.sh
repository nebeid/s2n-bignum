#!/bin/bash
set -euo pipefail

root=${1:-/tmp/intree-enc-fast1-4}
src_root=${2:-/tmp/enc-fast1-4}
cd "$root"
rm -rf tree
mkdir tree
tar xzf mila-benchmark-tree.tgz -C tree
cd tree

make -C arm -j"$(nproc)" libs2nbignum.a > "$root/arm-build.log" 2>&1

variants=(baseline compact-fast1-4 full-fast1-7 full-fast1-7)
labels=(base compact full fullAA)
: > "$root/columns.txt"
for i in "${!labels[@]}"; do
  label=${labels[$i]}
  source=${variants[$i]}
  cp "$src_root/src/$source.S" arm/aes-gcm/aesv8_gcm_8x_enc_256.S
  rm -f arm/aes-gcm/aesv8_gcm_8x_enc_256.o arm/libs2nbignum.a benchmarks/benchmark
  make -C arm libs2nbignum.a > "$root/relink-$label.log" 2>&1
  make -C benchmarks benchmark >> "$root/relink-$label.log" 2>&1

  object=arm/aes-gcm/aesv8_gcm_8x_enc_256.o
  text_bin="$root/kernel-$label.bin"
  objcopy -O binary --only-section=.text "$object" "$text_bin"
  text_size=$(stat -c%s "$text_bin")
  cp benchmarks/benchmark "$root/benchmark-$label"
  offset=$("$src_root/harness/probe-kernel.py" "$text_bin" "$root/benchmark-$label")
  printf "%s source=%s text=%s offset=%s object_sha256=%s binary_sha256=%s\n" \
    "$label" "$source" "$text_size" "$offset" \
    "$(sha256sum "$object" | cut -d' ' -f1)" \
    "$(sha256sum "$root/benchmark-$label" | cut -d' ' -f1)" |
    tee -a "$root/columns.txt"
done

cmp "$root/benchmark-full" "$root/benchmark-fullAA"
echo "A/A binaries byte-identical"
