#!/bin/bash
# build_bench.sh s0 s1 s2 s3 s4     (variant basenames for the 5 slots)
set -e
cd /tmp/pfx
i=0
objs=""
for v in "$@"; do
  slot="s$i"
  cp obj/$v.o obj/tmp_$slot.o
  objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_$slot obj/tmp_$slot.o obj/$slot.o
  objs="$objs obj/$slot.o"
  i=$((i+1))
done
gcc -O2 -o bench bench.c $objs
echo "linked bench with: $*"
nm bench | grep -E ' T dec_s' | sort
