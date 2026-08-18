#!/bin/bash
# build_bench.sh <variant basenames...>
# Special names: awslcfb = aws-lc aes_gcm_dec_kernel (4x fallback, void return)
#                awslc8x = aws-lc aesv8_gcm_8x_dec_256 (shipped 8x kernel)
set -e
cd /tmp/fsp
i=0; objs=""
for v in "$@"; do
  slot="s$i"
  case "$v" in
    awslcfb*) src=obj/awslcfb.o; sym=aes_gcm_dec_kernel ;;
    awslc8x*) src=obj/awslc8x.o; sym=aesv8_gcm_8x_dec_256 ;;
    *)        src=obj/$v.o;      sym=aesv8_gcm_8x_dec_256_wb ;;
  esac
  objcopy --redefine-sym $sym=dec_$slot --keep-global-symbol=dec_$slot $src obj/$slot.o
  objs="$objs obj/$slot.o"; i=$((i+1))
done
gcc -O2 -DNV=$# -o bench bench.c $objs obj/awslchelp.o
