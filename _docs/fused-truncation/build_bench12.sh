#!/bin/bash
# build_bench12.sh <variant basenames...>   (up to 12)
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
  objcopy --redefine-sym $sym=dec_$slot --keep-global-symbol=dec_$slot $src obj/b$slot.o
  objs="$objs obj/b$slot.o"; i=$((i+1))
done
rm -f bench12
gcc -O2 -DNV=$# -o bench12 bench12.c $objs obj/awslchelp.o
