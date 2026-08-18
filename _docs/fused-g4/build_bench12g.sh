#!/bin/bash
# build_bench12g.sh <variant basenames...>  (up to 12)
# build_bench12.sh, but linking bench12g.c (the byte-compare additionally
# asserts nothing is written past 16*nblk -- the characteristic g4 bug).
set -e
cd /tmp/fsp
[ -f bench12g.c ] || python3 mkbench12g.py bench12.c bench12g.c
i=0; objs=""
for v in "$@"; do
  slot="s$i"
  objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_$slot \
          --keep-global-symbol=dec_$slot obj/$v.o obj/b$slot.o
  objs="$objs obj/b$slot.o"; i=$((i+1))
done
rm -f bench12g
gcc -O2 -DNV=$# -o bench12g bench12g.c $objs obj/awslchelp.o
