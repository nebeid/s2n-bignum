#!/bin/bash
# build6.sh <variant names...>  (up to 12; a trailing "AA" means "the same
# object again in a different link slot", i.e. that variant's own A/A floor)
# objcopy --redefine-sym each object to its own symbol and link ALL of them into
# ONE binary, exactly as build_bench12g.sh does.
set -e
cd /tmp/fsw
i=0; objs=""
for v in "$@"; do
  o="${v%AA}"
  slot="s$i"
  objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_$slot \
          --keep-global-symbol=dec_$slot obj/$o.o obj/b$slot.o
  objs="$objs obj/b$slot.o"; i=$((i+1))
done
rm -f bench6
gcc -O2 -DNV=$# -o bench6 bench6.c $objs obj/awslchelp.o
