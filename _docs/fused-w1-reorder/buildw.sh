#!/bin/bash
# buildw.sh <variant names...> (up to 12; a trailing "AA" = the same object
# again in another link slot, i.e. that variant's own placement/A-A floor).
# Links the PUBLISHED 12-size harness bench12g.c, so the numbers are directly
# comparable with _docs/fused-mix4s4.md and _docs/fused-g4.md.
set -e
cd /tmp/fsw
i=0; objs=""
for v in "$@"; do
  o="${v%AA}"; slot="s$i"
  objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_$slot \
          --keep-global-symbol=dec_$slot obj/$o.o obj/b$slot.o
  objs="$objs obj/b$slot.o"; i=$((i+1))
done
rm -f benchw
gcc -O2 -DNV=$# -o benchw bench12g.c $objs obj/awslchelp.o
