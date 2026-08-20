#!/bin/bash
# build.sh : assemble the four kernels, give each a distinct exported symbol,
# link ALL of them plus four byte-identical A/A duplicates into ONE binary.
set -e
cd /tmp/pcb4

for v in A B C D; do ./mk.sh $v; done

# slot -> variant object, and the symbol each object exports
#  0 A   1 B   2 C   3 D   4 A(dup)  5 B(dup)  6 C(dup)  7 D(dup)
SLOTOBJ=(A B C D A B C D)
objs=""
for i in 0 1 2 3 4 5 6 7; do
  o=${SLOTOBJ[$i]}
  if [ "$o" = "A" ]; then SYM=aesv8_gcm_8x_dec_256; else SYM=aesv8_gcm_8x_dec_256_wb; fi
  # --keep-global-symbol also localises A's five sibling functions, so the two
  # copies of the aws-lc object can coexist in one link without symbol clashes.
  objcopy --redefine-sym ${SYM}=dec_s$i --keep-global-symbol=dec_s$i \
          obj/$o.o obj/slot$i.o
  objs="$objs obj/slot$i.o"
done

rm -f pcb4
gcc -O2 -o pcb4 harness.c $objs obj/awslchelp.o
echo "=== exported dec_ symbols in the binary ==="
nm pcb4 | grep -E ' T dec_s' | sort -k3
echo "=== byte-identical duplicate check (slot i vs slot i+4 code) ==="
for i in 0 1 2 3; do
  a=$(objcopy -O binary --only-section=.text obj/slot$i.o /dev/stdout 2>/dev/null | md5sum | cut -d' ' -f1)
  b=$(objcopy -O binary --only-section=.text obj/slot$((i+4)).o /dev/stdout 2>/dev/null | md5sum | cut -d' ' -f1)
  [ "$a" = "$b" ] && echo "  slot$i == slot$((i+4))  ($a)" || echo "  slot$i != slot$((i+4))  MISMATCH"
done
