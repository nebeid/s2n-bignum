#!/bin/bash
# makekat_t.sh : KAT per variant through the REAL top-level arm/Makefile and the
# real arm/aes-gcm/kat/Makefile, in a scratch COPY of the tree (no tracked file
# is touched, and `make clean` is never run in the tracked arm/aes-gcm/kat).
#
#   arm/Makefile's own  %.o : %.S  rule assembles the variant .S,
#   then  make -C aes-gcm/kat run  RE-LINKS kat_wb_dec against that fresh .o
#   (the binary is deleted first, so a stale link cannot be tested).
#
# Also asserts the make-built object is byte-identical to /tmp/fsw/obj/<v>.o,
# i.e. that mk.sh reproduces the Makefile rule exactly.
set -e
SRC=$HOME/whole-proofs/s2n-bignum
T=/tmp/fsw-mk/tree
rm -rf /tmp/fsw-mk; mkdir -p $T/arm
cp $SRC/arm/Makefile $T/arm/
cp -r $SRC/arm/aes-gcm $T/arm/
cp -r $SRC/include $T/
chmod -R u+w $T
# cp -r does not preserve mtimes, so make would try to rebuild the FROZEN
# reference objects from their .S with its builtin rule.  Mark them up to date.
touch $T/arm/aes-gcm/*.o
for v in "$@"; do
  cp /tmp/fsw/src/$v.S $T/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S
  rm -f $T/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o $T/arm/aes-gcm/kat/kat_wb_dec
  ( cd $T/arm && make aes-gcm/aesv8_gcm_8x_dec_256_wb.o >/dev/null )
  m1=$(md5sum $T/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o | cut -d' ' -f1)
  m2=$(md5sum /tmp/fsw/obj/$v.o | cut -d' ' -f1)
  [ "$m1" = "$m2" ] && same=SAME || same="DIFFER($m1 vs $m2)"
  r=$( cd $T/arm/aes-gcm/kat && make run 2>&1 | tail -2 | tr '\n' ' ' )
  printf "%-6s make-built .o vs mk.sh .o: %-6s | %s\n" "$v" "$same" "$r"
done
