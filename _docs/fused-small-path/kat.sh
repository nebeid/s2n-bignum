#!/bin/bash
# kat.sh <variant> : relink the differential KAT harness against the variant.
set -e
cd /tmp/fsp
[ -f obj/ref.o ] || ./mk.sh ref
./mk.sh "$1"
rm -f kat/kat_wb_dec
gcc -O2 -Wall -Wextra -std=c11 -o kat/kat_wb_dec kat/kat_wb_dec.c obj/$1.o obj/ref.o
./kat/kat_wb_dec
