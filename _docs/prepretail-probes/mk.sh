#!/bin/bash
# mk.sh <variant-basename>  -> obj/<v>.o (native symbol) and obj/<v>_<slot>.o on demand
# Mirrors arm/Makefile: gcc -E | tr ';' '\n' | as -march=armv8.2-a+sha3
set -e
cd /tmp/pfx
v="$1"
gcc -E -Iinclude -xassembler-with-cpp - < src/$v.S | tr ';' '\n' | as -march=armv8.2-a+sha3 -o obj/$v.o -
echo "built obj/$v.o"
