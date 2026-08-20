#!/bin/bash
# mk.sh <variant> -> obj/<v>.o   (mirrors arm/Makefile and /tmp/fsw/mk.sh exactly)
set -e
cd /tmp/pl
v="$1"
gcc -E -Iinclude -xassembler-with-cpp - < src/$v.S | tr ";" "\n" | as -march=armv8.2-a+sha3 -o obj/$v.o -
