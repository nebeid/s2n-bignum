#!/bin/bash
# mk.sh <variant-basename>  -> obj/<v>.o
# Mirrors arm/Makefile: gcc -E | tr ';' '\n' | as -march=armv8.2-a+sha3
set -e
cd /tmp/fsp
v="$1"
gcc -E -Iinclude -xassembler-with-cpp - < src/$v.S | tr ';' '\n' | as -march=armv8.2-a+sha3 -o obj/$v.o -
