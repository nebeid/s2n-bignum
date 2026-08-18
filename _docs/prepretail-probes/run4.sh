#!/bin/bash
cd /tmp/pfx
export ALLOW_MISMATCH=1
for v in ppload4 ppload8 ppload16 ppload32 prol48 prol96 pptail32; do ./mk.sh $v >/dev/null; done
echo "=== R4A: base AA ppload4 ppload8 ppload16"
./build_bench.sh base base ppload4 ppload8 ppload16 >/dev/null; taskset -c 3 ./bench 200
echo "=== R4B: base AA ppload32 pptail32 prol48"
./build_bench.sh base base ppload32 pptail32 prol48 >/dev/null; taskset -c 3 ./bench 200
echo "=== R4C: base AA prol96 ppload96 drain0"
./build_bench.sh base base prol96 ppload96 drain0 >/dev/null; taskset -c 3 ./bench 200
