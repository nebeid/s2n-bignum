#!/bin/bash
cd /tmp/pfx
export ALLOW_MISMATCH=1
for v in drain0 drain4 ppload24 ppload48 ppload72 ppload96; do ./mk.sh $v >/dev/null; done
echo "=== ROUND2: base AA drain0 drain4 ppload48"
./build_bench.sh base base drain0 drain4 ppload48 >/dev/null
for p in 1 2; do echo "### p$p"; taskset -c 3 ./bench 200; done
echo "=== ROUND3: base AA ppload24 ppload72 ppload96"
./build_bench.sh base base ppload24 ppload72 ppload96 >/dev/null
for p in 1 2; do echo "### p$p"; taskset -c 3 ./bench 200; done
