#!/bin/bash
# run.sh <reps> <core> <variants...>
set -e
cd /tmp/fsp
reps="$1"; core="$2"; shift 2
for v in "$@"; do [ -f obj/$v.o ] || ./mk.sh $v; done
./build_bench.sh "$@"
echo "SLOTS: $*"
taskset -c $core ./bench "$reps" "$@"
