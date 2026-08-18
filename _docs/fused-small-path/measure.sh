#!/bin/bash
# measure.sh <label> <core> <reps> <nproc>
set -e
cd /tmp/fsp
lbl="$1"; core="$2"; reps="$3"; np="$4"
SLOTS="base baseAA awslcfb awslc8x tuned fuse8"
./build_bench.sh base base awslcfb awslc8x tuned fuse8
taskset -c $core ./clk
for p in $(seq 1 $np); do
  echo "=== process $p"
  taskset -c $core ./bench "$reps" $SLOTS
done | tee logs/$lbl.log
