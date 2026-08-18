#!/bin/bash
# aead.sh <label> <core> <reps> <timeout_ms>
set -e
lbl="$1"; core="$2"; reps="$3"; tmo="$4"
CH=16,32,64,128,256,512,1024,4096
out=/tmp/fsp/logs/aead_$lbl.txt
: > $out
for r in $(seq 1 $reps); do
  for v in A B C; do
    echo "### rep=$r variant=$v"
    ( cd /tmp/awslc_$v/build && taskset -c $core ./tool/bssl speed \
        -filter AEAD-AES-256-GCM -chunks $CH -timeout_ms $tmo 2>&1 )
  done
done >> $out
echo "AEAD_DONE $lbl"
