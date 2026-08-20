#!/bin/bash
# runall.sh <core> <hosttag>
# One timing process at a time, pinned to a single non-zero core.
set -e
cd /tmp/pl
core="$1"; tag="$2"
mkdir -p logs
export LC_ALL=C

echo "== phase 1: exact banked pcb4 replication (8 sizes, 32 processes) =="
: > logs/p1_$tag.txt
for p in $(seq 1 32); do taskset -c $core ./pcb4 150 $p >> logs/p1_$tag.txt; done
echo "phase1 done $(date -u +%H:%M:%S)"

echo "== phase 2: placement sweep (5 link orders + 5 leading pads, 32 processes) =="
for cfg in P0 P1 P2 P3 P4 PAD16 PAD64 PAD128 PAD256 PAD1024; do
  : > logs/$cfg.txt
  for p in $(seq 1 32); do taskset -c $core ./bin/$cfg 50 $p >> logs/$cfg.txt; done
  echo "  $cfg done $(date -u +%H:%M:%S)"
done

echo "== phase 3: main-loop offset sweep (entry 64-aligned, 40 processes) =="
for cfg in A2X2 ACSW ADSW; do
  : > logs/$cfg.txt
  for p in $(seq 1 40); do taskset -c $core ./bin/$cfg 50 $p >> logs/$cfg.txt; done
  echo "  $cfg done $(date -u +%H:%M:%S)"
done
echo "ALL DONE $tag $(date -u +%H:%M:%S)"
