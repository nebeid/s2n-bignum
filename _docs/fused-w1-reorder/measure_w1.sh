#!/bin/bash
# measure_w1.sh <binlabel> <hostlabel> <core> <reps> <nproc> <variants...>
#
# The published discipline, unchanged: every variant objcopy --redefine-sym'd
# into ONE binary (bench12g.c, 12 lengths), timed round-robin with the slot
# order rotated every rep, `taskset` to one non-zero core, 200-call warm-up per
# pass, best-of-<reps>, THREE link orderings x <nproc> processes, `base` pinned
# to link slot 0 in every ordering.  The in-process byte-compare over all 256
# whole-block lengths runs at the start of EVERY process.
set -e
cd /tmp/fsw
bl="$1"; hl="$2"; core="$3"; reps="$4"; np="$5"; shift 5
O1="$*"
h=$(echo $O1 | awk '{print $1}')
t=$(echo $O1 | cut -d' ' -f2-)
O2="$h $(echo $t | tr ' ' '\n' | tac | tr '\n' ' ')"
n=$(echo $t | wc -w); k=$(( n / 2 ))
O3="$h $(echo $t | cut -d' ' -f$((k+1))-) $(echo $t | cut -d' ' -f1-$k)"
taskset -c "$core" ./clk
{
echo "## bin=$bl host=$hl core=$core reps=$reps nproc=$np"
for oi in 1 2 3; do echo "## O$oi: $(eval echo \$O$oi)"; done
for oi in 1 2 3; do
  eval "O=\$O$oi"
  ./buildw.sh $O
  for p in $(seq 1 "$np"); do
    echo "=== process $bl.order$oi.$p"
    taskset -c "$core" ./benchw "$reps" $O
  done
done
} 2>&1 | tee logs/${bl}_$hl.log
