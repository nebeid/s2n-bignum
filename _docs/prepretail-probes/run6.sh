#!/bin/bash
cd /tmp/pfx
echo "### KAT: cost-only probes must be 35/35 (they write only dead regs)"
for v in mixpp mixpr ppload96; do echo "-- $v"; ./kat.sh $v 2>&1 | tail -2; done
echo "### KAT: drain0 must fail EXACTLY on nblk%8==0 (proves the probe is on a live path)"
./kat.sh drain0 2>&1 | grep -E "FAIL|SUMMARY|GATE" | head -20
export ALLOW_MISMATCH=1
for v in fusepp_front fusepp_mid fusepp_back; do ./mk.sh $v >/dev/null; done
echo "=== R6 PLACEMENT: base AA fusepp_front fusepp_mid fusepp_back"
./build_bench.sh base base fusepp_front fusepp_mid fusepp_back >/dev/null; taskset -c 3 ./bench 200
