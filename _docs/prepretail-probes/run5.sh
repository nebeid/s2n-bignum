#!/bin/bash
cd /tmp/pfx
export ALLOW_MISMATCH=1
for v in mixpp mixpr fusepp fusepr fusepp_corr fusepr_corr; do ./mk.sh $v >/dev/null; done
echo "=== R5A COST-ONLY (selfcheck MUST pass): base AA mixpp mixpr drain0"
./build_bench.sh base base mixpp mixpr drain0 >/dev/null; taskset -c 3 ./bench 200
echo "=== R5B NET EMULATION: base AA fusepp fusepr expA"
./build_bench.sh base base fusepp fusepr expA >/dev/null; taskset -c 3 ./bench 200
echo "=== R5C NET + T*H^8 CORRECTION: base AA fusepp_corr fusepr_corr expA"
./build_bench.sh base base fusepp_corr fusepr_corr expA >/dev/null; taskset -c 3 ./bench 200
