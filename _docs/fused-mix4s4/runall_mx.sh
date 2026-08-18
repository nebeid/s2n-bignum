#!/bin/bash
# runall_mx.sh <label> <core> : full mix4s4 measurement sweep on this host
set -e
cd /tmp/fsp
L="$1"; C="${2:-3}"
echo "### CLOCK";     taskset -c $C ./clk | tee logs/clk_$L.txt
echo "### VERIFY";    CORE=$C ./verify_mx.sh > logs/verify_$L.txt 2>&1; tail -14 logs/verify_$L.txt
echo "### PROBES";    CORE=$C ./probe_mx.sh  > logs/probe_$L.txt  2>&1; grep -c . logs/probe_$L.txt
echo "### PER-LENGTH"; ./measure_mx.sh $L $C 300 5 > /dev/null
echo "### MIXES";     ./measure_mixmx.sh $L $C 150 3 > /dev/null
echo "### MIX CTRLS"; ./mixaa_mx.sh $C 150 2 > /dev/null
echo "### DONE $L"
