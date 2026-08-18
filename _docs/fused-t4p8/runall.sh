#!/bin/bash
# runall.sh <label> <core> : full t4p8 measurement sweep on this host
set -e
cd /tmp/fsp
L="$1"; C="${2:-3}"
echo "### CLOCK"; taskset -c $C ./clk
echo "### VERIFY"; CORE=$C ./verify_p8.sh 2>&1 | tail -20
echo "### MIXES (priority 1)"; ./measure_mixp8.sh $L $C 150 3 > /dev/null
echo "### PER-LENGTH"; ./measure_p8.sh ${L}_os1 $C 300 5 1 > /dev/null
echo "### MIX CONTROLS"; ./mixaa_p8.sh $C 150 2 > /dev/null
echo "### DONE $L"
