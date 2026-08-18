#!/bin/bash
# runall_g4.sh <label> <core> : the full g4 measurement sweep on this host
set -e
cd /tmp/fsp
L="$1"; C="${2:-3}"
echo "### CLOCK";       taskset -c $C ./clk | tee logs/clk_$L.txt
echo "### VERIFY";      CORE=$C ./verify_g4.sh > logs/verify_$L.txt 2>&1; tail -16 logs/verify_$L.txt
echo "### PROBES";      CORE=$C ./probe_g4.sh  > logs/probe_$L.txt  2>&1; tail -30 logs/probe_$L.txt
echo "### PER-LENGTH";  ./measure_g4.sh $L $C 300 5 > /dev/null
echo "### DECOMPOSE";   ./measure_aux_g4.sh $L $C 200 2 > /dev/null
echo "### MIXES";       ./measure_mixg4.sh $L $C 150 3 > /dev/null
echo "### MIX CTRLS";   ./mixaa_g4.sh $C 150 2 > /dev/null
echo "### DONE $L"
