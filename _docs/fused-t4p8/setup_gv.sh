#!/bin/bash
# unpack + provision the t4p8 experiment on a fresh host
set -e
mkdir -p /tmp/fsp
cd /tmp/fsp
tar xzf /tmp/fsp-min.tgz
mkdir -p obj logs src
chmod +x *.sh
gcc -O2 -o clk clk.c
python3 mkmix2.py bench_mix.c bench_mix2.c
./mk.sh base
echo "=== base.o md5 (must be 114cedb51f36c584e50843d2838d871e) ==="
md5sum obj/base.o
./provision_p8.sh
