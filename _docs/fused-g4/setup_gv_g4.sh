#!/bin/bash
# setup_gv_g4.sh : unpack + provision the g4 experiment on a fresh host.
set -e
mkdir -p /tmp/fsp
cd /tmp/fsp
tar xzf /tmp/fsp-g4.tgz
mkdir -p obj logs src
chmod +x *.sh
gcc -O2 -o clk clk.c
[ -f bench_mix2.c ] || python3 mkmix2.py bench_mix.c bench_mix2.c
python3 mkbench12g.py bench12.c bench12g.c
./mk.sh base
echo "=== base.o md5 (must be 114cedb51f36c584e50843d2838d871e) ==="
md5sum obj/base.o
./provision_g4.sh
