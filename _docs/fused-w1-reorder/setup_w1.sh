#!/bin/bash
# setup_w1.sh : stand up the W=1 reordering experiment in /tmp/fsw on this host.
# /tmp/fsw is a copy of the already-provisioned /tmp/fsp (same src/base.S, same
# mk.sh, same kat/ harness, same objcmp.py / verify_mx.py, same clk), so nothing
# is rebuilt from scratch and every object is produced the published way.
# No tracked file is touched; ~/clean-gate and ~/kat-check are not touched.
set -e
[ -d /tmp/fsp ] || { echo "FATAL: /tmp/fsp missing"; exit 1; }
mkdir -p /tmp/fsw
cp -a /tmp/fsp/. /tmp/fsw/
cd /tmp/fsw
rm -rf __pycache__
sed -i 's#/tmp/fsp#/tmp/fsw#g' *.sh *.py
tar xzf /tmp/fsw-add.tgz
chmod +x *.sh
[ -f bench12g.c ] || python3 mkbench12g.py bench12.c bench12g.c
python3 mkbench6.py bench12g.c bench6.c
gcc -O2 -o clk clk.c
./mk.sh base
echo "=== base.o md5 (must be 114cedb51f36c584e50843d2838d871e) ==="
md5sum obj/base.o
./provision_w1.sh
