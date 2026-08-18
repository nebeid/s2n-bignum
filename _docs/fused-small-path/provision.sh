#!/bin/bash
# provision.sh : build every object + variant on the current host
set -e
cd /tmp/fsp
mkdir -p obj logs
chmod +x *.sh
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70
python3 gen.py src/base.S src/tuned.S  fuse  $K   >/dev/null
python3 gen.py src/base.S src/fuse8.S  fuse8 $K   >/dev/null
for v in base ref tuned fuse8; do ./mk.sh $v; done
gcc -c -Iinclude -o obj/awslcfb.o src/aesv8-gcm-armv8.S        -march=armv8.2-a+crypto+sha3
gcc -c -Iinclude -o obj/awslc8x.o src/aesv8-gcm-armv8-unroll8.S -march=armv8.2-a+crypto+sha3
gcc -c -Iinclude -o obj/aesv8armx.o src/aesv8-armx.S  -march=armv8.2-a+crypto+sha3
gcc -c -Iinclude -o obj/ghashv8.o  src/ghashv8-armx.S -march=armv8.2-a+crypto+sha3
ld -r -o obj/awslchelp.o obj/aesv8armx.o obj/ghashv8.o
gcc -O2 -o clk clk.c
echo "provisioned: $(md5sum obj/base.o)"
