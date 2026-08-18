#!/bin/bash
# provision_t.sh : generate + assemble every truncation variant on this host.
#   t2..t8   truncated eight-body fused path, cutoff C = 2..8
#            (t8 must be byte-identical to the full variant's tuned.o)
#   cw4t     width-4 cascade for nblk <= 7 + existing path at nblk = 8
set -e
cd /tmp/fsp
mkdir -p obj logs src
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70
for C in 2 3 4 5 6 7 8; do
  python3 gen_trunc.py src/base.S src/t$C.S $C $K
  ./mk.sh t$C
done
python3 gen_cascWt.py src/base.S src/cw4t.S 4 7 1.0 0.35 cwt
./mk.sh cw4t
[ -f obj/tuned.o ] || { python3 gen.py src/base.S src/tuned.S fuse $K; ./mk.sh tuned; }
echo "=== md5 (t8 must equal tuned) ==="
md5sum obj/base.o obj/tuned.o obj/t8.o
echo "=== .text sizes ==="
for v in base tuned t2 t3 t4 t5 t6 t7 t8 cw4t; do
  printf "%-6s %s\n" "$v" "$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')"
done
