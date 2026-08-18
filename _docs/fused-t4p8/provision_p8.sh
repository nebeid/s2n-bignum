#!/bin/bash
# provision_p8.sh : generate + assemble everything the t4p8 experiment needs.
#
#   t4  t5  t7  t8   contiguous truncations (gen_trunc.py), the comparison set
#   dsp0             the pure-dispatch control (gen_trunc.py with C = 0)
#   g4 g5 g7 g8      gen_set.py on the CONTIGUOUS sets {1..C}: these objects MUST
#                    be md5-identical to t4/t5/t7/t8, which is the proof that
#                    gen_set.py is a strict generalisation and changes nothing
#   t4p8             bodies {1,2,3,4,8}, dispatch order "small" (design A)
#   t4p8b            same bodies, dispatch order "big"   (design B)
set -e
cd /tmp/fsp
mkdir -p obj logs src
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70

python3 gen_trunc.py src/base.S src/dsp0.S 0 $K >/dev/null; ./mk.sh dsp0
for C in 4 5 7 8; do
  python3 gen_trunc.py src/base.S src/t$C.S $C $K >/dev/null; ./mk.sh t$C
  python3 gen_set.py   src/base.S src/g$C.S $(seq -s, 1 $C) $K small >/dev/null; ./mk.sh g$C
done
python3 gen_set.py src/base.S src/t4p8.S  1,2,3,4,8 $K small >/dev/null; ./mk.sh t4p8
python3 gen_set.py src/base.S src/t4p8b.S 1,2,3,4,8 $K big   >/dev/null; ./mk.sh t4p8b
[ -f obj/ref.o ] || ./mk.sh ref

echo "=== gen_set.py vs gen_trunc.py on contiguous sets (must be SAME) ==="
for C in 4 5 7 8; do
  a=$(md5sum obj/t$C.o | cut -d' ' -f1); b=$(md5sum obj/g$C.o | cut -d' ' -f1)
  [ "$a" = "$b" ] && r=SAME || r="DIFFER"
  printf "  {1..%d}: t%d=%s g%d=%s  %s\n" "$C" "$C" "$a" "$C" "$b" "$r"
done

echo "=== md5 ==="
md5sum obj/base.o obj/dsp0.o obj/t4.o obj/t5.o obj/t7.o obj/t8.o obj/t4p8.o obj/t4p8b.o

echo "=== .text sizes ==="
for v in base dsp0 t4 t5 t7 t8 t4p8 t4p8b; do
  printf "%-6s %s\n" "$v" "$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')"
done
