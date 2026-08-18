#!/bin/bash
# provision_w1.sh : generate + assemble every ordering variant of the W=1
# four-section fused cascade.  Works in /tmp/fsw, which is a COPY of the g4
# experiment's /tmp/fsp (same base.S, same mk.sh, same kat harness, same
# objcmp.py, same generators), so every object here is built exactly the way the
# published runs built theirs.
#
# THE CONTROL THAT MAKES THIS A CONTROLLED EXPERIMENT: `w1` (all knobs at their
# defaults) must reproduce gen_mix.py's `s4h` object BIT FOR BIT.
set -e
cd /tmp/fsw
mkdir -p obj logs src
KSEC=1.0; MK1=0.35                    # the published cascade split points
K=0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70

g () { python3 gen_w1.py src/base.S src/$1.S $2 "${@:3}" >/dev/null; }

# ---- the published baseline, twice: once from gen_mix.py, once from gen_w1.py
python3 gen_mix.py src/base.S src/s4h.S 1,1,1,1 $KSEC $MK1 mxh hoist >/dev/null
g w1   mxh k=$KSEC K=$MK1
python3 gen_trunc.py src/base.S src/dsp0.S 0 $K >/dev/null

# ---- 1. K-split sweep: where the GHASH product ops sit among the AES rounds
g ka   w1a k=0.15 K=$MK1
g kb   w1b k=0.35 K=$MK1
g kc   w1c k=0.55 K=$MK1
g kd   w1d k=0.75 K=$MK1
# ---- 2. the terminal section's MODULO split
g Ka   w1e k=$KSEC K=0.15
g Kb   w1f k=$KSEC K=0.20
g Kc   w1g k=$KSEC K=0.55
g Kd   w1h k=$KSEC K=0.70
# ---- 3. product window start offset, and clumping between AES pairs
g gs30 w1i k=$KSEC K=$MK1 gs=0.3
g gs50 w1j k=$KSEC K=$MK1 gs=0.5
g cl2  w1k k=$KSEC K=$MK1 clump=2
g cl3  w1l k=$KSEC K=$MK1 clump=3
g cl4  w1m k=$KSEC K=$MK1 clump=4
# ---- 4. ciphertext load at the very top of the section
g cthd w1n k=$KSEC K=$MK1 ct=head
# ---- 5. end-relative static addressing (no post-index address chain)
g ptre w1o k=$KSEC K=$MK1 ptr=end
# ---- 6. dispatch: nblk=4 falls through; and the seed merged into section 4
g f4   w1p k=$KSEC K=$MK1 dsp=f4
g f4i  w1q k=$KSEC K=$MK1 dsp=f4i
g f4iE w1r k=$KSEC K=$MK1 dsp=f4i ptr=end
g f4iH w1s k=$KSEC K=$MK1 dsp=f4i ct=head
# ---- 7. section order / adjacency at the boundaries
g lbr  w1t k=$KSEC K=$MK1 lay=br
g lrev w1u k=$KSEC K=$MK1 lay=rev
# ---- 8. DIAGNOSTIC upper bounds (WRONG output on purpose, never shipped)
g dctr w1v k=$KSEC K=$MK1 ctr=free
g dct  w1w k=$KSEC K=$MK1 ctfree=1
g dbot w1x k=$KSEC K=$MK1 ctr=free ctfree=1

VAR="s4h w1 dsp0 ka kb kc kd Ka Kb Kc Kd gs30 gs50 cl2 cl3 cl4 cthd ptre f4 f4i f4iE f4iH lbr lrev"
DIAG="dctr dct dbot"
for v in $VAR $DIAG; do ./mk.sh $v; done
[ -f obj/ref.o ] || ./mk.sh ref

echo "=== CONTROL: gen_w1.py defaults == gen_mix.py s4h, bit for bit ==="
a=$(md5sum obj/w1.o | cut -d' ' -f1); b=$(md5sum obj/s4h.o | cut -d' ' -f1)
[ "$a" = "$b" ] && echo "  w1=$a s4h=$b  SAME" || { echo "  w1=$a s4h=$b  DIFFER"; exit 1; }
echo "=== base.o must be 114cedb51f36c584e50843d2838d871e ==="
md5sum obj/base.o

echo "=== .text sizes ==="
{ for v in base $VAR $DIAG; do
  t=$(objdump -h obj/$v.o | awk '$2==".text"{print strtonum("0x"$3)}')
  printf "%-6s %-6s x%.4f\n" "$v" "$t" "$(echo "$t/4968" | bc -l)"
done; } | tee logs/text.txt

echo "=== md5 (must be identical on every host) ==="
for v in base $VAR $DIAG; do md5sum obj/$v.o; done | tee logs/md5.txt
