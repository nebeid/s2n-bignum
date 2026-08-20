#!/usr/bin/env python3
"""gen_variant.py SRC OUT [--pad N] [--entry-align N]

Emit a copy of SRC (C.S or D.S) with

  * a global label `ml_mark` placed exactly at `.L256_dec_main_loop:`
    so the main-loop address is visible to nm;
  * optionally N bytes (N multiple of 4) of `nop` inserted immediately
    BEFORE the main loop, which shifts the whole main loop / prepretail /
    tail band forward by N bytes inside the function.  The nops are
    executed at most once per call (the main loop is entered by
    fall-through from `b.ge .L256_dec_prepretail`), never inside the loop;
  * optionally the function-entry `.align 4` replaced by `.balign N`, which
    also raises the object's .text alignment so the linker places the
    function entry at an N-byte boundary.  Padding before the entry is
    never executed.

Nothing else is touched: the instruction stream is byte-identical to the
input apart from the requested nops.
"""
import sys, re

src, out = sys.argv[1], sys.argv[2]
pad = 0
ealign = 0
a = sys.argv[3:]
while a:
    if a[0] == "--pad":
        pad = int(a[1]); a = a[2:]
    elif a[0] == "--entry-align":
        ealign = int(a[1]); a = a[2:]
    else:
        sys.exit("bad arg " + a[0])
assert pad % 4 == 0

lines = open(src).read().split("\n")
o = []
done_align = False
done_ml = False
for L in lines:
    if not done_align and ealign and re.match(r"^\s*\.align\s+4\s*$", L):
        o.append("\t.balign %d" % ealign)
        done_align = True
        continue
    if not done_ml and L.startswith(".L256_dec_main_loop:"):
        for _ in range(pad // 4):
            o.append("\tnop")
        o.append("\t.globl ml_mark")
        o.append("ml_mark:")
        done_ml = True
    o.append(L)
if not done_ml:
    sys.exit("main loop label not found in " + src)
if ealign and not done_align:
    sys.exit("entry .align 4 not found in " + src)
open(out, "w").write("\n".join(o))
print("%s -> %s  pad=%d entry_align=%d" % (src, out, pad, ealign))
