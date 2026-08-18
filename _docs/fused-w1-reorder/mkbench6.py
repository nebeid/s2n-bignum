#!/usr/bin/env python3
"""bench12g.c -> bench6.c : the SAME harness (same self-check over all 256
whole-block lengths, same warm-up, same round-robin with the slot order rotated
per rep, same best-of-N min estimator, same 12 slots), restricted to the six
lengths this experiment needs and with a smaller per-rep iteration budget so a
30-variant sweep fits in the available wall time.

  sizes   {1,2,3,4,5,256} blocks = 16, 32, 48, 64 B (the fused path),
          80 B (the first fall-through length) and 4096 B (the bulk check).
  budget  200000 -> 60000, and the minimum iteration count 2000 -> 50 (needed
          only by the 256-block size, where 50 calls is already a 40 us window).

Nothing else changes, so the published Delta % must be reproduced; that is
asserted by provision_w1.sh's anchor check (w1 == s4h at 16/32/48/64 B).

Usage: mkbench6.py bench12g.c bench6.c
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()
subs = [("static const size_t sizes[] = {1,2,3,4,5,6,7,8,16,32,64,256};",
         "static const size_t sizes[] = {1,2,3,4,5,256};"),
        ("long long budget = 200000;", "long long budget = 60000;"),
        ("if(iters<2000) iters=2000;", "if(iters<50) iters=50;")]
for a, b in subs:
    assert a in t, "anchor not found: %r" % a
    t = t.replace(a, b, 1)
open(dst, "w").write(t)
print("wrote", dst)
