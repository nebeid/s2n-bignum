#!/usr/bin/env python3
"""bench12.c -> bench12g.c : add the check that the DISCARDED blocks of a g4
group are not observable in the output buffer.

The g4 group always runs four blocks and always issues four stores; for
nblk < 4 the surplus lanes write block 0 (which the real block 0 then
overwrites).  The characteristic bug of that design is writing 16*4 bytes when
only 16*nblk were asked for, so the self-check pre-fills every output buffer
with 0xA5 for 64 bytes PAST the message and asserts those bytes are still 0xA5
after the call, for EVERY variant (including link slot 0) at every one of the
256 whole-block lengths.  Everything else in bench12.c is untouched.

Usage: mkbench12g.py bench12.c bench12g.c
"""
import sys, re

src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()

anchor = "    for(int v=1;v<NV;v++){\n      int bo="
assert anchor in t, "bench12.c selfcheck loop not found"
add = """    for(int v=0;v<NV;v++){
      for(size_t k=nb*BLK;k<nb*BLK+64;k++) if(out[v][k]!=0xA5){
        printf("TAILWRITE nblk=%zu variant %s: byte +%zu past the message was written\\n",
               nb, NAME[v], k-nb*BLK); bad=1; break; }
    }
"""
t = t.replace(anchor, add + anchor, 1)
t = t.replace('printf("SELFCHECK OK (%d whole-block lengths 1..256 blk x %d variants; '
              'out/Xi/ivec/ret byte-identical)\\n", nsz, NV);',
              'printf("SELFCHECK OK (%d whole-block lengths 1..256 blk x %d variants; '
              'out/Xi/ivec/ret byte-identical, nothing written past 16*nblk)\\n", nsz, NV);', 1)
open(dst, "w").write(t)
print("wrote", dst)
