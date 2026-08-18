#!/usr/bin/env python3
"""bench_mix.c -> bench_mix2.c : APPEND mixes to the existing mixed-length
harness without touching the ones already published.

Mixes A..E keep their exact pseudorandom sequences: the generator draws them
from one LCG stream in a fixed order per element, and the new draws are appended
AFTER seq[4][i] inside the same loop iteration, so seq[0..4] are bit-identical
to bench_mix.c's.

Appended:
  F   60 % nblk = 8, else uniform 1..4          (a realistic 128 B-heavy stream)
  R1  only nblk in {5,8}, ratio 1:1 of 8s to 5s |
  R2  ... 2:1                                   | the 128 B : 80 B traffic-ratio
  R3  ... 3:1                                   | scan that locates the t4p8 /
  R4  ... 4:1                                   | t5 break-even point
  R6  ... 6:1                                   |
"""
import sys, re

src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()

def sub1(t, old, new):
    assert t.count(old) == 1, "anchor not unique: %r" % old[:60]
    return t.replace(old, new)

t = sub1(t, "#define NMIX 5", "#define NMIX 11\nstatic const uint32_t RAT[5] = {1u,2u,3u,4u,6u};")

t = sub1(t,
         "    seq[4][i]=1u + (uint32_t)((z>>33)%4u);\n",
         "    seq[4][i]=1u + (uint32_t)((z>>33)%4u);\n"
         "    /* F: 60% nblk=8 (128 B), else uniform 1..4 */\n"
         "    z = z*6364136223846793005ULL + 1442695040888963407ULL;\n"
         "    seq[5][i] = ((uint32_t)((z>>33)%5u) < 3u) ? 8u\n"
         "                : (1u + (uint32_t)((z>>45)%4u));\n"
         "    /* R1..R6: ONLY nblk=8 (128 B) and nblk=5 (80 B), ratio RAT[j]:1 */\n"
         "    for(int j=0;j<5;j++){\n"
         "      z = z*6364136223846793005ULL + 1442695040888963407ULL;\n"
         "      uint32_t rr = RAT[j];\n"
         "      seq[6+j][i] = ((uint32_t)((z>>33)%(rr+1u)) < rr) ? 8u : 5u;\n"
         "    }\n")

t = sub1(t, 'const char *mn[NMIX]={"A","B","C","D","E"};',
            'const char *mn[NMIX]={"A","B","C","D","E","F","R1","R2","R3","R4","R6"};')

open(dst, "w").write(t)
print("wrote %s (NMIX=11)" % dst)
