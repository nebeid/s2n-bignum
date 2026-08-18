#!/usr/bin/env python3
"""Emit the markdown deliverable tables for the truncation curve."""
import re, sys, statistics as st
from analyze_t import parse

LEN = [16, 32, 48, 64, 80, 96, 112, 128, 256, 4096]
VARS = ["t2", "t3", "t4", "t5", "t6", "t7", "t8", "cw4t"]
CUT = {"t2": 2, "t3": 3, "t4": 4, "t5": 5, "t6": 6, "t7": 7, "t8": 8, "cw4t": 7}
TEXT = {"base": 4968, "dsp0": 4976, "t2": 5800, "t3": 6472, "t4": 7312, "t5": 8324,
        "t6": 9508, "t7": 10856, "t8": 12376, "cw4t": 8592}
PATHS = {"t2": 2, "t3": 3, "t4": 4, "t5": 5, "t6": 6, "t7": 7, "t8": 8, "cw4t": 7}

procs, names = parse(sys.argv[1])
NP = len(procs)


def dmin(n, s):
    b = min(p[s]["base"] for _, p in procs)
    v = min(p[s][n] for _, p in procs)
    return 100.0 * (v - b) / b


def dmed(n, s):
    return st.median([100.0 * (p[s][n] - p[s]["base"]) / p[s]["base"] for _, p in procs])


def dworst(n, s):
    ds = [100.0 * (p[s][n] - p[s]["base"]) / p[s]["base"] for _, p in procs]
    return max(ds, key=abs)


def aa(s):
    return max(abs(100.0 * (p[s][n] - p[s]["base"]) / p[s]["base"])
               for _, p in procs for n in ("baseAA", "baseAB"))


print("## Table 1 -- the curve (Delta%% vs HEAD from absolute mins over %d processes)\n" % NP)
print("| variant | .text B | x | new paths |" + "".join(" %d B |" % s for s in LEN))
print("|---|---:|---:|---:|" + "---:|" * len(LEN))
print("| HEAD | 4968 | 1.00 | 0 |" + " 0 |" * len(LEN))
print("| dsp0 ctl | 4976 | 1.00 | 0 |"
      + "".join(" %+.2f |" % dmin("dsp0", s) for s in LEN))
for n in VARS:
    print("| %s (C=%d) | %d | %.2f | %d |" % (n, CUT[n], TEXT[n], TEXT[n] / 4968.0, PATHS[n])
          + "".join(" %+.2f |" % dmin(n, s) for s in LEN))

print("\n## Table 1b -- same, median of the %d per-process best-deltas\n" % NP)
print("| variant |" + "".join(" %d B |" % s for s in LEN))
print("|---|" + "---:|" * len(LEN))
print("| A/A floor (worst \\|d\\| any process) |"
      + "".join(" %.2f |" % aa(s) for s in LEN))
print("| dsp0 ctl |" + "".join(" %+.2f |" % dmed("dsp0", s) for s in LEN))
for n in VARS:
    print("| %s |" % n + "".join(" %+.2f |" % dmed(n, s) for s in LEN))

print("\n## Table 2 -- ABOVE-cutoff lengths only (the dispatch-overhead question)\n")
print("| variant | cutoff C |" + "".join(" %d B |" % s for s in LEN[:8]))
print("|---|---:|" + "---:|" * 8)
print("| A/A floor, median | - |" + "".join(" %+.2f |" % dmed("baseAA", s) for s in LEN[:8]))
print("| A/A floor, worst \\|d\\| | - |" + "".join(" %.2f |" % aa(s) for s in LEN[:8]))
print("| dsp0 (2 dispatch instrs only) | 0 |"
      + "".join(" %+.2f |" % dmed("dsp0", s) for s in LEN[:8]))
for n in VARS:
    row = []
    for s in LEN[:8]:
        row.append("--" if s // 16 <= CUT[n] else "%+.2f" % dmed(n, s))
    print("| %s | %d |" % (n, CUT[n]) + "".join(" %s |" % x for x in row))

print("\nworst single-process above-cutoff delta over all variants/lengths: ", end="")
w = max(((dworst(n, s), n, s) for n in VARS for s in LEN[:8] if s // 16 > CUT[n]),
        key=lambda t: abs(t[0]))
print("%+.2f %% (%s at %d B); the A/A floor at that length is %.2f %%" % (w[0], w[1], w[2], aa(w[2])))

print("\n## Table 3 -- retained lengths: truncation vs the FULL eight-body variant\n")
print("| length | blk |" + "".join(" %s |" % n for n in VARS[:-1]) + " cw4t |")
print("|---:|---:|" + "---:|" * 8)
for s in LEN[:8]:
    nb = s // 16
    row = []
    for n in VARS:
        row.append("--" if nb > CUT[n] else "%+.2f" % (dmin(n, s) - dmin("t8", s)))
    print("| %d | %d |" % (s, nb) + "".join(" %s |" % x for x in row))
print("\n(percentage POINTS relative to t8's own Delta at that length; "
      "negative = the truncation is slightly faster)")

print("\n## Absolute ns/call (min over %d processes)\n" % NP)
allv = ["base", "baseAA", "baseAB", "dsp0"] + VARS
print("| bytes |" + "".join(" %s |" % n for n in allv))
print("|---:|" + "---:|" * len(allv))
for s in LEN + [512, 1024]:
    print("| %d |" % s + "".join(" %.3f |" % min(p[s][n] for _, p in procs) for n in allv))
