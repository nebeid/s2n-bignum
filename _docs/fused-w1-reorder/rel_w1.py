#!/usr/bin/env python3
"""Delta % of every variant against the BASELINE ORDERING `w1` in the same
binary, at 16/32/48/64/80/4096 B (absolute-min estimator over all processes).
`w1` is the byte-identical twin of the shipped `s4h`, so this is the number that
answers "does this ordering beat the one we ship", free of the link-slot
placement lottery that `base` (pinned to slot 0) carries at 16 and 48 B.
"""
import sys
from analyze_w1 import parse

SZ = [16, 32, 48, 64, 80, 4096]
for path in sys.argv[1:]:
    procs = parse(path)
    names = []
    for _, d in procs:
        for n in d:
            if n not in names:
                names.append(n)
    mn = {n: {b: min(d[n][b] for _, d in procs if n in d and b in d[n]) for b in SZ}
          for n in names}
    ref = "w1"
    print("== %s   (Delta %% vs %s, %d processes)" % (path.split("/")[-1], ref, len(procs)))
    print("%-8s %s" % ("variant", "".join("%9d" % b for b in SZ)))
    for n in names:
        if n in ("base", "baseAA", "dsp0"):
            continue
        print("%-8s %s" % (n, "".join("%+9.2f" % (100 * (mn[n][b] - mn[ref][b]) / mn[ref][b])
                                      for b in SZ)))
    print()
