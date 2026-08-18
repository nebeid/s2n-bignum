#!/usr/bin/env python3
"""Decomposition analysis for the g4 experiment: where does g4's cost go?

Reads logs/aux_<host>.log (measure_aux_g4.sh) and prints, in cycles, the chain

    t4  --(discarded AES)-->  a4  --(uniform 4-lane GHASH)-->  g4nm
        --(clamped addressing)-->  ...  --(branch-free masks)-->  g4

g4nm / g4nn are correct at nblk == 4 only, so their nblk<4 columns are shown in
brackets: they are the *cost of the code path*, which is nblk-independent by
construction, but not a correct result.

Usage: G4GHZ=2.7927 analyze_aux_g4.py <log> [<log> ...]
"""
import re, sys, os

GHZ = float(os.environ.get("G4GHZ", "0")) or None
SLOTS = {"t4": {1: 44, 2: 71, 3: 95, 4: 122},
         "a4": {1: 94, 2: 104, 3: 111, 4: 122},
         "g4": {n: 139 for n in (1, 2, 3, 4)},
         "g4i": {n: 139 for n in (1, 2, 3, 4)},
         "g4nm": {n: 124 for n in (1, 2, 3, 4)},
         "g4nn": {n: 121 for n in (1, 2, 3, 4)}}


def parse(paths):
    procs, cur, names = [], None, None
    for path in paths:
        for ln in open(path):
            if re.match(r"^=== process", ln):
                cur = {}
                procs.append(cur)
                continue
            if ln.startswith("bytes"):
                names = [x.strip() for x in ln.split("||")[0].split("|")[1:]]
                continue
            m = re.match(r"^(\d+)\s+(\d+)\s+\|", ln)
            if m and cur is not None:
                vals = [float(x) for x in re.findall(r"\|\s*([0-9.]+)", ln.split("||")[0])]
                cur[int(m.group(1))] = dict(zip(names, vals))
    return procs, names


procs, names = parse(sys.argv[1:])
mn = lambda n, s: min(p[s][n] for p in procs)
cyc = lambda n, s: mn(n, s) * GHZ if GHZ else float("nan")
print("%d processes; slots: %s" % (len(procs), " ".join(names)))

print("\n### ns/call, min over processes")
print("%-6s" % "bytes" + "".join(" %8s" % n for n in names))
for s in (16, 32, 48, 64, 128):
    print("%-6d" % s + "".join(" %8.3f" % mn(n, s) for n in names))

if GHZ:
    print("\n### the decomposition, in CYCLES at %.4f GHz" % GHZ)
    print("| nblk | t4 | +discarded AES (a4) | +uniform 4-lane GHASH (g4nn) |"
          " +clamped addressing (g4nm) | +branch-free masks (g4) | g4-t4 |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for nb in (1, 2, 3, 4):
        s = nb * 16
        t, a, nn, nm, g = (cyc("t4", s), cyc("a4", s), cyc("g4nn", s),
                           cyc("g4nm", s), cyc("g4", s))
        br = "" if nb == 4 else "*"
        print("| %d | %.1f | %.1f (%+.1f) | %s%.1f (%+.1f) | %s%.1f (%+.1f) | %.1f (%+.1f) | %+.1f |"
              % (nb, t, a, a - t, br, nn, nn - a, br, nm, nm - nn, g, g - nm, g - t))
    print("\n* g4nn / g4nm are correct at nblk = 4 only; their cost is "
          "nblk-independent by construction (the table shows this directly).")
    print("\n### achieved cycles / own slot floor (4 slots per cycle)")
    print("| variant |" + "".join(" nblk %d |" % n for n in (1, 2, 3, 4)))
    print("|---|" + "---:|" * 4)
    for v in ("t4", "a4", "g4nn", "g4nm", "g4i", "g4"):
        if v not in names:
            continue
        row = "| %s |" % v
        for nb in (1, 2, 3, 4):
            fl = SLOTS[v][nb] / 4.0
            row += " %.1f / %.2fx |" % (cyc(v, nb * 16), cyc(v, nb * 16) / fl)
        print(row)
    print("\n### mask strategy: g4 (precomputed) vs g4i (inline), %")
    for nb in (1, 2, 3, 4):
        s = nb * 16
        print("  nblk=%d  %+.2f %%" % (nb, 100 * (mn("g4i", s) - mn("g4", s)) / mn("g4", s)))
    print("\n### cw4 reference (the same 4-wide group reached by a per-nblk stub)")
    for nb in (1, 2, 3, 4):
        s = nb * 16
        print("  nblk=%d  cw4 %.1f cyc   g4 %.1f cyc   g4-cw4 %+.1f cyc"
              % (nb, cyc("cw4", s), cyc("g4", s), cyc("g4", s) - cyc("cw4", s)))
