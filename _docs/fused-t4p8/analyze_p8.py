#!/usr/bin/env python3
"""Per-length analysis for the t4p8 experiment.  Same estimators as the
truncation run's analyze_t.py/report_t.py: absolute mins over all processes,
median of per-process best-deltas, A/A floor, and -- for the 128 B column -- the
delta against the placement-matched `dsp0` control instead of `base`.

Usage: analyze_p8.py <log> [<log> ...]
"""
import re, sys, statistics as st

LEN = [16, 32, 48, 64, 80, 96, 112, 128, 256, 4096]
VARS = ["t4", "t5", "t7", "t8", "t4p8", "t4p8b"]
TEXT = {"base": 4968, "dsp0": 4976, "t4": 7312, "t5": 8324, "t7": 10856,
        "t8": 12376, "t4p8": 8832, "t4p8b": 8836}
PATHS = {"t4": 4, "t5": 5, "t7": 7, "t8": 8, "t4p8": 5, "t4p8b": 5}
AAS = ("baseAA", "baseAB")


def parse(paths):
    procs, cur, names = [], None, None
    for path in paths:
        for ln in open(path):
            m = re.match(r"^=== process order(\d+)\.(\d+)", ln)
            if m:
                cur = {}
                procs.append((path + ":" + m.group(1), cur))
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
NP = len(procs)
sizes = sorted(procs[0][1].keys())


def mn(n, s):
    return min(p[s][n] for _, p in procs)


def dmin(n, s, ref="base"):
    return 100.0 * (mn(n, s) - mn(ref, s)) / mn(ref, s)


def dmed(n, s, ref="base"):
    return st.median([100.0 * (p[s][n] - p[s][ref]) / p[s][ref] for _, p in procs])


def floor(s, ref, copies):
    return max(abs(100.0 * (p[s][x] - p[s][ref]) / p[s][ref]) for _, p in procs for x in copies)


print("%d processes; slots: %s\n" % (NP, " ".join(names)))

print("### absolute ns/call (min over %d processes)" % NP)
print("%-6s" % "bytes" + "".join(" %8s" % n for n in names))
for s in sizes:
    print("%-6d" % s + "".join(" %8.3f" % mn(n, s) for n in names))

print("\n### Table 1: Delta %% vs HEAD, absolute-min estimator")
print("| variant | .text B | x | paths |" + "".join(" %d B |" % s for s in LEN))
print("|---|---:|---:|---:|" + "---:|" * len(LEN))
print("| HEAD | 4968 | 1.00 | 0 |" + " 0 |" * len(LEN))
print("| dsp0 ctl | 4976 | 1.00 | 0 |" + "".join(" %+.2f |" % dmin("dsp0", s) for s in LEN))
for n in VARS:
    print("| %s | %d | %.2f | %d |" % (n, TEXT[n], TEXT[n] / 4968.0, PATHS[n])
          + "".join(" %+.2f |" % dmin(n, s) for s in LEN))

print("\n### Table 1b: Delta %% vs HEAD, median of per-process best-deltas")
print("| variant |" + "".join(" %d B |" % s for s in LEN))
print("|---|" + "---:|" * len(LEN))
print("| A/A floor base (worst \\|d\\|) |" + "".join(" %.2f |" % floor(s, "base", AAS) for s in LEN))
print("| A/A floor t4p8 (t4p8AA) |"
      + "".join(" %.2f |" % floor(s, "t4p8", ("t4p8AA",)) for s in LEN))
print("| A/A floor dsp0 (dsp0AA) |"
      + "".join(" %.2f |" % floor(s, "dsp0", ("dsp0AA",)) for s in LEN))
print("| dsp0 ctl |" + "".join(" %+.2f |" % dmed("dsp0", s) for s in LEN))
for n in VARS:
    print("| %s |" % n + "".join(" %+.2f |" % dmed(n, s) for s in LEN))

print("\n### Table 2: 128 B and the fall-through lengths referenced to dsp0")
print("| variant | 80 B vs dsp0 | 96 B | 112 B | 128 B | 256 B | 4096 B |")
print("|---|---:|---:|---:|---:|---:|---:|")
for n in ["base", "baseAA", "baseAB", "dsp0AA", "t4", "t5", "t7", "t8", "t4p8", "t4p8b"]:
    print("| %s |" % n + "".join(" %+.2f |" % dmed(n, s, "dsp0") for s in (80, 96, 112, 128, 256, 4096)))

print("\n### Table 3: t4p8 vs t5 and vs t8 at each length (percentage POINTS, min estimator)")
print("| length | t4p8-t5 | t4p8-t8 | t4p8-t4 | t4p8b-t4p8 |")
print("|---:|---:|---:|---:|---:|")
for s in LEN:
    print("| %d | %+.2f | %+.2f | %+.2f | %+.2f |"
          % (s, dmin("t4p8", s) - dmin("t5", s), dmin("t4p8", s) - dmin("t8", s),
             dmin("t4p8", s) - dmin("t4", s), dmin("t4p8b", s) - dmin("t4p8", s)))

print("\n### ns saved per call vs HEAD (min estimator), and the 80/128 trade")
print("| bytes | base ns | t5 saves | t4p8 saves | t8 saves |")
print("|---:|---:|---:|---:|---:|")
for s in LEN[:8]:
    b = mn("base", s)
    print("| %d | %.3f | %+.3f | %+.3f | %+.3f |"
          % (s, b, b - mn("t5", s), b - mn("t4p8", s), b - mn("t8", s)))
s80, s128 = 80, 128
g5 = mn("base", s80) - mn("t5", s80)
g8 = mn("base", s128) - mn("t4p8", s128)
print("\nfixed-length break-even 128B:80B call ratio (t4p8 overtakes t5) = "
      "%.3f / %.3f = %.2f : 1" % (g5, g8, g5 / g8))
