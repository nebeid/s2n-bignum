#!/usr/bin/env python3
"""Per-length analysis for the g4 experiment.  Same estimators as
fused-t4p8/analyze_p8.py and fused-mix4s4/analyze_mx.py: absolute mins over all
processes, median of per-process best-deltas, A/A floors, the placement-matched
`dsp0` reference, achieved cycles vs the slot floor per nblk, and the
decomposition g4 - a4 - t4 that isolates the cost of the discarded blocks.

Usage: G4GHZ=2.7927 analyze_g4.py <log> [<log> ...]
"""
import re, sys, os, statistics as st

LEN = [16, 32, 48, 64, 80, 96, 112, 128, 256, 512, 1024, 4096]
VARS = ["g4", "g4h", "a4", "g4p8", "t4p8", "t4", "m4s4h"]
GHZ = float(os.environ.get("G4GHZ", "0")) or None
# exact-work slot floor at 4 SIMD slots/cycle (the convention of
# fused-cascade-experiment.md): the ideal issue cost of n blocks of work.
FLOOR = {1: 12.50, 2: 19.00, 3: 25.50, 4: 32.00, 5: 38.50, 6: 45.00,
         7: 51.50, 8: 58.00}
# g4's own slot count is nblk-INDEPENDENT (it always runs 4 blocks); filled in
# from verify_g4.py via logs/slots.txt if present.
G4SLOTS = None
for cand in ("logs/slots.txt", "slots.txt"):
    if os.path.exists(cand):
        try:
            G4SLOTS = int(open(cand).read().split()[0])
        except Exception:
            pass
TEXT = {}
for cand in ("logs/text.txt", "text.txt"):
    if os.path.exists(cand):
        for ln in open(cand):
            p = ln.split()
            if len(p) >= 2 and p[1].isdigit():
                TEXT[p[0]] = int(p[1])


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
    return max(abs(100.0 * (p[s][x] - p[s][ref]) / p[s][ref])
               for _, p in procs for x in copies)


print("%d processes; slots: %s\n" % (NP, " ".join(names)))

print("### absolute ns/call (min over %d processes)" % NP)
print("%-6s" % "bytes" + "".join(" %8s" % n for n in names))
for s in sizes:
    print("%-6d" % s + "".join(" %8.3f" % mn(n, s) for n in names))

print("\n### Table 1: Delta %% vs HEAD, absolute-min estimator")
print("| variant | .text B | x |" + "".join(" %d B |" % s for s in LEN))
print("|---|---:|---:|" + "---:|" * len(LEN))
print("| HEAD | %s | 1.00 |" % TEXT.get("base", "?") + " 0 |" * len(LEN))
for n in ["dsp0"] + VARS:
    t = TEXT.get(n)
    print("| %s | %s | %s |" % (n, t if t else "?",
                                ("%.2f" % (t / TEXT["base"])) if t and TEXT.get("base") else "?")
          + "".join(" %+.2f |" % dmin(n, s) for s in LEN))

print("\n### Table 1b: Delta %% vs HEAD, median of per-process deltas, + A/A floors")
print("| variant |" + "".join(" %d B |" % s for s in LEN))
print("|---|" + "---:|" * len(LEN))
for lbl, ref, cp in (("base (baseAA)", "base", ("baseAA",)),
                     ("g4 (g4AA)", "g4", ("g4AA",)),
                     ("dsp0 (dsp0AA)", "dsp0", ("dsp0AA",))):
    print("| A/A floor %s |" % lbl + "".join(" %.2f |" % floor(s, ref, cp) for s in LEN))
for n in ["dsp0"] + VARS:
    print("| %s |" % n + "".join(" %+.2f |" % dmed(n, s) for s in LEN))

print("\n### Table 2: every length referenced to the dsp0 control (min estimator)")
print("| variant |" + "".join(" %d B |" % s for s in LEN))
print("|---|" + "---:|" * len(LEN))
for n in ["base", "baseAA", "dsp0AA"] + VARS:
    print("| %s |" % n + "".join(" %+.2f |" % dmin(n, s, "dsp0") for s in LEN))

print("\n### Table 3: THE PRIMARY RESULT -- the cost of the discarded blocks")
print("ns/call and Delta%% at nblk = 1,2,3,4, three designs doing the SAME GHASH")
print("work and differing only in how much AES they run and whether the")
print("exactly-nblk correction is branch-free.")
print("| nblk | t4 (exact n AES) | a4 (4 AES, exact GHASH) | a4-t4 | g4 (4 AES, masked) | g4-t4 | g4-a4 |")
print("|---:|---:|---:|---:|---:|---:|---:|")
for nb in (1, 2, 3, 4):
    s = nb * 16
    t, a, g = mn("t4", s), mn("a4", s), mn("g4", s)
    print("| %d | %.3f | %.3f | %+.2f%% | %.3f | %+.2f%% | %+.2f%% |"
          % (nb, t, a, 100 * (a - t) / t, g, 100 * (g - t) / t, 100 * (g - a) / a))

if GHZ:
    print("\n### Table 4: achieved cycles and achieved/exact-work-floor, per nblk  (%.4f GHz)" % GHZ)
    hdr = ["base", "g4", "g4h", "a4", "g4p8", "t4p8", "t4", "m4s4h"]
    print("| nblk | exact-work floor |" + "".join(" %s |" % h for h in hdr))
    print("|---:|---:|" + "---:|" * len(hdr))
    for nb in (1, 2, 3, 4, 5, 6, 7, 8):
        row = "| %d | %.2f |" % (nb, FLOOR[nb])
        for h in hdr:
            c = mn(h, nb * 16) * GHZ
            row += " %.1f / %.2fx |" % (c, c / FLOOR[nb])
        print(row)
    if G4SLOTS:
        print("\ng4's own slot count is %d for every nblk -> its own issue floor is "
              "%.2f cycles at 4 slots/cycle; achieved/own-floor:" % (G4SLOTS, G4SLOTS / 4.0))
        for nb in (1, 2, 3, 4):
            c = mn("g4", nb * 16) * GHZ
            print("  nblk=%d  %.1f cyc  = %.2fx its own floor" % (nb, c, c / (G4SLOTS / 4.0)))

print("\n### Table 5: head-to-head, percentage POINTS (min estimator; +ve = first slower)")
pairs = [("g4", "t4"), ("g4", "a4"), ("a4", "t4"), ("g4", "g4h"),
         ("g4", "t4p8"), ("g4p8", "t4p8"), ("g4", "m4s4h")]
print("| length |" + "".join(" %s-%s |" % p for p in pairs))
print("|---:|" + "---:|" * len(pairs))
for s in LEN:
    print("| %d |" % s + "".join(" %+.2f |" % (dmin(a, s) - dmin(b, s)) for a, b in pairs))

print("\n### uniform small-traffic value (sum over the eight small lengths)")
print("| variant | total ns, 8 calls | saved ns | %% of base |")
print("|---|---:|---:|---:|")
b = sum(mn("base", s) for s in LEN[:8])
print("| base | %.2f | 0 | 0 |" % b)
for n in ["dsp0"] + VARS:
    t = sum(mn(n, s) for s in LEN[:8])
    print("| %s | %.2f | %.2f | %.1f |" % (n, t, b - t, 100.0 * (b - t) / b))

print("\n### uniform value over nblk 1..4 only (the lengths g4 actually fuses)")
b4 = sum(mn("base", s) for s in LEN[:4])
for n in ["dsp0"] + VARS:
    t = sum(mn(n, s) for s in LEN[:4])
    print("  %-6s %8.2f ns  saved %6.2f  = %5.1f %%" % (n, t, b4 - t, 100.0 * (b4 - t) / b4))
