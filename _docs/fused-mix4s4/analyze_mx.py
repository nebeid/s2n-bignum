#!/usr/bin/env python3
"""Per-length analysis for the mix4s4 experiment.  Same estimators as
fused-t4p8/analyze_p8.py: absolute mins over all processes, median of
per-process best-deltas, A/A floors, and the placement-matched `dsp0` reference
for the 128 B column.  Adds the per-nblk achieved-cycles / slot-floor table.

Usage: MXGHZ=2.7927 analyze_mx.py <log> [<log> ...]
"""
import re, sys, os, statistics as st

LEN = [16, 32, 48, 64, 80, 96, 112, 128, 256, 512, 1024, 4096]
VARS = ["m4s4", "m4s4h", "s4", "s4h", "t4p8", "t4", "cw4"]
AAS = ("baseAA",)
GHZ = float(os.environ.get("MXGHZ", "0")) or None
# slot floor at 4 SIMD slots/cycle, from verify_mx.py (identical for both key
# modes and for the separate-body designs: the slot counts are width-invariant)
FLOOR = {1: 12.50, 2: 19.00, 3: 25.50, 4: 32.00, 5: 38.50, 6: 45.00,
         7: 51.50, 8: 58.00}
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

print("\n### Table 1b: Delta %% vs HEAD, median of per-process best-deltas, + A/A floors")
print("| variant |" + "".join(" %d B |" % s for s in LEN))
print("|---|" + "---:|" * len(LEN))
print("| A/A floor base (baseAA) |" + "".join(" %.2f |" % floor(s, "base", AAS) for s in LEN))
print("| A/A floor m4s4 (m4s4AA) |"
      + "".join(" %.2f |" % floor(s, "m4s4", ("m4s4AA",)) for s in LEN))
print("| A/A floor dsp0 (dsp0AA) |"
      + "".join(" %.2f |" % floor(s, "dsp0", ("dsp0AA",)) for s in LEN))
for n in ["dsp0"] + VARS:
    print("| %s |" % n + "".join(" %+.2f |" % dmed(n, s) for s in LEN))

print("\n### Table 2: every length referenced to the dsp0 control (min estimator)")
print("| variant |" + "".join(" %d B |" % s for s in LEN))
print("|---|" + "---:|" * len(LEN))
for n in ["base", "baseAA", "dsp0AA"] + VARS:
    print("| %s |" % n + "".join(" %+.2f |" % dmin(n, s, "dsp0") for s in LEN))

if GHZ:
    print("\n### Table 3: achieved cycles and achieved/slot-floor, per nblk  (%.4f GHz)" % GHZ)
    hdr = ["base", "m4s4", "m4s4h", "s4", "s4h", "t4p8", "t4", "cw4"]
    print("| nblk | floor |" + "".join(" %s |" % h for h in hdr))
    print("|---:|---:|" + "---:|" * len(hdr))
    for nb in (1, 2, 3, 4, 5, 6, 7, 8):
        row = "| %d | %.2f |" % (nb, FLOOR[nb])
        for h in hdr:
            c = mn(h, nb * 16) * GHZ
            row += " %.1f / %.2fx |" % (c, c / FLOOR[nb])
        print(row)

    print("\n### Table 4: marginal cycles per block")
    print("| variant | (nblk 1->4)/3 = the SEQUENTIAL group cost | (nblk 4->8)/4 = the 4-WIDE group cost | floor slope |")
    print("|---|---:|---:|---:|")
    for h in ["base", "m4s4", "m4s4h", "s4", "s4h", "t4p8", "t4", "cw4"]:
        c1, c4, c8 = (mn(h, 16) * GHZ, mn(h, 64) * GHZ, mn(h, 128) * GHZ)
        print("| %s | %.2f | %.2f | 6.50 |" % (h, (c4 - c1) / 3.0, (c8 - c4) / 4.0))

print("\n### Table 5: head-to-head, percentage POINTS (min estimator; +ve = first is slower)")
pairs = [("m4s4", "t4p8"), ("m4s4h", "t4p8"), ("m4s4", "m4s4h"),
         ("s4", "t4"), ("s4h", "t4"), ("m4s4h", "s4h"), ("m4s4h", "cw4")]
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
