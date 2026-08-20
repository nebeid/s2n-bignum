#!/usr/bin/env python3
"""an.py <logfile> [--ref GROUP] [--sizes 64,256,512,1024]

Estimator: MEDIAN of per-process PAIRED deltas, with a 20000-resample
bootstrap 95% CI on that median.  Never min-of-mins across processes.

A "group" is everything before the '.' in a slot label, so several slots
(different addresses, byte-identical code) belong to one group.  A process's
value for a group is the median over that group's slots; the paired delta for
that process is 100*(g - ref)/ref, computed inside the process so the
per-process clock/thermal state cancels.

Also prints the A/A distribution: every within-group slot pair, i.e. deltas
between byte-identical code at different addresses.
"""
import sys, collections, random, statistics

log = sys.argv[1]
ref = None
sizes = None
a = sys.argv[2:]
while a:
    if a[0] == "--ref":   ref = a[1]; a = a[2:]
    elif a[0] == "--sizes": sizes = [int(x) for x in a[1].split(",")]; a = a[2:]
    else: sys.exit("bad arg " + a[0])

V = {}                       # (proc,size,label) -> ns
labels, clk, procs = [], [], set()
for L in open(log):
    f = L.split()
    if not f: continue
    if f[0] == "RES":
        p, s, lab, v = int(f[1]), int(f[2]), f[3], float(f[4])
        V[(p, s, lab)] = v
        procs.add(p)
        if lab not in labels: labels.append(lab)
    elif f[0] == "CLK":
        clk += [float(f[2]), float(f[3])]
    elif f[0].startswith("GATE") and "FAIL" in L:
        print("!!! " + L.rstrip())
procs = sorted(procs)
if sizes is None:
    sizes = sorted({s for (_, s, _) in V})

grp = collections.OrderedDict()
for lab in labels:
    grp.setdefault(lab.split(".")[0], []).append(lab)
if ref is None:
    ref = list(grp)[0]

def med(x): return statistics.median(x)

def boot_ci(d, n=20000):
    if len(d) < 3: return (float("nan"), float("nan"))
    r = random.Random(12345)
    m = sorted(med([d[r.randrange(len(d))] for _ in range(len(d))]) for _ in range(n))
    return m[int(0.025 * n)], m[int(0.975 * n)]

print("file=%s  processes=%d  ref=%s  clock GHz min/max = %.4f / %.4f"
      % (log, len(procs), ref, min(clk), max(clk)))
print("groups: " + "  ".join("%s(%d slots)" % (g, len(v)) for g, v in grp.items()))

for s in sizes:
    print("\n--- size %d B ---" % s)
    pv = {}                                   # group -> per-process value
    for g, labs in grp.items():
        pv[g] = [med([V[(p, s, l)] for l in labs]) for p in procs]
    print("  %-8s %10s %10s   %-22s %s"
          % ("group", "med ns", "sd ns", "paired delta vs " + ref, "95% CI"))
    for g in grp:
        d = [100.0 * (b - a) / a for a, b in zip(pv[ref], pv[g])]
        lo, hi = boot_ci(d)
        sd = statistics.pstdev(pv[g]) if len(pv[g]) > 1 else 0.0
        print("  %-8s %10.4f %10.4f   %+21.3f%%  [%+.3f%%, %+.3f%%]"
              % (g, med(pv[g]), sd, med(d), lo, hi))
    # A/A: byte-identical code, different addresses
    aa = []
    for g, labs in grp.items():
        for i in range(len(labs)):
            for j in range(len(labs)):
                if i == j: continue
                d = [100.0 * (V[(p, s, labs[j])] - V[(p, s, labs[i])]) / V[(p, s, labs[i])]
                     for p in procs]
                aa.append((med(d), labs[i], labs[j]))
    if aa:
        vals = sorted(x[0] for x in aa)
        print("  A/A pairs (n=%d): min %+.3f%%  p25 %+.3f%%  median %+.3f%%  p75 %+.3f%%  max %+.3f%%  |max| %.3f%%"
              % (len(vals), vals[0], vals[len(vals)//4], med(vals),
                 vals[3*len(vals)//4], vals[-1], max(abs(v) for v in vals)))
        worst = max(aa, key=lambda x: abs(x[0]))
        print("       widest A/A pair: %s -> %s  %+.3f%%" % (worst[1], worst[2], worst[0]))
    # per-slot medians, useful for placement inspection
    print("  per-slot median ns: " + "  ".join(
        "%s %.3f" % (l, med([V[(p, s, l)] for p in procs])) for l in labels))
