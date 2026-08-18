#!/usr/bin/env python3
"""Parse logs/cascw_*.log -> absolute ns/call, delta% vs HEAD baseline (median
of per-process best-deltas), achieved cycles and achieved/slot-floor ratio."""
import re, os, statistics as st

HOSTS = ["GV3", "GV4", "GV5", "r8g"]
CORE = {"GV3": "Neoverse-V1", "GV4": "Neoverse-V2", "GV5": "Neoverse-V3", "r8g": "Neoverse-V2 dev"}
CLK = {"GV3": 2.5914, "GV4": 2.7927, "GV5": 3.2903, "r8g": 2.7928}

# SIMD issue slots (fused aese+aesmc = 1 slot, loads/stores excluded)
SLOTS = {
    "base":  {1: 195, 2: 207, 3: 217, 4: 227, 5: 235, 6: 243, 7: 249, 8: 226},
    "tuned": {1: 44, 2: 71, 3: 95, 4: 122, 5: 146, 6: 173, 7: 197, 8: 224},
    "casc":  {1: 50, 2: 76, 3: 102, 4: 128, 5: 154, 6: 180, 7: 206, 8: 232},
}
for k in ("casck", "cw1", "cw2", "cw4", "cw8"):
    SLOTS[k] = SLOTS["casc"]
SLOTS["baseAA"] = SLOTS["base"]


def parse(path):
    procs, cur, names = [], None, None
    for ln in open(path):
        if ln.startswith("=== process"):
            cur = {}
            procs.append(cur)
            continue
        if ln.startswith("bytes"):
            names = [n.split("||")[0].strip() for n in ln.split("|")[1:]]
            names = [n for n in names if n and not n.endswith("%")]
            continue
        m = re.match(r"^(\d+)\s+(\d+)\s+\|", ln)
        if m and cur is not None:
            cur[int(m.group(1))] = [float(x) for x in
                                    re.findall(r"\|\s*([0-9.]+)", ln.split("||")[0])]
    return procs, names


def main():
    d = os.path.dirname(os.path.abspath(__file__)) + "/logs"
    out = {}
    for h in HOSTS:
        p = os.path.join(d, "cascw_%s.log" % h)
        if os.path.exists(p):
            out[h] = parse(p)
    names = next(iter(out.values()))[1]
    sizes = sorted(next(iter(out.values()))[0][0].keys())
    print("slots:", names)

    print("\n=== ABSOLUTE ns/call (min over 3 processes x 150 reps) ===")
    print("%-5s %-6s %-4s" % ("host", "bytes", "blk") + "".join(" %8s" % n for n in names))
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            mins = [min(p[s][i] for p in procs) for i in range(len(names))]
            print("%-5s %-6d %-4d" % (h, s, s // 16) + "".join(" %8.3f" % v for v in mins))
        print()

    print("=== DELTA %% vs slot0 (base = our HEAD kernel); median of per-process best-deltas ===")
    print("%-5s %-6s" % ("host", "bytes") + "".join(" %8s" % n for n in names[1:]))
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            row = [st.median([100.0 * (p[s][i] - p[s][0]) / p[s][0] for p in procs])
                   for i in range(1, len(names))]
            print("%-5s %-6d" % (h, s) + "".join(" %+8.2f" % v for v in row))
        print()


    print("\n=== DELTA %% of each cascade width vs the EIGHT-BODY version (tuned) ===")
    it = names.index("tuned")
    print("%-5s %-6s" % ("host", "bytes") + "".join(" %8s" % n for n in names[it+1:]))
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            row = [st.median([100.0*(p[s][i]-p[s][it])/p[s][it] for p in procs])
                   for i in range(it+1, len(names))]
            print("%-5s %-6d" % (h, s) + "".join(" %+8.2f" % v for v in row))
        print()

    print("=== ACHIEVED CYCLES and ACHIEVED/SLOT-FLOOR RATIO, nblk = 1..8 ===")
    for h in out:
        procs, _ = out[h]
        print("\n-- %s (%s, %.4f GHz)" % (h, CORE[h], CLK[h]))
        print("%-4s %-7s" % ("nblk", "slots") + "".join(" %14s" % n for n in names))
        for nb in range(1, 9):
            s = nb * 16
            cells = []
            for i, n in enumerate(names):
                ns = min(p[s][i] for p in procs)
                cyc = ns * CLK[h]
                fl = SLOTS[n][nb] / 4.0
                cells.append("%7.1f/%5.2fx" % (cyc, cyc / fl))
            print("%-4d %-7s" % (nb, "%d/%d" % (SLOTS["casc"][nb], SLOTS["tuned"][nb]))
                  + "".join(" %14s" % c for c in cells))

    print("\n=== steady-state cycles per extra block (linear fit over nblk = 4..8) ===")
    print("%-5s" % "host" + "".join(" %9s" % n for n in names))
    for h in out:
        procs, _ = out[h]
        row = []
        for i in range(len(names)):
            xs = list(range(4, 9))
            ys = [min(p[nb * 16][i] for p in procs) * CLK[h] for nb in xs]
            mx = sum(xs) / len(xs)
            my = sum(ys) / len(ys)
            slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
            row.append(slope)
        print("%-5s" % h + "".join(" %9.2f" % v for v in row))
    print("(slot floor per extra block = 26/4 = 6.50 cyc for every cascade width;"
          " the eight-body version's is 25.7/4 = 6.43)")


main()
