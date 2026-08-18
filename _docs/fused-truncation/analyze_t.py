#!/usr/bin/env python3
"""Parse logs/trunc_<host>.log (3 link orderings x N processes) -> absolute mins,
median-of-per-process best-deltas, per-ordering deltas, and the A/A noise floor.

Column order differs per ordering, so everything is keyed by slot NAME.
"""
import re, sys, os, statistics as st

CLK = 2.7927


def parse(path):
    procs = []            # (ordering, {size: {name: ns}})
    cur, names, order = None, None, None
    for ln in open(path):
        m = re.match(r"^=== process order(\d+)\.(\d+)", ln)
        if m:
            order = int(m.group(1))
            cur = {}
            procs.append((order, cur))
            continue
        if ln.startswith("bytes"):
            head = ln.split("||")[0]
            names = [x.strip() for x in head.split("|")[1:]]
            continue
        m = re.match(r"^(\d+)\s+(\d+)\s+\|", ln)
        if m and cur is not None:
            vals = [float(x) for x in re.findall(r"\|\s*([0-9.]+)", ln.split("||")[0])]
            cur[int(m.group(1))] = dict(zip(names, vals))
    return procs, names


def main(path):
    procs, names = parse(path)
    sizes = sorted(procs[0][1].keys())
    orders = sorted(set(o for o, _ in procs))
    print("slots: %s" % " ".join(names))
    print("%d processes over %d link orderings\n" % (len(procs), len(orders)))

    print("=== ABSOLUTE ns/call (min over all %d processes) ===" % len(procs))
    print("%-6s" % "bytes" + "".join(" %8s" % n for n in names))
    for s in sizes:
        print("%-6d" % s + "".join(" %8.3f" % min(p[s][n] for _, p in procs) for n in names))

    print("\n=== DELTA %% vs base : median of the %d per-process best-deltas ===" % len(procs))
    print("%-6s" % "bytes" + "".join(" %8s" % n for n in names[1:]))
    med = {}
    for s in sizes:
        row = []
        for n in names[1:]:
            ds = [100.0 * (p[s][n] - p[s]["base"]) / p[s]["base"] for _, p in procs]
            med[(s, n)] = st.median(ds)
            row.append(st.median(ds))
        print("%-6d" % s + "".join(" %+8.2f" % v for v in row))

    print("\n=== A/A NOISE FLOOR (base vs the same object again) ===")
    print("%-6s %9s %9s %9s %9s" % ("bytes", "AA med", "AB med", "worst|d|", "dsp0 med"))
    for s in sizes:
        w = max(abs(100.0 * (p[s][n] - p[s]["base"]) / p[s]["base"])
                for _, p in procs for n in ("baseAA", "baseAB"))
        print("%-6d %+9.2f %+9.2f %9.2f %+9.2f"
              % (s, med[(s, "baseAA")], med[(s, "baseAB")], w, med[(s, "dsp0")]))

    print("\n=== DELTA %% vs base, PER LINK ORDERING (median of %d processes each) ==="
          % (len(procs) // len(orders)))
    for n in names[1:]:
        print("  %-8s" % n + "".join(" %7d" % s for s in sizes))
        for o in orders:
            sel = [p for oo, p in procs if oo == o]
            row = [st.median([100.0 * (p[s][n] - p[s]["base"]) / p[s]["base"] for p in sel])
                   for s in sizes]
            print("   order%d " % o + "".join(" %+7.2f" % v for v in row))

    print("\n=== CYCLES (min ns x %.4f GHz) ===" % CLK)
    print("%-6s" % "bytes" + "".join(" %8s" % n for n in names))
    for s in sizes:
        print("%-6d" % s + "".join(" %8.2f" % (min(p[s][n] for _, p in procs) * CLK)
                                   for n in names))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1
         else os.path.dirname(os.path.abspath(__file__)) + "/logs/trunc_r8g_all.log")
