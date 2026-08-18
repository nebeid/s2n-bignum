#!/usr/bin/env python3
"""Parse bench logs (3 processes x N reps) -> absolute mins and median-of-
per-process best-deltas, per host."""
import re, sys, os, statistics as st

HOSTS = ["GV3", "GV4", "GV5", "r8g"]
CORE = {"GV3": "Neoverse-V1", "GV4": "Neoverse-V2", "GV5": "Neoverse-V3", "r8g": "Neoverse-V2 (dev)"}
CLK = {"GV3": 2.5914, "GV4": 2.7926, "GV5": 3.2907, "r8g": 2.7925}


def parse(path):
    """-> list of dicts per process: {size: {slot: ns}}, plus slot names"""
    procs, cur, names = [], None, None
    for ln in open(path):
        if ln.startswith("=== process"):
            cur = {}
            procs.append(cur)
            continue
        if ln.startswith("bytes"):
            names = [x.strip() for x in ln.split("|")[1:]]
            names = [n.split("||")[0].strip() for n in names]
            names = [n for n in names if n and not n.endswith("%")]
            continue
        m = re.match(r"^(\d+)\s+(\d+)\s+\|", ln)
        if m and cur is not None:
            vals = [float(x) for x in re.findall(r"\|\s*([0-9.]+)", ln.split("||")[0])]
            cur[int(m.group(1))] = vals
    return procs, names


def main():
    d = os.path.dirname(os.path.abspath(__file__)) + "/logs"
    out = {}
    for h in HOSTS:
        p = os.path.join(d, h + ".log")
        if not os.path.exists(p):
            continue
        procs, names = parse(p)
        out[h] = (procs, names)
    sizes = sorted(next(iter(out.values()))[0][0].keys())
    names = next(iter(out.values()))[1]
    print("slots:", names)

    print("\n=== ABSOLUTE ns/call (min over %d processes) ===" % len(next(iter(out.values()))[0]))
    hdr = "%-5s %-6s" % ("host", "bytes") + "".join(" %10s" % n for n in names)
    print(hdr)
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            mins = [min(p[s][i] for p in procs) for i in range(len(names))]
            print("%-5s %-6d" % (h, s) + "".join(" %10.3f" % v for v in mins))
        print()

    print("=== DELTA %% vs slot0 (base = our HEAD kernel); median of per-process best-deltas ===")
    print("%-5s %-6s" % ("host", "bytes") + "".join(" %9s" % n for n in names[1:]))
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            row = []
            for i in range(1, len(names)):
                ds = [100.0 * (p[s][i] - p[s][0]) / p[s][0] for p in procs]
                row.append(st.median(ds))
            print("%-5s %-6d" % (h, s) + "".join(" %+9.2f" % v for v in row))
        print()

    print("=== DELTA %% of fused (tuned) vs AWS-LC AS SHIPPED (fallback <256B, 8x >=256B) ===")
    ifb, i8x, itn = names.index("awslcfb"), names.index("awslc8x"), names.index("tuned")
    print("%-5s %-6s %10s %10s %9s" % ("host", "bytes", "shipped", "fused", "delta%"))
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            ref = ifb if s < 256 else i8x
            ds = [100.0 * (p[s][itn] - p[s][ref]) / p[s][ref] for p in procs]
            print("%-5s %-6d %10.3f %10.3f %+9.2f" %
                  (h, s, min(p[s][ref] for p in procs), min(p[s][itn] for p in procs), st.median(ds)))
        print()

    print("=== CYCLES (min ns x clock) ===")
    print("%-5s %-6s" % ("host", "bytes") + "".join(" %10s" % n for n in names))
    for h in out:
        procs, _ = out[h]
        for s in sizes:
            mins = [min(p[s][i] for p in procs) * CLK[h] for i in range(len(names))]
            print("%-5s %-6d" % (h, s) + "".join(" %10.2f" % v for v in mins))
        print()


main()
