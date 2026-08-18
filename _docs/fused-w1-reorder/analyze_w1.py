#!/usr/bin/env python3
"""Parse measure_w1.sh logs -> per-size Delta % vs the base slot (absolute-min
estimator over every process and link ordering), plus the A/A floor for every
variant that appears twice (`x` and `xAA`).

Usage: analyze_w1.py <log...>
"""
import re, sys, collections

SIZE = re.compile(r"^(\d+)\s+(\d+)\s+\|")


def parse(path):
    procs = []                       # list of (order, {name: {bytes: ns}})
    names, cur, ordid = None, None, None
    for ln in open(path):
        if ln.startswith("bytes"):
            names = [c.strip() for c in ln.split("||")[0].split("|")[1:]]
            continue
        if ln.startswith("=== process"):
            ordid = ln.split()[-1]
            cur = collections.defaultdict(dict)
            procs.append((ordid, cur))
            continue
        m = SIZE.match(ln)
        if m and names is not None and cur is not None:
            nb = int(m.group(1))
            vals = [float(x) for x in ln.split("||")[0].split("|")[1:]]
            assert len(vals) == len(names), (len(vals), len(names))
            for n, v in zip(names, vals):
                cur[n][nb] = v
    return procs


def main(paths):
    procs = []
    for p in paths:
        procs += parse(p)
    allnames = []
    for _, d in procs:
        for n in d:
            if n not in allnames:
                allnames.append(n)
    sizes = sorted({b for _, d in procs for n in d for b in d[n]})
    mn = {n: {b: min(d[n][b] for _, d in procs if n in d and b in d[n])
              for b in sizes} for n in allnames}
    base = allnames[0]
    print("min ns/call over %d processes; base slot = %s" % (len(procs), base))
    print("%-8s %s" % ("variant", "".join("%10d" % b for b in sizes)))
    for n in allnames:
        print("%-8s %s" % (n, "".join("%10.3f" % mn[n][b] for b in sizes)))
    print()
    print("Delta %% vs %s" % base)
    print("%-8s %s" % ("variant", "".join("%10d" % b for b in sizes)))
    for n in allnames[1:]:
        print("%-8s %s" % (n, "".join("%+10.2f" % (100 * (mn[n][b] - mn[base][b])
                                                   / mn[base][b]) for b in sizes)))
    print()
    print("A/A floor (worst |Delta| between the two copies in any one process)")
    print("%-8s %s" % ("pair", "".join("%10d" % b for b in sizes)))
    for n in allnames:
        if n + "AA" in allnames:
            row = []
            for b in sizes:
                w = 0.0
                for _, d in procs:
                    if n in d and n + "AA" in d and b in d[n]:
                        w = max(w, abs(100 * (d[n + "AA"][b] - d[n][b]) / d[n][b]))
                row.append(w)
            print("%-8s %s" % (n, "".join("%10.2f" % x for x in row)))


if __name__ == "__main__":
    main(sys.argv[1:])
