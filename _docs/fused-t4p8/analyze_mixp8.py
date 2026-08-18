#!/usr/bin/env python3
"""Mixed-workload analysis for the t4p8 experiment.

  analyze_mixp8.py mix  logs/mixp8_<host>.log     -- the 12-slot mix run
  analyze_mixp8.py aa   logs/mixaa_p8_<host>.log  -- 4-slot placement controls

Mix run: per-mix absolute min ns/call over all processes, Delta % vs base
(median of per-process deltas), the A/A placement floors, and the 128 B : 80 B
traffic-ratio scan R1..R6 with the t4p8-vs-t5 break-even interpolated.
"""
import re, sys, statistics as st

RAT = {"R1": 1.0, "R2": 2.0, "R3": 3.0, "R4": 4.0, "R6": 6.0}


def parse(path):
    """-> list of (tag, {mix: {name: ns}})"""
    procs, cur, names, tag = [], None, None, ""
    for ln in open(path):
        m = re.match(r"^=== process (\S+)", ln)
        if m:
            tag = m.group(1)
            cur = None
            continue
        m = re.match(r"^### (\S+)", ln)
        if m:
            tag = m.group(1)
            cur = None
            continue
        if ln.startswith("mix "):
            names = [x.strip() for x in ln.split("||")[0].split("|")[1:]]
            cur = {}
            procs.append((tag, cur))
            continue
        m = re.match(r"^([A-Z][0-9]?)\s+\|", ln)
        if m and cur is not None:
            vals = [float(x) for x in re.findall(r"\|\s*([0-9.]+)", ln.split("||")[0])]
            cur[m.group(1)] = dict(zip(names, vals))
    return procs, names


def mixrun(path):
    procs, names = parse(path)
    mixes = [m for m in ["A", "B", "C", "D", "E", "F", "R1", "R2", "R3", "R4", "R6"]
             if m in procs[0][1]]
    print("%d processes; slots: %s\n" % (len(procs), " ".join(names)))

    def mn(n, m):
        return min(p[m][n] for _, p in procs)

    def dmed(n, m, ref="base"):
        return st.median([100.0 * (p[m][n] - p[m][ref]) / p[m][ref] for _, p in procs])

    def fl(m, ref, copies):
        return max(abs(100.0 * (p[m][x] - p[m][ref]) / p[m][ref]) for _, p in procs for x in copies)

    print("### absolute ns/call (min over processes)")
    print("%-4s" % "mix" + "".join(" %8s" % n for n in names))
    for m in mixes:
        print("%-4s" % m + "".join(" %8.3f" % mn(n, m) for n in names))

    print("\n### Delta %% vs base (median of per-process deltas)")
    cols = [n for n in names if n != "base"]
    print("| mix |" + "".join(" %s |" % n for n in cols))
    print("|---|" + "---:|" * len(cols))
    for m in mixes:
        print("| %s |" % m + "".join(" %+.2f |" % dmed(n, m) for n in cols))

    print("\n### placement floors (worst |delta| between identical objects)")
    print("| mix | base A/A | dsp0 A/A | t4p8 A/A |")
    print("|---|---:|---:|---:|")
    for m in mixes:
        print("| %s | %.2f | %.2f | %.2f |"
              % (m, fl(m, "base", ("baseAA", "baseAB")), fl(m, "dsp0", ("dsp0AA",)),
                 fl(m, "t4p8", ("t4p8AA",))))

    print("\n### 128 B : 80 B traffic-ratio scan (mixes R1..R6: only nblk=8 and nblk=5)")
    print("| ratio 8:5 | base ns | t5 ns | t4p8 ns | t8 ns | t5 D% | t4p8 D% | t4p8-t5 (points) |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|")
    pts = []
    for m in ["R1", "R2", "R3", "R4", "R6"]:
        if m not in mixes:
            continue
        d5, d48 = dmed("t5", m), dmed("t4p8", m)
        pts.append((RAT[m], d48 - d5))
        print("| %g:1 | %.3f | %.3f | %.3f | %.3f | %+.2f | %+.2f | %+.2f |"
              % (RAT[m], mn("base", m), mn("t5", m), mn("t4p8", m), mn("t8", m),
                 d5, d48, d48 - d5))
    # interpolate the crossing of (t4p8 - t5)
    cross = None
    for (r1, v1), (r2, v2) in zip(pts, pts[1:]):
        if v1 > 0 >= v2 or v1 < 0 <= v2:
            cross = r1 + (0 - v1) * (r2 - r1) / (v2 - v1)
            break
    if cross is not None:
        print("\nmeasured break-even ratio (t4p8 == t5): %.2f : 1  (128 B calls : 80 B calls)" % cross)
    else:
        print("\nno crossing inside the scanned range: t4p8 - t5 = %s"
              % ", ".join("%g:1 %+.2f" % p for p in pts))


def aarun(path):
    procs, _ = parse(path)
    groups = {}
    for tag, p in procs:
        groups.setdefault(tag, []).append(p)
    mixes = ["A", "B", "C", "D", "F", "R3"]
    for tag, ps in groups.items():
        names = list(ps[0]["A"].keys())
        if tag.startswith("AA-"):
            print("### %s : spread over 4 link slots (max-min)/min, %%" % tag)
            print("  " + "".join(" %6s" % m for m in mixes))
            row = []
            for m in mixes:
                sp = max(100.0 * (max(p[m][n] for n in names) - min(p[m][n] for n in names))
                         / min(p[m][n] for n in names) for p in ps)
                row.append(sp)
            print("  " + "".join(" %6.2f" % v for v in row))
        else:
            a, b = names[0].rsplit("_", 1)[0], names[1].rsplit("_", 1)[0]
            print("### %s : %s vs %s, per process, both address ranks (%% , +ve = %s slower)"
                  % (tag, names[1], names[0], b))
            print("  " + "".join(" %6s" % m for m in mixes))
            for p in ps:
                r0 = ["%+6.2f" % (100.0 * (p[m][names[1]] - p[m][names[0]]) / p[m][names[0]])
                      for m in mixes]
                r1 = ["%+6.2f" % (100.0 * (p[m][names[3]] - p[m][names[2]]) / p[m][names[2]])
                      for m in mixes]
                print("  " + " ".join(r0) + "   |" + " ".join(r1))


if __name__ == "__main__":
    if sys.argv[1] == "mix":
        mixrun(sys.argv[2])
    else:
        aarun(sys.argv[2])
