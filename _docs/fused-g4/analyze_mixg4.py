#!/usr/bin/env python3
"""Mixed-workload analysis for the g4 experiment.

  analyze_mixg4.py mix logs/mixg4_<host>.log     -- the 12-slot mix run
  analyze_mixg4.py aa  logs/mixaa_g4_<host>.log  -- 4-slot placement controls
                                                    and paired both-rank pairs

Mixes A-D are the same sequences as _docs/fused-t4p8.md and
_docs/fused-mix4s4.md, so the numbers are directly comparable.
"""
import re, sys, statistics as st

MIXES = ["A", "B", "C", "D", "E", "F", "R1", "R2", "R3", "R4", "R6"]


def parse(path):
    procs, cur, names, tag = [], None, None, ""
    for ln in open(path):
        m = re.match(r"^=== process (\S+)", ln) or re.match(r"^### (\S+)", ln)
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
    mixes = [m for m in MIXES if m in procs[0][1]]
    print("%d processes; slots: %s\n" % (len(procs), " ".join(names)))

    def mn(n, m):
        return min(p[m][n] for _, p in procs)

    def dmed(n, m, ref="base"):
        return st.median([100.0 * (p[m][n] - p[m][ref]) / p[m][ref] for _, p in procs])

    def fl(m, ref, copies):
        return max(abs(100.0 * (p[m][x] - p[m][ref]) / p[m][ref])
                   for _, p in procs for x in copies)

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
    print("| mix | base A/A | dsp0 A/A | g4 A/A |")
    print("|---|---:|---:|---:|")
    for m in mixes:
        print("| %s | %.2f | %.2f | %.2f |"
              % (m, fl(m, "base", ("baseAA",)), fl(m, "dsp0", ("dsp0AA",)),
                 fl(m, "g4", ("g4AA",))))

    print("\n### head-to-head in each mix (percentage POINTS, +ve = first slower)")
    pairs = [("g4", "t4"), ("g4", "a4"), ("a4", "t4"), ("g4", "g4h"),
             ("g4", "t4p8"), ("g4p8", "t4p8"), ("g4", "m4s4h")]
    print("| mix |" + "".join(" %s-%s |" % p for p in pairs))
    print("|---|" + "---:|" * len(pairs))
    for m in mixes:
        print("| %s |" % m + "".join(" %+.2f |" % (dmed(a, m) - dmed(b, m))
                                     for a, b in pairs))


def aarun(path):
    procs, _ = parse(path)
    groups = {}
    for tag, p in procs:
        groups.setdefault(tag, []).append(p)
    mixes = ["A", "B", "C", "D", "F", "R1", "R3"]
    for tag, ps in groups.items():
        names = list(ps[0]["A"].keys())
        if tag.startswith("AA-"):
            print("### %s : spread over 4 link slots (max-min)/min, %%" % tag)
            print("  " + "".join(" %6s" % m for m in mixes))
            row = [max(100.0 * (max(p[m][n] for n in names) - min(p[m][n] for n in names))
                       / min(p[m][n] for n in names) for p in ps) for m in mixes]
            print("  " + "".join(" %6.2f" % v for v in row))
        else:
            b = names[1].rsplit("_", 1)[0]
            print("### %s : %s vs %s, per process, both address ranks (%%, +ve = %s slower)"
                  % (tag, names[1], names[0], b))
            print("  " + "".join(" %6s" % m for m in mixes))
            for p in ps:
                r0 = ["%+6.2f" % (100.0 * (p[m][names[1]] - p[m][names[0]]) / p[m][names[0]])
                      for m in mixes]
                r1 = ["%+6.2f" % (100.0 * (p[m][names[3]] - p[m][names[2]]) / p[m][names[2]])
                      for m in mixes]
                print("  " + " ".join(r0) + "   |" + " ".join(r1))


if __name__ == "__main__":
    (mixrun if sys.argv[1] == "mix" else aarun)(sys.argv[2])
