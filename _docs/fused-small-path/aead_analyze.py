#!/usr/bin/env python3
"""Parse bssl-speed logs -> ns/op per (variant, direction, size), min over reps.

Only the EXACT algorithm name "AEAD-AES-256-GCM" is kept; -SIV / -TLS12 /
-TLS13 rows are discarded by exact-name match.
"""
import re, os, sys, statistics as st

HOSTS = ["GV3", "GV4", "GV5"]
SIZES = [16, 32, 64, 128, 256, 512, 1024, 4096]
VARIANT_DESC = {
    "A": "aws-lc as shipped (own fallback <256 B, own 8x kernel >=256 B)",
    "B": "our HEAD kernel, threshold 16",
    "C": "new fused <=8-block path, threshold 16",
}
LINE = re.compile(r"^Did (\d+) (\S+) (seal|open) \((\d+) bytes\) operations in (\d+)us \(([0-9.]+) ops/sec\)")


def parse(path):
    """-> {(variant,dir,size): [ns_per_op per rep]}"""
    d = {}
    var = None
    for ln in open(path):
        m = re.match(r"^### rep=(\d+) variant=(\S+)", ln)
        if m:
            var = m.group(2)
            continue
        m = LINE.match(ln)
        if not m:
            continue
        name, dirn, size, ops = m.group(2), m.group(3), int(m.group(4)), float(m.group(6))
        if name != "AEAD-AES-256-GCM":       # exact-name filter: drops -SIV, -TLS12/13
            continue
        d.setdefault((var, dirn, size), []).append(1e9 / ops)
    return d


def main():
    base = os.path.dirname(os.path.abspath(__file__)) + "/logs"
    for h in HOSTS:
        p = os.path.join(base, "aead_%s.txt" % h)
        if not os.path.exists(p):
            print("missing", p)
            continue
        d = parse(p)
        nreps = max(len(v) for v in d.values())
        print("\n================ %s  (ns/op, min of %d reps; AD = 13 bytes) ================" % (h, nreps))
        for dirn, label in (("open", "open = DECRYPT"), ("seal", "seal = encrypt")):
            print("\n  %s" % label)
            print("    %-8s" % "variant" + "".join("%9d" % s for s in SIZES))
            for v in ("A", "B", "C"):
                row = ["%9.1f" % min(d[(v, dirn, s)]) if (v, dirn, s) in d else "        -" for s in SIZES]
                print("    %-8s" % v + "".join(row))
            print("    %-8s" % "C vs A%" + "".join(
                "%+9.1f" % (100.0 * (min(d[("C", dirn, s)]) / min(d[("A", dirn, s)]) - 1))
                if ("C", dirn, s) in d and ("A", dirn, s) in d else "        -" for s in SIZES))
            print("    %-8s" % "C vs B%" + "".join(
                "%+9.1f" % (100.0 * (min(d[("C", dirn, s)]) / min(d[("B", dirn, s)]) - 1))
                if ("C", dirn, s) in d and ("B", dirn, s) in d else "        -" for s in SIZES))
            print("    %-8s" % "C-A ns " + "".join(
                "%+9.1f" % (min(d[("C", dirn, s)]) - min(d[("A", dirn, s)]))
                if ("C", dirn, s) in d and ("A", dirn, s) in d else "        -" for s in SIZES))
            print("    %-8s" % "spread%" + "".join(
                "%9.2f" % (100.0 * (max(d[("A", dirn, s)]) / min(d[("A", dirn, s)]) - 1))
                if ("A", dirn, s) in d else "        -" for s in SIZES))


main()
