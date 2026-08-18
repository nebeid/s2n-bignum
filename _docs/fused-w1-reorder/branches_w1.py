#!/usr/bin/env python3
"""Static trace of the fused region: for each nblk in 1..4, how many TAKEN
branches are executed between the entry test and the `ret`, and in what order
the section labels are visited.  This is the mechanism claim for the `f4`/`f4i`
dispatch variants, checked against the emitted assembly rather than asserted.

Only `cmp x9, #imm` / `b.<cond> L` / `b L` / `ret` matter; everything else is
straight-line.  Usage: branches_w1.py [variant:prefix ...]
"""
import re, sys

DEFAULT = ["w1:mxh", "f4:w1p", "f4i:w1q", "lbr:w1t", "lrev:w1u", "ptre:w1o"]
COND = {"eq": lambda a, b: a == b, "ne": lambda a, b: a != b,
        "le": lambda a, b: a <= b, "gt": lambda a, b: a > b,
        "lt": lambda a, b: a < b, "ge": lambda a, b: a >= b}


def trace(path, pfx, n):
    lines = [l.split("//")[0].rstrip() for l in open(path)]
    start = next(i for i, l in enumerate(lines)
                 if l.startswith(".L256_dec_%s_small:" % pfx))
    lab = {}
    for i, l in enumerate(lines):
        m = re.match(r"^(\.[A-Za-z0-9_.]+):", l)
        if m:
            lab.setdefault(m.group(1), i)
    # the entry test at the anchor
    pc, x9, cmpv, taken, visited, steps = start, 16 * n, None, 0, [], 0
    while steps < 4000:
        steps += 1
        l = lines[pc].strip()
        m = re.match(r"^(\.L256_dec_%s_g\d+):" % pfx, lines[pc])
        if m:
            visited.append(m.group(1).split("_")[-1])
        mm = re.match(r"cmp\s+x9,\s*#(\d+)", l)
        if mm:
            cmpv = int(mm.group(1))
            pc += 1
            continue
        mm = re.match(r"b\.(\w+)\s+(\S+)", l)
        if mm:
            c, t = mm.group(1), mm.group(2)
            if COND[c](x9, cmpv):
                taken += 1
                pc = lab[t]
                continue
            pc += 1
            continue
        mm = re.match(r"^b\s+(\S+)", l)
        if mm:
            taken += 1
            pc = lab[mm.group(1)]
            continue
        if l == "ret":
            return taken, visited
        pc += 1
    return None, visited


for a in (sys.argv[1:] or DEFAULT):
    v, pfx = a.split(":")
    row = []
    for n in (1, 2, 3, 4):
        t, vis = trace("src/%s.S" % v, pfx, n)
        row.append("n=%d: %s taken, sections %s" % (n, t, "->".join(vis)))
    print("%-6s %s" % (v, " | ".join(row)))
