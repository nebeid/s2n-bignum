#!/usr/bin/env python3
"""THE ONE-`ret` CHECK.

`AESV8_GCM_8X_DEC_256_CORRECT` pins a single literal exit address, so for
nblk >= 1 the function must have exactly one reachable `ret`.  This script
checks that three ways:

 1. STATIC INVENTORY.  Every `ret` in the source, with the label that governs
    it.  There must be exactly two: the one in `.L256_dec_epilogue`'s frame
    restore, and the PRE-EXISTING `.L256_dec_ret` zero-length/non-whole-blocks
    early-exit stub (`mov w0,#0` + `ret`), which is discharged one level up in
    the subroutine wrapper and is deliberately left alone.  A third `ret` -- the
    fused region's duplicated frame restore -- is the defect.
 2. STUB FIDELITY.  The `.L256_dec_ret` stub's instructions must be
    byte-identical to the baseline's.
 3. DYNAMIC TRACE.  Simulating the dispatch for nblk = 1,2,3,4 must land on the
    SAME `ret` line that the nblk > 8 path uses.

Usage: onret_w1.py <file.S> <label-prefix> [baseline.S]
"""
import re, sys

COND = {"eq": lambda a, b: a == b, "ne": lambda a, b: a != b,
        "le": lambda a, b: a <= b, "gt": lambda a, b: a > b,
        "lt": lambda a, b: a < b, "ge": lambda a, b: a >= b}


def load(path):
    return [l.split("//")[0].rstrip() for l in open(path)]


def labels(lines):
    lab = {}
    for i, l in enumerate(lines):
        m = re.match(r"^(\.[A-Za-z0-9_.]+):", l)
        if m:
            lab.setdefault(m.group(1), i)
    return lab


def governing(lines, i):
    for j in range(i, -1, -1):
        m = re.match(r"^(\.[A-Za-z0-9_.]+):", lines[j])
        if m:
            return m.group(1)
    return "<function entry>"


def trace_to_ret(lines, lab, start, x9):
    pc, cmpv, n = start, None, 0
    while n < 8000:
        n += 1
        l = lines[pc].strip()
        m = re.match(r"cmp\s+x9,\s*#(\d+)", l)
        if m:
            cmpv = int(m.group(1)); pc += 1; continue
        m = re.match(r"b\.(\w+)\s+(\S+)", l)
        if m:
            pc = lab[m.group(2)] if COND[m.group(1)](x9, cmpv) else pc + 1
            continue
        m = re.match(r"^b\s+(\S+)", l)
        if m:
            pc = lab[m.group(1)]; continue
        if l == "ret":
            return pc
        pc += 1
    return None


def main(path, pfx, basepath=None):
    lines = load(path)
    lab = labels(lines)
    rets = [i for i, l in enumerate(lines) if l.strip() == "ret"]
    print("== 1. static inventory: %d `ret` in %s" % (len(rets), path))
    for i in rets:
        print("   line %-5d governed by %s" % (i + 1, governing(lines, i)))
    stub = [i for i in rets if governing(lines, i) == ".L256_dec_ret"]
    other = [i for i in rets if i not in stub]
    ok = (len(rets) == 2 and len(stub) == 1 and len(other) == 1)
    print("   -> %s" % ("EXACTLY ONE non-stub `ret` (plus the pre-existing "
                        ".L256_dec_ret early-exit stub)" if ok
                        else "WRONG: expected 2 total / 1 stub / 1 non-stub"))

    if basepath:
        b = load(basepath)
        bl = labels(b)
        i, j = bl[".L256_dec_ret"], lab[".L256_dec_ret"]
        bs = [x.strip() for x in b[i:i + 4] if x.strip()][1:3]
        cs = [x.strip() for x in lines[j:j + 4] if x.strip()][1:3]
        same = bs == cs
        print("== 2. .L256_dec_ret stub fidelity: %s  %s"
              % ("UNTOUCHED" if same else "CHANGED", cs))
        ok = ok and same

    print("== 3. dynamic trace: which `ret` line does each nblk reach?")
    big = trace_to_ret(lines, lab, lab[".L256_dec_epilogue"], 16 * 64)
    print("   nblk>8 (via .L256_dec_epilogue) -> ret at line %s" % (big + 1))
    for n in (1, 2, 3, 4):
        r = trace_to_ret(lines, lab, lab[".L256_dec_%s_small" % pfx], 16 * n)
        good = (r == big)
        print("   nblk=%d -> ret at line %-5s  %s"
              % (n, r + 1, "SAME as nblk>8" if good else "*** DIFFERENT ***"))
        ok = ok and good
    print("VERDICT: %s" % ("one exit address for nblk >= 1" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2],
                  sys.argv[3] if len(sys.argv) > 3 else None))
