#!/usr/bin/env python3
"""Static checks + per-nblk SIMD issue-slot accounting for the cascade.

1. aese/aesmc adjacency over the WHOLE file (a split pair doubles AES cost).
2. Slot count of every cascade region (common prep, each entry stub, each
   fall-through section, epilogue) with the established convention:
   adjacent aese+aesmc = 1 slot, `.inst`-encoded eor3 counted, loads/stores
   excluded (they do not consume SIMD issue slots).
3. Per-nblk total = common + stub_n + sum(section_j for j=n..1) + epilogue,
   and the 4-slots/cycle floor.
4. Registers written inside the cascade (for the frame / MAYCHANGE argument).
"""
import re, sys

SIMD_ALU = re.compile(r"^\s*(aese|aesmc|pmull2?|eor3?|ext|rev64|rev32|movi|add|sub|mov|trn1|trn2|bif|and|zip1|zip2|ins|umov)\s+[vqd]")
LOADSTORE = re.compile(r"^\s*(ld[1-4rp]?|st[1-4rp]?)\b")

LBL = re.compile(r"^(\.L256_dec_casc2_[A-Za-z0-9_]+):")


def regions(lines):
    cur, name = None, None
    out = []
    for ln in lines:
        m = LBL.match(ln)
        if m:
            if cur is not None:
                out.append((name, cur))
            name, cur = m.group(1), []
            continue
        if ln.startswith(".L256_dec_ret:") and cur is not None:
            out.append((name, cur))
            cur = None
            continue
        if cur is not None:
            cur.append(ln)
    if cur is not None:
        out.append((name, cur))
    return out


def count(c):
    pairs = lone = pmull = oth = 0
    i = 0
    while i < len(c):
        l = c[i]
        if re.match(r"\s*aese\s", l):
            if i + 1 < len(c) and re.match(r"\s*aesmc\s", c[i + 1]):
                pairs += 1
                i += 2
            else:
                lone += 1
                i += 1
            continue
        if LOADSTORE.match(l):
            i += 1
            continue
        if re.match(r"\s*pmull2?\s", l):
            pmull += 1
        elif l.strip().startswith(".inst") or SIMD_ALU.match(l):
            oth += 1
        i += 1
    return pairs, lone, pmull, oth


def adjacency(lines):
    code = [l for l in lines if l.strip() and not l.strip().startswith("//")]
    bad = 0
    for i, l in enumerate(code):
        m = re.match(r"\s*aese\s+v(\d+)\.16b", l)
        if not m:
            continue
        r = m.group(1)
        nxt = code[i + 1] if i + 1 < len(code) else ""
        if re.match(r"\s*aesmc\s+v%s\.16b, v%s\.16b" % (r, r), nxt):
            continue
        for j in range(i + 1, min(i + 12, len(code))):
            if re.match(r"\s*aese\s+v%s\.16b" % r, code[j]):
                break
            if re.match(r"\s*aesmc\s+v%s\.16b" % r, code[j]):
                print("ADJACENCY VIOLATION near %r" % l.strip())
                bad += 1
                break
    return bad


def main(path):
    lines = open(path).read().split("\n")
    bad = adjacency(lines)
    print("adjacency: %d violation(s)" % bad)
    R = dict()
    order = []
    written = set()
    for name, body in regions(lines):
        c = [l for l in body if l.strip() and not l.strip().startswith("//")]
        R[name] = count(c)
        order.append(name)
        for l in c:
            s = l.strip()
            if s.startswith(".inst"):
                m = re.search(r"eor3 v(\d+)", s)
                if m:
                    written.add(int(m.group(1)))
                continue
            m = re.match(r"\S+\s+\{?\s*[vqd](\d+)", s)
            if m and not re.match(r"\s*st", s):
                written.add(int(m.group(1)))
    print("\n%-26s %6s %5s %6s %7s %7s" % ("region", "pairs", "lone", "pmull", "othALU", "slots"))
    for n in order:
        p, lo, pm, ot = R[n]
        print("%-26s %6d %5d %6d %7d %7d" % (n, p, lo, pm, ot, p + lo + pm + ot))

    def s(name):
        return sum(R[name]) if name in R else 0

    # regions that are pure dispatch/label glue have zero slots anyway
    common = s(".L256_dec_casc2_small") + s(".L256_dec_casc2_34") + \
        s(".L256_dec_casc2_hi") + s(".L256_dec_casc2_78")
    epi = s(".L256_dec_casc2_done")
    print("\nnblk  common  stub  sections  epi   slots  floor@4/cyc   aese")
    for n in range(1, 9):
        st = s(".L256_dec_casc2_stub_%d" % n)
        sec = sum(s(".L256_dec_casc2_%d" % j) for j in range(1, n + 1))
        tot = common + st + sec + epi
        print("%4d %7d %5d %9d %4d %7d %12.2f %6d" %
              (n, common, st, sec, epi, tot, tot / 4.0, 14 * n))
    print("\nSIMD regs written in the cascade: %s" % sorted(written))
    print("free: %s" % sorted(set(range(32)) - written))
    return bad


if __name__ == "__main__":
    sys.exit(1 if main(sys.argv[1]) else 0)
