#!/usr/bin/env python3
"""Static checks + slot accounting for the generated fused bodies.

1. aese/aesmc adjacency: every `aese` that has a partner `aesmc` on the same
   register must be IMMEDIATELY followed by it (breaking the fusion doubles
   AES cost -- established by the destagger experiment).
2. SIMD issue-slot count per fused body (fused pair = 1 slot, loads/stores
   excluded: they do not consume SIMD issue slots).
3. Register-partition report: which SIMD registers each body writes, and how
   many are free.
"""
import re, sys, collections

SIMD_ALU = re.compile(r"^\s*(aese|aesmc|pmull2?|eor3?|ext|rev64|rev32|movi|add|mov|trn1|trn2|bif|and|zip1|zip2|ins|umov)\b")
LOADSTORE = re.compile(r"^\s*(ld[1-4rp]?|st[1-4rp]?)\b")
VREG = re.compile(r"\bv(\d+)\.")


def regions(lines):
    """yield (name, [lines]) for each .L256_dec_fused_N body"""
    cur, name = None, None
    for ln in lines:
        m = re.match(r"^(\.L256_dec_fused_\d+):", ln)
        if m:
            if cur is not None:
                yield name, cur
            name, cur = m.group(1), []
            continue
        if re.match(r"^\.L256_dec_(ret|fs_)", ln) and cur is not None:
            yield name, cur
            cur, name = None, None
            continue
        if cur is not None:
            cur.append(ln)
    if cur is not None:
        yield name, cur


def check(path):
    lines = open(path).read().split("\n")
    bad = 0
    # ---- 1. global aese/aesmc adjacency ----
    code = [l for l in lines if l.strip() and not l.strip().startswith("//")]
    for i, l in enumerate(code):
        m = re.match(r"\s*aese\s+v(\d+)\.16b", l)
        if not m:
            continue
        r = m.group(1)
        nxt = code[i + 1] if i + 1 < len(code) else ""
        has_mc = re.match(r"\s*aesmc\s+v%s\.16b, v%s\.16b" % (r, r), nxt)
        # a lone aese (round 13) is legal; what is illegal is aesmc for the same
        # register appearing LATER with something in between.
        if not has_mc:
            # find the next aesmc for this register before the next aese for it
            for j in range(i + 1, min(i + 12, len(code))):
                if re.match(r"\s*aese\s+v%s\.16b" % r, code[j]):
                    break
                if re.match(r"\s*aesmc\s+v%s\.16b" % r, code[j]):
                    print("ADJACENCY VIOLATION at line %d: aese v%s split from its aesmc" % (i, r))
                    bad += 1
                    break
    print("adjacency: %d violation(s)" % bad)

    # ---- 2/3. per-body accounting ----
    print("%-24s %6s %6s %6s %6s %7s  %s" %
          ("body", "pairs", "lone", "pmull", "othALU", "slots", "regs written / free"))
    for name, body in regions(lines):
        c = [l for l in body if l.strip() and not l.strip().startswith("//")]
        pairs = lone = pmull = oth = 0
        written = set()
        i = 0
        while i < len(c):
            l = c[i]
            if re.match(r"\s*aese\s+v(\d+)\.16b", l):
                if i + 1 < len(c) and re.match(r"\s*aesmc\s", c[i + 1]):
                    pairs += 1
                    i += 2
                else:
                    lone += 1
                    i += 1
                continue
            if LOADSTORE.match(l):
                m = VREG.search(l)
                for r in re.findall(r"\b[qdv](\d+)", l.split(",")[0] + "," + (l.split(",")[1] if "," in l else "")):
                    pass
                i += 1
                continue
            if re.match(r"\s*(pmull2?)\b", l):
                pmull += 1
            elif SIMD_ALU.match(l) or l.strip().startswith(".inst"):
                oth += 1
            i += 1
        # registers written (destination = first vN/qN/dN operand)
        for l in c:
            s = l.strip()
            if s.startswith("//") or s.startswith("b") or s.startswith("cmp") or s.startswith("ret"):
                continue
            if s.startswith(".inst"):
                m = re.search(r"eor3 v(\d+)", s)
                if m:
                    written.add(int(m.group(1)))
                continue
            m = re.match(r"\S+\s+\{?\s*[vqd](\d+)", s)
            if m and not re.match(r"\s*st", s):
                written.add(int(m.group(1)))
        slots = pairs + lone + pmull + oth
        # registers touched in the INTERLEAVED region only (from the first aese
        # onward): the CTR-setup temps all die before AES round 0.
        first = next(k for k, l in enumerate(c) if re.match(r"\s*aese\b", l))
        ilv = set()
        for l in c[first:]:
            s = l.strip()
            if s.startswith(".inst"):
                m = re.search(r"eor3 v(\d+)", s)
                if m:
                    ilv.add(int(m.group(1)))
                continue
            m = re.match(r"\S+\s+\{?\s*[vqd](\d+)", s)
            if m and not re.match(r"\s*st", s):
                ilv.add(int(m.group(1)))
        ilv.add(30)          # counter, live across the region
        free = sorted(set(range(32)) - ilv)
        print("%-24s %6d %6d %6d %6d %7d  ilv_used=%d free=%d %s" %
              (name, pairs, lone, pmull, oth, slots, len(ilv), len(free), free))
    return bad


if __name__ == "__main__":
    sys.exit(1 if check(sys.argv[1]) else 0)
