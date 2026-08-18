#!/usr/bin/env python3
"""Static checks + per-nblk SIMD issue-slot accounting for a mix4s4 variant.

Same conventions as fused-cascade/verify_casck.py (from which the counters are
taken verbatim in spirit):
  1. aese/aesmc adjacency over the WHOLE file (a split pair doubles AES cost).
  2. Slot count per region: adjacent aese+aesmc = 1 slot, `.inst`-encoded eor3
     counted, loads/stores excluded (they consume no SIMD issue slot).
  3. Per-nblk total = common/dispatch + stub_n + every group with rem <= n +
     epilogue, and the 4-slots/cycle floor.
  4. `aese` count per nblk, which must be exactly 14n (no dead AES).
  5. SIMD registers written in the region.

Usage: verify_mx.py <file.S> [prefix]      (prefix default "mx")
"""
import re, sys

SIMD_ALU = re.compile(r"^\s*(aese|aesmc|pmull2?|eor3?|ext|rev64|rev32|movi|add|sub|mov|trn1|trn2|bif|and|zip1|zip2|ins|umov)\s+[vqd]")
LOADSTORE = re.compile(r"^\s*(ld[1-4rp]?|st[1-4rp]?)\b")


def count(c):
    pairs = lone = pmull = oth = aese = 0
    i = 0
    while i < len(c):
        l = c[i]
        if re.match(r"\s*aese\s", l):
            aese += 1
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
    return pairs + lone + pmull + oth, aese


def loads(c):
    return sum(1 for l in c if LOADSTORE.match(l) and re.match(r"\s*ld", l))


def main(path, pfx="mx"):
    lines = open(path).read().split("\n")
    LBL = re.compile(r"^(\.L256_dec_%s_[A-Za-z0-9_]+):" % pfx)

    # ---- adjacency, whole file
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
    print("adjacency: %d violation(s)" % bad)

    # ---- regions
    R, LD, AE, order, cur, name, written = {}, {}, {}, [], None, None, set()
    for ln in lines:
        m = LBL.match(ln)
        if m:
            if cur is not None:
                R[name], AE[name] = count(cur)
                LD[name] = loads(cur)
            name, cur, = m.group(1), []
            order.append(name)
            continue
        if ln.startswith(".L256_dec_ret:") and cur is not None:
            R[name], AE[name] = count(cur)
            LD[name] = loads(cur)
            cur = None
            continue
        if cur is not None:
            s = ln.strip()
            if s and not s.startswith("//"):
                cur.append(ln)
                if s.startswith(".inst"):
                    mm = re.search(r"eor3 v(\d+)", s)
                    if mm:
                        written.add(int(mm.group(1)))
                else:
                    mm = re.match(r"\S+\s+\{?\s*[vqd](\d+)", s)
                    if mm and not re.match(r"(st|cmp)", s):
                        written.add(int(mm.group(1)))
    if cur is not None:
        R[name], AE[name] = count(cur)
        LD[name] = loads(cur)

    print("\n%-30s %7s %7s %7s" % ("region", "slots", "aese", "loads"))
    for n in order:
        print("%-30s %7d %7d %7d" % (n, R[n], AE[n], LD[n]))

    pre = sum(R[n] for n in order if not re.search(r"_(stub_|g)\d+$", n) and not n.endswith("_done"))
    epi = sum(R[n] for n in order if n.endswith("_done"))
    lpre = sum(LD[n] for n in order if not re.search(r"_(stub_|g)\d+$", n) and not n.endswith("_done"))
    lepi = sum(LD[n] for n in order if n.endswith("_done"))
    gs = sorted((int(re.search(r"_g(\d+)$", n).group(1)), n)
                for n in order if re.search(r"_g\d+$", n))
    entries = [r for r, _ in gs]
    print("\nentry set (nblk with an entry label): %s" % sorted(entries))
    print("\nnblk  prep  stub  groups  epi   slots  floor@4/cyc   aese  want  loads")
    ok = True
    for n in sorted(entries):
        sn = ".L256_dec_%s_stub_%d" % (pfx, n)
        st = R.get(sn, 0)
        gsum = sum(R[g] for r, g in gs if r <= n)
        ae = AE.get(sn, 0) + sum(AE[g] for r, g in gs if r <= n)
        ld = lpre + LD.get(sn, 0) + sum(LD[g] for r, g in gs if r <= n) + lepi
        tot = pre + st + gsum + epi
        flag = "" if ae == 14 * n else "   <-- MISMATCH"
        if ae != 14 * n:
            ok = False
        print("%4d %5d %5d %7d %4d %7d %12.2f %6d %5d %6d%s"
              % (n, pre, st, gsum, epi, tot, tot / 4.0, ae, 14 * n, ld, flag))
    print("\nSIMD regs written: %s" % sorted(written))
    print("free: %s" % sorted(set(range(32)) - written))
    return (0 if (bad == 0 and ok) else 1)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "mx"))
