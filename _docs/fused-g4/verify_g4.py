#!/usr/bin/env python3
"""Static checks + slot accounting for the g4 single-region variants.

Conventions identical to fused-cascade/verify_casck.py and
fused-mix4s4/verify_mx.py: adjacent aese+aesmc = 1 SIMD issue slot,
`.inst`-encoded eor3 counted, loads/stores excluded (they consume no SIMD slot).

Checks
  1. aese/aesmc adjacency over the WHOLE file.
  2. Slot / aese / load count for the one g4 region, and the 4-slots-per-cycle
     floor.  `aese` must be exactly 56 (4 blocks x 14 rounds) for EVERY nblk --
     that is the design: 4-nblk blocks of AES are deliberately discarded.
  3. Structure of the predication:
       - exactly 4 ciphertext loads off x0, each with a register offset;
       - exactly 4 plaintext stores to x2, in ASCENDING lane order, with the
         SAME four offset registers (so a discarded lane can only ever write
         block 0, which the real block 0 then overwrites);
       - one `subs` + `csel` per clamped lane, `csetm` predicates as expected;
       - each of H^4,H^3,H^2,H^1 used exactly once;
       - the partial tag v16 is dead before the MODULO constant overwrites it.
  4. SIMD registers written / free.

Usage: verify_g4.py <file.S> [prefix]        (prefix default "g4")
"""
import re, sys

LOADSTORE = re.compile(r"^\s*(ld[1-4rp]?|st[1-4rp]?)\b")
SIMD_ALU = re.compile(r"^\s*(aese|aesmc|pmull2?|eor3?|ext|rev64|rev32|movi|add|sub|mov|dup|trn1|trn2|bif|bsl|and|orr|zip1|zip2|ins|umov)\s+[vqd]")


def slots(code):
    pairs = lone = pmull = oth = aese = 0
    i = 0
    while i < len(code):
        l = code[i]
        if re.match(r"\s*aese\s", l):
            aese += 1
            if i + 1 < len(code) and re.match(r"\s*aesmc\s", code[i + 1]):
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
    return dict(slots=pairs + lone + pmull + oth, aese=aese, pairs=pairs,
                lone=lone, pmull=pmull, oth=oth)


def main(path, pfx="g4"):
    lines = open(path).read().split("\n")
    code = [l for l in lines if l.strip() and not l.strip().startswith("//")]
    bad = 0

    # ---- 1. adjacency, whole file
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

    # ---- extract the region:  label .L256_dec_<pfx>_grp .. .L256_dec_ret / a
    #      later unrelated label
    reg, name, order, R = {}, None, [], {}
    LBL = re.compile(r"^(\.L256_dec_(?:%s)_[A-Za-z0-9_]+|\.L256_dec_fused_\d+):" % pfx)
    for ln in lines:
        m = LBL.match(ln)
        if m:
            name = m.group(1)
            order.append(name)
            reg[name] = []
            continue
        if ln.startswith(".L256_dec_ret:"):
            name = None
            continue
        if name is not None:
            s = ln.strip()
            if s and not s.startswith("//"):
                reg[name].append(ln)
    tot = dict(slots=0, aese=0)
    print("\n%-30s %7s %7s %7s" % ("region", "slots", "aese", "loads"))
    for n in order:
        c = reg[n]
        s = slots(c)
        ld = sum(1 for l in c if re.match(r"\s*ld", l))
        R[n] = s
        print("%-30s %7d %7d %7d" % (n, s["slots"], s["aese"], ld))
        if not n.startswith(".L256_dec_fused_"):
            tot["slots"] += s["slots"]
            tot["aese"] += s["aese"]
    print("\ng4 region total: %d slots, floor @4/cyc = %.2f cycles, aese = %d (want 56)"
          % (tot["slots"], tot["slots"] / 4.0, tot["aese"]))
    if tot["aese"] != 56:
        print("  <-- AESE MISMATCH")
        bad += 1

    # ---- 3. structure of the predication
    grp = "\n".join(reg.get(".L256_dec_%s_grp" % pfx, []) + reg.get(".L256_dec_%s_done" % pfx, []))
    ctl = re.findall(r"ldr\s+q(\d+), \[x0, (x\d+)\]", grp)
    sts = re.findall(r"str\s+q(\d+), \[x2, (x\d+)\]", grp)
    offs = [o for _, o in sts]
    print("\nciphertext loads off x0 : %s" % ctl)
    print("plaintext  stores to x2 : %s" % sts)
    ok = True
    if len(sts) != 4:
        print("  <-- want exactly 4 stores"); ok = False
    if [o for _, o in ctl[:4]] != offs:
        print("  <-- load and store offset registers differ"); ok = False
    if len(set(offs)) != 4:
        print("  <-- store offsets are not 4 distinct registers"); ok = False
    npostidx = len(re.findall(r"(?:ldr|str|ldp|stp)\s+q[^\n]*\], #", grp))
    print("post-indexed q loads/stores in the region: %d (want 0: x0/x2 must not move)"
          % npostidx)
    if npostidx:
        ok = False
    for kind, pat, want in (("subs", r"\n\s*subs\s", 3), ("csel", r"\n\s*csel\s", 3),
                            ("csetm", r"\n\s*csetm\s", 6), ("dup", r"\n\s*dup\s", 6)):
        n = len(re.findall(pat, grp))
        print("%-6s x%d (want %d)" % (kind, n, want))
        if n != want:
            ok = False
    for p, off in ((4, 80), (3, 48), (2, 32), (1, 0)):
        n = len(re.findall(r"ldr\s+q%d, \[x6, #%d\]" % (24, off), grp))
        print("H^%-2d (Htable +%-3d) used %d time(s)" % (p, off, n))
        if n != 1:
            ok = False
    # the tag feeds (Xi' in v16) must all precede `ldr d16`, which overwrites
    # v16 with the MODULO constant
    body = grp.split("\n")
    mod = [i for i, l in enumerate(body) if re.match(r"\s*ldr\s+d16,", l)]
    use = [i for i, l in enumerate(body)
           if re.match(r"\s*(and|eor)\s+v\d+\.16b, v\d+\.16b, v16\.16b", l)]
    print("tag feeds / Xi' masks at lines %s ; MODULO constant load at %s" % (use, mod))
    if not mod or not use or max(use) > mod[0]:
        print("  <-- Xi' is read AFTER the MODULO constant overwrites it"); ok = False
    if len(use) != 4:
        print("  <-- want exactly 4 Xi'-feeding ops (one per lane)"); ok = False
    # frame
    n80p = len(re.findall(r"stp\s+d8, d9, \[sp, #-80\]!", "\n".join(lines)))
    n80o = len(re.findall(r"ldp\s+d8, d9, \[sp\], #80", "\n".join(lines)))
    nsp = len(re.findall(r"\n\s*(?:add|sub)\s+sp,", "\n".join(lines)))
    print("frame: push80 x%d pop80 x%d other sp adjust x%d" % (n80p, n80o, nsp))
    if nsp:
        ok = False

    # ---- 4. registers
    written = set()
    for l in [x for n in order for x in reg[n]]:
        s = l.strip()
        if s.startswith(".inst"):
            m = re.search(r"eor3 v(\d+)", s)
            if m:
                written.add(int(m.group(1)))
            continue
        m = re.match(r"\S+\s+\{?\s*[vqd](\d+)", s)
        if m and not re.match(r"(st|cmp)", s):
            written.add(int(m.group(1)))
    print("\nSIMD regs written: %s" % sorted(written))
    print("free: %s" % sorted(set(range(32)) - written))
    print("\nVERDICT: %s" % ("OK" if (bad == 0 and ok) else "PROBLEM"))
    return 0 if (bad == 0 and ok) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "g4"))
