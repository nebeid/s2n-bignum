#!/usr/bin/env python3
"""WIDTH-W fall-through fused cascade -- one generator spanning the whole
spectrum from the pure cascade (W=1) to eight separate bodies (W=8).

    W = 1  pure shared fall-through cascade: 8 one-block sections
    W = 2  four two-block super-sections + one-block odd prefixes
    W = 4  two four-block super-sections + 1/2/3-block prefixes and bodies
    W = 8  one eight-block body + standalone 1..7-block bodies
           (== the eight-separate-bodies design of fused-small-path/gen.py)

Structure for a given W (W must divide 8):

  .L256_dec_cascW_small:  common prep (counter base, Xi') + dispatch on x9
  stub_8 .. stub_1        acc <- Xi' * H^n, then branch to that entry's body
  ss<k>  for k = 8, 8-W, ..., W    super-sections of W blocks, powers k..k-W+1,
                                   falling through to ss<k-W>; ss<W> also does
                                   the MODULO reduce, tag and counter stores and
                                   falls into the shared epilogue
  pb<n>  for n mod W = q != 0, n-q > 0     prefix body of q blocks
                                           (powers n..n-q+1) then b ss<n-q>
  sb<n>  for n < W                         standalone body of n blocks
                                           (powers n..1) + MODULO + epilogue

Every path performs exactly n blocks of AES for nblk = n: no dead AES at any
width.  The per-nblk SIMD issue-slot count is IDENTICAL for every W, so the
series is a controlled experiment in one variable: how much independent work
sits *adjacent in program order*.

Registers (all 32; frame unchanged at 80 bytes; round keys rotate through
v26/v27/v28 as in the baseline, so the key schedule is loaded once per body
rather than once per block):
  AES states  v0..v(W-1)        ciphertext  v8..v(8+W-1)
  GHASH block v20  mid v21      products v22,v23,v30 (v22,v23 double as the
  H^p l|h     v24  k v25        MODULO temps, v30 as the counter-store temp)
  round keys  v26,v27,v28 (v28 = rk14 for the plaintext eor3)
  accumulators v17 hi / v18 mid / v19 lo    v16 Xi' then the MODULO constant
  counter v29    +1 v31
"""
import sys

HL = {8: 176, 7: 144, 6: 128, 5: 96, 4: 80, 3: 48, 2: 32, 1: 0}
KD = {8: 168, 7: 160, 6: 120, 5: 112, 4: 72, 3: 64, 2: 24, 1: 16}

RKREG = [26, 27, 28, 26, 27, 28, 26, 27, 28, 26, 27, 28, 26, 27]
KEYLOAD = {
    0:  "\tldp\tq26, q27, [x11, #0]\t\t\t//rk0, rk1",
    1:  "\tldp\tq28, q26, [x11, #32]\t\t\t//rk2, rk3",
    3:  "\tldp\tq27, q28, [x11, #64]\t\t\t//rk4, rk5",
    5:  "\tldp\tq26, q27, [x11, #96]\t\t\t//rk6, rk7",
    7:  "\tldp\tq28, q26, [x11, #128]\t\t\t//rk8, rk9",
    9:  "\tldp\tq27, q28, [x11, #160]\t\t\t//rk10, rk11",
    11: "\tldp\tq26, q27, [x11, #192]\t\t\t//rk12, rk13",
    12: "\tldr\tq28, [x11, #224]\t\t\t//rk14",
}

BLK, MID = 20, 21
P = (22, 23, 30)
HREG, KREG = 24, 25
AHI, AMID, ALO = 17, 18, 19
TAG, CTR, INC = 16, 29, 31
RK14 = 28


def E(d, n, m, a, cmt=""):
    w = 0xce000000 | (m << 16) | (a << 10) | (n << 5) | d
    return ".inst\t0x%08x\t//eor3 v%d.16b, v%d.16b, v%d.16b, v%d.16b\t%s" % (w, d, n, m, a, cmt)


def L(pfx):
    return ".L256_dec_%s" % pfx


def body_label(W, n, pfx):
    """which body does entry point n jump to?"""
    q = n % W
    if q == 0:
        return L("%s_ss%d" % (pfx, n))
    if n - q > 0:
        return L("%s_pb%d" % (pfx, n))
    return L("%s_sb%d" % (pfx, n))


def common(pfx):
    return ["",
            "%s_small:\t//[CASCW] nblk <= 8: fall-through cascade" % L(pfx),
            "\tld1\t{ v30.16b}, [x16]\t\t\t\t//CTR block 0 (raw)",
            "\tld1\t{ v19.16b}, [x3]\t\t\t\t//load Xi",
            "\tmov\tx15, #0x100000000\t\t\t//counter increment",
            "\tmovi\tv31.16b, #0x0",
            "\text\tv19.16b, v19.16b, v19.16b, #8",
            "\trev64\tv19.16b, v19.16b",
            "\tmov\tv31.d[1], x15\t\t\t\t//+1",
            "\text\tv16.16b, v19.16b, v19.16b, #8\t\t//partial-tag feed Xi'",
            "\trev32\tv29.16b, v30.16b\t\t\t//reversed counter base"]


def dispatch(pfx):
    s = lambda n: "%s_stub_%d" % (L(pfx), n)
    return ["\tcmp\tx9, #64", "\tb.gt\t%s_hi" % L(pfx),
            "\tcmp\tx9, #32", "\tb.gt\t%s_34" % L(pfx),
            "\tcmp\tx9, #16", "\tb.eq\t%s" % s(1), "\tb\t%s" % s(2),
            "%s_34:" % L(pfx),
            "\tcmp\tx9, #48", "\tb.eq\t%s" % s(3), "\tb\t%s" % s(4),
            "%s_hi:" % L(pfx),
            "\tcmp\tx9, #96", "\tb.gt\t%s_78" % L(pfx),
            "\tcmp\tx9, #80", "\tb.eq\t%s" % s(5), "\tb\t%s" % s(6),
            "%s_78:" % L(pfx),
            "\tcmp\tx9, #112", "\tb.eq\t%s" % s(7), "\tb\t%s" % s(8)]


def stub(W, n, pfx, zap=False):
    out = ["",
           "%s_stub_%d:\t//[CASCW] entry for nblk=%d: seed acc = Xi' * H^%d"
           % (L(pfx), n, n, n),
           "\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HREG, HL[n], n, n),
           "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KREG, KD[n], n),
           "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//Xi' mid" % (MID, TAG, TAG),
           "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//Xi' mid" % (MID, MID, TAG)]
    if zap:
        out.append("\t//[ZAP] stub %d products replaced by ZERO (wrong on purpose)" % n)
        out += ["\tmovi\tv%d.16b, #0" % AHI, "\tmovi\tv%d.16b, #0" % ALO,
                "\tmovi\tv%d.16b, #0" % AMID]
    else:
        out += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//Xi' high" % (AHI, TAG, HREG),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//Xi' low" % (ALO, TAG, HREG),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//Xi' mid" % (AMID, MID, KREG)]
    out.append("\tb\t%s" % body_label(W, n, pfx))
    return out


def aes_units(nb):
    units = []
    for r in range(14):
        for b in range(nb):
            pre = [KEYLOAD[r]] if (b == 0 and r in KEYLOAD) else []
            ln = ["\taese\tv%d.16b, v%d.16b" % (b, RKREG[r])]
            if r < 13:
                ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//blk %d - round %d" % (b, b, b, r))
            else:
                ln[0] += "\t\t\t\t//blk %d - round 13" % b
            units.append((pre, ln))
    return units


def ghash_blk(b, p, zap=False):
    ct = 8 + b
    hi, lo, md = P
    out = ["\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HREG, HL[p], p, p),
           "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KREG, KD[p], p),
           "\trev64\tv%d.16b, v%d.16b\t\t\t\t//GHASH H^%d block" % (BLK, ct, p),
           "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//H^%d mid" % (MID, BLK, BLK, p),
           "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//H^%d mid" % (MID, MID, BLK, p)]
    if zap:
        out.append("\t//[ZAP] H^%d products replaced by ZERO (wrong on purpose)" % p)
        out += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
                "\tmovi\tv%d.16b, #0" % md]
    else:
        out += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//H^%d high" % (hi, BLK, HREG, p),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d low" % (lo, BLK, HREG, p),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d mid" % (md, MID, KREG, p)]
    out += ["\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold high" % (AHI, AHI, hi),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold low" % (ALO, ALO, lo),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold mid" % (AMID, AMID, md)]
    return out


def late_ops():
    t1, t2, t3 = P
    return ["\tldr\td%d, [x10]\t\t\t\t//MODULO - load modulo constant" % TAG,
            "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//MODULO - top 64b align with mid" % (t1, AHI, TAG),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t//MODULO - karatsuba tidy up" % (t2, AHI, ALO),
            "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//MODULO - other top alignment" % (AHI, AHI, AHI),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t//MODULO - karatsuba tidy up" % (AMID, AMID, t2),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t//MODULO - fold into mid" % (t1, AHI, t1),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t//MODULO - fold into mid" % (AMID, AMID, t1),
            "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//MODULO - mid 64b align with low" % (AHI, AMID, TAG),
            "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//MODULO - other mid alignment" % (AMID, AMID, AMID),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t//MODULO - fold into low" % (ALO, ALO, AHI),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t//MODULO - fold into low" % (ALO, ALO, AMID),
            "\text\tv%d.16b, v%d.16b, v%d.16b, #8" % (ALO, ALO, ALO),
            "\trev64\tv%d.16b, v%d.16b" % (ALO, ALO),
            "\tst1\t{ v%d.16b }, [x3]\t\t\t\t//store the tag" % ALO,
            "\trev32\tv%d.16b, v%d.16b\t\t\t//counter after the last block" % (t3, CTR),
            "\tstr\tq%d, [x16]\t\t\t\t//store the updated counter" % t3]


def place(units, early, late, K):
    U = len(units)
    gap = {}
    for i, op in enumerate(early):
        gap.setdefault(i * K // len(early), []).append(op)
    if late:
        for i, op in enumerate(late):
            gap.setdefault(K + i * (U - K) // len(late), []).append(op)
    out = []
    for u, (pre, ln) in enumerate(units):
        out += pre
        out += ln
        out += gap.get(u, [])
    return out


def epilogue(label):
    return ["",
            "%s:\t//[CASCW] epilogue" % label,
            "\tmov\tx0, x9",
            "\tldp\td10, d11, [sp, #16]",
            "\tldp\td12, d13, [sp, #32]",
            "\tldp\td14, d15, [sp, #48]",
            "\tldp\td8, d9, [sp], #80",
            "\tret"]


def gen_body(label, powers, terminal, cont, ksec, k1, zapsec=0):
    """A body covering len(powers) blocks with the given H powers, in order.

    terminal: this body ends the GHASH -> emit MODULO/tag/counter + epilogue.
    cont:     label to branch to afterwards (None if terminal or fall-through).
    """
    nb = len(powers)
    units = aes_units(nb)
    U = len(units)
    early = []
    for b, p in enumerate(powers):
        early += ghash_blk(b, p, zap=(zapsec == p))
    late = late_ops() if terminal else []
    K = max(1, min(U - 1 if terminal else U, int(round((k1 if terminal else ksec) * U))))
    out = ["", "%s:\t//[CASCW] %d block(s), H^%s" % (label, nb, ",H^".join(map(str, powers)))]
    for b in range(nb):
        out.append("\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block %d" % (b, CTR, b))
        out.append("\tadd\tv%d.4s, v%d.4s, v%d.4s" % (CTR, CTR, INC))
    b = 0
    while b < nb:
        if b + 1 < nb:
            out.append("\tldp\tq%d, q%d, [x0], #32\t\t\t//ciphertext %d,%d" % (8 + b, 9 + b, b, b + 1))
            b += 2
        else:
            out.append("\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext %d" % (8 + b, b))
            b += 1
    out += place(units, early, late, K)
    for b in range(nb):
        out.append(E(b, 8 + b, b, RK14, "//H^%d block - result" % powers[b]))
    b = 0
    while b < nb:
        if b + 1 < nb:
            out.append("\tstp\tq%d, q%d, [x2], #32" % (b, b + 1))
            b += 2
        else:
            out.append("\tstr\tq%d, [x2], #16" % b)
            b += 1
    if cont:
        out.append("\tb\t%s" % cont)
    return out


ENTRY_ANCHOR = "\tadd\tx10, sp, #64"
RET_ANCHOR = ".L256_dec_ret:"


def apply(text, W, pfx, ksec, k1, zap=0, zapsec=0):
    assert 8 % W == 0
    lines = text.split("\n")
    i = lines.index(ENTRY_ANCHOR)
    lines[i:i + 1] = [ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #128\t\t\t\t//[CASCW] nblk <= 8 ?",
                      "\tb.le\t%s_small" % L(pfx)]
    region = common(pfx) + dispatch(pfx)
    for n in range(8, 0, -1):
        region += stub(W, n, pfx, zap=(zap == n))
    # the fall-through chain of super-sections
    for k in range(8, 0, -W):
        region += gen_body(L("%s_ss%d" % (pfx, k)), list(range(k, k - W, -1)),
                           terminal=(k == W), cont=None, ksec=ksec, k1=k1, zapsec=zapsec)
    region += epilogue(L("%s_done" % pfx))
    # odd prefixes and standalone small bodies
    for n in range(8, 0, -1):
        q = n % W
        if q == 0:
            continue
        if n - q > 0:
            region += gen_body(L("%s_pb%d" % (pfx, n)), list(range(n, n - q, -1)),
                               terminal=False, cont=L("%s_ss%d" % (pfx, n - q)),
                               ksec=ksec, k1=k1, zapsec=zapsec)
        else:
            region += gen_body(L("%s_sb%d" % (pfx, n)), list(range(n, 0, -1)),
                               terminal=True, cont=None, ksec=ksec, k1=k1, zapsec=zapsec)
            region += epilogue(L("%s_done%d" % (pfx, n)))
    region.append("")
    j = lines.index(RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, W = sys.argv[1], sys.argv[2], int(sys.argv[3])
    ksec, k1 = float(sys.argv[4]), float(sys.argv[5])
    pfx = sys.argv[6] if len(sys.argv) > 6 else "cw"
    zap = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    zapsec = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    open(dst, "w").write(apply(open(src).read(), W, pfx, ksec, k1, zap, zapsec))
    print("wrote %s W=%d ksec=%s k1=%s zap=%d zapsec=%d" % (dst, W, ksec, k1, zap, zapsec))
