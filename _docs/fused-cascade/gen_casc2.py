#!/usr/bin/env python3
"""WIDTH-2 fall-through fused cascade (the hybrid between gen_casck.py's pure
cascade and fused-small-path/gen.py's eight separate bodies).

The pure cascade (width 1) has exactly ONE independent AES dependency chain per
section, so the machine can only overlap sections to the extent its ASIMD issue
queues hold several sections' AES micro-ops.  Measurement says that is ~3
chains, i.e. ~9.4 cyc per 14-round block against a 6.5 cyc slot floor.  This
generator raises the software-interleave width to 2 while keeping fall-through,
at the cost of duplicating the odd-length prefixes.

Program order:

  .L256_dec_casc2_small:  common prep (15 hoisted round keys, ctr base, Xi')
                          3-deep dispatch on x9 -> stub_n
  stub_8 .. stub_1        acc <- Xi' * H^n, then branch to
                            ss<n>  if n even,  t<n>  if n odd
  ss8:  H^8,H^7 round-major interleaved  <- entry for nblk = 8
  ss6:  H^6,H^5                          <- entry for nblk = 6
  ss4:  H^4,H^3                          <- entry for nblk = 4
  ss2:  H^2,H^1 + MODULO/tag/counter     <- entry for nblk = 2
  done: shared epilogue
  t7:   H^7               ; b ss6        <- entry for nblk = 7
  t5:   H^5               ; b ss4        <- entry for nblk = 5
  t3:   H^3               ; b ss2        <- entry for nblk = 3
  t1:   H^1 + MODULO/tag/counter + own epilogue   <- entry for nblk = 1

12 blocks of AES code (vs 8 for the pure cascade, 36 for the eight-body
version) and exactly the same per-nblk issue-slot count as the pure cascade.

Registers (all 32 used; frame unchanged at 80 bytes):
  rk0..rk14  v2..v15, v20        AES states v0, v1
  ciphertext v21, v22            GHASH block v23   mid v24
  products   v25,v26,v27 (also the MODULO temps and the counter-store temp)
  H^p l|h    v28                 H^p k (ldr d)  v29
  counter    v30                 +1  v31
  v16 partial tag Xi' then the MODULO constant   acc v17 hi / v18 mid / v19 lo
"""
import sys

HL = {8: 176, 7: 144, 6: 128, 5: 96, 4: 80, 3: 48, 2: 32, 1: 0}
KD = {8: 168, 7: 160, 6: 120, 5: 112, 4: 72, 3: 64, 2: 24, 1: 16}

RK = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20]
STV = (0, 1)
CTV = (21, 22)
BLK, MID = 23, 24
P = (25, 26, 27)
HREG, KREG = 28, 29
CTR, INC = 30, 31
TAG = 16
AHI, AMID, ALO = 17, 18, 19

KEYHOIST = [
    "\tldp\tq2, q3, [x11, #0]\t\t\t//rk0, rk1",
    "\tldp\tq4, q5, [x11, #32]\t\t\t//rk2, rk3",
    "\tldp\tq6, q7, [x11, #64]\t\t\t//rk4, rk5",
    "\tldp\tq8, q9, [x11, #96]\t\t\t//rk6, rk7",
    "\tldp\tq10, q11, [x11, #128]\t\t\t//rk8, rk9",
    "\tldp\tq12, q13, [x11, #160]\t\t\t//rk10, rk11",
    "\tldp\tq14, q15, [x11, #192]\t\t\t//rk12, rk13",
    "\tldr\tq20, [x11, #224]\t\t\t//rk14",
]


def E(d, n, m, a, cmt=""):
    w = 0xce000000 | (m << 16) | (a << 10) | (n << 5) | d
    return ".inst\t0x%08x\t//eor3 v%d.16b, v%d.16b, v%d.16b, v%d.16b\t%s" % (w, d, n, m, a, cmt)


def common():
    L = ["",
         ".L256_dec_casc2_small:\t//[CASC2] nblk <= 8: width-2 fall-through cascade",
         "\tld1\t{ v27.16b}, [x16]\t\t\t\t//CTR block 0 (raw)",
         "\tld1\t{ v19.16b}, [x3]\t\t\t\t//load Xi",
         "\tmov\tx15, #0x100000000\t\t\t//counter increment",
         "\tmovi\tv31.16b, #0x0"]
    L += KEYHOIST
    L += ["\text\tv19.16b, v19.16b, v19.16b, #8",
          "\trev64\tv19.16b, v19.16b",
          "\tmov\tv31.d[1], x15\t\t\t\t//+1",
          "\text\tv16.16b, v19.16b, v19.16b, #8\t\t//partial-tag feed Xi'",
          "\trev32\tv30.16b, v27.16b\t\t\t//reversed counter base"]
    return L


def tgt(n):
    return ".L256_dec_casc2_ss%d" % n if n % 2 == 0 else ".L256_dec_casc2_t%d" % n


def dispatch():
    return [
        "\tcmp\tx9, #64",
        "\tb.gt\t.L256_dec_casc2_hi",
        "\tcmp\tx9, #32",
        "\tb.gt\t.L256_dec_casc2_34",
        "\tcmp\tx9, #16",
        "\tb.eq\t.L256_dec_casc2_stub_1",
        "\tb\t.L256_dec_casc2_stub_2",
        ".L256_dec_casc2_34:",
        "\tcmp\tx9, #48",
        "\tb.eq\t.L256_dec_casc2_stub_3",
        "\tb\t.L256_dec_casc2_stub_4",
        ".L256_dec_casc2_hi:",
        "\tcmp\tx9, #96",
        "\tb.gt\t.L256_dec_casc2_78",
        "\tcmp\tx9, #80",
        "\tb.eq\t.L256_dec_casc2_stub_5",
        "\tb\t.L256_dec_casc2_stub_6",
        ".L256_dec_casc2_78:",
        "\tcmp\tx9, #112",
        "\tb.eq\t.L256_dec_casc2_stub_7",
        "\tb\t.L256_dec_casc2_stub_8",
    ]


def stub(n, zap=False):
    L = ["",
         ".L256_dec_casc2_stub_%d:\t//[CASC2] entry for nblk=%d: seed acc = Xi' * H^%d"
         % (n, n, n),
         "\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HREG, HL[n], n, n),
         "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KREG, KD[n], n),
         "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//Xi' mid" % (MID, TAG, TAG),
         "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//Xi' mid" % (MID, MID, TAG)]
    if zap:
        L.append("\t//[ZAP] stub %d products replaced by ZERO (wrong on purpose)" % n)
        L += ["\tmovi\tv%d.16b, #0" % AHI, "\tmovi\tv%d.16b, #0" % ALO,
              "\tmovi\tv%d.16b, #0" % AMID]
    else:
        L += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//Xi' high" % (AHI, TAG, HREG),
              "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//Xi' low" % (ALO, TAG, HREG),
              "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//Xi' mid" % (AMID, MID, KREG)]
    L.append("\tb\t%s" % tgt(n))
    return L


def aes_units(nb):
    """round-major over nb blocks: 14 rounds x nb states."""
    units = []
    for r in range(14):
        for b in range(nb):
            s = STV[b]
            ln = ["\taese\tv%d.16b, v%d.16b" % (s, RK[r])]
            if r < 13:
                ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//blk %d - round %d" % (s, s, b, r))
            else:
                ln[0] += "\t\t\t\t//blk %d - round 13" % b
            units.append(ln)
    return units


def ghash_blk(b, p, zap=False):
    ct = CTV[b]
    hi, lo, md = P
    L = ["\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HREG, HL[p], p, p),
         "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KREG, KD[p], p),
         "\trev64\tv%d.16b, v%d.16b\t\t\t\t//GHASH H^%d block" % (BLK, ct, p),
         "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//H^%d mid" % (MID, BLK, BLK, p),
         "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//H^%d mid" % (MID, MID, BLK, p)]
    if zap:
        L.append("\t//[ZAP] H^%d products replaced by ZERO (wrong on purpose)" % p)
        L += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
              "\tmovi\tv%d.16b, #0" % md]
    else:
        L += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//H^%d high" % (hi, BLK, HREG, p),
              "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d low" % (lo, BLK, HREG, p),
              "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d mid" % (md, MID, KREG, p)]
    L += ["\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold high" % (AHI, AHI, hi),
          "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold low" % (ALO, ALO, lo),
          "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold mid" % (AMID, AMID, md)]
    return L


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
    for u, ln in enumerate(units):
        out += ln
        out += gap.get(u, [])
    return out


def epilogue(label):
    return ["",
            "%s:\t//[CASC2] epilogue" % label,
            "\tmov\tx0, x9",
            "\tldp\td10, d11, [sp, #16]",
            "\tldp\td12, d13, [sp, #32]",
            "\tldp\td14, d15, [sp, #48]",
            "\tldp\td8, d9, [sp], #80",
            "\tret"]


def super_section(j, ksec, k1, zapsec=0):
    """Two blocks, powers j and j-1, round-major interleaved."""
    last = (j == 2)
    units = aes_units(2)
    U = len(units)
    early = ghash_blk(0, j, zap=(zapsec == j)) + ghash_blk(1, j - 1, zap=(zapsec == j - 1))
    late = late_ops() if last else []
    K = max(1, min(U - 1 if last else U, int(round((k1 if last else ksec) * U))))
    out = ["",
           ".L256_dec_casc2_ss%d:\t//[CASC2] super-section H^%d,H^%d  (entry for nblk=%d)"
           % (j, j, j - 1, j),
           "\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block a" % (STV[0], CTR),
           "\tadd\tv%d.4s, v%d.4s, v%d.4s" % (CTR, CTR, INC),
           "\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block b" % (STV[1], CTR),
           "\tadd\tv%d.4s, v%d.4s, v%d.4s" % (CTR, CTR, INC),
           "\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext a" % CTV[0],
           "\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext b" % CTV[1]]
    out += place(units, early, late, K)
    out += [E(STV[0], CTV[0], STV[0], RK[14], "//H^%d block - result" % j),
            E(STV[1], CTV[1], STV[1], RK[14], "//H^%d block - result" % (j - 1)),
            "\tstp\tq%d, q%d, [x2], #32" % (STV[0], STV[1])]
    return out


def prefix_section(j, ksec, k1, zapsec=0):
    """One block, power j (odd j).  j>1: branch into ss(j-1).  j==1: finish."""
    last = (j == 1)
    units = aes_units(1)
    U = len(units)
    early = ghash_blk(0, j, zap=(zapsec == j))
    late = late_ops() if last else []
    K = max(1, min(U - 1 if last else U, int(round((k1 if last else ksec) * U))))
    out = ["",
           ".L256_dec_casc2_t%d:\t//[CASC2] odd prefix block H^%d  (entry for nblk=%d)"
           % (j, j, j),
           "\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block" % (STV[0], CTR),
           "\tadd\tv%d.4s, v%d.4s, v%d.4s" % (CTR, CTR, INC),
           "\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext" % CTV[0]]
    out += place(units, early, late, K)
    out += [E(STV[0], CTV[0], STV[0], RK[14], "//H^%d block - result" % j),
            "\tstr\tq%d, [x2], #16" % STV[0]]
    if last:
        out += epilogue(".L256_dec_casc2_done1")
    else:
        out.append("\tb\t.L256_dec_casc2_ss%d" % (j - 1))
    return out


ENTRY_ANCHOR = "\tadd\tx10, sp, #64"
RET_ANCHOR = ".L256_dec_ret:"


def apply(text, ksec, k1, zap=0, zapsec=0):
    lines = text.split("\n")
    i = lines.index(ENTRY_ANCHOR)
    lines[i:i + 1] = [ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #128\t\t\t\t//[CASC2] nblk <= 8 ?",
                      "\tb.le\t.L256_dec_casc2_small"]
    region = common() + dispatch()
    for n in range(8, 0, -1):
        region += stub(n, zap=(zap == n))
    for j in (8, 6, 4, 2):
        region += super_section(j, ksec, k1, zapsec)
    region += epilogue(".L256_dec_casc2_done")
    for j in (7, 5, 3, 1):
        region += prefix_section(j, ksec, k1, zapsec)
    region.append("")
    j = lines.index(RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst = sys.argv[1], sys.argv[2]
    ksec, k1 = float(sys.argv[3]), float(sys.argv[4])
    zap = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    zapsec = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    open(dst, "w").write(apply(open(src).read(), ksec, k1, zap, zapsec))
    print("wrote %s ksec=%s k1=%s zap=%d zapsec=%d" % (dst, ksec, k1, zap, zapsec))
