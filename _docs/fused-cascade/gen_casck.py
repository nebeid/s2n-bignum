#!/usr/bin/env python3
"""Shared fall-through fused CASCADE with the AES round keys HOISTED.

Same structure as gen_casc.py, but all fifteen AES-256 round keys are loaded
once, before the dispatch, into v2..v15 + v20, so a cascade section issues only
three loads (ciphertext, H^j, H^j k) instead of three plus seven `ldp` round-key
reloads.  gen_casc.py's naive version reloads the whole key schedule in every
one of the eight sections (56 `ldp` = 896 B of L1 traffic for nblk=8), which on
its own costs ~4.8 ns at nblk=8 on Neoverse-V2.

Register map (31 of 32 SIMD registers; frame unchanged at 80 bytes):
  rk0..rk14  v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v20
  AES state  v0 (even-numbered section), v1 (odd-numbered section)
  ciphertext v21   GHASH block v22   mid v23   products v24,v25,v26
  H^j l|h    v27   H^j k (64-bit ldr d) v28
  accumulators v17 hi, v18 mid, v19 lo (v19 also holds Xi during prep)
  v16 partial tag Xi' (stub) then the MODULO constant
  v29 running counter (reversed form)   v31 = +1   v30 scratch / counter store
  MODULO temps reuse v24,v25 (dead products by then)

Modes:  casck              the design
        --zap N            stub N's Xi'*H^N products zeroed -> fails EXACTLY nblk==N
        --zapsec J         section J's own products zeroed  -> fails EXACTLY nblk>=J
"""
import sys

HL = {8: 176, 7: 144, 6: 128, 5: 96, 4: 80, 3: 48, 2: 32, 1: 0}
KD = {8: 168, 7: 160, 6: 120, 5: 112, 4: 72, 3: 64, 2: 24, 1: 16}

RK = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20]   # rk0..rk14
CT, BLK, MID = 21, 22, 23
P = (24, 25, 26)
HREG, KREG = 27, 28
AHI, AMID, ALO = 17, 18, 19
TAG, CTR, INC, SPARE = 16, 29, 31, 30

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


def eor3w(d, n, m, a):
    return 0xce000000 | (m << 16) | (a << 10) | (n << 5) | d


def E(d, n, m, a, cmt=""):
    return ".inst\t0x%08x\t//eor3 v%d.16b, v%d.16b, v%d.16b, v%d.16b\t%s" % (
        eor3w(d, n, m, a), d, n, m, a, cmt)


def st(j):
    return 0 if j % 2 == 0 else 1


def common():
    L = ["",
         ".L256_dec_casck_small:\t//[CASC] nblk <= 8: shared fall-through cascade",
         "\t//[CASC] common prep: hoisted round keys, reversed counter base, partial tag.",
         "\tld1\t{ v30.16b}, [x16]\t\t\t\t//CTR block 0 (raw)",
         "\tld1\t{ v19.16b}, [x3]\t\t\t\t//load Xi",
         "\tmov\tx15, #0x100000000\t\t\t//counter increment",
         "\tmovi\tv31.16b, #0x0"]
    L += KEYHOIST
    L += ["\text\tv19.16b, v19.16b, v19.16b, #8",
          "\trev64\tv19.16b, v19.16b",
          "\tmov\tv31.d[1], x15\t\t\t\t//+1",
          "\text\tv16.16b, v19.16b, v19.16b, #8\t\t//partial-tag feed Xi'",
          "\trev32\tv29.16b, v30.16b\t\t\t//reversed counter base"]
    return L


def dispatch():
    return [
        "\tcmp\tx9, #64",
        "\tb.gt\t.L256_dec_casck_hi",
        "\tcmp\tx9, #32",
        "\tb.gt\t.L256_dec_casck_34",
        "\tcmp\tx9, #16",
        "\tb.eq\t.L256_dec_casck_stub_1",
        "\tb\t.L256_dec_casck_stub_2",
        ".L256_dec_casck_34:",
        "\tcmp\tx9, #48",
        "\tb.eq\t.L256_dec_casck_stub_3",
        "\tb\t.L256_dec_casck_stub_4",
        ".L256_dec_casck_hi:",
        "\tcmp\tx9, #96",
        "\tb.gt\t.L256_dec_casck_78",
        "\tcmp\tx9, #80",
        "\tb.eq\t.L256_dec_casck_stub_5",
        "\tb\t.L256_dec_casck_stub_6",
        ".L256_dec_casck_78:",
        "\tcmp\tx9, #112",
        "\tb.eq\t.L256_dec_casck_stub_7",
        "\tb\t.L256_dec_casck_stub_8",
    ]


def stub(n, zap=False):
    L = ["",
         ".L256_dec_casck_stub_%d:\t//[CASC] entry for nblk=%d: seed acc = Xi' * H^%d"
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
    L.append("\tb\t.L256_dec_casck_%d" % n)
    return L


def aes_units(j):
    s = st(j)
    units = []
    for r in range(14):
        ln = ["\taese\tv%d.16b, v%d.16b" % (s, RK[r])]
        if r < 13:
            ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//H^%d block - round %d" % (s, s, j, r))
        else:
            ln[0] += "\t\t\t\t//H^%d block - round 13" % j
        units.append(ln)
    return units


def ghash_sec(j, zap=False):
    hi, lo, md = P
    L = ["\trev64\tv%d.16b, v%d.16b\t\t\t\t//GHASH H^%d block" % (BLK, CT, j),
         "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//H^%d mid" % (MID, BLK, BLK, j),
         "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//H^%d mid" % (MID, MID, BLK, j)]
    if zap:
        L.append("\t//[ZAP] section H^%d products replaced by ZERO (wrong on purpose)" % j)
        L += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
              "\tmovi\tv%d.16b, #0" % md]
    else:
        L += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//H^%d high" % (hi, BLK, HREG, j),
              "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d low" % (lo, BLK, HREG, j),
              "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d mid" % (md, MID, KREG, j)]
    L += ["\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold high" % (AHI, AHI, hi),
          "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold low" % (ALO, ALO, lo),
          "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold mid" % (AMID, AMID, md)]
    return L


def late_ops():
    t1, t2 = P[0], P[1]
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
            "\trev32\tv%d.16b, v%d.16b\t\t\t//counter after the last block" % (SPARE, CTR),
            "\tstr\tq%d, [x16]\t\t\t\t//store the updated counter" % SPARE]


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


def section(j, ksec, k1, zap=False):
    s = st(j)
    last = (j == 1)
    units = aes_units(j)
    U = len(units)
    early = ghash_sec(j, zap)
    late = late_ops() if last else []
    K = max(1, min(U - 1 if last else U, int(round((k1 if last else ksec) * U))))
    out = ["",
           ".L256_dec_casck_%d:\t//[CASC] cascade section: block using H^%d  (entry for nblk=%d)"
           % (j, j, j),
           "\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block for this section" % (s, CTR),
           "\tadd\tv%d.4s, v%d.4s, v%d.4s\t\t\t//advance counter" % (CTR, CTR, INC),
           "\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext" % CT,
           "\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HREG, HL[j], j, j),
           "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KREG, KD[j], j)]
    out += place(units, early, late, K)
    out += [E(s, CT, s, RK[14], "//H^%d block - result" % j),
            "\tstr\tq%d, [x2], #16" % s]
    return out


def epilogue():
    return ["",
            ".L256_dec_casck_done:\t//[CASC] shared epilogue",
            "\tmov\tx0, x9",
            "\tldp\td10, d11, [sp, #16]",
            "\tldp\td12, d13, [sp, #32]",
            "\tldp\td14, d15, [sp, #48]",
            "\tldp\td8, d9, [sp], #80",
            "\tret",
            ""]


ENTRY_ANCHOR = "\tadd\tx10, sp, #64"
RET_ANCHOR = ".L256_dec_ret:"


def apply(text, ksec, k1, zap=0, zapsec=0):
    lines = text.split("\n")
    i = lines.index(ENTRY_ANCHOR)
    lines[i:i + 1] = [ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #128\t\t\t\t//[CASC] nblk <= 8 ?",
                      "\tb.le\t.L256_dec_casck_small"]
    region = common() + dispatch()
    for n in range(8, 0, -1):
        region += stub(n, zap=(zap == n))
    for j in range(8, 0, -1):
        region += section(j, ksec, k1, zap=(zapsec == j))
    region += epilogue()
    j = lines.index(RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst = sys.argv[1], sys.argv[2]
    ksec, k1 = float(sys.argv[3]), float(sys.argv[4])
    zap = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    zapsec = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    t = open(src).read()
    open(dst, "w").write(apply(t, ksec, k1, zap, zapsec))
    print("wrote %s ksec=%s k1=%s zap=%d zapsec=%d" % (dst, ksec, k1, zap, zapsec))
