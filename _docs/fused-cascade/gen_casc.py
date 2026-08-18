#!/usr/bin/env python3
"""Generate a SHARED FALL-THROUGH FUSED CASCADE small-message path for
aesv8_gcm_8x_dec_256_wb.S.

Contrast with _docs/fused-small-path/gen.py (the "eight-body" version), which
emits eight *independent* straight-line bodies, each with its own copy of the
14-round AES sequence software-interleaved across its n blocks.  Here there is
ONE instruction stream with eight entry labels; each section performs exactly
one block and falls through to the next:

    .L256_dec_casc_small:      common CTR/Xi prep + 3-deep dispatch tree on x9
    .L256_dec_casc_stub_8..1:  per-entry seed  acc <- Xi' * H^n   (3 pmull)
    .L256_dec_casc_8:  block using H^8  ---+ enter here for nblk = 8
    .L256_dec_casc_7:  block using H^7     | enter here for nblk = 7
      ...                                  |
    .L256_dec_casc_1:  block using H^1,  --+ enter here for nblk = 1
                       + MODULO reduce + tag store + counter store
                       (interleaved into this section's AES units)
    <shared epilogue: mov x0,x9 / frame pop / ret>

Entering at .L256_dec_casc_j runs sections j, j-1, ..., 1 = exactly j blocks,
so there is NO dead AES, and the 14-round AES sequence appears once per
section (8 copies total = the same 112 aese the baseline prologue already has)
rather than once per length (8 bodies = 448 aese in the eight-body version).

Why this is well-formed even though `n` is not known to a section:
  * section .L256_dec_casc_j handles GHASH power H^j, a compile-time constant;
  * that section handles block index i = n - j, which is NOT constant -- so the
    ciphertext load and the plaintext store use post-increment addressing
    (`ldr q,[x0],#16` / `str q,[x2],#16`), which makes them n-independent
    because the sections execute with i = 0,1,...,n-1 in program order;
  * likewise the CTR block for a section is base + i, so the counter register
    v29 is advanced by +1 at the top of every section (a serial add chain --
    unavoidable in a cascade, 2 cyc/link);
  * the incoming tag must be multiplied by H^n, which IS entry-dependent, so it
    is handled once in the per-entry stub: acc_{hi,lo,mid} <- products of
    Xi'*H^n, and every section then folds its own products into acc with 3 eor.

Register partition (nothing spills; frame stays 80 bytes):
    v0..v7    AES state of sections .L_1 .. .L_8   (section j uses v(j-1))
    setA (even j): ct v9 , blk v8 , mid v10, products v11,v12,v13
    setB (odd  j): ct v23, blk v21, mid v22, products v14,v15,v20
    v16       partial tag Xi' (stub only), then the MODULO constant
    v17/v18/v19  GHASH accumulators hi/mid/lo  (v19 also holds Xi during prep)
    v24/v25   H^j {l|h} and H^j k (64-bit `ldr d`)
    v26/v27/v28  round keys (v28 = rk14 for the plaintext eor3)
    v29       running counter (reversed form), v31 = +1
    v30       free / counter-store temp

Modes
  casc    : the design above
  casc3   : same, but adjacent sections are paired and the second of each pair
            folds both blocks' products with 3 `eor3` instead of 2x3 `eor`
            (odd entry points zero setA in their stub)
  --zap N     : stub N's Xi*H^N products replaced by zero  -> must fail EXACTLY nblk==N
  --zapsec J  : section J's own products replaced by zero   -> must fail EXACTLY nblk>=J
"""
import sys

# Htable offsets: H^p full {hPl|hPh} (16 B) and the 64-bit Karatsuba "k" value.
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

SETA = dict(ct=9, blk=8, mid=10, p=(11, 12, 13))
SETB = dict(ct=23, blk=21, mid=22, p=(14, 15, 20))


def rs(j):
    return SETA if j % 2 == 0 else SETB


def eor3w(d, n, m, a):
    return 0xce000000 | (m << 16) | (a << 10) | (n << 5) | d


def E(d, n, m, a, cmt=""):
    return ".inst\t0x%08x\t//eor3 v%d.16b, v%d.16b, v%d.16b, v%d.16b\t%s" % (
        eor3w(d, n, m, a), d, n, m, a, cmt)


# ---------------------------------------------------------------- common prep
def common():
    return [
        "",
        ".L256_dec_casc_small:\t//[CASC] nblk <= 8: shared fall-through cascade",
        "\t//[CASC] common prep: reversed counter base, +1 increment, partial tag.",
        "\tld1\t{ v0.16b}, [x16]\t\t\t\t//CTR block 0 (raw)",
        "\tld1\t{ v19.16b}, [x3]\t\t\t\t//load Xi",
        "\tmov\tx15, #0x100000000\t\t\t//counter increment",
        "\tmovi\tv31.16b, #0x0",
        "\text\tv19.16b, v19.16b, v19.16b, #8",
        "\trev64\tv19.16b, v19.16b",
        "\tmov\tv31.d[1], x15\t\t\t\t//+1",
        "\text\tv16.16b, v19.16b, v19.16b, #8\t\t//partial-tag feed Xi'",
        "\trev32\tv29.16b, v0.16b\t\t\t\t//reversed counter base",
    ]


def dispatch():
    return [
        "\tcmp\tx9, #64",
        "\tb.gt\t.L256_dec_casc_hi",
        "\tcmp\tx9, #32",
        "\tb.gt\t.L256_dec_casc_34",
        "\tcmp\tx9, #16",
        "\tb.eq\t.L256_dec_casc_stub_1",
        "\tb\t.L256_dec_casc_stub_2",
        ".L256_dec_casc_34:",
        "\tcmp\tx9, #48",
        "\tb.eq\t.L256_dec_casc_stub_3",
        "\tb\t.L256_dec_casc_stub_4",
        ".L256_dec_casc_hi:",
        "\tcmp\tx9, #96",
        "\tb.gt\t.L256_dec_casc_78",
        "\tcmp\tx9, #80",
        "\tb.eq\t.L256_dec_casc_stub_5",
        "\tb\t.L256_dec_casc_stub_6",
        ".L256_dec_casc_78:",
        "\tcmp\tx9, #112",
        "\tb.eq\t.L256_dec_casc_stub_7",
        "\tb\t.L256_dec_casc_stub_8",
    ]


def stub(n, pair, zap=False):
    """acc <- Xi' * H^n, straight into the three accumulators."""
    L = ["",
         ".L256_dec_casc_stub_%d:\t//[CASC] entry for nblk=%d: seed acc = Xi' * H^%d"
         % (n, n, n),
         "\tldr\tq24, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HL[n], n, n),
         "\tldr\td25, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KD[n], n),
         "\text\tv10.16b, v16.16b, v16.16b, #8\t\t//Xi' mid",
         "\teor\tv10.8b, v10.8b, v16.8b\t\t\t//Xi' mid"]
    if zap:
        L.append("\t//[ZAP] stub %d products replaced by ZERO (wrong on purpose)" % n)
        L += ["\tmovi\tv17.16b, #0", "\tmovi\tv19.16b, #0", "\tmovi\tv18.16b, #0"]
    else:
        L += ["\tpmull2\tv17.1q, v16.2d, v24.2d\t\t\t//Xi' high",
              "\tpmull\tv19.1q, v16.1d, v24.1d\t\t\t//Xi' low",
              "\tpmull\tv18.1q, v10.1d, v25.1d\t\t\t//Xi' mid"]
    if pair and (n % 2 == 1):
        # this entry starts mid-pair: the first-of-pair product registers are
        # not written on this path, so zero them.
        hi, lo, md = SETA["p"]
        L.append("\t//[CASC] odd entry: zero the unrun first-of-pair products")
        L += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
              "\tmovi\tv%d.16b, #0" % md]
    L.append("\tb\t.L256_dec_casc_%d" % n)
    return L


# ------------------------------------------------------------------ a section
def aes_units(j):
    s = j - 1
    units = []
    for r in range(14):
        pre = [KEYLOAD[r]] if r in KEYLOAD else []
        ln = ["\taese\tv%d.16b, v%d.16b" % (s, RKREG[r])]
        if r < 13:
            ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//H^%d block - round %d" % (s, s, j, r))
        else:
            ln[0] += "\t\t\t\t//H^%d block - round 13" % j
        units.append((pre, ln))
    return units


def ghash_sec(j, mode, zap=False):
    """This section's GHASH: 3 products + fold into the accumulators.

    mode 'casc'  : always fold with 3 eor.
    mode 'casc3' : first-of-pair (even j) leaves products in setA and folds
                   nothing; second-of-pair (odd j) folds setA+setB with eor3.
    """
    R = rs(j)
    ct, blk, mid = R["ct"], R["blk"], R["mid"]
    hi, lo, md = R["p"]
    L = ["\trev64\tv%d.16b, v%d.16b\t\t\t\t//GHASH H^%d block" % (blk, ct, j),
         "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//H^%d mid" % (mid, blk, blk, j),
         "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//H^%d mid" % (mid, mid, blk, j)]
    if zap:
        L.append("\t//[ZAP] section H^%d products replaced by ZERO (wrong on purpose)" % j)
        L += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
              "\tmovi\tv%d.16b, #0" % md]
    else:
        L += ["\tpmull2\tv%d.1q, v%d.2d, v24.2d\t\t\t//H^%d high" % (hi, blk, j),
              "\tpmull\tv%d.1q, v%d.1d, v24.1d\t\t\t//H^%d low" % (lo, blk, j),
              "\tpmull\tv%d.1q, v%d.1d, v25.1d\t\t\t//H^%d mid" % (md, mid, j)]
    if mode == "casc3" and j % 2 == 0:
        return L                                    # first of pair: no fold yet
    if mode == "casc3":
        ah, al, am = SETA["p"]
        L += [E(17, 17, ah, hi, "//fold high"),
              E(19, 19, al, lo, "//fold low"),
              E(18, 18, am, md, "//fold mid")]
    else:
        L += ["\teor\tv17.16b, v17.16b, v%d.16b\t\t\t//fold high" % hi,
              "\teor\tv19.16b, v19.16b, v%d.16b\t\t\t//fold low" % lo,
              "\teor\tv18.16b, v18.16b, v%d.16b\t\t\t//fold mid" % md]
    return L


def late_ops():
    """MODULO reduce + tag store + counter store (interleaved into section 1)."""
    return ["\tldr\td16, [x10]\t\t\t\t//MODULO - load modulo constant",
            "\tpmull\tv21.1q, v17.1d, v16.1d\t\t\t//MODULO - top 64b align with mid",
            "\teor\tv20.16b, v17.16b, v19.16b\t\t//MODULO - karatsuba tidy up",
            "\text\tv17.16b, v17.16b, v17.16b, #8\t\t//MODULO - other top alignment",
            "\teor\tv18.16b, v18.16b, v20.16b\t\t//MODULO - karatsuba tidy up",
            "\teor\tv21.16b, v17.16b, v21.16b\t\t//MODULO - fold into mid",
            "\teor\tv18.16b, v18.16b, v21.16b\t\t//MODULO - fold into mid",
            "\tpmull\tv17.1q, v18.1d, v16.1d\t\t\t//MODULO - mid 64b align with low",
            "\text\tv18.16b, v18.16b, v18.16b, #8\t\t//MODULO - other mid alignment",
            "\teor\tv19.16b, v19.16b, v17.16b\t\t//MODULO - fold into low",
            "\teor\tv19.16b, v19.16b, v18.16b\t\t//MODULO - fold into low",
            "\text\tv19.16b, v19.16b, v19.16b, #8",
            "\trev64\tv19.16b, v19.16b",
            "\tst1\t{ v19.16b }, [x3]\t\t\t\t//store the tag",
            "\trev32\tv30.16b, v29.16b\t\t\t//counter after the last block",
            "\tstr\tq30, [x16]\t\t\t\t//store the updated counter"]


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


def section(j, mode, ksec, k1, zap=False):
    s = j - 1
    R = rs(j)
    ct = R["ct"]
    last = (j == 1)
    units = aes_units(j)
    U = len(units)
    early = ghash_sec(j, mode, zap)
    late = late_ops() if last else []
    if last:
        K = max(1, min(U - 1, int(round(k1 * U))))
    else:
        K = max(1, min(U, int(round(ksec * U))))
    out = ["",
           ".L256_dec_casc_%d:\t//[CASC] cascade section: block using H^%d%s"
           % (j, j, "  (fall-through target for nblk=%d)" % j),
           "\trev32\tv%d.16b, v29.16b\t\t\t//CTR block for this section" % s,
           "\tadd\tv29.4s, v29.4s, v31.4s\t\t\t//advance counter",
           "\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext" % ct,
           "\tldr\tq24, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HL[j], j, j),
           "\tldr\td25, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KD[j], j)]
    out += place(units, early, late, K)
    out += [E(s, ct, s, 28, "//H^%d block - result" % j),
            "\tstr\tq%d, [x2], #16" % s]
    return out


def epilogue():
    return ["",
            ".L256_dec_casc_done:\t//[CASC] shared epilogue",
            "\tmov\tx0, x9",
            "\tldp\td10, d11, [sp, #16]",
            "\tldp\td12, d13, [sp, #32]",
            "\tldp\td14, d15, [sp, #48]",
            "\tldp\td8, d9, [sp], #80",
            "\tret",
            ""]


ENTRY_ANCHOR = "\tadd\tx10, sp, #64"
RET_ANCHOR = ".L256_dec_ret:"


def apply(text, mode, ksec, k1, zap=0, zapsec=0):
    lines = text.split("\n")
    i = lines.index(ENTRY_ANCHOR)
    lines[i:i + 1] = [ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #128\t\t\t\t//[CASC] nblk <= 8 ?",
                      "\tb.le\t.L256_dec_casc_small"]
    pair = (mode == "casc3")
    region = common() + dispatch()
    for n in range(8, 0, -1):
        region += stub(n, pair, zap=(zap == n))
    for j in range(8, 0, -1):
        region += section(j, mode, ksec, k1, zap=(zapsec == j))
    region += epilogue()
    j = lines.index(RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, mode = sys.argv[1], sys.argv[2], sys.argv[3]
    ksec = float(sys.argv[4])
    k1 = float(sys.argv[5])
    zap = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    zapsec = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    t = open(src).read()
    open(dst, "w").write(apply(t, mode, ksec, k1, zap, zapsec))
    print("wrote %s mode=%s ksec=%s k1=%s zap=%d zapsec=%d" % (dst, mode, ksec, k1, zap, zapsec))
