#!/usr/bin/env python3
"""Generate a generalised FUSED SMALL-MESSAGE path for aesv8_gcm_8x_dec_256_wb.S.

Today nblk<=8 is handled by prologue(AES for 8 blocks, always) -> 8-way tail
cascade (GHASH only).  AES and GHASH never overlap, and for nblk<8 the prologue
computes 8-nblk keystream blocks that the cascade throws away.

This generator emits, at the end of the file, a new region

    .L256_dec_fused_small        (3-deep compare tree on x9 = byte_len)
      .L256_dec_fused_1 ... .L256_dec_fused_8

entered by `cmp x9,#128 / b.le .L256_dec_fused_small` inserted right after
`add x10, sp, #64`.  Each body is a straight-line AES+GHASH *interleaved*
schedule for exactly n blocks.  Nothing else in the kernel changes, so the
nblk>8 path is byte-identical in content (addresses shift by 8).

Variants
  fuse   : n_aes == n_gh == n            -- the real design (fusion + no dead AES)
  fuse8  : n_aes == 8, n_gh == n         -- fusion only; keeps the prologue's
                                            dead AES for nblk<8 (diagnostic)
  zapN   : `fuse`, but body N's block-0 GHASH products are replaced by zero
           (functionally wrong on purpose: must fail EXACTLY nblk==N)

Register partition inside a fused body (identical for every n):
  AES     : v0..v(n_aes-1) states, v26/v27/v28 round keys, v30 counter
  GHASH   : v8,v9,v10 (blk/ct/mid), v11-v15+v20 (products), v16 (tag feed then
            MODULO constant), v17/v18/v19 (hi/mid/lo accumulators),
            v24 (H^p l|h), v25 (H^p k, loaded as a 64-bit `ldr d`)
  CTR set : v29 (reversed base, dead before AES round 0), v31 (+1),
            v20..v25 + v17 (increment temps, all dead before AES round 0)
  spare   : v21,v22,v23 (during GHASH) + v(n_aes)..v7 + v29 + v31
"""
import sys, re

# Htable offsets.  H^p full {hPl|hPh} 16 bytes, and the 64-bit "k" value.
# Derived from the baseline cascade / exact-8 drain (verified against
# .L256_dec_blocks_more_than_7 .. .L256_dec_blocks_less_than_1).
HL = {8: 176, 7: 144, 6: 128, 5: 96, 4: 80, 3: 48, 2: 32, 1: 0}
KD = {8: 168, 7: 160, 6: 120, 5: 112, 4: 72, 3: 64, 2: 24, 1: 16}

# round r (0..13) -> round-key register
RKREG = [26, 27, 28, 26, 27, 28, 26, 27, 28, 26, 27, 28, 26, 27]
# key loads, emitted immediately before round r
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

INC = {1: 31, 2: 20, 3: 21, 4: 22, 5: 23, 6: 24, 7: 25, 8: 17}


def eor3(d, n, m, a):
    return 0xce000000 | (m << 16) | (a << 10) | (n << 5) | d


def E(d, n, m, a, cmt=""):
    return ".inst\t0x%08x\t//eor3 v%d.16b, v%d.16b, v%d.16b, v%d.16b\t%s" % (
        eor3(d, n, m, a), d, n, m, a, cmt)


def ctr_setup(n_aes, n_gh):
    """CTR block preparation.  All temps die before AES round 0."""
    L = ["\tld1\t{ v0.16b}, [x16]\t\t\t\t//CTR block 0",
         "\tmov\tx15, #0x100000000\t\t\t//counter increment",
         "\tmovi\tv31.16b, #0x0",
         "\tmov\tv31.d[1], x15\t\t\t\t//+1",
         "\trev32\tv29.16b, v0.16b\t\t\t\t//reversed counter base"]
    m = max(n_aes - 1, n_gh)
    # increments +2..+m
    tree = {2: (31, 31), 3: (2, 31), 4: (2, 2), 5: (4, 31), 6: (4, 2), 7: (4, 3), 8: (4, 4)}
    for k in range(2, m + 1):
        a, b = tree[k]
        ra = INC[a] if a != 31 else 31
        rb = INC[b] if b != 31 else 31
        L.append("\tadd\tv%d.4s, v%d.4s, v%d.4s\t\t\t//+%d increment" % (INC[k], ra, rb, k))
    # CTR blocks 1..n_aes-1
    for i in range(1, n_aes):
        L.append("\tadd\tv%d.4s, v29.4s, v%d.4s\t\t\t//CTR block %d" % (8 + i - 1, INC[i], i))
    for i in range(1, n_aes):
        L.append("\trev32\tv%d.16b, v%d.16b\t\t\t\t//CTR block %d" % (i, 8 + i - 1, i))
    # final counter = base + n_gh (blocks actually consumed)
    L.append("\tadd\tv30.4s, v29.4s, v%d.4s\t\t\t//final counter = base + %d" % (INC[n_gh], n_gh))
    return L


def ghash_ops(n_gh, zap=False):
    """ops_early: tag prep + n_gh GHASH blocks + accumulator folds."""
    L = ["\tld1\t{ v19.16b}, [x3]\t\t\t\t//load Xi",
         "\text\tv19.16b, v19.16b, v19.16b, #8",
         "\trev64\tv19.16b, v19.16b",
         "\text\tv16.16b, v19.16b, v19.16b, #8\t\t//partial-tag feed"]
    SLOT = [(11, 12, 13), (14, 15, 20)]
    pend = []          # (hi,lo,mid) products awaiting a fold
    for i in range(n_gh):
        p = n_gh - i
        if i == 0:
            hi, lo, mid = 17, 19, 18            # straight into the accumulators
        else:
            hi, lo, mid = SLOT[(i - 1) % 2]
        L.append("\tldr\tq9, [x0, #%d]\t\t\t\t//GHASH blk%d ciphertext" % (16 * i, i))
        L.append("\tldr\tq24, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HL[p], p, p))
        L.append("\tldr\td25, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KD[p], p))
        L.append("\trev64\tv8.16b, v9.16b\t\t\t\t//GHASH blk%d (H^%d)" % (i, p))
        if i == 0:
            L.append("\teor\tv8.16b, v8.16b, v16.16b\t\t\t//feed in tag")
        L.append("\text\tv10.16b, v8.16b, v8.16b, #8\t\t//blk%d mid" % i)
        L.append("\teor\tv10.8b, v10.8b, v8.8b\t\t\t//blk%d mid" % i)
        if zap and i == 0:
            L.append("\t//[ZAP] block-0 GHASH products replaced by ZERO (wrong on purpose)")
            L.append("\tmovi\tv%d.16b, #0" % hi)
            L.append("\tmovi\tv%d.16b, #0" % lo)
            L.append("\tmovi\tv%d.16b, #0" % mid)
        else:
            L.append("\tpmull2\tv%d.1q, v8.2d, v24.2d\t\t\t//blk%d high" % (hi, i))
            L.append("\tpmull\tv%d.1q, v8.1d, v24.1d\t\t\t//blk%d low" % (lo, i))
            L.append("\tpmull\tv%d.1q, v10.1d, v25.1d\t\t\t//blk%d mid" % (mid, i))
        if i >= 1:
            pend.append((hi, lo, mid))
            if len(pend) == 2 or i == n_gh - 1:
                if len(pend) == 2:
                    (h1, l1, m1), (h2, l2, m2) = pend
                    L.append(E(17, 17, h1, h2, "//fold high"))
                    L.append(E(19, 19, l1, l2, "//fold low"))
                    L.append(E(18, 18, m1, m2, "//fold mid"))
                else:
                    (h1, l1, m1), = pend
                    L.append("\teor\tv17.16b, v17.16b, v%d.16b\t\t\t//fold high" % h1)
                    L.append("\teor\tv19.16b, v19.16b, v%d.16b\t\t\t//fold low" % l1)
                    L.append("\teor\tv18.16b, v18.16b, v%d.16b\t\t\t//fold mid" % m1)
                pend = []
    return L


def late_ops(n_gh):
    """ops_late: MODULO reduce + tag store + counter store + ciphertext reload."""
    L = ["\tldr\td16, [x10]\t\t\t\t//MODULO - load modulo constant",
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
         "\trev32\tv30.16b, v30.16b",
         "\tstr\tq30, [x16]\t\t\t\t//store the updated counter"]
    # ciphertext reload (L1-hot: the GHASH just touched these lines)
    i = 0
    while i < n_gh:
        if i + 1 < n_gh:
            L.append("\tldp\tq%d, q%d, [x0], #32\t\t\t//reload ct %d,%d" % (8 + i, 9 + i, i, i + 1))
            i += 2
        else:
            L.append("\tldr\tq%d, [x0], #16\t\t\t\t//reload ct %d" % (8 + i, i))
            i += 1
    return L


def final_ops(n_gh):
    L = []
    for i in range(n_gh):
        L.append(E(i, 8 + i, i, 28, "//AES block %d - result" % i))
    i = 0
    while i < n_gh:
        if i + 1 < n_gh:
            L.append("\tstp\tq%d, q%d, [x2], #32" % (i, i + 1))
            i += 2
        else:
            L.append("\tstr\tq%d, [x2], #16" % i)
            i += 1
    L += ["\tmov\tx0, x9",
          "\tldp\td10, d11, [sp, #16]",
          "\tldp\td12, d13, [sp, #32]",
          "\tldp\td14, d15, [sp, #48]",
          "\tldp\td8, d9, [sp], #80",
          "\tret"]
    return L


def body(n, n_aes, kfrac, zap=False):
    """One fused straight-line body for exactly n whole blocks."""
    units = []                        # (prefix_lines, unit_lines)
    for r in range(14):
        for b in range(n_aes):
            pre = [KEYLOAD[r]] if (b == 0 and r in KEYLOAD) else []
            ln = ["\taese\tv%d.16b, v%d.16b" % (b, RKREG[r])]
            if r < 13:
                ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//AES block %d - round %d" % (b, b, b, r))
            else:
                ln[0] += "\t\t\t\t//AES block %d - round 13" % b
            units.append((pre, ln))
    U = len(units)
    early = ghash_ops(n, zap)
    late = late_ops(n)
    K = max(1, min(U - 1, int(round(kfrac * U))))
    gap = {}
    for j, op in enumerate(early):
        gap.setdefault(j * K // len(early), []).append(op)
    for j, op in enumerate(late):
        gap.setdefault(K + j * (U - K) // len(late), []).append(op)

    out = ["", ".L256_dec_fused_%d:\t//[FUSE] fused straight-line path, exactly %d block%s"
           % (n, n, "" if n == 1 else "s"),
           "\t//[FUSE] AES(%d blk) and GHASH(%d blk) interleaved; GHASH front-loaded into"
           % (n_aes, n),
           "\t//[FUSE] AES units 0..%d of %d, MODULO + ct reload over units %d..%d."
           % (K - 1, U, K, U - 1)]
    out += ctr_setup(n_aes, n)
    for u, (pre, ln) in enumerate(units):
        out += pre
        out += ln
        out += gap.get(u, [])
    out += final_ops(n)
    return out


def dispatch():
    return ["",
            ".L256_dec_fused_small:\t//[FUSE] nblk <= 8: dispatch on byte_len (x9)",
            "\tcmp\tx9, #64",
            "\tb.gt\t.L256_dec_fs_hi",
            "\tcmp\tx9, #32",
            "\tb.gt\t.L256_dec_fs_34",
            "\tcmp\tx9, #16",
            "\tb.eq\t.L256_dec_fused_1",
            "\tb\t.L256_dec_fused_2",
            ".L256_dec_fs_34:",
            "\tcmp\tx9, #48",
            "\tb.eq\t.L256_dec_fused_3",
            "\tb\t.L256_dec_fused_4",
            ".L256_dec_fs_hi:",
            "\tcmp\tx9, #96",
            "\tb.gt\t.L256_dec_fs_78",
            "\tcmp\tx9, #80",
            "\tb.eq\t.L256_dec_fused_5",
            "\tb\t.L256_dec_fused_6",
            ".L256_dec_fs_78:",
            "\tcmp\tx9, #112",
            "\tb.eq\t.L256_dec_fused_7",
            "\tb\t.L256_dec_fused_8"]


ENTRY_ANCHOR = "\tadd\tx10, sp, #64"
RET_ANCHOR = ".L256_dec_ret:"


def apply(text, kfracs, dead_aes=False, zap=0):
    lines = text.split("\n")
    i = lines.index(ENTRY_ANCHOR)
    lines[i:i + 1] = [ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #128\t\t\t\t//[FUSE] nblk <= 8 ?",
                      "\tb.le\t.L256_dec_fused_small"]
    region = dispatch()
    for n in range(1, 9):
        region += body(n, 8 if dead_aes else n, kfracs[n], zap=(zap == n))
    region.append("")
    j = lines.index(RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst = sys.argv[1], sys.argv[2]
    mode = sys.argv[3]                      # fuse | fuse8
    karg = sys.argv[4]                      # single float, or 8 comma-separated
    zap = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    if "," in karg:
        vals = [float(x) for x in karg.split(",")]
        assert len(vals) == 8
        kfracs = {n: vals[n - 1] for n in range(1, 9)}
    else:
        kfracs = {n: float(karg) for n in range(1, 9)}
    t = open(src).read()
    open(dst, "w").write(apply(t, kfracs, dead_aes=(mode == "fuse8"), zap=zap))
    print("wrote", dst, "mode=", mode, "k=", karg, "zap=", zap)
