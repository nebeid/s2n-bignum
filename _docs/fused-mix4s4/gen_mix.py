#!/usr/bin/env python3
"""mix4s4 -- MIXED-WIDTH fall-through fused small path for
aesv8_gcm_8x_dec_256_wb.S.

The shape asked for by the brief, generalised to an arbitrary list of GROUP
WIDTHS `G` (execution order, summing to N <= 8).  For G = [4,1,1,1,1]:

    .L..._mx_g8:  4 blocks (H^8,H^7,H^6,H^5) INTERLEAVED over rounds  <- nblk=8
    .L..._mx_g4:  block H^4, all 14 rounds                            <- nblk=4
    .L..._mx_g3:  block H^3, all 14 rounds                            <- nblk=3
    .L..._mx_g2:  block H^2, all 14 rounds                            <- nblk=2
    .L..._mx_g1:  block H^1, all 14 rounds + MODULO + tag + ctr store <- nblk=1
    .L..._mx_done: shared epilogue

Entry set  E = { sum(G[i:]) : i } = {8,4,3,2,1} for G = [4,1,1,1,1].  Every
other nblk (here 5,6,7 and everything > 8) falls through to the EXISTING
staggered prologue+cascade path, completely unchanged.  Exactly `14n` `aese` for
nblk = n at every entry: no dead AES.

This module is a composition of the three published generators, not a rewrite:

  * `fused-cascade/gen_cascW.py`  -- common prep, entry stubs, the body emitter
    (`gen_body`), `late_ops`, `place`, `epilogue`.  Used VERBATIM in the default
    ("rotate") key mode, so a group of width w is instruction-for-instruction
    the code the published width-w cascade ships.
  * `fused-truncation/gen_cascWt.py` -- the balanced compare `tree()` over the
    contiguous part of the entry set, and the truncated entry test.
  * `fused-t4p8/gen_set.py`       -- the DISCONTIGUOUS dispatch (design A,
    "small test first"), which is what lets {1,2,3,4} and 8 be fused while
    5,6,7 fall through.  Reproduced here for the cascade label scheme; the
    instruction sequence is gen_set.entry()'s.

KEY MODES.  A width-4 group needs 4 AES states + 4 ciphertext registers, so the
15 round keys cannot be hoisted the way the published W=1 cascade (`casck`)
hoists them, and gen_cascW rotates them through v26/v27/v28 -- 8 key-load
instructions per group, i.e. 40 for nblk = 8 with G = [4,1,1,1,1].  That is a
known ~1.9 cyc/block tax (published: rotating W=1 11.20 vs hoisted W=1 9.32
cyc/block on V2), and it is NOT part of the structure under test, so a second
key mode is provided:

  keys = "rotate"  (default)  gen_cascW verbatim; 8 key loads per group.
  keys = "hoist"              all 15 round keys live in v1..v15 for the WHOLE
                              region, loaded once (8 instructions) in the common
                              prep.  The 4-wide group then has only v0,v26,v27,
                              v28 left for AES states and no register to hold
                              ciphertext, so it loads each ciphertext block
                              transiently into v30 for the GHASH and RELOADS all
                              four (2 `ldp`, L1-hot) for the final eor3 -- the
                              same trick the eight-body generator uses in
                              `late_ops`.  Per-nblk SIMD slot counts are
                              IDENTICAL to "rotate" (verified by verify_mx.py),
                              so the two modes differ only in load traffic.

Register map, keys = "hoist" (all 32 SIMD registers, frame unchanged at 80 B):
  rk0..rk14      v1..v15                (v(i+1) = rk_i)
  AES states     v0,v26,v27,v28         (4-wide group);  v0 (1-wide sections)
  ciphertext     v30 transient + reload into v20..v23 (4-wide);  v26 (1-wide)
  GHASH blk/mid  v20 / v21              products v22,v23,v30
  H^p l|h / k    v24 / v25
  accumulators   v17 hi / v18 mid / v19 lo
  v16            Xi' (partial tag) then the MODULO constant
  counter v29    +1 v31

Usage:
  gen_mix.py <src.S> <dst.S> <widths> <ksec> <k1> [pfx] [rotate|hoist]
             [zapN|all] [zsecP]
  gen_mix.py base.S m4s4.S 4,1,1,1,1 1.0 0.35 mx rotate
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/tmp/fsp")
import gen_cascW as G                       # fused-cascade/gen_cascW.py
import gen_cascWt as GT                     # fused-truncation/gen_cascWt.py

tree = GT.tree                              # reused verbatim

# ---------------------------------------------------------------- hoisted mode
HK = [i + 1 for i in range(15)]             # rk_i -> v(i+1)
ST4 = [0, 26, 27, 28]                       # 4-wide group AES states
CT1 = 26                                    # 1-wide section holds ciphertext
CTT = 30                                    # transient ciphertext (wide groups)
RELOAD = [20, 21, 22, 23]                   # wide-group ciphertext reload regs

KEYHOIST = [
    "\tldp\tq1, q2, [x11, #0]\t\t\t//rk0, rk1",
    "\tldp\tq3, q4, [x11, #32]\t\t\t//rk2, rk3",
    "\tldp\tq5, q6, [x11, #64]\t\t\t//rk4, rk5",
    "\tldp\tq7, q8, [x11, #96]\t\t\t//rk6, rk7",
    "\tldp\tq9, q10, [x11, #128]\t\t\t//rk8, rk9",
    "\tldp\tq11, q12, [x11, #160]\t\t\t//rk10, rk11",
    "\tldp\tq13, q14, [x11, #192]\t\t\t//rk12, rk13",
    "\tldr\tq15, [x11, #224]\t\t\t//rk14",
]


def aes_units_h(states):
    """AES units with the round keys read from the hoisted registers."""
    units = []
    for r in range(14):
        for b, s in enumerate(states):
            ln = ["\taese\tv%d.16b, v%d.16b" % (s, HK[r])]
            if r < 13:
                ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//blk %d - round %d"
                          % (s, s, b, r))
            else:
                ln[0] += "\t\t\t\t//blk %d - round 13" % b
            units.append(([], ln))
    return units


def ghash_blk_h(b, p, ctreg, zap=False):
    """One GHASH block, ciphertext loaded here into `ctreg`."""
    hi, lo, md = G.P
    out = ["\tldr\tq%d, [x0], #16\t\t\t\t//ciphertext %d" % (ctreg, b),
           "\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (G.HREG, G.HL[p], p, p),
           "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (G.KREG, G.KD[p], p),
           "\trev64\tv%d.16b, v%d.16b\t\t\t\t//GHASH H^%d block" % (G.BLK, ctreg, p),
           "\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//H^%d mid" % (G.MID, G.BLK, G.BLK, p),
           "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//H^%d mid" % (G.MID, G.MID, G.BLK, p)]
    if zap:
        out.append("\t//[ZAP] H^%d products replaced by ZERO (wrong on purpose)" % p)
        out += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
                "\tmovi\tv%d.16b, #0" % md]
    else:
        out += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//H^%d high" % (hi, G.BLK, G.HREG, p),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d low" % (lo, G.BLK, G.HREG, p),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d mid" % (md, G.MID, G.KREG, p)]
    out += ["\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold high" % (G.AHI, G.AHI, hi),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold low" % (G.ALO, G.ALO, lo),
            "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold mid" % (G.AMID, G.AMID, md)]
    return out


def gen_body_h(label, powers, terminal, ksec, k1, zapsec=0):
    """Hoisted-key body covering len(powers) blocks, falling through at the end."""
    nb = len(powers)
    assert nb <= 4
    states = ST4[:nb] if nb > 1 else [ST4[0]]
    wide = nb > 1
    units = aes_units_h(states)
    U = len(units)
    early = []
    for b, p in enumerate(powers):
        early += ghash_blk_h(b, p, CTT if wide else CT1, zap=(zapsec == p))
    late = G.late_ops() if terminal else []
    K = max(1, min(U - 1 if terminal else U,
                   int(round((k1 if terminal else ksec) * U))))
    out = ["", "%s:\t//[MIX] %d block(s), H^%s  (hoisted round keys)"
           % (label, nb, ",H^".join(map(str, powers)))]
    for b, s in enumerate(states):
        out.append("\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block %d" % (s, G.CTR, b))
        out.append("\tadd\tv%d.4s, v%d.4s, v%d.4s" % (G.CTR, G.CTR, G.INC))
    out += G.place(units, early, late, K)
    if wide:
        # ciphertext reload: x0 has advanced by 16*nb; the lines are L1-hot
        b = 0
        while b < nb:
            if b + 1 < nb:
                out.append("\tldp\tq%d, q%d, [x0, #%d]\t\t\t//reload ct %d,%d"
                           % (RELOAD[b], RELOAD[b + 1], -16 * nb + 16 * b, b, b + 1))
                b += 2
            else:
                out.append("\tldr\tq%d, [x0, #%d]\t\t\t\t//reload ct %d"
                           % (RELOAD[b], -16 * nb + 16 * b, b))
                b += 1
    for b, s in enumerate(states):
        ct = RELOAD[b] if wide else CT1
        out.append(G.E(s, ct, s, HK[14], "//H^%d block - result" % powers[b]))
    b = 0
    while b < nb:
        if b + 1 < nb:
            out.append("\tstp\tq%d, q%d, [x2], #32" % (states[b], states[b + 1]))
            b += 2
        else:
            out.append("\tstr\tq%d, [x2], #16" % states[b])
            b += 1
    return out


# ------------------------------------------------------------------- assembly
def groups(W):
    """width list -> [(remaining_at_entry, [powers])], execution order."""
    rem = [sum(W[i:]) for i in range(len(W))]
    return [(rem[i], list(range(rem[i], rem[i] - W[i], -1))) for i in range(len(W))]


def split(entries):
    """entry set -> (m, extras): m = top of the contiguous run 1..m."""
    E = sorted(entries)
    assert E[0] == 1, "the entry set must contain nblk = 1 (got %s)" % E
    m = 1
    while m + 1 in E:
        m += 1
    return m, [k for k in E if k > m]


def gl(pfx, r):
    return "%s_g%d" % (G.L(pfx), r)


def stub(n, pfx, target, zap=False):
    """gen_cascW's entry stub with its trailing branch retargeted."""
    L = G.stub(1, n, pfx, zap=zap)
    assert L[-1].startswith("\tb\t"), L[-1]
    L[-1] = "\tb\t%s" % target
    return L


def apply(text, W, pfx, ksec, k1, keys="rotate", zap=0, zapall=False, zapsec=0):
    gs = groups(W)
    entries = [r for r, _ in gs]
    m, extras = split(entries)
    lines = text.split("\n")

    # ---- dispatch, gen_set.py design A: small test first, no taken branch on
    # the fall-through path.  Both tests route to the one common-prep label.
    ent = ["\tcmp\tx9, #%d\t\t\t\t//[MIX] nblk <= %d ?" % (16 * m, m),
           "\tb.le\t%s_small" % G.L(pfx)]
    for k in extras:
        ent += ["\tcmp\tx9, #%d\t\t\t\t//[MIX] nblk == %d ?" % (16 * k, k),
                "\tb.eq\t%s_small" % G.L(pfx)]
    i = lines.index(G.ENTRY_ANCHOR)
    lines[i:i + 1] = [G.ENTRY_ANCHOR, ""] + ent

    # ---- the appended region
    region = G.common(pfx)
    if keys == "hoist":
        region += KEYHOIST
    # the isolated entries are re-tested here (x9 is still live) so that the
    # common prep is emitted once; then the balanced tree over {1..m}.
    for k in sorted(extras, reverse=True):
        region += ["\tcmp\tx9, #%d\t\t\t\t//[MIX] nblk == %d" % (16 * k, k),
                   "\tb.eq\t%s_stub_%d" % (G.L(pfx), k)]
    region += tree(list(range(1, m + 1)), pfx, [0])
    for r, _ in gs:                                     # stubs, descending
        region += stub(r, pfx, gl(pfx, r), zap=(zapall or zap == r))
    for idx, (r, powers) in enumerate(gs):              # the fall-through chain
        terminal = (idx == len(gs) - 1)
        if keys == "hoist":
            region += gen_body_h(gl(pfx, r), powers, terminal, ksec, k1, zapsec)
        else:
            region += G.gen_body(gl(pfx, r), powers, terminal=terminal, cont=None,
                                 ksec=ksec, k1=k1, zapsec=zapsec)
    region += G.epilogue("%s_done" % G.L(pfx))
    region.append("")
    j = lines.index(G.RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, warg = sys.argv[1], sys.argv[2], sys.argv[3]
    ksec, k1 = float(sys.argv[4]), float(sys.argv[5])
    pfx = sys.argv[6] if len(sys.argv) > 6 else "mx"
    keys = sys.argv[7] if len(sys.argv) > 7 else "rotate"
    z = sys.argv[8] if len(sys.argv) > 8 else "0"
    zsec = int(sys.argv[9]) if len(sys.argv) > 9 else 0
    assert keys in ("rotate", "hoist")
    W = [int(x) for x in warg.split(",")]
    assert sum(W) <= 8 and all(1 <= w <= 8 for w in W)
    open(dst, "w").write(apply(open(src).read(), W, pfx, ksec, k1, keys,
                               zap=(0 if z == "all" else int(z)),
                               zapall=(z == "all"), zapsec=zsec))
    print("wrote %s widths=%s keys=%s ksec=%s k1=%s zap=%s zsec=%d"
          % (dst, warg, keys, ksec, k1, z, zsec))
