#!/usr/bin/env python3
"""g4 -- ONE shared region, ONE entry point, for every nblk <= 4.

    .L256_dec_g4_grp:   4 blocks, INTERLEAVED over rounds (4-wide), 14 rounds
                        shared GHASH accumulate + MODULO + tag + counter +
                        stores + epilogue

Any nblk in {1,2,3,4} enters at the single label and the group runs FOUR blocks
of AES.  For nblk < 4 the 4-nblk surplus keystream blocks are *discarded*; the
GHASH/store half is made exactly-nblk correct BRANCH-FREE, so the region really
is one straight-line path with one entry.  nblk in {5,6,7} and nblk > 8 never
leave the baseline path (`g4p8` additionally sends nblk == 8 to a dedicated
8-wide body, gen.py's body 8, unchanged).

HOW nblk < 4 IS MADE CORRECT WITHOUT BRANCHES
---------------------------------------------
Let d = 4 - nblk be the number of discarded lanes.  The REAL blocks are put in
the HIGH lanes: lane j carries message block j - d.  Then

  * lane j always uses H^(4-j), a FIXED Htable offset, because the first real
    lane j = d uses H^(4-d) = H^nblk and the last, lane 3, uses H^1 -- exactly
    the powers exactly-nblk GHASH needs, with no pointer arithmetic;
  * lane j's ciphertext/plaintext byte offset is 16*max(0, j-d)
    = max(0, 16*nblk - 16*(4-j)), which is `subs`+`csel` per lane: DISCARDED
    LANES READ AND WRITE BLOCK 0, never out of bounds, so there is no overread
    of `in` and no overwrite of `out` beyond 16*nblk;
  * the stores are emitted in ASCENDING lane order, so every discarded lane
    writes garbage to out[0..16) *before* lane d writes the real block 0 over
    it.  All four ciphertext loads happen before any store, so in-place
    (out == in) decryption is safe too;
  * a discarded lane's GHASH input is ANDed to zero (mask Z_j = -1 iff
    nblk >= 4-j), and 0 * H^p = 0 contributes nothing to the accumulator;
  * the partial tag Xi' is XORed into lane d only, via F_j = -1 iff
    nblk == 4-j.  Both masks come from ONE `subs` per lane (`pl` gives Z, `eq`
    gives F) and are materialised with `dup vS.2d, xN`;
  * the counter base is shifted to base' = base + (nblk - 4) so lane j carries
    base' + j = base + (j - d); after four `add v29,v29,v31` the register holds
    base' + 4 = base + nblk, which is precisely the counter the epilogue stores.
    (All counter arithmetic is mod 2^32 inside 4s lane 3, as in the baseline.)

So the discarded blocks cost exactly 3 blocks' worth of AES issue slots plus
the predication (2..5 extra SIMD ops per lane) and NOTHING else is observable:
out, Xi and ivec are byte-identical to the reference at every length.

DERIVATION -- nothing is hand-written
-------------------------------------
This generator IMPORTS and reuses
  * fused-cascade/gen_cascW.py : HL/KD Htable offsets, RKREG/KEYLOAD, aes_units
                                 (the 4-wide interleave), ghash_blk's body,
                                 late_ops (MODULO + tag + counter store),
                                 place() (the GHASH/AES interleaver) and
                                 epilogue() -- verbatim where the register map
                                 allows, otherwise re-emitted through the same
                                 helpers with the mask ops spliced in;
  * fused-small-path/gen.py    : body() for the a4 control and for g4p8's body 8
                                 (n_aes != n_gh is gen.py's own `fuse8` idea);
  * fused-truncation/gen_trunc.py : tree() for the a4 control's dispatch;
  * fused-t4p8/gen_set.py      : the design-A ("small test first") dispatch.

Variants
  g4     one region, keys ROTATE through v26/v27/v28 (gen_cascW's map)
  g4h    one region, all 15 round keys HOISTED into v1..v15
  g4p8   g4 plus gen.py's dedicated 8-wide body 8 (nblk == 8 fused as well)
  a4     the CONTROL that isolates the cost of the discarded AES: FOUR separate
         gen.py bodies for nblk = 1..4, each with n_aes = 4 (always four blocks
         of AES) and n_gh = nblk (exact GHASH, no predication at all)
  probes zlaneJ / zapall (GHASH products of lane J / of every lane zeroed) and
         brk (a `brk #0` at the region's single entry)

Usage
  gen_g4.py <src.S> <dst.S> g4|g4h|g4p8   <k1> [zlaneJ|zapall|brk]
  gen_g4.py <src.S> <dst.S> a4            <k1,..,k8> [naes] [zapN|all]
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/tmp/fsp")
import gen                                      # fused-small-path/gen.py
import gen_trunc                                # fused-truncation/gen_trunc.py
import gen_set                                  # fused-t4p8/gen_set.py
import gen_cascW as cw                          # fused-cascade/gen_cascW.py

HL, KD, E = cw.HL, cw.KD, cw.E
BLK, MID, P = cw.BLK, cw.MID, cw.P              # 20, 21, (22,23,30)
HREG, KREG = cw.HREG, cw.KREG                   # 24, 25
AHI, AMID, ALO = cw.AHI, cw.AMID, cw.ALO        # 17, 18, 19
TAG, CTR, INCR = cw.TAG, cw.CTR, cw.INC         # 16, 29, 31

W = 4                                           # the one group width

# ---------------------------------------------------------------- register maps
# rotate: gen_cascW's map exactly -- states v0..v3, ciphertext v8..v11,
#         round keys rotating through v26/v27/v28, v12 spare as the mask scratch
# hoist : round keys v1..v15, states v0/v26/v27/v28, ciphertext transient in
#         v30 (which is also P[2]) and reloaded into v1..v4 (dead keys) for the
#         plaintext eor3; v30 doubles as the mask scratch.  Zero spare registers.
# The two mask strategies (same instruction COUNT, hence the same .text and the
# same slot count -- they differ only in WHERE the ops sit):
#   inline : materialise each lane's masks with `dup` inside that lane's GHASH.
#            The only strategy the hoisted map can use, because hoisting the 15
#            round keys leaves ZERO spare SIMD registers.
#   pre    : precompute all six mask values in the prep, in the six registers
#            the rotating-key map leaves spare (v4,v5,v6,v7,v12,v13), so no
#            GPR->SIMD `dup` sits on a GHASH dependency chain.
ROT = dict(state=[0, 1, 2, 3], ct=[8, 9, 10, 11], scratch=12, rk14=28,
           ptdst=[0, 1, 2, 3], hoist=False,
           mpre={"Z0": 4, "Z1": 5, "Z2": 6, "X1": 7, "X2": 12, "X3": 13})
HST = dict(state=[0, 26, 27, 28], ct=[None] * 4, scratch=30, rk14=15,
           ptdst=[1, 2, 3, 4], hoist=True, mpre=None)

# per-lane predicate/offset GPRs.  x1,x4,x5,x7,x8,x12..x15,x17 are all dead at
# `add x10,sp,#64` (x1 = bit_len consumed by lsr, x4 copied to x16, x5 a
# baseline scratch used only further down the fall-through path, x7/x8 unused by
# the kernel, x15 the counter-increment scratch, reused after v31 is built).
OFF = {0: "x12", 1: "x13", 2: "x14", 3: "x4"}
ZM = {0: "x5", 1: "x7", 2: "x15"}               # lane 3 is real for every nblk
FM = {0: "x5", 1: "x8", 2: "x17", 3: "x1"}      # lane 0: F0 == Z0


def L(pfx, s):
    return ".L256_dec_%s_%s" % (pfx, s)


def addr(base, j, diag):
    """lane j's ciphertext/plaintext address: the CLAMPED register offset, or a
    plain immediate for the `plain` diagnostic (correct at nblk == 4 only)."""
    return "%s, #%d" % (base, 16 * j) if diag == "plain" else "%s, %s" % (base, OFF[j])


# ---------------------------------------------------------------------- prep
def prep(rm, pfx, pre=False, diag="none"):
    """Counter base', per-lane clamped offsets + predicates, ciphertext loads."""
    out = ["", "%s:\t//[G4] nblk <= 4: ONE 4-wide group, ALWAYS 4 blocks of AES"
           % L(pfx, "grp"),
           "\t//[G4] real blocks live in the HIGH lanes: lane j = block j-(4-nblk),",
           "\t//[G4] so lane j always uses H^(4-j).  Discarded lanes read/write",
           "\t//[G4] block 0 (never out of bounds) and are ANDed out of the GHASH."]
    # gen_cascW.common(): Xi' in v16, counter base in v29, +1 in v31
    out += cw.common(pfx)[2:]                   # drop its label lines
    # ---- counter base' = base + (nblk - 4), in 4s lane 3 (mod 2^32)
    if diag == "plain":
        out.append("\t//[DIAG] base' shift and the clamped offsets OMITTED"
                   " (correct at nblk == 4 only)")
    out += [] if diag == "plain" else ["\tsub\tx8, x9, #64\t\t\t\t//[G4] 16*(nblk-4) <= 0",
            "\tlsl\tx7, x8, #28\t\t\t\t//[G4] (nblk-4) << 32",
            "\tmovi\tv30.16b, #0x0",
            "\tmov\tv30.d[1], x7",
            "\tadd\tv%d.4s, v%d.4s, v30.4s\t\t\t//[G4] counter base' = base + nblk - 4"
            % (CTR, CTR)]
    # ---- per-lane clamped byte offset + the two predicates, from ONE subs
    for j in ([] if diag == "plain" else (0, 1, 2)):
        imm = 16 * (4 - j)
        out += ["\tsubs\t%s, x9, #%d\t\t\t\t//[G4] lane %d offset = 16*(nblk-%d)"
                % (OFF[j], imm, j, 4 - j),
                "\tcsel\t%s, %s, xzr, pl\t\t\t//[G4] clamp at block 0" % (OFF[j], OFF[j]),
                "\tcsetm\t%s, pl\t\t\t\t//[G4] lane %d real?  nblk >= %d"
                % (ZM[j], j, 4 - j)]
        if j:                                   # lane 0: F0 == Z0, no second mask
            out.append("\tcsetm\t%s, eq\t\t\t\t//[G4] lane %d first real?  nblk == %d"
                       % (FM[j], j, 4 - j))
    if diag != "plain":
        out += ["\tsub\t%s, x9, #16\t\t\t\t//[G4] lane 3 offset (always >= 0)" % OFF[3],
                "\tcmp\tx9, #16",
                "\tcsetm\t%s, eq\t\t\t\t//[G4] lane 3 first real?  nblk == 1" % FM[3]]
    if rm["hoist"]:
        out += ["\tldp\tq1, q2, [x11, #0]\t\t\t//[G4] hoist rk0, rk1",
                "\tldp\tq3, q4, [x11, #32]\t\t\t//rk2, rk3",
                "\tldp\tq5, q6, [x11, #64]\t\t\t//rk4, rk5",
                "\tldp\tq7, q8, [x11, #96]\t\t\t//rk6, rk7",
                "\tldp\tq9, q10, [x11, #128]\t\t\t//rk8, rk9",
                "\tldp\tq11, q12, [x11, #160]\t\t\t//rk10, rk11",
                "\tldp\tq13, q14, [x11, #192]\t\t\t//rk12, rk13",
                "\tldr\tq15, [x11, #224]\t\t\t//rk14"]
    else:
        for j in range(W):
            out.append("\tldr\tq%d, [%s]\t\t\t//[G4] ciphertext lane %d"
                       % (rm["ct"][j], addr("x0", j, diag), j))
    if pre and diag == "none":
        M = rm["mpre"]
        for j in (0, 1, 2):
            out.append("\tdup\tv%d.2d, %s\t\t\t\t//[G4] Z%d mask, precomputed"
                       % (M["Z%d" % j], ZM[j], j))
        for j in (1, 2, 3):
            out += ["\tdup\tv%d.2d, %s\t\t\t\t//[G4] F%d mask" % (M["X%d" % j], FM[j], j),
                    "\tand\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] Xi' & F%d, precomputed"
                    % (M["X%d" % j], M["X%d" % j], TAG, j)]
    # ---- the four counter blocks, from base'
    for j in range(W):
        out.append("\trev32\tv%d.16b, v%d.16b\t\t\t//[G4] CTR lane %d"
                   % (rm["state"][j], CTR, j))
        out.append("\tadd\tv%d.4s, v%d.4s, v%d.4s" % (CTR, CTR, INCR))
    return out


# ------------------------------------------------------------------ AES units
def aes_units(rm):
    if not rm["hoist"]:
        return cw.aes_units(W)                  # gen_cascW's, verbatim
    units = []
    for r in range(14):
        for b in range(W):
            v = rm["state"][b]
            ln = ["\taese\tv%d.16b, v%d.16b" % (v, r + 1)]
            if r < 13:
                ln.append("\taesmc\tv%d.16b, v%d.16b\t\t\t//blk %d - round %d" % (v, v, b, r))
            else:
                ln[0] += "\t\t\t\t//blk %d - round 13" % b
            units.append(([], ln))
    return units


# ---------------------------------------------------------------- GHASH lanes
def ghash_lane(rm, j, zap=False, pre=False, diag="none"):
    """gen_cascW.ghash_blk's body for lane j (power 4-j) + the predication.

    Lane 0's products go straight into the accumulators (gen.py's i == 0 idiom),
    so no accumulator initialisation is needed; lanes 1..3 fold with three eors.
    """
    p = W - j
    S = rm["scratch"]
    hi, lo, md = (AHI, ALO, AMID) if j == 0 else P
    out = ["\tldr\tq%d, [x6, #%d]\t\t\t\t//h%dl | h%dh" % (HREG, HL[p], p, p),
           "\tldr\td%d, [x6, #%d]\t\t\t\t//h%dk (64-bit)" % (KREG, KD[p], p)]
    if rm["hoist"]:
        out.append("\tldr\tq%d, [%s]\t\t\t//[G4] ciphertext lane %d (transient)"
                   % (S, addr("x0", j, diag), j))
        src = S
    else:
        src = rm["ct"][j]
    out.append("\trev64\tv%d.16b, v%d.16b\t\t\t\t//GHASH lane %d (H^%d)" % (BLK, src, j, p))
    # ---- partial tag Xi' into the FIRST REAL lane only
    if diag != "none":
        if j == 0:
            out.append("\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[DIAG] tag feed, unmasked"
                       % (BLK, BLK, TAG))
    elif j == 0:
        out.append("\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] feed Xi' (masked below)"
                   % (BLK, BLK, TAG))
    elif pre:
        out.append("\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] feed Xi'&F%d (precomputed)"
                   % (BLK, BLK, rm["mpre"]["X%d" % j], j))
    else:
        out += ["\tdup\tv%d.2d, %s\t\t\t\t//[G4] F%d: nblk == %d ?" % (S, FM[j], j, p),
                "\tand\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] Xi' & F%d" % (S, S, TAG, j),
                "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] feed Xi' if lane %d is first"
                % (BLK, BLK, S, j)]
    # ---- zero the lane entirely when it is a DISCARDED block
    if j in ZM and diag == "none":
        if pre:
            out.append("\tand\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] discard lane %d if nblk < %d"
                       % (BLK, BLK, rm["mpre"]["Z%d" % j], j, p))
        else:
            out += ["\tdup\tv%d.2d, %s\t\t\t\t//[G4] Z%d: nblk >= %d ?" % (S, ZM[j], j, p),
                    "\tand\tv%d.16b, v%d.16b, v%d.16b\t\t\t//[G4] discard lane %d if nblk < %d"
                    % (BLK, BLK, S, j, p)]
    out += ["\text\tv%d.16b, v%d.16b, v%d.16b, #8\t\t//H^%d mid" % (MID, BLK, BLK, p),
            "\teor\tv%d.8b, v%d.8b, v%d.8b\t\t\t//H^%d mid" % (MID, MID, BLK, p)]
    if zap:
        out.append("\t//[ZAP] lane %d (H^%d) products replaced by ZERO (wrong on purpose)"
                   % (j, p))
        out += ["\tmovi\tv%d.16b, #0" % hi, "\tmovi\tv%d.16b, #0" % lo,
                "\tmovi\tv%d.16b, #0" % md]
    else:
        out += ["\tpmull2\tv%d.1q, v%d.2d, v%d.2d\t\t\t//H^%d high" % (hi, BLK, HREG, p),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d low" % (lo, BLK, HREG, p),
                "\tpmull\tv%d.1q, v%d.1d, v%d.1d\t\t\t//H^%d mid" % (md, MID, KREG, p)]
    if j:                                       # lane 0 wrote the accumulators
        out += ["\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold high" % (AHI, AHI, hi),
                "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold low" % (ALO, ALO, lo),
                "\teor\tv%d.16b, v%d.16b, v%d.16b\t\t\t//fold mid" % (AMID, AMID, md)]
    return out


# --------------------------------------------------------- plaintext + stores
def tail(rm, diag="none"):
    """Plaintext eor3 then the four CLAMPED stores, in ASCENDING lane order."""
    out = []
    if rm["hoist"]:                             # reload ct into the dead keys
        for j in range(W):
            out.append("\tldr\tq%d, [%s]\t\t\t//[G4] reload ciphertext lane %d"
                       % (rm["ptdst"][j], addr("x0", j, diag), j))
    for j in range(W):
        ct = rm["ptdst"][j] if rm["hoist"] else rm["ct"][j]
        out.append(E(rm["ptdst"][j], ct, rm["state"][j], rm["rk14"],
                     "//lane %d - plaintext" % j))
    out.append("\t//[G4] ASCENDING lane order: every discarded lane writes block 0")
    out.append("\t//[G4] BEFORE lane 4-nblk writes the real block 0 over it.")
    for j in range(W):
        out.append("\tstr\tq%d, [%s]\t\t\t//[G4] store lane %d"
                   % (rm["ptdst"][j], addr("x2", j, diag), j))
    return out


# --------------------------------------------------------------- the region
def region(pfx, mode, k1, zlane=None, zapall=False, brk=False, pre=False,
           diag="none"):
    rm = HST if mode == "hoist" else ROT
    assert not (pre and rm["mpre"] is None), "no spare registers to precompute masks in"
    units = aes_units(rm)
    U = len(units)
    early = []
    for j in range(W):
        early += ghash_lane(rm, j, zap=(zapall or zlane == j), pre=pre, diag=diag)
    late = cw.late_ops()
    K = max(1, min(U - 1, int(round(k1 * U))))
    out = prep(rm, pfx, pre=pre, diag=diag)
    if brk:
        out.insert(2, "\tbrk\t#0\t\t\t\t//[BRK] liveness probe: the group was entered")
    out += ["\t//[G4] GHASH(4 lanes) over AES units 0..%d of %d; MODULO + tag +"
            % (K - 1, U),
            "\t//[G4] counter store over units %d..%d." % (K, U - 1)]
    out += cw.place(units, early, late, K)
    out += tail(rm, diag=diag)
    out += cw.epilogue(L(pfx, "done"))
    return out


# ------------------------------------------------------------------- variants
def apply_g4(text, mode, k1, plus8=False, k8=0.70, zlane=None, zapall=False, brk=False,
             pre=False, pfx=None, diag="none"):
    pfx = pfx or ("g4h" if mode == "hoist" else "g4")
    lines = text.split("\n")
    i = lines.index(gen.ENTRY_ANCHOR)
    ent = ["\tcmp\tx9, #64\t\t\t\t//[G4] nblk <= 4 ?",
           "\tb.le\t%s" % L(pfx, "grp")]
    if plus8:                                   # gen_set.py design A, small first
        ent += ["\tcmp\tx9, #128\t\t\t\t//[G4] nblk == 8 ?",
                "\tb.eq\t.L256_dec_fused_8"]
    lines[i:i + 1] = [gen.ENTRY_ANCHOR, ""] + ent
    reg = region(pfx, mode, k1, zlane=zlane, zapall=zapall, brk=brk, pre=pre,
                 diag=diag)
    if plus8:
        reg += gen.body(8, 8, k8)               # gen.py's body 8, unchanged
    reg.append("")
    j = lines.index(gen.RET_ANCHOR)
    lines[j:j] = reg
    return "\n".join(lines)


def apply_a4(text, kfracs, C=4, n_aes=4, zap=0, zapall=False):
    """gen_trunc.apply's structure with gen.body(n, n_aes, ...): separate bodies
    for nblk = 1..C, each doing n_aes blocks of AES and exactly nblk of GHASH.
    n_aes = 4 isolates the cost of the DISCARDED AES with no predication."""
    lines = text.split("\n")
    i = lines.index(gen.ENTRY_ANCHOR)
    lines[i:i + 1] = [gen.ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #%d\t\t\t\t//[A4] nblk <= %d ?" % (16 * C, C),
                      "\tb.le\t.L256_dec_fused_small"]
    region = ["", ".L256_dec_fused_small:\t//[A4] nblk <= %d: dispatch on byte_len (x9)" % C]
    region += gen_trunc.tree(list(range(1, C + 1)), [0])
    for n in range(1, C + 1):
        region += gen.body(n, max(n, n_aes), kfracs[n], zap=(zapall or zap == n))
    region.append("")
    j = lines.index(gen.RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, mode, karg = sys.argv[1:5]
    t = open(src).read()
    if mode == "a4":
        vals = [float(x) for x in karg.split(",")]
        assert len(vals) == 8
        kf = {n: vals[n - 1] for n in range(1, 9)}
        naes = int(sys.argv[5]) if len(sys.argv) > 5 else 4
        z = sys.argv[6] if len(sys.argv) > 6 else "0"
        open(dst, "w").write(apply_a4(t, kf, 4, naes,
                                      zap=(0 if z == "all" else int(z)),
                                      zapall=(z == "all")))
        print("wrote %s a4 n_aes=%d k=%s zap=%s" % (dst, naes, karg, z))
    else:
        # g4   : rotating keys, masks PREcomputed  (the primary build)
        # g4i  : rotating keys, masks INLINE       (matched to g4h's strategy)
        # g4h  : hoisted keys, masks inline (no spare registers to precompute in)
        # g4p8 : g4 + gen.py's body 8
        assert mode in ("g4", "g4i", "g4h", "g4p8", "g4nm", "g4nn")
        z = sys.argv[5] if len(sys.argv) > 5 else "0"
        kw = dict(zlane=None, zapall=False, brk=False)
        if z.startswith("zlane"):
            kw["zlane"] = int(z[5:])
        elif z == "zapall":
            kw["zapall"] = True
        elif z == "brk":
            kw["brk"] = True
        open(dst, "w").write(apply_g4(t, "hoist" if mode == "g4h" else "rotate",
                                      float(karg), plus8=(mode == "g4p8"),
                                      pre=(mode in ("g4", "g4p8", "g4nm", "g4nn")),
                                      diag={"g4nm": "nomask", "g4nn": "plain"}.get(mode, "none"),
                                      pfx=({"g4i": "g4i", "g4nm": "g4nm",
                                            "g4nn": "g4nn"}.get(mode)), **kw))
        print("wrote %s %s k1=%s probe=%s" % (dst, mode, karg, z))
