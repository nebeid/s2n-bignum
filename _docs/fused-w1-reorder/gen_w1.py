#!/usr/bin/env python3
"""W=1 FOUR-SECTION fused cascade with INSTRUCTION-ORDERING knobs.

The structure is FIXED and is exactly the published `s4h` variant of
`_docs/fused-mix4s4.md` (gen_mix.py widths 1,1,1,1, keys hoisted):

    .L..._w1_small:   common prep (CTR base, Xi', 15 round keys -> v1..v15)
                      dispatch over {1,2,3,4}
    .L..._w1_stub_r:  acc <- Xi' * H^r  (3 pmull), then b .L..._w1_g<r>
    .L..._w1_g4:      1 block, H^4, 14 AES rounds, GHASH product, eor3 + store
    .L..._w1_g3:      1 block, H^3, ditto                    <- fall through
    .L..._w1_g2:      1 block, H^2, ditto
    .L..._w1_g1:      1 block, H^1, ditto, + MODULO + tag + counter store
    .L..._w1_done:    shared epilogue

nblk in {5,6,7} and nblk > 8 never leave the baseline path.  Exactly 14n `aese`
for nblk = n.  Frame unchanged at 80 bytes.

WHAT THIS MODULE ADDS: nothing but ORDERING.  Every knob below is a permutation
of the same instruction multiset (or, where marked, a strictly smaller one), and
with all knobs at their defaults the emitted object is byte-identical to
gen_mix.py's `s4h` -- asserted by provision_w1.sh (md5 compare).

KNOBS
  ksec   float   GHASH-product span in the NON-terminal sections: the products
                 are spread over units [gs*U, ksec*U) of the 14 AES units.
  k1     float   the terminal section's split: products over [gs*U, k1*U), the
                 MODULO/tag/counter over [k1*U, U).
  gs     float   start of the product window (default 0.0).
  clump  int     0 = one product op per AES unit (default);  c>0 = bursts of c
                 product ops between AES pairs.
  ct     in|head where the ciphertext ldr sits: with the other product ops
                 (default) or as the very first instruction of the section,
                 before the counter rev32.
  ptr    post|end  addressing of ciphertext/plaintext.  `post` = the published
                 `ldr q26,[x0],#16` / `str q0,[x2],#16` post-index chain.
                 `end`  = two extra integer adds in the SHARED prep
                 (x14 = x0+x9, x13 = x2+x9) and then STATIC offsets
                 [x14,#-16r] / [x13,#-16r] -- legal because section r always
                 handles the block r-th from the END of the message, so the
                 offset is a compile-time constant.  Removes both address
                 chains and makes all four loads/stores independent.
  dsp    tree|f4|f4i
                 `tree` = the published balanced compare tree over {1,2,3,4};
                 nblk=4 costs 3 taken branches inside the region.
                 `f4`   = nblk=4 falls THROUGH the dispatch into stub_4 which
                 falls through into g4: 0 taken branches inside the region for
                 nblk=4, one extra for nblk<4.
                 `f4i`  = f4, and stub_4's seed ops are MERGED into g4's AES
                 rounds (legal: section 4 executes if and only if nblk = 4, so
                 the seed and the section are in 1:1 correspondence) and its two
                 duplicated H^4 table loads are dropped.
  lay    fall|br|rev
                 `fall` = the published descending fall-through.
                 `br`   = descending, but an explicit `b` to the immediately
                 following section label (isolates the taken-branch cost).
                 `rev`  = sections laid out ASCENDING in memory (g1 first) with
                 explicit backward branches -- same execution order, different
                 adjacency at the section boundaries.
  ctr    chain|free
                 `chain` = the published serial `add v29.4s,v29.4s,v31.4s` at
                 each section head.  `free` = DIAGNOSTIC ONLY, produces a WRONG
                 counter/plaintext: every section reads the same v29.  Bounds
                 from above the benefit of any counter scheme that removes the
                 chain (base+k, precomputation, ...).
  rejoin bool    ONE `ret` FOR nblk >= 1.  The fused region's `_done` block is
                 six instructions duplicated from `.L256_dec_epilogue`'s frame
                 restore plus a second `ret`, so for nblk = 1..4 the function
                 exits at an address the exported
                 `AESV8_GCM_8X_DEC_256_CORRECT` postcondition does not name.
                 With rejoin=1 a NEW LABEL `.L256_dec_frame_restore` is inserted
                 into the existing epilogue immediately before its `mov x0, x9`
                 -- after the last plaintext store `st1 {v12.16b},[x2]`, after
                 the tag store `st1 {v19.16b},[x3]` and after the counter store
                 `str q30,[x16]` (which is earlier still), so NO instruction
                 moves and nothing on the nblk>8 path changes -- and the fused
                 `_done` body becomes the single `b .L256_dec_frame_restore`.
                 The fused path performs its own MODULO, tag store and counter
                 store in its terminal section before branching, so no work is
                 repeated or skipped.  Net: 5 instructions smaller, one extra
                 taken branch after every store, ONE exit address for nblk >= 1.
                 The pre-existing `.L256_dec_ret` stub (`mov w0,#0` + `ret`, the
                 zero-length early exit) is deliberately NOT touched.
                 This is the pattern the file already uses at `b
                 .L256_dec_epilogue`.
  ctfree bool    DIAGNOSTIC ONLY, wrong plaintext for nblk>1: the ciphertext is
                 loaded once in the prep and no section loads it.  Bounds from
                 above the benefit of any load-slack scheme (prefetching a
                 ciphertext block one section early).

Usage:
  gen_w1.py <src.S> <dst.S> <pfx> k=<ksec> K=<k1> [gs=..] [clump=..] [ct=..]
            [ptr=..] [dsp=..] [lay=..] [ctr=..] [ctfree=1] [zap=N|all] [zsec=P]
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
for d in ("/tmp/fsw", "/tmp/fsp"):
    sys.path.insert(0, d)
import gen_cascW as G
import gen_cascWt as GT
import gen_mix as M

HK = M.HK              # rk_i -> v(i+1)
CT1 = M.CT1            # v26: the 1-wide section's ciphertext register
ST = 0                 # v0: the AES state

DEF = dict(ksec=1.0, k1=0.35, gs=0.0, clump=0, ct="in", ptr="post",
           dsp="tree", sub="tree", lay="fall", ctr="chain", ctfree=False,
           pre=False, ldh=False, fold="in", rejoin=False, brk=0)


# --------------------------------------------------------------- placement
def place2(units, early, late, K, S=0, clump=0):
    """gen_cascW.place, with a start offset for the early window and optional
    clumping.  S=0, clump=0 reproduces gen_cascW.place exactly."""
    U = len(units)
    gap = {}
    if early:
        n = len(early)
        if clump:
            ng = (n + clump - 1) // clump
            for i, op in enumerate(early):
                gap.setdefault(min(U - 1, S + (i // clump) * (K - S) // ng),
                               []).append(op)
        else:
            for i, op in enumerate(early):
                gap.setdefault(min(U - 1, S + i * (K - S) // n), []).append(op)
    if late:
        for i, op in enumerate(late):
            gap.setdefault(min(U - 1, K + i * (U - K) // len(late)), []).append(op)
    out = []
    for u, (pre, ln) in enumerate(units):
        out += pre
        out += ln
        out += gap.get(u, [])
    return out


# ------------------------------------------------------------------ pieces
def seed_ops(p, zap=False):
    """stub_p's body: the Xi' * H^p accumulator seed, without label or branch."""
    return G.stub(1, p, "seed", zap=zap)[2:-1]


def section(pfx, p, terminal, o, seed=False, zapsec=0, zapseed=False):
    """One section: the block that is p-th from the END of the message."""
    units = M.aes_units_h([ST])
    U = len(units)
    g = M.ghash_blk_h(0, p, CT1, zap=(zapsec == p))
    if o["ptr"] == "end":
        g[0] = ("\tldr\tq%d, [x14, #%d]\t\t\t//ciphertext (end-relative)"
                % (CT1, -16 * p))
    ctload, rest = g[0], g[1:]
    if o["ctfree"]:
        ctload = None                      # DIAGNOSTIC: loaded once in the prep
    head = []
    early = []
    sops = []
    if seed:
        sops = seed_ops(p, zap=zapseed)
        rest = rest[2:]                    # drop the duplicated H^p table loads
    if o["ldh"]:
        # every LOAD the section needs, at the very top: the ciphertext and the
        # two H^p table reads.  Loads take no SIMD issue slot, so this is free.
        if seed:
            head += sops[:2]; sops = sops[2:]
        else:
            head += rest[:2]; rest = rest[2:]
        if ctload is not None:
            head.insert(0, ctload)
    elif ctload is not None and o["ct"] == "in":
        rest = [ctload] + rest
    early += sops + rest
    folds = []
    if o["fold"] == "late" and not terminal:
        folds, early = early[-3:], early[:-3]   # the 3 accumulator eors last
    late = G.late_ops() if terminal else []
    kk = o["k1"] if terminal else o["ksec"]
    K = max(1, min(U - 1 if terminal else U, int(round(kk * U))))
    S = max(0, min(K - 1, int(round(o["gs"] * U))))
    out = ["", "%s:\t//[W1] 1 block, H^%d%s" % (secl(pfx, p), p,
                                                "  (seed merged)" if seed else "")]
    if o["brk"] == p:
        out.append("\tbrk\t#0\t\t\t\t\t//[PROBE] entered section %d" % p)
    if o["ldh"]:
        out += head
    elif ctload is not None and o["ct"] == "head":
        out.append(ctload)
    out.append("\trev32\tv%d.16b, v%d.16b\t\t\t//CTR block 0" % (ST, G.CTR))
    if o["ctr"] != "free":
        out.append("\tadd\tv%d.4s, v%d.4s, v%d.4s" % (G.CTR, G.CTR, G.INC))
    if o["pre"]:
        out += early                       # every product op before round 0
        out += place2(units, [], late, K, S, o["clump"])
    else:
        out += place2(units, early, late, K, S, o["clump"])
    out += folds
    out.append(G.E(ST, CT1, ST, HK[14], "//H^%d block - result" % p))
    if o["ptr"] == "end":
        out.append("\tstr\tq%d, [x13, #%d]" % (ST, -16 * p))
    else:
        out.append("\tstr\tq%d, [x2], #16" % ST)
    return out


def secl(pfx, r):
    return "%s_g%d" % (G.L(pfx), r)


def stub(pfx, n, target, zap=False):
    L = G.stub(1, n, pfx, zap=zap)
    assert L[-1].startswith("\tb\t"), L[-1]
    if target is None:
        L = L[:-1]                          # falls through into its section
    else:
        L[-1] = "\tb\t%s" % target
    return L


# ---------------------------------------------------------------- assembly
FR_ANCHOR = "\tmov\tx0, x9"          # unique in the kernel: epilogue line 1513
FR_LABEL = ".L256_dec_frame_restore"


def epilogue(label, o):
    """The fused region's exit.  Default: gen_cascW's own six-instruction copy
    of the frame restore.  rejoin=1: a single branch to the ONE frame restore."""
    if not o["rejoin"]:
        return G.epilogue(label)
    return ["",
            "%s:\t//[W1] rejoin the one epilogue: single `ret` for nblk >= 1"
            % label,
            "\tb\t%s" % FR_LABEL]


def apply(text, o, pfx, zap=0, zapall=False, zapsec=0):
    lines = text.split("\n")
    if o["rejoin"]:
        # LABEL ONLY -- no instruction is added, moved or removed here, so the
        # nblk > 8 instruction stream is untouched.  The insertion point is
        # after every store on the main path (the plaintext st1 to [x2], the tag
        # st1 to [x3] and, earlier, the counter str to [x16]).
        assert lines.count(FR_ANCHOR) == 1, \
            "frame-restore anchor %r is not unique" % FR_ANCHOR
        assert FR_LABEL not in text
        k = lines.index(FR_ANCHOR)
        tail = [l for l in lines[k:] if l.strip() and
                not l.strip().startswith("//")]
        assert not any(l.split("//")[0].strip().startswith(("st", "str"))
                       for l in tail[:6]), \
            "a store follows the frame-restore anchor: %r" % tail[:6]
        lines[k:k] = ["%s:\t//[W1] the ONE frame restore; the fused region "
                      "rejoins here" % FR_LABEL]
    ent = ["\tcmp\tx9, #64\t\t\t\t//[W1] nblk <= 4 ?",
           "\tb.le\t%s_small" % G.L(pfx)]
    i = lines.index(G.ENTRY_ANCHOR)
    lines[i:i + 1] = [G.ENTRY_ANCHOR, ""] + ent

    region = G.common(pfx) + M.KEYHOIST
    if o["ptr"] == "end":
        region += ["\tadd\tx14, x0, x9\t\t\t\t//[W1] one past the last ciphertext block",
                   "\tadd\tx13, x2, x9\t\t\t\t//[W1] one past the last plaintext block"]
    if o["ctfree"]:
        region += ["\tldr\tq%d, [x0]\t\t\t\t//[DIAG] the only ciphertext load" % CT1]

    order = [4, 3, 2, 1] if o["lay"] != "rev" else [1, 2, 3, 4]

    def sections():
        out = []
        for r in order:
            merged = (o["dsp"] == "f4i" and r == 4)
            out += section(pfx, r, terminal=(r == 1), o=o, seed=merged,
                           zapsec=zapsec, zapseed=(zapall or zap == 4))
            if o["lay"] == "rev":
                out.append("\tb\t%s" % (secl(pfx, r - 1) if r > 1
                                        else "%s_done" % G.L(pfx)))
            elif o["lay"] == "br":
                out.append("\tb\t%s" % (secl(pfx, r - 1) if r > 1
                                        else "%s_done" % G.L(pfx)))
        return out

    if o["dsp"] == "tree":
        region += GT.tree([1, 2, 3, 4], pfx, [0])
        for r in (4, 3, 2, 1):
            region += stub(pfx, r, secl(pfx, r), zap=(zapall or zap == r))
        region += sections()
        region += epilogue("%s_done" % G.L(pfx), o)
    else:
        # nblk == 4 falls THROUGH the dispatch and (for dsp=f4) through stub_4
        if o["sub"] == "eq":
            # a linear ascending eq-chain: nblk = 1,2,3 each cost ONE taken
            # branch here (plus their stub's `b`), nblk = 4 costs NONE and pays
            # only 6 not-taken instructions.  Strictly fewer taken branches than
            # the balanced tree at every entry.
            for r in (1, 2, 3):
                region += ["\tcmp\tx9, #%d\t\t\t\t//[W1] nblk == %d ?" % (16 * r, r),
                           "\tb.eq\t%s_stub_%d" % (G.L(pfx), r)]
        else:
            region += ["\tcmp\tx9, #64\t\t\t\t//[W1] nblk == 4 falls through",
                       "\tb.ne\t%s_d3" % G.L(pfx)]
        if o["dsp"] == "f4":
            region += stub(pfx, 4, None, zap=(zapall or zap == 4))
        elif o["lay"] == "rev":
            region += ["\tb\t%s" % secl(pfx, 4)]
        region += sections()
        region += epilogue("%s_done" % G.L(pfx), o)
        if o["sub"] != "eq":
            region += ["", "%s_d3:\t//[W1] nblk in {1,2,3}" % G.L(pfx)]
            region += GT.tree([1, 2, 3], pfx, [0])
        for r in (3, 2, 1):
            region += stub(pfx, r, secl(pfx, r), zap=(zapall or zap == r))
    region.append("")
    j = lines.index(G.RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, pfx = sys.argv[1], sys.argv[2], sys.argv[3]
    o = dict(DEF)
    zap, zapall, zsec = 0, False, 0
    for a in sys.argv[4:]:
        k, _, v = a.partition("=")
        if k == "k":
            o["ksec"] = float(v)
        elif k == "K":
            o["k1"] = float(v)
        elif k == "gs":
            o["gs"] = float(v)
        elif k == "clump":
            o["clump"] = int(v)
        elif k == "brk":
            o["brk"] = int(v)
        elif k == "ctfree":
            o["ctfree"] = bool(int(v))
        elif k == "pre":
            o["pre"] = bool(int(v))
        elif k == "ldh":
            o["ldh"] = bool(int(v))
        elif k == "rejoin":
            o["rejoin"] = bool(int(v))
        elif k == "zap":
            zapall = (v == "all")
            zap = 0 if zapall else int(v)
        elif k == "zsec":
            zsec = int(v)
        elif k in o:
            o[k] = v
        else:
            raise SystemExit("unknown knob %r" % a)
    assert o["ct"] in ("in", "head")
    assert o["fold"] in ("in", "late")
    assert o["ptr"] in ("post", "end")
    assert o["dsp"] in ("tree", "f4", "f4i")
    assert o["sub"] in ("tree", "eq")
    assert o["lay"] in ("fall", "br", "rev")
    assert o["ctr"] in ("chain", "free")
    assert not (o["lay"] == "rev" and o["dsp"] != "tree"), \
        "lay=rev needs an out-of-line stub for every entry, i.e. dsp=tree"
    open(dst, "w").write(apply(open(src).read(), o, pfx, zap, zapall, zsec))
    print("wrote %s pfx=%s %s zap=%s%s zsec=%d"
          % (dst, pfx, " ".join("%s=%s" % kv for kv in sorted(o.items())),
             "all" if zapall else zap, "", zsec))
