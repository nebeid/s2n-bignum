#!/usr/bin/env python3
"""BODY-SET fused small path: keep fused bodies for an ARBITRARY, possibly
DISCONTIGUOUS set of block counts.  `t4p8` is the set {1,2,3,4,8}.

Strict generalisation of `_docs/fused-truncation/gen_trunc.py`: this module
IMPORTS that file and reuses its `tree()` (the balanced compare tree) and, via
it, `fused-small-path/gen.py`'s `body()` generator verbatim.  Nothing is copied.
So a retained body for a given n is instruction-for-instruction the same code
every other member of the family ships.

Dispatch.  A contiguous set {1..m} needs one test.  A set {1..m} u E with
E = {k1<..<kt} above m needs one test per isolated k.  Two orderings are
emitted, because the ordering decides which lengths pay the extra test:

  order "small"  (design A, the default)
        cmp  x9, #16m   /  b.le .L256_dec_fused_small
        cmp  x9, #16k   /  b.eq .L256_dec_fused_k        (per k in E, ascending)
    -> nblk <= m: 2 instrs; nblk = k: 2+2i; nblk NOT retained: 2+2t.

  order "big"    (design B)
        cmp  x9, #16kt  /  b.gt .L256_dec_nofuse
                           b.eq .L256_dec_fused_kt
        cmp  x9, #16k   /  b.eq .L256_dec_fused_k        (descending)
        cmp  x9, #16m   /  b.le .L256_dec_fused_small
      .L256_dec_nofuse:
    -> nblk > kt (the bulk path) pays exactly the SAME TWO instructions a
       contiguous truncation pays; the retained small lengths pay the rest.

Self-check: for a contiguous set and order "small" the emitted assembly is
gen_trunc.py's, so the ASSEMBLED OBJECT must be md5-identical to gen_trunc's
`tC` (asserted in provision_p8.sh for C = 4,5,7,8).

Usage: gen_set.py <src.S> <dst.S> <set> <k1,..,k8> [small|big] [zapN|all]
       gen_set.py base.S t4p8.S 1,2,3,4,8 0.45,0.30,... small
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/tmp/fsp")
import gen                                     # fused-small-path/gen.py
import gen_trunc                               # fused-truncation/gen_trunc.py
tree = gen_trunc.tree                          # reused verbatim


def split(S):
    """S -> (m, extras): m = top of the contiguous run 1..m, extras = the rest."""
    S = sorted(S)
    assert S and S[0] == 1, "the set must contain nblk = 1"
    m = 1
    while m + 1 in S:
        m += 1
    return m, [k for k in S if k > m]


def entry(m, extras, order):
    if not extras:                             # contiguous: gen_trunc verbatim
        return ["\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk <= %d ?" % (16 * m, m),
                "\tb.le\t.L256_dec_fused_small"], []
    if order == "small":
        L = ["\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk <= %d ?" % (16 * m, m),
             "\tb.le\t.L256_dec_fused_small"]
        for k in extras:
            L += ["\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk == %d ?" % (16 * k, k),
                  "\tb.eq\t.L256_dec_fused_%d" % k]
        return L, []
    top = extras[-1]
    L = ["\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk > %d: not fused" % (16 * top, top),
         "\tb.gt\t.L256_dec_nofuse",
         "\tb.eq\t.L256_dec_fused_%d" % top]
    for k in reversed(extras[:-1]):
        L += ["\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk == %d ?" % (16 * k, k),
              "\tb.eq\t.L256_dec_fused_%d" % k]
    L += ["\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk <= %d ?" % (16 * m, m),
          "\tb.le\t.L256_dec_fused_small"]
    return L, [".L256_dec_nofuse:"]


def apply(text, kfracs, S, order="small", zap=0, zapall=False):
    m, extras = split(S)
    lines = text.split("\n")
    i = lines.index(gen.ENTRY_ANCHOR)
    ent, tail = entry(m, extras, order)
    lines[i:i + 1] = [gen.ENTRY_ANCHOR, ""] + ent + tail
    region = ["",
              ".L256_dec_fused_small:\t//[FUSE] dispatch on byte_len (x9), bodies %s"
              % ",".join(str(x) for x in sorted(S))]
    region += tree(list(range(1, m + 1)), [0])
    for n in sorted(S):
        region += gen.body(n, n, kfracs[n], zap=(zapall or zap == n))
    region.append("")
    j = lines.index(gen.RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, sarg, karg = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    order = sys.argv[5] if len(sys.argv) > 5 else "small"
    z = sys.argv[6] if len(sys.argv) > 6 else "0"
    S = sorted(int(x) for x in sarg.split(","))
    vals = [float(x) for x in karg.split(",")]
    assert len(vals) == 8
    kfracs = {n: vals[n - 1] for n in range(1, 9)}
    open(dst, "w").write(apply(open(src).read(), kfracs, S, order,
                               zap=(0 if z == "all" else int(z)),
                               zapall=(z == "all")))
    print("wrote %s set=%s order=%s k=%s zap=%s" % (dst, sarg, order, karg, z))
