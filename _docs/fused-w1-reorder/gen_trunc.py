#!/usr/bin/env python3
"""TRUNCATED eight-body fused small path: keep fused bodies for nblk <= C only,
and let nblk > C fall through to the EXISTING staggered prologue+cascade path,
completely unchanged.

Family 1 of _docs/fused-truncation-curve.md.  Reuses fused-small-path/gen.py's
body generator verbatim (imported, not copied), so a retained body for a given n
is instruction-for-instruction the same code the full eight-body variant ships.
The only differences from that variant are

  * the entry test becomes   cmp x9, #16*C  /  b.le .L256_dec_fused_small
    (so nblk in (C,8] simply never leaves the baseline path), and
  * the dispatch tree spans {1..C} instead of {1..8}.

The dispatch tree is a balanced compare tree built by the same recursion that
reproduces gen.py's hand-written tree exactly at C = 8 (self-checked: the C=8
object md5 must equal the full variant's tuned.o).

Usage:  gen_trunc.py <src.S> <dst.S> <C> <k1,..,k8> [zapN | all]
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/tmp/fsp")
import gen                                    # fused-small-path/gen.py


def tree(vals, ctr):
    """Balanced compare tree on x9 (= byte_len) over the block counts `vals`."""
    if len(vals) == 1:
        return ["\tb\t.L256_dec_fused_%d" % vals[0]]
    if len(vals) == 2:
        return ["\tcmp\tx9, #%d" % (16 * vals[0]),
                "\tb.eq\t.L256_dec_fused_%d" % vals[0],
                "\tb\t.L256_dec_fused_%d" % vals[1]]
    mid = (len(vals) + 1) // 2
    lo, hi = vals[:mid], vals[mid:]
    ctr[0] += 1
    lbl = ".L256_dec_fs_h%d" % ctr[0]
    return (["\tcmp\tx9, #%d" % (16 * lo[-1]), "\tb.gt\t%s" % lbl]
            + tree(lo, ctr) + ["%s:" % lbl] + tree(hi, ctr))


def apply(text, kfracs, C, zap=0, zapall=False):
    lines = text.split("\n")
    i = lines.index(gen.ENTRY_ANCHOR)
    if C == 0:
        # PURE-DISPATCH CONTROL (`dsp0`): the same two instructions every
        # truncation puts on the fall-through path, and the same 8-byte shift of
        # everything after them, but NO fused region at all.  The whole-blocks
        # contract gives x9 >= 16, so the branch is never taken and the kernel
        # is functionally the baseline.  Isolates the cost of the dispatch test
        # from the cost of the appended code.
        lines[i:i + 1] = [gen.ENTRY_ANCHOR, "",
                          "\tcmp\tx9, #0\t\t\t\t//[FUSE] never taken (x9 >= 16)",
                          "\tb.le\t.L256_dec_ret"]
        return "\n".join(lines)
    lines[i:i + 1] = [gen.ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #%d\t\t\t\t//[FUSE] nblk <= %d ?" % (16 * C, C),
                      "\tb.le\t.L256_dec_fused_small"]
    region = ["",
              ".L256_dec_fused_small:\t//[FUSE] nblk <= %d: dispatch on byte_len (x9)" % C]
    region += tree(list(range(1, C + 1)), [0])
    for n in range(1, C + 1):
        region += gen.body(n, n, kfracs[n], zap=(zapall or zap == n))
    region.append("")
    j = lines.index(gen.RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst, C, karg = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    z = sys.argv[5] if len(sys.argv) > 5 else "0"
    vals = [float(x) for x in karg.split(",")]
    assert len(vals) == 8
    kfracs = {n: vals[n - 1] for n in range(1, 9)}
    open(dst, "w").write(apply(open(src).read(), kfracs, C,
                               zap=(0 if z == "all" else int(z)),
                               zapall=(z == "all")))
    print("wrote %s C=%d k=%s zap=%s" % (dst, C, karg, z))
