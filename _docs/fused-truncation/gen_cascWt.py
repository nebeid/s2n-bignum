#!/usr/bin/env python3
"""TRUNCATED width-W fall-through cascade: cover nblk <= MAXN with the cascade
and let nblk > MAXN fall through to the EXISTING staggered path unchanged.

Family 2 of _docs/fused-truncation-curve.md: W = 4, MAXN = 7 (the W=4 cascade
regresses +7 % against HEAD at nblk = 8, so nblk = 8 must keep the baseline's
dedicated exact-8 drain).

Reuses fused-cascade/gen_cascW.py's section/stub/body generators verbatim; the
only changes are the entry test (#16*MAXN instead of #128), a dispatch tree over
{1..MAXN}, and dropping the now-unreachable super-sections above MAXN.

Usage:  gen_cascWt.py <src.S> <dst.S> <W> <MAXN> <ksec> <k1> [pfx] [zapN] [zsecJ]
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/tmp/fsp")
import gen_cascW as G


def tree(vals, pfx, ctr):
    s = lambda n: "%s_stub_%d" % (G.L(pfx), n)
    if len(vals) == 1:
        return ["\tb\t%s" % s(vals[0])]
    if len(vals) == 2:
        return ["\tcmp\tx9, #%d" % (16 * vals[0]),
                "\tb.eq\t%s" % s(vals[0]), "\tb\t%s" % s(vals[1])]
    mid = (len(vals) + 1) // 2
    lo, hi = vals[:mid], vals[mid:]
    ctr[0] += 1
    lbl = "%s_h%d" % (G.L(pfx), ctr[0])
    return (["\tcmp\tx9, #%d" % (16 * lo[-1]), "\tb.gt\t%s" % lbl]
            + tree(lo, pfx, ctr) + ["%s:" % lbl] + tree(hi, pfx, ctr))


def apply(text, W, maxn, pfx, ksec, k1, zap=0, zapsec=0):
    assert 8 % W == 0 and 1 <= maxn <= 8
    lines = text.split("\n")
    i = lines.index(G.ENTRY_ANCHOR)
    lines[i:i + 1] = [G.ENTRY_ANCHOR, "",
                      "\tcmp\tx9, #%d\t\t\t\t//[CASCW] nblk <= %d ?" % (16 * maxn, maxn),
                      "\tb.le\t%s_small" % G.L(pfx)]
    region = G.common(pfx) + tree(list(range(1, maxn + 1)), pfx, [0])
    for n in range(maxn, 0, -1):
        region += G.stub(W, n, pfx, zap=(zap == n))
    # fall-through chain of super-sections, only those still reachable
    ss = [k for k in range(W, maxn + 1, W)][::-1]
    for k in ss:
        region += G.gen_body(G.L("%s_ss%d" % (pfx, k)), list(range(k, k - W, -1)),
                             terminal=(k == W), cont=None, ksec=ksec, k1=k1,
                             zapsec=zapsec)
    region += G.epilogue(G.L("%s_done" % pfx))
    for n in range(maxn, 0, -1):
        q = n % W
        if q == 0:
            continue
        if n - q > 0:
            region += G.gen_body(G.L("%s_pb%d" % (pfx, n)), list(range(n, n - q, -1)),
                                 terminal=False, cont=G.L("%s_ss%d" % (pfx, n - q)),
                                 ksec=ksec, k1=k1, zapsec=zapsec)
        else:
            region += G.gen_body(G.L("%s_sb%d" % (pfx, n)), list(range(n, 0, -1)),
                                 terminal=True, cont=None, ksec=ksec, k1=k1,
                                 zapsec=zapsec)
            region += G.epilogue(G.L("%s_done%d" % (pfx, n)))
    region.append("")
    j = lines.index(G.RET_ANCHOR)
    lines[j:j] = region
    return "\n".join(lines)


if __name__ == "__main__":
    src, dst = sys.argv[1], sys.argv[2]
    W, maxn = int(sys.argv[3]), int(sys.argv[4])
    ksec, k1 = float(sys.argv[5]), float(sys.argv[6])
    pfx = sys.argv[7] if len(sys.argv) > 7 else "cwt"
    zap = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    zapsec = int(sys.argv[9]) if len(sys.argv) > 9 else 0
    open(dst, "w").write(apply(open(src).read(), W, maxn, pfx, ksec, k1, zap, zapsec))
    print("wrote %s W=%d maxn=%d ksec=%s k1=%s zap=%d zsec=%d"
          % (dst, W, maxn, ksec, k1, zap, zapsec))
