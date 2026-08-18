#!/usr/bin/env python3
"""Generate ceiling-probe and fusion variants of aesv8_gcm_8x_dec_256_wb.S.

Probes (functionally WRONG on purpose, upper bounds only):
  drain0  : delete ALL GHASH SIMD-ALU work from .L256_dec_exact8_drain
  drain4  : delete GHASH SIMD-ALU work of 4 of the 8 drain blocks
  pploadK : add K independent dummy pmulls into the prepretail (free-reg dests)
"""
import re, sys, os

SRC = sys.argv[1]
OUT = sys.argv[2]
lines = open(SRC).read().split("\n")

def mn_of(ln):
    body = ln.split("//")[0].strip()
    if not body: return None
    if body.startswith(".inst"):
        c = ln[ln.find("//")+2:].strip()
        return "eor3:" + c.split()[1].rstrip(",") if c.startswith("eor3") else ".inst"
    if body.startswith(".") or body.endswith(":"): return None
    return body.split()[0]

GH_ALU = ("rev64","ext","pmull","pmull2","eor","movi","trn1","trn2")

def strip_ghash(lo, hi):
    """blank out GHASH SIMD-ALU lines in [lo,hi] 1-based inclusive; keep ld/st,
       plaintext eor3 (dest v12), rev32 v30."""
    n = 0
    for i in range(lo-1, hi):
        ln = lines[i]
        m = mn_of(ln)
        if m is None: continue
        if m.startswith("eor3:"):
            dst = m[5:]
            if dst.startswith("v12"):     # plaintext result - keep
                continue
            lines[i] = "\t// [PROBE removed] " + ln.strip(); n += 1; continue
        if m in GH_ALU:
            lines[i] = "\t// [PROBE removed] " + ln.strip(); n += 1
    return n

mode = os.environ.get("MODE")

if mode == "drain0":
    n = strip_ghash(1521, 1716)
    print(f"drain0: removed {n} GHASH SIMD-ALU ops from the exact-8 drain")
elif mode == "drain4":
    # blocks final-6, final-5, final-4, final-3  (source lines 1549..1641)
    n = strip_ghash(1549, 1641)
    print(f"drain4: removed {n} GHASH SIMD-ALU ops (4 of 8 drain blocks)")
elif mode and mode.startswith("ppload"):
    K = int(mode[6:])
    # insert K independent dummy pmulls spread over the prepretail, only at
    # positions that do NOT break an aese/aesmc pair, using a dead dest reg.
    # free-reg map recomputed by analyze-style liveness would be ideal; here we
    # use v29 / v16 / v26 rotation restricted to points where they are dead is
    # hard, so instead use the SAFEST possible dummy: write to a register that
    # is immediately redefined by the very next definition of itself... simpler:
    # use `pmull v<d>.1q, v30.1d, v31.1d` with d chosen from the per-point free
    # set computed below.
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import analyze_lib
    freeset = analyze_lib.prepretail_free(lines)     # list per source line
    cands = []
    for i in range(834-1, 1214):
        m = mn_of(lines[i])
        if m is None: continue
        if m == "aese": continue          # inserting after aese breaks the pair
        fs = sorted(freeset.get(i+2, set()))   # free AFTER this line
        if fs: cands.append((i, fs))
    if not cands:
        sys.exit("no insertion candidates")
    step = len(cands)/K
    ins = {}
    for j in range(K):
        idx, fs = cands[int(j*step)]
        ins.setdefault(idx, []).append(fs[j % len(fs)])
    for idx, regs in ins.items():
        extra = "\n".join(f"\tpmull\tv{r}.1q, v30.1d, v31.1d\t\t// [PROBE dummy]" for r in regs)
        lines[idx] = lines[idx] + "\n" + extra
    print(f"ppload{K}: inserted {K} dummy pmulls at {len(ins)} sites in the prepretail")
elif mode and (mode.startswith("emulpp") or mode.startswith("emulpr")):
    # COMPOSITE emulation of the proposed fusion:
    #   remove the drain GHASH (as drain0) AND add the same number of
    #   independent SIMD ops back into the destination region.
    K = int(mode[6:])
    dest = "pp" if mode.startswith("emulpp") else "pr"
    n = strip_ghash(1521, 1716)
    if dest == "pp":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import analyze_lib
        freeset = analyze_lib.prepretail_free(lines)
        cands = []
        for i in range(834-1, 1214):
            m = mn_of(lines[i])
            if m is None or m == "aese": continue
            fs = sorted(freeset.get(i+2, set()))
            if fs: cands.append((i, fs))
        step = len(cands)/K; ins = {}
        for j in range(K):
            idx, fs = cands[int(j*step)]
            ins.setdefault(idx, []).append(fs[j % len(fs)])
    else:
        FREE = [8,9,10,11,12,13,14,15,16,17,18,20,21,22,23,24,25]
        cands = [i for i in range(180-1,371) if mn_of(lines[i]) not in (None,"aese")]
        step = len(cands)/K; ins = {}
        for j in range(K):
            idx = cands[int(j*step)]
            ins.setdefault(idx, []).append(FREE[j % len(FREE)])
    for idx, regs in ins.items():
        lines[idx] += "\n" + "\n".join(f"\tpmull\tv{r}.1q, v30.1d, v31.1d\t\t// [PROBE dummy]" for r in regs)
    print(f"{mode}: removed {n} drain GHASH ops, re-added {K} independent SIMD ops to "
          + ("the PREPRETAIL" if dest=="pp" else "the PROLOGUE"))
elif mode and mode.startswith("prol"):
    K = int(mode[4:])
    FREE = [8,9,10,11,12,13,14,15,16,17,18,20,21,22,23,24,25]
    cands = [i for i in range(180-1,371) if mn_of(lines[i]) not in (None,"aese")]
    step = len(cands)/K
    ins = {}
    for j in range(K):
        idx = cands[int(j*step)]
        ins.setdefault(idx, []).append(FREE[j % len(FREE)])
    for idx, regs in ins.items():
        lines[idx] += "\n" + "\n".join(f"\tpmull\tv{r}.1q, v30.1d, v31.1d\t\t// [PROBE dummy]" for r in regs)
    print(f"prol{K}: inserted {K} dummy pmulls in the PROLOGUE AES region (control)")
elif mode and mode.startswith("pptail"):
    K = int(mode[6:])
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import analyze_lib
    fs = sorted(analyze_lib.prepretail_free(lines)[1215])
    body = "\n".join(f"\tpmull\tv{fs[j % len(fs)]}.1q, v30.1d, v31.1d\t\t// [PROBE dummy]" for j in range(K))
    lines[1214-1] += "\n" + body
    print(f"pptail{K}: appended {K} dummy pmulls at the END of the prepretail (free regs {fs})")
else:
    sys.exit("set MODE=drain0|drain4|pploadK|prolK|pptailK")

open(OUT,"w").write("\n".join(lines))
