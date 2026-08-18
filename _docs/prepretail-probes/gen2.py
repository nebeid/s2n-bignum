#!/usr/bin/env python3
"""gen2.py SRC OUT   env: REMOVE_DRAIN=0|1  DEST=pp|pr|none  NPMULL=n NEOR=n

Emulates relocating the exact-8 drain's GHASH work into another region without
writing a real schedule: optionally strips the drain's GHASH SIMD-ALU ops and
injects the SAME op mix (pmull / vector-eor) into the destination region using
registers that liveness proves dead there.  Functionally wrong when
REMOVE_DRAIN=1 (upper-bound probe); functionally CORRECT when REMOVE_DRAIN=0
(pure cost probe -> the bench self-check must still pass).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze_lib
from analyze_lib import parse

SRC, OUT = sys.argv[1], sys.argv[2]
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
    n = 0
    for i in range(lo-1, hi):
        m = mn_of(lines[i])
        if m is None: continue
        if m.startswith("eor3:"):
            if m[5:].startswith("v12"): continue
            lines[i] = "\t// [PROBE removed] " + lines[i].strip(); n += 1; continue
        if m in GH_ALU:
            lines[i] = "\t// [PROBE removed] " + lines[i].strip(); n += 1
    return n

REMOVE = os.environ.get("REMOVE_DRAIN","0") == "1"
DEST   = os.environ.get("DEST","none")
NP     = int(os.environ.get("NPMULL","0"))
NE     = int(os.environ.get("NEOR","0"))

nrem = strip_ghash(1521, 1716) if REMOVE else 0

K = NP + NE
if K:
    if DEST == "pp":
        freeset = analyze_lib.prepretail_free(lines)
        cands = []
        for i in range(834-1, 1214):
            m = mn_of(lines[i])
            if m is None or m == "aese": continue
            fs = sorted(freeset.get(i+2, set()))
            if fs: cands.append((i, fs))
    elif DEST == "pr":
        FREE = [8,9,10,11,12,13,14,15,16,17,18,20,21,22,23,24,25]
        cands = [(i, FREE) for i in range(180-1, 371) if mn_of(lines[i]) not in (None,"aese")]
    else:
        sys.exit("DEST must be pp or pr when injecting")
    # op list: interleave pmulls and eors evenly
    ops = []
    for j in range(K):
        ops.append("pmull" if (j * NP) % K < NP else "eor")
    ops = ["pmull"]*NP + ["eor"]*NE
    # shuffle deterministically so the mix is spread
    ops = [ops[(j*7) % K] for j in range(K)] if False else \
          [("pmull" if (j % K) * NP // K != ((j+1) % (K+1)) * NP // K or j < NP else "eor") for j in range(K)]
    ops = []
    p = e = 0
    for j in range(K):
        if p * NE <= e * NP and p < NP: ops.append("pmull"); p += 1
        else: ops.append("eor"); e += 1
    assert ops.count("pmull") == NP and ops.count("eor") == NE, (ops.count("pmull"), NP)
    ZONE = os.environ.get("ZONE","all")
    if ZONE == "front": cands = cands[:len(cands)//3]
    elif ZONE == "back": cands = cands[-len(cands)//3:]
    elif ZONE == "mid": cands = cands[len(cands)//3:2*len(cands)//3]
    step = len(cands)/K
    ins = {}
    for j in range(K):
        idx, fs = cands[int(j*step)]
        r = fs[j % len(fs)]
        ins.setdefault(idx, []).append(
            f"\tpmull\tv{r}.1q, v30.1d, v31.1d\t\t// [PROBE dummy]" if ops[j] == "pmull"
            else f"\teor\tv{r}.16b, v30.16b, v31.16b\t\t// [PROBE dummy]")
    for idx, body in ins.items():
        lines[idx] += "\n" + "\n".join(body)
    sites = len(ins)
else:
    sites = 0

print(f"gen2: drain GHASH removed={nrem}  injected {NP} pmull + {NE} eor into "
      f"{DEST} at {sites} sites")
open(OUT, "w").write("\n".join(lines))
