#!/usr/bin/env python3
"""Slot counting + SIMD register liveness analysis for aesv8_gcm_8x_dec_256_wb.S"""
import re, sys, os, collections

# Default: the decrypt kernel, resolved relative to this script's location in
# the repository.  Pass a path explicitly to analyse a different .S file.
PATH = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), os.pardir, os.pardir,
    "arm", "aes-gcm", "aesv8_gcm_8x_dec_256_wb.S")
lines = open(PATH).read().split("\n")

def strip_comment(s):
    i = s.find("//")
    return s[:i] if i >= 0 else s

def parse(ln):
    """-> (mnemonic, [dst regs], [src regs], raw) for SIMD-relevant insns, else None"""
    raw = ln
    body = strip_comment(ln).strip()
    if body.startswith(".inst"):
        # take the operands from the comment (eor3 vX, vY, vZ, vW)
        c = ln[ln.find("//") + 2:].strip()
        body = strip_comment(c).strip() if c.startswith("eor3") else c.strip()
        m = re.match(r'(eor3)\s+(.*)', body)
        if not m:
            return None
        ops = [o.strip() for o in m.group(2).split(",")]
        regs = [regnum(o) for o in ops]
        return ("eor3", [regs[0]], regs[1:], raw)
    if not body or body.startswith(".") or body.endswith(":") or body.startswith("#"):
        return None
    m = re.match(r'([a-z][a-z0-9_.]*)\s*(.*)', body)
    if not m:
        return None
    mn, rest = m.group(1), m.group(2)
    ops = [o.strip() for o in rest.split(",")] if rest else []
    return (mn, ops, raw)

VREG = re.compile(r'^[vqd](\d+)')
def regnum(op):
    op = op.strip().strip("{} ").split(".")[0]
    m = VREG.match(op)
    return int(m.group(1)) if m else None

def defuse(mn, ops):
    """return (defs,uses) sets of SIMD reg numbers"""
    defs, uses = set(), set()
    if mn in ("aese", "aesmc", "aesd", "aesimc"):
        d = regnum(ops[0]); defs.add(d); uses.add(d)
        for o in ops[1:]:
            r = regnum(o)
            if r is not None: uses.add(r)
    elif mn in ("ldr", "ldp", "ld1"):
        # destinations are the vector regs before the [addr]
        txt = ",".join(ops)
        addr = txt.find("[")
        head = txt[:addr] if addr >= 0 else txt
        for o in head.split(","):
            r = regnum(o)
            if r is not None: defs.add(r)
    elif mn in ("str", "stp", "st1"):
        txt = ",".join(ops)
        addr = txt.find("[")
        head = txt[:addr] if addr >= 0 else txt
        for o in head.split(","):
            r = regnum(o)
            if r is not None: uses.add(r)
    elif mn in ("movi",):
        d = regnum(ops[0])
        if d is not None: defs.add(d)
    elif mn in ("mov",) and regnum(ops[0]) is not None:
        d = regnum(ops[0]); defs.add(d)
        # mov v.d[1], x15 : partial write -> also a use
        if "[" in ops[0]: uses.add(d)
        for o in ops[1:]:
            r = regnum(o)
            if r is not None: uses.add(r)
    else:
        # generic: first operand is dest, rest are sources
        if not ops: return defs, uses
        d = regnum(ops[0])
        if d is None:
            return defs, uses      # not a SIMD insn (b, cmp, add x.., etc.)
        defs.add(d)
        for o in ops[1:]:
            r = regnum(o)
            if r is not None: uses.add(r)
    return defs, uses

# ---------------- slot counting ----------------
def slots(lo, hi):
    """count SIMD issue slots in [lo,hi] (1-based inclusive); aese+aesmc adjacent pair = 1"""
    n_pair = n_lone_aese = n_pmull = n_other = 0
    i = lo - 1
    prev_aese_reg = None
    while i < hi:
        p = parse(lines[i])
        i += 1
        if p is None: continue
        if p[0] == "eor3":
            n_other += 1; prev_aese_reg = None; continue
        mn, ops = p[0], p[1]
        if mn == "aese":
            if prev_aese_reg is not None: n_lone_aese += 1
            prev_aese_reg = regnum(ops[0]); continue
        if mn == "aesmc":
            if prev_aese_reg is not None and regnum(ops[0]) == prev_aese_reg:
                n_pair += 1; prev_aese_reg = None; continue
            n_other += 1; continue
        if prev_aese_reg is not None:
            n_lone_aese += 1; prev_aese_reg = None
        if mn.startswith("pmull"):
            n_pmull += 1
        elif mn in ("ldr","ldp","ld1","str","stp","st1"):
            pass                      # load/store pipes, not SIMD issue slots
        elif ops and regnum(ops[0]) is not None:
            n_other += 1
    if prev_aese_reg is not None: n_lone_aese += 1
    return n_pair, n_lone_aese, n_pmull, n_other

REGIONS = [("prologue", 52, 371), ("main loop body", 415, 832),
           ("prepretail", 834, 1214), ("tail entry", 1215, 1230),
           ("tail cascade", 1294, 1489), ("exact-8 drain", 1521, 1716),
           ("epilogue", 1490, 1518)]
print("region                 pairs lone pmull other  SLOTS  floor@4/cyc")
tot = {}
for nm, lo, hi in REGIONS:
    a, b, c, d = slots(lo, hi)
    s = a + b + c + d
    tot[nm] = s
    print(f"{nm:22s} {a:5d} {b:4d} {c:5d} {d:5d} {s:6d} {s/4:11.2f}")

print()
for nblk, iters in ((8,0),(16,0),(32,2),(64,6),(256,30)):
    if nblk == 8:
        s = tot["prologue"] + tot["tail entry"] + tot["exact-8 drain"] + tot["epilogue"]
        desc = "prologue+tailentry+drain+epilogue"
    else:
        s = (tot["prologue"] + iters*tot["main loop body"] + tot["prepretail"]
             + tot["tail entry"] + tot["exact-8 drain"] + tot["epilogue"])
        desc = f"prologue+{iters}*loop+prepretail+tailentry+drain+epilogue"
    print(f"nblk={nblk:3d} ({nblk*16:4d} B): {s:5d} slots -> floor {s/4:8.2f} cyc   [{desc}]")

# ---------------- liveness in prepretail ----------------
PRE_LO, PRE_HI = 834, 1214
# live-out at the fallthrough into .L256_dec_tail (line 1215..):
# compute by scanning the tail region for first-use-before-def of each vreg.
def live_in_of(lo, hi, also=()):
    live = set(also)
    defined = set()
    for i in range(lo-1, hi):
        p = parse(lines[i])
        if p is None: continue
        if p[0] == "eor3":
            d, u = set(p[1]), set(p[2])
        else:
            d, u = defuse(p[0], p[1])
        for r in u:
            if r not in defined: live.add(r)
        defined |= d
    return live

# tail path is the exact-8 drain (for whole-multiple-of-8 sizes) but the cascade
# is also reachable; take the union of both to be safe.
lo_tail = live_in_of(1215, 1230)
lo_drain = live_in_of(1521, 1716)
lo_casc = live_in_of(1294, 1518)
lo_epi = live_in_of(1490, 1518)
# defs in tail entry
d_tail = set()
for i in range(1215-1, 1230):
    p = parse(lines[i])
    if p is None: continue
    d = set(p[1]) if p[0]=="eor3" else defuse(p[0],p[1])[0]
    d_tail |= d
live_out_pre = lo_tail | ((lo_drain | lo_casc) - d_tail)
print("\nlive-out of prepretail (vregs needed by tail):", sorted(live_out_pre))

# backward liveness through prepretail
n = PRE_HI - PRE_LO + 1
live = set(live_out_pre)
liveset = [None]*(n+1)
liveset[n] = set(live)
for k in range(n-1, -1, -1):
    p = parse(lines[PRE_LO-1+k])
    if p is not None:
        if p[0] == "eor3":
            d, u = set(p[1]), set(p[2])
        else:
            d, u = defuse(p[0], p[1])
        live = (live - d) | u
    liveset[k] = set(live)
print("live-in  of prepretail:", sorted(liveset[0]))

ALL = set(range(32))
print("\nprepretail free-register profile (registers dead at each point):")
prev = None
minfree = 99; maxfree = 0
freehist = collections.Counter()
for k in range(n+1):
    free = ALL - liveset[k]
    freehist[len(free)] += 1
    minfree = min(minfree, len(free)); maxfree = max(maxfree, len(free))
print("  free-count histogram (points):", dict(sorted(freehist.items())))
print(f"  min free = {minfree}, max free = {maxfree}")

# registers free for the WHOLE prepretail region (never live at any point)
always_free = set(ALL)
for k in range(n+1):
    always_free &= (ALL - liveset[k])
print("  registers dead across the ENTIRE prepretail:", sorted(always_free))

# print the free set at coarse checkpoints
print("\n  free sets at checkpoints (source line -> free regs):")
for k in range(0, n+1, 20):
    ln = PRE_LO + k
    free = sorted(ALL - liveset[k])
    print(f"   L{ln:5d} n={len(free):2d}: {free}")
ln = PRE_HI+1
print(f"   L{ln:5d} n={len(ALL-liveset[n]):2d}: {sorted(ALL-liveset[n])}")
