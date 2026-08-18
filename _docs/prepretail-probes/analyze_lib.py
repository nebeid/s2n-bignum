#!/usr/bin/env python3
"""Slot counting + SIMD register liveness analysis for aesv8_gcm_8x_dec_256_wb.S"""
import re, sys, collections

PATH = sys.argv[1] if len(sys.argv) > 1 else \
    "/Volumes/workplace/git-code/s2n-bignum-kiro/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S"
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


PRE_LO, PRE_HI = 834, 1214

def _live_in_of(lines, lo, hi, also=()):
    live = set(also); defined = set()
    for i in range(lo-1, hi):
        p = parse(lines[i])
        if p is None: continue
        if p[0] == "eor3": d, u = set(p[1]), set(p[2])
        else: d, u = defuse(p[0], p[1])
        for r in u:
            if r not in defined: live.add(r)
        defined |= d
    return live

def prepretail_free(lines):
    """-> dict: source line number L -> set of vregs DEAD just before line L"""
    lo_tail  = _live_in_of(lines, 1215, 1230)
    lo_drain = _live_in_of(lines, 1521, 1716)
    lo_casc  = _live_in_of(lines, 1294, 1518)
    d_tail = set()
    for i in range(1215-1, 1230):
        p = parse(lines[i])
        if p is None: continue
        d_tail |= (set(p[1]) if p[0]=="eor3" else defuse(p[0],p[1])[0])
    live_out = lo_tail | ((lo_drain | lo_casc) - d_tail)
    n = PRE_HI - PRE_LO + 1
    live = set(live_out); ls = [None]*(n+1); ls[n] = set(live)
    for k in range(n-1, -1, -1):
        p = parse(lines[PRE_LO-1+k])
        if p is not None:
            if p[0] == "eor3": d, u = set(p[1]), set(p[2])
            else: d, u = defuse(p[0], p[1])
            live = (live - d) | u
        ls[k] = set(live)
    ALL = set(range(32))
    return { PRE_LO+k: (ALL - ls[k]) for k in range(n+1) }
