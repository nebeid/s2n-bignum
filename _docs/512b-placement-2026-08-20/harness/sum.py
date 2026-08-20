#!/usr/bin/env python3
import sys, collections, statistics, random, os
R = "/tmp/plres"
HOSTS = [("gv3", "Neoverse-V1 c7g.2xlarge"), ("gv4", "Neoverse-V2 c8g.4xlarge"),
         ("gv5", "Neoverse-V3 c9g.4xlarge"), ("r8g", "Neoverse-V2 r8g.xlarge")]

def load(p):
    V, clk, procs, labels = {}, [], set(), []
    for L in open(p):
        f = L.split()
        if not f: continue
        if f[0] == "RES":
            V[(int(f[1]), int(f[2]), f[3])] = float(f[4]); procs.add(int(f[1]))
            if f[3] not in labels: labels.append(f[3])
        elif f[0] == "CLK": clk += [float(f[2]), float(f[3])]
    return V, clk, sorted(procs), labels

def med(x): return statistics.median(x)
def ci(d, n=20000):
    r = random.Random(7)
    m = sorted(med([d[r.randrange(len(d))] for _ in range(len(d))]) for _ in range(n))
    return m[int(.025*n)], m[int(.975*n)]

def groups(labels):
    g = collections.OrderedDict()
    for l in labels: g.setdefault(l.split(".")[0], []).append(l)
    return g

def pdelta(V, procs, s, ra, rb):          # paired delta list, groups of labels
    A = [med([V[(p, s, l)] for l in ra]) for p in procs]
    B = [med([V[(p, s, l)] for l in rb]) for p in procs]
    return [100.0*(b-a)/a for a, b in zip(A, B)]

def aa(V, procs, s, g):
    out = []
    for _, labs in g.items():
        for i in range(len(labs)):
            for j in range(i+1, len(labs)):
                out.append(med(pdelta(V, procs, s, [labs[i]], [labs[j]])))
    return out

SZ = [64, 256, 512, 1024]

print("="*100)
print("TABLE 1  Phase 1: the EXACT banked pcb4 binary, 32 processes, median of per-process paired deltas")
print("          C = 91b1ce25 optimised kernel, D = fused d5r.  negative = D faster.")
print("="*100)
print("%-5s %-9s | %s" % ("host", "clockGHz", "  ".join("%-28s" % ("%d B  C->D" % s) for s in SZ)))
for t, _ in HOSTS:
    V, clk, procs, labels = load("%s/p1_%s.txt" % (t, t))
    row = []
    for s in SZ:
        d = pdelta(V, procs, s, ["C_91b1ce25"], ["D_fused"])
        lo, hi = ci(d)
        row.append("%+7.3f%% [%+6.3f,%+6.3f]" % (med(d), lo, hi))
    print("%-5s %-9.4f | %s" % (t, max(clk), "  ".join("%-28s" % x for x in row)))
print()
print("A/A floor in the same binary (C vs aaC, D vs aaD; byte-identical code, two addresses):")
print("%-5s | %s" % ("host", "  ".join("%-22s" % ("%d B" % s) for s in SZ)))
for t, _ in HOSTS:
    V, clk, procs, labels = load("%s/p1_%s.txt" % (t, t))
    row = []
    for s in SZ:
        a = med(pdelta(V, procs, s, ["C_91b1ce25"], ["aaC"]))
        b = med(pdelta(V, procs, s, ["D_fused"], ["aaD"]))
        row.append("C %+6.3f%%  D %+6.3f%%" % (a, b))
    print("%-5s | %s" % (t, "  ".join("%-22s" % x for x in row)))

print()
print("="*100)
print("TABLE 2  Phase 2: does the 512 B C->D delta move when only PLACEMENT changes?")
print("          P0..P4 = five link orders of 4 C-copies + 4 D-copies; PADn = n bytes of")
print("          never-executed .text linked ahead of the whole kernel group (P0 order).")
print("          32 processes per cell.  A/A |max| = widest byte-identical-pair delta in the same cell.")
print("="*100)
CFG = ["P0","P1","P2","P3","P4","PAD16","PAD64","PAD128","PAD256","PAD1024"]
for t, desc in HOSTS:
    print("\n-- %s (%s)" % (t, desc))
    print("   %-8s | %-26s %-9s | %-26s %-9s" %
          ("cfg", "512 B  C->D (median+CI)", "AA|max|", "64 B  C->D (pos. control)", "AA|max|"))
    for c in CFG:
        f = "%s/%s.txt" % (t, c)
        if not os.path.exists(f): continue
        V, clk, procs, labels = load(f)
        g = groups(labels)
        cells = []
        for s in (512, 64):
            d = pdelta(V, procs, s, g["cn"], g["dn"]); lo, hi = ci(d)
            f_ = max(abs(x) for x in aa(V, procs, s, g))
            cells.append(("%+7.3f%% [%+6.3f,%+6.3f]" % (med(d), lo, hi), "%.3f%%" % f_))
        print("   %-8s | %-26s %-9s | %-26s %-9s" % (c, cells[0][0], cells[0][1], cells[1][0], cells[1][1]))

print()
print("="*100)
print("TABLE 3  Phase 3a: 2x2, function entry forced to a 64-byte boundary, 40 processes.")
print("          ca0/da0 = C/D unmodified; ca8/da8 = same code with 8 bytes (2 nop) inserted")
print("          immediately before .L256_dec_main_loop.  main-loop address mod 16:")
print("          ca0 = 8, da0 = 0, ca8 = 0, da8 = 8.   ref = ca0.")
print("="*100)
for t, desc in HOSTS:
    V, clk, procs, labels = load("%s/A2X2.txt" % t)
    g = groups(labels)
    print("\n-- %s (%s)  clock %.4f GHz" % (t, desc, max(clk)))
    for s in (512, 64):
        f_ = max(abs(x) for x in aa(V, procs, s, g))
        cells = []
        for k in ["ca0", "da0", "ca8", "da8"]:
            d = pdelta(V, procs, s, g["ca0"], g[k])
            cells.append("%-4s %+7.3f%%" % (k, med(d)))
        print("   %5d B  %s   | A/A |max| %.3f%%" % (s, "  ".join(cells), f_))

print()
print("="*100)
print("TABLE 4  Phase 3b/3c: main-loop entry address mod 16 vs time, 40 processes.")
print("          One variant only (all 8 slots are the SAME kernel), function entry 64-byte")
print("          aligned, main loop shifted by 0..56 bytes of nop.  Rows grouped by (ml addr mod 16).")
print("          Delta is vs the pad=0 slot of the same sweep.")
print("="*100)
MOD = {"0": 8, "8": 0, "16": 8, "24": 0, "32": 8, "40": 0, "48": 8, "56": 0}
# pad p -> ml mod 16 : C's natural ml offset is 1208 (=8 mod 16), D's is 1216 (=0 mod 16)
CMOD = {p: (1208 + p) % 16 for p in (0,8,16,24,32,40,48,56)}
DMOD = {p: (1216 + p) % 16 for p in (0,8,16,24,32,40,48,56)}
for t, desc in HOSTS:
    print("\n-- %s (%s)" % (t, desc))
    for sw, pre, mm in (("ACSW", "ca", CMOD), ("ADSW", "da", DMOD)):
        V, clk, procs, labels = load("%s/%s.txt" % (t, sw))
        g = groups(labels)
        for s in (512,):
            b0 = {}
            for p in (0,8,16,24,32,40,48,56):
                b0[p] = med(pdelta(V, procs, s, g[pre+"0"], g[pre+"%d"%p]))
            m0 = [b0[p] for p in b0 if mm[p] == 0]
            m8 = [b0[p] for p in b0 if mm[p] == 8]
            print("   %s %4dB  ml@0 mod16: %s (mean %+6.3f%%)" %
                  (sw, s, " ".join("%+6.3f" % x for x in m0), sum(m0)/len(m0)))
            print("   %s %4dB  ml@8 mod16: %s (mean %+6.3f%%)  ==> gap %+6.3f%%" %
                  (" "*len(sw), s, " ".join("%+6.3f" % x for x in m8), sum(m8)/len(m8),
                   sum(m8)/len(m8) - sum(m0)/len(m0)))
