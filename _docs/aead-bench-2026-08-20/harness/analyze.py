import sys, collections
SZ=[16,32,64,128,256,512,1024,4096]
NAMES=["A_awslc","B_5500b7e6","C_91b1ce25","D_fused","aaA","aaB","aaC","aaD"]
per=collections.defaultdict(list)   # (size,name) -> per-process minima
clk=[]
for L in open(sys.argv[1]):
    f=L.split()
    if f[0]=="RES": per[(int(f[2]),f[3])].append(float(f[4]))
    elif f[0]=="CLK": clk += [float(f[2]),float(f[3])]
GHZ=max(clk)
mn={k:min(v) for k,v in per.items()}
nproc=len(per[(16,"A_awslc")])
print("processes=%d  reps/process=200  clock GHz min/max = %.4f / %.4f  (using %.4f)"%(nproc,min(clk),max(clk),GHZ))

print("\n### ns/call (min over %d processes of best-of-200)\n"%nproc)
print("| size | A aws-lc | B 5500b7e6 | C 91b1ce25 | D fused |")
print("|---|---|---|---|---|")
for s in SZ:
    print("| %d | %.3f | %.3f | %.3f | %.3f |"%(s,mn[(s,"A_awslc")],mn[(s,"B_5500b7e6")],mn[(s,"C_91b1ce25")],mn[(s,"D_fused")]))

print("\n### cycles/call and cycles/byte at %.4f GHz\n"%GHZ)
print("| size | A cyc | A c/B | B cyc | B c/B | C cyc | C c/B | D cyc | D c/B |")
print("|---|---|---|---|---|---|---|---|---|")
for s in SZ:
    r=[]
    for n in ["A_awslc","B_5500b7e6","C_91b1ce25","D_fused"]:
        c=mn[(s,n)]*GHZ; r += ["%.1f"%c, "%.3f"%(c/s)]
    print("| %d | %s |"%(s," | ".join(r)))

print("\n### A/A noise floor (byte-identical code under two symbol names)\n")
print("| size | A vs aaA | B vs aaB | C vs aaC | D vs aaD | floor (max abs) | max per-proc spread |")
print("|---|---|---|---|---|---|---|")
floor={}
for s in SZ:
    ds=[]
    for a,b in [("A_awslc","aaA"),("B_5500b7e6","aaB"),("C_91b1ce25","aaC"),("D_fused","aaD")]:
        ds.append(100.0*(mn[(s,b)]-mn[(s,a)])/mn[(s,a)])
    fl=max(abs(d) for d in ds); floor[s]=fl
    sp=max(100.0*(max(per[(s,n)])-min(per[(s,n)]))/min(per[(s,n)]) for n in NAMES)
    print("| %d | %+.2f%% | %+.2f%% | %+.2f%% | %+.2f%% | %.2f%% | %.2f%% |"%(s,ds[0],ds[1],ds[2],ds[3],fl,sp))

def d(s,frm,to):
    a,b=mn[(s,frm)],mn[(s,to)]
    return 100.0*(b-a)/a

print("\n### deltas (negative = the second one is faster). `~` = |delta| below that size's A/A floor\n")
print("| size | B->C | C->D | A->C | A->D | floor |")
print("|---|---|---|---|---|---|")
for s in SZ:
    row=[]
    for frm,to in [("B_5500b7e6","C_91b1ce25"),("C_91b1ce25","D_fused"),
                   ("A_awslc","C_91b1ce25"),("A_awslc","D_fused")]:
        v=d(s,frm,to)
        row.append("%+.2f%%%s"%(v,"~" if abs(v)<floor[s] else ""))
    print("| %d | %s | %.2f%% |"%(s," | ".join(row),floor[s]))

print("\n### speedup form (how much faster, positive = faster)\n")
print("| size | C vs B | D vs C | C vs A | D vs A |")
print("|---|---|---|---|---|")
for s in SZ:
    def sp(frm,to): return 100.0*(mn[(s,frm)]-mn[(s,to)])/mn[(s,frm)]
    print("| %d | +%.1f%% | +%.1f%% | +%.1f%% | +%.1f%% |"%(s,
        sp("B_5500b7e6","C_91b1ce25"),sp("C_91b1ce25","D_fused"),
        sp("A_awslc","C_91b1ce25"),sp("A_awslc","D_fused")))

print("\n### per-process minima spread, all symbols (info)\n")
for s in SZ:
    print("size %5d: "%s + "  ".join("%s %.3f-%.3f"%(n,min(per[(s,n)]),max(per[(s,n)])) for n in NAMES[:4]))
