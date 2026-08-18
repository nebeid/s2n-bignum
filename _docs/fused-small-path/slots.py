import re,sys
L=open('src/base.S').read().split('\n')
def rng(a,b): return L[a-1:b]
SIMD=re.compile(r"^\s*(aese|aesmc|pmull2?|eor3?|ext|rev64|rev32|movi|add|mov|sub|and|trn1|trn2|bif|ins|umov)\s+[vqd]")
def count(lines):
    p=lo=pm=oth=0; i=0
    while i<len(lines):
        l=lines[i]
        if re.match(r"\s*aese\s",l):
            if i+1<len(lines) and re.match(r"\s*aesmc\s",lines[i+1]): p+=1; i+=2
            else: lo+=1; i+=1
            continue
        if re.match(r"\s*pmull2?\s",l): pm+=1
        elif l.strip().startswith('.inst') or SIMD.match(l): oth+=1
        i+=1
    return p,lo,pm,oth
R={'prologue':(58,371),'tailhead':(1215,1230),
   'sh1':(1232,1246),'sh2':(1248,1257),'sh3':(1259,1267),'sh4':(1269,1275),
   'sh5':(1277,1283),'sh6':(1285,1289),'sh7':(1291,1293),
   'mt7':(1294,1312),'mt6':(1313,1334),'mt5':(1335,1359),'mt4':(1360,1384),
   'mt3':(1385,1411),'mt2':(1412,1435),'mt1':(1436,1464),'lt1':(1465,1489),
   'epi':(1490,1518),'drain':(1521,1717)}
C={k:count(rng(*v)) for k,v in R.items()}
def tot(keys):
    s=[0,0,0,0]
    for k in keys:
        for i in range(4): s[i]+=C[k][i]
    return s, sum(s)
ENTRY={8:['drain'],7:['sh1','mt6','mt5','mt4','mt3','mt2','mt1','lt1'],
       6:['sh1','sh2','mt5','mt4','mt3','mt2','mt1','lt1'],
       5:['sh1','sh2','sh3','mt4','mt3','mt2','mt1','lt1'],
       4:['sh1','sh2','sh3','sh4','mt3','mt2','mt1','lt1'],
       3:['sh1','sh2','sh3','sh4','sh5','mt2','mt1','lt1'],
       2:['sh1','sh2','sh3','sh4','sh5','sh6','mt1','lt1'],
       1:['sh1','sh2','sh3','sh4','sh5','sh6','sh7','lt1']}
print("nblk  pairs lone pmull othALU  slots  floor_cyc")
for n in range(1,9):
    keys=['prologue','tailhead']+ENTRY[n]+['epi']
    s,t=tot(keys)
    print("%4d %6d %4d %5d %6d %6d %8.2f"%(n,s[0],s[1],s[2],s[3],t,t/4.0))
print()
print("region breakdown:", {k:sum(v) for k,v in C.items()})
