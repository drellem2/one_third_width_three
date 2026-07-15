from itertools import permutations, combinations
from fractions import Fraction as F

def closure(n, rels):
    R=set(rels); ch=True
    while ch:
        ch=False
        for (a,b) in list(R):
            for (c,d) in list(R):
                if b==c and (a,d) not in R: R.add((a,d)); ch=True
    return R
def linexts(n,R):
    res=[]
    for perm in permutations(range(n)):
        pos={perm[i]:i for i in range(n)}
        if all(pos[a]<pos[b] for (a,b) in R): res.append(perm)
    return res

# P3: chain 1<2<3 ; x=0 free (e-min) ; 4,5 free. width 4.
n=6
R=closure(n,[(1,2),(2,3)])
LE=linexts(n,R); L=len(LE)
def pos_of(perm): return {perm[i]:i for i in range(n)}

# crossing cut m (m in 1..n-1): element x crosses cut m iff min(rank,pos)<m<=max  i.e. rank,pos on opposite sides of the boundary between position m-1 and m
def crosses(rank,posx,m):
    lo=min(rank,posx); hi=max(rank,posx)
    return lo < m <= hi   # boundary m sits between index m-1 and m; crossed iff lo<m<=hi

# K_m = #{x: rank<m<=pos}  (prefix elt pushed past); but total crossers of cut m = 2 K_m. |disp| = #cuts crossed.
# Verify |disp(x)| = # cuts crossed
import sys
Edisp2=F(0);Einv=F(0);EsumK=F(0)
incomp=[(i,j) for i in range(n) for j in range(i+1,n) if (i,j) not in R and (j,i) not in R]
# M_{k,l} accumulation
Mkl={(k,l):F(0) for k in range(1,n) for l in range(k+1,n)}
Km_e={m:F(0) for m in range(1,n)}
for perm in LE:
    pos=pos_of(perm)
    Edisp2+=F(sum((pos[x]-x)**2 for x in range(n)),L)
    Einv+=F(sum(1 for (i,j) in incomp if pos[j]<pos[i]),L)
    for m in range(1,n):
        Km=sum(1 for x in range(n) if x<m and pos[x]>=m)
        EsumK+=F(Km,L); Km_e[m]+=F(Km,L)
        # check crossers
    for k in range(1,n):
        for l in range(k+1,n):
            cnt=sum(1 for x in range(n) if crosses(x,pos[x],k) and crosses(x,pos[x],l))
            Mkl[(k,l)]+=F(cnt,L)
sumM=sum(Mkl.values())
print(f"n={n} width=4 |LE|={L}")
print(f"E[sum disp^2] = {Edisp2} = {float(Edisp2):.4f}")
print(f"E[inv_e]      = {Einv} = {float(Einv):.4f}")
print(f"E[sum_m K_m]  = {EsumK} = {float(EsumK):.4f}")
print(f"sum_kl E[M_kl]= {sumM} = {float(sumM):.4f}")
print(f"GID: 2*EsumK+2*sumM = {2*EsumK+2*sumM}  vs E[sumdisp2]={Edisp2}  MATCH={2*EsumK+2*sumM==Edisp2}")
print(f"DiaconisGraham: E[sum_m K_m] <= E[inv_e]? {EsumK} <= {Einv} : {EsumK<=Einv}")
print("per-cut leakage E[K_m]:", {m:float(Km_e[m]) for m in Km_e})
print("M_kl table E[M_kl]:")
for k in range(1,n):
    for l in range(k+1,n):
        print(f"   E[M_{{{k},{l}}}]={float(Mkl[(k,l)]):.4f}", end="")
    print()
# slot law for x=0 vs chain C=(1,2,3): q_i=Pr[c_i before x]=Pr[pos(i)<pos(0)]
print("\nBlock-cross object: x=element 0 (e-min), chain C=(c1,c2,c3)=(1,2,3)")
for i in [1,2,3]:
    c=sum(1 for perm in LE if pos_of(perm)[i]<pos_of(perm)[0])
    q=F(c,L)
    print(f"  q_{i} = Pr[c_{i} (rank {i}) before x] = {q} = {float(q):.4f}")
qs={i:F(sum(1 for perm in LE if pos_of(perm)[i]<pos_of(perm)[0]),L) for i in [1,2,3]}
for i in [1,2]:
    print(f"  rho_{i} = q_{i+1}/q_{i} = {qs[i+1]/qs[i]} = {float(qs[i+1]/qs[i]):.4f}")
# g = #{c_i before x}, E[g], E[g^2]
Eg=F(0);Eg2=F(0)
for perm in LE:
    p=pos_of(perm); g=sum(1 for i in [1,2,3] if p[i]<p[0])
    Eg+=F(g,L); Eg2+=F(g*g,L)
print(f"  E[g]={Eg}={float(Eg):.4f}  E[g^2]={Eg2}={float(Eg2):.4f}  single-elt ratio E[g^2]/E[g]={float(Eg2/Eg):.4f}")
