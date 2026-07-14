import sys, itertools, random
sys.path.insert(0,"scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset
def posmaps(P): return [{e:i for i,e in enumerate(pm)} for pm in P.linear_extensions()]
def chains(P,x):
    inc=[y for y in range(P.n) if y!=x and not P.comparable(x,y)]
    out=[]
    for r in range(2,len(inc)+1):
        for sub in itertools.combinations(inc,r):
            if all(P.comparable(a,b) for a,b in itertools.combinations(sub,2)):
                out.append(tuple(sorted(sub,key=lambda z: sum(1 for w in sub if w in P.less[z]))))
    return out
def rp(n,p,rng):
    o=list(range(n)); rng.shuffle(o); pr=[]
    for i in range(n):
        for j in range(i+1,n):
            if rng.random()<p: pr.append((o[i],o[j]))
    return Poset(n,pr)
rng=random.Random(99); worst=[]; nf=0
for _ in range(25000):
    n=rng.randint(4,8); P=rp(n,rng.choice([.25,.35,.45]),rng)
    if P.linext_count()>25000: continue
    pms=posmaps(P); L=len(pms)
    for x in range(n):
        for ch in chains(P,x):
            p=len(ch); a=[0]*(p+1)
            for pm in pms: a[sum(1 for c in ch if pm[c]<pm[x])]+=1
            bias=[sum(1 for pm in pms if pm[c]<pm[x])/L for c in ch]
            dmax=max(min(b,1-b) for b in bias)
            j=sum(1 for b in bias if b>0.5)
            ES2=sum((m-j)**2*c/L for m,c in enumerate(a)); Eab=sum(abs(m-j)*c/L for m,c in enumerate(a))
            ratio=ES2/Eab if Eab>1e-12 else 0
            if dmax<1/3-1e-9:
                nf+=1; worst.append((ratio,p,dmax,n,tuple(a),j))
worst.sort(reverse=True)
print("strictly-frozen chains(len>=2):",nf)
print("top frozen-chain ratios (ratio,p,dmax,n,a,j):")
for w in worst[:10]: print("  %.3f p=%d dmax=%.3f n=%d a=%s j=%d"%w)
print("MAX frozen ratio:", max((w[0] for w in worst),default=None))
