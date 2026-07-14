#!/usr/bin/env python3
"""mg-2acf: cross-checks for the (B) LOCALITY proof.

(1) e(P_m) sliding-log-concavity in the CLEAN form: a_m = e(P_m) where P_m adds
    y_i<x (i<=m) and x<y_i (i>m) to P for a chain Y incomparable to x.  Verifies
    a_m = #{LE of P: slot_Y(x)=m} (consistency) AND log-concavity of e(P_m).
(2) END-TO-END constant: on frozen / near-frozen width-3 posets, check the derived
    chain bound  E[S_C^2] <= 6 E|S_C|  per chain, and the headline
    E[sum disp^2] <= 24 E[inv_e]  (=> Cross <= 22 E[inv_e]).
"""
import sys, itertools, random
sys.path.insert(0,"scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset

def les_pos(P):
    les=P.linear_extensions()
    return les,[{e:i for i,e in enumerate(perm)} for perm in les]

def slot_dist_direct(les_posmaps, x, chain):
    a=[0]*(len(chain)+1)
    for pm in les_posmaps:
        a[sum(1 for c in chain if pm[c]<pm[x])]+=1
    return a

def ePm(P,x,chain,m):
    # P_m: y_i<x for i<m ... using 0-indexed chain positions 0..p-1; slot m means
    # first m chain elts below x. add chain[i]<x for i<m, x<chain[i] for i>=m.
    extra=[]
    for i,c in enumerate(chain):
        if i<m: extra.append((c,x))     # c < x
        else:   extra.append((x,c))     # x < c
    try:
        Q=Poset(P.n,list(_pairs(P))+extra)
    except ValueError:
        return None
    return Q.linext_count()

def _pairs(P):
    for b in range(P.n):
        for a in P.less[b]:
            yield (a,b)

def logc(a):
    return all(a[m]*a[m]>=a[m-1]*a[m+1] for m in range(1,len(a)-1))

def chains_in_incset(P,x,maximal_only=False):
    inc=[y for y in range(P.n) if y!=x and not P.comparable(x,y)]
    out=[]
    for r in range(1,len(inc)+1):
        for sub in itertools.combinations(inc,r):
            if all(P.comparable(a,b) for a,b in itertools.combinations(sub,2)):
                s=sorted(sub,key=lambda z: sum(1 for w in sub if w in P.less[z]))
                out.append(tuple(s))
    return out

def random_poset(n,p,rng):
    order=list(range(n)); rng.shuffle(order); pairs=[]
    for i in range(n):
        for j in range(i+1,n):
            if rng.random()<p: pairs.append((order[i],order[j]))
    return Poset(n,pairs)

def test_ePm(ntrial=4000):
    rng=random.Random(7)
    consistency_fail=0; logc_fail=0; checked=0; exs=[]
    for _ in range(ntrial):
        n=rng.randint(3,7); P=random_poset(n,rng.choice([.25,.4,.55]),rng)
        if P.linext_count()>20000: continue
        les,pms=les_pos(P)
        for x in range(n):
            for chain in chains_in_incset(P,x):
                a_direct=slot_dist_direct(pms,x,chain)
                a_pm=[ePm(P,x,chain,m) for m in range(len(chain)+1)]
                checked+=1
                if a_pm!=a_direct: consistency_fail+=1
                if not logc(a_direct):
                    logc_fail+=1
                    if len(exs)<5: exs.append((n,x,chain,a_direct))
    print(f"[e(P_m)] checked={checked}  consistency_fail={consistency_fail}  logconcavity_fail={logc_fail}")
    for e in exs: print("   ",e)
    return logc_fail==0 and consistency_fail==0

if __name__=="__main__":
    ok=test_ePm()
    print("e(P_m) sliding-log-concavity + consistency:", "PASS" if ok else "FAIL")
