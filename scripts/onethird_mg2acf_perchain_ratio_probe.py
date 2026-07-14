#!/usr/bin/env python3
"""mg-2acf: the SHARP residual test. My reduction shows (B) LOCALITY holds iff, per
chain C incomparable to x, E[S_C^2] = O(E|S_C|), where S_C = slot_C - j_C. Log-concavity
of the slot distribution WOULD give constant 6 but is FALSE unconditionally. So I test
the ACTUAL target on FROZEN chains: for each (P,x,chain) whose x-vs-chain pairs are all
strictly frozen (per-pair delta<1/3), report E[S^2]/E|S| and correlate with chain length.

The 'bimodal block-cross' a=[1-c,0,...,0,c] would give ratio = p (chain length). If it is
realizable under frozen width-3, some frozen chain shows a large ratio. If it is NOT
realizable at reachable n, ratios stay small -> (B) holds in-reach (consistent with wall
being out of empirical reach)."""
import sys, itertools, random
sys.path.insert(0,"scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset

def les_posmaps(P):
    return [{e:i for i,e in enumerate(perm)} for perm in P.linear_extensions()]

def chains_in_incset(P,x):
    inc=[y for y in range(P.n) if y!=x and not P.comparable(x,y)]
    out=[]
    for r in range(1,len(inc)+1):
        for sub in itertools.combinations(inc,r):
            if all(P.comparable(a,b) for a,b in itertools.combinations(sub,2)):
                out.append(tuple(sorted(sub,key=lambda z: sum(1 for w in sub if w in P.less[z]))))
    return out

def width(P):
    els=list(range(P.n))
    for r in range(P.n,0,-1):
        for sub in itertools.combinations(els,r):
            if all(not P.comparable(a,b) for a,b in itertools.combinations(sub,2)):
                return r
    return 1

def random_poset(n,p,rng):
    order=list(range(n)); rng.shuffle(order); pairs=[]
    for i in range(n):
        for j in range(i+1,n):
            if rng.random()<p: pairs.append((order[i],order[j]))
    return Poset(n,pairs)

def analyze_chain(pms,L,x,chain):
    p=len(chain)
    # slot distribution
    a=[0]*(p+1)
    for pm in pms:
        a[sum(1 for c in chain if pm[c]<pm[x])]+=1
    # per-pair bias vs x: Pr[c before x]; also need e-order j. e-rank ~ E[pos].
    # Determine j via frozen straddle: j = #chain elts that should be 'e-below' x.
    # Use bias: pair {x,c} frozen if min(Pr[c<x],1-.)<1/3. delta_max over chain:
    biases=[sum(1 for pm in pms if pm[c]<pm[x])/L for c in chain]  # Pr[c before x]
    deltas=[min(b,1-b) for b in biases]
    dmax=max(deltas)
    # j = number of chain elts e-below x. e has x-vs-c oriented by majority: c e-below x
    # iff Pr[c before x]>1/2 (c tends before x => c is 'earlier' => e-smaller). chain is
    # ordered so biases are non-increasing; j = #{c: bias>1/2}.
    j=sum(1 for b in biases if b>0.5)
    # S = slot - j
    ES=0.0; ES2=0.0; Eabs=0.0
    for m,cnt in enumerate(a):
        s=m-j; w=cnt/L
        ES+=s*w; ES2+=s*s*w; Eabs+=abs(s)*w
    ratio=ES2/Eabs if Eabs>1e-12 else 0.0
    return dict(p=p,dmax=dmax,ES2=ES2,Eabs=Eabs,ratio=ratio,a=a,j=j)

def main():
    rng=random.Random(2024)
    worst=[]      # frozen chains, by ratio
    worst_any=[]  # any chain
    frozen_count=0
    for _ in range(120000):
        n=rng.randint(4,9); P=random_poset(n,rng.choice([.2,.3,.4,.5]),rng)
        if P.linext_count()>60000: continue
        if width(P)>3: continue
        pms=les_posmaps(P); L=len(pms)
        for x in range(n):
            for chain in chains_in_incset(P,x):
                if len(chain)<2: continue
                r=analyze_chain(pms,L,x,chain)
                worst_any.append((r['ratio'],r['p'],r['dmax'],n))
                if r['dmax']<1/3-1e-9:     # strictly frozen chain
                    frozen_count+=1
                    worst.append((r['ratio'],r['p'],r['dmax'],n,r['a'],r['j']))
    worst.sort(reverse=True); worst_any.sort(reverse=True)
    print(f"strictly-frozen chains (len>=2) found: {frozen_count}")
    print("TOP frozen-chain ratios E[S^2]/E|S|  (ratio, p=len, dmax, n, a, j):")
    for w in worst[:12]: print("  %.3f  p=%d dmax=%.3f n=%d a=%s j=%d"%w)
    print("TOP over ALL width-3 chains (ratio, p, dmax, n):")
    for w in worst_any[:8]: print("  %.3f p=%d dmax=%.3f n=%d"%w)
    if worst:
        maxr=max(w[0] for w in worst)
        print(f"MAX frozen-chain ratio = {maxr:.3f}  (target: bounded by ~6 if (B) holds in-reach)")

if __name__=="__main__": main()
