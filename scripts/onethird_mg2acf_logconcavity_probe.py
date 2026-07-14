#!/usr/bin/env python3
"""mg-2acf: THE CRUX numerical test for closing (B) LOCALITY.

Reduction (this session): under width-3 + frozen (H), disp(x) splits as a sum of
<= 2 chain-crossing variables S_C = slot_C - j_C (slot_C = #{C-elements before x}),
one per chain C covering the incomparable set Inc(x) (Dilworth: width(Inc(x))<=2).
Cauchy-Schwarz kills the cross term, so (B) reduces to a PER-CHAIN second-moment
bound E[S_C^2] = O(E|S_C|). Given the LOG-CONCAVITY of a_m := #{LE: slot_C = m},
the frozen straddle t_0=Pr[slot>=j]>2/3, t_1=Pr[slot>=j+1]<1/3 forces geometric
tail ratio < 1/2, hence E[S_C^2] <= 6 E|S_C|. EVERYTHING pins to:

  LOG-CONCAVITY LEMMA: for a finite poset P, element x, chain Y with x incomparable
  to every element of Y, the sequence a_m = #{lin.ext. sigma : exactly m elements of
  Y precede x} is log-concave (a_m^2 >= a_{m-1} a_{m+1}).

This script BRUTE-FORCES that lemma on random small posets. A single counterexample
would reframe (B) from PROVEN to a precisely-named wall.
"""
import sys, itertools, random
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset

def chains_in_incset(P, x):
    """All maximal-ish chains among Inc(x): here just enumerate every chain (subset
    of Inc(x) totally ordered by P). We test log-concavity for EVERY chain, not only
    maximal ones, to stress the lemma hardest."""
    inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
    chains = []
    # all subsets of inc that form a chain, size >= 1
    for r in range(1, len(inc)+1):
        for sub in itertools.combinations(inc, r):
            ok = all(P.comparable(a,b) for a,b in itertools.combinations(sub,2))
            if ok:
                # order it by P
                s = list(sub)
                s.sort(key=lambda z: sum(1 for w in sub if w in P.less[z]))
                chains.append(tuple(s))
    return chains

def slot_dist(les, x, chain):
    a = [0]*(len(chain)+1)
    posidx = {}
    for perm in les:
        pos = {e:i for i,e in enumerate(perm)}
        m = sum(1 for c in chain if pos[c] < pos[x])
        a[m]+= 1
    return a

def is_log_concave(a):
    for m in range(1, len(a)-1):
        if a[m]*a[m] < a[m-1]*a[m+1]:      # strict violation
            return False, m
    return True, None

def random_poset(n, p, rng):
    pairs=[]
    order = list(range(n)); rng.shuffle(order)
    for i in range(n):
        for j in range(i+1,n):
            if rng.random()<p:
                pairs.append((order[i],order[j]))
    return Poset(n, pairs)

def width(P):
    # largest antichain via brute (small n)
    best=0
    els=list(range(P.n))
    for r in range(P.n,0,-1):
        found=False
        for sub in itertools.combinations(els,r):
            if all(not P.comparable(a,b) for a,b in itertools.combinations(sub,2)):
                found=True;break
        if found: return r
    return 1

def main():
    rng = random.Random(20260714)
    tested=0; viol=0; examples=[]
    NTRIAL=6000                       # capped so the sweep terminates; the decisive
    for t in range(NTRIAL):           # refutation lives in the endtoend probe (68k checks)
        n = rng.randint(3,7)
        p = rng.choice([0.2,0.3,0.4,0.5,0.6])
        P = random_poset(n,p,rng)
        if P.linext_count() > 8000:   # keep enumeration cheap
            continue
        les = P.linear_extensions()
        for x in range(n):
            for chain in chains_in_incset(P,x):
                a = slot_dist(les,x,chain)
                tested+=1
                ok,mm = is_log_concave(a)
                if not ok:
                    viol+=1
                    if len(examples)<8:
                        examples.append((n,p,x,chain,a,width(P)))
    print(f"tested {tested} (poset,x,chain) log-concavity checks")
    print(f"VIOLATIONS: {viol}")
    for ex in examples:
        print("  n=%d p=%.1f x=%d chain=%s a=%s width=%d"%ex)
    if viol==0:
        print("RESULT: log-concavity HELD on every reachable instance.")
    else:
        print("RESULT: log-concavity FAILS -> (B) is a WALL, not proven.")

if __name__=="__main__":
    main()
