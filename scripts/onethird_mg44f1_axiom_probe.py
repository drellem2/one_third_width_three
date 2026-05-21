"""
mg-44f1 : audit probe for the disclosed axiom
   OneThird.Step8.lem_layered_balanced_irreducible_base

Claim of the axiom (step8.tex prop:in-situ-balanced Cases 2+3, the
irreducible twin-free residual of lem_layered_balanced_full):

  Every finite poset beta with
    * |beta| >= 2,
    * beta is NOT a chain,
    * width(beta) <= 3,
    * beta admits a layered decomposition L with interaction width L.w <= 4,
    * beta is layer-ordinal IRREDUCIBLE w.r.t. L (no band cut 1<=k<K with
      both sides non-empty is reducible),
    * beta is TWIN-FREE (no two distinct elements share the ambient
      up-profile AND down-profile),
  contains a BALANCED PAIR: an incomparable (x,y) with 1/3 <= Pr[x<y] <= 2/3
  over uniform random linear extensions.

This script does a genuine counterexample search:
  (E1) the unbounded canonical residual family  P_K : i<j  iff  j-i>2,
  (E2) exhaustive enumeration of ALL width-3 non-chain posets up to n=7
       (subsumes the axiom for small n; also = the width-3 1/3-2/3
       conjecture for n<=7),
  (E3) randomised generation of layered width-3 posets directly, filtered
       to the exact axiom hypothesis class (irreducible, twin-free,
       w<=4), at moderate-to-large n.
  (E4) several other structured unbounded irreducible families.

Outcome tags per experiment:  ALL-BALANCED / COUNTEREXAMPLE.
"""
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
import random, sys

sys.setrecursionlimit(1_000_000)
ONE_THIRD = Fraction(1,3)
TWO_THIRD = Fraction(2,3)

# ===========================================================================
#  Core: exact Pr[x<y] over uniform linear extensions, via order-ideal DP.
# ===========================================================================

def transitive_closure(n, edges):
    less = [[False]*n for _ in range(n)]
    for (i,j) in edges:
        less[i][j] = True
    for k in range(n):
        lk = less[k]
        for i in range(n):
            if less[i][k]:
                li = less[i]
                for j in range(n):
                    if lk[j]:
                        li[j] = True
    return less

def is_valid_poset(n, less):
    for i in range(n):
        if less[i][i]:
            return False
        for j in range(n):
            if less[i][j] and less[j][i]:
                return False
    return True

def width(n, less):
    for r in range(min(n,6), 0, -1):
        for S in combinations(range(n), r):
            if all(not less[a][b] and not less[b][a]
                   for a,b in combinations(S,2)):
                return r
    return 0

def width_at_most(n, less, k):
    """True iff every antichain has size <= k. (faster than full width)"""
    for S in combinations(range(n), k+1):
        if all(not less[a][b] and not less[b][a]
               for a,b in combinations(S,2)):
            return False
    return True

def is_chain(n, less):
    for i in range(n):
        for j in range(i+1,n):
            if not less[i][j] and not less[j][i]:
                return False
    return True

def has_twin(n, less):
    ups = [frozenset(z for z in range(n) if less[a][z]) for a in range(n)]
    dns = [frozenset(z for z in range(n) if less[z][a]) for a in range(n)]
    for a in range(n):
        for b in range(a+1,n):
            if ups[a]==ups[b] and dns[a]==dns[b]:
                return True
    return False

def linext_analyze(n, less):
    """Return (N, prob) : N = #linear extensions (int),
    prob[(x,y)] = Pr[x<_L y] (Fraction) for every ordered incomparable pair."""
    pred = [0]*n
    for j in range(n):
        for i in range(n):
            if less[i][j]:
                pred[j] |= (1<<i)
    succ = [0]*n
    for i in range(n):
        for j in range(n):
            if less[i][j]:
                succ[i] |= (1<<j)
    full = (1<<n)-1

    ideals = {0}
    stack = [0]
    while stack:
        I = stack.pop()
        for e in range(n):
            if not (I>>e)&1 and (pred[e]&I)==pred[e]:
                J = I|(1<<e)
                if J not in ideals:
                    ideals.add(J); stack.append(J)

    @lru_cache(maxsize=None)
    def g(I):
        if I==0: return 1
        s=0
        for e in range(n):
            if (I>>e)&1:
                if (succ[e] & I)==0:          # e maximal inside I
                    s += g(I & ~(1<<e))
        return s

    @lru_cache(maxsize=None)
    def h(I):
        if I==full: return 1
        s=0
        for e in range(n):
            if not (I>>e)&1 and (pred[e]&I)==pred[e]:
                s += h(I|(1<<e))
        return s

    N = g(full)
    prob = {}
    for x in range(n):
        for y in range(n):
            if x==y or less[x][y] or less[y][x]:
                continue
            num = 0
            for I in ideals:
                if (I>>y)&1: continue
                if (pred[y]&I)!=pred[y]: continue
                if not (I>>x)&1: continue
                num += g(I)*h(I|(1<<y))
            prob[(x,y)] = Fraction(num, N)
    g.cache_clear(); h.cache_clear()
    return N, prob

def best_balanced(n, less):
    """Return (has_balanced, best_pair, best_prob, closest_dist_to_half)."""
    N, prob = linext_analyze(n, less)
    has = False
    best = None
    best_gap = None      # distance of p from the interval [1/3,2/3]
    for (x,y),p in prob.items():
        if x>y: continue
        if ONE_THIRD <= p <= TWO_THIRD:
            has = True
        if p < ONE_THIRD:
            gap = ONE_THIRD - p
        elif p > TWO_THIRD:
            gap = p - TWO_THIRD
        else:
            gap = Fraction(0)
        if best_gap is None or gap < best_gap:
            best_gap = gap; best = (x,y,p)
    return has, best, best_gap, prob

# ===========================================================================
#  E1 : the canonical unbounded residual family  P_K  (i<j iff j-i>2)
# ===========================================================================

def family_PK(K):
    edges = [(i,j) for i in range(K) for j in range(K) if j-i>2]
    return transitive_closure(K, edges)

def run_E1(Kmax=90):
    print("="*72)
    print("E1  canonical unbounded residual family  P_K : i<j iff j-i>2")
    print("    band:=id, w=2, width 3, irreducible, twin-free for K>=6.")
    print("="*72)
    worst = None
    ce = []
    for K in range(6, Kmax+1):
        less = family_PK(K)
        assert is_valid_poset(K, less)
        assert width_at_most(K, less, 3) and not width_at_most(K, less, 2)
        assert not is_chain(K, less)
        assert not has_twin(K, less)
        has, best, gap, prob = best_balanced(K, less)
        # report the central adjacent pair too
        mid = K//2
        pm = prob.get((mid-1,mid)) or prob.get((mid,mid-1))
        tag = "BALANCED" if has else "*** COUNTEREXAMPLE ***"
        if not has:
            ce.append(K)
        if worst is None or gap > worst[1]:
            worst = (K, gap, best)
        if K<=14 or K%10==0 or not has:
            bx,by,bp = best
            print(f"  K={K:3d}  {tag:10s}  best pair ({bx},{by}) p={bp}"
                  f" ~{float(bp):.5f}   central adj p~"
                  f"{float(pm) if pm else float('nan'):.5f}")
    print(f"  --> worst-case 'gap from balance' over K in [6,{Kmax}]:"
          f" K={worst[0]}, gap={worst[1]} (~{float(worst[1]):.5f})")
    print(f"  --> counterexamples: {ce if ce else 'NONE'}")
    return len(ce)==0

# ===========================================================================
#  E2 : exhaustive width-3 non-chain posets up to n=7
# ===========================================================================

def run_E2(nmax=7):
    print("="*72)
    print(f"E2  exhaustive: EVERY width-3 non-chain poset, n=2..{nmax}")
    print("    (subsumes the axiom for small n = width-3 1/3-2/3 conj.)")
    print("="*72)
    overall_ok = True
    for n in range(2, nmax+1):
        pairs = [(i,j) for i in range(n) for j in range(i+1,n)]
        m = len(pairs)
        cnt = 0; ce = 0; checked = 0
        worst_gap = Fraction(0)
        for mask in range(1<<m):
            edges = [pairs[t] for t in range(m) if (mask>>t)&1]
            # only consider relations already transitively closed & valid
            less = transitive_closure(n, edges)
            # require the chosen edge set to BE its own transitive closure
            # restricted to the upper triangle (canonical: one poset per LE)
            if any(less[i][j]!=( (i,j) in set(edges) ) for (i,j) in pairs):
                continue
            if not is_valid_poset(n, less):
                continue
            if is_chain(n, less):
                continue
            if not width_at_most(n, less, 3):
                continue
            checked += 1
            has, best, gap, prob = best_balanced(n, less)
            if gap>worst_gap: worst_gap=gap
            if not has:
                ce += 1
                overall_ok = False
                print(f"   n={n}  COUNTEREXAMPLE edges={edges}")
        print(f"  n={n}: width-3 non-chain posets checked={checked:6d}"
              f"  counterexamples={ce}  worst gap-from-balance={worst_gap}")
    return overall_ok

# ===========================================================================
#  E3 : randomised layered width-3 posets, exact axiom hypothesis class
# ===========================================================================

def gen_layered(K, bandsizes, w, rng, p_comp=0.5):
    """Build a layered width-3 poset:
       elements 0..n-1 partitioned into bands 1..K with sizes bandsizes;
       cross-band pairs at band-distance>w are FORCED comparable (up);
       cross-band pairs at band-distance in [1,w] are comparable w.p. p_comp;
       same-band pairs never comparable.
    Returns (n, less, band, w)  or None if the result violates the
    layered axioms (band not an antichain after transitive closure, or
    width>3, or a forced relation got contradicted)."""
    band = []
    for k,sz in enumerate(bandsizes, start=1):
        band += [k]*sz
    n = len(band)
    edges = []
    for x in range(n):
        for y in range(n):
            bx,by = band[x],band[y]
            if by>bx:
                d = by-bx
                if d>w:
                    edges.append((x,y))
                elif rng.random()<p_comp:
                    edges.append((x,y))
    less = transitive_closure(n, edges)
    if not is_valid_poset(n, less):
        return None
    # bands must stay antichains
    for x in range(n):
        for y in range(n):
            if x!=y and band[x]==band[y] and less[x][y]:
                return None
    # (L2-upward): comparable => band non-decreasing  (true by construction)
    # (L2-forced): far pairs comparable               (true by construction)
    if not width_at_most(n, less, 3):
        return None
    return n, less, band, w

def layer_ordinal_reducible(n, less, band, k):
    for u in range(n):
        if band[u]<=k:
            for v in range(n):
                if band[v]>k and not less[u][v]:
                    return False
    return True

def is_irreducible(n, less, band, K):
    for k in range(1, K):
        lo = any(band[z]<=k for z in range(n))
        hi = any(band[z]> k for z in range(n))
        if lo and hi and layer_ordinal_reducible(n, less, band, k):
            return False
    return True

def run_E3(trials=40000, seed=20260521):
    print("="*72)
    print(f"E3  randomised layered width-3 posets in the EXACT axiom class")
    print(f"    (irreducible, twin-free, w<=4); {trials} trials")
    print("="*72)
    rng = random.Random(seed)
    inclass = 0; ce = 0
    worst = None
    sizes_seen = {}
    for t in range(trials):
        w  = rng.randint(1,4)
        K  = rng.randint(3, 14)
        bandsizes = [rng.randint(1,3) for _ in range(K)]
        pc = rng.choice([0.3,0.4,0.5,0.6,0.7])
        res = gen_layered(K, bandsizes, w, rng, pc)
        if res is None:
            continue
        n, less, band, ww = res
        if n>22:           # keep DP feasible
            continue
        if n<2: continue
        if is_chain(n, less):
            continue
        if not is_irreducible(n, less, band, K):
            continue
        if has_twin(n, less):
            continue
        inclass += 1
        sizes_seen[n] = sizes_seen.get(n,0)+1
        has, best, gap, prob = best_balanced(n, less)
        if worst is None or gap>worst[1]:
            worst = (n, gap, best, band[:], [(i,j) for i in range(n)
                     for j in range(n) if less[i][j]])
        if not has:
            ce += 1
            print(f"  *** COUNTEREXAMPLE  n={n} band={band}")
            print(f"      relations={[(i,j) for i in range(n) for j in range(n) if less[i][j]]}")
    print(f"  in-class posets tested: {inclass}   counterexamples: {ce}")
    print(f"  size distribution: {dict(sorted(sizes_seen.items()))}")
    if worst:
        n,gap,best,band,rel = worst
        print(f"  worst gap-from-balance: n={n} gap={gap} (~{float(gap):.5f})"
              f" best pair {best[:2]} p={best[2]} (~{float(best[2]):.5f})")
    return ce==0

# ===========================================================================
#  E4 : other structured unbounded irreducible width-3 families
# ===========================================================================

def run_E4(Kmax=40):
    print("="*72)
    print("E4  other structured unbounded irreducible width-3 families")
    print("="*72)
    ok = True

    # F4a: i<j iff j-i>2 OR (j-i==2 and i even)  -- perturbed P_K, w=2
    def f4a(K):
        edges=[(i,j) for i in range(K) for j in range(K)
               if (j-i>2) or (j-i==2 and i%2==0)]
        return transitive_closure(K,edges)
    # F4b: 'doubled spine' -- bands of size 2 with a diagonal break.
    #      band k has elements (k,0),(k,1); (k,a)<(k',a') iff k'-k>2;
    #      plus break twins via (k,0)<(k+2,1) for all k (k+2<=K).
    def f4b(K):
        idx={}
        els=[]
        for k in range(1,K+1):
            for a in (0,1):
                idx[(k,a)]=len(els); els.append((k,a))
        edges=[]
        for (k,a) in els:
            for (k2,a2) in els:
                if k2-k>2:
                    edges.append((idx[(k,a)],idx[(k2,a2)]))
                elif k2-k==2 and a==0 and a2==1:
                    edges.append((idx[(k,a)],idx[(k2,a2)]))
        n=len(els)
        less=transitive_closure(n,edges)
        return n,less
    # F4c: i<j iff j-i>2 OR j-i>1 and (i mod 3==0)   (width<=3 check applied)
    def f4c(K):
        edges=[(i,j) for i in range(K) for j in range(K)
               if (j-i>2) or (j-i==2 and i%3==0)]
        return transitive_closure(K,edges)

    for name,fam,rng_ in [("F4a perturbed-PK", f4a, range(8,Kmax+1,2)),
                          ("F4c mod3-perturbed-PK", f4c, range(8,Kmax+1,2))]:
        bad=[]
        for K in rng_:
            less=fam(K)
            if not is_valid_poset(K,less): continue
            if not width_at_most(K,less,3): continue
            if is_chain(K,less): continue
            if has_twin(K,less): continue
            has,best,gap,prob=best_balanced(K,less)
            if not has: bad.append(K)
        st = "ALL-BALANCED" if not bad else f"COUNTEREXAMPLES {bad}"
        print(f"  {name:26s}: {st}")
        ok &= (not bad)

    bad=[]
    for K in range(6, 22):
        n,less=f4b(K)
        if not is_valid_poset(n,less): continue
        if not width_at_most(n,less,3): continue
        if is_chain(n,less): continue
        tw = has_twin(n,less)
        if tw:                    # doubled spine may still have twins
            continue
        if n>22: break
        has,best,gap,prob=best_balanced(n,less)
        if not has: bad.append(K)
    st = "ALL-BALANCED" if not bad else f"COUNTEREXAMPLES {bad}"
    print(f"  {'F4b doubled-spine':26s}: {st}")
    ok &= (not bad)
    return ok

# ===========================================================================
if __name__=="__main__":
    import time
    t0=time.time()
    r1=run_E1(Kmax=90)
    r2=run_E2(nmax=7)
    r3=run_E3(trials=40000)
    r4=run_E4(Kmax=40)
    print("="*72)
    print(f"SUMMARY  E1={'PASS' if r1 else 'FAIL'}  E2={'PASS' if r2 else 'FAIL'}"
          f"  E3={'PASS' if r3 else 'FAIL'}  E4={'PASS' if r4 else 'FAIL'}")
    print(f"  all experiments: {'NO COUNTEREXAMPLE FOUND' if (r1 and r2 and r3 and r4) else 'COUNTEREXAMPLE(S) FOUND'}")
    print(f"  elapsed: {time.time()-t0:.1f}s")
