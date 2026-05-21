"""
mg-44f1 : DEEP probe (E5/E6/E7) for lem_layered_balanced_irreducible_base.

Builds on onethird_mg44f1_axiom_probe.py.  Targets the genuine residual
regime identified by mg-65de: the UNBOUNDED, layer-ordinal-IRREDUCIBLE,
twin-free width-3 class.  Three deeper probes:

  E5  exhaustive enumeration of SINGLETON-BAND irreducible width-3 w<=4
      posets up to K bands (this is exactly mg-4d7b's cap-1 regime, but
      run UNBOUNDED in K instead of capped at |Q|<=10) -- plus random
      sampling at large K.  Reports the in-class poset with the best
      balanced pair CLOSEST to the 1/3 or 2/3 boundary.

  E6  the balance spectrum: across every in-class poset found, the
      distribution of  delta(P) = max over incomparable pairs of the
      'balancedness' (1/2 - |p-1/2| folded); how much margin the class
      keeps from the [1/3,2/3] edge.

  E7  homogeneous / periodic layered posets at very large K -- kills the
      boundary advantage, isolates the 'bulk' behaviour.
"""
from fractions import Fraction
from itertools import combinations
import random, sys, time

sys.path.insert(0, "/Users/daniel/.pogo/polecats/44f1/scripts")
from onethird_mg44f1_axiom_probe import (
    transitive_closure, is_valid_poset, width_at_most, is_chain, has_twin,
    linext_analyze, best_balanced, is_irreducible, layer_ordinal_reducible,
    ONE_THIRD, TWO_THIRD)

# ---------------------------------------------------------------------------
def edge_gap(p):
    """distance of p from the closed interval [1/3,2/3]; 0 if inside."""
    if p < ONE_THIRD: return ONE_THIRD - p
    if p > TWO_THIRD: return p - TWO_THIRD
    return Fraction(0)

def balance_margin(p):
    """how far INSIDE [1/3,2/3] p sits (min distance to either edge);
    negative if outside."""
    return min(p-ONE_THIRD, TWO_THIRD-p)

# ===========================================================================
#  E5 : singleton-band irreducible width-3 w<=4 posets, UNBOUNDED in K.
# ===========================================================================

def enum_singleton_band(K, w, width_cap=3):
    """Yield every poset on 0..K-1 (element i in band i+1) such that
    band:=id is a layered decomposition of interaction width exactly <=w:
    forced  j<i  whenever i-j>w; free choice whenever 1<=i-j<=w;
    width<=3.  Yields `less` matrices."""
    # incremental: posets[k] are valid posets on 0..k-1 (as 'less' tuples).
    # We carry the boolean 'less' as a tuple-of-tuples for hashing.
    start = ((),)  # less for k=1 element: 1x1 all False
    # represent less as list of lists; build recursively
    results = []
    def rec(k, less):
        if k == K:
            results.append([row[:] for row in less])
            return
        # add element k ; choose predecessor set among 0..k-1
        forced = set(j for j in range(k) if k-j > w)
        # candidates for free predecessors: j with 1<=k-j<=w
        free = [j for j in range(k) if 1 <= k-j <= w]
        for r in range(len(free)+1):
            for chosen in combinations(free, r):
                pred = forced | set(chosen)
                # pred must be a down-set of `less`
                ok = True
                for j in pred:
                    for j2 in range(k):
                        if less[j2][j] and j2 not in pred:
                            ok = False; break
                    if not ok: break
                if not ok:
                    continue
                # build new less on 0..k
                nl = [row[:]+[False] for row in less]
                nl.append([False]*(k+1))
                for j in pred:
                    nl[j][k] = True
                # transitive closure is automatic since pred is a down-set
                # check no antichain of size width_cap+1 involving k
                # (only need to check sets containing k; rest already ok)
                bad = False
                others = list(range(k))
                for S in combinations(others, width_cap):
                    Sk = S + (k,)
                    if all(not nl[a][b] and not nl[b][a]
                           for a,b in combinations(Sk,2)):
                        bad = True; break
                if bad:
                    continue
                rec(k+1, nl)
    rec(1, [[False]])
    return results

def run_E5(Kexhaust=12, Krandom=(20,30,45,65), rand_trials=4000,
           seed=4421):
    print("="*72)
    print("E5  SINGLETON-BAND irreducible width-3 w<=4 posets, UNBOUNDED K")
    print("    (= mg-4d7b cap-1 regime, run unbounded; mg-4d7b only did |Q|<=10)")
    print("="*72)
    rng = random.Random(seed)
    hardest = None          # (edge_gap_of_best, K, descr)  -- want it 0
    closest_inside = None   # in-class poset whose best pair is nearest an edge
    total_inclass = 0
    total_ce = 0
    # ---- exhaustive small K ----
    for K in range(6, Kexhaust+1):
        cnt = 0; ce = 0
        for w in (1,2,3,4):
            for less in enum_singleton_band(K, w):
                if is_chain(K, less):       continue
                if not is_irreducible(K, less, list(range(1,K+1)), K):
                    continue
                if has_twin(K, less):       continue
                cnt += 1; total_inclass += 1
                has, best, gap, prob = best_balanced(K, less)
                if not has:
                    ce += 1; total_ce += 1
                    print(f"   *** COUNTEREXAMPLE K={K} w={w} less="
                          f"{[(i,j) for i in range(K) for j in range(K) if less[i][j]]}")
                # track best pair's margin
                bx,by,bp = best
                marg = balance_margin(bp)
                if closest_inside is None or marg < closest_inside[0]:
                    closest_inside = (marg, K, w, (bx,by), bp)
        print(f"  K={K:2d}: in-class singleton-band posets={cnt:6d}"
              f"  counterexamples={ce}")
    # ---- random large K ----
    print(f"  -- random sampling at large K --")
    for K in Krandom:
        cnt = 0; ce = 0
        for t in range(rand_trials):
            w = rng.randint(1,4)
            # build a random singleton-band poset of K bands
            less = [[False]*K for _ in range(K)]
            ok = True
            for k in range(K):
                forced = [j for j in range(k) if k-j>w]
                free   = [j for j in range(k) if 1<=k-j<=w]
                pred = set(forced)
                for j in free:
                    if rng.random() < rng.choice([0.3,0.45,0.6]):
                        pred.add(j)
                # close downward
                changed = True
                while changed:
                    changed = False
                    for j in list(pred):
                        for j2 in range(K):
                            if less[j2][j] and j2 not in pred:
                                pred.add(j2); changed=True
                for j in pred:
                    less[j][k] = True
                # quick width prune involving k
                bad=False
                for S in combinations(range(k),3):
                    Sk=S+(k,)
                    if all(not less[a][b] and not less[b][a]
                           for a,b in combinations(Sk,2)):
                        bad=True;break
                if bad:
                    ok=False;break
            if not ok:
                continue
            if not is_valid_poset(K,less):      continue
            if not width_at_most(K,less,3):     continue
            if is_chain(K,less):                continue
            if not is_irreducible(K,less,list(range(1,K+1)),K): continue
            if has_twin(K,less):                continue
            cnt += 1; total_inclass += 1
            has, best, gap, prob = best_balanced(K,less)
            bx,by,bp = best
            marg = balance_margin(bp)
            if closest_inside is None or marg < closest_inside[0]:
                closest_inside = (marg, K, w, (bx,by), bp)
            if not has:
                ce += 1; total_ce += 1
                print(f"   *** COUNTEREXAMPLE K={K} w={w}")
        print(f"  K={K:2d} (random {rand_trials}): in-class={cnt:5d}"
              f"  counterexamples={ce}")
    print(f"  TOTAL in-class singleton-band posets tested: {total_inclass}")
    print(f"  TOTAL counterexamples: {total_ce}")
    if closest_inside:
        marg,K,w,pair,bp = closest_inside
        print(f"  closest-to-edge in-class poset: K={K} w={w} best pair {pair}"
              f"  p={bp} (~{float(bp):.5f})  margin-inside-[1/3,2/3]="
              f"{marg} (~{float(marg):.5f})")
    return total_ce == 0

# ===========================================================================
#  E7 : homogeneous / periodic layered posets at very large K
# ===========================================================================

def run_E7():
    print("="*72)
    print("E7  homogeneous periodic layered posets, very large K")
    print("    (boundary advantage minimised -> isolates the bulk)")
    print("="*72)
    ok = True
    # G1: P_K itself but very large -- confirm asymptotics
    # G2: period-2 pattern: i<j iff j-i>2, plus j-i==2 when band parity matches
    # G3: 'every other near-edge present'
    families = []
    def g_PK(K):
        return transitive_closure(K,[(i,j) for i in range(K) for j in range(K) if j-i>2])
    def g_per2(K):
        e=[]
        for i in range(K):
            for j in range(K):
                if j-i>2: e.append((i,j))
                elif j-i==2 and (i%2==0): e.append((i,j))
        return transitive_closure(K,e)
    def g_per3(K):
        e=[]
        for i in range(K):
            for j in range(K):
                if j-i>2: e.append((i,j))
                elif j-i==2 and (i%3!=0): e.append((i,j))
        return transitive_closure(K,e)
    families=[("P_K", g_PK),("period-2 dist2", g_per2),("period-3 dist2", g_per3)]
    for name,gen in families:
        bad=[]
        line=[]
        for K in (60,120,200):
            less=gen(K)
            if not is_valid_poset(K,less):  line.append(f"K={K}:invalid"); continue
            if not width_at_most(K,less,3): line.append(f"K={K}:width>3"); continue
            if is_chain(K,less):            line.append(f"K={K}:chain"); continue
            tw=has_twin(K,less)
            has,best,gap,prob=best_balanced(K,less)
            bx,by,bp=best
            line.append(f"K={K}:best p~{float(bp):.5f}{' TWIN' if tw else ''}"
                        f"{' **CE**' if not has else ''}")
            if not has and not tw:
                bad.append(K)
        print(f"  {name:18s}: " + "  ".join(line))
        ok &= (not bad)
    return ok

# ===========================================================================
if __name__=="__main__":
    t0=time.time()
    r5=run_E5()
    r7=run_E7()
    print("="*72)
    print(f"DEEP SUMMARY  E5={'PASS' if r5 else 'FAIL'}  E7={'PASS' if r7 else 'FAIL'}")
    print(f"  {'NO COUNTEREXAMPLE FOUND' if (r5 and r7) else 'COUNTEREXAMPLE(S) FOUND'}")
    print(f"  elapsed: {time.time()-t0:.1f}s")
