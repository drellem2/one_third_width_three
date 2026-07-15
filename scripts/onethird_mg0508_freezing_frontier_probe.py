#!/usr/bin/env python3
"""mg-0508: OneThird L1b (B) ANY-WIDTH -- the FREEZING FRONTIER for deep displacement tails.

Predecessor mg-a7c5 reduced (B) LOCALITY, WIDTH-FREE, to the exact iff

    (B)  <=>  Sum_x E[disp^2]  =  O( Sum_x E[|disp|] )   =  O(E[inv_e]),        (*)

and named the single residual: is a *deep block-cross* -- an element x whose displacement
reaches PAST a long incomparable chain with Theta(1) probability -- realizable under the
whole-poset frozen hypothesis (H): every incomparable pair {a,b}, a<_e b, has
Pr[b before a] < 1/3, i.e. balance(a,b) := min(Pr[a<b],Pr[b<a]) < 1/3 for EVERY inc pair.

a7c5 (and mg-9de3) reported that every *directed* block-cross construction was PINNED at
worst-pair balance >= 0.357 > 1/3 -- freezing appears to forbid the deep tail.  This probe
tests that claim GLOBALLY and at WIDTH > 3, quantitatively:

  For a poset P let
      Bworst(P) = max over incomparable pairs of balance     (LEAST frozen pair; (H) <=> Bworst<1/3)
      R(P)      = E[Sum_x disp^2] / E[inv_e]                  (the (B) ratio in (*))
      deeptail  = max over (x, incomparable chain C, |C|=p) of  p^2 * Pr[x after ALL of C] / E[inv]
                                                             (single-element block-cross badness)

The (B)=TRUE prediction: pushing R (or deeptail) UP forces Bworst UP toward/above ~0.357 --
you cannot manufacture a deep tail without UN-freezing some pair.  A refutation (RED) would be
a family with R -> infinity (grows with n) while Bworst stays < 1/3.

Method: (1) random poset search at width >=4 recording the (Bworst, R) Pareto frontier;
        (2) a STRUCTURED block-cross family (element x below a chain, with ballast biasing x
            early) hill-climbed to MINIMIZE Bworst while KEEPING a deep tail, across growing
            chain length p -- the direct test of "can the tail survive as p grows while frozen".

Exact rational LE enumeration.  Reuses the mg-b0a6 Poset engine byte-for-byte."""
import sys, itertools, random
from fractions import Fraction
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp


# --------------------------------------------------------------------------- observables
def ensemble_stats(P):
    """Exact E[Sum disp^2], E[inv], R over uniform LE(P). e = identity labels."""
    les = P.linear_extensions()
    N = len(les)
    tot_s2 = tot_inv = 0
    for perm in les:
        pos = [0] * P.n
        for a, el in enumerate(perm):
            pos[el] = a
        tot_s2 += sum((pos[x] - x) ** 2 for x in range(P.n))
        tot_inv += sum(1 for a in range(P.n) for b in range(a + 1, P.n) if pos[a] > pos[b])
    R = Fraction(tot_s2, tot_inv) if tot_inv else Fraction(0)
    return Fraction(tot_s2, N), Fraction(tot_inv, N), R, N


def worst_balance(P):
    """Bworst = max over incomparable pairs of min(Pr[a<b],Pr[b<a]).  (H) <=> Bworst < 1/3."""
    worst = Fraction(0)
    worst_pair = None
    for (a, b) in P.incomparable_pairs():
        p = before_prob_dp(P, a, b)          # Pr[a before b]
        bal = min(p, 1 - p)
        if bal > worst:
            worst, worst_pair = bal, (a, b, float(p))
    return worst, worst_pair


def deep_tail(P, Einv):
    """max over (x, incomparable chain C) of  p^2 * Pr[x after all of C] / E[inv].
    Uses exact enumeration for the joint 'x after all of C' probability."""
    les = P.linear_extensions()
    N = len(les)
    best = Fraction(0)
    best_info = None
    for x in range(P.n):
        inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
        # maximal incomparable chains through inc (greedy over subsets up to size 5)
        for r in range(2, min(len(inc), 5) + 1):
            for sub in itertools.combinations(inc, r):
                if not all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                    continue
                cnt = 0
                for perm in les:
                    pos = {e: i for i, e in enumerate(perm)}
                    if all(pos[c] < pos[x] for c in sub):   # every chain elt before x => x after all
                        cnt += 1
                tail = Fraction(cnt, N)
                val = Fraction(r * r, 1) * tail / Einv if Einv else Fraction(0)
                if val > best:
                    best = val
                    best_info = (x, tuple(sorted(sub)), float(tail), r)
    return best, best_info


def width(P):
    els = list(range(P.n))
    for r in range(P.n, 0, -1):
        for sub in itertools.combinations(els, r):
            if all(not P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                return r
    return 1


def random_poset(n, pr, rng):
    order = list(range(n)); rng.shuffle(order); pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < pr:
                pairs.append((order[i], order[j]))
    P0 = Poset(n, pairs)
    order2, placed = [], set()
    while len(order2) < n:
        for e in range(n):
            if e in placed:
                continue
            if all(pp in placed for pp in P0.less[e]):
                order2.append(e); placed.add(e); break
    relabel = {old: new for new, old in enumerate(order2)}
    return [(relabel[a], relabel[b]) for a, b in pairs], relabel


# --------------------------------------------------------------------------- [1] frontier
def frontier_search(trials=9000, seed=1, min_width=4, nmax=8):
    """Random posets width>=min_width; record the (Bworst, R) Pareto frontier and the global
    minimum Bworst seen at each R-band."""
    rng = random.Random(seed)
    # bucket by R rounded down to integer; track min Bworst achieving R>=band
    best_lowfreeze = []      # list of (Bworst, R, n, width) with small Bworst and notable R
    global_min_bworst = Fraction(1)
    max_R = Fraction(0)
    max_R_at_lowfreeze = Fraction(0)   # max R seen among posets with Bworst < 0.40
    frontier = {}            # R_band -> min Bworst
    seen = 0
    for t in range(trials):
        if t % 1500 == 0:
            print(f"    ...trial {t}/{trials} (examined={seen}, "
                  f"min_Bworst={float(global_min_bworst):.4f})", flush=True)
        n = rng.randint(min_width + 1, nmax)
        pairs, _ = random_poset(n, rng.choice([0.15, 0.2, 0.28, 0.35]), rng)
        P = Poset(n, pairs)
        lc = P.linext_count()
        if lc == 0 or lc > 25000:
            continue
        if not P.incomparable_pairs():
            continue
        if width(P) < min_width:
            continue
        seen += 1
        Bw, wp = worst_balance(P)
        _, Einv, R, N = ensemble_stats(P)
        global_min_bworst = min(global_min_bworst, Bw)
        max_R = max(max_R, R)
        if Bw < Fraction(2, 5):     # < 0.40, "nearly frozen"
            max_R_at_lowfreeze = max(max_R_at_lowfreeze, R)
            if R > Fraction(9, 2):  # notable ratio while nearly frozen
                best_lowfreeze.append((float(Bw), float(R), n, width(P)))
        band = int(R)              # floor
        if band not in frontier or Bw < frontier[band]:
            frontier[band] = Bw
    print(f"[1] random width>={min_width} frontier: examined={seen}  "
          f"global_min_Bworst={float(global_min_bworst):.4f}  max_R={float(max_R):.3f}  "
          f"max_R among Bworst<0.40 = {float(max_R_at_lowfreeze):.3f}")
    print("    Pareto: min Bworst achieving each R-band  (want: higher R forces higher Bworst):")
    for band in sorted(frontier):
        print(f"       R>={band}: min Bworst = {float(frontier[band]):.4f}")
    best_lowfreeze.sort(key=lambda t: (t[0], -t[1]))
    print("    nearly-frozen (Bworst<0.40) posets with R>4.5 (Bworst, R, n, width):")
    for t in best_lowfreeze[:8]:
        print(f"       Bworst={t[0]:.4f}  R={t[1]:.3f}  n={t[2]}  width={t[3]}")
    return global_min_bworst, max_R_at_lowfreeze


# --------------------------------------------------------------------------- [2] structured
def block_cross_family(p_values=(2, 3, 4), seed=7, iters=3000):
    """STRUCTURED test: element x incomparable to a length-p chain C, plus 'ballast' elements
    that we (hill-climb) wire to bias x early (make x-before-C likely) WITHOUT unfreezing.
    Report, for each p, the SMALLEST worst-pair balance achievable while keeping a deep tail
    Pr[x after all of C] >= 0.10.  Prediction (B=TRUE): min Bworst stays >~0.357 and does NOT
    fall to 1/3 as p grows."""
    rng = random.Random(seed)
    print("[2] structured block-cross family: min Bworst subject to Pr[x after chain]>=0.10")
    print("    (x incomparable to length-p chain; ballast hill-climbed; want tail deep+frozen)")
    for p in p_values:
        print(f"    (searching p={p}...)", flush=True)
        # base: chain c_0<..<c_{p-1}; x isolated; b ballast elements below the chain (predecessors
        # of c_0) that x is ALSO below -> biases x and chain apart but x stays incomparable to C.
        best = None
        for _ in range(iters):
            b = rng.randint(1, 4)                 # ballast count
            n = p + 1 + b
            # labels: 0..b-1 ballast, b = x, b+1..b+p = chain c_0..c_{p-1}
            chain = list(range(b + 1, b + 1 + p))
            x = b
            ballast = list(range(b))
            pairs = []
            for i in range(p - 1):                # chain
                pairs.append((chain[i], chain[i + 1]))
            # ballast below chain start, and random extra relations to bias x
            for u in ballast:
                if rng.random() < 0.8:
                    pairs.append((u, chain[0]))   # ballast precedes chain
                if rng.random() < 0.5:
                    pairs.append((u, x))          # ballast precedes x  (keeps x early-ish)
                elif rng.random() < 0.5:
                    pairs.append((x, u))
            # occasionally let x sit below some chain top to bias, but that makes x,ci comparable
            P = Poset(n, pairs)
            # require x incomparable to every chain element
            if any(P.comparable(x, c) for c in chain):
                continue
            lc = P.linext_count()
            if lc == 0 or lc > 40000:
                continue
            # deep tail Pr[x after all chain]
            les = P.linear_extensions(); N = len(les)
            cnt = 0
            for perm in les:
                pos = {e: i for i, e in enumerate(perm)}
                if all(pos[c] < pos[x] for c in chain):
                    cnt += 1
            tail = Fraction(cnt, N)
            if tail < Fraction(1, 10):
                continue
            Bw, wp = worst_balance(P)
            if best is None or Bw < best[0]:
                best = (Bw, float(tail), n, wp)
        if best is None:
            print(f"    p={p}: no config with tail>=0.10 found in budget")
        else:
            Bw, tail, n, wp = best
            print(f"    p={p}: min Bworst = {float(Bw):.4f}   (deep tail Pr={tail:.3f}, n={n}, "
                  f"worst pair a<b Pr[a<b]={wp[2]:.3f})   frozen? {float(Bw) < 1/3}")


def check_nesting_identities(trials=4000, seed=3):
    """Verify the mg-0508 chain-nesting crystallization (§8.2) on exact LE ensembles:
    for x incomparable to a chain C = c_1<_P..<_P c_p, with q_i = Pr[c_i before x] and
    g = #{c_i before x}:  (a) q_i is DECREASING (nesting A_1 ⊇ .. ⊇ A_p);
    (b) E[g] = Σ q_i;  (c) E[g^2] = Σ (2i-1) q_i;  (d) Pr[x after whole chain] = q_p."""
    rng = random.Random(seed)
    bad = checked = 0
    for _ in range(trials):
        n = rng.randint(4, 7)
        pairs, _ = random_poset(n, rng.choice([0.2, 0.3]), rng)
        P = Poset(n, pairs)
        lc = P.linext_count()
        if lc == 0 or lc > 20000:
            continue
        les = P.linear_extensions(); N = len(les)
        for x in range(n):
            inc = [y for y in range(n) if y != x and not P.comparable(x, y)]
            for r in range(2, min(len(inc), 4) + 1):
                for sub in itertools.combinations(inc, r):
                    if not all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                        continue
                    C = sorted(sub, key=lambda z: len(P.less[z]))       # chain bottom -> top
                    if not all(C[i] in P.less[C[i + 1]] for i in range(len(C) - 1)):
                        continue
                    p = len(C)
                    qs = [0] * (p + 1); gcnt = {}; deep = 0
                    for perm in les:
                        pos = {e: i for i, e in enumerate(perm)}
                        g = sum(1 for c in C if pos[c] < pos[x])
                        gcnt[g] = gcnt.get(g, 0) + 1
                        for i in range(1, p + 1):
                            if pos[C[i - 1]] < pos[x]:
                                qs[i] += 1
                        if g == p:
                            deep += 1
                    q = [Fraction(qs[i], N) for i in range(p + 1)]
                    Eg = sum(Fraction(g * c, N) for g, c in gcnt.items())
                    Eg2 = sum(Fraction(g * g * c, N) for g, c in gcnt.items())
                    ok = (all(q[i] >= q[i + 1] for i in range(1, p)) and
                          Eg == sum(q[1:]) and
                          Eg2 == sum((2 * i - 1) * q[i] for i in range(1, p + 1)) and
                          Fraction(deep, N) == q[p])
                    checked += 1
                    if not ok:
                        bad += 1
    print(f"[0] chain-nesting identities (§8.2): checked={checked}  violations={bad}")
    return bad == 0


def main():
    ok0 = check_nesting_identities()
    print()
    gm, mrl = frontier_search()
    print()
    block_cross_family()
    print()
    print("READ: (B)=TRUE prediction is that deep tails (large R / deep block-cross) cannot be")
    print("achieved while Bworst<1/3.  A RED refutation would show R growing with n at Bworst<1/3.")
    print(f"This run's global min Bworst over width>=4 search = {float(gm):.4f} "
          f"(> 1/3 = {float(gm) > 1/3}); max R among nearly-frozen (Bworst<0.40) = {float(mrl):.3f}.")


if __name__ == "__main__":
    main()
