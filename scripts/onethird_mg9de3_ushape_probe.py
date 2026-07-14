#!/usr/bin/env python3
"""mg-9de3: crux sub-question. A block-cross needs the slot distribution a_m=Pr[slot=m]
to be U-SHAPED (bimodal: mass at m=0 and m=p, a dip in the middle). Note a_m=e(P_m)>0
ALWAYS (x incomparable to every chain elt => inserting x in any gap is consistent), so the
EXACT block-cross (middle=0) is impossible; the residual is whether the middle can be made
exponentially small while FROZEN (delta<1/3) in WIDTH 3.

This probe SEARCHES small posets for x + incomparable chain C whose slot dist a is U-shaped,
and reports the depth of the U (min interior a_m / min(a_0,a_p)) correlated with delta and
width. If deep U-shapes require delta>=1/3 (or width>3), that supports (B) LOCALITY.

Exact rationals; fast O(2^n) LE-count DP (no n! blowup) so we can go to n~13."""
import sys, itertools, random
from fractions import Fraction
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp


def width(P):
    els = list(range(P.n))
    for r in range(P.n, 0, -1):
        for sub in itertools.combinations(els, r):
            if all(not P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                return r
    return 1


def delta_of(P):
    d = Fraction(0)
    for x, y in P.incomparable_pairs():
        pxy = before_prob_dp(P, x, y)
        m = min(pxy, 1 - pxy)
        if m > d:
            d = m
    return d


def slot_dist(P, x, chain):
    p = len(chain)
    base = [(a, e) for e in range(P.n) for a in P.less[e]]
    tot = P.linext_count()
    a = []
    for m in range(p + 1):
        extra = [(chain[i], x) for i in range(m)] + [(x, chain[i]) for i in range(m, p)]
        Pm = Poset(P.n, base + extra)
        a.append(Fraction(Pm.linext_count(), tot))
    return a


def ushape_depth(a):
    """How U-shaped is a? interior min vs the smaller endpoint. depth<1 => dip exists.
    Return (depth, is_U). is_U requires an interior index strictly below both nbr-maxima."""
    p = len(a) - 1
    if p < 2:
        return Fraction(1), False
    interior_min = min(a[1:p])
    end = min(a[0], a[p])
    # a genuine U: some interior value < both a[0] and a[p]
    is_U = interior_min < a[0] and interior_min < a[p]
    depth = interior_min / end if end > 0 else Fraction(1)
    return depth, is_U


def chains_in_incset(P, x, maxlen=None):
    inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
    out = []
    for r in range(2, len(inc) + 1):
        if maxlen and r > maxlen:
            break
        for sub in itertools.combinations(inc, r):
            if all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                # order by P
                out.append(tuple(sorted(sub, key=lambda z: len([w for w in sub if w in P.less[z]]))))
    return out


def random_poset(n, pr, rng):
    order = list(range(n)); rng.shuffle(order); pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < pr:
                pairs.append((order[i], order[j]))
    return Poset(n, pairs)


def main():
    rng = random.Random(7)
    best_U = []          # deepest U shapes among width<=3
    best_U_frozen = []   # deepest U shapes among width<=3 AND frozen
    n_frozen_chains = 0
    trials = 200000
    for t in range(trials):
        n = rng.randint(5, 11)
        P = random_poset(n, rng.choice([0.18, 0.25, 0.32, 0.4]), rng)
        if P.linext_count() > 200000 or P.linext_count() == 0:
            continue
        if width(P) > 3:
            continue
        d = delta_of(P)
        frozen = d < Fraction(1, 3)
        for x in range(n):
            for chain in chains_in_incset(P, x, maxlen=6):
                a = slot_dist(P, x, chain)
                depth, isU = ushape_depth(a)
                if not isU:
                    continue
                rec = (float(depth), len(chain), float(d), n, [float(v) for v in a])
                best_U.append(rec)
                if frozen:
                    n_frozen_chains += 1
                    best_U_frozen.append(rec)
    best_U.sort(key=lambda r: r[0])          # smallest depth = deepest U
    best_U_frozen.sort(key=lambda r: r[0])
    print(f"trials={trials}")
    print(f"U-shaped slot dists found (width<=3, any delta): {len(best_U)}")
    print("DEEPEST U-shapes (depth=interior_min/endpoint; smaller=deeper), width<=3:")
    for r in best_U[:12]:
        print("  depth=%.4f p=%d delta=%.4f n=%d a=%s" % (r[0], r[1], r[2], r[3], [round(v,3) for v in r[4]]))
    print(f"\nU-shaped AND FROZEN (delta<1/3): {len(best_U_frozen)}")
    for r in best_U_frozen[:12]:
        print("  depth=%.4f p=%d delta=%.4f n=%d a=%s" % (r[0], r[1], r[2], r[3], [round(v,3) for v in r[4]]))
    if best_U_frozen:
        print("MIN depth among frozen U-shapes: %.4f  (deep U + frozen => block-cross seed)" % best_U_frozen[0][0])
    else:
        print("NO frozen (delta<1/3) width-3 U-shaped slot distribution found "
              "=> block-cross seed absent in reach (supports (B)).")


if __name__ == "__main__":
    main()
