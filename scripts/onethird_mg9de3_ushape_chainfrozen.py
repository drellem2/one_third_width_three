#!/usr/bin/env python3
"""mg-9de3: REFINED crux probe. The mg-2acf per-chain reduction needs E[S_C^2]=O(E|S_C|)
for chains C whose pairs {x,c_i} are all frozen (per-pair delta<1/3). That CHAIN-frozen
notion is far more common than whole-poset delta<1/3 (my first probe found ~0 whole-frozen
posets, so it was near-vacuous). Here I:
  (1) count chain-frozen configs actually seen (sanity: non-vacuous),
  (2) among them, find any with U-SHAPED slot dist a (block-cross seed) or ratio>2.5,
  (3) measure the TRADEOFF: minimum chain-delta achievable as a function of U-depth and of
      ratio -- does deep-U / high-ratio force chain-delta up toward/above 1/3?

A clean law 'genuine interior dip (U-shape) forces chain-delta >= 1/3' would essentially
PROVE (B). Exact rationals; fast O(2^n) DP; n up to ~11."""
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


def chains_in_incset(P, x, maxlen=6):
    inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
    out = []
    for r in range(2, min(len(inc), maxlen) + 1):
        for sub in itertools.combinations(inc, r):
            if all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                out.append(tuple(sorted(sub, key=lambda z: len([w for w in sub if w in P.less[z]]))))
    return out


def slot_dist_and_biases(P, x, chain):
    """a_m=Pr[slot=m] via e(P_m); biases t: Pr[c_i before x]. Returns (a, biases)."""
    p = len(chain)
    base = [(a, e) for e in range(P.n) for a in P.less[e]]
    tot = P.linext_count()
    a = []
    for m in range(p + 1):
        extra = [(chain[i], x) for i in range(m)] + [(x, chain[i]) for i in range(m, p)]
        Pm = Poset(P.n, base + extra)
        a.append(Fraction(Pm.linext_count(), tot))
    biases = [before_prob_dp(P, c, x) for c in chain]   # Pr[c_i before x]
    return a, biases


def analyze(P, x, chain):
    a, biases = slot_dist_and_biases(P, x, chain)
    p = len(chain)
    # chain-delta = max over chain pairs of min(Pr[c<x],Pr[x<c])
    cdelta = max(min(b, 1 - b) for b in biases)
    # j = # chain elts with bias>1/2 (tend before x => e-below x)
    j = sum(1 for b in biases if b > Fraction(1, 2))
    ES = sum((m - j) * a[m] for m in range(p + 1))
    ES2 = sum((m - j) ** 2 * a[m] for m in range(p + 1))
    Eabs = sum(abs(m - j) * a[m] for m in range(p + 1))
    ratio = ES2 / Eabs if Eabs > 0 else Fraction(0)
    interior_min = min(a[1:p]) if p >= 2 else a[0]
    isU = p >= 2 and interior_min < a[0] and interior_min < a[p]
    depth = interior_min / min(a[0], a[p]) if min(a[0], a[p]) > 0 else Fraction(1)
    return dict(cdelta=cdelta, ratio=ratio, isU=isU, depth=depth, a=a, p=p, j=j)


def random_poset(n, pr, rng):
    order = list(range(n)); rng.shuffle(order); pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < pr:
                pairs.append((order[i], order[j]))
    return Poset(n, pairs)


def main():
    rng = random.Random(11)
    n_chainfrozen = 0
    frozen_U = []                 # chain-frozen AND U-shaped
    frozen_hi = []                # chain-frozen AND ratio>2.5
    minratio_by_none = 0.0
    max_ratio_frozen = Fraction(0)
    # tradeoff: for each U-shaped config (any delta), record (depth, cdelta)
    U_tradeoff = []
    trials = 150000
    for t in range(trials):
        n = rng.randint(5, 11)
        P = random_poset(n, rng.choice([0.15, 0.22, 0.3, 0.38]), rng)
        lc = P.linext_count()
        if lc == 0 or lc > 300000:
            continue
        if width(P) > 3:
            continue
        for x in range(n):
            for chain in chains_in_incset(P, x):
                r = analyze(P, x, chain)
                chain_frozen = r['cdelta'] < Fraction(1, 3)
                if r['isU']:
                    U_tradeoff.append((float(r['depth']), float(r['cdelta']), r['p']))
                if chain_frozen:
                    n_chainfrozen += 1
                    if r['ratio'] > max_ratio_frozen:
                        max_ratio_frozen = r['ratio']
                    if r['isU']:
                        frozen_U.append((float(r['depth']), float(r['cdelta']), r['p'], [float(v) for v in r['a']]))
                    if r['ratio'] > Fraction(5, 2):
                        frozen_hi.append((float(r['ratio']), float(r['cdelta']), r['p'], [float(v) for v in r['a']]))
    print(f"trials={trials}")
    print(f"chain-frozen configs seen (NON-VACUOUS check): {n_chainfrozen}")
    print(f"MAX ratio E[S^2]/E|S| over chain-frozen configs: {float(max_ratio_frozen):.4f}")
    print(f"chain-frozen AND U-shaped slot dist: {len(frozen_U)}")
    for r in sorted(frozen_U)[:10]:
        print("   depth=%.4f cdelta=%.4f p=%d a=%s" % (r[0], r[1], r[2], [round(v,3) for v in r[3]]))
    print(f"chain-frozen AND ratio>2.5: {len(frozen_hi)}")
    for r in sorted(frozen_hi, reverse=True)[:10]:
        print("   ratio=%.4f cdelta=%.4f p=%d a=%s" % (r[0], r[1], r[2], [round(v,3) for v in r[3]]))
    # tradeoff: min cdelta as a function of U-depth bucket
    print("\nTRADEOFF  U-depth-bucket -> min chain-delta observed (depth smaller = deeper U):")
    buckets = [(0.0,0.3),(0.3,0.5),(0.5,0.7),(0.7,0.85),(0.85,1.0)]
    for lo,hi in buckets:
        ds = [cd for (dp,cd,pp) in U_tradeoff if lo <= dp < hi]
        if ds:
            print(f"   depth in [{lo:.2f},{hi:.2f}): count={len(ds):6d}  min chain-delta={min(ds):.4f}")
        else:
            print(f"   depth in [{lo:.2f},{hi:.2f}): count=0")
    # overall min chain-delta among ALL U-shapes
    if U_tradeoff:
        print("MIN chain-delta over ALL U-shaped configs: %.4f  (if >1/3=0.3333, U-shape excludes frozen)"
              % min(cd for (dp,cd,pp) in U_tradeoff))


if __name__ == "__main__":
    main()
