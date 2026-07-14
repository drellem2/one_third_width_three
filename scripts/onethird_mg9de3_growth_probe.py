#!/usr/bin/env python3
"""mg-9de3: THE decisive diagnostic. mg-2acf reported max chain-frozen ratio E[S^2]/E|S|=2.0
at n<=8. My broader search finds 2.91 at n<=11 -- the ratio GROWS with n. (B) LOCALITY holds
iff this ratio is O(1); it fails (block-cross realizable) iff it -> infinity. So the single
decisive number is the GROWTH CURVE: max chain-frozen ratio as a function of n (and chain
length p). This probe buckets by n, records the actual poset achieving each bucket max (so it
can be hand-scaled), and reports the (n, maxratio, p, poset) trajectory.

chain-frozen = every pair {x,c_i} has min(Pr[c_i<x],Pr[x<c_i]) < 1/3. Exact; fast O(2^n) DP."""
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


def chains_in_incset(P, x, maxlen=8):
    inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
    out = []
    for r in range(2, min(len(inc), maxlen) + 1):
        for sub in itertools.combinations(inc, r):
            if all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                out.append(tuple(sorted(sub, key=lambda z: len([w for w in sub if w in P.less[z]]))))
    return out


def ratio_of(P, x, chain, base, tot):
    p = len(chain)
    biases = [before_prob_dp(P, c, x) for c in chain]
    cdelta = max(min(b, 1 - b) for b in biases)
    if cdelta >= Fraction(1, 3):
        return None
    a = []
    for m in range(p + 1):
        extra = [(chain[i], x) for i in range(m)] + [(x, chain[i]) for i in range(m, p)]
        Pm = Poset(P.n, base + extra)
        a.append(Fraction(Pm.linext_count(), tot))
    j = sum(1 for b in biases if b > Fraction(1, 2))
    ES2 = sum((m - j) ** 2 * a[m] for m in range(p + 1))
    Eabs = sum(abs(m - j) * a[m] for m in range(p + 1))
    if Eabs == 0:
        return None
    return float(ES2 / Eabs), cdelta, a, j


def random_poset(n, pr, rng):
    order = list(range(n)); rng.shuffle(order); pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < pr:
                pairs.append((order[i], order[j]))
    return pairs, Poset(n, pairs)


def main():
    rng = random.Random(2027)
    best = {}   # n -> (ratio, p, cdelta, a, pairs, x, chain)
    trials = 400000
    for t in range(trials):
        n = rng.randint(6, 13)
        pairs, P = random_poset(n, rng.choice([0.14, 0.2, 0.26, 0.34]), rng)
        lc = P.linext_count()
        if lc == 0 or lc > 500000:
            continue
        if width(P) > 3:
            continue
        base = [(a, e) for e in range(P.n) for a in P.less[e]]
        for x in range(n):
            for chain in chains_in_incset(P, x):
                r = ratio_of(P, x, chain, base, lc)
                if r is None:
                    continue
                ratio, cdelta, a, j = r
                cur = best.get(n)
                if cur is None or ratio > cur[0]:
                    best[n] = (ratio, len(chain), float(cdelta), [float(v) for v in a], pairs, x, chain)
    print(f"trials={trials}")
    print("GROWTH CURVE: max chain-frozen ratio E[S^2]/E|S| by n")
    print(" n | maxratio | p  | cdelta | slot a (rounded)")
    for n in sorted(best):
        ratio, p, cd, a, pairs, x, chain = best[n]
        print(" %2d | %7.4f | %2d | %.4f | %s" % (n, ratio, p, cd, [round(v, 3) for v in a]))
    # print the best overall poset for hand-scaling
    if best:
        nbest = max(best, key=lambda n: best[n][0])
        ratio, p, cd, a, pairs, x, chain = best[nbest]
        print(f"\nBEST OVERALL: n={nbest} ratio={ratio:.4f} p={p} cdelta={cd:.4f} x={x} chain={chain}")
        print(f"  poset pairs (a<b): {sorted(pairs)}")
        print(f"  slot a = {[round(v,4) for v in a]}")


if __name__ == "__main__":
    main()
