#!/usr/bin/env python3
"""mg-9de3: directed p-scaling. The growth probe (random search) caps chain length at p<=5
(reachable n). The residual asks the ASYMPTOTIC ratio-vs-p for FROZEN width-3. Here I build
DIRECTED gadgets that push p to 8..14 while trying to keep whole-poset delta<1/3, and read
off ratio(p). If ratio keeps climbing ~linearly in p -> block-cross realizable ((B) FALSE).
If ratio saturates -> (B) holds.

Mechanism (from the n=13 winner a~[.023,.045,.068,.068,.081,.715]): x sits frozen just above
a chain c_1<..<c_p (x after all c_i most of the time), with a fat lower tail where top chain
elements occasionally escape past x. To create that escape while freezing, use a shared floor
below {x, chain} and 'coupler' elements that let chain-tops jump. All width<=3.

Exact; fast O(2^n) DP; whole-poset delta over ALL incomparable pairs (the strict H)."""
import sys, itertools
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


def full_delta(P):
    d = Fraction(0); wp = None
    for u, v in P.incomparable_pairs():
        puv = before_prob_dp(P, u, v)
        m = min(puv, 1 - puv)
        if m > d:
            d = m; wp = (u, v)
    return d, wp


def analyze(P, x, chain):
    p = len(chain)
    base = [(a, e) for e in range(P.n) for a in P.less[e]]
    tot = P.linext_count()
    a = []
    for m in range(p + 1):
        extra = [(chain[i], x) for i in range(m)] + [(x, chain[i]) for i in range(m, p)]
        Pm = Poset(P.n, base + extra)
        a.append(Fraction(Pm.linext_count(), tot))
    biases = [before_prob_dp(P, c, x) for c in chain]
    j = sum(1 for b in biases if b > Fraction(1, 2))
    ES2 = sum((m - j) ** 2 * a[m] for m in range(p + 1))
    Eabs = sum(abs(m - j) * a[m] for m in range(p + 1))
    cdelta = max(min(b, 1 - b) for b in biases)
    ratio = float(ES2 / Eabs) if Eabs > 0 else 0.0
    return ratio, [float(v) for v in a], j, float(cdelta)


def gA(p, ncoup):
    """floor F0 below everything; chain c_1<..<c_p; x above F0, below top-lid Ltop and below
    each coupler; couplers b_1..b_k each above chain-mid+ and below Ltop, incomparable to x,
    giving chain-tops a route to sit after x. Kept width<=3 by chaining couplers."""
    idx = 0
    def nw():
        nonlocal idx; v = idx; idx += 1; return v
    f = nw()
    x = nw()
    C = [nw() for _ in range(p)]
    Bs = [nw() for _ in range(ncoup)]
    ltop = nw()
    n = idx
    pairs = [(C[i], C[i + 1]) for i in range(p - 1)]
    pairs += [(f, x), (f, C[0])]
    pairs += [(x, ltop), (C[-1], ltop)]
    # couplers form a chain among themselves, each below ltop, above a chain elt (spread)
    for t, b in enumerate(Bs):
        anchor = C[min(p - 1, (t + 1) * p // (ncoup + 1))]
        pairs += [(anchor, b), (b, ltop)]
        if t > 0:
            pairs += [(Bs[t - 1], b)]
    P = Poset(n, pairs)
    return P, x, tuple(C)


def main():
    print("=== gadget A (frozen-above chain + coupler stack), scaling p ===")
    for ncoup in [1, 2, 3]:
        print(f"-- ncoup={ncoup} --")
        for p in [4, 6, 8, 10, 12]:
            P, x, C = gA(p, ncoup)
            if P.n > 23:
                continue
            w = width(P)
            d, wp = full_delta(P)
            ratio, a, j, cd = analyze(P, x, C)
            fr = d < Fraction(1, 3)
            tag = "  <<<FROZEN" + ("+HI" if ratio > 2.5 else "") if fr else ""
            print(f"  p={p:2d} n={P.n} w={w} delta={float(d):.4f} chaindelta={cd:.4f} "
                  f"ratio={ratio:.3f} j={j} frozen={fr}{tag}")
            print(f"      a={[round(v,3) for v in a]} worst={wp}")
    print("\n=== gadget B (frozen-below chain), scaling p ===")
    for p in [4, 6, 8, 10, 12]:
        P, x, C = gB(p)
        w = width(P)
        d, wp = full_delta(P)
        ratio, a, j, cd = analyze(P, x, C)
        fr = d < Fraction(1, 3)
        print(f"  p={p:2d} n={P.n} w={w} delta={float(d):.4f} chaindelta={cd:.4f} "
              f"ratio={ratio:.3f} j={j} frozen={fr}")


if __name__ == "__main__":
    main()
