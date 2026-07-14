#!/usr/bin/env python3
"""mg-9de3: LARGE-n block-cross hunt for FROZEN width-3 posets.

Goal: refute (or support) that a FROZEN (delta<1/3) width-3 poset can have an
element x + incomparable chain C with RATIO = E[S^2]/E|S| growing with p (the
"block-cross" slot distribution ~ [1-c,0,...,0,c], ratio ~ p).

Uses the FAST O(2^n) linext DP (Poset.linext_count) so we reach n=12..22, well
past the old n<=9 brute ceiling. Slot distribution computed exactly via augmented
posets; delta computed exactly via before_prob_dp on ALL incomparable pairs.
"""
import sys, itertools
from fractions import Fraction
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp


def base_pairs(P):
    return [(a, e) for e in range(P.n) for a in P.less[e]]


def width(P):
    """Largest antichain size (exact, via max independent set in comparability
    graph). For width<=3 checking we only need to confirm no antichain of size 4."""
    n = P.n
    inc = [[y for y in range(n) if y != x and not P.comparable(x, y)] for x in range(n)]
    # find max antichain by growing cliques in incomparability graph
    best = 1
    # iterative deepening: check antichains of size k
    def has_antichain(k):
        # backtracking
        def rec(start, chosen):
            if len(chosen) == k:
                return True
            for v in range(start, n):
                if all(v in [] or (not P.comparable(v, c)) for c in chosen):
                    # v incomparable to all chosen
                    if all(not P.comparable(v, c) for c in chosen):
                        if rec(v + 1, chosen + [v]):
                            return True
            return False
        return rec(0, [])
    k = 1
    while k <= n and has_antichain(k):
        best = k
        k += 1
    return best


def slot_distribution(P, x, chain):
    """chain: tuple of elements sorted ascending by P-order (c_1<...<c_p), all
    incomparable to x. Returns list a[0..p], a[m] = Pr[exactly m chain elts before x]."""
    p = len(chain)
    total = P.linext_count()
    bp = base_pairs(P)
    a = []
    for m in range(p + 1):
        added = [(chain[i], x) for i in range(m)] + [(x, chain[i]) for i in range(m, p)]
        try:
            Pm = Poset(P.n, bp + added)
            cnt = Pm.linext_count()
        except ValueError:
            cnt = 0
        a.append(Fraction(cnt, total))
    return a


def analyze(P, x, chain):
    """Return dict with slot dist, j, S-moments, ratio (uses reference j = #chain
    elts with Pr[c before x] > 1/2, matching mg-2acf convention)."""
    p = len(chain)
    a = slot_distribution(P, x, chain)
    # biases Pr[c before x]
    biases = [1 - before_prob_dp(P, x, c) for c in chain]  # before_prob_dp(P,x,c)=Pr[x before c]
    j = sum(1 for b in biases if b > Fraction(1, 2))
    ES = Fraction(0); ES2 = Fraction(0); Eabs = Fraction(0)
    for m in range(p + 1):
        s = m - j
        ES += s * a[m]
        ES2 += s * s * a[m]
        Eabs += abs(s) * a[m]
    ratio = float(ES2) / float(Eabs) if Eabs > 0 else 0.0
    return dict(a=[float(v) for v in a], af=a, j=j, ES=float(ES), ES2=float(ES2),
                Eabs=float(Eabs), ratio=ratio, biases=[float(b) for b in biases])


def full_delta(P):
    """max over ALL incomparable pairs of min(Pr[x before y], Pr[y before x])."""
    d = Fraction(0)
    worst = None
    for (x, y) in P.incomparable_pairs():
        pxy = before_prob_dp(P, x, y)
        m = min(pxy, 1 - pxy)
        if m > d:
            d = m; worst = (x, y, float(pxy))
    return float(d), worst


def report(name, P, x, chain, verbose=True):
    w = width(P)
    dlt, worst = full_delta(P)
    r = analyze(P, x, chain)
    frozen = dlt < 1/3 - 1e-12
    flag = ""
    if frozen and r['ratio'] > 2.5:
        flag = "  <<< FROZEN & ratio>2.5 !!!"
    elif frozen:
        flag = "  [frozen]"
    if verbose:
        print(f"[{name}] n={P.n} p={len(chain)} width={w} delta={dlt:.4f} "
              f"ratio={r['ratio']:.3f} j={r['j']} frozen={frozen}{flag}")
        print(f"    slot a = [{', '.join(f'{v:.3f}' for v in r['a'])}]")
        print(f"    x-vs-chain biases Pr[c<x] = [{', '.join(f'{b:.3f}' for b in r['biases'])}]  worst-pair delta={dlt:.4f} at {worst}")
    return dict(n=P.n, p=len(chain), width=w, delta=dlt, ratio=r['ratio'], frozen=frozen, a=r['a'])


# ============================================================
# GADGET FAMILIES
# ============================================================

def gadget_bare_chain(p):
    """x incomparable to chain c_1<...<c_p, nothing else. Baseline (uniform slot)."""
    # elements: 0..p-1 chain, p = x
    chain = tuple(range(p))
    pairs = [(i, i + 1) for i in range(p - 1)]
    P = Poset(p + 1, pairs)
    x = p
    return P, x, chain


def gadget_downup(p, d, u):
    """chain c_1<...<c_p. x has down-set of d elements below it and u above.
    The down/up sets are separate chains attached to x (not to C)."""
    # layout: chain 0..p-1; x = p; down elements p+1..p+d (each < x); up p+d+1..p+d+u (x<each)
    n = p + 1 + d + u
    chain = tuple(range(p))
    x = p
    pairs = [(i, i + 1) for i in range(p - 1)]
    down = list(range(p + 1, p + 1 + d))
    up = list(range(p + 1 + d, p + 1 + d + u))
    for e in down:
        pairs.append((e, x))
    for e in up:
        pairs.append((x, e))
    return P_from(n, pairs), x, chain


def P_from(n, pairs):
    return Poset(n, pairs)


if __name__ == "__main__":
    print("=== Baseline: bare incomparable chain (expect uniform, not frozen) ===")
    for p in (3, 5, 8, 12):
        P, x, chain = gadget_bare_chain(p)
        report("bare", P, x, chain)
    print()
    print("=== down/up glue: x pinned between a down-chain and up-chain ===")
    for p in (4, 6, 8):
        for (d, u) in [(2, 2), (3, 3)]:
            P, x, chain = gadget_downup(p, d, u)
            report(f"downup d={d} u={u}", P, x, chain)
