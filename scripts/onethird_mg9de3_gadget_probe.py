#!/usr/bin/env python3
"""mg-9de3: my own targeted gadget probe for the L1b (B)-wall residual.

Residual (mg-2acf): is a *block-cross* realizable in a FROZEN (delta<1/3) width-3 poset?
A block-cross of a length-p chain C incomparable to x has slot distribution ~ [1-c,0,..,0,c]
and ratio E[S^2]/E|S| ~ p (>> 2). The conjecture (=> (B) => L1b) is NO: frozen+width3 forces
ratio = O(1). Prior small-n search stuck at delta>=0.357. I use the FAST O(2^n) LE-count DP
(before_prob_dp / linext_count) to reach n up to ~20 and test analytic gadget families:
does min delta over block-crossing configs stay above 1/3 as p grows?

Everything is EXACT (Fractions). delta = max over incomparable pairs of min(p, 1-p)."""
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


def delta_of(P):
    """max over incomparable pairs of min(Pr[a<b],Pr[b<a]); returns (delta, worstpair)."""
    d = Fraction(0); wp = None
    for x, y in P.incomparable_pairs():
        pxy = before_prob_dp(P, x, y)
        m = min(pxy, 1 - pxy)
        if m > d:
            d = m; wp = (x, y)
    return d, wp


def slot_stats(P, x, chain):
    """chain = tuple c_1<..<c_p (P-increasing) all incomparable to x. Return
    (ratio E[S^2]/E|S|, a-distribution, j, E|S|, ES2). a_m = e(P + c_1<x..c_m<x, x<c_{m+1}..)."""
    p = len(chain)
    base = [(a, e) for e in range(P.n) for a in P.less[e]]
    tot = P.linext_count()
    a = []
    for m in range(p + 1):
        extra = [(chain[i], x) for i in range(m)] + [(x, chain[i]) for i in range(m, p)]
        Pm = Poset(P.n, base + extra)
        a.append(Fraction(Pm.linext_count(), tot))
    # j = # chain elts e-below x. e-rank == element label (caller must relabel by e).
    j = sum(1 for c in chain if c < x)
    ES = sum((m - j) * a[m] for m in range(p + 1))
    ES2 = sum((m - j) ** 2 * a[m] for m in range(p + 1))
    Eabs = sum(abs(m - j) * a[m] for m in range(p + 1))
    ratio = ES2 / Eabs if Eabs > 0 else Fraction(0)
    return ratio, a, j, Eabs, ES2


def report(name, P, x, chain, verbose=True):
    w = width(P)
    d, wp = delta_of(P)
    ratio, a, j, Eabs, ES2 = slot_stats(P, x, chain)
    frozen = d < Fraction(1, 3)
    flag = "  <<<FROZEN+HIGH" if (frozen and ratio > Fraction(5, 2)) else ""
    if verbose:
        af = [f"{float(v):.3f}" for v in a]
        print(f"{name}: n={P.n} p={len(chain)} width={w} delta={float(d):.4f} "
              f"frozen={frozen} ratio={float(ratio):.3f} E|S|={float(Eabs):.3f} j={j}{flag}")
        print(f"    slot a={af}  worstpair={wp}")
    return dict(n=P.n, p=len(chain), width=w, delta=float(d), frozen=frozen,
               ratio=float(ratio), Eabs=float(Eabs))


# ---------------------------------------------------------------------------
# GADGET FAMILIES. Labels are e-ranks; we build so that label order is an LE
# (a<b in P => a<b as int) so j counting is correct, and x is the target.
# ---------------------------------------------------------------------------

def gadget_two_parallel_chains(p):
    """x=0 e-min. Chain A = a_1..a_p (target, incomparable to x). To FREEZE x before A,
    add an up-chain U above x. Width 3: x, a_i, u_k can be a 3-antichain, so keep U short.
    Simplest: x incomparable to chain A; a 'lid' element L above x AND above a_p, pulling
    both up but x pinned below L. Try lid variants."""
    # elements: x=0, then interleave? We'll just place chain A and a lid.
    n = 1 + p + 1
    x = 0
    A = list(range(1, 1 + p))            # a_1<..<a_p as a P-chain
    lid = 1 + p
    pairs = [(A[i], A[i + 1]) for i in range(p - 1)]
    pairs += [(x, lid)]                  # x below lid
    pairs += [(A[-1], lid)]              # chain-top below lid too
    P = Poset(n, pairs)
    return P, x, tuple(A)


def gadget_lid_and_floor(p, kfloor=1, klid=1):
    """x incomparable to chain A=a_1..a_p. A floor F (kfloor elts) below x and below a_1
    (pins bottom); a lid L (klid elts) above x and above a_p (pins top). This is the
    natural 'x threaded alongside a chain between shared floor and lid' -> width 3."""
    idx = 0
    def new():
        nonlocal idx; v = idx; idx += 1; return v
    F = [new() for _ in range(kfloor)]
    x = new()
    A = [new() for _ in range(p)]
    L = [new() for _ in range(klid)]
    n = idx
    pairs = []
    pairs += [(F[i], F[i + 1]) for i in range(kfloor - 1)]
    pairs += [(A[i], A[i + 1]) for i in range(p - 1)]
    pairs += [(L[i], L[i + 1]) for i in range(klid - 1)]
    # floor below x and below chain-bottom
    for f in F:
        pairs += [(f, x), (f, A[0])]
    # lid above x and chain-top
    for l in L:
        pairs += [(x, l), (A[-1], l)]
    P = Poset(n, pairs)
    return P, x, tuple(A)


def gadget_coupler(p):
    """Add a 'coupler' chain incomparable to x that shares comparabilities with A to make
    x's insertion window bimodal. x=floor.. Attempt a genuine width-3 block-cross:
    x incomparable to A (chain) and to B (chain), with A below a lid, B above a floor,
    arranged so x sometimes sits below all A (window low) sometimes above (window high)."""
    idx = 0
    def new():
        nonlocal idx; v = idx; idx += 1; return v
    # floor f, then x, chain A, coupler b linking; lid l
    f = new()
    x = new()
    A = [new() for _ in range(p)]
    b = new()          # single coupler incomparable to x, above chain-mid, below lid
    l = new()
    n = idx
    pairs = []
    pairs += [(A[i], A[i + 1]) for i in range(p - 1)]
    pairs += [(f, x), (f, A[0])]
    pairs += [(x, l), (A[-1], l)]
    # coupler b: below l, above A[mid]; incomparable to x
    pairs += [(A[p // 2], b), (b, l)]
    P = Poset(n, pairs)
    return P, x, tuple(A)


def main():
    print("=== gadget: two_parallel_chains (lid over x and chain-top) ===")
    for p in [3, 5, 8, 12, 16]:
        P, x, A = gadget_two_parallel_chains(p)
        report(f"twoPar p={p}", P, x, A)
    print("\n=== gadget: lid_and_floor (shared floor+lid) — vary kfloor,klid ===")
    for (kf, kl) in [(1, 1), (2, 2), (3, 3), (2, 1)]:
        for p in [3, 5, 8, 12]:
            P, x, A = gadget_lid_and_floor(p, kf, kl)
            report(f"LF kf={kf} kl={kl} p={p}", P, x, A, verbose=(p in (5, 12)))
        print()
    print("=== gadget: coupler ===")
    for p in [4, 6, 8, 12]:
        P, x, A = gadget_coupler(p)
        report(f"coupler p={p}", P, x, A)


if __name__ == "__main__":
    main()
