#!/usr/bin/env python3
"""INDEPENDENT AUDIT engine for mg-0eac. Shares NO code with the merged scripts.

Computes e(P) and delta(P) by directly enumerating linear extensions via
recursion over currently-minimal available elements. Deliberately naive and
slow; correctness by construction, not by cleverness.
"""
from fractions import Fraction
from itertools import combinations
import sys


def linear_extensions(n, below):
    """Yield every linear extension as a tuple, by repeatedly picking any
    element all of whose strict predecessors are already placed."""
    out = []
    seq = []
    placed = 0

    def rec(placed, seq):
        if len(seq) == n:
            out.append(tuple(seq))
            return
        for x in range(n):
            if placed >> x & 1:
                continue
            if below[x] & ~placed:      # some predecessor not yet placed
                continue
            seq.append(x)
            rec(placed | (1 << x), seq)
            seq.pop()

    rec(0, seq)
    return out


def audit_delta(n, below):
    """Return (e, delta, argpair). delta = max over INCOMPARABLE pairs of
    min(Pr[x<y], Pr[y<x]).  None for chains."""
    exts = linear_extensions(n, below)
    e = len(exts)
    # position of each element in each extension
    pos = []
    for ext in exts:
        p = [0] * n
        for i, x in enumerate(ext):
            p[x] = i
        pos.append(p)
    # comparability: y above x iff x in below[y] (relation assumed transitively closed)
    def comparable(x, y):
        return bool(below[y] >> x & 1) or bool(below[x] >> y & 1)

    best = None
    arg = None
    for x, y in combinations(range(n), 2):
        if comparable(x, y):
            continue
        cnt = sum(1 for p in pos if p[x] < p[y])
        a = Fraction(cnt, e)
        b = 1 - a
        v = min(a, b)
        if best is None or v > best:
            best, arg = v, (x, y)
    return e, best, arg


def is_transitively_closed(n, below):
    for y in range(n):
        for x in range(n):
            if below[y] >> x & 1:
                if below[y] & below[x] != below[x]:
                    return False
    return True


def incomparability_connected(n, below):
    """Independent primitivity check: incomparability graph connected."""
    def comparable(x, y):
        return bool(below[y] >> x & 1) or bool(below[x] >> y & 1)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in range(n):
            if v != u and v not in seen and not comparable(u, v):
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def width_bruteforce(n, below):
    """Independent width: largest antichain, by brute force over subsets."""
    def comparable(x, y):
        return bool(below[y] >> x & 1) or bool(below[x] >> y & 1)
    best = 0
    for size in range(n, 0, -1):
        if size <= best:
            break
        for S in combinations(range(n), size):
            if all(not comparable(a, b) for a, b in combinations(S, 2)):
                best = max(best, size)
                break
    return best


def ladder_below(n, broken):
    """INDEPENDENT reconstruction of Peczarski's L_{n;S} from the doc's own
    prose spec (doc sec.3.3): ground set {0..n-1} by height; rails j < j+2 for
    0<=j<=n-3; rungs j < j+3 for 0<=j<=n-4 EXCEPT the broken ones; then
    transitive closure."""
    rel = [set() for _ in range(n)]   # rel[y] = elements strictly below y
    for j in range(0, n - 2):
        rel[j + 2].add(j)
    for j in range(0, n - 3):
        if j in broken:
            continue
        rel[j + 3].add(j)
    # transitive closure (Floyd-ish, repeat to fixpoint)
    changed = True
    while changed:
        changed = False
        for y in range(n):
            add = set()
            for x in list(rel[y]):
                add |= rel[x]
            if not add <= rel[y]:
                rel[y] |= add
                changed = True
    return [sum(1 << x for x in rel[y]) for y in range(n)]


# ---- exact rational vs algebraic comparisons, derived here from scratch ---- #
def lt_beta(q):
    """q < (5864893 + 27*sqrt(57))/16812976 ?  Derived independently."""
    L = Fraction(16812976) * q - 5864893     # want L < 27*sqrt(57)
    if L <= 0:
        return True
    return L * L < 27 * 27 * 57


def lt_kappa(q):
    """q < (93 - sqrt(6697))/32 ?"""
    R = 93 - Fraction(32) * q                # want R > sqrt(6697)
    if R <= 0:
        return False
    return R * R > 6697


def show(name, n, below, expect=None, expect_e=None):
    assert is_transitively_closed(n, below), f"{name}: not transitively closed"
    e, d, arg = audit_delta(n, below)
    w = width_bruteforce(n, below)
    prim = incomparability_connected(n, below)
    ok = "" if expect is None else ("  PASS" if d == expect else "  *** FAIL ***")
    oke = "" if expect_e is None else ("  e-PASS" if e == expect_e else f"  *** e-FAIL (got {e}) ***")
    print(f"  {name:<34} n={n:<3} e={e:<8} delta={str(d):<14} "
          f"~{float(d) if d is not None else float('nan'):.9f}  "
          f"width={w} prim={prim} argpair={arg}{ok}{oke}")
    return e, d


if __name__ == "__main__":
    print("=" * 96)
    print("INDEPENDENT AUDIT ENGINE -- from-scratch LE enumeration, no shared code")
    print("=" * 96)

    print("\n[A] Mandated positive controls")
    show("T = ({a,b,c}, a<b)", 3, [0, 1, 0], Fraction(1, 3), 3)
    show("antichain A_3", 3, [0, 0, 0], Fraction(1, 2), 6)
    show("antichain A_4", 4, [0, 0, 0, 0], Fraction(1, 2), 24)
    show("antichain A_5", 5, [0] * 5, Fraction(1, 2), 120)
    # ordinal sum T (+) T : elements 0,1,2 then 3,4,5 with everything in first
    # block below everything in second; within block a<b i.e. 0<1 and 3<4.
    tt_low = 0b111
    show("ordinal sum T (+) T", 6,
         [0, 1, 0, tt_low, tt_low | 0b1000, tt_low], Fraction(1, 3), 9)

    print("\n[B] External control -- Peczarski's published (delta, e) pairs")
    published = [
        ("L_{6;1}", 6, (1,), Fraction(5, 14), 14),
        ("L_{9;1,2,3,4}", 9, (1, 2, 3, 4), Fraction(6, 17), 85),
        ("L_{10;1,5}", 10, (1, 5), Fraction(37, 106), 106),
        ("L_{11;1,6}", 11, (1, 6), Fraction(20, 57), 171),
        ("L_{20;1,5,8,11,15}", 20, (1, 5, 8, 11, 15), Fraction(6059, 17366), 17366),
        ("L_{21;1,5,8,9,12,16}", 21, (1, 5, 8, 9, 12, 16), Fraction(5402, 15485), 30970),
        ("L_{25;1,5,8,9,12,13,16,20}", 25, (1, 5, 8, 9, 12, 13, 16, 20),
         Fraction(7451, 21359), 256308),
    ]
    for name, n, br, exp_d, exp_e in published:
        show(name, n, ladder_below(n, set(br)), exp_d, exp_e)

    print("\n[C] The two sec.9.3a record witnesses (doc's stated `below` arrays)")
    show("n=10 width-3 argmin", 10, [0, 0, 1, 1, 7, 11, 43, 107, 111, 255],
         Fraction(6, 17), 187)
    show("n=11 width-3 argmin", 11, [0, 0, 1, 1, 3, 7, 47, 127, 111, 39, 895],
         Fraction(134, 375), 750)

    print("\n[D] Exact threshold arithmetic, derived independently")
    beta_f = (5864893 + 27 * 57 ** 0.5) / 16812976
    kappa_f = (93 - 6697 ** 0.5) / 32
    print(f"  beta  = (5864893+27*sqrt57)/16812976 = {beta_f:.20f}")
    print(f"  kappa = (93-sqrt6697)/32            = {kappa_f:.20f}")
    print(f"  14/39 = {float(Fraction(14,39)):.20f}")
    print(f"  6/17  = {float(Fraction(6,17)):.20f}")
    for q, label in [(Fraction(7451, 21359), "record 7451/21359 (n=25)"),
                     (Fraction(6, 17), "width-3 best 6/17 (n=10)"),
                     (Fraction(14, 39), "Olson-Sagan 14/39"),
                     (Fraction(5402, 15485), "5402/15485 (n=21)"),
                     (Fraction(1, 3), "1/3")]:
        print(f"  {label:<30} = {float(q):.14f}  < beta? {lt_beta(q)!s:<5} "
              f"< kappa? {lt_kappa(q)!s:<5}")
    print(f"\n  6/17 < 14/39 ? {Fraction(6,17) < Fraction(14,39)}")
    print(f"  6/17 - beta  ~ {float(Fraction(6,17)) - beta_f:.6e}")
    print(f"  7451/21359 - beta ~ {float(Fraction(7451,21359)) - beta_f:.6e}")
