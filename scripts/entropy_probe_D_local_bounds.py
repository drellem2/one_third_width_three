#!/usr/bin/env python3
"""Entropy probe D (mg-e2de), part 2: local-geometry bounds on the balance of
a single incomparable pair.

For every poset on n <= 6 elements (up to isomorphism) and every incomparable
pair {x,y} we record

    b(x,y)   = min(Pr[x<y], Pr[y<x])                        (pair balance)
    m(x,y)   = |(N_G(x) u N_G(y)) \\ {x,y}|                   (local co-degree)
    c(x,y)   = Pr[x,y consecutive in sigma] = 2 e(P/xy)/e(P)

and test three claims:

  (T1) PROVEN   b >= c/2                       (contraction / transposition)
  (T2) PROVEN   #elements between x and y in any sigma  <=  m
  (T3) CONJ     b >= 1/(m+2)                   (tight on {pt} (+) chain)

plus the twin lemma:

  (T4) PROVEN   N(x)\\{y} = N(y)\\{x}  ==>  b = 1/2
"""

from itertools import permutations
from functools import lru_cache
import sys

from entropy_probe_D_incomparability_local import (
    gen_posets, canon, incomparability_edges, count_ext, below_masks,
    transitive_closure_add,
)


def contract(n, rel, x, y):
    """Poset P/xy on the vertex set {0..n-1}\\{x,y} u {x} (x plays the merged
    vertex *).  Returns (size, below-masks) after relabelling."""
    verts = [v for v in range(n) if v != y]
    idx = {v: i for i, v in enumerate(verts)}
    less = set()
    for (a, b) in rel:
        a2 = x if a == y else a
        b2 = x if b == y else b
        if a2 != b2:
            less.add((idx[a2], idx[b2]))
    # transitive closure (cheap, tiny)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(less):
            for (c, d) in list(less):
                if b == c and (a, d) not in less:
                    less.add((a, d))
                    changed = True
    bm = [0] * len(verts)
    for (a, b) in less:
        bm[b] |= 1 << a
    return len(verts), tuple(bm)


def max_between(n, rel, x, y):
    """Max over linear extensions of #elements strictly between x and y.
    Brute force over extensions (n <= 6)."""
    bm = below_masks(n, rel)
    best = 0
    stack = [(0, [])]
    while stack:
        S, order = stack.pop()
        if S == (1 << n) - 1:
            i, j = order.index(x), order.index(y)
            best = max(best, abs(i - j) - 1)
            continue
        for v in range(n):
            if not (S >> v & 1) and (bm[v] & ~S) == 0:
                stack.append((S | 1 << v, order + [v]))
    return best


def run(n, verbose=False):
    seen = {}
    for rel in gen_posets(n):
        c = canon(n, rel)
        if c not in seen:
            seen[c] = rel

    worst_T3 = (10.0, None)
    viol = {"T1": 0, "T2": 0, "T3": 0, "T4": 0}
    npairs = 0

    for rel in seen.values():
        e = count_ext(n, below_masks(n, rel))
        inc = incomparability_edges(n, rel)
        nb = {v: set() for v in range(n)}
        for (a, b) in inc:
            nb[a].add(b)
            nb[b].add(a)
        for (x, y) in inc:
            npairs += 1
            exy = count_ext(n, below_masks(n, transitive_closure_add(n, rel, x, y)))
            p = exy / e
            b = min(p, 1 - p)
            m = len((nb[x] | nb[y]) - {x, y})
            k, bmc = contract(n, rel, x, y)
            c = 2 * count_ext(k, bmc) / e

            if b < c / 2 - 1e-12:
                viol["T1"] += 1
            if max_between(n, rel, x, y) > m:
                viol["T2"] += 1
            if b < 1.0 / (m + 2) - 1e-12:
                viol["T3"] += 1
                if verbose:
                    print("   T3 violation", sorted(rel), (x, y), b, m)
            if nb[x] - {y} == nb[y] - {x} and abs(b - 0.5) > 1e-12:
                viol["T4"] += 1
            slack = b * (m + 2)
            if slack < worst_T3[0]:
                worst_T3 = (slack, (sorted(rel), (x, y), b, m, c))

    print(f"n={n}: {len(seen)} posets, {npairs} incomparable pairs")
    print(f"  violations: {viol}")
    print(f"  tightest T3 (b*(m+2), min over pairs): {worst_T3[0]:.6f}")
    print(f"    witness: rel={worst_T3[1][0]}")
    print(f"    pair={worst_T3[1][1]} b={worst_T3[1][2]:.4f} "
          f"m={worst_T3[1][3]} Pr[consec]={worst_T3[1][4]:.4f}")


if __name__ == "__main__":
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in range(2, top + 1):
        run(n)


def table(top=6):
    """min pair-balance b as a function of the local co-degree m."""
    best = {}
    for n in range(2, top + 1):
        seen = {}
        for rel in gen_posets(n):
            c = canon(n, rel)
            if c not in seen:
                seen[c] = rel
        for rel in seen.values():
            e = count_ext(n, below_masks(n, rel))
            inc = incomparability_edges(n, rel)
            nb = {v: set() for v in range(n)}
            for (a, b) in inc:
                nb[a].add(b); nb[b].add(a)
            for (x, y) in inc:
                exy = count_ext(n, below_masks(n,
                        transitive_closure_add(n, rel, x, y)))
                p = exy / e
                b = min(p, 1 - p)
                m = len((nb[x] | nb[y]) - {x, y})
                if m not in best or b < best[m][0]:
                    best[m] = (b, n, sorted(rel), (x, y), exy, e)
    print("\n m | min b over all pairs with that local co-degree (n<=%d)" % top)
    for m in sorted(best):
        b, n, rel, pair, exy, e = best[m]
        print(f" {m} | {b:.5f}  (= {min(exy, e-exy)}/{e})  n={n} "
              f"pair={pair} rel={rel}")
