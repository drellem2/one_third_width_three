#!/usr/bin/env python3
"""Exhaustive search for FROZEN posets and their incomparability density.

The master bound of docs/probe-lambda-constant-bound.md reads

    lambda_std  >  1 - d * n/(n+1)        for frozen P

where d = (#incomparable pairs)/C(n,2).  So the bound yields a positive CONSTANT
iff frozen posets have d bounded away from 1.  This script measures, exactly, the
maximum d over all frozen posets on n <= NMAX elements, and separately reports the
maximum over frozen *primitive* posets (incomparability graph connected).

"Frozen" = every incomparable pair has minority probability < 1/3.

Posets are enumerated up to isomorphism by the standard construction: every poset
on [n] arises from a poset on [n-1] by adjoining a new maximal element whose strict
down-set is a down-set of the old poset.  We dedupe by a canonical form (minimum
adjacency bitstring over all n! relabellings), which is fine at these sizes.

Usage:  python3 scripts/probe_lambda_frozen_search.py [nmax]
"""

import itertools
import sys
from fractions import Fraction


def canon(less, n):
    best = None
    for perm in itertools.permutations(range(n)):
        bits = 0
        for i in range(n):
            for j in range(n):
                if less[perm[i]][perm[j]]:
                    bits |= 1 << (i * n + j)
        if best is None or bits < best:
            best = bits
    return best


def grow(posets, n):
    """posets: list of (n-1)-element `less` matrices.  Returns n-element ones."""
    out = {}
    for less in posets:
        m = len(less)
        # down-sets of the old poset
        downsets = []
        for mask in range(1 << m):
            ok = True
            for j in range(m):
                if mask >> j & 1:
                    for i in range(m):
                        if less[i][j] and not (mask >> i & 1):
                            ok = False
                            break
                if not ok:
                    break
            if ok:
                downsets.append(mask)
        for mask in downsets:
            new = [[less[i][j] for j in range(m)] + [bool(mask >> i & 1)]
                   for i in range(m)]
            new.append([False] * (m + 1))
            c = canon(new, n)
            if c not in out:
                out[c] = new
    return list(out.values())


def all_posets(nmax):
    levels = {1: [[[False]]]}
    for n in range(2, nmax + 1):
        levels[n] = grow(levels[n - 1], n)
    return levels


def linear_extensions(less, n):
    return [p for p in itertools.permutations(range(n))
            if all(not less[p[b]][p[a]] for a in range(n) for b in range(a + 1, n))]


def connected_incomparability(less, n):
    inc = [[not less[i][j] and not less[j][i] and i != j for j in range(n)]
           for i in range(n)]
    seen = {0}
    stack = [0]
    while stack:
        x = stack.pop()
        for y in range(n):
            if inc[x][y] and y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == n


def stats(less, n):
    exts = linear_extensions(less, n)
    N = len(exts)
    inc = [(i, j) for i in range(n) for j in range(i + 1, n)
           if not less[i][j] and not less[j][i]]
    beta_max = Fraction(0)
    for (a, b) in inc:
        cnt = sum(1 for e in exts if e.index(a) < e.index(b))
        p = Fraction(cnt, N)
        beta_max = max(beta_max, min(p, 1 - p))
    d = Fraction(len(inc), n * (n - 1) // 2) if n > 1 else Fraction(0)
    return len(inc), d, beta_max


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    levels = all_posets(nmax)
    third = Fraction(1, 3)
    print(f"{'n':>3} {'#posets':>9} {'#frozen':>8} {'max d frozen':>13} "
          f"{'#frozen primitive':>18} {'max d frozen prim':>18} {'witness beta':>13}")
    for n in range(2, nmax + 1):
        best_all = (Fraction(0), None)
        best_prim = (Fraction(0), None)
        nfroz = nprim = 0
        for less in levels[n]:
            m, d, beta = stats(less, n)
            if beta >= third:
                continue
            nfroz += 1
            if d > best_all[0]:
                best_all = (d, (less, beta))
            if m > 0 and connected_incomparability(less, n):
                nprim += 1
                if d > best_prim[0]:
                    best_prim = (d, (less, beta))
        bp = f"{float(best_prim[0]):.4f}" if best_prim[1] else "   -  "
        wb = f"{float(best_prim[1][1]):.4f}" if best_prim[1] else "   -  "
        print(f"{n:>3} {len(levels[n]):>9} {nfroz:>8} {float(best_all[0]):>13.4f} "
              f"{nprim:>18} {bp:>18} {wb:>13}")
        if best_prim[1]:
            less = best_prim[1][0]
            rel = [f"{i}<{j}" for i in range(n) for j in range(n) if less[i][j]]
            print(f"      densest frozen primitive poset on {n}: " + " ".join(rel))


if __name__ == "__main__":
    main()
