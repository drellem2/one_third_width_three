#!/usr/bin/env python3
"""
mg-c47a SCOPING probe: structural inspection of the TWO committed record
witnesses of mg-0eac sec.9.3a.

This is not a search and not an enumeration.  It reads two already-committed
posets (n = 10 and n = 11, sec.9.3a) out of the write-up and prints their
structure: covers, maximum antichains, and the (down-set, up-set) profiles of
the elements of a maximum antichain.  Total work: two posets.

Purpose (Q1 of the ticket): the candidate structural mechanisms for "low delta
forces small width" all run through symmetry / near-duplication of the elements
of a wide antichain.  This checks what the known width-3 minimiser actually
does at its own width-3 antichain -- i.e. how it pays for keeping all three
pairwise-incomparable pairs strongly decided.
"""

import os
import sys
from itertools import combinations

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust import (
    width_value_bitmask,
)

# sec.9.3a, verified through six independent engines.
WITNESSES = [
    ("n=10  min delta = 6/17   (proven width-exactly-3 minimum)",
     10, [0, 0, 1, 1, 7, 11, 43, 107, 111, 255]),
    ("n=11  min delta = 134/375 (proven width-exactly-3 minimum)",
     11, [0, 0, 1, 1, 3, 7, 47, 127, 111, 39, 895]),
]


def strict_below(n, below):
    """below[i] is a bitmask of the elements strictly below i."""
    return [set(j for j in range(n) if (below[i] >> j) & 1) for i in range(n)]


def report(title, n, below):
    D = strict_below(n, below)          # strict down-sets
    U = [set(j for j in range(n) if i in D[j]) for i in range(n)]
    inc = [(i, j) for i, j in combinations(range(n), 2)
           if j not in D[i] and i not in D[j]]

    print("=" * 74)
    print(title)
    print(f"  width (oracle) = {width_value_bitmask(n, below)}")
    print(f"  incomparable pairs = {len(inc)} of {n*(n-1)//2}")

    # covers
    covers = []
    for j in range(n):
        for i in D[j]:
            if not any(i in D[k] and k in D[j] for k in D[j]):
                covers.append((i, j))
    print(f"  cover relations: {sorted(covers)}")

    # maximum antichains, by brute force over subsets of a small poset
    best = []
    for size in range(n, 1, -1):
        found = [S for S in combinations(range(n), size)
                 if all((b not in D[a]) and (a not in D[b])
                        for a, b in combinations(S, 2))]
        if found:
            best = found
            break
    print(f"  maximum antichains (size {len(best[0])}): {len(best)} of them")

    for S in best[:6]:
        print(f"    antichain {S}:")
        for x in S:
            print(f"      x={x:2d}  |D|={len(D[x]):2d} D={sorted(D[x])}"
                  f"   |U|={len(U[x]):2d} U={sorted(U[x])}")
        # the two structural obstructions of the write-up, checked on this
        # antichain: twins (D and U both equal) and comparable profiles
        for a, b in combinations(S, 2):
            twin = (D[a] == D[b] and U[a] == U[b])
            nested = ((D[a] <= D[b] and U[b] <= U[a]) or
                      (D[b] <= D[a] and U[a] <= U[b]))
            sep = len(D[a] ^ D[b]) + len(U[a] ^ U[b])
            print(f"      pair ({a},{b}): twins={twin}  nested-profile={nested}"
                  f"  separator size |D_a^D_b|+|U_a^U_b| = {sep}")
    print()


if __name__ == "__main__":
    for title, n, below in WITNESSES:
        report(title, n, below)
