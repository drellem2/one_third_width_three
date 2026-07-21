#!/usr/bin/env python3
"""
mg-8ff1: the worked non-example for Lemma 3.2b of the width-4 scoping doc.

mg-7d24's audit found Lemma 3.2b [BROKEN]: the boxed statement hypothesised
that some automorphism MAPS x to y, while the proof needs one that SWAPS them.
The gap is real and not vacuous -- an automorphism can move x to y without any
automorphism exchanging them, whenever x and y sit adjacent in an orbit of
length k >= 3, since no power of a k-cycle transposes two of its elements.

This script pins the counterexample so the weaker hypothesis cannot be quietly
re-introduced later.  It re-derives every figure quoted in the doc rather than
asserting them: the poset axioms, |Aut(P)|, the maps/swaps distinction, and
delta.

Run:
    python3 scripts/onethird_mg8ff1_lemma32b_counterexample.py

Exits non-zero if any claimed figure fails to reproduce.
"""

import os
import sys
from fractions import Fraction
from itertools import permutations

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from onethird_mg0eac_primitive_delta_search import delta_of

# below[y] is the bitmask of elements strictly below y.
N = 9
BELOW = (256, 64, 128, 322, 196, 385, 0, 0, 0)

# The figures the doc quotes, asserted here so the doc and the code cannot
# drift apart silently.
CLAIM_AUT_ORDER = 3
CLAIM_E = 1431
CLAIM_DELTA = Fraction(79, 159)
CLAIM_PAIR = (0, 1)


def relation(n, below):
    """rel[x][y] is True iff x < y."""
    return [[bool(below[y] >> x & 1) for y in range(n)] for x in range(n)]


def check_poset(n, rel):
    assert all(not rel[x][x] for x in range(n)), "irreflexivity"
    assert all(not (rel[x][y] and rel[y][x])
               for x in range(n) for y in range(n)), "antisymmetry"
    assert all(not (rel[x][y] and rel[y][z]) or rel[x][z]
               for x in range(n) for y in range(n)
               for z in range(n)), "transitivity"


def automorphisms(n, rel):
    """All of them, by brute force over n! -- n = 9 is 362 880, ~1 s."""
    return [p for p in permutations(range(n))
            if all(rel[x][y] == rel[p[x]][p[y]]
                   for x in range(n) for y in range(n))]


def main():
    rel = relation(N, BELOW)
    check_poset(N, rel)
    print("poset axioms (irreflexive, antisymmetric, transitive): OK")

    auts = automorphisms(N, rel)
    print(f"|Aut(P)| = {len(auts)}  (claimed {CLAIM_AUT_ORDER})")
    assert len(auts) == CLAIM_AUT_ORDER, "automorphism group order"

    x, y = CLAIM_PAIR
    assert not rel[x][y] and not rel[y][x], f"{x} || {y} must be incomparable"

    maps = [p for p in auts if p[x] == y]
    swaps = [p for p in auts if p[x] == y and p[y] == x]
    print(f"automorphisms mapping {x} -> {y}: {len(maps)}  {maps}")
    print(f"automorphisms swapping {x} <-> {y}: {len(swaps)}")
    assert maps, "the BOXED hypothesis must be satisfied"
    assert not swaps, "the hypothesis the PROOF needs must fail"

    e, delta, (ax, ay, pr) = delta_of(N, BELOW)
    print(f"e(P) = {e}  (claimed {CLAIM_E})")
    print(f"delta(P) = {delta} = {float(delta):.6f}  (claimed {CLAIM_DELTA})")
    print(f"argmin pair = ({ax}, {ay}), Pr[{ax} < {ay}] = {pr}")
    assert e == CLAIM_E, "e(P)"
    assert delta == CLAIM_DELTA, "delta"
    assert (ax, ay) == CLAIM_PAIR, "argmin pair"

    # The two conclusions of the boxed statement, both false here.
    assert pr != Fraction(1, 2), "Pr must not be 1/2"
    assert delta < Fraction(1, 2), "delta must be < 1/2"

    print()
    print("boxed hypothesis  (some automorphism MAPS x to y):  SATISFIED")
    print("hypothesis needed (some automorphism SWAPS x, y):   FAILS")
    print(f"conclusion Pr = 1/2:      FAILS ({pr} != 1/2)")
    print(f"conclusion delta >= 1/2:  FAILS ({delta} < 1/2)")
    print()
    print("=> the boxed 'maps' hypothesis is strictly weaker than the proof "
          "uses; 'swaps' is the correct one.  ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
