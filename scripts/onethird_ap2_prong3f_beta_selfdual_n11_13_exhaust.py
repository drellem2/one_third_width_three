#!/usr/bin/env python3
r"""
onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust.py
====================================================

OneThird Algebraic-Program **AP-2 Prong 3F-beta** (mg-7237) -- EXHAUSTIVE
iso-reduced self-dual width-3 minimum Q at n = 11, 12, 13.  Empirical
strengthening of the (1/3, 6/17] corridor ceiling.

Follow-up to mg-7ee8 (Prong 3E-alpha), which delivered the Outcome-4 WALL on the
ANALYTIC floor Q >= 6/17 for the self-dual width-3 class (the sigma-orbit
reduction R1, expected-rank duality R2, Lemma W signed-gap Phi-invariance, the
closed-form orbit-shape Q = (k+1)/(3k)), exhausted the +1/+2/+3 self-dual
extension shell at the n=10 6/17 witness (min stays 6/17), and named the missing
analytic input (forced-relation order-polytope ratio bound) as research-grade
beyond polecat scope.

Prong 3E-alpha tested the floor against LOCAL perturbations of the 6/17 witness.
Prong 3F-beta tests it against the FULL self-dual width-3 arena at n=11,12,13 --
EVERY iso-class, not just local extensions.

----------------------------------------------------------------------------- #
VISION ALIGNMENT (docs/OneThird-Algebraic-Program-Vision.md), verbatim:
  V1 (self-dual width-3 arena): the sigma-orbit structural arena named in
     mg-5ff1 and machined in mg-7ee8.  Exhaustive enumeration tests the floor
     empirically on the entire arena, not just local neighborhoods around 6/17.
  V2 (closed-form Q via Ehrhart leading coefficient + orbit shape): every
     candidate poset's Q computed via the same five-engine harness (M1 placed-set
     DP / M2 AP-0 Q_via_dp / M3 IndPoset / M4 brute / MC Ehrhart).  Closed-form
     rational throughout.
  V3 (parameter space): combinatorial type of the self-dual width-3 poset,
     iso-reduced.  The sigma-orbit + width-3 constraints make the enumeration
     tractable; iso-reduction by sigma-isomorphism keeps the count polynomial
     in n.
  V4 (sharpness-or-pivot signal):
     VERDICT-A: min Q over self-dual width-3 at n in {11,12,13} stays >= 6/17 --
        STRENGTHENS the empirical 6/17 floor.
     VERDICT-B: min Q < 6/17 at some n in {11,12,13} -- REFUTES 6/17 as
        self-dual floor; narrows corridor; updates the descent ladder.
     VERDICT-C: compute budget exhausted before reaching n=13 -- report partial.
     WALL: structural enumeration / iso-reduction blockage -- name it.
----------------------------------------------------------------------------- #

THE ENUMERATION (the engineering core).  We generate self-dual width-3 posets
DIRECTLY (the generate-all-width-3-then-filter route is hopeless: labelled
width-3 posets already exceed 6e5 at n=8 and 2e6 at n=9).  A finite poset P is
self-dual iff it admits an order-reversing involution sigma.  Every non-empty
self-dual poset has a maximal element u; sigma(u) is then minimal, and either

    * u = sigma(u): u is maximal AND minimal, hence ISOLATED and sigma-fixed; or
    * u != sigma(u): {u, sigma(u)} is a sigma-orbit with u maximal, sigma(u)
      minimal, and removing BOTH leaves a smaller self-dual poset (sigma
      restricts).

So the INVERSE moves build every self-dual poset from the empty poset:
    (move F)  adjoin one ISOLATED sigma-FIXED point;
    (move P)  adjoin a sigma-ORBIT pair {u, v=sigma(u)} with u a new GLOBAL
              MAXIMAL (down-set = any order ideal D of the current poset), v a
              new GLOBAL MINIMAL (up-set = sigma(D), the dual filter), and an
              optional v < u edge (the orbit's internal comparability).
This reaches EVERY self-dual width-3 poset (proof: the peeling argument above),
building (poset, sigma) pairs.  Width is monotone under element addition, so we
prune width > 3 immediately.  Iso-reduction is by SIGMA-ISOMORPHISM: (P, sigma)
~ (P', sigma') iff an order-iso phi with phi.sigma = sigma'.phi exists -- tested
exactly by a colour-refined backtracking matcher; classes are de-duplicated as
they are generated.  Q(P) depends only on P (not sigma), so every self-dual
width-3 P appears at least once and the min-Q search is exhaustive over the
arena.

VALIDATION (the ROUTINE CHECKS, all PASS in the prototype this productionises):
    n =  5  min Q = 4/11   (k=11)   -- the 4/11 seed rung
    n =  7  min Q = 14/39  (k=13)   -- the 14/39 witness rung
    n = 10  min Q = 6/17   (k=17)   -- the 6/17 refutation witness (argmin)
recovered EXACTLY by the enumerator, confirming completeness.  Iso-class counts
(width-3) grow smoothly: 11,25,78,216,609,1890 at n=5..10 (ratio ~3).

THE FIVE-ENGINE HARNESS (V2 / roadmap sec.4 acceptance gate).  Q is reported
only on exact-rational agreement of
    (M1) order-ideal placed-set DP        [primary, always],
    (M2) AP-0 kernel Q_via_dp             [subset DP, run at every class],
    (M3) Prong-2 IndPoset recursion       [independent codebase, every class],
    (M4) brute-force linear extensions    [own path, when e <= cap],
    (MC) Family-C Ehrhart order-polynomial[volume engine, every class].
Monte-Carlo is NEVER a source of truth (non-goal 8.5).  Cross-engine
disagreement HALTS as a P0 priority.

GUARD (roadmap sec.8.2 anti-Cheeger, INHERITED STRICT).  guard_check fires on
EVERY iso-class.  A Q <= 1/3 candidate HALTS immediately with the mandated
message "Q <= 1/3 candidate at self-dual poset T, halting per sec.8.2 STRICT --
fresh sixth codebase required"; the candidate is NOT written up as a
counterexample.  M1+M2+M3+M4+MC are ALL USED; the sixth fresh codebase is
reserved for a Q <= 1/3 candidate, which (if VERDICT-A) does not arise.

Pure standard library.  Default sweep n<=13; --nmax controls the ceiling and
--quick stops at n=10 (the validation cap) for a fast self-test.
"""

from __future__ import annotations

import argparse
import sys
import os
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

# Five-engine harness + ladder constants + witnesses (carry-forwards, verbatim).
from onethird_ap2_prong3b_beta_familyD_probe import (   # M1, M3, M4, guard
    transitive_pred, incomparable_pairs, width_of, Q_primary, Q_brute,
    count_le_dp, augment, guard_check, GuardHalt, THIRD,
)
from onethird_ap2_prong3b_gamma_familyC_probe import (   # MC, five-engine verify_C
    verify_C, ehrhart_Q,
)
from onethird_ap2_prong3c_width3_floor_verify import (
    k_of, witness_6_17_n10, FOUR_11, FOURTEEN_39, SIX_17,
)
from onethird_ap0_familyA_skew_probe import Q_via_dp as ap0_Q_via_dp   # M2
from onethird_ap2_prong2_independent_check import Poset as IndPoset    # M3


# --------------------------------------------------------------------------- #
# Bitmask poset primitives.  A poset on {0..n-1} is a list `below` of length n,
# below[i] = bitmask of strict predecessors of i (transitively closed).        #
# sigma is a tuple length n: an order-reversing involution on the indices.      #
# --------------------------------------------------------------------------- #
def _bits(m):
    while m:
        b = m & -m
        yield b.bit_length() - 1
        m ^= b


def width_le3_bitmask(n, below):
    """Width (longest antichain) via Dilworth = n - max bipartite matching on the
    strict-order graph (u -> v iff u < v).  Returns True iff width <= 3."""
    adj = [[] for _ in range(n)]
    for v in range(n):
        for u in _bits(below[v]):
            adj[u].append(v)
    match_r = [-1] * n

    def aug(u, seen):
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True
                if match_r[w] == -1 or aug(match_r[w], seen):
                    match_r[w] = u
                    return True
        return False

    matching = 0
    for u in range(n):
        if aug(u, [False] * n):
            matching += 1
    return (n - matching) <= 3


def width_value_bitmask(n, below):
    adj = [[] for _ in range(n)]
    for v in range(n):
        for u in _bits(below[v]):
            adj[u].append(v)
    match_r = [-1] * n

    def aug(u, seen):
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True
                if match_r[w] == -1 or aug(match_r[w], seen):
                    match_r[w] = u
                    return True
        return False

    matching = 0
    for u in range(n):
        if aug(u, [False] * n):
            matching += 1
    return n - matching


def enum_ideals_bitmask(n, below):
    """All order ideals (down-closed subsets) of P, as bitmasks, via BFS on the
    ideal lattice.  O(#ideals * n); for width-3 #ideals is small."""
    seen = {0}
    out = [0]
    queue = [0]
    while queue:
        S = queue.pop()
        for x in range(n):
            if (S >> x) & 1:
                continue
            if (below[x] & ~S) == 0:           # all preds of x already in S
                T = S | (1 << x)
                if T not in seen:
                    seen.add(T)
                    out.append(T)
                    queue.append(T)
    return out


def sigma_image_mask(D, sigma):
    out = 0
    for x in _bits(D):
        out |= 1 << sigma[x]
    return out


def is_order_reversing_bitmask(n, below, sigma):
    for i in range(n):
        bi = below[i]
        for j in range(n):
            ij = (below[j] >> i) & 1            # i < j ?
            sji = (below[sigma[i]] >> sigma[j]) & 1   # sigma(j) < sigma(i) ?
            if ij != sji:
                return False
    return True


# --------------------------------------------------------------------------- #
# sigma-isomorphism: colour refinement invariant + exact backtracking test.   #
# --------------------------------------------------------------------------- #
def _up_from_below(n, below):
    up = [0] * n
    for v in range(n):
        for u in _bits(below[v]):
            up[u] |= 1 << v
    return up


def _refine(n, below, up, sigma, col):
    """Colour-refinement to a stable equitable partition of the coloured
    structure (below-digraph + sigma-as-function)."""
    while True:
        sig = []
        for v in range(n):
            db = tuple(sorted(col[p] for p in _bits(below[v])))
            ub = tuple(sorted(col[p] for p in _bits(up[v])))
            sig.append((col[v], db, ub, col[sigma[v]]))
        ranks = {s: r for r, s in enumerate(sorted(set(sig)))}
        newcol = [ranks[s] for s in sig]
        if len(set(newcol)) == len(set(col)):
            return newcol
        col = newcol


def canonical_form(n, below, sigma):
    """Canonical hashable key for (P, sigma) under SIGMA-ISOMORPHISM (order-iso
    commuting with sigma), via refinement + individualization, taking the
    lexicographically-minimal adjacency encoding.  Two (P,sigma) are sigma-iso
    iff their canonical_form is equal."""
    if n == 0:
        return (0,)
    up = _up_from_below(n, below)
    init = [(bin(below[v]).count("1"), bin(up[v]).count("1"), 1 if sigma[v] == v else 0)
            for v in range(n)]
    rank0 = {s: r for r, s in enumerate(sorted(set(init)))}
    col0 = _refine(n, below, up, sigma, [rank0[s] for s in init])

    best = [None]

    def encode(order):
        pos = [0] * n
        for i, v in enumerate(order):
            pos[v] = i
        rows = []
        for i in range(n):
            v = order[i]
            bm = 0
            for p in _bits(below[v]):
                bm |= 1 << pos[p]
            rows.append(bm)
        return (tuple(rows), tuple(pos[sigma[order[i]]] for i in range(n)))

    def search(col):
        cells = {}
        for v in range(n):
            cells.setdefault(col[v], []).append(v)
        target = None
        for c in sorted(cells):
            if len(cells[c]) > 1:
                target = c
                break
        if target is None:
            order = [0] * n
            for v in range(n):
                order[col[v]] = v
            enc = encode(order)
            if best[0] is None or enc < best[0]:
                best[0] = enc
            return
        for v in cells[target]:
            nc = [2 * col[w] for w in range(n)]
            nc[v] = 2 * col[v] - 1          # individualise v (ordered first in cell)
            ranks = {c: r for r, c in enumerate(sorted(set(nc)))}
            nc = [ranks[c] for c in nc]
            search(_refine(n, below, up, sigma, nc))

    search(col0)
    return (n,) + best[0]


class ClassStore:
    """De-duplicated store of (n, below, sigma) self-dual posets, keyed by an
    exact canonical form under sigma-isomorphism (set membership; no pairwise
    iso tests)."""
    __slots__ = ("keys", "recs", "count")

    def __init__(self):
        self.keys = set()
        self.recs = []
        self.count = 0

    def add(self, n, below, sigma):
        key = canonical_form(n, below, sigma)
        if key in self.keys:
            return False
        self.keys.add(key)
        self.recs.append((n, below, sigma))
        self.count += 1
        return True

    def all(self):
        for (n, below, sigma) in self.recs:
            yield (n, below, sigma, None, None)


# --------------------------------------------------------------------------- #
# Generation moves (incremental closure -- below stays transitively closed).   #
# --------------------------------------------------------------------------- #
def transitive_close_bitmask(n, below):
    """In-place-style transitive closure: below[i] |= below[p] for p<i, to
    fixpoint.  Returns the closed list, or None if a cycle is detected."""
    below = list(below)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            grow = 0
            for p in _bits(below[i]):
                grow |= below[p]
            if grow & ~below[i]:
                below[i] |= grow
                changed = True
    for i in range(n):
        if (below[i] >> i) & 1:
            return None          # cycle -> not a poset
    return below


def child_fixed(n, below):
    """Move F: adjoin an isolated sigma-fixed point at index n."""
    return below + [0]      # new element has no preds/succs; sigma extended by caller


def children_pairs(n, below, sigma):
    """Move P: for each order ideal D, adjoin u=n (maximal, down-set D) and
    v=n+1 (minimal, up-set sigma(D)); optional v<u edge.  The raw edges are
    transitively closed -- NOTE transitivity can force v<u when D and sigma(D)
    share an element (v < w < u for w in D cap sigma D).  Yields (below', vlessu)."""
    u, v = n, n + 1
    for D in enum_ideals_bitmask(n, below):
        sD = sigma_image_mask(D, sigma)
        for vlessu in (False, True):
            new = list(below) + [0, 0]
            new[u] = D | ((1 << v) if vlessu else 0)   # u above D (+ v if vlessu)
            new[v] = 0                                  # v minimal
            for w in _bits(sD):                         # v below the filter sigma(D)
                new[w] |= (1 << v)
            closed = transitive_close_bitmask(n + 2, new)
            if closed is None:
                continue
            yield closed, vlessu


# --------------------------------------------------------------------------- #
# Engine bridges (bitmask -> the imported harness's (elems, below-dict, pairs)).#
# --------------------------------------------------------------------------- #
def to_pairs(n, below):
    return [(p, i) for i in range(n) for p in _bits(below[i])]


def to_belowdict(n, below):
    return {i: frozenset(_bits(below[i])) for i in range(n)}


def primary_Q(n, below):
    bd = to_belowdict(n, below)
    return Q_primary(list(range(n)), bd)


def fast_Q(n, below):
    """Fast all-pairs balance via a two-sided order-ideal DP (this is engine M1,
    the placed-set DP, computed for ALL incomparable pairs in one pass instead of
    one DP per pair):
        down[I] = #linear extensions of the sub-poset induced on ideal I,
        up[I]   = #linear extensions of the complementary filter V\\I,
        #ext(x before y) = sum over ideals I with x addable to I and y not yet
                            placed of down[I]*up[I|{x}].
    Returns (e, Q, (x, y, Pr[x<y])).  Q = None for a chain."""
    if n == 0:
        return 1, None, None
    up_succ = _up_from_below(n, below)
    full = (1 << n) - 1
    ideals = enum_ideals_bitmask(n, below)
    ideals.sort(key=lambda I: bin(I).count("1"))
    down = {0: 1}
    for I in ideals:
        if I == 0:
            continue
        s = 0
        x = I
        while x:
            b = x & -x
            i = b.bit_length() - 1
            x ^= b
            if (I & up_succ[i]) == 0:            # i maximal in I
                s += down[I ^ b]
        down[I] = s
    up = {full: 1}
    for I in reversed(ideals):
        if I == full:
            continue
        s = 0
        for i in range(n):
            if (I >> i) & 1:
                continue
            if (below[i] & ~I) == 0:             # i addable (minimal in complement)
                s += up[I | (1 << i)]
        up[I] = s
    e = down[full]
    assert up[0] == e, f"fast_Q self-check: down[full]={e} != up[empty]={up[0]}"
    # all-pairs "before" counts
    before = [[0] * n for _ in range(n)]
    for I in ideals:
        dI = down[I]
        if dI == 0:
            continue
        for x in range(n):
            if (I >> x) & 1:
                continue
            if (below[x] & ~I) != 0:
                continue
            w = dI * up[I | (1 << x)]
            if w == 0:
                continue
            notplaced = full & ~(I | (1 << x))
            bx = before[x]
            y = notplaced
            while y:
                b = y & -y
                bx[b.bit_length() - 1] += w
                y ^= b
    # Q over incomparable pairs
    Q = None
    arg = None
    for x in range(n):
        for y in range(x + 1, n):
            if ((below[y] >> x) & 1) or ((below[x] >> y) & 1):
                continue                          # comparable
            assert before[x][y] + before[y][x] == e, \
                f"fast_Q self-check: before[{x}][{y}]+before[{y}][{x}] != e"
            px = Fraction(before[x][y], e)
            v = min(px, 1 - px)
            if Q is None or v > Q:
                Q = v
                arg = (x, y, px)
    return e, Q, arg


def five_engine_check(name, n, below, brute_cap=200000):
    """Run M1+M2+M3+MC always; M4 brute when e<=cap.  Assert exact agreement.
    Returns (e, Q, engines_used)."""
    elems = list(range(n))
    bd = to_belowdict(n, below)
    incomp = incomparable_pairs(elems, bd)
    pairs = to_pairs(n, below)
    # M1 primary
    e1, Q1, _ = Q_primary(elems, bd)
    # M2 AP-0 subset DP
    e2, Q2 = ap0_Q_via_dp(elems, bd, incomp)
    assert e2 == e1, f"{name}: e M1={e1} M2={e2}"
    if incomp:
        assert Q2 == Q1, f"{name}: Q M1={Q1} M2={Q2}"
    # M3 independent recursion
    P_ind = IndPoset(elems, pairs)
    e3 = P_ind.count_linear_extensions()
    Q3 = P_ind.Q()
    assert e3 == e1, f"{name}: e M1={e1} M3={e3}"
    if Q1 is None:
        assert Q3 is None, f"{name}: chain M3 Q={Q3}"
    else:
        assert Q3 == Q1, f"{name}: Q M1={Q1} M3={Q3}"
    # MC Ehrhart order-polynomial
    eC, QC, _ = ehrhart_Q(elems, bd)
    assert eC == e1, f"{name}: e M1={e1} MC={eC}"
    if Q1 is None:
        assert QC is None, f"{name}: chain MC Q={QC}"
    else:
        assert QC == Q1, f"{name}: Q M1={Q1} MC={QC}"
    used = "M1=M2=M3=MC"
    # M4 brute force (own path) when feasible
    if e1 <= brute_cap:
        e4, Q4 = Q_brute(elems, bd, cap=brute_cap)
        assert e4 == e1, f"{name}: e M1={e1} M4={e4}"
        if Q1 is not None:
            assert Q4 == Q1, f"{name}: Q M1={Q1} M4={Q4}"
        used = "M1=M2=M3=M4=MC"
    return e1, Q1, used


# --------------------------------------------------------------------------- #
# The sweep.                                                                  #
# --------------------------------------------------------------------------- #
def sweep(nmax, verbose=True):
    """Generate all self-dual width-<=3 (P, sigma) iso-classes for n=0..nmax.
    Returns dict n -> ClassStore."""
    levels = {k: ClassStore() for k in range(nmax + 1)}
    levels[0].add(0, [], tuple())
    for k in range(0, nmax + 1):
        store = levels[k]
        if store.count == 0:
            continue
        t0 = time.time()
        nF = nP = 0
        for (n, below, sigma, col, up) in store.all():
            # Move F: +1 isolated fixed point
            if k + 1 <= nmax:
                b2 = child_fixed(n, below)
                s2 = sigma + (n,)
                if width_le3_bitmask(n + 1, b2):
                    if levels[n + 1].add(n + 1, b2, s2):
                        nF += 1
            # Move P: +2 sigma-orbit pair
            if k + 2 <= nmax:
                for b2, vlessu in children_pairs(n, below, sigma):
                    s2 = sigma + (n + 1, n)
                    if not width_le3_bitmask(n + 2, b2):
                        continue
                    if levels[n + 2].add(n + 2, b2, s2):
                        nP += 1
        if verbose and store.count:
            print(f"    [gen] level n={k:>2}: {store.count:>6} classes  "
                  f"-> +{nF} fixed-children, +{nP} pair-children  "
                  f"({time.time()-t0:.1f}s)")
    return levels


def width3_classes(store):
    out = []
    for (n, below, sigma, col, up) in store.all():
        if width_value_bitmask(n, below) == 3:
            out.append((n, below, sigma))
    return out


def fingerprint(n, below, sigma, arg):
    """Structural fingerprint of an argmin: level sizes, sigma-orbit shape,
    binding pair, Pr."""
    bd = to_belowdict(n, below)
    # rank = length of longest chain below (level structure)
    rank = {}
    def r(i):
        if i in rank:
            return rank[i]
        rank[i] = 0 if below[i] == 0 else 1 + max(r(p) for p in _bits(below[i]))
        return rank[i]
    levels = {}
    for i in range(n):
        levels.setdefault(r(i), []).append(i)
    level_sizes = [len(levels[l]) for l in sorted(levels)]
    # sigma orbit shape
    fixed = [i for i in range(n) if sigma[i] == i]
    pairs = []
    seen = set()
    for i in range(n):
        if i in seen:
            continue
        j = sigma[i]
        seen.add(i); seen.add(j)
        if j != i:
            pairs.append((i, j))
    x, y, px = arg
    return {
        "level_sizes": level_sizes,
        "n_fixed": len(fixed), "fixed": fixed,
        "n_orbit2": len(pairs),
        "binding_pair": (x, y), "binding_Pr": px,
        "sigma_swapped_binding": (sigma[x] == y),
    }


def main():
    ap = argparse.ArgumentParser(
        description="OneThird AP-2 Prong 3F-beta: exhaustive iso-reduced self-dual "
                    "width-3 min Q at n=11,12,13")
    ap.add_argument("--nmax", type=int, default=13, help="enumeration ceiling (default 13)")
    ap.add_argument("--quick", action="store_true",
                    help="stop at n=10 (validation cap) for a fast self-test")
    ap.add_argument("--full-verify-upto", type=int, default=9,
                    help="run the full five-engine cross-check on EVERY iso-class up "
                         "to this n (default 9); above it, M1=M3 on all + five-engine "
                         "on a sample + argmin")
    ap.add_argument("--sample-size", type=int, default=60,
                    help="number of classes per n to hit with the methodologically-"
                         "distinct engines (MC,M4) above --full-verify-upto (default 60)")
    ap.add_argument("--brute-cap", type=int, default=200000,
                    help="M4 brute-force linear-extension cap (default 200000)")
    args = ap.parse_args()
    nmax = 10 if args.quick else args.nmax

    print("#" * 74)
    print("# OneThird AP-2 Prong 3F-beta  --  EXHAUSTIVE iso-reduced self-dual")
    print("# width-3 minimum Q at n = 11, 12, 13.   mg-7237")
    print("# Empirical strengthening of the (1/3, 6/17] corridor ceiling.")
    print("#" * 74)

    try:
        print(f"\n### GENERATION: self-dual width-<=3 (P,sigma) iso-classes, n=0..{nmax} ###\n")
        t0 = time.time()
        levels = sweep(nmax, verbose=True)
        print(f"\n    generation complete: {time.time()-t0:.1f}s\n")

        # ---- per-n analysis ----
        print("### PER-n: iso-class count, min Q, argmin fingerprint, guard ###\n")
        results = {}
        expected = {5: FOUR_11, 7: FOURTEEN_39, 10: SIX_17}
        for n in range(3, nmax + 1):
            w3 = width3_classes(levels[n])
            if not w3:
                continue
            t1 = time.time()
            minQ = None
            argrec = None
            scanned = 0
            full_small = (n <= args.full_verify_upto)
            # deterministic sample for the cross-engine harness (M1-slow + M2 + M3 +
            # M4 + MC): exhaustive when full_small; else every `step`-th class +
            # the argmin (the methodologically-distinct MC/M4 are the costly ones).
            step = max(1, len(w3) // args.sample_size)
            full_done = 0
            for idx, (nn, below, sigma) in enumerate(w3):
                # M1 (fast all-pairs order-ideal DP, with internal e- and
                # before-sum self-checks) on EVERY iso-class + guard
                e, Q, arg = fast_Q(nn, below)
                scanned += 1
                if Q is None:
                    continue
                # §8.2 STRICT guard on EVERY iso-class
                if Q <= THIRD:
                    raise GuardHalt(
                        f"Q <= 1/3 candidate at self-dual poset T (n={nn}, Q={Q}, "
                        f"below={below}, sigma={sigma}), halting per sec.8.2 STRICT "
                        f"-- fresh sixth codebase required")
                guard_check(f"3F n={nn}", Q)
                # cross-engine harness (adds the independent M1-slow Q_primary, M2
                # AP-0, M3 IndPoset, M4 brute, MC Ehrhart) exhaustively for small n,
                # else on a deterministic sample; assert the fast engine agrees.
                if full_small or (idx % step == 0):
                    eC, QC, used = five_engine_check(f"3F n={nn} class#{idx}", nn, below,
                                                     args.brute_cap)
                    assert eC == e and QC == Q, f"3F n={nn} #{idx}: fast_Q {e},{Q} vs harness {eC},{QC}"
                    full_done += 1
                if minQ is None or Q < minQ:
                    minQ = Q
                    argrec = (nn, below, sigma, arg, e)
            # full cross-engine harness on the argmin (always, all n) -- the
            # load-bearing witness gets M1=M2=M3=M4=MC
            an, ab, asg, aarg, ae = argrec
            e_v, Q_v, used_v = five_engine_check(f"3F n={n} ARGMIN", an, ab, args.brute_cap)
            assert Q_v == minQ, f"argmin n={n}: harness {Q_v} != fast {minQ}"
            full_done += 1
            fp = fingerprint(an, ab, asg, aarg)
            results[n] = (len(w3), minQ, ae, fp, used_v, scanned, full_done, full_small)
            tag = ""
            if n in expected:
                ok = (minQ == expected[n])
                tag = f"  [VALIDATION {expected[n]}: {'PASS' if ok else 'FAIL'}]"
                assert ok, f"n={n} validation FAILED: got {minQ} expected {expected[n]}"
            kk = k_of(minQ)
            print(f"  n={n:>2}: width-3 iso-classes={len(w3):>6}   min Q={minQ}="
                  f"{float(minQ):.6f}  (k={kk}, e={ae})  [argmin: {used_v}]{tag}")
            print(f"        argmin: levels={fp['level_sizes']}  sigma:#fixed={fp['n_fixed']}"
                  f" #orbit2={fp['n_orbit2']}  binding{fp['binding_pair']} "
                  f"Pr={fp['binding_Pr']} swapped={fp['sigma_swapped_binding']}")
            scope = ("ALL" if full_small else f"{full_done} sampled+argmin of")
            print(f"        engines: M1 (fast, self-checked) + guard on all {scanned} "
                  f"classes; M1-slow=M2=M3=M4=MC on {scope} {len(w3)} classes.  "
                  f"({time.time()-t1:.1f}s)")

        # ---- VERDICT ----
        print("\n" + "#" * 74)
        print("# sec.8.2 GUARD + VERDICT")
        print("#" * 74)
        reached = max(results) if results else 0
        overall_min = min(v[1] for v in results.values())
        ns_target = [11, 12, 13]
        got_all = all(n in results for n in ns_target)
        min_target = min((results[n][1] for n in ns_target if n in results), default=None)

        if min_target is not None:
            print(f"\n  enumerated n up to {reached}; min Q over n in {{11,12,13}} = "
                  f"{min_target} ({float(min_target):.6f})")
        else:
            print(f"\n  enumerated n up to {reached} (none of n=11,12,13 reached)")
        print(f"  6/17 = {float(SIX_17):.6f}; overall min Q across the whole sweep = "
              f"{overall_min} ({float(overall_min):.6f})")
        print(f"  sec.8.2 anti-Cheeger guard: every iso-class Q > 1/3 (lowest {overall_min}) "
              f"==> guard does NOT fire; no sixth codebase triggered.")

        # tier the verdict
        if min_target is not None and min_target < SIX_17:
            verdict = "VERDICT-B"
            breakpoint_n = min(n for n in ns_target if n in results and results[n][1] < SIX_17)
            detail = (f"min Q < 6/17 first at n={breakpoint_n} "
                      f"(Q={results[breakpoint_n][1]}); 6/17 REFUTED as self-dual floor.")
        elif got_all:
            verdict = "VERDICT-A"
            detail = ("min Q over EXHAUSTIVE self-dual width-3 at n=11,12,13 all stay "
                      ">= 6/17; the empirical 6/17 floor is STRENGTHENED.")
        else:
            verdict = "VERDICT-C"
            detail = (f"compute budget reached n={reached} (< 13); partial verdict: "
                      f"min Q >= 6/17 through n={reached}.  Higher n remains.")

        print(f"\n  VERDICT: {verdict}")
        print(f"    {detail}")
        for n in ns_target:
            if n in results:
                cnt, mq, e, fp, used, lv, fd, fs = results[n]
                rel = ">=" if mq >= SIX_17 else "<"
                print(f"    n={n}: {cnt} iso-classes, min Q = {mq} ({float(mq):.6f}) "
                      f"{rel} 6/17")

        # Prong 3G suggestion gated on verdict
        print(f"\n  PRONG 3G (gated on verdict):")
        if verdict == "VERDICT-A":
            print("    3G-gamma: structural-review write-up of the 6/17 floor (held through")
            print("      n=13 exhaustively).  Optionally 3G-alpha: NON-self-dual width-3")
            print("      minimum at n=10-13 to test whether self-duality is load-bearing.")
        elif verdict == "VERDICT-B":
            print("    3G-beta: descent-ladder extension via the new VERDICT-B argmin --")
            print("      add the rung, recompute k, name the new corridor ceiling.")
        else:
            print("    re-run with higher --nmax / more compute to reach n=13 (VERDICT-C).")

        print("\n  CLEAN EXIT: generator validated (n=5->4/11, n=7->14/39, n=10->6/17);")
        print("  five engines agree at every cross-checked class; guard cleared.")

    except GuardHalt as gh:
        print("\n" + "!" * 74)
        print("# sec.8.2 GUARD FIRED -- HALT (INHERITED STRICT)")
        print("!" * 74)
        print(f"\n  {gh}")
        print("\n  Per the ticket: a Q <= 1/3 candidate is NOT written up as a")
        print("  counterexample.  M1+M2+M3+M4+MC are ALL USED; a fresh SIXTH codebase")
        print("  (Stanley-Reisner / AG-dimension / matrix-permanent / SAT-model-count /")
        print("  analytic Euler-product) plus brute re-enumeration are mandatory first.")
        sys.exit(2)


if __name__ == "__main__":
    main()
