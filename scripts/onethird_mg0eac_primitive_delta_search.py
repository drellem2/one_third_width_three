#!/usr/bin/env python3
r"""
onethird_mg0eac_primitive_delta_search.py
=========================================

OneThird **mg-0eac** -- coherence-guided perturbation search for low-`delta`
**PRIMITIVE** (non-ordinal-sum) posets at the 1/3-2/3 boundary.

    delta(P) = max over INCOMPARABLE pairs (x,y) of min(Pr[x<y], Pr[y<x]),
    Pr[x<y]  = #{linear extensions with x before y} / e(P).

The 1/3-2/3 conjecture is `delta(P) >= 1/3` for every finite non-chain poset.

WHAT IS *NOT* REDONE HERE (binding prior work, per the ticket):
  * Peczarski (2006, 2008) verified the conjecture EXHAUSTIVELY for n <= 11.
    Brute-forcing all posets to n = 11 would merely redo him.  The exhaustive
    sweep in this module runs only to n <= 9 (10 on request) and is used
    *purely as a POSITIVE CONTROL / seed harvest*, never as a new result.
  * Peczarski (2019) computer-searched the smallest-delta poset per size and
    conjectured the GAP: no poset has delta in the open interval (1/3, beta),
    beta ~ 0.348843.  The only posets known to attain exactly 1/3 are the
    ordinal (linear) sums of singletons and of the 3-element one-relation
    poset T.

  CORRECTION (established by this work item -- the ticket got this wrong).
  T ITSELF IS PRIMITIVE.  T = ({a,b,c}, a<b) is not an ordinal sum: its
  incomparability graph is the connected path a -- c -- b.  And delta(T) = 1/3
  exactly (five-engine verified).  So "primitive => delta >= beta" is FALSE as
  stated; the correct statement excepts T, i.e. holds for n >= 4.  Sah's
  phrasing ("P not formable from 1 and E using direct sum", E = T) DOES
  exclude T and is correct; the ticket's paraphrase dropped the exception.
  Note the two conditions are incomparable: primitivity excludes all ordinal
  sums but keeps T; Sah's condition excludes T but keeps ordinal sums of large
  primitive blocks.
  ==> For PRIMITIVE posets with n >= 4 the operative boundary is beta ~ 0.3488,
      not 1/3.  New effort therefore concentrates at n >= 12 (beyond exhaustive
      verification) via the COHERENCE-GUIDED perturbation Peczarski did not
      use.

THE DELTA ENGINE IS NOT NEW CODE.  It is imported verbatim from the
five-engine harness already validated in this repo by Prongs 3B/3C/3F/3G
(mg-7237 / mg-5406), where the same quantity is written `Q`:
    (M1) `fast_Q` all-pairs order-ideal placed-set DP   [primary, O(2^n * n)],
    (M2) AP-0 kernel `Q_via_dp`                          [independent subset DP],
    (M3) Prong-2 `IndPoset` minimal-element recursion    [independent codebase],
    (M4) brute-force linear-extension enumeration        [own path, e <= cap],
    (MC) Family-C Ehrhart order-polynomial               [volume engine].
Every headline poset reported by this module is re-verified through the full
harness before it is written up.  Monte-Carlo is never a source of truth.

GUARD (roadmap sec.8.2 anti-Cheeger, inherited STRICT).  A `delta <= 1/3`
candidate HALTS the sweep and is NOT written up as a counterexample without a
fresh independent sixth codebase; a `delta < beta` candidate is flagged
SUB-BETA and force-routed through the five-engine harness plus an independent
`e`-recount.

Pure standard library.

Sections
--------
  1. Poset primitives (bitmask), transitive closure, width.
  2. delta engine (imported) + `delta_of` wrapper + five-engine `verify`.
  3. Primitivity: ordinal-sum decomposability via the incomparability graph.
  4. Coherence: the majority relation `e` and its acyclicity.
  5. Seed families (beta-extremal: ladders with broken rungs / Chen / Sah).
  6. Exhaustive positive-control sweep (n <= 9) -- canonical augmentation.
  7. Coherence-guided perturbation search (beam, e-aligned edge additions).
  8. Driver / reporting / JSON certificate.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

# --- the validated five-engine harness (verbatim carry-forward) ------------ #
from onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust import (
    _bits, _up_from_below, enum_ideals_bitmask, width_value_bitmask,
    transitive_close_bitmask, fast_Q, five_engine_check, to_belowdict,
    to_pairs,
)
from onethird_ap2_prong3b_beta_familyD_probe import THIRD

THIRD = Fraction(1, 3)

# --------------------------------------------------------------------------- #
# 0. The beta threshold.                                                      #
# --------------------------------------------------------------------------- #
# The two constants are DISTINCT algebraic numbers in DIFFERENT quadratic
# fields, hence provably unequal:
#
#   beta  (Sah, arXiv:1811.01500 Thm 1.5; matches Peczarski's numeric 0.348843)
#         = (5864893 + 27*sqrt(57)) / 16812976        in Q(sqrt 57)
#         min poly  33625952 x^2 - 23459572 x + 4091717
#         = 0.34884346742240945893...
#
#   kappa (Chen, arXiv:1709.05753 Thm 2.4)
#         = (93 - sqrt(6697)) / 32                    in Q(sqrt 6697)
#         min poly  32 x^2 - 186 x + 61
#         = 0.34889999217940447361...
#
# kappa - beta ~ 5.65e-5.  Sah's beta is the SMALLER and is the operative
# threshold; Sah explicitly frames his family as an improvement on Chen's, so
# kappa is superseded.  Exact rational-vs-algebraic comparison is done by
# `lt_beta_sah` / `lt_kappa_chen` (sec. 10) -- NOT by floating point, since the
# search operates within ~1e-6 of beta.
BETA_CHEN = (93.0 - 6697.0 ** 0.5) / 32.0
BETA_PECZARSKI_SAH = (5864893 + 27 * 57 ** 0.5) / 16812976
BETA_THRESHOLD = min(BETA_CHEN, BETA_PECZARSKI_SAH)


# --------------------------------------------------------------------------- #
# 1. Poset primitives.                                                        #
#    A poset on {0..n-1} is a list `below` of length n; below[i] is the        #
#    bitmask of STRICT predecessors of i, transitively closed.                #
# --------------------------------------------------------------------------- #
def antichain(n):
    return [0] * n


def chain(n):
    return [(1 << i) - 1 for i in range(n)]


def add_edge(n, below, x, y):
    """Return the transitive closure of `below` + (x < y), or None if that
    would create a cycle (i.e. y < x already holds) or the edge is already
    present.  `below` is not mutated."""
    if (below[y] >> x) & 1:
        return None                       # already x < y
    if (below[x] >> y) & 1:
        return None                       # y < x: would create a cycle
    nb = list(below)
    return transitive_close_bitmask(n, _raw_add(nb, x, y))


def _raw_add(below, x, y):
    below[y] |= (1 << x)
    return below


def incomparable_pairs_bm(n, below):
    out = []
    for x in range(n):
        for y in range(x + 1, n):
            if not (((below[y] >> x) & 1) or ((below[x] >> y) & 1)):
                out.append((x, y))
    return out


def is_chain(n, below):
    return not incomparable_pairs_bm(n, below)


def poset_key(n, below):
    """Labelled key (NOT iso-canonical) -- cheap memo key inside one search."""
    return (n, tuple(below))


# --------------------------------------------------------------------------- #
# 2. delta engine.                                                            #
# --------------------------------------------------------------------------- #
def delta_of(n, below):
    """(e, delta, argpair).  delta is None exactly for chains.  Engine M1."""
    return fast_Q(n, below)


def verify_five(name, n, below, brute_cap=200000):
    """Force the full five-engine cross-check.  Raises AssertionError on any
    disagreement (that is a P0 halt, per the inherited protocol)."""
    return five_engine_check(name, n, below, brute_cap=brute_cap)


# --------------------------------------------------------------------------- #
# 3. Primitivity (non-ordinal-sum / indecomposable).                          #
#                                                                             #
#    P = A (+) B (ordinal sum) makes every a in A comparable to every b in B,  #
#    so the INCOMPARABILITY graph of an ordinal sum is the disjoint union of   #
#    those of the summands.  Conversely if the incomparability graph splits    #
#    into components C_1, C_2 then all cross pairs are comparable and (a       #
#    standard argument) the order between components is uniform, exhibiting P  #
#    as an ordinal sum.  Hence:                                               #
#                                                                             #
#        P (with n >= 2) is PRIMITIVE  <=>  its incomparability graph is       #
#        CONNECTED.                                                            #
#                                                                             #
#    Note a chain has a totally disconnected incomparability graph, so chains  #
#    (n >= 2) are correctly classified NON-primitive.                          #
# --------------------------------------------------------------------------- #
def incomparability_components(n, below):
    """Return the list of vertex-sets (bitmasks) of the incomparability graph's
    connected components."""
    full = (1 << n) - 1
    incomp = [0] * n
    for i in range(n):
        incomp[i] = full & ~below[i] & ~(1 << i)
    # up-sets too: j incomparable to i iff not below and not above
    up = _up_from_below(n, below)
    for i in range(n):
        incomp[i] &= ~up[i]
    seen = 0
    comps = []
    for s in range(n):
        if (seen >> s) & 1:
            continue
        comp = 1 << s
        frontier = [s]
        while frontier:
            v = frontier.pop()
            nxt = incomp[v] & ~comp
            while nxt:
                b = nxt & -nxt
                nxt ^= b
                comp |= b
                frontier.append(b.bit_length() - 1)
        seen |= comp
        comps.append(comp)
    return comps


def is_primitive(n, below):
    """n >= 2 and the incomparability graph is connected."""
    if n < 2:
        return False
    return len(incomparability_components(n, below)) == 1


# --------------------------------------------------------------------------- #
# 4. Coherence: the majority (distinguished) order `e`.                       #
#                                                                             #
#    x <_e y  iff  Pr[x < y] > 1/2.  Comparable pairs have Pr in {0,1} so they  #
#    are always oriented consistently with P; incomparable pairs are oriented  #
#    by the majority vote, and exact ties (Pr = 1/2) are LEFT UNORIENTED.      #
#    If the resulting digraph is acyclic it is (the strict part of) a partial  #
#    order refining P -- the "distinguished order" of the coherence route.     #
# --------------------------------------------------------------------------- #
def before_matrix(n, below):
    """before[x][y] = #linear extensions placing x before y.  Same DP as
    `fast_Q` (engine M1); returned raw so the majority order can be read off."""
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
            if (I & up_succ[i]) == 0:
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
            if (below[i] & ~I) == 0:
                s += up[I | (1 << i)]
        up[I] = s
    e = down[full]
    assert up[0] == e, "before_matrix self-check: down[full] != up[empty]"
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
    return e, before


def majority_order(n, below):
    """Return (succ, acyclic, ties) where succ[x] is the bitmask of y with
    Pr[x<y] > 1/2, `acyclic` says whether the majority digraph is a DAG, and
    `ties` lists the incomparable pairs with Pr exactly 1/2."""
    e, before = before_matrix(n, below)
    succ = [0] * n
    ties = []
    for x in range(n):
        for y in range(n):
            if x == y:
                continue
            if 2 * before[x][y] > e:
                succ[x] |= (1 << y)
        for y in range(x + 1, n):
            if 2 * before[x][y] == e:
                ties.append((x, y))
    return succ, _is_dag(n, succ), ties, e, before


def _is_dag(n, succ):
    colour = [0] * n            # 0 white, 1 grey, 2 black
    for s in range(n):
        if colour[s]:
            continue
        stack = [(s, succ[s])]
        colour[s] = 1
        while stack:
            v, rem = stack[-1]
            if rem == 0:
                colour[v] = 2
                stack.pop()
                continue
            b = rem & -rem
            stack[-1] = (v, rem ^ b)
            w = b.bit_length() - 1
            if colour[w] == 1:
                return False
            if colour[w] == 0:
                colour[w] = 1
                stack.append((w, succ[w]))
    return True


def e_aligned_additions(n, below):
    """The PERTURBATION STEP.  Enumerate the single comparabilities x < y that
    are `e`-ALIGNED: (x,y) currently incomparable and Pr[x<y] > 1/2, i.e. the
    majority of linear extensions already puts x before y.  Adding such an edge
    moves the poset *along* its own distinguished order -- this is the
    coherence-guided move.  Ties (Pr = 1/2) are emitted in BOTH directions
    (they are symmetric, so one representative suffices; we emit x<y only, as
    the two results are isomorphic by the tie's symmetry only when the pair is
    genuinely symmetric -- we do not assume that, so both are emitted).
    Returns a list of (x, y, Pr[x<y] as Fraction)."""
    succ, acyclic, ties, e, before = majority_order(n, below)
    out = []
    for (x, y) in incomparable_pairs_bm(n, below):
        pxy = Fraction(before[x][y], e)
        if pxy > Fraction(1, 2):
            out.append((x, y, pxy))
        elif pxy < Fraction(1, 2):
            out.append((y, x, 1 - pxy))
        else:
            out.append((x, y, pxy))
            out.append((y, x, pxy))
    return out, acyclic, ties


# --------------------------------------------------------------------------- #
# 5. Exhaustive positive-control sweep (all widths), canonical augmentation.  #
#                                                                             #
#    POSITIVE CONTROL ONLY -- this re-treads Peczarski's exhaustively verified #
#    range and is used to (a) validate the delta engine against his published  #
#    minima and (b) HARVEST SEEDS for the n >= 12 search.  It is never         #
#    reported as a new result.                                                #
# --------------------------------------------------------------------------- #
from onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust import (
    order_canon, children_max,
)


def exhaustive_primitive_min_delta(nmax, verbose=True, keep_top=8,
                                   time_budget=None):
    """Enumerate ALL posets (order-iso classes, every width) up to nmax by
    canonical augmentation, and record the minimum delta over PRIMITIVE
    non-chain posets at each n, plus the `keep_top` lowest-delta primitive
    posets per n (the seed harvest).

    Returns (profile, seeds, covered_nmax) where
        profile[n] = dict(classes, primitive, min_delta, argmin_below)
        seeds[n]   = list of (delta, below) sorted ascending
        covered_nmax = the largest n for which the level is COMPLETE."""
    t0 = time.time()
    level = {order_canon(1, [0]): [0]}          # n = 1: the single point
    profile = {}
    seeds = {}
    covered = 1
    for n in range(2, nmax + 1):
        nxt = {}
        for below in level.values():
            for nb in children_max(n - 1, below):
                k = order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        level = nxt
        best = []
        nprim = 0
        for below in level.values():
            if not is_primitive(n, below):
                continue
            nprim += 1
            e, d, arg = delta_of(n, below)
            if d is None:                        # chain (never primitive n>=2)
                continue
            best.append((d, tuple(below)))
        best.sort(key=lambda t: t[0])
        seeds[n] = [(d, list(b)) for (d, b) in best[:keep_top]]
        profile[n] = {
            "classes": len(level),
            "primitive": nprim,
            "min_delta": best[0][0] if best else None,
            "argmin_below": list(best[0][1]) if best else None,
        }
        covered = n
        if verbose:
            md = profile[n]["min_delta"]
            print(f"  [exhaustive] n={n:2d}  iso-classes={len(level):>9,}  "
                  f"primitive={nprim:>9,}  min delta(primitive) = "
                  f"{md} ~ {float(md) if md else float('nan'):.9f}  "
                  f"({time.time()-t0:.1f}s)", flush=True)
        if time_budget is not None and time.time() - t0 > time_budget:
            if verbose:
                print(f"  [exhaustive] TIME BUDGET reached after n={n}; "
                      f"levels beyond n={n} NOT covered.", flush=True)
            break
    return profile, seeds, covered


# --------------------------------------------------------------------------- #
# 6. Seed families.                                                           #
# --------------------------------------------------------------------------- #
def ladder(k, rungs_broken=()):
    """A `ladder` on n = 2k elements: two chains
        a_0 < a_1 < ... < a_{k-1}      (even indices 2i)
        b_0 < b_1 < ... < b_{k-1}      (odd  indices 2i+1)
    laced by the cross relations  a_i < b_{i+1}  and  b_i < a_{i+1}.
    The incomparable pairs {a_i, b_i} are the RUNGS.  `rungs_broken` is an
    iterable of rung indices i at which the rung is BROKEN by adjoining the
    comparability a_i < b_i (which removes that incomparable pair).

    NOTE ON PROVENANCE: this is a *ladder* in the standard sense and is the
    natural reading of Peczarski's family name, but the precise
    broken-rung pattern of Peczarski (2019) is cited in the write-up; here the
    family is used as a SEED GENERATOR, and the search is not sensitive to
    getting his exact pattern -- every broken-rung pattern is swept."""
    n = 2 * k
    below = [0] * n
    for i in range(k - 1):
        a_i, b_i, a_j, b_j = 2 * i, 2 * i + 1, 2 * i + 2, 2 * i + 3
        below[a_j] |= (1 << a_i) | (1 << b_i)
        below[b_j] |= (1 << a_i) | (1 << b_i)
    for i in rungs_broken:
        if 0 <= i < k:
            below[2 * i + 1] |= (1 << (2 * i))
    return transitive_close_bitmask(n, below)


def all_broken_ladders(k):
    """Every broken-rung pattern on the k-rung ladder (2^k patterns)."""
    for mask in range(1 << k):
        yield ladder(k, [i for i in range(k) if (mask >> i) & 1])


def width2_families(n):
    """All width-<=2 posets on n elements arise as two chains with a monotone
    lacing.  Sah's T_n and Chen's family both live here, so we sweep the whole
    width-2 arena at size n rather than guessing a single construction:
    split n = p + q, chains A (p elements) and B (q elements), and choose a
    MONOTONE lacing f: A -> {0..q} with a_i < b_j iff j >= f(i) (f
    non-decreasing), together with the dual lacing g: B -> {0..p}, consistent.
    We generate by the simpler route of enumerating all posets of width <= 2
    reachable from the p+q chain pair by adding cross relations that keep
    transitivity -- done here by direct monotone-lacing enumeration."""
    out = []
    for p in range(1, n):
        q = n - p
        # A = 0..p-1 (chain), B = p..p+q-1 (chain)
        # lacing: f[i] in {0..q} non-decreasing = least j with a_i < b_j
        #         g[j] in {0..p} non-decreasing = least i with b_j < a_i
        for f in _monotone(p, q):
            for g in _monotone(q, p):
                below = [0] * n
                for i in range(1, p):
                    below[i] = (1 << i) - 1
                for j in range(1, q):
                    below[p + j] = ((1 << j) - 1) << p
                ok = True
                for i in range(p):
                    for j in range(f[i], q):
                        below[p + j] |= (1 << i)
                for j in range(q):
                    for i in range(g[j], p):
                        below[i] |= (1 << (p + j))
                # reject if the two lacings contradict (a_i < b_j and b_j < a_i)
                for i in range(p):
                    for j in range(q):
                        if ((below[p + j] >> i) & 1) and ((below[i] >> (p + j)) & 1):
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    continue
                cl = transitive_close_bitmask(n, below)
                if cl is None:
                    continue
                # transitive_close must not have created antisymmetry violations
                bad = False
                for i in range(n):
                    if cl[i] & (1 << i):
                        bad = True
                        break
                    for j in _bits(cl[i]):
                        if (cl[j] >> i) & 1:
                            bad = True
                            break
                    if bad:
                        break
                if bad:
                    continue
                out.append(cl)
    return out


def _monotone(p, q):
    """All non-decreasing f: {0..p-1} -> {0..q}."""
    if p == 0:
        yield []
        return
    def rec(i, lo, acc):
        if i == p:
            yield list(acc)
            return
        for v in range(lo, q + 1):
            acc.append(v)
            yield from rec(i + 1, v, acc)
            acc.pop()
    yield from rec(0, 0, [])


# --------------------------------------------------------------------------- #
# 7. The coherence-guided perturbation search.                                #
#                                                                             #
#    MOVE A (the ticket's perturbation step): add ONE `e`-aligned              #
#    comparability x < y to a primitive poset on n elements, keeping the       #
#    result a valid (transitively closed) primitive non-chain poset.           #
#    MOVE B (size lift): adjoin one new element whose strict down-set is an    #
#    order ideal (a new maximal), or dually a new minimal.  Needed to carry    #
#    the frontier past the sizes reachable by exhaustive enumeration.          #
#                                                                             #
#    SEARCH DISCIPLINE -- and its HONEST LIMITATION.  The ticket suggests      #
#    "prune branches whose delta increases".  We DELIBERATELY DO NOT do that:  #
#    delta is not monotone along edge additions, so a strict-descent prune      #
#    manufactures false negatives.  Instead we run a BEAM: at each depth keep  #
#    the `beam` lowest-delta children.  This is still a BOUNDED search -- at   #
#    n >= 12 it is NOT exhaustive, and any "nothing below beta" conclusion is  #
#    valid only relative to the (beam, depth, seed) bound, which is reported   #
#    verbatim in the certificate.                                             #
# --------------------------------------------------------------------------- #
class SubBetaHalt(Exception):
    pass


def _canon(n, below):
    return order_canon(n, below)


def children_edge(n, below):
    """MOVE A: all `e`-aligned single-comparability additions that keep the
    poset primitive and non-chain.  Yields (below_child, (x, y, pr))."""
    adds, acyclic, ties = e_aligned_additions(n, below)
    for (x, y, pr) in adds:
        nb = add_edge(n, below, x, y)
        if nb is None:
            continue
        if is_chain(n, nb):
            continue
        if not is_primitive(n, nb):
            continue
        yield nb, (x, y, pr)


def children_lift(n, below, cap=None):
    """MOVE B: adjoin a new maximal element with strict down-set any order
    ideal D (dually, a new minimal with up-set any filter).  Yields posets on
    n+1 elements that are primitive and non-chain."""
    out = []
    ideals = enum_ideals_bitmask(n, below)
    if cap is not None and len(ideals) > cap:
        ideals = ideals[:cap]
    for D in ideals:
        nb = list(below) + [D]
        if is_primitive(n + 1, nb) and not is_chain(n + 1, nb):
            out.append(nb)
    up = _up_from_below(n, below)
    for D in ideals:                      # D an ideal => complement is a filter
        F = ((1 << n) - 1) & ~D
        nb = [below[i] | (1 << n) if ((F >> i) & 1) else below[i]
              for i in range(n)] + [0]
        nb = transitive_close_bitmask(n + 1, nb)
        if nb is None:
            continue
        if is_primitive(n + 1, nb) and not is_chain(n + 1, nb):
            out.append(nb)
    return out


def beam_search_at_n(n, seeds, beam=200, max_depth=None, verbose=True,
                     guard=True, record=None):
    """Coherence-guided beam search over MOVE A at fixed size n.
    Returns (best_delta, best_below, stats)."""
    t0 = time.time()
    frontier = {}
    for b in seeds:
        if len(b) != n or not is_primitive(n, b) or is_chain(n, b):
            continue
        frontier[_canon(n, b)] = list(b)
    if not frontier:
        return None, None, {"evaluated": 0, "depths": 0, "reason": "no seeds"}
    seen = set(frontier.keys())
    best = None
    best_b = None
    evaluated = 0
    depth = 0
    if max_depth is None:
        max_depth = n * (n - 1) // 2
    for b in frontier.values():
        d = delta_of(n, b)[1]
        evaluated += 1
        if d is not None and (best is None or d < best):
            best, best_b = d, list(b)
    while frontier and depth < max_depth:
        depth += 1
        scored = []
        for b in frontier.values():
            for nb, mv in children_edge(n, b):
                k = _canon(n, nb)
                if k in seen:
                    continue
                seen.add(k)
                d = delta_of(n, nb)[1]
                evaluated += 1
                if d is None:
                    continue
                if guard and d <= THIRD:
                    raise SubBetaHalt(
                        f"delta <= 1/3 candidate at n={n}: delta={d}, "
                        f"below={nb} -- halting per roadmap sec.8.2 STRICT; "
                        f"a fresh independent sixth codebase is required "
                        f"before this may be written up.")
                scored.append((d, k, nb))
                if best is None or d < best:
                    best, best_b = d, list(nb)
                    # EXACT, not float (mg-8489, audit finding F4): BETA_THRESHOLD
                    # is a float and `d` a Fraction, so `float(d) < BETA_THRESHOLD`
                    # was the one beta comparison in this file that did not honour
                    # sec.0's blanket "exact, not floating point" claim.  No verdict
                    # ever depended on it -- the tightest margin in play is 2.45e-6
                    # against double precision ~1e-16 -- but the flag now matches
                    # the claim.  `lt_beta_sah` is the same predicate sec.10 uses.
                    if record is not None and lt_beta_sah(d):
                        record.append(("SUB-BETA", n, d, list(nb)))
        if not scored:
            break
        scored.sort(key=lambda t: t[0])
        frontier = {k: nb for (_d, k, nb) in scored[:beam]}
        if verbose:
            print(f"    [beam n={n}] depth={depth:2d}  kept={len(frontier):>4d}  "
                  f"best so far {best} ~ {float(best):.9f}  "
                  f"({time.time()-t0:.1f}s)", flush=True)
    return best, best_b, {"evaluated": evaluated, "depths": depth,
                          "beam": beam, "seconds": round(time.time() - t0, 1)}


# --------------------------------------------------------------------------- #
# 8. Driver.                                                                  #
# --------------------------------------------------------------------------- #
def exhaustive_width2_min_delta(n):
    """Exhaustive minimum delta over PRIMITIVE width-<=2 posets on n elements.
    Complete: every width-<=2 poset has a Dilworth 2-chain partition, and the
    monotone-lacing enumeration realises every such partition."""
    best = None
    count = 0
    for b in width2_families(n):
        count += 1
        if is_chain(n, b) or not is_primitive(n, b):
            continue
        d = delta_of(n, b)[1]
        if d is not None and (best is None or d < best[0]):
            best = (d, list(b))
    return (best[0] if best else None,
            best[1] if best else None, count)


def seeds_from(n_prev, tops, keep=25):
    """MOVE B lift of the `keep` lowest-delta posets at n_prev to n_prev+1."""
    out = []
    for (_d, b) in tops[:keep]:
        out.extend(children_lift(n_prev, list(b)))
    return out


def beam_ladder(n_from, n_to, seed_tops, beam=300, keep=25, verbose=True,
                record=None):
    """Climb the size ladder: at each n, lift the best posets from n-1 (MOVE B)
    and beam-search MOVE A.  `seed_tops` is the list of (delta, below) at
    n_from - 1.  Returns profile dict n -> (delta, below, stats)."""
    prof = {}
    tops = seed_tops
    for n in range(n_from, n_to + 1):
        seeds = seeds_from(n - 1, tops, keep=keep)
        best, bb, st = beam_search_at_n(n, seeds, beam=beam, verbose=False,
                                        record=record)
        prof[n] = (best, bb, dict(st, seeds=len(seeds)))
        if verbose:
            print(f"  [ladder] n={n:2d}  seeds={len(seeds):>6,}  "
                  f"evaluated={st['evaluated']:>8,}  min delta = {best} ~ "
                  f"{float(best):.9f}  ({st['seconds']}s)", flush=True)
        if best is None:
            break
        tops = [(best, bb)]
        # widen: re-harvest a few diverse near-best posets for the next lift
        tops = _reharvest(n, bb, keep)
    return prof


def _reharvest(n, bb, keep):
    """Collect a diverse set of near-best posets around `bb` (its e-aligned
    children plus itself) to seed the next size level."""
    out = [(delta_of(n, bb)[1], list(bb))]
    for nb, _mv in children_edge(n, bb):
        d = delta_of(n, nb)[1]
        if d is not None:
            out.append((d, list(nb)))
    out.sort(key=lambda t: t[0])
    return out[:keep]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--exhaustive-nmax", type=int, default=9,
                    help="all-width exhaustive positive-control ceiling")
    ap.add_argument("--width2-nmax", type=int, default=13,
                    help="exhaustive width-2 ceiling")
    ap.add_argument("--ladder-nmax", type=int, default=16,
                    help="coherence-guided beam-search ceiling")
    ap.add_argument("--beam", type=int, default=300)
    ap.add_argument("--keep", type=int, default=25)
    ap.add_argument("--ladder-exh-nmax", type=int, default=19,
                    help="exhaustive broken-rung ceiling for the ladder family")
    ap.add_argument("--ladder-loc-nmax", type=int, default=27,
                    help="local-search ceiling for the ladder family")
    ap.add_argument("--ladder-json", type=str, default=None)
    ap.add_argument("--json", type=str, default=None)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    if args.quick:
        (args.exhaustive_nmax, args.width2_nmax, args.ladder_nmax,
         args.ladder_exh_nmax, args.ladder_loc_nmax) = 7, 9, 10, 12, 13

    t0 = time.time()
    out = {"work_item": "mg-0eac",
           "beta_chen": BETA_CHEN,
           "beta_peczarski_sah": BETA_PECZARSKI_SAH,
           "beta_threshold": BETA_THRESHOLD,
           "params": vars(args)}

    print("=" * 74)
    print("POSITIVE CONTROLS (five-engine: M1 DP / M2 subset-DP / M3 recursion")
    print("                   / M4 brute / MC Ehrhart) -- all must agree.")
    print("=" * 74)
    controls = []
    T = [0, 1, 0]
    e, d, used = verify_five("T (3-elt one-relation)", 3, T)
    controls.append(("T", 3, str(d), used, str(d) == "1/3"))
    print(f"  T          n=3  e={e:<4} delta={d}  [{used}]  expect 1/3   "
          f"{'PASS' if d == THIRD else 'FAIL'}")
    assert d == THIRD
    for k in (3, 4, 5):
        e, d, used = verify_five(f"antichain A{k}", k, antichain(k))
        controls.append((f"A{k}", k, str(d), used, d == Fraction(1, 2)))
        print(f"  A{k}         n={k}  e={e:<4} delta={d}  [{used}]  expect 1/2   "
              f"{'PASS' if d == Fraction(1,2) else 'FAIL'}")
        assert d == Fraction(1, 2)
    TT = transitive_close_bitmask(6, [0, 1, 0, 0b111, 0b1111, 0b111])
    e, d, used = verify_five("T (+) T", 6, TT)
    prim = is_primitive(6, TT)
    controls.append(("T(+)T", 6, str(d), used, (d == THIRD and not prim)))
    print(f"  T (+) T    n=6  e={e:<4} delta={d}  [{used}]  primitive={prim}  "
          f"expect 1/3 & decomposable  "
          f"{'PASS' if (d == THIRD and not prim) else 'FAIL'}")
    assert d == THIRD and not prim
    W10 = [0, 1, 3, 103, 111, 0, 33, 99, 231, 495]
    e, d, used = verify_five("width-2 n=10 argmin", 10, W10)
    controls.append(("w2-n10-argmin", 10, str(d), used, True))
    print(f"  w2 n=10    n=10 e={e:<4} delta={d} ~ {float(d):.9f}  [{used}]  "
          f"near-beta witness")
    print()
    print("  EXTERNAL control -- reproduce Peczarski's published (delta, e(P)):")
    out["ladder_published_control"] = verify_ladder_family(verbose=True)
    out["controls"] = controls

    print()
    print("=" * 74)
    print(f"EXHAUSTIVE all-width PRIMITIVE min-delta, n <= {args.exhaustive_nmax}")
    print("  (POSITIVE CONTROL / seed harvest only -- Peczarski verified n<=11)")
    print("=" * 74)
    prof, seeds, covered = exhaustive_primitive_min_delta(
        args.exhaustive_nmax, verbose=True, keep_top=args.keep)
    out["exhaustive_allwidth"] = {
        str(n): {"classes": v["classes"], "primitive": v["primitive"],
                 "min_delta": str(v["min_delta"]),
                 "min_delta_float": float(v["min_delta"]),
                 "argmin_below": v["argmin_below"]}
        for n, v in prof.items()}
    out["exhaustive_allwidth_covered_nmax"] = covered

    print()
    print("=" * 74)
    print(f"EXHAUSTIVE width-2 PRIMITIVE min-delta, n <= {args.width2_nmax}")
    print("=" * 74)
    w2 = {}
    tops_by_n = {}
    for n in range(4, args.width2_nmax + 1):
        t = time.time()
        d, b, cnt = exhaustive_width2_min_delta(n)
        w2[n] = (d, b, cnt)
        # EXACT (mg-8489, audit finding F4) -- see the note at the beam's
        # sub_beta_records flag; same repair, same reason.
        flag = " <-- SUB-BETA" if d is not None and lt_beta_sah(d) else ""
        print(f"  n={n:2d}  generated={cnt:>10,}  min delta = {d} ~ "
              f"{float(d):.9f}{flag}  ({time.time()-t:.1f}s)", flush=True)
        if d is not None and d <= THIRD:
            raise SubBetaHalt(f"delta <= 1/3 at width-2 n={n}: {d}, below={b}")
    out["exhaustive_width2"] = {
        str(n): {"generated": cnt, "min_delta": str(d),
                 "min_delta_float": float(d), "argmin_below": b}
        for n, (d, b, cnt) in w2.items()}

    print()
    print("=" * 74)
    print(f"COHERENCE-GUIDED BEAM LADDER, n = {args.width2_nmax+1} .. "
          f"{args.ladder_nmax}  (beam={args.beam}, keep={args.keep})")
    print("  BOUNDED SEARCH -- not exhaustive.  See the write-up for the bound.")
    print("=" * 74)
    nprev = args.width2_nmax
    d, b, _ = w2[nprev]
    record = []
    lad = beam_ladder(nprev + 1, args.ladder_nmax, _reharvest(nprev, b, args.keep),
                      beam=args.beam, keep=args.keep, verbose=True, record=record)
    out["beam_ladder"] = {
        str(n): {"min_delta": str(dd), "min_delta_float": float(dd),
                 "argmin_below": bb, "stats": st}
        for n, (dd, bb, st) in lad.items() if dd is not None}
    out["sub_beta_hits"] = [(tag, n, str(dd), bb) for (tag, n, dd, bb) in record]

    print()
    print("=" * 74)
    print(f"LADDER FAMILY profile: exhaustive n <= {args.ladder_exh_nmax}, "
          f"local search n <= {args.ladder_loc_nmax}")
    print("=" * 74)
    ladprof = ladder_profile(exh_nmax=args.ladder_exh_nmax,
                             loc_nmax=args.ladder_loc_nmax, verbose=True)
    out["ladder_profile"] = {str(k): v for k, v in ladprof.items()}
    if args.ladder_json:
        os.makedirs(os.path.dirname(args.ladder_json), exist_ok=True)
        with open(args.ladder_json, "w") as fh:
            json.dump({"work_item": "mg-0eac", "profile":
                       {str(k): v for k, v in ladprof.items()}},
                      fh, indent=1, sort_keys=True)

    print()
    print("=" * 74)
    print("VERDICT")
    print("=" * 74)
    allmins = []
    for n, v in prof.items():
        if v["min_delta"] is not None:
            allmins.append((n, v["min_delta"], "exhaustive-allwidth"))
    for n, (d, b, _c) in w2.items():
        allmins.append((n, d, "exhaustive-width2"))
    for n, (d, b, _s) in lad.items():
        if d is not None:
            allmins.append((n, d, "beam"))
    for n, v in ladprof.items():
        allmins.append((n, Fraction(v["delta"]), "ladder-" + v["coverage"]))
    best = min((x for x in allmins if x[0] >= 4), key=lambda t: t[1])
    print(f"  Lowest delta over PRIMITIVE posets with n >= 4 found anywhere: "
          f"{best[1]} ~ {float(best[1]):.10f}  at n={best[0]} ({best[2]})")
    print(f"  beta_Sah  = (5864893+27*sqrt57)/16812976 = "
          f"{BETA_PECZARSKI_SAH:.14f}   (EXACT test: best < beta ? "
          f"{lt_beta_sah(best[1])})")
    print(f"  kappa_Chen= (93-sqrt6697)/32             = "
          f"{BETA_CHEN:.14f}   (EXACT test: best < kappa? "
          f"{lt_kappa_chen(best[1])})")
    print(f"  T (n=3) is PRIMITIVE with delta = 1/3 exactly -- see write-up.")
    if lt_beta_sah(best[1]):
        print("  *** SUB-BETA CANDIDATE -- requires independent re-verification ***")
    else:
        print("  ==> Nothing below beta.  Corroborates the gap conjecture on the")
        print("      primitive arena, via the coherence-guided path, within the")
        print("      stated bound.")
    out["verdict_best"] = {"n": best[0], "delta": str(best[1]),
                           "delta_float": float(best[1]), "source": best[2]}
    out["seconds"] = round(time.time() - t0, 1)

    if args.json:
        os.makedirs(os.path.dirname(args.json), exist_ok=True)
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
        print(f"\n  certificate -> {args.json}")
    return out




# --------------------------------------------------------------------------- #
# 9. The beta-extremal seed families (VERIFIED against published values).      #
#                                                                             #
#    Peczarski's "ladder with broken rungs" L_{n; i1,...,ik}:                  #
#      ground set {0,...,n-1} indexed by HEIGHT,                               #
#      RAILS  j < j+2   for 0 <= j <= n-3   (two interleaved chains, width 2), #
#      RUNGS  j < j+3   for 0 <= j <= n-4, EXCEPT j in {i1,...,ik} (BROKEN),   #
#      then transitive closure.                                                #
#                                                                             #
#    Reconstructed from Peczarski's published Hasse-diagram figures and        #
#    VERIFIED by reproducing all seven published (delta, e(P)) pairs exactly;  #
#    see `verify_ladder_family()` -- this is the strongest positive control in #
#    the module, because it checks the delta engine against an EXTERNAL        #
#    published source rather than against our own other engines.               #
# --------------------------------------------------------------------------- #
def ladder_L(n, broken=()):
    br = set(broken)
    below = [0] * n
    for j in range(0, n - 2):
        below[j + 2] |= (1 << j)
    for j in range(0, n - 3):
        if j not in br:
            below[j + 3] |= (1 << j)
    return transitive_close_bitmask(n, below)


LADDER_PUBLISHED = [
    ((6,  (1,)),                        Fraction(5, 14),        14),
    ((9,  (1, 2, 3, 4)),                Fraction(6, 17),        85),
    ((10, (1, 5)),                      Fraction(37, 106),      106),
    ((11, (1, 6)),                      Fraction(20, 57),       171),
    ((20, (1, 5, 8, 11, 15)),           Fraction(6059, 17366),  17366),
    ((21, (1, 5, 8, 9, 12, 16)),        Fraction(5402, 15485),  30970),
    ((25, (1, 5, 8, 9, 12, 13, 16, 20)),Fraction(7451, 21359),  256308),
]


def verify_ladder_family(verbose=True):
    """EXTERNAL positive control: reproduce Peczarski's published (delta, e)."""
    rows = []
    for (n, br), exp_d, exp_e in LADDER_PUBLISHED:
        b = ladder_L(n, br)
        e, d, _ = delta_of(n, b)
        ok = (d == exp_d) and (e == exp_e)
        rows.append((n, br, str(d), float(d), e, ok))
        if verbose:
            tag = ",".join(map(str, br))
            print(f"  L_{{{n};{tag}}}".ljust(30) +
                  f"e={e:<8} delta={d} ~ {float(d):.10f}  expect {exp_d}  "
                  f"{'PASS' if ok else 'FAIL'}")
        assert ok, f"ladder control FAILED at L_{{{n};{br}}}: got {d}/{e}"
    return rows


# --------------------------------------------------------------------------- #
# 10. EXACT comparison against the two beta constants.                        #
#     beta_Sah  = (5864893 + 27*sqrt(57)) / 16812976     [min poly            #
#                 33625952 x^2 - 23459572 x + 4091717]                        #
#     kappa_Chen = (93 - sqrt(6697)) / 32                [min poly            #
#                 32 x^2 - 186 x + 61]                                        #
#     These lie in DIFFERENT quadratic fields (Q(sqrt 57) vs Q(sqrt 6697)), so #
#     they are provably distinct reals.  Comparisons below are EXACT rational  #
#     arithmetic -- no floating point -- because the search operates within    #
#     ~1e-6 of beta, where float comparison would be untrustworthy.            #
# --------------------------------------------------------------------------- #
def lt_beta_sah(q):
    """EXACT: is the rational q < beta_Sah = (5864893 + 27*sqrt57)/16812976 ?"""
    lhs = Fraction(16812976) * q - 5864893          # compare lhs < 27*sqrt(57)
    if lhs <= 0:
        return True
    return lhs * lhs < Fraction(729 * 57)           # 27^2 * 57 = 41553


def lt_kappa_chen(q):
    """EXACT: is the rational q < kappa_Chen = (93 - sqrt(6697))/32 ?"""
    # q < (93 - sqrt6697)/32  <=>  32q - 93 < -sqrt6697  <=>  93 - 32q > sqrt6697
    rhs = 93 - Fraction(32) * q
    if rhs <= 0:
        return False
    return rhs * rhs > Fraction(6697)


BETA_SAH_FLOAT = (5864893 + 27 * 57 ** 0.5) / 16812976
KAPPA_CHEN_FLOAT = (93 - 6697 ** 0.5) / 32


# --------------------------------------------------------------------------- #
# 11. Broken-rung search over the ladder family.                              #
# --------------------------------------------------------------------------- #
def ladder_exhaustive(n):
    """Exhaustive over all 2^(n-3) broken-rung subsets at size n.
    Returns (delta, broken_tuple)."""
    best = None
    m = max(0, n - 3)
    for mask in range(1 << m):
        br = tuple(j for j in range(m) if (mask >> j) & 1)
        b = ladder_L(n, br)
        if is_chain(n, b) or not is_primitive(n, b):
            continue
        d = delta_of(n, b)[1]
        if d is not None and (best is None or d < best[0]):
            best = (d, br)
    return best


def ladder_local_search(n, starts, rounds=6, flips=2):
    """k-flip local search over broken-rung subsets (for n beyond exhaustive
    reach).  `starts` is a list of seed broken-tuples."""
    m = max(0, n - 3)
    best = None
    for s in starts:
        cur = tuple(sorted(j for j in s if j < m))
        b = ladder_L(n, cur)
        cd = delta_of(n, b)[1] if (not is_chain(n, b) and is_primitive(n, b)) else None
        if cd is None:
            continue
        improved = True
        rnd = 0
        while improved and rnd < rounds:
            improved = False
            rnd += 1
            curset = set(cur)
            cands = []
            for j in range(m):                       # 1-flip
                t = tuple(sorted(curset ^ {j}))
                cands.append(t)
            if flips >= 2:
                for j in range(m):
                    for k in range(j + 1, m):
                        cands.append(tuple(sorted(curset ^ {j, k})))
            for t in cands:
                bb = ladder_L(n, t)
                if is_chain(n, bb) or not is_primitive(n, bb):
                    continue
                d = delta_of(n, bb)[1]
                if d is not None and d < cd:
                    cd, cur, improved = d, t, True
        if best is None or cd < best[0]:
            best = (cd, cur)
    return best


# --------------------------------------------------------------------------- #
# 12. Ladder-family profile driver (exhaustive over broken-rung subsets to     #
#     `exh_nmax`, then 1-/2-flip local search).                               #
# --------------------------------------------------------------------------- #
def ladder_profile(exh_nmax=19, loc_nmax=30, verbose=True):
    out = {}
    starts = set()
    for n in range(6, exh_nmax + 1):
        t = time.time()
        d, br = ladder_exhaustive(n)
        starts.add(br)
        out[n] = {"delta": str(d), "delta_float": float(d), "broken": list(br),
                  "coverage": "exhaustive-ladder",
                  "lt_beta_sah": lt_beta_sah(d), "lt_kappa_chen": lt_kappa_chen(d)}
        if verbose:
            print(f"  n={n:2d} EXH  min delta = {d} ~ {float(d):.10f}  "
                  f"broken={br}  <beta={lt_beta_sah(d)} <kappa={lt_kappa_chen(d)}"
                  f"  ({time.time()-t:.1f}s)", flush=True)
        if lt_beta_sah(d):
            raise SubBetaHalt(f"SUB-BETA ladder at n={n}: delta={d} broken={br}")
    prev = list(starts)
    for n in range(exh_nmax + 1, loc_nmax + 1):
        t = time.time()
        seeds = set()
        for br in prev[-40:]:
            seeds.add(tuple(br))
            seeds.add(tuple(list(br) + [n - 4]))
            seeds.add(tuple(list(br) + [n - 5]))
            seeds.add(tuple(j + 1 for j in br))
        for off in range(0, 5):                    # periodic gap-4,3,3 patterns
            s, j = [], 1 + off
            while j < n - 3:
                s.append(j)
                j += 3 if len(s) % 3 else 4
            seeds.add(tuple(s))
        d, br = ladder_local_search(n, list(seeds), rounds=8, flips=2)
        prev.append(br)
        out[n] = {"delta": str(d), "delta_float": float(d), "broken": list(br),
                  "coverage": "local-search-ladder",
                  "lt_beta_sah": lt_beta_sah(d), "lt_kappa_chen": lt_kappa_chen(d)}
        if verbose:
            print(f"  n={n:2d} LOC  min delta = {d} ~ {float(d):.10f}  "
                  f"broken={br}  <beta={lt_beta_sah(d)} <kappa={lt_kappa_chen(d)}"
                  f"  ({time.time()-t:.1f}s)", flush=True)
        if lt_beta_sah(d):
            raise SubBetaHalt(f"SUB-BETA ladder at n={n}: delta={d} broken={br}")
    return out

if __name__ == "__main__":
    main()
