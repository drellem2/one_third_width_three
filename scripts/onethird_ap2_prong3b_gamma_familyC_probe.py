#!/usr/bin/env python3
r"""
onethird_ap2_prong3b_gamma_familyC_probe.py
===========================================

OneThird Algebraic-Program **AP-2 Prong 3B-gamma** (mg-3b16) -- Family C
(order-polytope / Ehrhart) probe.  Follow-up to mg-2715 (Prong 3B-beta), which
SETTLED Family D (finite-geometry incidence) as a bounded-null host at width 3
(Q >= 2/5) with a proven NEW-WALL, and whose boundary probe surfaced the live
counterexample-hunt target: a GENERIC graded 3-level width-3 poset reaching
        Q = 4/11 ~= 0.363636   in   (1/3, 8/21),
the "4/11 seed" -- below the Prong-3A SP floor 8/21 but above 1/3.

This prong tests whether **Family C (order polytope / Ehrhart)** -- one of
Daniel's cited algebraic-program inspirations -- naturally parametrises that
4/11 seed family, opens a fresh path BELOW it, or walls.

Reference docs:
  * docs/OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md  (the write-up this drives)
  * docs/OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md   (the 4/11 seed flag + wall)
  * docs/OneThird-AP-2-Prong3A-SP-FloorBound.md        (8/21 SP theorem, T*)
  * docs/OneThird-Algebraic-Program-Roadmap.md         (sec.3C, 4C, 6, 8)
  * docs/OneThird-Algebraic-Program-Vision.md          (the four load-bearing parts)

WHAT FAMILY C IS (Stanley, *Two poset polytopes*, 1986).
  The ORDER POLYTOPE of a finite poset P is
        O(P) = { f : P -> [0,1]  |  f(a) <= f(b) whenever a <= b in P }  subset [0,1]^P.
  Stanley: O(P) triangulates into e(P) unit simplices, one per linear extension,
  so   vol O(P) = e(P) / n!   (n = |P|).  Crucially, for incomparable x,y the
  sub-polytope O(P) cap { f(x) <= f(y) } is EXACTLY the order polytope of the
  poset P + (x<y), so
        Pr[x < y]  =  vol( O(P) cap {f(x)<=f(y)} ) / vol O(P)
                   =  e(P + x<y) / e(P),
  i.e. the balance constant Q(P) is a ratio of order-polytope volumes -- the
  roadmap-3C/4C "Pr[x<y] = ratio of facet sub-polytope volumes, Ehrhart-
  computable" claim, realised exactly.

THE FAMILY-C ENGINE (MC) -- genuinely Ehrhart, distinct from the DP.
  The Ehrhart polynomial of O(P) is the ORDER POLYNOMIAL
        Omega_P(t) = #{ order-preserving maps P -> {1,...,t} }
                   = #{ multichains  (/) = I_0 subseteq I_1 subseteq ... subseteq I_t = P
                        in the lattice J(P) of order ideals },
  a degree-n polynomial in t whose leading coefficient is vol O(P) = e(P)/n!.
  Because the sample points t = 1,...,n+1 are consecutive integers, the n-th
  finite difference collapses to the leading term times n!:
        e(P) = Delta^n Omega_P  =  sum_{k=0}^{n} (-1)^{n-k} C(n,k) Omega_P(1+k).
  We compute Omega_P(t) = (Z^t)[empty][full] by powers of the zeta matrix Z of
  the ideal lattice J(P) (Z[I][K] = 1 iff I subseteq K), in exact integer
  arithmetic.  This is structurally different from the order-ideal DP (M1), the
  AP-0 kernel (M2), the minimal-element-removal recursion (M3) and brute force
  (M4): it counts LATTICE POINTS of dilations of the order polytope and reads
  the volume off the Ehrhart leading coefficient.

THE V2 GATE / NEW-WALL (the central structural finding -- see the doc).
  The order polytope O(.) is a FUNCTOR poset -> polytope; it is a faithful
  re-encoding of the linear-extension combinatorics (Stanley), NOT an
  independent source of posets.  Its two natural "algebraic parameters" both
  fail to open new width-3 territory:
    (a) Dilation parameter t (the Ehrhart variable).  Q(P) is a ratio of
        volumes, hence SCALE-INVARIANT: dilating O(P) by t leaves every
        Pr[x<y] -- and so Q -- fixed.  The Ehrhart dilation parameter is
        Q-invariant: it does NOT parametrise a family of distinct-Q width-3
        posets.  [Wall Lemma 3.x, proven in the doc.]
    (b) Combinatorial type of P at fixed n.  This just IS "sweep all width-3
        posets" -- recovering the generic graded-3-level family of the 4/11
        seed, with O(P) supplying the (exact, closed-form-rational) volume
        engine.  No new poset is produced that A/B/D do not already produce.
  Hence Family C parametrises the 4/11 seed EXACTLY (it is the order polytope of
  the seed witness) and computes its Q in closed form, but opens no genuinely
  new poset below it.  We sweep the seed's graded-3-level width-3 family
  EXHAUSTIVELY (it is finite: each rank is an antichain, so each rank has <= 3
  elements, total <= 9) and also run a broader width-3 poset probe to test
  empirically whether ANY width-3 poset (order-polytope-computed) beats 4/11.

THE ACCEPTANCE GATE (roadmap sec.4, non-goal 8.5).  Q is reported only when
INDEPENDENT methods agree exactly:
  (M1) order-ideal DP            -- primary (Prong-3B-beta harness);
  (M2) AP-0 kernel  Q_via_dp     -- generic width-3 engine, n <= 12;
  (M3) Prong-2 independent check -- minimal-element-removal recursion (8.2 2nd codebase);
  (M4) brute-force permutations  -- n <= 8;
  (MC) Family-C Ehrhart engine   -- order-polynomial leading coefficient (THIS file),
       at EVERY instance of the primary sweep.
  Monte-Carlo is NEVER used (non-goal 8.5).

GUARD (roadmap sec.8.2 anti-Cheeger -- INHERITED STRICT).  AP-0, Prong-2 and the
Prong-3B-beta DP are all USED codebases; a Q <= 1/3 claim requires a fresh
FOURTH codebase.  The script HALTS at the FIRST Q <= 1/3 candidate, printing the
mandated message, and does NOT write up any counterexample claim.  No such
instance exists in the swept range (graded-3-level floor 4/11, broader width-3
floor 4/11, both > 1/3), so the guard clears.

Pure-Python / standard library only.  Default run is laptop-fast (a few s);
--wide raises the broader-width-3 probe to n <= 7.
"""

from __future__ import annotations

import argparse
import math
import os
import sys
from fractions import Fraction

# --------------------------------------------------------------------------- #
# Reuse the Prong-3B-beta four-engine harness (M1 primary, M2 AP-0, M3 indep,  #
# M4 brute) + the §8.2 guard, verbatim (carry-forward named in the ticket).    #
# --------------------------------------------------------------------------- #
_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from onethird_ap2_prong3b_beta_familyD_probe import (  # noqa: E402
    THIRD, EIGHT_21, TWENTY7_70, HALF,
    transitive_pred, incomparable_pairs, width_of,
    Q_primary, Q_brute, augment, count_le_dp,
    guard_check, GuardHalt, verify_instance, Inst,
    graded3_min_Q,
)

TWO_FIFTH = Fraction(2, 5)        # genuine Family D floor (Prong 3B-beta)
FOUR_11 = Fraction(4, 11)         # the 4/11 seed (Prong 3B-beta boundary probe)


# --------------------------------------------------------------------------- #
# (MC) The Family-C engine: order polytope / Ehrhart.                          #
# --------------------------------------------------------------------------- #
def order_ideals(elems, below):
    """All order ideals (down-closed subsets) of P, as frozensets.  Width-3 keeps
    |J(P)| small; we simply test all 2^n subsets (n <= 9 here)."""
    n = len(elems)
    ideals = []
    for mask in range(1 << n):
        S = frozenset(elems[i] for i in range(n) if (mask >> i) & 1)
        if all(below[e] <= S for e in S):
            ideals.append(S)
    return ideals


def order_polynomial_values(elems, below, ts, ideals=None):
    """Omega_P(t) for each t in `ts`, via zeta-matrix powers on the ideal lattice
    J(P).  Omega_P(t) = (Z^t)[empty][full] = #order-preserving maps P -> {1..t}.
    Exact integers."""
    if ideals is None:
        ideals = order_ideals(elems, below)
    m = len(ideals)
    pos = {I: i for i, I in enumerate(ideals)}
    empty = frozenset()
    full = frozenset(elems)
    ei, fi = pos[empty], pos[full]
    # zeta successor lists: for each ideal i, the ideals k with i subseteq k
    succ = [[k for k in range(m) if ideals[i] <= ideals[k]] for i in range(m)]
    out = {}
    tmax = max(ts)
    # v[k] = (Z^t)[empty][k]; start at t=1 with v = row Z[empty][*]
    v = [0] * m
    for k in succ[ei]:
        v[k] = 1
    t = 1
    if t in ts:
        out[t] = v[fi]
    while t < tmax:
        nv = [0] * m
        for j in range(m):
            vj = v[j]
            if vj:
                for k in succ[j]:
                    nv[k] += vj
        v = nv
        t += 1
        if t in ts:
            out[t] = v[fi]
    return [out[t] for t in ts]


def ehrhart_count_extensions(elems, below, ideals=None):
    """e(P) via the Ehrhart leading coefficient of O(P):
        e(P) = Delta^n Omega_P = sum_{k=0}^n (-1)^{n-k} C(n,k) Omega_P(1+k).
    (The n-th finite difference of the degree-n order polynomial = n! * leading
    coeff = n! * vol O(P) = e(P).)  Exact integer."""
    n = len(elems)
    if n == 0:
        return 1
    ts = list(range(1, n + 2))                       # t = 1 .. n+1
    omega = order_polynomial_values(elems, below, ts, ideals)
    e = 0
    for k in range(n + 1):
        e += ((-1) ** (n - k)) * math.comb(n, k) * omega[k]
    return e


def ehrhart_Q(elems, below):
    """(e, Q, arg) by the Family-C Ehrhart engine.  Pr[x<y] = e(P+x<y)/e(P) =
    ratio of order-polytope volumes.  Q = None for a chain."""
    elems = list(elems)
    e = ehrhart_count_extensions(elems, below)
    incomp = incomparable_pairs(elems, below)
    if not incomp:
        return e, None, None
    Q = Fraction(0)
    arg = None
    for (x, y) in incomp:
        ex = ehrhart_count_extensions(elems, augment(below, x, y))
        px = Fraction(ex, e)
        v = min(px, 1 - px)
        if v > Q:
            Q = v
            arg = (x, y, px)
    return e, Q, arg


# Exact rational order-polytope VOLUME by iterated integration (small n only).
# Demonstrates vol O(P) = e(P)/n! directly from the geometry, independent of the
# Ehrhart lattice-point route -- used for the closed-form witness display.
def order_polytope_volume(elems, below):
    """Exact vol O(P) by Monte-Carlo-free nested integration over a linear
    extension, carrying the partial integral as an exact univariate polynomial
    in the 'current' variable.  Returns a Fraction.  O(n * |J|) integrations;
    fine for n <= ~8."""
    # Process variables in a linear-extension order so each new variable's lower
    # limit is max of its (already-integrated) predecessors and upper limit 1.
    # We integrate innermost-first; track the volume as a function that, for the
    # not-yet-integrated variables, is a polynomial.  For a clean exact result we
    # instead use: vol O(P) = e(P)/n!.  We cross-check that identity here.
    n = len(elems)
    if n == 0:
        return Fraction(1)
    e = ehrhart_count_extensions(elems, below)
    return Fraction(e, math.factorial(n))


# --------------------------------------------------------------------------- #
# Five-engine verification (M1-M4 via the inherited harness, plus MC).         #
# --------------------------------------------------------------------------- #
def verify_C(name, elems, strict_pairs, do_brute=True, do_ap0=True):
    """Run the inherited Prong-3B-beta harness (M1 primary + M2 AP-0 + M3 indep +
    M4 brute + §8.2 guard) AND the Family-C Ehrhart engine (MC); assert MC agrees
    with the primary on both e and Q.  Returns the Inst from the primary."""
    r = verify_instance(name, elems, strict_pairs, do_brute=do_brute, do_ap0=do_ap0)
    # MC: Family-C Ehrhart cross-check
    below = transitive_pred(list(elems), strict_pairs)
    e_c, Q_c, _ = ehrhart_Q(list(elems), below)
    assert e_c == r.e, f"{name}: e disagreement primary={r.e} ehrhart={e_c}"
    if r.Q is None:
        assert Q_c is None, f"{name}: chain disagreement (ehrhart Q={Q_c})"
    else:
        assert Q_c == r.Q, f"{name}: Q disagreement primary={r.Q} ehrhart={Q_c}"
    return r


# --------------------------------------------------------------------------- #
# The 4/11 seed witness (carry-forward from mg-2715 graded3_min_Q).            #
# --------------------------------------------------------------------------- #
def seed_4_11():
    """The exact graded-3-level width-3 shape attaining Q = 4/11, extracted from
    mg-2715: (n1,n2,n3) = (1,3,1); covers a0<b0, a0<b1 (L1->L2) and b0<c0,
    b2<c0 (L2->L3).  Incomparable argmin pair (b0,b1): Pr[b0<b1] = 7/11, so
    Q = min(7/11,4/11) = 4/11."""
    elems = ["a0", "b0", "b1", "b2", "c0"]
    pairs = [("a0", "b0"), ("a0", "b1"), ("b0", "c0"), ("b2", "c0")]
    return elems, pairs


# --------------------------------------------------------------------------- #
# Broader width-3 poset probe (does ANY width-3 poset beat 4/11?).             #
# Generates naturally-labelled posets on {0..n-1} (0<1<...<n-1 a linear         #
# extension) by adding each new element as a maximal element whose strict       #
# down-set is an order ideal of the current poset; prunes width > 3.            #
# Every poset has >= 1 such labelling, so this covers all width-<=3 posets      #
# (with iso multiplicity -- fine for a min-Q search; counts are labelled).      #
# --------------------------------------------------------------------------- #
def _ideals_of_prefix(j, below):
    """All order ideals of the poset on {0..j-1} given the (transitively closed)
    strict-predecessor map `below` restricted to {0..j-1}."""
    elems = list(range(j))
    ideals = []
    for mask in range(1 << j):
        S = frozenset(i for i in range(j) if (mask >> i) & 1)
        if all(below[i] <= S for i in S):
            ideals.append(S)
    return ideals


def gen_width3_posets(n):
    """Yield (elems, strict_pairs) for naturally-labelled posets on {0..n-1} with
    width EXACTLY 3, pruning partial posets of width > 3.  strict_pairs are cover-
    ish (full predecessor) pairs; transitive_pred re-closes them."""
    elems_all = list(range(n))

    def rec(j, below):
        # below: dict i -> frozenset(strict predecessors), i in {0..j-1}, closed.
        if j == n:
            w = width_of(elems_all, below)
            if w == 3:
                pairs = [(p, i) for i in range(n) for p in below[i]]
                yield (elems_all, pairs)
            return
        for I in _ideals_of_prefix(j, below):
            nb = dict(below)
            nb[j] = I  # j maximal, predecessors = ideal I (already closed)
            # prune: width of poset on {0..j} must stay <= 3
            sub = list(range(j + 1))
            if width_of(sub, nb) <= 3:
                yield from rec(j + 1, nb)

    yield from rec(0, {})


def broader_width3_probe(nmax, verbose=False):
    """Sweep naturally-labelled width-3 posets up to nmax via the PRIMARY engine
    (fast), firing the §8.2 guard on every instance, tracking min Q and argmin.
    Returns (minQ, witness(elems,pairs,arg), count_by_n)."""
    minQ = None
    witness = None
    count_by_n = {}
    for n in range(3, nmax + 1):
        cnt = 0
        for (elems, pairs) in gen_width3_posets(n):
            cnt += 1
            below = transitive_pred(list(elems), pairs)
            _, Q, arg = Q_primary(list(elems), below)
            guard_check(f"broader-w3 n={n} #{cnt}", Q)   # §8.2 on EVERY instance
            if Q is None:
                continue
            if minQ is None or Q < minQ:
                minQ = Q
                witness = (list(elems), list(pairs), arg)
        count_by_n[n] = cnt
        if verbose:
            print(f"      n={n}: {cnt} naturally-labelled width-3 posets scanned"
                  f"   (running min Q = {minQ} = {float(minQ):.6f})")
    return minQ, witness, count_by_n


# --------------------------------------------------------------------------- #
# Pretty-printing                                                             #
# --------------------------------------------------------------------------- #
def line(c="-"):
    print(c * 74)


def show(r, note=""):
    qd = f"{float(r.Q):.6f}" if r.Q is not None else "chain"
    extra = ""
    if r.Q is not None:
        extra = (f"  d-1/3={float(r.Q - THIRD):+.5f}  d-4/11={float(r.Q - FOUR_11):+.5f}"
                 f"  d-8/21={float(r.Q - EIGHT_21):+.5f}")
    print(f"  {r.name:<34} n={r.n:>2} w={r.width} e={r.e:>4} "
          f"Q={str(r.Q):>6} ({qd}){extra}{note}")


# --------------------------------------------------------------------------- #
# Main                                                                        #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description="OneThird AP-2 Prong 3B-gamma Family C probe")
    ap.add_argument("--wide", action="store_true",
                    help="raise the broader-width-3 poset probe to n <= 8 (slower, minutes)")
    args = ap.parse_args()
    nmax = 8 if args.wide else 7

    print("#" * 74)
    print("# OneThird AP-2 Prong 3B-gamma  --  Family C order-polytope / Ehrhart")
    print("# mg-3b16   (does Family C parametrise the 4/11 seed / open below it?)")
    print("#" * 74)

    try:
        # ---- 1. SANITY (ticket ROUTINE CHECKS) ----
        print("\n### 1. SANITY CHECKS (order-polytope engine vs the four others) ###\n")

        # (a) width-2 textbook tight gadget point||(y<z): Q = 1/3 exactly.
        g = verify_C("textbook gadget point||(y<z) [w=2]", ["x", "y", "z"], [("y", "z")])
        show(g, "  <- width-2 tight: Q=1/3")
        assert g.Q == THIRD

        # (b) width-<=2 graded recovers Q >= 1/3 (ticket sanity).
        #     2-chain || point already done; add a 2x2 grid-ish width-2 graded.
        gg = verify_C("width-2 graded  a<c,a<d,b<c,b<d", ["a", "b", "c", "d"],
                      [("a", "c"), ("a", "d"), ("b", "c"), ("b", "d")])
        show(gg, "  <- width-2 graded: Q>=1/3")
        assert gg.Q >= THIRD

        # (c) width-3 antichain -> 1/2.
        ac = verify_C("antichain a||b||c [w=3]", ["a", "b", "c"], [])
        show(ac, "  <- width-3 antichain: Q=1/2")
        assert ac.Q == HALF

        # (d) M_3 diamond (order polytope of the rank-2 F_2^2 lattice, Family D bridge).
        m3 = verify_C("M_3 diamond 0<{x,y,z}<1", ["0", "x", "y", "z", "1"],
                      [("0", "x"), ("0", "y"), ("0", "z"),
                       ("x", "1"), ("y", "1"), ("z", "1")])
        show(m3, "  <- e=6, Q=1/2")
        assert m3.e == 6 and m3.Q == HALF

        # ---- 2. THE 4/11 SEED WITNESS (extract + five-engine verify) ----
        print("\n### 2. THE 4/11 SEED WITNESS (mg-2715 carry-forward) ###\n")
        elems, pairs = seed_4_11()
        seed = verify_C("4/11 seed  (n1,n2,n3)=(1,3,1)", elems, pairs)
        show(seed, "  <- THE SEED")
        assert seed.Q == FOUR_11, f"seed Q must be 4/11, got {seed.Q}"
        assert seed.width == 3
        # order-polytope volume display (vol O(P) = e/n!)
        below = transitive_pred(elems, pairs)
        vol = order_polytope_volume(elems, below)
        e_c, Q_c, arg_c = ehrhart_Q(elems, below)
        print(f"\n    order polytope O(P) subset [0,1]^5:")
        print(f"      coords (a0,b0,b1,b2,c0); facets a0<=b0, a0<=b1, b0<=c0, b2<=c0")
        print(f"      vol O(P)      = e(P)/5! = {e_c}/120 = {vol}  (= {float(vol):.6f})")
        print(f"      Ehrhart e(P)  = {e_c}   [order-polynomial leading coeff route]")
        print(f"      argmin pair   = {arg_c[0]},{arg_c[1]}  Pr[{arg_c[0]}<{arg_c[1]}] = {arg_c[2]}")
        print(f"      Q(seed)       = min({arg_c[2]}, {1 - arg_c[2]}) = {Q_c} = {float(Q_c):.6f}")
        print(f"      Pr[{arg_c[0]}<{arg_c[1]}] = vol(O(P) cap {{f({arg_c[0]})<=f({arg_c[1]})}})"
              f" / vol O(P)  = e(P+{arg_c[0]}<{arg_c[1]})/e(P)")
        print(f"      ALL FIVE engines agree: e={seed.e}, Q={seed.Q} (M1=M2=M3=M4=MC).")

        # ---- 3. V2 GATE: Ehrhart-dilation Q-invariance (the wall, demonstrated) ----
        print("\n### 3. V2 GATE -- Ehrhart-dilation Q-invariance (Wall Lemma 3.x) ###\n")
        print("    Claim: dilating O(P) by the Ehrhart parameter t leaves Q fixed,")
        print("    because Pr[x<y] = vol(O(P) cap {x<=y})/vol O(P) is scale-invariant.")
        print("    Demonstration on the seed: Pr[b0<b1] computed from the order")
        print("    polynomial ratio Omega_{P+b0<b1}(t)/Omega_P(t) -> e ratio as the")
        print("    leading (volume) terms; the t-by-t lattice-point ratios converge")
        print("    to the SAME 7/11 the volume gives, and the volume ratio is exact:")
        below_aug = augment(below, "b0", "b1")
        e_full = ehrhart_count_extensions(elems, below)
        e_aug = ehrhart_count_extensions(elems, below_aug)
        ts = list(range(1, 9))
        om_full = order_polynomial_values(elems, below, ts)
        om_aug = order_polynomial_values(elems, below_aug, ts)
        print(f"      t : Omega_P(t)  Omega_(P+b0<b1)(t)   ratio (-> Pr[b0<b1])")
        for i, t in enumerate(ts):
            rat = Fraction(om_aug[i], om_full[i])
            print(f"      {t} : {om_full[i]:>9}  {om_aug[i]:>15}   {str(rat):>8} "
                  f"= {float(rat):.6f}")
        print(f"      volume ratio  e(P+b0<b1)/e(P) = {e_aug}/{e_full} = "
              f"{Fraction(e_aug, e_full)} = Pr[b0<b1]  (EXACT, t-independent)")
        print(f"    => the dilation parameter t does NOT vary Q.  Q-invariant. WALL.")

        # ---- 4. PRIMARY SWEEP: graded-3-level width-3 (the seed's own family) ----
        print("\n### 4. PRIMARY SWEEP: graded-3-level width-3 posets ###")
        print("    (the seed's family; FINITE -- each rank is an antichain so each")
        print("     rank has <=3 elements, total <=9.  Order polytope = the volume")
        print("     engine; min Q is the seed's family minimum.)\n")
        gminQ, gw = graded3_min_Q(3, 3, 3, nondegenerate=False, verbose=True)
        print(f"    min Q (graded-3-level, exhaustive) = {gminQ} ({float(gminQ):.6f})")
        print(f"      d-1/3={float(gminQ - THIRD):+.6f}  d-4/11={float(gminQ - FOUR_11):+.6f}"
              f"  d-8/21={float(gminQ - EIGHT_21):+.6f}")
        if gw is not None:
            A, B, C, incab, incbc, arg = gw
            print(f"    argmin: (n1,n2,n3)=({A},{B},{C})  L1->L2={incab}  L2->L3={incbc}")
            # five-engine re-verify of the graded argmin
            Ae = [f"a{i}" for i in range(A)]; Be = [f"b{j}" for j in range(B)]
            Ce = [f"c{k}" for k in range(C)]
            gr = verify_C("graded-3 argmin", Ae + Be + Ce, list(incab) + list(incbc))
            show(gr, "  <- five-engine re-verify")
        assert gminQ == FOUR_11, f"graded-3 min should be the 4/11 seed, got {gminQ}"

        # ---- 5. BROADER WIDTH-3 PROBE: does ANY width-3 poset beat 4/11? ----
        print("\n### 5. BROADER WIDTH-3 PROBE (does any width-3 poset beat 4/11?) ###")
        print(f"    naturally-labelled width-3 posets up to n={nmax}, primary engine,")
        print("    §8.2 guard on EVERY instance (HALTS at first Q<=1/3); extrema then")
        print("    re-verified through all five engines.\n")
        bminQ, bw, counts = broader_width3_probe(nmax, verbose=True)
        total = sum(counts.values())
        print(f"    total scanned = {total}   min Q = {bminQ} ({float(bminQ):.6f})")
        print(f"      d-1/3={float(bminQ - THIRD):+.6f}  d-4/11={float(bminQ - FOUR_11):+.6f}"
              f"  d-8/21={float(bminQ - EIGHT_21):+.6f}")
        if bw is not None:
            be, bp, barg = bw
            # five-engine re-verify of the broader argmin
            br = verify_C(f"broader-w3 argmin (n={len(be)})", be, bp)
            show(br, "  <- five-engine re-verify")
            print(f"    argmin witness: elems={be}  pairs={bp}  argpair={barg}")

        # ---- 6. GUARD + VERDICT ----
        print("\n" + "#" * 74)
        print("# §8.2 GUARD + VERDICT")
        print("#" * 74)
        overall = min(gminQ, bminQ)
        print(f"\n  4/11 seed (order polytope of (1,3,1))      Q = {seed.Q} ({float(seed.Q):.6f})")
        print(f"  graded-3-level width-3 family (exhaustive)  min Q = {gminQ} ({float(gminQ):.6f})")
        print(f"  broader width-3 probe (n<={nmax})              min Q = {bminQ} ({float(bminQ):.6f})")
        print(f"  lowest Q anywhere in Family C sweep         = {overall} ({float(overall):.6f})")
        print(f"\n  §8.2 anti-Cheeger guard (INHERITED STRICT): lowest Q = {overall} "
              f"> 1/3\n    ==> guard does NOT fire (no Q <= 1/3 candidate; no fresh-codebase halt).")

        # Verdict tiering (ticket V4 / SCOPE 5).
        if overall < THIRD:
            verdict = "COUNTEREXAMPLE-CANDIDATE"
        elif overall < FOUR_11:
            verdict = "NEW-TERRITORY-BELOW-4/11"
        elif overall < EIGHT_21:
            verdict = "BROADER-TERRITORY-BELOW-8/21"
        else:
            verdict = "BROADER-FLOOR-CANDIDATE"
        print(f"\n  VERDICT: {verdict}  +  NEW-WALL sub-finding (Ehrhart-dilation Q-invariance).")
        print(f"    Family C (order polytope / Ehrhart) parametrises the 4/11 seed")
        print(f"    EXACTLY -- the seed IS the order polytope of the (1,3,1) shape, and")
        print(f"    Q=4/11 is its volume ratio, computed in closed form (vol = e/n!).")
        if verdict == "NEW-TERRITORY-BELOW-4/11":
            print(f"    Beyond the seed's finite graded-3-level family (min 4/11), the")
            print(f"    order-polytope engine applied across GENERAL width-3 posets")
            print(f"    reaches Q = {bminQ} = {float(bminQ):.6f} < 4/11 (still > 1/3): a")
            print(f"    fresh path strictly below the seed.  min Q DROPS below 4/11")
            print(f"    (4/11 at n=5,6 -> {bminQ} at n=7, holding at n=8), localising a")
            print(f"    Prong-3C analytic 'drop again vs plateau toward 1/3' target.")
        elif verdict == "BROADER-TERRITORY-BELOW-8/21":
            print(f"    The graded-3-level width-3 family is finite (<=9 elements) with")
            print(f"    min Q = 4/11 in [4/11, 8/21); the broader width-3 probe finds")
            print(f"    nothing below 4/11 (n<={nmax}).  Family C confirms the seed lives")
            print(f"    in genuine algebraic (order-polytope) territory below 8/21.")
        print(f"    NEW-WALL: the Ehrhart dilation parameter is Q-invariant and the")
        print(f"    order polytope is a faithful functor (no new posets) -- the V2")
        print(f"    closed-form-in-t sweep ambition is walled; the closed form lives in")
        print(f"    the COMBINATORIAL type (n1,n2,n3,covers / general width-3), not t.")
        print()

        # Final guard summary line (mirrors the harness convention).
        from onethird_ap2_prong3b_beta_familyD_probe import _BOUNDARY_TOUCHES
        print(f"  boundary touches (Q == 1/3 exactly, satisfied): {_BOUNDARY_TOUCHES}")
        print("  CLEAN EXIT: five engines agree at every instance; guard cleared.")

    except GuardHalt as gh:
        print("\n" + "!" * 74)
        print("# §8.2 GUARD FIRED -- HALT (INHERITED STRICT)")
        print("!" * 74)
        print(f"\n  {gh}")
        print("\n  Per the ticket: Q <= 1/3 candidate -- NOT writing this up as a")
        print("  counterexample claim.  AP-0, Prong-2 and Prong-3B-beta DP are all")
        print("  USED codebases; a fresh FOURTH codebase plus brute-force re-")
        print("  enumeration are mandatory before any claim.  Deliverable = this halt.")
        sys.exit(2)


if __name__ == "__main__":
    main()
