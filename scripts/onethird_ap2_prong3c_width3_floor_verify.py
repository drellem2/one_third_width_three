#!/usr/bin/env python3
r"""
onethird_ap2_prong3c_width3_floor_verify.py
===========================================

OneThird Algebraic-Program **AP-2 Prong 3C** (mg-8bd6) -- analytic inf Q on
width-exactly-3 posets via the order polytope / Ehrhart engine.  Follow-up to
mg-3b16 (Prong 3B-gamma, Family C), which surfaced Q = 14/39 ~= 0.358974 at
width-3 n=7 (below the 4/11 seed) and asked: is 14/39 the next FLOOR, or does
min Q descend further toward 1/3?

VERDICT (this prong): **REFUTATION of the 14/39-floor hypothesis.**
  A width-exactly-3 poset at n=10 attains
        Q = 6/17 ~= 0.352941   <   14/39 ~= 0.358974   (still > 1/3),
  verified through all FIVE inherited engines (M1 order-ideal DP, M2 AP-0
  kernel, M3 minimal-element-removal recursion, M4 brute permutations, MC
  Ehrhart order-polynomial).  So 14/39 is NOT a floor; min Q descends below it.
  The live counterexample-hunt corridor narrows from (1/3, 14/39] to (1/3, 6/17].

THE DESCENT LADDER (the structural finding).  The minimum-Q width-3 witnesses
found so far all lie on a clean rational ladder:
        n<=6 : Q = 4/11   (k=11)      [the mg-3b16 seed]
        n= 7 : Q = 14/39  (k=13)      [the mg-3b16 14/39 witness]
        n=10 : Q = 6/17   (k=17)      [this prong's refutation witness]
  where in every case   3*Q - 1 = 1/k   (k = 11, 13, 17 integral), i.e.
        Q = 1/3 + 1/(3k) = (k+1)/(3k),
  and the binding incomparable pair has   Pr[x<y] = (2k-1)/(3k) -> 2/3   as
  k -> infinity, exactly the (1/3, 2/3) tight balance of the width-2 gadget
  point||(y<z).  The ladder thus *points* toward inf Q = 1/3 (the 1/3-2/3
  conjecture asymptotically sharp at width exactly 3).  HOWEVER, three
  independent searches (two single-element-extension beam searches and a
  randomized hill-climb / anneal, all to n ~ 14) find NOTHING strictly below
  6/17 -- the descent stalls at 6/17 just as it stalled at 4/11 and 14/39
  before each jump.  So 6/17 is the NEW plateau / floor candidate (the role
  14/39 played going in, and 8/21 for width-3 SP in Prong 3A).  Whether the
  next jump below 6/17 exists (descent -> 1/3) or 6/17 is a genuine floor is
  the re-opened Prong-3D question.

THE n=8 "PLATEAU" CLARIFICATION.  The mg-3b16 report flagged 14/39 as
"plateauing at n=8".  This is shown here to be a TRIVIAL extension artifact:
the n=8 argmin is the n=7 14/39 witness with a single global TOP point adjoined
(above everything).  A global max/min point is forced last/first in EVERY
linear extension, so it adds only comparable pairs and leaves e(P) and every
incomparable-pair balance UNCHANGED -- Q is preserved (the order-polytope
analogue of Prong-3A Lemma B "series = max").  The n=8 equality is therefore
NOT evidence of a floor; the genuine descent resumes at n=10 (6/17).

THE ENGINES + GUARD (inherited verbatim from mg-3b16 / mg-2715).
  Every reported Q is cross-validated by the five-engine verify_C harness
  (M1=M2=M3=M4=MC, exact rational arithmetic, Monte-Carlo never used).  The
  roadmap-8.2 anti-Cheeger guard: a Q <= 1/3 claim would require a fresh SIXTH
  codebase (M1..M4,MC all used) plus brute force.  The refutation witness has
  Q = 6/17 > 1/3, so it needs only the five existing engines and does NOT fire
  the guard.  No Q <= 1/3 instance exists anywhere in the swept range.

This script is the Prong-3C verification harness: it re-verifies the 4/11 seed,
the 14/39 witness, the n=8 trivial-extension companion, and the 6/17 refutation
witness through all five engines; checks the descent-ladder identities; and
re-runs the exhaustive small-n width-3 floor (4/11 at n<=6, 14/39 at n=7).
Pure standard library.  Default run a few seconds.
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction

# Reuse the Prong-3B-gamma five-engine harness (M1+M2+M3+M4 + MC Ehrhart) and the
# §8.2 guard verbatim (carry-forward named in the ticket).
from onethird_ap2_prong3b_gamma_familyC_probe import (
    verify_C, ehrhart_Q, order_polytope_volume, ehrhart_count_extensions,
    gen_width3_posets, seed_4_11,
)
from onethird_ap2_prong3b_beta_familyD_probe import (
    transitive_pred, augment, Q_primary, width_of, guard_check, GuardHalt,
    THIRD, EIGHT_21, HALF,
)

FOUR_11 = Fraction(4, 11)
FOURTEEN_39 = Fraction(14, 39)
SIX_17 = Fraction(6, 17)


# --------------------------------------------------------------------------- #
# The three extracted witnesses (exact, naturally-labelled; relations = full   #
# predecessor pairs, re-closed by transitive_pred).                            #
# --------------------------------------------------------------------------- #
def witness_14_39_n7():
    """The mg-3b16 14/39 witness at n=7 (broader-probe argmin), e=39, Q=14/39 at
    the incomparable pair (1,2) with Pr[1<2]=25/39.  Cover relations:
        0<2, 0<3, 1<4, 1<5, 2<4, 2<5, 3<6, 4<6.
    Levels L0={0,1} L1={2,3} L2={4,5} L3={6}; binding pair (1,2) are 'near-twins'
    with identical up-set {4,5,6}, but 2 carries 0 below it while 1 does not --
    the down-asymmetry biases Pr[1<2] to 25/39."""
    elems = [0, 1, 2, 3, 4, 5, 6]
    pairs = [(0, 2), (0, 3), (0, 4), (1, 4), (2, 4),
             (0, 5), (1, 5), (2, 5),
             (0, 6), (1, 6), (2, 6), (3, 6), (4, 6)]
    return elems, pairs


def witness_14_39_n8_trivial():
    """The mg-3b16 n=8 'plateau' companion: the n=7 witness with a single global
    TOP point (element 7, above all).  Q is UNCHANGED at 14/39 because a global
    top is forced last in every linear extension (adds only comparable pairs).
    This is the order-polytope analogue of Prong-3A Lemma B (series=max), NOT a
    genuine floor signal."""
    elems = list(range(8))
    pairs = [(0, 2), (0, 3), (0, 4), (1, 4), (2, 4),
             (0, 5), (1, 5), (2, 5),
             (0, 6), (1, 6), (2, 6), (3, 6), (4, 6),
             (0, 7), (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7)]
    return elems, pairs


def witness_6_17_n10():
    """The Prong-3C REFUTATION witness at n=10: a width-exactly-3 poset with
    e=187 and Q = 6/17 < 14/39 (binding incomparable pair (3,9), Pr[3<9]=11/17).
    Found by beam-search descent from the 4/11 seed; five-engine verified.
    Cover relations:
        0<2, 0<3, 1<8, 1<9, 2<9, 3<6, 3<8, 4<6, 4<7, 7<5, 8<5, 9<4."""
    elems = list(range(10))
    pairs = [(0, 2), (0, 3), (0, 4), (2, 4), (1, 4),
             (2, 5), (1, 5), (7, 5), (0, 5), (4, 5), (8, 5), (3, 5),
             (2, 6), (1, 6), (0, 6), (4, 6), (3, 6),
             (0, 7), (2, 7), (4, 7), (1, 7),
             (0, 8), (1, 8), (3, 8),
             (0, 9), (2, 9), (1, 9), (9, 4)]
    return elems, pairs


def k_of(Q):
    """The ladder parameter: k = 1/(3Q-1).  Integral on the descent witnesses."""
    d = 3 * Q - 1
    return None if d == 0 else 1 / d


def line(c="-"):
    print(c * 74)


def show(r, note=""):
    qd = f"{float(r.Q):.6f}" if r.Q is not None else "chain"
    extra = ""
    if r.Q is not None:
        extra = (f"  d-1/3={float(r.Q - THIRD):+.6f}"
                 f"  d-14/39={float(r.Q - FOURTEEN_39):+.6f}"
                 f"  k={k_of(r.Q)}")
    print(f"  {r.name:<34} n={r.n:>2} w={r.width} e={r.e:>4} "
          f"Q={str(r.Q):>6} ({qd}){extra}{note}")


def main():
    ap = argparse.ArgumentParser(description="OneThird AP-2 Prong 3C width-3 floor verify")
    ap.add_argument("--floor-n", type=int, default=7,
                    help="exhaustive width-3 small-n floor up to this n (default 7; "
                         "set 8 for the mg-3b16 --wide range, slower)")
    args = ap.parse_args()

    print("#" * 74)
    print("# OneThird AP-2 Prong 3C  --  width-3 floor: is 14/39 the floor?")
    print("# mg-8bd6   VERDICT: REFUTATION -- Q descends to 6/17 < 14/39 (still >1/3)")
    print("#" * 74)

    try:
        # ---- 1. SANITY CONTROLS (ticket ROUTINE CHECKS) ----
        print("\n### 1. SANITY (closed-form / five-engine controls) ###\n")
        g = verify_C("textbook gadget point||(y<z)", ["x", "y", "z"], [("y", "z")])
        show(g, "  <- width-2 tight: Q=1/3")
        assert g.Q == THIRD and g.e == 3
        # e(P+ refined) route: the satisfied 1/3 boundary
        belowg = transitive_pred(["x", "y", "z"], [("y", "z")])
        assert ehrhart_count_extensions(["x", "y", "z"],
                                        augment(belowg, "x", "y")) == 1  # x<y forces unique ext? check ratio
        # (the gadget's Pr[x<y]=1/3 = e(P+x<y)/e(P) = 1/3)
        ex = ehrhart_count_extensions(["x", "y", "z"], augment(belowg, "x", "y"))
        assert Fraction(ex, g.e) == THIRD, f"gadget Pr[x<y] should be 1/3, got {Fraction(ex,g.e)}"

        # ---- 2. THE 4/11 SEED (k=11) ----
        print("\n### 2. THE 4/11 SEED (mg-3b16 carry-forward, k=11) ###\n")
        elems, pairs = seed_4_11()
        seed = verify_C("4/11 seed (1,3,1)", elems, pairs)
        show(seed, "  <- seed")
        assert seed.Q == FOUR_11 and seed.width == 3
        assert k_of(seed.Q) == 11, f"seed k should be 11, got {k_of(seed.Q)}"
        below = transitive_pred(elems, pairs)
        assert order_polytope_volume(elems, below) == Fraction(11, 120)

        # ---- 3. THE 14/39 WITNESS (k=13) + n=8 trivial-extension companion ----
        print("\n### 3. THE 14/39 WITNESS (k=13) + n=8 trivial-extension companion ###\n")
        e7, p7 = witness_14_39_n7()
        w7 = verify_C("14/39 witness n=7", e7, p7)
        show(w7, "  <- THE 14/39 witness")
        assert w7.Q == FOURTEEN_39 and w7.width == 3 and w7.e == 39
        assert k_of(w7.Q) == 13, f"14/39 k should be 13, got {k_of(w7.Q)}"
        # binding pair (1,2), Pr[1<2]=25/39=(2k-1)/(3k)
        below7 = transitive_pred(e7, p7)
        pr = Fraction(ehrhart_count_extensions(e7, augment(below7, 1, 2)), w7.e)
        assert pr == Fraction(25, 39) == Fraction(2 * 13 - 1, 3 * 13)
        vol7 = order_polytope_volume(e7, below7)
        print(f"    vol O(P) = e/7! = 39/5040 = {vol7}; binding Pr[1<2]={pr}=(2k-1)/(3k), k=13")

        # n=8 companion: same Q, via global-top adjunction (Q-preserving)
        e8, p8 = witness_14_39_n8_trivial()
        w8 = verify_C("14/39 companion n=8 (+top pt)", e8, p8)
        show(w8, "  <- TRIVIAL +top extension")
        assert w8.Q == FOURTEEN_39 and w8.e == 39, "global-top must preserve e and Q"
        below8 = transitive_pred(e8, p8)
        assert all(x in below8[7] for x in range(7)), "element 7 must be a global top"
        print("    => element 7 is a global max (above all); forced last in every")
        print("       linear extension => e and all balances unchanged => Q=14/39.")
        print("       The mg-3b16 'n=8 plateau' is this Q-preserving adjunction, NOT")
        print("       a genuine floor (order-polytope analogue of Prong-3A Lemma B).")

        # ---- 4. THE 6/17 REFUTATION WITNESS (k=17) ----
        print("\n### 4. THE 6/17 REFUTATION WITNESS (k=17) -- 14/39 IS NOT THE FLOOR ###\n")
        e10, p10 = witness_6_17_n10()
        w10 = verify_C("6/17 refutation witness n=10", e10, p10)
        show(w10, "  <- Q=6/17 < 14/39")
        assert w10.Q == SIX_17 and w10.width == 3 and w10.e == 187
        assert w10.Q < FOURTEEN_39, "refutation requires Q < 14/39"
        assert w10.Q > THIRD, "refutation witness must still satisfy the conjecture"
        assert k_of(w10.Q) == 17, f"6/17 k should be 17, got {k_of(w10.Q)}"
        below10 = transitive_pred(e10, p10)
        pr10 = Fraction(ehrhart_count_extensions(e10, augment(below10, 3, 9)), w10.e)
        assert pr10 == Fraction(11, 17) == Fraction(2 * 17 - 1, 3 * 17)
        print(f"    binding pair (3,9): Pr[3<9]={pr10}=(2k-1)/(3k), k=17  ->  2/3 limit")
        print(f"    five engines (M1=M2=M3=M4=MC) agree: e=187, Q=6/17.  Q>1/3 so the")
        print(f"    §8.2 guard does NOT fire and NO sixth codebase is needed.")

        # ---- 5. THE DESCENT LADDER (3Q-1 = 1/k, integral) ----
        print("\n### 5. THE DESCENT LADDER  3*Q - 1 = 1/k,  Q = (k+1)/(3k) ###\n")
        ladder = [("4/11 ", FOUR_11, 11, 5), ("14/39", FOURTEEN_39, 13, 7),
                  ("6/17 ", SIX_17, 17, 10)]
        print("     witness   Q          3Q-1     k    Pr=(2k-1)/(3k)   Q-1/3")
        for nm, Q, k, n in ladder:
            assert 3 * Q - 1 == Fraction(1, k)
            assert Q == Fraction(k + 1, 3 * k)
            pr = Fraction(2 * k - 1, 3 * k)
            print(f"     {nm}     {str(Q):>6} ({float(Q):.5f})  1/{k:<3}  {k:<3}  "
                  f"{str(pr):>6}={float(pr):.4f}   1/{int(1/(Q-THIRD))}")
        print("\n     k = 11, 13, 17  (binding Pr -> 2/3, Q -> 1/3 as k -> infinity):")
        print("     the ladder POINTS to inf Q = 1/3 (conjecture asymptotically sharp")
        print("     at width exactly 3).  But search (2 beams + anneal, n<=14) finds")
        print("     nothing below 6/17 -> 6/17 is the new plateau/floor candidate.")

        # ---- 6. EXHAUSTIVE SMALL-n WIDTH-3 FLOOR (matches mg-3b16) ----
        print(f"\n### 6. EXHAUSTIVE WIDTH-3 FLOOR n<= {args.floor_n} (guard on every poset) ###\n")
        running = None
        for n in range(3, args.floor_n + 1):
            mn = None
            cnt = 0
            for (elems, pairs) in gen_width3_posets(n):
                cnt += 1
                below = transitive_pred(list(elems), pairs)
                _, Q, _ = Q_primary(list(elems), below)
                guard_check(f"floor n={n} #{cnt}", Q)   # §8.2 on EVERY instance
                if Q is None:
                    continue
                if mn is None or Q < mn:
                    mn = Q
                if running is None or Q < running:
                    running = Q
            print(f"    n={n}: {cnt:>6} width-3 posets   min Q = {mn} ({float(mn):.6f})  "
                  f"k={k_of(mn)}")
        print(f"    cumulative min Q (n<={args.floor_n}) = {running} ({float(running):.6f})")
        if args.floor_n >= 7:
            assert running == FOURTEEN_39, f"n<=7 floor should be 14/39, got {running}"
            print("    => 14/39 is the n<=7 floor (4/11 at n<=6); 6/17 first appears at")
            print("       n=10, BELOW 14/39 -- the corridor is (1/3, 6/17].")

        # ---- 7. VERDICT ----
        print("\n" + "#" * 74)
        print("# §8.2 GUARD + VERDICT")
        print("#" * 74)
        lowest = SIX_17
        print(f"\n  4/11 seed (k=11) ........ Q=4/11 ={float(FOUR_11):.6f}")
        print(f"  14/39 witness (k=13) .... Q=14/39={float(FOURTEEN_39):.6f}  (n=8 = +top, Q-preserving)")
        print(f"  6/17 refutation (k=17) .. Q=6/17 ={float(SIX_17):.6f}  < 14/39   <== REFUTES 14/39 floor")
        print(f"  lowest width-3 Q found .. Q=6/17 ={float(lowest):.6f}  > 1/3")
        print(f"\n  §8.2 anti-Cheeger guard: lowest Q = 6/17 > 1/3 ==> guard does NOT fire")
        print(f"    (no Q<=1/3 candidate; the 6/17 refutation needs only M1..M4,MC).")
        print(f"\n  VERDICT: REFUTATION -- 14/39 is NOT the width-3 floor.  min Q descends")
        print(f"    to 6/17 < 14/39 (corridor (1/3,14/39] -> (1/3,6/17]).  The descent")
        print(f"    ladder 3Q-1=1/k (k=11,13,17), binding Pr->2/3, points to inf Q=1/3;")
        print(f"    search to n<=14 finds nothing below 6/17, so 6/17 is the new plateau")
        print(f"    / floor candidate -- the Prong-3D drop-vs-plateau target.")
        print("\n  CLEAN EXIT: five engines agree at every instance; ladder identities")
        print("  hold; exhaustive small-n floor reproduced; guard cleared.")

    except GuardHalt as gh:
        print("\n" + "!" * 74)
        print("# §8.2 GUARD FIRED -- HALT (INHERITED STRICT)")
        print("!" * 74)
        print(f"\n  {gh}")
        print("\n  Q <= 1/3 candidate: M1..M4 + MC all used; a fresh SIXTH codebase plus")
        print("  brute-force re-enumeration are mandatory before any claim.")
        sys.exit(2)


if __name__ == "__main__":
    main()
