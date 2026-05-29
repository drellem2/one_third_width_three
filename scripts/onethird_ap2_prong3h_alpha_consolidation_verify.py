#!/usr/bin/env python3
r"""
onethird_ap2_prong3h_alpha_consolidation_verify.py
==================================================

OneThird Algebraic-Program **AP-2 Prong 3H-alpha** (mg-6728) -- structural
consolidation of the AP-2 arc + the analytic Q >= 6/17 attempt on the self-dual
core via the Q-preserving extreme-adjunction lemma and the extreme-reduction
theorem.  Follow-up to mg-5406 (Prong 3G-alpha, OUTCOME-C + PARTIAL OUTCOME-A:
6/17 holds across the FULL width-3 arena exhaustively through n=11, reached
NON-self-dually from n=11 by global-top adjunction of the n=10 self-dual
witness) and mg-7ee8 (Prong 3E-alpha, the self-dual-core Outcome-4 WALL).

VERDICT (this prong): **OUTCOME-4 (WALL) on the STRONG reduction-to-self-dual-
core + analytic Q>=6/17, carrying TWO NEW RIGOROUS ANALYTIC DELIVERABLES.**

  (ADJ)  THE Q-PRESERVING EXTREME-ADJUNCTION LEMMA -- now a proved theorem, not
         an empirical pattern.  For any finite poset P and a global maximum top
         adjoined (P + top), and dually a global minimum bottom (bottom + P):
              e(P + top) = e(P),
              Pr_{P+top}[x<y] = Pr_P[x<y]  for every incomparable {x,y} in P,
              Q(P + top) = Q(P),
         and likewise for bottom.  Proof: a global maximum is forced LAST in
         every linear extension (lambda(top)=n+1), so linear extensions of
         P+top biject with those of P by restriction; the incomparable pairs of
         P+top are exactly those of P (top is comparable to all), each with the
         same conditional order.  This is the R=singleton case of the general
         ordinal-sum identity Q(P (+) R) = max(Q(P), Q(R)) -- the order-polytope
         analogue of Prong-3A's Lemma B "series = max", now for ARBITRARY P
         (not only series-parallel P).

  (RED)  THE EXTREME-REDUCTION THEOREM -- rigorous.  Iteratively deleting global
         maxima and global minima from a width-3 poset P (with an incomparable
         pair) terminates at an EXTREME-REDUCED core core(P) with
              Q(P) = Q(core(P)),  width(core(P)) = width(P) = 3,
              core(P) has no global maximum and no global minimum.
         Hence  inf{Q(P): width-3} = inf{Q(C): width-3, extreme-reduced}.  The
         full-arena floor REDUCES (rigorously) to the extreme-reduced core.

  (GAP)  THE REDUCTION TO THE *SELF-DUAL* CORE IS CONDITIONAL.  The adjunction +
         extreme-reduction do NOT prove core(P) self-dual (no Q-preserving
         self-dualization operation exists).  The full "self-dual core suffices"
         statement requires the additional SELF-DUALIZATION HYPOTHESIS: every
         Q-minimizing extreme-reduced width-3 poset is self-dual.  This is
         EMPIRICALLY verified exhaustively through n=11 (mg-5406): every overall
         per-n argmin either (a) reduces to a self-dual core by stripping global
         extremes [n=8 = n=7 + top; n=11 = n=10 + top], or (b) is itself an
         extreme-reduced self-dual minimum [n=5,7,10].  It is NOT proved -- this
         is the named gap.

  (WALL) THE SELF-DUAL-CORE ANALYTIC FLOOR IS STILL WALLED (Prong 3E-alpha).
         On the self-dual core the bound Q>=6/17 reduces to the forced-relation
         order-polytope ratio  6/17 e(P) <= e(P+x<y) <= 11/17 e(P)  on the
         near-twin sigma-orbit class -- the SAME named missing input as mg-7ee8.
         The sigma-orbit reduction (Thm R1) is re-verified at the rungs as the
         genuine closed-form V2 lever; extreme-reduction merely SHARPENS the
         target (the trivial Q-preserving adjunction families are now excluded
         from the core, so the bound is needed only on extreme-reduced self-dual
         width-3 posets).  No explicit c>1/3 is provable (open-problem-hard).

Corridor UNCHANGED at (1/3, 6/17]; 6/17 = corridor ceiling, now an explicit
theorem-shaped reduction target on the extreme-reduced self-dual core.

GUARD (roadmap 8.2 anti-Cheeger, INHERITED STRICT).  Every Q encountered is
> 1/3 (lowest 6/17).  The guard does NOT fire; M1..M4 + MC suffice; no SIXTH
codebase is triggered (that trigger is reserved for a Q <= 1/3 claim).

Reuses the five-engine verify_C harness (M1 order-ideal DP, M2 AP-0 kernel, M3
IndPoset removal recursion, M4 brute permutations, MC Ehrhart order-polynomial)
+ find_involution + the Prong-3E sigma-orbit checker VERBATIM, and adds the
adjunction-lemma checker, the extreme-reduction core, the reduction-theorem
argmin-table sanity, and the self-dual-core analytic-bound sanity.  Pure
standard library; default run a few seconds.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction

from onethird_ap2_prong3b_gamma_familyC_probe import (
    verify_C, seed_4_11, gen_width3_posets,
)
from onethird_ap2_prong3b_beta_familyD_probe import (
    transitive_pred, augment, count_le_dp, incomparable_pairs,
    width_of, Q_primary, guard_check, GuardHalt, THIRD, EIGHT_21, HALF,
)
from onethird_ap2_prong3c_width3_floor_verify import (
    witness_14_39_n7, witness_14_39_n8_trivial, witness_6_17_n10,
    k_of, FOUR_11, FOURTEEN_39, SIX_17,
)
from onethird_ap2_prong3d_alpha_descent_verify import find_involution
from onethird_ap2_prong3e_alpha_selfdual_floor_verify import (
    pr_lt, balance, check_R1_orbit_reduction,
)

# Reference bars / rungs of the consolidated AP-2 taxonomy.
TWENTY7_70 = Fraction(27, 70)        # Family-A skew SKEW-ARTIFACT
TWO_5 = Fraction(2, 5)               # Family-D bar
ONE_THIRD4_375 = Fraction(134, 375)  # the odd-n off-ladder self-dual minimum


# --------------------------------------------------------------------------- #
# Adjunction constructors (global top / global bottom) and the extreme core.  #
# --------------------------------------------------------------------------- #
def _fresh(elems, base):
    """A fresh label NOT in elems, type-compatible with the existing labels so
    the M3 engine's sorted() does not mix int and str.  Integer labels -> next
    integer; otherwise a fresh string."""
    seen = set(elems)
    if all(isinstance(e, int) for e in elems):
        return (max(elems) + 1) if elems else 0
    lab = base
    while lab in seen:
        lab += "'"
    return lab


def adjoin_top(elems, pairs):
    """P + top: a fresh element above EVERYTHING (a global maximum)."""
    top = _fresh(elems, "TOP")
    return list(elems) + [top], list(pairs) + [(x, top) for x in elems], top


def adjoin_bottom(elems, pairs):
    """bottom + P: a fresh element below EVERYTHING (a global minimum)."""
    bot = _fresh(elems, "BOT")
    return list(elems) + [bot], list(pairs) + [(bot, x) for x in elems], bot


def pairs_of(elems, below):
    """Strict relation pairs from a transitively-closed below-map (re-closed by
    transitive_pred downstream; this is just a generating set)."""
    return [(p, e) for e in elems for p in below[e]]


def is_global_max(z, elems, below):
    return below[z] == frozenset(x for x in elems if x != z)


def is_global_min(b, elems, below):
    return all(b in below[x] for x in elems if x != b)


def extreme_core(elems, below):
    """Iteratively strip global maxima and global minima.  Returns
    (core_elems, core_below, n_top_stripped, n_bot_stripped).  Each strip is
    Q-preserving by the adjunction lemma, so Q(core) = Q(P)."""
    elems = list(elems)
    below = {e: set(below[e]) for e in elems}
    n_top = n_bot = 0
    changed = True
    while changed and len(elems) > 1:
        changed = False
        for z in list(elems):
            if is_global_max(z, elems, below):
                elems.remove(z); del below[z]      # nobody had z as a predecessor
                n_top += 1; changed = True; break
        if changed:
            continue
        for b in list(elems):
            if is_global_min(b, elems, below):
                elems.remove(b); del below[b]
                for x in elems:
                    below[x].discard(b)
                n_bot += 1; changed = True; break
    return elems, {e: frozenset(below[e]) for e in elems}, n_top, n_bot


# --------------------------------------------------------------------------- #
# (ADJ) the adjunction-lemma checker.                                         #
# --------------------------------------------------------------------------- #
def check_adjunction_pointwise(name, elems, pairs):
    """Verify e, every pairwise balance, width and Q are preserved by both the
    global-top and global-bottom adjunctions.  Exact rationals throughout."""
    below = transitive_pred(list(elems), pairs)
    e0 = count_le_dp(list(elems), below)
    w0 = width_of(list(elems), below)
    _, Q0, _ = Q_primary(list(elems), below)
    incomp0 = incomparable_pairs(list(elems), below)
    bal0 = {frozenset((x, y)): pr_lt(list(elems), below, e0, x, y) for x, y in incomp0}

    for tag, (el, pr, _new) in (("+top", adjoin_top(elems, pairs)),
                                ("+bot", adjoin_bottom(elems, pairs))):
        b = transitive_pred(el, pr)
        e1 = count_le_dp(el, b)
        w1 = width_of(el, b)
        _, Q1, _ = Q_primary(el, b)
        incomp1 = incomparable_pairs(el, b)
        assert e1 == e0, f"{name} {tag}: e changed {e0}->{e1}"
        assert Q1 == Q0, f"{name} {tag}: Q changed {Q0}->{Q1}"
        assert w1 == w0, f"{name} {tag}: width changed {w0}->{w1}"
        # incomparable pairs are exactly the original ones (new element is comparable)
        assert {frozenset(p) for p in incomp1} == {frozenset(p) for p in incomp0}, \
            f"{name} {tag}: incomparable-pair set changed"
        for x, y in incomp1:
            assert pr_lt(el, b, e1, x, y) == bal0[frozenset((x, y))], \
                f"{name} {tag}: balance of ({x},{y}) changed"
    return e0, Q0, w0


# --------------------------------------------------------------------------- #
# main                                                                        #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(
        description="OneThird AP-2 Prong 3H-alpha consolidation + adjunction-"
                    "reduction + self-dual-core analytic attempt verifier")
    ap.add_argument("--adj-nmax", type=int, default=6,
                    help="exhaustive adjunction-lemma sweep up to this n "
                         "(default 6; the lemma is checked on every width-3 "
                         "poset emitted by gen_width3_posets at n=4..adj-nmax)")
    args = ap.parse_args()

    print("#" * 74)
    print("# OneThird AP-2 Prong 3H-alpha  --  consolidation + Q-preserving extreme")
    print("# adjunction lemma + extreme-reduction theorem + self-dual-core attempt")
    print("# mg-6728   VERDICT: OUTCOME-4 (WALL) + two new rigorous analytic theorems")
    print("#" * 74)

    try:
        # ---- 1. THE RUNG WITNESSES -- five-engine + ladder identity ----
        print("\n### 1. THE RUNG WITNESSES -- five-engine + ladder identity ###\n")
        rungs = [("4/11 seed (k=11, n=5)", seed_4_11(), FOUR_11, 11),
                 ("14/39 witness (k=13, n=7)", witness_14_39_n7(), FOURTEEN_39, 13),
                 ("6/17 witness (k=17, n=10)", witness_6_17_n10(), SIX_17, 17)]
        for nm, (el, pr), Qexp, kexp in rungs:
            r = verify_C(nm, el, pr)
            assert r.Q == Qexp and r.width == 3
            assert k_of(r.Q) == kexp and r.Q == Fraction(kexp + 1, 3 * kexp)
            print(f"    {nm:30s} e={r.e:>4} Q={r.Q} = (k+1)/(3k), k={kexp}  [M1=M2=M3=M4=MC]")

        # ---- 2. (ADJ) Q-PRESERVING EXTREME-ADJUNCTION LEMMA -- the witnesses ----
        print("\n### 2. (ADJ) Q-PRESERVING EXTREME-ADJUNCTION LEMMA ###")
        print("###     e, all balances, width, Q preserved by +top AND +bottom        ###\n")
        for nm, (el, pr), Qexp, kexp in rungs:
            e0, Q0, w0 = check_adjunction_pointwise(nm, el, pr)
            # build the n+1 non-self-dual companion and five-engine it
            tel, tpr, top = adjoin_top(el, pr)
            rt = verify_C(nm + " +top", tel, tpr)
            sd = find_involution(tel, transitive_pred(tel, tpr)) is not None
            guard_check(nm + " +top", rt.Q)
            print(f"    {nm:30s} Q={Q0} preserved: +top -> n={rt.n} Q={rt.Q} "
                  f"(self-dual={sd}); +bottom dual.  e={e0} fixed.")
        # the headline mg-5406 fact: the n=10 6/17 self-dual witness, +global top,
        # is the n=11 NON-self-dual 6/17 argmin (e=187 unchanged).
        el10, pr10 = witness_6_17_n10()
        tel, tpr, _ = adjoin_top(el10, pr10)
        rt = verify_C("6/17 +top (the n=11 argmin)", tel, tpr)
        assert rt.Q == SIX_17 and rt.e == 187 and rt.width == 3
        assert find_involution(tel, transitive_pred(tel, tpr)) is None, \
            "P+top of a self-dual P must be NON-self-dual (no mirror bottom)"
        bel, bpr, _ = adjoin_bottom(el10, pr10)
        rb = verify_C("6/17 +bottom (dual)", bel, bpr)
        assert rb.Q == SIX_17 and rb.e == 187 and rb.width == 3
        print(f"\n    HEADLINE: 6/17 self-dual witness (n=10) + global top = NON-self-dual")
        print(f"    width-3 poset (n=11) with Q=6/17 EXACTLY (e=187 fixed); matches the")
        print(f"    mg-5406 exhaustive n=11 NON-self-dual argmin.  +bottom dual: Q=6/17.")
        print(f"    => the order-polytope analogue of Prong-3A Lemma B 'series = max',")
        print(f"       now for ARBITRARY P (R=singleton case of Q(P(+)R)=max(Q(P),Q(R))).")

        # ---- 3. (ADJ) EXHAUSTIVE adjunction-lemma sweep on small width-3 posets ----
        print(f"\n### 3. (ADJ) EXHAUSTIVE lemma sweep -- every width-3 poset n=4..{args.adj_nmax} ###\n")
        for n in range(4, args.adj_nmax + 1):
            cnt = 0
            for el, pr in gen_width3_posets(n):
                el = list(el)
                below = transitive_pred(el, pr)
                if not incomparable_pairs(el, below):
                    continue                      # chains: Q undefined, skip
                check_adjunction_pointwise(f"n={n}#{cnt}", el, pr)
                cnt += 1
            print(f"    n={n}: {cnt:>5} width-3 posets (with an incomparable pair) -- "
                  f"e, all balances, width, Q preserved by +top AND +bottom  [OK]")
        print("    => the adjunction lemma holds on EVERY case in the swept range.")

        # ---- 4. (RED) EXTREME-REDUCTION THEOREM -- core(P), Q-preserving ----
        print("\n### 4. (RED) EXTREME-REDUCTION THEOREM -- Q(P) = Q(core(P)) ###\n")
        # the three primary rungs are already extreme-reduced (no global max/min)
        for nm, (el, pr), Qexp, kexp in rungs:
            below = transitive_pred(list(el), pr)
            ce, cb, nt, nb = extreme_core(list(el), below)
            assert nt == 0 and nb == 0, f"{nm}: expected already extreme-reduced"
            _, Qc, _ = Q_primary(ce, cb)
            assert Qc == Qexp
            sd = find_involution(ce, cb) is not None
            assert sd, f"{nm}: primary rung must be self-dual"
            print(f"    {nm:30s} extreme-reduced ALREADY (0 stripped); core self-dual; "
                  f"Q={Qc}  [fact (b)]")
        # the trivial-extension companions reduce to the self-dual core
        print()
        companions = [
            ("14/39 +top companion (n=8)", witness_14_39_n8_trivial(), FOURTEEN_39, 7),
            ("6/17 +top companion (n=11)", adjoin_top(*witness_6_17_n10())[:2], SIX_17, 10),
            ("6/17 +bottom companion (n=11)", adjoin_bottom(*witness_6_17_n10())[:2], SIX_17, 10),
        ]
        for nm, (el, pr), Qexp, ncore in companions:
            r = verify_C(nm, el, pr)
            below = transitive_pred(list(el), pr)
            ce, cb, nt, nb = extreme_core(list(el), below)
            _, Qc, _ = Q_primary(ce, cb)
            sd = find_involution(ce, cb) is not None
            assert r.Q == Qexp and Qc == Qexp and Qc == r.Q, f"{nm}: core Q mismatch"
            assert len(ce) == ncore and sd, f"{nm}: core must be the self-dual rung at n={ncore}"
            print(f"    {nm:32s} Q={r.Q}; core strips {nt} top + {nb} bottom -> "
                  f"n={len(ce)} self-dual core, Q={Qc}  [fact (a)]")
        print("\n    => the per-n overall argmin table reduces to the self-dual core:")
        print("       n=5,7,10 ARE extreme-reduced self-dual minima (fact b); n=8,11 strip")
        print("       a global extreme to reach the n=7,10 self-dual core (fact a).")
        print("       inf{Q : width-3} = inf{Q : width-3, extreme-reduced}  (RIGOROUS).")

        # ---- 5. (GAP) the self-dualization hypothesis is the named gap ----
        print("\n### 5. (GAP) reduction to the *self-dual* core is CONDITIONAL ###\n")
        print("    Adjunction + extreme-reduction reduce the full arena to the EXTREME-")
        print("    REDUCED core -- RIGOROUSLY.  They do NOT prove core(P) is self-dual")
        print("    (no Q-preserving self-dualization operation exists).  The STRONG")
        print("    statement 'self-dual core Q>=6/17 ==> full-arena Q>=6/17' needs:")
        print("      SELF-DUALIZATION HYPOTHESIS: every Q-minimizing extreme-reduced")
        print("      width-3 poset is self-dual.")
        print("    EMPIRICALLY verified exhaustively through n=11 (mg-5406, 3 168 869")
        print("    classes): every overall per-n argmin is (a) a global-extreme adjunction")
        print("    of a self-dual core, or (b) an extreme-reduced self-dual minimum.")
        print("    NOT proved -- this is the named gap; STRONG is therefore WALLED here.")

        # ---- 6. (WALL) self-dual-core analytic floor -- R1 closed-form lever ----
        print("\n### 6. (WALL) self-dual-core analytic floor -- sigma-orbit reduction R1 ###\n")
        for nm, (el, pr), Qexp, kexp in rungs:
            below = transitive_pred(list(el), pr)
            check_R1_orbit_reduction(nm, list(el), below)
        print("\n    R1 (the closed-form V2 lever): Q(P) = max over sigma-orbit reps of the")
        print("    orbit balance.  The binding orbit is a near-twin orbit-2 pair; an order-")
        print("    reversing involution PINS NO balance (Prong 3E-alpha WALL, Lemma W).  The")
        print("    bound Q>=6/17 reduces to the forced-relation order-polytope ratio")
        print("       6/17 e(P) <= e(P+x<y) <= 11/17 e(P)")
        print("    on the near-twin sigma-orbit class -- the SAME named missing input as")
        print("    mg-7ee8.  Extreme-reduction SHARPENS the target (the trivial Q-preserving")
        print("    adjunction families are excluded from the core); it does not supply it.")

        # ---- 7. self-dual-core analytic-bound sanity vs five-engine truth ----
        print("\n### 7. ANALYTIC-BOUND SANITY -- rungs + the 134/375 odd-n family ###\n")
        # the ladder identity is the closed form; it agrees with five-engine truth
        for nm, (el, pr), Qexp, kexp in rungs:
            below = transitive_pred(list(el), pr)
            e = count_le_dp(list(el), below)
            # binding pair balance (2k-1)/(3k) reproduces Q = (k+1)/(3k)
            mb = max(balance(list(el), below, e, x, y)[0]
                     for x, y in incomparable_pairs(list(el), below))
            assert mb == Qexp == Fraction(kexp + 1, 3 * kexp)
            print(f"    {nm:30s} Q={Qexp}=(k+1)/(3k), k={kexp}: closed form == five-engine")
        # the 134/375 odd-n off-ladder self-dual minimum (mg-7237, five-engine-verified
        # there): symbolic consistency with the floor candidate and the ladder.
        v = ONE_THIRD4_375
        assert SIX_17 < v < FOURTEEN_39, "134/375 must sit strictly in (6/17, 14/39)"
        assert v >= SIX_17, "134/375 must respect the 6/17 floor candidate"
        kv = k_of(v)
        assert kv == Fraction(125, 9) and kv.denominator != 1, "134/375 must be OFF-ladder"
        assert Fraction(241, 375) == 1 - v, "134/375 binding Pr = 241/375 = 1 - 134/375"
        print(f"    134/375 (odd-n self-dual min, mg-7237) = {float(v):.6f}: 6/17 < 134/375")
        print(f"      < 14/39; k=1/(3Q-1)=125/9 NOT integral (OFF the ladder); binding")
        print(f"      Pr=241/375=1-134/375 (near-twin orbit-2).  Respects the 6/17 floor;")
        print(f"      full five-engine verification lives in mg-7237 (not re-enumerated).")

        # ---- 8. CONSOLIDATED TAXONOMY -- bars / rungs / sharpness ordering ----
        print("\n### 8. CONSOLIDATED TAXONOMY -- the reference bars, in order ###\n")
        bars = [
            ("1/2  ", HALF, "trivial antichain/upper ceiling"),
            ("2/5  ", TWO_5, "Family-D bar; the {1,1,1} three-chain SP bound"),
            ("8/21 ", EIGHT_21, "width-3 SP analytic floor (Prong 3A, SHARP)"),
            ("4/11 ", FOUR_11, "descent-ladder seed (k=11)"),
            ("14/39", FOURTEEN_39, "ladder rung (k=13); odd-n NON-floor (debunked 3C)"),
            ("134/375", ONE_THIRD4_375, "odd-n off-ladder self-dual min (3F-beta)"),
            ("6/17 ", SIX_17, "width-3 corridor CEILING / floor candidate (k=17)"),
            ("1/3  ", THIRD, "global tight bound (the conjecture)"),
        ]
        prev = None
        for nm, val, note in bars:
            assert prev is None or val <= prev, f"taxonomy not sorted at {nm}"
            prev = val
            print(f"    {nm:>7} = {float(val):.6f}   {note}")
        # 27/70 is a SKEW-ARTIFACT bar (Family A): a skew-shape empirical value,
        # NOT a genuine width-3 poset Q (it does not arise from a width-3 poset).
        assert TWENTY7_70 > THIRD, "27/70 sits above 1/3"
        print(f"    {'27/70':>7} = {float(TWENTY7_70):.6f}   Family-A SKEW-ARTIFACT (skew-shape "
              f"value; NOT a genuine width-3 poset Q)")
        # the analytic sharpness ordering of the genuine width-3 floor candidates
        assert EIGHT_21 > FOUR_11 > FOURTEEN_39 > ONE_THIRD4_375 > SIX_17 > THIRD
        print("\n    sharpness: 8/21(SP) > 4/11 > 14/39 > 134/375 > 6/17 > 1/3")
        print("    => 6/17 is the deepest non-SP width-3 value found; SP cannot reach it")
        print("       (Prong 3A floors SP at 8/21); the descent lives off the SP class.")

        # ---- 9. VERDICT ----
        print("\n" + "#" * 74)
        print("# §8.2 GUARD + VERDICT")
        print("#" * 74)
        print(f"\n  lowest Q anywhere in this prong .. 6/17 = {float(SIX_17):.6f} > 1/3")
        print(f"  §8.2 anti-Cheeger guard: lowest Q = 6/17 > 1/3 ==> guard does NOT fire")
        print(f"    (no Q<=1/3 candidate; M1..M4,MC suffice; no sixth codebase triggered).")
        print(f"\n  VERDICT: OUTCOME-4 (WALL) on the STRONG self-dual-core reduction +")
        print(f"    analytic Q>=6/17, carrying TWO NEW RIGOROUS ANALYTIC DELIVERABLES:")
        print(f"    * (ADJ) Q-preserving extreme-adjunction lemma -- PROVED (the R=singleton")
        print(f"      case of Q(P(+)R)=max(Q(P),Q(R)) for arbitrary P; Lemma-B analogue).")
        print(f"    * (RED) extreme-reduction theorem -- PROVED: Q(P)=Q(core(P)), width-")
        print(f"      preserving; inf over width-3 = inf over extreme-reduced width-3.")
        print(f"    * (GAP) reduction to the SELF-DUAL core is conditional on the self-")
        print(f"      dualization hypothesis (empirical through n=11, mg-5406; not proved).")
        print(f"    * (WALL) the self-dual-core floor stays the mg-7ee8 missing input:")
        print(f"      6/17 e(P) <= e(P+x<y) <= 11/17 e(P) on the near-twin sigma-orbit class.")
        print(f"    * Corridor UNCHANGED at (1/3, 6/17]; 6/17 the corridor ceiling.")
        print("\n  CLEAN EXIT: five engines agree; the adjunction lemma holds exhaustively")
        print("  on the swept arena; the extreme-reduction core is Q-preserving and lands on")
        print("  the self-dual rungs; R1 + the named missing input re-confirm the WALL; guard")
        print("  cleared.  Prong 3I (gated on the verdict) is sketched in the math doc.")

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
