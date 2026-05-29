#!/usr/bin/env python3
r"""
onethird_ap2_prong3e_alpha_selfdual_floor_verify.py
===================================================

OneThird Algebraic-Program **AP-2 Prong 3E-alpha** (mg-7ee8) -- the analytic
floor theorem Q >= 6/17 on the SELF-DUAL width-3 class.  Follow-up to mg-5ff1
(Prong 3D-alpha), which returned LADDER-STALLED-WEAKER + Outcome-4 and the new
structural finding that all three descent-ladder rungs

        Q = 1/3 + 1/(3k) = (k+1)/(3k),  k in {11, 13, 17},
        rungs:  4/11 (k=11, n=5),  14/39 (k=13, n=7),  6/17 (k=17, n=10),

are SELF-DUAL width-3 posets whose near-twin binding pair is the sigma-orbit
pair.  Prong 3E-alpha attempts the analytic floor Q >= 6/17 on that arena.

VERDICT (this prong): **Outcome-4 -- clean negative diagnosis (WALL),
strengthening the Prong-1 precedent.**  The PRIMARY "Q >= 6/17 for all" goal is
NOT reachable from the self-dual symmetry.  The deliverable is the exact
location of the wall plus the rigorous positive structure self-duality buys:

  (R1) THE SIGMA-ORBIT REDUCTION.  With sigma an order-reversing involution on
       P, the extension involution  (Phi lambda)(c) = n+1 - lambda(sigma c)  is
       a bijection of the linear extensions, giving for incomparable {x,y}
            Pr[x<y] = Pr[sigma y < sigma x] = 1 - Pr[sigma x < sigma y],
       so incomparable pairs split into sigma-orbits of equal balance and
            Q(P) = max over sigma-orbit representatives of the orbit balance.

  (R2) EXPECTED-RANK SIGMA-ANTISYMMETRY.  rbar(x) + rbar(sigma x) = n+1, so
       every sigma-fixed element is exactly central, rbar = (n+1)/2.

  (BIND) THE BINDING SIGMA-ORBIT IS A NEAR-TWIN ORBIT-2 PAIR.  At every rung the
       Q-realising pair is a sigma-orbit of size 2 (mirrored to a DISTINCT
       equal-balance partner) -- never a sigma-swapped self-pair, never a
       both-fixed pair.  Binding Pr = (2k-1)/(3k); balance = (k+1)/(3k) = Q.

  (WALL) AN ORDER-REVERSING INVOLUTION PINS NO BALANCE.  For orbit-2 pairs sigma
       only relates the pair to its equal-balance mirror (no pinning equation).
       For a sigma-SWAPPED pair {x, sigma x} the signed gap g = lambda(sigma x)
       - lambda(x) is Phi-INVARIANT (Lemma W), so Phi permutes within each gap
       level set and cannot force 1/2.  Concretely the seed's swapped near-twins
       {b1,b2} have Pr[b1<b2] = 3/11 (BELOW 1/3, the most-biased pair), all of
       it Phi-symmetric.  Self-duality is anti-symmetry: it mirrors bias, it
       does not cancel it.  Identical to Prong-1 sec.4, transferred to width-3.

  (LEVERS) THE GADGET IDENTITY + WIDTH-3 LEVERS ALSO FAIL.  The gadget identity
       Pr[x<y_i]=i/(t+1) is single-strand; the binding balance is the
       three-strand ratio e(P+x<y)/e(P) governed by the SPORADIC global count
       e = 11, 39, 187 = 11*17 (not a clean 3k).  Width-3 yields no
       order-preserving swap.  The bound reduces to the forced-relation
       order-polytope ratio  6/17 e(P) <= e(P+x<y) <= 11/17 e(P)  on the
       near-twin sigma-orbit class -- the Ehrhart twin of Prong-1's skew-SYT
       Missing Lemma -- which self-duality provably does not supply.

  (FLOOR) LOCAL FLOOR EXHAUSTED THROUGH THE +3 SELF-DUAL SHELL.  Across all 4539
       width-3 self-dual +1/+2/+3 extensions of the 6/17 witness, min Q = 6/17,
       attained ONLY by the Q-preserving global-top/bottom adjunction (e=187
       fixed); deepest strict move 634/1763 ~ 0.3596 > 6/17.  Closes the mg-5ff1
       "+3 sampled-not-exhausted" caveat.  Evidence, not proof.

Corridor UNCHANGED at (1/3, 6/17]; 6/17 = stall rung / corridor ceiling.

GUARD (roadmap 8.2 anti-Cheeger, INHERITED STRICT).  Every Q is > 1/3 (lowest
6/17).  The guard does NOT fire; M1..M4 + MC suffice; no SIXTH codebase is
triggered (that trigger is reserved for a Q <= 1/3 claim, which does not arise).

Reuses the mg-5ff1 / mg-8bd6 five-engine harness (verify_C: M1 order-ideal DP,
M2 AP-0 kernel, M3 minimal-element-removal recursion, M4 brute permutations,
MC Ehrhart order-polynomial) and find_involution VERBATIM, and adds the
analytic-bound checkers R1-ORBIT, R2-RANK, WALL, BIND-ORBIT, LOCAL-FLOOR + the
+3 exhaustion.  Pure standard library; default run ~ 15 s.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction

from onethird_ap2_prong3c_width3_floor_verify import (
    verify_C, k_of, witness_14_39_n7, witness_6_17_n10,
    FOUR_11, FOURTEEN_39, SIX_17,
)
from onethird_ap2_prong3b_gamma_familyC_probe import seed_4_11
from onethird_ap2_prong3b_beta_familyD_probe import (
    transitive_pred, incomparable_pairs, count_le_dp, augment, Q_primary,
    guard_check, GuardHalt, THIRD,
)
from onethird_ap2_prong3d_alpha_descent_verify import (
    find_involution, gadget_point_chain,
    selfdual_extend_fixed, selfdual_extend_pair, _close,
)


# --------------------------------------------------------------------------- #
# Probability / expected-rank primitives (closed-form, exact rationals).      #
# --------------------------------------------------------------------------- #
def pr_lt(elems, below, e, x, y):
    """Pr[x < y] = e(P + x<y)/e(P) for incomparable x,y (order-polytope ratio)."""
    return Fraction(count_le_dp(elems, augment(below, x, y)), e)


def balance(elems, below, e, x, y):
    p = pr_lt(elems, below, e, x, y)
    return min(p, 1 - p), p


def expected_ranks(elems, below, e):
    """rbar(x) = 1 + sum_{y != x} Pr[y < x].  Exact rationals."""
    R = {}
    for x in elems:
        s = Fraction(1)
        for y in elems:
            if y == x:
                continue
            if y in below[x]:          # y < x always
                s += 1
            elif x in below[y]:        # x < y always -> 0
                pass
            else:                      # incomparable
                s += pr_lt(elems, below, e, y, x)
        R[x] = s
    return R


# --------------------------------------------------------------------------- #
# The extension involution Phi (Theorem R1 / R2 / Lemma W constructor).       #
# --------------------------------------------------------------------------- #
def all_linear_extensions(elems, below):
    elems = list(elems)
    out = []

    def rec(placed, seq):
        if len(seq) == len(elems):
            out.append(tuple(seq))
            return
        for x in elems:
            if x in placed:
                continue
            if below[x] <= placed:
                placed.add(x); seq.append(x)
                rec(placed, seq)
                seq.pop(); placed.remove(x)

    rec(set(), [])
    return out


def sigma_as_value_map(elems, sigma):
    """Convert the index-permutation sigma (over list(elems)) into a value->value map."""
    el = list(elems)
    idx = {v: i for i, v in enumerate(el)}
    return lambda v: el[sigma[idx[v]]], idx


# --------------------------------------------------------------------------- #
# Checkers                                                                    #
# --------------------------------------------------------------------------- #
def check_R1_orbit_reduction(name, elems, below):
    """Theorem R1: Q = max over sigma-orbit reps; every orbit carries one balance."""
    elems = list(elems)
    sigma = find_involution(elems, below)
    assert sigma is not None, f"{name}: not self-dual"
    sig, _ = sigma_as_value_map(elems, sigma)
    e = count_le_dp(elems, below)
    incomp = incomparable_pairs(elems, below)
    pset = set(frozenset(p) for p in incomp)

    # Theorem R1(a): {sigma x, sigma y} incomparable and Pr[x<y] = 1 - Pr[sigma x < sigma y].
    for x, y in incomp:
        sx, sy = sig(x), sig(y)
        assert frozenset((sx, sy)) in pset, f"{name}: sigma-image of incomp pair not incomparable"
        pxy = pr_lt(elems, below, e, x, y)
        psxsy = pr_lt(elems, below, e, sx, sy)
        assert pxy == 1 - psxsy, f"{name}: R1(a) Pr identity failed"

    # build orbits, check equal balance within orbit, and Q = max over reps
    seen = set(); reps = []
    for x, y in incomp:
        key = frozenset((x, y))
        if key in seen:
            continue
        img = frozenset((sig(x), sig(y)))
        orbit = {key} | ({img} if img in pset else set())
        seen |= orbit
        bxy = balance(elems, below, e, x, y)[0]
        for k in orbit:
            a, b = tuple(k)
            assert balance(elems, below, e, a, b)[0] == bxy, f"{name}: orbit balance not constant"
        reps.append((x, y, len(orbit), bxy))

    Q_all = max(balance(elems, below, e, x, y)[0] for x, y in incomp)
    Q_rep = max(b for *_, b in reps)
    assert Q_all == Q_rep, f"{name}: Q(orbit-reps) != Q(all)"
    n_orbit2 = sum(1 for *_, sz, _ in [(r[0], r[1], r[2], r[3]) for r in reps] if sz == 2)
    print(f"    R1-ORBIT  {name:20s} #incomp={len(incomp):>2} #orbits={len(reps):>2} "
          f"Q(reps)={Q_rep} == Q(all)  [orbit-2 reps: {n_orbit2}]")
    return sigma, sig, e, reps


def check_R2_expected_rank(name, elems, below, sigma):
    """Theorem R2: rbar(x)+rbar(sigma x)=n+1; sigma-fixed => central."""
    elems = list(elems)
    sig, _ = sigma_as_value_map(elems, sigma)
    n = len(elems); e = count_le_dp(elems, below)
    R = expected_ranks(elems, below, e)
    for x in elems:
        assert R[x] + R[sig(x)] == n + 1, f"{name}: R2 duality failed at {x}"
    fixed = [x for x in elems if sig(x) == x]
    for f in fixed:
        assert R[f] == Fraction(n + 1, 2), f"{name}: sigma-fixed {f} not central"
    ftxt = (", ".join(f"rbar({f})={R[f]}" for f in fixed)) if fixed else "fixed-point-free"
    print(f"    R2-RANK   {name:20s} rbar(x)+rbar(sx)=n+1 OK; centre: {ftxt}")
    return R


def check_binding_orbit(name, elems, below, sigma, k_expected):
    """The binding pair is a sigma-orbit-2 near-twin pair (not swapped, not both-fixed),
    with Pr = (2k-1)/(3k)."""
    elems = list(elems)
    sig, _ = sigma_as_value_map(elems, sigma)
    e = count_le_dp(elems, below)
    incomp = incomparable_pairs(elems, below)
    bx, by = max(incomp, key=lambda xy: balance(elems, below, e, *xy)[0])
    b, p = balance(elems, below, e, bx, by)
    sx, sy = sig(bx), sig(by)
    swapped = (sx == by and sy == bx)
    both_fixed = (sx == bx and sy == by)
    orbit2 = (not swapped and not both_fixed)
    assert orbit2, f"{name}: binding pair expected orbit-2, got swapped={swapped} both_fixed={both_fixed}"
    # Pr (oriented toward the larger side) = (2k-1)/(3k)
    pr_big = max(p, 1 - p)
    assert pr_big == Fraction(2 * k_expected - 1, 3 * k_expected), \
        f"{name}: binding Pr {pr_big} != (2k-1)/(3k)"
    assert b == Fraction(k_expected + 1, 3 * k_expected), f"{name}: balance != (k+1)/(3k)"
    print(f"    BIND-ORBIT {name:19s} binding ({bx},{by}) Pr={pr_big}=(2k-1)/(3k) "
          f"-> sigma-image ({sx},{sy}) [ORBIT-2, near-twin]  Q={b}")


def check_wall(name, elems, below, sigma):
    """Lemma W: the extension involution Phi is a closed involution on E, and for a
    sigma-swapped incomparable pair the signed gap is Phi-invariant => no balance
    is pinned.  Demonstrated on the seed's swapped near-twins {b1,b2}, Pr=3/11."""
    elems = list(elems)
    sig, idx = sigma_as_value_map(elems, sigma)
    n = len(elems)
    exts = all_linear_extensions(elems, below)
    e = len(exts)
    ext_set = set(exts)

    def Phi(s):
        pos = {v: i + 1 for i, v in enumerate(s)}
        newpos = {c: n + 1 - pos[sig(c)] for c in elems}
        return tuple(sorted(elems, key=lambda c: newpos[c]))

    assert all(Phi(s) in ext_set for s in exts), f"{name}: Phi not closed on E"
    assert all(Phi(Phi(s)) == s for s in exts), f"{name}: Phi not an involution"

    swapped = [(x, y) for x, y in incomparable_pairs(elems, below) if sig(x) == y]
    msg = "(no sigma-swapped incomparable pair)"
    for x, y in swapped:
        def gap(s):
            pos = {v: i + 1 for i, v in enumerate(s)}
            return pos[y] - pos[x]
        assert all(gap(Phi(s)) == gap(s) for s in exts), f"{name}: signed gap not Phi-invariant"
        p_lt = Fraction(sum(1 for s in exts if gap(s) > 0), e)
        bias = "BELOW 1/3" if p_lt < THIRD else ("ABOVE 2/3" if p_lt > 1 - THIRD else "")
        msg = (f"swapped {{{x},{y}}}: signed gap Phi-invariant, Pr[{x}<{y}]={p_lt} {bias}".strip())
    print(f"    WALL      {name:20s} Phi closed+involution on E ({e} exts); {msg}")


def main():
    ap = argparse.ArgumentParser(description="OneThird AP-2 Prong 3E-alpha self-dual floor verify")
    ap.add_argument("--skip-plus3", action="store_true",
                    help="skip the exhaustive +3 self-dual shell (faster sanity run)")
    args = ap.parse_args()

    print("#" * 74)
    print("# OneThird AP-2 Prong 3E-alpha  --  analytic floor Q >= 6/17 on the")
    print("# self-dual width-3 class.   mg-7ee8")
    print("# VERDICT: Outcome-4 -- clean negative diagnosis (WALL); 6/17 = stall rung")
    print("#" * 74)

    rungs = [("4/11 seed (k=11)", seed_4_11(), FOUR_11, 11),
             ("14/39 witness (k=13)", witness_14_39_n7(), FOURTEEN_39, 13),
             ("6/17 witness (k=17)", witness_6_17_n10(), SIX_17, 17)]

    try:
        # ---- 1. THE THREE RUNGS -- five-engine + ladder identity ----
        print("\n### 1. THE THREE RUNGS -- five-engine + ladder identity ###\n")
        built = []
        for nm, (el, pr), Qexp, kexp in rungs:
            r = verify_C(nm, el, pr)
            assert r.Q == Qexp and r.width == 3, f"{nm}: Q/width mismatch"
            assert k_of(r.Q) == kexp and 3 * r.Q - 1 == Fraction(1, kexp)
            assert r.Q == Fraction(kexp + 1, 3 * kexp)
            below = transitive_pred(list(el), pr)
            built.append((nm, list(el), below, kexp))
            print(f"    {nm:24s} e={r.e:>4} Q={r.Q} = (k+1)/(3k), k={kexp}  [M1=M2=M3=M4=MC]")

        # ---- 2. THEOREM R1 -- the sigma-orbit reduction ----
        print("\n### 2. THEOREM R1 -- the sigma-orbit reduction (Q = max over orbit reps) ###\n")
        sigmas = {}
        for nm, el, below, kexp in built:
            sigma, sig, e, reps = check_R1_orbit_reduction(nm, el, below)
            sigmas[nm] = sigma

        # ---- 3. THEOREM R2 -- expected-rank sigma-antisymmetry ----
        print("\n### 3. THEOREM R2 -- expected-rank duality rbar(x)+rbar(sx)=n+1 ###\n")
        for nm, el, below, kexp in built:
            check_R2_expected_rank(nm, el, below, sigmas[nm])

        # ---- 4. BINDING SIGMA-ORBIT CHARACTERISATION ----
        print("\n### 4. BINDING SIGMA-ORBIT -- a near-twin ORBIT-2 pair, Pr=(2k-1)/(3k) ###\n")
        for nm, el, below, kexp in built:
            check_binding_orbit(nm, el, below, sigmas[nm], kexp)

        # ---- 5. THE WALL -- Lemma W signed-gap invariance ----
        print("\n### 5. THE WALL -- an order-reversing involution pins no balance ###\n")
        for nm, el, below, kexp in built:
            check_wall(nm, el, below, sigmas[nm])
        print("\n     => sigma-orbit-2 pairs are only mirrored to equal-balance partners")
        print("        (no pinning equation); the seed's sigma-SWAPPED near-twins {b1,b2}")
        print("        are signed-gap Phi-invariant yet sit at Pr=3/11 (below 1/3).  An")
        print("        order-reversing involution is anti-symmetry: it mirrors bias, it")
        print("        does NOT cancel it.  (Prong-1 sec.4 wall, transferred to width-3.)")

        # ---- 6. THE EXTRA LEVERS -- gadget identity is single-strand ----
        print("\n### 6. WHY THE EXTRA LEVERS FAIL -- gadget Pr[x<y_i]=i/(t+1) is single-strand ###\n")
        for t in range(1, 6):
            gel, gpr = gadget_point_chain(t)
            gbelow = transitive_pred(gel, gpr)
            ge = count_le_dp(gel, gbelow)
            prs = [pr_lt(gel, gbelow, ge, "x", f"y{i}") for i in range(1, t + 1)]
            for i in range(1, t + 1):
                assert prs[i - 1] == Fraction(i, t + 1), "gadget identity failed"
            _, gQ, _ = Q_primary(gel, gbelow)
            tag = "  <- t=2: unique {1/3,2/3}, no middle pair (Q=1/3)" if t == 2 else ""
            print(f"     t={t}: Pr[x<y_i]={[str(p) for p in prs]}  Q={gQ}{tag}")
        print("\n     single-strand only; the binding balance is the THREE-strand ratio")
        print("     e(P+x<y)/e(P) governed by the SPORADIC e = 11, 39, 187=11*17 (not 3k).")
        print("     The bound reduces to  6/17 e(P) <= e(P+x<y) <= 11/17 e(P)  on the")
        print("     near-twin sigma-orbit class -- self-duality provably does not supply it.")

        # ---- 7. LOCAL FLOOR -- exhaustive +1, +2, +3 self-dual shell ----
        print("\n### 7. LOCAL FLOOR -- exhaustive +1 / +2 / +3 self-dual shell at 6/17 ###\n")
        bn, bp = 10, witness_6_17_n10()[1]
        sig6 = sigmas["6/17 witness (k=17)"]

        # +1: sigma-fixed central element
        plus1 = list(selfdual_extend_fixed(bn, bp, sig6))
        for Q, e, D, _ in plus1:
            guard_check(f"+1 D={D}", Q)
        min1 = min(Q for Q, *_ in plus1)
        print(f"    +1 (sigma-fixed central): {len(plus1)} exts, min Q = {min1} = {float(min1):.6f}")
        assert min1 == FOUR_11 and min1 >= SIX_17

        # +2: sigma-symmetric pair
        plus2 = list(selfdual_extend_pair(bn, bp, sig6))
        for Q, e, D, U, _flag, _ in plus2:
            guard_check(f"+2 D={D} U={U}", Q)
        min2 = min(Q for Q, *_ in plus2)
        ep_Q = {Q for Q, e, *_ in plus2 if e == 187}
        einc_min = min((Q for Q, e, *_ in plus2 if e != 187), default=None)
        print(f"    +2 (sigma-symmetric pair): {len(plus2)} exts, min Q = {min2} = {float(min2):.6f}")
        print(f"        e-preserving (global top+bottom) adjunctions hold Q in {sorted(map(str, ep_Q))}")
        print(f"        min over e-INCREASING extensions = {einc_min} = {float(einc_min):.6f} > 6/17")
        assert min2 == SIX_17 and ep_Q == {SIX_17} and einc_min > SIX_17

        total = len(plus1) + len(plus2)
        overall = min(min1, min2)
        if not args.skip_plus3:
            print("    +3 (EXHAUSTIVE -- closes the mg-5ff1 sampled-only caveat):")
            cnt3 = 0; min3 = None
            # +3a: fixed + fixed tower
            for Q1, e1, D1, (p1, n1) in plus1:
                s1 = find_involution(list(range(n1)), _close(n1, p1))
                if s1 is None:
                    continue
                for Q2, e2, D2, (p2, n2) in selfdual_extend_fixed(n1, p1, s1):
                    cnt3 += 1; guard_check("+3ff", Q2)
                    min3 = Q2 if min3 is None else min(min3, Q2)
            # +3b: fixed + pair
            for Q1, e1, D1, (p1, n1) in plus1:
                s1 = find_involution(list(range(n1)), _close(n1, p1))
                if s1 is None:
                    continue
                for Q2, e2, D2, U2, _f, (p2, n2) in selfdual_extend_pair(n1, p1, s1):
                    cnt3 += 1; guard_check("+3fp", Q2)
                    min3 = Q2 if min3 is None else min(min3, Q2)
            # +3c: pair + fixed
            for Q1, e1, D1, U1, _f, (p1, n1) in plus2:
                s1 = find_involution(list(range(n1)), _close(n1, p1))
                if s1 is None:
                    continue
                for Q2, e2, D2, (p2, n2) in selfdual_extend_fixed(n1, p1, s1):
                    cnt3 += 1; guard_check("+3pf", Q2)
                    min3 = Q2 if min3 is None else min(min3, Q2)
            print(f"        {cnt3} width-3 self-dual +3 extensions, min Q = {min3} = {float(min3):.6f} > 6/17")
            assert min3 > SIX_17, "a +3 self-dual extension matched/beat 6/17?!"
            total += cnt3
            print(f"\n    OVERALL self-dual local floor over {total} exts (+1/+2/+3): "
                  f"min Q = {overall} = 6/17, held ONLY by the Q-preserving adjunction.")
        else:
            print(f"    (+3 shell skipped; +1/+2 over {total} exts give min Q = 6/17.)")

        # ---- 8. SHARPNESS ORDERING ----
        print("\n### 8. SHARPNESS -- 6/17 is the deepest rung ###\n")
        assert FOUR_11 > FOURTEEN_39 > SIX_17 > THIRD
        print(f"    4/11={float(FOUR_11):.6f} > 14/39={float(FOURTEEN_39):.6f} "
              f"> 6/17={float(SIX_17):.6f} > 1/3={float(THIRD):.6f}")
        print("    => a 6/17 floor (if proved) is LOOSE at k=11,13 and SHARP at k=17.")

        # ---- 9. VERDICT ----
        print("\n" + "#" * 74)
        print("# §8.2 GUARD + VERDICT")
        print("#" * 74)
        print(f"\n  lowest Q anywhere in this prong .. 6/17 = {float(SIX_17):.6f} > 1/3")
        print(f"  §8.2 anti-Cheeger guard: lowest Q = 6/17 > 1/3 ==> guard does NOT fire")
        print(f"    (no Q<=1/3 candidate; M1..M4,MC suffice; no sixth codebase triggered).")
        print(f"\n  VERDICT: Outcome-4 -- clean negative diagnosis (WALL).")
        print(f"    * POSITIVE: Theorem R1 (sigma-orbit reduction) + Theorem R2 (expected-")
        print(f"      rank duality) are the complete probabilistic content of self-duality.")
        print(f"    * WALL: an order-reversing involution pins NO balance -- orbit-2 pairs")
        print(f"      only mirror to equal-balance partners; swapped pairs are signed-gap")
        print(f"      Phi-invariant (Lemma W).  The gadget identity is single-strand; the")
        print(f"      binding balance is the three-strand ratio e(P+x<y)/e(P) (sporadic e).")
        print(f"    * Bound reduces to 6/17 e(P) <= e(P+x<y) <= 11/17 e(P) on the near-twin")
        print(f"      sigma-orbit class -- the named missing input; self-duality cannot give it.")
        print(f"    * Local floor 6/17 EXHAUSTIVE through the +3 self-dual shell (evidence).")
        print(f"    * Corridor UNCHANGED at (1/3, 6/17]; PRIMARY/PARTIAL/REFUTATION not reached.")
        print("\n  CLEAN EXIT: five engines agree; R1/R2/WALL/BIND-ORBIT/LOCAL-FLOOR pass;")
        print("  guard cleared.  Prong 3F-beta (exhaustive self-dual floor n=11,12,13) gated.")

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
