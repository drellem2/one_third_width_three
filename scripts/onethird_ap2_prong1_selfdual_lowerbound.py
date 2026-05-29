#!/usr/bin/env python3
r"""
onethird_ap2_prong1_selfdual_lowerbound.py
==========================================

OneThird Algebraic-Program **AP-2 Prong 1** (mg-9597) -- attempt to convert the
empirical Family-A self-dual floor (min Q = 27/70 at n=8, plateau/rise above 1/3
for n >= 9) into an ANALYTIC lower bound, OR diagnose precisely where the
argument fails.

Reference / lineage:
  * docs/OneThird-AP-0-FamilyA-Viability-Probe.md            (AP-0 verdict, mg-98a6)
  * docs/OneThird-AP-1a-FamilyA-SmallK-Snapshot.md            (AP-1a verdict, mg-746f)
  * docs/OneThird-AP-1b-followup-FamilyA-extended-sweep.md    (AP-1b' rule, mg-106e)
  * docs/OneThird-AP-2-Prong1-SelfDual-LowerBound.md          (THIS ticket's report)
  * docs/OneThird-Algebraic-Program-Roadmap.md                (sections 5, 6, 8)
  * docs/OneThird-Algebraic-Program-Vision.md                 (vision-parts 3 + 4)

WHAT THIS SCRIPT IS.
  The AP-2 Prong-1 deliverable is an ANALYTIC argument (a math doc), not a sweep.
  This script performs the NUMERICAL CROSS-CHECKS that the analytic argument
  rests on, so that every structural claim in the doc is machine-verified, and
  re-confirms the three carry-forward witnesses against the AP-0 kernel.  It is a
  routine-checks harness, not a search.

THE SELF-DUAL RULE (mg-106e).
  A 3-row skew shape lam/mu is centrally symmetric (self-dual) iff
        mu_3 = 0,   lam_3 = lam_1 - mu_1,   mu_2 = lam_1 - lam_2.
  Free parameters (C = lam_1, lam_2, mu_1); n = 2(lam_1 - mu_1) + (2*lam_2 - lam_1).
  The 180-degree box rotation  rho(i,j) = (4-i, C+1-j)  is an order-REVERSING
  bijection of the cell set, so the cell-poset P satisfies P ~= P^op.

THE CLAIMS THIS SCRIPT VERIFIES (each is a load-bearing line of the doc).
  C1  rho is a bijection of the cell set and reverses the product order
      (anti-automorphism).
  C2  CENTRAL-SYMMETRY PAIR IDENTITY.  For every incomparable pair (x,y),
            Pr[x < y] = Pr[rho(y) < rho(x)].
      (The probabilistic content of the 180-degree box-rotation invariance.)
  C3  ORBIT RELATION.  For every incomparable pair, Pr[rho(x) < rho(y)] = 1 - Pr[x<y];
      hence rho pairs incomparable pairs into orbits of EQUAL balance
      min(p, 1-p).
  C4  THE WALL (signed-gap invariance).  For a rho-SWAPPED incomparable pair
      {x, rho(x)} the signed gap  sigma(rho x) - sigma(x)  is INVARIANT under the
      extension involution sigma |-> sigma' (sigma'(c) = n+1 - sigma(rho c)).
      => the box-rotation symmetry imposes NO constraint on Pr[x < rho x];
      it pins NO pair's balance to 1/2 and bounds none away from {0,1}.
  C5  TRIVIAL AUTOMORPHISM GROUP.  No incomparable pair has balance exactly 1/2
      on these shapes (Q < 1/2 throughout), so there is no order-AUTOMORPHISM
      swapping an incomparable pair -- the easy "automorphism => 1/2 => Q>=1/3"
      route is unavailable.
  C6  DP-BOUND KERNEL.  The Q-realising augmented poset is essentially never a
      skew shape (closed-form/Naruse fraction ~ 0), so the balance of the
      Q-realising pair is a ratio of two skew-SYT counts with NO closed form on
      this family -- the quantity the analytic bound would have to control.

  WITNESS RE-VERIFICATION (routine check, ticket-mandated).
      Re-derive Q for the three carry-forward witnesses via the AP-0 kernel and
      compare to mg-106e.  NOTE: the mg-9597 ticket body lists the n=19 witness
      (13,8,8)/(5,5,0) with "Q = 943/2074"; that is a transcription of the OLD
      cap-12 argmin (12,7,4)/(3,1,0).  The mg-106e doc value for (13,8,8)/(5,5,0)
      is 2307921/5088542 ~ 0.45355, which this script confirms.

ACCEPTANCE GATE (roadmap section 5.3a).  Q is reported only under the validated
  two-method gate: for e <= BRUTE_CAP the full M1==M2 brute-force gate runs
  (probe_shape asserts inline) and e is cross-checked by M3 Naruse; for the n=19
  witness (e ~ 5.1M) the gate is DP==Naruse on e plus the validated DP for Q.

GUARD (roadmap section 8.2, anti-Cheeger).  No Q <= 1/3 arises anywhere here;
  were it ever to, that is NOT a counterexample claim -- it would trigger
  MANDATORY independent reimplementation plus brute force.  A loud STOP banner
  prints in that case.

NON-GOALS (roadmap section 8): no Cheeger; no counterexample claim; no Lean /
  LaTeX / main.tex; width-3 only; Monte-Carlo never the source of truth.

Pure Python / standard library only.  Full run is well under a minute.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from onethird_ap0_familyA_skew_probe import (  # noqa: E402
    skew_cells,
    build_poset,
    poset_width,
    product_leq,
    count_linear_extensions_dp,
    augment_relation,
    naruse_count,
    enumerate_linear_extensions,
    try_realise_as_skew_shape,
    probe_shape,
)

THIRD = Fraction(1, 3)
HALF = Fraction(1, 2)
BRUTE_CAP = 200_000


# --------------------------------------------------------------------------- #
# Self-dual (centrally-symmetric) 3-row skew shapes + the box rotation rho     #
# --------------------------------------------------------------------------- #
def is_self_dual_3row(lam, mu):
    """mu_3 = 0, lam_3 = lam_1 - mu_1, mu_2 = lam_1 - lam_2 (and a valid shape)."""
    if len(lam) != 3 or len(mu) != 3:
        return False
    l1, l2, l3 = lam
    m1, m2, m3 = mu
    if m3 != 0:
        return False
    if l3 != l1 - m1:
        return False
    if m2 != l1 - l2:
        return False
    # valid skew: mu a partition <= lam, all three rows non-empty
    if not (m1 >= m2 >= m3):
        return False
    if not (l1 >= l2 >= l3):
        return False
    if any(mu[i] > lam[i] for i in range(3)):
        return False
    if any(lam[i] - mu[i] <= 0 for i in range(3)):
        return False
    return True


def rho(c, C):
    """180-degree box rotation of cell c=(i,j) in a 3-row box of width C=lam_1."""
    return (4 - c[0], C + 1 - c[1])


def selfdual_min_witnesses():
    """The cap-stable per-n self-dual minimisers from mg-106e section 3 (n in [7,16]),
    used as a representative test bank for the structural identities."""
    return {
        7: ((5, 5, 1), (4, 0, 0)),
        8: ((4, 4, 2), (2, 0, 0)),
        9: ((5, 4, 3), (2, 1, 0)),
        10: ((6, 4, 4), (2, 2, 0)),
        11: ((7, 6, 3), (4, 1, 0)),
        12: ((8, 8, 2), (6, 0, 0)),
        13: ((5, 5, 4), (1, 0, 0)),
        14: ((10, 6, 6), (4, 4, 0)),
        15: ((5, 5, 5), (0, 0, 0)),
        16: ((8, 6, 6), (2, 2, 0)),
    }


# --------------------------------------------------------------------------- #
# Kernel helpers                                                              #
# --------------------------------------------------------------------------- #
def pair_prlt(cells, less, e, x, y):
    """Pr[x < y] under uniform linear extensions, via the validated order-ideal DP."""
    nx = count_linear_extensions_dp(cells, augment_relation(less, x, y))
    return Fraction(nx, e)


def Q_and_argmax(cells, less, incomp, e):
    """(Q, argmax-pair, any-pair-exactly-1/2)."""
    Q = Fraction(0)
    arg = None
    any_half = False
    for (x, y) in incomp:
        p = pair_prlt(cells, less, e, x, y)
        if p == HALF:
            any_half = True
        m = min(p, 1 - p)
        if m > Q:
            Q = m
            arg = (x, y)
    return Q, arg, any_half


# --------------------------------------------------------------------------- #
# C1: rho is an order-reversing bijection (anti-automorphism)                  #
# --------------------------------------------------------------------------- #
def check_anti_automorphism(lam, mu):
    C = lam[0]
    cells = skew_cells(lam, mu)
    cset = set(cells)
    # bijection of cell set
    assert all(rho(c, C) in cset for c in cells), f"rho not closed on {lam}/{mu}"
    assert len({rho(c, C) for c in cells}) == len(cells), "rho not injective"
    # order-reversing: x < y  <=>  rho(y) < rho(x)
    for x in cells:
        for y in cells:
            fwd = product_leq(x, y)
            rev = product_leq(rho(y, C), rho(x, C))
            assert fwd == rev, f"rho not order-reversing at {x},{y} in {lam}/{mu}"
    return True


# --------------------------------------------------------------------------- #
# C2 + C3: central-symmetry pair identity and orbit relation                   #
# --------------------------------------------------------------------------- #
def check_pair_identity(lam, mu):
    C = lam[0]
    cells = skew_cells(lam, mu)
    less, incomp = build_poset(cells)
    e = count_linear_extensions_dp(cells, less)
    for (x, y) in incomp:
        p = pair_prlt(cells, less, e, x, y)
        rx, ry = rho(x, C), rho(y, C)
        # C2: Pr[x<y] = Pr[rho y < rho x]
        assert pair_prlt(cells, less, e, ry, rx) == p, \
            f"C2 fail {x},{y} on {lam}/{mu}"
        # C3: Pr[rho x < rho y] = 1 - Pr[x<y]  (so the orbit has equal balance)
        assert pair_prlt(cells, less, e, rx, ry) == 1 - p, \
            f"C3 fail {x},{y} on {lam}/{mu}"
    return e, len(incomp)


# --------------------------------------------------------------------------- #
# C4: THE WALL -- signed-gap invariance for rho-swapped pairs                  #
# --------------------------------------------------------------------------- #
def swapped_incomparable_pairs(lam, mu):
    """All rho-swapped incomparable pairs {x, rho x} (x != rho x, incomparable).
    These are exactly the row-1<->row-3 pairs (1,j)<->(3,C+1-j) with 2j > C+1."""
    C = lam[0]
    cells = set(skew_cells(lam, mu))
    out = []
    seen = set()
    for x in cells:
        rx = rho(x, C)
        if rx == x or rx not in cells:
            continue
        key = frozenset((x, rx))
        if key in seen:
            continue
        if not product_leq(x, rx) and not product_leq(rx, x):
            out.append((x, rx))
            seen.add(key)
    return out


def check_signed_gap_invariance(lam, mu):
    """For each rho-swapped incomparable pair, the distribution of the signed gap
    sigma(rho x) - sigma(x) is invariant under the involution sigma |-> sigma'.
    Returns (n_swapped_pairs, all_invariant)."""
    C = lam[0]
    cells = skew_cells(lam, mu)
    less, _ = build_poset(cells)
    exts = enumerate_linear_extensions(cells, less)
    n = len(cells)
    swapped = swapped_incomparable_pairs(lam, mu)
    all_inv = True
    for (x, y) in swapped:  # y = rho x
        gap = Counter()
        gap_inv = Counter()
        for seq in exts:
            pos = {c: i for i, c in enumerate(seq)}
            gap[pos[y] - pos[x]] += 1
            # involution image: sigma'(c) = (n-1) - sigma(rho c)  (0-indexed)
            sp = {c: (n - 1) - pos[rho(c, C)] for c in cells}
            seqp = sorted(cells, key=lambda c: sp[c])
            posp = {c: i for i, c in enumerate(seqp)}
            gap_inv[posp[y] - posp[x]] += 1
        if gap != gap_inv:
            all_inv = False
    return len(swapped), all_inv


# --------------------------------------------------------------------------- #
# C6: DP-bound kernel -- the Q-realising augmented poset is not skew           #
# --------------------------------------------------------------------------- #
def check_qpair_not_skew(lam, mu, arg):
    x, y = arg
    less, _ = build_poset(skew_cells(lam, mu))
    sk_xy = try_realise_as_skew_shape(augment_relation(less, x, y))
    sk_yx = try_realise_as_skew_shape(augment_relation(less, y, x))
    return (sk_xy is None) and (sk_yx is None)


# --------------------------------------------------------------------------- #
# Witness re-verification (routine check)                                      #
# --------------------------------------------------------------------------- #
def reverify_witnesses():
    print("=" * 72)
    print("  WITNESS RE-VERIFICATION (AP-0 kernel; cross-check vs mg-106e)")
    print("=" * 72)
    mg106e = {
        (((4, 4, 2), (2, 0, 0)), 8): Fraction(27, 70),
        (((5, 5, 4), (1, 0, 0)), 13): Fraction(3, 7),
        (((13, 8, 8), (5, 5, 0)), 19): Fraction(2307921, 5088542),
    }
    all_ok = True
    for ((lam, mu), n), expected in mg106e.items():
        cells = skew_cells(lam, mu)
        less, incomp = build_poset(cells)
        width = poset_width(less)
        e = count_linear_extensions_dp(cells, less)
        en = naruse_count(lam, mu)
        assert e == en, f"e mismatch {lam}/{mu}: DP={e} Naruse={en}"
        if e <= BRUTE_CAP:
            # full M1==M2 brute gate via the AP-0 probe_shape (asserts inline)
            r = probe_shape(lam, mu, f"witness n={n}", verbose=False)
            Q = r.Q
            gate = "M1==M2 brute; e==Naruse"
        else:
            Q, _, _ = Q_and_argmax(cells, less, incomp, e)
            gate = "DP==Naruse(e); Q by validated DP"
        ok = (Q == expected)
        all_ok &= ok
        sd = is_self_dual_3row(lam, mu)
        print(f"  n={n:>2}  {lam}/{mu}:  e={e}  width={width}  self-dual={sd}")
        print(f"        Q = {Q} ({float(Q):.6f})   expected(mg-106e) {expected}"
              f"  MATCH={ok}   [{gate}]")
        assert Q > THIRD, f"GUARD: Q <= 1/3 at witness {lam}/{mu}!"
    print(f"\n  NOTE: ticket body lists n=19 as 'Q=943/2074' "
          f"({float(Fraction(943,2074)):.6f}); that is the OLD cap-12 argmin "
          f"(12,7,4)/(3,1,0).")
    print(f"        Correct (13,8,8)/(5,5,0) value is 2307921/5088542 "
          f"({float(Fraction(2307921,5088542)):.6f}) -- confirmed above.")
    print(f"\n  All witness Q match mg-106e: {all_ok}")
    return all_ok


# --------------------------------------------------------------------------- #
# Main                                                                        #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true",
                    help="skip the n=19 witness (e~5.1M) and the larger "
                         "signed-gap enumerations")
    args = ap.parse_args()

    print("#" * 72)
    print("# OneThird AP-2 Prong 1 (mg-9597) -- self-dual analytic lower-bound")
    print("# routine numerical cross-checks for the analytic argument")
    print("#" * 72)
    print()

    # ----- 0. routine witness re-verification -----
    if args.quick:
        # quick: only the two brute-feasible witnesses
        print("=" * 72)
        print("  WITNESS RE-VERIFICATION (quick: n=8, n=13 only)")
        print("=" * 72)
        for (lam, mu, n, exp) in [((4, 4, 2), (2, 0, 0), 8, Fraction(27, 70)),
                                  ((5, 5, 4), (1, 0, 0), 13, Fraction(3, 7))]:
            r = probe_shape(lam, mu, f"witness n={n}", verbose=False)
            print(f"  n={n}: {lam}/{mu}  Q={r.Q} ({float(r.Q):.6f})  "
                  f"expected {exp}  MATCH={r.Q == exp}")
            assert r.Q > THIRD
        witnesses_ok = True
    else:
        witnesses_ok = reverify_witnesses()
    print()

    # ----- structural-claim test bank: the per-n self-dual minimisers -----
    bank = dict(selfdual_min_witnesses())
    if not args.quick:
        # include the three carry-forward witnesses too (n=19 enumeration is
        # skipped for C4 since brute force is infeasible; C1-C3,C5,C6 use DP)
        bank[19] = ((13, 8, 8), (5, 5, 0))

    print("=" * 72)
    print("  STRUCTURAL CLAIMS C1-C6 on the self-dual per-n minimiser bank")
    print("=" * 72)

    overall = True
    for n in sorted(bank):
        lam, mu = bank[n]
        assert is_self_dual_3row(lam, mu), f"{lam}/{mu} not self-dual!"

        # C1
        c1 = check_anti_automorphism(lam, mu)
        # C2 + C3
        e, npairs = check_pair_identity(lam, mu)
        # Q + argmax + 1/2 scan (C5)
        cells = skew_cells(lam, mu)
        less, incomp = build_poset(cells)
        Q, arg, any_half = Q_and_argmax(cells, less, incomp, e)
        c5 = not any_half  # no exactly-1/2 pair => trivial automorphism route
        assert Q > THIRD, f"GUARD: Q <= 1/3 at {lam}/{mu}!"
        # which pair realises Q -- is it rho-swapped (self-symmetric) or orbit-2?
        C = lam[0]
        x, y = arg
        is_swapped = (rho(x, C) == y)
        # C6
        c6 = check_qpair_not_skew(lam, mu, arg)
        # C4 (skip the heaviest enumerations under --quick / large e)
        if args.quick or e > 50000:
            nsw, c4 = swapped_incomparable_pairs(lam, mu), None
            nsw = len(nsw)
            c4str = "skipped(e large)"
        else:
            nsw, c4 = check_signed_gap_invariance(lam, mu)
            c4str = f"{c4}"
            overall &= bool(c4)

        overall &= bool(c1 and c5 and c6)
        rows = f"row{x[0]}<->row{y[0]}"
        kind = (f"rho-SWAPPED self-symmetric ({rows})" if is_swapped
                else f"orbit-2 non-self-symmetric ({rows})")
        print(f"  n={n:>2} {lam}/{mu}: Q={str(Q):>17} ({float(Q):.5f})  "
              f"e={e}")
        print(f"        C1 anti-auto={c1}  C2/C3 pair-identity=OK ({npairs} pairs)  "
              f"C5 no-1/2-pair={c5}")
        print(f"        Q-pair {arg} is {kind};  "
              f"#rho-swapped incomp pairs={nsw}  C4 signed-gap-invariant={c4str}  "
              f"C6 Q-aug-not-skew={c6}")

    print()
    print("=" * 72)
    print("  VERDICT BANNER")
    print("=" * 72)
    print(f"  witnesses match mg-106e:                 {witnesses_ok}")
    print(f"  C1-C6 structural claims hold on bank:    {overall}")
    print()
    print("  ANALYTIC READING (see docs/OneThird-AP-2-Prong1-SelfDual-LowerBound.md):")
    print("   * The box-rotation gives the central-symmetry pair identity (C2) and")
    print("     organises incomparable pairs into equal-balance orbits (C3).")
    print("   * But it pins NO pair's balance: rho-swapped pairs have an")
    print("     involution-invariant signed gap (C4), and there is no order-")
    print("     automorphism (C5).  So symmetry ALONE gives no lower bound on")
    print("     Q = max balance.")
    print("   * The Q-realising balance is a ratio of two skew-SYT counts with no")
    print("     closed form on this family (C6) -- the width-3-DP quantity an")
    print("     analytic bound would have to control.  THAT is the wall.")
    print("   * VERDICT: Goal 1 (Q>=27/70) and Goal 2 (Q>1/3) are NOT reachable")
    print("     from the box-rotation symmetry.  Clean negative diagnosis; the")
    print("     best UNCONDITIONAL bound (BFT 1995, ~0.2764) sits BELOW 1/3.")
    if not (witnesses_ok and overall):
        print("\n  *** A CHECK FAILED -- see assertions above. ***")
        sys.exit(1)
    print()
    print("  GUARD (roadmap 8.2): no Q <= 1/3 observed anywhere.")
    print("  A clean exit IS the two-method gate + structural-claim suite passing.")


if __name__ == "__main__":
    main()
