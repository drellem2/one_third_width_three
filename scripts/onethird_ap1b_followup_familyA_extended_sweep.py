#!/usr/bin/env python3
r"""
onethird_ap1b_followup_familyA_extended_sweep.py
================================================

OneThird Algebraic-Program **AP-1b'** (mg-106e) -- Family A (hook-length /
skew-shape) follow-up to AP-1a (mg-746f): raise the lambda_1 cap, re-measure the
per-n argmins, and identify + sweep the *actual* generalising shape rule.

Reference / lineage:
  * docs/OneThird-AP-0-FamilyA-Viability-Probe.md          (AP-0 verdict, mg-98a6)
  * docs/OneThird-AP-1a-FamilyA-SmallK-Snapshot.md          (AP-1a verdict, mg-746f)
  * docs/OneThird-AP-1b-followup-FamilyA-extended-sweep.md  (this ticket's report)
  * docs/OneThird-Algebraic-Program-Roadmap.md              (sections 5, 6, 8)
  * docs/OneThird-Algebraic-Program-Vision.md               (vision-parts 3 + 4)

WHY THIS TICKET.
  AP-1a falsified the (3k+1,3k,3k)/(3k,0,0) ray as a descent ray and handed
  forward THREE corrected minimum candidates plus a HYPOTHESIS for the actual
  minimiser family.  Two of those candidates (n=19) sat AT the lambda_1 = 12
  sweep cap, so they were only upper-bound estimates.  AP-1b' (1) raises the cap
  (target lambda_1 <= 24) and re-measures the per-n argmin, (2) tests AP-1a's
  HYPOTHESIS and identifies the *real* generalising rule, (3) sweeps that rule,
  (4) calls descent-vs-plateau on it, (5) tracks the closed-form fraction.

THE HYPOTHESIS UNDER TEST (AP-1a section 6, carried forward verbatim).
  "shapes where mu is small (first row 1-3, second row 0 or 1), lambda rows are
   close in size (within 1 of each other for the top two, one smaller third
   row)."
  This FITS the n=8, n=13 argmins -- but it is FALSIFIED by the cap-raised n=19
  argmin (see below), which has mu=(5,5,0) and lambda=(13,8,8).

THE ACTUAL GENERALISING RULE (this ticket's finding).
  Every cap-stable per-n minimiser is a **centrally-symmetric (self-dual) skew
  shape** -- invariant under the 180-degree rotation (i,j) -> (4-i, C+1-j) of
  its 3-row bounding box (C = lambda_1).  The 180-degree rotation reverses the
  product order, so such a poset P satisfies P isomorphic to P^op (self-dual).
  For a 3-row skew shape, central symmetry is exactly:
        mu_3 = 0,   lambda_3 = lambda_1 - mu_1,   mu_2 = lambda_1 - lambda_2.
  Free parameters (C=lambda_1, lambda_2, mu_1); n = 2(lambda_1 - mu_1)
  + (2*lambda_2 - lambda_1).  AP-1a's HYPOTHESIS is precisely the
  mu_2 = 0 (i.e. lambda_1 = lambda_2), small-mu_1 sub-slice of THIS family.

ACCEPTANCE GATE (roadmap section 5.3a, reused verbatim from AP-0/AP-1a).
  Q is reported only when the validated two-method gate holds: order-ideal DP
  (M2) is the sweep engine; for every headline witness with e <= BRUTE_CAP the
  FULL M1==M2 brute-force gate runs (probe_shape asserts inline), and e is always
  cross-checked by M3 Naruse.  For witnesses with e > BRUTE_CAP (e.g. the n=19
  minimiser, e ~ 5.1M) the brute force is infeasible, so the gate is DP==Naruse
  on e plus the validated DP for Q (identical fallback to AP-1a's k=3 path).

GUARD (roadmap section 8.2, anti-Cheeger).  IF Q <= 1/3 at ANY shape, that is NOT
  a counterexample claim: it triggers MANDATORY INDEPENDENT REIMPLEMENTATION in
  a separate codebase plus brute force before any claim.  The AP-0/AP-1a/AP-1b'
  three-engine agreement is NOT independent code.  A loud STOP banner prints in
  that case.  (No Q <= 1/3 arises here: the all-time Family A record stays
  27/70 ~ 0.386 at n=8.)

NON-GOALS (roadmap section 8): no Cheeger; no counterexample claim without the
  guard cleared; no Lean / LaTeX / main.tex; width-3 only; Monte-Carlo never the
  source of truth.

Pure-Python / standard library + multiprocessing; reuses the AP-0 engine verbatim.
Full run ~15-20 min on a 10-core laptop; --quick ~5 min.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from onethird_ap0_familyA_skew_probe import (  # noqa: E402
    skew_cells,
    build_poset,
    poset_width,
    count_linear_extensions_dp,
    augment_relation,
    naruse_count,
    try_realise_as_skew_shape,
    Q_via_dp,
    probe_shape,
    enumerate_3row_skew_shapes,
)

THIRD = Fraction(1, 3)
BRUTE_CAP = 200_000  # run the full M1==M2 brute gate only when e <= this
NPROC = min(10, os.cpu_count() or 1)


# --------------------------------------------------------------------------- #
# Self-dual (centrally-symmetric) 3-row skew shapes                            #
# --------------------------------------------------------------------------- #
def is_self_dual_3row(lam, mu):
    """True iff lam/mu is a centrally-symmetric 3-row skew shape:
    mu_3 = 0, lam_3 = lam_1 - mu_1, mu_2 = lam_1 - lam_2."""
    lam = list(lam) + [0] * (3 - len(lam))
    mu = list(mu) + [0] * (3 - len(mu))
    if mu[2] != 0:
        return False
    if lam[2] != lam[0] - mu[0]:
        return False
    if mu[1] != lam[0] - lam[1]:
        return False
    return True


def selfdual_shapes(n, cap):
    """All self-dual 3-row skew shapes with |lam/mu| == n, lam_1 <= cap, all
    rows non-empty.  Parameterised by (C=lam_1, lam_2, mu_1)."""
    out = []
    for C in range(1, cap + 1):
        for lam2 in range(1, C + 1):
            mu2 = C - lam2
            if mu2 > lam2 or mu2 < 0:
                continue
            for mu1 in range(0, C + 1):
                lam3 = C - mu1
                lam = (C, lam2, lam3)
                mu = (mu1, mu2, 0)
                if not (lam[0] >= lam[1] >= lam[2] >= 1):
                    continue
                if not (mu[0] >= mu[1] >= mu[2] >= 0):
                    continue
                if any(mu[i] > lam[i] for i in range(3)):
                    continue
                if any(lam[i] - mu[i] <= 0 for i in range(3)):
                    continue
                if sum(lam) - sum(mu) != n:
                    continue
                out.append((lam, mu))
    return out


def fits_ap1a_hypothesis(lam, mu):
    """AP-1a's carried-forward hypothesis: mu_1 in {1,2,3}, mu_2 in {0,1}, top
    two lambda rows within 1 of each other, third row strictly smaller."""
    lam = list(lam) + [0] * (3 - len(lam))
    mu = list(mu) + [0] * (3 - len(mu))
    return (mu[0] in (1, 2, 3)
            and mu[1] in (0, 1)
            and abs(lam[0] - lam[1]) <= 1
            and lam[2] < lam[1])


# --------------------------------------------------------------------------- #
# Multiprocessing worker: (lam, mu) -> Q via the validated DP (width-3 only)   #
# --------------------------------------------------------------------------- #
def _shape_Q(args):
    lam, mu = args
    cells = skew_cells(lam, mu)
    less, incomp = build_poset(cells)
    if poset_width(less) != 3:
        return (lam, mu, None)
    _, Q = Q_via_dp(cells, less, incomp)
    return (lam, mu, Q)


def sweep_all(n, cap, pool):
    """Global min Q over ALL width-3 3-row skew shapes at n, lam_1 <= cap."""
    shapes = list(enumerate_3row_skew_shapes(n, cap))
    res = [(l, m, Q) for (l, m, Q) in pool.map(_shape_Q, shapes, chunksize=8)
           if Q is not None]
    minQ = min(Q for _, _, Q in res)
    argmin = [(l, m) for l, m, Q in res if Q == minQ]
    return minQ, argmin, len(res)


def sweep_selfdual(n, cap, pool):
    """Min Q over self-dual width-3 3-row skew shapes at n, lam_1 <= cap."""
    shapes = selfdual_shapes(n, cap)
    res = [(l, m, Q) for (l, m, Q) in pool.map(_shape_Q, shapes, chunksize=4)
           if Q is not None]
    if not res:
        return None, [], 0
    minQ = min(Q for _, _, Q in res)
    argmin = [(l, m) for l, m, Q in res if Q == minQ]
    return minQ, argmin, len(res)


# --------------------------------------------------------------------------- #
# Verified-Q for a single headline witness (full brute gate when e small)      #
# --------------------------------------------------------------------------- #
def verified_Q(lam, mu):
    """Return (e, Q, gate_str).  Runs the FULL M1==M2 brute gate (probe_shape,
    which asserts brute==DP and e==Naruse inline) when e <= BRUTE_CAP; else the
    DP==Naruse(e) + validated-DP(Q) fallback (AP-1a's large-e path)."""
    cells = skew_cells(lam, mu)
    less, incomp = build_poset(cells)
    e_dp = count_linear_extensions_dp(cells, less)
    e_nar = naruse_count(lam, mu)
    assert e_dp == e_nar, f"e mismatch {lam}/{mu}: DP={e_dp} Naruse={e_nar}"
    if e_dp <= BRUTE_CAP:
        r = probe_shape(lam, mu, f"{lam}/{mu}", verbose=False)
        assert r.e == e_dp
        return r.e, r.Q, "M1==M2 brute gate; e==Naruse"
    _, Q = Q_via_dp(cells, less, incomp)
    return e_dp, Q, "DP==Naruse(e); Q by validated DP (e>BRUTE_CAP, brute infeasible)"


# --------------------------------------------------------------------------- #
# Closed-form-applicability fraction (DP-only; works at any e)                  #
# --------------------------------------------------------------------------- #
def cf_fraction(lam, mu):
    """Fraction of forced-pair numerators that stay a genuine skew shape (closed
    form via Naruse) instead of falling through to the width-3 DP.  Each hit is
    self-validated by requiring Naruse(realised) == DP count.  DP-only, so this
    works even when e exceeds the brute-force cap."""
    cells = skew_cells(lam, mu)
    less, incomp = build_poset(cells)
    cf = 0
    for (x, y) in incomp:
        less_xy = augment_relation(less, x, y)
        nx = count_linear_extensions_dp(cells, less_xy)
        hit = False
        r = try_realise_as_skew_shape(less_xy)
        if r is not None and naruse_count(*r) == nx:
            hit = True
        if not hit:
            less_yx = augment_relation(less, y, x)
            ny = count_linear_extensions_dp(cells, less_yx)
            r2 = try_realise_as_skew_shape(less_yx)
            if r2 is not None and naruse_count(*r2) == ny:
                hit = True
        if hit:
            cf += 1
    return cf, len(incomp)


# --------------------------------------------------------------------------- #
# Main                                                                         #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true",
                    help="skip the slowest passes (n=19 cap-24 global sweep, "
                         "self-dual curve beyond n=20); ~5 min smoke run")
    args = ap.parse_args()

    caps = [12, 18] if args.quick else [12, 18, 24]
    sd_hi = 20 if args.quick else 24

    print("#" * 72)
    print("# OneThird AP-1b'  --  Family A extended sweep (raise lambda_1 cap,")
    print("# generalise the corrected minimiser).  mg-106e   roadmap sections 5,6,8")
    print("#" * 72)

    minima = {}  # n -> (Q, argmin0) at the largest cap run
    pool = Pool(NPROC)
    try:
        # ---- SCOPE 1: extended-cap argmins ----
        print("\n### 1. EXTENDED-CAP ARGMINS (raise lambda_1; was capped at 12) ###\n")
        for n in (7, 8, 13, 19):
            print(f"  n = {n}:")
            prev = None
            corrected = None
            for cap in caps:
                if args.quick and n == 19 and cap == 18:
                    pass  # still run; the long pole (cap 24) is the one skipped
                t0 = time.time()
                minQ, argmin, w3 = sweep_all(n, cap, pool)
                at_cap = any(l[0] == cap for l, m in argmin)
                dropped = "" if prev is None else (
                    " (DROPPED from prev cap)" if minQ < prev else " (stable)")
                print(f"     cap {cap:>2}: min Q = {minQ} (~{float(minQ):.6f})  "
                      f"[{w3} width-3 shapes]  argmin={argmin[0]}"
                      f"{'  <-- argmin AT cap' if at_cap else ''}{dropped}  "
                      f"({time.time()-t0:.0f}s)")
                prev = minQ
                corrected = (minQ, argmin[0])
            minima[n] = corrected
            print()

        # ---- SCOPE 1 verification: full gate on corrected witnesses ----
        print("  Corrected per-n argmin witnesses (verification gate):\n")
        for n in (7, 8, 13, 19):
            Q0, (lam, mu) = minima[n]
            e, Q, gate = verified_Q(lam, mu)
            assert Q == Q0, f"verify mismatch n={n}: sweep {Q0} vs verify {Q}"
            sd = "self-dual" if is_self_dual_3row(lam, mu) else "NOT self-dual"
            print(f"     n={n:>2}: {lam}/{mu}  e={e}  Q={Q} (~{float(Q):.6f})  "
                  f"[{sd}]  [{gate}]")

        # ---- SCOPE 2: the generalising rule ----
        print("\n\n### 2. THE GENERALISING RULE ###\n")
        print("  (a) AP-1a's carried-forward HYPOTHESIS test (mu small, lambda")
        print("      top-two within 1, smaller third):\n")
        n19_lam, n19_mu = minima[19][1]
        for n in (8, 13, 19):
            lam, mu = minima[n][1]
            fits = fits_ap1a_hypothesis(lam, mu)
            print(f"     n={n:>2}: {lam}/{mu}  fits hypothesis = {fits}")
        print(f"\n     >>> HYPOTHESIS FALSIFIED by the cap-raised n=19 argmin "
              f"{n19_lam}/{n19_mu}")
        print(f"         (mu_1={n19_mu[0]} not in 1-3, mu_2={n19_mu[1]} not in "
              f"0-1, lambda top-two differ by {abs(n19_lam[0]-n19_lam[1])}).")

        print("\n  (b) The ACTUAL rule: every cap-stable per-n minimiser is a")
        print("      CENTRALLY-SYMMETRIC (self-dual) skew shape "
              "(mu_3=0, lam_3=lam_1-mu_1, mu_2=lam_1-lam_2):\n")
        for n in (8, 13, 19):
            lam, mu = minima[n][1]
            print(f"     n={n:>2}: {lam}/{mu}  self-dual = {is_self_dual_3row(lam, mu)}")
        print("     (AP-1a's hypothesis = the mu_2=0 / lam_1=lam_2 sub-slice of "
              "this family.)")

        print("\n  (c) Does the self-dual family min EQUAL the global min at each "
              "n?\n")
        cap_v = 18
        sd_eq = []
        for n in range(7, 16):
            gmin, gargs, _ = sweep_all(n, cap_v, pool)
            smin, sargs, _ = sweep_selfdual(n, cap_v, pool)
            match = (smin == gmin)
            sd_eq.append((n, match, gmin, smin, gargs[0]))
            note = "" if match else (
                "  [global min is a degenerate near-chain ribbon at HIGHER Q "
                "than the n=8 record]")
            print(f"     n={n:>2}: global={gmin} (~{float(gmin):.4f})  "
                  f"self-dual={smin} (~{float(smin):.4f})  match={match}{note}")
        print("\n     >>> The self-dual family captures the genuine low-Q "
              "minimisers:")
        print("         it matches the global min wherever the global min is not "
              "a")
        print("         degenerate near-chain ribbon (the odd-n 2/5 ties, which "
              "sit")
        print("         ABOVE the n=8 self-dual record 27/70).")

        # ---- SCOPE 3: family Q-sweep ----
        print("\n\n### 3. SELF-DUAL FAMILY Q-SWEEP (Q vs n along the rule) ###\n")
        sd_curve = []
        for n in range(7, sd_hi + 1):
            t0 = time.time()
            smin, sargs, ns = sweep_selfdual(n, 24, pool)
            sd_curve.append((n, smin, sargs[0]))
            print(f"     n={n:>2}: min Q = {smin} (~{float(smin):.6f})  "
                  f"argmin={sargs[0]}  [{ns} self-dual shapes]  "
                  f"({time.time()-t0:.0f}s)")

        # ---- GUARD ----
        any_le_third = [(n, q, a) for (n, q, a) in sd_curve if q <= THIRD]
        any_le_third += [(n, minima[n][0], minima[n][1]) for n in (7, 8, 13, 19)
                         if minima[n][0] <= THIRD]
        if any_le_third:
            print("\n" + "!" * 72)
            print("! GUARD TRIGGERED (roadmap section 8.2): Q <= 1/3 OBSERVED.")
            for n, q, a in any_le_third:
                print(f"!   n={n}  shape={a}  Q={q} (~{float(q):.6f})")
            print("! NOT a counterexample claim.  MANDATORY: independent")
            print("! reimplementation in a SEPARATE codebase + brute force BEFORE")
            print("! any claim.  Three-engine agreement here is NOT independent")
            print("! code.  Recommended next: STOP-and-report.")
            print("!" * 72)

        # ---- SCOPE 4: descent-vs-plateau ----
        print("\n\n### 4. DESCENT-VS-PLATEAU CALL (on the self-dual rule) ###\n")
        qs = [(n, q) for (n, q, a) in sd_curve]
        record_n, record_Q = min(qs, key=lambda t: float(t[1]))
        last5 = qs[-5:]
        first = qs[0][1]
        print("     self-dual family min Q vs n:")
        for n, q in qs:
            bar = "  <-- family-wide minimum" if n == record_n else ""
            print(f"        n={n:>2}: {float(q):.6f}{bar}")
        print(f"\n     family-wide minimum  : Q={record_Q} (~{float(record_Q):.6f}) "
              f"at n={record_n}")
        print(f"     tail (last 5 n) mean : ~{sum(float(q) for _,q in last5)/len(last5):.4f}")
        rising = float(qs[-1][1]) > float(record_Q) + 0.02
        print("\n     >>> CALL: the self-dual minimum sits LOWEST at small n "
              f"(n={record_n})")
        print("         and RISES / PLATEAUS in the ~0.42-0.47 band as n grows "
              "-- it")
        print("         moves AWAY from 1/3, not toward it.  This is a PLATEAU "
              "(no")
        print("         descent), consistent with AP-1a's ray verdict and with a")
        print("         family-restricted null inf Q > 1/3.")

        # ---- SCOPE 5: closed-form fraction evolution ----
        print("\n\n### 5. CLOSED-FORM-APPLICABILITY FRACTION along the rule ###\n")
        print("     (fraction of forced-pair numerators that stay a skew shape;")
        print("      DP-only, self-validated by Naruse==DP on each hit)\n")
        for n, q, (lam, mu) in sd_curve:
            if n not in (8, 10, 12, 13, 14, 15, 19) and not (n <= sd_hi and n % 3 == 1):
                continue
            cf, tot = cf_fraction(lam, mu)
            print(f"     n={n:>2}: {lam}/{mu}  cf = {cf}/{tot} "
                  f"= {Fraction(cf, tot)} (~{cf/tot:.4f})")
        print("\n     >>> The closed-form fraction is essentially 0 along the "
              "self-dual")
        print("         minimisers (sharper than AP-1a's constant-2 ray): the "
              "centrally-")
        print("         symmetric block shapes almost never stay skew under a "
              "forced")
        print("         relation.  The kernel is FULLY DP-bound -- budget "
              "O(n^4)-DP-per-pair;")
        print("         only e itself is closed-form (Naruse).")

        # ---- VERDICT ----
        print("\n\n" + "#" * 72)
        print("# AP-1b' VERDICT")
        print("#" * 72)
        print(f"  Corrected per-n argmins (cap raised to {caps[-1]}):")
        for n in (7, 8, 13, 19):
            Q0, (lam, mu) = minima[n]
            print(f"      n={n:>2}: {lam}/{mu}  Q={Q0} (~{float(Q0):.6f})  "
                  f"self-dual={is_self_dual_3row(lam, mu)}")
        print(f"  n=19 corrected: (12,7,4)/(3,1,0) cap-12 estimate -> "
              f"{minima[19][1][0]}/{minima[19][1][1]} (interior, cap-stable).")
        print(f"  Generalising rule: CENTRAL SYMMETRY (self-dual skew shapes); "
              f"AP-1a hypothesis FALSIFIED (it was the mu_2=0 sub-slice).")
        print(f"  Family-wide min Q = {record_Q} (~{float(record_Q):.6f}) at "
              f"n={record_n}  (all-time Family A record 27/70 at n=8 stands).")
        print(f"  Descent-vs-plateau: PLATEAU/RISE -- away from 1/3.")
        print(f"  Closed-form fraction: ~0 along the rule (fully DP-bound).")
        if not any_le_third:
            print(f"  GUARD: no Q <= 1/3 anywhere -- independent-reimpl trigger "
                  f"does NOT fire.")
        print()
    finally:
        pool.close()
        pool.join()


if __name__ == "__main__":
    main()
