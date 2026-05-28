#!/usr/bin/env python3
r"""
onethird_ap1a_familyA_smallk_snapshot.py
========================================

OneThird Algebraic-Program **AP-1a** (mg-746f) -- Family A (hook-length /
skew-shape) sweep at k = 1, 2, 3 along the data-earned ray: the first
descent-vs-plateau snapshot.

Reference / lineage:
  * docs/OneThird-AP-0-FamilyA-Viability-Probe.md   (AP-0 verdict, mg-98a6)
  * docs/OneThird-AP-1a-FamilyA-SmallK-Snapshot.md   (this ticket's report)
  * docs/OneThird-Algebraic-Program-Roadmap.md       (sections 5, 6, 8)
  * docs/OneThird-Algebraic-Program-Vision.md        (vision-parts 3 + 4)

THE RAY (AP-0 carry-forward, mayor's verified relay).
  AP-0 found that the small-Q minimisers of width-3 3-row skew shapes are NOT
  thin near-chain ribbons (empirically falsified) but **stacked near-equal-row**
  shapes.  The (4,3,3)/(3,0,0) shape was an n=7 sweep argmin (Q = 2/5).  The
  carried-forward "main ray" generalises it as

        lambda = (3k+1, 3k, 3k),   mu = (3k, 0, 0),   n = |lambda/mu| = 6k+1.

  Geometrically: a single top cell (row 1, column 3k+1) stacked above two full
  rows of length 3k (rows 2 and 3, columns 1..3k).  The three requested shapes:
        k=1: (4,3,3)/(3,0,0)    n=7
        k=2: (7,6,6)/(6,0,0)    n=13
        k=3: (10,9,9)/(9,0,0)   n=19

WHAT THIS COMPUTES (scope = bounded snapshot, AP-1a SCOPE 1-4).
  1. Q(k) on the ray at k = 1, 2, 3 under the two-method gate
       (M1 brute-force == M2 order-ideal DP), e cross-checked by M3 Naruse.
     Brute-force is feasible at all three k here (e <= 92378), so the FULL gate
     runs at every k by default (use --quick to skip the k=3 brute force, which
     is the ~70 s step, falling back to DP+Naruse for k=3).
  2. Stability check: a bounded sweep over ALL width-3 3-row skew shapes at each
     n in {7, 13, 19} (translation-normalised mu_3=0, all rows non-empty,
     lambda_1 <= LAM1_MAX), reporting whether the ray shape is the sweep argmin
     and whether any nearby shape has a strictly lower Q.  (The expensive
     n=13 / n=19 sweeps are skipped under --quick.)
  3. Closed-form-applicability fraction at each k (mayor W1 watch-item): the
     fraction of forced-pair numerators that stay a genuine skew shape (Naruse
     closed-form) instead of falling through to the width-3 DP.
  4. First descent-vs-plateau snapshot verdict: is the small-k Q(k) sequence
     monotone-decreasing toward 1/3, plateauing, or non-monotone?  Three points
     cannot prove asymptotics -- we only name the shape of the small-k sequence.

GUARD (roadmap section 8.2, anti-Cheeger).  IF Q(k) <= 1/3 at any k, that is NOT
  a counterexample claim from AP-1a: it triggers MANDATORY INDEPENDENT
  REIMPLEMENTATION in a separate codebase plus brute force before any claim.
  AP-0/AP-1a three-engine agreement is NOT independent code.  This script prints
  a loud STOP banner in that case and recommends STOP-and-report.

NON-GOALS (roadmap section 8): no Cheeger re-litigation; no counterexample claim
  without independent reimpl; no Lean / LaTeX / main.tex; width-3 only;
  Monte-Carlo is never the source of truth.

OUT OF SCOPE (deferred to AP-1b on AP-1a GREEN): k > 3, adjacent rays, the
  asymptotic fit and the lim_{k->inf} Q estimate.

Pure-Python / standard library only; reuses the AP-0 engine verbatim.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from fractions import Fraction

# Reuse the AP-0 engine verbatim (functions Q_via_dp, naruse_count,
# try_realise_as_skew_shape, sweep_min_Q, probe_shape, ...).
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from onethird_ap0_familyA_skew_probe import (  # noqa: E402
    skew_cells,
    build_poset,
    poset_width,
    count_linear_extensions_dp,
    naruse_count,
    Q_via_dp,
    probe_shape,
    sweep_min_Q,
)

THIRD = Fraction(1, 3)

# Bound on lambda_1 for the stability sweep.  AP-0 verified the sweep minimum is
# stable for lambda_1 in {9, 12, 15} at n in {7,8,9}; we keep 12 as the default
# and report honestly when an argmin sits at the cap boundary (which signals a
# larger cap might find a still-lower Q -- an AP-1b item, not AP-1a's claim).
LAM1_MAX = 12

# The data-earned ray.
def ray_shape(k):
    """(lambda, mu) for the AP-0 carry-forward ray at parameter k >= 1."""
    return (3 * k + 1, 3 * k, 3 * k), (3 * k, 0, 0)


# --------------------------------------------------------------------------- #
# 1. Q(k) on the ray under the two-method gate                                #
# --------------------------------------------------------------------------- #
def snapshot_on_ray(ks=(1, 2, 3), do_brute_k3=True, verbose=True):
    """Return [(k, ShapeResult-or-dpdict)] for the ray at each k.

    For k where brute force is feasible (and not suppressed) we run probe_shape,
    which enforces the FULL M1==M2 gate and the M3 e cross-check inline (it
    asserts on any disagreement, so a clean return IS the gate passing).  For a
    suppressed k we fall back to the validated DP path with an M3 e cross-check.
    """
    rows = []
    for k in ks:
        lam, mu = ray_shape(k)
        cells = skew_cells(lam, mu)
        less, incomp = build_poset(cells)
        n = len(cells)
        suppress = (k == 3) and not do_brute_k3
        t0 = time.time()
        if not suppress:
            r = probe_shape(lam, mu, f"AP-1a ray k={k}", verbose=False)
            gate = "M1==M2 (brute==DP), e==Naruse"
            e, Q = r.e, r.Q
            cf_app, cf_tot, cf_frac = r.cf_applicable, r.cf_total, r.cf_fraction
            width = r.width
            pair_rows = r.pair_rows
        else:
            # DP + Naruse only (brute suppressed).  Still independent of each
            # other: order-ideal DP vs excited-diagram Naruse.
            e_dp = count_linear_extensions_dp(cells, less)
            e_nar = naruse_count(lam, mu)
            assert e_dp == e_nar, f"k={k}: DP e={e_dp} != Naruse e={e_nar}"
            e, Q = Q_via_dp(cells, less, incomp)
            width = poset_width(less)
            gate = "DP==Naruse (e); Q by validated DP (brute suppressed)"
            cf_app = cf_tot = None
            cf_frac = None
            pair_rows = None
        dt = time.time() - t0
        worst = None
        if pair_rows is not None:
            worst = [(p["x"], p["y"]) for p in pair_rows if p["minp"] == Q]
        rows.append(
            dict(k=k, lam=lam, mu=mu, n=n, e=e, width=width, Q=Q,
                 Qf=float(Q), dist=float(Q - THIRD), cf_app=cf_app,
                 cf_tot=cf_tot, cf_frac=cf_frac, gate=gate, worst=worst,
                 time=dt)
        )
        if verbose:
            print(f"  k={k}  shape={lam}/{mu}  n={n}")
            print(f"      e = {e}   width = {width}   [{gate}]")
            print(f"      Q = {Q}  (~{float(Q):.6f})   "
                  f"dist to 1/3 = {float(Q - THIRD):+.6f}")
            if cf_frac is not None:
                print(f"      closed-form-applicability = {cf_app}/{cf_tot} "
                      f"= {cf_frac} (~{float(cf_frac):.4f})")
            if worst is not None:
                wstr = ", ".join(f"{x}~{y}" for x, y in worst[:4])
                print(f"      worst (argmax-min) pair(s): {wstr}"
                      f"{' ...' if len(worst) > 4 else ''}")
            print(f"      [gate passed; {dt:.1f}s]")
            print()
    return rows


# --------------------------------------------------------------------------- #
# 2. Stability check: bounded sweep at each n                                  #
# --------------------------------------------------------------------------- #
def stability_check(ray_rows, verbose=True):
    """For each ray k, sweep all width-3 3-row skew shapes at the same n and
    compare the global sweep min against the ray Q.  Reports whether the ray is
    the sweep argmin and whether a strictly-lower-Q shape exists nearby."""
    results = []
    for row in ray_rows:
        k, n, rayQ = row["k"], row["n"], row["Q"]
        t0 = time.time()
        minQ, argmin, scanned, w3 = sweep_min_Q(n, lam1_max=LAM1_MAX)
        dt = time.time() - t0
        ray_lm = (row["lam"], row["mu"])
        ray_is_argmin = ray_lm in argmin
        lower_exists = minQ < rayQ
        # boundary flag: if any argmin sits at lambda_1 == LAM1_MAX the true
        # sweep min may be lower under a larger cap (AP-1b item).
        at_cap = any(lam[0] == LAM1_MAX for lam, mu in argmin)
        results.append(
            dict(k=k, n=n, rayQ=rayQ, minQ=minQ, scanned=scanned, w3=w3,
                 nargmin=len(argmin), argmin=argmin[:6],
                 ray_is_argmin=ray_is_argmin, lower_exists=lower_exists,
                 at_cap=at_cap, time=dt)
        )
        if verbose:
            print(f"  k={k} (n={n}): swept {w3} width-3 shapes "
                  f"(lambda_1 <= {LAM1_MAX})")
            print(f"      ray Q       = {rayQ} (~{float(rayQ):.6f})")
            print(f"      sweep min Q = {minQ} (~{float(minQ):.6f})  "
                  f"({len(argmin)} argmin shape(s))")
            ex = ", ".join(f"{lam}/{mu}" for lam, mu in argmin[:4])
            print(f"      argmin: {ex}{' ...' if len(argmin) > 4 else ''}")
            if ray_is_argmin:
                print(f"      >>> ray IS a sweep argmin at this n.")
            else:
                print(f"      >>> ray is NOT the sweep argmin: a lower-Q shape "
                      f"exists ({minQ} < {rayQ}).")
            if at_cap:
                print(f"      [NOTE: an argmin sits at lambda_1 = {LAM1_MAX} "
                      f"(the cap) -- a larger cap may find a lower Q; AP-1b.]")
            print(f"      [{dt:.1f}s]")
            print()
    return results


# --------------------------------------------------------------------------- #
# 4. Descent-vs-plateau snapshot verdict                                       #
# --------------------------------------------------------------------------- #
def descent_verdict(ray_rows):
    Qs = [r["Q"] for r in ray_rows]
    Qf = [float(q) for q in Qs]
    # name the shape of the small-k sequence (3 points -> qualitative only)
    deltas = [Qf[i + 1] - Qf[i] for i in range(len(Qf) - 1)]
    decreasing = all(d < 0 for d in deltas)
    increasing = all(d > 0 for d in deltas)
    # "plateau": last step nearly flat (|delta| < 0.01)
    flat_tail = abs(deltas[-1]) < 0.01 if deltas else False
    if decreasing:
        shape = "MONOTONE-DECREASING (toward 1/3)"
    elif increasing and flat_tail:
        shape = "RISES then PLATEAUS (non-monotone; away from 1/3)"
    elif increasing:
        shape = "MONOTONE-INCREASING (away from 1/3)"
    elif flat_tail:
        shape = "NON-MONOTONE with a flat tail (plateau)"
    else:
        shape = "NON-MONOTONE"
    return shape, deltas, Qs


# --------------------------------------------------------------------------- #
# Main                                                                         #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true",
                    help="skip the k=3 brute force and the n=13/n=19 stability "
                         "sweeps (fast smoke run; DP+Naruse still gate e/Q)")
    args = ap.parse_args()

    print("#" * 72)
    print("# OneThird AP-1a  --  Family A small-k snapshot (k = 1, 2, 3)")
    print("# mg-746f   ray (3k+1,3k,3k)/(3k,0,0)   roadmap sections 5, 6, 8")
    print("#" * 72)

    print("\n### 1. Q(k) ON THE RAY (two-method gate: brute == DP; e == Naruse) ###\n")
    ray_rows = snapshot_on_ray(do_brute_k3=not args.quick)

    # ---- GUARD: any Q <= 1/3 ? ----
    any_le_third = [r for r in ray_rows if r["Q"] <= THIRD]
    if any_le_third:
        print("\n" + "!" * 72)
        print("! GUARD TRIGGERED (roadmap section 8.2): Q <= 1/3 OBSERVED on the ray.")
        for r in any_le_third:
            print(f"!   k={r['k']}  shape={r['lam']}/{r['mu']}  Q={r['Q']} "
                  f"(~{float(r['Q']):.6f})")
        print("! This is NOT a counterexample claim from AP-1a.  MANDATORY:")
        print("!   independent reimplementation in a SEPARATE codebase + brute")
        print("!   force BEFORE any claim.  Three-engine agreement here is NOT")
        print("!   independent code.  Recommended next: STOP-and-report.")
        print("!" * 72)

    if not args.quick:
        print("\n### 2. STABILITY CHECK (bounded sweep at each n; no hidden lower-Q?) ###\n")
        stab = stability_check(ray_rows)
    else:
        print("\n### 2. STABILITY CHECK -- SKIPPED (--quick) ###\n")
        stab = None

    print("\n### 3. CLOSED-FORM-APPLICABILITY FRACTION per k ###\n")
    for r in ray_rows:
        if r["cf_frac"] is not None:
            print(f"  k={r['k']}: {r['cf_app']}/{r['cf_tot']} "
                  f"= {r['cf_frac']} (~{float(r['cf_frac']):.4f})")
        else:
            print(f"  k={r['k']}: (brute suppressed under --quick; re-run "
                  f"without --quick for the closed-form fraction)")

    print("\n### 4. DESCENT-VS-PLATEAU SNAPSHOT VERDICT ###\n")
    shape, deltas, Qs = descent_verdict(ray_rows)
    print("  Q(k) on the ray:")
    for r in ray_rows:
        print(f"      Q({r['k']}) = {r['Q']:>12}  (~{float(r['Q']):.6f})  "
              f"dist to 1/3 = {float(r['Q'] - THIRD):+.6f}")
    print(f"  step deltas (float): "
          f"{', '.join(f'{d:+.6f}' for d in deltas)}")
    print(f"  small-k sequence shape: {shape}")
    print("  (three data points cannot prove asymptotics -- shape only.)")

    print("\n" + "#" * 72)
    print("# AP-1a SUMMARY")
    print("#" * 72)
    print(f"  Q(1) = {Qs[0]} (~{float(Qs[0]):.6f})")
    print(f"  Q(2) = {Qs[1]} (~{float(Qs[1]):.6f})")
    print(f"  Q(3) = {Qs[2]} (~{float(Qs[2]):.6f})")
    print(f"  min Q on ray = {min(Qs)} (~{float(min(Qs)):.6f})  "
          f"(all > 1/3: {min(Qs) > THIRD})")
    if stab is not None:
        any_lower = any(s["lower_exists"] for s in stab)
        print(f"  ray is the sweep argmin at every k: "
              f"{all(s['ray_is_argmin'] for s in stab)}")
        print(f"  a strictly-lower-Q width-3 shape exists at some n: {any_lower}")
        for s in stab:
            print(f"      n={s['n']}: sweep min {s['minQ']} "
                  f"(~{float(s['minQ']):.6f}) vs ray {s['rayQ']} "
                  f"(~{float(s['rayQ']):.6f})"
                  f"{'  [argmin at lambda_1 cap]' if s['at_cap'] else ''}")
    print(f"  descent-vs-plateau: {shape}")
    if not any_le_third:
        print("  GUARD: no Q <= 1/3 anywhere -- no independent-reimpl trigger.")
    print()


if __name__ == "__main__":
    main()
