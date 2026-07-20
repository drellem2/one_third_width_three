#!/usr/bin/env python3
"""
mg-0eac follow-up: attack the ONE uncovered region of Counterexample Search C.

The main search (`onethird_mg0eac_primitive_delta_search.py`, and
`docs/OneThird-CounterexampleSearch-C.md`) covers:

    all widths, all posets   n <= 9    exhaustive
    width <= 2               n <= 14   exhaustive
    ladder family L_{n;S}    n <= 19   exhaustive, n <= 27 local search
    all widths, beam         n <= 18   bounded beam

and names exactly one genuine gap in its section 6 / section 7 follow-up 1:

    >>> WIDTH >= 3 AT n >= 12 -- NOT COVERED.  "the only place a
        counterexample could still hide from this search."

This module attacks that region.  It does NOT claim to close it (an exhaustive
width-3 sweep at n >= 12 is out of reach -- see `WIDTH3_GROWTH` below), but it
replaces "not covered at all" with "covered by a bounded, width->=3-constrained
coherence-guided search whose bound is stated".

Two pieces:

  (A) EXHAUSTIVE width-<=W sweep by canonical augmentation with a width prune.
      COMPLETENESS ARGUMENT: `children_max` adds a new MAXIMAL element, and
      width is monotone under deletion of a maximal element (an induced
      subposet of a width-<=W poset has width <= W).  Hence every width-<=W
      poset on n elements is reachable from a width-<=W poset on n-1 elements,
      and the pruned level-by-level enumeration is COMPLETE.
      The prune is CERTIFIED, not assumed: at W = 2 it must reproduce the
      independently-validated `width2_families` counts exactly (sec. 2).

  (B) A WIDTH->=3-CONSTRAINED coherence beam at n >= 12, seeded from (A).
      The width->=3 constraint is the point: an unconstrained beam drifts back
      into the width-2 arena, which is already exhaustively covered to n = 14,
      so it would re-derive known results instead of probing the gap.

Every delta is an exact Fraction; every beta/kappa verdict is exact
rational-vs-algebraic arithmetic (`lt_beta_sah` / `lt_kappa_chen`), reused from
the validated module.  The `delta <= 1/3` guard is inherited STRICT: such a
candidate raises `SubBetaHalt` rather than being written up.

Usage
-----
    python3 scripts/onethird_mg0eac_width3_gap_search.py --quick
    python3 scripts/onethird_mg0eac_width3_gap_search.py \
        --exh-nmax 10 --beam-nmax 16 --beam 400 --keep 30 \
        --json data/onethird-mg0eac-width3-gap.json
"""

import argparse
import json
import os
import sys
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

# --- the validated engine, imported verbatim; NOTHING is re-implemented ----- #
from onethird_mg0eac_primitive_delta_search import (
    THIRD, BETA_THRESHOLD,
    delta_of, verify_five, is_primitive, is_chain, add_edge,
    e_aligned_additions, children_edge, children_lift,
    lt_beta_sah, lt_kappa_chen,
    width2_families, ladder_L,
    SubBetaHalt, _canon,
)
from onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust import (
    width_value_bitmask, enum_ideals_bitmask,
)
from onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust import (
    order_canon, children_max,
)

# Measured on this machine (probe, 2026-07-21).  Width-<=3 iso-class counts:
#   n     2   3   4    5    6     7      8      9       10
#   cls   2   5  15   55  245  1285   7790  53108  397222
# Ratio ~7.5x per level => n=11 ~ 3.0e6, n=12 ~ 2.4e7 classes.  With an
# O(2^n * n) delta on each, n >= 12 exhaustive is out of reach in Python.
# This is WHY piece (B) is a bounded beam and not a sweep.
WIDTH3_GROWTH = {2: 2, 3: 5, 4: 15, 5: 55, 6: 245, 7: 1285, 8: 7790,
                 9: 53108, 10: 397222}


# --------------------------------------------------------------------------- #
# 1. Width-pruned canonical augmentation (piece A).                           #
# --------------------------------------------------------------------------- #
def enumerate_width_le(W, nmax, verbose=True, keep_top=12, time_budget=None,
                       collect_counts=False):
    """Exhaustive enumeration of order-iso classes of posets with width <= W,
    level by level, via canonical augmentation with a width prune.

    COMPLETE for every n <= the returned `covered` (see module docstring for
    the monotone-under-maximal-deletion argument).

    Returns (profile, seeds, covered, counts) where
        profile[n] = dict(classes, primitive, min_delta, argmin_below, width)
        seeds[n]   = the keep_top lowest-delta PRIMITIVE posets, ascending
        covered    = largest n whose level is COMPLETE
        counts[n]  = number of width-<=W iso-classes at n
    """
    t0 = time.time()
    level = {order_canon(1, [0]): [0]}
    profile, seeds, counts = {}, {}, {1: 1}
    covered = 1
    for n in range(2, nmax + 1):
        nxt = {}
        for below in level.values():
            for nb in children_max(n - 1, below):
                if width_value_bitmask(n, nb) > W:
                    continue
                k = order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        level = nxt
        counts[n] = len(level)
        best, nprim = [], 0
        # `exact` tracks the minimum over posets of width EXACTLY W.  This is
        # the number that matters for the gap: the width-<=W minimum is
        # dominated by width-2 posets, whose arena is already exhaustively
        # covered to n = 14 by the main module, so it would just re-derive
        # known results.
        exact, nexact = [], 0
        for below in level.values():
            if not is_primitive(n, below):
                continue
            nprim += 1
            _e, d, _arg = delta_of(n, below)
            if d is None:
                continue
            if width_value_bitmask(n, below) == W:
                nexact += 1
                exact.append((d, tuple(below)))
            # The guard is scoped to n >= 4, matching the write-up's headline.
            # T = ({a,b,c}, a<b) is PRIMITIVE with delta = 1/3 exactly (write-up
            # sec. 0 -- the correction to the ticket's framing), so it is a
            # KNOWN and EXPECTED 1/3-attainer, not a counterexample event.  It
            # is the unique such poset; any delta <= 1/3 at n >= 4 is genuine.
            if n >= 4 and d <= THIRD:
                raise SubBetaHalt(
                    f"delta <= 1/3 candidate in width<={W} sweep at n={n}: "
                    f"delta={d}, below={list(below)} -- halting per roadmap "
                    f"sec.8.2 STRICT; a fresh independent codebase is required "
                    f"before this may be written up.")
            best.append((d, tuple(below)))
        best.sort(key=lambda t: t[0])
        exact.sort(key=lambda t: t[0])
        # seed the gap search from the width-EXACTLY-W posets
        seeds[n] = [(d, list(b)) for (d, b) in exact[:keep_top]]
        profile[n] = {
            "classes": len(level),
            "primitive": nprim,
            "min_delta": best[0][0] if best else None,
            "argmin_below": list(best[0][1]) if best else None,
            "argmin_width": (width_value_bitmask(n, list(best[0][1]))
                             if best else None),
            "primitive_width_exactly_W": nexact,
            "min_delta_width_exactly_W": exact[0][0] if exact else None,
            "argmin_below_width_exactly_W": (list(exact[0][1]) if exact
                                             else None),
        }
        covered = n
        if verbose:
            md = profile[n]["min_delta"]
            mx = profile[n]["min_delta_width_exactly_W"]
            print(f"  [width<={W}] n={n:2d}  classes={len(level):>9,}  "
                  f"prim={nprim:>8,}  min delta = {md} ~ "
                  f"{float(md) if md else float('nan'):.9f}   |  "
                  f"width=={W}: prim={nexact:>8,} min = {mx} ~ "
                  f"{float(mx) if mx else float('nan'):.9f}"
                  f"  ({time.time()-t0:.1f}s)", flush=True)
        if time_budget is not None and time.time() - t0 > time_budget:
            if verbose:
                print(f"  [width<={W}] TIME BUDGET hit after n={n}; "
                      f"levels beyond n={n} NOT covered.", flush=True)
            break
    return profile, seeds, covered, counts


# --------------------------------------------------------------------------- #
# 2. CERTIFICATION of the width prune (mandatory gate).                       #
# --------------------------------------------------------------------------- #
def certify_width_prune(nmax=8, verbose=True):
    """The width prune must not silently drop posets.  Certify it at W = 2
    against `width2_families`, the INDEPENDENT Dilworth-2-chain-lacing
    enumerator that the main module already certified iso-class-by-iso-class
    against the unrestricted all-width enumerator (write-up sec. 3.4c).

    Two independent routes to the same set => the prune is sound.
    """
    if verbose:
        print("=" * 74)
        print("CERTIFY the width prune: pruned canonical augmentation (W=2)")
        print("           vs independent Dilworth-lacing `width2_families`")
        print("=" * 74)
    prof, _seeds, covered, counts = enumerate_width_le(
        2, nmax, verbose=False, keep_top=1)
    ok = True
    for n in range(2, covered + 1):
        indep = set()
        for b in width2_families(n):
            if width_value_bitmask(n, b) <= 2:
                indep.add(order_canon(n, b))
        mine = counts[n]
        match = (len(indep) == mine)
        ok = ok and match
        if verbose:
            print(f"  n={n:2d}  pruned-augmentation={mine:>6,}   "
                  f"width2_families={len(indep):>6,}   "
                  f"{'MATCH' if match else '*** MISMATCH ***'}", flush=True)
    if verbose:
        print(f"  => width prune {'CERTIFIED' if ok else 'FAILED'} "
              f"for n <= {covered}\n", flush=True)
    assert ok, "width prune certification FAILED -- do not trust the sweep"
    return ok


def positive_controls(verbose=True):
    """Re-run the engine controls in THIS process, so this module never trusts
    a delta it did not itself verify through all five engines."""
    if verbose:
        print("=" * 74)
        print("POSITIVE CONTROLS re-run in this module (five-engine agreement)")
        print("=" * 74)
    checks = [
        ("T", 3, [0, 1, 0], Fraction(1, 3)),
        ("A3", 3, [0, 0, 0], Fraction(1, 2)),
        ("A4", 4, [0, 0, 0, 0], Fraction(1, 2)),
        ("L_{9;1,2,3,4}", 9, None, Fraction(6, 17)),
        ("L_{10;1,5}", 10, None, Fraction(37, 106)),
    ]
    allok = True
    for name, n, below, expect in checks:
        if below is None:
            if name == "L_{9;1,2,3,4}":
                below = ladder_L(9, (1, 2, 3, 4))
            else:
                below = ladder_L(10, (1, 5))
        e, d, engines = verify_five(name, n, below)
        good = (d == expect)
        allok = allok and good
        if verbose:
            print(f"  {name:<16} n={n:<3} e={e:<8} delta={d}  [{engines}]  "
                  f"expect {expect}  {'PASS' if good else '*** FAIL ***'}",
                  flush=True)
    assert allok, "positive controls FAILED -- delta engine is not trustworthy"
    if verbose:
        print("  => engine CONTROLS PASS in this module\n", flush=True)
    return allok


# --------------------------------------------------------------------------- #
# 3. Width->=3-constrained coherence beam (piece B).                          #
# --------------------------------------------------------------------------- #
def children_edge_w3(n, below, wmin=3, wmax=None):
    """MOVE A restricted to the gap arena: e-aligned single-comparability
    additions that keep the poset primitive, non-chain, AND of width >= wmin.

    Adding a comparability can only DECREASE width, so the wmin filter is a
    real constraint that stops the beam draining into the width-2 arena
    (already exhaustively covered to n = 14 by the main module)."""
    for nb, mv in children_edge(n, below):
        w = width_value_bitmask(n, nb)
        if w < wmin:
            continue
        if wmax is not None and w > wmax:
            continue
        yield nb, mv


def children_lift_w3(n, below, wmin=3, wmax=None, cap=None):
    """MOVE B restricted to the gap arena."""
    out = []
    for nb in children_lift(n, below, cap=cap):
        w = width_value_bitmask(n + 1, nb)
        if w < wmin:
            continue
        if wmax is not None and w > wmax:
            continue
        out.append(nb)
    return out


def beam_w3_at_n(n, seeds, beam=400, wmin=3, wmax=None, max_depth=None,
                 verbose=False, record=None):
    """Coherence-guided beam over MOVE A at fixed size n, constrained to
    width in [wmin, wmax].  BOUNDED SEARCH -- returns an UPPER BOUND on the
    true minimum delta over the arena, never a proven minimum."""
    t0 = time.time()
    frontier = {}
    for b in seeds:
        if len(b) != n or not is_primitive(n, b) or is_chain(n, b):
            continue
        w = width_value_bitmask(n, b)
        if w < wmin or (wmax is not None and w > wmax):
            continue
        frontier[_canon(n, b)] = list(b)
    if not frontier:
        return None, None, {"evaluated": 0, "depths": 0, "reason": "no seeds"}
    seen = set(frontier.keys())
    best, best_b, evaluated, depth = None, None, 0, 0
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
            for nb, _mv in children_edge_w3(n, b, wmin=wmin, wmax=wmax):
                k = _canon(n, nb)
                if k in seen:
                    continue
                seen.add(k)
                d = delta_of(n, nb)[1]
                evaluated += 1
                if d is None:
                    continue
                if d <= THIRD:
                    raise SubBetaHalt(
                        f"delta <= 1/3 candidate at n={n} width>={wmin}: "
                        f"delta={d}, below={nb} -- halting per roadmap "
                        f"sec.8.2 STRICT.")
                scored.append((d, k, nb))
                if best is None or d < best:
                    best, best_b = d, list(nb)
                    if record is not None and lt_beta_sah(d):
                        record.append(("SUB-BETA", n, str(d), list(nb)))
        if not scored:
            break
        scored.sort(key=lambda t: t[0])
        frontier = {k: nb for (_d, k, nb) in scored[:beam]}
        if verbose:
            print(f"    [w>={wmin} beam n={n}] depth={depth:2d} "
                  f"kept={len(frontier):>4d} best {best} ~ {float(best):.9f} "
                  f"({time.time()-t0:.1f}s)", flush=True)
    return best, best_b, {"evaluated": evaluated, "depths": depth,
                          "beam": beam, "seconds": round(time.time() - t0, 1)}


def _reharvest_w3(n, bb, keep, wmin=3, wmax=None):
    """Diverse near-best posets around `bb` to seed the next size level."""
    out = [(delta_of(n, bb)[1], list(bb))]
    for nb, _mv in children_edge_w3(n, bb, wmin=wmin, wmax=wmax):
        d = delta_of(n, nb)[1]
        if d is not None:
            out.append((d, list(nb)))
    out.sort(key=lambda t: t[0])
    return out[:keep]


def beam_ladder_w3(n_from, n_to, seed_tops, beam=400, keep=30, wmin=3,
                   wmax=None, verbose=True, record=None):
    """Climb the size ladder inside the width->=wmin arena."""
    prof, tops = {}, seed_tops
    for n in range(n_from, n_to + 1):
        seeds = []
        for (_d, b) in tops[:keep]:
            seeds.extend(children_lift_w3(n - 1, list(b), wmin=wmin, wmax=wmax))
        best, bb, st = beam_w3_at_n(n, seeds, beam=beam, wmin=wmin, wmax=wmax,
                                    verbose=False, record=record)
        if best is None:
            if verbose:
                print(f"  [w>={wmin} ladder] n={n:2d}  NO SEEDS -- stopping",
                      flush=True)
            break
        w = width_value_bitmask(n, bb)
        prof[n] = (best, bb, dict(st, seeds=len(seeds), width=w))
        if verbose:
            print(f"  [w>={wmin} ladder] n={n:2d}  seeds={len(seeds):>6,}  "
                  f"eval={st['evaluated']:>8,}  width={w}  min delta = {best} "
                  f"~ {float(best):.9f}  <beta={lt_beta_sah(best)}  "
                  f"<kappa={lt_kappa_chen(best)}  ({st['seconds']}s)",
                  flush=True)
        tops = _reharvest_w3(n, bb, keep, wmin=wmin, wmax=wmax)
    return prof


# --------------------------------------------------------------------------- #
# 4. Driver.                                                                  #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--exh-nmax", type=int, default=10,
                    help="exhaustive width-<=3 sweep up to this n")
    ap.add_argument("--beam-nmax", type=int, default=16,
                    help="width->=3 constrained beam up to this n")
    ap.add_argument("--beam", type=int, default=400)
    ap.add_argument("--keep", type=int, default=30)
    ap.add_argument("--wmin", type=int, default=3)
    ap.add_argument("--wmax", type=int, default=None)
    ap.add_argument("--certify-nmax", type=int, default=8)
    ap.add_argument("--exh-time-budget", type=float, default=None)
    ap.add_argument("--json", type=str, default=None)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    if args.quick:
        args.exh_nmax, args.beam_nmax, args.certify_nmax = 8, 12, 7
        args.beam, args.keep = 150, 15

    t0 = time.time()
    out = {"work_item": "mg-0eac",
           "purpose": "attack the width>=3, n>=12 gap named in "
                      "docs/OneThird-CounterexampleSearch-C.md sec.6/sec.7",
           "width3_class_counts_measured": WIDTH3_GROWTH}

    # --- gate 1: the engine -------------------------------------------------
    positive_controls(verbose=True)
    # --- gate 2: the width prune -------------------------------------------
    certify_width_prune(nmax=args.certify_nmax, verbose=True)

    # --- piece A: exhaustive width-<=3 -------------------------------------
    print("=" * 74)
    print(f"EXHAUSTIVE width-<=3 PRIMITIVE min-delta, n <= {args.exh_nmax}")
    print("  (n <= 11 lies INSIDE Peczarski's exhaustively verified range --")
    print("   reported as a positive control + certified seed harvest, NOT")
    print("   as a new result.)")
    print("=" * 74)
    prof3, seeds3, covered3, counts3 = enumerate_width_le(
        3, args.exh_nmax, verbose=True, keep_top=max(args.keep, 12),
        time_budget=args.exh_time_budget)
    out["exhaustive_width_le_3"] = {
        str(n): {"classes": p["classes"], "primitive": p["primitive"],
                 "min_delta": str(p["min_delta"]),
                 "min_delta_float": float(p["min_delta"]) if p["min_delta"] else None,
                 "argmin_width": p["argmin_width"],
                 "argmin_below": p["argmin_below"],
                 "lt_beta": lt_beta_sah(p["min_delta"]) if p["min_delta"] else None,
                 "primitive_width_exactly_3": p["primitive_width_exactly_W"],
                 "min_delta_width_exactly_3": str(p["min_delta_width_exactly_W"]),
                 "min_delta_width_exactly_3_float":
                     (float(p["min_delta_width_exactly_W"])
                      if p["min_delta_width_exactly_W"] else None),
                 "argmin_below_width_exactly_3":
                     p["argmin_below_width_exactly_W"],
                 "lt_beta_width_exactly_3":
                     (lt_beta_sah(p["min_delta_width_exactly_W"])
                      if p["min_delta_width_exactly_W"] else None),
                 "lt_14_39_width_exactly_3":
                     (p["min_delta_width_exactly_W"] < Fraction(14, 39)
                      if p["min_delta_width_exactly_W"] else None),
                 "coverage": "exhaustive-width-le-3"}
        for n, p in prof3.items()}
    out["exhaustive_width_le_3_covered_nmax"] = covered3

    # the seeds that actually have width >= 3 (the gap arena)
    gap_seeds = []
    for n in sorted(seeds3):
        if n != covered3:
            continue
        for (d, b) in seeds3[n]:
            if width_value_bitmask(n, b) >= args.wmin:
                gap_seeds.append((d, b))
    print(f"\n  seed harvest at n={covered3}: {len(gap_seeds)} primitive "
          f"posets of width >= {args.wmin}", flush=True)

    # --- piece B: width->=3 constrained beam into the gap -------------------
    print("\n" + "=" * 74)
    print(f"WIDTH->={args.wmin} CONSTRAINED COHERENCE BEAM, "
          f"n = {covered3+1} .. {args.beam_nmax}  (beam={args.beam})")
    print("  *** BOUNDED SEARCH -- upper bound only, NOT a proven minimum. ***")
    print("  This is the region the main search reports as NOT COVERED.")
    print("=" * 74)
    record = []
    profB = beam_ladder_w3(covered3 + 1, args.beam_nmax, gap_seeds,
                           beam=args.beam, keep=args.keep, wmin=args.wmin,
                           wmax=args.wmax, verbose=True, record=record)
    out["width_ge_3_beam"] = {
        str(n): {"min_delta": str(d), "min_delta_float": float(d),
                 "width": st["width"], "argmin_below": bb,
                 "lt_beta": lt_beta_sah(d), "lt_kappa": lt_kappa_chen(d),
                 "stats": st, "coverage": f"bounded-beam-width-ge-{args.wmin}"}
        for n, (d, bb, st) in profB.items()}
    out["sub_beta_records"] = record

    # --- verdict ------------------------------------------------------------
    print("\n" + "=" * 74)
    print("VERDICT (width >= 3 arena)")
    print("=" * 74)
    cands = []
    for n, p in prof3.items():
        if p["min_delta_width_exactly_W"] is not None:
            cands.append((p["min_delta_width_exactly_W"], n,
                          "exhaustive-width-exactly-3"))
    for n, (d, _bb, _st) in profB.items():
        cands.append((d, n, f"bounded-beam-width-ge-{args.wmin}"))
    if cands:
        cands.sort(key=lambda t: t[0])
        bd, bn, bcov = cands[0]
        print(f"  Lowest delta over PRIMITIVE width>={args.wmin} posets found: "
              f"{bd} ~ {float(bd):.10f}  at n={bn}  [{bcov}]")
        print(f"  < beta_Sah  (exact test): {lt_beta_sah(bd)}")
        print(f"  < kappa_Chen(exact test): {lt_kappa_chen(bd)}")
        print(f"  < 14/39 ~ 0.3589743590 (Olson-Sagan: smallest delta known")
        print(f"    at width > 2, their computer search covered n <= 9)"
              f": {bd < Fraction(14, 39)}")
        out["best_width_ge_3"] = {"delta": str(bd), "delta_float": float(bd),
                                  "n": bn, "coverage": bcov,
                                  "lt_beta": lt_beta_sah(bd),
                                  "lt_kappa": lt_kappa_chen(bd),
                                  "lt_14_39_olson_sagan":
                                      bd < Fraction(14, 39)}
        if not lt_beta_sah(bd):
            print("  ==> Nothing below beta in the width>=3 arena either,\n"
                  "      within the stated bound.  The gap named in sec.6 of\n"
                  "      the write-up is NARROWED, not closed: the beam is\n"
                  "      bounded and no width>=3 sweep at n>=12 is claimed.")
    out["seconds"] = round(time.time() - t0, 1)

    if args.json:
        os.makedirs(os.path.dirname(args.json) or ".", exist_ok=True)
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
        print(f"\n  wrote {args.json}  ({out['seconds']}s total)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
