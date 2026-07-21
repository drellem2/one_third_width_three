#!/usr/bin/env python3
"""
mg-c47a SCOPING probe: how big is the width-4 arena?

This is a CLASS-COUNTING calibration, NOT a search.  It computes NO delta, has
no minimiser, no beam, no seeds -- it only counts order-iso classes of posets
of width <= W, level by level, so that Q2 of the scoping ticket ("is a width-4
search even tractable?") can be answered with measured numbers and a measured
growth rate instead of adjectives.  Nothing here can find or miss a
counterexample, because nothing here evaluates balance.

It reuses the SAME width-pruned canonical augmentation that mg-0eac certified
and aud0eac independently re-certified (`enumerate_width_le` in
`onethird_mg0eac_width3_gap_search.py`), with the delta evaluation stripped
out.  Reusing it is also the point: `enumerate_width_le` is already
parameterised in `W`, and its completeness argument -- width is monotone under
deletion of a maximal element, and every finite poset has a maximal element --
mentions no particular value of `W`.  Running it at W = 4 and recovering the
known W = 2 and W = 3 counts is the empirical half of the answer to "does the
prune extend to width 4 as-is?".

Self-check: at W = 2 and W = 3 the counts printed here must reproduce the
values already in the repo (W=2: 2,4,10,26,75,225,711 for n=2..8; W=3:
2,5,15,55,245,1285,7790,53108,397222 for n=2..10).  Any mismatch invalidates
the calibration.

Usage
-----
    python3 scripts/onethird_mgc47a_width4_arena_count.py --nmax 9 --budget 600

`--budget` is a wall-clock budget PER WIDTH, enforced inside a level (see
`count_width_le`).  Until mg-8ff1 it was tested only after a level completed,
which bounded nothing: levels grow ~10x, so the reading `--nmax 11
--budget 600` did not stop at 600s, it ran for about an hour and then reported
that the budget had been exceeded.  Measured on this machine at W = 4: n = 8
completes ~3s cumulative, n = 9 ~34s, n = 10 ~5min, n = 11 ~50min.  So a full
`--nmax 11` run over widths 2,3,4 is roughly an hour, NOT the "~10 min" once
claimed; budget accordingly, or cap `--nmax` at 9 for a fast calibration.
"""

import argparse
import json
import os
import sys
import time

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust import (
    width_value_bitmask,
)
from onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust import (
    order_canon, children_max,
)
from onethird_mg0eac_primitive_delta_search import is_primitive

# Reference counts already in the repo, for the self-check.
KNOWN = {
    2: {2: 2, 3: 4, 4: 10, 5: 26, 6: 75, 7: 225, 8: 711},
    3: {2: 2, 3: 5, 4: 15, 5: 55, 6: 245, 7: 1285, 8: 7790, 9: 53108,
        10: 397222},
}

# How often to consult the wall clock inside a level, in parents processed.
# Overshoot past --budget is bounded by the time to process this many parents;
# at the level sizes this probe reaches that is well under a second, and the
# `--budget` control in the doc measures it.  Large enough that time.time()
# is not itself a cost.
_BUDGET_CHECK_EVERY = 512


def count_width_le(W, nmax, time_budget=None, verbose=True):
    """Count order-iso classes of posets of width <= W, level by level.

    Same width-pruned canonical augmentation as the certified sweep; the delta
    evaluation, the primitivity filter and the sub-beta guard are all absent
    because nothing here looks at balance.

    `time_budget` is enforced *inside* a level, not only at level boundaries.
    That distinction is the whole point: levels grow ~10x here, so by n = 11 a
    single level runs for tens of minutes, and a budget consulted only between
    levels bounds nothing (it was checked only between levels until mg-8ff1,
    which is why `--nmax 11 --budget 600` ran for about an hour).

    A level aborted mid-way is NOT reported.  Every returned per-level dict
    covers exactly the levels that ran to completion, so a partial level can
    never be misread as a complete count; `covered` is the last complete level
    and `aborted_at` names the level that was abandoned, if any.
    """
    t0 = time.time()
    deadline = None if time_budget is None else t0 + time_budget

    def expired():
        return deadline is not None and time.time() > deadline

    level = {order_canon(1, [0]): [0]}
    counts = {1: 1}
    exact_counts, prim_counts, prim_exact_counts = {}, {}, {}
    times = {}
    covered = 1
    aborted_at = None
    budget_hit = False
    for n in range(2, nmax + 1):
        nxt = {}
        aborted = False
        for i, below in enumerate(level.values()):
            if i % _BUDGET_CHECK_EVERY == 0 and expired():
                aborted = True
                break
            for nb in children_max(n - 1, below):
                if width_value_bitmask(n, nb) > W:
                    continue
                k = order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        if aborted:
            aborted_at = n
            break
        level = nxt
        n_classes = len(level)
        # The ticket asks for width-EXACTLY-W and PRIMITIVE counts, so split
        # the level.  Still no delta: `is_primitive` is connectivity of the
        # incomparability graph, and `width_value_bitmask` is the certified
        # oracle -- neither looks at linear extensions.
        nexact = nprim = nprim_exact = 0
        for i, below in enumerate(level.values()):
            if i % _BUDGET_CHECK_EVERY == 0 and expired():
                aborted = True
                break
            w_exact = (width_value_bitmask(n, below) == W)
            prim = is_primitive(n, below)
            nexact += w_exact
            nprim += prim
            nprim_exact += (w_exact and prim)
        if aborted:
            # The augmentation for level n finished, so `n_classes` is sound --
            # but the split is not.  Drop the whole level rather than report a
            # complete count beside partial ones: every dict below then covers
            # the same set of levels, which is the property that makes a
            # truncated run safe to read.
            aborted_at = n
            break
        counts[n] = n_classes
        exact_counts[n] = nexact
        prim_counts[n] = nprim
        prim_exact_counts[n] = nprim_exact
        times[n] = time.time() - t0
        covered = n
        if verbose:
            ratio = (counts[n] / counts[n - 1]) if counts.get(n - 1) else 0.0
            flag = ""
            if n in KNOWN.get(W, {}):
                flag = ("  [self-check OK]" if KNOWN[W][n] == counts[n]
                        else f"  [SELF-CHECK FAIL, expected {KNOWN[W][n]}]")
            print(f"  [width<={W}] n={n:2d}  classes={counts[n]:>12,}  "
                  f"ratio={ratio:6.3f}  |  width=={W}: {nexact:>12,}  "
                  f"primitive: {nprim:>12,}  primitive&width=={W}: "
                  f"{nprim_exact:>12,}  ({times[n]:8.1f}s){flag}", flush=True)
        if expired():
            # Clean stop: level n completed, level n+1 never begun.
            budget_hit = True
            if verbose:
                print(f"  [width<={W}] TIME BUDGET hit after n={n}; "
                      f"levels beyond n={n} NOT counted.", flush=True)
            break
    if aborted_at is not None:
        budget_hit = True
        if verbose:
            print(f"  [width<={W}] TIME BUDGET hit DURING n={aborted_at} "
                  f"after {time.time()-t0:.1f}s; n={aborted_at} abandoned and "
                  f"NOT counted (last complete level: n={covered}).",
                  flush=True)
    return {"counts": counts, "width_exactly_W": exact_counts,
            "primitive": prim_counts, "primitive_width_exactly_W":
            prim_exact_counts, "seconds": times, "covered": covered,
            "aborted_at": aborted_at, "budget_exhausted": budget_hit,
            "wall_seconds": time.time() - t0}


def certify_prune_unpruned(W, nmax=8, time_budget=None, verbose=True):
    """Certify the width-`W` prune against an UNPRUNED enumeration.

    mg-0eac's `certify_width_prune` checks the prune at W = 2 only, against
    `width2_families` -- a width-2-specific Dilworth-lacing enumerator with no
    width-4 counterpart.  So at W = 4 that gate has no analogue.  This supplies
    one, by the route aud0eac used for width <= 3 (audit sec.3): enumerate ALL
    order-iso classes with no width prune at all, filter by width afterwards,
    and require the counts to match the pruned enumeration exactly.

    A pruned enumerator that silently dropped a width-<=W poset would show up
    here as a shortfall.  Cheap: 19,448 classes at n = 8.

    Cheap at the default n = 8, but this enumeration has NO width prune, so it
    grows faster than the pruned one and is the more dangerous of the two to
    leave unbounded.  It honours `time_budget` on the same terms as
    `count_width_le`: checked inside a level, and an abandoned level is
    dropped rather than reported short.
    """
    t0 = time.time()
    deadline = None if time_budget is None else t0 + time_budget

    def expired():
        return deadline is not None and time.time() > deadline

    level = {order_canon(1, [0]): [0]}
    unpruned = {1: 1}
    for n in range(2, nmax + 1):
        nxt = {}
        aborted = False
        for i, below in enumerate(level.values()):
            if i % _BUDGET_CHECK_EVERY == 0 and expired():
                aborted = True
                break
            for nb in children_max(n - 1, below):
                k = order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        if aborted:
            if verbose:
                print(f"  [unpruned] TIME BUDGET hit DURING n={n} after "
                      f"{time.time()-t0:.1f}s; n={n} abandoned and NOT "
                      f"certified.", flush=True)
            break
        level = nxt
        unpruned[n] = sum(1 for b in level.values()
                          if width_value_bitmask(n, b) <= W)
        if verbose:
            print(f"  [unpruned] n={n:2d}  all classes={len(level):>8,}  "
                  f"of which width<={W}: {unpruned[n]:>8,}  "
                  f"({time.time()-t0:6.1f}s)", flush=True)
        if expired():
            if verbose:
                print(f"  [unpruned] TIME BUDGET hit after n={n}; levels "
                      f"beyond n={n} NOT certified.", flush=True)
            break
    return unpruned


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=11)
    ap.add_argument("--budget", type=float, default=600.0,
                    help="wall-clock budget per width, seconds; enforced "
                         "DURING a level, not only between levels. A level "
                         "abandoned mid-way is dropped, not reported short.")
    ap.add_argument("--widths", type=int, nargs="+", default=[2, 3, 4])
    ap.add_argument("--json", default=None)
    ap.add_argument("--certify-nmax", type=int, default=0,
                    help="if >0, certify the prune against an UNPRUNED "
                         "enumeration up to this n (8 is cheap)")
    args = ap.parse_args()

    out = {}
    certs = {}
    if args.certify_nmax:
        for W in args.widths:
            print(f"\n=== certifying the width-<={W} prune against an "
                  f"UNPRUNED enumeration, n <= {args.certify_nmax} ===",
                  flush=True)
            certs[W] = certify_prune_unpruned(W, args.certify_nmax,
                                              time_budget=args.budget)
    for W in args.widths:
        print(f"\n=== counting width <= {W} (no delta computed) ===",
              flush=True)
        res = count_width_le(W, args.nmax, time_budget=args.budget)
        counts = res["counts"]
        mismatches = [n for n, c in counts.items()
                      if n in KNOWN.get(W, {}) and KNOWN[W][n] != c]
        res["self_check_mismatches"] = mismatches
        if W in certs:
            disagree = {n: (certs[W][n], counts[n])
                        for n in certs[W] if n in counts
                        and certs[W][n] != counts[n]}
            res["prune_certification_unpruned"] = certs[W]
            res["prune_certification_disagreements"] = disagree
            print(f"  PRUNE CERTIFICATION vs unpruned enumeration: "
                  f"{'CERTIFIED (0 disagreements)' if not disagree else disagree}",
                  flush=True)
        out[W] = res
        print(f"  self-check mismatches vs repo reference: {mismatches or 0}",
              flush=True)
        if res["budget_exhausted"]:
            print(f"  BUDGET EXHAUSTED after {res['wall_seconds']:.1f}s "
                  f"(--budget {args.budget:g}s): complete levels n <= "
                  f"{res['covered']}"
                  + (f"; n = {res['aborted_at']} abandoned mid-level"
                     if res["aborted_at"] else "")
                  + ". Counts above are NOT the full arena.", flush=True)

    print("\n=== summary: width-<=W iso-class counts ===")
    ns = sorted({n for W in out for n in out[W]["counts"]})
    hdr = "  n  " + "".join(f"{('W<=' + str(W)):>14}" for W in args.widths)
    print(hdr)
    for n in ns:
        row = f" {n:2d}  "
        for W in args.widths:
            c = out[W]["counts"].get(n)
            row += f"{(f'{c:,}' if c is not None else '-'):>14}"
        print(row)

    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"widths": {str(k): v for k, v in out.items()}},
                      fh, indent=1)
        print(f"\nwrote {args.json}")


if __name__ == "__main__":
    main()
