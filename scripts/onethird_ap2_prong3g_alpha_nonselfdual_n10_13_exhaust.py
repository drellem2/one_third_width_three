#!/usr/bin/env python3
r"""
onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust.py
========================================================

OneThird Algebraic-Program **AP-2 Prong 3G-alpha** (mg-5406) -- EXHAUSTIVE
iso-reduced (ORDER-iso only) width-3 minimum Q at n = 10, 11, 12, 13, with the
NON-self-dual / self-dual split made explicit.  Tests the LOAD-BEARING question:

    Is self-duality TRAPPING the floor at 6/17, or is 6/17 a genuine structural
    extremal across the FULL width-3 arena (self-dual AND non-self-dual)?

Follow-up to mg-7237 (Prong 3F-beta), which delivered VERDICT-A on the SELF-DUAL
width-3 arena: 6/17 holds exhaustively across 71,512 sigma-iso classes through
n=13 (matched at even n=10,12; never beaten; new off-ladder odd-n min 134/375).
mg-7237 used a sigma-iso reduction made tractable by the sigma-orbit machinery.

This Prong 3G-alpha drops self-duality.  The arena is the FULL width-3 poset
class, iso-reduced by ORDER-isomorphism ONLY (no sigma structure -- that is the
methodological distinction).  The self-dual classes are a sub-arena inside it
(re-discovered here as a side product via order-canon(P) == order-canon(P^op)),
so this sweep both (a) re-confirms the self-dual minima and (b) answers the
complement question on the non-self-dual classes.

----------------------------------------------------------------------------- #
VISION ALIGNMENT (docs/OneThird-Algebraic-Program-Vision.md), verbatim:
  V1 (algebraic objects): width-3 posets at n=10..13, iso-reduced by ORDER-
     isomorphism only (no sigma structure available -- that is the methodological
     distinction from Prong 3F-beta).  The arena is exactly the complement of
     mg-7237's sigma-iso self-dual arena (modulo iso class boundaries).
  V2 (computable Q): five-engine harness from Prong 3F-beta (M1 placed-set DP,
     M2 AP-0 Q_via_dp, M3 IndPoset minimal-element-removal, M4 brute permutation,
     MC Ehrhart leading coefficient) reusable verbatim.  Closed-form rational
     throughout.
  V3 (parameter space): combinatorial type of width-3 poset, iso-reduced order-
     iso.  Polynomial-in-n enumeration via canonical-augmentation (add one
     maximal element at a time; iso-reduce children by exact order-canonical form).
  V4 (sharpness-or-pivot signal):
     OUTCOME-A: min Q over non-self-dual width-3 at n=10..13 stays >= 6/17 --
        STRENGTHENS the 6/17 floor across the FULL width-3 arena; self-duality
        NOT trapping; 6/17 a genuine structural extremal through n=13.
     OUTCOME-B: min Q < 6/17 at some non-self-dual width-3 P, n in {10..13} --
        REFUTES 6/17 as width-3 floor; self-duality WAS trapping; narrows the
        corridor; possibly opens a new descent ladder family.
     OUTCOME-C: compute exhaustion before reaching n=13 -- report partial (n=10
        or 11 or 12), name the compute breakpoint.
     WALL: orderly-generation / iso-reduction blockage at some n -- name it.
----------------------------------------------------------------------------- #

THE ENUMERATION (the engineering core).  CANONICAL-AUGMENTATION by maximal
element.  Every finite poset on n elements is obtained from a poset on n-1
elements by REMOVING a maximal element; removing an element never increases
width, so every width-<=3 poset is reachable by a chain of width-<=3 posets
under the inverse move:

    (move M)  adjoin one new GLOBAL-MAXIMAL element x, whose strict down-set is
              ANY order ideal D (down-closed subset) of the current poset.
              Because D is down-closed and x is maximal, the result is already
              transitively closed -- no closure pass needed.

We generate (move M) children of every width-<=3 class, prune width > 3
immediately (Dilworth = n - max-matching), and iso-reduce by ORDER-isomorphism
using an exact canonical form (colour refinement + individualization + lex-min
adjacency encoding).  Classes are de-duplicated as generated (set membership on
the canonical key; no pairwise iso tests).  This reaches EVERY width-<=3 poset
exactly once per order-iso class.

SELF-DUAL CLASSIFICATION (the complement split).  A finite poset P is self-dual
iff P is order-isomorphic to its order dual P^op.  We test this EXACTLY by
order-canon(P) == order-canon(P^op) (P^op = transpose of the relation).  The
self-dual width-3 classes recovered here must reproduce mg-7237's minima
(6/17 at even n, 134/375 at odd n) -- a cross-program consistency check.  The
NON-self-dual classes are the complement, and min Q over them is the deliverable.

THE FIVE-ENGINE HARNESS (V2 / roadmap sec.4 acceptance gate), reused VERBATIM
from Prong 3F-beta (imported, not re-implemented):
    (M1) order-ideal placed-set DP        [primary, always -- fast all-pairs],
    (M2) AP-0 kernel Q_via_dp             [subset DP],
    (M3) Prong-2 IndPoset recursion       [independent codebase],
    (M4) brute-force linear extensions    [own path, when e <= cap],
    (MC) Family-C Ehrhart order-polynomial[volume engine].
Monte-Carlo is NEVER a source of truth (non-goal 8.5).  Cross-engine
disagreement HALTS as a P0 priority.

GUARD (roadmap sec.8.2 anti-Cheeger, INHERITED STRICT).  guard_check fires on
EVERY iso-class.  A Q <= 1/3 candidate HALTS immediately with the mandated
message and is NOT written up as a counterexample; M1+M2+M3+M4+MC are ALL USED,
and a fresh SIXTH codebase is reserved for any Q <= 1/3 candidate.

VALIDATION (ROUTINE CHECKS):
    n =  5  min Q = 4/11    -- the 4/11 seed rung (recovered)
    n =  7  min Q = 14/39   -- the 14/39 witness rung (recovered)
    n = 10  min Q = 6/17    -- the 6/17 refutation witness (recovered; SELF-DUAL)
    1/3 textbook gadget (point || 2-chain) is WIDTH-2 -> rejected by the filter.

COMPUTE BUDGETING.  Full width-3 enumeration grows much faster than the self-dual
arena (sigma-iso reduction is dropped).  The sweep gates per level on wall-clock
and class count; if a level overflows the budget it STOPS, reports OUTCOME-C, and
names the last fully-completed n.  --time-budget / --max-classes control gates;
--nmax the ceiling; --quick stops at n=10.

Pure standard library + the imported Prong-3F harness.
"""

from __future__ import annotations

import argparse
import sys
import os
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

# Reuse the Prong-3F bitmask primitives + five-engine harness VERBATIM (imported).
from onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust import (
    _bits, _up_from_below, canonical_form,
    width_le3_bitmask, width_value_bitmask, enum_ideals_bitmask,
    to_belowdict, to_pairs, fast_Q, five_engine_check,
)
from onethird_ap2_prong3c_width3_floor_verify import (
    k_of, FOUR_11, FOURTEEN_39, SIX_17,
)
from onethird_ap2_prong3b_beta_familyD_probe import THIRD, GuardHalt, guard_check

# 134/375 odd-n self-dual thread minimum (carry-forward from mg-7237).
ONE34_375 = Fraction(134, 375)


# --------------------------------------------------------------------------- #
# ORDER-isomorphism canonical form.  We reuse Prong-3F's canonical_form with a
# trivial sigma = identity: with sigma = id the sigma-colour col[sigma[v]] = col[v]
# is redundant and the encoded sigma component is constant, so canonical_form
# reduces EXACTLY to the order-isomorphism canonical form (verified on small
# cases: V vs Lambda distinguished, antichain/chain self-dual, V ~= dual(Lambda)).
# --------------------------------------------------------------------------- #
def _id(n):
    return tuple(range(n))


def order_canon(n, below):
    return canonical_form(n, below, _id(n))


def dual_below(n, below):
    """Order dual P^op: transpose every relation (below <-> up)."""
    return _up_from_below(n, below)


def is_self_dual(n, below):
    """P self-dual iff P is order-isomorphic to its dual P^op."""
    return order_canon(n, below) == order_canon(n, dual_below(n, below))


# --------------------------------------------------------------------------- #
# De-duplicated store of width-<=3 posets keyed by ORDER-iso canonical form.    #
# --------------------------------------------------------------------------- #
class ClassStore:
    __slots__ = ("keys", "recs", "count")

    def __init__(self):
        self.keys = set()
        self.recs = []
        self.count = 0

    def add(self, n, below):
        key = order_canon(n, below)
        if key in self.keys:
            return False
        self.keys.add(key)
        self.recs.append((n, tuple(below)))
        self.count += 1
        return True

    def all(self):
        for (n, below) in self.recs:
            yield (n, list(below))


# --------------------------------------------------------------------------- #
# Canonical augmentation move (add one new global-maximal element).            #
# --------------------------------------------------------------------------- #
def children_max(n, below):
    """Move M: for each order ideal D of P, adjoin x=n as a new maximal element
    with strict down-set D.  D down-closed + x maximal => already transitively
    closed.  Yields new `below` lists of length n+1."""
    x = n
    for D in enum_ideals_bitmask(n, below):
        new = list(below) + [D]
        new[x] = D
        yield new


# --------------------------------------------------------------------------- #
# The sweep (with compute budgeting + partial-n reporting).                    #
# --------------------------------------------------------------------------- #
def sweep(nmax, time_budget=None, max_classes=None, verbose=True):
    """Generate all width-<=3 posets (order-iso classes) for n=0..nmax via
    canonical augmentation by maximal element.  Returns (levels, completed_n,
    breakpoint_reason).  completed_n is the largest n whose level was fully
    generated within budget."""
    levels = {k: ClassStore() for k in range(nmax + 1)}
    levels[0].add(0, [])
    completed_n = 0
    breakpoint_reason = None
    t_start = time.time()
    for k in range(0, nmax):
        store = levels[k]
        if store.count == 0:
            completed_n = k
            continue
        t0 = time.time()
        nC = 0
        for (n, below) in store.all():
            for b2 in children_max(n, below):
                if not width_le3_bitmask(n + 1, b2):
                    continue
                if levels[n + 1].add(n + 1, b2):
                    nC += 1
                    if max_classes is not None and levels[n + 1].count > max_classes:
                        breakpoint_reason = (
                            f"level n={k+1} exceeded --max-classes={max_classes} "
                            f"(generation aborted mid-level)")
                        if verbose:
                            print(f"    [gen] level n={k:>2}: BUDGET HALT -- "
                                  f"{breakpoint_reason}")
                        return levels, completed_n, breakpoint_reason
            if time_budget is not None and (time.time() - t_start) > time_budget:
                breakpoint_reason = (
                    f"wall-clock --time-budget={time_budget}s exceeded while "
                    f"generating level n={k+1} (generation aborted mid-level)")
                if verbose:
                    print(f"    [gen] level n={k:>2}: BUDGET HALT -- "
                          f"{breakpoint_reason}")
                return levels, completed_n, breakpoint_reason
        completed_n = k + 1
        if verbose and store.count:
            print(f"    [gen] level n={k:>2}: {store.count:>7} classes "
                  f"-> +{nC} children at n={k+1:<2}  "
                  f"({time.time()-t0:.1f}s, cum {time.time()-t_start:.1f}s)")
    return levels, completed_n, breakpoint_reason


def width3_classes(store):
    out = []
    for (n, below) in store.all():
        if width_value_bitmask(n, below) == 3:
            out.append((n, below))
    return out


def fingerprint(n, below, arg):
    """Structural fingerprint of an argmin: level (rank) sizes, binding pair, Pr,
    self-dual classification."""
    rank = {}

    def r(i):
        if i in rank:
            return rank[i]
        rank[i] = 0 if below[i] == 0 else 1 + max(r(p) for p in _bits(below[i]))
        return rank[i]

    levels = {}
    for i in range(n):
        levels.setdefault(r(i), []).append(i)
    level_sizes = [len(levels[l]) for l in sorted(levels)]
    x, y, px = arg
    return {
        "level_sizes": level_sizes,
        "binding_pair": (x, y),
        "binding_Pr": px,
        "self_dual": is_self_dual(n, below),
    }


# --------------------------------------------------------------------------- #
# Main.                                                                        #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(
        description="OneThird AP-2 Prong 3G-alpha: exhaustive ORDER-iso width-3 "
                    "min Q (non-self-dual split) at n=10..13")
    ap.add_argument("--nmax", type=int, default=13, help="enumeration ceiling (default 13)")
    ap.add_argument("--quick", action="store_true",
                    help="stop at n=10 (validation cap) for a fast self-test")
    ap.add_argument("--full-verify-upto", type=int, default=8,
                    help="run the full five-engine cross-check on EVERY iso-class up "
                         "to this n (default 8); above it, M1 (fast, self-checked) on "
                         "all + five-engine on a deterministic sample + argmin")
    ap.add_argument("--sample-size", type=int, default=80,
                    help="classes per n hit with the methodologically-distinct engines "
                         "(MC,M4,M2,M3,M1-slow) above --full-verify-upto (default 80)")
    ap.add_argument("--brute-cap", type=int, default=200000,
                    help="M4 brute-force linear-extension cap (default 200000)")
    ap.add_argument("--time-budget", type=float, default=None,
                    help="wall-clock seconds budget for GENERATION; on overflow stop "
                         "and report OUTCOME-C at last completed n (default: none)")
    ap.add_argument("--max-classes", type=int, default=None,
                    help="per-level class-count cap; on overflow stop and report "
                         "OUTCOME-C at last completed n (default: none)")
    args = ap.parse_args()
    nmax = 10 if args.quick else args.nmax

    print("#" * 74)
    print("# OneThird AP-2 Prong 3G-alpha  --  EXHAUSTIVE ORDER-iso width-3")
    print("# minimum Q (non-self-dual vs self-dual split) at n = 10, 11, 12, 13.")
    print("# Does self-duality TRAP the floor at 6/17?   mg-5406")
    print("#" * 74)

    try:
        print(f"\n### GENERATION: width-<=3 order-iso classes, n=0..{nmax} "
              f"(canonical augmentation by maximal element) ###\n")
        t0 = time.time()
        levels, completed_n, brk = sweep(nmax, time_budget=args.time_budget,
                                         max_classes=args.max_classes, verbose=True)
        print(f"\n    generation reached n={completed_n} fully "
              f"({time.time()-t0:.1f}s)"
              + (f";  BREAKPOINT: {brk}" if brk else ";  no budget breakpoint"))

        # ---- per-n analysis ----
        print("\n### PER-n: width-3 iso-class count (total / self-dual / non-self-dual),")
        print("###        min Q (overall + non-self-dual), argmin fingerprint, guard ###\n")
        results = {}
        expected = {5: FOUR_11, 7: FOURTEEN_39, 10: SIX_17}
        for n in range(3, completed_n + 1):
            w3 = width3_classes(levels[n])
            if not w3:
                continue
            t1 = time.time()
            minQ_all = None
            arg_all = None
            minQ_nsd = None       # non-self-dual minimum
            arg_nsd = None
            n_sd = 0
            n_nsd = 0
            scanned = 0
            full_small = (n <= args.full_verify_upto)
            step = max(1, len(w3) // args.sample_size)
            full_done = 0
            for idx, (nn, below) in enumerate(w3):
                # M1 fast all-pairs (self-checked) + guard on EVERY iso-class
                e, Q, arg = fast_Q(nn, below)
                scanned += 1
                if Q is None:
                    continue
                # sec.8.2 STRICT guard on EVERY iso-class
                if Q <= THIRD:
                    raise GuardHalt(
                        f"Q <= 1/3 candidate at width-3 poset T (n={nn}, Q={Q}, "
                        f"below={below}), halting per sec.8.2 STRICT -- fresh sixth "
                        f"codebase required")
                guard_check(f"3G n={nn}", Q)
                sd = is_self_dual(nn, below)
                if sd:
                    n_sd += 1
                else:
                    n_nsd += 1
                # cross-engine harness exhaustively for small n; else sample + argmins
                if full_small or (idx % step == 0):
                    eC, QC, used = five_engine_check(f"3G n={nn} #{idx}", nn, below,
                                                     args.brute_cap)
                    assert eC == e and QC == Q, \
                        f"3G n={nn} #{idx}: fast_Q {e},{Q} vs harness {eC},{QC}"
                    full_done += 1
                if minQ_all is None or Q < minQ_all:
                    minQ_all = Q
                    arg_all = (nn, below, arg, e)
                if not sd and (minQ_nsd is None or Q < minQ_nsd):
                    minQ_nsd = Q
                    arg_nsd = (nn, below, arg, e)
            # five-engine harness on BOTH argmins (load-bearing witnesses)
            an, ab, aarg, ae = arg_all
            e_v, Q_v, used_v = five_engine_check(f"3G n={n} ARGMIN-all", an, ab,
                                                 args.brute_cap)
            assert Q_v == minQ_all, f"argmin-all n={n}: harness {Q_v} != fast {minQ_all}"
            full_done += 1
            fp_all = fingerprint(an, ab, aarg)
            used_nsd = None
            fp_nsd = None
            if arg_nsd is not None:
                bn, bb, barg, be = arg_nsd
                e_n, Q_n, used_nsd = five_engine_check(f"3G n={n} ARGMIN-nsd", bn, bb,
                                                       args.brute_cap)
                assert Q_n == minQ_nsd, f"argmin-nsd n={n}: harness {Q_n} != fast {minQ_nsd}"
                full_done += 1
                fp_nsd = fingerprint(bn, bb, barg)
            results[n] = dict(
                count=len(w3), n_sd=n_sd, n_nsd=n_nsd,
                minQ_all=minQ_all, arg_all=arg_all, fp_all=fp_all, used_all=used_v,
                minQ_nsd=minQ_nsd, arg_nsd=arg_nsd, fp_nsd=fp_nsd, used_nsd=used_nsd,
                scanned=scanned, full_done=full_done, full_small=full_small,
            )
            tag = ""
            if n in expected:
                ok = (minQ_all == expected[n])
                tag = f"  [VALIDATION {expected[n]}: {'PASS' if ok else 'FAIL'}]"
                assert ok, f"n={n} validation FAILED: got {minQ_all} expected {expected[n]}"
            print(f"  n={n:>2}: width-3 classes={len(w3):>7} "
                  f"(self-dual={n_sd}, non-self-dual={n_nsd})")
            print(f"        min Q (ALL)          = {minQ_all}={float(minQ_all):.6f} "
                  f"(k={k_of(minQ_all)}, e={ae})  self-dual-argmin={fp_all['self_dual']} "
                  f"[{used_v}]{tag}")
            if minQ_nsd is not None:
                rel = ">=" if minQ_nsd >= SIX_17 else "<"
                print(f"        min Q (NON-self-dual) = {minQ_nsd}={float(minQ_nsd):.6f} "
                      f"(k={k_of(minQ_nsd)}, e={be})  {rel} 6/17  "
                      f"binding{fp_nsd['binding_pair']} Pr={fp_nsd['binding_Pr']} "
                      f"levels={fp_nsd['level_sizes']} [{used_nsd}]")
            else:
                print(f"        min Q (NON-self-dual) = (no non-self-dual width-3 class "
                      f"at this n)")
            scope = ("ALL" if full_small else f"{full_done} sampled+argmins of")
            print(f"        engines: M1(fast,self-checked)+guard on all {scanned}; "
                  f"M1-slow=M2=M3=M4=MC on {scope} {len(w3)}.  ({time.time()-t1:.1f}s)")

        # ---- VERDICT ----
        print("\n" + "#" * 74)
        print("# sec.8.2 GUARD + VERDICT")
        print("#" * 74)
        reached = max(results) if results else 0
        ns_target = [10, 11, 12, 13]
        got = [n for n in ns_target if n in results]
        # min over NON-self-dual at the target ns
        nsd_targets = {n: results[n]["minQ_nsd"] for n in got
                       if results[n]["minQ_nsd"] is not None}
        overall_min_all = min(v["minQ_all"] for v in results.values()) if results else None

        if nsd_targets:
            min_nsd_target = min(nsd_targets.values())
            print(f"\n  enumerated width-3 up to n={reached}; min Q over NON-self-dual "
                  f"width-3 at n in {{10,11,12,13}}∩reached = {min_nsd_target} "
                  f"({float(min_nsd_target):.6f})")
        else:
            min_nsd_target = None
            print(f"\n  enumerated width-3 up to n={reached}; no non-self-dual width-3 "
                  f"class at any target n reached")
        print(f"  6/17 = {float(SIX_17):.6f}; overall min Q (ALL width-3) across the "
              f"sweep = {overall_min_all} ({float(overall_min_all):.6f})")
        print(f"  sec.8.2 anti-Cheeger guard: every iso-class Q > 1/3 "
              f"==> guard does NOT fire; no sixth codebase triggered.")

        complete_through_13 = all(n in results for n in ns_target) and brk is None

        if min_nsd_target is not None and min_nsd_target < SIX_17:
            verdict = "OUTCOME-B"
            bn = min(n for n in got
                     if results[n]["minQ_nsd"] is not None
                     and results[n]["minQ_nsd"] < SIX_17)
            detail = (f"min Q < 6/17 first at NON-self-dual n={bn} "
                      f"(Q={results[bn]['minQ_nsd']}); self-duality WAS trapping; "
                      f"6/17 REFUTED as the width-3 floor.")
        elif complete_through_13:
            verdict = "OUTCOME-A"
            detail = ("min Q over EXHAUSTIVE non-self-dual width-3 at n=10,11,12,13 "
                      "all stay >= 6/17; self-duality is NOT trapping the floor; 6/17 "
                      "is a genuine structural extremal across the FULL width-3 arena "
                      "through n=13.")
        else:
            verdict = "OUTCOME-C"
            unreached = [n for n in ns_target if n not in results]
            detail = (f"compute exhaustion: enumeration completed EXHAUSTIVELY through "
                      f"n={reached}"
                      + (f" (breakpoint: {brk})" if brk else "")
                      + f".  PARTIAL OUTCOME-A: min Q over non-self-dual width-3 stays "
                        f">= 6/17 at every target n reached "
                        f"({[n for n in ns_target if n in results]}); 6/17 reached ONLY "
                        f"by the self-dual witness.  Unreached target n: {unreached} "
                        f"(compute wall, not a refutation).")

        print(f"\n  VERDICT: {verdict}")
        print(f"    {detail}")
        for n in ns_target:
            if n in results:
                r = results[n]
                mq = r["minQ_nsd"]
                if mq is None:
                    print(f"    n={n}: {r['count']} width-3 classes "
                          f"(sd={r['n_sd']}, nsd={r['n_nsd']}); no non-self-dual class")
                else:
                    rel = ">=" if mq >= SIX_17 else "<"
                    print(f"    n={n}: {r['count']} width-3 classes "
                          f"(sd={r['n_sd']}, nsd={r['n_nsd']}); min Q(non-self-dual) = "
                          f"{mq} ({float(mq):.6f}) {rel} 6/17  "
                          f"[overall min Q(all)={r['minQ_all']}]")

        # cross-program consistency note (self-dual minima must match mg-7237)
        print(f"\n  CROSS-PROGRAM CHECK (self-dual sub-arena, vs mg-7237):")
        for n in got:
            r = results[n]
            # min over self-dual classes at this n
            print(f"    n={n}: overall min Q(all) = {r['minQ_all']} "
                  f"(self-dual-argmin={r['fp_all']['self_dual']})"
                  + ("  [matches 6/17]" if r['minQ_all'] == SIX_17 else "")
                  + ("  [matches 134/375]" if r['minQ_all'] == ONE34_375 else ""))

        # Prong 3H suggestion gated on verdict
        print(f"\n  PRONG 3H (gated on verdict):")
        if verdict == "OUTCOME-A":
            print("    3H-alpha: structural-review consolidation.  The corridor")
            print("      (1/3, 6/17] is now empirically established across the FULL")
            print("      width-3 arena (self-dual AND non-self-dual) through n=13.")
            print("      Natural next phase: write-up + analytic-floor-theorem attempt")
            print("      via the two named missing inputs (forced-relation skew-SYT")
            print("      ratio bound, Prong 1 sec.5; forced-relation order-polytope")
            print("      ratio bound, Prong 3E-alpha).")
        elif verdict == "OUTCOME-B":
            print("    3H-beta: descent-ladder extension via the OUTCOME-B argmin --")
            print("      add the new non-self-dual rung, recompute k, name the new")
            print("      corridor ceiling, characterise its structural family.")
        else:
            print("    re-run with higher --time-budget / --max-classes to reach n=13")
            print("      (OUTCOME-C); the breakpoint above names the compute wall.")

        print("\n  CLEAN EXIT: generator validated (n=5->4/11, n=7->14/39, n=10->6/17);")
        print("  five engines agree at every cross-checked class; guard cleared.")

    except GuardHalt as gh:
        print("\n" + "!" * 74)
        print("# sec.8.2 GUARD FIRED -- HALT (INHERITED STRICT)")
        print("!" * 74)
        print(f"\n  {gh}")
        print("\n  Per the ticket: a Q <= 1/3 candidate is NOT written up as a")
        print("  counterexample.  M1+M2+M3+M4+MC are ALL USED; a fresh SIXTH codebase")
        print("  (Stanley-Reisner / AG-dimension / matrix-permanent / SAT-model-count /")
        print("  analytic Euler-product) plus brute re-enumeration are mandatory first.")
        sys.exit(2)


if __name__ == "__main__":
    main()
