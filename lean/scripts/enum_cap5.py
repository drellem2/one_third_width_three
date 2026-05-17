#!/usr/bin/env python3
"""
enum_cap5.py — Case3Witness cap-5 enumeration (mg-4d7b).

Enumerates the full cap-5 scope of `Step8.Case3Witness.{u}`:

  ∀ β width-≤-3 non-chain finite poset, ∀ LB : LayeredDecomposition β,
  caps 1–5 ⇒ HasBalancedPair β.

Under cap 1 (`Function.Injective LB.band`) + cap 4 (nonempty bands), the
band map is a bijection α ↔ {1..K}, so K = |β| and band sizes are all 1.
Cap 2 (K ≤ 2w+2) + cap 5 (w ≤ 4) bound K ≤ 10.  So the cap-5 scope is

  K ∈ {2, …, 10}, w ∈ {max(0, ⌈(K-2)/2⌉), …, 4} with K ≤ 2w+2,
  bands singletons.

For each tuple (K, w) in scope, enumerate every transitively-closed
predecessor mask on K elements with:

  * forced edges:  i < j  whenever  j − i > w  (cap (L2-forced));
  * free edges:    i < j  for some subset of pairs with j − i ≤ w.

Filter to closure-canonical masks (those that are fixed under Warshall
closure); for each surviving poset on K elements, verify HasBalancedPair
via the existing symmetric-pair fast path + linear-extension DP fallback.

Output: JSON certificate per (K, w) with `checked`, `balanced`,
optional counterexample.  If any configuration lacks a balanced pair,
the script reports the counterexample and exits non-zero.

This is the *enumeration substrate* for the Lean-side Case3Witness
proof:  Case3Witness is a Prop over β, but its antecedent (the LB
witness) forces |β| ≤ 10, so the universal reduces to a finite
case-by-case verification.

The existing `enum_case3.py` only covers K = 3 (with cap-1 dropped,
so band sizes vary in {1, 2, 3}).  This script covers the full cap-5
range with cap-1 enforced (bands singletons).

References
----------
* `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9): the
  architecture analysis that named cap 5.
* `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0): the Lean
  signature-restatement that added cap 5.
* mg-4d7b ticket body: enumeration scope + Daniel's "TOP PRIORITY"
  directive (2026-05-17T20:55Z).
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction


# ---------------------------------------------------------------------------
# Bitmask primitives (mirroring `Case3Enum.lean` for byte-for-byte parity).
# ---------------------------------------------------------------------------


def warshall(pred: list[int], n: int) -> list[int]:
    """Warshall transitive closure of `pred`."""
    out = pred.copy()
    for k in range(n):
        bit_k = 1 << k
        pk = out[k]
        for v in range(n):
            if out[v] & bit_k:
                out[v] |= pk
    return out


def successor_masks(pred: list[int], n: int) -> list[int]:
    succ = [0] * n
    for v in range(n):
        m = pred[v]
        while m:
            lsb = m & -m
            u = lsb.bit_length() - 1
            m ^= lsb
            succ[u] |= 1 << v
    return succ


def antichain_width(pred: list[int], n: int) -> int:
    """
    Width of the poset (= maximum antichain size).
    For n ≤ 10 we compute by brute force over 2^n subsets, filtering
    to antichains.  Used only for the width-≤3 acceptance filter.
    """
    succ = successor_masks(pred, n)
    # comp[v] bits = u, where u is comparable to v (u ≠ v).
    comp = [pred[v] | succ[v] for v in range(n)]
    best = 0
    # Iterate over subsets; skip early if subset already > best.
    for S in range(1, 1 << n):
        # Check antichain: for every v in S, no comparable u in S \ {v}.
        ok = True
        rem = S
        while rem:
            lsb = rem & -rem
            v = lsb.bit_length() - 1
            rem ^= lsb
            if comp[v] & (S ^ (1 << v)):
                ok = False
                break
        if ok:
            c = bin(S).count("1")
            if c > best:
                best = c
                if best == 4:  # > 3 — already too wide, can short-circuit
                    return best
    return best


def is_chain(pred: list[int], n: int) -> bool:
    """Check whether the poset is a (total) chain."""
    succ = successor_masks(pred, n)
    for x in range(n):
        for y in range(x + 1, n):
            comp_xy = (pred[y] & (1 << x)) or (pred[x] & (1 << y)) \
                      or (succ[y] & (1 << x)) or (succ[x] & (1 << y))
            if not comp_xy:
                return False
    return True


def irreducible(pred: list[int], K: int) -> bool:
    """
    Layer-ordinal-sum irreducible (singletons case): for every cut
    k ∈ {1..K-1}, some element in {k+1..K} is incomparable to some
    element in {1..k}.
    """
    for k in range(1, K):
        lower_mask = (1 << k) - 1
        found_incomp = False
        for v in range(k, K):
            if (pred[v] & lower_mask) != lower_mask:
                found_incomp = True
                break
        if not found_incomp:
            return False
    return True


def has_adjacent_incomp(pred: list[int], K: int) -> bool:
    """
    Singletons case: exists s ∈ {0..K-2}, element s+1 not greater than s
    (here band s = {s} for 0-indexed elements).
    """
    for s in range(K - 1):
        if not (pred[s + 1] & (1 << s)):
            return True
    return False


# ---------------------------------------------------------------------------
# Balanced-pair check (fast symmetric path + linear-extension DP fallback).
# ---------------------------------------------------------------------------


def find_symmetric_pair(pred: list[int], n: int) -> tuple[int, int] | None:
    succ = successor_masks(pred, n)
    full = (1 << n) - 1
    for x in range(n):
        for y in range(x + 1, n):
            if pred[y] & (1 << x):
                continue
            if pred[x] & (1 << y):
                continue
            cMask = full ^ ((1 << x) | (1 << y))
            if (pred[x] & cMask) != (pred[y] & cMask):
                continue
            if (succ[x] & cMask) != (succ[y] & cMask):
                continue
            return (x, y)
    return None


def count_linear_extensions(pred: list[int], n: int) -> int:
    """Subset DP."""
    full = (1 << n) - 1
    memo: dict[int, int] = {}

    def rec(placed: int) -> int:
        if placed == full:
            return 1
        c = memo.get(placed)
        if c is not None:
            return c
        total = 0
        remaining = full ^ placed
        m = remaining
        while m:
            lsb = m & -m
            e = lsb.bit_length() - 1
            m ^= lsb
            if (pred[e] & placed) == pred[e]:
                total += rec(placed | lsb)
        memo[placed] = total
        return total

    return rec(0)


def find_balanced_pair(pred: list[int], n: int) -> tuple[int, int, Fraction] | None:
    sym = find_symmetric_pair(pred, n)
    if sym is not None:
        return (sym[0], sym[1], Fraction(1, 2))
    total = count_linear_extensions(pred, n)
    if total == 0:
        return None
    for x in range(n):
        for y in range(x + 1, n):
            if pred[y] & (1 << x):
                continue
            if pred[x] & (1 << y):
                continue
            pred2 = pred.copy()
            pred2[y] |= 1 << x
            pred2 = warshall(pred2, n)
            cnt = count_linear_extensions(pred2, n)
            p = Fraction(cnt, total)
            if Fraction(1, 3) <= p <= Fraction(2, 3):
                return (x, y, p)
    return None


# ---------------------------------------------------------------------------
# Enumeration core (mask-based, mirror of Case3Enum.enumPosetsFor).
# ---------------------------------------------------------------------------


def enum_singleton_posets(K: int, w: int, *, require_width3: bool = True,
                          require_non_chain: bool = True,
                          require_irreducible: bool = False,
                          require_adjacent_incomp: bool = False,
                          require_closure_canonical: bool = True,
                          ) -> tuple[int, int, int, list]:
    """
    Enumerate posets on K elements with bands singletons and (L2-forced) at
    interaction width w.  Returns
        (total_masks_tried, accepted, balanced, counterexamples)
    where `accepted` counts configurations passing all `require_*` filters
    and `counterexamples` is a list of {mask, pred, ...} dicts for accepted
    configs missing a balanced pair (empty list expected for cap-5 scope).
    """
    # Free pairs: (i, j) with j > i, j - i ≤ w.  Forced pairs: j - i > w.
    free_pairs = []
    forced_pairs = []
    for i in range(K):
        for j in range(i + 1, K):
            if j - i > w:
                forced_pairs.append((i, j))
            else:
                free_pairs.append((i, j))
    nfree = len(free_pairs)
    base_pred = [0] * K
    for u, v in forced_pairs:
        base_pred[v] |= 1 << u

    total = 1 << nfree
    accepted = 0
    balanced = 0
    counters: list = []
    # Closure check is the only place where we may discard non-canonical masks
    # (canonical = closure adds no new free-edge); for the rest we do the
    # filters in order.
    for mask in range(total):
        pred = base_pred.copy()
        for k in range(nfree):
            if mask & (1 << k):
                u, v = free_pairs[k]
                pred[v] |= 1 << u
        pred = warshall(pred, K)
        if require_closure_canonical:
            skip = False
            for k, (u, v) in enumerate(free_pairs):
                cb = 1 if (pred[v] & (1 << u)) else 0
                mb = 1 if (mask & (1 << k)) else 0
                if cb != mb:
                    skip = True
                    break
            if skip:
                continue
        if require_irreducible and not irreducible(pred, K):
            continue
        if require_adjacent_incomp and not has_adjacent_incomp(pred, K):
            continue
        if require_non_chain and is_chain(pred, K):
            continue
        if require_width3 and antichain_width(pred, K) > 3:
            continue
        accepted += 1
        wit = find_balanced_pair(pred, K)
        if wit is not None:
            balanced += 1
        else:
            counters.append({
                "mask": mask,
                "pred": list(pred),
            })
            # Don't bail — collect all for forensic review.
    return total, accepted, balanced, counters


# ---------------------------------------------------------------------------
# Cap-5 scope iteration.
# ---------------------------------------------------------------------------


def cap5_scope():
    """
    Yield (K, w) tuples in the cap-5 scope:
        K ∈ {2..10}, w ∈ {0..4} with K ≤ 2w + 2.
    Sorted in nondecreasing order of `nfree = #{(i,j) : j > i, j - i ≤ w}`
    for predictable progress reporting.
    """
    out = []
    for K in range(2, 11):
        for w in range(0, 5):
            if K > 2 * w + 2:
                continue
            # nfree at (K, w): each i has min(w, K-1-i) free successors
            nfree = sum(min(w, K - 1 - i) for i in range(K))
            out.append((nfree, K, w))
    out.sort()
    return [(K, w) for _nfree, K, w in out]


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--K-min", type=int, default=2,
                   help="Minimum K to enumerate (default 2)")
    p.add_argument("--K-max", type=int, default=10,
                   help="Maximum K to enumerate (default 10)")
    p.add_argument("--w-max", type=int, default=4,
                   help="Maximum w to enumerate (default 4)")
    p.add_argument("--require-irreducible", action="store_true",
                   help="Only count irreducible posets (matches Case3 residual scope)")
    p.add_argument("--require-adjacent-incomp", action="store_true",
                   help="Only count posets with an adjacent incomparable cross-pair")
    p.add_argument("--output", type=str,
                   default="enum_cap5_certificate.json",
                   help="Output certificate JSON path")
    p.add_argument("--skip-K10", action="store_true",
                   help="Skip K=10 (the 2^30 mask cell) for fast runs")
    p.add_argument("--verbose", action="store_true")
    args = p.parse_args(argv)

    cert: dict = {
        "description": "mg-4d7b — Case3Witness cap-5 enumeration certificate",
        "script": "enum_cap5.py",
        "scope": (
            "All (β, LB) where β is a width-≤3 non-chain finite poset and "
            "LB : LayeredDecomposition β satisfies caps 1–5 of "
            "Step8.Case3Witness.{u}.  Cap 1+4 ⇒ band singletons; "
            "cap 2+5 ⇒ K = |β| ≤ 10."
        ),
        "filters": {
            "require_width3": True,
            "require_non_chain": True,
            "require_irreducible": args.require_irreducible,
            "require_adjacent_incomp": args.require_adjacent_incomp,
            "require_closure_canonical": True,
        },
        "per_cell": [],
        "status": "unknown",
    }
    overall_ok = True
    start = time.time()
    for (K, w) in cap5_scope():
        if K < args.K_min or K > args.K_max or w > args.w_max:
            continue
        if args.skip_K10 and K == 10:
            cert["per_cell"].append({
                "K": K, "w": w, "skipped": True, "reason": "--skip-K10",
            })
            continue
        nfree = sum(min(w, K - 1 - i) for i in range(K))
        t0 = time.time()
        try:
            tot, acc, bal, counters = enum_singleton_posets(
                K, w,
                require_width3=True,
                require_non_chain=True,
                require_irreducible=args.require_irreducible,
                require_adjacent_incomp=args.require_adjacent_incomp,
                require_closure_canonical=True,
            )
        except KeyboardInterrupt:
            print(f"  Interrupted at K={K} w={w}", flush=True)
            raise
        elapsed = time.time() - t0
        entry = {
            "K": K, "w": w, "nfree": nfree,
            "masks_tried": tot,
            "accepted": acc,
            "balanced": bal,
            "elapsed_s": round(elapsed, 2),
        }
        if counters:
            entry["counterexamples"] = counters
            overall_ok = False
        cert["per_cell"].append(entry)
        if args.verbose:
            cflag = " *COUNTER*" if counters else ""
            print(
                f"  K={K:2d} w={w}  nfree={nfree:2d}  "
                f"masks={tot:>11d}  accepted={acc:>8d}  balanced={bal:>8d}  "
                f"{elapsed:7.2f}s{cflag}",
                flush=True,
            )
    cert["status"] = "pass" if overall_ok else "fail"
    cert["elapsed_s"] = round(time.time() - start, 2)
    with open(args.output, "w") as f:
        json.dump(cert, f, indent=2, default=str)
    print(f"\nCertificate written to {args.output}")
    print(f"Overall status: {cert['status']}")
    return 0 if overall_ok else 1


if __name__ == "__main__":
    sys.exit(main())
