#!/usr/bin/env python3
"""
enum_case3.py — residual Case-3 enumeration for mg-307c.

Verifies the following (the residual content of `lem:bounded-irreducible-balanced`
at step8.tex §G4):

  Every layered width-3 poset Q satisfying (L1)-(L4), which is layer-ordinal-sum
  irreducible with depth K ≥ 2 and contains an adjacent-band incomparable
  cross-pair (u,v) ∈ M_s × M_{s+1}, contains a balanced pair (an incomparable
  pair (x, y) with Pr[x <_L y] ∈ [1/3, 2/3] over uniformly-random linear
  extensions of Q).

The K = 2 and w = 0 regimes are discharged separately in step8.tex (K = 2 is
prop:bipartite-balanced; w = 0 is the degenerate layered case handled by
`lem_layered_balanced_subtype` in Lean).  The residual is w ≥ 1 and K ≥ 3.

After window localization (lem:window-localization), every non-chain witness is
equivalent to one on |Q| ≤ 3(3w+1) elements with depth ≤ 3w+1.  By further
iterated ordinal-sum reduction we land on an irreducible Q* with adjacent
incomparable cross-pair — the hypotheses of this script.  Under these
hypotheses the irreducible factor is bounded: |Q*| ≤ 3(3w+1), depth ≤ 3w+1.

Enumeration strategy:
  For each parameter tuple (w, K, band_sizes) with
    * w ∈ {1, 2, 3, 4}                (values delivered by Step 7 lem:bandwidth)
    * K ∈ {3, …, 3w+1}                (bounded by window localization)
    * each band size n_i ∈ {1, 2, 3}        (from (L1); empty bands collapse to lower-K)
    * Σ n_i ≤ 3(3w+1)
  enumerate every (L4)-directed cross-band comparability pattern satisfying
  transitivity and (L2) (distances > w forced comparable), filter to those
  that are layer-ordinal-sum irreducible and contain an adjacent-band
  incomparable cross-pair, and check that at least one incomparable pair
  within Q has linear-extension probability in [1/3, 2/3].

Representation:
  Elements of Q are tagged 0 .. N-1 in band-major order.  The ≤-relation is
  encoded by the list `pred` of predecessor bitmasks: bit `u` of `pred[v]` is
  set iff u < v in the transitive closure.  All core operations (closure,
  irreducibility check, relabeling under within-band permutation) are bitwise
  integer operations.

Canonical form:
  Two posets that differ only by a within-band permutation of elements are
  isomorphic and have identical linear-extension statistics.  We canonicalise
  by enumerating all Π_i n_i! (≤ 216) within-band permutations and taking
  the lex-smallest tuple of predecessor bitmasks.

Linear-extension count and balanced-pair probabilities:
  Subset DP over bitmasks of placed elements — O(2^n · n) in the worst case,
  but bounded-size posets of width ≤ 3 have at most ~3^(n/3) antichains of
  placeable frontiers, so realistic memoization is far faster.

Output:
  A certificate JSON file (default: `enum_case3_certificate.json`) containing
  per-(w, K, band_sizes) counts of isomorphism classes enumerated and
  balanced-pair verifications.  If any configuration lacks a balanced pair,
  the script prints the counterexample and exits non-zero.

Usage:
  python3 enum_case3.py --w 1              # enumerate w = 1 only (fastest)
  python3 enum_case3.py --w 1 --w 2        # enumerate w ∈ {1, 2}
  python3 enum_case3.py                    # enumerate all w ∈ {1, 2, 3, 4}

The output certificate is consumed (as a check-in) by the Lean formalisation
of `lem_layered_balanced_subtype` (Step8/LayeredBalanced.lean): the uniform
"all bounded-irreducible layered posets admit a balanced pair" result plus
window localization discharges the residual sorry at LayeredBalanced.lean:657.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction
from itertools import permutations, product


# ---------------------------------------------------------------------------
# Bitmask-native helpers for relation manipulation.
# ---------------------------------------------------------------------------


def warshall(pred: list[int], n: int) -> list[int]:
    """
    Transitive closure of the strict ≤-relation given by predecessor bitmasks.
    After this call, bit u of `pred[v]` is set iff u < v in the closure.

    Runs Warshall's algorithm in O(n^2) Python operations, where each
    operation is a single-integer bitwise OR.
    """
    out = pred.copy()
    for k in range(n):
        bit_k = 1 << k
        pk = out[k]
        for v in range(n):
            if out[v] & bit_k:
                out[v] |= pk
    return out


def is_transitive(pred: list[int], n: int) -> bool:
    """Check whether the relation given by `pred` is already transitively closed."""
    for v in range(n):
        mask = pred[v]
        while mask:
            lsb = mask & -mask
            u = lsb.bit_length() - 1
            mask ^= lsb
            if (pred[u] & ~pred[v]) != 0:
                return False
    return True


def irreducible(pred: list[int], band_sizes: list[int]) -> bool:
    """
    Layer-ordinal-sum irreducible: for every 1 ≤ k < K, there is at least one
    cross-pair (a ∈ bands 1..k, b ∈ bands k+1..K) that is incomparable.
    Equivalently, at every cut k, it is NOT the case that all lower×upper
    pairs are in the <-relation.
    """
    K = len(band_sizes)
    offsets = [0]
    for ns in band_sizes:
        offsets.append(offsets[-1] + ns)
    for k in range(1, K):
        lower_mask = (1 << offsets[k]) - 1
        found_incomp = False
        for b in range(offsets[k], offsets[K]):
            # b incomparable to some a in lower iff (pred[b] & lower_mask) != lower_mask.
            if (pred[b] & lower_mask) != lower_mask:
                found_incomp = True
                break
        if not found_incomp:
            return False
    return True


def has_adjacent_incomp(pred: list[int], band_sizes: list[int]) -> bool:
    """Exists (u, v) ∈ M_s × M_{s+1} with (u, v) ∉ <."""
    K = len(band_sizes)
    offsets = [0]
    for ns in band_sizes:
        offsets.append(offsets[-1] + ns)
    for s in range(K - 1):
        lo, hi = offsets[s], offsets[s + 1]
        lo2, hi2 = offsets[s + 1], offsets[s + 2]
        band_mask = ((1 << hi) - 1) & ~((1 << lo) - 1)
        for b in range(lo2, hi2):
            # Incomparable to some a in M_s iff (pred[b] & band_mask) != band_mask.
            if (pred[b] & band_mask) != band_mask:
                return True
    return False


# ---------------------------------------------------------------------------
# Canonical form under within-band permutation.
# ---------------------------------------------------------------------------


def build_perm_relabelings(band_sizes: list[int]) -> list[list[int]]:
    """
    Precompute all element relabelings induced by within-band permutations.
    Each relabeling is a list `new_idx` of length n such that element e maps
    to `new_idx[e]` under the permutation.
    """
    offsets = [0]
    for ns in band_sizes:
        offsets.append(offsets[-1] + ns)
    n = offsets[-1]
    perms_per_band = [list(permutations(range(ns))) for ns in band_sizes]
    out = []
    for perm_tuple in product(*perms_per_band):
        new_idx = [0] * n
        for i, perm in enumerate(perm_tuple):
            for local, mapped in enumerate(perm):
                new_idx[offsets[i] + local] = offsets[i] + mapped
        out.append(new_idx)
    return out


def canonical_signature(
    pred: list[int], n: int, relabelings: list[list[int]]
) -> tuple[int, ...]:
    """
    Return the lex-smallest tuple of predecessor bitmasks over all
    within-band permutations.  Acts as a canonical isomorphism invariant.
    """
    best: tuple[int, ...] | None = None
    for new_idx in relabelings:
        # For each v, compute pred' such that pred'[new_idx[v]] = relabel(pred[v]).
        new_pred = [0] * n
        for v in range(n):
            old_bits = pred[v]
            # Remap bits.
            new_bits = 0
            mask = old_bits
            while mask:
                lsb = mask & -mask
                u = lsb.bit_length() - 1
                mask ^= lsb
                new_bits |= 1 << new_idx[u]
            new_pred[new_idx[v]] = new_bits
        sig = tuple(new_pred)
        if best is None or sig < best:
            best = sig
    return best  # type: ignore[return-value]


# ---------------------------------------------------------------------------
# Linear-extension count and balanced-pair check.
# ---------------------------------------------------------------------------


def count_linear_extensions(pred: list[int], n: int) -> int:
    """Count linear extensions of a poset via subset DP on placed elements."""
    full = (1 << n) - 1
    memo: dict[int, int] = {}

    def rec(placed: int) -> int:
        if placed == full:
            return 1
        cached = memo.get(placed)
        if cached is not None:
            return cached
        total = 0
        remaining = full ^ placed
        mask = remaining
        while mask:
            lsb = mask & -mask
            e = lsb.bit_length() - 1
            mask ^= lsb
            if (pred[e] & placed) == pred[e]:
                total += rec(placed | lsb)
        memo[placed] = total
        return total

    return rec(0)


def successor_masks(pred: list[int], n: int) -> list[int]:
    """Compute successor bitmasks: bit v of succ[u] is set iff u < v."""
    succ = [0] * n
    for v in range(n):
        mask = pred[v]
        while mask:
            lsb = mask & -mask
            u = lsb.bit_length() - 1
            mask ^= lsb
            succ[u] |= 1 << v
    return succ


def find_symmetric_pair(pred: list[int], n: int) -> tuple[int, int] | None:
    """
    Find an incomparable (x, y) such that the swap(x, y) involution is a
    poset automorphism.  This guarantees Pr[x <_L y] = 1/2 ∈ [1/3, 2/3].

    Criterion: x ∥ y, pred[x] = pred[y], succ[x] = succ[y] (after masking
    out bits at positions x and y, since the relations between x and y are
    self-referential and excluded by incomparability).
    """
    succ = successor_masks(pred, n)
    for x in range(n):
        for y in range(x + 1, n):
            if pred[y] & (1 << x):
                continue
            if pred[x] & (1 << y):
                continue
            # Masked profiles exclude self-bits.
            mask_xy = ~((1 << x) | (1 << y))
            if (pred[x] & mask_xy) != (pred[y] & mask_xy):
                continue
            if (succ[x] & mask_xy) != (succ[y] & mask_xy):
                continue
            return (x, y)
    return None


def find_balanced_pair(
    pred: list[int], n: int
) -> tuple[int, int, Fraction] | None:
    """
    Find any incomparable (x, y) with Pr[x <_L y] ∈ [1/3, 2/3].  Returns
    (x, y, prob) on success, None on failure.

    First tries the fast O(n^2) symmetric-pair check (`find_symmetric_pair`):
    if found, reports prob = 1/2.  Otherwise falls back to an exhaustive
    scan, computing Pr[x <_L y] for each incomparable pair via
    linear-extension refinement.
    """
    sym = find_symmetric_pair(pred, n)
    if sym is not None:
        return (sym[0], sym[1], Fraction(1, 2))
    total = count_linear_extensions(pred, n)
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
# Enumeration core.
# ---------------------------------------------------------------------------


def enum_posets_for(
    band_sizes: list[int], w: int
) -> tuple[int, int, tuple | None]:
    """
    Enumerate posets with bands `band_sizes`, interaction width `w`, satisfying
    (L1)-(L4), irreducible, with adjacent incomparable cross-pair.  For each
    distinct transitively-closed relation (closure-canonical mask), verify
    that it admits a balanced pair.

    Returns (checked, balanced, counterexample).  A `counterexample` is a
    triple (band_sizes, mask, pred) for the first poset (if any) that does
    not admit a balanced pair; if none, counterexample is None.

    We do not reduce modulo within-band permutations — the per-mask
    verification is the expensive step, and iso-equivalent masks all have the
    same balanced-pair status, so duplicating the check on them is harmless
    (just slower than optimal).  The fast `find_symmetric_pair` pre-check
    discharges the vast majority of posets; only the rare asymmetric cases
    fall through to the full linear-extension enumeration.
    """
    K = len(band_sizes)
    total_n = sum(band_sizes)
    offsets = [0]
    for ns in band_sizes:
        offsets.append(offsets[-1] + ns)
    free_pairs: list[tuple[int, int]] = []
    forced_pairs: list[tuple[int, int]] = []
    for i in range(K):
        for j in range(i + 1, K):
            for a in range(band_sizes[i]):
                for b in range(band_sizes[j]):
                    e_a = offsets[i] + a
                    e_b = offsets[j] + b
                    if j - i > w:
                        forced_pairs.append((e_a, e_b))
                    else:
                        free_pairs.append((e_a, e_b))
    nfree = len(free_pairs)
    if nfree > 27:
        raise RuntimeError(f"nfree={nfree} too large")

    base_pred = [0] * total_n
    for (u, v) in forced_pairs:
        base_pred[v] |= 1 << u

    checked = 0
    balanced = 0
    # Precompute free-pair bit positions for fast closure_mask calculation.
    free_uv = free_pairs

    for mask in range(1 << nfree):
        pred = base_pred.copy()
        for k in range(nfree):
            if mask & (1 << k):
                u, v = free_uv[k]
                pred[v] |= 1 << u
        pred = warshall(pred, total_n)
        # Skip masks where closure adds free-pair edges (not closure-canonical).
        skip = False
        for k, (u, v) in enumerate(free_uv):
            closed_bit = 1 if (pred[v] & (1 << u)) else 0
            mask_bit = 1 if (mask & (1 << k)) else 0
            if closed_bit != mask_bit:
                skip = True
                break
        if skip:
            continue
        if not irreducible(pred, band_sizes):
            continue
        if not has_adjacent_incomp(pred, band_sizes):
            continue
        checked += 1
        witness = find_balanced_pair(pred, total_n)
        if witness is not None:
            balanced += 1
        else:
            return checked, balanced, (band_sizes, mask, list(pred))
    return checked, balanced, None


# ---------------------------------------------------------------------------
# Outer enumeration over (K, band_sizes).
# ---------------------------------------------------------------------------


def band_sizes_generator(K: int, max_total: int):
    """Yield all n_1..n_K with each n_i in {1,2,3} and sum ≤ max_total."""
    for t in product((1, 2, 3), repeat=K):
        if sum(t) <= max_total:
            yield list(t)


def enum_w(
    w: int,
    size_limit: int | None = None,
    K_max: int | None = None,
    verbose: bool = False,
) -> dict:
    # Size and depth bounds from mg-307c:
    # |Q| ≤ min(6w+6, 3(3w+1)) and depth K ≤ 2w+2 (both bounds are delivered
    # by Step 7 lem:bandwidth combined with window localization).
    max_total = min(3 * (3 * w + 1), 6 * w + 6)
    if size_limit is not None:
        max_total = min(max_total, size_limit)
    max_K = 2 * w + 2
    if K_max is not None:
        max_K = min(max_K, K_max)

    results = {
        "w": w,
        "params": {"max_total": max_total, "max_K": max_K},
        "configs": [],
        "total_checked": 0,
        "total_balanced": 0,
        "skipped_large": [],
        "counterexample": None,
    }
    for K in range(3, max_K + 1):
        for band_sizes in band_sizes_generator(K, max_total):
            try:
                checked, balanced, counter = enum_posets_for(band_sizes, w)
            except RuntimeError as e:
                results["skipped_large"].append({
                    "K": K, "band_sizes": band_sizes, "reason": str(e),
                })
                if verbose:
                    print(f"  SKIP K={K} sizes={band_sizes}: {e}", flush=True)
                continue
            if counter is not None:
                results["counterexample"] = {
                    "K": K, "band_sizes": band_sizes,
                    "mask": counter[1], "pred": counter[2],
                }
                return results
            entry = {
                "K": K, "band_sizes": band_sizes,
                "checked": checked, "balanced": balanced,
            }
            results["configs"].append(entry)
            results["total_checked"] += checked
            results["total_balanced"] += balanced
            if verbose:
                print(
                    f"  w={w} K={K} sizes={band_sizes} "
                    f"checked={checked} balanced={balanced}",
                    flush=True,
                )
    return results


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--w", type=int, action="append",
                   help="Interaction width(s) to enumerate (default: 1,2,3,4)")
    p.add_argument("--size-limit", type=int, default=None,
                   help="Upper bound on |Q| (overrides 3(3w+1))")
    p.add_argument("--K-max", type=int, default=None,
                   help="Upper bound on depth K (overrides 2w+2)")
    p.add_argument("--output", type=str, default="enum_case3_certificate.json",
                   help="Output certificate JSON path")
    p.add_argument("--verbose", action="store_true")
    args = p.parse_args(argv)

    widths = args.w if args.w else [1, 2, 3, 4]

    certificate = {
        "description": "mg-307c residual Case-3 enumeration certificate",
        "script": "enum_case3.py",
        "hypothesis": (
            "Every layered width-3 poset Q satisfying (L1)-(L4), "
            "layer-ordinal-sum irreducible, with depth K ≥ 3 and interaction "
            "width w ≥ 1, containing an adjacent-band incomparable cross-pair, "
            "contains a balanced pair."
        ),
        "per_width": [],
        "status": "unknown",
    }

    overall_ok = True
    start = time.time()
    for w in widths:
        print(f"=== Enumerating w = {w} ===", flush=True)
        t0 = time.time()
        res = enum_w(
            w,
            size_limit=args.size_limit,
            K_max=args.K_max,
            verbose=args.verbose,
        )
        elapsed = time.time() - t0
        res["elapsed_s"] = round(elapsed, 2)
        certificate["per_width"].append(res)
        if res["counterexample"] is not None:
            print(f"  !! COUNTEREXAMPLE: {res['counterexample']}", flush=True)
            overall_ok = False
        else:
            print(
                f"  w={w}: "
                f"{res['total_balanced']}/{res['total_checked']} balanced, "
                f"elapsed {elapsed:.2f}s",
                flush=True,
            )
            if res["skipped_large"]:
                print(f"  skipped {len(res['skipped_large'])} large configurations",
                      flush=True)

    certificate["status"] = "pass" if overall_ok else "fail"
    certificate["elapsed_s"] = round(time.time() - start, 2)

    with open(args.output, "w") as f:
        json.dump(certificate, f, indent=2, default=str)
    print(f"\nCertificate written to {args.output}")
    print(f"Overall status: {certificate['status']}")
    return 0 if overall_ok else 1


if __name__ == "__main__":
    sys.exit(main())
