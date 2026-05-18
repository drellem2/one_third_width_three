#!/usr/bin/env python3
"""
enum_cap_light.py — Case3Witness cap-LIGHT enumeration (mg-be48).

Extends `enum_cap5.py` (mg-4d7b) by **dropping cap 1**
(`Function.Injective LB.band`). The remaining caps:

* (L1a)  each band has size ≤ 3
* cap 2  `LB.K ≤ 2 * LB.w + 2`        (so `K ≤ 10` for `w ≤ 4`)
* cap 3  `|β| ≤ 6 * LB.w + 6`         (so `|β| ≤ 30` for `w ≤ 4`;
                                       redundant given L1a + cap 2)
* cap 4  bands `[1, K]` nonempty      (each band size ≥ 1)
* cap 5  `LB.w ≤ 4`

The (β, LB) pair is parameterised by

* `(K, w)` in the cap-5 scope (`K ≤ 2w+2`, `w ∈ {0..4}`),
* a band-size tuple `(k_1, …, k_K)` with `k_i ∈ {1, 2, 3}`,
* for each cross-band pair `(x, y)` with `band(x) < band(y)` and
  `band(y) − band(x) ≤ w` (a *free* pair), a Boolean ∈ {0, 1}
  indicating whether `x < y` in the partial order;
* cross-band pairs with `band(y) − band(x) > w` are *forced* to be
  `<` by (L2-forced).

Within-band relations are absent (L1b says each band is an
antichain; since we only add cross-band `<` edges and (L2-upward)
forbids backward edges, transitive closure never introduces a
within-band edge).

This script is intentionally a structural superset of `enum_cap5.py`:
when each `k_i = 1` (the cap-1 sub-slice), it reduces to the same
configuration count as the singleton-band enumeration.

Output: JSON certificate per `(K, w, band-sizes)` cell with
`(masks_tried, accepted, balanced, counterexamples)`. Cells whose
mask space exceeds `--max-masks` (default 2^28 ≈ 268M) are reported
as `skipped` with an upper-bound note; these need a smarter
enumeration (within-band symmetry quotient, structural pruning).

References
----------
* `docs/coherence-collapse-case-extraction.md` (mg-ac13) §5.4 forward
  action #2: "Extend mg-4d7b enumeration to cap-light".
* `docs/width3-residual-statement.md` (mg-2970) §1.2 discharge-coverage
  gap: cap-1 singleton-band restriction misses non-singleton-band
  configurations (canonical example: `3-antichain ⊕ 3-antichain`).
* `lean/scripts/enum_cap5.py` (mg-4d7b): the singleton-band predecessor
  this generalises.
"""
from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import os
import sys
import time
from typing import Iterator

# Use 'fork' start method to avoid macOS spawn-pool overhead. Workers
# inherit the parent's already-loaded enum_cap5 module without
# re-importing or pickling state. Safe here because workers only read
# their args + the imported pure-function library.
try:
    _MP_CTX = mp.get_context("fork")
except ValueError:
    _MP_CTX = mp

# Re-use the bit-mask primitives + balanced-pair check from enum_cap5.
sys.path.insert(0, os.path.dirname(__file__))
from enum_cap5 import (  # noqa: E402
    warshall,
    successor_masks,
    antichain_width,
    is_chain,
    find_symmetric_pair,
    find_balanced_pair,
)


# ---------------------------------------------------------------------------
# Band tuple iteration + free/forced cross-band pair set-up.
# ---------------------------------------------------------------------------


def band_size_tuples(K: int, max_band: int = 3) -> Iterator[tuple[int, ...]]:
    """Iterate band-size tuples (k_1, …, k_K) with 1 ≤ k_i ≤ max_band."""
    if K == 0:
        yield ()
        return
    for sizes in band_size_tuples(K - 1, max_band):
        for k in range(1, max_band + 1):
            yield sizes + (k,)


def setup_pairs(band_sizes: tuple[int, ...], w: int):
    """
    Returns (n, band_of, band_starts, free_pairs, forced_pairs).

    Elements are numbered 0, …, n-1. Element x belongs to band `band_of[x]`
    (0-indexed). Within-band elements are contiguous.
    Cross-band pair (x, y) with x < y has band_y − band_x ≥ 1.
    `free` = band_y − band_x ≤ w; `forced` = band_y − band_x > w.

    For w = 0 every cross-band pair is forced.
    """
    K = len(band_sizes)
    n = sum(band_sizes)
    band_of: list[int] = []
    band_starts: list[int] = []
    for i, k in enumerate(band_sizes):
        band_starts.append(len(band_of))
        band_of.extend([i] * k)
    free_pairs: list[tuple[int, int]] = []
    forced_pairs: list[tuple[int, int]] = []
    for x in range(n):
        for y in range(x + 1, n):
            bx = band_of[x]
            by = band_of[y]
            if bx == by:
                continue
            gap = by - bx
            if gap > w:
                forced_pairs.append((x, y))
            else:
                free_pairs.append((x, y))
    return n, band_of, band_starts, free_pairs, forced_pairs


# ---------------------------------------------------------------------------
# Per-cell enumeration.
# ---------------------------------------------------------------------------


def _enum_cell_brute(band_sizes, w, mask_start, mask_stop):
    """
    Worker function for parallel mask enumeration over [mask_start, mask_stop).

    Returns (accepted, balanced, counterexamples).
    """
    n, band_of, band_starts, free_pairs, forced_pairs = setup_pairs(band_sizes, w)
    nfree = len(free_pairs)
    base_pred = [0] * n
    for u, v in forced_pairs:
        base_pred[v] |= 1 << u

    # Precompute per-band element lists (for early symmetric-pair check).
    K = len(band_sizes)
    band_elems = [[] for _ in range(K)]
    for x, b in enumerate(band_of):
        band_elems[b].append(x)

    # Precompute free-pair indices grouped per element-position:
    # for each cross-band pair (u, v), record (idx, u, v).
    # We'll use this later if needed for early sym check; for now skip.

    accepted = 0
    balanced = 0
    counters: list = []
    for mask in range(mask_start, mask_stop):
        pred = base_pred.copy()
        for k in range(nfree):
            if mask & (1 << k):
                u, v = free_pairs[k]
                pred[v] |= 1 << u
        pred = warshall(pred, n)
        # Closure-canonical: free-pair bits in closure match mask.
        skip = False
        for k, (u, v) in enumerate(free_pairs):
            cb = 1 if (pred[v] & (1 << u)) else 0
            mb = 1 if (mask & (1 << k)) else 0
            if cb != mb:
                skip = True
                break
        if skip:
            continue
        if is_chain(pred, n):
            continue
        if antichain_width(pred, n) > 3:
            continue
        accepted += 1
        wit = find_balanced_pair(pred, n)
        if wit is not None:
            balanced += 1
        else:
            counters.append({
                "mask": mask,
                "pred": list(pred),
                "band_of": list(band_of),
            })
    return accepted, balanced, counters


def enum_cell(band_sizes, w, *,
              max_masks: int,
              parallel_threshold: int = 1 << 20,
              n_workers: int = 1,
              pool=None,
              ) -> dict:
    """
    Enumerate one cell. If `masks_total > parallel_threshold` AND a
    persistent `pool` is supplied, split work across processes.
    """
    n, band_of, band_starts, free_pairs, forced_pairs = setup_pairs(band_sizes, w)
    nfree = len(free_pairs)
    masks_total = 1 << nfree
    entry: dict = {
        "K": len(band_sizes),
        "w": w,
        "band_sizes": list(band_sizes),
        "n": n,
        "nfree": nfree,
        "masks_total": masks_total,
    }
    if masks_total > max_masks:
        entry["skipped"] = True
        entry["reason"] = f"masks {masks_total} exceeds max_masks={max_masks}"
        return entry

    t0 = time.time()
    if pool is not None and masks_total > parallel_threshold:
        chunk = (masks_total + n_workers - 1) // n_workers
        ranges = []
        for i in range(n_workers):
            s = i * chunk
            e = min(masks_total, s + chunk)
            if s >= e:
                break
            ranges.append((band_sizes, w, s, e))
        results = pool.starmap(_enum_cell_brute, ranges)
        accepted = sum(r[0] for r in results)
        balanced = sum(r[1] for r in results)
        counters: list = []
        for r in results:
            counters.extend(r[2])
    else:
        accepted, balanced, counters = _enum_cell_brute(
            band_sizes, w, 0, masks_total)

    entry["accepted"] = accepted
    entry["balanced"] = balanced
    entry["counterexamples"] = counters
    entry["elapsed_s"] = round(time.time() - t0, 2)
    return entry


# ---------------------------------------------------------------------------
# Cell scope: (K, w) and band-size tuples.
# ---------------------------------------------------------------------------


def cap_scope(K_min: int = 1, K_max: int = 10, w_max: int = 4):
    """
    Yield (K, w) tuples in the cap-light scope:
        K ∈ [K_min..K_max], w ∈ [0..w_max] with K ≤ 2w + 2.
    """
    pairs = []
    for K in range(K_min, K_max + 1):
        for w in range(0, w_max + 1):
            if K > 2 * w + 2:
                continue
            # crude upper bound on max free pairs (assuming all-3 bands)
            free_ub = 0
            for i in range(K):
                for j in range(i + 1, K):
                    if j - i <= w:
                        free_ub += 9
            pairs.append((free_ub, K, w))
    pairs.sort()
    return [(K, w) for _ub, K, w in pairs]


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--K-min", type=int, default=1)
    p.add_argument("--K-max", type=int, default=10)
    p.add_argument("--w-max", type=int, default=4)
    p.add_argument("--max-masks", type=int, default=1 << 28,
                   help="Skip cells whose raw mask space exceeds this "
                        "(default 2^28 = ~268M).")
    p.add_argument("--workers", type=int,
                   default=max(1, (os.cpu_count() or 1) - 1))
    p.add_argument("--parallel-threshold", type=int, default=1 << 18,
                   help="Cells with masks > this run multi-process.")
    p.add_argument("--singleton-only", action="store_true",
                   help="Re-run only the singleton-bands sub-slice "
                        "(parity check against mg-4d7b).")
    p.add_argument("--skip-singleton", action="store_true",
                   help="Skip the singleton-bands sub-slice (already "
                        "covered by mg-4d7b).")
    p.add_argument("--output", type=str,
                   default="data/case3witness-cap-light-enum.json")
    p.add_argument("--verbose", action="store_true")
    args = p.parse_args(argv)

    cert: dict = {
        "description": "mg-be48 — Case3Witness cap-LIGHT enumeration certificate",
        "script": "enum_cap_light.py",
        "scope": (
            "All (β, LB) where β is a width-≤3 non-chain finite poset and "
            "LB : LayeredDecomposition β satisfies caps 2-5 + L1a (band "
            "size ≤ 3) of Step8.Case3Witness, with cap 1 (Injective band) "
            "DROPPED. Bands may be non-singleton. K ≤ 2w+2 ⇒ K ≤ 10 for "
            "w ≤ 4; |β| ≤ 3K ≤ 30."
        ),
        "filters": {
            "require_width3": True,
            "require_non_chain": True,
            "require_closure_canonical": True,
            "max_band_size": 3,
        },
        "per_cell": [],
        "status": "unknown",
        "args": vars(args),
    }
    overall_ok = True
    overall_skipped = 0
    accepted_total = 0
    balanced_total = 0
    start = time.time()
    # Persistent fork-mode pool, created once and reused across cells.
    pool = None
    if args.workers > 1:
        pool = _MP_CTX.Pool(args.workers)
    try:
        for (K, w) in cap_scope(args.K_min, args.K_max, args.w_max):
            for band_sizes in band_size_tuples(K):
                is_singleton = all(k == 1 for k in band_sizes)
                if args.singleton_only and not is_singleton:
                    continue
                if args.skip_singleton and is_singleton:
                    continue
                entry = enum_cell(
                    band_sizes, w,
                    max_masks=args.max_masks,
                    parallel_threshold=args.parallel_threshold,
                    n_workers=args.workers,
                    pool=pool,
                )
                cert["per_cell"].append(entry)
                if entry.get("skipped"):
                    overall_skipped += 1
                    if args.verbose:
                        print(
                            f"  K={K} w={w} sizes={list(band_sizes)} "
                            f"masks={entry['masks_total']} SKIPPED",
                            flush=True,
                        )
                    continue
                accepted_total += entry["accepted"]
                balanced_total += entry["balanced"]
                if entry["counterexamples"]:
                    overall_ok = False
                # Print one line per non-trivial cell (masks ≥ 1024)
                # or for counterexamples (always).
                should_print = (
                    args.verbose
                    and (entry["masks_total"] >= 1024 or entry["counterexamples"])
                )
                if should_print:
                    cflag = " *COUNTER*" if entry["counterexamples"] else ""
                    print(
                        f"  K={K} w={w} sizes={list(band_sizes)} "
                        f"nfree={entry['nfree']:2d}  "
                        f"masks={entry['masks_total']:>11d}  "
                        f"accepted={entry['accepted']:>7d}  "
                        f"balanced={entry['balanced']:>7d}  "
                        f"{entry['elapsed_s']:7.2f}s{cflag}",
                        flush=True,
                    )

    finally:
        if pool is not None:
            pool.close()
            pool.join()

    if overall_skipped > 0 and overall_ok:
        cert["status"] = "amber"
    else:
        cert["status"] = "pass" if overall_ok else "fail"
    cert["summary"] = {
        "cells_total": len(cert["per_cell"]),
        "cells_skipped": overall_skipped,
        "accepted_total": accepted_total,
        "balanced_total": balanced_total,
    }
    cert["elapsed_s"] = round(time.time() - start, 2)
    os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
    with open(args.output, "w") as f:
        json.dump(cert, f, indent=2, default=str)
    print(f"\nCertificate written to {args.output}")
    print(
        f"Cells: {len(cert['per_cell'])}  "
        f"skipped: {overall_skipped}  "
        f"accepted: {accepted_total}  "
        f"balanced: {balanced_total}  "
        f"status: {cert['status']}",
        flush=True,
    )
    return 0 if overall_ok else 1


if __name__ == "__main__":
    sys.exit(main())
