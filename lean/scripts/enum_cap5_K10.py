#!/usr/bin/env python3
"""
enum_cap5_K10.py — parallel K=10, w=4 cell of mg-4d7b cap-5 enumeration.

The K=10, w=4 cell has nfree = 30 free pairs (gap ≤ 4 between bands
0..9), so 2^30 ≈ 1.07B masks to scan.  Single-threaded Python at ~9µs
per mask = ~2.5 hours; with N workers we cut to ~2.5/N hours.

Splits the mask range into NWORKERS contiguous chunks and reduces
their (accepted, balanced, counterexamples) tuples.
"""
from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import os
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
from enum_cap5 import (  # noqa: E402
    warshall,
    successor_masks,
    antichain_width,
    is_chain,
    find_symmetric_pair,
    count_linear_extensions,
    find_balanced_pair,
)


K = 10
W = 4


def _setup_pairs():
    free_pairs = []
    forced_pairs = []
    for i in range(K):
        for j in range(i + 1, K):
            if j - i > W:
                forced_pairs.append((i, j))
            else:
                free_pairs.append((i, j))
    return free_pairs, forced_pairs


FREE_PAIRS, FORCED_PAIRS = _setup_pairs()
NFREE = len(FREE_PAIRS)
BASE_PRED = [0] * K
for u, v in FORCED_PAIRS:
    BASE_PRED[v] |= 1 << u


def worker(args):
    start, stop, worker_id = args
    accepted = 0
    balanced = 0
    counters: list = []
    t0 = time.time()
    last_report = t0
    progress_interval = 5 * 10**6  # report every 5M masks
    next_report = start + progress_interval
    for mask in range(start, stop):
        pred = BASE_PRED.copy()
        for k in range(NFREE):
            if mask & (1 << k):
                u, v = FREE_PAIRS[k]
                pred[v] |= 1 << u
        pred = warshall(pred, K)
        # Closure-canonical
        skip = False
        for k, (u, v) in enumerate(FREE_PAIRS):
            cb = 1 if (pred[v] & (1 << u)) else 0
            mb = 1 if (mask & (1 << k)) else 0
            if cb != mb:
                skip = True
                break
        if skip:
            if mask >= next_report:
                now = time.time()
                print(
                    f"  worker {worker_id:2d}: mask={mask:>11d}/{stop:>11d} "
                    f"({100*(mask-start)/(stop-start):5.1f}%) "
                    f"accepted={accepted} balanced={balanced} "
                    f"elapsed={now-t0:.0f}s",
                    flush=True,
                )
                next_report = mask + progress_interval
            continue
        if is_chain(pred, K):
            if mask >= next_report:
                pass
            continue
        if antichain_width(pred, K) > 3:
            if mask >= next_report:
                pass
            continue
        accepted += 1
        wit = find_balanced_pair(pred, K)
        if wit is not None:
            balanced += 1
        else:
            counters.append({"mask": mask, "pred": list(pred)})
        if mask >= next_report:
            now = time.time()
            print(
                f"  worker {worker_id:2d}: mask={mask:>11d}/{stop:>11d} "
                f"({100*(mask-start)/(stop-start):5.1f}%) "
                f"accepted={accepted} balanced={balanced} "
                f"elapsed={now-t0:.0f}s",
                flush=True,
            )
            next_report = mask + progress_interval
    elapsed = time.time() - t0
    return {
        "worker_id": worker_id,
        "start": start,
        "stop": stop,
        "accepted": accepted,
        "balanced": balanced,
        "counterexamples": counters,
        "elapsed_s": round(elapsed, 2),
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 1) - 1))
    p.add_argument("--output", type=str, default="enum_cap5_K10_certificate.json")
    p.add_argument("--mask-min", type=int, default=0)
    p.add_argument("--mask-max", type=int, default=1 << NFREE)
    args = p.parse_args(argv)

    nworkers = args.workers
    lo, hi = args.mask_min, args.mask_max
    chunk = (hi - lo + nworkers - 1) // nworkers
    chunks = []
    for i in range(nworkers):
        s = lo + i * chunk
        e = min(hi, s + chunk)
        if s >= e:
            break
        chunks.append((s, e, i))

    print(
        f"K={K} w={W} nfree={NFREE} masks=[{lo}..{hi}) workers={len(chunks)} "
        f"chunk_size={chunk}",
        flush=True,
    )
    start = time.time()
    with mp.Pool(nworkers) as pool:
        results = pool.map(worker, chunks)
    total_elapsed = time.time() - start
    cert = {
        "description": "mg-4d7b — Case3Witness cap-5 K=10 w=4 cell",
        "script": "enum_cap5_K10.py",
        "K": K,
        "w": W,
        "nfree": NFREE,
        "masks_range": [lo, hi],
        "workers": len(chunks),
        "per_worker": results,
        "accepted_total": sum(r["accepted"] for r in results),
        "balanced_total": sum(r["balanced"] for r in results),
        "counterexamples_total": sum(len(r["counterexamples"]) for r in results),
        "elapsed_s": round(total_elapsed, 2),
    }
    cert["status"] = "pass" if cert["counterexamples_total"] == 0 else "fail"
    with open(args.output, "w") as f:
        json.dump(cert, f, indent=2, default=str)
    print(
        f"\nK=10 w=4 done in {total_elapsed:.0f}s: "
        f"accepted={cert['accepted_total']} balanced={cert['balanced_total']} "
        f"counterexamples={cert['counterexamples_total']} → {cert['status']}",
        flush=True,
    )
    return 0 if cert["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
