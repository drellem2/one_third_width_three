#!/usr/bin/env python3
r"""
posn_n6_chi_tilde_full.py
==========================

Direct computation of χ̃(Δ(PPF_6)) via bitmask-based chain-count DP.

|PPF_6| = 129302.  Strict-inclusion below-graph has up to N^2/2 ≈ 8.4·10^9
pairs; checking each pair via int-bitmask subset is ~50 ns in Python.
Estimated runtime: hours per layer in pure Python (mg-3bf3 session 1
measurement: layer 1 did not complete in 3 min of wall time → estimate
~30-60 min/layer; ~14 layers → multi-hour total).  Deferred from
mg-3bf3 session 1; replaces extrapolation χ̃(Δ_6) = +1 in
posn_n6_hpc.py Phase 3 with a direct computation once a session
with HPC budget runs it.

Encoding: 30 directed pairs (i,j), i ∈ {0..5}, j ∈ {0..5}, i ≠ j.
  pair_index(i, j) = i*5 + (j if j < i else j-1)
  poset → 30-bit int bitmask.

Subset check (P ⊂ Q in 30-bit space):  (P & Q) == P AND P != Q.

DP: layer_k[P] = #chains-of-length-k+1 ending at P.
  f_k = Σ_P layer_k[P]
  χ̃ = -1 + Σ_k (-1)^k f_k.

Usage:
    python3 posn_n6_chi_tilde_full.py [--limit-layer K] [--verbose]
"""

from __future__ import annotations
import argparse
import os
import pickle
import sys
import time
from fractions import Fraction

CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '_n6_cache')
N = 6


def pair_index(i, j):
    """Pack ordered pair (i, j), i != j, into 30-bit index 0..29."""
    assert i != j and 0 <= i < N and 0 <= j < N
    if j > i:
        return i * (N - 1) + (j - 1)
    else:
        return i * (N - 1) + j


def poset_to_mask(P):
    m = 0
    for (i, j) in P:
        m |= 1 << pair_index(i, j)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--limit-layer', type=int, default=None,
                    help='Stop after computing f_k for k=0..limit-layer')
    ap.add_argument('--verbose', '-v', action='store_true')
    args = ap.parse_args()

    cache_path = os.path.join(CACHE_DIR, 'ppf6.pkl')
    if not os.path.exists(cache_path):
        print(f"ERROR: ppf6 cache not found.  Run posn_n6_hpc.py --phase=enum first.")
        sys.exit(1)
    # Unbuffer stdout so progress is visible in real time even when
    # piping to a file (the default block-buffering makes the script
    # appear hung for minutes — see mg-3bf3 session 1 ledger).
    sys.stdout.reconfigure(line_buffering=True)
    print(f"  Loading PPF_6 cache...")
    t0 = time.time()
    with open(cache_path, 'rb') as f:
        ppf = pickle.load(f)
    print(f"    |PPF_6| = {len(ppf)}  ({time.time()-t0:.1f}s)")

    # Sort by rank then lex.
    print(f"  Encoding as 30-bit bitmasks + sorting by rank...")
    t0 = time.time()
    items = [(len(P), tuple(sorted(P)), poset_to_mask(P)) for P in ppf]
    items.sort()
    masks = [it[2] for it in items]
    ranks = [it[0] for it in items]
    N_elts = len(masks)
    print(f"    encoded {N_elts} masks; rank range [{min(ranks)}..{max(ranks)}]"
          f" ({time.time()-t0:.1f}s)")
    # Group by rank for efficient "below" iteration.
    rank_to_idx = {}
    for i, r in enumerate(ranks):
        rank_to_idx.setdefault(r, []).append(i)
    print(f"    rank distribution: " +
          ", ".join(f"r={r}:{len(v)}" for r, v in sorted(rank_to_idx.items())))

    # Layer-0 (length-1 chains): every element is a length-1 chain.
    layer = [1] * N_elts
    f_vec = [N_elts]  # f_0 = #vertices = N_elts
    k = 1
    t_total = time.time()
    while True:
        if args.limit_layer is not None and k > args.limit_layer:
            break
        t_layer = time.time()
        nxt = [0] * N_elts
        # For each i, sum layer[j] over j with masks[j] ⊊ masks[i] (strict subset).
        # Strict subset: (masks[j] & masks[i]) == masks[j] AND masks[j] != masks[i].
        # Since rank[j] < rank[i] implies strict (subset) AND less, iterate over
        # lower-rank j only.
        all_ranks = sorted(rank_to_idx.keys())
        lower_js_cumul = []
        for r_i in all_ranks:
            if not lower_js_cumul:
                # First rank; nothing to do.
                lower_js_cumul = list(rank_to_idx[r_i])
                continue
            # For each i in rank r_i, check against lower_js_cumul.
            print(f"      r={r_i}: |lower|={len(lower_js_cumul)}, |rank_r|={len(rank_to_idx[r_i])}")
            for idx_i, i in enumerate(rank_to_idx[r_i]):
                mi = masks[i]
                s = 0
                for j in lower_js_cumul:
                    mj = masks[j]
                    if (mj & mi) == mj:
                        s += layer[j]
                nxt[i] = s
                if idx_i and idx_i % 1000 == 0:
                    print(f"        ... r={r_i} row {idx_i}/{len(rank_to_idx[r_i])}")
            # advance cumulative lower-rank pool
            lower_js_cumul.extend(rank_to_idx[r_i])
        fk = sum(nxt)
        elapsed_layer = time.time() - t_layer
        print(f"    layer k={k}: f_{k} = {fk}  ({elapsed_layer:.1f}s, "
              f"cumul {time.time()-t_total:.1f}s)")
        if fk == 0:
            break
        f_vec.append(fk)
        layer = nxt
        k += 1

    chi_tilde = -1
    for kk, fk in enumerate(f_vec):
        chi_tilde += ((-1) ** kk) * fk
    print()
    print(f"  f-vector: {f_vec}")
    print(f"  χ̃(Δ(PPF_6)) = -1 + Σ(-1)^k f_k = {chi_tilde}")
    print(f"  Expected (clean Lefschetz): χ̃ = sgn(id) = +1")
    print(f"  Match: {'✓' if chi_tilde == 1 else '✗'}")

    save_path = os.path.join(CACHE_DIR, 'chi_tilde_full.pkl')
    with open(save_path, 'wb') as f:
        pickle.dump({'f_vec': f_vec, 'chi_tilde': chi_tilde,
                     'limit_layer': args.limit_layer}, f)
    print(f"  Saved → {save_path}")


if __name__ == '__main__':
    main()
