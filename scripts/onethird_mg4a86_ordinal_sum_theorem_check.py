#!/usr/bin/env python3
"""
mg-4a86 -- numerical verification of the ORDINAL-SUM THEOREM used in
docs/OneThird-StandardDominance-ComparisonRoute.md.

THEOREM (stated in the doc, proved by hand there; checked numerically here).
Let P = P_1 (+) ... (+) P_k be an ordinal sum (every element of P_i below every
element of P_j for i<j), with |P_i| = n_i, n = sum n_i. Then:

  (i)  L(P) = L(P_1) x ... x L(P_k)  (concatenation), and the BK graph on L(P)
       is the CARTESIAN PRODUCT of the BK graphs on the L(P_i). Reason: an
       adjacent pair of a linear extension is incomparable only if both members
       lie in the same block, so every BK move is internal to one block.

  (ii) In the repo's normalization (lazy, step 1/(2(n-1)) per position), the
       generator is the direct sum of the blocks' generators at that same step,
       hence
           gap_BK(P) = min_i gap_BK(P_i @ step 1/(2(n-1))).
       Since a chain's gap is linear in the step rate,
           gap_BK(P_i @ step 1/(2(n-1))) = gap_BK(P_i @ step 1/(2(n_i-1)))
                                            * (n_i - 1) / (n - 1).

  (iii) lambda_std(P) = 1 for every ordinal sum with k >= 2.

CONSEQUENCE. For any ordinal sum with at least one non-singleton block that is
not a chain, gap_BK(P) > 0 = 1 - lambda_std(P), so lambda_2^BK != lambda_std:
standard dominance in the "lambda_2^BK = lambda_std" form fails on the ENTIRE
class of nontrivial ordinal sums -- the very class the programme treats as
extremal (lambda_std = 1 <=> ordinal sum).
"""

import os
import sys
import math
import json
import itertools

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

from onethird_mg4a86_standard_dominance_target_audit import (  # noqa: E402
    Poset, bk_walk_matrix, lambda_std,
)


def ordinal_sum(blocks):
    """blocks = list of Poset. Returns the ordinal sum poset on the disjoint
    union, relabelled 0..n-1 blockwise."""
    offs, off = [], 0
    for B in blocks:
        offs.append(off)
        off += B.n
    n = off
    lt = [[False] * n for _ in range(n)]
    for B, o in zip(blocks, offs):
        for i in range(B.n):
            for j in range(B.n):
                if B.lt[i][j]:
                    lt[o + i][o + j] = True
    for bi in range(len(blocks)):
        for bj in range(bi + 1, len(blocks)):
            for i in range(blocks[bi].n):
                for j in range(blocks[bj].n):
                    lt[offs[bi] + i][offs[bj] + j] = True
    return Poset(n, lt)


def anti(k):
    return Poset(k, [[False] * k for _ in range(k)])


def chain(k):
    lt = [[False] * k for _ in range(k)]
    for i in range(k):
        for j in range(i + 1, k):
            lt[i][j] = True
    return Poset(k, lt)


def gap_of(P):
    W = bk_walk_matrix(P)
    if W.shape[0] < 2:
        return None
    ev = np.sort(np.linalg.eigvalsh(W))[::-1]
    return 1.0 - float(ev[1])


def main():
    out = []
    print("=" * 90)
    print("ORDINAL-SUM THEOREM CHECK")
    print("  predicted gap_BK(P) = min_i  gap_BK(P_i) * (n_i - 1)/(n - 1)")
    print("  predicted lambda_std(P) = 1")
    print("=" * 90)
    print(f"{'ordinal sum':>34} {'|L(P)|':>7} {'gap actual':>12} "
          f"{'gap predicted':>14} {'lam_std':>9} {'dominance?':>11}")

    families = {
        "anti(3) (+) anti(3)": [anti(3), anti(3)],
        "anti(2) (+) anti(2)": [anti(2), anti(2)],
        "anti(2) (+) anti(3)": [anti(2), anti(3)],
        "anti(3) (+) anti(2)": [anti(3), anti(2)],
        "anti(2) (+) anti(2) (+) anti(2)": [anti(2), anti(2), anti(2)],
        "chain(1) (+) anti(3)": [chain(1), anti(3)],
        "anti(4) (+) chain(1)": [anti(4), chain(1)],
        "anti(2) (+) chain(2) (+) anti(2)": [anti(2), chain(2), anti(2)],
        "V(3) (+) anti(2)": [Poset(3, [[False, True, True],
                                       [False] * 3, [False] * 3]), anti(2)],
    }

    ok = True
    for name, blocks in families.items():
        P = ordinal_sum(blocks)
        n = P.n
        les = P.linear_extensions()
        if len(les) < 2 or math.factorial(n) > 500000:
            continue
        g_actual = gap_of(P)

        # predicted: min over blocks of (block gap at its own step) * (n_i-1)/(n-1)
        preds = []
        for B in blocks:
            if B.n < 2:
                continue
            gB = gap_of(B)
            if gB is None or gB <= 1e-12:
                continue          # block is a chain: no BK moves, contributes nothing
            preds.append(gB * (B.n - 1) / (n - 1))
        g_pred = min(preds) if preds else 0.0

        ls = lambda_std(P)
        # product structure check: |L(P)| == prod |L(P_i)|
        prod_le = 1
        for B in blocks:
            prod_le *= len(B.linear_extensions())

        agree = abs(g_actual - g_pred) < 1e-9
        ls_is_one = abs(ls - 1.0) < 1e-9
        dom = abs((1.0 - g_actual) - ls) < 1e-9
        ok = ok and agree and ls_is_one and (len(les) == prod_le)
        out.append({"name": name, "n": n, "n_le": len(les),
                    "prod_block_le": prod_le,
                    "gap_actual": g_actual, "gap_predicted": g_pred,
                    "lambda_std": ls, "dominance_holds": dom})
        print(f"{name:>34} {len(les):>7} {g_actual:>12.9f} {g_pred:>14.9f} "
              f"{ls:>9.6f} {'YES' if dom else 'NO':>11}")

    print()
    print(f"  product structure |L(P)| = prod |L(P_i)| : "
          f"{'ALL OK' if all(r['n_le']==r['prod_block_le'] for r in out) else 'MISMATCH'}")
    print(f"  gap formula matches                      : "
          f"{'ALL OK' if all(abs(r['gap_actual']-r['gap_predicted'])<1e-9 for r in out) else 'MISMATCH'}")
    print(f"  lambda_std == 1 on every ordinal sum     : "
          f"{'ALL OK' if all(abs(r['lambda_std']-1)<1e-9 for r in out) else 'MISMATCH'}")
    print(f"  standard dominance holds anywhere        : "
          f"{sum(r['dominance_holds'] for r in out)} / {len(out)}")

    with open(os.path.join(REPO, "data",
                           "onethird-mg4a86-ordinal-sum-check.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("\nwrote data/onethird-mg4a86-ordinal-sum-check.json")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
