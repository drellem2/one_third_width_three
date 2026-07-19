#!/usr/bin/env python3
"""
mg-4a86 -- measuring the constant in SD-quant.

SD-BK ("lambda_2^BK = lambda_std") is FALSE (see the target audit). The
well-posed statement the programme actually needs is the OVERLAP form:

    SD-quant(c):  the slowest BK mode f satisfies  ||P_U f||^2 >= c ||f||^2,

where U = span{ sigma |-> 1[sigma(a)=x] } is the one-particle observable span.
This is well-posed WITHOUT U being invariant (which it is not on L(P)).

This script measures c(P) directly:
  - take the BK eigenspace at lambda_2 (excluding the constant mode),
  - compute the LARGEST overlap over that eigenspace (the most favourable
    reading, which matters because lambda_2 is frequently degenerate):
        c(P) = lambda_max( V^T P_U V ),  V = orthonormal basis of the eigenspace.

A c(P) bounded away from 0 supports SD-quant; a c(P) near 0 refutes it.
"""

import os
import sys
import json
import math

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

from onethird_mg4a86_standard_dominance_target_audit import (  # noqa: E402
    antichain, poset_from_relation, all_labeled_posets,
    bk_walk_matrix, lambda_std,
)
from onethird_mg4a86_sector_leakage_and_tempering import (  # noqa: E402
    one_particle_span,
)


def projector_U(P):
    M = one_particle_span(P)
    Uu, s, _ = np.linalg.svd(M, full_matrices=False)
    tol = max(M.shape) * np.finfo(float).eps * (s[0] if len(s) else 0.0)
    Q = Uu[:, s > max(tol, 1e-10)]
    return Q @ Q.T, Q.shape[1]


def sd_quant_constant(P, tol=1e-9):
    """Largest ||P_U f||^2/||f||^2 over the BK lambda_2 eigenspace."""
    W = bk_walk_matrix(P)
    if W.shape[0] < 2:
        return None, None
    ev, V = np.linalg.eigh(W)
    order = np.argsort(ev)[::-1]
    ev, V = ev[order], V[:, order]
    lam2 = ev[1]
    # eigenspace at lambda_2, skipping the top (constant) mode
    idx = [j for j in range(1, len(ev)) if abs(ev[j] - lam2) < tol]
    Vs = V[:, idx]
    PU, _ = projector_U(P)
    Mat = Vs.T @ PU @ Vs
    c = float(np.max(np.linalg.eigvalsh(Mat)))
    return c, float(lam2)


def main():
    report = {"named": [], "exhaustive": {}}

    print("=" * 78)
    print("SD-quant constant c(P) = max overlap of the slowest BK mode with U")
    print("=" * 78)

    named = {
        "antichain-3": antichain(3),
        "antichain-4": antichain(4),
        "antichain-5": antichain(5),
        "N-poset (2+2)": poset_from_relation(4, [(0, 2), (1, 3)]),
        "chain2+anti2": poset_from_relation(4, [(0, 1)]),
        "A2 (+) A2 ordinal sum": poset_from_relation(
            4, [(0, 2), (0, 3), (1, 2), (1, 3)]),
        "A3 (+) A3 ordinal sum": poset_from_relation(
            6, [(i, j) for i in range(3) for j in range(3, 6)]),
    }
    print(f"{'poset':>26} {'|L(P)|':>7} {'lambda2_BK':>12} {'c(P)':>10} {'lam_std':>10}")
    for name, P in named.items():
        les = P.linear_extensions()
        if len(les) < 2:
            continue
        c, lam2 = sd_quant_constant(P)
        ls = lambda_std(P)
        report["named"].append({"name": name, "n": P.n, "n_le": len(les),
                                "c": c, "lambda2_BK": lam2, "lambda_std": ls})
        print(f"{name:>26} {len(les):>7} {lam2:>12.9f} {c:>10.6f} {ls:>10.6f}")

    print()
    print("  NOTE: the antichain rows are the ambient S_n interchange process,")
    print("  where the slowest mode IS the single-particle mode, so c must be 1.")
    print("  That is the control for this measurement.")

    print()
    print("=" * 78)
    print("EXHAUSTIVE: distribution of c(P) over all labeled posets")
    print("=" * 78)
    # CALIBRATION: c ~ 1 is only meaningful when U is a SMALL subspace of
    # L^2(L(P)). If dim U / |L(P)| ~ 1 then P_U ~ I and c ~ 1 is vacuous.
    # We therefore report c stratified by the dimension ratio.
    for n in (4, 5):
        cs, ratios = [], []
        worst = None
        for P in all_labeled_posets(n):
            les = P.linear_extensions()
            if len(les) < 2:
                continue
            c, lam2 = sd_quant_constant(P)
            _, dimU = projector_U(P)
            r = dimU / len(les)
            cs.append(c)
            ratios.append(r)
            if worst is None or c < worst["c"]:
                worst = {"c": c, "lambda2_BK": lam2, "dim_U": dimU,
                         "relation": [[int(b) for b in row] for row in P.lt],
                         "n_le": len(les), "dim_ratio": r}
        cs, ratios = np.array(cs), np.array(ratios)
        # the informative stratum: U occupies at most half the space
        info = ratios <= 0.5
        strat = {}
        if info.any():
            strat = {"n_informative": int(info.sum()),
                     "min_c_informative": float(cs[info].min()),
                     "median_c_informative": float(np.median(cs[info]))}
        report["exhaustive"][f"n={n}"] = {
            "tested": len(cs), "min_c": float(cs.min()),
            "median_c": float(np.median(cs)), "max_c": float(cs.max()),
            "median_dim_ratio": float(np.median(ratios)),
            "frac_dim_ratio_above_0.9": float((ratios > 0.9).mean()),
            "worst": worst, **strat,
        }
        print(f"  n={n}: {len(cs)} posets | min c = {cs.min():.6f} | "
              f"median = {np.median(cs):.6f} | max = {cs.max():.6f}")
        print(f"        dim U / |L(P)| : median = {np.median(ratios):.4f}, "
              f"fraction > 0.9 = {(ratios > 0.9).mean():.4f}")
        if info.any():
            print(f"        INFORMATIVE stratum (dim U <= |L(P)|/2): "
                  f"{int(info.sum())} posets, min c = {cs[info].min():.6f}, "
                  f"median c = {np.median(cs[info]):.6f}")
        else:
            print("        INFORMATIVE stratum EMPTY -- c ~ 1 is vacuous here")

    with open(os.path.join(REPO, "data",
                           "onethird-mg4a86-sdquant-overlap.json"), "w") as f:
        json.dump(report, f, indent=2)
    print("\nwrote data/onethird-mg4a86-sdquant-overlap.json")


if __name__ == "__main__":
    main()
