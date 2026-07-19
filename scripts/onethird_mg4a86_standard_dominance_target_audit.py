#!/usr/bin/env python3
"""
mg-4a86 — audit of the TARGET STATEMENT of "standard dominance".

The comparison/lift ticket asks to transfer Aldous single-particle dominance
(Caputo-Liggett-Richthammer) from the ambient S_n interchange process to the
constrained BK chain on L(P), with the conclusion "lambda_2(BK) = lambda_std".

This script tests whether that conclusion is the right target, by separating
THREE objects that the framing conflates:

  (A) lambda_2^BK   -- 2nd eigenvalue of the lazy BK walk on L(P)
                       (dynamic; the constrained interchange process)
  (B) lambda_std    -- top eigenvalue on 1^perp of S_P = (T_P + T_P^T)/2,
                       (T_P)_{x,a} = Pr_{sigma ~ Unif L(P)}[sigma(a) = x]
                       (STATIC: a functional of the stationary measure only)
  (C) lambda_1part  -- 2nd eigenvalue of the ALDOUS single-particle walk:
                       one particle on the position path graph, same rates.
                       This is the object CLR's theorem actually controls.

Conventions copied byte-for-byte from the in-repo probes:
  - BK walk: lazy, W[L,L'] += 1/(2(n-1)) per adjacent incomparable position,
    diagonal = 1 - rowsum   (onethird_mg8b64_L1b_bk_transport_transfer_probe.py)
  - T_P, S_P, lambda_std   (onethird_mgb0a6_spectral_killshot_probe.py)

Outputs a JSON certificate. No large datasets: n <= 6 exhaustive over labeled
posets is the cap, plus the antichain family in closed form.
"""

import json
import math
import itertools
from fractions import Fraction

import numpy as np


# ---------------------------------------------------------------- posets ----
class Poset:
    """Strict order given by a boolean matrix lt[x][y] == (x <_P y)."""

    def __init__(self, n, lt):
        self.n = n
        self.lt = lt
        self._les = None

    def comparable(self, a, b):
        return self.lt[a][b] or self.lt[b][a]

    def linear_extensions(self):
        if self._les is None:
            out = []
            for perm in itertools.permutations(range(self.n)):
                pos = {x: i for i, x in enumerate(perm)}
                ok = True
                for x in range(self.n):
                    for y in range(self.n):
                        if self.lt[x][y] and pos[x] > pos[y]:
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    out.append(perm)
            self._les = out
        return self._les


def antichain(n):
    return Poset(n, [[False] * n for _ in range(n)])


def poset_from_relation(n, pairs):
    """pairs = iterable of (x,y) meaning x < y; takes transitive closure."""
    lt = [[False] * n for _ in range(n)]
    for x, y in pairs:
        lt[x][y] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if lt[i][k] and lt[k][j]:
                    lt[i][j] = True
    return Poset(n, lt)


def all_labeled_posets(n):
    """Every strict partial order on [n], enumerated by transitively-closed,
    irreflexive, antisymmetric relation matrices. n <= 5 only (2^(n(n-1)) scan)."""
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in itertools.product([False, True], repeat=len(pairs)):
        lt = [[False] * n for _ in range(n)]
        ok = True
        for (i, j), b in zip(pairs, bits):
            if b:
                if lt[j][i]:
                    ok = False
                    break
                lt[i][j] = True
        if not ok:
            continue
        # transitively closed?
        closed = True
        for i in range(n):
            for k in range(n):
                if not lt[i][k]:
                    continue
                for j in range(n):
                    if lt[k][j] and not lt[i][j]:
                        closed = False
                        break
                if not closed:
                    break
            if not closed:
                break
        if closed:
            yield Poset(n, lt)


# ------------------------------------------------------------- operators ----
def bk_walk_matrix(P):
    """Lazy (n-1)-regular symmetric BK walk on L(P) -- repo convention."""
    les = P.linear_extensions()
    m = len(les)
    n = P.n
    index = {perm: i for i, perm in enumerate(les)}
    W = np.zeros((m, m))
    step = 1.0 / (2 * (n - 1)) if n > 1 else 0.0
    for perm in les:
        i0 = index[perm]
        for i in range(n - 1):
            a, b = perm[i], perm[i + 1]
            if not P.comparable(a, b):
                nb = list(perm)
                nb[i], nb[i + 1] = nb[i + 1], nb[i]
                W[i0, index[tuple(nb)]] += step
    for i0 in range(m):
        W[i0, i0] += 1.0 - W[i0].sum()
    return (W + W.T) / 2.0


def bk_lambda2(P):
    W = bk_walk_matrix(P)
    if W.shape[0] < 2:
        return None
    ev = np.sort(np.linalg.eigvalsh(W))[::-1]
    return float(ev[1])


def transport_matrix(P):
    n = P.n
    les = P.linear_extensions()
    tot = len(les)
    T = np.zeros((n, n))
    for perm in les:
        for a, x in enumerate(perm):
            T[x, a] += 1.0
    return T / tot


def _ortho_H_basis(n):
    """Orthonormal basis (n x (n-1)) of H = {v : sum v_i = 0} (Helmert)."""
    B = np.zeros((n, n - 1))
    for k in range(1, n):
        B[:k, k - 1] = 1.0 / math.sqrt(k * (k + 1))
        B[k, k - 1] = -k / math.sqrt(k * (k + 1))
    return B


def lambda_std(P):
    n = P.n
    T = transport_matrix(P)
    S = (T + T.T) / 2.0
    B = _ortho_H_basis(n)
    w = np.linalg.eigvalsh(B.T @ S @ B)
    return float(np.max(w))


def lambda_one_particle(n):
    """ALDOUS single-particle object for the BK rates: one particle on the
    position path 1..n, moving to each adjacent site w.p. 1/(2(n-1)).
    Eigenvalues 1 - (1 - cos(pi k / n))/(n-1); 2nd largest is k=1."""
    if n < 2:
        return None
    return 1.0 - (1.0 - math.cos(math.pi / n)) / (n - 1)


# ------------------------------------------------------------------ main ----
def main():
    report = {"antichain_family": [], "exhaustive": {}, "named": []}

    # --- Test 1. Antichain: the case where CLR/Aldous applies EXACTLY. ------
    # L(P) = S_n, BK chain = interchange process on the path graph P_n.
    # Aldous  =>  lambda_2(BK) == lambda_one_particle  exactly.
    # Meanwhile T_P = J/n  =>  S_P = J/n  =>  lambda_std = 0 on 1^perp.
    print("=" * 74)
    print("TEST 1 -- ANTICHAIN (Aldous/CLR applies exactly; L(P) = S_n)")
    print("=" * 74)
    print(f"{'n':>3} {'lam2_BK':>12} {'lam_1particle':>14} {'|diff|':>10} "
          f"{'lam_std':>10} {'lam2_BK - lam_std':>18}")
    for n in range(2, 8):
        P = antichain(n)
        if math.factorial(n) > 5100:
            l2 = None
        else:
            l2 = bk_lambda2(P)
        l1 = lambda_one_particle(n)
        ls = lambda_std(P)
        row = {"n": n, "lambda2_BK": l2, "lambda_one_particle": l1,
               "lambda_std": ls,
               "aldous_residual": (abs(l2 - l1) if l2 is not None else None),
               "dominance_excess": (l2 - ls if l2 is not None else None)}
        report["antichain_family"].append(row)
        if l2 is not None:
            print(f"{n:>3} {l2:>12.9f} {l1:>14.9f} {abs(l2-l1):>10.2e} "
                  f"{ls:>10.2e} {l2-ls:>18.9f}")
        else:
            print(f"{n:>3} {'(n! cap)':>12} {l1:>14.9f} {'-':>10} "
                  f"{ls:>10.2e} {'-':>18}")

    # --- Test 2. Exhaustive over labeled posets, n = 4,5. ------------------
    # Question: is lambda_2^BK == lambda_std (standard dominance, BK form)?
    # Also test the claimed inequality lambda_std <= lambda_2^BK.
    print()
    print("=" * 74)
    print("TEST 2 -- EXHAUSTIVE labeled posets: does lambda_2^BK == lambda_std?")
    print("=" * 74)
    for n in (4, 5):
        tested = 0
        dominance_holds = 0
        ineq_violations = []     # lambda_std > lambda_2^BK
        worst = None             # largest lambda_2^BK - lambda_std
        for P in all_labeled_posets(n):
            les = P.linear_extensions()
            if len(les) < 2:
                continue
            l2 = bk_lambda2(P)
            ls = lambda_std(P)
            tested += 1
            if abs(l2 - ls) <= 1e-9:
                dominance_holds += 1
            if ls > l2 + 1e-9:
                ineq_violations.append({"lt": P.lt, "l2": l2, "ls": ls})
            if worst is None or (l2 - ls) > worst["excess"]:
                worst = {"excess": l2 - ls, "lambda2_BK": l2,
                         "lambda_std": ls,
                         "relation": [[int(b) for b in row] for row in P.lt],
                         "n_le": len(les)}
        report["exhaustive"][f"n={n}"] = {
            "tested": tested,
            "dominance_holds": dominance_holds,
            "dominance_fails": tested - dominance_holds,
            "lambda_std_gt_lambda2_violations": len(ineq_violations),
            "worst_excess": worst,
        }
        print(f"n={n}: tested {tested} posets (|L(P)|>=2)")
        print(f"      lambda_2^BK == lambda_std holds : {dominance_holds}")
        print(f"      FAILS                           : {tested-dominance_holds}")
        print(f"      lambda_std > lambda_2^BK        : {len(ineq_violations)}")
        print(f"      worst excess (lam2-lam_std)     : {worst['excess']:.9f}")

    # --- Test 3. Named posets. --------------------------------------------
    print()
    print("=" * 74)
    print("TEST 3 -- NAMED posets")
    print("=" * 74)
    named = {
        "antichain-4": antichain(4),
        "N-poset (2+2): 0<2, 1<3": poset_from_relation(4, [(0, 2), (1, 3)]),
        "chain-2 + antichain-2 (0<1, 2||3)": poset_from_relation(4, [(0, 1)]),
        "V (0<1, 0<2)": poset_from_relation(3, [(0, 1), (0, 2)]),
        "Lambda (0<2, 1<2)": poset_from_relation(3, [(0, 2), (1, 2)]),
        "antichain-3": antichain(3),
        "3+3 ordinal sum of antichains": poset_from_relation(
            6, [(i, j) for i in range(3) for j in range(3, 6)]),
    }
    print(f"{'poset':>36} {'|L(P)|':>7} {'lam2_BK':>11} {'lam_std':>11} {'excess':>11}")
    for name, P in named.items():
        les = P.linear_extensions()
        if len(les) < 2:
            continue
        l2 = bk_lambda2(P)
        ls = lambda_std(P)
        report["named"].append({"name": name, "n": P.n, "n_le": len(les),
                                "lambda2_BK": l2, "lambda_std": ls,
                                "excess": l2 - ls})
        print(f"{name:>36} {len(les):>7} {l2:>11.7f} {ls:>11.7f} {l2-ls:>11.7f}")

    with open("data/onethird-mg4a86-standard-dominance-target-audit.json", "w") as f:
        json.dump(report, f, indent=2)
    print()
    print("wrote data/onethird-mg4a86-standard-dominance-target-audit.json")


if __name__ == "__main__":
    main()
