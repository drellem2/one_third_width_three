#!/usr/bin/env python3
"""
mg-4a86 -- (a) standard-sector NON-INVARIANCE on L(P), and
           (b) the beta-tempering / soft-constraint DEFORMATION S_n -> L(P).

(a) SECTOR LEAKAGE.
    On S_n the span U = span{ sigma |-> 1[sigma(a)=x] } of one-particle
    observables is INVARIANT under the interchange process (a BK move permutes
    the position index a, so it maps U into U). That invariance is what makes
    "the gap lives in the standard sector" a well-posed statement, and it is
    what Schur/CLR exploit.
    On L(P) the move at position i is applied only when sigma(i), sigma(i+1)
    are incomparable -- the action on the position index is sigma-DEPENDENT --
    so U need not be invariant. We measure the leakage
        leak(P) := || (I - P_U) W P_U ||_op
    which is exactly the "constraint-boundary term" of any comparison route.
    leak = 0 would mean the sector language transfers; leak > 0 means there is
    no invariant standard sector on L(P) at all.

(b) TEMPERING DEFORMATION.
    Gibbs measure on ALL of S_n:  pi_beta(sigma) ~ exp(-beta * V(sigma)),
    V(sigma) = #{(x,y) : x <_P y but sigma places y before x}  (poset violations).
    Metropolis chain: pick position i in 1..n-1 uniformly, propose the adjacent
    swap, accept w.p. min(1, exp(-beta * dV)).  beta=0 is the uniform-S_n
    interchange process on the path (Aldous/CLR applies exactly); beta=inf
    restricted to {V=0} is exactly the BK chain.
    We track along the ladder: lambda_2(beta), lambda_std(beta), and the
    dominance excess lambda_2(beta) - lambda_std(beta).
"""

import json
import math
import os
import sys
import itertools

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

from onethird_mg4a86_standard_dominance_target_audit import (
    Poset, antichain, poset_from_relation, bk_walk_matrix,
    transport_matrix, _ortho_H_basis, lambda_std,
)


# --------------------------------------------------- (a) sector leakage -----
def one_particle_span(P):
    """Basis matrix (|L(P)| x n^2) whose columns are the one-particle
    observables sigma |-> 1[sigma(a) = x]."""
    les = P.linear_extensions()
    m, n = len(les), P.n
    M = np.zeros((m, n * n))
    for r, perm in enumerate(les):
        for a, x in enumerate(perm):
            M[r, x * n + a] = 1.0
    return M


def sector_leakage(W, M):
    """|| (I - P_U) W P_U ||_op where U = col span of M."""
    # Orthonormal basis of U = col span(M) via SVD (QR's trailing columns are
    # NOT in the span once M is rank-deficient, which it always is here:
    # rank = (n-1)^2 + 1 on S_n, not n^2).
    Uu, s, _ = np.linalg.svd(M, full_matrices=False)
    tol = max(M.shape) * np.finfo(float).eps * (s[0] if len(s) else 0.0)
    Q = Uu[:, s > max(tol, 1e-10)]
    PU = Q @ Q.T
    resid = (np.eye(W.shape[0]) - PU) @ W @ PU
    return float(np.linalg.norm(resid, 2)), Q.shape[1]


# ------------------------------------------------------ (b) tempering -------
def violations(P, perm):
    pos = {x: i for i, x in enumerate(perm)}
    v = 0
    for x in range(P.n):
        for y in range(P.n):
            if P.lt[x][y] and pos[x] > pos[y]:
                v += 1
    return v


def tempered_chain(P, beta):
    """Metropolis chain on ALL of S_n at inverse temperature beta.
    Returns (W, pi, perms). beta = math.inf allowed."""
    n = P.n
    perms = list(itertools.permutations(range(n)))
    index = {p: i for i, p in enumerate(perms)}
    m = len(perms)
    V = np.array([violations(P, p) for p in perms], dtype=float)
    W = np.zeros((m, m))
    step = 1.0 / (n - 1)
    for p in perms:
        i0 = index[p]
        for i in range(n - 1):
            q = list(p)
            q[i], q[i + 1] = q[i + 1], q[i]
            j0 = index[tuple(q)]
            dV = V[j0] - V[i0]
            if beta == math.inf:
                acc = 1.0 if dV <= 0 else 0.0
            else:
                acc = 1.0 if dV <= 0 else math.exp(-beta * dV)
            W[i0, j0] += step * acc
    for i0 in range(m):
        W[i0, i0] += 1.0 - W[i0].sum()
    if beta == math.inf:
        pi = (V == 0).astype(float)
    else:
        pi = np.exp(-beta * V)
    pi = pi / pi.sum()
    return W, pi, perms


def reversible_lambda2(W, pi):
    """2nd eigenvalue of a pi-reversible chain, via the symmetrized conjugate
    D^{1/2} W D^{-1/2}. Restricted to the support of pi."""
    supp = np.where(pi > 1e-14)[0]
    Ws = W[np.ix_(supp, supp)]
    ps = pi[supp]
    d = np.sqrt(ps)
    A = (Ws * d[:, None]) / d[None, :]
    A = (A + A.T) / 2.0
    ev = np.sort(np.linalg.eigvalsh(A))[::-1]
    return float(ev[1]) if len(ev) > 1 else None


def lambda_std_of_measure(P, pi, perms):
    """lambda_std computed from an arbitrary measure pi on S_n (not just
    uniform-on-L(P)): (T)_{x,a} = Pr_pi[sigma(a) = x]."""
    n = P.n
    T = np.zeros((n, n))
    for w, perm in zip(pi, perms):
        if w <= 0:
            continue
        for a, x in enumerate(perm):
            T[x, a] += w
    S = (T + T.T) / 2.0
    B = _ortho_H_basis(n)
    return float(np.max(np.linalg.eigvalsh(B.T @ S @ B)))


# ------------------------------------------------------------------ main ----
def main():
    report = {"leakage": [], "tempering": {}}

    cases = {
        "antichain-4": antichain(4),
        "antichain-5": antichain(5),
        "N-poset (2+2)": poset_from_relation(4, [(0, 2), (1, 3)]),
        "chain2+anti2 (0<1, 2||3)": poset_from_relation(4, [(0, 1)]),
        "V (0<1,0<2)+isolated 3": poset_from_relation(4, [(0, 1), (0, 2)]),
        "2+2 ordinal sum (anti2 -> anti2)": poset_from_relation(
            4, [(0, 2), (0, 3), (1, 2), (1, 3)]),
        "antichain-3": antichain(3),
    }

    print("=" * 78)
    print("(a) STANDARD-SECTOR LEAKAGE on L(P):  || (I-P_U) W P_U ||")
    print("    U = span of one-particle observables. leak=0 <=> U is BK-invariant.")
    print("=" * 78)
    print(f"{'poset':>34} {'|L(P)|':>7} {'dim U':>6} {'leakage':>12}")
    for name, P in cases.items():
        les = P.linear_extensions()
        if len(les) < 2:
            continue
        W = bk_walk_matrix(P)
        M = one_particle_span(P)
        leak, dimU = sector_leakage(W, M)
        report["leakage"].append({"name": name, "n": P.n, "n_le": len(les),
                                  "dim_U": dimU, "leakage": leak})
        print(f"{name:>34} {len(les):>7} {dimU:>6} {leak:>12.3e}")

    # ambient control: the antichain IS S_n, so leakage must be 0 there.
    print()
    print("  (control: antichain rows are the ambient S_n interchange process,")
    print("   where U is provably invariant -- leakage there should be ~0.)")

    print()
    print("=" * 78)
    print("(b) TEMPERING DEFORMATION  S_n --> L(P):  pi_beta ~ exp(-beta * #violations)")
    print("=" * 78)
    betas = [0.0, 0.25, 0.5, 1.0, 1.5, 2.0, 3.0, 5.0, 8.0, 12.0, math.inf]
    for name, P in cases.items():
        if P.n > 5:
            continue
        les = P.linear_extensions()
        if len(les) < 2:
            continue
        print()
        print(f"  {name}   (n={P.n}, |L(P)|={len(les)})")
        print(f"  {'beta':>7} {'lambda2(beta)':>15} {'lambda_std(beta)':>17} "
              f"{'excess':>12}")
        rows = []
        for b in betas:
            W, pi, perms = tempered_chain(P, b)
            l2 = reversible_lambda2(W, pi)
            ls = lambda_std_of_measure(P, pi, perms)
            rows.append({"beta": (None if b == math.inf else b),
                         "beta_is_inf": b == math.inf,
                         "lambda2": l2, "lambda_std": ls,
                         "excess": (l2 - ls) if l2 is not None else None})
            bl = "inf" if b == math.inf else f"{b:.2f}"
            print(f"  {bl:>7} {l2:>15.9f} {ls:>17.9f} {l2-ls:>12.9f}")
        report["tempering"][name] = rows

    # ---- (c) endpoint behaviour: does lambda_2(beta) -> lambda_2(BK)? ------
    print()
    print("=" * 78)
    print("(c) ENDPOINT of the deformation: what is lim_{beta->inf} lambda_2(beta)?")
    print("    At beta=inf the chain is block-triangular: L(P) is closed (the BK")
    print("    block) and the violating states {V>0} are transient. So")
    print("        spec(W_inf) = spec(BK block)  U  spec(transient block).")
    print("    NOTE on normalization: the tempered chain uses step 1/(n-1), i.e.")
    print("    TWICE the rate of the repo's bk_walk_matrix (step 1/(2(n-1)));")
    print("    we therefore read the BK block off W_inf directly, not from")
    print("    bk_walk_matrix, so the two are on the same clock.")
    print("    Eigenvalues are taken RAW (np.linalg.eigvals): the D^{1/2} W D^{-1/2}")
    print("    symmetrization is numerically destroyed for beta >~ 40.")
    print("=" * 78)
    report["endpoint"] = []
    for name, P in cases.items():
        if P.n > 4:
            continue
        les = P.linear_extensions()
        if len(les) < 2 or len(les) == math.factorial(P.n):
            continue   # antichain: no constraint, nothing to deform
        big = [5.0, 10.0, 20.0, 40.0, 80.0]
        vals = []
        for b in big:
            W, _, _ = tempered_chain(P, b)
            ev = np.sort(np.real(np.linalg.eigvals(W)))[::-1]
            vals.append(float(ev[1]))

        Winf, _, perms = tempered_chain(P, math.inf)
        inside = [i for i, p in enumerate(perms) if violations(P, p) == 0]
        outside = [i for i, p in enumerate(perms) if violations(P, p) > 0]
        bk_block = np.sort(np.real(np.linalg.eigvals(
            Winf[np.ix_(inside, inside)])))[::-1]
        l2bk = float(bk_block[1])
        trans = None
        if outside:
            trans = float(np.max(np.real(np.linalg.eigvals(
                Winf[np.ix_(outside, outside)]))))
        limit = vals[-1]
        governed_by = ("transient" if (trans is not None and trans > l2bk + 1e-9)
                       else "BK")
        report["endpoint"].append({
            "name": name, "betas": big, "lambda2_at_betas": vals,
            "lambda2_BK_block_matched_clock": l2bk,
            "transient_block_spectral_radius": trans,
            "limit": limit, "limit_governed_by": governed_by,
            "limit_equals_BK": abs(limit - l2bk) < 1e-6,
        })
        print(f"\n  {name}")
        for b, v in zip(big, vals):
            print(f"      lambda_2(beta={b:>5.0f}) = {v:.9f}")
        print(f"      lambda_2 of BK block (matched clock) = {l2bk:.9f}")
        if trans is not None:
            print(f"      spec.radius of transient (V>0) block  = {trans:.9f}")
        print(f"      => limit = {limit:.9f}, governed by the {governed_by.upper()} block"
              f"; equals lambda_2^BK ? "
              f"{'YES' if abs(limit - l2bk) < 1e-6 else 'NO'}")

    with open(os.path.join(REPO, "data",
                           "onethird-mg4a86-sector-leakage-tempering.json"), "w") as f:
        json.dump(report, f, indent=2)
    print()
    print("wrote data/onethird-mg4a86-sector-leakage-tempering.json")


if __name__ == "__main__":
    main()
