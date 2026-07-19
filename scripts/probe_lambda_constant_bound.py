#!/usr/bin/env python3
"""Numerical check of the elementary identities behind docs/probe-lambda-constant-bound.md.

Self-contained (no numpy). For small random posets we verify, exactly:

  (I1)  leak(A_k) = |A_k| - <1_A, S 1_A>            (Buser test-vector bookkeeping)
  (I2)  sum_{k=1}^{n-1} leak(A_k) = E[F]/2          (F = Spearman footrule)
  (I3)  E[F] <= 2 E[inv]                            (Diaconis-Graham, upper half)
  (I4)  1 - lambda_std <= n*leak(A)/(|A||A^c|)      (the Buser tool, all subsets A)
  (I5)  1 - lambda_std <= 6 E[inv] / (n^2 - 1)      (the master bound of the note)

plus, for a reference order drawn from the uniform linear-extension law,

  (I6)  E_L E[inv_L] = sum over incomparable pairs of 2 p (1-p).

Usage:  python3 scripts/probe_lambda_constant_bound.py [trials]
"""

import itertools
import random
import sys
from fractions import Fraction


# ---------------------------------------------------------------- posets ----

def random_poset(n, p_edge, rng):
    """Random strict order: take a random DAG on 0..n-1 respecting index order,
    then transitively close.  `less[x][y]` iff x < y in P."""
    less = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p_edge:
                less[i][j] = True
    for k in range(n):
        for i in range(n):
            if less[i][k]:
                for j in range(n):
                    if less[k][j]:
                        less[i][j] = True
    return less


def linear_extensions(less, n):
    return [perm for perm in itertools.permutations(range(n))
            if all(not less[perm[b]][perm[a]] for a in range(n) for b in range(a + 1, n))]


def incomparable_pairs(less, n):
    return [(x, y) for x in range(n) for y in range(x + 1, n)
            if not less[x][y] and not less[y][x]]


# ------------------------------------------------------------- transport ----

def transport(exts, n, ref):
    """T[x][i] = Pr[element x sits at position i], with elements *relabelled*
    by the reference linear extension `ref`: reference-label r of element ref[r].
    So T is indexed label x position, and T^T makes sense."""
    N = len(exts)
    pos_of_label = {ref[r]: r for r in range(n)}
    T = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for e in exts:
        for i, elt in enumerate(e):
            T[pos_of_label[elt]][i] += Fraction(1, N)
    return T


def symmetrize(T, n):
    return [[(T[i][j] + T[j][i]) / 2 for j in range(n)] for i in range(n)]


# ------------------------------------------- Jacobi eigenvalues (float) -----

def eigenvalues_sym(M, n, sweeps=100):
    A = [[float(M[i][j]) for j in range(n)] for i in range(n)]
    for _ in range(sweeps):
        off = sum(A[i][j] ** 2 for i in range(n) for j in range(n) if i != j)
        if off < 1e-24:
            break
        for p in range(n - 1):
            for q in range(p + 1, n):
                if abs(A[p][q]) < 1e-18:
                    continue
                theta = (A[q][q] - A[p][p]) / (2 * A[p][q])
                t = (1 if theta >= 0 else -1) / (abs(theta) + (theta ** 2 + 1) ** 0.5)
                c = 1 / (t ** 2 + 1) ** 0.5
                s = t * c
                for k in range(n):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p] = c * akp - s * akq
                    A[k][q] = s * akp + c * akq
                for k in range(n):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k] = c * apk - s * aqk
                    A[q][k] = s * apk + c * aqk
    return sorted(A[i][i] for i in range(n))


def lambda_std(S, n):
    """Top eigenvalue of S on 1-perp.  S is doubly stochastic and symmetric, so
    S1 = 1; deflate by subtracting 2 * J/n (pushes the all-ones eigenvalue to -1,
    strictly below every other eigenvalue since spec(S) subset [-1,1])."""
    D = [[S[i][j] - Fraction(2, n) for j in range(n)] for i in range(n)]
    return max(eigenvalues_sym(D, n))


# ------------------------------------------------------------ quantities ----

def leak(S, n, A):
    """|A| - <1_A, S 1_A>, exactly."""
    return len(A) - sum(S[i][j] for i in A for j in A)


def leak_direct(exts, n, ref, A):
    """E |{x in A : position of x not in A}|, exactly -- the combinatorial form."""
    N = len(exts)
    pos_of_label = {ref[r]: r for r in range(n)}
    tot = Fraction(0)
    for e in exts:
        for i, elt in enumerate(e):
            if pos_of_label[elt] in A and i not in A:
                tot += Fraction(1, N)
    return tot


def footrule_and_inv(exts, n, ref):
    """E[F] and E[inv], both relative to the reference labelling."""
    N = len(exts)
    pos_of_label = {ref[r]: r for r in range(n)}
    F = Fraction(0)
    inv = Fraction(0)
    for e in exts:
        lab = [pos_of_label[elt] for elt in e]   # lab[i] = reference label at position i
        F += Fraction(sum(abs(lab[i] - i) for i in range(n)), N)
        inv += Fraction(sum(1 for i in range(n) for j in range(i + 1, n) if lab[i] > lab[j]), N)
    return F, inv


# ----------------------------------------------------------------- main -----

def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    rng = random.Random(20260719)
    checked = 0
    worst_slack = None

    for _ in range(trials):
        n = rng.randint(3, 7)
        less = random_poset(n, rng.choice([0.12, 0.2, 0.35, 0.5]), rng)
        exts = linear_extensions(less, n)
        if len(exts) < 2:
            continue
        ref = list(rng.choice(exts))

        T = transport(exts, n, ref)
        S = symmetrize(T, n)
        lam = lambda_std(S, n)
        EF, Einv = footrule_and_inv(exts, n, ref)

        # (I1) + (I2): threshold cuts A_k = {0,...,k-1} in reference labels
        tot_leak = Fraction(0)
        for k in range(1, n):
            A = set(range(k))
            lk = leak(S, n, A)
            assert lk == leak_direct(exts, n, ref, A), "(I1) failed"
            tot_leak += lk
        assert tot_leak * 2 == EF, f"(I2) failed: {tot_leak} vs {EF}"

        # (I3) Diaconis-Graham upper half
        assert EF <= 2 * Einv, "(I3) failed"

        # (I4) Buser tool over *every* nonempty proper subset
        for r in range(1, n):
            for A in itertools.combinations(range(n), r):
                A = set(A)
                rhs = n * leak(S, n, A) / (len(A) * (n - len(A)))
                assert 1 - lam <= float(rhs) + 1e-9, "(I4) failed"

        # (I5) the master bound
        rhs5 = float(6 * Einv) / (n * n - 1)
        slack = rhs5 - (1 - lam)
        assert slack > -1e-9, f"(I5) failed: 1-lam={1-lam}, rhs={rhs5}"
        if worst_slack is None or slack < worst_slack[0]:
            worst_slack = (slack, n, len(exts), float(lam), rhs5)

        # (I6) averaging the reference over the uniform linear-extension law
        inc = incomparable_pairs(less, n)
        avg_inv = Fraction(0)
        for L in exts:
            _, iv = footrule_and_inv(exts, n, list(L))
            avg_inv += iv
        avg_inv /= len(exts)
        pred = Fraction(0)
        for (x, y) in inc:
            p = Fraction(sum(1 for e in exts if e.index(x) < e.index(y)), len(exts))
            pred += 2 * p * (1 - p)
        assert avg_inv == pred, f"(I6) failed: {avg_inv} vs {pred}"

        checked += 1

    print(f"all identities (I1)-(I6) verified on {checked} posets")
    s, n, N, lam, rhs = worst_slack
    print(f"tightest (I5) instance: n={n}, e(P)={N}, lambda_std={lam:.6f}, "
          f"bound rhs={rhs:.6f}, slack={s:.6f}")


if __name__ == "__main__":
    main()
