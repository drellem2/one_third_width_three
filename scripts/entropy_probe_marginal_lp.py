#!/usr/bin/env python3
"""Exact marginal-only ceiling for delta  (mg-92e6).

Given the two rows mu = T[x,.], nu = T[y,.] of the position matrix and the
distinctness constraint R_x != R_y, the smallest value of Pr[R_x > R_y]
consistent with those marginals is a transportation LP.  Because the cost is
0/1 it is a max-flow, and the staircase structure gives a closed form:

    minPr[R_x > R_y]  =  max_t [ F_nu(t) - F_mu(t-1) ]
                      =  max_t [ F_nu(t) - F_mu(t) + mu_t ]

This script (a) cross-checks that closed form against a brute-force max-flow on
random marginals, and (b) evaluates it on every naturally-labelled poset with
n <= 7, comparing it to Theorem A and to the true delta.
"""

from fractions import Fraction
import random
import sys

sys.path.insert(0, "scripts")
from entropy_probe_matrix_majorization import (  # noqa: E402
    transitive_upper_triangular_posets, position_matrix, before_counts, analyse)


# ---------------------------------------------------------------- closed form
def min_pr_greater(mu, nu):
    """min over couplings with R_x != R_y of Pr[R_x > R_y]."""
    n = len(mu)
    best = Fraction(0)
    Fmu = Fraction(0)
    Fnu = Fraction(0)
    # t ranges over 1..n (1-indexed); F(t-1) is the prefix strictly before t
    for t in range(n):
        prev_Fmu = Fmu
        Fmu += mu[t]
        Fnu += nu[t]
        best = max(best, Fnu - prev_Fmu)
    return best


def marginal_only_delta_bound(mu, nu):
    """Exact best lower bound on min(Pr[x<y],Pr[y<x]) from the two marginals."""
    return min(min_pr_greater(mu, nu), min_pr_greater(nu, mu))


# ------------------------------------------------------- brute-force max flow
def maxflow_upper_triangle(mu, nu):
    """max mass placeable on {(i,j): i<j} with row sums <= mu, col sums <= nu.
    Simple Ford-Fulkerson on the bipartite staircase, exact rationals."""
    n = len(mu)
    # node ids: 0 = source, 1..n = rows, n+1..2n = cols, 2n+1 = sink
    S, Tk = 0, 2 * n + 1
    cap = {}

    def add(u, v, c):
        cap[(u, v)] = cap.get((u, v), Fraction(0)) + c
        cap.setdefault((v, u), Fraction(0))

    for i in range(n):
        add(S, 1 + i, mu[i])
        add(n + 1 + i, Tk, nu[i])
        for j in range(i + 1, n):
            add(1 + i, n + 1 + j, Fraction(10**6))

    flow = Fraction(0)
    while True:
        # BFS for augmenting path
        par = {S: None}
        q = [S]
        while q and Tk not in par:
            u = q.pop(0)
            for (a, b), c in cap.items():
                if a == u and c > 0 and b not in par:
                    par[b] = u
                    q.append(b)
        if Tk not in par:
            return flow
        # bottleneck
        path = []
        v = Tk
        while par[v] is not None:
            path.append((par[v], v))
            v = par[v]
        b = min(cap[e] for e in path)
        for (u, v) in path:
            cap[(u, v)] -= b
            cap[(v, u)] = cap.get((v, u), Fraction(0)) + b
        flow += b


def cross_check(trials=300, seed=1):
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(2, 6)
        def rand_dist():
            w = [Fraction(rng.randint(0, 6)) for _ in range(n)]
            if sum(w) == 0:
                w[rng.randrange(n)] = Fraction(1)
            s = sum(w)
            return [x / s for x in w]
        mu, nu = rand_dist(), rand_dist()
        # feasibility of a distinct coupling is not guaranteed for random
        # marginals; skip infeasible ones (max flow on the FULL off-diagonal
        # bipartite graph < 1).
        closed = min_pr_greater(mu, nu)
        flow = maxflow_upper_triangle(mu, nu)
        if Fraction(1) - flow != closed:
            print("MISMATCH", mu, nu, "closed", closed, "1-flow", 1 - flow)
            return False
    print(f"closed form cross-checked against max-flow on {trials} random "
          f"marginal pairs: OK")
    return True


# --------------------------------------------------------------- poset sweep
def sweep(max_n):
    for n in range(2, max_n + 1):
        nonchain = 0
        certA = 0        # Theorem A certifies >= 1/3
        certLP = 0       # exact marginal bound certifies >= 1/3
        lp_beats_A = 0
        lp_pairs = 0
        lp_exact = 0     # marginal bound equals the true min(p,1-p)
        for lt in transitive_upper_triangular_posets(n):
            total, T = position_matrix(n, lt)
            cnt = before_counts(n, lt)
            delta, inc = analyse(n, lt, total, T, cnt)
            if delta is None:
                continue
            nonchain += 1
            bestA = Fraction(0)
            bestLP = Fraction(0)
            for x, y, p in inc:
                mu = [Fraction(T[x][i], total) for i in range(n)]
                nu = [Fraction(T[y][i], total) for i in range(n)]
                actual = min(p, 1 - p)
                # Theorem A
                g = [max(Fraction(0), mu[k] + mu[k + 1] + nu[k] + nu[k + 1] - 1)
                     for k in range(n - 1)]
                a = max([Fraction(0)] + [sum(g[k] for k in range(par, n - 1, 2))
                                         / 2 for par in (0, 1)])
                lp = marginal_only_delta_bound(mu, nu)
                # the marginal ceiling is always a valid lower bound on delta
                assert lp <= actual, (n, lt, x, y, lp, actual)
                # Theorem A is NOT a marginal-only bound: it additionally uses
                # the adjacent-transposition involution, so it may EXCEED the
                # marginal ceiling.  Count how often it does.
                assert a <= actual, (n, lt, x, y, a, actual)
                lp_pairs += 1
                if a > lp:
                    lp_beats_A += 1
                if lp == actual:
                    lp_exact += 1
                bestA = max(bestA, a)
                bestLP = max(bestLP, lp)
            if bestA >= Fraction(1, 3):
                certA += 1
            if bestLP >= Fraction(1, 3):
                certLP += 1
        print(f"n={n}: non-chain={nonchain}  ThmA certifies 1/3 on {certA} "
              f"({100*certA/nonchain:.1f}%)  exact-marginal certifies 1/3 on "
              f"{certLP} ({100*certLP/nonchain:.1f}%)  "
              f"[ThmA>marginal-ceiling on {lp_beats_A}/{lp_pairs} pairs, "
              f"LP tight on {lp_exact}/{lp_pairs}]")


if __name__ == "__main__":
    cross_check()
    sweep(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
