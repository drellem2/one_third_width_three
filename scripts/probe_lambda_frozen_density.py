#!/usr/bin/env python3
"""How large can the incomparability density d be on a *frozen* poset?

This is the one quantity the master bound of docs/probe-lambda-constant-bound.md
turns on:   lambda_std >= 1 - d*n/(n+1)   for frozen P.  A constant lower bound
on lambda_std exists iff frozen posets have d bounded away from 1.

We scan the "gap-g shift poset"  G(n,g):  x_i < x_j  iff  j - i >= g.
It is the natural family interpolating between a chain (g=1) and an antichain
(g=n), and its incomparability density is d ~ (2g-1)/n ... up to 1.

For each member we report exactly:
  d              = m / C(n,2),  m = #incomparable pairs
  beta_max       = max over incomparable pairs of the minority probability
                   (P is "frozen" iff beta_max < 1/3)
  lambda_std     = top eigenvalue of (T+T^T)/2 on 1-perp, reference = index order
  bound          = 1 - 3 E[F] / (n^2-1)   (master bound, footrule form)

Exact rational linear-extension counting via down-set DP.

Usage:  python3 scripts/probe_lambda_frozen_density.py [nmax]
"""

import sys
from fractions import Fraction

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from probe_lambda_constant_bound import eigenvalues_sym  # noqa: E402


def gap_poset(n, g):
    """less[i][j] iff x_i < x_j.  Already transitive: j-i>=g and k-j>=g => k-i>=g."""
    return [[(j - i) >= g for j in range(n)] for i in range(n)]


def count_extensions(less, n, extra=None):
    """#linear extensions of P (optionally with one extra relation a<b), by DP
    over down-sets.  Returns an int.  `extra` = (a, b) meaning a < b."""
    pred = [set(i for i in range(n) if less[i][j]) for j in range(n)]
    if extra is not None:
        a, b = extra
        pred[b] = pred[b] | {a}
        # transitive closure of the single added relation: anything <= a is < b,
        # and b < anything means a < it too.  Recompute reachability cheaply.
        changed = True
        while changed:
            changed = False
            for j in range(n):
                add = set()
                for i in pred[j]:
                    add |= pred[i]
                if not add <= pred[j]:
                    pred[j] |= add
                    changed = True
        for j in range(n):
            if j in pred[j]:
                return 0  # cycle: the extra relation contradicts P
    full = (1 << n) - 1
    dp = {0: 1}
    for _ in range(n):
        nxt = {}
        for mask, cnt in dp.items():
            for j in range(n):
                if mask >> j & 1:
                    continue
                if all(mask >> i & 1 for i in pred[j]):
                    nm = mask | 1 << j
                    nxt[nm] = nxt.get(nm, 0) + cnt
        dp = nxt
    return dp.get(full, 0)


def position_matrix(less, n):
    """T[i][k] = Pr[x_i lands at position k], exact rationals, via forward/backward
    down-set DP:  Pr = sum over down-sets D of size k with i minimal-addable ..."""
    pred = [frozenset(i for i in range(n) if less[i][j]) for j in range(n)]
    # forward[mask] = #ways to build the down-set `mask`
    forward = {0: 1}
    frontier = {0: 1}
    by_size = [dict() for _ in range(n + 1)]
    by_size[0][0] = 1
    for size in range(n):
        for mask, cnt in by_size[size].items():
            for j in range(n):
                if mask >> j & 1:
                    continue
                if all(mask >> i & 1 for i in pred[j]):
                    nm = mask | 1 << j
                    by_size[size + 1][nm] = by_size[size + 1].get(nm, 0) + cnt
    # backward[mask] = #ways to complete the down-set `mask` to the full set
    full = (1 << n) - 1
    back = {full: 1}
    for size in range(n, 0, -1):
        for mask, cnt in list(by_size[size].items()):
            if mask not in back:
                # completions of mask = sum over j addable
                tot = 0
                for j in range(n):
                    if mask >> j & 1:
                        continue
                    if all(mask >> i & 1 for i in pred[j]):
                        tot += back.get(mask | 1 << j, 0)
                back[mask] = tot
    for size in range(n, -1, -1):
        for mask in by_size[size]:
            if mask not in back:
                tot = 0
                for j in range(n):
                    if mask >> j & 1:
                        continue
                    if all(mask >> i & 1 for i in pred[j]):
                        tot += back.get(mask | 1 << j, 0)
                back[mask] = tot
    total = back[0]
    T = [[0 for _ in range(n)] for _ in range(n)]
    for size in range(n):
        for mask, cnt in by_size[size].items():
            for j in range(n):
                if mask >> j & 1:
                    continue
                if all(mask >> i & 1 for i in pred[j]):
                    T[j][size] += cnt * back[mask | 1 << j]
    return [[Fraction(T[i][k], total) for k in range(n)] for i in range(n)], total


def analyse(n, g):
    less = gap_poset(n, g)
    inc = [(i, j) for i in range(n) for j in range(i + 1, n)
           if not less[i][j] and not less[j][i]]
    m = len(inc)
    total = count_extensions(less, n)
    beta_max = Fraction(0)
    argmax = None
    for (a, b) in inc:
        p = Fraction(count_extensions(less, n, extra=(a, b)), total)   # Pr[x_a < x_b]
        beta = min(p, 1 - p)
        if beta > beta_max:
            beta_max, argmax = beta, (a, b)
    T, _ = position_matrix(less, n)
    S = [[(T[i][j] + T[j][i]) / 2 for j in range(n)] for i in range(n)]
    D = [[S[i][j] - Fraction(2, n) for j in range(n)] for i in range(n)]
    lam = max(eigenvalues_sym(D, n))
    EF = sum(abs(k - i) * T[i][k] for i in range(n) for k in range(n))
    d = Fraction(m, n * (n - 1) // 2)
    bound = 1 - Fraction(3, n * n - 1) * EF
    return dict(n=n, g=g, m=m, d=d, beta_max=beta_max, argmax=argmax,
                lam=lam, EF=EF, bound=float(bound), e=total)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    print(f"{'n':>3} {'g':>3} {'e(P)':>12} {'d':>7} {'beta_max':>9} {'frozen':>7} "
          f"{'lambda_std':>11} {'1-d*n/(n+1)':>12} {'footrule bd':>12}")
    for n in range(6, nmax + 1):
        for g in range(1, n + 1):
            r = analyse(n, g)
            frozen = r['beta_max'] < Fraction(1, 3)
            pred = 1 - float(r['d']) * n / (n + 1)
            print(f"{n:>3} {g:>3} {r['e']:>12} {float(r['d']):>7.3f} "
                  f"{float(r['beta_max']):>9.4f} {str(frozen):>7} {r['lam']:>11.6f} "
                  f"{pred:>12.4f} {r['bound']:>12.4f}")
        print()


if __name__ == "__main__":
    main()
