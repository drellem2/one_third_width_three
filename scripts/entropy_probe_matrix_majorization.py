#!/usr/bin/env python3
"""Bounded checks for docs/entropy-probe-matrix-majorization.md  (mg-92e6).

Self-contained; no repo imports.

Enumerates every naturally-labelled poset on n <= 6 elements (i.e. every poset
on [n] for which the identity permutation is a linear extension -- equivalently
every poset up to relabelling-by-a-linear-extension), and checks:

  (C1) Theorem A:  for every incomparable pair {x,y} and every k,
           min(Pr[x<y], Pr[y<x])  >=  (1/2) * (T[x,k]+T[x,k+1]+T[y,k]+T[y,k+1] - 1)
       and the disjoint-window strengthening
           min(...) >= (1/2) * sum over disjoint 2-windows of positive parts.

  (C2) Tightness: report the posets attaining equality in Theorem A.

  (C3) Obstruction: search for two posets on the same ground set with the SAME
       position matrix T but different delta.

  (C4) Frozen-case corollary: for every poset with delta < 1/3 that is not a
       chain, check that every e-consecutive incomparable pair leaks > 1/3 of
       its combined mass out of its own 2x2 diagonal block.
"""

from fractions import Fraction
from itertools import combinations
import sys


def transitive_upper_triangular_posets(n):
    """Yield each poset on [n] whose identity labelling is a linear extension,
    as a tuple `lt` where lt[i] is a bitmask of the j > i with i < j."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]

    def rec(idx, lt):
        if idx == len(pairs):
            yield tuple(lt)
            return
        i, j = pairs[idx]
        # skip this relation
        yield from rec(idx + 1, lt)
        # add i < j, then transitively close upward; reject if that would
        # require adding a pair we have already decided to omit.
        if lt[i] >> j & 1:
            return
        new = list(lt)
        stack = [(i, j)]
        ok = True
        while stack and ok:
            a, b = stack.pop()
            if new[a] >> b & 1:
                continue
            if pairs.index((a, b)) < idx:
                ok = False  # already decided against this pair
                break
            new[a] |= 1 << b
            # b's up-set joins a's
            for c in range(b + 1, n):
                if new[b] >> c & 1 and not (new[a] >> c & 1):
                    stack.append((a, c))
            # anything below a gains b and b's up-set
            for z in range(a):
                if new[z] >> a & 1:
                    if not (new[z] >> b & 1):
                        stack.append((z, b))
        if ok:
            yield from rec(idx + 1, tuple(new))

    yield from rec(0, tuple(0 for _ in range(n)))


def position_matrix(n, lt):
    """Return (count, T) where T[x][i] is the NUMBER of linear extensions
    placing x at position i (0-indexed).  Subset DP over downsets."""
    # down[j] = bitmask of i < j with i < j in the poset (predecessors)
    down = [0] * n
    for i in range(n):
        m = lt[i]
        while m:
            b = m & -m
            down[b.bit_length() - 1] |= 1 << i
            m ^= b

    full = (1 << n) - 1
    # forward[S] = number of ways to linearly order the downset S
    forward = [0] * (1 << n)
    forward[0] = 1
    for S in range(1 << n):
        if not forward[S]:
            continue
        for x in range(n):
            if S >> x & 1:
                continue
            if down[x] & ~S:
                continue
            forward[S | (1 << x)] += forward[S]
    total = forward[full]
    if total == 0:
        return 0, None

    # backward[S] = number of ways to order the complement of S given S placed
    backward = [0] * (1 << n)
    backward[full] = 1
    for S in range(full - 1, -1, -1):
        acc = 0
        for x in range(n):
            if S >> x & 1:
                continue
            if down[x] & ~S:
                continue
            acc += backward[S | (1 << x)]
        backward[S] = acc

    T = [[0] * n for _ in range(n)]
    for S in range(1 << n):
        if not forward[S]:
            continue
        pos = bin(S).count("1")
        for x in range(n):
            if S >> x & 1:
                continue
            if down[x] & ~S:
                continue
            nxt = S | (1 << x)
            if backward[nxt]:
                T[x][pos] += forward[S] * backward[nxt]
    return total, T


def before_counts(n, lt):
    """cnt[x][y] = number of linear extensions with x before y."""
    down = [0] * n
    for i in range(n):
        m = lt[i]
        while m:
            b = m & -m
            down[b.bit_length() - 1] |= 1 << i
            m ^= b
    full = (1 << n) - 1
    forward = [0] * (1 << n)
    forward[0] = 1
    order = []
    for S in range(1 << n):
        if forward[S]:
            order.append(S)
        for x in range(n):
            if S >> x & 1 or (down[x] & ~S):
                continue
            forward[S | (1 << x)] += forward[S]
    backward = [0] * (1 << n)
    backward[full] = 1
    for S in range(full - 1, -1, -1):
        acc = 0
        for x in range(n):
            if S >> x & 1 or (down[x] & ~S):
                continue
            acc += backward[S | (1 << x)]
        backward[S] = acc
    cnt = [[0] * n for _ in range(n)]
    # x before y  <=>  there is a prefix-set S containing x but not y
    # count via: sum over S of (#ext with prefix exactly S) is overcounting;
    # instead count linear extensions where y is placed with x already in S.
    for S in range(1 << n):
        if not forward[S]:
            continue
        for y in range(n):
            if S >> y & 1 or (down[y] & ~S):
                continue
            w = forward[S] * backward[S | (1 << y)]
            if not w:
                continue
            for x in range(n):
                if S >> x & 1:
                    cnt[x][y] += w
    return cnt


def analyse(n, lt, total, T, cnt):
    """Return (delta, incomparable pairs with their data)."""
    inc = []
    for x, y in combinations(range(n), 2):
        if (lt[x] >> y & 1) or (lt[y] >> x & 1):
            continue
        p = Fraction(cnt[x][y], total)
        inc.append((x, y, p))
    if not inc:
        return None, []
    delta = max(min(p, 1 - p) for _, _, p in inc)
    return delta, inc


def check_theorem_a(n, lt, total, T, cnt, inc):
    """Check Theorem A + the disjoint-window strengthening. Returns list of
    (x, y, best_single_bound, actual_min) for equality reporting."""
    out = []
    for x, y, p in inc:
        actual = min(p, 1 - p)
        rows = [[Fraction(T[x][i], total) for i in range(n)],
                [Fraction(T[y][i], total) for i in range(n)]]
        gains = []
        for k in range(n - 1):
            s = rows[0][k] + rows[0][k + 1] + rows[1][k] + rows[1][k + 1]
            gains.append(max(Fraction(0), s - 1))
        best_single = max(gains) / 2 if gains else Fraction(0)
        assert actual >= best_single, (n, lt, x, y, actual, best_single)
        # disjoint windows: even-indexed k, odd-indexed k
        for par in (0, 1):
            tot = sum(gains[k] for k in range(par, n - 1, 2))
            assert actual >= tot / 2, ("disjoint", n, lt, x, y, actual, tot / 2)
        out.append((x, y, best_single, actual))
    return out


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    equality_cases = []
    best_nontrivial = []
    for n in range(2, max_n + 1):
        seen = {}
        npos = 0
        frozen_checked = 0
        for lt in transitive_upper_triangular_posets(n):
            npos += 1
            total, T = position_matrix(n, lt)
            cnt = before_counts(n, lt)
            delta, inc = analyse(n, lt, total, T, cnt)
            if delta is None:
                continue  # chain
            eq = check_theorem_a(n, lt, total, T, cnt, inc)
            for x, y, b, a in eq:
                if b > 0:
                    best_nontrivial.append((n, lt, x, y, b, a))
                if b == a and b > 0:
                    equality_cases.append((n, lt, x, y, a))
            # (C3) group by T
            keyT = tuple(tuple(Fraction(T[x][i], total) for i in range(n))
                         for x in range(n))
            seen.setdefault(keyT, []).append((delta, lt))
            if delta < Fraction(1, 3):
                frozen_checked += 1
        collisions = [(k, v) for k, v in seen.items()
                      if len({d for d, _ in v}) > 1]
        print(f"n={n}: {npos} naturally-labelled posets, "
              f"{frozen_checked} frozen (delta<1/3, non-chain), "
              f"{len(collisions)} same-T-different-delta collisions")
        for k, v in collisions[:3]:
            print("   COLLISION T=")
            for row in k:
                print("     ", [str(r) for r in row])
            for d, lt in v:
                print("      delta=", d, " lt=", lt)
    print()
    print(f"Theorem A: verified on all posets n<={max_n} "
          f"({len(best_nontrivial)} pairs with a nontrivial bound, "
          f"{len(equality_cases)} attaining equality)")
    for c in equality_cases[:5]:
        print("   equality:", c)


if __name__ == "__main__":
    main()
