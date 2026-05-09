#!/usr/bin/env python3
"""Numerical sanity check for Stanley log-supermodularity.

For each test poset α and every pair (I, J) of lower sets of α, verify

    e(I) · e(J) ≤ e(I ∪ J) · e(I ∩ J),

where e(K) := |L(α[K])| is the number of linear extensions of the
sub-poset of α induced on K. This is Stanley 1981's
log-supermodularity inequality.

This is a brute-force numerical sanity check supporting the
independent-verification ticket mg-e22f.

Usage:
    python3 stanley_log_supermod_check.py
"""
from __future__ import annotations

import itertools
from functools import lru_cache


def transitive_closure(n: int, relations: list[tuple[int, int]]) -> list[list[bool]]:
    """Build the reflexive transitive closure leq[i][j] = (i ≤ j)."""
    leq = [[i == j for j in range(n)] for i in range(n)]
    for (a, b) in relations:
        leq[a][b] = True
    # Floyd–Warshall
    for k in range(n):
        for i in range(n):
            if leq[i][k]:
                for j in range(n):
                    if leq[k][j]:
                        leq[i][j] = True
    return leq


def lower_sets(n: int, leq: list[list[bool]]) -> list[frozenset[int]]:
    """Enumerate all lower sets (order ideals) of α."""
    out = []
    for mask in range(1 << n):
        members = [i for i in range(n) if (mask >> i) & 1]
        ok = True
        for j in members:
            for i in range(n):
                if leq[i][j] and not ((mask >> i) & 1):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append(frozenset(members))
    return out


def num_linear_extensions(K: frozenset[int], leq: list[list[bool]]) -> int:
    r"""Count linear extensions of the sub-poset of α induced on K.

    e(∅) = 1; for nonempty K, sum over maximal elements m ∈ K of
    e(K \ {m}). Memoised on the bitmask state.
    """
    K_list = sorted(K)
    n_K = len(K_list)
    if n_K == 0:
        return 1
    # bit-positions are indices into K_list
    leq_local = [[leq[K_list[i]][K_list[j]] for j in range(n_K)] for i in range(n_K)]

    @lru_cache(maxsize=None)
    def count(state: int) -> int:
        if state == 0:
            return 1
        total = 0
        for idx in range(n_K):
            if not ((state >> idx) & 1):
                continue
            # is idx maximal in `state`?
            is_max = True
            for jdx in range(n_K):
                if jdx == idx or not ((state >> jdx) & 1):
                    continue
                if leq_local[idx][jdx]:
                    is_max = False
                    break
            if is_max:
                total += count(state & ~(1 << idx))
        return total

    full = (1 << n_K) - 1
    return count(full)


def verify_poset(name: str, n: int, relations: list[tuple[int, int]]) -> dict:
    """Verify Stanley log-supermod on every (I, J) ∈ J(α) × J(α)."""
    leq = transitive_closure(n, relations)
    LS = lower_sets(n, leq)
    e_cache: dict[frozenset[int], int] = {}

    def e(K: frozenset[int]) -> int:
        if K not in e_cache:
            e_cache[K] = num_linear_extensions(K, leq)
        return e_cache[K]

    pairs = 0
    tight = 0
    violations = []
    slack_min = None
    for I in LS:
        for J in LS:
            U = I | J
            X = I & J
            lhs = e(I) * e(J)
            rhs = e(U) * e(X)
            pairs += 1
            if lhs > rhs:
                violations.append(
                    {
                        "I": sorted(I),
                        "J": sorted(J),
                        "lhs": lhs,
                        "rhs": rhs,
                    }
                )
            elif lhs == rhs:
                tight += 1
            slack = rhs - lhs
            if slack_min is None or slack < slack_min:
                slack_min = slack

    print(f"=== {name} ===")
    print(f"  |α| = {n}, |J(α)| = {len(LS)}, distinct e(K) values = {len(e_cache)}")
    print(f"  pairs (I,J) checked: {pairs}")
    print(f"  tight (e(I)e(J) = e(I∪J)e(I∩J)): {tight}")
    print(f"  violations: {len(violations)}")
    if violations:
        for v in violations:
            print(f"    VIOLATION I={v['I']} J={v['J']}  {v['lhs']} > {v['rhs']}")
    print(f"  e(α) = |L(α)| = {e(frozenset(range(n)))}")
    print()
    return {
        "name": name,
        "n": n,
        "lower_sets": len(LS),
        "pairs": pairs,
        "tight": tight,
        "violations": len(violations),
        "e_alpha": e(frozenset(range(n))),
    }


# Test posets. For relations (a,b) we mean a < b in the *cover* (we
# take transitive closure below). Vertices are 0..n-1.
POSETS = [
    # antichains
    ("3-antichain", 3, []),
    ("4-antichain", 4, []),
    ("5-antichain", 5, []),
    # chains
    ("3-chain (a<b<c)", 3, [(0, 1), (1, 2)]),
    ("4-chain (a<b<c<d)", 4, [(0, 1), (1, 2), (2, 3)]),
    # 3-vertex non-chain non-antichain (the only two up to iso)
    ("V on 3 (a<b, a<c)", 3, [(0, 1), (0, 2)]),
    ("Λ on 3 (a<c, b<c)", 3, [(0, 2), (1, 2)]),
    # 4-vertex shapes
    ("N on 4 (a<c, b<c, b<d)", 4, [(0, 2), (1, 2), (1, 3)]),
    ("Diamond on 4 (a<b, a<c, b<d, c<d)", 4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
    ("2+2 on 4 (a<b, c<d)", 4, [(0, 1), (2, 3)]),
    ("Y on 4 (a<b, a<c, a<d)", 4, [(0, 1), (0, 2), (0, 3)]),
    ("Λ on 4 (a<d, b<d, c<d)", 4, [(0, 3), (1, 3), (2, 3)]),
    # 5-vertex sample (boolean lattice 2^3 minus top? just take a small one)
    ("N on 5 (a<c, b<c, b<d, e free)", 5, [(0, 2), (1, 2), (1, 3)]),
    ("Diamond on 5 (a<b, a<c, b<d, c<d, e free)", 5, [(0, 1), (0, 2), (1, 3), (2, 3)]),
    # width-3 examples (relevant for the project's downstream use)
    ("3-antichain + chain (3+chain) on 5: a||b||c, d<e", 5,
     [(3, 4)]),
    ("Width-3 layered: {a,b,c} bottom antichain, {d} on top covering all",
     4, [(0, 3), (1, 3), (2, 3)]),
]


def main() -> None:
    summary = []
    for name, n, rels in POSETS:
        summary.append(verify_poset(name, n, rels))

    print("=" * 60)
    print("AGGREGATE SUMMARY")
    print("=" * 60)
    total_pairs = sum(s["pairs"] for s in summary)
    total_tight = sum(s["tight"] for s in summary)
    total_viol = sum(s["violations"] for s in summary)
    print(f"  posets tested:      {len(summary)}")
    print(f"  total pairs (I,J):  {total_pairs}")
    print(f"  total tight:        {total_tight}")
    print(f"  total violations:   {total_viol}")
    print()
    if total_viol == 0:
        print(
            "VERDICT: Stanley log-supermodularity holds on every (I,J) pair "
            "across every test poset. No counterexample found."
        )
    else:
        print("VERDICT: COUNTEREXAMPLE FOUND — see violations above.")


if __name__ == "__main__":
    main()
