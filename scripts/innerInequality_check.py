#!/usr/bin/env python3
"""Numerical sanity check for the single-edge inner inequality
(Brightwell 1999 §4 / Daykin-Saks 1981 Theorem 1 / Preston 1974
Theorem 5.4 inner content).

For a finite poset Q with carrier alpha, an alpha-incomparable pair
(a, b), a level k in {0, ..., |alpha|}, and an up-closed predicate
S : Finset alpha -> Prop (i.e. I subset J and S(I) implies S(J)),

    N(Q^-) * |{L in L(Q^+) : S(L_k)}|
        >=
    N(Q^+) * |{L in L(Q^-) : S(L_k)}|,

where Q^+ := addRel Q a b (taking transitive closure) is the poset Q
augmented by a < b, Q^- is Q augmented by b < a, N(R) := |L(R)| is
the number of linear extensions of R, and L_k is the level-k
initial ideal of L (the set of the first k elements of L, as a
Finset alpha).

This script supports independent-verification ticket mg-2f8c, the
parallel of mg-d731 (cellMass_AD GREEN) and mg-e22f
(stanley_log_supermod GREEN) for the fifth project axiom
`OneThird.RelationPoset.InnerInequality_axiom` (mg-87de).

Usage:
    python3 innerInequality_check.py
"""
from __future__ import annotations

import itertools
from functools import lru_cache


# ---------------------------------------------------------------------------
# Poset machinery
# ---------------------------------------------------------------------------


def transitive_closure(n: int, edges: list[tuple[int, int]]) -> list[list[bool]]:
    """Reflexive transitive closure leq[i][j] = (i <= j) given cover edges."""
    leq = [[i == j for j in range(n)] for i in range(n)]
    for (a, b) in edges:
        leq[a][b] = True
    for k in range(n):
        for i in range(n):
            if leq[i][k]:
                for j in range(n):
                    if leq[k][j]:
                        leq[i][j] = True
    return leq


def is_strict_partial(leq: list[list[bool]], n: int) -> bool:
    """Sanity: leq is reflexive and antisymmetric (transitive by construction)."""
    for i in range(n):
        if not leq[i][i]:
            return False
    for i in range(n):
        for j in range(i + 1, n):
            if leq[i][j] and leq[j][i]:
                return False
    return True


def add_edge_close(leq: list[list[bool]], n: int, a: int, b: int) -> list[list[bool]]:
    """Return a new leq with the cover edge a <= b added, then transitively closed.

    Returns None if the resulting relation is inconsistent (i.e., creates a
    cycle, meaning b <= a was already present).
    """
    new = [row[:] for row in leq]
    new[a][b] = True
    # one-shot transitive closure (only need to propagate through the new edge)
    for k in range(n):
        for i in range(n):
            if new[i][k]:
                for j in range(n):
                    if new[k][j]:
                        new[i][j] = True
    if not is_strict_partial(new, n):
        return None
    return new


def is_incomparable(leq: list[list[bool]], a: int, b: int) -> bool:
    return a != b and not leq[a][b] and not leq[b][a]


def linear_extensions(leq: list[list[bool]], n: int) -> list[tuple[int, ...]]:
    """All linear extensions of the poset with reachability matrix `leq`.

    Each is a tuple (e_0, ..., e_{n-1}) of elements of {0, ..., n-1}; for
    each i < j the relation `leq[e_j][e_i]` does NOT hold (i.e., the
    permutation respects the partial order).
    """
    out: list[tuple[int, ...]] = []

    def rec(state_mask: int, prefix: list[int]):
        if state_mask == 0:
            out.append(tuple(prefix))
            return
        for x in range(n):
            if not ((state_mask >> x) & 1):
                continue
            # x is minimal in `state_mask` iff no other element of state_mask
            # is strictly below x.
            is_min = True
            for y in range(n):
                if y == x or not ((state_mask >> y) & 1):
                    continue
                if leq[y][x]:
                    is_min = False
                    break
            if is_min:
                prefix.append(x)
                rec(state_mask & ~(1 << x), prefix)
                prefix.pop()

    rec((1 << n) - 1, [])
    return out


def initial_ideal_mask(L: tuple[int, ...], k: int) -> int:
    """Bitmask of the first k elements of L."""
    m = 0
    for i in range(k):
        m |= 1 << L[i]
    return m


# ---------------------------------------------------------------------------
# Up-closed event enumeration (monotone Boolean functions)
# ---------------------------------------------------------------------------


def enumerate_upsets(n: int) -> list[frozenset[int]]:
    """Enumerate every up-closed subset U of 2^[n], as a frozenset of bitmasks.

    An up-closed S : Finset [n] -> Prop corresponds to a set U of subsets
    such that if I in U and I subset J then J in U. Equivalently, U is an
    up-set in the Boolean lattice 2^[n].

    We enumerate by deciding membership for subsets in INCREASING size; once
    a smaller subset has been put in U, every superset is forced in.
    """
    universe = list(range(1 << n))
    universe.sort(key=lambda m: bin(m).count("1"))

    forced_in: set[int] = set()
    forced_out: set[int] = set()
    out: list[frozenset[int]] = []

    def rec(idx: int):
        if idx == len(universe):
            # Build the U as the union of forced_in
            out.append(frozenset(forced_in))
            return
        m = universe[idx]
        if m in forced_in or m in forced_out:
            rec(idx + 1)
            return
        # Branch 1: m not in U. This forces every subset of m to also be out
        # (they cannot be in U either, since if they were, m would be in U
        # by upward closure). For our process where we go from small-to-big,
        # this means: m and every subset of m must remain out. The subsets
        # were already decided in earlier levels (since they are smaller),
        # so if any subset of m is in forced_in, this branch is infeasible.
        ok_out = True
        for s in forced_in:
            if (s & m) == s and s != m:  # s subset of m, s in forced_in -> would force m in
                ok_out = False
                break
        if ok_out:
            forced_out.add(m)
            rec(idx + 1)
            forced_out.remove(m)
        # Branch 2: m in U. Forces every superset of m into U.
        new_forces: set[int] = set()
        feasible = True
        for t in universe:
            if (t & m) == m and t != m and t not in forced_in:
                if t in forced_out:
                    feasible = False
                    break
                new_forces.add(t)
        if feasible:
            forced_in.add(m)
            for t in new_forces:
                forced_in.add(t)
            rec(idx + 1)
            for t in new_forces:
                forced_in.remove(t)
            forced_in.remove(m)

    rec(0)
    return out


# ---------------------------------------------------------------------------
# Verification driver
# ---------------------------------------------------------------------------


def verify_inner_inequality_for_poset(
    name: str,
    n: int,
    edges: list[tuple[int, int]],
    upsets: list[frozenset[int]],
    verbose: bool = False,
) -> dict:
    """Verify the inner inequality on every (a, b, k, S) for the given poset Q."""
    leq = transitive_closure(n, edges)
    assert is_strict_partial(leq, n), f"poset '{name}' is not a valid partial order"

    # Find all Q-incomparable pairs (a < b lexicographically).
    incomp_pairs = [
        (a, b) for a in range(n) for b in range(a + 1, n) if is_incomparable(leq, a, b)
    ]

    instances = 0
    pairs_checked = 0
    tight = 0
    violations: list[dict] = []
    slack_min = None

    for (a, b) in incomp_pairs:
        # Build Q^+ := Q + (a -> b) and Q^- := Q + (b -> a).
        Qp_leq = add_edge_close(leq, n, a, b)
        Qm_leq = add_edge_close(leq, n, b, a)
        if Qp_leq is None or Qm_leq is None:
            # Should never happen since (a, b) is Q-incomparable.
            continue

        Lp = linear_extensions(Qp_leq, n)
        Lm = linear_extensions(Qm_leq, n)
        Np = len(Lp)
        Nm = len(Lm)

        # Pre-compute initial ideal masks for each level.
        # ideal_masks_p[L_idx][k] = bitmask of first k elements
        ideal_masks_p = [
            tuple(initial_ideal_mask(L, k) for k in range(n + 1)) for L in Lp
        ]
        ideal_masks_m = [
            tuple(initial_ideal_mask(L, k) for k in range(n + 1)) for L in Lm
        ]

        for k in range(n + 1):
            for U in upsets:
                Mp = sum(1 for masks in ideal_masks_p if masks[k] in U)
                Mm = sum(1 for masks in ideal_masks_m if masks[k] in U)
                lhs = Nm * Mp
                rhs = Np * Mm
                pairs_checked += 1
                instances += 1
                if lhs > rhs:
                    pass  # this is the GOOD direction
                elif lhs == rhs:
                    tight += 1
                else:
                    violations.append(
                        {
                            "name": name,
                            "ab": (a, b),
                            "k": k,
                            "U_size": len(U),
                            "Np": Np,
                            "Nm": Nm,
                            "Mp": Mp,
                            "Mm": Mm,
                            "lhs": lhs,
                            "rhs": rhs,
                        }
                    )
                slack = lhs - rhs
                if slack_min is None or slack < slack_min:
                    slack_min = slack

    if verbose:
        print(
            f"  [{name}] n={n} edges={edges} -> incomp_pairs={len(incomp_pairs)} "
            f"upsets={len(upsets)} levels={n + 1} -> instances={instances} "
            f"tight={tight} violations={len(violations)}"
        )

    return {
        "name": name,
        "n": n,
        "incomp_pairs": len(incomp_pairs),
        "upsets": len(upsets),
        "levels": n + 1,
        "instances": instances,
        "tight": tight,
        "violations": violations,
        "slack_min": slack_min,
    }


# Test posets. Vertex labels are 0..n-1; relations are cover edges (we
# transitively close below).  Mirrors the layout used in
# `scripts/stanley_log_supermod_check.py`, expanded to cover the
# project's downstream-relevant shapes.
POSETS = [
    # antichains
    ("3-antichain", 3, []),
    ("4-antichain", 4, []),
    ("5-antichain", 5, []),
    # chains
    ("3-chain (a<b<c)", 3, [(0, 1), (1, 2)]),
    ("4-chain (a<b<c<d)", 4, [(0, 1), (1, 2), (2, 3)]),
    # 3-vertex non-chain non-antichain
    ("V on 3 (a<b, a<c)", 3, [(0, 1), (0, 2)]),
    ("Lambda on 3 (a<c, b<c)", 3, [(0, 2), (1, 2)]),
    # 4-vertex shapes
    ("N on 4 (a<c, b<c, b<d)", 4, [(0, 2), (1, 2), (1, 3)]),
    ("Diamond on 4 (a<b, a<c, b<d, c<d)", 4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
    ("2+2 on 4 (a<b, c<d)", 4, [(0, 1), (2, 3)]),
    ("Y on 4 (a<b, a<c, a<d)", 4, [(0, 1), (0, 2), (0, 3)]),
    ("Lambda on 4 (a<d, b<d, c<d)", 4, [(0, 3), (1, 3), (2, 3)]),
    # Width-2 / width-3 layered shapes (drops headline downstream-relevant)
    (
        "Width-3 layered (a||b||c, d covers all) on 4",
        4,
        [(0, 3), (1, 3), (2, 3)],
    ),  # = Lambda on 4 (alias kept for state.md cite)
    ("3-antichain + 2-chain on 5 (a||b||c, d<e)", 5, [(3, 4)]),
    ("Width-2 antichain", 2, []),
    ("Width-2 layered (a||b, c covers both)", 3, [(0, 2), (1, 2)]),  # = Lambda on 3
    # 5-vertex sample shapes
    ("N on 5 (a<c, b<c, b<d, e free)", 5, [(0, 2), (1, 2), (1, 3)]),
    (
        "Diamond on 5 (a<b, a<c, b<d, c<d, e free)",
        5,
        [(0, 1), (0, 2), (1, 3), (2, 3)],
    ),
    # Boolean-cube-like 4-element example: 2x2 product (a<c, a<d, b<c, b<d)
    ("2x2 product (a<c, a<d, b<c, b<d)", 4, [(0, 2), (0, 3), (1, 2), (1, 3)]),
]


def main() -> None:
    print("=" * 72)
    print("InnerInequality numerical sanity check (mg-2f8c)")
    print("=" * 72)
    print()
    print(
        "For each test poset Q, each Q-incomparable pair (a, b), each level k in"
    )
    print(
        "{0, ..., |alpha|}, and each up-closed predicate S : Finset alpha -> Prop,"
    )
    print(
        "verify  N(Q^-) * |{L in L(Q^+) : S(L_k)}| >= N(Q^+) * |{L in L(Q^-) : S(L_k)}|"
    )
    print(
        "where Q^+ = addRel Q a b, Q^- = addRel Q b a (transitive closures)."
    )
    print()

    # Pre-compute up-set families for each n we test.  For n <= 4 we
    # enumerate every up-closed predicate (Dedekind D(n) families); for
    # n = 5 the count is 7581, still feasible.
    upsets_cache: dict[int, list[frozenset[int]]] = {}
    for n in sorted({n for _, n, _ in POSETS}):
        if n not in upsets_cache:
            U = enumerate_upsets(n)
            upsets_cache[n] = U
            print(f"  n={n}: enumerated {len(U)} up-closed predicates")
    print()

    summary: list[dict] = []
    for (name, n, edges) in POSETS:
        upsets = upsets_cache[n]
        result = verify_inner_inequality_for_poset(
            name, n, edges, upsets, verbose=True
        )
        summary.append(result)

    print()
    print("=" * 72)
    print("AGGREGATE SUMMARY")
    print("=" * 72)
    total_instances = sum(s["instances"] for s in summary)
    total_tight = sum(s["tight"] for s in summary)
    total_viol = sum(len(s["violations"]) for s in summary)
    total_pairs = sum(s["incomp_pairs"] for s in summary)
    print(f"  posets tested:             {len(summary)}")
    print(f"  total Q-incomparable (a,b):{total_pairs}")
    print(f"  total instances checked:   {total_instances}")
    print(f"  total tight (equality):    {total_tight}")
    print(f"  total violations:          {total_viol}")
    print()
    if total_viol == 0:
        print(
            "VERDICT: PASS.  No violation of the inner inequality found across"
        )
        print(
            "         every (Q, a, b, k, S) tested.  The single-edge inner"
        )
        print(
            "         inequality holds on every test instance."
        )
    else:
        print(
            "VERDICT: FAIL.  Violations found (lhs := N(Q-)*Mp,  rhs := N(Q+)*Mm;"
        )
        print(
            "                                    inequality requires lhs >= rhs)."
        )
        # Sort summaries by |alpha| ascending so the smallest counterexamples
        # show first (the minimal counterexample is the cleanest evidence).
        sorted_summary = sorted(summary, key=lambda s: (s["n"], s["name"]))
        printed = 0
        for s in sorted_summary:
            for v in s["violations"]:
                if printed >= 30:
                    break
                print(
                    f"  {v['name']}: a={v['ab'][0]} b={v['ab'][1]} k={v['k']} "
                    f"|U|={v['U_size']} Np={v['Np']} Nm={v['Nm']} Mp={v['Mp']} "
                    f"Mm={v['Mm']} -> lhs={v['lhs']} < rhs={v['rhs']}"
                )
                printed += 1
            if printed >= 30:
                break
        if total_viol > 30:
            print(f"  ...and {total_viol - 30} more violations omitted.")

    # Coverage breakdown.
    by_n: dict[int, list[dict]] = {}
    for s in summary:
        by_n.setdefault(s["n"], []).append(s)
    print()
    print("Coverage by |alpha|:")
    for n, rs in sorted(by_n.items()):
        ins = sum(r["instances"] for r in rs)
        tt = sum(r["tight"] for r in rs)
        vv = sum(len(r["violations"]) for r in rs)
        print(
            f"  n={n}: {len(rs)} posets, {len(upsets_cache[n])} up-set families, "
            f"{ins} instances, {tt} tight, {vv} violations"
        )


if __name__ == "__main__":
    main()
