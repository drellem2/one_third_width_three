#!/usr/bin/env python3
"""Consumer-specific probe for EX-7 Option (b) refined target.

Following the (b.Q-SYMM) verifier (innerInequalityRefined_check.py),
which showed 0 violations but ALL instances TIGHT (i.e., the universal
Q-symmetric refined target gives a vacuous always-equality), this
script tests *weaker, decomposition-dependent* candidates:

(b.SOURCE-DIR):  S is up-closed AND for every source `a ∈ Sources(Q ⊆ Q')`
                 (i.e., a is the source of some added edge a → b in Q' \\ Q)
                 and every `c` Q-incomparable to `a`,
                 `S(K ∪ {c}) → S(K ∪ {a})` (one direction only).

For this target to be useful for the EX-8 case3-port-2 consumer, the
case3 witness events S_x(I) := (x ∈ I) must satisfy (b.SOURCE-DIR) on
the case3 chain Q ⊆ Q'.  This probe:

1. Constructs the case3-port-2 setup: Q on n=4 (the 3-antichain
   {a_1, a_2, a_3} plus one auxiliary element to give some structure;
   or simply the bare 3-antichain on n=3), Q' adding edges within A.
2. For each candidate witness x ∈ A and each Q ⊆ Q', filters up-closed
   S to those satisfying (b.SOURCE-DIR) and checks whether the witness
   event S_x is among them.
3. Also probes the EX-9 Brightwell §4 indicator family on a tau-inversion
   product lattice proxy.

Output: a structured report showing which (witness, chain) combinations
admit S_x as (b.SOURCE-DIR), and which fail.
"""
from __future__ import annotations

import itertools


def transitive_closure(n: int, edges: list[tuple[int, int]]) -> list[list[bool]]:
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


def is_incomparable(leq: list[list[bool]], a: int, b: int) -> bool:
    return a != b and not leq[a][b] and not leq[b][a]


def is_a_c_directional(
    U: frozenset[int], n: int, a: int, c: int
) -> bool:
    """Check `S(K ∪ {c}) → S(K ∪ {a})` for all K disjoint from {a, c}."""
    full_mask = (1 << n) - 1
    forbid = (1 << a) | (1 << c)
    K_universe = full_mask & ~forbid
    K_mask = K_universe
    while True:
        Kc = K_mask | (1 << c)
        Ka = K_mask | (1 << a)
        if (Kc in U) and not (Ka in U):
            return False
        if K_mask == 0:
            break
        K_mask = (K_mask - 1) & K_universe
    return True


def encode_event_x_in_I(x: int, n: int) -> frozenset[int]:
    """S(I) := (x ∈ I) — bit-x set in mask."""
    return frozenset(m for m in range(1 << n) if (m >> x) & 1)


def encode_event_T_subset_I(T: frozenset[int], n: int) -> frozenset[int]:
    """S(I) := (T ⊆ I) — every bit in T set in mask."""
    T_mask = 0
    for t in T:
        T_mask |= 1 << t
    return frozenset(m for m in range(1 << n) if (m & T_mask) == T_mask)


def case3_setup() -> None:
    """EX-8 case3-port-2 setup.

    The case3 dispatch (mg-75ef §3) operates on a width-3 antichain
    A = {a_1, a_2, a_3} embedded in a larger poset α.  For the bare
    structural analysis, we take α = A (n = 3, Q = empty 3-antichain).

    The case3 chain Q ⊆ Q' adds edges within A — e.g., Q' = Q + (a_0 < a_1)
    + (a_1 < a_2) or various other configurations forced by case3's
    L1/L2 dispatch.  The witness pair (x, y) is drawn from A.
    """
    print()
    print("=" * 72)
    print("EX-8 case3-port-2 probe: bare 3-antichain on A = {a_0, a_1, a_2}")
    print("=" * 72)

    n = 3
    leq_Q = transitive_closure(n, [])  # Q = empty 3-antichain

    # Sample case3 chains (Q' specifications).  Sources is the set of a_i in
    # the added edges (a_i < b_i).
    chains = [
        ("Q' = Q + (a_0 < a_1)", [(0, 1)], {0}),
        ("Q' = Q + (a_0 < a_1) + (a_1 < a_2)", [(0, 1), (1, 2)], {0, 1}),
        ("Q' = Q + (a_0 < a_2) + (a_1 < a_2)", [(0, 2), (1, 2)], {0, 1}),
        ("Q' = Q + (a_0 < a_1) + (a_0 < a_2)", [(0, 1), (0, 2)], {0}),
        ("Q' = all 3 edges (case3 full)", [(0, 1), (0, 2), (1, 2)], {0, 1}),
    ]

    for (label, extra_edges, sources) in chains:
        print(f"\n  {label}")
        print(f"    sources = {sorted(sources)}")

        for x in range(n):
            S_x = encode_event_x_in_I(x, n)
            # Check (b.SOURCE-DIR): for every a ∈ sources, every c Q-incomp to a,
            # is S_x (a, c)-directional?
            failures = []
            for a in sources:
                for c in range(n):
                    if c == a:
                        continue
                    if not is_incomparable(leq_Q, a, c):
                        continue
                    if not is_a_c_directional(S_x, n, a, c):
                        failures.append((a, c))
            verdict = "OK" if not failures else f"FAIL on pairs {failures}"
            print(
                f"    Witness x = {x}: S_x(I) := ({x} ∈ I) — (b.SOURCE-DIR) = {verdict}"
            )


def brightwell_setup() -> None:
    """EX-9 Brightwell-port-A probe (simplified proxy).

    Brightwell §4 applies `four_functions_theorem` to monotone functions
    on the tau-inversion product lattice (L(α), ≤_τ) × ({1, ..., m}, ≤).
    We use a bare 4-antichain as a structural proxy.  For each `S_T(I)
    := T ⊆ I`, check whether (b.SOURCE-DIR) holds under various source
    sets.

    The point: Brightwell §4's argument doesn't specify a "source" set —
    AD's symmetric-pair structure applies to all monotone functions over
    the full algebra.  Restricting to a directional sub-algebra (any
    source set) structurally breaks the argument.
    """
    print()
    print("=" * 72)
    print("EX-9 Brightwell-port-A probe: 4-antichain proxy")
    print("=" * 72)

    n = 4
    leq_Q = transitive_closure(n, [])
    # Try various source sets.
    source_options = [
        ("Sources = ∅ (trivial)", set()),
        ("Sources = {0}", {0}),
        ("Sources = {0, 1}", {0, 1}),
        ("Sources = full {0, 1, 2, 3}", {0, 1, 2, 3}),
    ]

    test_Ts = [
        frozenset(),
        frozenset({0}),
        frozenset({1}),
        frozenset({0, 1}),
        frozenset({0, 2}),
        frozenset({0, 1, 2}),
    ]

    for (label, sources) in source_options:
        print(f"\n  {label}")
        for T in test_Ts:
            S_T = encode_event_T_subset_I(T, n)
            failures = []
            for a in sources:
                for c in range(n):
                    if c == a:
                        continue
                    if not is_incomparable(leq_Q, a, c):
                        continue
                    if not is_a_c_directional(S_T, n, a, c):
                        failures.append((a, c))
            verdict = "OK" if not failures else f"FAIL on pairs {failures}"
            print(
                f"    S_T(I) := (T ⊆ I), T = {sorted(T)}: (b.SOURCE-DIR) = {verdict}"
            )


if __name__ == "__main__":
    case3_setup()
    brightwell_setup()
    print()
    print("=" * 72)
    print("INTERPRETATION")
    print("=" * 72)
    print()
    print("• If S_x is (b.SOURCE-DIR)-compatible for the chain's source set:")
    print("  the refined target (b.SOURCE-DIR) admits the consumer event.")
    print("• If S_x FAILS: the chain's bubble-sort step (a, c) requires")
    print("  S to be (a, c)-directional, which S_x violates whenever c = x.")
    print("  This means the chained-adjacent-transposition reduction cannot")
    print("  inject (b.SOURCE-DIR)-S along the consumer chain → the refined")
    print("  target does NOT cover the consumer's structural pattern.")
