#!/usr/bin/env python3
"""Numerical sanity check for the EX-7 Option (b) refined master theorem.

After mg-fd0d's trip-wire confirmed the *universal-up-closed* master
theorem `probEvent'_mono_of_subseteq_upClosed` is mathematically FALSE
(mg-2f8c: 133180 violations / 19 posets), this script verifies the
*refined* target derived from the chained-adjacent-transposition
reduction: the single-edge inner inequality

    N(Q^-) * |{L in L(Q^+) : S(L_k)}|
        >=
    N(Q^+) * |{L in L(Q^-) : S(L_k)}|

restricted to S that satisfy BOTH:

  (H1) S is up-closed (I subset J and S(I) ⇒ S(J)),
  (H2) S is *Q-mutually-directional*:
       for every Q-incomparable pair {x, y} and every K disjoint from
       {x, y}, S(K ∪ {x}) ↔ S(K ∪ {y}).

The Q-mutually-directional condition (H2) is the **symmetric** form
of mg-c8ac's `DirectionalUpClosed` `(a, b)`-directional condition: it
requires both `(x, y)`-directional AND `(y, x)`-directional for every
Q-incomparable {x, y}.  This is the strongest natural target emerging
from the chained-adjacent-transposition (Brightwell §4) reduction:

* For each single-edge step `Q → Q + (a, b)` in any chain
  `Q ⊆ Q_1 ⊆ ... ⊆ Q'`, the bubble-sort reduction within the step
  involves adjacent swaps of `(a_i, c)` for `c` Q_{i-1}-incomparable
  to `a_i`.
* At each bubble step, mg-c8ac's chamber-restricted single-edge
  inequality requires `S` to be `(a_i, c)`-directional.
* Since the decomposition (chain) is not unique and any element of α
  may be a source `a_i` in some decomposition, the universal target
  requires `S` to be `(x, c)`-directional for every pair (x, c) that
  could appear as a bubble pair, which is bounded by every Q-incomp
  ordered pair.
* Requiring `(x, y)`-directional for both orientations of a Q-incomp
  pair gives the symmetric (H2) condition.

(In Lean / mg-c8ac terms: `DirectionalUpClosed x y S ∧ DirectionalUpClosed y x S`
for every Q-incomp {x, y}.)

VERDICT criterion:
  * 0 violations on |α| ∈ {2, 3, 4, 5} ⇒ target (b) is consistent with
    the chained-adjacent-transposition reduction and admissible as
    the Session E execution target.
  * Any violation ⇒ trip-wire; the chained-adjacent-transposition
    reduction promises more than it can deliver; STOP and escalate to
    Daniel for Option (c) (axiomatize after stronger numerical
    verification) or Option (d) (architectural redesign).

This script also confirms by negation that the mg-2f8c counterexamples
(e.g., S(I) := 1 ∈ I on the 2-antichain) are *excluded* from the
(b.Q-SYMM) hypothesis envelope, providing a structural sanity check.

Usage:
    python3 innerInequalityRefined_check.py
"""
from __future__ import annotations

import itertools


# ---------------------------------------------------------------------------
# Poset machinery — same as scripts/innerInequality_check.py (mg-2f8c)
# ---------------------------------------------------------------------------


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


def is_strict_partial(leq: list[list[bool]], n: int) -> bool:
    for i in range(n):
        if not leq[i][i]:
            return False
    for i in range(n):
        for j in range(i + 1, n):
            if leq[i][j] and leq[j][i]:
                return False
    return True


def add_edge_close(leq: list[list[bool]], n: int, a: int, b: int):
    new = [row[:] for row in leq]
    new[a][b] = True
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
    out: list[tuple[int, ...]] = []

    def rec(state_mask: int, prefix: list[int]):
        if state_mask == 0:
            out.append(tuple(prefix))
            return
        for x in range(n):
            if not ((state_mask >> x) & 1):
                continue
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
    m = 0
    for i in range(k):
        m |= 1 << L[i]
    return m


# ---------------------------------------------------------------------------
# Up-closed event enumeration — same as scripts/innerInequality_check.py
# ---------------------------------------------------------------------------


def enumerate_upsets(n: int) -> list[frozenset[int]]:
    universe = list(range(1 << n))
    universe.sort(key=lambda m: bin(m).count("1"))

    forced_in: set[int] = set()
    forced_out: set[int] = set()
    out: list[frozenset[int]] = []

    def rec(idx: int):
        if idx == len(universe):
            out.append(frozenset(forced_in))
            return
        m = universe[idx]
        if m in forced_in or m in forced_out:
            rec(idx + 1)
            return
        ok_out = True
        for s in forced_in:
            if (s & m) == s and s != m:
                ok_out = False
                break
        if ok_out:
            forced_out.add(m)
            rec(idx + 1)
            forced_out.remove(m)
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
# (b.Q-SYMM) — Q-mutually-directional filter on S
# ---------------------------------------------------------------------------


def is_q_mutually_directional(
    U: frozenset[int], n: int, leq: list[list[bool]]
) -> bool:
    """Check if U (up-closed set) is Q-mutually-directional:
    for every Q-incomparable {x, y} and every K disjoint from {x, y},
    (K ∪ {x}) ∈ U ↔ (K ∪ {y}) ∈ U.
    """
    incomp_pairs = [
        (x, y) for x in range(n) for y in range(x + 1, n) if is_incomparable(leq, x, y)
    ]
    full_mask = (1 << n) - 1
    for (x, y) in incomp_pairs:
        forbid_xy = (1 << x) | (1 << y)
        # iterate K_mask over subsets of α \ {x, y}
        K_universe = full_mask & ~forbid_xy
        # enumerate all subsets of K_universe
        K_mask = K_universe
        while True:
            # K_mask is a subset of K_universe
            Kx = K_mask | (1 << x)
            Ky = K_mask | (1 << y)
            if (Kx in U) != (Ky in U):
                return False
            if K_mask == 0:
                break
            K_mask = (K_mask - 1) & K_universe
    return True


def is_q_directional_one_dir(
    U: frozenset[int], n: int, leq: list[list[bool]], a: int, b: int
) -> bool:
    """Check if U is (a, b)-directional (one direction only):
    for every K disjoint from {a, b}, (K ∪ {b}) ∈ U → (K ∪ {a}) ∈ U.
    """
    full_mask = (1 << n) - 1
    forbid_ab = (1 << a) | (1 << b)
    K_universe = full_mask & ~forbid_ab
    K_mask = K_universe
    while True:
        Kb = K_mask | (1 << b)
        Ka = K_mask | (1 << a)
        if (Kb in U) and not (Ka in U):
            return False
        if K_mask == 0:
            break
        K_mask = (K_mask - 1) & K_universe
    return True


# ---------------------------------------------------------------------------
# Verification driver: per-poset Q-SYMM inner-inequality check
# ---------------------------------------------------------------------------


def verify_refined_inner_inequality(
    name: str,
    n: int,
    edges: list[tuple[int, int]],
    upsets: list[frozenset[int]],
    verbose: bool = False,
) -> dict:
    """For each (a, b) Q-incomparable, each level k, each (b.Q-SYMM) up-closed S,
    verify the single-edge inner inequality N(Q^-) * Mp >= N(Q^+) * Mm.
    """
    leq = transitive_closure(n, edges)
    assert is_strict_partial(leq, n), f"poset '{name}' is not a valid partial order"

    # Filter upsets to Q-mutually-directional.
    upsets_qsymm = [U for U in upsets if is_q_mutually_directional(U, n, leq)]

    incomp_pairs = [
        (a, b) for a in range(n) for b in range(a + 1, n) if is_incomparable(leq, a, b)
    ]

    instances = 0
    tight = 0
    violations: list[dict] = []

    for (a, b) in incomp_pairs:
        Qp_leq = add_edge_close(leq, n, a, b)
        Qm_leq = add_edge_close(leq, n, b, a)
        if Qp_leq is None or Qm_leq is None:
            continue

        Lp = linear_extensions(Qp_leq, n)
        Lm = linear_extensions(Qm_leq, n)
        Np = len(Lp)
        Nm = len(Lm)

        ideal_masks_p = [
            tuple(initial_ideal_mask(L, k) for k in range(n + 1)) for L in Lp
        ]
        ideal_masks_m = [
            tuple(initial_ideal_mask(L, k) for k in range(n + 1)) for L in Lm
        ]

        for k in range(n + 1):
            for U in upsets_qsymm:
                Mp = sum(1 for masks in ideal_masks_p if masks[k] in U)
                Mm = sum(1 for masks in ideal_masks_m if masks[k] in U)
                lhs = Nm * Mp
                rhs = Np * Mm
                instances += 1
                if lhs == rhs:
                    tight += 1
                elif lhs < rhs:
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

    if verbose:
        print(
            f"  [{name}] n={n} -> incomp_pairs={len(incomp_pairs)} "
            f"upsets_total={len(upsets)} upsets_qsymm={len(upsets_qsymm)} "
            f"instances={instances} tight={tight} violations={len(violations)}"
        )

    return {
        "name": name,
        "n": n,
        "incomp_pairs": len(incomp_pairs),
        "upsets_total": len(upsets),
        "upsets_qsymm": len(upsets_qsymm),
        "instances": instances,
        "tight": tight,
        "violations": violations,
    }


# ---------------------------------------------------------------------------
# mg-2f8c counterexample exclusion check (sanity probe)
# ---------------------------------------------------------------------------


def check_mg_2f8c_exclusion() -> bool:
    """Verify that the mg-2f8c minimal counterexample S(I) := 1 ∈ I on the
    2-element antichain is *excluded* by the (b.Q-SYMM) hypothesis filter.
    """
    n = 2
    leq = transitive_closure(n, [])  # empty 2-antichain
    # S(I) := 1 ∈ I; encoded as the set of bitmasks containing bit 1.
    S_2f8c = frozenset({0b10, 0b11})  # subsets {1} and {0, 1}
    # Check up-closedness (sanity).
    is_upclosed = all(
        not (((s & t) == s) and (s in S_2f8c) and (t not in S_2f8c))
        for s in range(1 << n)
        for t in range(1 << n)
    )
    assert is_upclosed, "mg-2f8c S should be up-closed"
    # Check (b.Q-SYMM): should be FALSE since S({0}) = ⊥ but S({1}) = ⊤
    # and {0, 1} is Q-incomparable on the empty 2-antichain.
    is_qsymm = is_q_mutually_directional(S_2f8c, n, leq)
    return not is_qsymm  # exclusion ⇒ NOT Q-symmetric


# ---------------------------------------------------------------------------
# Consumer event directionality probe (EX-8 + EX-9 re-audit)
# ---------------------------------------------------------------------------


def check_consumer_event_directionality():
    """Probe: for the EX-8 case3 witness event S(L_k) := x ∈ L_k and the
    EX-9 Brightwell §4 indicator family, check whether they satisfy
    (b.Q-SYMM) on a representative test poset.

    For EX-8: encode S_x(I) := (x ∈ I) on |α|=3 case3 antichain.
    For each Q-incomp pair {y, z}: S_x is Q-symmetric iff x ∉ {y, z}.
    Since the case3 chain ranges (x, y) over A × A, the witness x will
    appear as one element of some Q-incomp pair, breaking Q-symmetry.

    For EX-9: encode a simplified version of Brightwell §4's `1_A` family
    `S(I) := T ⊆ I` for T = a specific subset.  Check Q-symmetric for
    various T.
    """
    print()
    print("Consumer event directionality probe (EX-8 + EX-9):")
    print()

    # EX-8: case3 antichain on |α| = 3, S_x(I) := (x ∈ I) for each x.
    n = 3
    leq = transitive_closure(n, [])  # 3-antichain
    incomp_pairs = [
        (x, y) for x in range(n) for y in range(x + 1, n) if is_incomparable(leq, x, y)
    ]
    print(f"  EX-8 setup: |α| = {n}, Q = empty antichain, Q-incomp pairs = {incomp_pairs}")
    print(f"             Event family: S_x(I) := (x ∈ I) for x ∈ {{0, 1, 2}}.")
    for x in range(n):
        S = frozenset(m for m in range(1 << n) if (m >> x) & 1)
        is_qsymm = is_q_mutually_directional(S, n, leq)
        # Check directional for each (a, b) ordered pair
        dir_pairs = []
        for (a, b) in incomp_pairs:
            d_ab = is_q_directional_one_dir(S, n, leq, a, b)
            d_ba = is_q_directional_one_dir(S, n, leq, b, a)
            dir_pairs.append(((a, b), d_ab, d_ba))
        print(
            f"    S_{x}(I) := ({x} ∈ I): Q-symm = {is_qsymm} ; per-pair (a,b)-dir, (b,a)-dir:"
        )
        for (p, d_ab, d_ba) in dir_pairs:
            print(f"        pair {p}: (a,b)-dir = {d_ab}, (b,a)-dir = {d_ba}")

    print()
    # EX-9: Brightwell §4 indicator family proxy. Use `S(I) := T ⊆ I` for various T.
    n = 4
    leq = transitive_closure(n, [])  # 4-antichain
    incomp_pairs = [
        (x, y) for x in range(n) for y in range(x + 1, n) if is_incomparable(leq, x, y)
    ]
    print(
        f"  EX-9 setup: |α| = {n}, Q = empty antichain (proxy for τ-inversion lattice)."
    )
    print(f"             Event family: S_T(I) := (T ⊆ I) for various T.")
    test_Ts = [frozenset(), frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})]
    for T in test_Ts:
        T_mask = 0
        for t in T:
            T_mask |= 1 << t
        S = frozenset(m for m in range(1 << n) if (m & T_mask) == T_mask)
        is_qsymm = is_q_mutually_directional(S, n, leq)
        print(f"    S_T(I) := (T ⊆ I), T = {sorted(T)}: Q-symm = {is_qsymm}")


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


POSETS = [
    ("3-antichain", 3, []),
    ("4-antichain", 4, []),
    ("5-antichain", 5, []),
    ("3-chain (a<b<c)", 3, [(0, 1), (1, 2)]),
    ("4-chain (a<b<c<d)", 4, [(0, 1), (1, 2), (2, 3)]),
    ("V on 3 (a<b, a<c)", 3, [(0, 1), (0, 2)]),
    ("Lambda on 3 (a<c, b<c)", 3, [(0, 2), (1, 2)]),
    ("N on 4 (a<c, b<c, b<d)", 4, [(0, 2), (1, 2), (1, 3)]),
    ("Diamond on 4 (a<b, a<c, b<d, c<d)", 4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
    ("2+2 on 4 (a<b, c<d)", 4, [(0, 1), (2, 3)]),
    ("Y on 4 (a<b, a<c, a<d)", 4, [(0, 1), (0, 2), (0, 3)]),
    ("Lambda on 4 (a<d, b<d, c<d)", 4, [(0, 3), (1, 3), (2, 3)]),
    (
        "Width-3 layered (a||b||c, d covers all) on 4",
        4,
        [(0, 3), (1, 3), (2, 3)],
    ),
    ("3-antichain + 2-chain on 5 (a||b||c, d<e)", 5, [(3, 4)]),
    ("Width-2 antichain", 2, []),
    ("Width-2 layered (a||b, c covers both)", 3, [(0, 2), (1, 2)]),
    ("N on 5 (a<c, b<c, b<d, e free)", 5, [(0, 2), (1, 2), (1, 3)]),
    (
        "Diamond on 5 (a<b, a<c, b<d, c<d, e free)",
        5,
        [(0, 1), (0, 2), (1, 3), (2, 3)],
    ),
    ("2x2 product (a<c, a<d, b<c, b<d)", 4, [(0, 2), (0, 3), (1, 2), (1, 3)]),
]


def main() -> None:
    print("=" * 72)
    print("EX-7 Option (b) refined inner inequality numerical sanity check")
    print("                                                          (mg-a1aa)")
    print("=" * 72)
    print()
    print(
        "For each test poset Q, each Q-incomparable pair (a, b), each level k,"
    )
    print(
        "and each up-closed S that is Q-mutually-directional [i.e., for every"
    )
    print(
        "Q-incomp {x, y} and every K avoiding {x, y}, S(K∪{x}) ↔ S(K∪{y})],"
    )
    print(
        "verify  N(Q^-) * |{L in L(Q^+): S(L_k)}| >= N(Q^+) * |{L in L(Q^-): S(L_k)}|."
    )
    print()

    # mg-2f8c exclusion sanity check.
    excluded = check_mg_2f8c_exclusion()
    print(
        f"  mg-2f8c counterexample S(I) := (1 ∈ I) excluded by (b.Q-SYMM)? {excluded}"
    )
    print()

    # Pre-compute up-set families.
    upsets_cache: dict[int, list[frozenset[int]]] = {}
    for n in sorted({n for _, n, _ in POSETS}):
        if n not in upsets_cache:
            U = enumerate_upsets(n)
            upsets_cache[n] = U
            print(f"  n={n}: enumerated {len(U)} up-closed predicates (total)")
    print()

    summary: list[dict] = []
    for (name, n, edges) in POSETS:
        upsets = upsets_cache[n]
        result = verify_refined_inner_inequality(name, n, edges, upsets, verbose=True)
        summary.append(result)

    print()
    print("=" * 72)
    print("AGGREGATE SUMMARY")
    print("=" * 72)
    total_instances = sum(s["instances"] for s in summary)
    total_tight = sum(s["tight"] for s in summary)
    total_viol = sum(len(s["violations"]) for s in summary)
    total_pairs = sum(s["incomp_pairs"] for s in summary)
    print(f"  posets tested:              {len(summary)}")
    print(f"  total Q-incomparable (a,b): {total_pairs}")
    print(f"  total instances checked:    {total_instances}")
    print(f"  total tight (equality):     {total_tight}")
    print(f"  total violations:           {total_viol}")
    print()
    if total_viol == 0:
        print("VERDICT: PASS.  No violation found across every (Q, a, b, k, S)")
        print("         tested.  The (b.Q-SYMM) refined target is consistent")
        print("         with the chained-adjacent-transposition reduction.")
    else:
        print("VERDICT: FAIL.  Violations found (trip-wire).")
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

    by_n: dict[int, list[dict]] = {}
    for s in summary:
        by_n.setdefault(s["n"], []).append(s)
    print()
    print("Coverage by |α|:")
    for n, rs in sorted(by_n.items()):
        ins = sum(r["instances"] for r in rs)
        tt = sum(r["tight"] for r in rs)
        vv = sum(len(r["violations"]) for r in rs)
        sym_avg = sum(r["upsets_qsymm"] for r in rs) / len(rs) if rs else 0
        print(
            f"  n={n}: {len(rs)} posets, avg {sym_avg:.1f} Q-symm up-sets/poset, "
            f"{ins} instances, {tt} tight, {vv} violations"
        )

    # Consumer probe
    check_consumer_event_directionality()


if __name__ == "__main__":
    main()
