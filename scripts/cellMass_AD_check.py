#!/usr/bin/env python3
"""Numerical sanity check for the cell-AD lemma (Ahlswede-Daykin 1979 Lemma 2).

For non-negative `f₁, f₂, f₃, f₄` on `(Fin F)^n` satisfying the pointwise
four-function inequality

    f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y)        (∀ x, y ∈ (Fin F)^n)

with `⊓, ⊔` componentwise min / max, the cell-summed values

    M_i^{(N)}(p) := Σ_{x ∈ C_p^{F → N}} f_i(x)

over the half-open block partition `C_p` of `(Fin F)^n` into `N^n` cells
(with `F = N · S` for some `S ≥ 1`) satisfy the **same** four-function
inequality on the coarser lattice `(Fin N)^n`:

    M_1^{(N)}(p) M_2^{(N)}(q) ≤ M_3^{(N)}(p ⊓ q) M_4^{(N)}(p ⊔ q).

This is the **literature-standard "cell averages preserve AD" lemma**
(Ahlswede–Daykin 1979 §2 Lemma 2 / Preston 1974 Thm 5.4 inner content /
Brightwell 1999 §4.2 averaging step), which is the substantive content
of `OneThird.ContinuousFKG.cellMass_AD` (lean/AXIOMS.md, fourth project
axiom).

The continuous version follows by Riemann-sum approximation: any
non-negative integrable `f` on `[0,1]^n` is the limit (in L¹) of its
fine-grid sampler `f_F`, and `cellMass N f p ≈ (1/F^n) Σ_{x ∈ C_p^{F→N}}
f_F(x)` up to an O(1/F) error. So a violation in the continuous version
would imply a violation in the discrete version at sufficiently large
F — i.e., the discrete sanity check is a faithful witness for the
continuous statement.

This script supports independent-verification ticket mg-d731 (cellMass_AD).

Usage:
    python3 cellMass_AD_check.py
"""
from __future__ import annotations

import itertools
import random
from fractions import Fraction
from typing import Callable, Iterable

# Use Fraction throughout to avoid floating-point ambiguity in tight cases.
NumT = Fraction


def meet(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(min(a, b) for a, b in zip(x, y))


def join(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(max(a, b) for a, b in zip(x, y))


def grid(n: int, F: int) -> Iterable[tuple[int, ...]]:
    return itertools.product(range(F), repeat=n)


def verify_pointwise_AD(
    f1: dict, f2: dict, f3: dict, f4: dict, n: int, F: int
) -> tuple[bool, tuple | None]:
    """Check f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y) on the grid (Fin F)^n."""
    points = list(grid(n, F))
    for x in points:
        for y in points:
            lhs = f1[x] * f2[y]
            rhs = f3[meet(x, y)] * f4[join(x, y)]
            if lhs > rhs:
                return False, (x, y, lhs, rhs)
    return True, None


def cell_mass(f: dict, n: int, F: int, N: int, p: tuple[int, ...]) -> NumT:
    """Sum f over the cell C_p = ∏_i [p_i · S, (p_i+1) · S) where F = N · S."""
    assert F % N == 0, f"F={F} not divisible by N={N}"
    S = F // N
    total: NumT = Fraction(0)
    base = tuple(p[i] * S for i in range(n))
    for offs in itertools.product(range(S), repeat=n):
        idx = tuple(base[i] + offs[i] for i in range(n))
        total += f[idx]
    return total


def verify_cell_AD(
    f1: dict, f2: dict, f3: dict, f4: dict, n: int, F: int, N: int
) -> tuple[int, int]:
    """Check cell-AD on (Fin N)^n; returns (pairs, violations)."""
    # Pre-compute cell masses.
    M1 = {p: cell_mass(f1, n, F, N, p) for p in grid(n, N)}
    M2 = {p: cell_mass(f2, n, F, N, p) for p in grid(n, N)}
    M3 = {p: cell_mass(f3, n, F, N, p) for p in grid(n, N)}
    M4 = {p: cell_mass(f4, n, F, N, p) for p in grid(n, N)}
    pairs = 0
    violations = 0
    for p in grid(n, N):
        for q in grid(n, N):
            pairs += 1
            lhs = M1[p] * M2[q]
            rhs = M3[meet(p, q)] * M4[join(p, q)]
            if lhs > rhs:
                violations += 1
                print(f"  VIOLATION at p={p}, q={q}: lhs={lhs} > rhs={rhs}")
    return pairs, violations


# -----------------------------------------------------------------------------
# Test-instance generators
# -----------------------------------------------------------------------------


def instance_constant(n: int, F: int, c: int = 1) -> tuple[dict, dict, dict, dict]:
    """f_i ≡ c.  AD trivially: c·c ≤ c·c."""
    val = Fraction(c)
    f = {x: val for x in grid(n, F)}
    return f, dict(f), dict(f), dict(f)


def instance_log_supermod_pairwise(
    n: int, F: int, c: int = 1
) -> tuple[dict, dict, dict, dict]:
    """f_i(x) := exp(c · Σ_{i<j} x_i x_j) (in rational form via product).

    Sum-of-pairwise-products is supermodular on (Fin F)^n; exponential of
    supermodular is log-supermod, which is the f₁ = f₂ = f₃ = f₄ AD case.

    Use rationals: f(x) := ∏_{i<j} 2^{c · x_i · x_j}.  Bigger ⊔ ⊓ values
    drive the exponent up super-additively, giving log-supermod.
    """
    def val(x):
        e = sum(x[i] * x[j] for i in range(n) for j in range(i + 1, n))
        return Fraction(2 ** (c * e))
    f = {x: val(x) for x in grid(n, F)}
    return f, dict(f), dict(f), dict(f)


def instance_sublattice_indicator(
    n: int, F: int, kind: str = "subcube"
) -> tuple[dict, dict, dict, dict]:
    """f_i ≡ 1_S for a sublattice S ⊆ (Fin F)^n.

    Sublattices include: lower sets, upper sets, sub-cubes, "diagonal" sets.
    Polytope indicators 1_{O(Q)} of order polytopes are the project's
    motivating example (sublattice but NOT cube-monotone).
    """
    if kind == "subcube":
        # S = {x : x_i ≤ a_i for all i} (lower-cube); upper bound varies per coord.
        a = [F // 2 + (i % 2) for i in range(n)]
        S = {x for x in grid(n, F) if all(x[i] <= a[i] for i in range(n))}
    elif kind == "lower_set_diag":
        # S = {x : x_0 ≤ x_1 ≤ ...} — sublattice (closed under ⊓, ⊔).
        S = {x for x in grid(n, F) if all(x[i] <= x[i + 1] for i in range(n - 1))}
    elif kind == "polytope_2chain":
        # Order polytope of 2-chain (a < b): O(Q) = {(x_a, x_b) : x_a ≤ x_b}.
        # Sublattice but not cube-monotone (taking componentwise max can break ≤).
        if n != 2:
            raise ValueError("polytope_2chain only defined for n=2")
        S = {x for x in grid(n, F) if x[0] <= x[1]}
    elif kind == "polytope_V":
        # Order polytope of V (a < c, b < c): {(x_a, x_b, x_c) : x_a, x_b ≤ x_c}.
        if n != 3:
            raise ValueError("polytope_V only defined for n=3")
        S = {x for x in grid(n, F) if x[0] <= x[2] and x[1] <= x[2]}
    elif kind == "polytope_Lambda":
        # Order polytope of Λ (a < b, a < c): {(x_a, x_b, x_c) : x_a ≤ x_b, x_a ≤ x_c}.
        if n != 3:
            raise ValueError("polytope_Lambda only defined for n=3")
        S = {x for x in grid(n, F) if x[0] <= x[1] and x[0] <= x[2]}
    elif kind == "polytope_3chain":
        # O(a < b < c) = {x_a ≤ x_b ≤ x_c}.
        if n != 3:
            raise ValueError("polytope_3chain only defined for n=3")
        S = {x for x in grid(n, F) if x[0] <= x[1] and x[1] <= x[2]}
    elif kind == "polytope_diamond":
        # Diamond on 4: a < b, a < c, b < d, c < d.
        # O(diamond) = {(x_a, x_b, x_c, x_d) : x_a ≤ x_b, x_a ≤ x_c, x_b ≤ x_d, x_c ≤ x_d}.
        if n != 4:
            raise ValueError("polytope_diamond only defined for n=4")
        S = {x for x in grid(n, F)
             if x[0] <= x[1] and x[0] <= x[2] and x[1] <= x[3] and x[2] <= x[3]}
    else:
        raise ValueError(f"unknown sublattice kind {kind}")
    f = {x: (Fraction(1) if x in S else Fraction(0)) for x in grid(n, F)}
    return f, dict(f), dict(f), dict(f)


def instance_random_4tuple(
    n: int, F: int, seed: int, max_val: int = 5
) -> tuple[dict, dict, dict, dict]:
    """Random non-negative f₁, f₂, f₃, f₄ satisfying pointwise AD.

    Construction: pick f₁, f₂ ≥ 0 randomly with values in [0, max_val];
    set f₃ ≡ f₄ ≡ M := max_val (a global constant upper bound).  Then
        f₁(x) f₂(y) ≤ max_val² = f₃(x⊓y) f₄(x⊔y),
    pointwise everywhere — a non-trivial 4-tuple with f₁ ≠ f₂ that
    satisfies the AD hypothesis on the nose, regardless of the random
    samples.  Useful for stress-testing the cell-AD conclusion on
    arbitrary spatially-varying f₁, f₂.
    """
    rng = random.Random(seed)
    f1 = {x: Fraction(rng.randint(0, max_val)) for x in grid(n, F)}
    f2 = {x: Fraction(rng.randint(0, max_val)) for x in grid(n, F)}
    M = Fraction(max_val)
    f3 = {x: M for x in grid(n, F)}
    f4 = dict(f3)
    return f1, f2, f3, f4


def instance_random_logsupermod(
    n: int, F: int, seed: int
) -> tuple[dict, dict, dict, dict]:
    """f₁ = f₂ = f₃ = f₄ := exp(supermod), where the supermodular
    function is built as a random non-neg linear combination of
    coordinate-pair products `x_i * x_j` plus coordinatewise terms.

    For non-neg coefs c_{ij} ≥ 0 and c_i,
        φ(x) := Σ c_i x_i + Σ_{i<j} c_{ij} x_i x_j
    is supermodular on (Fin F)^n (every monomial is supermod or modular,
    and non-neg combinations preserve supermod), so f := 2^φ is
    log-supermod, satisfying f(x) f(y) ≤ f(x⊓y) f(x⊔y).
    """
    rng = random.Random(seed)
    coef_lin = [rng.randint(0, 2) for _ in range(n)]
    coef_quad = [[rng.randint(0, 2) for _ in range(n)] for _ in range(n)]
    def phi(x):
        v = sum(coef_lin[i] * x[i] for i in range(n))
        v += sum(coef_quad[i][j] * x[i] * x[j]
                 for i in range(n) for j in range(i + 1, n))
        return v
    f = {x: Fraction(2 ** phi(x)) for x in grid(n, F)}
    return f, dict(f), dict(f), dict(f)


def instance_distinct_4tuple_chain(
    n: int, F: int
) -> tuple[dict, dict, dict, dict]:
    """A distinct (f₁, f₂, f₃, f₄)-quadruple where AD is non-trivial.

    Take f_i(x) := a_i + b_i · (Σ x_j) for non-negative coefficients
    chosen so that the pointwise AD holds via direct algebra:
        f₁ = c,           f₂ = c,
        f₃(x) = c + (Σ x_j),    f₄(x) = c + (Σ x_j).
    Pointwise AD: c² ≤ (c + Σ(x⊓y)) · (c + Σ(x⊔y)).  Since
    Σ(x⊓y) + Σ(x⊔y) = Σ x + Σ y, AM-GM gives
        (c + Σ(x⊓y))(c + Σ(x⊔y)) ≥ (c + (Σx + Σy)/2)² ≥ c².

    This gives a four-tuple with f₁ = f₂ ≠ f₃ = f₄, varying spatially
    on the cube — a genuinely distinct test case from the symmetric ones.
    """
    c = Fraction(1)
    f1 = {x: c for x in grid(n, F)}
    f2 = dict(f1)
    f3 = {x: c + Fraction(sum(x)) for x in grid(n, F)}
    f4 = dict(f3)
    return f1, f2, f3, f4


# -----------------------------------------------------------------------------
# Driver
# -----------------------------------------------------------------------------


def run_test(
    name: str,
    instance_factory: Callable,
    n: int,
    F: int,
    Ns: list[int],
    skip_pointwise: bool = False,
) -> dict:
    f1, f2, f3, f4 = instance_factory(n, F)

    if not skip_pointwise:
        ok, witness = verify_pointwise_AD(f1, f2, f3, f4, n, F)
        if not ok:
            print(f"  [{name}] POINTWISE AD VIOLATED: {witness}")
            return {"name": name, "n": n, "F": F, "ok_pointwise": False,
                    "results": {}}

    results = {}
    total_pairs = 0
    total_viol = 0
    for N in Ns:
        if F % N != 0:
            continue
        pairs, violations = verify_cell_AD(f1, f2, f3, f4, n, F, N)
        results[N] = (pairs, violations)
        total_pairs += pairs
        total_viol += violations

    print(f"  [{name}] n={n} F={F} → {total_pairs} pairs, {total_viol} violations")
    return {
        "name": name,
        "n": n,
        "F": F,
        "ok_pointwise": True,
        "results": results,
        "total_pairs": total_pairs,
        "total_violations": total_viol,
    }


def main() -> None:
    print("=" * 72)
    print("cellMass_AD numerical sanity check (mg-d731)")
    print("=" * 72)

    all_results = []

    # n = 1: F ∈ {4, 6, 12}, N divides F.
    print("\n--- n = 1 ---")
    for F in [4, 6, 12]:
        Ns = [N for N in [1, 2, 3, 4, 6] if F % N == 0]
        all_results.append(run_test(
            "constant", lambda nn, FF: instance_constant(nn, FF, c=2), 1, F, Ns))
        all_results.append(run_test(
            "log_supermod c=1",
            lambda nn, FF: instance_log_supermod_pairwise(nn, FF, c=1), 1, F, Ns))
        all_results.append(run_test(
            "sublattice subcube",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "subcube"), 1, F, Ns))
        all_results.append(run_test(
            "distinct 4-tuple chain",
            lambda nn, FF: instance_distinct_4tuple_chain(nn, FF), 1, F, Ns))
        for seed in [1, 2, 3]:
            all_results.append(run_test(
                f"random 4tup seed={seed}",
                lambda nn, FF, s=seed: instance_random_4tuple(nn, FF, s), 1, F, Ns))
        for seed in [1, 2]:
            all_results.append(run_test(
                f"random log-sup seed={seed}",
                lambda nn, FF, s=seed: instance_random_logsupermod(nn, FF, s),
                1, F, Ns))

    # n = 2: F ∈ {4, 6}, N divides F.
    print("\n--- n = 2 ---")
    for F in [4, 6]:
        Ns = [N for N in [1, 2, 3] if F % N == 0]
        all_results.append(run_test(
            "constant", lambda nn, FF: instance_constant(nn, FF, c=2), 2, F, Ns))
        all_results.append(run_test(
            "log_supermod c=1",
            lambda nn, FF: instance_log_supermod_pairwise(nn, FF, c=1), 2, F, Ns))
        all_results.append(run_test(
            "sublattice subcube",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "subcube"), 2, F, Ns))
        all_results.append(run_test(
            "sublattice diag (lower-set)",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "lower_set_diag"),
            2, F, Ns))
        all_results.append(run_test(
            "polytope O(2-chain)",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "polytope_2chain"),
            2, F, Ns))
        all_results.append(run_test(
            "distinct 4-tuple chain",
            lambda nn, FF: instance_distinct_4tuple_chain(nn, FF), 2, F, Ns))
        for seed in [1, 2, 3, 4]:
            all_results.append(run_test(
                f"random 4tup seed={seed}",
                lambda nn, FF, s=seed: instance_random_4tuple(nn, FF, s), 2, F, Ns))
        for seed in [1, 2, 3]:
            all_results.append(run_test(
                f"random log-sup seed={seed}",
                lambda nn, FF, s=seed: instance_random_logsupermod(nn, FF, s),
                2, F, Ns))

    # n = 3: F ∈ {2, 4, 6}.
    print("\n--- n = 3 ---")
    for F in [2, 4, 6]:
        Ns = [N for N in [1, 2, 3] if F % N == 0]
        all_results.append(run_test(
            "constant", lambda nn, FF: instance_constant(nn, FF, c=2), 3, F, Ns))
        all_results.append(run_test(
            "log_supermod c=1",
            lambda nn, FF: instance_log_supermod_pairwise(nn, FF, c=1), 3, F, Ns))
        all_results.append(run_test(
            "sublattice subcube",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "subcube"), 3, F, Ns))
        all_results.append(run_test(
            "polytope O(V)",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "polytope_V"),
            3, F, Ns))
        all_results.append(run_test(
            "polytope O(Λ)",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "polytope_Lambda"),
            3, F, Ns))
        all_results.append(run_test(
            "polytope O(3-chain)",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "polytope_3chain"),
            3, F, Ns))
        all_results.append(run_test(
            "distinct 4-tuple chain",
            lambda nn, FF: instance_distinct_4tuple_chain(nn, FF), 3, F, Ns))
        for seed in [1, 2]:
            all_results.append(run_test(
                f"random 4tup seed={seed}",
                lambda nn, FF, s=seed: instance_random_4tuple(nn, FF, s), 3, F, Ns))
        for seed in [1, 2]:
            all_results.append(run_test(
                f"random log-sup seed={seed}",
                lambda nn, FF, s=seed: instance_random_logsupermod(nn, FF, s),
                3, F, Ns))

    # n = 4: small only (F = 2, 4 with N = 1, 2).
    print("\n--- n = 4 ---")
    for F in [2, 4]:
        Ns = [N for N in [1, 2] if F % N == 0]
        all_results.append(run_test(
            "constant", lambda nn, FF: instance_constant(nn, FF, c=2), 4, F, Ns))
        all_results.append(run_test(
            "log_supermod c=1",
            lambda nn, FF: instance_log_supermod_pairwise(nn, FF, c=1), 4, F, Ns))
        all_results.append(run_test(
            "polytope O(diamond)",
            lambda nn, FF: instance_sublattice_indicator(nn, FF, "polytope_diamond"),
            4, F, Ns))
        all_results.append(run_test(
            "distinct 4-tuple chain",
            lambda nn, FF: instance_distinct_4tuple_chain(nn, FF), 4, F, Ns))

    # ---- Summary ----
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    n_ok = sum(1 for r in all_results if r.get("ok_pointwise"))
    n_total = len(all_results)
    total_pairs = sum(r.get("total_pairs", 0) for r in all_results)
    total_viol = sum(r.get("total_violations", 0) for r in all_results)
    print(f"Total instances: {n_total} ({n_ok} pointwise-AD-valid)")
    print(f"Total cell-pair checks: {total_pairs}")
    print(f"Total violations: {total_viol}")

    # Coverage breakdown.
    by_n = {}
    for r in all_results:
        by_n.setdefault(r["n"], []).append(r)
    print("\nCoverage by dimension:")
    for n, rs in sorted(by_n.items()):
        ps = sum(r.get("total_pairs", 0) for r in rs)
        vs = sum(r.get("total_violations", 0) for r in rs)
        print(f"  n={n}: {len(rs)} instances, {ps} pair-checks, {vs} violations")

    if total_viol == 0 and n_ok == n_total:
        print("\nVERDICT: PASS.  No violations of cell-AD found.")
    elif total_viol == 0:
        print(f"\nVERDICT: PASS on cell-AD ({n_total - n_ok} pointwise-AD-invalid")
        print("instances skipped — those are bad TEST INPUTS, not cell-AD failures).")
    else:
        print("\nVERDICT: FAIL.  See cell-AD violations above.")


if __name__ == "__main__":
    main()
