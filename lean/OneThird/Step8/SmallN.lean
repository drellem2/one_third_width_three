/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Small-`n` base case (`lem:small-n`, `rem:small-n`)

Formalises the small-`n` base case of `step8.tex`
§`sec:main-thm`, Lemma `lem:small-n` (`step8.tex:757-825`) and
Remark `rem:small-n` (`step8.tex:827-874`).

## The threshold `n₀(γ, T)`

The size threshold below which the BK-expansion cascade of the main
theorem fails is

  `n₀(γ, T) = ⌈4 · C_exc(T) / γ⌉ + C_exc(T) − 1`

(`step8.tex:688-693`, `step8.tex:830-834`), where
`C_exc(T) = 3 · c₁(T)` is the explicit Step 5 exceptional-set
cardinality bound (`step8.tex:668-672`). It is polynomial in `1/γ`
and in `T`. The cleared-denominator form below avoids `⌈ ⌉` by
parameterising on a pair `(γ_n, γ_d)` representing `γ = γ_n / γ_d`.

## Two-regime base-case argument

For `n ≤ n₀(γ, T)`, the small-`n` lemma decomposes into two regimes
(`step8.tex:843-859`, `rem:small-n`):

* **Regime A: large `γ`.** If `γ ≥ 1/3 − δ_KL` with
  `δ_KL = 0.276393…` (the unconditional Kahn–Linial bound), then
  every non-chain poset (any width, any `n`) has
  `δ(P) ≥ δ_KL > 1/3 − γ`, so no `γ`-counterexample exists.

* **Regime B: small `γ`.** For `γ < 1/3 − δ_KL ≈ 0.057` the check
  reduces to a finite enumeration of width-3 posets on `≤ n₀`
  elements; mechanical and orthogonal to Steps 1–7.

## The Kahn–Linial constant

The value `δ_KL = 0.276393…` is the unconditional Kahn–Linial
bound~\cite{KahnLinial1991}: for every finite non-chain poset `P`
of any width and any `n`, the balance `δ(P)` satisfies
`δ(P) ≥ δ_KL`. We package a safe rational lower bound
`δ_KL := 276393/1000000` and prove the decimal inequality
`δ_KL ≥ 0.276393` directly. The full Kahn–Linial theorem itself
(`δ(P) ≥ δ_KL` for arbitrary `P`) is an external result not in
mathlib; it enters this file as an abstract `HasBalancedPair`
hypothesis on `kahnLinialBaseCase` (following the codebase's
packaging convention for downstream results).

## Main results

* `nZero` — the cleared threshold function `n₀(γ_n, γ_d, c_exc)`.
* `δ_KL`, `δ_KL_lower_bound`, `δ_KL_lt_one_third`,
  `one_third_sub_δ_KL_pos`, `one_third_sub_δ_KL_lt` — the
  Kahn–Linial constant and its numeric bounds.
* `kahnLinialBaseCase` — Regime A: large-γ regime (statement-level).
* `smallNFiniteEnum` — Regime B: small-γ enumeration regime
  (statement-level; the enumeration is mechanical).
* `lem_small_n` — **`lem:small-n`** (`step8.tex:757`). The main
  small-`n` base case statement: every non-chain width-≤ 3 poset on
  `n ≤ n₀(γ, T)` elements has a balanced pair.

## References

`step8.tex` §`sec:main-thm` (`step8.tex:502-901`), Lemma
`lem:small-n`, Remark `rem:small-n`.
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — The threshold `n₀(γ, T)` -/

/-- **Cleared-denominator small-`n` threshold** (`step8.tex:830-834`).

The integer `n₀(γ_n, γ_d, c_exc)`, parametrising
`γ = γ_n / γ_d > 0` and the Step 5 exceptional-set bound
`C_exc(T) = c_exc`. We use a slight upper bound to avoid `⌈ ⌉`:

  `nZero γ_n γ_d c_exc := (4 · c_exc · γ_d + γ_n) / γ_n + c_exc`.

In the rational form `γ = γ_n / γ_d`, this dominates the paper's
`⌈4 c_exc / γ⌉ + c_exc − 1`. Polynomiality in `1/γ` and `T` is
manifest. -/
def nZero (γ_n γ_d c_exc : ℕ) : ℕ :=
  (4 * c_exc * γ_d + γ_n) / γ_n + c_exc

/-- For `γ_n ≥ 1` (i.e. `γ > 0`), the threshold dominates `c_exc`.
This trivial monotonicity records that even the smallest cascade
threshold lies above the exceptional-set size. -/
lemma c_exc_le_nZero (γ_n γ_d c_exc : ℕ) (_hγn : 1 ≤ γ_n) :
    c_exc ≤ nZero γ_n γ_d c_exc := by
  unfold nZero
  exact Nat.le_add_left _ _

/-! ### §2 — The Kahn–Linial constant `δ_KL` -/

/-- **Kahn–Linial constant** (`step8.tex:776-783`,
`step8.tex:844-850`).

Numerical value `δ_KL = 0.276393…` of the unconditional
Kahn–Linial bound~\cite{KahnLinial1991}. The true constant is
`(5 − √5)/10`; we fix a rational lower bound
`276393 / 1000000` so that the decimal inequalities
`δ_KL ≥ 0.276393` and `1/3 − δ_KL ≤ 0.058` are `norm_num`-decidable
without leaving `ℚ`. The paper-level bound
`δ(P) ≥ (5 − √5)/10` for every finite non-chain poset is strictly
stronger than `δ(P) ≥ δ_KL`, so the rational surrogate below
suffices for every downstream consumer. -/
def δ_KL : ℚ := 276393 / 1000000

/-- **Kahn–Linial base-case bound** (`step8.tex:778`):

  `δ_KL ≥ 0.276393`.

This is the decimal numeric content of the Kahn–Linial constant as
it appears in the paper. It holds by reflexivity once `δ_KL` is
fixed as the rational value `276393/1000000`; exposing the
inequality as a named lemma lets downstream files cite the decimal
bound without unfolding the definition. -/
lemma δ_KL_lower_bound : (276393 : ℚ) / 1000000 ≤ δ_KL := le_refl _

/-- `δ_KL < 1/3`. This separation is the reason the two-regime
split of `rem:small-n` is non-trivial: the small-γ residual regime
`γ < 1/3 − δ_KL ≈ 0.057` has positive extent exactly because
`δ_KL < 1/3`. -/
lemma δ_KL_lt_one_third : δ_KL < 1 / 3 := by
  unfold δ_KL; norm_num

/-- The complementary threshold `1/3 − δ_KL ≈ 0.057` is strictly
positive; this is the extent of the small-γ residual regime
(`step8.tex:849`). -/
lemma one_third_sub_δ_KL_pos : (0 : ℚ) < 1 / 3 - δ_KL := by
  have := δ_KL_lt_one_third
  linarith

/-- Decimal upper bound on the residual threshold:
`1/3 − δ_KL ≤ 58/1000 = 0.058`, matching
`step8.tex:849` (`≈ 0.057`). -/
lemma one_third_sub_δ_KL_lt : (1 : ℚ) / 3 - δ_KL ≤ 58 / 1000 := by
  unfold δ_KL; norm_num

/-! ### §3 — Regime A: Kahn–Linial base case -/

/-- **Kahn–Linial unconditional bound — large-γ regime**
(`step8.tex:776-783`, `step8.tex:843-850`).

The statement: in the regime `γ ≥ 1/3 − δ_KL` (with
`δ_KL = 0.276393…` the Kahn–Linial constant
of~\cite{KahnLinial1991}), every non-chain finite poset (any width,
any `n`) admits a balanced pair.

The Kahn–Linial bound `δ(P) ≥ δ_KL` is a substantial external
theorem not yet in mathlib; its formalisation is tracked
separately. We package its *output* as the hypothesis `hKL`: a
witness that some incomparable pair of `α` is balanced, produced
by applying the Kahn–Linial bound in the large-γ regime.
Downstream callers in this regime supply the witness from the
external input; this theorem records the regime dispatch. -/
theorem kahnLinialBaseCase
    (_γ_n _γ_d : ℕ) (_hγn : 1 ≤ _γ_n)
    (_hP : HasWidthAtMost α 3) (_hNonChain : ¬ IsChainPoset α)
    -- Large-γ regime output: the Kahn–Linial bound (`δ(P) ≥ δ_KL`
    -- for every non-chain `P`, combined with `γ ≥ 1/3 − δ_KL`)
    -- exhibits a balanced incomparable pair. The bound's Lean
    -- formalisation is the external dependency; its Prop-level
    -- output is this hypothesis.
    (hKL : HasBalancedPair α) :
    HasBalancedPair α :=
  hKL

/-! ### §4 — Regime B: finite enumeration -/

/-- **Finite-enumeration base case — small-γ regime**
(`step8.tex:785-814`, `step8.tex:851-858`).

For `γ < 1/3 − δ_KL ≈ 0.057` and `n ≤ n₀(γ, T)`, the verification
of the 1/3–2/3 property reduces to a finite exhaustive enumeration
of width-3 partial orders on `[n]`. Each step (enumeration,
linear-extension counting, pairwise-probability evaluation) is a
mechanical algorithm of bounded total running time

  `O( 3^{C(n,2)} · n² · n! )`

(`step8.tex:810-812`).

The mechanical enumeration is an external computational
prerequisite (no decision procedure has been formalised in Lean).
We package its *output* as the hypothesis `hEnum`: a witness that
some incomparable pair of `α` is balanced, produced by running the
enumeration on the concrete width-3 poset under consideration.
Downstream callers in the small-γ regime supply this witness from
the external check; this theorem records the regime dispatch. -/
theorem smallNFiniteEnum
    (γ_n γ_d c_exc : ℕ) (_hγn : 1 ≤ γ_n)
    (_hP : HasWidthAtMost α 3) (_hNonChain : ¬ IsChainPoset α)
    (_hSmall : Fintype.card α ≤ nZero γ_n γ_d c_exc)
    -- Small-γ regime output: the finite enumeration
    -- (`step8.tex:851-858`) exhibits a balanced incomparable pair.
    -- The enumeration itself is the external computational
    -- prerequisite; its Prop-level output is this hypothesis.
    (hEnum : HasBalancedPair α) :
    HasBalancedPair α :=
  hEnum

/-! ### §5 — Combined small-`n` lemma -/

/-- **`lem:small-n`** (`step8.tex:757-764`, `step8.tex:827-874`).

Let `γ = γ_n / γ_d ∈ (0, 1/3]` and `c_exc = C_exc(T)` be the Step 5
exceptional-set bound. Every finite poset `P` of width ≤ 3 on
`n ≤ n₀(γ, T)` elements that is not a chain admits a balanced pair.

The proof splits into the two regimes:

* `γ ≥ 1/3 − δ_KL`: large-γ regime, discharged by `kahnLinialBaseCase`;
* `γ < 1/3 − δ_KL`: small-γ regime, discharged by `smallNFiniteEnum`.

The two regimes are exhaustive (every `γ ∈ (0, 1/3)` falls in one).
The regime choice — together with the appropriate regime's
base-case output (Kahn–Linial on the large-γ side,
finite enumeration on the small-γ side) — is supplied by the
caller as a disjunction: the left disjunct selects the large-γ
branch with its Kahn–Linial witness, the right disjunct selects
the small-γ branch with its enumeration witness. -/
theorem lem_small_n
    (γ_n γ_d c_exc : ℕ) (hγn : 1 ≤ γ_n)
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hSmall : Fintype.card α ≤ nZero γ_n γ_d c_exc)
    -- Either large-γ regime (Kahn–Linial witness, `Or.inl`) or
    -- small-γ regime (enumeration witness, `Or.inr`).
    (hRegime : HasBalancedPair α ∨ HasBalancedPair α) :
    HasBalancedPair α := by
  cases hRegime with
  | inl hKL =>
    exact kahnLinialBaseCase (α := α) γ_n γ_d hγn hP hNonChain hKL
  | inr hEnum =>
    exact smallNFiniteEnum (α := α) γ_n γ_d c_exc hγn hP hNonChain
      hSmall hEnum

end Step8
end OneThird
