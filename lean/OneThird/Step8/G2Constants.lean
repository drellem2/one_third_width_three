/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 8 — G2 constants coherence (`sec:G2-constants`)

Formalises the constants-coherence chain of `step8.tex`
§`sec:G2-constants` (`step8.tex:1460-1871`).

The Step 8 constants are bundled in `G2Constants` (the named
parameters `c₀, c₅, c₆, K, δ, ε, η` of the paper). The
**compatibility function** `g(T, ε, δ) := c₆ · (δ − K ε)` and
the **G2 compatibility inequality**

  `η · (n − 1) < c₀ · c₅ · g(T, ε, δ)`

(`step8.tex:1532`, `eq:G2`) are the central objects.

## Main results

* `compatFun` — the compatibility function
  `g(T, ε, δ) := c₆ · (δ − K ε)` (`step8.tex:1515`).
* `G2Compat` — the cleared-denominator form of the compatibility
  inequality `eq:G2` (`step8.tex:1532`).
* `prop_G2` — **Proposition G2** (`step8.tex:1528`,
  `prop:G2`). Given the Step 4/5/6 aggregated lower bound, the
  Theorem E upper bound, and the G2 compatibility inequality,
  conclude the coherence statement `δ ≤ K · ε` (the
  $o(1)$-coherence of `prop:step6`).

* `prop_G2_sharp` — the sharper form of `rem:G2-sharp`
  (`step8.tex:1597-1607`): `2 c₅ c₆ (δ − K ε)` suffices on the
  RHS, with `c₀` absent.

* `prop_G2_realizable` — the cascade-realisability check of
  `rem:G2-order` (`step8.tex:1609-1655`): with `c₀ = γ` and
  `η = 2 / (γ n)`, the compatibility reduces to the
  `n`-independent arithmetic condition `γ² c₅ c₆ (δ − K ε) ≥ 4`.

## References

`step8.tex` §`sec:G2-constants` (`step8.tex:1460-1871`),
Proposition `prop:G2`, Remarks `rem:G2-sharp`, `rem:G2-order`.
-/

namespace OneThird
namespace Step8

/-! ### §1 — Constants and the compatibility function -/

/-- **Step 8 named constants** (`step8.tex:1468-1511`).

The six rational constants of the G2 cascade, packaged together
for use throughout the section:

* `c₀` — Theorem E volume fraction (`step8.tex:1470`); `0 < c₀ ≤ 1/2`,
  quantitatively `c₀ = γ`.
* `c₅` — Step 5 richness second-moment constant
  (`step8.tex:1476`); `c₅ = c_T'(T)`, independent of `n`.
* `c₆` — Step 6 overlap-counting constant
  (`step8.tex:1497`); independent of `T, γ, ε, δ`.
* `K`  — `K(T) := C₄/c₄ + C₂(T)` (`step8.tex:1519`); absorbs Step 4
  rectangle noise and Step 2 block-transfer loss.
* `δ`  — aggregate weighted incoherent-mass fraction in `M`
  (`step8.tex:1506`).
* `ε`  — Step 2 fiber error (`step8.tex:1508`); free parameter,
  `ε(φ) ↓ 0` as BK conductance `φ ↓ 0`. -/
structure G2Constants where
  /-- Theorem E volume fraction (`step8.tex:1470`). -/
  c₀ : ℚ
  /-- Step 5 richness second-moment (`step8.tex:1476`). -/
  c₅ : ℚ
  /-- Step 6 overlap-counting (`step8.tex:1497`). -/
  c₆ : ℚ
  /-- Step 4/2 absorbed noise constant (`step8.tex:1519`). -/
  K : ℚ
  /-- Step 6 incoherent-mass fraction (`step8.tex:1506`). -/
  δ : ℚ
  /-- Step 2 fiber error (`step8.tex:1508`). -/
  ε : ℚ
  /-- Sign conventions (`step8.tex:1468-1511`). -/
  c₀_pos : 0 < c₀
  c₀_le_half : c₀ ≤ 1 / 2
  c₅_pos : 0 < c₅
  c₆_pos : 0 < c₆

/-- **Compatibility function** `g(T, ε, δ) := c₆ · (δ − K ε)`
(`step8.tex:1515-1518`).

In the paper this is `c₆ · (δ − K(T) ε)_+`, but we drop the
positive-part since the contradictory branch only triggers when
`δ > K · ε` (i.e.\ when the argument is positive). -/
def compatFun (G : G2Constants) : ℚ :=
  G.c₆ * (G.δ - G.K * G.ε)

/-- **G2 compatibility inequality `eq:G2`** (`step8.tex:1532`).

Cleared-denominator form: with the upper-bound input
`η · (n − 1)` (the `step8.tex:1577` `eq:G2-upper` quantity)
and the lower-bound coefficient `c₀ · c₅ · g(T, ε, δ)`, the
inequality

  `η · (n − 1)  <  c₀ · c₅ · g(T, ε, δ)`

is the hypothesis under which Case (R) of Theorem `thm:main`
yields the coherence conclusion `δ ≤ K · ε`. -/
def G2Compat (G : G2Constants) (η : ℚ) (n : ℕ) : Prop :=
  η * ((n : ℚ) - 1) < G.c₀ * G.c₅ * compatFun G

/-! ### §2 — Proposition G2 -/

/-- **Proposition G2** (`step8.tex:1528`, `prop:G2`).

Cleared-denominator algebraic form. Given:
* `hLower` — Step 4/5/6 aggregated lower bound
  `c₅ · c₆ · (δ − K ε) · |L(P)| ≤ |∂S|`
  (`step8.tex:1567`, `eq:G2-lowerfinal`);
* `hUpper` — Theorem E upper bound
  `|∂S| ≤ ½ · η · (n − 1) · |L(P)|`
  (`step8.tex:1577`, `eq:G2-upper`);
* `hCompat` — the compatibility inequality `eq:G2`;

the proof follows by contradiction (`step8.tex:1555-1595`):
suppose `δ > K · ε`, so `δ − K ε > 0`. Combining the lower and
upper bounds and cancelling `|L(P)| > 0` gives

  `c₅ c₆ (δ − K ε)  ≤  ½ η (n − 1)`,                 (A)

while combining the compatibility with `c₀ ≤ ½`:

  `η (n − 1)  <  c₀ c₅ c₆ (δ − K ε)
              ≤  ½ c₅ c₆ (δ − K ε)`.                 (B)

Multiplying (B) by `½` and chaining with (A):

  `c₅ c₆ (δ − K ε)  ≤  ½ η (n − 1)  <  ¼ c₅ c₆ (δ − K ε)`,

i.e.\ `1 < 1/4` after cancelling the positive quantity, a
numerical contradiction. -/
theorem prop_G2
    (G : G2Constants) (η : ℚ) (n LP boundary : ℕ)
    (hLP : 0 < LP)
    (hLower :
      G.c₅ * G.c₆ * (G.δ - G.K * G.ε) * (LP : ℚ) ≤ (boundary : ℚ))
    (hUpper :
      (boundary : ℚ) ≤ (1 / 2) * η * ((n : ℚ) - 1) * (LP : ℚ))
    (hCompat : G2Compat G η n) :
    G.δ ≤ G.K * G.ε := by
  by_contra hpos
  rw [not_le] at hpos
  -- `hpos : G.K * G.ε < G.δ`, so `δ − K ε > 0`.
  have hgap : 0 < G.δ - G.K * G.ε := by linarith
  have hLPq : (0 : ℚ) < (LP : ℚ) := by exact_mod_cast hLP
  have hMpos : 0 < G.c₅ * G.c₆ * (G.δ - G.K * G.ε) :=
    mul_pos (mul_pos G.c₅_pos G.c₆_pos) hgap
  -- (A): combine the two bounds and cancel `LP > 0`.
  have hChain :
      G.c₅ * G.c₆ * (G.δ - G.K * G.ε) * (LP : ℚ) ≤
        (1 / 2) * η * ((n : ℚ) - 1) * (LP : ℚ) :=
    le_trans hLower hUpper
  have hCancel :
      G.c₅ * G.c₆ * (G.δ - G.K * G.ε) ≤ (1 / 2) * η * ((n : ℚ) - 1) := by
    nlinarith [hChain, hLPq, hMpos]
  -- (B): the compatibility inequality with `c₀ ≤ 1/2`.
  unfold G2Compat compatFun at hCompat
  -- `nlinarith` closes the contradiction directly using
  --   2 * hCancel,  hCompat,  G.c₀_le_half * (positive M),
  --   M = c₅ c₆ (δ − Kε) > 0.
  nlinarith [hCancel, hCompat, G.c₀_le_half, G.c₀_pos,
              G.c₅_pos, G.c₆_pos, hgap, hMpos,
              mul_pos G.c₅_pos G.c₆_pos]

/-- **Proposition G2 — sharp form** (`step8.tex:1597-1607`,
`rem:G2-sharp`).

The contradiction in `prop_G2` actually goes through with the
weaker compatibility hypothesis `η (n−1) < 2 c₅ c₆ (δ − K ε)`, in
which the volume fraction `c₀` is absent.

This is exactly the inequality `eq:G2-combined`
of `step8.tex:1584`, contradicted directly by the strict
`<` form (no `c₀` factor needed). -/
theorem prop_G2_sharp
    (G : G2Constants) (η : ℚ) (n LP boundary : ℕ)
    (hLP : 0 < LP)
    (hLower :
      G.c₅ * G.c₆ * (G.δ - G.K * G.ε) * (LP : ℚ) ≤ (boundary : ℚ))
    (hUpper :
      (boundary : ℚ) ≤ (1 / 2) * η * ((n : ℚ) - 1) * (LP : ℚ))
    (hSharp : η * ((n : ℚ) - 1) <
        2 * G.c₅ * G.c₆ * (G.δ - G.K * G.ε)) :
    G.δ ≤ G.K * G.ε := by
  by_contra hpos
  rw [not_le] at hpos
  have hgap : 0 < G.δ - G.K * G.ε := by linarith
  have hLPq : (0 : ℚ) < (LP : ℚ) := by exact_mod_cast hLP
  have hMpos : 0 < G.c₅ * G.c₆ * (G.δ - G.K * G.ε) :=
    mul_pos (mul_pos G.c₅_pos G.c₆_pos) hgap
  have hChain :
      G.c₅ * G.c₆ * (G.δ - G.K * G.ε) * (LP : ℚ) ≤
        (1 / 2) * η * ((n : ℚ) - 1) * (LP : ℚ) :=
    le_trans hLower hUpper
  have hCancel :
      G.c₅ * G.c₆ * (G.δ - G.K * G.ε) ≤ (1 / 2) * η * ((n : ℚ) - 1) := by
    nlinarith [hChain, hLPq, hMpos]
  -- (A) says `2 M ≤ η (n−1)`; (hSharp) says `η (n−1) < 2 M`,
  -- where `M = c₅ c₆ (δ − Kε) > 0`. Contradiction.
  nlinarith [hCancel, hSharp, hMpos]

/-! ### §3 — Cascade realisability (`rem:G2-order`) -/

/-- **Cascade realisability — quantitative form**
(`step8.tex:1609-1655`, `rem:G2-order`; also `step8.tex:1728-1749`,
"Parameter cascade realizability", `mg-0704`).

With Theorem E supplying `c₀ = γ` and `η(γ, n) = 2 / (γ n)`, the
compatibility inequality `eq:G2` reads

  `(2 (n−1)) / (γ n)  <  γ · c₅ · c₆ · (δ − K ε)`,

which (using `(n−1)/n < 1` for all `n ≥ 2`) is implied by the
`n`-independent arithmetic condition

  `γ² · c₅ · c₆ · (δ − K ε)  ≥  2`,

i.e. once the Step 5/6 second-moment constant `c₅ c₆` dominates
`2 / (γ² (δ − K ε))`. We state the result for `n ≥ 2` (the
regime of `rem:G2-order`); the `n < 2` case is handled by the
small-`n` base case (`rem:small-n`, `step8.tex:827-874`). -/
theorem prop_G2_realizable
    (G : G2Constants) (γ : ℚ) (n : ℕ)
    (hγ : 0 < γ)
    (hn : 2 ≤ n)
    (hc₀ : G.c₀ = γ)
    (hgap : 0 < G.δ - G.K * G.ε)
    (hArith :
      γ * γ * (G.c₅ * G.c₆ * (G.δ - G.K * G.ε)) ≥ 2) :
    G2Compat G (2 / (γ * (n : ℚ))) n := by
  unfold G2Compat compatFun
  rw [hc₀]
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hnQ_pos : (0 : ℚ) < (n : ℚ) := by linarith
  have hγn_pos : (0 : ℚ) < γ * (n : ℚ) := mul_pos hγ hnQ_pos
  have hpredpos : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hMpos : 0 < G.c₅ * G.c₆ * (G.δ - G.K * G.ε) :=
    mul_pos (mul_pos G.c₅_pos G.c₆_pos) hgap
  -- Rewrite LHS: `(2 / (γ n)) * (n − 1) = (2 (n − 1)) / (γ n)`.
  rw [div_mul_eq_mul_div]
  -- Now use `div_lt_iff₀` to clear the denominator γn > 0.
  rw [div_lt_iff₀ hγn_pos]
  -- Goal: `2 (n − 1) < γ · c₅ · (c₆ (δ − K ε)) · (γ n)`.
  -- Equivalently `2 (n − 1) < γ² · n · (c₅ c₆ Δ)`.
  -- Using `hArith : γ² · (c₅ c₆ Δ) ≥ 2` and `n ≥ 2`:
  -- `γ² · n · (c₅ c₆ Δ) ≥ 2 n > 2 (n − 1)`.
  nlinarith [hArith, hMpos, hpredpos, hnQ_pos, hγ, hnQ,
             mul_pos hγ hMpos]

end Step8
end OneThird
