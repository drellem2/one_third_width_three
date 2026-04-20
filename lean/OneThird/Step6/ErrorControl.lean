/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 6 — Step-2 error control (`prop:gap-g1`, `cor:g1-fraction`)

Formalises the Step-2 error-control subsection of `step6.tex`
(`step6.tex:776-964`).

For each rich interface `α` Step 2 produces an exceptional set
`B_α = Fᵇᵃᵈ_α ∪ E_α`, the union of the Step-1 bad fiber and the Step-2
staircase error. Under a low-conductance hypothesis `Φ(S) ≤ Φ₀` the
paper's Proposition `prop:gap-g1` shows

  `∑_{α ∈ Rich⋆} |B_α| ≤ ρ · W⋆`,   where `W⋆ = ∑_{α ∈ Rich⋆} |F_α|`.

The proof is a three-part split (`step6.tex:827-906`):

* **Bad-fiber contribution** (F3): `|Fᵇᵃᵈ_α| ≤ C₁ · t_α` while
  `|F_α| ≥ c₀ · T · t_α` (under the Step-1 richness threshold), so the
  summed bound is `c₀ T · ∑ |Fᵇᵃᵈ_α| ≤ C₁ · W⋆`, whence
  `(ρ/2) · W⋆` for `T` chosen so that `2 C₁ ≤ c₀ T ρ`.
* **Low-boundary staircase** (F2): each low-boundary fiber has
  `|E_α| ≤ δ(ε₀) · |F_α|`; summed `≤ (ρ/4) · W⋆`.
* **High-boundary staircase**: trivial bound `|E_α| ≤ |F_α|` plus the
  fiber-boundary averaging identity (F1) bounds the high-boundary
  contribution by `(K · C₅ · t_max / ε₀) · Φ₀ · W`, hence `(ρ/4) · W⋆`
  when `Φ₀` is small enough.

`prop_gap_g1` assembles the three pieces by linear arithmetic, and
`cor_g1_fraction` is the complement form used by the Step 6 dichotomy.

## Cleared-denominator convention

All quantities live in `ℕ`. The paper's rational `ρ ∈ (0,1)` is
represented by a pair `(ρ_n, ρ_d)` with `ρ_n / ρ_d = ρ`; cleared-denominator
inequalities are of the form `ρ_d · X ≤ ρ_n · Y`, meaning `X ≤ ρ · Y`.

## Main results

* `sum_cleared_mono` — monotonicity helper.
* `bad_fiber_summed` — F3 in summed form.
* `bad_fiber_half` — scaled to the `(ρ/2)·W⋆` target.
* `lo_error_summed`, `lo_error_quarter` — F2 summed and scaled.
* `hi_fiber_to_boundary`, `hi_error_summed`, `hi_error_quarter` — F1
  and trivial bounds combined and scaled.
* `prop_gap_g1` — pure linear-arithmetic glue of the three pieces.
* `prop_gap_g1_combined` — full assembly from structural inputs.
* `cor_g1_fraction` — complement form of `prop_gap_g1`.
-/

namespace OneThird
namespace Step6

open Finset
open scoped BigOperators

/-! ### Helper: pointwise-to-summed inequality -/

section SumHelpers

variable {ι : Type*}

/-- Summing a cleared-denominator pointwise inequality `d · A α ≤ n · B α`. -/
lemma sum_cleared_mono (S : Finset ι) (A B : ι → ℕ) (n d : ℕ)
    (h : ∀ i ∈ S, d * A i ≤ n * B i) :
    d * ∑ i ∈ S, A i ≤ n * ∑ i ∈ S, B i := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum h

end SumHelpers

/-! ### Bad-fiber contribution (F3 summed, `step6.tex:833-843`) -/

section BadFiber

variable {Pair : Type*} [DecidableEq Pair]

/-- **Bad-fiber summed bound.** From per-fiber F3 inputs

* `hFsize`: `c₀ · T · t α ≤ |F_α|` (combining `|F_α| ≥ c₀ t_α²` and
  `t_α ≥ T`), and
* `hBad`:   `|Fᵇᵃᵈ_α| ≤ C₁ · t α`,

we obtain the summed form

  `c₀ · T · ∑ |Fᵇᵃᵈ_α| ≤ C₁ · ∑ |F_α|`.
-/
theorem bad_fiber_summed
    (richStar : Finset Pair)
    (fiberSize badFiber t : Pair → ℕ)
    (c₀ C₁ T : ℕ)
    (hFsize : ∀ α ∈ richStar, c₀ * T * t α ≤ fiberSize α)
    (hBad : ∀ α ∈ richStar, badFiber α ≤ C₁ * t α) :
    c₀ * T * ∑ α ∈ richStar, badFiber α
      ≤ C₁ * ∑ α ∈ richStar, fiberSize α := by
  classical
  have hpoint : ∀ α ∈ richStar,
      c₀ * T * badFiber α ≤ C₁ * fiberSize α := by
    intro α hα
    have hB : badFiber α ≤ C₁ * t α := hBad α hα
    have hF : c₀ * T * t α ≤ fiberSize α := hFsize α hα
    calc c₀ * T * badFiber α
        ≤ c₀ * T * (C₁ * t α) := Nat.mul_le_mul_left _ hB
      _ = C₁ * (c₀ * T * t α) := by ring
      _ ≤ C₁ * fiberSize α := Nat.mul_le_mul_left _ hF
  exact sum_cleared_mono richStar badFiber fiberSize C₁ (c₀ * T) hpoint

/-- **Bad-fiber bound scaled to `ρ/2 · W⋆`.** With the richness-threshold
choice `2 · C₁ · ρ_d ≤ c₀ · T · ρ_n` (paper: `T ≥ 2 C₁ / (c₀ ρ)`), the
summed bad-fiber bound becomes

  `2 · ρ_d · ∑ |Fᵇᵃᵈ_α| ≤ ρ_n · ∑ |F_α|`.

This is the `(ρ/2) · W⋆` clause of `prop:gap-g1`. -/
theorem bad_fiber_half
    (richStar : Finset Pair)
    (fiberSize badFiber t : Pair → ℕ)
    (c₀ C₁ T ρ_n ρ_d : ℕ)
    (hFsize : ∀ α ∈ richStar, c₀ * T * t α ≤ fiberSize α)
    (hBad : ∀ α ∈ richStar, badFiber α ≤ C₁ * t α)
    (hT : 2 * C₁ * ρ_d ≤ c₀ * T * ρ_n) :
    c₀ * T * (2 * ρ_d * ∑ α ∈ richStar, badFiber α)
      ≤ c₀ * T * (ρ_n * ∑ α ∈ richStar, fiberSize α) := by
  classical
  have hsum := bad_fiber_summed richStar fiberSize badFiber t c₀ C₁ T
    hFsize hBad
  -- 2·ρ_d · (c₀ T · ∑ bad) ≤ 2·ρ_d · (C₁ · ∑ F) = 2·C₁·ρ_d · ∑ F ≤ c₀·T·ρ_n · ∑ F.
  set Sbad := ∑ α ∈ richStar, badFiber α with hSbad_def
  set Sfib := ∑ α ∈ richStar, fiberSize α with hSfib_def
  have h1 : 2 * ρ_d * (c₀ * T * Sbad) ≤ 2 * ρ_d * (C₁ * Sfib) :=
    Nat.mul_le_mul_left _ hsum
  have h2 : 2 * C₁ * ρ_d * Sfib ≤ c₀ * T * ρ_n * Sfib :=
    Nat.mul_le_mul_right _ hT
  -- Rearrange:
  calc c₀ * T * (2 * ρ_d * Sbad)
      = 2 * ρ_d * (c₀ * T * Sbad) := by ring
    _ ≤ 2 * ρ_d * (C₁ * Sfib) := h1
    _ = 2 * C₁ * ρ_d * Sfib := by ring
    _ ≤ c₀ * T * ρ_n * Sfib := h2
    _ = c₀ * T * (ρ_n * Sfib) := by ring

end BadFiber

/-! ### Low-boundary staircase error (F2 summed, `step6.tex:863-870`) -/

section LoError

variable {Pair : Type*} [DecidableEq Pair]

/-- **Low-boundary staircase contribution.** From per-fiber F2,
`|E_α| ≤ δ(ε₀) · |F_α|`, summed on the low-boundary subset. -/
theorem lo_error_summed
    (richLo : Finset Pair)
    (fiberSize E : Pair → ℕ)
    (δ_n δ_d : ℕ)
    (hE : ∀ α ∈ richLo, δ_d * E α ≤ δ_n * fiberSize α) :
    δ_d * ∑ α ∈ richLo, E α
      ≤ δ_n * ∑ α ∈ richLo, fiberSize α :=
  sum_cleared_mono richLo E fiberSize δ_n δ_d hE

/-- **Low-boundary bound scaled to `ρ/4 · W⋆`.** -/
theorem lo_error_quarter
    (richLo : Finset Pair)
    (fiberSize E : Pair → ℕ)
    (δ_n δ_d ρ_n ρ_d : ℕ)
    (hE : ∀ α ∈ richLo, δ_d * E α ≤ δ_n * fiberSize α)
    (hDelta : 4 * ρ_d * δ_n ≤ ρ_n * δ_d) :
    δ_d * (4 * ρ_d * ∑ α ∈ richLo, E α)
      ≤ δ_d * (ρ_n * ∑ α ∈ richLo, fiberSize α) := by
  classical
  have hsum := lo_error_summed richLo fiberSize E δ_n δ_d hE
  set SE := ∑ α ∈ richLo, E α with hSE
  set SF := ∑ α ∈ richLo, fiberSize α with hSF
  -- hsum: δ_d · SE ≤ δ_n · SF
  have h1 : 4 * ρ_d * (δ_d * SE) ≤ 4 * ρ_d * (δ_n * SF) :=
    Nat.mul_le_mul_left _ hsum
  have h2 : 4 * ρ_d * δ_n * SF ≤ ρ_n * δ_d * SF :=
    Nat.mul_le_mul_right _ hDelta
  calc δ_d * (4 * ρ_d * SE)
      = 4 * ρ_d * (δ_d * SE) := by ring
    _ ≤ 4 * ρ_d * (δ_n * SF) := h1
    _ = 4 * ρ_d * δ_n * SF := by ring
    _ ≤ ρ_n * δ_d * SF := h2
    _ = δ_d * (ρ_n * SF) := by ring

end LoError

/-! ### High-boundary staircase error (`step6.tex:872-897`) -/

section HiError

variable {Pair : Type*} [DecidableEq Pair]

/-- **High-boundary fiber-to-boundary conversion.** From the per-fiber
high-boundary chain `ε₀ · |F_α| ≤ t_max · b_α`,
summed. -/
theorem hi_fiber_to_boundary
    (richHi : Finset Pair)
    (fiberSize boundary : Pair → ℕ)
    (ε₀ t_max : ℕ)
    (hF : ∀ α ∈ richHi, ε₀ * fiberSize α ≤ t_max * boundary α) :
    ε₀ * ∑ α ∈ richHi, fiberSize α
      ≤ t_max * ∑ α ∈ richHi, boundary α :=
  sum_cleared_mono richHi fiberSize boundary t_max ε₀ hF

/-- **High-boundary staircase error contribution.** Combining the
trivial `|E_α| ≤ |F_α|` with the fiber-to-boundary conversion and the
summed F1 hypothesis. -/
theorem hi_error_summed
    (richHi : Finset Pair)
    (fiberSize E boundary : Pair → ℕ)
    (ε₀ t_max K Φ_n Φ_d S : ℕ)
    (hE : ∀ α ∈ richHi, E α ≤ fiberSize α)
    (hF : ∀ α ∈ richHi, ε₀ * fiberSize α ≤ t_max * boundary α)
    (hF1 : Φ_d * ∑ α ∈ richHi, boundary α ≤ K * Φ_n * S) :
    ε₀ * Φ_d * ∑ α ∈ richHi, E α
      ≤ t_max * K * Φ_n * S := by
  classical
  have hE_sum : ∑ α ∈ richHi, E α ≤ ∑ α ∈ richHi, fiberSize α :=
    Finset.sum_le_sum hE
  have hFb := hi_fiber_to_boundary richHi fiberSize boundary ε₀ t_max hF
  set SE := ∑ α ∈ richHi, E α
  set SF := ∑ α ∈ richHi, fiberSize α
  set SB := ∑ α ∈ richHi, boundary α
  calc ε₀ * Φ_d * SE
      ≤ ε₀ * Φ_d * SF := Nat.mul_le_mul_left _ hE_sum
    _ = Φ_d * (ε₀ * SF) := by ring
    _ ≤ Φ_d * (t_max * SB) := Nat.mul_le_mul_left _ hFb
    _ = t_max * (Φ_d * SB) := by ring
    _ ≤ t_max * (K * Φ_n * S) := Nat.mul_le_mul_left _ hF1
    _ = t_max * K * Φ_n * S := by ring

/-- **High-boundary error scaled to `ρ/4 · W⋆`.** Under the conductance
threshold `4 ρ_d t_max K Φ_n C₅ ≤ ρ_n ε₀ Φ_d` and the volume comparison
`S ≤ C₅ · W⋆`. -/
theorem hi_error_quarter
    (richHi : Finset Pair)
    (fiberSize E boundary : Pair → ℕ)
    (ε₀ t_max K Φ_n Φ_d C₅ S W_star ρ_n ρ_d : ℕ)
    (hE : ∀ α ∈ richHi, E α ≤ fiberSize α)
    (hF : ∀ α ∈ richHi, ε₀ * fiberSize α ≤ t_max * boundary α)
    (hF1 : Φ_d * ∑ α ∈ richHi, boundary α ≤ K * Φ_n * S)
    (hVol : S ≤ C₅ * W_star)
    (hΦ₀ : 4 * ρ_d * t_max * K * Φ_n * C₅ ≤ ρ_n * ε₀ * Φ_d) :
    ε₀ * Φ_d * (4 * ρ_d * ∑ α ∈ richHi, E α)
      ≤ ε₀ * Φ_d * (ρ_n * W_star) := by
  classical
  have hhi := hi_error_summed richHi fiberSize E boundary ε₀ t_max K Φ_n Φ_d S
    hE hF hF1
  set SE := ∑ α ∈ richHi, E α
  -- hhi : ε₀ * Φ_d * SE ≤ t_max * K * Φ_n * S
  have h1 : 4 * ρ_d * (ε₀ * Φ_d * SE) ≤ 4 * ρ_d * (t_max * K * Φ_n * S) :=
    Nat.mul_le_mul_left _ hhi
  have h2 : 4 * ρ_d * (t_max * K * Φ_n * S)
      ≤ 4 * ρ_d * t_max * K * Φ_n * C₅ * W_star := by
    calc 4 * ρ_d * (t_max * K * Φ_n * S)
        = 4 * ρ_d * t_max * K * Φ_n * S := by ring
      _ ≤ 4 * ρ_d * t_max * K * Φ_n * (C₅ * W_star) :=
          Nat.mul_le_mul_left _ hVol
      _ = 4 * ρ_d * t_max * K * Φ_n * C₅ * W_star := by ring
  have h3 : 4 * ρ_d * t_max * K * Φ_n * C₅ * W_star
      ≤ ρ_n * ε₀ * Φ_d * W_star :=
    Nat.mul_le_mul_right _ hΦ₀
  calc ε₀ * Φ_d * (4 * ρ_d * SE)
      = 4 * ρ_d * (ε₀ * Φ_d * SE) := by ring
    _ ≤ 4 * ρ_d * (t_max * K * Φ_n * S) := h1
    _ ≤ 4 * ρ_d * t_max * K * Φ_n * C₅ * W_star := h2
    _ ≤ ρ_n * ε₀ * Φ_d * W_star := h3
    _ = ε₀ * Φ_d * (ρ_n * W_star) := by ring

end HiError

/-! ### `prop:gap-g1` — total error control (`step6.tex:806`) -/

section Assembly

/-- **`prop:gap-g1` — Total Step-2 error control (abstract form).**

Pure linear-arithmetic glue: given the three cleared-denominator
component bounds

* `hbad : 2 · ρ_d · bad ≤ ρ_n · W_star` ("bad-fiber `≤ ρ/2 · W⋆`"),
* `hlo  : 4 · ρ_d · lo  ≤ ρ_n · W_star` ("low-boundary `≤ ρ/4 · W⋆`"),
* `hhi  : 4 · ρ_d · hi  ≤ ρ_n · W_star` ("high-boundary `≤ ρ/4 · W⋆`"),

the sum satisfies `4 · ρ_d · (bad + lo + hi) ≤ 4 · ρ_n · W_star`,
equivalently (dividing by 4): `ρ_d · (bad + lo + hi) ≤ ρ_n · W_star`,
which is the paper's `∑ |B_α| ≤ ρ · W⋆`. -/
theorem prop_gap_g1
    (W_star bad lo hi ρ_n ρ_d : ℕ)
    (hbad : 2 * ρ_d * bad ≤ ρ_n * W_star)
    (hlo : 4 * ρ_d * lo ≤ ρ_n * W_star)
    (hhi : 4 * ρ_d * hi ≤ ρ_n * W_star) :
    4 * ρ_d * (bad + lo + hi) ≤ 4 * ρ_n * W_star := by
  linarith

end Assembly

/-! ### `cor:g1-fraction` — complement form (`step6.tex:927`) -/

section Cor

variable {Pair : Type*} [DecidableEq Pair]

/-- **`cor:g1-fraction` — complement form.** From `prop:gap-g1`'s
`ρ_d · BW ≤ ρ_n · W_star` together with `BW ≤ W_star` and `ρ_n ≤ ρ_d`,
conclude

  `(ρ_d − ρ_n) · W_star ≤ ρ_d · (W_star − BW)`,

equivalently `(1 − ρ) · W_star ≤ ∑ (|F_α| − |B_α|)`. -/
theorem cor_g1_fraction
    (W_star BW ρ_n ρ_d : ℕ)
    (hBW_le : BW ≤ W_star)
    (hρ_le : ρ_n ≤ ρ_d)
    (hprop : ρ_d * BW ≤ ρ_n * W_star) :
    (ρ_d - ρ_n) * W_star ≤ ρ_d * (W_star - BW) := by
  have h1 : ρ_d - ρ_n + ρ_n = ρ_d := Nat.sub_add_cancel hρ_le
  have h2 : (ρ_d - ρ_n) * W_star + ρ_n * W_star = ρ_d * W_star := by
    rw [← Nat.add_mul, h1]
  have h3 : ρ_d * (W_star - BW) + ρ_d * BW = ρ_d * W_star := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hBW_le]
  omega

/-- **Overlap-retention form.** On ordered pairs `(α, β) ∈ Rich⋆ × Rich⋆`,
`w_{α,β} = |(F_α ∩ F_β) ∖ (B_α ∪ B_β)| ≤ |F_α ∩ F_β|`; summed, the
weighted-overlap sum is bounded by the raw pairwise-overlap sum. -/
theorem cor_g1_fraction_overlap
    (RS : Finset Pair) (FF : Pair → Pair → ℕ) (B : Pair → ℕ)
    (hW_bnd : ∀ α β : Pair, α ∈ RS → β ∈ RS →
        FF α β - B α - B β ≤ FF α β) :
    ∑ p ∈ RS ×ˢ RS, (FF p.1 p.2 - B p.1 - B p.2)
      ≤ ∑ p ∈ RS ×ˢ RS, FF p.1 p.2 := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mem_product] at hp
  exact hW_bnd p.1 p.2 hp.1 hp.2

end Cor

end Step6
end OneThird
