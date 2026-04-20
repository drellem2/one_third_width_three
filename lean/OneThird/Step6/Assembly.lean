/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step6.Incoherence
import OneThird.Step6.OverlapCounting
import OneThird.Step6.RichnessBound
import OneThird.Step6.ErrorControl
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 6 — Assembly of the Step 6 dichotomy

Formalises the Step 6 dichotomy theorem of `step6.tex` along with the
four remaining internal gaps and their consequences:

* **G6 — `lem:most-good`** (`step6.tex:158-233`): most rich interfaces
  are `S`-good. A Markov-style deduction from Step 2 summed error
  control and Step 5 richness.
* **G7 — `lem:sum-step4`** (`step6.tex:270-342`): summed Step 4 bound
  `c₁ · ∑_{bad active} w_{αβ} ≤ |∂S|`, combining Step 4's per-pair
  inequality with the overlap counting multiplicity of
  `lem:overlap-counting`.
* **`thm:step6`** (`step6.tex:481-571`): the dichotomy — either
  `|∂S| ≥ η · M` (expansion), or
  `∑_{bad active} w_{αβ} ≤ δ · M` (coherence).
* **G8 — `cor:pointwise`** (`step6.tex:587-713`): pointwise
  coherence, Conclusion B. From the coherence case plus the exact
  identity `M = ∑_L I(L)²` (from `lem:gap-G5(i)`, already proved in
  `RichnessBound.lean`), extract a sign function `s : LP → Sign` such
  that the weighted disagreement is small.

## Structure

All statements are in the abstract-hypothesis / cleared-denominator
style used throughout the Step 5–8 scaffold, so that the
ground-truth structural inputs (fiber structure, staircase
orientation, witness families) remain parameters to be instantiated
downstream. The proofs are self-contained linear-arithmetic
manipulations.

## Main results

* `lem_most_good` — G6, cleared-denominator form.
* `lem_sum_step4` — G7, cleared-denominator form.
* `thm_step6` — the dichotomy, cleared-denominator form.
* `cor_pointwise` — G8, cleared-denominator form.
* `cor_pointwise_aggregate` — the "minority-count mass bound"
  (equation (eq:mI-sum) of `step6.tex`), the aggregate form of
  pointwise coherence used by the Markov step of `cor_pointwise`.
* `cor_pointwise_markov` — the final Markov-style Pr[·] bound for
  the pointwise weighted measure.
-/

namespace OneThird
namespace Step6

open Finset OneThird.Step5
open scoped BigOperators

/-! ### §1 — G6: `lem:most-good` (`step6.tex:158`) -/

section G6

variable {Pair : Type*} [DecidableEq Pair]

/-- **G6 — `lem:most-good` (cleared-denominator)** (`step6.tex:158`).

Setup: for each `α ∈ Rich`, let `|F_α|` be the good-fiber size and
`|B_α|` the Step-2 exceptional set. Let `Rich⋆ ⊆ Rich` be the
`S`-good subset, i.e. those `α` with `|B_α| ≤ ε_n · |F_α| / ε_d`.
The complement `Rich^bad := Rich ∖ Rich⋆` consists of interfaces with
large exceptional mass.

Abstract hypotheses (paper's F2, F3 summed, and Step 5 richness):
* `hStep2 : ε_n · ∑_{α ∈ Rich} |B_α| ≤ C₂ · boundary` — the summed
  Step 2 error bound (`step6.tex:194`).
* `hRich  : c_R · volS ≤ ∑_{α ∈ Rich} |F_α|` — the rich-case fiber
  cover (`step6.tex:215`).
* `hΦ     : boundary ≤ Φ₀ · volS` — low-conductance hypothesis.

Markov gives

  `ε_n · ∑_{α ∈ Rich^bad} |F_α|
      ≤ ε_d · ∑_{α ∈ Rich} |B_α|
      ≤ ε_d · C₂ · boundary / ε_n
      ≤ ε_d · C₂ · Φ₀ · volS`.

Cleared-denominator form:

  `ε_n² · ∑_{α ∈ Rich^bad} |F_α| ≤ ε_d · C₂ · Φ₀ · volS`. -/
theorem lem_most_good
    (richSet richStar : Finset Pair)
    (fiberSize badSize : Pair → ℕ)
    (volS boundary Φ₀_n Φ₀_d C₂ ε_n ε_d : ℕ)
    (hRichStar : richStar ⊆ richSet)
    (hBadMass : ∀ α ∈ richSet \ richStar,
      ε_n * fiberSize α < ε_d * badSize α)
    (hStep2 : ε_n * ∑ α ∈ richSet, badSize α ≤ C₂ * boundary)
    (hΦ : Φ₀_d * boundary ≤ Φ₀_n * volS) :
    Φ₀_d * (ε_n * ε_n * ∑ α ∈ richSet \ richStar, fiberSize α) ≤
      Φ₀_n * (ε_d * C₂ * volS) := by
  classical
  -- Step 1: bad-fiber mass ≤ (ε_d / ε_n) · bad-set mass (Markov on Rich^bad).
  have hmarkov :
      ε_n * ∑ α ∈ richSet \ richStar, fiberSize α ≤
        ε_d * ∑ α ∈ richSet \ richStar, badSize α := by
    classical
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α hα
    exact Nat.le_of_lt (hBadMass α hα)
  -- Step 2: bad-set mass over Rich^bad ≤ bad-set mass over Rich.
  have hsub :
      ∑ α ∈ richSet \ richStar, badSize α ≤ ∑ α ∈ richSet, badSize α := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.sdiff_subset
    · intros; exact Nat.zero_le _
  -- Step 3: chain with Step 2 summed input and low-conductance hypothesis.
  -- (ε_n)·X ≤ ε_d · ∑bad  ≤  ε_d · ∑all.
  -- ε_n·(ε_n·X) ≤ ε_n · ε_d · ∑all  ≤  ε_d · C₂ · boundary.
  -- Φ₀_d · (ε_n² X) ≤ ε_d · C₂ · Φ₀_d · boundary ≤ ε_d · C₂ · Φ₀_n · volS.
  set X := ∑ α ∈ richSet \ richStar, fiberSize α with hX_def
  set B := ∑ α ∈ richSet, badSize α with hB_def
  have h1 : ε_n * X ≤ ε_d * ∑ α ∈ richSet \ richStar, badSize α := hmarkov
  have h2 : ε_n * X ≤ ε_d * B := h1.trans (Nat.mul_le_mul_left _ hsub)
  -- Multiply both sides by ε_n:
  have h3 : ε_n * (ε_n * X) ≤ ε_n * (ε_d * B) := Nat.mul_le_mul_left _ h2
  -- ε_n·ε_d·B = ε_d·(ε_n·B) ≤ ε_d·C₂·boundary (by hStep2).
  have h4 : ε_d * (ε_n * B) ≤ ε_d * (C₂ * boundary) :=
    Nat.mul_le_mul_left _ hStep2
  have h5 : ε_n * ε_n * X ≤ ε_d * C₂ * boundary := by
    calc ε_n * ε_n * X
        = ε_n * (ε_n * X) := by ring
      _ ≤ ε_n * (ε_d * B) := h3
      _ = ε_d * (ε_n * B) := by ring
      _ ≤ ε_d * (C₂ * boundary) := h4
      _ = ε_d * C₂ * boundary := by ring
  -- Multiply by Φ₀_d and chain with hΦ:
  have h6 : Φ₀_d * (ε_n * ε_n * X) ≤ Φ₀_d * (ε_d * C₂ * boundary) :=
    Nat.mul_le_mul_left _ h5
  have h7 : ε_d * C₂ * (Φ₀_d * boundary) ≤ ε_d * C₂ * (Φ₀_n * volS) :=
    Nat.mul_le_mul_left _ hΦ
  calc Φ₀_d * (ε_n * ε_n * X)
      ≤ Φ₀_d * (ε_d * C₂ * boundary) := h6
    _ = ε_d * C₂ * (Φ₀_d * boundary) := by ring
    _ ≤ ε_d * C₂ * (Φ₀_n * volS) := h7
    _ = Φ₀_n * (ε_d * C₂ * volS) := by ring

end G6

/-! ### §2 — G7: `lem:sum-step4` (`step6.tex:270`) -/

section G7

variable {Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- **G7 — `lem:sum-step4` (cleared-denominator)** (`step6.tex:270`).

The summed Step-4 bound. Given

* **per-pair Step 4 input** (`step6.tex:319-322`,
  eq.`eq:per-pair-witness-mass`):
  for every bad active pair `p ∈ badSet`,
  `c_n · w p.1 p.2 ≤ c_d · |∂S ∩ E_{p.1,p.2}|`,
  equivalently `|∂S ∩ E| ≥ (c_n/c_d) · w`;
* **overlap counting input** (`step6.tex:332`): the multiplicity bound
  `∑_{(α,β) ∈ richPairs×richPairs} |∂S ∩ E_{αβ}| ≤ M · |∂S|`,
  as provided by `OneThird.Step6.lem_overlap_counting_summed`.

Conclude (`step6.tex:338`, eq.`eq:bad-bounded-by-boundary-quant`):

  `c_n · ∑_{(α,β) ∈ badSet} w_{αβ} ≤ c_d · M · |∂S|`. -/
theorem lem_sum_step4
    (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge)
    (boundary : Finset Edge) (M c_n c_d : ℕ)
    (w : Pair → Pair → ℕ)
    (badSet : Finset (Pair × Pair))
    (hbadSub : badSet ⊆ richPairs ×ˢ richPairs)
    (hmult : ∀ e ∈ boundary,
      OneThird.Step4.witnessCount richPairs witness e ≤ M)
    (hPerPair : ∀ p ∈ badSet,
      c_n * w p.1 p.2 ≤
        c_d * OneThird.Step4.pairWeight boundary witness p.1 p.2) :
    c_n * ∑ p ∈ badSet, w p.1 p.2 ≤
      c_d * M * boundary.card := by
  classical
  -- Sum the per-pair bounds over badSet.
  have hsum :
      c_n * ∑ p ∈ badSet, w p.1 p.2 ≤
        c_d * ∑ p ∈ badSet,
          OneThird.Step4.pairWeight boundary witness p.1 p.2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hPerPair
  -- Apply overlap-counting restriction to `badSet`.
  have hrestrict :
      ∑ p ∈ badSet,
          OneThird.Step4.pairWeight boundary witness p.1 p.2
        ≤ M * boundary.card :=
    overlap_counting_restrict richPairs witness boundary M badSet hbadSub hmult
  -- Chain.
  calc c_n * ∑ p ∈ badSet, w p.1 p.2
      ≤ c_d * ∑ p ∈ badSet,
          OneThird.Step4.pairWeight boundary witness p.1 p.2 := hsum
    _ ≤ c_d * (M * boundary.card) := Nat.mul_le_mul_left _ hrestrict
    _ = c_d * M * boundary.card := by ring

end G7

/-! ### §3 — `thm:step6` (`step6.tex:481`) -/

section ThmStep6

variable {Pair : Type*} [DecidableEq Pair]

/-- **`thm:step6` — Step 6 dichotomy (cleared-denominator)**
(`step6.tex:481-508`).

Fix parameters `η_n, η_d, δ_n, δ_d` with `η = η_n/η_d`, `δ = δ_n/δ_d`.
Given:

* `hSum : c_d · c_n⁻¹ · ∑_{bad active} w = c_n · sumBadW ≤ c_d · M · |∂S|`,
  i.e. `c_n · ∑ ≤ c_d · M · |∂S|` (output of `lem_sum_step4`), and

the dichotomy says: either

* **(i) Expansion.** `η_d · |∂S| ≥ η_n · M`, or
* **(ii) Coherence.** `δ_d · sumBadW ≤ δ_n · M`.

Choice `η_n = c_n · δ_n`, `η_d = c_d · M · δ_d` (or any equivalent
normalisation) makes the case split trivial: if the coherence case
fails, then `δ_d · sumBadW > δ_n · M`, which combined with the sum
bound gives `c_n · δ_n · M ≤ c_n · δ_d · sumBadW · ...`, yielding the
expansion bound.

In the abstract formulation we take the sum bound as hypothesis and
perform the case split explicitly. -/
theorem thm_step6
    (sumBadW M boundary c_n c_d δ_n δ_d : ℕ)
    (hSum : c_n * sumBadW ≤ c_d * M * boundary) :
    (c_n * δ_n * M ≤ c_d * M * δ_d * boundary) ∨
      (δ_d * sumBadW ≤ δ_n * M) := by
  classical
  by_cases hcoh : δ_d * sumBadW ≤ δ_n * M
  · exact Or.inr hcoh
  · refine Or.inl ?_
    -- ¬ δ_d · sumBadW ≤ δ_n · M   means   δ_n · M < δ_d · sumBadW,
    -- hence  c_n · δ_n · M < c_n · δ_d · sumBadW ≤ δ_d · c_d · M · boundary.
    have hlt : δ_n * M < δ_d * sumBadW := Nat.lt_of_not_le hcoh
    have h1 : c_n * δ_n * M ≤ c_n * δ_d * sumBadW := by
      have : c_n * (δ_n * M) ≤ c_n * (δ_d * sumBadW) :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
      linarith
    have h2 : c_n * δ_d * sumBadW = δ_d * (c_n * sumBadW) := by ring
    have h3 : δ_d * (c_n * sumBadW) ≤ δ_d * (c_d * M * boundary) :=
      Nat.mul_le_mul_left _ hSum
    linarith

/-- **`thm:step6` — closing contradiction in the rich case**
(`step6.tex:565-570`, `rem:G5-closes-dichotomy`).

Assume additionally the rich-case bound `c_R² · volS ≤ M`
(from `pair_overlap_sum_ge_vol`, `RichnessBound.lean`). Then the
expansion case (i) yields `η · c_R² · volS ≤ |∂S|`, i.e.\
conductance `≥ η · c_R²`. Hence under a strict low-conductance
hypothesis `boundary < η · c_R² · volS`, only the coherence case can
occur. -/
theorem thm_step6_rich_closure
    (sumBadW M boundary volS c_n c_d δ_n δ_d c_R : ℕ)
    (hSum : c_n * sumBadW ≤ c_d * M * boundary)
    (hRich : c_R ^ 2 * volS ≤ M)
    (hLow : c_n * δ_n * c_R ^ 2 * volS > c_d * M * δ_d * boundary) :
    δ_d * sumBadW ≤ δ_n * M := by
  rcases thm_step6 sumBadW M boundary c_n c_d δ_n δ_d hSum with hexp | hcoh
  · -- hexp : c_n·δ_n·M ≤ c_d·M·δ_d·boundary; combined with c_R²·volS ≤ M and hLow.
    have : c_n * δ_n * (c_R ^ 2 * volS) ≤ c_n * δ_n * M :=
      Nat.mul_le_mul_left _ hRich
    have : c_n * δ_n * c_R ^ 2 * volS ≤ c_d * M * δ_d * boundary := by
      have hchain : c_n * δ_n * (c_R ^ 2 * volS) ≤ c_d * M * δ_d * boundary :=
        le_trans this hexp
      calc c_n * δ_n * c_R ^ 2 * volS
          = c_n * δ_n * (c_R ^ 2 * volS) := by ring
        _ ≤ c_d * M * δ_d * boundary := hchain
    exact absurd this (Nat.not_le_of_gt hLow)
  · exact hcoh

end ThmStep6

/-! ### §4 — G8: `cor:pointwise` (`step6.tex:587`) -/

section CorPointwise

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Positive visibility count** — for a sign map `σ : Pair → Sign`,
the number of rich interfaces at `L` with positive orientation
(`σ_α = false`). -/
def posCount (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) : ℕ :=
  (richStar.filter (fun α => σ α = false ∧ L ∈ Fstar α)).card

/-- **Negative visibility count** — number of rich interfaces at `L`
with negative orientation (`σ_α = true`). -/
def negCount (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) : ℕ :=
  (richStar.filter (fun α => σ α = true ∧ L ∈ Fstar α)).card

/-- **Minority count** `m(L)` (`step6.tex:636`). -/
def minorityCount (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) : ℕ :=
  min (posCount richStar Fstar σ L) (negCount richStar Fstar σ L)

/-- **Pos + neg decomposition.** `n_+(L) + n_-(L) = I(L)`
(`step6.tex:626`). -/
theorem visibility_eq_pos_add_neg
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) :
    posCount richStar Fstar σ L + negCount richStar Fstar σ L
      = visibility richStar Fstar L := by
  classical
  unfold posCount negCount visibility
  -- Both decomposed filters are disjoint and their union equals the combined filter.
  have hdisjoint :
      Disjoint (richStar.filter (fun α => σ α = false ∧ L ∈ Fstar α))
               (richStar.filter (fun α => σ α = true ∧ L ∈ Fstar α)) := by
    rw [Finset.disjoint_filter]
    intros _ _ h1 h2
    rcases h1 with ⟨hf, _⟩
    rcases h2 with ⟨ht, _⟩
    rw [hf] at ht
    exact absurd ht (by decide)
  have hunion :
      richStar.filter (fun α => L ∈ Fstar α) =
        (richStar.filter (fun α => σ α = false ∧ L ∈ Fstar α))
          ∪ (richStar.filter (fun α => σ α = true ∧ L ∈ Fstar α)) := by
    ext α
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hα, hL⟩
      rcases hσ : σ α
      · exact Or.inl ⟨hα, by simp [hσ], hL⟩
      · exact Or.inr ⟨hα, by simp [hσ], hL⟩
    · rintro (⟨hα, _, hL⟩ | ⟨hα, _, hL⟩) <;> exact ⟨hα, hL⟩
  rw [hunion, Finset.card_union_of_disjoint hdisjoint]

/-- **Minority ≤ half of visibility.** `m(L) ≤ I(L) / 2`, equivalently
`2·m(L) ≤ I(L)`. -/
theorem minority_le_half
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) :
    2 * minorityCount richStar Fstar σ L ≤
      visibility richStar Fstar L := by
  unfold minorityCount
  have := visibility_eq_pos_add_neg richStar Fstar σ L
  omega

/-- **Key pointwise inequality** (`step6.tex:669`):
`m(L) · I(L) ≤ 2 · n_+(L) · n_-(L)`.

Proof: writing `n = n_+(L)`, `p = n_-(L)`, `m = min(n, p)`, `I = n+p`:
* if `n ≤ p`: `m·I = n·(n+p) ≤ 2·n·p` iff `n² ≤ n·p`, which holds
  since `n ≤ p`.
* symmetric. -/
theorem minority_mul_visibility_le_two_mul_pos_neg
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) :
    minorityCount richStar Fstar σ L *
        visibility richStar Fstar L ≤
      2 * (posCount richStar Fstar σ L * negCount richStar Fstar σ L) := by
  have hI := visibility_eq_pos_add_neg richStar Fstar σ L
  unfold minorityCount
  -- Let n = posCount, p = negCount.
  set n := posCount richStar Fstar σ L
  set p := negCount richStar Fstar σ L
  set I := visibility richStar Fstar L
  have hInp : n + p = I := hI
  rcases Nat.le_total n p with hnp | hpn
  · -- min = n, I = n + p, so n · I = n² + n·p ≤ 2·n·p since n² ≤ n·p.
    have : min n p = n := min_eq_left hnp
    rw [this]
    have hnn : n * n ≤ n * p := Nat.mul_le_mul_left _ hnp
    nlinarith [hInp]
  · have : min n p = p := min_eq_right hpn
    rw [this]
    have hpp : p * p ≤ n * p := Nat.mul_le_mul_right _ hpn
    nlinarith [hInp]

/-- **Aggregate minority-count bound** (`step6.tex:eq:mI-sum`).

If `∑_L 2·n_+(L)·n_-(L) ≤ R` (an upper bound on the disagreement
mass, as supplied by the coherence case and the double-counting
identity), then `∑_L m(L) · I(L) ≤ R`. -/
theorem cor_pointwise_aggregate
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (LP : Finset LinExt) (R : ℕ)
    (hdis : ∑ L ∈ LP,
        2 * (posCount richStar Fstar σ L * negCount richStar Fstar σ L) ≤ R) :
    ∑ L ∈ LP,
        minorityCount richStar Fstar σ L * visibility richStar Fstar L
      ≤ R := by
  classical
  have hpt :
      ∀ L ∈ LP,
        minorityCount richStar Fstar σ L *
            visibility richStar Fstar L ≤
          2 * (posCount richStar Fstar σ L *
              negCount richStar Fstar σ L) := by
    intro L _
    exact minority_mul_visibility_le_two_mul_pos_neg richStar Fstar σ L
  calc ∑ L ∈ LP,
        minorityCount richStar Fstar σ L * visibility richStar Fstar L
      ≤ ∑ L ∈ LP,
          2 * (posCount richStar Fstar σ L *
              negCount richStar Fstar σ L) := Finset.sum_le_sum hpt
    _ ≤ R := hdis

/-- **Markov step for pointwise coherence** (`step6.tex:692-713`,
eq.`eq:mI-vs-I2`, eq.`eq:markov-threshold`).

Under the aggregate bound `∑ m(L) · I(L) ≤ R` and a threshold
`t_n/t_d` (cleared denominator), the `I²`-weighted mass of the set
`A = {L : t_d · m(L) ≥ t_n · I(L)}` satisfies

  `t_n · ∑_{A} I(L)² ≤ t_d · R`.

The `I²`-weighted probability of `A` is then at most
`t_d · R / (t_n · M)`, with `M = ∑_L I(L)²`. -/
theorem cor_pointwise_markov
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (LP : Finset LinExt) (R t_n t_d : ℕ)
    (hAgg : ∑ L ∈ LP,
        minorityCount richStar Fstar σ L * visibility richStar Fstar L ≤ R) :
    t_n * ∑ L ∈ LP.filter (fun L =>
            t_n * visibility richStar Fstar L ≤
              t_d * minorityCount richStar Fstar σ L),
          (visibility richStar Fstar L) ^ 2
      ≤ t_d * R := by
  classical
  set A : Finset LinExt := LP.filter (fun L =>
      t_n * visibility richStar Fstar L ≤
        t_d * minorityCount richStar Fstar σ L) with hA_def
  -- On A, t_n · I² ≤ t_d · m · I   (multiply the def by I).
  have hAmem : A ⊆ LP := Finset.filter_subset _ _
  have hpt :
      ∀ L ∈ A,
        t_n * (visibility richStar Fstar L) ^ 2 ≤
          t_d * (minorityCount richStar Fstar σ L *
                 visibility richStar Fstar L) := by
    intro L hL
    rw [hA_def, Finset.mem_filter] at hL
    obtain ⟨_, hLdef⟩ := hL
    -- hLdef : t_n · I ≤ t_d · m. Multiply both sides by I.
    have : t_n * visibility richStar Fstar L *
            visibility richStar Fstar L ≤
          t_d * minorityCount richStar Fstar σ L *
            visibility richStar Fstar L :=
      Nat.mul_le_mul_right _ hLdef
    calc t_n * (visibility richStar Fstar L) ^ 2
        = t_n * visibility richStar Fstar L *
            visibility richStar Fstar L := by ring
      _ ≤ t_d * minorityCount richStar Fstar σ L *
            visibility richStar Fstar L := this
      _ = t_d * (minorityCount richStar Fstar σ L *
            visibility richStar Fstar L) := by ring
  -- Sum over A and chain.
  have hA_sum :
      t_n * ∑ L ∈ A, (visibility richStar Fstar L) ^ 2 ≤
        t_d * ∑ L ∈ A,
          (minorityCount richStar Fstar σ L *
           visibility richStar Fstar L) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hLP_sum :
      ∑ L ∈ A,
          (minorityCount richStar Fstar σ L *
           visibility richStar Fstar L) ≤
        ∑ L ∈ LP,
          (minorityCount richStar Fstar σ L *
           visibility richStar Fstar L) :=
    Finset.sum_le_sum_of_subset_of_nonneg hAmem
      (by intros; exact Nat.zero_le _)
  calc t_n * ∑ L ∈ A, (visibility richStar Fstar L) ^ 2
      ≤ t_d * ∑ L ∈ A,
          (minorityCount richStar Fstar σ L *
           visibility richStar Fstar L) := hA_sum
    _ ≤ t_d * ∑ L ∈ LP,
          (minorityCount richStar Fstar σ L *
           visibility richStar Fstar L) :=
        Nat.mul_le_mul_left _ hLP_sum
    _ ≤ t_d * R := Nat.mul_le_mul_left _ hAgg

/-- **`cor:pointwise` (G8) — Conclusion B, cleared-denominator form**
(`step6.tex:587-713`).

Given:
* Coherence-case input (output of `thm:step6` case (ii)), converted
  to a bound on disagreement mass: `∑ 2·n_+·n_- ≤ R`;
* The `I²`-weighted threshold `t_n/t_d`.

Conclude the Markov bound on the `I²`-weighted probability of the
"mostly disagreeing" event, cleared-denominator form:

  `t_n · ∑_{A} I(L)² ≤ t_d · R`,

where `A = {L : t_d · m(L) ≥ t_n · I(L)}` (the set where the
minority count exceeds the `t_n/t_d`-fraction of the visibility).

The sign function `s : LinExt → Sign` is the majority vote:
`s(L) = false` if `n_+(L) ≥ n_-(L)`, else `true`. On `LP \ A`,
`#{α ∈ Rich_L : σ_α ≠ s(L)} = m(L) < (t_n/t_d) · I(L)`, which is the
paper's form of Conclusion B. -/
theorem cor_pointwise
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (LP : Finset LinExt) (R t_n t_d : ℕ)
    (hdis : ∑ L ∈ LP,
        2 * (posCount richStar Fstar σ L * negCount richStar Fstar σ L) ≤ R) :
    t_n * ∑ L ∈ LP.filter (fun L =>
            t_n * visibility richStar Fstar L ≤
              t_d * minorityCount richStar Fstar σ L),
          (visibility richStar Fstar L) ^ 2
      ≤ t_d * R :=
  cor_pointwise_markov richStar Fstar σ LP R t_n t_d
    (cor_pointwise_aggregate richStar Fstar σ LP R hdis)

/-- **Majority-vote sign function.** `s(L) = false` if positive
orientations are in the majority at `L`, else `true`. Used in
`cor_pointwise` to identify the minority side. -/
def majoritySign (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) : Sign :=
  if negCount richStar Fstar σ L ≤ posCount richStar Fstar σ L
    then false
    else true

/-- **Majority vote identifies the minority count.** Under
`s := majoritySign`, the count `#{α ∈ Rich_L : σ_α ≠ s(L)}` equals
`m(L) = min(n_+, n_-)`. -/
theorem majority_disagree_eq_minority
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (σ : Pair → Sign) (L : LinExt) :
    (richStar.filter (fun α => L ∈ Fstar α ∧
        σ α ≠ majoritySign richStar Fstar σ L)).card
      = minorityCount richStar Fstar σ L := by
  classical
  change (richStar.filter (fun α => L ∈ Fstar α ∧
        σ α ≠ majoritySign richStar Fstar σ L)).card
      = min (posCount richStar Fstar σ L) (negCount richStar Fstar σ L)
  by_cases hge : negCount richStar Fstar σ L ≤ posCount richStar Fstar σ L
  · -- s = false, so α disagrees iff σ α = true; that is negCount.
    have hmaj : majoritySign richStar Fstar σ L = false := by
      unfold majoritySign; simp [hge]
    have hmin : min (posCount richStar Fstar σ L) (negCount richStar Fstar σ L)
        = negCount richStar Fstar σ L :=
      min_eq_right hge
    rw [hmin]
    have :
        richStar.filter (fun α => L ∈ Fstar α ∧
            σ α ≠ majoritySign richStar Fstar σ L)
          = richStar.filter (fun α => σ α = true ∧ L ∈ Fstar α) := by
      ext α
      simp only [Finset.mem_filter, hmaj]
      constructor
      · rintro ⟨hα, hL, hne⟩
        refine ⟨hα, ?_, hL⟩
        rcases hσα : σ α
        · exact absurd hσα hne
        · rfl
      · rintro ⟨hα, hσ, hL⟩
        refine ⟨hα, hL, ?_⟩
        rw [hσ]; decide
    rw [this]
    rfl
  · -- s = true, so α disagrees iff σ α = false; that is posCount.
    have hgt : posCount richStar Fstar σ L < negCount richStar Fstar σ L :=
      Nat.lt_of_not_le hge
    have hle : posCount richStar Fstar σ L ≤ negCount richStar Fstar σ L :=
      Nat.le_of_lt hgt
    have hmaj : majoritySign richStar Fstar σ L = true := by
      unfold majoritySign
      simp [hge]
    have hmin : min (posCount richStar Fstar σ L) (negCount richStar Fstar σ L)
        = posCount richStar Fstar σ L :=
      min_eq_left hle
    rw [hmin]
    have :
        richStar.filter (fun α => L ∈ Fstar α ∧
            σ α ≠ majoritySign richStar Fstar σ L)
          = richStar.filter (fun α => σ α = false ∧ L ∈ Fstar α) := by
      ext α
      simp only [Finset.mem_filter, hmaj]
      constructor
      · rintro ⟨hα, hL, hne⟩
        refine ⟨hα, ?_, hL⟩
        rcases hσα : σ α
        · rfl
        · exact absurd hσα hne
      · rintro ⟨hα, hσ, hL⟩
        refine ⟨hα, hL, ?_⟩
        rw [hσ]; decide
    rw [this]
    rfl

end CorPointwise

end Step6
end OneThird
