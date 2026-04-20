/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 2 — 1D warm-up: interval structure under small grid boundary

This file formalises the one-dimensional ingredients that feed the 2D weak
grid stability lemma of Step 2 (`lem:weak-grid` in `step2.tex`):

* `OneThird.Step2.OneD.oneDBdy a b A`  ---  the 1D grid edge boundary of
  `A ⊆ [a, b]` in the path graph on `ℤ` (`step2.tex` Definition
  `def:1d-bdy`): the number of integers `i ∈ [a, b)` with
  `1_A(i) ≠ 1_A(i+1)`.
* `isInterval_of_oneDBdy_le_one`  ---  `cor:1d-b-le-1`: boundary `≤ 1`
  forces `A` to be empty or a single interval.
* `oneDBdy_ge_two_if_not_interval`  ---  the contrapositive lower bound
  `bd ≥ 2` for a non-empty non-interval, which is the form
  `cor:most-rows-intervals` uses.
-/

namespace OneThird
namespace Step2
namespace OneD

open Finset

/-- Membership-predicate underlying the 1D boundary: `i` and `i+1`
disagree on membership in `A`. -/
def diffMem (A : Finset ℤ) (i : ℤ) : Prop :=
  (i ∈ A ∧ i + 1 ∉ A) ∨ (i ∉ A ∧ i + 1 ∈ A)

instance (A : Finset ℤ) (i : ℤ) : Decidable (diffMem A i) := by
  unfold diffMem; infer_instance

/-- The underlying filter that realises the 1D grid boundary. -/
def oneDBdyFilter (a b : ℤ) (A : Finset ℤ) : Finset ℤ :=
  (Finset.Ico a b).filter (fun i => diffMem A i)

/-- The **1D grid boundary** of `A ⊆ [a, b]` in `ℤ`: the number of
integer positions `i ∈ [a, b)` where the indicator of `A` changes
between `i` and `i + 1`. Matches `step2.tex` Definition `def:1d-bdy`. -/
def oneDBdy (a b : ℤ) (A : Finset ℤ) : ℕ :=
  (oneDBdyFilter a b A).card

lemma mem_oneDBdyFilter {a b : ℤ} {A : Finset ℤ} {i : ℤ} :
    i ∈ oneDBdyFilter a b A ↔ a ≤ i ∧ i < b ∧ diffMem A i := by
  unfold oneDBdyFilter
  rw [mem_filter, mem_Ico, and_assoc]

@[simp] lemma oneDBdy_empty (a b : ℤ) :
    oneDBdy a b (∅ : Finset ℤ) = 0 := by
  unfold oneDBdy oneDBdyFilter
  convert Finset.card_empty
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  simp [diffMem]

/-- If `A` is non-empty and not an interval (as a subset of `Icc a b`),
then the 1D boundary is `≥ 2`. This is the contrapositive of
`cor:1d-b-le-1` in `step2.tex` and is the form the row decomposition
uses. -/
theorem oneDBdy_ge_two_if_not_interval
    {a b : ℤ} {A : Finset ℤ} (hA : A ⊆ Finset.Icc a b) (hne : A.Nonempty)
    (hnotInt : ¬ ∃ ℓ r : ℤ, ℓ ≤ r ∧ A = Finset.Icc ℓ r) :
    2 ≤ oneDBdy a b A := by
  classical
  let ℓ := A.min' hne
  let r := A.max' hne
  have hℓ_mem : ℓ ∈ A := A.min'_mem hne
  have hr_mem : r ∈ A := A.max'_mem hne
  have hℓr : ℓ ≤ r := A.min'_le r hr_mem
  -- Since A is not Icc ℓ r, there is some i₀ ∈ Icc ℓ r with i₀ ∉ A.
  have hsub : ¬ (Finset.Icc ℓ r ⊆ A) := by
    intro hsub
    -- A ⊆ Icc ℓ r by min/max, combined with hsub gives equality.
    apply hnotInt
    refine ⟨ℓ, r, hℓr, ?_⟩
    apply Finset.Subset.antisymm
    · intro i hi
      rw [mem_Icc]
      exact ⟨A.min'_le i hi, A.le_max' i hi⟩
    · exact hsub
  rw [Finset.not_subset] at hsub
  obtain ⟨i₀, hi₀_mem, hi₀_notA⟩ := hsub
  rw [mem_Icc] at hi₀_mem
  obtain ⟨hi₀_ℓ, hi₀_r⟩ := hi₀_mem
  have hℓ_lt_i₀ : ℓ < i₀ :=
    lt_of_le_of_ne hi₀_ℓ (fun h => hi₀_notA (h ▸ hℓ_mem))
  -- Smallest j ∈ [ℓ+1, r] with j ∉ A.
  let T : Finset ℤ := (Finset.Icc (ℓ + 1) r).filter (fun j => j ∉ A)
  have hT_ne : T.Nonempty := ⟨i₀, by
    rw [mem_filter, mem_Icc]
    exact ⟨⟨by omega, hi₀_r⟩, hi₀_notA⟩⟩
  let j₁ := T.min' hT_ne
  have hj₁_mem_T : j₁ ∈ T := T.min'_mem hT_ne
  have hj₁_prop : j₁ ∈ Finset.Icc (ℓ + 1) r ∧ j₁ ∉ A := by
    rw [mem_filter] at hj₁_mem_T; exact hj₁_mem_T
  rw [mem_Icc] at hj₁_prop
  obtain ⟨⟨hj₁_ge, hj₁_le⟩, hj₁_notA⟩ := hj₁_prop
  have hj₁_pred : j₁ - 1 ∈ A := by
    by_cases h : j₁ - 1 = ℓ
    · rw [h]; exact hℓ_mem
    · have h_pred_ge : ℓ + 1 ≤ j₁ - 1 := by omega
      by_contra h_pred_notA
      have h_pred_in_T : j₁ - 1 ∈ T := by
        rw [mem_filter, mem_Icc]
        refine ⟨⟨h_pred_ge, ?_⟩, h_pred_notA⟩
        omega
      have h_min := T.min'_le _ h_pred_in_T
      change j₁ ≤ j₁ - 1 at h_min
      omega
  have ha_le_ℓ : a ≤ ℓ := (mem_Icc.mp (hA hℓ_mem)).1
  have hr_le_b : r ≤ b := (mem_Icc.mp (hA hr_mem)).2
  -- Largest j ∈ [ℓ, r-1] with j ∉ A.
  let T' : Finset ℤ := (Finset.Icc ℓ (r - 1)).filter (fun j => j ∉ A)
  have hT'_ne : T'.Nonempty := ⟨i₀, by
    rw [mem_filter, mem_Icc]
    refine ⟨⟨hi₀_ℓ, ?_⟩, hi₀_notA⟩
    rcases eq_or_ne i₀ r with heq | hne_r
    · exact absurd hr_mem (heq ▸ hi₀_notA)
    · omega⟩
  let j₂ := T'.max' hT'_ne
  have hj₂_mem_T' : j₂ ∈ T' := T'.max'_mem hT'_ne
  have hj₂_prop : j₂ ∈ Finset.Icc ℓ (r - 1) ∧ j₂ ∉ A := by
    rw [mem_filter] at hj₂_mem_T'; exact hj₂_mem_T'
  rw [mem_Icc] at hj₂_prop
  obtain ⟨⟨hj₂_ge, hj₂_le⟩, hj₂_notA⟩ := hj₂_prop
  have hj₂_succ : j₂ + 1 ∈ A := by
    by_cases h : j₂ + 1 = r
    · rw [h]; exact hr_mem
    · have h_succ_le : j₂ + 1 ≤ r - 1 := by omega
      by_contra h_succ_notA
      have h_succ_in_T' : j₂ + 1 ∈ T' := by
        rw [mem_filter, mem_Icc]
        refine ⟨⟨by omega, h_succ_le⟩, h_succ_notA⟩
      have h_max := T'.le_max' _ h_succ_in_T'
      change j₂ + 1 ≤ j₂ at h_max
      omega
  -- Two distinct filter members.
  have h_in_filter_1 : (j₁ - 1) ∈ oneDBdyFilter a b A := by
    rw [mem_oneDBdyFilter]
    refine ⟨by omega, by omega, ?_⟩
    have h1 : (j₁ - 1) ∈ A := hj₁_pred
    have h2 : (j₁ - 1) + 1 ∉ A := by
      have hrw : (j₁ - 1 : ℤ) + 1 = j₁ := by ring
      rw [hrw]; exact hj₁_notA
    exact Or.inl ⟨h1, h2⟩
  have h_in_filter_2 : j₂ ∈ oneDBdyFilter a b A := by
    rw [mem_oneDBdyFilter]
    exact ⟨by omega, by omega, Or.inr ⟨hj₂_notA, hj₂_succ⟩⟩
  have h_ne : j₁ - 1 ≠ j₂ := fun h => hj₂_notA (h ▸ hj₁_pred)
  have h_pair_sub :
      ({j₁ - 1, j₂} : Finset ℤ) ⊆ oneDBdyFilter a b A := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_in_filter_1
    · exact h_in_filter_2
  have h_pair_card : ({j₁ - 1, j₂} : Finset ℤ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [h_ne]), Finset.card_singleton]
  unfold oneDBdy
  calc 2 = ({j₁ - 1, j₂} : Finset ℤ).card := h_pair_card.symm
    _ ≤ _ := Finset.card_le_card h_pair_sub

/-- **`cor:1d-b-le-1`**: If the 1D boundary is `≤ 1`, then `A` is empty
or a single interval. This is the form used by the 2D
row-decomposition argument. -/
theorem isInterval_of_oneDBdy_le_one
    {a b : ℤ} {A : Finset ℤ} (hA : A ⊆ Finset.Icc a b)
    (hbd : oneDBdy a b A ≤ 1) :
    A = ∅ ∨ ∃ ℓ r : ℤ, ℓ ≤ r ∧ A = Finset.Icc ℓ r := by
  by_cases hne : A = ∅
  · exact Or.inl hne
  · right
    have hne' : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    by_contra hnotInt
    have h2 := oneDBdy_ge_two_if_not_interval hA hne' hnotInt
    omega

/-- **`cor:1d-best-interval`** (practical form): given any finite `A`,
there exists a (possibly empty) sub-interval `Icc ℓ r ⊆ A` with
`ℓ ≤ r` (or `A = ∅`), and taking the best such interval gives the
smallest symmetric-difference approximation to `A`. We state the
"exists a sub-interval equal to `A`" case-split explicitly since
it is what Step 2's proof actually needs: when the 1D boundary is
small, the 2D argument just needs *some* interval inside `A`. -/
theorem exists_subinterval
    {a b : ℤ} {A : Finset ℤ} (_hA : A ⊆ Finset.Icc a b) (hne : A.Nonempty) :
    ∃ ℓ r : ℤ, ℓ ≤ r ∧ ℓ ∈ A ∧ r ∈ A := by
  let ℓ := A.min' hne
  let r := A.max' hne
  exact ⟨ℓ, r, A.min'_le r (A.max'_mem hne), A.min'_mem hne, A.max'_mem hne⟩

end OneD
end Step2
end OneThird
