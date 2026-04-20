/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.Grid2D
import OneThird.Step2.OneD
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Step 2 — Directional decomposition of the 2D grid boundary

This file formalises the 2D row/column decomposition of `∂_D A` that
turns the 1D warm-up (`OneThird/Step2/OneD.lean`) into a statement
about rows and columns of an order-convex subset of `ℤ²`. It covers
`lem:row-decomp` (in its consumer form) and `cor:most-rows-intervals`
from `step2.tex`:

* `rowSlice D i`  ---  row `i` of a Finset `D ⊆ ℤ²`: the Finset of
  second coordinates with `(i, ·) ∈ D`.
* `rowSlice_ordConvex_isInterval`  ---  rows of an order-convex
  `D ⊆ ℤ²` are intervals of `ℤ`.
* `horizRowBdy_le_gridBdy`  ---  horizontal boundary edges in a row
  inject into the full 2D boundary `gridBdy D A`.
* `twice_badRows_le_gridBdy_card`  ---  `cor:most-rows-intervals`:
  for order-convex `D` and any `A ⊆ D`, the number of rows where
  `A_i` is non-empty but not a single interval is at most
  `|gridBdy D A| / 2`.
-/

namespace OneThird
namespace Step2
namespace RowDecomp

open Finset OneThird.Mathlib.Grid2D

/-- The row slice of a finset `D ⊆ ℤ²` at row `i`: the set of second
coordinates `j` with `(i, j) ∈ D`. -/
def rowSlice (D : Finset (ℤ × ℤ)) (i : ℤ) : Finset ℤ :=
  (D.filter (fun p => p.1 = i)).image Prod.snd

lemma mem_rowSlice {D : Finset (ℤ × ℤ)} {i j : ℤ} :
    j ∈ rowSlice D i ↔ (i, j) ∈ D := by
  unfold rowSlice
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨⟨i', j'⟩, ⟨hD, hi⟩, hj⟩
    dsimp at hi hj
    subst hi
    subst hj
    exact hD
  · intro hij
    exact ⟨(i, j), ⟨hij, rfl⟩, rfl⟩

/-- Rows of an order-convex `D : Set (ℤ × ℤ)` are order-convex (hence
"intervals" in `ℤ`). We phrase the result for Finsets: if `D` (as a
Set) is order-convex and `D_i` has two members `j₁ ≤ j₂`, every
integer in `[j₁, j₂]` is in `D_i`. -/
theorem rowSlice_ordConvex {D : Finset (ℤ × ℤ)}
    (hD : IsOrdConvex (D : Set (ℤ × ℤ))) (i : ℤ) {j₁ j₂ : ℤ}
    (hj₁ : j₁ ∈ rowSlice D i) (hj₂ : j₂ ∈ rowSlice D i) (hle : j₁ ≤ j₂)
    {j : ℤ} (hj : j₁ ≤ j ∧ j ≤ j₂) : j ∈ rowSlice D i := by
  rw [mem_rowSlice] at hj₁ hj₂
  rw [mem_rowSlice]
  have hp : ((i, j₁) : ℤ × ℤ) ≤ (i, j₂) := ⟨le_refl _, hle⟩
  have hq : (i, j) ∈ Set.Icc ((i, j₁) : ℤ × ℤ) (i, j₂) := by
    refine ⟨⟨le_refl _, hj.1⟩, le_refl _, hj.2⟩
  have : (i, j) ∈ (D : Set (ℤ × ℤ)) :=
    hD.icc_subset (by exact_mod_cast hj₁) (by exact_mod_cast hj₂) hq
  exact_mod_cast this

/-- When non-empty and with `D` order-convex, the row slice is a closed
interval. -/
theorem rowSlice_eq_Icc_of_ordConvex {D : Finset (ℤ × ℤ)}
    (hD : IsOrdConvex (D : Set (ℤ × ℤ))) (i : ℤ)
    (hne : (rowSlice D i).Nonempty) :
    ∃ a b : ℤ, a ≤ b ∧ rowSlice D i = Finset.Icc a b := by
  classical
  let a := (rowSlice D i).min' hne
  let b := (rowSlice D i).max' hne
  have ha_mem : a ∈ rowSlice D i := (rowSlice D i).min'_mem hne
  have hb_mem : b ∈ rowSlice D i := (rowSlice D i).max'_mem hne
  have hab : a ≤ b := (rowSlice D i).min'_le b hb_mem
  refine ⟨a, b, hab, ?_⟩
  apply Finset.Subset.antisymm
  · intro j hj
    rw [mem_Icc]
    exact ⟨(rowSlice D i).min'_le j hj, (rowSlice D i).le_max' j hj⟩
  · intro j hj
    rw [mem_Icc] at hj
    exact rowSlice_ordConvex hD i ha_mem hb_mem hab hj

/-- "Bad" rows where `A_i` is non-empty but not a single interval. -/
noncomputable def badRowsAt (D A : Finset (ℤ × ℤ)) : Finset ℤ := by
  classical exact
    ((D.image Prod.fst)).filter (fun i =>
      (rowSlice A i).Nonempty ∧
      ¬ ∃ ℓ r : ℤ, ℓ ≤ r ∧ rowSlice A i = Finset.Icc ℓ r)

lemma mem_badRowsAt {D A : Finset (ℤ × ℤ)} {i : ℤ} :
    i ∈ badRowsAt D A ↔
      i ∈ D.image Prod.fst ∧
      (rowSlice A i).Nonempty ∧
      ¬ ∃ ℓ r : ℤ, ℓ ≤ r ∧ rowSlice A i = Finset.Icc ℓ r := by
  classical
  unfold badRowsAt
  simp only [Finset.mem_filter]

/-- A "horizontal" boundary edge in row `i`: an element `(u, v)` of
`gridBdy D A` with `u.1 = v.1 = i` and `v.2 = u.2 + 1` or
`v.2 = u.2 - 1`. We pick the ordered pair form where `u ∈ A` and
`v ∈ D \ A`, matching `gridBdy`. -/
def horizRowBdy (D A : Finset (ℤ × ℤ)) (i : ℤ) :
    Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (gridBdy D A).filter (fun p => p.1.1 = i ∧ p.2.1 = i)

lemma mem_horizRowBdy {D A : Finset (ℤ × ℤ)}
    {i : ℤ} {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ horizRowBdy D A i ↔ p ∈ gridBdy D A ∧ p.1.1 = i ∧ p.2.1 = i := by
  unfold horizRowBdy
  rw [mem_filter]

/-- If `D` is order-convex, horizontal boundary edges in row `i` inject
into 1D boundary edges of `rowSlice A i` as a subset of `rowSlice D i`.

Specifically, each horizontal edge `((i, j), (i, j'))` with
`|j - j'| = 1`, `(i, j) ∈ A`, `(i, j') ∈ D \ A` gives rise to an
integer `min(j, j') ∈ [a, b)` (where `rowSlice D i = Icc a b`) where
the indicator of `rowSlice A i` changes. -/
theorem twice_horizRowBdy_le_oneDBdy {D A : Finset (ℤ × ℤ)}
    (hD : IsOrdConvex (D : Set (ℤ × ℤ))) (hA : A ⊆ D) (i : ℤ)
    (hne : (rowSlice A i).Nonempty)
    (hNotInt : ¬ ∃ ℓ r : ℤ, ℓ ≤ r ∧ rowSlice A i = Finset.Icc ℓ r) :
    2 ≤ (horizRowBdy D A i).card := by
  classical
  -- A ⊆ D ⇒ rowSlice A i ⊆ rowSlice D i.
  have hA_row_sub : rowSlice A i ⊆ rowSlice D i := by
    intro j hj
    rw [mem_rowSlice] at hj ⊢
    exact hA hj
  -- rowSlice D i must be nonempty (since rowSlice A i ⊆ it and hne).
  have hD_row_ne : (rowSlice D i).Nonempty :=
    hne.mono hA_row_sub
  obtain ⟨a, b, hab, hD_row_eq⟩ := rowSlice_eq_Icc_of_ordConvex hD i hD_row_ne
  have hA_row_sub_Icc : rowSlice A i ⊆ Finset.Icc a b := by
    rw [← hD_row_eq]; exact hA_row_sub
  -- Apply 1D component lower bound.
  have h1D := OneThird.Step2.OneD.oneDBdy_ge_two_if_not_interval
    hA_row_sub_Icc hne hNotInt
  -- Now build an injection from the 1D filter into horizRowBdy.
  let rowFilter := OneThird.Step2.OneD.oneDBdyFilter a b (rowSlice A i)
  have hrowFilter_card : 2 ≤ rowFilter.card := h1D
  -- For each k ∈ rowFilter, produce an edge in horizRowBdy.
  -- k ∈ [a, b), and exactly one of k, k+1 is in rowSlice A i.
  -- Both k and k+1 are in rowSlice D i = Icc a b (since a ≤ k < b ≤ b, so a ≤ k+1 ≤ b).
  -- So one of (i, k), (i, k+1) is in A, and the other is in D \ A.
  -- They are L1-adjacent.
  let φ : ℤ → (ℤ × ℤ) × (ℤ × ℤ) := fun k =>
    if k ∈ rowSlice A i then ((i, k), (i, k + 1)) else ((i, k + 1), (i, k))
  have hφ_mem : ∀ k ∈ rowFilter, φ k ∈ horizRowBdy D A i := by
    intro k hk
    rw [OneThird.Step2.OneD.mem_oneDBdyFilter] at hk
    obtain ⟨hka, hkb, hdiff⟩ := hk
    unfold OneThird.Step2.OneD.diffMem at hdiff
    have hk_in_D_row : k ∈ rowSlice D i := by
      rw [hD_row_eq, mem_Icc]; exact ⟨hka, by omega⟩
    have hk1_in_D_row : (k + 1) ∈ rowSlice D i := by
      rw [hD_row_eq, mem_Icc]; exact ⟨by omega, by omega⟩
    rw [mem_rowSlice] at hk_in_D_row hk1_in_D_row
    unfold φ
    split_ifs with hkA
    · -- k ∈ rowSlice A i, so k+1 ∉ rowSlice A i (from hdiff)
      have hk1_notA : k + 1 ∉ rowSlice A i := by
        rcases hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd hkA h1
      have hk1_notA' : (i, k + 1) ∉ A := by
        intro h; exact hk1_notA (mem_rowSlice.mpr h)
      have hkA' : (i, k) ∈ A := mem_rowSlice.mp hkA
      rw [mem_horizRowBdy, mem_gridBdy]
      refine ⟨⟨hkA', hk1_in_D_row, hk1_notA', ?_⟩, rfl, rfl⟩
      unfold L1Adj l1dist
      simp only
      have : ((k : ℤ) - (k + 1)).natAbs = 1 := by
        have heq : (k : ℤ) - (k + 1) = -1 := by ring
        rw [heq]; rfl
      omega
    · -- k ∉ rowSlice A i, so k+1 ∈ rowSlice A i (from hdiff)
      have hk1_A : k + 1 ∈ rowSlice A i := by
        rcases hdiff with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd h1 hkA
        · exact h2
      have hk1_A' : (i, k + 1) ∈ A := mem_rowSlice.mp hk1_A
      have hkA' : (i, k) ∉ A := by
        intro h; exact hkA (mem_rowSlice.mpr h)
      rw [mem_horizRowBdy, mem_gridBdy]
      refine ⟨⟨hk1_A', hk_in_D_row, hkA', ?_⟩, rfl, rfl⟩
      unfold L1Adj l1dist
      simp only
      have : ((k + 1 : ℤ) - k).natAbs = 1 := by
        have heq : ((k + 1 : ℤ) - k) = 1 := by ring
        rw [heq]; rfl
      omega
  -- φ is injective on rowFilter.
  have hφ_inj : Set.InjOn φ rowFilter := by
    intro k hk k' hk' hφ_eq
    -- From φ k = φ k' read off k.
    unfold φ at hφ_eq
    split_ifs at hφ_eq with hkA hk'A hk'A
    · -- both k and k' in A: edges are ((i,k),(i,k+1)) = ((i,k'),(i,k'+1))
      have := (Prod.mk.inj hφ_eq).1
      exact (Prod.mk.inj this).2
    · have := (Prod.mk.inj hφ_eq).1
      have hkk' : k = k' + 1 := by
        have := (Prod.mk.inj this).2
        exact this
      have := (Prod.mk.inj hφ_eq).2
      have hk1k' : k + 1 = k' := by
        have := (Prod.mk.inj this).2
        exact this
      -- k = k'+1 and k+1 = k' ⇒ contradiction.
      omega
    · have := (Prod.mk.inj hφ_eq).1
      have hk1k' : k + 1 = k' := by exact (Prod.mk.inj this).2
      have := (Prod.mk.inj hφ_eq).2
      have hkk1 : k = k' + 1 := by exact (Prod.mk.inj this).2
      omega
    · have := (Prod.mk.inj hφ_eq).1
      have hk1k'1 : k + 1 = k' + 1 := by exact (Prod.mk.inj this).2
      omega
  calc 2 ≤ rowFilter.card := h1D
    _ = (rowFilter.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
    _ ≤ (horizRowBdy D A i).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨k, hk_mem, rfl⟩ := hx
        exact hφ_mem k hk_mem

/-- Horizontal row boundaries with distinct row indices are disjoint. -/
lemma horizRowBdy_disjoint {D A : Finset (ℤ × ℤ)} {i i' : ℤ} (h : i ≠ i') :
    Disjoint (horizRowBdy D A i) (horizRowBdy D A i') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_horizRowBdy] at hp hp'
  obtain ⟨_, hi, _⟩ := hp
  obtain ⟨_, hi', _⟩ := hp'
  exact h (hi.symm.trans hi')

/-- All horizontal boundaries (ranging over first coordinates of `D`)
are a subset of `gridBdy D A`. -/
lemma horizRowBdy_subset_gridBdy (D A : Finset (ℤ × ℤ)) (i : ℤ) :
    horizRowBdy D A i ⊆ gridBdy D A := by
  intro p hp
  rw [mem_horizRowBdy] at hp
  exact hp.1

/-- **`cor:most-rows-intervals`**: For order-convex `D ⊆ ℤ²` and
`A ⊆ D`, the number of rows where `A_i` is non-empty but not a single
interval is at most `|gridBdy D A| / 2`. Equivalently,
`2 · #badRows ≤ |gridBdy D A|`. -/
theorem twice_badRows_le_gridBdy_card {D A : Finset (ℤ × ℤ)}
    (hD : IsOrdConvex (D : Set (ℤ × ℤ))) (hA : A ⊆ D) :
    2 * (badRowsAt D A).card ≤ (gridBdy D A).card := by
  classical
  -- Sum over bad rows of 2 ≤ |horizRowBdy D A i|; horizRowBdy's over distinct rows are disjoint.
  have h_sum : ∑ i ∈ badRowsAt D A, (horizRowBdy D A i).card
      ≤ (gridBdy D A).card := by
    -- Use the disjoint union bound.
    have h_disj : (badRowsAt D A : Set ℤ).Pairwise
        (fun i i' => Disjoint (horizRowBdy D A i) (horizRowBdy D A i')) := by
      intro i _ i' _ hii'
      exact horizRowBdy_disjoint hii'
    calc ∑ i ∈ badRowsAt D A, (horizRowBdy D A i).card
        = (Finset.biUnion (badRowsAt D A) (horizRowBdy D A)).card := by
          rw [Finset.card_biUnion (by
            intro i hi i' hi' hii'
            exact horizRowBdy_disjoint hii')]
      _ ≤ (gridBdy D A).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_biUnion] at hp
          obtain ⟨i, _, hpi⟩ := hp
          exact horizRowBdy_subset_gridBdy D A i hpi
  have h_each : ∀ i ∈ badRowsAt D A, 2 ≤ (horizRowBdy D A i).card := by
    intro i hi
    rw [mem_badRowsAt] at hi
    obtain ⟨_, hne, hnotInt⟩ := hi
    exact twice_horizRowBdy_le_oneDBdy hD hA i hne hnotInt
  have h_const : (2 * (badRowsAt D A).card : ℕ)
      = ∑ _i ∈ badRowsAt D A, (2 : ℕ) := by
    simp [Finset.sum_const, mul_comm]
  calc 2 * (badRowsAt D A).card
      = ∑ _i ∈ badRowsAt D A, (2 : ℕ) := h_const
    _ ≤ ∑ i ∈ badRowsAt D A, (horizRowBdy D A i).card := by
          gcongr with i hi
          exact h_each i hi
    _ ≤ (gridBdy D A).card := h_sum

end RowDecomp
end Step2
end OneThird
