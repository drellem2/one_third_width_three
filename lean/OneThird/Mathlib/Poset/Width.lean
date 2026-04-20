/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import OneThird.Basic
import OneThird.Poset

/-!
# Width of a finite poset

The **width** of a finite poset is the maximum cardinality of an
antichain. This file develops the elementary properties of `width`
as a function `α → ℕ` for a finite poset `α`. Dilworth's theorem
identifies the width with the minimum number of chains needed to
partition the poset, but that is not developed here.

This file lives in the `OneThird/Mathlib/` tier — its results are
intentionally independent of the 1/3–2/3 conjecture and could be
extracted into mathlib as a small `Order.Width` module.

## Main definitions

* `OneThird.Mathlib.Poset.antichains α` — the `Finset (Finset α)` of
  all antichains of a finite poset `α`.
* `OneThird.Mathlib.Poset.width α` — the maximum cardinality of an
  antichain, with the convention `width α = 0` when `α` is empty.

## Main results

* `card_le_width` — every antichain has cardinality at most `width α`.
* `exists_antichain_card_eq_width` — the maximum is attained by some
  antichain.
* `width_le_card` — `width α ≤ Fintype.card α`.
* `width_eq_zero_iff_isEmpty`, `width_pos_iff_nonempty` — width is 0
  exactly on empty types.
* `hasWidthAtMost_iff_width_le`, `hasWidth_iff_width_eq` — the
  propositional `OneThird.HasWidthAtMost` / `OneThird.HasWidth` from
  `OneThird.Poset` agree with the function `width`.
* `width_le_one_of_isChain` — a poset whose universe is a chain has
  width at most one.
-/

open Finset

namespace OneThird
namespace Mathlib
namespace Poset

variable {α : Type*}

section Width
variable [PartialOrder α] [Fintype α]

/-- The set of antichains of a finite poset, viewed as a `Finset` of
`Finset α`. The empty antichain is always present. -/
noncomputable def antichains (α : Type*) [PartialOrder α] [Fintype α] :
    Finset (Finset α) :=
  letI : DecidablePred fun s : Finset α => IsAntichain (· ≤ ·) (s : Set α) :=
    fun _ => Classical.dec _
  (Finset.univ : Finset α).powerset.filter
    (fun s => IsAntichain (· ≤ ·) (s : Set α))

@[simp] lemma mem_antichains {s : Finset α} :
    s ∈ antichains α ↔ IsAntichain (· ≤ ·) (s : Set α) := by
  classical
  unfold antichains
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (Finset.mem_filter.mp h).2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), h⟩

lemma antichains_nonempty : (antichains α).Nonempty :=
  ⟨∅, mem_antichains.mpr (by simp [IsAntichain.empty])⟩

/-- The **width** of a finite poset: the maximum cardinality of an
antichain. By convention `width α = 0` when `α` is empty. -/
noncomputable def width (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  (antichains α).sup Finset.card

/-- Every antichain has cardinality at most the width. -/
theorem card_le_width {s : Finset α}
    (hs : IsAntichain (· ≤ ·) (s : Set α)) : s.card ≤ width α :=
  Finset.le_sup (f := Finset.card) (mem_antichains.mpr hs)

/-- The supremum defining `width α` is attained by some antichain. -/
theorem exists_antichain_card_eq_width :
    ∃ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) ∧ s.card = width α := by
  obtain ⟨s, hs, heq⟩ :=
    Finset.exists_mem_eq_sup (antichains α) antichains_nonempty Finset.card
  exact ⟨s, mem_antichains.mp hs, heq.symm⟩

/-- The width is at most the cardinality of the carrier. -/
theorem width_le_card : width α ≤ Fintype.card α := by
  obtain ⟨s, _, hs⟩ := exists_antichain_card_eq_width (α := α)
  rw [← hs, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ s)

@[simp] theorem width_eq_zero_of_isEmpty [IsEmpty α] : width α = 0 := by
  refine Nat.le_antisymm ?_ (Nat.zero_le _)
  refine width_le_card.trans_eq ?_
  simp [Fintype.card_eq_zero]

theorem width_pos_of_nonempty [Nonempty α] : 0 < width α := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have hs : IsAntichain (· ≤ ·) (({a} : Finset α) : Set α) := by
    rw [Finset.coe_singleton]
    exact IsAntichain.singleton
  have h := card_le_width hs
  rw [Finset.card_singleton] at h
  exact h

theorem width_eq_zero_iff_isEmpty : width α = 0 ↔ IsEmpty α := by
  refine ⟨fun h => ?_, fun _ => width_eq_zero_of_isEmpty⟩
  rw [← not_nonempty_iff]
  intro hne
  exact (Nat.lt_irrefl 0) (h ▸ width_pos_of_nonempty)

theorem width_pos_iff_nonempty : 0 < width α ↔ Nonempty α := by
  rw [Nat.pos_iff_ne_zero, ne_eq, width_eq_zero_iff_isEmpty, not_isEmpty_iff]

/-- Compatibility with the propositional `HasWidthAtMost` from
`OneThird.Poset`. -/
theorem hasWidthAtMost_iff_width_le {k : ℕ} :
    OneThird.HasWidthAtMost α k ↔ width α ≤ k := by
  refine ⟨fun h => ?_, fun h s hs => (card_le_width hs).trans h⟩
  obtain ⟨s, hs, hcard⟩ := exists_antichain_card_eq_width (α := α)
  exact hcard ▸ h s hs

/-- Compatibility with the propositional `HasWidth` from
`OneThird.Poset`. -/
theorem hasWidth_iff_width_eq {k : ℕ} :
    OneThird.HasWidth α k ↔ width α = k := by
  refine ⟨fun ⟨h1, s, hs, hcard⟩ => ?_, fun hw => ?_⟩
  · refine Nat.le_antisymm (hasWidthAtMost_iff_width_le.mp h1) ?_
    exact hcard ▸ card_le_width hs
  · refine ⟨hasWidthAtMost_iff_width_le.mpr hw.le, ?_⟩
    obtain ⟨s, hs, hcard⟩ := exists_antichain_card_eq_width (α := α)
    exact ⟨s, hs, hcard.trans hw⟩

/-- A poset whose universe is a chain has width at most one. -/
theorem width_le_one_of_isChain (h : IsChain (· ≤ ·) (Set.univ : Set α)) :
    width α ≤ 1 := by
  rw [← hasWidthAtMost_iff_width_le]
  intro s hs
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  rcases h (Set.mem_univ a) (Set.mem_univ b) hab with hle | hle
  · exact hs ha hb hab hle
  · exact hs hb ha (Ne.symm hab) hle

end Width

end Poset
end Mathlib
end OneThird
