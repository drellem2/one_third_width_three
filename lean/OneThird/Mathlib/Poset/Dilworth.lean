/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.Poset.Width

/-!
# Dilworth's theorem for finite posets

A finite partial order of width `w` admits a chain cover of size `w`: there
is a function `f : α → Fin w` whose fibers are chains. Standard proof by
strong induction on `|α|`, splitting on whether removing a maximal element
decreases the width.

This file lives in the `OneThird/Mathlib/` tier — it is a self-contained
mathlib-flavored contribution, independent of the 1/3–2/3 conjecture, and
could be extracted as a small `Order.Dilworth` module.

## Main definitions

* `OneThird.Mathlib.Poset.HasChainCover` — a cover of `α` by `w` chains,
  presented as a function `f : α → Fin w` whose fibers are chains.

## Main results

* `OneThird.Mathlib.Poset.HasChainCover.mono` — a cover of size `w`
  extends to a cover of any larger size.
* `OneThird.Mathlib.Poset.width_le_of_hasChainCover` — the easy direction:
  every chain cover has at least `width α` classes.
* `OneThird.Mathlib.Poset.hasChainCover_of_hasWidth` — Dilworth's theorem:
  if `α` has width `w`, then it admits a chain cover of size `w`.
* `OneThird.Mathlib.Poset.hasChainCover_iff_width_le` — the width is
  the minimum number of chains in a chain cover.
-/

open Finset

namespace OneThird
namespace Mathlib
namespace Poset

variable {α : Type*}

section HasChainCover

/-- A chain cover of `α` by `w` chains is a function `f : α → Fin w` such
that each fiber `{x | f x = i}` is a chain. -/
def HasChainCover (α : Type*) [PartialOrder α] (w : ℕ) : Prop :=
  ∃ f : α → Fin w, ∀ i : Fin w, IsChain (· ≤ ·) ({x | f x = i} : Set α)

variable [PartialOrder α]

/-- An empty type is covered by `0` chains. -/
theorem hasChainCover_zero_of_isEmpty [IsEmpty α] : HasChainCover α 0 :=
  ⟨fun a => isEmptyElim a, fun i => i.elim0⟩

/-- A chain cover of size `w` gives a chain cover of any larger size
`w'` by leaving extra classes empty. -/
theorem HasChainCover.mono {w w' : ℕ} (hw : HasChainCover α w) (h : w ≤ w') :
    HasChainCover α w' := by
  obtain ⟨f, hf⟩ := hw
  refine ⟨fun a => (f a).castLE h, fun i => ?_⟩
  intro x hx y hy hxy
  simp only [Set.mem_setOf_eq] at hx hy
  have hfxy : f x = f y := by
    apply Fin.castLE_injective h
    rw [hx, hy]
  have hxmem : x ∈ ({z | f z = f x} : Set α) := rfl
  have hymem : y ∈ ({z | f z = f x} : Set α) := hfxy.symm
  exact hf (f x) hxmem hymem hxy

end HasChainCover

section Dilworth

variable [PartialOrder α] [Fintype α] [DecidableEq α]

/-- The universal cover where each element is in its own class: a chain
cover of size `Fintype.card α`. Singletons are chains. -/
theorem hasChainCover_card : HasChainCover α (Fintype.card α) := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  refine ⟨e, fun _ => ?_⟩
  intro x hx y hy hxy
  simp only [Set.mem_setOf_eq] at hx hy
  exact absurd (e.injective (hx.trans hy.symm)) hxy

/-- Chain covers of size `< width α` do not exist: every chain cover has
at least `width α` classes. This is the easy direction of Dilworth. -/
theorem width_le_of_hasChainCover {w : ℕ} (hw : HasChainCover α w) :
    width α ≤ w := by
  classical
  obtain ⟨f, hf⟩ := hw
  obtain ⟨s, hs, hcard⟩ := exists_antichain_card_eq_width (α := α)
  rw [← hcard]
  have hinj : Set.InjOn f (s : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    have hchain := hf (f x)
    have hxmem : x ∈ ({z | f z = f x} : Set α) := rfl
    have hymem : y ∈ ({z | f z = f x} : Set α) := by
      show f y = f x
      exact hxy.symm
    rcases hchain hxmem hymem hne with hle | hle
    · exact hs hx hy hne hle
    · exact hs hy hx (Ne.symm hne) hle
  have hcard_image : s.card = (s.image f).card := by
    symm
    apply Finset.card_image_of_injOn
    intro x hx y hy
    exact hinj hx hy
  rw [hcard_image]
  calc (s.image f).card
      ≤ (Finset.univ : Finset (Fin w)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = w := (Finset.card_univ).trans (Fintype.card_fin w)

/-- **Dilworth's theorem** (finite case): a finite partial order of width `w`
admits a chain cover of size `w`.

*Proof sketch.* Strong induction on `Fintype.card α`. In the inductive step,
pick a maximal element `a ∈ α` and let `P' = α \ {a}` with `k' = width P'`.

- If `k' < w`, inductively cover `P'` with `k'` chains and add `{a}` as a
  new (possibly empty-if-`k' = w - 1`) chain.
- If `k' = w`, use Galvin's antichain-split: pick a maximum antichain `A` in
  `P'` (size `w`), and let `D = {x ∈ α : ∃ a' ∈ A, x ≤ a'}`,
  `U = {x ∈ α : ∃ a' ∈ A, a' ≤ x}`. Then `D ∩ U = A` and `D ∪ U = α`, with
  `a ∈ U \ D` (so `|D| < |α|`). Inductively cover `D` with `w` chains aligned
  so chain `i` contains `a_i ∈ A`; do the same for `U`; splice along `A`.

The full formalization is substantial (≈500–1000 lines of Lean) and is the
subject of ongoing work tracked as `mg-19ca`. -/
theorem hasChainCover_of_hasWidth {w : ℕ} (hw : HasWidth α w) :
    HasChainCover α w := by
  sorry

/-- Dilworth's theorem specialized to `width α`. -/
theorem hasChainCover_width : HasChainCover α (width α) := by
  classical
  refine hasChainCover_of_hasWidth ?_
  exact (hasWidth_iff_width_eq).mpr rfl

/-- Dilworth duality (finite case): a chain cover of size `w` exists iff
`width α ≤ w`. -/
theorem hasChainCover_iff_width_le {w : ℕ} :
    HasChainCover α w ↔ width α ≤ w := by
  refine ⟨width_le_of_hasChainCover, fun h => (hasChainCover_width (α := α)).mono h⟩

end Dilworth

end Poset
end Mathlib
end OneThird
