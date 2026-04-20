/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset

/-!
# Step 1: Common-neighbor chain in width 3

Proof of `commonNbhd_isChain_of_width3` (`lem:CNchain-width3` in
`step1.tex`): in a width-3 poset, the common-neighbor set of any
incomparable pair `x ∥ y` is a chain.

Strategy. If `z, z' ∈ commonNbhd x y` were incomparable, the set
`{x, y, z, z'}` would be a 4-element antichain: `x ∥ y` by hypothesis,
`z ∥ x`, `z ∥ y`, `z' ∥ x`, `z' ∥ y` by `commonNbhd` membership, and
`z ∥ z'` by assumption. This contradicts `HasWidthAtMost α 3`.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α]

/-- In a width-3 poset, every two elements of `commonNbhd x y` are
comparable — i.e., the common-neighbor set is a chain.
Corresponds to `lem:CNchain-width3` in `step1.tex`. -/
theorem commonNbhd_isChain_of_width3
    (hP : HasWidthAtMost α 3) {x y : α} (hxy : x ∥ y) :
    IsChain (· ≤ ·) (commonNbhd x y) := by
  classical
  intro z hz z' hz' hne
  obtain ⟨hzx, hzy⟩ := hz
  obtain ⟨hz'x, hz'y⟩ := hz'
  by_contra hnc
  rw [not_or] at hnc
  obtain ⟨hle1, hle2⟩ := hnc
  have hzz' : z ∥ z' := ⟨hle1, hle2⟩
  have hxy_ne : x ≠ y := fun h => hxy.1 (h ▸ le_refl x)
  have hxz_ne : x ≠ z := fun h => hzx.2 (h ▸ le_refl x)
  have hxz'_ne : x ≠ z' := fun h => hz'x.2 (h ▸ le_refl x)
  have hyz_ne : y ≠ z := fun h => hzy.2 (h ▸ le_refl y)
  have hyz'_ne : y ≠ z' := fun h => hz'y.2 (h ▸ le_refl y)
  let s : Finset α := {x, y, z, z'}
  have hs_eq : s = insert x (insert y (insert z ({z'} : Finset α))) := rfl
  have hs_antichain : IsAntichain (· ≤ ·) (↑s : Set α) := by
    intro a ha b hb hab hle
    simp only [hs_eq, Finset.coe_insert, Finset.coe_singleton,
               Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      first
        | exact hab rfl
        | exact hxy.1 hle
        | exact hxy.2 hle
        | exact hzx.1 hle
        | exact hzx.2 hle
        | exact hzy.1 hle
        | exact hzy.2 hle
        | exact hz'x.1 hle
        | exact hz'x.2 hle
        | exact hz'y.1 hle
        | exact hz'y.2 hle
        | exact hzz'.1 hle
        | exact hzz'.2 hle
  have hz_notmem : z ∉ ({z'} : Finset α) := by
    simp only [Finset.mem_singleton]; exact hne
  have hy_notmem : y ∉ (insert z ({z'} : Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hyz_ne, hyz'_ne⟩
  have hx_notmem : x ∉ (insert y (insert z ({z'} : Finset α))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy_ne, hxz_ne, hxz'_ne⟩
  have hs_card : s.card = 4 := by
    rw [hs_eq, Finset.card_insert_of_notMem hx_notmem,
        Finset.card_insert_of_notMem hy_notmem,
        Finset.card_insert_of_notMem hz_notmem,
        Finset.card_singleton]
  have h3 : s.card ≤ 3 := hP s hs_antichain
  omega

end OneThird
