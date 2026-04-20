/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Hom.Basic

/-!
# Ordinal sum of posets and indecomposable posets

Mathlib-flavored wrappers for B6/B7 of `lean/MATHLIB_GAPS.md`:

* `OneThird.Mathlib.Poset.ordSum α β` — the ordinal sum of two posets,
  a thin abbreviation on top of mathlib's lexicographic `α ⊕ₗ β`.
* `OneThird.Mathlib.Poset.Indecomposable α` — `α` is not order-isomorphic
  to a non-trivial ordinal sum.

## Main results

* `Indecomposable.of_unique` — singleton posets are indecomposable.
* `not_indecomposable_two_chain` — the two-element chain `Unit ⊕ₗ Unit`
  is decomposable.
* `Indecomposable.exists_incomp` — **`lem:indec-incompairs`**
  (`step8.tex:165`): in a finite indecomposable poset of size `≥ 2`,
  every element has an incomparable partner.
-/

namespace OneThird.Mathlib.Poset

open Sum

universe u

/-- Ordinal sum of two partially ordered types, defined as the mathlib
lexicographic sum `α ⊕ₗ β = Lex (α ⊕ β)`. Every element of `α` sits below
every element of `β`, and the original orders are preserved within each
summand. -/
abbrev ordSum (α β : Type u) : Type u := α ⊕ₗ β

namespace ordSum

/-- Left injection into `ordSum α β`. -/
abbrev inL {α β : Type u} (a : α) : ordSum α β := toLex (Sum.inl a)

/-- Right injection into `ordSum α β`. -/
abbrev inR {α β : Type u} (b : β) : ordSum α β := toLex (Sum.inr b)

instance instFintype {α β : Type u} [Fintype α] [Fintype β] :
    Fintype (ordSum α β) :=
  inferInstanceAs (Fintype (α ⊕ β))

end ordSum

/-! ### Indecomposability -/

/-- A partial order `α` is *indecomposable* iff it is not order-isomorphic
to an ordinal sum of two non-empty partial orders. -/
def Indecomposable (α : Type u) [PartialOrder α] : Prop :=
  ¬ ∃ (P₁ P₂ : Type u) (_ : PartialOrder P₁) (_ : PartialOrder P₂),
      Nonempty P₁ ∧ Nonempty P₂ ∧ Nonempty (α ≃o ordSum P₁ P₂)

namespace Indecomposable

/-- A singleton poset is indecomposable: any supposed decomposition would
force `inl p₁ = inr p₂` in the underlying sum. -/
theorem of_unique (α : Type u) [PartialOrder α] [Subsingleton α]
    [Nonempty α] : Indecomposable α := by
  rintro ⟨P₁, P₂, _, _, ⟨p₁⟩, ⟨p₂⟩, ⟨f⟩⟩
  have h₁ : f.symm (ordSum.inL p₁) = f.symm (ordSum.inR p₂) :=
    Subsingleton.elim _ _
  have h₂ : (ordSum.inL p₁ : ordSum P₁ P₂) = ordSum.inR p₂ :=
    f.symm.injective h₁
  -- `ordSum.inL p₁ = toLex (Sum.inl p₁)`; `ofLex` unfolds to `Sum.inl p₁`.
  have h₃ : (Sum.inl p₁ : P₁ ⊕ P₂) = Sum.inr p₂ := congrArg ofLex h₂
  nomatch h₃

end Indecomposable

/-- The two-element chain `Unit ⊕ₗ Unit` is decomposable. -/
theorem not_indecomposable_two_chain : ¬ Indecomposable (Unit ⊕ₗ Unit) :=
  fun h => h ⟨Unit, Unit, inferInstance, inferInstance,
              ⟨()⟩, ⟨()⟩, ⟨OrderIso.refl _⟩⟩

/-! ### Key combinatorial lemma: `lem:indec-incompairs` -/

section ExistsIncomp

variable {α : Type u} [PartialOrder α]

/-- Order iso for the case where `x` has something strictly above. The
partition is `{y // y ≤ x}` (below or at `x`) and `{y // x < y}`
(strictly above). -/
noncomputable def splitAtIso_bottomHeavy
    (x : α) (hx : ∀ y : α, y ≤ x ∨ x ≤ y) :
    α ≃o ordSum {y : α // y ≤ x} {y : α // x < y} := by
  classical
  let S : Set α := {y | y ≤ x}
  let T : Set α := {y | x < y}
  -- Forward map.
  let fwd : α → ordSum ↥S ↥T := fun y =>
    if hy : y ≤ x then ordSum.inL ⟨y, hy⟩
    else ordSum.inR ⟨y, by
      rcases hx y with h | h
      · exact absurd h hy
      · exact lt_of_le_not_ge h hy⟩
  -- Characterisations of `fwd`.
  have fwd_inL : ∀ {y : α} (hy : y ≤ x),
      fwd y = ordSum.inL ⟨y, hy⟩ := fun hy => dif_pos hy
  have fwd_inR : ∀ {y : α} (hy : ¬ y ≤ x),
      ∃ h : x < y, fwd y = ordSum.inR ⟨y, h⟩ := by
    intro y hy
    have : x < y := by
      rcases hx y with h | h
      · exact absurd h hy
      · exact lt_of_le_not_ge h hy
    exact ⟨this, dif_neg hy⟩
  refine
    { toFun := fwd
      invFun := fun s => Sum.elim (·.1) (·.1) (ofLex s)
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · -- left_inv
    intro y
    by_cases hy : y ≤ x
    · rw [fwd_inL hy]; rfl
    · obtain ⟨_, h⟩ := fwd_inR hy; rw [h]; rfl
  · -- right_inv
    intro s
    have hse : s = toLex (ofLex s) := rfl
    rcases h : ofLex s with a | b
    · rw [hse, h]
      change fwd a.1 = toLex (Sum.inl a)
      rw [fwd_inL a.2]; rfl
    · rw [hse, h]
      have hb_nle : ¬ b.1 ≤ x :=
        fun hle => absurd (lt_of_le_of_lt hle b.2) (lt_irrefl _)
      obtain ⟨_, hfwd⟩ := fwd_inR hb_nle
      change fwd b.1 = toLex (Sum.inr b)
      rw [hfwd]; rfl
  · -- map_rel_iff'
    intro a b
    change fwd a ≤ fwd b ↔ a ≤ b
    by_cases ha : a ≤ x
    · by_cases hb : b ≤ x
      · rw [fwd_inL ha, fwd_inL hb]
        change (ordSum.inL (⟨a, ha⟩ : ↥S)) ≤ ordSum.inL ⟨b, hb⟩ ↔ _
        exact Sum.Lex.inl_le_inl_iff
      · obtain ⟨hxb, hRb⟩ := fwd_inR hb
        rw [fwd_inL ha, hRb]
        refine ⟨fun _ => ha.trans hxb.le, fun _ => ?_⟩
        exact Sum.Lex.inl_le_inr _ _
    · obtain ⟨hxa, hRa⟩ := fwd_inR ha
      by_cases hb : b ≤ x
      · rw [hRa, fwd_inL hb]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact (Sum.Lex.not_inr_le_inl h).elim
        · exact absurd (lt_of_lt_of_le hxa (h.trans hb)) (lt_irrefl _)
      · obtain ⟨hxb, hRb⟩ := fwd_inR hb
        rw [hRa, hRb]
        change (ordSum.inR (⟨a, hxa⟩ : ↥T)) ≤ ordSum.inR ⟨b, hxb⟩ ↔ _
        exact Sum.Lex.inr_le_inr_iff

/-- Order iso for the case where every element is `≤ x`. The partition
is `{y // y < x}` and `{y // y = x}` (a singleton). -/
noncomputable def splitAtIso_topElement
    (x : α) (hx : ∀ y : α, y ≤ x) :
    α ≃o ordSum {y : α // y < x} {y : α // y = x} := by
  classical
  let S : Set α := {y | y < x}
  let T : Set α := {y | y = x}
  let fwd : α → ordSum ↥S ↥T := fun y =>
    if hy : y = x then ordSum.inR ⟨y, hy⟩
    else ordSum.inL ⟨y, lt_of_le_of_ne (hx y) hy⟩
  have fwd_eq : ∀ {y : α} (hy : y = x),
      fwd y = ordSum.inR ⟨y, hy⟩ := fun hy => dif_pos hy
  have fwd_ne : ∀ {y : α} (hy : y ≠ x),
      ∃ h : y < x, fwd y = ordSum.inL ⟨y, h⟩ := by
    intro y hy
    exact ⟨lt_of_le_of_ne (hx y) hy, dif_neg hy⟩
  refine
    { toFun := fwd
      invFun := fun s => Sum.elim (·.1) (·.1) (ofLex s)
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · -- left_inv
    intro y
    by_cases hy : y = x
    · rw [fwd_eq hy]; rfl
    · obtain ⟨_, h⟩ := fwd_ne hy; rw [h]; rfl
  · -- right_inv
    intro s
    have hse : s = toLex (ofLex s) := rfl
    rcases h : ofLex s with a | b
    · rw [hse, h]
      have ha_ne : a.1 ≠ x := ne_of_lt a.2
      obtain ⟨_, hfwd⟩ := fwd_ne ha_ne
      change fwd a.1 = toLex (Sum.inl a)
      rw [hfwd]; rfl
    · rw [hse, h]
      change fwd b.1 = toLex (Sum.inr b)
      rw [fwd_eq b.2]; rfl
  · -- map_rel_iff'
    intro a b
    change fwd a ≤ fwd b ↔ a ≤ b
    by_cases ha : a = x
    · by_cases hb : b = x
      · rw [fwd_eq ha, fwd_eq hb]
        refine ⟨fun _ => ha.le.trans hb.symm.le, fun _ => ?_⟩
        change (ordSum.inR (⟨a, ha⟩ : ↥T)) ≤ ordSum.inR ⟨b, hb⟩
        exact Sum.Lex.inr_le_inr_iff.mpr (ha.le.trans hb.symm.le)
      · obtain ⟨hblt, hLb⟩ := fwd_ne hb
        rw [fwd_eq ha, hLb]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact (Sum.Lex.not_inr_le_inl h).elim
        · exact absurd (lt_of_le_of_lt (ha ▸ h) hblt) (lt_irrefl _)
    · obtain ⟨halt, hLa⟩ := fwd_ne ha
      by_cases hb : b = x
      · rw [hLa, fwd_eq hb]
        refine ⟨fun _ => halt.le.trans hb.symm.le, fun _ => ?_⟩
        exact Sum.Lex.inl_le_inr _ _
      · obtain ⟨hblt, hLb⟩ := fwd_ne hb
        rw [hLa, hLb]
        change (ordSum.inL (⟨a, halt⟩ : ↥S)) ≤ ordSum.inL ⟨b, hblt⟩ ↔ _
        exact Sum.Lex.inl_le_inl_iff

/-- **`lem:indec-incompairs`** (`step8.tex:165`). In a finite
indecomposable poset of size `≥ 2`, every element has an incomparable
partner. -/
theorem Indecomposable.exists_incomp [Fintype α]
    (hI : Indecomposable α) (h2 : 2 ≤ Fintype.card α) (x : α) :
    ∃ y : α, y ∥ x := by
  classical
  by_contra H
  push Not at H
  have compare : ∀ y : α, y ≤ x ∨ x ≤ y := fun y => by
    by_contra hc
    push Not at hc
    exact H y ⟨hc.1, hc.2⟩
  by_cases hT : ∃ y, x < y
  · apply hI
    obtain ⟨y₀, hy₀⟩ := hT
    exact ⟨{y : α // y ≤ x}, {y : α // x < y},
           inferInstance, inferInstance,
           ⟨⟨x, le_refl x⟩⟩, ⟨⟨y₀, hy₀⟩⟩,
           ⟨splitAtIso_bottomHeavy x compare⟩⟩
  · push Not at hT
    have hx : ∀ y : α, y ≤ x := fun y => by
      rcases compare y with h | h
      · exact h
      · rcases lt_or_eq_of_le h with hlt | heq
        · exact absurd hlt (hT y)
        · exact heq ▸ le_refl x
    apply hI
    have : ∃ y : α, y ≠ x := by
      by_contra hall
      push Not at hall
      have : Fintype.card α ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        exact fun a b => (hall a).trans (hall b).symm
      omega
    obtain ⟨y₀, hy₀⟩ := this
    have hlt₀ : y₀ < x := lt_of_le_of_ne (hx y₀) hy₀
    exact ⟨{y : α // y < x}, {y : α // y = x},
           inferInstance, inferInstance,
           ⟨⟨y₀, hlt₀⟩⟩, ⟨⟨x, rfl⟩⟩,
           ⟨splitAtIso_topElement x hx⟩⟩

end ExistsIncomp

end OneThird.Mathlib.Poset
