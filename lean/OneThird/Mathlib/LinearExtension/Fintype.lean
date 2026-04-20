/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Linear extensions of a finite poset: finiteness and counting

For a finite partial order `α`, a *linear extension* is an
order-preserving bijection `α ≃ Fin (Fintype.card α)`. This file
introduces the type `LinearExt α` of such bijections and proves:

* `Fintype (LinearExt α)`: there are finitely many linear extensions
  (by injection into the finite type `α ≃ Fin n`);
* `LinearExt.szpilrajn`: at least one linear extension exists
  (Szpilrajn's extension theorem);
* `one_le_numLinExt`: the count `numLinExt α := Fintype.card (LinearExt α)`
  is at least one.

The probability-style operator `probLT x y = Pr[x <_L y]` in a uniformly
random linear extension is also defined, with basic bounds.

## Location

All definitions here depend only on `Fintype`/`PartialOrder` and the
Szpilrajn theorem from mathlib. They are kept under `OneThird.Mathlib.*`
so they can be contributed to mathlib later without restructuring.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- A *linear extension* of a finite poset `P = (α, ≤)` is an
order-preserving bijection `α ≃ Fin n` (where `n = |α|`). -/
structure LinearExt (α : Type*) [PartialOrder α] [Fintype α] where
  /-- Underlying bijection to `Fin n`. -/
  toFun : α ≃ Fin (Fintype.card α)
  /-- The bijection respects `≤`. -/
  monotone : ∀ {x y : α}, x ≤ y → toFun x ≤ toFun y

namespace LinearExt

/-- Two linear extensions with equal underlying equivalences are equal.
The `monotone` field is a `Prop`, so proof irrelevance does the rest. -/
@[ext]
lemma ext {L₁ L₂ : LinearExt α} (h : L₁.toFun = L₂.toFun) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

lemma toFun_injective :
    Function.Injective (fun L : LinearExt α => L.toFun) :=
  fun _ _ h => ext h

/-- Position of `x` under a linear extension `L`. -/
def pos (L : LinearExt α) (x : α) : Fin (Fintype.card α) := L.toFun x

/-- `L.lt x y` iff `x` precedes `y` in the linear extension `L`. -/
def lt (L : LinearExt α) (x y : α) : Prop := L.pos x < L.pos y

instance instDecidableEq : DecidableEq (LinearExt α) := fun L₁ L₂ =>
  decidable_of_iff (L₁.toFun = L₂.toFun) ⟨ext, fun h => h ▸ rfl⟩

/-- `LinearExt α` is a `Fintype`: it injects into the finite type
`α ≃ Fin (Fintype.card α)`. -/
noncomputable instance instFintype : Fintype (LinearExt α) :=
  Fintype.ofInjective (fun L : LinearExt α => L.toFun) toFun_injective

instance instDecidableLt (L : LinearExt α) (x y : α) :
    Decidable (L.lt x y) :=
  inferInstanceAs (Decidable (L.pos x < L.pos y))

lemma pos_injective (L : LinearExt α) : Function.Injective L.pos :=
  L.toFun.injective

lemma pos_lt_pos_of_lt (L : LinearExt α) {x y : α} (hle : x ≤ y)
    (hne : x ≠ y) : L.pos x < L.pos y :=
  lt_of_le_of_ne (L.monotone hle) (fun h => hne (L.pos_injective h))

lemma lt_of_lt (L : LinearExt α) {x y : α} (h : x < y) : L.lt x y :=
  L.pos_lt_pos_of_lt h.le (ne_of_lt h)

/-- **Szpilrajn existence**: any finite poset admits a linear extension. -/
noncomputable def szpilrajn (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] : LinearExt α :=
  letI : Fintype (LinearExtension α) := (inferInstance : Fintype α)
  let e : Fin (Fintype.card α) ≃o LinearExtension α :=
    Fintype.orderIsoFinOfCardEq (LinearExtension α) rfl
  { toFun := e.symm.toEquiv
    monotone := fun h => e.symm.monotone (toLinearExtension.monotone' h) }

instance instNonempty : Nonempty (LinearExt α) := ⟨szpilrajn α⟩

end LinearExt

/-- Number of linear extensions of the poset `α`. -/
noncomputable def numLinExt (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] : ℕ :=
  Fintype.card (LinearExt α)

/-- Szpilrajn: every finite poset has at least one linear extension. -/
lemma one_le_numLinExt : 1 ≤ numLinExt α :=
  Fintype.card_pos

lemma numLinExt_pos : 0 < numLinExt α := one_le_numLinExt

lemma numLinExt_ne_zero : numLinExt α ≠ 0 := numLinExt_pos.ne'

/-- `probLT x y = Pr[x <_L y]`: fraction of linear extensions in which
`x` precedes `y`. -/
noncomputable def probLT (x y : α) : ℚ :=
  ((Finset.univ.filter (fun L : LinearExt α => L.lt x y)).card : ℚ)
    / (numLinExt α : ℚ)

lemma probLT_nonneg (x y : α) : 0 ≤ probLT x y := by
  unfold probLT
  positivity

lemma filter_lt_card_le_numLinExt (x y : α) :
    (Finset.univ.filter (fun L : LinearExt α => L.lt x y)).card ≤ numLinExt α := by
  unfold numLinExt
  exact (Finset.card_filter_le _ _).trans (Finset.card_univ.le)

lemma probLT_le_one (x y : α) : probLT x y ≤ 1 := by
  unfold probLT
  rw [div_le_one (by exact_mod_cast numLinExt_pos)]
  exact_mod_cast filter_lt_card_le_numLinExt x y

lemma probLT_self (x : α) : probLT x x = 0 := by
  have : (Finset.univ.filter (fun L : LinearExt α => L.lt x x)) = ∅ := by
    simp [LinearExt.lt]
  simp [probLT, this]

/-- On a strict inequality `x < y`, every linear extension places
`x` before `y`, so `probLT x y = 1`. -/
lemma probLT_of_lt {x y : α} (h : x < y) : probLT x y = 1 := by
  have hfilter :
      (Finset.univ.filter (fun L : LinearExt α => L.lt x y)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro L _
    exact L.lt_of_lt h
  have hpos : (numLinExt α : ℚ) ≠ 0 := by exact_mod_cast numLinExt_ne_zero
  unfold probLT
  rw [hfilter, Finset.card_univ]
  exact div_self hpos

/-- On `y < x`, no linear extension places `x` before `y`, so
`probLT x y = 0`. -/
lemma probLT_of_gt {x y : α} (h : y < x) : probLT x y = 0 := by
  have hfilter :
      (Finset.univ.filter (fun L : LinearExt α => L.lt x y)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro L _ hlt
    exact lt_asymm hlt (L.lt_of_lt h)
  simp [probLT, hfilter]

/-- For distinct `x` and `y`, the two one-sided probabilities sum to one:
each linear extension contributes to exactly one of the filters. -/
lemma probLT_add_probLT_of_ne {x y : α} (hxy : x ≠ y) :
    probLT x y + probLT y x = 1 := by
  have hdisj :
      Disjoint (Finset.univ.filter (fun L : LinearExt α => L.lt x y))
               (Finset.univ.filter (fun L : LinearExt α => L.lt y x)) := by
    rw [Finset.disjoint_left]
    intro L hL hL'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      LinearExt.lt] at hL hL'
    exact absurd (hL.trans hL') (lt_irrefl _)
  have hunion :
      (Finset.univ.filter (fun L : LinearExt α => L.lt x y)) ∪
        (Finset.univ.filter (fun L : LinearExt α => L.lt y x)) =
      (Finset.univ : Finset (LinearExt α)) := by
    ext L
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, LinearExt.lt]
    rcases lt_trichotomy (L.pos x) (L.pos y) with h | h | h
    · exact ⟨fun _ => True.intro, fun _ => Or.inl h⟩
    · exact absurd (L.pos_injective h) hxy
    · exact ⟨fun _ => True.intro, fun _ => Or.inr h⟩
  have hcard :
      (Finset.univ.filter (fun L : LinearExt α => L.lt x y)).card +
        (Finset.univ.filter (fun L : LinearExt α => L.lt y x)).card =
      numLinExt α := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rfl
  have hpos : (numLinExt α : ℚ) ≠ 0 := by exact_mod_cast numLinExt_ne_zero
  unfold probLT
  rw [← add_div, ← Nat.cast_add, hcard]
  exact div_self hpos

end OneThird
