/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.Case3Enum
import OneThird.Step8.Case3Enum.Correctness
import OneThird.Step8.BipartiteEnum
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Case-3 enumeration: Bool↔Prop lift of `findSymmetricPair`
and `hasBalancedPairSlow` (Path A4, `mg-8795`)

Companion to `OneThird.Step8.Case3Enum.Correctness` (Path A3, the
`countLinearExtensions ↔ numLinExt` identification). This file
provides the Prop-level lift of the symmetric-pair fast path of
`Case3Enum.hasBalancedPair`, plus shared infrastructure (the abstract
strengthened partial order `predOrderPlus`) for the slow-path lift.

## What is delivered (this file, A4a)

* §0 — Generic `probLT_eq_half_of_swap_auto` for any swap automorphism
  on a finite poset.
* §1 — `predOrderPlus`: the abstract strengthened partial order
  `predOrder pred ∪ {(x, y)}` for an incomparable pair `(x, y)` in
  `predOrder pred`. Used by both lifts.
* §3 — `Symmetric` predicate (the structural conditions extracted
  from `findSymmetricPair pred n = some (x, y)`); `swap_preserves_le`;
  `hasBalancedPair_of_symmetric`.

## Slow-path lift status

The slow-path lift of `hasBalancedPairSlow` requires:

* a `ValidPrefix (addEdgeClose pred n x.val y.val) n Finset.univ ≃
  {L : LinearExt (predOrder pred h) // L.lt x y}` bijection (uses
  A3's lower-level `clERec_eq_card_validPrefix`);
* warshall properties on `addEdgeClose`: bit-monotonicity,
  `predBitsBoundedBy` preservation, and SOUNDNESS (bit-relation of
  the warshall output ⊆ `predLTPlus`).

This infrastructure is deferred to a follow-up work item; see the
mailbox for the split proposal.

## References

`step8.tex` §G4 `lem:bounded-irreducible-balanced`; A1
(`mg-449b`, band-major Equiv), A2 (`mg-b7b0`, predMaskOf order iso),
A3 (`mg-7d1a`/`mg-a66d`, DP correctness).
-/

namespace OneThird

/-! ### §0 — Abstract `probLT = 1/2` from a swap automorphism

Generic finite-poset version of the symmetric-pair argument: if
`σ : α ≃ α` is order-preserving with `σ x = y`, `σ y = x`, and
`σ ∘ σ = id`, then `probLT x y = 1/2`. Pull-back along `σ`
exhibits a bijection between the linear extensions placing `x` before
`y` and those placing `y` before `x`. -/

/-- **Generic `probLT = 1/2` from a swap automorphism**.

For any finite poset `α` with a poset automorphism `σ : α ≃ α`
satisfying `σ x = y`, `σ y = x`, and `σ ∘ σ = id`, the linear-
extension probability satisfies `probLT x y = 1/2`. -/
theorem probLT_eq_half_of_swap_auto
    {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    {x y : α} (hxy : x ≠ y)
    (σ : α ≃ α) (hσ : ∀ a b : α, a ≤ b → σ a ≤ σ b)
    (hσx : σ x = y) (hσy : σ y = x)
    (hinv : ∀ z : α, σ (σ z) = z) :
    probLT x y = 1 / 2 := by
  classical
  -- Pull-back is an involution that swaps the two filters' cardinalities.
  have hcard :
      ((Finset.univ : Finset (LinearExt α)).filter
          (fun L => L.lt x y)).card =
        ((Finset.univ : Finset (LinearExt α)).filter
          (fun L => L.lt y x)).card := by
    refine Finset.card_bij
      (fun L _ => L.pullback hσ) ?_ ?_ ?_
    · intro L hL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
      change (L.pullback hσ).pos y < (L.pullback hσ).pos x
      rw [LinearExt.pullback_pos, LinearExt.pullback_pos, hσx, hσy]
      exact hL
    · intro L₁ _ L₂ _ heq
      have h1 : (L₁.pullback hσ).pullback hσ = (L₂.pullback hσ).pullback hσ :=
        congrArg (fun L : LinearExt α => L.pullback hσ) heq
      rw [L₁.pullback_pullback hσ hinv,
        L₂.pullback_pullback hσ hinv] at h1
      exact h1
    · intro L hL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL
      refine ⟨L.pullback hσ, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (L.pullback hσ).pos x < (L.pullback hσ).pos y
        rw [LinearExt.pullback_pos, LinearExt.pullback_pos, hσx, hσy]
        exact hL
      · exact L.pullback_pullback hσ hinv
  -- Combine with `probLT x y + probLT y x = 1`.
  have hsum : probLT x y + probLT y x = 1 := probLT_add_probLT_of_ne hxy
  have heq : probLT x y = probLT y x := by
    unfold probLT
    have hcardℚ :
        (((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt x y)).card : ℚ) =
        (((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt y x)).card : ℚ) := by exact_mod_cast hcard
    rw [hcardℚ]
  linarith

namespace Step8
namespace Case3Enum

open Finset

variable {n : ℕ}

/-! ### §1 — Abstract strengthened partial order `predOrderPlus`

For a valid pred-mask `pred` and an incomparable pair `(x, y)` in
`predOrder pred`, the strict relation of the *strengthened* partial
order is

  `u <_+ v  ↔  predLT pred u v  ∨  ((u = x ∨ predLT pred u x) ∧
                                   (v = y ∨ predLT pred y v))`. -/

section PredOrderPlus

variable {pred : Array Nat}

/-- The strict relation of `predOrderPlus`. -/
def predLTPlus (pred : Array Nat) (x y u v : Fin n) : Prop :=
  predLT pred u v ∨
    ((u = x ∨ predLT pred u x) ∧ (v = y ∨ predLT pred y v))

instance (pred : Array Nat) (x y u v : Fin n) :
    Decidable (predLTPlus pred x y u v) := by
  unfold predLTPlus; infer_instance

lemma predLTPlus_xy (x y : Fin n) : predLTPlus (pred := pred) x y x y :=
  Or.inr ⟨Or.inl rfl, Or.inl rfl⟩

/-- Irreflexivity of `predLTPlus`. -/
lemma predLTPlus_irrefl
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy : @Incomp (Fin n) (predOrder pred h).toLE x y)
    (u : Fin n) : ¬ predLTPlus pred x y u u := by
  rintro (hRuu | ⟨hux, huy⟩)
  · exact h.irrefl u hRuu
  · have hyx_le : @LE.le (Fin n) (predOrder pred h).toLE y x := by
      rcases hux with rfl | hux
      · rcases huy with hxy' | hxy'
        · exact Or.inl hxy'.symm
        · exact Or.inr hxy'
      · rcases huy with rfl | hyu
        · exact Or.inr hux
        · exact Or.inr (h.trans y u x hyu hux)
    exact hxy.2 hyx_le

/-- Transitivity of `predLTPlus`. -/
lemma predLTPlus_trans
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy : @Incomp (Fin n) (predOrder pred h).toLE x y)
    {u v w : Fin n} (huv : predLTPlus pred x y u v)
    (hvw : predLTPlus pred x y v w) : predLTPlus pred x y u w := by
  rcases huv with hRuv | ⟨hux, hvy⟩
  · rcases hvw with hRvw | ⟨hvx, hwy⟩
    · exact Or.inl (h.trans u v w hRuv hRvw)
    · refine Or.inr ⟨?_, hwy⟩
      rcases hvx with rfl | hvx
      · exact Or.inr hRuv
      · exact Or.inr (h.trans u v x hRuv hvx)
  · rcases hvw with hRvw | ⟨hvx, hwy⟩
    · refine Or.inr ⟨hux, ?_⟩
      rcases hvy with rfl | hvy
      · exact Or.inr hRvw
      · exact Or.inr (h.trans y v w hvy hRvw)
    · exfalso
      have hyx_le : @LE.le (Fin n) (predOrder pred h).toLE y x := by
        rcases hvy with rfl | hvy
        · rcases hvx with hyx | hRyx
          · exact Or.inl hyx
          · exact Or.inr hRyx
        · rcases hvx with rfl | hRvx
          · exact Or.inr hvy
          · exact Or.inr (h.trans y v x hvy hRvx)
      exact hxy.2 hyx_le

/-- The partial order on `Fin n` that strengthens `predOrder pred` by
adjoining the pair `(x, y)`. -/
@[reducible]
def predOrderPlus
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy : @Incomp (Fin n) (predOrder pred h).toLE x y) :
    PartialOrder (Fin n) where
  le u v := u = v ∨ predLTPlus pred x y u v
  lt u v := predLTPlus pred x y u v
  le_refl _ := Or.inl rfl
  le_trans u v w huv hvw := by
    rcases huv with rfl | huv
    · exact hvw
    · rcases hvw with rfl | hvw
      · exact Or.inr huv
      · exact Or.inr (predLTPlus_trans h x y hxy huv hvw)
  le_antisymm u v huv hvu := by
    rcases huv with rfl | huv
    · rfl
    · rcases hvu with rfl | hvu
      · rfl
      · exact (predLTPlus_irrefl h x y hxy u
          (predLTPlus_trans h x y hxy huv hvu)).elim
  lt_iff_le_not_ge := by
    intro u v
    constructor
    · intro hlt
      refine ⟨Or.inr hlt, ?_⟩
      rintro (heq | hge)
      · exact predLTPlus_irrefl h x y hxy v (heq ▸ hlt)
      · exact predLTPlus_irrefl h x y hxy u
          (predLTPlus_trans h x y hxy hlt hge)
    · rintro ⟨hle, hnle⟩
      rcases hle with heq | hle
      · exact (hnle (Or.inl heq.symm)).elim
      · exact hle

lemma predOrderPlus_le_of_predOrder_le
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy : @Incomp (Fin n) (predOrder pred h).toLE x y) {u v : Fin n}
    (huv : @LE.le (Fin n) (predOrder pred h).toLE u v) :
    @LE.le (Fin n) (predOrderPlus h x y hxy).toLE u v := by
  rcases huv with rfl | hRuv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hRuv)

lemma predOrderPlus_x_le_y
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy : @Incomp (Fin n) (predOrder pred h).toLE x y) :
    @LE.le (Fin n) (predOrderPlus h x y hxy).toLE x y :=
  Or.inr (predLTPlus_xy x y)

end PredOrderPlus

/-! ### §3 — `Symmetric` predicate and `findSymmetricPair` lift

The structural conditions implied by `findSymmetricPair pred n =
some (x, y)`. -/

section FindSymmetricPair

variable {pred : Array Nat}

/-- Structural conditions for the symmetric pair. -/
structure Symmetric (pred : Array Nat) (n : ℕ) (x y : Fin n) : Prop where
  ne : x ≠ y
  not_xy : ¬ predLT pred x y
  not_yx : ¬ predLT pred y x
  pred_agree : ∀ z : Fin n, z ≠ x → z ≠ y →
    (predLT pred z x ↔ predLT pred z y)
  succ_agree : ∀ z : Fin n, z ≠ x → z ≠ y →
    (predLT pred x z ↔ predLT pred y z)

namespace Symmetric

variable {pred : Array Nat} {x y : Fin n}

/-- `x ∥ y` in `predOrder pred`. -/
lemma incomp (h : ValidPredMask pred n) (hSym : Symmetric pred n x y) :
    @Incomp (Fin n) (predOrder pred h).toLE x y := by
  refine ⟨?_, ?_⟩
  · rintro (hxy | hxy)
    · exact hSym.ne hxy
    · exact hSym.not_xy hxy
  · rintro (hyx | hyx)
    · exact hSym.ne hyx.symm
    · exact hSym.not_yx hyx

end Symmetric

/-! #### §3.1 — Swap preserves `predLT pred` -/

private lemma swap_eval (x y z : Fin n) :
    Equiv.swap x y z = (if z = x then y else if z = y then x else z) := by
  split_ifs with h1 h2
  · rw [h1]; exact Equiv.swap_apply_left x y
  · rw [h2]; exact Equiv.swap_apply_right x y
  · exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- `Equiv.swap x y` preserves `predLT pred` when `Symmetric pred n x y`
holds. -/
private lemma swap_preserves_predLT
    {pred : Array Nat} (h : ValidPredMask pred n) {x y : Fin n}
    (hSym : Symmetric pred n x y) {u v : Fin n}
    (huv : predLT pred u v) :
    predLT pred (Equiv.swap x y u) (Equiv.swap x y v) := by
  rw [swap_eval x y u, swap_eval x y v]
  by_cases hux : u = x
  · rw [if_pos hux]
    by_cases hvx : v = x
    · rw [if_pos hvx]
      rw [hux, hvx] at huv
      exact (h.irrefl _ huv).elim
    · rw [if_neg hvx]
      by_cases hvy : v = y
      · rw [if_pos hvy]
        rw [hux, hvy] at huv
        exact (hSym.not_xy huv).elim
      · rw [if_neg hvy]
        rw [hux] at huv
        exact (hSym.succ_agree v hvx hvy).mp huv
  · rw [if_neg hux]
    by_cases huy : u = y
    · rw [if_pos huy]
      by_cases hvx : v = x
      · rw [if_pos hvx]
        rw [huy, hvx] at huv
        exact (hSym.not_yx huv).elim
      · rw [if_neg hvx]
        by_cases hvy : v = y
        · rw [if_pos hvy]
          rw [huy, hvy] at huv
          exact (h.irrefl _ huv).elim
        · rw [if_neg hvy]
          rw [huy] at huv
          exact (hSym.succ_agree v hvx hvy).mpr huv
    · rw [if_neg huy]
      by_cases hvx : v = x
      · rw [if_pos hvx]
        rw [hvx] at huv
        exact (hSym.pred_agree u hux huy).mp huv
      · rw [if_neg hvx]
        by_cases hvy : v = y
        · rw [if_pos hvy]
          rw [hvy] at huv
          exact (hSym.pred_agree u hux huy).mpr huv
        · rw [if_neg hvy]
          exact huv

/-- `Equiv.swap x y` preserves `≤` in `predOrder pred`. -/
lemma swap_preserves_le
    {pred : Array Nat} (h : ValidPredMask pred n) {x y : Fin n}
    (hSym : Symmetric pred n x y) (a b : Fin n)
    (hab : @LE.le (Fin n) (predOrder pred h).toLE a b) :
    @LE.le (Fin n) (predOrder pred h).toLE
      (Equiv.swap x y a) (Equiv.swap x y b) := by
  rcases hab with rfl | hab
  · exact Or.inl rfl
  · exact Or.inr (swap_preserves_predLT h hSym hab)

/-! #### §3.2 — `probLT = 1/2` and `HasBalancedPair` -/

/-- **`probLT x y = 1/2`** for any `Symmetric` pair under `predOrder pred`. -/
theorem probLT_eq_half_of_symmetric
    {pred : Array Nat} (h : ValidPredMask pred n) {x y : Fin n}
    (hSym : Symmetric pred n x y) :
    @probLT (Fin n) (predOrder pred h) _ _ x y = 1 / 2 := by
  have hσ : ∀ a b : Fin n,
      @LE.le (Fin n) (predOrder pred h).toLE a b →
      @LE.le (Fin n) (predOrder pred h).toLE
        (Equiv.swap x y a) (Equiv.swap x y b) :=
    swap_preserves_le h hSym
  have hσx : (Equiv.swap x y) x = y := Equiv.swap_apply_left x y
  have hσy : (Equiv.swap x y) y = x := Equiv.swap_apply_right x y
  have hinv : ∀ z : Fin n, (Equiv.swap x y) ((Equiv.swap x y) z) = z :=
    fun z => Equiv.swap_apply_self x y z
  exact @probLT_eq_half_of_swap_auto (Fin n) (predOrder pred h) _ _
    x y hSym.ne (Equiv.swap x y) hσ hσx hσy hinv

/-- **HasBalancedPair from a `Symmetric` pair.** -/
theorem hasBalancedPair_of_symmetric
    {pred : Array Nat} (h : ValidPredMask pred n) {x y : Fin n}
    (hSym : Symmetric pred n x y) :
    @HasBalancedPair (Fin n) (predOrder pred h) _ _ := by
  refine ⟨x, y, hSym.incomp h, ?_, ?_⟩
  · change (1 : ℚ) / 3 ≤ @probLT (Fin n) (predOrder pred h) _ _ x y
    rw [probLT_eq_half_of_symmetric h hSym]; norm_num
  · change @probLT (Fin n) (predOrder pred h) _ _ x y ≤ (2 : ℚ) / 3
    rw [probLT_eq_half_of_symmetric h hSym]; norm_num

end FindSymmetricPair

end Case3Enum
end Step8
end OneThird
