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

## What is delivered (this file, A4b — slow-path infrastructure)

* §4 — Warshall properties on `addEdgeClose`-augmented pred:
  bit-monotonicity (`warshall_bit_mono`), `predBitsBoundedBy`
  preservation (`warshall_predBitsBoundedBy`), and SOUNDNESS
  (`warshall_addEdge_sound`: bit-relation of the warshall output ⊆
  `predLTPlus`). The doubly-nested for-loop is handled by reducing
  the imperative form to a list-`foldl` via a generic
  `Id.forIn_invariant` helper, then preserving each invariant
  through the inner step (`innerStep`) by induction on the
  inner/outer lists.
* §5 — Helper lemmas for the slow-path bridge:
  `predLT_pred_subset_predAddEdge` (warshall `bit_mono` lifted to
  `predLT`), `predLT_predAddEdge_xy` (the `(x, y)` bit survives the
  warshall pass), and `predBitsBoundedBy_predAddEdge`.
* §6 — `validPrefixPredAddEdgeEquivLinearExtLt`:
  `ValidPrefix (predAddEdge pred n x y) n Finset.univ ≃ {L :
  LinearExt(predOrder pred h) // L.lt x y}`. Combines the warshall
  facts from §4-§5 with the A3 bridge `validPrefixUnivEquivLinearExt`
  (now public in `Correctness.lean`).

## Slow-path bridge status

The full Bool→Prop lift of `hasBalancedPairSlow` has been split into
follow-up work items (see `mg mail` history). The remaining pieces:

* §7 — `hasBalancedPairSlow` `Bool → Prop` lift via `forIn`
  unrolling and the probability-bound bridge.
* §8 — Final `bounded_irreducible_balanced`-consumable theorem.

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

/-! ### §4 — Warshall properties on `addEdgeClose`-augmented pred

We prove three properties of `Case3Enum.warshall`, all needed for the
slow-path bridge:

* **Bit-monotonicity**: warshall does not remove bits.
* **`predBitsBoundedBy` preservation**: bit-bounded input gives a
  bit-bounded output.
* **SOUNDNESS**: for any transitive `R : Nat → Nat → Prop`
  containing the input bit-relation, the output bit-relation is also
  contained in `R`.

To make the doubly-nested for-loop tractable, we first reduce the
imperative `Case3Enum.warshall` to a list-`foldl` recursive form
(`warshallRec`), then induct on the list level. -/

section WarshallProps

open Case3Enum

/-! #### §4.1 — `set!` / `getD` helpers -/

/-- `(out.set! v w).getD v' 0` analyzed by case on `v' = v` and bounds. -/
lemma getD_set!_eq (out : Array Nat) (v : Nat) (w : Nat) (v' : Nat) :
    (out.set! v w).getD v' 0 =
      if v' = v ∧ v < out.size then w else out.getD v' 0 := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hv' : v' = v
  · subst hv'
    by_cases hvsize : v' < out.size
    · simp only [Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt hvsize, Option.getD_some,
        and_self, hvsize, ↓reduceIte, true_and, if_pos hvsize]
    · rw [Array.setIfInBounds_eq_of_size_le (Nat.not_lt.mp hvsize)]
      simp [hvsize]
  · have hne : v' ≠ v := hv'
    have hne' : v ≠ v' := fun h => hne h.symm
    simp only [Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hne', and_iff_left_of_imp]
    rw [if_neg]
    intro ⟨h1, _⟩; exact hne h1

/-- Bits of `0` are all unset. -/
private lemma testBit'_zero (u : ℕ) : testBit' 0 u = false := by
  unfold testBit' bit
  rw [Nat.zero_and]
  rfl

/-- `getD` at an out-of-bounds index returns the default. -/
private lemma getD_out_of_bounds (out : Array Nat) (v : Nat)
    (h : out.size ≤ v) : out.getD v 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-! #### §4.2 — Generic `forIn` invariant lemma -/

/-- A `forIn` over a list in the `Id` monad preserves any predicate `P`
whose body always evaluates to `pure (yield acc')` with `P acc'`. -/
private theorem Id.forIn_invariant {α : Type} (l : List α)
    (init : Array Nat) (P : Array Nat → Prop) (h_init : P init)
    (body : α → Array Nat → Id (ForInStep (Array Nat)))
    (h_step : ∀ x ∈ l, ∀ acc : Array Nat, P acc →
      ∃ acc', body x acc = (pure (ForInStep.yield acc') : Id _) ∧ P acc') :
    P (forIn (m := Id) l init body) := by
  induction l generalizing init with
  | nil =>
    show P (Id.run (forIn [] init body))
    simp [forIn]; exact h_init
  | cons x xs ih =>
    rw [List.forIn_cons]
    obtain ⟨acc', hbody, hPacc'⟩ := h_step x List.mem_cons_self init h_init
    show P (Id.run (body x init >>= _))
    rw [hbody]
    show P (Id.run (forIn xs acc' body))
    exact ih acc' hPacc' (fun y hy acc hacc => h_step y (List.mem_cons_of_mem _ hy) acc hacc)

/-! #### §4.3 — Bit-monotonicity, bit-bounded preservation, R-soundness

We package the imperative warshall's structural property: at the start
of each outer iteration, the "k-row" `out[k]` has been frozen as `pk`,
and the inner for-loop OR's `pk` into entries `out[v]` whose bit `k` is
set. This means that any predicate `P` that:

(a) is preserved by the inner step `out ↦ if testBit' out[v] k then
    out.set! v (out[v] ||| pk) else out`,

(b) is preserved by the outer step (which calls the inner pass),

is preserved by the imperative warshall. -/

/-- The inner step. -/
private def innerStep (k pk v : Nat) (out : Array Nat) : Array Nat :=
  if testBit' (out.getD v 0) k then out.set! v (out.getD v 0 ||| pk) else out

private lemma innerStep_eq_imperative_body (k v : Nat) (pk : Nat)
    (out : Array Nat) :
    (if (out.getD v 0 &&& bit k != 0) = true then
      out.set! v (out.getD v 0 ||| pk) else out) =
    innerStep k pk v out := by
  unfold innerStep testBit'
  rfl

/-! #### §4.4 — Inner step preserves bit-monotonicity -/

private lemma innerStep_bit_mono (k pk v : Nat) (out : Array Nat)
    {u v' : Nat} (h : testBit' (out.getD v' 0) u = true) :
    testBit' ((innerStep k pk v out).getD v' 0) u = true := by
  unfold innerStep
  split_ifs with hgate
  · rw [getD_set!_eq]
    split_ifs with hcase
    · obtain ⟨hv'_eq, _⟩ := hcase
      subst hv'_eq
      rw [testBit'_eq, Nat.testBit_or, ← testBit'_eq, h]; rfl
    · exact h
  · exact h

private lemma innerStep_bits_bounded (k pk v : Nat) (out : Array Nat)
    {v' u : Nat}
    (hout : testBit' (out.getD v' 0) u = false)
    (hpk : testBit' pk u = false) :
    testBit' ((innerStep k pk v out).getD v' 0) u = false := by
  unfold innerStep
  split_ifs with hgate
  · rw [getD_set!_eq]
    split_ifs with hcase
    · obtain ⟨hv'_eq, _⟩ := hcase
      subst hv'_eq
      rw [testBit'_eq, Nat.testBit_or, ← testBit'_eq, hout,
          ← testBit'_eq, hpk]
      rfl
    · exact hout
  · exact hout

/-! #### §4.5 — Imperative inner forIn body equals `pure (yield (innerStep ...))` -/

/-- The body of the imperative inner for-loop reduces, in `Id`, to
`pure (yield (innerStep k pk v out))`. The leading `pure unit;` discards
are absorbed by the monad laws. -/
private lemma inner_body_eq (k pk v : Nat) (out : Array Nat) :
    (if (out.getD v 0 &&& bit k != 0) = true then
      (do pure PUnit.unit; pure (ForInStep.yield (out.set! v (out.getD v 0 ||| pk))) : Id _)
    else
      (do pure PUnit.unit; pure (ForInStep.yield out) : Id _)) =
    (pure (ForInStep.yield (innerStep k pk v out)) : Id _) := by
  unfold innerStep testBit'
  split_ifs <;> rfl

/-! #### §4.6 — Bit-monotonicity, the imperative version -/

/-- A wrapper for the outer for-in body of the imperative warshall.
Made explicit to factor through `Id.forIn_invariant`. -/
private def warshallOuterBody (n : ℕ) :
    Nat → Array Nat → Id (ForInStep (Array Nat)) :=
  fun k acc =>
    (do
      pure PUnit.unit
      let r ← (forIn (m := Id) (List.range' 0 n) acc (fun v acc' =>
        if (acc'.getD v 0 &&& bit k != 0) = true then
          (do pure PUnit.unit; pure (ForInStep.yield (acc'.set! v (acc'.getD v 0 ||| acc.getD k 0))) : Id _)
        else
          (do pure PUnit.unit; pure (ForInStep.yield acc') : Id _)) : Id _)
      pure (ForInStep.yield r))

private lemma warshall_imperative_eq (pred : Array Nat) (n : ℕ) :
    Case3Enum.warshall pred n =
      forIn (m := Id) (List.range' 0 n) pred (warshallOuterBody n) := by
  classical
  unfold Case3Enum.warshall warshallOuterBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- The outer-loop body, evaluated, satisfies any predicate preserved
by the inner forIn (whose body is gated OR with `pk = acc[k]`). The
inner-step hypothesis is given access to `v < n`. -/
private lemma warshallOuterBody_pred (n : ℕ) (k : Nat) (acc : Array Nat)
    (P : Array Nat → Prop) (hacc : P acc)
    (h_inner_step : ∀ v, v < n → ∀ acc', P acc' →
      P (innerStep k (acc.getD k 0) v acc')) :
    ∃ acc', warshallOuterBody n k acc =
      (pure (ForInStep.yield acc') : Id _) ∧ P acc' := by
  have hbody_eq :
      (fun (v : Nat) (acc' : Array Nat) =>
        (if (acc'.getD v 0 &&& bit k != 0) = true then
          (do pure PUnit.unit; pure (ForInStep.yield (acc'.set! v (acc'.getD v 0 ||| acc.getD k 0))) : Id _)
        else
          (do pure PUnit.unit; pure (ForInStep.yield acc') : Id _) :
          Id (ForInStep (Array Nat)))) =
      fun v acc' =>
        (pure (ForInStep.yield (innerStep k (acc.getD k 0) v acc')) : Id _) := by
    funext v acc'
    exact inner_body_eq k (acc.getD k 0) v acc'
  set inner_result : Array Nat :=
    (forIn (m := Id) (List.range' 0 n) acc (fun v acc' =>
      (pure (ForInStep.yield (innerStep k (acc.getD k 0) v acc')) : Id _))) with hres
  have h_inner_pred : P inner_result := by
    rw [hres]
    apply Id.forIn_invariant (P := P)
    · exact hacc
    · intro v hv acc' hacc'
      have hv_lt : v < n := by
        have := List.mem_range'.mp hv
        omega
      exact ⟨_, rfl, h_inner_step v hv_lt acc' hacc'⟩
  refine ⟨inner_result, ?_, h_inner_pred⟩
  unfold warshallOuterBody
  rw [hbody_eq]
  rfl

/-- **Bit-monotonicity of `Case3Enum.warshall`**: bits in the input are
preserved in the output. -/
theorem warshall_bit_mono (pred : Array Nat) (n : ℕ)
    {u v : Nat} (h : testBit' (pred.getD v 0) u = true) :
    testBit' ((Case3Enum.warshall pred n).getD v 0) u = true := by
  rw [warshall_imperative_eq]
  apply Id.forIn_invariant
    (P := fun out => testBit' (out.getD v 0) u = true)
  · exact h
  · intro k _ acc hacc
    apply warshallOuterBody_pred
    · exact hacc
    · intro w _ acc' hacc'
      exact innerStep_bit_mono _ _ _ _ hacc'

/-! #### §4.7 — `predBitsBoundedBy` preservation -/

/-- **`predBitsBoundedBy` is preserved by `Case3Enum.warshall`.** -/
theorem warshall_predBitsBoundedBy (pred : Array Nat) (n : ℕ)
    (hbnd : predBitsBoundedBy pred n) :
    predBitsBoundedBy (Case3Enum.warshall pred n) n := by
  intro e u hu
  rw [warshall_imperative_eq]
  set P : Array Nat → Prop :=
    fun out => ∀ v < n, ∀ u ≥ n, testBit' (out.getD v 0) u = false
  have hpred_init : P pred := fun v hv u' hu' => hbnd ⟨v, hv⟩ u' hu'
  have h_final : P
      (forIn (m := Id) (List.range' 0 n) pred (warshallOuterBody n)) := by
    apply Id.forIn_invariant (P := P)
    · exact hpred_init
    · intro k hk acc hacc
      have hk_lt : k < n := by
        have := List.mem_range'.mp hk
        omega
      apply warshallOuterBody_pred
      · exact hacc
      · intro w _ acc' hacc' v' hv' u' hu'
        exact innerStep_bits_bounded _ _ _ _ (hacc' v' hv' u' hu')
          (hacc k hk_lt u' hu')
  exact h_final e.val e.isLt u hu

/-! #### §4.8 — SOUNDNESS: bit-relation of `addEdgeClose pred n x y`
contained in `predLTPlus pred x y`

For an `x ∥ y` incomparable pair in `predOrder pred h`, we show that
warshall applied to the augmented mask `pred + (x, y)` produces only
bits whose pairs are in `predLTPlus pred x y`.

The key facts used:
* `predLTPlus` is *transitive* (provided by `predLTPlus_trans`).
* Bits of `pred.set! y.val (pred[y.val] ||| bit x.val)` are either bits
  of `pred` (so in `predLT pred ⊆ predLTPlus`) or the new bit `(x, y)`
  (so `predLTPlus_xy`).
* Each warshall inner step OR's `pk = out[k]` into `out[v]` gated by
  `bit k of out[v] = true`. By `predLTPlus_trans`, the new bits stay in
  `predLTPlus`. -/

variable {n : ℕ}

/-- **SOUNDNESS** of `Case3Enum.warshall (pred.set! y (pred[y] ||| bit x)) n`:
the bit-relation of the warshall output (restricted to `Fin n`) is
contained in `predLTPlus pred x y`. -/
theorem warshall_addEdge_sound {pred : Array Nat}
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy : @Incomp (Fin n) (predOrder pred h).toLE x y)
    (u v : Fin n)
    (hbit : testBit'
      ((Case3Enum.warshall (pred.set! y.val
        (pred.getD y.val 0 ||| bit x.val)) n).getD v.val 0) u.val = true) :
    predLTPlus pred x y u v := by
  rw [warshall_imperative_eq] at hbit
  set inputArr := pred.set! y.val (pred.getD y.val 0 ||| bit x.val)
  set R : Fin n → Fin n → Prop := predLTPlus pred x y
  set P : Array Nat → Prop :=
    fun out => ∀ u v : Fin n,
      testBit' (out.getD v.val 0) u.val = true → R u v with hP_def
  -- Initial state satisfies P.
  have hP_init : P inputArr := by
    intro u v hbit
    rw [show inputArr.getD v.val 0 =
          if v.val = y.val ∧ y.val < pred.size
          then pred.getD y.val 0 ||| bit x.val else pred.getD v.val 0 from
        getD_set!_eq pred y.val _ v.val] at hbit
    split_ifs at hbit with hcase
    · obtain ⟨hvy, _⟩ := hcase
      have hvy' : v = y := Fin.ext hvy
      subst hvy'
      -- bit u.val of (pred[y] | bit x.val) = true.
      rw [testBit'_eq, Nat.testBit_or] at hbit
      by_cases hpred_bit : Nat.testBit (pred.getD v.val 0) u.val = true
      · have hpr : predLT pred u v := by
          rw [show predLT pred u v ↔ testBit' (pred.getD v.val 0) u.val = true
            from Iff.rfl, testBit'_iff_testBit]
          exact hpred_bit
        exact Or.inl hpr
      · have hpred_bit_false : Nat.testBit (pred.getD v.val 0) u.val = false := by
          cases hb : Nat.testBit (pred.getD v.val 0) u.val with
          | true => exact absurd hb hpred_bit
          | false => rfl
        rw [hpred_bit_false, Bool.false_or] at hbit
        -- bit u.val of `bit x.val = 1 <<< x.val` is true iff u.val = x.val.
        unfold bit at hbit
        rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at hbit
        have hux : x.val = u.val := by
          rcases h_eq : decide (x.val = u.val) with _ | _
          · rw [h_eq] at hbit; exact absurd hbit (Bool.false_ne_true)
          · exact decide_eq_true_iff.mp h_eq
        have hu : u = x := Fin.ext hux.symm
        subst hu
        -- Goal: R u y, with u = x (subst applied) and v = y (earlier subst).
        -- After subst, the local var name may be `u` or `x`; use the lemma directly.
        exact predLTPlus_xy _ _
    · have hpr : predLT pred u v := hbit
      exact Or.inl hpr
  -- Apply outer forIn invariant.
  have h_final : P
      (forIn (m := Id) (List.range' 0 n) inputArr (warshallOuterBody n)) := by
    apply Id.forIn_invariant (P := P)
    · exact hP_init
    · intro k hk acc hacc
      have hk_lt : k < n := by
        have := List.mem_range'.mp hk
        omega
      apply warshallOuterBody_pred
      · exact hacc
      · intro w hw acc' hacc' u' v' hbit'
        -- Inner step at w: out[w] := out[w] | acc[k] (gated). v' (Fin n).
        -- Show R u' v' from hbit' (bit u' of new out[v'] = true).
        -- Cast w to Fin n.
        let kFin : Fin n := ⟨k, hk_lt⟩
        let wFin : Fin n := ⟨w, hw⟩
        -- Analyse innerStep.
        rw [show (innerStep k (acc.getD k 0) w acc').getD v'.val 0 =
            if testBit' (acc'.getD w 0) k then
              (acc'.set! w (acc'.getD w 0 ||| acc.getD k 0)).getD v'.val 0
            else acc'.getD v'.val 0 by unfold innerStep; split_ifs <;> rfl]
            at hbit'
        split_ifs at hbit' with hgate
        · -- Gate fired: out[v'.val] = if v'.val = w then ... else acc'[v'.val].
          rw [getD_set!_eq] at hbit'
          split_ifs at hbit' with hcase
          · obtain ⟨hv'w, _⟩ := hcase
            have hv'w_fin : v' = wFin := Fin.ext hv'w
            -- bit u'.val of (acc'[w] | acc[k]) = true.
            -- testBit' (a ||| b) i = testBit' a i || testBit' b i.
            have h_or : testBit' (acc'.getD w 0) u'.val = true ∨
                        testBit' (acc.getD k 0) u'.val = true := by
              rw [testBit'_eq, Nat.testBit_or] at hbit'
              rw [testBit'_eq, testBit'_eq]
              cases h_a : Nat.testBit (acc'.getD w 0) u'.val with
              | true => exact Or.inl rfl
              | false =>
                rw [h_a, Bool.false_or] at hbit'
                exact Or.inr hbit'
            rcases h_or with h1 | h2
            · -- bit from acc'[w] true.
              rw [hv'w_fin]
              exact hacc' u' wFin h1
            · -- bit from acc[k] true; need R u' kFin and R kFin wFin.
              have hu_k : R u' kFin := hacc u' kFin h2
              have hk_v : R kFin wFin := hacc' kFin wFin hgate
              rw [hv'w_fin]
              exact predLTPlus_trans h x y hxy hu_k hk_v
          · -- v'.val ≠ w or w ≥ acc'.size: out[v'.val] unchanged.
            exact hacc' u' v' hbit'
        · -- Gate didn't fire: same as old out[v'.val].
          exact hacc' u' v' hbit'
  exact h_final u v hbit

end WarshallProps

/-! ### §5 — Helper lemmas for the slow-path bridge

The full bridge `ValidPrefix(addEdgeClose) ↔ {L : LinearExt | L.lt x y}`
requires access to private equivalences from `Correctness.lean`
(`validPrefixUnivEquivLinearExt`, `ValidPrefix.toFinPerm`). The two
helper lemmas below capture the warshall facts needed by the bridge
and are deferred to a follow-up work item.

* `predLT_pred_subset_predAddEdge` — bit-monotonicity at the
  `predLT`-relation level.
* `predLT_predAddEdge_xy` — the `(x, y)` bit is in the augmented
  pred-mask. -/

section SlowPathHelpers

open Case3Enum

variable {pred : Array Nat} {n : ℕ}

/-- The augmented (closed) pred-mask for the `(x, y)` edge. -/
def predAddEdge (pred : Array Nat) (n : ℕ) (x y : Fin n) : Array Nat :=
  Case3Enum.warshall (pred.set! y.val (pred.getD y.val 0 ||| bit x.val)) n

lemma predAddEdge_eq (pred : Array Nat) (n : ℕ) (x y : Fin n) :
    predAddEdge pred n x y = Case3Enum.addEdgeClose pred n x.val y.val := by
  unfold predAddEdge Case3Enum.addEdgeClose
  rfl

/-- `predLT pred ⊆ predLT (predAddEdge pred n x y)`. -/
lemma predLT_pred_subset_predAddEdge (x y : Fin n) (u v : Fin n)
    (hpred : predLT pred u v) :
    predLT (predAddEdge pred n x y) u v := by
  apply warshall_bit_mono _ n
  rw [getD_set!_eq]
  split_ifs with hcase
  · obtain ⟨hvy, _⟩ := hcase
    have hvy' : v = y := Fin.ext hvy
    subst hvy'
    rw [testBit'_eq, Nat.testBit_or]
    rw [show Nat.testBit (pred.getD v.val 0) u.val = true from
      testBit'_iff_testBit.mp hpred]
    rfl
  · exact hpred

/-- `predLT (predAddEdge pred n x y) x y` (the `(x, y)` bit is set in
the augmented pred-mask, provided `y.val < pred.size`). -/
lemma predLT_predAddEdge_xy (x y : Fin n)
    (hsize : y.val < pred.size) :
    predLT (predAddEdge pred n x y) x y := by
  apply warshall_bit_mono _ n
  rw [getD_set!_eq]
  rw [if_pos ⟨rfl, hsize⟩]
  rw [testBit'_eq, Nat.testBit_or]
  rw [show Nat.testBit (bit x.val) x.val = true from by
    unfold bit
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    simp]
  cases Nat.testBit (pred.getD y.val 0) x.val <;> rfl

/-- `predBitsBoundedBy` of `predAddEdge`, given the same on `pred` and
`y.val < pred.size`. -/
lemma predBitsBoundedBy_predAddEdge (h_bnd : predBitsBoundedBy pred n)
    (x y : Fin n) :
    predBitsBoundedBy (predAddEdge pred n x y) n := by
  apply warshall_predBitsBoundedBy
  -- pred.set! y.val (pred[y.val] ||| bit x.val) is bit-bounded.
  intro e u hu
  rw [getD_set!_eq]
  split_ifs with hcase
  · obtain ⟨hey, _⟩ := hcase
    rw [testBit'_eq, Nat.testBit_or]
    have h1 : Nat.testBit (pred.getD e.val 0) u = false := by
      have := h_bnd e u hu
      rw [testBit'_eq] at this
      exact this
    rw [show pred.getD e.val 0 = pred.getD y.val 0 by rw [hey]] at h1
    rw [h1, Bool.false_or]
    -- bit u of `bit x.val = 1 <<< x.val` = false because u ≥ n > x.val.
    unfold bit
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    have hx_lt : x.val < u := lt_of_lt_of_le x.isLt hu
    have : x.val ≠ u := Nat.ne_of_lt hx_lt
    simp [this]
  · exact h_bnd e u hu

end SlowPathHelpers

/-! ### §6 — Bridge: `ValidPrefix(predAddEdge) ≃ {L : LinearExt // L.lt x y}`

Combines the warshall facts from §4-§5 with the A3 bridge
`validPrefixUnivEquivLinearExt` (now public in `Correctness.lean`)
to identify valid prefixes on the augmented mask `predAddEdge pred n
x y` with linear extensions of `predOrder pred h` placing `x` before
`y`.

Three lemmas glue together: (a) `predLT pred ⊆ predLT (predAddEdge)`
(`predLT_pred_subset_predAddEdge`) lets a `ValidPrefix (predAddEdge)`
restrict to a `ValidPrefix pred`; (b) `predLT (predAddEdge) x y`
(`predLT_predAddEdge_xy`) identifies the new `(x, y)` bit;
(c) SOUNDNESS (`warshall_addEdge_sound`) says
`predLT (predAddEdge) ⊆ predLTPlus pred x y`, so a `ValidPrefix pred`
placing `x` before `y` strengthens to a `ValidPrefix (predAddEdge)`. -/

section BridgeA4b3

open Case3Enum

variable {pred : Array Nat} {n : ℕ}

/-- Restrict a `ValidPrefix (predAddEdge pred n x y)` to a
`ValidPrefix pred` by weakening the `predClosed` invariant via
`predLT pred ⊆ predLT (predAddEdge)` (`predLT_pred_subset_predAddEdge`). -/
def ValidPrefix.restrictFromAddEdge
    {S : Finset (Fin n)} (x y : Fin n)
    (P : ValidPrefix (predAddEdge pred n x y) n S) :
    ValidPrefix pred n S :=
  ⟨P.val, P.inj, P.mem,
    fun i u hu => P.predClosed i u
      (predLT_pred_subset_predAddEdge x y u (P.val i) hu)⟩

@[simp] lemma ValidPrefix.restrictFromAddEdge_val
    {S : Finset (Fin n)} (x y : Fin n)
    (P : ValidPrefix (predAddEdge pred n x y) n S) :
    (P.restrictFromAddEdge x y).val = P.val := rfl

/-- Position-of monotonicity for any `ValidPrefix pred`: if
`predLT pred u v`, then `(P.toFinPerm.symm u).val < (P.toFinPerm.symm v).val`.
Derived from `P.predClosed` at `i := P.toFinPerm.symm v`. -/
lemma ValidPrefix.toFinPerm_symm_val_lt_of_predLT
    (P : ValidPrefix pred n (Finset.univ : Finset (Fin n)))
    {u v : Fin n} (hpred : predLT pred u v) :
    (P.toFinPerm.symm u).val < (P.toFinPerm.symm v).val := by
  classical
  set π := P.toFinPerm with hπ_def
  set iv := π.symm v with hiv_def
  have hπ_iv : π iv = v := π.apply_symm_apply v
  -- π iv = P.val (liftToCardUniv iv) by definition of toFinPerm.
  have hPiv : P.val (liftToCardUniv iv) = v := hπ_iv
  have hpred' : predLT pred u (P.val (liftToCardUniv iv)) := by
    rw [hPiv]; exact hpred
  obtain ⟨j, hjlt, hju⟩ := P.predClosed (liftToCardUniv iv) u hpred'
  set j' : Fin n := lowerFromCardUniv j with hj'_def
  have hπ_j' : π j' = u := by
    show P.val (liftToCardUniv j') = u
    rw [liftToCardUniv_lowerFromCardUniv]; exact hju
  have hsymm_u : π.symm u = j' := by
    rw [← hπ_j', π.symm_apply_apply]
  rw [hsymm_u]
  show j.val < iv.val
  exact hjlt

/-- For `P : ValidPrefix pred n univ`, `(P.toLinearExtUniv h).lt x y`
is exactly the position-of inequality on `P.toFinPerm`. The `@LinearExt.lt`
makes the partial-order instance explicit, since `Fin n` has a default
`PartialOrder` that would otherwise be synthesized. -/
lemma ValidPrefix.toLinearExtUniv_lt_iff
    (h : ValidPredMask pred n)
    (P : ValidPrefix pred n (Finset.univ : Finset (Fin n)))
    (x y : Fin n) :
    @LinearExt.lt (Fin n) (predOrder pred h) _ (P.toLinearExtUniv h) x y ↔
      (P.toFinPerm.symm x).val < (P.toFinPerm.symm y).val := Iff.rfl

/-- The `Fin.castOrderIso` cast inside `linearExtUnivToValidPrefix` is
val-preserving; combined with `linearExtUnivToValidPrefix_toFinPerm`,
the position of `x` under the resulting valid prefix has the same
`.val` as `L.toFun x`. -/
lemma linearExtUnivToValidPrefix_toFinPerm_symm_val
    (h : ValidPredMask pred n)
    (L : @LinearExt (Fin n) (predOrder pred h) _) (x : Fin n) :
    ((linearExtUnivToValidPrefix h L).toFinPerm.symm x).val =
      (@LinearExt.toFun (Fin n) (predOrder pred h) _ L x).val := by
  rw [linearExtUnivToValidPrefix_toFinPerm h L, Equiv.symm_symm]
  rfl

/-- Forward map: a `ValidPrefix (predAddEdge pred n x y)` on `univ`
defines a linear extension of `predOrder pred h` placing `x`
before `y`. Requires `y.val < pred.size` (the new `(x, y)` bit is set
only if the array slot exists). -/
noncomputable def ValidPrefix.toLinearExtLtUniv
    (h : ValidPredMask pred n) (x y : Fin n) (hsize : y.val < pred.size)
    (P : ValidPrefix (predAddEdge pred n x y) n
      (Finset.univ : Finset (Fin n))) :
    { L : @LinearExt (Fin n) (predOrder pred h) _ //
        @LinearExt.lt (Fin n) (predOrder pred h) _ L x y } :=
  ⟨(P.restrictFromAddEdge x y).toLinearExtUniv h, by
    classical
    rw [(P.restrictFromAddEdge x y).toLinearExtUniv_lt_iff h x y]
    -- (P.restrictFromAddEdge).toFinPerm = P.toFinPerm definitionally,
    -- since both unfold to `Equiv.ofBijective (fun i => P.val (liftToCardUniv i)) ...`.
    -- Apply the position-of monotonicity to predLT (predAddEdge) x y.
    exact P.toFinPerm_symm_val_lt_of_predLT
      (predLT_predAddEdge_xy x y hsize)⟩

/-- Strengthen a `ValidPrefix pred` (with `x` placed before `y`) to a
`ValidPrefix (predAddEdge pred n x y)`, using SOUNDNESS
(`warshall_addEdge_sound`) to verify the strengthened `predClosed`. -/
def ValidPrefix.strengthenToAddEdge
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy_inc : @Incomp (Fin n) (predOrder pred h).toLE x y)
    (P : ValidPrefix pred n (Finset.univ : Finset (Fin n)))
    (hxy : (P.toFinPerm.symm x).val < (P.toFinPerm.symm y).val) :
    ValidPrefix (predAddEdge pred n x y) n
      (Finset.univ : Finset (Fin n)) := by
  classical
  refine ⟨P.val, P.inj, P.mem, ?_⟩
  intro i u hu_addEdge
  -- u : Fin n, hu_addEdge : predLT (predAddEdge pred n x y) u (P.val i)
  -- Convert via SOUNDNESS to predLTPlus pred x y u (P.val i).
  have h_LTPlus : predLTPlus pred x y u (P.val i) :=
    warshall_addEdge_sound h x y hxy_inc u (P.val i) hu_addEdge
  rcases h_LTPlus with h_pred | ⟨h_ux, h_yvi⟩
  · -- Standard case: predLT pred u (P.val i) — apply P.predClosed.
    exact P.predClosed i u h_pred
  · -- Strengthened case: u ≤ x and y ≤ P.val i in predOrder pred h.
    -- Take j := liftToCardUniv (P.toFinPerm.symm u); position of u.
    set π := P.toFinPerm with hπ_def
    refine ⟨liftToCardUniv (π.symm u), ?_, ?_⟩
    · -- (π.symm u).val < i.val: chain via π.symm x and π.symm y.
      -- Step A: (π.symm u).val ≤ (π.symm x).val.
      have hA : (π.symm u).val ≤ (π.symm x).val := by
        rcases h_ux with rfl | hux
        · exact le_refl _
        · exact le_of_lt (P.toFinPerm_symm_val_lt_of_predLT hux)
      -- Step B: (π.symm y).val ≤ (π.symm (P.val i)).val.
      have hB : (π.symm y).val ≤ (π.symm (P.val i)).val := by
        rcases h_yvi with hPvi | hyvi
        · rw [hPvi]
        · exact le_of_lt (P.toFinPerm_symm_val_lt_of_predLT hyvi)
      -- Step C: (π.symm (P.val i)).val = i.val.
      -- Let i' := lowerFromCardUniv i. Then liftToCardUniv i' = i and
      -- π i' = P.val (liftToCardUniv i') = P.val i, so π.symm (P.val i) = i'.
      have hC : (π.symm (P.val i)).val = i.val := by
        set i' : Fin n := lowerFromCardUniv i with hi'_def
        have hπ_i' : π i' = P.val i := by
          show P.val (liftToCardUniv i') = P.val i
          rw [liftToCardUniv_lowerFromCardUniv]
        have hsymm_i' : π.symm (P.val i) = i' := by
          rw [← hπ_i', π.symm_apply_apply]
        rw [hsymm_i']; rfl
      -- Combine A, hxy, B, C.
      show (liftToCardUniv (π.symm u)).val < i.val
      rw [liftToCardUniv_val]
      omega
    · -- P.val (liftToCardUniv (π.symm u)) = u: by definition of toFinPerm.
      show P.val (liftToCardUniv (π.symm u)) = u
      change π (π.symm u) = u
      exact π.apply_symm_apply u

@[simp] lemma ValidPrefix.strengthenToAddEdge_val
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy_inc : @Incomp (Fin n) (predOrder pred h).toLE x y)
    (P : ValidPrefix pred n (Finset.univ : Finset (Fin n)))
    (hxy : (P.toFinPerm.symm x).val < (P.toFinPerm.symm y).val) :
    (P.strengthenToAddEdge h x y hxy_inc hxy).val = P.val := rfl

/-- Backward map: a linear extension of `predOrder pred h` placing
`x` before `y` defines a `ValidPrefix (predAddEdge pred n x y)`
on `univ`. -/
noncomputable def ValidPrefix.ofLinearExtLtUniv
    (h : ValidPredMask pred n) (x y : Fin n)
    (hxy_inc : @Incomp (Fin n) (predOrder pred h).toLE x y)
    (PL : { L : @LinearExt (Fin n) (predOrder pred h) _ //
        @LinearExt.lt (Fin n) (predOrder pred h) _ L x y }) :
    ValidPrefix (predAddEdge pred n x y) n
      (Finset.univ : Finset (Fin n)) :=
  let P := linearExtUnivToValidPrefix h PL.val
  P.strengthenToAddEdge h x y hxy_inc <| by
    -- (P.toFinPerm.symm x).val = (PL.val.toFun x).val and similarly for y.
    -- PL.val.lt x y means (PL.val.toFun x).val < (PL.val.toFun y).val.
    rw [linearExtUnivToValidPrefix_toFinPerm_symm_val,
        linearExtUnivToValidPrefix_toFinPerm_symm_val]
    exact PL.property

/-- The bridge equivalence:

    `ValidPrefix (predAddEdge pred n x y) n univ ≃
        { L : LinearExt(predOrder pred h) // L.lt x y }`. -/
noncomputable def validPrefixPredAddEdgeEquivLinearExtLt
    (h : ValidPredMask pred n) (x y : Fin n) (hsize : y.val < pred.size)
    (hxy_inc : @Incomp (Fin n) (predOrder pred h).toLE x y) :
    ValidPrefix (predAddEdge pred n x y) n
      (Finset.univ : Finset (Fin n)) ≃
      { L : @LinearExt (Fin n) (predOrder pred h) _ //
          @LinearExt.lt (Fin n) (predOrder pred h) _ L x y } where
  toFun P := P.toLinearExtLtUniv h x y hsize
  invFun PL := ValidPrefix.ofLinearExtLtUniv h x y hxy_inc PL
  left_inv := fun P => by
    classical
    -- Both ValidPrefix structures share the same .val function — Subtype.ext suffices.
    apply Subtype.ext
    show (ValidPrefix.ofLinearExtLtUniv h x y hxy_inc
      (P.toLinearExtLtUniv h x y hsize)).val = P.val
    -- LHS unfolds: strengthen (linearExtUnivToValidPrefix h ((P.restrict).toLinearExtUniv h)).
    -- The `.val` of a `strengthen` is the `.val` of its argument:
    show (linearExtUnivToValidPrefix h
        ((P.restrictFromAddEdge x y).toLinearExtUniv h)).val =
      P.val
    -- And linearExtUnivToValidPrefix is the inverse of toLinearExtUniv (left_inv of
    -- validPrefixUnivEquivLinearExt, applied to P.restrictFromAddEdge x y).
    have hround :
        linearExtUnivToValidPrefix h
          ((P.restrictFromAddEdge x y).toLinearExtUniv h) =
        P.restrictFromAddEdge x y :=
      (validPrefixUnivEquivLinearExt pred h).left_inv
        (P.restrictFromAddEdge x y)
    rw [hround]
    rfl
  right_inv := fun PL => by
    classical
    apply Subtype.ext
    show ((ValidPrefix.ofLinearExtLtUniv h x y hxy_inc PL).toLinearExtLtUniv
      h x y hsize).val = PL.val
    -- LHS = ((strengthen (linExtUnivToValidPrefix h L)).restrict).toLinearExtUniv h
    -- = (linExtUnivToValidPrefix h L).toLinearExtUniv h
    --   (restrict ∘ strengthen = id on .val)
    -- = L (right_inv of validPrefixUnivEquivLinearExt)
    show ((ValidPrefix.ofLinearExtLtUniv h x y hxy_inc PL).restrictFromAddEdge x y
        ).toLinearExtUniv h = PL.val
    -- The `.val` of a restrictFromAddEdge equals the original .val,
    -- so as a ValidPrefix pred it's the same data as `linearExtUnivToValidPrefix h PL.val`.
    have hsame : (ValidPrefix.ofLinearExtLtUniv h x y hxy_inc PL).restrictFromAddEdge
        x y = linearExtUnivToValidPrefix h PL.val := by
      apply Subtype.ext
      rfl
    rw [hsame]
    -- Now apply right_inv of validPrefixUnivEquivLinearExt.
    exact (validPrefixUnivEquivLinearExt pred h).right_inv PL.val

end BridgeA4b3

/-! ### §7 — `hasBalancedPairSlow` Bool→Prop lift

The imperative `Case3Enum.hasBalancedPairSlow` uses two nested `for x in
[0:n]` / `for y in [x+1:n]` loops, with an inner `return true` short-
circuit when an incomparable pair `(x, y)` has count ratio in `[1/3,
2/3]`. Lean elaborates this to a doubly-nested `forIn (m := Id)` whose
accumulator type is `MProd (Option Bool) PUnit`: the `.fst` field is
`some true` once the early return has fired. We extract the existence
of a witness pair via a generic forIn invariant. -/

section SlowPathLift

open Case3Enum

variable {pred : Array Nat} {n : ℕ}

/-- **Generic `forIn (Id)` "yield-or-done" extraction**: a `forIn` over
a list whose body returns either `pure (yield ⟨none, ()⟩)` or
`pure (done ⟨some true, ()⟩)` results in `(some true, ())` iff some
list element triggers the `done` branch. -/
private theorem forIn_id_yield_or_done_iff
    {α : Type} (l : List α)
    (body : α → Id (ForInStep (MProd (Option Bool) PUnit)))
    (h_body : ∀ a,
      body a = pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                                        MProd (Option Bool) PUnit)) ∨
      body a = pure (ForInStep.done (⟨some true, PUnit.unit⟩ :
                                        MProd (Option Bool) PUnit))) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun a _ => body a)).fst = some true ↔
    ∃ a ∈ l, body a = pure (ForInStep.done (⟨some true, PUnit.unit⟩ :
                                              MProd (Option Bool) PUnit)) := by
  induction l with
  | nil => simp [forIn]
  | cons a as ih =>
    rw [List.forIn_cons]
    rcases h_body a with hy | hd
    · rw [hy]
      change (forIn (m := Id) as
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _).fst = some true ↔ _
      rw [ih]
      constructor
      · rintro ⟨a', hmem, hb⟩
        exact ⟨a', List.mem_cons_of_mem _ hmem, hb⟩
      · rintro ⟨a', hmem, hb⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · rw [hy] at hb
          exact absurd hb (fun h => by cases h)
        · exact ⟨a', hmem', hb⟩
    · rw [hd]
      change (((⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit).fst :
                Option Bool) = some true) ↔ _
      refine ⟨fun _ => ⟨a, ?_, hd⟩, fun _ => rfl⟩
      exact List.mem_cons_self

/-- The inner loop body of `hasBalancedPairSlow`. Decision-style `if`
chain over `testBit'` and the count gate. -/
private def slowInnerBody (pred : Array Nat) (n total x : ℕ) :
    ℕ → Id (ForInStep (MProd (Option Bool) PUnit)) :=
  fun y =>
    if testBit' (pred.getD y 0) x = true then
      (pure (ForInStep.yield ⟨none, PUnit.unit⟩) : Id _)
    else if testBit' (pred.getD x 0) y = true then
      pure (ForInStep.yield ⟨none, PUnit.unit⟩)
    else if (decide (3 * countLinearExtensions
        (addEdgeClose pred n x y) n ≥ total) &&
        decide (3 * countLinearExtensions
          (addEdgeClose pred n x y) n ≤ 2 * total)) = true then
      pure (ForInStep.done ⟨some true, PUnit.unit⟩)
    else pure (ForInStep.yield ⟨none, PUnit.unit⟩)

private lemma slowInnerBody_yield_or_done
    (pred : Array Nat) (n total x y : ℕ) :
    slowInnerBody pred n total x y =
      pure (ForInStep.yield (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ∨
    slowInnerBody pred n total x y =
      pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
  unfold slowInnerBody
  by_cases h1 : testBit' (pred.getD y 0) x = true
  · left; rw [if_pos h1]
  by_cases h2 : testBit' (pred.getD x 0) y = true
  · left; rw [if_neg h1, if_pos h2]
  by_cases h3 : (decide (3 * countLinearExtensions (addEdgeClose pred n x y) n ≥ total) &&
                  decide (3 * countLinearExtensions (addEdgeClose pred n x y) n ≤ 2 * total)) = true
  · right; rw [if_neg h1, if_neg h2, if_pos h3]
  · left; rw [if_neg h1, if_neg h2, if_neg h3]

private lemma slowInnerBody_done_iff (pred : Array Nat) (n total x y : ℕ) :
    slowInnerBody pred n total x y =
        pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ↔
      ¬ testBit' (pred.getD y 0) x = true ∧
      ¬ testBit' (pred.getD x 0) y = true ∧
      3 * countLinearExtensions (addEdgeClose pred n x y) n ≥ total ∧
      3 * countLinearExtensions (addEdgeClose pred n x y) n ≤ 2 * total := by
  unfold slowInnerBody
  -- yield ≠ done in pure form.
  have hYne : (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
        MProd (Option Bool) PUnit)) : Id _) ≠
      pure (ForInStep.done ⟨some true, PUnit.unit⟩) := fun h => by cases h
  by_cases h1 : testBit' (pred.getD y 0) x = true
  · rw [if_pos h1]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨h, _, _, _⟩; exact absurd h1 h
  by_cases h2 : testBit' (pred.getD x 0) y = true
  · rw [if_neg h1, if_pos h2]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨_, h, _, _⟩; exact absurd h2 h
  by_cases h3 : (decide (3 * countLinearExtensions (addEdgeClose pred n x y) n ≥ total) &&
                  decide (3 * countLinearExtensions (addEdgeClose pred n x y) n ≤ 2 * total)) = true
  · rw [if_neg h1, if_neg h2, if_pos h3]
    refine ⟨fun _ => ⟨h1, h2, ?_⟩, fun _ => rfl⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h3
    exact h3
  · rw [if_neg h1, if_neg h2, if_neg h3]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨_, _, ha, hb⟩
    refine absurd ?_ h3
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨ha, hb⟩

/-- The outer loop body of `hasBalancedPairSlow`: run the inner forIn,
then propagate `done` if the inner found a pair, else `yield`. -/
private def slowOuterBody (pred : Array Nat) (n total : ℕ) :
    ℕ → Id (ForInStep (MProd (Option Bool) PUnit)) :=
  fun x => do
    let r ← forIn (m := Id) (List.range' (x+1) (n - (x+1)))
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun y _ => slowInnerBody pred n total x y)
    match r.fst with
    | none => pure (ForInStep.yield ⟨none, PUnit.unit⟩)
    | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)

/-- The inner forIn's `.fst` is in `{none, some true}` (not `some false`). -/
private lemma slow_inner_forIn_fst (pred : Array Nat) (n total x : ℕ)
    (l : List ℕ) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun y _ => slowInnerBody pred n total x y)).fst = none ∨
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun y _ => slowInnerBody pred n total x y)).fst = some true := by
  induction l with
  | nil => left; rfl
  | cons y ys ih =>
    rw [List.forIn_cons]
    rcases slowInnerBody_yield_or_done pred n total x y with hy | hd
    · rw [hy]
      change ((forIn (m := Id) ys
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = none) ∨ _ = some true
      exact ih
    · rw [hd]
      right; rfl

private lemma slowOuterBody_yield_or_done
    (pred : Array Nat) (n total x : ℕ) :
    slowOuterBody pred n total x =
      pure (ForInStep.yield (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ∨
    slowOuterBody pred n total x =
      pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
  rcases slow_inner_forIn_fst pred n total x (List.range' (x+1) (n - (x+1)))
    with hn | hs
  · left
    show (match (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun y _ => slowInnerBody pred n total x y) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _
    rw [hn]
  · right
    show (match (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun y _ => slowInnerBody pred n total x y) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _
    rw [hs]

private lemma slowOuterBody_done_iff (pred : Array Nat) (n total x : ℕ) :
    slowOuterBody pred n total x =
        pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ↔
    ∃ y ∈ List.range' (x+1) (n - (x+1)),
      ¬ testBit' (pred.getD y 0) x = true ∧
      ¬ testBit' (pred.getD x 0) y = true ∧
      3 * countLinearExtensions (addEdgeClose pred n x y) n ≥ total ∧
      3 * countLinearExtensions (addEdgeClose pred n x y) n ≤ 2 * total := by
  rcases slow_inner_forIn_fst pred n total x (List.range' (x+1) (n - (x+1)))
    with hn | hs
  · -- inner returned none: outer yields, never equals done
    show (match (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun y _ => slowInnerBody pred n total x y) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _ ↔ _
    rw [hn]
    refine ⟨fun h => absurd h (fun h => by cases h), ?_⟩
    rintro ⟨y, hmem, hgate⟩
    -- Inner's fst is `none`, but a witness exists — contradiction.
    have hex : ∃ y ∈ List.range' (x+1) (n - (x+1)),
        slowInnerBody pred n total x y =
          pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) :=
      ⟨y, hmem, (slowInnerBody_done_iff pred n total x y).mpr hgate⟩
    have hcontra : (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun y _ => slowInnerBody pred n total x y) :
        MProd (Option Bool) PUnit).fst = some true :=
      (forIn_id_yield_or_done_iff (List.range' (x+1) (n - (x+1)))
        (slowInnerBody pred n total x)
        (slowInnerBody_yield_or_done pred n total x)).mpr hex
    rw [hn] at hcontra; exact absurd hcontra (by intro h; cases h)
  · -- inner returned some true: outer is done
    show (match (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun y _ => slowInnerBody pred n total x y) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _ ↔ _
    rw [hs]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    -- inner forIn returned some true ⇒ a witness exists.
    have hex : ∃ y ∈ List.range' (x+1) (n - (x+1)),
        slowInnerBody pred n total x y =
          pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) :=
      (forIn_id_yield_or_done_iff (List.range' (x+1) (n - (x+1)))
        (slowInnerBody pred n total x)
        (slowInnerBody_yield_or_done pred n total x)).mp hs
    obtain ⟨y, hmem, hbody⟩ := hex
    exact ⟨y, hmem, (slowInnerBody_done_iff pred n total x y).mp hbody⟩

/-- **Imperative→functional reduction** for `hasBalancedPairSlow`. -/
private theorem hasBalancedPairSlow_eq_outer_fst (pred : Array Nat) (n : ℕ) :
    Case3Enum.hasBalancedPairSlow pred n =
      (match (forIn (m := Id) (List.range' 0 n)
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun x _ => slowOuterBody pred n (countLinearExtensions pred n) x)).fst with
       | none => false
       | some a => a) := by
  unfold Case3Enum.hasBalancedPairSlow slowOuterBody slowInnerBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- **`hasBalancedPairSlow` Bool→Prop lift, on raw `ℕ`-indices.** -/
private theorem hasBalancedPairSlow_eq_true_iff_nat (pred : Array Nat) (n : ℕ) :
    Case3Enum.hasBalancedPairSlow pred n = true ↔
    ∃ x ∈ List.range' 0 n, ∃ y ∈ List.range' (x+1) (n - (x+1)),
      ¬ testBit' (pred.getD y 0) x = true ∧
      ¬ testBit' (pred.getD x 0) y = true ∧
      3 * countLinearExtensions (addEdgeClose pred n x y) n ≥
        countLinearExtensions pred n ∧
      3 * countLinearExtensions (addEdgeClose pred n x y) n ≤
        2 * countLinearExtensions pred n := by
  rw [hasBalancedPairSlow_eq_outer_fst]
  set total := countLinearExtensions pred n
  -- Outer forIn `.fst` is in `{none, some true}` (analogous to inner).
  have h_outer_fst :
      (forIn (m := Id) (List.range' 0 n)
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun x _ => slowOuterBody pred n total x)).fst = some true ↔
      ∃ x ∈ List.range' 0 n,
        slowOuterBody pred n total x =
          pure (ForInStep.done (⟨some true, PUnit.unit⟩ :
                                  MProd (Option Bool) PUnit)) :=
    forIn_id_yield_or_done_iff _ _ (slowOuterBody_yield_or_done pred n total)
  -- The match on `.fst` reduces to checking `= some true`.
  set f := (forIn (m := Id) (List.range' 0 n)
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun x _ => slowOuterBody pred n total x)).fst with hf_def
  -- Step: f = some true ↔ match f with | none => false | some a => a = true.
  -- We need the latter form; case analysis on f's value.
  rcases (show f = none ∨ f = some true by
    -- Same yield_or_done argument as for the inner.
    rcases slow_inner_forIn_fst (n := 0) (total := 0) (pred := #[]) (x := 0) [] with _ | _
    -- Just structural: by ih on the outer list, using slowOuterBody_yield_or_done.
    -- Use forIn_id_yield_or_done structure inductively.
    · clear * - pred n total
      -- Re-prove for outer.
      have aux : ∀ (l : List ℕ),
          (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
            (fun x _ => slowOuterBody pred n total x)).fst = none ∨
          (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
            (fun x _ => slowOuterBody pred n total x)).fst = some true := by
        intro l
        induction l with
        | nil => left; rfl
        | cons x xs ih =>
          rw [List.forIn_cons]
          rcases slowOuterBody_yield_or_done pred n total x with hy | hd
          · rw [hy]
            change ((forIn (m := Id) xs
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
              MProd (Option Bool) PUnit).fst = none) ∨ _ = some true
            exact ih
          · rw [hd]; right; rfl
      exact aux (List.range' 0 n)
    · clear * - pred n total
      have aux : ∀ (l : List ℕ),
          (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
            (fun x _ => slowOuterBody pred n total x)).fst = none ∨
          (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
            (fun x _ => slowOuterBody pred n total x)).fst = some true := by
        intro l
        induction l with
        | nil => left; rfl
        | cons x xs ih =>
          rw [List.forIn_cons]
          rcases slowOuterBody_yield_or_done pred n total x with hy | hd
          · rw [hy]
            change ((forIn (m := Id) xs
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
              MProd (Option Bool) PUnit).fst = none) ∨ _ = some true
            exact ih
          · rw [hd]; right; rfl
      exact aux (List.range' 0 n)) with hfn | hfs
  · -- f = none: LHS is false; RHS must also be false.
    rw [hfn]
    refine ⟨fun h => absurd h Bool.false_ne_true, ?_⟩
    rintro ⟨x, hx, y, hy, hgate⟩
    have hex : ∃ x ∈ List.range' 0 n,
        slowOuterBody pred n total x =
          pure (ForInStep.done (⟨some true, PUnit.unit⟩ :
                                  MProd (Option Bool) PUnit)) :=
      ⟨x, hx, (slowOuterBody_done_iff pred n total x).mpr ⟨y, hy, hgate⟩⟩
    have := h_outer_fst.mpr hex
    rw [hfn] at this; cases this
  · -- f = some true: LHS is true; RHS witnessed.
    rw [hfs]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, hbody⟩ := h_outer_fst.mp hfs
    obtain ⟨y, hy, hgate⟩ := (slowOuterBody_done_iff pred n total x).mp hbody
    exact ⟨x, hx, y, hy, hgate⟩

/-- **`hasBalancedPairSlow` Bool→Prop lift, with `Fin n` quantifiers.**
A balanced-pair-slow positive result yields an explicit incomparable
pair `(x, y) : Fin n × Fin n` with `x.val < y.val` whose count gate
holds. -/
theorem hasBalancedPairSlow_eq_true_iff (pred : Array Nat) (n : ℕ) :
    Case3Enum.hasBalancedPairSlow pred n = true ↔
    ∃ x : Fin n, ∃ y : Fin n, x.val < y.val ∧
      ¬ testBit' (pred.getD y.val 0) x.val = true ∧
      ¬ testBit' (pred.getD x.val 0) y.val = true ∧
      3 * countLinearExtensions (addEdgeClose pred n x.val y.val) n ≥
        countLinearExtensions pred n ∧
      3 * countLinearExtensions (addEdgeClose pred n x.val y.val) n ≤
        2 * countLinearExtensions pred n := by
  rw [hasBalancedPairSlow_eq_true_iff_nat]
  constructor
  · rintro ⟨x, hx, y, hy, hgate⟩
    rw [List.mem_range'] at hx hy
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    -- hxi : x = 0 + 1 * i, so x = i and x < n.
    have hx_eq : x = i := by simp at hxi; exact hxi
    have hy_eq : y = (x + 1) + j := by simp at hyj; exact hyj
    have hx_lt : x < n := by rw [hx_eq]; exact hi
    have hy_lt : y < n := by rw [hy_eq]; omega
    refine ⟨⟨x, hx_lt⟩, ⟨y, hy_lt⟩, ?_, hgate⟩
    show x < y
    rw [hy_eq]; omega
  · rintro ⟨x, y, hxy, hgate⟩
    refine ⟨x.val, ?_, y.val, ?_, hgate⟩
    · rw [List.mem_range']
      exact ⟨x.val, x.isLt, by simp⟩
    · rw [List.mem_range']
      refine ⟨y.val - (x.val + 1), ?_, ?_⟩
      · have := y.isLt; omega
      · simp; omega

end SlowPathLift

/-! ### §8 — Final balanced-pair theorem

Combine the §7 slow-path Bool→Prop lift with the §6 bridge
(`validPrefixPredAddEdgeEquivLinearExtLt`) and the A3 main theorem
(`countLinearExtensions_eq_numLinExt`) to identify the count gate
`3 · cnt ≥ total ∧ 3 · cnt ≤ 2 · total` with `1/3 ≤ probLT x y ≤ 2/3`,
giving the Prop-level conclusion `HasBalancedPair`. -/

section FinalBalancedTheorem

open Case3Enum

variable {pred : Array Nat} {n : ℕ}

/-- **Slow-path Prop lift to `HasBalancedPair`.** Given the Bool-level
fact `hasBalancedPairSlow pred n = true`, plus structural validity of
`pred` and the size constraint `pred.size = n`, the Prop-level
conclusion `HasBalancedPair (Fin n) [predOrder pred h]` follows. -/
theorem hasBalancedPair_of_hasBalancedPairSlow
    (h : ValidPredMask pred n) (h_bnd : predBitsBoundedBy pred n)
    (h_size : pred.size = n)
    (h_slow : Case3Enum.hasBalancedPairSlow pred n = true) :
    @HasBalancedPair (Fin n) (predOrder pred h) _ _ := by
  classical
  obtain ⟨x, y, hxy_lt, hbit_yx, hbit_xy, hgate_lo, hgate_hi⟩ :=
    (hasBalancedPairSlow_eq_true_iff pred n).mp h_slow
  -- x ∥ y in predOrder pred h.
  have hne : x ≠ y := fun heq => Nat.lt_irrefl _ (heq ▸ hxy_lt)
  -- predLT pred x y = testBit' (pred[y]) x.val. So:
  --   hbit_yx : ¬ testBit' (pred.getD y.val 0) x.val = true ↔ ¬ predLT pred x y.
  --   hbit_xy : ¬ testBit' (pred.getD x.val 0) y.val = true ↔ ¬ predLT pred y x.
  have hnxy : ¬ predLT pred x y := hbit_yx
  have hnyx : ¬ predLT pred y x := hbit_xy
  have hinc : @Incomp (Fin n) (predOrder pred h).toLE x y := by
    refine ⟨?_, ?_⟩
    · rintro (rfl | hxy) <;> [exact hne rfl; exact hnxy hxy]
    · rintro (heq | hyx) <;> [exact hne heq.symm; exact hnyx hyx]
  -- y.val < pred.size from h_size.
  have hsize : y.val < pred.size := h_size ▸ y.isLt
  -- Bridge: Fintype.card { L : LinearExt // L.lt x y } = countLinearExtensions (predAddEdge ...) n.
  have hcnt_eq :
      Fintype.card { L : @LinearExt (Fin n) (predOrder pred h) _ //
          @LinearExt.lt (Fin n) (predOrder pred h) _ L x y } =
        countLinearExtensions (predAddEdge pred n x y) n := by
    have h_bnd_add : predBitsBoundedBy (predAddEdge pred n x y) n :=
      predBitsBoundedBy_predAddEdge h_bnd x y
    have hN : 0 < 1 <<< n := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos n
    have hN' : (1 <<< n) - 1 < 1 <<< n := Nat.sub_lt hN Nat.one_pos
    rw [show countLinearExtensions (predAddEdge pred n x y) n =
        clERec (predAddEdge pred n x y) n ((1 <<< n) - 1) from
      countLinearExtensions_eq_clERec _ _]
    rw [clERec_eq_card_validPrefix h_bnd_add ((1 <<< n) - 1) hN', maskSet_full]
    exact (Fintype.card_congr
      (validPrefixPredAddEdgeEquivLinearExtLt h x y hsize hinc).symm)
  -- countLinearExtensions pred n = numLinExt (Fin n).
  have hnum_eq :
      countLinearExtensions pred n =
        @numLinExt (Fin n) (predOrder pred h) _ _ :=
    countLinearExtensions_eq_numLinExt h h_bnd
  -- Convert the count-card to filter-card.
  have hfilter_card_eq :
      ((Finset.univ : Finset (@LinearExt (Fin n) (predOrder pred h) _)).filter
          (fun L => @LinearExt.lt (Fin n) (predOrder pred h) _ L x y)).card =
        countLinearExtensions (predAddEdge pred n x y) n := by
    rw [← hcnt_eq]
    exact (Fintype.card_subtype _).symm
  -- probLT x y = cnt / total in ℚ.
  have hprob_eq :
      @probLT (Fin n) (predOrder pred h) _ _ x y =
        (countLinearExtensions (predAddEdge pred n x y) n : ℚ) /
        (countLinearExtensions pred n : ℚ) := by
    unfold probLT
    congr 1
    · norm_cast
      convert hfilter_card_eq using 3
    · norm_cast
      exact hnum_eq.symm
  -- Total > 0.
  have htotal_pos : (0 : ℚ) < (countLinearExtensions pred n : ℚ) := by
    rw [hnum_eq]
    exact_mod_cast (@numLinExt_pos (Fin n) (predOrder pred h) _ _)
  -- Lift the integer gate to ℚ.
  have h_lo : (1 : ℚ) / 3 ≤ @probLT (Fin n) (predOrder pred h) _ _ x y := by
    rw [hprob_eq]
    rw [le_div_iff₀ htotal_pos]
    have : (countLinearExtensions pred n : ℚ) ≤
        3 * (countLinearExtensions (predAddEdge pred n x y) n : ℚ) := by
      have := hgate_lo
      rw [show (predAddEdge pred n x y) = addEdgeClose pred n x.val y.val from
          predAddEdge_eq pred n x y] at *
      exact_mod_cast hgate_lo
    linarith
  have h_hi : @probLT (Fin n) (predOrder pred h) _ _ x y ≤ (2 : ℚ) / 3 := by
    rw [hprob_eq]
    rw [div_le_iff₀ htotal_pos]
    have : 3 * (countLinearExtensions (predAddEdge pred n x y) n : ℚ) ≤
        2 * (countLinearExtensions pred n : ℚ) := by
      rw [show (predAddEdge pred n x y) = addEdgeClose pred n x.val y.val from
          predAddEdge_eq pred n x y] at *
      exact_mod_cast hgate_hi
    linarith
  refine ⟨x, y, hinc, h_lo, h_hi⟩

/-- **Final theorem**: `Case3Enum.hasBalancedPair pred n = true` lifts
to `HasBalancedPair (Fin n) [predOrder pred h]`. The fast path
(`findSymmetricPair`) is dispatched to §3's
`hasBalancedPair_of_symmetric` whenever a `Symmetric` witness is
extracted from the Bool indicator; the slow path is dispatched to
`hasBalancedPair_of_hasBalancedPairSlow` (§8). The `findSymmetricPair`
Bool→`Symmetric` extraction (parallel to §7) is supplied as the
hypothesis `h_sym_lift`; A5 (`mg-ff49`) provides this together with
the band-major Fin-n encoding when calling
`bounded_irreducible_balanced`. -/
theorem hasBalancedPair_of_hasBalancedPair
    (h : ValidPredMask pred n) (h_bnd : predBitsBoundedBy pred n)
    (h_size : pred.size = n)
    (h_sym_lift : (Case3Enum.findSymmetricPair pred n).isSome = true →
                  ∃ x y : Fin n, Symmetric pred n x y)
    (h_bal : Case3Enum.hasBalancedPair pred n = true) :
    @HasBalancedPair (Fin n) (predOrder pred h) _ _ := by
  unfold Case3Enum.hasBalancedPair at h_bal
  cases h_eq : Case3Enum.findSymmetricPair pred n with
  | none =>
    rw [h_eq] at h_bal
    exact hasBalancedPair_of_hasBalancedPairSlow h h_bnd h_size h_bal
  | some pair =>
    obtain ⟨x, y, hSym⟩ :=
      h_sym_lift (by rw [h_eq]; rfl)
    exact hasBalancedPair_of_symmetric h hSym

end FinalBalancedTheorem

end Case3Enum
end Step8
end OneThird
