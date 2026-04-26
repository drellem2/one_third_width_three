/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.BipartiteEnum
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Case 1 of `prop:in-situ-balanced` as a reusable structural lemma
(`mg-A8` partial deliverable, `mg-f92d`)

This file ports `prop:in-situ-balanced` Case 1 (`step8.tex:2984-2999`) — the
"symmetric within-band pair with full ambient profile match" automorphism
argument — from its specialised K=2 form in
`OneThird.Step8.BipartiteEnum.bipartite_balanced_enum` to a general Prop-level
lemma `Step8.hasBalancedPair_of_ambient_profile_match`. The lemma takes the
ambient profile-match conditions directly as hypotheses and returns a
balanced pair, without depending on bipartite or layered structure.

## Lemma

```
theorem hasBalancedPair_of_ambient_profile_match
    (a a' : α) (hne : a ≠ a')
    (h_up : ∀ z, a < z ↔ a' < z)
    (h_down : ∀ z, z < a ↔ z < a') :
    HasBalancedPair α
```

## Proof outline

The hypotheses say `a` and `a'` have identical ambient strict-`<` profile
in `α` (both up-set and down-set, on the strict order). The transposition
`Equiv.swap a a'` is therefore a poset automorphism of `α`:

* **Incomparability falls out.** Applying `h_up` at `z = a'` gives
  `a < a' ↔ a' < a'`; the right-hand side is false by irreflexivity, so
  `¬ a < a'`. Symmetric reasoning with `h_up` at `z = a` gives `¬ a' < a`.
  Combined with `hne`, this forces `a ∥ a'`.
* **`Equiv.swap a a'` preserves `≤`.** Case-split on whether `x, y ∈ {a, a'}`:
  the only non-trivial cases use `h_up` (resp.\ `h_down`) to upgrade
  `a ≤ y` (resp.\ `x ≤ a`) past the inequality `≠ a` into the strict form,
  then transport across the profile equivalence.

`Equiv.swap a a'` is its own inverse, so the pullback of a linear extension
along `swap a a'` is an involution on `LinearExt α`. Pullback exchanges the
filters `{L : L.lt a a'}` and `{L : L.lt a' a}`, giving them equal
cardinality. Combined with `probLT_add_probLT_of_ne`, we conclude
`probLT a a' = 1/2 ∈ [1/3, 2/3]`, so `(a, a')` is a balanced pair.

## Why this is reusable

The lemma's hypothesis is the ambient form of Case 1 of
`prop:in-situ-balanced`: it is **stronger** than the K=2 bipartite hypothesis
of `BipartiteEnum.bipartite_balanced_enum` (which derives the same swap
automorphism from the bipartite cover + cross-comparability axioms), but
**weaker** than requiring a specific layered structure on `α`.
Any future implementation of the `hStruct` slot of
`Step8.bounded_irreducible_balanced_hybrid` (= the structural-Case-1/2
discharge of `prop:in-situ-balanced` for `¬ InCase3Scope` leaves) that
produces a within-band pair with matching ambient profile can plug
directly into this lemma to extract the balanced pair.

## What this file does **not** do

It does **not** discharge the `hStruct` slot of
`bounded_irreducible_balanced_hybrid`. The Case 1 hypothesis (existence of
an ambient-profile-matching within-band pair) is **not implied** by the
hybrid theorem's hypotheses on every `¬ InCase3Scope` leaf — Cases 2 and 3
of `prop:in-situ-balanced` may apply instead. See `docs/a8-status.md` for
the full mg-A8 status report and the recommended sub-split (A8-S1
generalising this Case 1 lift, A8-S2 porting the FKG monotonicity
argument of Case 2, A8-S3 the residual width-3 profile-antichain
discharge for `¬ InCase3Scope`).

## References

* `step8.tex` `prop:in-situ-balanced` Case 1 (`step8.tex:2984-2999`).
* `lean/OneThird/Step8/BipartiteEnum.lean` — K=2 specialisation
  (`bipartite_balanced_enum`).
* `docs/a8-status.md` — full mg-A8 status report (this commit).
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-! ### §1 — `Equiv.swap` evaluation -/

/-- Evaluate `Equiv.swap a a'` at any element as a branching expression.
A local restatement of the helper used in `BipartiteEnum.lean §2`. -/
private lemma swap_eval (a a' z : α) :
    Equiv.swap a a' z = (if z = a then a' else if z = a' then a else z) := by
  split_ifs with h1 h2
  · rw [h1]; exact Equiv.swap_apply_left a a'
  · rw [h2]; exact Equiv.swap_apply_right a a'
  · exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-! ### §2 — `Equiv.swap a a'` is a poset automorphism from profile match -/

/-- Generalisation of `OneThird.Step8.BipartiteEnum.swap_preserves_le` from
the bipartite hypotheses (cover + directed cross-comparability) to the
ambient profile-match hypothesis (`prop:in-situ-balanced` Case 1).

Given `a, a' : α` with identical ambient strict-`<` profile in both
directions, `Equiv.swap a a'` preserves `≤`. -/
private lemma swap_preserves_le_of_profile_match
    {a a' : α} (hne : a ≠ a')
    (h_up : ∀ z, a < z ↔ a' < z)
    (h_down : ∀ z, z < a ↔ z < a')
    {x y : α} (hxy : x ≤ y) :
    Equiv.swap a a' x ≤ Equiv.swap a a' y := by
  -- Strict-< version of the ambient incomparability of `a` and `a'`.
  have h_aa' : ¬ a < a' := fun h => lt_irrefl a' ((h_up a').mp h)
  have h_a'a : ¬ a' < a := fun h => lt_irrefl a ((h_up a).mpr h)
  -- Case-split on the swap evaluation at `x` and `y`, following the
  -- pattern of `BipartiteEnum.swap_preserves_le`.
  rw [swap_eval a a' x, swap_eval a a' y]
  by_cases hxa : x = a
  · rw [if_pos hxa]
    by_cases hya : y = a
    · rw [if_pos hya]
    rw [if_neg hya]
    by_cases hya' : y = a'
    · rw [if_pos hya']
      -- `hxy : a ≤ a'` (after `x = a`, `y = a'`) with `a ≠ a'` gives
      -- `a < a'`, contradicting `h_aa'`.
      exfalso
      have hae : a ≤ a' := hxa ▸ hya' ▸ hxy
      exact h_aa' (lt_of_le_of_ne hae hne)
    rw [if_neg hya']
    -- `y ∉ {a, a'}`, `x = a`. Goal: `a' ≤ y`.
    have hay : a ≤ y := hxa ▸ hxy
    have hay_lt : a < y := lt_of_le_of_ne hay (Ne.symm hya)
    exact ((h_up y).mp hay_lt).le
  rw [if_neg hxa]
  by_cases hxa' : x = a'
  · rw [if_pos hxa']
    by_cases hya : y = a
    · rw [if_pos hya]
      -- `hxy : a' ≤ a` (after `x = a'`, `y = a`) gives `a' < a`,
      -- contradicting `h_a'a`.
      exfalso
      have hae : a' ≤ a := hxa' ▸ hya ▸ hxy
      exact h_a'a (lt_of_le_of_ne hae (Ne.symm hne))
    rw [if_neg hya]
    by_cases hya' : y = a'
    · rw [if_pos hya']
    rw [if_neg hya']
    -- `y ∉ {a, a'}`, `x = a'`. Goal: `a ≤ y`.
    have hay : a' ≤ y := hxa' ▸ hxy
    have hay_lt : a' < y := lt_of_le_of_ne hay (Ne.symm hya')
    exact ((h_up y).mpr hay_lt).le
  rw [if_neg hxa']
  -- `x ∉ {a, a'}`.
  by_cases hya : y = a
  · rw [if_pos hya]
    -- Goal: `x ≤ a'`.
    have hax : x ≤ a := hya ▸ hxy
    have hax_lt : x < a := lt_of_le_of_ne hax hxa
    exact ((h_down x).mp hax_lt).le
  rw [if_neg hya]
  by_cases hya' : y = a'
  · rw [if_pos hya']
    -- Goal: `x ≤ a`.
    have hax : x ≤ a' := hya' ▸ hxy
    have hax_lt : x < a' := lt_of_le_of_ne hax hxa'
    exact ((h_down x).mpr hax_lt).le
  rw [if_neg hya']
  -- `x, y` both `∉ {a, a'}`: trivial.
  exact hxy

/-! ### §3 — Filter cardinality via the swap involution -/

/-- The swap involution on `LinearExt α` exchanges the ordered filters
`{L : L.lt a a'}` and `{L : L.lt a' a}`, so the two have equal
cardinality. Generalises
`OneThird.Step8.BipartiteEnum.filter_lt_card_eq_of_same_layer`. -/
private lemma filter_lt_card_eq_of_profile_match
    {a a' : α} (hne : a ≠ a')
    (h_up : ∀ z, a < z ↔ a' < z)
    (h_down : ∀ z, z < a ↔ z < a') :
    ((Finset.univ : Finset (LinearExt α)).filter
        (fun L => L.lt a a')).card =
      ((Finset.univ : Finset (LinearExt α)).filter
        (fun L => L.lt a' a)).card := by
  classical
  -- The swap automorphism's `≤`-preservation, packaged as the
  -- `LinearExt.pullback` hypothesis.
  have hσ : ∀ x y : α, x ≤ y → Equiv.swap a a' x ≤ Equiv.swap a a' y :=
    fun _ _ hxy =>
      swap_preserves_le_of_profile_match hne h_up h_down hxy
  -- Pullback by the swap is an involution on `LinearExt α`.
  have hinv : ∀ x : α, (Equiv.swap a a') ((Equiv.swap a a') x) = x :=
    fun x => Equiv.swap_apply_self a a' x
  refine Finset.card_bij (fun L _ => L.pullback hσ) ?_ ?_ ?_
  · intro L hL
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
    show (L.pullback hσ).pos a' < (L.pullback hσ).pos a
    rw [LinearExt.pullback_pos, LinearExt.pullback_pos,
        Equiv.swap_apply_right, Equiv.swap_apply_left]
    exact hL
  · intro L₁ _ L₂ _ heq
    have heq' : L₁.pullback hσ = L₂.pullback hσ := heq
    have h : (L₁.pullback hσ).pullback hσ = (L₂.pullback hσ).pullback hσ := by
      rw [heq']
    rw [L₁.pullback_pullback hσ hinv,
        L₂.pullback_pullback hσ hinv] at h
    exact h
  · intro L hL
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL
    refine ⟨L.pullback hσ, ?_, L.pullback_pullback hσ hinv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (L.pullback hσ).pos a < (L.pullback hσ).pos a'
    rw [LinearExt.pullback_pos, LinearExt.pullback_pos,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact hL

/-! ### §4 — `probLT a a' = 1/2` -/

/-- For `a, a' : α` with identical ambient strict-`<` profile,
`probLT a a' = 1/2`. -/
private lemma probLT_eq_half_of_profile_match
    {a a' : α} (hne : a ≠ a')
    (h_up : ∀ z, a < z ↔ a' < z)
    (h_down : ∀ z, z < a ↔ z < a') :
    probLT a a' = 1 / 2 := by
  have hcard := filter_lt_card_eq_of_profile_match hne h_up h_down
  have hsum := probLT_add_probLT_of_ne hne
  have heq : probLT a a' = probLT a' a := by
    unfold probLT
    have : ((((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt a a')).card : ℚ)) =
            ((((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt a' a)).card : ℚ)) := by
      exact_mod_cast hcard
    rw [this]
  linarith

/-! ### §5 — Main theorem: `prop:in-situ-balanced` Case 1, ambient form -/

/-- **`prop:in-situ-balanced` Case 1 (general)** (`step8.tex:2984-2999`,
`mg-A8` partial / `mg-f92d`).

If `α` admits two distinct elements `a, a'` with identical ambient
strict-`<` profile in both directions, then `α` has a balanced pair.

This generalises `OneThird.Step8.BipartiteEnum.bipartite_balanced_enum`
from the K=2 bipartite specialisation to the ambient profile-match form,
matching the wording of `prop:in-situ-balanced` Case 1 in
`step8.tex:2984-2999`.

**Proof.** The hypothesis forces `a ∥ a'` (Case 1 of the discussion in
`§5` above), and `Equiv.swap a a'` is a poset automorphism of `α`
(`swap_preserves_le_of_profile_match`). Pullback along the swap is an
involution on `LinearExt α` exchanging `{L : a <_L a'}` and
`{L : a' <_L a}`, giving `probLT a a' = 1/2 ∈ [1/3, 2/3]`. -/
theorem hasBalancedPair_of_ambient_profile_match
    (a a' : α) (hne : a ≠ a')
    (h_up : ∀ z, a < z ↔ a' < z)
    (h_down : ∀ z, z < a ↔ z < a') :
    HasBalancedPair α := by
  -- Incomparability of `a, a'` falls out of the strict-< profile match.
  have h_aa' : ¬ a < a' := fun h => lt_irrefl a' ((h_up a').mp h)
  have h_a'a : ¬ a' < a := fun h => lt_irrefl a ((h_up a).mpr h)
  have hIncomp : a ∥ a' := by
    refine ⟨?_, ?_⟩
    · intro hle
      exact h_aa' (lt_of_le_of_ne hle hne)
    · intro hle
      exact h_a'a (lt_of_le_of_ne hle (Ne.symm hne))
  have hhalf := probLT_eq_half_of_profile_match hne h_up h_down
  refine ⟨a, a', hIncomp, ?_, ?_⟩
  · rw [hhalf]; norm_num
  · rw [hhalf]; norm_num

end Step8
end OneThird
