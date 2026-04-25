/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Bipartite finite enumeration: discharges the F4 axiom
(`step8.tex:2942-2955`)

This file closes the `fkg_case_output` axiom of
`OneThird.Step8.LayeredBalanced` by a uniform finite argument across the
`≤ 1024` bipartite configurations on `|A|, |B| ≤ 3`. `mg-68af` rescoped
the axiom so that the ambient poset `α = A ⊔ B` is *entirely* a height-2
bipartite reduct: the covering hypothesis `A ∪ B = Finset.univ` bounds
`|α| ≤ 6`, and the directed-comparabilities hypothesis
`∀ a ∈ A, b ∈ B, a ≤ b` reduces the poset up to isomorphism to the data
`(|A|, |B|) ∈ {(0,0), …, (3,3)}`.

## The symmetry argument

For each bipartite configuration, the proof is the *Case 1* involution
of `prop:bipartite-balanced` (`step8.tex:2836-2845`, the
symmetric-pair case) applied uniformly:

1. An incomparable pair `(u, v)` in such a poset lies either entirely
   in `A` or entirely in `B` (cross-layer pairs are forced comparable
   by `hAB`).
2. With `u, v` in the same antichain, every element of `α` has the same
   `≤`-relation to `u` as to `v`: they share `up(u) = up(v)` and
   `down(u) = down(v)` because `A, B` are antichains and all cross-layer
   relations go `A < B`.
3. Hence `Equiv.swap u v : α ≃ α` is a poset automorphism.
4. Pull-back of linear extensions along `swap u v` gives an involution
   `LinearExt α ≃ LinearExt α` that exchanges the filters
   `{L : L.lt u v}` and `{L : L.lt v u}`; their cardinalities are
   therefore equal.
5. Combined with `probLT u v + probLT v u = 1`
   (`probLT_add_probLT_of_ne`), we get `probLT u v = 1/2 ∈ [1/3, 2/3]`,
   so `(u, v)` is balanced.

This discharges the former axiom: every bipartite configuration with an
incomparable pair satisfies the `prop:bipartite-balanced` conclusion
uniformly via the Case 1 involution.

## Main result

* `bipartite_balanced_enum` — replaces the `fkg_case_output` axiom.
* After this file loads, `#print axioms bipartite_balanced_enum` reports
  only `[propext, Classical.choice, Quot.sound]`.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Pullback of a linear extension along a poset automorphism -/

/-- Pull back a linear extension `L : LinearExt α` along a `≤`-preserving
endo-equivalence `σ : α ≃ α`. The pulled-back extension sends
`x ↦ L.pos (σ x)`. -/
def LinearExt.pullback (L : LinearExt α) {σ : α ≃ α}
    (hσ : ∀ x y : α, x ≤ y → σ x ≤ σ y) : LinearExt α where
  toFun := σ.trans L.toFun
  monotone := fun {x y} hle => L.monotone (hσ x y hle)

lemma LinearExt.pullback_pos (L : LinearExt α) {σ : α ≃ α}
    (hσ : ∀ x y : α, x ≤ y → σ x ≤ σ y) (x : α) :
    (L.pullback hσ).pos x = L.pos (σ x) := rfl

/-- Pullback by an involutive poset automorphism is an involution on
`LinearExt α`. -/
lemma LinearExt.pullback_pullback (L : LinearExt α) {σ : α ≃ α}
    (hσ : ∀ x y : α, x ≤ y → σ x ≤ σ y)
    (hinv : ∀ x, σ (σ x) = x) :
    (L.pullback hσ).pullback hσ = L := by
  apply LinearExt.ext
  apply Equiv.ext
  intro x
  show L.toFun (σ (σ x)) = L.toFun x
  rw [hinv]

namespace Step8

/-! ### §2 — Bipartite swap automorphism -/

private lemma mem_A_or_B_of_cover
    {A B : Finset α} (hCover : A ∪ B = (Finset.univ : Finset α)) (z : α) :
    z ∈ A ∨ z ∈ B := by
  have hu : z ∈ A ∪ B := by rw [hCover]; exact Finset.mem_univ z
  exact Finset.mem_union.mp hu

/-- Evaluate `Equiv.swap u v` at any element as a branching expression. -/
private lemma swap_eval (u v z : α) :
    Equiv.swap u v z = (if z = u then v else if z = v then u else z) := by
  split_ifs with h1 h2
  · rw [h1]; exact Equiv.swap_apply_left u v
  · rw [h2]; exact Equiv.swap_apply_right u v
  · exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- In a bipartite height-2 poset `α = A ⊔ B` (antichains, covering `α`,
every comparability directed `A < B`), swapping two same-layer elements
preserves `≤`. -/
private lemma swap_preserves_le
    {A B : Finset α}
    (hA_anti : IsAntichain (· ≤ ·) (A : Set α))
    (hB_anti : IsAntichain (· ≤ ·) (B : Set α))
    (hCover : A ∪ B = (Finset.univ : Finset α))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    {u v : α} (huv : u ≠ v)
    (hSame : (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (x y : α) (hxy : x ≤ y) :
    Equiv.swap u v x ≤ Equiv.swap u v y := by
  have hmem := mem_A_or_B_of_cover hCover
  -- Evaluate both sides of the goal via `swap_eval`.
  rw [swap_eval u v x, swap_eval u v y]
  -- Split on the four boolean outcomes.
  by_cases hxu : x = u
  · rw [if_pos hxu]
    by_cases hyu : y = u
    · rw [if_pos hyu]
    rw [if_neg hyu]
    by_cases hyv : y = v
    · rw [if_pos hyv]
      -- hxy : x ≤ y, with x = u, y = v: u ≤ v. Same-layer antichain ⟹ contradiction.
      exfalso
      have huv_le : u ≤ v := hxu ▸ hyv ▸ hxy
      rcases hSame with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact hA_anti hu hv huv huv_le
      · exact hB_anti hu hv huv huv_le
    rw [if_neg hyv]
    -- Goal: v ≤ y. Given hxy : x ≤ y with x = u, y ∉ {u, v}.
    have hu_y : u ≤ y := hxu ▸ hxy
    rcases hSame with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases hmem y with hyA | hyB
      · exact absurd hu_y (hA_anti hu hyA (Ne.symm hyu))
      · exact hAB v hv y hyB
    · rcases hmem y with hyA | hyB
      · exact absurd (le_antisymm (hAB y hyA u hu) hu_y) hyu
      · exact absurd hu_y (hB_anti hu hyB (Ne.symm hyu))
  rw [if_neg hxu]
  by_cases hxv : x = v
  · rw [if_pos hxv]
    by_cases hyu : y = u
    · rw [if_pos hyu]
      -- hxy : x ≤ y with x = v, y = u: v ≤ u. Same-layer antichain ⟹ contradiction.
      exfalso
      have hvu_le : v ≤ u := hxv ▸ hyu ▸ hxy
      rcases hSame with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact hA_anti hv hu (Ne.symm huv) hvu_le
      · exact hB_anti hv hu (Ne.symm huv) hvu_le
    rw [if_neg hyu]
    by_cases hyv : y = v
    · rw [if_pos hyv]
    rw [if_neg hyv]
    -- Goal: u ≤ y. Given hxy with x = v, y ∉ {u, v}.
    have hv_y : v ≤ y := hxv ▸ hxy
    rcases hSame with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases hmem y with hyA | hyB
      · exact absurd hv_y (hA_anti hv hyA (Ne.symm hyv))
      · exact hAB u hu y hyB
    · rcases hmem y with hyA | hyB
      · exact absurd (le_antisymm (hAB y hyA v hv) hv_y) hyv
      · exact absurd hv_y (hB_anti hv hyB (Ne.symm hyv))
  rw [if_neg hxv]
  -- x ∉ {u, v}.
  by_cases hyu : y = u
  · rw [if_pos hyu]
    -- Goal: x ≤ v. Given hxy with x ∉ {u, v}, y = u.
    have hx_u : x ≤ u := hyu ▸ hxy
    rcases hSame with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases hmem x with hxA | hxB
      · exact absurd hx_u (hA_anti hxA hu hxu)
      · exact absurd (le_antisymm hx_u (hAB u hu x hxB)) hxu
    · rcases hmem x with hxA | hxB
      · exact hAB x hxA v hv
      · exact absurd hx_u (hB_anti hxB hu hxu)
  rw [if_neg hyu]
  by_cases hyv : y = v
  · rw [if_pos hyv]
    -- Goal: x ≤ u. Given hxy with x ∉ {u, v}, y = v.
    have hx_v : x ≤ v := hyv ▸ hxy
    rcases hSame with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases hmem x with hxA | hxB
      · exact absurd hx_v (hA_anti hxA hv hxv)
      · exact absurd (le_antisymm hx_v (hAB v hv x hxB)) hxv
    · rcases hmem x with hxA | hxB
      · exact hAB x hxA u hu
      · exact absurd hx_v (hB_anti hxB hv hxv)
  rw [if_neg hyv]
  -- x, y both ∉ {u, v}.
  exact hxy

/-! ### §3 — Filter cardinality via the swap involution -/

/-- The swap involution on `LinearExt α` exchanges the ordered filters
`{L : L.lt u v}` and `{L : L.lt v u}`, so the two have equal cardinality. -/
private lemma filter_lt_card_eq_of_same_layer
    {A B : Finset α}
    (hA_anti : IsAntichain (· ≤ ·) (A : Set α))
    (hB_anti : IsAntichain (· ≤ ·) (B : Set α))
    (hCover : A ∪ B = (Finset.univ : Finset α))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    {u v : α} (huv : u ≠ v)
    (hSame : (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    ((Finset.univ : Finset (LinearExt α)).filter
        (fun L => L.lt u v)).card =
      ((Finset.univ : Finset (LinearExt α)).filter
        (fun L => L.lt v u)).card := by
  classical
  have hσ :=
    swap_preserves_le hA_anti hB_anti hCover hAB huv hSame
  have hinv : ∀ x : α, (Equiv.swap u v) ((Equiv.swap u v) x) = x :=
    fun x => Equiv.swap_apply_self u v x
  refine Finset.card_bij (fun L _ => L.pullback hσ) ?_ ?_ ?_
  · intro L hL
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
    show (L.pullback hσ).pos v < (L.pullback hσ).pos u
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
    show (L.pullback hσ).pos u < (L.pullback hσ).pos v
    rw [LinearExt.pullback_pos, LinearExt.pullback_pos,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact hL

/-! ### §4 — Same-layer pair has probability `1/2` -/

/-- For a bipartite height-2 poset with an incomparable same-layer pair
`(u, v)`, the linear-extension probability `Pr[u <_L v] = 1/2`. -/
private lemma probLT_eq_half_of_same_layer
    {A B : Finset α}
    (hA_anti : IsAntichain (· ≤ ·) (A : Set α))
    (hB_anti : IsAntichain (· ≤ ·) (B : Set α))
    (hCover : A ∪ B = (Finset.univ : Finset α))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    {u v : α} (huv : u ≠ v)
    (hSame : (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    probLT u v = 1 / 2 := by
  have hcard :=
    filter_lt_card_eq_of_same_layer hA_anti hB_anti hCover hAB huv hSame
  have hsum := probLT_add_probLT_of_ne huv
  -- `probLT u v = probLT v u` follows from cardinality equality.
  have heq : probLT u v = probLT v u := by
    unfold probLT
    have : ((((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt u v)).card : ℚ)) =
            ((((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt v u)).card : ℚ)) := by
      exact_mod_cast hcard
    rw [this]
  linarith

/-! ### §5 — Main theorem: discharges `fkg_case_output` -/

/-- **`prop:bipartite-balanced` — discharged by finite enumeration**
(`step8.tex:2824-2940`, `step8.tex:2942-2955`).

For a bipartite height-2 poset `α = A ⊔ B` with `A, B` disjoint
antichains of size `≤ 3`, covering `α`, every comparability directed
`A < B`, and at least one incomparable pair, `α` has a balanced pair.

**Proof.** The incomparable pair `(u, v)` is within-layer (cross-layer
pairs are forced comparable by `hAB`); hence `Equiv.swap u v` is a poset
automorphism of `α`, and pullback along this swap is an involution on
`LinearExt α` exchanging `{L : u <_L v}` and `{L : v <_L u}`. Combined
with `Pr[u<v] + Pr[v<u] = 1`, we get `Pr[u<v] = 1/2 ∈ [1/3, 2/3]`.

The `|A|, |B| ≤ 3` and disjointness hypotheses are retained for
signature-compatibility with the original axiom `fkg_case_output`; the
symmetry argument above does not use them. -/
theorem bipartite_balanced_enum
    (A B : Finset α)
    (hA_anti : IsAntichain (· ≤ ·) (A : Set α))
    (hB_anti : IsAntichain (· ≤ ·) (B : Set α))
    (_hA_size : A.card ≤ 3) (_hB_size : B.card ≤ 3)
    (_hDisj : Disjoint A B)
    (hCover : A ∪ B = (Finset.univ : Finset α))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (hIncomp : ∃ u v : α, u ∥ v) :
    HasBalancedPair α := by
  classical
  obtain ⟨u, v, huv⟩ := hIncomp
  have hmem := mem_A_or_B_of_cover hCover
  have hSame : (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
    rcases hmem u with hu | hu
    · rcases hmem v with hv | hv
      · exact Or.inl ⟨hu, hv⟩
      · exact absurd (hAB u hu v hv) huv.1
    · rcases hmem v with hv | hv
      · exact absurd (hAB v hv u hu) huv.2
      · exact Or.inr ⟨hu, hv⟩
  have hne : u ≠ v := fun h => huv.1 (h ▸ le_refl u)
  have hhalf :=
    probLT_eq_half_of_same_layer hA_anti hB_anti hCover hAB hne hSame
  refine ⟨u, v, huv, ?_, ?_⟩
  · rw [hhalf]; norm_num
  · rw [hhalf]; norm_num

end Step8
end OneThird
