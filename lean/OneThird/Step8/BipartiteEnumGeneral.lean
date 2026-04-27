/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.BipartiteEnum
import OneThird.Step8.Case3Struct
import OneThird.Step8.Case3Dispatch
import OneThird.Step8.Case2Rotation
import OneThird.Step8.CompoundMatching
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Generalised bipartite-balanced dispatch (drops `hAB`)
(`docs/path-c-cleanup-roadmap.md` §6a, PATH B step 3)

This file generalises `OneThird.Step8.bipartite_balanced_enum`
(`BipartiteEnum.lean`) to drop its
`hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b` hypothesis. The replacement is a
**three-way dispatch** on excluded middle:

* **Case 1** — ambient profile match: closed inline by
  `Step8.InSitu.hasBalancedPair_of_case1`
  (i.e. `Step8.hasBalancedPair_of_ambient_profile_match`, mg-f92d).
* **Case 2** — within-band `⪯`-comparable pair: closed by
  `Step8.InSitu.case2Witness_balanced_under_FKG` (mg-27c2).
* **Case 3** — neither: the `NoWithinBandPreceq` regime, closed by
  combining `Step8.CompoundMatching.matching_exists_of_K2_irreducible_noWithinBand`
  (mg-c0c7) with `Step8.CompoundSwap.compoundSwap_preserves_le`
  (mg-84f2) via the pullback / linear-extension involution.

The result is the **unconditional** `bipartite_balanced` discharge for
the K=2 + irreducible + `w ≥ 1` + `|α| ≥ 3` regime, modulo the
`Case2FKGSubClaim` bundled hypothesis (which is the same hypothesis
`mg-27c2` already takes — this ticket adds no new axioms or sub-claims).

## Main result

```
theorem bipartite_balanced_enum_general
    (L : LayeredDecomposition α)
    (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hK2 : L.K = 2) (hw : 1 ≤ L.w)
    (hCard : 3 ≤ Fintype.card α)
    (hFKG : Step8.InSitu.Case2FKGSubClaim L) :
    HasBalancedPair α
```

The original `Step8.bipartite_balanced_enum` (with `hAB`) stays in
place; this file only adds the more general entry-point.

## References

* `lean/OneThird/Step8/BipartiteEnum.lean` — the `hAB`-restricted
  predecessor and the `LinearExt.pullback` infrastructure.
* `lean/OneThird/Step8/Case3Struct.lean` (mg-f92d) — Case 1 closure.
* `lean/OneThird/Step8/Case2Rotation.lean` (mg-27c2) — Case 2 closure
  (`case2Witness_balanced_under_FKG`) and `Case2FKGSubClaim` bundle.
* `lean/OneThird/Step8/CompoundSwap.lean` (mg-84f2) — `SameBandPair`,
  `MatchingCompatible`, `compoundSwap`, `compoundSwap_preserves_le`,
  `compoundSwap_involutive`.
* `lean/OneThird/Step8/CompoundMatching.lean` (mg-c0c7) — the
  structural matching lemma `matching_exists_of_K2_irreducible_noWithinBand`
  and the equivalence `noWithinBandPreceq_iff_not_case2Witness`.
* `docs/path-c-cleanup-roadmap.md` §6a (PATH B architectural plan).
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Generic involution-on-`LinearExt` half-probability lemma

For an involutive poset automorphism `σ : α ≃ α` that swaps
`u ↔ v` (i.e. `σ u = v`), the pullback of linear extensions along
`σ` (via `LinearExt.pullback`, `BipartiteEnum.lean`) is an involution
on `LinearExt α` exchanging the filters `{L : L.lt u v}` and
`{L : L.lt v u}`. Combined with `probLT_add_probLT_of_ne`, this gives
`probLT u v = 1/2`.

This generalises the `same-layer` form
`probLT_eq_half_of_same_layer` (`BipartiteEnum.lean`) to any
involutive `≤`-monotone equivalence; in particular, `compoundSwap`
under `MatchingCompatible` instantiates it. -/

/-- **`probLT u v = 1/2` from an involutive `≤`-monotone swap.**

If `σ : α ≃ α` is `≤`-monotone, an involution, and swaps `u ↔ v`
(`σ u = v`), then `probLT u v = 1/2`. The pullback of linear
extensions along `σ` is an involution on `LinearExt α` exchanging the
ordered filters `{L : L.lt u v}` and `{L : L.lt v u}`, so the two
have equal cardinality; combined with `probLT u v + probLT v u = 1`,
this gives `probLT u v = 1/2`. -/
lemma probLT_eq_half_of_swap_aut
    {σ : α ≃ α}
    (hσ : ∀ x y : α, x ≤ y → σ x ≤ σ y)
    (hinv : ∀ x, σ (σ x) = x)
    {u v : α} (huv : u ≠ v) (hσu : σ u = v) :
    probLT u v = 1 / 2 := by
  classical
  -- The involutive partner: `σ v = u`.
  have hσv : σ v = u := by
    have h := hinv u
    rw [hσu] at h
    exact h
  -- Cardinality equality of the two ordered filters via pullback.
  have hcard :
      ((Finset.univ : Finset (LinearExt α)).filter
          (fun L => L.lt u v)).card =
        ((Finset.univ : Finset (LinearExt α)).filter
          (fun L => L.lt v u)).card := by
    refine Finset.card_bij (fun L _ => L.pullback hσ) ?_ ?_ ?_
    · intro L hL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
      show (L.pullback hσ).pos v < (L.pullback hσ).pos u
      rw [LinearExt.pullback_pos, LinearExt.pullback_pos, hσu, hσv]
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
      rw [LinearExt.pullback_pos, LinearExt.pullback_pos, hσu, hσv]
      exact hL
  have hsum := probLT_add_probLT_of_ne huv
  have heq : probLT u v = probLT v u := by
    unfold probLT
    have hcastQ : ((((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt u v)).card : ℚ)) =
            ((((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt v u)).card : ℚ)) := by
      exact_mod_cast hcard
    rw [hcastQ]
  linarith

/-! ### §2 — `HasBalancedPair α` from a `MatchingCompatible` pair -/

/-- **`HasBalancedPair α` from a matching-compatible pair**
(`mg-84f2` consumer; PATH B step 3).

Given a `MatchingCompatible` pair `(P₁, P₂)` of `SameBandPair`s, the
compound swap `σ = (a₁ a₂)(b₁ b₂)` is a `≤`-monotone involutive
equivalence with `σ a₁ = a₂`, so `probLT a₁ a₂ = 1/2 ∈ [1/3, 2/3]`,
witnessing `HasBalancedPair α` on the same-band pair `(a₁, a₂)`. -/
theorem hasBalancedPair_of_matchingCompatible
    (L : LayeredDecomposition α)
    {P₁ P₂ : CompoundSwap.SameBandPair L}
    (h : CompoundSwap.MatchingCompatible L P₁ P₂) :
    HasBalancedPair α := by
  have hσ_le : ∀ x y : α, x ≤ y →
      CompoundSwap.compoundSwap L P₁ P₂ x ≤
        CompoundSwap.compoundSwap L P₁ P₂ y :=
    fun _ _ hxy => CompoundSwap.compoundSwap_preserves_le h hxy
  have hσ_inv : ∀ x,
      CompoundSwap.compoundSwap L P₁ P₂
        (CompoundSwap.compoundSwap L P₁ P₂ x) = x :=
    fun x => CompoundSwap.compoundSwap_involutive h x
  have hσ_a₁ :
      CompoundSwap.compoundSwap L P₁ P₂ P₁.a₁ = P₁.a₂ :=
    CompoundSwap.compoundSwap_a₁ h
  have hIncomp : P₁.a₁ ∥ P₁.a₂ := ⟨P₁.not_le, P₁.not_ge⟩
  have hhalf : probLT P₁.a₁ P₁.a₂ = 1 / 2 :=
    probLT_eq_half_of_swap_aut hσ_le hσ_inv P₁.hne hσ_a₁
  refine ⟨P₁.a₁, P₁.a₂, hIncomp, ?_, ?_⟩
  · rw [hhalf]; norm_num
  · rw [hhalf]; norm_num

/-! ### §3 — Generalised bipartite-balanced dispatch (drops `hAB`) -/

namespace InSitu

set_option linter.unusedVariables false in
/-- **Generalised bipartite-balanced dispatch**
(`docs/path-c-cleanup-roadmap.md` §6a, PATH B step 3).

For a `LayeredDecomposition` with `K = 2`, `LayerOrdinalIrreducible`,
`w ≥ 1`, `|α| ≥ 3`, and the bundled `Case2FKGSubClaim` hypothesis,
`α` has a balanced pair.

**Proof.** Three-way classical case split on the existence of a Case 1
ambient profile-match pair and a Case 2 within-band `⪯`-comparable
pair (identical to `case1_dispatch_inScope`'s shape):

1. **Case 1 branch** (ambient match): closed by
   `hasBalancedPair_of_case1` (the `Step8.hasBalancedPair_of_ambient_profile_match`
   wiring, mg-f92d).
2. **Case 2 branch** (`Case2Witness L`): closed by
   `case2Witness_balanced_under_FKG` (mg-27c2) using the bundled
   `hFKG`.
3. **Case 3 branch** (neither): under `¬ Case2Witness L`, the
   `NoWithinBandPreceq` hypothesis holds (via
   `noWithinBandPreceq_iff_not_case2Witness`); the structural matching
   lemma `matching_exists_of_K2_irreducible_noWithinBand` (mg-c0c7)
   then produces a `MatchingCompatible` pair, and
   `hasBalancedPair_of_matchingCompatible` closes via the compound
   swap's pullback involution on `LinearExt α`.

The Case 1 branch's `(hWidth3, hIrr, hK2, hw, hCard)` hypotheses are
unused (Case 1 closes structurally); the Case 2 branch's are unused
(carried by `case2Witness_balanced_under_FKG`'s hypothesis); the
Case 3 branch consumes them all when invoking the matching lemma. -/
theorem bipartite_balanced_enum_general
    (L : LayeredDecomposition α)
    (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hK2 : L.K = 2) (hw : 1 ≤ L.w)
    (hCard : 3 ≤ Fintype.card α)
    (hFKG : Case2FKGSubClaim L) :
    HasBalancedPair α := by
  classical
  -- Case 1: ambient profile-match pair.
  by_cases h1 : ∃ a a' : α, a ≠ a' ∧
      (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')
  · exact hasBalancedPair_of_case1 h1
  -- Case 2: within-band `⪯`-comparable pair.
  by_cases h2 : Case2Witness L
  · exact case2Witness_balanced_under_FKG L h2 hFKG
  -- Case 3: neither — invoke the compound-automorphism witness.
  have hNo : Step8.CompoundMatching.NoWithinBandPreceq L :=
    (Step8.CompoundMatching.noWithinBandPreceq_iff_not_case2Witness L).mpr h2
  obtain ⟨P₁, P₂, _hBandNe, hMatch⟩ :=
    Step8.CompoundMatching.matching_exists_of_K2_irreducible_noWithinBand
      L hWidth3 hK2 hIrr hw hCard hNo
  exact Step8.hasBalancedPair_of_matchingCompatible L hMatch

end InSitu
end Step8
end OneThird
