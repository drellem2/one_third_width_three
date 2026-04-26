/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Poset
import OneThird.Step8.BipartiteEnum
import OneThird.Step8.LayerOrdinal
import OneThird.Step8.LayeredBalanced
import OneThird.Step8.LayeredReduction

/-!
# Step 8 — A5-G3e: F3 strong-induction proof of `Case3Witness`
(`mg-b329`)

This file packages the F3 strong-induction proof of the outer
`Step8.Case3Witness` ∀-family (`Step8.LayeredBalanced.lean:419`) into
the form needed by Path C of `docs/gap-analysis.md`: from a single
F3-shaped step function `hStep` (closing the K ≥ 2 leaf, with the
strong-induction hypothesis available for Case B / Case C1 descent),
produce a proof of `Case3Witness`.

## Structure

The K = 1 case (single antichain on 2 or 3 elements) is closed inline
by `bipartite_balanced_enum` (from `BipartiteEnum.lean`); the K ≥ 2
case is dispatched to the caller-supplied `hStep` together with the
F3 induction hypothesis for smaller types. The induction is on
`Fintype.card β`, generalised over `β` via `Nat.strong_induction_on`.

This matches the F3 framework of
`Step8.hasBalancedPair_of_layered_strongInduction`
(`LayerOrdinal.lean:370`), but adds explicit width-3 threading through
the IH (so that downstream `hStep` discharges have access to
`HasWidthAtMost β 3` on the recursive sub-poset, which the bare F3
framework drops).

## What this file delivers

* `Step8.Case3WitnessHStep` — the F3-shaped step-function predicate
  (with width-3 threading) that closes the K ≥ 2 case of the
  `Case3Witness` ∀-family.

* `Step8.case3Witness_of_hStep` — the F3-strong-induction proof:
  given `hStep : Case3WitnessHStep`, conclude `Case3Witness`.

The remaining proof obligations live inside `hStep`:

1. **Case B** (`L` reducible at some band index `k`): use the
   strong-induction IH on a non-chain side of the
   `OrdinalDecompOfReducible` decomposition.
2. **Case C** (`L` irreducible, `K ≥ 2`): the leaf case
   `prop:in-situ-balanced`. Composes:
   * G3d's `bounded_irreducible_balanced_inScope`
     (`Step8.BoundedIrreducibleBalancedInScope.lean`) for the
     `InCase3Scope` parameter range.
   * The structural argument from `Case3Dispatch.lean` /
     `Case2FKG.lean` / `Case3Residual.lean` for the
     `¬ InCase3Scope` parameter range, ending in the
     `case3Witness_hasBalancedPair_outOfScope` axiom.

Both branches still depend on caller-side closures that are *not*
fully discharged in this file: G3c-followup (`mg-7268-followup`) for
the `enumPredAtMaskOf_eq_predMaskOf` / `enumFreeUVOf_eq_freeUVOf`
identities feeding `bounded_irreducible_balanced_inScope`, and a
`StrictCase2Witness L → HasBalancedPair α` discharge for the residual
case-2 sub-branch flagged by `case2Witness_balanced_or_strict`
(`Case2FKG.lean:226`).

## Why F3 + width-3 threading

The bare F3 `Step8.hasBalancedPair_of_layered_strongInduction` does
*not* thread `HasWidthAtMost β 3` through the IH: its hypothesis
profile lacks the width-3 hypothesis altogether. Width-3 is essential
for the C2-leaf in-scope discharge (the `case3_certificate`
enumeration is hardwired to bands of size `≤ 3`), so the F3 form here
explicitly threads `HasWidthAtMost β 3` into the IH.

This keeps the F3 framework reusable for non-width-3 variants while
specialising it for the `Case3Witness` use case in this file.

## References

* `step8.tex` `lem:layered-balanced` (`step8.tex:2336-3237`),
  Case-A (`3080-3082`), Case-B (`3084-3094`), Case-C
  (`3096-3122`).
* `Step8.LayeredBalanced.lean:419` — `Case3Witness` def.
* `Step8.LayerOrdinal.lean:370` —
  `hasBalancedPair_of_layered_strongInduction` (bare F3).
* `docs/gap-analysis.md` Path C — Case3Witness elimination plan.
* `docs/a5-glue-status.md` §3 A5-G3 — Path C deliverable scope.
-/

namespace OneThird
namespace Step8

set_option linter.unusedSectionVars false

/-! ### §1 — F3-shaped step-function predicate -/

/-- **F3-shaped step function for `Case3Witness`** with width-3
threading.

Closes the K ≥ 2 case of the `Case3Witness` ∀-family for an arbitrary
universe-`u` width-3 layered β with `2 ≤ |β|`, using the F3
strong-induction hypothesis on smaller types (the `ih` parameter).

The `2 ≤ L.K` hypothesis matches the K-case dispatch of
`Step8.lem_layered_balanced` (`Step8.LayeredBalanced.lean:489`):
the K = 1 case is closed inline (it does not need `ih`), and only
K ≥ 2 needs the structural / certificate-driven leaf discharge.

Implementations of this predicate compose:
1. `OrdinalDecompOfReducible` + `ih` (Case B reducible).
2. `bounded_irreducible_balanced_inScope` /
   `bounded_irreducible_balanced_hybrid` + `case1_dispatch_inScope` +
   `case2Witness_balanced_or_strict` +
   `case3Witness_hasBalancedPair_outOfScope`
   (Case C irreducible leaf).

The remaining gaps for a no-hypotheses `Case3Witness` proof
(the `mg-7268-followup` G3c-followup obligations and the residual
`StrictCase2Witness` closure) are inside this predicate's scope; this
file does not attempt to discharge them. -/
def Case3WitnessHStep.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
      (L : LayeredDecomposition α),
      HasWidthAtMost α 3 →
      ¬ OneThird.IsChainPoset α →
      2 ≤ Fintype.card α →
      2 ≤ L.K →
      (∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
           (LB : LayeredDecomposition β),
        Fintype.card β < Fintype.card α →
        2 ≤ Fintype.card β →
        ¬ OneThird.IsChainPoset β →
        HasWidthAtMost β 3 →
        OneThird.HasBalancedPair β) →
      OneThird.HasBalancedPair α

/-! ### §2 — F3 strong-induction proof of `Case3Witness` -/

/-- **`Case3Witness` from a width-3 F3-shaped step function.**

Proves the outer `Case3Witness` ∀-family by F3 strong induction on
`Fintype.card β`, with the K = 1 case closed inline via
`bipartite_balanced_enum` and the K ≥ 2 case dispatched to the
parametric `hStep`.

This factorisation is the "F3 strong induction" structure called for
by A5-G3e (`mg-b329`); the parametric `hStep` packages the unproved
"irreducible C2 leaf" content (`prop:in-situ-balanced`) plus any
reducible-leaf reductions that compose with the F3 IH.

**Proof.** Strong induction on `Fintype.card β`, packaged via
`Nat.strong_induction_on` with the type parameter generalised inside
the inductive step. The induction step:

* If `LB.K < 2` (K = 1): the whole ground set collapses to the single
  band `M_1`, which is an antichain by (L1b). Apply
  `bipartite_balanced_enum` with `A := Finset.univ`, `B := ∅`.

* If `LB.K ≥ 2`: invoke `hStep` on the current `β`, threading the
  IH for smaller types as the recursion hypothesis. The IH form is
  the width-3-aware specialisation of
  `Step8.hasBalancedPair_of_layered_strongInduction`. -/
theorem case3Witness_of_hStep.{u} (hStep : Case3WitnessHStep.{u}) :
    Case3Witness.{u} := by
  -- Strong induction on `n = Fintype.card β`, generalising over `β`.
  suffices h : ∀ n : ℕ, ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
      (LB : LayeredDecomposition β),
      Fintype.card β = n →
      HasWidthAtMost β 3 →
      ¬ OneThird.IsChainPoset β →
      2 ≤ Fintype.card β →
      OneThird.HasBalancedPair β by
    intro β _ _ _ LB hW3 hNC h2
    exact h (Fintype.card β) β LB rfl hW3 hNC h2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro β _ _ _ LB hcard hW3 hNC h2
    classical
    -- K = 1 vs K ≥ 2 dispatch (matches `lem_layered_balanced`'s
    -- K-case structure at `LayeredBalanced.lean:489`).
    by_cases hK1 : LB.K < 2
    · -- **Case A (K = 1).** Single antichain on 2 or 3 elements.
      have hK : LB.K ≤ 1 := by omega
      -- Extract incomparable pair from the non-chain hypothesis.
      have hNC' := hNC
      unfold OneThird.IsChainPoset at hNC'
      push_neg at hNC'
      obtain ⟨x, y, hxy, hyx⟩ := hNC'
      have hxy_inc : x ∥ y := ⟨hxy, hyx⟩
      have hband_eq : ∀ z : β, LB.band z = 1 := fun z =>
        le_antisymm (le_trans (LB.band_le z) hK) (LB.band_pos z)
      have hFilter_eq :
          ((Finset.univ : Finset β).filter (fun z => LB.band z = 1)) =
            (Finset.univ : Finset β) :=
        Finset.filter_true_of_mem (fun z _ => hband_eq z)
      have hUniv_anti :
          IsAntichain (· ≤ ·) ((Finset.univ : Finset β) : Set β) := by
        have h := LB.band_antichain 1
        rw [hFilter_eq] at h
        exact h
      have hCard_le : (Finset.univ : Finset β).card ≤ 3 := by
        have h := LB.band_size 1
        rw [hFilter_eq] at h
        exact h
      have hEmpty_anti :
          IsAntichain (· ≤ ·) ((∅ : Finset β) : Set β) := by
        simp only [Finset.coe_empty]
        exact Set.pairwise_empty _
      exact bipartite_balanced_enum (Finset.univ : Finset β) (∅ : Finset β)
        hUniv_anti hEmpty_anti hCard_le (by simp)
        (Finset.disjoint_empty_right _) (Finset.union_empty _)
        (fun _ _ b hb => absurd hb (Finset.notMem_empty b))
        ⟨x, y, hxy_inc⟩
    · push_neg at hK1
      have hK2 : 2 ≤ LB.K := hK1
      -- **Case B / C (K ≥ 2).** Build the width-3-aware IH closure
      -- for `hStep`.
      have ih' : ∀ (γ : Type u) [PartialOrder γ] [Fintype γ] [DecidableEq γ]
          (LC : LayeredDecomposition γ),
          Fintype.card γ < Fintype.card β →
          2 ≤ Fintype.card γ →
          ¬ OneThird.IsChainPoset γ →
          HasWidthAtMost γ 3 →
          OneThird.HasBalancedPair γ := by
        intros γ _ _ _ LC hγLt h2γ hNCγ hW3γ
        -- Lift `hγLt` from `< Fintype.card β` to `< n` via `hcard`.
        rw [hcard] at hγLt
        exact ih (Fintype.card γ) hγLt γ LC rfl hW3γ hNCγ h2γ
      exact hStep β LB hW3 hNC h2 hK2 ih'

end Step8
end OneThird
