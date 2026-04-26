/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.BipartiteEnum
import OneThird.Step8.LayeredReduction
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Within-band `Pr ≤ 2/3` upper bound from bipartite enumeration
(`mg-A8` sub-split A8-S2-bipartite-bound, `mg-ed4d`)

This file lifts the extremal `Pr ≤ 2/3` upper bound of
`prop:bipartite-balanced` Case 2 (`step8.tex:2916-2940`) — already
discharged in the K=2 bipartite enumeration
`OneThird.Step8.BipartiteEnum.bipartite_balanced_enum` — to a
within-band statement on `LayeredDecomposition`.

## Summary

When `L : LayeredDecomposition α` is *bipartite* — depth `K = 2` and
interaction width `w = 0` — the (L1) and (L2) axioms collapse the
ambient poset to the bipartite shape `α = bandSet 1 ∪ bandSet 2`,
with both bands antichains, disjoint, and every band-1 element
strictly below every band-2 element. This is exactly the hypothesis
profile of `bipartite_balanced_enum`.

* `bandSet_one_isAntichain`, `bandSet_two_isAntichain`,
  `bandSets_disjoint`, `bandSets_cover_K2`,
  `bandSet_one_le_bandSet_two_of_w0` — the bipartite hypotheses
  derived from `LayeredDecomposition`.
* `hasBalancedPair_of_K2_w0_incomp` — every depth-2, width-0
  layered decomposition with an incomparable pair has a balanced
  pair (direct application of `bipartite_balanced_enum`).
* `within_band_same_layer` — within-band pairs in a depth-2
  layered decomposition fall in the same `bandSet`, packaging the
  hypothesis required by the bipartite enumeration's same-layer
  lemma.
* `probLT_eq_half_of_within_band_K2_w0` — the within-band
  probability identity `probLT u v = 1/2` for any incomparable
  within-band pair in a depth-2, width-0 layered decomposition.
* `probLT_le_two_thirds_of_within_band_K2_w0` — **the headline
  upper bound:** `probLT u v ≤ 2/3` for any incomparable within-band
  pair in a depth-2, width-0 `LayeredDecomposition`.
* `probLT_ge_one_third_of_within_band_K2_w0` — the symmetric
  `1/3 ≤ probLT u v` lower bound (the K=2 specialisation of
  A8-S2-cont's deferred FKG `Pr ≥ 1/2` bound).
* `isBalanced_of_within_band_K2_w0` — full `IsBalanced` packaging.

This is the upper-bound counterpart to A8-S2-cont's deferred
`Pr_Q[a <_L a'] ≥ 1/2` lower bound (`step8.tex:3001-3032`); the two
together would give the full Case 2 within-band balance bound. The
lower bound depends on the cross-poset coupling infrastructure
described in `docs/a8-s2-status.md`; the upper bound discharged here
uses only the existing within-poset enumeration of
`bipartite_balanced_enum`.

## Why bipartite (K=2, w=0) is the right scope

The (L2) axiom `band x + w < band y → x < y` with `K = 2` and `w = 0`
forces every band-1 element strictly below every band-2 element.
With `K = 2`, the only band indices in use are `1` and `2` (by
`band_pos` / `band_le`). Together with `band_size ≤ 3` and
`band_antichain`, this matches verbatim the bipartite hypotheses of
`bipartite_balanced_enum`. Higher `w` values (with `K = 2`) drop the
forced-comparability axiom into vacuous form (`1 + w < 2` only at
`w = 0`), so the bipartite content is genuinely tied to `w = 0` in
this depth-2 specialisation.

## Re-use by A8-S2 / A8-S3

The headline `probLT_le_two_thirds_of_within_band_K2_w0` is the
upper-bound half of the Case 2 sub-claim of
`prop:in-situ-balanced` for the bipartite (K=2) base case. The
within-band-pair shape `L.band u = L.band v` matches `Case2Witness`
(`Case3Dispatch.lean:156`) and `StrictCase2Witness`
(`Case2FKG.lean:217`), making this lemma directly composable with
the deferred FKG lower-bound discharge once A8-S2-cont lands.

`#print axioms` on the new theorems reports only the mathlib trio
`[propext, Classical.choice, Quot.sound]` — no new axioms, no
sorries.

## References

* `step8.tex` `prop:bipartite-balanced` Case 2, extremal upper
  bound (`step8.tex:2916-2940`); finite-enumeration remark
  (`step8.tex:2942-2955`).
* `lean/OneThird/Step8/BipartiteEnum.lean` — K=2 bipartite
  enumeration (`bipartite_balanced_enum`, `mg-68af`) and the
  `probLT_eq_half_of_same_layer` building block exposed for this
  lift.
* `lean/OneThird/Step8/LayeredReduction.lean` —
  `LayeredDecomposition` structure (`def:layered`, `step8.tex:1883`).
* `lean/OneThird/Step8/Case2FKG.lean` — A8-S2's `Case2Witness` and
  `StrictCase2Witness` predicates (the within-band pair targets of
  the deferred FKG lower bound).
* `docs/a8-s2-status.md` — A8-S2 status report and recommended
  sub-split.
-/

namespace OneThird
namespace Step8
namespace InSitu

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### §1 — Bipartite hypotheses from a depth-2, width-0 layered decomposition

A `LayeredDecomposition L` with `L.K = 2` and `L.w = 0` collapses by
(L1) and (L2) into the bipartite shape `α = bandSet 1 ∪ bandSet 2`,
matching the hypothesis profile of `bipartite_balanced_enum`. -/

/-- Under `L.K = 2`, every element's band is either `1` or `2`. -/
lemma band_in_one_or_two_of_K2 (L : LayeredDecomposition α)
    (hK : L.K = 2) (x : α) :
    L.band x = 1 ∨ L.band x = 2 := by
  have hp := L.band_pos x
  have hle := L.band_le x
  rw [hK] at hle
  rcases Nat.lt_or_ge (L.band x) 2 with h | h
  · left; omega
  · right; omega

/-- `bandSet 1` is an antichain. -/
lemma bandSet_one_isAntichain (L : LayeredDecomposition α) :
    IsAntichain (· ≤ ·) ((L.bandSet 1) : Set α) := by
  unfold LayeredDecomposition.bandSet
  exact L.band_antichain 1

/-- `bandSet 2` is an antichain. -/
lemma bandSet_two_isAntichain (L : LayeredDecomposition α) :
    IsAntichain (· ≤ ·) ((L.bandSet 2) : Set α) := by
  unfold LayeredDecomposition.bandSet
  exact L.band_antichain 2

/-- `bandSet 1` has size at most `3` (specialisation of `band_size`). -/
lemma bandSet_one_card_le (L : LayeredDecomposition α) :
    (L.bandSet 1).card ≤ 3 := L.band_size 1

/-- `bandSet 2` has size at most `3`. -/
lemma bandSet_two_card_le (L : LayeredDecomposition α) :
    (L.bandSet 2).card ≤ 3 := L.band_size 2

/-- The two bands of any layered decomposition are disjoint. -/
lemma bandSets_disjoint (L : LayeredDecomposition α) :
    Disjoint (L.bandSet 1) (L.bandSet 2) := by
  unfold LayeredDecomposition.bandSet
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
  rw [hx1] at hx2
  exact absurd hx2 (by decide)

/-- Under `L.K = 2`, the union of the two bands covers `α`. -/
lemma bandSets_cover_K2 (L : LayeredDecomposition α) (hK : L.K = 2) :
    L.bandSet 1 ∪ L.bandSet 2 = (Finset.univ : Finset α) := by
  apply Finset.eq_univ_of_forall
  intro x
  simp only [LayeredDecomposition.bandSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact band_in_one_or_two_of_K2 L hK x

/-- Under `L.w = 0`, every band-1 element is strictly below every
band-2 element (specialisation of `forced_lt`). -/
lemma bandSet_one_lt_bandSet_two_of_w0
    (L : LayeredDecomposition α) (hw : L.w = 0)
    {a b : α} (ha : a ∈ L.bandSet 1) (hb : b ∈ L.bandSet 2) :
    a < b := by
  rw [LayeredDecomposition.mem_bandSet] at ha hb
  apply L.forced_lt
  rw [ha, hb, hw]
  decide

/-- Hypothesis-form of `bandSet_one_lt_bandSet_two_of_w0` matching
the `hAB` signature of `bipartite_balanced_enum`. -/
lemma bandSet_one_le_bandSet_two_of_w0
    (L : LayeredDecomposition α) (hw : L.w = 0) :
    ∀ a ∈ L.bandSet 1, ∀ b ∈ L.bandSet 2, a ≤ b :=
  fun _ ha _ hb => (bandSet_one_lt_bandSet_two_of_w0 L hw ha hb).le

/-! ### §2 — `bipartite_balanced_enum` lift

Wraps `bipartite_balanced_enum` with the bipartite hypotheses derived
from a depth-2, width-0 `LayeredDecomposition`. -/

/-- **Within-band balanced-pair lift** (K=2, w=0).

Every depth-2, width-0 `LayeredDecomposition` with at least one
incomparable pair admits a balanced pair, by direct application of
`bipartite_balanced_enum`. -/
theorem hasBalancedPair_of_K2_w0_incomp
    (L : LayeredDecomposition α) (hK : L.K = 2) (hw : L.w = 0)
    (hIncomp : ∃ u v : α, u ∥ v) :
    HasBalancedPair α :=
  bipartite_balanced_enum (L.bandSet 1) (L.bandSet 2)
    (bandSet_one_isAntichain L) (bandSet_two_isAntichain L)
    (bandSet_one_card_le L) (bandSet_two_card_le L)
    (bandSets_disjoint L) (bandSets_cover_K2 L hK)
    (bandSet_one_le_bandSet_two_of_w0 L hw) hIncomp

/-! ### §3 — Within-band pairs lie in a single band

A within-band pair `(u, v)` of a depth-2 `LayeredDecomposition` (i.e.
`L.band u = L.band v`) lies entirely inside `bandSet 1` or entirely
inside `bandSet 2`. This is the `hSame` hypothesis of the bipartite
same-layer lemma. -/

/-- A within-band pair in a depth-2 `LayeredDecomposition` is
same-layer in the bipartite sense: both elements live in `bandSet 1`
or both in `bandSet 2`. -/
lemma within_band_same_layer
    (L : LayeredDecomposition α) (hK : L.K = 2)
    {u v : α} (hband : L.band u = L.band v) :
    (u ∈ L.bandSet 1 ∧ v ∈ L.bandSet 1) ∨
      (u ∈ L.bandSet 2 ∧ v ∈ L.bandSet 2) := by
  rcases band_in_one_or_two_of_K2 L hK u with hu | hu
  · refine Or.inl ⟨?_, ?_⟩
    · simpa [LayeredDecomposition.mem_bandSet] using hu
    · simpa [LayeredDecomposition.mem_bandSet] using hband.symm.trans hu
  · refine Or.inr ⟨?_, ?_⟩
    · simpa [LayeredDecomposition.mem_bandSet] using hu
    · simpa [LayeredDecomposition.mem_bandSet] using hband.symm.trans hu

/-! ### §4 — Within-band `probLT = 1/2` for K=2, w=0 layered

Direct lift of `BipartiteEnum.probLT_eq_half_of_same_layer` to the
within-band shape `L.band u = L.band v`. Together with `huv : u ≠ v`,
this gives `probLT u v = 1/2`, from which both the `≤ 2/3` and
`≥ 1/3` bounds follow immediately. -/

/-- **Within-band probability identity** (K=2, w=0).

For any depth-2, width-0 `LayeredDecomposition L` and any distinct
within-band pair `(u, v)` (i.e. `L.band u = L.band v`),
`probLT u v = 1/2`. -/
theorem probLT_eq_half_of_within_band_K2_w0
    (L : LayeredDecomposition α) (hK : L.K = 2) (hw : L.w = 0)
    {u v : α} (huv : u ≠ v) (hband : L.band u = L.band v) :
    probLT u v = 1 / 2 :=
  probLT_eq_half_of_same_layer
    (bandSet_one_isAntichain L) (bandSet_two_isAntichain L)
    (bandSets_cover_K2 L hK)
    (bandSet_one_le_bandSet_two_of_w0 L hw)
    huv (within_band_same_layer L hK hband)

/-! ### §5 — The headline `Pr ≤ 2/3` within-band upper bound -/

/-- **Within-band `Pr ≤ 2/3`** (K=2, w=0) — the headline upper-bound
lift (`step8.tex:2916-2940`).

For any depth-2, width-0 `LayeredDecomposition L` and any distinct
within-band pair `(u, v)`, `probLT u v ≤ 2/3`. Immediate corollary of
`probLT_eq_half_of_within_band_K2_w0`. -/
theorem probLT_le_two_thirds_of_within_band_K2_w0
    (L : LayeredDecomposition α) (hK : L.K = 2) (hw : L.w = 0)
    {u v : α} (huv : u ≠ v) (hband : L.band u = L.band v) :
    probLT u v ≤ 2 / 3 := by
  rw [probLT_eq_half_of_within_band_K2_w0 L hK hw huv hband]
  norm_num

/-- **Within-band `Pr ≥ 1/3`** (K=2, w=0) — the symmetric lower
bound (the K=2 specialisation of A8-S2-cont's deferred FKG argument). -/
theorem probLT_ge_one_third_of_within_band_K2_w0
    (L : LayeredDecomposition α) (hK : L.K = 2) (hw : L.w = 0)
    {u v : α} (huv : u ≠ v) (hband : L.band u = L.band v) :
    (1 : ℚ) / 3 ≤ probLT u v := by
  rw [probLT_eq_half_of_within_band_K2_w0 L hK hw huv hband]
  norm_num

/-! ### §6 — Full `IsBalanced` packaging -/

/-- **Within-band `IsBalanced`** (K=2, w=0).

Combines the upper and lower bounds: for any distinct within-band
pair `(u, v)` in a depth-2, width-0 `LayeredDecomposition L`,
`IsBalanced u v` holds. -/
theorem isBalanced_of_within_band_K2_w0
    (L : LayeredDecomposition α) (hK : L.K = 2) (hw : L.w = 0)
    {u v : α} (huv : u ≠ v) (hband : L.band u = L.band v) :
    IsBalanced u v :=
  ⟨probLT_ge_one_third_of_within_band_K2_w0 L hK hw huv hband,
   probLT_le_two_thirds_of_within_band_K2_w0 L hK hw huv hband⟩

/-! ### §7 — Composed `HasBalancedPair α` from a within-band pair -/

/-- Within-band distinct elements of a depth-2 `LayeredDecomposition`
are incomparable (specialisation of `band_antichain`). Re-stated here
as a self-contained corollary; analogous to
`Case2FKG.incomp_of_within_band` for general `L`. -/
private lemma incomp_of_within_band_K2
    (L : LayeredDecomposition α)
    {u v : α} (huv : u ≠ v) (hband : L.band u = L.band v) :
    u ∥ v := by
  have hA := L.band_antichain (L.band u)
  have hu_mem :
      u ∈ ((((Finset.univ : Finset α).filter
              (fun x => L.band x = L.band u)) : Set α)) := by
    simp
  have hv_mem :
      v ∈ ((((Finset.univ : Finset α).filter
              (fun x => L.band x = L.band u)) : Set α)) := by
    simp [hband.symm]
  refine ⟨?_, ?_⟩
  · intro hle
    exact hA hu_mem hv_mem huv hle
  · intro hle
    exact hA hv_mem hu_mem (Ne.symm huv) hle

/-- **`HasBalancedPair α` directly from a within-band distinct pair**
(K=2, w=0).

Existence-form packaging: a depth-2, width-0 `LayeredDecomposition`
with any distinct within-band pair (which is automatically
incomparable) yields a balanced pair via the within-band
`IsBalanced` discharge. -/
theorem hasBalancedPair_of_within_band_K2_w0
    (L : LayeredDecomposition α) (hK : L.K = 2) (hw : L.w = 0)
    {u v : α} (huv : u ≠ v) (hband : L.band u = L.band v) :
    HasBalancedPair α :=
  ⟨u, v, incomp_of_within_band_K2 L huv hband,
    isBalanced_of_within_band_K2_w0 L hK hw huv hband⟩

end InSitu
end Step8
end OneThird
