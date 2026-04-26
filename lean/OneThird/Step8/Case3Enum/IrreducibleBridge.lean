/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.BoundedIrreducibleBalanced
import Mathlib.Algebra.BigOperators.Fin

/-!
# Step 8 — A5-B1 (foundations): Band-major positional infrastructure
for the `LayerOrdinalIrreducible` ⇒ `Case3Enum.irreducible` bridge
(`mg-46d7`)

The Bool↔Prop bridge for the `irreducible` validity check used by
`Case3Enum.enumPosetsFor` requires significantly more infrastructure
than the original spec anticipated, primarily because the band-major
positional property of `bandMajorEquiv L` was not in tree.

This file provides the foundational pieces:

* §1 — `bandOffset L k = |M_1| + ⋯ + |M_k|`, the cumulative band size.
* §2 — Band-major positional formula: `(bandMajorEquiv L x).val ∈
  [bandOffset L (L.band x − 1), bandOffset L (L.band x))`. This is
  the key positional property that the refactored `bandMajorEquiv`
  (now using `finSigmaFinEquiv` to ensure band-major layout) makes
  available. Closes one direction of the iff
  `bandMajorEquiv L x).val < bandOffset L k ↔ L.band x ≤ k`.
* §3 — Bit-mask reasoning: the `(pred &&& lowerMask) ≠ lowerMask`
  predicate is equivalent to "some bit `< offk` is unset in `pred`".

The remaining pieces (`offsetsOf` characterization, imperative
`forIn`-with-`break` unfolding, and the final bridge theorem) are
deferred to a follow-up work item (the original scope of `mg-46d7`
was ~50-100 LOC; the realized work is ~200 LOC just for foundations).

## References

`step8.tex` Definition `def:layer-reducible` (`step8.tex:2580-2593`);
A1 (`mg-449b`); A2 (`mg-b7b0`).
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! ### §1 — Cumulative band-size: `bandOffset L k` -/

/-- Cumulative band-size: `bandOffset L k = |M_1| + ⋯ + |M_k|`. -/
noncomputable def bandOffset (L : LayeredDecomposition α) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bandOffset L k + bandSize L (k + 1)

@[simp] lemma bandOffset_zero (L : LayeredDecomposition α) :
    bandOffset L 0 = 0 := rfl

@[simp] lemma bandOffset_succ (L : LayeredDecomposition α) (k : ℕ) :
    bandOffset L (k + 1) = bandOffset L k + bandSize L (k + 1) := rfl

lemma bandOffset_eq_finset_sum (L : LayeredDecomposition α) (k : ℕ) :
    bandOffset L k = ∑ i ∈ Finset.range k, bandSize L (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [bandOffset_succ, Finset.sum_range_succ, ih]

lemma bandOffset_eq_fin_sum (L : LayeredDecomposition α) (k : ℕ) :
    bandOffset L k = ∑ i : Fin k, bandSize L (i.val + 1) := by
  rw [bandOffset_eq_finset_sum,
    Fin.sum_univ_eq_sum_range (f := fun i => bandSize L (i + 1))]

lemma bandOffset_K (L : LayeredDecomposition α) :
    bandOffset L L.K = Fintype.card α := by
  rw [bandOffset_eq_finset_sum]; exact sum_bandSize_eq_card L

lemma bandOffset_mono (L : LayeredDecomposition α) :
    Monotone (bandOffset L) := by
  intro a b h
  induction h with
  | refl => exact le_refl _
  | step _ ih =>
    rw [bandOffset_succ]
    exact ih.trans (Nat.le_add_right _ _)

/-! ### §2 — Band-major positional formula -/

/-- Internal helper: factor the position as a `bandOffset` plus
within-band offset, computed through `finSigmaFinEquiv_apply`. -/
private lemma bandMajorEquiv_apply_val_split (L : LayeredDecomposition α) (x : α) :
    (bandMajorEquiv L x).val = bandOffset L (L.band x - 1)
      + ((bandFinEquiv L ((bandFiberEquiv L x).fst.val + 1))
          (bandFiberEquiv L x).snd).val := by
  classical
  unfold bandMajorEquiv
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, finCongr_apply,
    Fin.val_cast]
  rw [finSigmaFinEquiv_apply]
  have hpos := L.band_pos x
  have hsum :
      (∑ k : Fin (bandFiberEquiv L x).fst.val,
          bandSize L
            ((Fin.castLE (bandFiberEquiv L x).fst.isLt.le k).val + 1))
        = bandOffset L (L.band x - 1) := by
    -- First, simplify the Fin.castLE: it preserves .val.
    have hcastLE : (∑ k : Fin (bandFiberEquiv L x).fst.val,
          bandSize L ((Fin.castLE (bandFiberEquiv L x).fst.isLt.le k).val + 1))
        = (∑ k : Fin (bandFiberEquiv L x).fst.val,
          bandSize L (k.val + 1)) := by
      apply Finset.sum_congr rfl
      intros k _
      rfl
    rw [hcastLE]
    -- Now the sum is bandOffset L ((bandFiberEquiv L x).fst.val).
    rw [← bandOffset_eq_fin_sum]
    -- Show (bandFiberEquiv L x).fst.val = L.band x - 1.
    have : (bandFiberEquiv L x).fst.val = L.band x - 1 := by
      rw [bandFiberEquiv_apply, bandIdx_val]
    rw [this]
  rw [hsum]

lemma bandMajorEquiv_apply_val_lt (L : LayeredDecomposition α) (x : α) :
    (bandMajorEquiv L x).val < bandOffset L (L.band x) := by
  classical
  rw [bandMajorEquiv_apply_val_split]
  have hpos := L.band_pos x
  have hindex : (bandFiberEquiv L x).fst.val + 1 = L.band x := by
    rw [bandFiberEquiv_apply, bandIdx_val]; omega
  -- The within-band index has value < bandSize L (...).
  have hsnd_lt : ((bandFinEquiv L ((bandFiberEquiv L x).fst.val + 1))
        (bandFiberEquiv L x).snd).val
      < bandSize L ((bandFiberEquiv L x).fst.val + 1) :=
    ((bandFinEquiv L ((bandFiberEquiv L x).fst.val + 1))
        (bandFiberEquiv L x).snd).isLt
  -- Lift to bandSize L (L.band x) via congrArg on hindex.
  have hsnd_lt' : ((bandFinEquiv L ((bandFiberEquiv L x).fst.val + 1))
        (bandFiberEquiv L x).snd).val
      < bandSize L (L.band x) :=
    hsnd_lt.trans_eq (congrArg (bandSize L) hindex)
  have heq : bandOffset L (L.band x)
      = bandOffset L (L.band x - 1) + bandSize L (L.band x) := by
    have hb : L.band x = (L.band x - 1) + 1 := by omega
    conv_lhs => rw [hb]
    rw [bandOffset_succ]
    have : L.band x - 1 + 1 = L.band x := by omega
    rw [this]
  rw [heq]; omega

lemma bandOffset_le_bandMajorEquiv_apply_val
    (L : LayeredDecomposition α) (x : α) :
    bandOffset L (L.band x - 1) ≤ (bandMajorEquiv L x).val := by
  rw [bandMajorEquiv_apply_val_split]; exact Nat.le_add_right _ _

/-- **Position-vs-band iff** (key band-major property of
`bandMajorEquiv`). For any `x : α` and band-cut `k`, the band-major
position of `x` lies below `bandOffset L k` iff `x` belongs to a band
`≤ k`. This is the foundation for translating `LayerOrdinalIrreducible
L` into bitmask-positional terms. -/
lemma bandMajorEquiv_val_lt_bandOffset_iff
    (L : LayeredDecomposition α) (x : α) (k : ℕ) :
    (bandMajorEquiv L x).val < bandOffset L k ↔ L.band x ≤ k := by
  refine ⟨?_, ?_⟩
  · intro hlt
    by_contra hgt
    push Not at hgt
    have h1 : bandOffset L k ≤ bandOffset L (L.band x - 1) :=
      bandOffset_mono L (by omega)
    have h2 := bandOffset_le_bandMajorEquiv_apply_val L x
    omega
  · intro hle
    have h1 := bandMajorEquiv_apply_val_lt L x
    have h2 : bandOffset L (L.band x) ≤ bandOffset L k := bandOffset_mono L hle
    omega

/-- Band-major position bound: every element's image under
`bandMajorEquiv` lies in the cardinality range. -/
lemma bandMajorEquiv_apply_val_lt_card
    (L : LayeredDecomposition α) (x : α) :
    (bandMajorEquiv L x).val < Fintype.card α := (bandMajorEquiv L x).isLt

/-- For elements in upper bands (`L.band x > k`), the position is at
least `bandOffset L k`. -/
lemma bandOffset_le_bandMajorEquiv_apply_val_of_lt
    (L : LayeredDecomposition α) (x : α) (k : ℕ) (hk : k < L.band x) :
    bandOffset L k ≤ (bandMajorEquiv L x).val := by
  have h1 : bandOffset L k ≤ bandOffset L (L.band x - 1) :=
    bandOffset_mono L (by omega)
  have h2 := bandOffset_le_bandMajorEquiv_apply_val L x
  omega

/-! ### §3 — Bit-mask reasoning -/

/-- The "lower-mask" predicate `pred &&& ((1 <<< offk) - 1) =
(1 <<< offk) - 1` (used by `Case3Enum.irreducible`'s inner check) holds
iff every bit in positions `< offk` is set in `pred`. -/
lemma and_lowerMask_eq_iff_all_bits (pred offk : ℕ) :
    pred &&& ((1 <<< offk) - 1) = (1 <<< offk) - 1 ↔
      ∀ u, u < offk → Nat.testBit pred u = true := by
  refine ⟨fun h u hu => ?_, fun h => Nat.eq_of_testBit_eq fun u => ?_⟩
  · -- Forward direction.
    have hbit : Nat.testBit (pred &&& (1 <<< offk - 1)) u
        = Nat.testBit ((1 <<< offk) - 1) u := by rw [h]
    rw [Nat.testBit_and] at hbit
    have hmask : Nat.testBit ((1 <<< offk) - 1) u = true := by
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true hu]
    rw [hmask, Bool.and_true] at hbit
    exact hbit
  · -- Backward direction (testBit equality).
    rw [Nat.testBit_and]
    by_cases hu : u < offk
    · have hmask : Nat.testBit ((1 <<< offk) - 1) u = true := by
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true hu]
      rw [hmask, Bool.and_true]
      exact h u hu
    · have hmask : Nat.testBit ((1 <<< offk) - 1) u = false := by
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hu
      rw [hmask, Bool.and_false]

/-- The complement: `(pred &&& lowerMask) ≠ lowerMask` is the
inner-check trigger of `Case3Enum.irreducible`'s inner for-loop. It
holds iff some bit `u < offk` is *not* set in `pred`. -/
lemma and_lowerMask_ne_iff_some_bit_unset (pred offk : ℕ) :
    pred &&& ((1 <<< offk) - 1) ≠ (1 <<< offk) - 1 ↔
      ∃ u, u < offk ∧ Nat.testBit pred u = false := by
  rw [Ne, and_lowerMask_eq_iff_all_bits]
  push Not
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu, hbit⟩
    refine ⟨u, hu, ?_⟩
    rcases hcase : Nat.testBit pred u with _ | _
    · rfl
    · exact absurd hcase hbit
  · rintro ⟨u, hu, hbit⟩
    exact ⟨u, hu, by rw [hbit]; decide⟩

/-! ### §4 — Layer-ordinal-irreducibility translates to bitmask
positions

The Prop-level `LayerOrdinalIrreducible L` provides, for each `k ∈
[1, L.K)`, a pair `(u, v)` of cross-cut elements with `¬ (u < v)`.
Through `bandMajorEquiv` and the band-major positional formulae of §2,
this lifts to a witness in the bitmask encoding: positions `(U, V)`
with `U < bandOffset L k`, `bandOffset L k ≤ V < Fintype.card α`, and
bit `U.val` of `(predMaskOf L)[V.val]` *not* set.

This is the structural Prop-level statement at the bitmask level; the
final Bool-level identity `Case3Enum.irreducible (predMaskOf L)
(offsetsOf (bandSizes L)) = true` requires (a) imperative `forIn`-with-
`break` unfolding and (b) the `offsetsOf (bandSizes L)` characterization,
both of which are deferred to follow-up work. -/

/-- **Bitmask-level witness from `LayerOrdinalIrreducible`**.

For every band-cut `k ∈ [1, L.K)`, the irreducibility hypothesis
provides a position-level witness `U ∈ [0, bandOffset L k)`, `V ∈
[bandOffset L k, Fintype.card α)`, with bit `U` of `(predMaskOf L)[V]`
unset (equivalently, `¬ ((bandMajorEquiv L).symm ⟨U, _⟩ <
(bandMajorEquiv L).symm ⟨V, _⟩)` in `α`). -/
theorem exists_unset_bit_of_LayerOrdinalIrreducible
    (L : LayeredDecomposition α)
    (hIrr : LayerOrdinalIrreducible L)
    (k : ℕ) (hk1 : 1 ≤ k) (hkK : k < L.K) :
    ∃ U V, U < bandOffset L k ∧ bandOffset L k ≤ V ∧ V < Fintype.card α ∧
      Case3Enum.testBit' ((predMaskOf L).getD V 0) U = false := by
  classical
  -- Extract the abstract witness from ¬ LayerOrdinalReducible L k.
  have hRedNeg : ¬ LayerOrdinalReducible L k := hIrr k hk1 hkK
  -- LayerOrdinalReducible L k = ∀ u v, L.band u ≤ k → k < L.band v → u < v.
  -- Negation: ∃ u v, L.band u ≤ k ∧ k < L.band v ∧ ¬ u < v.
  have : ∃ u v, L.band u ≤ k ∧ k < L.band v ∧ ¬ (u < v) := by
    unfold LayerOrdinalReducible at hRedNeg
    push Not at hRedNeg
    exact hRedNeg
  obtain ⟨u, v, hu_band, hv_band, h_nlt⟩ := this
  -- Map u, v through bandMajorEquiv.
  refine ⟨(bandMajorEquiv L u).val, (bandMajorEquiv L v).val, ?_, ?_, ?_, ?_⟩
  · -- U < bandOffset L k.
    rw [bandMajorEquiv_val_lt_bandOffset_iff]; exact hu_band
  · -- bandOffset L k ≤ V.
    exact bandOffset_le_bandMajorEquiv_apply_val_of_lt L v k hv_band
  · -- V < Fintype.card α.
    exact bandMajorEquiv_apply_val_lt_card L v
  · -- bit U of pred[V] is FALSE.
    -- pred[V] has bit U set iff (bandMajorEquiv).symm U < (bandMajorEquiv).symm V
    -- = u < v. We have ¬ (u < v).
    rcases hbit : Case3Enum.testBit' ((predMaskOf L).getD
        (bandMajorEquiv L v).val 0) (bandMajorEquiv L u).val with _ | _
    · rfl
    · exfalso
      have := (testBit'_predMaskOf L (bandMajorEquiv L u) (bandMajorEquiv L v)).mp hbit
      simp only [Equiv.symm_apply_apply] at this
      exact h_nlt this

end Step8
end OneThird
