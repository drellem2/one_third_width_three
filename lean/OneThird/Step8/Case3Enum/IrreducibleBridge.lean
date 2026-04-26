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

/-! ### §5 — `Case3Enum.offsetsOf` characterization (A5-B1') -/

namespace Step8.Case3Enum

set_option linter.unusedSectionVars false
set_option linter.style.show false

/-- Recursive form of `Case3Enum.offsetsOf`'s loop body. Starting from
state `(acc, out)` and a list `bs`, it pushes the running cumulative
sum `acc + s_1, acc + s_1 + s_2, …` onto `out`. -/
private def offsetsOfAux : Nat → Array Nat → List Nat → Array Nat
  | _, out, [] => out
  | acc, out, s :: rest => offsetsOfAux (acc + s) (out.push (acc + s)) rest

/-- The body of `offsetsOf`'s for-loop, as a standalone function. -/
private def offsetsOfBody (s : Nat) (r : MProd Nat (Array Nat)) :
    Id (ForInStep (MProd Nat (Array Nat))) :=
  pure PUnit.unit >>= fun _ =>
    pure (ForInStep.yield ⟨r.fst + s, r.snd.push (r.fst + s)⟩)

/-- forIn over `offsetsOfBody` reduces to `offsetsOfAux`. -/
private lemma forIn_offsetsOfBody (bs : List Nat) :
    ∀ (acc : Nat) (out : Array Nat),
    (forIn (m := Id) bs (⟨acc, out⟩ : MProd Nat (Array Nat)) offsetsOfBody) =
      (⟨acc + bs.sum, offsetsOfAux acc out bs⟩ : MProd Nat (Array Nat)) := by
  induction bs with
  | nil =>
    intros acc out
    show (⟨acc, out⟩ : MProd Nat (Array Nat)) = _
    simp [offsetsOfAux]
  | cons s rest ih =>
    intros acc out
    rw [List.forIn_cons]
    show (forIn (m := Id) rest
            (⟨acc + s, out.push (acc + s)⟩ : MProd Nat (Array Nat))
            offsetsOfBody : Id _) = _
    rw [ih]
    show (⟨acc + s + rest.sum, _⟩ : MProd Nat (Array Nat)) = _
    have hassoc : acc + s + rest.sum = acc + (s + rest.sum) := by ring
    rw [hassoc]
    rfl

/-- `Case3Enum.offsetsOf` rewrites to its recursive form. -/
private lemma offsetsOf_eq_aux (bs : List Nat) :
    offsetsOf bs = offsetsOfAux 0 #[0] bs := by
  show (forIn (m := Id) bs (⟨0, #[0]⟩ : MProd Nat (Array Nat)) offsetsOfBody >>=
    fun r => pure r.snd : Id _) = _
  rw [forIn_offsetsOfBody]
  rfl

/-- Size of `offsetsOfAux`: each entry of `bs` pushes one element. -/
private lemma offsetsOfAux_size (acc : Nat) (out : Array Nat) (bs : List Nat) :
    (offsetsOfAux acc out bs).size = out.size + bs.length := by
  induction bs generalizing acc out with
  | nil => simp [offsetsOfAux]
  | cons s rest ih =>
    show (offsetsOfAux (acc + s) (out.push (acc + s)) rest).size = _
    rw [ih]; rw [Array.size_push]; simp; omega

/-- Indices below `out.size` are unchanged by `offsetsOfAux`. -/
private lemma offsetsOfAux_getD_lt (acc : Nat) (out : Array Nat) (bs : List Nat)
    (k : Nat) (hk : k < out.size) :
    (offsetsOfAux acc out bs).getD k 0 = out.getD k 0 := by
  induction bs generalizing acc out with
  | nil => rfl
  | cons s rest ih =>
    show (offsetsOfAux (acc + s) (out.push (acc + s)) rest).getD k 0 = _
    rw [ih (acc + s) (out.push (acc + s)) (by rw [Array.size_push]; omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem
      (by rw [Array.size_push]; omega : k < (out.push (acc + s)).size)]
    simp [Array.getElem_push, hk]

/-- Index `out.size` of `offsetsOfAux acc out (s :: rest)` is `acc + s`. -/
private lemma offsetsOfAux_getD_initialPush (acc : Nat) (out : Array Nat)
    (s : Nat) (rest : List Nat) :
    (offsetsOfAux acc out (s :: rest)).getD out.size 0 = acc + s := by
  show (offsetsOfAux (acc + s) (out.push (acc + s)) rest).getD out.size 0 = _
  rw [offsetsOfAux_getD_lt (acc + s) (out.push (acc + s)) rest out.size
    (by rw [Array.size_push]; omega)]
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem (by rw [Array.size_push]; omega :
    out.size < (out.push (acc + s)).size)]
  simp [Array.getElem_push]

/-- Closed-form for `offsetsOfAux`'s `getD` at indices `out.size ≤ k <
out.size + bs.length`: the value is `acc` plus the sum of the first
`(k - out.size + 1)` entries of `bs`. -/
private lemma offsetsOfAux_getD_ge (acc : Nat) (out : Array Nat) (bs : List Nat)
    (k : Nat) (hkLo : out.size ≤ k) (hkHi : k < out.size + bs.length) :
    (offsetsOfAux acc out bs).getD k 0 =
      acc + (bs.take (k - out.size + 1)).sum := by
  induction bs generalizing acc out k with
  | nil =>
    -- vacuous: out.size ≤ k < out.size + 0 is impossible.
    simp at hkHi; omega
  | cons s rest ih =>
    by_cases hk0 : k = out.size
    · subst hk0
      rw [offsetsOfAux_getD_initialPush]
      simp [List.take]
    · have hkLo' : out.size < k := lt_of_le_of_ne hkLo (Ne.symm hk0)
      show (offsetsOfAux (acc + s) (out.push (acc + s)) rest).getD k 0 = _
      have hsizePush : (out.push (acc + s)).size = out.size + 1 := by
        rw [Array.size_push]
      have hkLo2 : (out.push (acc + s)).size ≤ k := by rw [hsizePush]; omega
      have hkHi2 : k < (out.push (acc + s)).size + rest.length := by
        rw [hsizePush]
        have hh : (s :: rest).length = rest.length + 1 := by simp
        rw [hh] at hkHi; omega
      rw [ih (acc + s) (out.push (acc + s)) k hkLo2 hkHi2]
      rw [hsizePush]
      -- LHS: (acc + s) + (rest.take (k - (out.size + 1) + 1)).sum
      --    = (acc + s) + (rest.take (k - out.size)).sum
      -- RHS: acc + ((s :: rest).take (k - out.size + 1)).sum
      --    = acc + (s :: rest.take (k - out.size)).sum
      --    = acc + s + (rest.take (k - out.size)).sum
      have hpos : 0 < k - out.size + 1 := by omega
      have htake : (s :: rest).take (k - out.size + 1) =
          s :: rest.take (k - out.size + 1 - 1) := by
        rfl
      rw [htake]
      have hsubeq : k - (out.size + 1) + 1 = k - out.size + 1 - 1 := by omega
      rw [hsubeq]
      simp [List.sum_cons, Nat.add_assoc]

/-- **`Case3Enum.offsetsOf` size** (A5-B1'). -/
lemma offsetsOf_size (bs : List Nat) :
    (offsetsOf bs).size = bs.length + 1 := by
  rw [offsetsOf_eq_aux, offsetsOfAux_size]
  show 1 + bs.length = bs.length + 1
  ring

/-- **`Case3Enum.offsetsOf` value** (A5-B1'). For `k ≤ bs.length`,
`(offsetsOf bs).getD k 0 = (bs.take k).sum`. -/
lemma offsetsOf_getD (bs : List Nat) (k : Nat) (hk : k ≤ bs.length) :
    (offsetsOf bs).getD k 0 = (bs.take k).sum := by
  rw [offsetsOf_eq_aux]
  by_cases h0 : k = 0
  · subst h0
    show (offsetsOfAux 0 #[0] bs).getD 0 0 = (List.take 0 bs).sum
    rcases bs with _ | ⟨s, rest⟩
    · show (offsetsOfAux 0 #[0] []).getD 0 0 = _
      show (#[0] : Array Nat).getD 0 0 = _
      rfl
    · show (offsetsOfAux (0 + s) ((#[0] : Array Nat).push (0 + s)) rest).getD 0 0
        = _
      rw [offsetsOfAux_getD_lt (0 + s) ((#[0] : Array Nat).push (0 + s)) rest 0
        (by rw [Array.size_push]; simp)]
      rw [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_getElem (by rw [Array.size_push]; simp :
        0 < ((#[0] : Array Nat).push (0 + s)).size)]
      show ((#[0] : Array Nat).push (0 + s))[0] = (List.take 0 (s :: rest)).sum
      simp [List.take]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    have h1 : (#[0] : Array Nat).size ≤ k := by
      show 1 ≤ k
      omega
    have h2 : k < (#[0] : Array Nat).size + bs.length := by
      show k < 1 + bs.length
      omega
    rw [offsetsOfAux_getD_ge 0 #[0] bs k h1 h2]
    show 0 + (bs.take (k - 1 + 1)).sum = (bs.take k).sum
    have : k - 1 + 1 = k := by omega
    rw [this]; simp

end Step8.Case3Enum

/-! ### §6 — Imperative-loop unrolling for `Case3Enum.irreducible` -/

namespace Step8.Case3Enum

set_option linter.style.show false

variable (pred offsets : Array Nat)

/-- Inner-loop body of `irreducible`: at index `b`, if the bit-mask
check fails set `foundIncomp := true` and break (`done`); otherwise
yield the unchanged state. -/
def irrInnerBody (lowerMask : Nat) (b : Nat) (foundIncomp : Bool) :
    Id (ForInStep Bool) :=
  if (pred.getD b 0 &&& lowerMask) != lowerMask then
    pure (ForInStep.done true)
  else
    pure (ForInStep.yield foundIncomp)

/-- Outer-loop body of `irreducible`: at cut `k`, run the inner forIn,
then early-return `done some-false` if no witness was found, else continue.

The signature matches the elaborated form: a function taking the cut
`k` and the (irrelevant) outer state `r : MProd (Option Bool) PUnit`.
-/
def irrOuterBody (K : Nat) (k : Nat)
    (_r : MProd (Option Bool) PUnit) :
    Id (ForInStep (MProd (Option Bool) PUnit)) :=
  let offk := offsets.getD k 0
  let offK := offsets.getD K 0
  let lowerMask : Nat := (1 <<< offk) - 1
  let r' := forIn (m := Id) (List.range' offk (offK - offk)) false
    (fun b foundIncomp => irrInnerBody pred lowerMask b foundIncomp)
  if !r' then
    pure (ForInStep.done (⟨some false, PUnit.unit⟩ : MProd (Option Bool) PUnit))
  else
    pure (ForInStep.yield (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit))

/-- Imperative→functional reduction of `irreducible`. -/
private theorem irreducible_eq_outer_match :
    irreducible pred offsets =
      (match (forIn (m := Id) (List.range' 1 (offsets.size - 1 - 1))
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun k r => irrOuterBody pred offsets (offsets.size - 1) k r)).fst with
       | none => true
       | some a => a) := by
  unfold irreducible irrOuterBody irrInnerBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- Inner-loop body always yields `false` or `done true`, depending on
the bit-mask check (and assuming initial state is `false`). -/
private lemma irrInnerBody_yield_or_done (lowerMask b : Nat) :
    irrInnerBody pred lowerMask b false =
        pure (ForInStep.yield false) ∨
    irrInnerBody pred lowerMask b false =
        pure (ForInStep.done true) := by
  unfold irrInnerBody
  by_cases h : ((pred.getD b 0 &&& lowerMask) != lowerMask) = true
  · right; rw [if_pos h]
  · left; rw [if_neg h]

/-- Inner-loop body returns `done true` iff the bit-mask check fails. -/
private lemma irrInnerBody_done_iff (lowerMask b : Nat) (foundIncomp : Bool) :
    irrInnerBody pred lowerMask b foundIncomp =
        pure (ForInStep.done true) ↔
      pred.getD b 0 &&& lowerMask ≠ lowerMask := by
  unfold irrInnerBody
  have hYne : ∀ x : Bool, (pure (ForInStep.yield x) : Id _) ≠
      pure (ForInStep.done true) := fun x h => by cases h
  by_cases h : ((pred.getD b 0 &&& lowerMask) != lowerMask) = true
  · rw [if_pos h]
    refine ⟨fun _ => bne_iff_ne.mp h, fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨fun e => absurd e (hYne _), fun hne => ?_⟩
    rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    exact absurd h hne

/-- The inner forIn (state `Bool`, init `false`) returns `true` iff
some element of the iteration list triggers the `done true` branch. -/
private lemma irrInner_forIn_true_iff (lowerMask : Nat) (l : List Nat) :
    (forIn (m := Id) l false
      (fun b foundIncomp => irrInnerBody pred lowerMask b foundIncomp)) = true ↔
    ∃ b ∈ l, pred.getD b 0 &&& lowerMask ≠ lowerMask := by
  induction l with
  | nil => simp [forIn]
  | cons b bs ih =>
    rw [List.forIn_cons]
    rcases irrInnerBody_yield_or_done pred lowerMask b with hy | hd
    · rw [hy]
      change (forIn (m := Id) bs false _ : Id Bool) = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨b', hmem, hbit⟩
        exact ⟨b', List.mem_cons_of_mem _ hmem, hbit⟩
      · rintro ⟨b', hmem, hbit⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exfalso
          have := (irrInnerBody_done_iff pred lowerMask b' false).mpr hbit
          rw [hy] at this
          exact absurd this (fun h => by cases h)
        · exact ⟨b', hmem', hbit⟩
    · rw [hd]
      change ((true : Bool) = true) ↔ _
      refine ⟨fun _ => ⟨b, ?_, ?_⟩, fun _ => rfl⟩
      · exact List.mem_cons_self
      · exact (irrInnerBody_done_iff pred lowerMask b false).mp hd

/-- Outer body case-split via the inner forIn's Bool result. -/
private lemma irrOuterBody_eq_of_inner_true (K k : Nat)
    (r : MProd (Option Bool) PUnit)
    (htrue : (forIn (m := Id) (List.range' (offsets.getD k 0)
        (offsets.getD K 0 - offsets.getD k 0)) false
      (fun b foundIncomp => irrInnerBody pred
        ((1 <<< offsets.getD k 0) - 1) b foundIncomp)) = true) :
    irrOuterBody pred offsets K k r =
      pure (ForInStep.yield
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
  unfold irrOuterBody
  show (if (!(forIn (m := Id) (List.range' (offsets.getD k 0)
        (offsets.getD K 0 - offsets.getD k 0)) false
        (fun b foundIncomp => irrInnerBody pred
          ((1 <<< offsets.getD k 0) - 1) b foundIncomp))) = true
    then pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
      MProd (Option Bool) PUnit))
    else pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
      MProd (Option Bool) PUnit))) = _
  rw [htrue]; rfl

private lemma irrOuterBody_eq_of_inner_false (K k : Nat)
    (r : MProd (Option Bool) PUnit)
    (hfalse : (forIn (m := Id) (List.range' (offsets.getD k 0)
        (offsets.getD K 0 - offsets.getD k 0)) false
      (fun b foundIncomp => irrInnerBody pred
        ((1 <<< offsets.getD k 0) - 1) b foundIncomp)) = false) :
    irrOuterBody pred offsets K k r =
      pure (ForInStep.done
        (⟨some false, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
  unfold irrOuterBody
  show (if (!(forIn (m := Id) (List.range' (offsets.getD k 0)
        (offsets.getD K 0 - offsets.getD k 0)) false
        (fun b foundIncomp => irrInnerBody pred
          ((1 <<< offsets.getD k 0) - 1) b foundIncomp))) = true
    then pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
      MProd (Option Bool) PUnit))
    else pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
      MProd (Option Bool) PUnit))) = _
  rw [hfalse]; rfl

/-- Outer body always yields `none` or done `some-false`. -/
private lemma irrOuterBody_yield_or_done (K k : Nat)
    (r : MProd (Option Bool) PUnit) :
    irrOuterBody pred offsets K k r =
        pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
          MProd (Option Bool) PUnit)) ∨
    irrOuterBody pred offsets K k r =
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
          MProd (Option Bool) PUnit)) := by
  generalize hg : (forIn (m := Id) (List.range' (offsets.getD k 0)
      (offsets.getD K 0 - offsets.getD k 0)) false
    (fun b foundIncomp => irrInnerBody pred
      ((1 <<< offsets.getD k 0) - 1) b foundIncomp) : Id Bool) = rv
  cases rv with
  | true => left; exact irrOuterBody_eq_of_inner_true pred offsets K k r hg
  | false => right; exact irrOuterBody_eq_of_inner_false pred offsets K k r hg

/-- Outer body returns `yield none` iff inner forIn finds witness. -/
private lemma irrOuterBody_yield_iff (K k : Nat)
    (r : MProd (Option Bool) PUnit) :
    irrOuterBody pred offsets K k r =
        pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
          MProd (Option Bool) PUnit)) ↔
    ∃ b ∈ List.range' (offsets.getD k 0)
        (offsets.getD K 0 - offsets.getD k 0),
      pred.getD b 0 &&& ((1 <<< offsets.getD k 0) - 1) ≠
        (1 <<< offsets.getD k 0) - 1 := by
  rw [← irrInner_forIn_true_iff]
  generalize hg : (forIn (m := Id) (List.range' (offsets.getD k 0)
      (offsets.getD K 0 - offsets.getD k 0)) false
    (fun b foundIncomp => irrInnerBody pred
      ((1 <<< offsets.getD k 0) - 1) b foundIncomp) : Id Bool) = rv
  cases rv with
  | true =>
    rw [irrOuterBody_eq_of_inner_true pred offsets K k r hg]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | false =>
    rw [irrOuterBody_eq_of_inner_false pred offsets K k r hg]
    refine ⟨fun e => absurd e (fun h => by cases h), fun e => ?_⟩
    exact absurd e (fun h => by cases h)

/-- The outer forIn yields `.fst = none` (no early return triggered)
iff every cut `k` finds an inner-loop witness. -/
private lemma irrOuter_forIn_fst_none_iff (K : Nat) (l : List Nat) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun k r => irrOuterBody pred offsets K k r)).fst = none ↔
    ∀ k ∈ l, ∃ b ∈ List.range' (offsets.getD k 0)
        (offsets.getD K 0 - offsets.getD k 0),
      pred.getD b 0 &&& ((1 <<< offsets.getD k 0) - 1) ≠
        (1 <<< offsets.getD k 0) - 1 := by
  induction l with
  | nil =>
    show ((⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit).fst = none) ↔ _
    simp
  | cons k ks ih =>
    rw [List.forIn_cons]
    rcases irrOuterBody_yield_or_done pred offsets K k
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) with hy | hd
    · rw [hy]
      change (forIn (m := Id) ks
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = none ↔ _
      rw [ih]
      have hk_witness : ∃ b ∈ List.range' (offsets.getD k 0)
          (offsets.getD K 0 - offsets.getD k 0),
        pred.getD b 0 &&& ((1 <<< offsets.getD k 0) - 1) ≠
          (1 <<< offsets.getD k 0) - 1 :=
        (irrOuterBody_yield_iff pred offsets K k _).mp hy
      constructor
      · intro h k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk_mem
        · exact hk_witness
        · exact h k' hk_mem
      · intro h k' hk_mem
        exact h k' (List.mem_cons_of_mem _ hk_mem)
    · rw [hd]
      change ((⟨some false, PUnit.unit⟩ :
          MProd (Option Bool) PUnit).fst = none) ↔ _
      refine ⟨fun e => by simp at e, fun h => ?_⟩
      exfalso
      have hk_witness := h k List.mem_cons_self
      have := (irrOuterBody_yield_iff pred offsets K k
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)).mpr hk_witness
      rw [hd] at this
      exact absurd this (fun h => by cases h)

/-- **Sufficient condition for `Case3Enum.irreducible = true`** (A5-B1').
For every cut `k ∈ [1, K)` (where `K = offsets.size - 1`), if there
exists `b ∈ [offsets[k], offsets[K])` such that the bit-mask check
`pred[b] &&& lowerMask ≠ lowerMask` holds (i.e. some bit in
`[0, offsets[k])` is unset in `pred[b]`), then `irreducible pred
offsets = true`. -/
theorem irreducible_eq_true_of_witnesses
    (h : ∀ k ∈ List.range' 1 (offsets.size - 1 - 1),
      ∃ b ∈ List.range' (offsets.getD k 0)
          (offsets.getD (offsets.size - 1) 0 - offsets.getD k 0),
        pred.getD b 0 &&& ((1 <<< offsets.getD k 0) - 1) ≠
          (1 <<< offsets.getD k 0) - 1) :
    irreducible pred offsets = true := by
  rw [irreducible_eq_outer_match]
  rw [show (forIn (m := Id) (List.range' 1 (offsets.size - 1 - 1))
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun k r => irrOuterBody pred offsets (offsets.size - 1) k r)).fst = none from
    (irrOuter_forIn_fst_none_iff pred offsets (offsets.size - 1)
      (List.range' 1 (offsets.size - 1 - 1))).mpr h]

end Step8.Case3Enum

/-! ### §7 — Final bridge: `LayerOrdinalIrreducible L` ⇒
`Case3Enum.irreducible (predMaskOf L) (offsetsOf (bandSizes L)) = true` -/

namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false

/-- Helper: `((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i`. -/
private lemma sum_map_range_eq_finset_sum (k : Nat) (f : Nat → Nat) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    rw [Finset.sum_range_succ]
    simp

/-- `bandOffset L k = (bandSizes L).take k` summed.

Connects the recursive cumulative-sum form `bandOffset L` with the
list-take-sum view used by `offsetsOf_getD`. -/
private lemma bandOffset_eq_take_sum (L : LayeredDecomposition α) (k : Nat)
    (hk : k ≤ L.K) :
    bandOffset L k = ((bandSizes L).take k).sum := by
  rw [bandOffset_eq_finset_sum]
  unfold bandSizes
  rw [← List.map_take]
  -- Reduce: (List.range L.K).take k = List.range k when k ≤ L.K.
  have hrange_take : (List.range L.K).take k = List.range k := by
    rw [List.take_range, Nat.min_eq_left hk]
  rw [hrange_take]
  rw [sum_map_range_eq_finset_sum]

/-- Restated: `(offsetsOf (bandSizes L)).getD k 0 = bandOffset L k`
for `k ≤ L.K`. -/
lemma offsetsOf_bandSizes_getD (L : LayeredDecomposition α) (k : Nat)
    (hk : k ≤ L.K) :
    (Case3Enum.offsetsOf (bandSizes L)).getD k 0 = bandOffset L k := by
  rw [Case3Enum.offsetsOf_getD _ k (by rw [bandSizes_length]; exact hk)]
  exact (bandOffset_eq_take_sum L k hk).symm

/-- Restated: `(offsetsOf (bandSizes L)).size = L.K + 1`. -/
lemma offsetsOf_bandSizes_size (L : LayeredDecomposition α) :
    (Case3Enum.offsetsOf (bandSizes L)).size = L.K + 1 := by
  rw [Case3Enum.offsetsOf_size, bandSizes_length]

/-- **Final bridge** (A5-B1'): `LayerOrdinalIrreducible L` lifts to the
Bool-level identity `Case3Enum.irreducible (predMaskOf L)
(offsetsOf (bandSizes L)) = true`.

This combines:
* `exists_unset_bit_of_LayerOrdinalIrreducible` (§4) — for each cut
  `k ∈ [1, L.K)`, irreducibility gives positions `(U, V)` with bit
  `U` of `predMaskOf[V]` unset.
* `offsetsOf_bandSizes_getD` (§7) — `(offsetsOf (bandSizes L)).getD k 0
  = bandOffset L k`.
* `and_lowerMask_ne_iff_some_bit_unset` (§3) — the unset-bit witness
  forces the bit-mask check `pred[V] &&& lowerMask ≠ lowerMask`.
* `irreducible_eq_true_of_witnesses` (§6) — if every cut has a
  witness, the imperative `Case3Enum.irreducible` returns `true`. -/
theorem irreducible_predMaskOf_offsetsOf_eq_true
    (L : LayeredDecomposition α)
    (hIrr : LayerOrdinalIrreducible L) :
    Case3Enum.irreducible (predMaskOf L) (Case3Enum.offsetsOf (bandSizes L)) =
      true := by
  classical
  apply Case3Enum.irreducible_eq_true_of_witnesses
  intro k hk_mem
  -- k ∈ [1, K), where K = (offsetsOf (bandSizes L)).size - 1 = L.K.
  rw [List.mem_range'_1] at hk_mem
  obtain ⟨hk1, hk_lt⟩ := hk_mem
  have hsize : (Case3Enum.offsetsOf (bandSizes L)).size - 1 - 1 = L.K - 1 := by
    rw [offsetsOf_bandSizes_size]; omega
  rw [hsize] at hk_lt
  have hkK : k < L.K := by omega
  -- Extract (U, V) witnesses from irreducibility.
  obtain ⟨U, V, hU_lt, hV_ge, hV_lt, hbit_false⟩ :=
    exists_unset_bit_of_LayerOrdinalIrreducible L hIrr k hk1 hkK
  -- offsets[k] = bandOffset L k.
  have hoffk : (Case3Enum.offsetsOf (bandSizes L)).getD k 0 = bandOffset L k :=
    offsetsOf_bandSizes_getD L k (le_of_lt hkK)
  -- offsets[K] = bandOffset L K = Fintype.card α.
  have hoffK : (Case3Enum.offsetsOf (bandSizes L)).getD
      ((Case3Enum.offsetsOf (bandSizes L)).size - 1) 0 = Fintype.card α := by
    rw [offsetsOf_bandSizes_size]
    simp only [Nat.add_sub_cancel]
    rw [offsetsOf_bandSizes_getD L L.K (le_refl _)]
    exact bandOffset_K L
  -- Provide V as the inner witness.
  refine ⟨V, ?_, ?_⟩
  · -- V ∈ List.range' offsets[k] (offsets[K] - offsets[k]).
    rw [hoffk, hoffK, List.mem_range'_1]
    refine ⟨hV_ge, ?_⟩
    -- V < bandOffset L k + (Fintype.card α - bandOffset L k) = Fintype.card α.
    have : bandOffset L k ≤ Fintype.card α := by
      rw [← bandOffset_K L]
      exact bandOffset_mono L (le_of_lt hkK)
    omega
  · -- pred[V] &&& lowerMask ≠ lowerMask.
    rw [hoffk]
    rw [and_lowerMask_ne_iff_some_bit_unset]
    refine ⟨U, hU_lt, ?_⟩
    -- testBit (predMaskOf[V]) U = false.
    -- We have hbit_false : Case3Enum.testBit' ((predMaskOf L).getD V 0) U = false.
    -- testBit' = testBit by `testBit'_eq_testBit`.
    have := hbit_false
    rw [testBit'_eq_testBit] at this
    exact this

end Step8
end OneThird
