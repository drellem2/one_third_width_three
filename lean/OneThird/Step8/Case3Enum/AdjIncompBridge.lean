/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.BoundedIrreducibleBalanced

/-!
# Step 8 — Bool↔Prop bridge: `hasAdjacentIncomp` from `LayerOrdinalIrreducible`
(A5-B2, `mg-e9d6`)

For a `LayeredDecomposition L` with `L.K ≥ 2`, all bands non-empty,
and `LayerOrdinalIrreducible L`, we show that the Bool-level
`Case3Enum.hasAdjacentIncomp (predMaskOf L) offsets = true` whenever
`offsets` carries the band-major positional alignment of `L`'s bands.

The proof combines `Step8.exists_adjacent_not_lt_of_irreducible`
(F2 / `lem:irr-adjacent`, `mg-7946`) with the §2c `predMaskOf` /
`bandMajorEquiv` encoding of A1+A2.

## Main results

* `Case3Enum.hasAdjacentIncomp_eq_true_of_witness` — sufficient
  condition: an explicit `(s, b)` pair with the bit-mask check
  failing forces `hasAdjacentIncomp = true`.
* `Step8.hasAdjacentIncomp_predMaskOf_eq_true` — the F2 bridge:
  given a positional alignment of `offsets` with `bandMajorEquiv L`,
  the irreducibility hypothesis discharges the Bool check.
-/

namespace OneThird
namespace Step8.Case3Enum

set_option linter.unusedSectionVars false

/-! ### §1 — Imperative-loop unrolling: outer/inner body factoring

`hasAdjacentIncomp` follows the same `MProd (Option Bool) PUnit`
early-return pattern used by `hasBalancedPairSlow` (cf.
`BalancedLift.lean` §7); we replay the bookkeeping locally with the
band-mask body.
-/

variable (pred : Array Nat) (offsets : Array Nat)

/-- The "band mask" extracting bits in `[offsets[s], offsets[s+1])`. -/
def adjBandMask (s : Nat) : Nat :=
  ((1 <<< offsets.getD (s + 1) 0) - 1) ^^^ ((1 <<< offsets.getD s 0) - 1)

/-- Inner-loop body of `hasAdjacentIncomp`: triggers `done` if the
band-mask check fails at index `b`. -/
def adjInnerBody (s b : Nat) : Id (ForInStep (MProd (Option Bool) PUnit)) :=
  if (pred.getD b 0 &&& adjBandMask offsets s) != adjBandMask offsets s then
    pure (ForInStep.done ⟨some true, PUnit.unit⟩)
  else
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)

/-- Outer-loop body: runs the inner loop, then propagates `done` if
the inner triggered. -/
def adjOuterBody (s : Nat) : Id (ForInStep (MProd (Option Bool) PUnit)) := do
  let r ← forIn (m := Id) (List.range' (offsets.getD (s + 1) 0)
                            (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
    (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
    (fun b _ => adjInnerBody pred offsets s b)
  match r.fst with
  | none => pure (ForInStep.yield ⟨none, PUnit.unit⟩)
  | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)

/-- Imperative→functional reduction: `hasAdjacentIncomp` rewrites as
the outer `forIn` over `List.range' 0 (K - 1)`. -/
private theorem hasAdjacentIncomp_eq_outer_fst :
    hasAdjacentIncomp pred offsets =
      (match (forIn (m := Id) (List.range' 0 (offsets.size - 1 - 1))
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun s _ => adjOuterBody pred offsets s)).fst with
       | none => false
       | some a => a) := by
  unfold hasAdjacentIncomp adjOuterBody adjInnerBody adjBandMask
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- Inner-loop body always returns `yield none` or `done some-true`. -/
private lemma adjInnerBody_yield_or_done (s b : Nat) :
    adjInnerBody pred offsets s b =
        pure (ForInStep.yield (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ∨
    adjInnerBody pred offsets s b =
        pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
  unfold adjInnerBody
  by_cases h : ((pred.getD b 0 &&& adjBandMask offsets s) != adjBandMask offsets s) = true
  · right; rw [if_pos h]
  · left; rw [if_neg h]

/-- Inner-loop body returns `done` iff the band-mask check fails. -/
private lemma adjInnerBody_done_iff (s b : Nat) :
    adjInnerBody pred offsets s b =
        pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ↔
      pred.getD b 0 &&& adjBandMask offsets s ≠ adjBandMask offsets s := by
  unfold adjInnerBody
  have hYne : (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
        MProd (Option Bool) PUnit)) : Id _) ≠
      pure (ForInStep.done ⟨some true, PUnit.unit⟩) := fun h => by cases h
  by_cases h : ((pred.getD b 0 &&& adjBandMask offsets s) != adjBandMask offsets s) = true
  · rw [if_pos h]
    refine ⟨fun _ => bne_iff_ne.mp h, fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨fun e => absurd e hYne, fun hne => ?_⟩
    rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    exact absurd h hne

/-- Generic `forIn (Id)` "yield-or-done" extraction: `forIn` over
a list whose body always yields `none` or done-`true` produces
`some true` iff some element triggers the `done` branch. -/
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

/-- Inner forIn's `.fst` is `none` or `some true`. -/
private lemma adjInner_forIn_fst (s : Nat) (l : List Nat) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun b _ => adjInnerBody pred offsets s b)).fst = none ∨
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun b _ => adjInnerBody pred offsets s b)).fst = some true := by
  induction l with
  | nil => left; rfl
  | cons b bs ih =>
    rw [List.forIn_cons]
    rcases adjInnerBody_yield_or_done pred offsets s b with hy | hd
    · rw [hy]
      change ((forIn (m := Id) bs
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = none) ∨ _ = some true
      exact ih
    · rw [hd]; right; rfl

/-- Outer-loop body always returns `yield none` or `done some-true`. -/
private lemma adjOuterBody_yield_or_done (s : Nat) :
    adjOuterBody pred offsets s =
        pure (ForInStep.yield (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ∨
    adjOuterBody pred offsets s =
        pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
  rcases adjInner_forIn_fst pred offsets s
      (List.range' (offsets.getD (s + 1) 0) (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
      with hn | hs'
  · left
    show (match (forIn (m := Id)
              (List.range' (offsets.getD (s + 1) 0)
                (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun b _ => adjInnerBody pred offsets s b) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _
    rw [hn]
  · right
    show (match (forIn (m := Id)
              (List.range' (offsets.getD (s + 1) 0)
                (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun b _ => adjInnerBody pred offsets s b) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _
    rw [hs']

/-- Sufficient condition for `hasAdjacentIncomp = true`: an explicit
`(s, b)` witness with the band-mask check failing. -/
theorem hasAdjacentIncomp_eq_true_of_witness
    {pred offsets : Array Nat} {s b : Nat}
    (hsRange : s ∈ List.range' 0 (offsets.size - 1 - 1))
    (hbRange : b ∈ List.range' (offsets.getD (s + 1) 0)
                    (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
    (hbit : pred.getD b 0 &&& adjBandMask offsets s ≠ adjBandMask offsets s) :
    hasAdjacentIncomp pred offsets = true := by
  rw [hasAdjacentIncomp_eq_outer_fst]
  -- The outer body at iteration `s` triggers `done`, since the inner forIn
  -- finds `b` as a witness.
  have h_inner_done : adjInnerBody pred offsets s b =
      pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) :=
    (adjInnerBody_done_iff pred offsets s b).mpr hbit
  have h_inner_some : (forIn (m := Id)
      (List.range' (offsets.getD (s + 1) 0) (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun b _ => adjInnerBody pred offsets s b)).fst = some true :=
    (forIn_id_yield_or_done_iff _ _ (adjInnerBody_yield_or_done pred offsets s)).mpr
      ⟨b, hbRange, h_inner_done⟩
  have h_outer_done : adjOuterBody pred offsets s =
      pure (ForInStep.done (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit)) := by
    show (match (forIn (m := Id)
              (List.range' (offsets.getD (s + 1) 0)
                (offsets.getD (s + 2) 0 - offsets.getD (s + 1) 0))
              (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
              (fun b _ => adjInnerBody pred offsets s b) :
              MProd (Option Bool) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option Bool) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) =
        pure (ForInStep.done ⟨some true, PUnit.unit⟩)
    rw [h_inner_some]
  -- The outer forIn produces `some true`, since `s` is a `done`-witness.
  have h_outer_some : (forIn (m := Id) (List.range' 0 (offsets.size - 1 - 1))
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun s _ => adjOuterBody pred offsets s)).fst = some true :=
    (forIn_id_yield_or_done_iff _ _ (adjOuterBody_yield_or_done pred offsets)).mpr
      ⟨s, hsRange, h_outer_done⟩
  -- Final step: the outer `match` returns `true`.
  show (match (forIn (m := Id) (List.range' 0 (offsets.size - 1 - 1))
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun s _ => adjOuterBody pred offsets s)).fst with
        | none => false
        | some a => a) = true
  rw [h_outer_some]

end Step8.Case3Enum

/-! ### §2 — F2 bridge: irreducibility ⇒ `hasAdjacentIncomp = true` -/

namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- **Bool↔Prop bridge: `hasAdjacentIncomp` from `LayerOrdinalIrreducible`** (A5-B2).

For a `LayeredDecomposition L` with depth `≥ 2`, all bands non-empty,
and layer-ordinal-sum irreducible, the band-major Bool check
`Case3Enum.hasAdjacentIncomp (predMaskOf L) offsets` is `true`,
provided `offsets` carries the band-major positional alignment of
`L` — i.e., for every `x : α` with band-index `k = L.band x`, the
band-major position `(bandMajorEquiv L x).val` lies in
`[offsets[k-1], offsets[k])`, with `offsets.size ≥ L.K + 1`.

This is the F2 piece of the F5a-ℓ Bool↔Prop bridge: the positional
hypothesis is supplied by the A5-B3 enumPosetsFor unrolling
(`mg-0f0e`); B2 (this file) supplies the irreducibility-driven
adjacent-incomparable-pair witness via `exists_adjacent_not_lt_of_
irreducible` (`mg-7946`). -/
theorem hasAdjacentIncomp_predMaskOf_eq_true
    (L : LayeredDecomposition α)
    (hK : 2 ≤ L.K)
    (hIrr : LayerOrdinalIrreducible L)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty)
    (offsets : Array Nat)
    (hSize : L.K + 1 ≤ offsets.size)
    (hPosLo : ∀ x : α, offsets.getD (L.band x - 1) 0 ≤ (bandMajorEquiv L x).val)
    (hPosHi : ∀ x : α, (bandMajorEquiv L x).val < offsets.getD (L.band x) 0) :
    Case3Enum.hasAdjacentIncomp (predMaskOf L) offsets = true := by
  -- Extract the adjacent-incomp witness from F2.
  obtain ⟨i, u, v, h1i, hiK, hbu, hbv, hnotlt⟩ :=
    exists_adjacent_not_lt_of_irreducible L hK hIrr hNonempty
  -- Outer-loop range: `s = i - 1 ∈ [0, K-1)`.
  have hsRange : (i - 1) ∈ List.range' 0 (offsets.size - 1 - 1) := by
    rw [List.mem_range'_1]; refine ⟨Nat.zero_le _, ?_⟩; omega
  -- Inner-loop range: `b = (bandMajorEquiv L v).val ∈ [offsets[i], offsets[i+1])`.
  -- (Recall `s = i - 1`, so `s + 1 = i` and `s + 2 = i + 1`.)
  have hsi : i - 1 + 1 = i := by omega
  have hsi2 : i - 1 + 2 = i + 1 := by omega
  have hbLo : offsets.getD (i - 1 + 1) 0 ≤ (bandMajorEquiv L v).val := by
    have hp := hPosLo v
    rw [hbv] at hp
    rw [hsi]
    convert hp using 2
  have hbHi : (bandMajorEquiv L v).val < offsets.getD (i - 1 + 2) 0 := by
    have hp := hPosHi v
    rw [hbv] at hp
    rw [hsi2]
    exact hp
  have hbRange : (bandMajorEquiv L v).val ∈
      List.range' (offsets.getD (i - 1 + 1) 0)
        (offsets.getD (i - 1 + 2) 0 - offsets.getD (i - 1 + 1) 0) := by
    rw [List.mem_range'_1]; refine ⟨hbLo, ?_⟩; omega
  -- Position of `u` in the band-mask range `[offsets[i-1], offsets[i])`.
  have hu'_lt : (bandMajorEquiv L u).val < offsets.getD (i - 1 + 1) 0 := by
    have hp := hPosHi u
    rw [hbu] at hp
    rw [hsi]
    exact hp
  have hu'_ge : offsets.getD (i - 1) 0 ≤ (bandMajorEquiv L u).val := by
    have hp := hPosLo u
    rw [hbu] at hp
    convert hp using 2
  -- Bit-positional reasoning: bit `(bandMajorEquiv L u).val` is in `adjBandMask offsets (i-1)`,
  -- but *not* in `(predMaskOf L)[(bandMajorEquiv L v).val]` (because ¬ (u < v)).
  have h_mask_bit : Nat.testBit (Case3Enum.adjBandMask offsets (i - 1))
        (bandMajorEquiv L u).val = true := by
    unfold Case3Enum.adjBandMask
    rw [Nat.testBit_xor]
    have h1 : Nat.testBit ((1 <<< offsets.getD (i - 1 + 1) 0) - 1)
        (bandMajorEquiv L u).val = true := by
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hu'_lt
    have h2 : Nat.testBit ((1 <<< offsets.getD (i - 1) 0) - 1)
        (bandMajorEquiv L u).val = false := by
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
      exact decide_eq_false (Nat.not_lt.mpr hu'_ge)
    rw [h1, h2]; rfl
  have h_pred_bit : Nat.testBit ((predMaskOf L).getD (bandMajorEquiv L v).val 0)
        (bandMajorEquiv L u).val = false := by
    rcases h : Nat.testBit ((predMaskOf L).getD (bandMajorEquiv L v).val 0)
        (bandMajorEquiv L u).val with _ | _
    · rfl
    · exfalso
      have hbit := (testBit_predMaskOf L (bandMajorEquiv L u) (bandMajorEquiv L v)).mp h
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hbit
      exact hnotlt hbit
  -- Combine: the masked value at bit `u'` is `false` while the mask itself has bit `u'` `true`.
  have h_neq : (predMaskOf L).getD (bandMajorEquiv L v).val 0 &&&
                Case3Enum.adjBandMask offsets (i - 1) ≠
              Case3Enum.adjBandMask offsets (i - 1) := by
    intro heq
    have := congrArg (fun n => Nat.testBit n (bandMajorEquiv L u).val) heq
    simp only [Nat.testBit_and] at this
    rw [h_pred_bit, h_mask_bit] at this
    exact Bool.false_ne_true this
  -- Apply the sufficient-condition theorem.
  exact Case3Enum.hasAdjacentIncomp_eq_true_of_witness hsRange hbRange h_neq

end Step8

end OneThird
