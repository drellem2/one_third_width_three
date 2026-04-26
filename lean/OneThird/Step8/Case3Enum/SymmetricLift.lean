/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum.BalancedLift
import OneThird.Step8.BoundedIrreducibleBalanced

/-!
# Step 8 — Bool→Prop lift of `findSymmetricPair` (A5-G3a, `mg-609a`)

The Bool indicator `Case3Enum.findSymmetricPair pred n = some (x, y)`
fast path lifts to a `Symmetric pred n x y` Prop-witness for some
`x y : Fin n`.  Combined with `BalancedLift.lean` §3's
`hasBalancedPair_of_symmetric`, this discharges the `h_sym_lift`
hypothesis of `hasBalancedPair_of_hasBalancedPair`.

## Scope (A5-G3a)

This file ships the imperative-loop unrolling and `Symmetric`
extraction.  The `succ_agree` field of `Symmetric` requires
`successorMasks` bit-correctness:

```
Nat.testBit ((Case3Enum.successorMasks pred n).getD u 0) v =
  Case3Enum.testBit' (pred.getD v 0) u    (for u, v < n)
```

This is split off into the follow-up work item `mg-G3a-followup`
(per pc-b53a's recommendation; A5-G3a was sized for the
loop-unrolling/extraction half).  The main theorem here takes
the bit-correctness as an explicit hypothesis.

## Pattern

Imperative-loop unrolling parallel to `BalancedLift.lean` §7's
slow-path lift:

* §1 — `findSymmetricPair` outer/inner forIn unrolling.
* §2 — Conversion of the loop's bit conditions to `Symmetric`
  fields, with `succ_agree` mediated by the bit-correctness
  hypothesis on `successorMasks`.
-/

namespace OneThird
namespace Step8
namespace Case3Enum

set_option linter.unusedSectionVars false

/-! ## §1 — `findSymmetricPair` outer/inner forIn unrolling -/

/-- Inner-loop body of `findSymmetricPair`. -/
private def symInnerBody (pred : Array Nat) (succ : Array Nat) (n x : ℕ) :
    ℕ → Id (ForInStep (MProd (Option (Option (Nat × Nat))) PUnit)) :=
  fun y =>
    if testBit' (pred.getD y 0) x = true then
      (pure (ForInStep.yield ⟨none, PUnit.unit⟩) : Id _)
    else if testBit' (pred.getD x 0) y = true then
      pure (ForInStep.yield ⟨none, PUnit.unit⟩)
    else if (pred.getD x 0 &&& lnotN (bit x ||| bit y) n !=
             pred.getD y 0 &&& lnotN (bit x ||| bit y) n) = true then
      pure (ForInStep.yield ⟨none, PUnit.unit⟩)
    else if (succ.getD x 0 &&& lnotN (bit x ||| bit y) n !=
             succ.getD y 0 &&& lnotN (bit x ||| bit y) n) = true then
      pure (ForInStep.yield ⟨none, PUnit.unit⟩)
    else
      pure (ForInStep.done ⟨some (some (x, y)), PUnit.unit⟩)

private lemma symInnerBody_yield_or_done (pred : Array Nat) (succ : Array Nat)
    (n x y : ℕ) :
    symInnerBody pred succ n x y =
      pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit)) ∨
    symInnerBody pred succ n x y =
      pure (ForInStep.done (⟨some (some (x, y)), PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit)) := by
  unfold symInnerBody
  by_cases h1 : testBit' (pred.getD y 0) x = true
  · left; rw [if_pos h1]
  by_cases h2 : testBit' (pred.getD x 0) y = true
  · left; rw [if_neg h1, if_pos h2]
  by_cases h3 : (pred.getD x 0 &&& lnotN (bit x ||| bit y) n !=
                 pred.getD y 0 &&& lnotN (bit x ||| bit y) n) = true
  · left; rw [if_neg h1, if_neg h2, if_pos h3]
  by_cases h4 : (succ.getD x 0 &&& lnotN (bit x ||| bit y) n !=
                 succ.getD y 0 &&& lnotN (bit x ||| bit y) n) = true
  · left; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  · right; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

private lemma symInnerBody_done_iff (pred : Array Nat) (succ : Array Nat)
    (n x y : ℕ) :
    symInnerBody pred succ n x y =
        pure (ForInStep.done (⟨some (some (x, y)), PUnit.unit⟩ :
          MProd (Option (Option (Nat × Nat))) PUnit)) ↔
      ¬ testBit' (pred.getD y 0) x = true ∧
      ¬ testBit' (pred.getD x 0) y = true ∧
      (pred.getD x 0 &&& lnotN (bit x ||| bit y) n) =
        (pred.getD y 0 &&& lnotN (bit x ||| bit y) n) ∧
      (succ.getD x 0 &&& lnotN (bit x ||| bit y) n) =
        (succ.getD y 0 &&& lnotN (bit x ||| bit y) n) := by
  unfold symInnerBody
  have hYne : (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit)) : Id _) ≠
      pure (ForInStep.done ⟨some (some (x, y)), PUnit.unit⟩) := fun h => by cases h
  by_cases h1 : testBit' (pred.getD y 0) x = true
  · rw [if_pos h1]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨h, _, _, _⟩; exact absurd h1 h
  by_cases h2 : testBit' (pred.getD x 0) y = true
  · rw [if_neg h1, if_pos h2]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨_, h, _, _⟩; exact absurd h2 h
  by_cases h3 : (pred.getD x 0 &&& lnotN (bit x ||| bit y) n !=
                 pred.getD y 0 &&& lnotN (bit x ||| bit y) n) = true
  · rw [if_neg h1, if_neg h2, if_pos h3]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨_, _, h, _⟩
    rw [bne_iff_ne] at h3
    exact absurd h h3
  by_cases h4 : (succ.getD x 0 &&& lnotN (bit x ||| bit y) n !=
                 succ.getD y 0 &&& lnotN (bit x ||| bit y) n) = true
  · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    refine ⟨fun h => absurd h hYne, ?_⟩
    rintro ⟨_, _, _, h⟩
    rw [bne_iff_ne] at h4
    exact absurd h h4
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    refine ⟨fun _ => ⟨h1, h2, ?_, ?_⟩, fun _ => rfl⟩
    · rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h3
      exact h3
    · rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h4
      exact h4

/-- The outer loop body of `findSymmetricPair`. -/
private def symOuterBody (pred : Array Nat) (succ : Array Nat) (n : ℕ) :
    ℕ → Id (ForInStep (MProd (Option (Option (Nat × Nat))) PUnit)) :=
  fun x => do
    let r ← forIn (m := Id) (List.range' (x+1) (n - (x+1)))
      (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit)
      (fun y _ => symInnerBody pred succ n x y)
    match r.fst with
    | none => pure (ForInStep.yield ⟨none, PUnit.unit⟩)
    | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)

/-- Inner forIn's `.fst` is `none` or it `done`-extracted from a `y`
in the iteration range. -/
private lemma sym_inner_forIn_fst (pred : Array Nat) (succ : Array Nat)
    (n x : ℕ) (l : List ℕ) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit)
        (fun y _ => symInnerBody pred succ n x y)).fst = none ∨
    ∃ y ∈ l, (forIn (m := Id) l (⟨none, PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit)
        (fun y _ => symInnerBody pred succ n x y)).fst = some (some (x, y)) ∧
      symInnerBody pred succ n x y =
        pure (ForInStep.done ⟨some (some (x, y)), PUnit.unit⟩) := by
  induction l with
  | nil => left; rfl
  | cons y ys ih =>
    rw [List.forIn_cons]
    rcases symInnerBody_yield_or_done pred succ n x y with hy | hd
    · rw [hy]
      change ((forIn (m := Id) ys
        (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit) _ :
        MProd (Option (Option (Nat × Nat))) PUnit).fst = none) ∨ _
      rcases ih with hn | ⟨y', hy', hsome, hdone⟩
      · left; exact hn
      · right
        exact ⟨y', List.mem_cons_of_mem _ hy', hsome, hdone⟩
    · rw [hd]
      change (((⟨some (some (x, y)), PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit).fst :
        Option (Option (Nat × Nat))) = none) ∨ _
      right
      exact ⟨y, List.mem_cons_self, rfl, hd⟩

/-- The outer body returns `yield none` or `done (some (some (x, y)))`
for some `y` in the iteration range whose inner body is done. -/
private lemma symOuterBody_yield_or_done (pred : Array Nat) (succ : Array Nat)
    (n x : ℕ) :
    symOuterBody pred succ n x =
      pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit)) ∨
    ∃ y ∈ List.range' (x+1) (n - (x+1)),
      symInnerBody pred succ n x y =
        pure (ForInStep.done ⟨some (some (x, y)), PUnit.unit⟩) ∧
      symOuterBody pred succ n x =
        pure (ForInStep.done (⟨some (some (x, y)), PUnit.unit⟩ :
          MProd (Option (Option (Nat × Nat))) PUnit)) := by
  rcases sym_inner_forIn_fst pred succ n x (List.range' (x+1) (n - (x+1))) with
    hn | ⟨y, hy_mem, hsome, hdone⟩
  · left
    change (match (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
              (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit)
              (fun y _ => symInnerBody pred succ n x y) :
              MProd (Option (Option (Nat × Nat))) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option (Option (Nat × Nat))) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _
    rw [hn]
  · right
    refine ⟨y, hy_mem, hdone, ?_⟩
    change (match (forIn (m := Id) (List.range' (x+1) (n - (x+1)))
              (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit)
              (fun y _ => symInnerBody pred succ n x y) :
              MProd (Option (Option (Nat × Nat))) PUnit).fst with
          | none => (pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                      MProd (Option (Option (Nat × Nat))) PUnit)) : Id _)
          | some a => pure (ForInStep.done ⟨some a, PUnit.unit⟩)) = _
    rw [hsome]

/-- Imperative→functional reduction for `findSymmetricPair`. -/
private theorem findSymmetricPair_eq_outer_fst (pred : Array Nat) (n : ℕ) :
    Case3Enum.findSymmetricPair pred n =
      (match (forIn (m := Id) (List.range' 0 n)
        (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit)
        (fun x _ => symOuterBody pred (successorMasks pred n) n x)).fst with
       | none => none
       | some a => a) := by
  unfold Case3Enum.findSymmetricPair symOuterBody symInnerBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- The outer forIn `.fst` is `none` or `some (some (x, y))` with the
bit conditions satisfied for some `(x, y)` in range. -/
private lemma sym_outer_forIn_extract (pred : Array Nat) (n : ℕ) :
    (forIn (m := Id) (List.range' 0 n)
        (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit)
        (fun x _ => symOuterBody pred (successorMasks pred n) n x)).fst = none ∨
    ∃ x ∈ List.range' 0 n, ∃ y ∈ List.range' (x+1) (n - (x+1)),
      ¬ testBit' (pred.getD y 0) x = true ∧
      ¬ testBit' (pred.getD x 0) y = true ∧
      (pred.getD x 0 &&& lnotN (bit x ||| bit y) n) =
        (pred.getD y 0 &&& lnotN (bit x ||| bit y) n) ∧
      ((successorMasks pred n).getD x 0 &&& lnotN (bit x ||| bit y) n) =
        ((successorMasks pred n).getD y 0 &&& lnotN (bit x ||| bit y) n) := by
  set succ := successorMasks pred n with hsucc
  suffices aux : ∀ (lo : List ℕ),
      (forIn (m := Id) lo
          (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit)
          (fun x _ => symOuterBody pred succ n x)).fst = none ∨
      ∃ x ∈ lo, ∃ y ∈ List.range' (x+1) (n - (x+1)),
        ¬ testBit' (pred.getD y 0) x = true ∧
        ¬ testBit' (pred.getD x 0) y = true ∧
        (pred.getD x 0 &&& lnotN (bit x ||| bit y) n) =
          (pred.getD y 0 &&& lnotN (bit x ||| bit y) n) ∧
        (succ.getD x 0 &&& lnotN (bit x ||| bit y) n) =
          (succ.getD y 0 &&& lnotN (bit x ||| bit y) n)
    by exact aux (List.range' 0 n)
  intro lo
  induction lo with
  | nil => left; rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    rcases symOuterBody_yield_or_done pred succ n x with
      hy | ⟨y, hy_mem, h_inner_done, hd⟩
    · rw [hy]
      change ((forIn (m := Id) xs
        (⟨none, PUnit.unit⟩ : MProd (Option (Option (Nat × Nat))) PUnit) _ :
        MProd (Option (Option (Nat × Nat))) PUnit).fst = none) ∨ _
      rcases ih with hn | ⟨x', hx', y', hy', hb1, hb2, hb3, hb4⟩
      · left; exact hn
      · right
        exact ⟨x', List.mem_cons_of_mem _ hx', y', hy', hb1, hb2, hb3, hb4⟩
    · rw [hd]
      change (((⟨some (some (x, y)), PUnit.unit⟩ :
        MProd (Option (Option (Nat × Nat))) PUnit).fst :
        Option (Option (Nat × Nat))) = none) ∨ _
      right
      obtain ⟨hb1, hb2, hb3, hb4⟩ :=
        (symInnerBody_done_iff pred succ n x y).mp h_inner_done
      exact ⟨x, List.mem_cons_self, y, hy_mem, hb1, hb2, hb3, hb4⟩

/-! ## §2 — Bit conditions → `Symmetric` (succ_agree via hypothesis) -/

/-- Bit `b` of `cMask = lnotN (bit x ||| bit y) n` is `true` iff
`b < n ∧ b ≠ x ∧ b ≠ y` (assuming `x, y < n`). -/
private lemma testBit_cMask (n x y b : ℕ) (hx : x < n) (hy : y < n) :
    Nat.testBit (lnotN (bit x ||| bit y) n) b =
      (decide (b < n) && decide (b ≠ x) && decide (b ≠ y)) := by
  unfold lnotN
  rw [Nat.testBit_xor]
  have testBit_bit_eq : ∀ v b : ℕ, Nat.testBit (bit v) b = decide (b = v) := by
    intro v b
    unfold bit
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : v = b
    · subst h; simp
    · have h' : ¬ b = v := fun heq => h heq.symm
      simp [h, h']
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_or, testBit_bit_eq, testBit_bit_eq]
  by_cases h_bn : b < n
  · simp only [decide_eq_true h_bn, Bool.true_and]
    by_cases h_bx : b = x
    · subst h_bx; simp
    · by_cases h_by : b = y
      · subst h_by; simp [fun heq : b = x => h_bx heq]
      · simp [h_bx, h_by]
  · have h_bx : b ≠ x := fun h => h_bn (h ▸ hx)
    have h_by : b ≠ y := fun h => h_bn (h ▸ hy)
    simp [h_bn, h_bx, h_by]

/-- Bit-equality at masked positions. -/
private lemma masked_bit_eq {a b cMask z : ℕ}
    (h : a &&& cMask = b &&& cMask)
    (hz : Nat.testBit cMask z = true) :
    Nat.testBit a z = Nat.testBit b z := by
  have := congrArg (fun w => Nat.testBit w z) h
  simp only [Nat.testBit_and, hz, Bool.and_true] at this
  exact this

/-- **Bool→Prop lift of `findSymmetricPair`**. If
`findSymmetricPair pred n = some (x, y)` (equivalently `.isSome = true`),
there is a `Symmetric` witness in `Fin n × Fin n`.

Takes `successorMasks` bit-correctness as an explicit hypothesis. The
hypothesis discharge is split off as `mg-G3a-followup` per pc-b53a's
recommendation. -/
theorem findSymmetricPair_isSome_imp_symmetric_aux (pred : Array Nat) (n : ℕ)
    (h_succ : ∀ u v : ℕ, u < n → v < n →
      Nat.testBit ((Case3Enum.successorMasks pred n).getD u 0) v =
        testBit' (pred.getD v 0) u)
    (h : (Case3Enum.findSymmetricPair pred n).isSome = true) :
    ∃ x y : Fin n, Symmetric pred n x y := by
  rw [findSymmetricPair_eq_outer_fst] at h
  rcases sym_outer_forIn_extract pred n with hn |
    ⟨xn, hx_mem, yn, hy_mem, hb1, hb2, hb3, hb4⟩
  · rw [hn] at h
    cases h
  rw [List.mem_range'] at hx_mem
  obtain ⟨ix, hix, _⟩ := hx_mem
  have hxn_lt : xn < n := by omega
  rw [List.mem_range'] at hy_mem
  obtain ⟨iy, hiy, _⟩ := hy_mem
  have hyn_lt : yn < n := by omega
  refine ⟨⟨xn, hxn_lt⟩, ⟨yn, hyn_lt⟩, ?_⟩
  refine
    { ne := ?_
      not_xy := ?_
      not_yx := ?_
      pred_agree := ?_
      succ_agree := ?_ }
  · intro h_eq
    have h_xy : xn = yn := Fin.mk.inj_iff.mp h_eq
    omega
  · change ¬ testBit' (pred.getD yn 0) xn = true
    exact hb1
  · change ¬ testBit' (pred.getD xn 0) yn = true
    exact hb2
  · intro z hzx hzy
    change testBit' (pred.getD xn 0) z.val = true ↔
           testBit' (pred.getD yn 0) z.val = true
    have hz_ne_xn : z.val ≠ xn := fun h => hzx (Fin.ext h)
    have hz_ne_yn : z.val ≠ yn := fun h => hzy (Fin.ext h)
    have hcmask_z : Nat.testBit (lnotN (bit xn ||| bit yn) n) z.val = true := by
      rw [testBit_cMask _ _ _ _ hxn_lt hyn_lt]
      simp [z.isLt, hz_ne_xn, hz_ne_yn]
    have hbit_eq : Nat.testBit (pred.getD xn 0) z.val =
                   Nat.testBit (pred.getD yn 0) z.val :=
      masked_bit_eq hb3 hcmask_z
    rw [testBit'_eq_testBit, testBit'_eq_testBit, hbit_eq]
  · intro z hzx hzy
    change testBit' (pred.getD z.val 0) xn = true ↔
           testBit' (pred.getD z.val 0) yn = true
    have hz_ne_xn : z.val ≠ xn := fun h => hzx (Fin.ext h)
    have hz_ne_yn : z.val ≠ yn := fun h => hzy (Fin.ext h)
    have hcmask_z : Nat.testBit (lnotN (bit xn ||| bit yn) n) z.val = true := by
      rw [testBit_cMask _ _ _ _ hxn_lt hyn_lt]
      simp [z.isLt, hz_ne_xn, hz_ne_yn]
    have h_sx_sy_z : Nat.testBit ((successorMasks pred n).getD xn 0) z.val =
                     Nat.testBit ((successorMasks pred n).getD yn 0) z.val :=
      masked_bit_eq hb4 hcmask_z
    -- Apply the successorMasks bit-correctness hypothesis.
    rw [h_succ xn z.val hxn_lt z.isLt, h_succ yn z.val hyn_lt z.isLt]
      at h_sx_sy_z
    rw [h_sx_sy_z]

/-! ## §3 — `successorMasks` bit-correctness (A5-G3a-followup, `mg-792a`)

Discharges the explicit `h_succ` hypothesis of
`findSymmetricPair_isSome_imp_symmetric_aux`.  The pattern parallels
`BalancedLift.lean` §4: imperative `successorMasks` is reduced to a
nested `forIn` whose inner step is a gated `set!` of `bit v` into
`out[u]`.  We then track, by induction on the outer-loop prefix, the
position-by-position bit-state of the accumulator. -/

/-- Functional inner step of `successorMasks`: gated OR of `bit v`
into `out[u]`, conditioned on `testBit' pv u`. -/
private def succInnerStep (v pv u : ℕ) (out : Array Nat) : Array Nat :=
  if testBit' pv u then out.set! u (out.getD u 0 ||| bit v) else out

private lemma succInnerStep_size (v pv u : ℕ) (out : Array Nat) :
    (succInnerStep v pv u out).size = out.size := by
  unfold succInnerStep
  split_ifs <;> simp

/-- Bit-effect of `succInnerStep` at a specific (u', b') position. -/
private lemma succInnerStep_testBit (v pv u u' b' : ℕ) (out : Array Nat) :
    Nat.testBit ((succInnerStep v pv u out).getD u' 0) b' =
      (Nat.testBit (out.getD u' 0) b' ||
        (decide (u' = u) && decide (u < out.size) &&
         testBit' pv u && decide (b' = v))) := by
  unfold succInnerStep
  by_cases h : testBit' pv u = true
  · rw [if_pos h, getD_set!_eq]
    by_cases hu' : u' = u
    · subst hu'
      by_cases hsz : u' < out.size
      · rw [if_pos ⟨rfl, hsz⟩, Nat.testBit_or]
        have hbit : Nat.testBit (bit v) b' = decide (b' = v) := by
          unfold bit
          rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
          by_cases h_eq : v = b'
          · subst h_eq; simp
          · have h_eq' : ¬ b' = v := fun heq => h_eq heq.symm
            simp [h_eq, h_eq']
        rw [hbit]
        simp [h, hsz]
      · rw [if_neg (fun ⟨_, h2⟩ => hsz h2)]
        simp [h, hsz]
    · rw [if_neg (fun ⟨h1, _⟩ => hu' h1)]
      simp [hu']
  · rw [if_neg h]
    have hf : testBit' pv u = false := by
      cases hb : testBit' pv u
      · rfl
      · exact absurd hb h
    simp [hf]

/-- Imperative outer body of `successorMasks` (in imperative shape for
`rfl`-reduction; `succOuterBody_eq` gives the functional form). -/
private def succOuterBody (pred : Array Nat) (n : ℕ) :
    Nat → Array Nat → Id (ForInStep (Array Nat)) :=
  fun v acc =>
    (do
      pure PUnit.unit
      let r ← (forIn (m := Id) (List.range' 0 n) acc (fun u acc' =>
        if testBit' (pred.getD v 0) u then
          (do pure PUnit.unit;
              pure (ForInStep.yield (acc'.set! u (acc'.getD u 0 ||| bit v))) : Id _)
        else
          (do pure PUnit.unit; pure (ForInStep.yield acc') : Id _)) : Id _)
      pure (ForInStep.yield r))

/-- `successorMasks` reduces to a `forIn` over its outer body. -/
private lemma successorMasks_imperative_eq (pred : Array Nat) (n : ℕ) :
    Case3Enum.successorMasks pred n =
      forIn (m := Id) (List.range' 0 n)
        (Array.replicate n 0 : Array Nat) (succOuterBody pred n) := by
  classical
  unfold Case3Enum.successorMasks succOuterBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- Inner imperative body equals `pure (yield (succInnerStep ...))`. -/
private lemma succ_inner_body_eq (v pv u : ℕ) (out : Array Nat) :
    (if testBit' pv u then
      (do pure PUnit.unit;
          pure (ForInStep.yield (out.set! u (out.getD u 0 ||| bit v))) : Id _)
    else
      (do pure PUnit.unit; pure (ForInStep.yield out) : Id _)) =
    (pure (ForInStep.yield (succInnerStep v pv u out)) : Id _) := by
  unfold succInnerStep
  split_ifs <;> rfl

/-- Functional outer step. -/
private def succOuterStep (pred : Array Nat) (n v : ℕ) (out : Array Nat) :
    Array Nat :=
  forIn (m := Id) (List.range' 0 n) out (fun u acc =>
    (pure (ForInStep.yield (succInnerStep v (pred.getD v 0) u acc)) : Id _))

private lemma succOuterStep_size (pred : Array Nat) (n v : ℕ) (out : Array Nat) :
    (succOuterStep pred n v out).size = out.size := by
  unfold succOuterStep
  generalize hL : (List.range' 0 n) = lo
  clear hL
  induction lo generalizing out with
  | nil => rfl
  | cons u us ih =>
    rw [List.forIn_cons]
    show (forIn (m := Id) us
      (succInnerStep v (pred.getD v 0) u out) _).size = out.size
    rw [ih]
    exact succInnerStep_size ..

/-- Outer body equals functional outer step under `pure (yield ...)`. -/
private lemma succOuterBody_eq (pred : Array Nat) (n v : ℕ) (out : Array Nat) :
    succOuterBody pred n v out =
      (pure (ForInStep.yield (succOuterStep pred n v out)) : Id _) := by
  unfold succOuterBody succOuterStep
  have hbody_eq :
    (fun (u : Nat) (acc' : Array Nat) =>
      (if testBit' (pred.getD v 0) u then
        (do pure PUnit.unit;
            pure (ForInStep.yield (acc'.set! u (acc'.getD u 0 ||| bit v))) : Id _)
      else
        (do pure PUnit.unit; pure (ForInStep.yield acc') : Id _) :
        Id (ForInStep (Array Nat)))) =
    fun u acc' =>
      (pure (ForInStep.yield
        (succInnerStep v (pred.getD v 0) u acc')) : Id _) := by
    funext u acc'
    exact succ_inner_body_eq v _ u acc'
  rw [hbody_eq]
  rfl

/-- `forIn`-cons reduction for the outer body. -/
private lemma succ_outer_forIn_cons (pred : Array Nat) (n v : ℕ)
    (init : Array Nat) (vs : List ℕ) :
    (forIn (m := Id) (v :: vs) init (succOuterBody pred n) : Array Nat) =
      forIn (m := Id) vs (succOuterStep pred n v init) (succOuterBody pred n) := by
  rw [List.forIn_cons, succOuterBody_eq]
  rfl

/-- Bit-effect of the inner `forIn`: at position `(u', b')`, OR-ing over
the iteration sets bit `v` of `out[u']` whenever `u' ∈ lo` (so `u'` is
visited) and `testBit' pv u'` (so the gate fires) and `b' = v`. -/
private lemma succ_inner_forIn_testBit (pred : Array Nat) (n v : ℕ) :
    ∀ (lo : List ℕ) (init : Array Nat),
    init.size = n →
    (∀ u ∈ lo, u < n) →
    ∀ u' b' : ℕ,
    Nat.testBit ((forIn (m := Id) lo init (fun u acc =>
        (pure (ForInStep.yield
          (succInnerStep v (pred.getD v 0) u acc)) : Id _))).getD u' 0) b' =
      (Nat.testBit (init.getD u' 0) b' ||
        (decide (u' ∈ lo) && testBit' (pred.getD v 0) u' && decide (b' = v))) := by
  intro lo
  induction lo with
  | nil =>
    intro init _ _ u' b'
    show Nat.testBit (init.getD u' 0) b' = _
    simp
  | cons u us ih =>
    intro init hsize hbound u' b'
    rw [List.forIn_cons]
    show Nat.testBit ((forIn (m := Id) us
      (succInnerStep v (pred.getD v 0) u init) _).getD u' 0) b' = _
    have hu_lt : u < n := hbound u List.mem_cons_self
    have hbound' : ∀ x ∈ us, x < n := fun x hx =>
      hbound x (List.mem_cons_of_mem _ hx)
    have hsize' : (succInnerStep v (pred.getD v 0) u init).size = n := by
      rw [succInnerStep_size]; exact hsize
    rw [ih (succInnerStep v (pred.getD v 0) u init) hsize' hbound' u' b',
        succInnerStep_testBit, hsize]
    have h_u_size : decide (u < n) = true := decide_eq_true hu_lt
    rw [h_u_size]
    by_cases h_u_eq : u' = u
    · subst h_u_eq
      have h1 : decide (u' = u') = true := decide_eq_true rfl
      have h2 : decide (u' ∈ u' :: us) = true := by
        have : u' ∈ u' :: us := List.mem_cons_self
        exact decide_eq_true this
      rw [h1, h2]
      cases h_init : Nat.testBit (init.getD u' 0) b' <;>
      cases h_pv : testBit' (pred.getD v 0) u' <;>
      cases h_bv : decide (b' = v) <;>
      cases h_uss : decide (u' ∈ us) <;> rfl
    · have h1 : decide (u' = u) = false := decide_eq_false h_u_eq
      have h2 : decide (u' ∈ u :: us) = decide (u' ∈ us) := by
        by_cases hin : u' ∈ us
        · have : u' ∈ u :: us := List.mem_cons_of_mem _ hin
          rw [decide_eq_true this, decide_eq_true hin]
        · have hnotin : u' ∉ u :: us := by
            intro hh
            rcases List.mem_cons.mp hh with h_eq | h_inus
            · exact h_u_eq h_eq
            · exact hin h_inus
          rw [decide_eq_false hnotin, decide_eq_false hin]
      rw [h1, h2]
      simp [Bool.false_and]

/-- Bit-effect of one outer step. -/
private lemma succOuterStep_testBit (pred : Array Nat) (n v u' b' : ℕ)
    (hu : u' < n) (init : Array Nat) (hsize : init.size = n) :
    Nat.testBit ((succOuterStep pred n v init).getD u' 0) b' =
      (Nat.testBit (init.getD u' 0) b' ||
        (testBit' (pred.getD v 0) u' && decide (b' = v))) := by
  unfold succOuterStep
  rw [succ_inner_forIn_testBit pred n v (List.range' 0 n) init hsize
        (fun u hu_in => by
          have := List.mem_range'.mp hu_in
          omega) u' b']
  have h_in : u' ∈ List.range' 0 n :=
    List.mem_range'.mpr ⟨u', hu, by omega⟩
  rw [decide_eq_true h_in, Bool.true_and]

/-- The outer-loop invariant, generalized in `lo` (the prefix to process)
and `init` (the accumulator at the start of `lo`). -/
private lemma succ_outer_forIn_aux (pred : Array Nat) (n : ℕ) :
    ∀ (lo : List ℕ) (init : Array Nat),
    lo.Nodup →
    (∀ v ∈ lo, v < n) →
    init.size = n →
    (∀ u' b' : ℕ, u' < n → b' ∈ lo →
      Nat.testBit (init.getD u' 0) b' = false) →
    let result : Array Nat := forIn (m := Id) lo init (succOuterBody pred n)
    result.size = n ∧
    ∀ u' b' : ℕ, u' < n → b' < n →
      Nat.testBit (result.getD u' 0) b' =
        if b' ∈ lo then testBit' (pred.getD b' 0) u'
        else Nat.testBit (init.getD u' 0) b' := by
  intro lo
  induction lo with
  | nil =>
    intro init _ _ hsize _
    refine ⟨hsize, ?_⟩
    intros u' b' _ _
    show Nat.testBit (init.getD u' 0) b' = _
    simp
  | cons v vs ih =>
    intro init hnodup hbound hsize hinit
    show let result : Array Nat :=
            forIn (m := Id) (v :: vs) init (succOuterBody pred n)
         result.size = n ∧ _
    rw [show (forIn (m := Id) (v :: vs) init (succOuterBody pred n) :
              Array Nat) =
            forIn (m := Id) vs (succOuterStep pred n v init)
              (succOuterBody pred n) from
        succ_outer_forIn_cons pred n v init vs]
    have hnodup' : vs.Nodup := hnodup.of_cons
    have hv_notin : v ∉ vs := List.Nodup.notMem hnodup
    have hv_lt : v < n := hbound v List.mem_cons_self
    have hbound' : ∀ x ∈ vs, x < n := fun x hx =>
      hbound x (List.mem_cons_of_mem _ hx)
    have hsize' : (succOuterStep pred n v init).size = n := by
      rw [succOuterStep_size]; exact hsize
    have hinit' : ∀ u' b' : ℕ, u' < n → b' ∈ vs →
        Nat.testBit ((succOuterStep pred n v init).getD u' 0) b' = false := by
      intros u' b' hu' hb'_in_vs
      have h_b'_ne_v : b' ≠ v := fun h_eq => hv_notin (h_eq ▸ hb'_in_vs)
      have h_b'_in_lo : b' ∈ v :: vs := List.mem_cons_of_mem _ hb'_in_vs
      rw [succOuterStep_testBit pred n v u' b' hu' init hsize,
          hinit u' b' hu' h_b'_in_lo]
      simp [decide_eq_false h_b'_ne_v]
    obtain ⟨hsize_result, h_result⟩ := ih _ hnodup' hbound' hsize' hinit'
    refine ⟨hsize_result, ?_⟩
    intros u' b' hu' hb'
    rw [h_result u' b' hu' hb']
    by_cases hb'_in_vs : b' ∈ vs
    · rw [if_pos hb'_in_vs, if_pos (List.mem_cons_of_mem _ hb'_in_vs)]
    · rw [if_neg hb'_in_vs,
          succOuterStep_testBit pred n v u' b' hu' init hsize]
      by_cases h_b'_eq_v : b' = v
      · subst h_b'_eq_v
        have h_in : b' ∈ b' :: vs := List.mem_cons_self
        rw [if_pos h_in, hinit u' b' hu' h_in]
        simp
      · have h_b'_notin : b' ∉ v :: vs := by
          intro hh
          rcases List.mem_cons.mp hh with h_eq | h_in
          · exact h_b'_eq_v h_eq
          · exact hb'_in_vs h_in
        rw [if_neg h_b'_notin]
        simp [decide_eq_false h_b'_eq_v]

/-- **Bit-correctness of `Case3Enum.successorMasks`**.

For `u, v < n`,
`Nat.testBit ((successorMasks pred n).getD u 0) v = testBit' (pred.getD v 0) u`.

Discharges the explicit `h_succ` hypothesis of
`findSymmetricPair_isSome_imp_symmetric_aux`. -/
theorem successorMasks_testBit (pred : Array Nat) (n u v : ℕ)
    (hu : u < n) (hv : v < n) :
    Nat.testBit ((Case3Enum.successorMasks pred n).getD u 0) v =
      testBit' (pred.getD v 0) u := by
  rw [successorMasks_imperative_eq]
  have h_init_size : (Array.replicate n 0 : Array Nat).size = n :=
    Array.size_replicate
  have h_init_zero : ∀ u' b' : ℕ, u' < n → b' ∈ List.range' 0 n →
      Nat.testBit ((Array.replicate n 0 : Array Nat).getD u' 0) b' = false := by
    intros u' b' _ _
    have h_getD : (Array.replicate n 0 : Array Nat).getD u' 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [h_getD]
    exact Nat.zero_testBit _
  have hnodup : (List.range' 0 n).Nodup := List.nodup_range'
  have hbound : ∀ x ∈ List.range' 0 n, x < n := fun x hx => by
    have := List.mem_range'.mp hx
    omega
  obtain ⟨_, hresult⟩ := succ_outer_forIn_aux pred n (List.range' 0 n)
    (Array.replicate n 0) hnodup hbound h_init_size h_init_zero
  rw [hresult u v hu hv]
  have hv_in : v ∈ List.range' 0 n :=
    List.mem_range'.mpr ⟨v, hv, by omega⟩
  rw [if_pos hv_in]

/-- **Bool→Prop lift of `findSymmetricPair`** (no `_aux`).

Wraps `findSymmetricPair_isSome_imp_symmetric_aux` with the
`successorMasks` bit-correctness hypothesis already discharged. -/
theorem findSymmetricPair_isSome_imp_symmetric (pred : Array Nat) (n : ℕ)
    (h : (Case3Enum.findSymmetricPair pred n).isSome = true) :
    ∃ x y : Fin n, Symmetric pred n x y :=
  findSymmetricPair_isSome_imp_symmetric_aux pred n
    (fun u v hu hv => successorMasks_testBit pred n u v hu hv) h

end Case3Enum
end Step8
end OneThird
