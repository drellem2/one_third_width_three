/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — A5-G1: `enumPosetsFor` Bool→Prop iteration theorem
(`mg-580e` partial; `mg-b487` completion)

`Case3Enum.enumPosetsFor` is a `Bool := Id.run do` whose for-loop
body, after the `mg-b487` refactor of `Case3Enum.lean §5`, is a
single-mutable per-mask check chain calling `enumPredAtMaskOf`,
`closureCanonical`, `findSymmetricPair`, `irreducible`,
`hasAdjacentIncomp`, `hasBalancedPairSlow`. The two-mutable-variable
partition phase is now factored out into the standalone helper
`Case3Enum.enumPartition` (which `enumPredAtMaskOf` consumes).

This file packages the Bool↔Prop bridge:

* §1 — `enumOuterBody`, the per-mask `MProd (Option Bool) PUnit`
  body of the outer `for mask in [0:1 <<< nfree]` loop.
* §2 — `enumOuterBody_yield_or_done` / `enumOuterBody_done_iff`:
  the body's two-state behaviour and the precise condition under
  which it triggers the early `return-false` branch.
* §3 — `enumOuter_forIn_fst_cases` /
  `enumOuter_forIn_fst_some_false_iff`: the outer `forIn`'s `.fst`
  characterization (always in `{none, some false}`; `= some false`
  iff some `mask` triggers `done`).
* §4 — `enumPosetsFor_eq_outer_fst`, the
  imperative→functional reduction reducing `enumPosetsFor` to the
  `forIn` over masks via the now-trivial `unfold + rfl` pattern.
* §5 — `enumPosetsFor_iter_balanced`, the headline iteration
  theorem (A5-G1 deliverable): for every `mask` in range satisfying
  the four Bool gates, `hasBalancedPairSlow` is forced to `true`.
* §6 — `hasBalancedPair_of_findSymmetricPair_some`, the trivial
  fast-path companion (when `findSymmetricPair = some _`,
  `hasBalancedPair = true` by definition).

## Pattern

The refactor in `Case3Enum.lean` removed the multi-mutable elaboration
mismatch identified during `mg-580e`: the per-mask body now has only
one mutable variable (the implicit `MProd (Option Bool) PUnit` state),
matching the same `forIn`-state shape used by `slowOuterBody`
(`BalancedLift.lean §7`), `adjOuterBody` (`AdjIncompBridge.lean §1`),
and `irrOuterBody` (`IrreducibleBridge.lean §6`).

## References

* B1' (`mg-a08f`): `Case3Enum/IrreducibleBridge.lean §6`.
* B2 (`mg-e9d6`): `Case3Enum/AdjIncompBridge.lean §1`.
* BalancedLift §4 + §7: warshall + `hasBalancedPairSlow` reductions.
* `docs/a5-glue-status.md` §3 (recommended split): G1 deliverable.
-/

namespace OneThird
namespace Step8.Case3Enum

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false

/-! ### §1 — Outer-loop body factoring

The body of `for mask in [0:1 <<< nfree] do …` in `enumPosetsFor`,
elaborated as a `MProd (Option Bool) PUnit`-state forIn body. -/

/-- Outer mask-loop body: build `pred` at iteration `mask`, then
run the four early-skip Bool gates plus the
`hasBalancedPairSlow`-`return-false` check. -/
def enumOuterBody (w : Nat) (bs : List Nat) (mask : Nat)
    (_r : MProd (Option Bool) PUnit) :
    Id (ForInStep (MProd (Option Bool) PUnit)) :=
  if !closureCanonical (enumPredAtMaskOf w bs mask) mask
        (enumFreeUVOf w bs) then
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)
  else if (findSymmetricPair (enumPredAtMaskOf w bs mask)
        (enumNOf bs)).isSome then
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)
  else if !irreducible (enumPredAtMaskOf w bs mask) (offsetsOf bs) then
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)
  else if !hasAdjacentIncomp (enumPredAtMaskOf w bs mask)
        (offsetsOf bs) then
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)
  else if !hasBalancedPairSlow (enumPredAtMaskOf w bs mask)
        (enumNOf bs) then
    pure (ForInStep.done ⟨some false, PUnit.unit⟩)
  else
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)

/-! ### §2 — Yield-or-done case-split and `done`-iff -/

/-- The outer body always either yields `none` (continue) or returns
`done ⟨some false, ()⟩` (early `return false` after a failing
`hasBalancedPairSlow`). -/
private lemma enumOuterBody_yield_or_done (w : Nat) (bs : List Nat)
    (mask : Nat) (r : MProd (Option Bool) PUnit) :
    enumOuterBody w bs mask r =
        pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) ∨
    enumOuterBody w bs mask r =
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) := by
  unfold enumOuterBody
  by_cases h1 :
    (!closureCanonical (enumPredAtMaskOf w bs mask) mask
        (enumFreeUVOf w bs)) = true
  · left; rw [if_pos h1]
  by_cases h2 : ((findSymmetricPair (enumPredAtMaskOf w bs mask)
        (enumNOf bs)).isSome) = true
  · left; rw [if_neg h1, if_pos h2]
  by_cases h3 :
    (!irreducible (enumPredAtMaskOf w bs mask) (offsetsOf bs)) = true
  · left; rw [if_neg h1, if_neg h2, if_pos h3]
  by_cases h4 :
    (!hasAdjacentIncomp (enumPredAtMaskOf w bs mask) (offsetsOf bs)) = true
  · left; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  by_cases h5 :
    (!hasBalancedPairSlow (enumPredAtMaskOf w bs mask) (enumNOf bs)) = true
  · right; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
  · left; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- The outer body returns `done ⟨some false, ()⟩` iff all four Bool
gates pass at iteration `mask` and `hasBalancedPairSlow` fails. -/
private lemma enumOuterBody_done_iff (w : Nat) (bs : List Nat)
    (mask : Nat) (r : MProd (Option Bool) PUnit) :
    enumOuterBody w bs mask r =
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) ↔
    closureCanonical (enumPredAtMaskOf w bs mask) mask
        (enumFreeUVOf w bs) = true ∧
    (findSymmetricPair (enumPredAtMaskOf w bs mask) (enumNOf bs)).isSome
        = false ∧
    irreducible (enumPredAtMaskOf w bs mask) (offsetsOf bs) = true ∧
    hasAdjacentIncomp (enumPredAtMaskOf w bs mask) (offsetsOf bs) = true ∧
    hasBalancedPairSlow (enumPredAtMaskOf w bs mask) (enumNOf bs)
        = false := by
  unfold enumOuterBody
  -- Bool helper: (!b) = true ↔ b = false.
  have not_eq_true_iff_eq_false : ∀ (b : Bool), (!b) = true ↔ b = false := by
    intro b; cases b <;> decide
  split_ifs with h1 h2 h3 h4 h5
  · -- Case 1: !closureCanonical ... = true ⇒ closureCanonical ... = false.
    rw [not_eq_true_iff_eq_false] at h1
    refine ⟨?_, ?_⟩
    · intro h; cases h
    · rintro ⟨hc, _, _, _, _⟩; rw [h1] at hc; cases hc
  · -- Case 2: closureCanonical ok, (findSymmetricPair ...).isSome = true.
    refine ⟨?_, ?_⟩
    · intro h; cases h
    · rintro ⟨_, hs, _, _, _⟩; rw [hs] at h2; cases h2
  · -- Case 3: !irreducible ... = true ⇒ irreducible ... = false.
    rw [not_eq_true_iff_eq_false] at h3
    refine ⟨?_, ?_⟩
    · intro h; cases h
    · rintro ⟨_, _, hi, _, _⟩; rw [h3] at hi; cases hi
  · -- Case 4: !hasAdjacentIncomp ... = true ⇒ hasAdjacentIncomp ... = false.
    rw [not_eq_true_iff_eq_false] at h4
    refine ⟨?_, ?_⟩
    · intro h; cases h
    · rintro ⟨_, _, _, ha, _⟩; rw [h4] at ha; cases ha
  · -- Case 5: gates pass; !hasBalancedPairSlow = true ⇒ slow = false. THE DONE CASE.
    rw [not_eq_true_iff_eq_false] at h5
    have hcg : closureCanonical (enumPredAtMaskOf w bs mask) mask
                (enumFreeUVOf w bs) = true := by
      cases hb : closureCanonical (enumPredAtMaskOf w bs mask) mask
                  (enumFreeUVOf w bs)
      · exfalso; apply h1; rw [hb]; rfl
      · rfl
    have hsf : (findSymmetricPair (enumPredAtMaskOf w bs mask)
                (enumNOf bs)).isSome = false := by
      cases hb : (findSymmetricPair (enumPredAtMaskOf w bs mask)
                  (enumNOf bs)).isSome
      · rfl
      · exact absurd hb h2
    have hig : irreducible (enumPredAtMaskOf w bs mask) (offsetsOf bs)
                = true := by
      cases hb : irreducible (enumPredAtMaskOf w bs mask) (offsetsOf bs)
      · exfalso; apply h3; rw [hb]; rfl
      · rfl
    have hag : hasAdjacentIncomp (enumPredAtMaskOf w bs mask)
                (offsetsOf bs) = true := by
      cases hb : hasAdjacentIncomp (enumPredAtMaskOf w bs mask)
                  (offsetsOf bs)
      · exfalso; apply h4; rw [hb]; rfl
      · rfl
    exact ⟨fun _ => ⟨hcg, hsf, hig, hag, h5⟩, fun _ => rfl⟩
  · -- Case 6: nothing fired; LHS is yield ≠ done, RHS demands done.
    refine ⟨?_, ?_⟩
    · intro h; cases h
    · rintro ⟨_, _, _, _, hb⟩; apply h5; rw [hb]; rfl

/-! ### §3 — Outer forIn `.fst = some false` characterization -/

/-- The outer forIn's `.fst` is in `{none, some false}` (never
`some true`), since the body only `yield`s `none` or `done`s `some
false`. -/
private lemma enumOuter_forIn_fst_cases (w : Nat) (bs : List Nat)
    (l : List Nat) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun mask r => enumOuterBody w bs mask r)).fst = none ∨
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun mask r => enumOuterBody w bs mask r)).fst = some false := by
  induction l with
  | nil => left; rfl
  | cons mask ms ih =>
    rw [List.forIn_cons]
    rcases enumOuterBody_yield_or_done w bs mask
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) with hy | hd
    · rw [hy]
      change ((forIn (m := Id) ms
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = none) ∨ _ = some false
      exact ih
    · rw [hd]; right; rfl

/-- The outer forIn's `.fst = some false` iff some `mask ∈ l` triggers
the outer body's `done` branch. -/
private lemma enumOuter_forIn_fst_some_false_iff (w : Nat) (bs : List Nat)
    (l : List Nat) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun mask r => enumOuterBody w bs mask r)).fst = some false ↔
    ∃ mask ∈ l, enumOuterBody w bs mask
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) =
      pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                              MProd (Option Bool) PUnit)) := by
  induction l with
  | nil =>
    show ((⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit).fst = some false) ↔ _
    simp
  | cons mask ms ih =>
    rw [List.forIn_cons]
    rcases enumOuterBody_yield_or_done w bs mask
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) with hy | hd
    · rw [hy]
      change (forIn (m := Id) ms
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = some false ↔ _
      rw [ih]
      constructor
      · rintro ⟨m', hmem, hb⟩
        exact ⟨m', List.mem_cons_of_mem _ hmem, hb⟩
      · rintro ⟨m', hmem, hb⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · rw [hy] at hb
          exact absurd hb (fun h => by cases h)
        · exact ⟨m', hmem', hb⟩
    · rw [hd]
      change (((⟨some false, PUnit.unit⟩ : MProd (Option Bool) PUnit).fst :
                Option Bool) = some false) ↔ _
      refine ⟨fun _ => ⟨mask, ?_, hd⟩, fun _ => rfl⟩
      exact List.mem_cons_self

/-! ### §4 — Imperative→functional reduction of `enumPosetsFor` -/

/-- **Imperative→functional reduction** for `enumPosetsFor`.
After the `mg-b487` refactor of `Case3Enum.lean §5`, the body of the
outer `for mask in [0:1 <<< nfree]` loop matches `enumOuterBody` on
the nose, so the reduction is just `unfold + rfl` (modulo the
`Std.Legacy.Range.forIn_eq_forIn_range'` rewrite that converts the
`Range`-driven `forIn` to a `List.range'`-driven one). -/
private theorem enumPosetsFor_eq_outer_fst (w : Nat) (bs : List Nat) :
    enumPosetsFor w bs =
      (if enumNfreeOf w bs > 27 then false
       else
         match (forIn (m := Id) (List.range' 0 (1 <<< enumNfreeOf w bs))
           (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
           (fun mask r => enumOuterBody w bs mask r)).fst with
         | none => true
         | some a => a) := by
  unfold enumPosetsFor enumOuterBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-! ### §5 — Headline iteration theorem -/

/-- **A5-G1 headline (`mg-b487`)**: `enumPosetsFor`-iteration theorem
for the slow-path branch.

If `enumPosetsFor w bs = true` and at iteration `mask` the four Bool
gates are satisfied (`closureCanonical`, no symmetric pair,
`irreducible`, `hasAdjacentIncomp`), then `hasBalancedPairSlow`
*must* return `true` at this iteration — otherwise the loop body
would have triggered `return false`, contradicting the hypothesis.

The hypothesis `hmask : mask < 1 <<< enumNfreeOf w bs` is the
loop-range membership in `List.range' 0 (1 <<< enumNfreeOf w bs)`.
The hypothesis `enumNfreeOf w bs ≤ 27` is implicit in `h` (otherwise
the early `if nfree > 27 then return false` would have fired and `h`
would contradict). -/
theorem enumPosetsFor_iter_balanced
    (w : Nat) (bs : List Nat) (h : enumPosetsFor w bs = true)
    (mask : Nat) (hmask : mask < 1 <<< enumNfreeOf w bs)
    (h_canon : closureCanonical (enumPredAtMaskOf w bs mask) mask
      (enumFreeUVOf w bs) = true)
    (h_sym : (findSymmetricPair (enumPredAtMaskOf w bs mask)
      (enumNOf bs)).isSome = false)
    (h_irr : irreducible (enumPredAtMaskOf w bs mask)
      (offsetsOf bs) = true)
    (h_adj : hasAdjacentIncomp (enumPredAtMaskOf w bs mask)
      (offsetsOf bs) = true) :
    hasBalancedPairSlow (enumPredAtMaskOf w bs mask) (enumNOf bs)
      = true := by
  -- Step 1: Reduce `enumPosetsFor` to its outer-`forIn` form.
  rw [enumPosetsFor_eq_outer_fst] at h
  -- Step 2: Discharge `enumNfreeOf w bs ≤ 27` from `h`.
  by_cases hN : enumNfreeOf w bs > 27
  · -- The early-return branch fires; `h : false = true`, contradiction.
    rw [if_pos hN] at h; cases h
  rw [if_neg hN] at h
  -- `h` now says: match (forIn …).fst with | none => true | some a => a = true.
  -- Combined with the `enumOuter_forIn_fst_cases` fact that
  -- `.fst ∈ {none, some false}`, this forces `.fst = none`
  -- (the only value that yields `true` from the match).
  have hcase := enumOuter_forIn_fst_cases w bs
    (List.range' 0 (1 <<< enumNfreeOf w bs))
  rcases hcase with hnone | hsf
  · -- `.fst = none`: no mask triggered `done`, which is what we need.
    have h_no_done : ∀ m ∈ List.range' 0 (1 <<< enumNfreeOf w bs),
        enumOuterBody w bs m
          (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) ≠
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) := by
      intro m hm hbody
      have h_some_false :
          (forIn (m := Id) (List.range' 0 (1 <<< enumNfreeOf w bs))
                (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
                (fun mask r => enumOuterBody w bs mask r)).fst = some false :=
        (enumOuter_forIn_fst_some_false_iff w bs _).mpr ⟨m, hm, hbody⟩
      rw [hnone] at h_some_false
      cases h_some_false
    -- Step 3: Specialize to our `mask`.
    have hmem : mask ∈ List.range' 0 (1 <<< enumNfreeOf w bs) := by
      rw [List.mem_range'_1]
      exact ⟨Nat.zero_le _, by simpa using hmask⟩
    have h_no := h_no_done mask hmem
    -- Step 4: If `hasBalancedPairSlow` returned `false`, the body would
    -- `done`, contradicting `h_no`.
    by_contra hslow
    rw [Bool.not_eq_true] at hslow
    apply h_no
    exact (enumOuterBody_done_iff w bs mask
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)).mpr
      ⟨h_canon, h_sym, h_irr, h_adj, hslow⟩
  · -- `.fst = some false`: match returns `false`, contradicting `h`.
    rw [hsf] at h
    cases h

/-! ### §6 — Companion fast-path form -/

/-- Trivial fast-path companion: when `findSymmetricPair = some _`,
`hasBalancedPair = true` regardless of the slow path.  The
nontrivial half — `findSymmetricPair pred n = some (x, y) → ∃ x' y',
Symmetric pred n x' y'` — belongs to A5-G2 (gap (B) of
`docs/a5-glue-status.md`); this companion is just the Bool-level
identity. -/
theorem hasBalancedPair_of_findSymmetricPair_some
    (pred : Array Nat) (n : Nat) {p : Nat × Nat}
    (h_sym : findSymmetricPair pred n = some p) :
    hasBalancedPair pred n = true := by
  unfold hasBalancedPair
  rw [h_sym]

end Step8.Case3Enum
end OneThird
