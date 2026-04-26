/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — A5-G1: `enumPosetsFor` Prop-level reduction (imperative loop unrolling)
(`mg-580e`)

`Case3Enum.enumPosetsFor` is a `Bool := Id.run do` whose body has two
imperative phases: (i) a partition phase with **four nested for-loops**
and **two mutable variables** (`freeUV` / `forcedUV`); (ii) a per-mask
phase with two nested for-loops and a single mutable `pred`, gated by
`closureCanonical`/`findSymmetricPair`/`irreducible`/`hasAdjacentIncomp`
checks plus a `hasBalancedPairSlow`-`return-false` final test.

This file packages the *building blocks* for the `enumPosetsFor`
Bool→Prop bridge: per-mask body factoring, the yield-or-done case
analysis on the body, the outer `forIn`-`.fst` characterization, and a
trivial fast-path companion (`hasBalancedPair_of_findSymmetricPair_some`).

## What landed

* §1 — Pure-form definitions matching the imperative pieces:
  `enumNOf`, `enumPartition`, `enumFreeUVOf`, `enumForcedUVOf`,
  `enumNfreeOf`, `enumPredPreWarshallOf`, `enumPredAtMaskOf`.
* §2 — `enumOuterBody`, the per-mask body of the outer
  `for mask in [0:1 <<< nfree]` loop, factored as `Id (ForInStep
  (MProd (Option Bool) PUnit))`.
* §3 — `enumOuterBody_yield_or_done` and `enumOuterBody_done_iff`:
  the body's two-state behaviour and the precise condition under
  which it triggers the early `return-false` (`done ⟨some false, ()⟩`).
* §4 — `enumOuter_forIn_fst_cases` and
  `enumOuter_forIn_fst_some_false_iff`: the outer `forIn`'s `.fst`
  characterization (always in `{none, some false}`; `= some false`
  iff some `mask` triggers `done`).
* §5 — `hasBalancedPair_of_findSymmetricPair_some`: the trivial
  fast-path companion claim (when `findSymmetricPair = some _`,
  `hasBalancedPair = true` by definition).

## What did NOT land — paper vs formalization gap

The headline iteration theorem `enumPosetsFor_iter_balanced`
(spec'd in `docs/a5-glue-status.md` as A5-G1's deliverable) requires
an imperative→functional reduction of `enumPosetsFor` to a clean
`forIn` over masks calling `enumOuterBody`.  The analogous
reductions for `irreducible` / `hasAdjacentIncomp` / `warshall` /
`hasBalancedPairSlow` (in
`Case3Enum/IrreducibleBridge.lean §6`,
`Case3Enum/AdjIncompBridge.lean §1`,
`Case3Enum/BalancedLift.lean §4 + §7`) all use the
`unfold + simp [Std.Legacy.Range.forIn_eq_forIn_range', …] + rfl`
pattern.  This works for those four because their imperative bodies
have **at most one mutable variable** in the outermost loop.

`enumPosetsFor`'s body has **two mutable variables** (`freeUV` /
`forcedUV`) carried through four nested for-loops in the partition
phase.  Lean elaborates such multi-mut do-blocks as `forIn` over an
`MProd`-state, with a slot ordering that depends on Lean's internal
heuristics — *not* declaration order.  Empirically (build trace,
`mg-580e` polecat session): the elaborated form returns
`pure (r.snd, r.fst)` from `return (freeUV, forcedUV)`, indicating
`r.fst = forcedUV` and `r.snd = freeUV`, despite `freeUV` being
declared first.  When this is composed with the per-helper unfolds
of `enumPartition` / `enumFreeUVOf` / `enumForcedUVOf` (each of
which inlines the partition body), the resulting RHS expression has
*multiple* copies of the partition for-loop, while the LHS (from
`enumPosetsFor` directly) has only *one* inline copy.  The `rfl`
between the LHS and a factored RHS therefore fails: the multi-mut
elaboration mismatch propagates through all the unfolds.

The B1' / B2 / B-§7 patterns do **not** generalize to this
multi-mut, multi-helper setting without additional infrastructure:

* Either a refactoring of `enumPosetsFor` (modify
  `Case3Enum.lean`) to call an auxiliary that takes
  `(freeUV, forcedUV)` as a parameter — invasive, scope-creep
  outside `mg-580e`.
* Or a generic `forIn`-with-`MProd`-state extraction lemma that
  decomposes `(.fst, .snd)` projections through the multi-mut
  do-block elaboration — does not exist in mathlib for the
  `MProd (Array …) (Array …)` shape we need.
* Or a manual `Id.forIn_invariant`-style invariant chain through
  all four nested for-loops in the partition, threading the
  partition output to the outer mask loop — feasible but
  substantially larger LOC than the IrreducibleBridge / AdjIncompBridge
  patterns suggested by the spec.

This file therefore stops at the building blocks (§§1–5) and a
companion fast-path form (§5).  The full iteration theorem is
left for a follow-up work item with one of the three
infrastructure lift options above.

## References

* B1' (`mg-a08f`): `Case3Enum/IrreducibleBridge.lean §6` —
  single-mut imperative→functional reduction of `irreducible`.
* B2 (`mg-e9d6`): `Case3Enum/AdjIncompBridge.lean §1` —
  single-mut reduction of `hasAdjacentIncomp`.
* BalancedLift §4 + §7: warshall (single-mut nested) and
  `hasBalancedPairSlow` (no muts beyond accumulator) reductions.
* `docs/a5-glue-status.md` §3 (recommended split): the
  ~400-600 LOC estimate assumed the single-mut pattern; the
  multi-mut partition's elaboration mismatch is the unforeseen
  obstacle.
-/

namespace OneThird
namespace Step8.Case3Enum

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false

/-! ### §1 — Pure-form definitions -/

/-- `enumNOf bs` = total number of poset elements at band-sizes `bs`. -/
def enumNOf (bs : List Nat) : Nat := (offsetsOf bs).getD bs.length 0

/-- Partition `(a, b)`-pairs into `freeUV` (band-gap ≤ w) and
`forcedUV` (band-gap > w), matching `enumPosetsFor`'s partition loop. -/
def enumPartition (w : Nat) (bs : List Nat) :
    Array (Nat × Nat) × Array (Nat × Nat) := Id.run do
  let offsets := offsetsOf bs
  let K := bs.length
  let mut freeUV : Array (Nat × Nat) := #[]
  let mut forcedUV : Array (Nat × Nat) := #[]
  for i in [0:K] do
    for j in [i+1:K] do
      let offI := offsets.getD i 0
      let offI1 := offsets.getD (i + 1) 0
      let offJ := offsets.getD j 0
      let offJ1 := offsets.getD (j + 1) 0
      for a in [offI:offI1] do
        for b in [offJ:offJ1] do
          if j - i > w then
            forcedUV := forcedUV.push (a, b)
          else
            freeUV := freeUV.push (a, b)
  return (freeUV, forcedUV)

/-- The free `(u, v)`-pairs at `(w, bs)`. -/
def enumFreeUVOf (w : Nat) (bs : List Nat) : Array (Nat × Nat) :=
  (enumPartition w bs).1

/-- The forced `(u, v)`-pairs at `(w, bs)`. -/
def enumForcedUVOf (w : Nat) (bs : List Nat) : Array (Nat × Nat) :=
  (enumPartition w bs).2

/-- The number of free `(u, v)`-pairs at `(w, bs)`. -/
def enumNfreeOf (w : Nat) (bs : List Nat) : Nat := (enumFreeUVOf w bs).size

/-- Per-mask pred *before* the warshall closure: starts with all-zeros,
applies forced-edge pushes, then mask-gated free-edge pushes. -/
def enumPredPreWarshallOf (w : Nat) (bs : List Nat) (mask : Nat) :
    Array Nat := Id.run do
  let n := enumNOf bs
  let freeUV := enumFreeUVOf w bs
  let forcedUV := enumForcedUVOf w bs
  let nfree := freeUV.size
  let mut pred : Array Nat := Array.replicate n 0
  for uv in forcedUV do
    let (u, v) := uv
    pred := pred.set! v ((pred.getD v 0) ||| bit u)
  for k in [0:nfree] do
    if testBit' mask k then
      let (u, v) := freeUV.getD k (0, 0)
      pred := pred.set! v ((pred.getD v 0) ||| bit u)
  return pred

/-- Per-mask pred at iteration `mask`, after warshall closure. -/
def enumPredAtMaskOf (w : Nat) (bs : List Nat) (mask : Nat) : Array Nat :=
  warshall (enumPredPreWarshallOf w bs mask) (enumNOf bs)

/-! ### §2 — Outer-loop body factoring

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

/-! ### §3 — Yield-or-done case-split and `done`-iff -/

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

/-! ### §4 — Outer forIn `.fst = some false` characterization -/

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

/-! ### §5 — Companion fast-path form -/

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
