/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — A5-G3e (Path C): `allBalanced` outer-loop Bool→Prop bridge
(`mg-26bb`)

`Case3Enum.allBalanced` is a `Bool := Id.run do` whose for-loop
iterates over `bandSizesGen 3 sizeLimit` and short-circuits on the
first `bs` with `enumPosetsFor w bs = false`.

This file packages the outer-loop Bool↔Prop bridge:

* §1 — `allBalancedBody`, the per-`bs` `MProd (Option Bool) PUnit`
  body of the outer `for bs in bandSizesGen 3 sizeLimit` loop.
* §2 — `allBalancedBody_yield_or_done` /
  `allBalancedBody_done_iff`: the body's two-state behaviour and
  the precise condition under which it triggers the early
  `return-false` branch.
* §3 — `allBalanced_forIn_fst_cases` /
  `allBalanced_forIn_fst_some_false_iff`: the outer `forIn`'s
  `.fst` characterization (always in `{none, some false}`;
  `= some false` iff some `bs` triggers `done`).
* §4 — `allBalanced_eq_forIn_fst`, the imperative→functional
  reduction reducing `allBalanced` to the `forIn` over
  `bandSizesGen 3 sizeLimit` via the now-trivial `unfold + rfl`
  pattern.
* §5 — `allBalanced_imp_enumPosetsFor`, the headline outer-loop
  iteration theorem (A5-G3e Path C deliverable): for every
  `bs ∈ bandSizesGen 3 sizeLimit`, `enumPosetsFor w bs = true`.

## Pattern

This file is structurally identical to `EnumPosetsForBridge.lean`
(which carries the inner per-mask iteration theorem of `mg-b487`),
but for the simpler outer loop: the body is a single `if` rather
than a five-stage gate cascade, and the source is a plain `List`
rather than a `Std.Range`, so the imperative→functional reduction
is just `unfold + rfl` (no `Std.Legacy.Range.forIn_eq_forIn_range'`
rewrite required).

## References

* `mg-b487`: `Case3Enum/EnumPosetsForBridge.lean` — inner per-mask
  bridge template.
* `docs/a5-g3e-path-c-wiring-v3-status.md` §4 (commit `b35949e`):
  the audit of the missing outer-loop bridge.
* `lean/OneThird/Step8/Case3Enum.lean:360-363` — `allBalanced`
  outer for-loop definition.
* `lean/OneThird/Step8/Case3Enum/Certificate.lean:57-62` —
  `case3_certificate`, the source of `allBalanced w sizeLimit
  = true`.
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:114-115`
  — consumer obligation `enumPosetsFor L.w (bandSizes L) = true`.
-/

namespace OneThird
namespace Step8.Case3Enum

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false

/-! ### §1 — Outer-loop body factoring

The body of `for bs in bandSizesGen 3 sizeLimit do …` in
`allBalanced`, elaborated as a `MProd (Option Bool) PUnit`-state
forIn body. -/

/-- Outer band-size-loop body: short-circuit `done ⟨some false,
()⟩` when `enumPosetsFor w bs = false`, else `yield ⟨none, ()⟩`. -/
def allBalancedBody (w : Nat) (bs : List Nat)
    (_r : MProd (Option Bool) PUnit) :
    Id (ForInStep (MProd (Option Bool) PUnit)) :=
  if !enumPosetsFor w bs then
    pure (ForInStep.done ⟨some false, PUnit.unit⟩)
  else
    pure (ForInStep.yield ⟨none, PUnit.unit⟩)

/-! ### §2 — Yield-or-done case-split and `done`-iff -/

/-- The outer body always either yields `none` (continue) or
returns `done ⟨some false, ()⟩` (early `return false` after a
failing `enumPosetsFor`). -/
private lemma allBalancedBody_yield_or_done (w : Nat) (bs : List Nat)
    (r : MProd (Option Bool) PUnit) :
    allBalancedBody w bs r =
        pure (ForInStep.yield (⟨none, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) ∨
    allBalancedBody w bs r =
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) := by
  unfold allBalancedBody
  by_cases h1 : (!enumPosetsFor w bs) = true
  · right; rw [if_pos h1]
  · left; rw [if_neg h1]

/-- The outer body returns `done ⟨some false, ()⟩` iff
`enumPosetsFor w bs = false`. -/
private lemma allBalancedBody_done_iff (w : Nat) (bs : List Nat)
    (r : MProd (Option Bool) PUnit) :
    allBalancedBody w bs r =
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) ↔
    enumPosetsFor w bs = false := by
  unfold allBalancedBody
  -- Bool helper: (!b) = true ↔ b = false.
  have not_eq_true_iff_eq_false : ∀ (b : Bool), (!b) = true ↔ b = false := by
    intro b; cases b <;> decide
  by_cases h1 : (!enumPosetsFor w bs) = true
  · rw [if_pos h1]
    rw [not_eq_true_iff_eq_false] at h1
    exact ⟨fun _ => h1, fun _ => rfl⟩
  · rw [if_neg h1]
    refine ⟨?_, ?_⟩
    · intro h; cases h
    · intro hf
      exfalso; apply h1
      rw [hf]; rfl

/-! ### §3 — Outer forIn `.fst = some false` characterization -/

/-- The outer forIn's `.fst` is in `{none, some false}` (never
`some true`), since the body only `yield`s `none` or `done`s
`some false`. -/
private lemma allBalanced_forIn_fst_cases (w : Nat)
    (l : List (List Nat)) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun bs r => allBalancedBody w bs r)).fst = none ∨
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun bs r => allBalancedBody w bs r)).fst = some false := by
  induction l with
  | nil => left; rfl
  | cons bs bss ih =>
    rw [List.forIn_cons]
    rcases allBalancedBody_yield_or_done w bs
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) with hy | hd
    · rw [hy]
      change ((forIn (m := Id) bss
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = none) ∨ _ = some false
      exact ih
    · rw [hd]; right; rfl

/-- The outer forIn's `.fst = some false` iff some `bs ∈ l`
triggers the outer body's `done` branch. -/
private lemma allBalanced_forIn_fst_some_false_iff (w : Nat)
    (l : List (List Nat)) :
    (forIn (m := Id) l (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
      (fun bs r => allBalancedBody w bs r)).fst = some false ↔
    ∃ bs ∈ l, allBalancedBody w bs
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) =
      pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                              MProd (Option Bool) PUnit)) := by
  induction l with
  | nil =>
    show ((⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit).fst = some false) ↔ _
    simp
  | cons bs bss ih =>
    rw [List.forIn_cons]
    rcases allBalancedBody_yield_or_done w bs
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) with hy | hd
    · rw [hy]
      change (forIn (m := Id) bss
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) _ :
        MProd (Option Bool) PUnit).fst = some false ↔ _
      rw [ih]
      constructor
      · rintro ⟨bs', hmem, hb⟩
        exact ⟨bs', List.mem_cons_of_mem _ hmem, hb⟩
      · rintro ⟨bs', hmem, hb⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · rw [hy] at hb
          exact absurd hb (fun h => by cases h)
        · exact ⟨bs', hmem', hb⟩
    · rw [hd]
      change (((⟨some false, PUnit.unit⟩ : MProd (Option Bool) PUnit).fst :
                Option Bool) = some false) ↔ _
      refine ⟨fun _ => ⟨bs, ?_, hd⟩, fun _ => rfl⟩
      exact List.mem_cons_self

/-! ### §4 — Imperative→functional reduction of `allBalanced` -/

/-- **Imperative→functional reduction** for `allBalanced`.
The body of the outer `for bs in bandSizesGen 3 sizeLimit` loop
matches `allBalancedBody` on the nose, and the source is already a
`List`, so the reduction is just `unfold + rfl`. -/
private theorem allBalanced_eq_forIn_fst (w sizeLimit : Nat) :
    allBalanced w sizeLimit =
      match (forIn (m := Id) (bandSizesGen 3 sizeLimit)
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun bs r => allBalancedBody w bs r)).fst with
      | none => true
      | some a => a := by
  unfold allBalanced allBalancedBody
  rfl

/-! ### §5 — Headline outer-loop iteration theorem -/

/-- **A5-G3e Path C headline (`mg-26bb`)**: `allBalanced`
outer-loop Bool→Prop bridge.

If `allBalanced w sizeLimit = true`, then for every `bs` in the
list `bandSizesGen 3 sizeLimit` of band-size tuples,
`enumPosetsFor w bs = true` — otherwise the outer loop body
would have triggered `return false`, contradicting the hypothesis.

This is the analogue of `enumPosetsFor_iter_balanced`
(`EnumPosetsForBridge.lean §5`, `mg-b487`) lifted from the inner
per-mask loop to the outer per-`bs` loop, and is what discharges
the `h_certificate : enumPosetsFor L.w (bandSizes L) = true`
obligation in `bounded_irreducible_balanced_inScope`
(`BoundedIrreducibleBalancedInScope.lean:103-105`) from F5a's
Bool-level `case3_certificate`. -/
theorem allBalanced_imp_enumPosetsFor
    (w sizeLimit : Nat) (h : allBalanced w sizeLimit = true)
    (bs : List Nat) (hbs : bs ∈ bandSizesGen 3 sizeLimit) :
    enumPosetsFor w bs = true := by
  -- Step 1: Reduce `allBalanced` to its outer-`forIn` form.
  rw [allBalanced_eq_forIn_fst] at h
  -- `h` now says: match (forIn …).fst with | none => true | some a => a = true.
  -- Combined with the `allBalanced_forIn_fst_cases` fact that
  -- `.fst ∈ {none, some false}`, this forces `.fst = none`
  -- (the only value that yields `true` from the match).
  have hcase := allBalanced_forIn_fst_cases w (bandSizesGen 3 sizeLimit)
  rcases hcase with hnone | hsf
  · -- `.fst = none`: no `bs` triggered `done`, which is what we need.
    have h_no_done : ∀ b ∈ bandSizesGen 3 sizeLimit,
        allBalancedBody w b
          (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) ≠
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) := by
      intro b hb hbody
      have h_some_false :
          (forIn (m := Id) (bandSizesGen 3 sizeLimit)
                (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
                (fun bs r => allBalancedBody w bs r)).fst = some false :=
        (allBalanced_forIn_fst_some_false_iff w _).mpr ⟨b, hb, hbody⟩
      rw [hnone] at h_some_false
      cases h_some_false
    -- Step 2: Specialize to our `bs`.
    have h_no := h_no_done bs hbs
    -- Step 3: If `enumPosetsFor w bs` returned `false`, the body
    -- would `done`, contradicting `h_no`.
    by_contra hep
    rw [Bool.not_eq_true] at hep
    apply h_no
    exact (allBalancedBody_done_iff w bs
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)).mpr hep
  · -- `.fst = some false`: match returns `false`, contradicting `h`.
    rw [hsf] at h
    cases h

/-! ### §6 — K-parametric variant (`mg-9a4a` Window C) -/

/-- Imperative→functional reduction for `allBalancedAtK`, the
K-parametric generalisation of `allBalanced` (`mg-9a4a`). The outer
loop source is `bandSizesGen K sizeLimit`; the body matches
`allBalancedBody` on the nose, so the reduction is again `unfold + rfl`. -/
private theorem allBalancedAtK_eq_forIn_fst (K w sizeLimit : Nat) :
    allBalancedAtK K w sizeLimit =
      match (forIn (m := Id) (bandSizesGen K sizeLimit)
        (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun bs r => allBalancedBody w bs r)).fst with
      | none => true
      | some a => a := by
  unfold allBalancedAtK allBalancedBody
  rfl

/-- K-parametric outer-loop Bool→Prop bridge (`mg-9a4a` Window C).

Identical statement to `allBalanced_imp_enumPosetsFor` but with the
band count `K` an explicit parameter. Used by
`enumPosetsFor_eq_true_of_inScope` to extract `enumPosetsFor`
witnesses from the K=4 entries of `case3_certificate`. -/
theorem allBalancedAtK_imp_enumPosetsFor
    (K w sizeLimit : Nat) (h : allBalancedAtK K w sizeLimit = true)
    (bs : List Nat) (hbs : bs ∈ bandSizesGen K sizeLimit) :
    enumPosetsFor w bs = true := by
  -- Structurally identical to `allBalanced_imp_enumPosetsFor`.
  rw [allBalancedAtK_eq_forIn_fst] at h
  have hcase := allBalanced_forIn_fst_cases w (bandSizesGen K sizeLimit)
  rcases hcase with hnone | hsf
  · have h_no_done : ∀ b ∈ bandSizesGen K sizeLimit,
        allBalancedBody w b
          (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) ≠
        pure (ForInStep.done (⟨some false, PUnit.unit⟩ :
                                MProd (Option Bool) PUnit)) := by
      intro b hb hbody
      have h_some_false :
          (forIn (m := Id) (bandSizesGen K sizeLimit)
                (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
                (fun bs r => allBalancedBody w bs r)).fst = some false :=
        (allBalanced_forIn_fst_some_false_iff w _).mpr ⟨b, hb, hbody⟩
      rw [hnone] at h_some_false
      cases h_some_false
    have h_no := h_no_done bs hbs
    by_contra hep
    rw [Bool.not_eq_true] at hep
    apply h_no
    exact (allBalancedBody_done_iff w bs
      (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)).mpr hep
  · rw [hsf] at h
    cases h

end Step8.Case3Enum
end OneThird
