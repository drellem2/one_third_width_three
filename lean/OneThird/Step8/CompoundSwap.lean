/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredReduction
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Compound-automorphism `Equiv.swap` for layered K=2 same-band pairs
(`docs/path-c-cleanup-roadmap.md` §6a, PATH B step 1)

This file builds the **compound-automorphism `Equiv.swap`** for layered
decompositions where two same-band pairs with a matching extension form
a poset automorphism. It is the foundation piece for the PATH B
compound-automorphism arc that closes the
`K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3` N-poset regime documented
in `docs/a5-g3e-path-c-wiring-v5-status.md` (`mg-94fd`).

## What this closes

The minimal failing instance for the existing rotation infrastructure
(`Step8/Case2Rotation.lean`, mg-ba0c / mg-5a62 / mg-27c2) is the
**N-poset**: `α = {x₁, x₂, y₁, y₂}` with `x₁ < y₁`, `x₂ < y₂`, no
other comparabilities, `band 1 = {x₁, x₂}`, `band 2 = {y₁, y₂}`,
`K = 2`, `w = 1`. The single transposition `(x₁ x₂)` alone is *not* a
poset automorphism (it would map `x₁ < y₁` to `x₂ < y₁`, but
`x₂ ∥ y₁`). The witness is the **compound** automorphism
`σ := (x₁ x₂)(y₁ y₂)`. The existing rotation argument operates on
within-band `⪯`-comparable pairs/chains and has no machinery for
compound multi-orbit automorphisms across bands; this file builds that
machinery.

## API

* `SameBandPair L` — a pair of distinct elements in the same band of
  a layered decomposition.
* `MatchingCompatible L P₁ P₂` — the matching-compatibility predicate
  saying the bijection `(a₁, a₂) ↔ (b₁, b₂)` extends to a poset
  automorphism: the four elements are pairwise distinct and the
  compound transposition preserves `≤`. The constructive verification
  of this hypothesis on layered configurations is left to a downstream
  ticket (the structural matching lemma).
* `compoundSwap L P₁ P₂` — the compound permutation
  `Equiv.swap b₁ b₂ ∘ Equiv.swap a₁ a₂`.
* `compoundSwap_eval` — explicit piecewise evaluation: maps the four
  elements pairwise and fixes everything else.
* `compoundSwap_preserves_le` — the compound swap preserves `≤`.
* `compoundSwap_involutive` — the compound swap is an involution.
* `compoundSwap_le_iff` — the compound swap induces a poset isomorphism:
  `x ≤ y ↔ compoundSwap x ≤ compoundSwap y`.

## N-poset canary

The bottom of the file includes a worked example: a concrete
4-element `NElt` type with `x₁ < y₁` and `x₂ < y₂` as the only
comparabilities, equipped with a `LayeredDecomposition`
(`K = 2`, `w = 1`), and a `MatchingCompatible` instance for the pair
`((x₁, x₂), (y₁, y₂))`. The example concludes with an application of
`compoundSwap_preserves_le`. This validates that the design handles
the named obstruction cleanly.

## References

* `docs/path-c-cleanup-roadmap.md` §5 (named obstruction), §6a (the
  compound-automorphism plan this file implements).
* `docs/a5-g3e-path-c-wiring-v5-status.md` — the round-4 firm
  stop-loss audit naming the N-poset.
* `lean/OneThird/Step8/BipartiteEnum.lean` `swap_preserves_le` — the
  single-orbit analogue.
* `lean/OneThird/Step8/Case2Rotation.lean` — the within-band rotation
  infrastructure that this compound construction complements.
-/

namespace OneThird
namespace Step8
namespace CompoundSwap

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Same-band pairs and the compound permutation -/

/-- A **same-band pair** in a layered decomposition `L`: two distinct
elements of `α` that share a band index.  Membership in a single band
forces `a₁` and `a₂` to be incomparable (each band is an antichain by
`(L1b)`); the compound swap construction uses both halves of this
constraint. -/
structure SameBandPair (L : LayeredDecomposition α) where
  /-- First element of the pair. -/
  a₁ : α
  /-- Second element of the pair. -/
  a₂ : α
  /-- Both elements live in the same band. -/
  hSameBand : L.band a₁ = L.band a₂
  /-- The two elements are distinct. -/
  hne : a₁ ≠ a₂

namespace SameBandPair

variable {L : LayeredDecomposition α}

omit [DecidableEq α] in
/-- Same-band elements of a `LayeredDecomposition` are incomparable
(the `(L1b)` antichain axiom restricted to the pair). -/
lemma not_le (P : SameBandPair L) : ¬ P.a₁ ≤ P.a₂ := by
  intro hle
  have hmem₁ :
      P.a₁ ∈ ((((Finset.univ : Finset α).filter
        (fun x => L.band x = L.band P.a₁)) : Set α)) := by
    simp [Finset.coe_filter]
  have hmem₂ :
      P.a₂ ∈ ((((Finset.univ : Finset α).filter
        (fun x => L.band x = L.band P.a₁)) : Set α)) := by
    simp [Finset.coe_filter, P.hSameBand]
  exact L.band_antichain (L.band P.a₁) hmem₁ hmem₂ P.hne hle

omit [DecidableEq α] in
/-- Symmetric form of `not_le`. -/
lemma not_ge (P : SameBandPair L) : ¬ P.a₂ ≤ P.a₁ := by
  intro hle
  have hmem₁ :
      P.a₁ ∈ ((((Finset.univ : Finset α).filter
        (fun x => L.band x = L.band P.a₁)) : Set α)) := by
    simp [Finset.coe_filter]
  have hmem₂ :
      P.a₂ ∈ ((((Finset.univ : Finset α).filter
        (fun x => L.band x = L.band P.a₁)) : Set α)) := by
    simp [Finset.coe_filter, P.hSameBand]
  exact L.band_antichain (L.band P.a₁) hmem₂ hmem₁ (Ne.symm P.hne) hle

end SameBandPair

/-- The **compound permutation** of two same-band pairs: simultaneously
swap `a₁ ↔ a₂` (in `P₁`'s band) and `b₁ ↔ b₂` (in `P₂`'s band).
Concretely, `compoundSwap = swap b₁ b₂ ∘ swap a₁ a₂` (the order does
not matter when the supports are disjoint, which is the typical use
under `MatchingCompatible`). -/
def compoundSwap (L : LayeredDecomposition α)
    (P₁ P₂ : SameBandPair L) : Equiv.Perm α :=
  (Equiv.swap P₁.a₁ P₁.a₂).trans (Equiv.swap P₂.a₁ P₂.a₂)

/-- The compound swap composes the two transpositions: applying it
unfolds to the inner transposition (on `P₁`) followed by the outer
transposition (on `P₂`). -/
@[simp] lemma compoundSwap_apply (L : LayeredDecomposition α)
    (P₁ P₂ : SameBandPair L) (x : α) :
    compoundSwap L P₁ P₂ x =
      Equiv.swap P₂.a₁ P₂.a₂ (Equiv.swap P₁.a₁ P₁.a₂ x) := rfl

/-! ### §2 — Matching compatibility -/

/-- **Matching compatibility** between two same-band pairs.

The bijection `(a₁, a₂) ↔ (b₁, b₂)` "extends to a poset automorphism"
when:

1. the four elements are pairwise distinct (so the supports of the two
   transpositions are disjoint, and the compound is a true
   double-orbit involution);
2. the compound swap `σ := swap b₁ b₂ ∘ swap a₁ a₂` is `≤`-monotone
   (the matching extends from the four elements to the ambient
   partial order without breaking any comparabilities).

Constructive verification of this hypothesis on layered configurations
is the structural matching lemma's job (a downstream ticket); this
file only consumes the hypothesis to build the compound `Equiv.swap`
and prove it preserves `≤`. -/
structure MatchingCompatible (L : LayeredDecomposition α)
    (P₁ P₂ : SameBandPair L) : Prop where
  /-- `P₁.a₁` and `P₂.a₁` are distinct. -/
  ne_a₁_b₁ : P₁.a₁ ≠ P₂.a₁
  /-- `P₁.a₁` and `P₂.a₂` are distinct. -/
  ne_a₁_b₂ : P₁.a₁ ≠ P₂.a₂
  /-- `P₁.a₂` and `P₂.a₁` are distinct. -/
  ne_a₂_b₁ : P₁.a₂ ≠ P₂.a₁
  /-- `P₁.a₂` and `P₂.a₂` are distinct. -/
  ne_a₂_b₂ : P₁.a₂ ≠ P₂.a₂
  /-- The compound swap preserves `≤`. -/
  preserves_le : ∀ ⦃x y : α⦄, x ≤ y →
      Equiv.swap P₂.a₁ P₂.a₂ (Equiv.swap P₁.a₁ P₁.a₂ x) ≤
      Equiv.swap P₂.a₁ P₂.a₂ (Equiv.swap P₁.a₁ P₁.a₂ y)

namespace MatchingCompatible

variable {L : LayeredDecomposition α} {P₁ P₂ : SameBandPair L}

/-- The four elements `a₁, a₂, b₁, b₂` of a matching-compatible pair
are pairwise distinct.  This packages the four `≠` fields together for
case-analysis convenience. -/
lemma all_distinct (h : MatchingCompatible L P₁ P₂) :
    P₁.a₁ ≠ P₁.a₂ ∧ P₁.a₁ ≠ P₂.a₁ ∧ P₁.a₁ ≠ P₂.a₂ ∧
    P₁.a₂ ≠ P₂.a₁ ∧ P₁.a₂ ≠ P₂.a₂ ∧ P₂.a₁ ≠ P₂.a₂ :=
  ⟨P₁.hne, h.ne_a₁_b₁, h.ne_a₁_b₂, h.ne_a₂_b₁, h.ne_a₂_b₂, P₂.hne⟩

end MatchingCompatible

/-! ### §3 — Compound swap evaluation -/

/-- **Evaluation at the first paired element.**  The compound swap
sends `P₁.a₁` to `P₁.a₂` (the inner swap flips, the outer leaves it
since `P₁.a₂ ∉ {P₂.a₁, P₂.a₂}`). -/
@[simp] lemma compoundSwap_a₁ {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂) :
    compoundSwap L P₁ P₂ P₁.a₁ = P₁.a₂ := by
  rw [compoundSwap_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne h.ne_a₂_b₁ h.ne_a₂_b₂

/-- **Evaluation at the second paired element.** -/
@[simp] lemma compoundSwap_a₂ {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂) :
    compoundSwap L P₁ P₂ P₁.a₂ = P₁.a₁ := by
  rw [compoundSwap_apply, Equiv.swap_apply_right]
  exact Equiv.swap_apply_of_ne_of_ne h.ne_a₁_b₁ h.ne_a₁_b₂

/-- **Evaluation at the third paired element.**  The inner swap leaves
`P₂.a₁` fixed (since `P₂.a₁ ∉ {P₁.a₁, P₁.a₂}`), and the outer swap
sends it to `P₂.a₂`. -/
@[simp] lemma compoundSwap_b₁ {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂) :
    compoundSwap L P₁ P₂ P₂.a₁ = P₂.a₂ := by
  rw [compoundSwap_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h.ne_a₁_b₁) (Ne.symm h.ne_a₂_b₁)]
  exact Equiv.swap_apply_left _ _

/-- **Evaluation at the fourth paired element.** -/
@[simp] lemma compoundSwap_b₂ {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂) :
    compoundSwap L P₁ P₂ P₂.a₂ = P₂.a₁ := by
  rw [compoundSwap_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h.ne_a₁_b₂) (Ne.symm h.ne_a₂_b₂)]
  exact Equiv.swap_apply_right _ _

/-- **Evaluation outside the four paired elements.**  The compound
swap fixes any element that is none of `a₁, a₂, b₁, b₂`. -/
lemma compoundSwap_other {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} {x : α}
    (hx₁ : x ≠ P₁.a₁) (hx₂ : x ≠ P₁.a₂)
    (hx₃ : x ≠ P₂.a₁) (hx₄ : x ≠ P₂.a₂) :
    compoundSwap L P₁ P₂ x = x := by
  rw [compoundSwap_apply,
      Equiv.swap_apply_of_ne_of_ne hx₁ hx₂,
      Equiv.swap_apply_of_ne_of_ne hx₃ hx₄]

/-! ### §4 — Involutivity -/

/-- The compound swap is an **involution** under
`MatchingCompatible`: applying it twice returns the original element.
This relies on the four elements being pairwise distinct (i.e. the two
transpositions have disjoint supports), which is part of the matching
compatibility hypothesis. -/
lemma compoundSwap_involutive {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂) (x : α) :
    compoundSwap L P₁ P₂ (compoundSwap L P₁ P₂ x) = x := by
  -- Case-split on whether `x` is one of the four paired elements; in
  -- each case both applications reduce to the obvious value.
  by_cases hx1 : x = P₁.a₁
  · subst hx1
    rw [compoundSwap_a₁ h, compoundSwap_a₂ h]
  by_cases hx2 : x = P₁.a₂
  · subst hx2
    rw [compoundSwap_a₂ h, compoundSwap_a₁ h]
  by_cases hx3 : x = P₂.a₁
  · subst hx3
    rw [compoundSwap_b₁ h, compoundSwap_b₂ h]
  by_cases hx4 : x = P₂.a₂
  · subst hx4
    rw [compoundSwap_b₂ h, compoundSwap_b₁ h]
  -- `x` is outside the four; both applications fix it.
  rw [compoundSwap_other hx1 hx2 hx3 hx4,
      compoundSwap_other hx1 hx2 hx3 hx4]

/-! ### §5 — Preservation of `≤` -/

/-- **The compound swap preserves `≤`** (forward direction).  This is
the direct content of `MatchingCompatible.preserves_le` repackaged
through `compoundSwap`. -/
theorem compoundSwap_preserves_le {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂)
    {x y : α} (hxy : x ≤ y) :
    compoundSwap L P₁ P₂ x ≤ compoundSwap L P₁ P₂ y :=
  h.preserves_le hxy

/-- **The compound swap is a poset automorphism** (iff form): for all
`x y : α`, `x ≤ y ↔ σ(x) ≤ σ(y)`.  The reverse direction comes from
involutivity (apply `preserves_le` to `σ(x), σ(y)` and use
`σ ∘ σ = id`). -/
theorem compoundSwap_le_iff {L : LayeredDecomposition α}
    {P₁ P₂ : SameBandPair L} (h : MatchingCompatible L P₁ P₂)
    (x y : α) :
    x ≤ y ↔ compoundSwap L P₁ P₂ x ≤ compoundSwap L P₁ P₂ y := by
  refine ⟨fun hxy => compoundSwap_preserves_le h hxy, fun hxy => ?_⟩
  have hback : compoundSwap L P₁ P₂ (compoundSwap L P₁ P₂ x) ≤
      compoundSwap L P₁ P₂ (compoundSwap L P₁ P₂ y) :=
    compoundSwap_preserves_le h hxy
  rwa [compoundSwap_involutive h, compoundSwap_involutive h] at hback

/-! ### §6 — N-poset canary

The minimal failing instance for the existing rotation infrastructure
(see `docs/a5-g3e-path-c-wiring-v5-status.md`).  We define the
4-element N-poset by hand, equip it with a `LayeredDecomposition` of
depth `K = 2` and width `w = 1`, build the two same-band pairs, verify
matching compatibility, and apply `compoundSwap_preserves_le`.  This
is the canary: if the construction handles the N-poset cleanly, the
compound-swap design works for the named obstruction. -/

namespace NPosetExample

/-- The four ground elements of the N-poset. -/
inductive NElt : Type
  | x₁ : NElt
  | x₂ : NElt
  | y₁ : NElt
  | y₂ : NElt
  deriving DecidableEq

/-- Manually supplied `Fintype` instance: the universe is just the four
constructors. -/
instance : Fintype NElt where
  elems := {NElt.x₁, NElt.x₂, NElt.y₁, NElt.y₂}
  complete a := by cases a <;> decide

/-- The N-poset comparabilities: `x₁ < y₁` and `x₂ < y₂`, plus
reflexivity.  All other pairs are incomparable. -/
def NElt.le : NElt → NElt → Prop
  | .x₁, .x₁ => True
  | .x₁, .y₁ => True
  | .x₂, .x₂ => True
  | .x₂, .y₂ => True
  | .y₁, .y₁ => True
  | .y₂, .y₂ => True
  | _, _ => False

instance : LE NElt := ⟨NElt.le⟩

instance NElt.decLE : DecidableRel ((· ≤ ·) : NElt → NElt → Prop) := by
  intro a b
  cases a <;> cases b <;>
    first
    | exact isTrue trivial
    | exact isFalse (fun h => h)

instance NElt.partialOrder : PartialOrder NElt where
  le := NElt.le
  le_refl a := by cases a <;> exact trivial
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      first
      | exact trivial
      | (exact (hab : False).elim)
      | (exact (hbc : False).elim)
  le_antisymm a b hab hba := by
    cases a <;> cases b <;>
      first
      | rfl
      | (exact (hab : False).elim)
      | (exact (hba : False).elim)

/-- Band map: `x₁, x₂` go to band 1, `y₁, y₂` go to band 2. -/
def NElt.band : NElt → ℕ
  | .x₁ | .x₂ => 1
  | .y₁ | .y₂ => 2

/-- Layered decomposition of the N-poset (`K = 2`, `w = 1`). -/
def layered : LayeredDecomposition NElt where
  K := 2
  w := 1
  band := NElt.band
  band_pos a := by cases a <;> decide
  band_le a := by cases a <;> decide
  band_size k := by
    classical
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> decide
    · -- For k ≥ 3, no element has band k, so the filter is empty.
      have hempty : ((Finset.univ : Finset NElt).filter
          (fun x => NElt.band x = k)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a _ ha
        cases a <;> simp [NElt.band] at ha <;> omega
      rw [hempty]; exact Nat.zero_le _
  band_antichain k := by
    classical
    intro a ha b hb hne hle
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at ha hb
    -- `ha : NElt.band a = k`, `hb : NElt.band b = k`.
    -- Reduce hle to its underlying `NElt.le` and case-split.
    change NElt.le a b at hle
    cases a <;> cases b <;>
      first
      | exact hne rfl
      | (exact (hle : False).elim)
      | (exfalso; simp [NElt.band] at ha hb; omega)
  forced_lt a b h := by
    cases a <;> cases b <;> simp [NElt.band] at h
  cross_band_lt_upward a b hab := by
    -- `a < b` in `NElt`: extract `a ≤ b` and case-split.
    have hle : a ≤ b := le_of_lt hab
    have hne : a ≠ b := ne_of_lt hab
    change NElt.le a b at hle
    cases a <;> cases b <;>
      first
      | (exfalso; exact hne rfl)
      | (exact (hle : False).elim)
      | (simp [NElt.band])

/-- The same-band pair `(x₁, x₂)` in band 1. -/
def pairX : SameBandPair layered where
  a₁ := NElt.x₁
  a₂ := NElt.x₂
  hSameBand := rfl
  hne := by decide

/-- The same-band pair `(y₁, y₂)` in band 2. -/
def pairY : SameBandPair layered where
  a₁ := NElt.y₁
  a₂ := NElt.y₂
  hSameBand := rfl
  hne := by decide

/-- The compound swap `σ = (x₁ x₂)(y₁ y₂)` is matching-compatible: it
preserves `≤`.  The structural verification proceeds by case analysis
on the constructors of `NElt`. -/
theorem matchingCompatible : MatchingCompatible layered pairX pairY where
  ne_a₁_b₁ := by decide
  ne_a₁_b₂ := by decide
  ne_a₂_b₁ := by decide
  ne_a₂_b₂ := by decide
  preserves_le := by
    intro x y hxy
    -- Reduce both sides via `Equiv.swap_apply_def` and case-split on
    -- the constructors of `NElt`.
    change NElt.le x y at hxy
    change NElt.le _ _
    cases x <;> cases y <;>
      first
      | (exact (hxy : False).elim)
      | (simp only [pairX, pairY, Equiv.swap_apply_def, NElt.le,
            if_pos]
         trivial)

/-- **N-poset canary**: the compound swap of `((x₁, x₂), (y₁, y₂))`
on the N-poset preserves `≤`.  This is the consumer-side test that
the design handles the named obstruction. -/
example : ∀ ⦃x y : NElt⦄, x ≤ y →
    compoundSwap layered pairX pairY x ≤ compoundSwap layered pairX pairY y :=
  fun _ _ => compoundSwap_preserves_le matchingCompatible

/-- The single transposition `(x₁ x₂)` is **not** a poset automorphism
of the N-poset: it would map `x₁ < y₁` to `x₂ < y₁`, but `x₂ ∥ y₁`.
The compound `(x₁ x₂)(y₁ y₂)` repairs this by simultaneously swapping
the matched partners.  This documents the non-triviality of needing
the compound construction. -/
example :
    ¬ ∀ ⦃x y : NElt⦄, x ≤ y →
        Equiv.swap NElt.x₁ NElt.x₂ x ≤ Equiv.swap NElt.x₁ NElt.x₂ y := by
  intro hSwapMono
  -- `x₁ ≤ y₁` in the N-poset by construction; under the lone
  -- transposition, this would become `x₂ ≤ y₁`, which is false.
  have hx1y1 : (NElt.x₁ : NElt) ≤ NElt.y₁ := show NElt.le _ _ from trivial
  have hSwap := hSwapMono hx1y1
  rw [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne
        (by decide : (NElt.y₁ : NElt) ≠ NElt.x₁)
        (by decide : (NElt.y₁ : NElt) ≠ NElt.x₂)] at hSwap
  -- `hSwap : (NElt.x₂ : NElt) ≤ NElt.y₁`, which is `False`.
  exact (hSwap : (False : Prop))

end NPosetExample

end CompoundSwap
end Step8
end OneThird
