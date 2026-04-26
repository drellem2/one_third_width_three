/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Subtype
import OneThird.Step8.LayeredReduction

/-!
# Step 8 — Window `OrdinalDecomp` constructor for F3 irreducible Case C1

Constructs an `OrdinalDecomp α` whose `Mid` is a band-window
containing a chosen pair of elements `(x, y)`. This is the geometric
reduction underlying *window descent* (paper `step8.tex:3112-3116`,
Case C1 of the F3 irreducible branch).

## Setup

Given `L : LayeredDecomposition α` and a pair `(x, y) : α × α`, build
a partition

  `α = Lower ⊔ Mid ⊔ Upper`

by choosing band cutoffs `B_lo ≤ min(L.band x, L.band y)` and
`B_hi ≥ max(L.band x, L.band y)` such that the half-open band
intervals `[B_lo - L.w, B_lo)` and `(B_hi, B_hi + L.w]` are *empty*
in `α`. The empty band buffers are exactly what `(L2-forced)` needs
to fire across the partition boundary: for `z ∈ Lower` (band `< B_lo`,
hence band `≤ B_lo - L.w - 1` since the buffer is empty), and
`m ∈ Mid` (band `≥ B_lo`),
`L.band z + L.w ≤ B_lo - 1 < B_lo ≤ L.band m`, so `L.forced_lt`
fires.

## Why this avoids the natural-window failure mode

The "natural" window `[min(i,j) - L.w, max(i,j) + L.w]` packed as the
`Mid` of an `OrdinalDecomp` does *not* satisfy `Lower < Mid < Upper`
via `(L2-forced)`: the boundary band-distance from a top-`Mid`
element to a bottom-`Upper` element is exactly `1 ≤ L.w`, which fails
the strict separation `band x + L.w < band y` required by
`(L2-forced)`. See `docs/a5-g3e-path-c-wiring-v3-status.md` §3b.

This file's construction sidesteps the failure by *only* allowing
cutoffs at empty-band gaps in `α` of width `≥ L.w`, where the strict
separation needed by `L.forced_lt` holds vacuously. The
`B_lo = 1` and `B_hi = L.K` cutoffs are unconditionally valid (`α`
has no element of band `< 1` or `> L.K` by `band_pos` / `band_le`),
so the constructor unconditionally produces some `OrdinalDecomp α`,
with the trivial choice giving the degenerate `Lower = Upper = ∅`,
`Mid = α` decomposition. For the F3 step proof's Case C1 to actually
descend, the caller must find a non-trivial cutoff pair producing
`|Mid| < |α|` — the maximal-`B_lo` / minimal-`B_hi` derived
constructor `OrdinalDecomp.windowOfPairAt` selects the tightest valid
cutoffs.

## Main results

* `IsValidLowerCutoff` / `IsValidUpperCutoff` — predicates on band
  cutoffs ensuring `(L2-forced)` fires across the boundary.
* `one_isValidLowerCutoff` / `K_isValidUpperCutoff` — the
  unconditionally-valid trivial cutoffs.
* `OrdinalDecomp.ofLayeredCutoffs` — the constructor from explicit
  cutoffs and validity proofs.
* `OrdinalDecomp.windowOfPairAt` — derived constructor using the
  maximal `B_lo ≤ min(L.band x, L.band y)` and minimal
  `B_hi ≥ max(L.band x, L.band y)` valid cutoffs.
* `OrdinalDecomp.windowOfPairAt_mem_mid_left` /
  `OrdinalDecomp.windowOfPairAt_mem_mid_right` — `x` and `y` lie in
  the constructed `Mid`.

## References

* `step8.tex:3112-3116` — Case C1 of the F3 irreducible branch.
* `docs/a5-g3e-path-c-wiring-v3-status.md` §3 — audit identifying the
  boundary failure mode of the natural window.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:140` —
  `OrdinalDecomp` structure definition.
* `lean/OneThird/Step8/LayeredReduction.lean:96` —
  `LayeredDecomposition` definition (carries `(L2-forced)`).
-/

namespace OneThird
namespace Step8

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Cutoff validity predicates -/

/-- A natural number `B` is a *valid lower cutoff* (relative to a
layered decomposition `L`) if no element of `α` has band in the
half-open interval `[B - L.w, B)`. Bands in this interval would
violate the strict separation needed by `L.forced_lt` between
elements of band `< B` and elements of band `≥ B`. -/
def IsValidLowerCutoff (L : LayeredDecomposition α) (B : ℕ) : Prop :=
  ∀ z : α, ¬ (B - L.w ≤ L.band z ∧ L.band z < B)

/-- A natural number `B` is a *valid upper cutoff* if no element of
`α` has band in the half-open interval `(B, B + L.w]`. -/
def IsValidUpperCutoff (L : LayeredDecomposition α) (B : ℕ) : Prop :=
  ∀ z : α, ¬ (B < L.band z ∧ L.band z ≤ B + L.w)

/-- `B = 1` is always a valid lower cutoff: the interval `[1 - L.w, 1)`
contains only band `0` (since natural subtraction caps at `0`), and
no `α`-element has band `0` by `L.band_pos`. -/
lemma one_isValidLowerCutoff (L : LayeredDecomposition α) :
    IsValidLowerCutoff L 1 := by
  intro z ⟨_, hz_lt⟩
  exact absurd hz_lt (Nat.not_lt.mpr (L.band_pos z))

/-- `B = L.K` is always a valid upper cutoff: bands of `α` are `≤ L.K`
by `L.band_le`. -/
lemma K_isValidUpperCutoff (L : LayeredDecomposition α) :
    IsValidUpperCutoff L L.K := by
  intro z ⟨hz_gt, _⟩
  exact absurd hz_gt (Nat.not_lt.mpr (L.band_le z))

/-! ### §2 — The constructor from explicit cutoffs -/

/-- **Window `OrdinalDecomp` constructor — explicit cutoffs**
(`step8.tex:3112-3116`).

Given a layered decomposition `L`, valid cutoffs `B_lo`, `B_hi` with
`B_lo ≤ B_hi`, build the `OrdinalDecomp α` with:

* `Lower = {z : L.band z < B_lo}`,
* `Mid = {z : B_lo ≤ L.band z ∧ L.band z ≤ B_hi}`,
* `Upper = {z : B_hi < L.band z}`.

The cross-band orderings `Lower < Mid`, `Mid < Upper`, `Lower < Upper`
follow from `L.forced_lt` together with the validity of the cutoffs:
the empty-band gap `[B_lo - L.w, B_lo)` (resp. `(B_hi, B_hi + L.w]`)
forces every `Lower` (resp. `Upper`) element to lie at band-distance
`> L.w` from `Mid`, triggering the strict-separation hypothesis of
`L.forced_lt`. -/
noncomputable def OrdinalDecomp.ofLayeredCutoffs
    (L : LayeredDecomposition α) (B_lo B_hi : ℕ)
    (h_lo_valid : IsValidLowerCutoff L B_lo)
    (h_hi_valid : IsValidUpperCutoff L B_hi)
    (h_le : B_lo ≤ B_hi) : OneThird.OrdinalDecomp α := by
  classical
  refine
    { Lower := (Finset.univ : Finset α).filter (fun z => L.band z < B_lo)
      Mid := (Finset.univ : Finset α).filter
        (fun z => B_lo ≤ L.band z ∧ L.band z ≤ B_hi)
      Upper := (Finset.univ : Finset α).filter (fun z => B_hi < L.band z)
      hCover := ?_
      hDisjLM := ?_
      hDisjLU := ?_
      hDisjMU := ?_
      hLM_lt := ?_
      hLU_lt := ?_
      hMU_lt := ?_ }
  · -- hCover: every element falls into exactly one of the three sets.
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro _; trivial
    · intro _
      rcases lt_or_ge (L.band z) B_lo with h₁ | h₁
      · exact Or.inl (Or.inl h₁)
      · rcases le_or_gt (L.band z) B_hi with h₂ | h₂
        · exact Or.inl (Or.inr ⟨h₁, h₂⟩)
        · exact Or.inr h₂
  · -- hDisjLM.
    rw [Finset.disjoint_filter]
    intro z _ hL ⟨hM, _⟩
    omega
  · -- hDisjLU.
    rw [Finset.disjoint_filter]
    intro z _ hL hU
    omega
  · -- hDisjMU.
    rw [Finset.disjoint_filter]
    intro z _ ⟨_, hM⟩ hU
    omega
  · -- hLM_lt: Lower < Mid via L.forced_lt.
    intro x hx y hy
    rcases Finset.mem_filter.mp hx with ⟨_, hxL⟩
    rcases Finset.mem_filter.mp hy with ⟨_, hyM, _⟩
    apply L.forced_lt
    -- L.band x < B_lo. By validity of B_lo, in fact L.band x + L.w < B_lo.
    -- Combined with B_lo ≤ L.band y, this gives L.band x + L.w < L.band y.
    have h_lo_strict : L.band x + L.w < B_lo := by
      by_contra h
      apply h_lo_valid x
      refine ⟨?_, hxL⟩
      omega
    omega
  · -- hLU_lt: Lower < Upper via L.forced_lt.
    intro x hx y hy
    rcases Finset.mem_filter.mp hx with ⟨_, hxL⟩
    rcases Finset.mem_filter.mp hy with ⟨_, hyU⟩
    apply L.forced_lt
    have h_lo_strict : L.band x + L.w < B_lo := by
      by_contra h
      apply h_lo_valid x
      refine ⟨?_, hxL⟩
      omega
    omega
  · -- hMU_lt: Mid < Upper via L.forced_lt.
    intro x hx y hy
    rcases Finset.mem_filter.mp hx with ⟨_, _, hxM⟩
    rcases Finset.mem_filter.mp hy with ⟨_, hyU⟩
    apply L.forced_lt
    have h_hi_strict : B_hi + L.w < L.band y := by
      by_contra h
      apply h_hi_valid y
      refine ⟨hyU, ?_⟩
      omega
    omega

/-! ### §3 — Membership lemmas -/

/-- An element `x : α` whose band lies in `[B_lo, B_hi]` lies in the
`Mid` of the constructor's output. -/
lemma OrdinalDecomp.mem_mid_ofLayeredCutoffs
    (L : LayeredDecomposition α) {B_lo B_hi : ℕ}
    (h_lo_valid : IsValidLowerCutoff L B_lo)
    (h_hi_valid : IsValidUpperCutoff L B_hi)
    (h_le : B_lo ≤ B_hi) (x : α)
    (hx_lo : B_lo ≤ L.band x) (hx_hi : L.band x ≤ B_hi) :
    x ∈ (OrdinalDecomp.ofLayeredCutoffs L B_lo B_hi
      h_lo_valid h_hi_valid h_le).Mid := by
  classical
  change x ∈ (Finset.univ : Finset α).filter
      (fun z => B_lo ≤ L.band z ∧ L.band z ≤ B_hi)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_lo, hx_hi⟩

/-! ### §4 — Derived constructor: maximal cutoffs from a chosen pair -/

/-- All valid lower cutoffs `B` with `1 ≤ B ≤ lo`. -/
noncomputable def validLowerCutoffsLe (L : LayeredDecomposition α) (lo : ℕ) :
    Finset ℕ :=
  (Finset.Icc 1 lo).filter (fun B =>
    ((Finset.univ : Finset α).filter
        (fun z => B - L.w ≤ L.band z ∧ L.band z < B)).card = 0)

lemma mem_validLowerCutoffsLe {L : LayeredDecomposition α} {lo B : ℕ} :
    B ∈ validLowerCutoffsLe L lo ↔
      (1 ≤ B ∧ B ≤ lo) ∧ IsValidLowerCutoff L B := by
  classical
  unfold validLowerCutoffsLe
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨h1, h2⟩, hcard⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro z hz
    have hmem : z ∈ ((Finset.univ : Finset α).filter
        (fun z => B - L.w ≤ L.band z ∧ L.band z < B)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hpos : 0 < ((Finset.univ : Finset α).filter
        (fun z => B - L.w ≤ L.band z ∧ L.band z < B)).card :=
      Finset.card_pos.mpr ⟨z, hmem⟩
    omega
  · rintro ⟨hbnds, hvalid⟩
    refine ⟨hbnds, ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z _
    exact hvalid z

lemma one_mem_validLowerCutoffsLe (L : LayeredDecomposition α) {lo : ℕ}
    (hlo : 1 ≤ lo) : 1 ∈ validLowerCutoffsLe L lo :=
  mem_validLowerCutoffsLe.mpr ⟨⟨le_refl _, hlo⟩, one_isValidLowerCutoff L⟩

/-- All valid upper cutoffs `B` with `hi ≤ B ≤ L.K`. -/
noncomputable def validUpperCutoffsGe (L : LayeredDecomposition α) (hi : ℕ) :
    Finset ℕ :=
  (Finset.Icc hi L.K).filter (fun B =>
    ((Finset.univ : Finset α).filter
        (fun z => B < L.band z ∧ L.band z ≤ B + L.w)).card = 0)

lemma mem_validUpperCutoffsGe {L : LayeredDecomposition α} {hi B : ℕ} :
    B ∈ validUpperCutoffsGe L hi ↔
      (hi ≤ B ∧ B ≤ L.K) ∧ IsValidUpperCutoff L B := by
  classical
  unfold validUpperCutoffsGe
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨h1, h2⟩, hcard⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro z hz
    have hmem : z ∈ ((Finset.univ : Finset α).filter
        (fun z => B < L.band z ∧ L.band z ≤ B + L.w)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hpos : 0 < ((Finset.univ : Finset α).filter
        (fun z => B < L.band z ∧ L.band z ≤ B + L.w)).card :=
      Finset.card_pos.mpr ⟨z, hmem⟩
    omega
  · rintro ⟨hbnds, hvalid⟩
    refine ⟨hbnds, ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z _
    exact hvalid z

lemma K_mem_validUpperCutoffsGe (L : LayeredDecomposition α) {hi : ℕ}
    (hhi : hi ≤ L.K) : L.K ∈ validUpperCutoffsGe L hi :=
  mem_validUpperCutoffsGe.mpr ⟨⟨hhi, le_refl _⟩, K_isValidUpperCutoff L⟩

/-- The maximal valid lower cutoff `≤ lo`. Always defined (defaults to
the unconditionally-valid `1` when `lo = 0`). -/
noncomputable def lowerCutoff (L : LayeredDecomposition α) (lo : ℕ) : ℕ :=
  if h : (validLowerCutoffsLe L lo).Nonempty then
    (validLowerCutoffsLe L lo).max' h
  else 1

/-- The minimal valid upper cutoff `≥ hi`. Always defined (defaults to
the unconditionally-valid `L.K` when `hi > L.K`). -/
noncomputable def upperCutoff (L : LayeredDecomposition α) (hi : ℕ) : ℕ :=
  if h : (validUpperCutoffsGe L hi).Nonempty then
    (validUpperCutoffsGe L hi).min' h
  else L.K

lemma lowerCutoff_isValid (L : LayeredDecomposition α) {lo : ℕ}
    (hlo : 1 ≤ lo) : IsValidLowerCutoff L (lowerCutoff L lo) := by
  unfold lowerCutoff
  have h_ne : (validLowerCutoffsLe L lo).Nonempty :=
    ⟨1, one_mem_validLowerCutoffsLe L hlo⟩
  rw [dif_pos h_ne]
  have hmax : (validLowerCutoffsLe L lo).max' h_ne ∈ validLowerCutoffsLe L lo :=
    Finset.max'_mem _ h_ne
  exact (mem_validLowerCutoffsLe.mp hmax).2

lemma lowerCutoff_le (L : LayeredDecomposition α) {lo : ℕ}
    (hlo : 1 ≤ lo) : lowerCutoff L lo ≤ lo := by
  unfold lowerCutoff
  have h_ne : (validLowerCutoffsLe L lo).Nonempty :=
    ⟨1, one_mem_validLowerCutoffsLe L hlo⟩
  rw [dif_pos h_ne]
  have hmax : (validLowerCutoffsLe L lo).max' h_ne ∈ validLowerCutoffsLe L lo :=
    Finset.max'_mem _ h_ne
  exact (mem_validLowerCutoffsLe.mp hmax).1.2

lemma upperCutoff_isValid (L : LayeredDecomposition α) {hi : ℕ}
    (hhi : hi ≤ L.K) : IsValidUpperCutoff L (upperCutoff L hi) := by
  unfold upperCutoff
  have h_ne : (validUpperCutoffsGe L hi).Nonempty :=
    ⟨L.K, K_mem_validUpperCutoffsGe L hhi⟩
  rw [dif_pos h_ne]
  have hmin : (validUpperCutoffsGe L hi).min' h_ne ∈ validUpperCutoffsGe L hi :=
    Finset.min'_mem _ h_ne
  exact (mem_validUpperCutoffsGe.mp hmin).2

lemma upperCutoff_ge (L : LayeredDecomposition α) {hi : ℕ}
    (hhi : hi ≤ L.K) : hi ≤ upperCutoff L hi := by
  unfold upperCutoff
  have h_ne : (validUpperCutoffsGe L hi).Nonempty :=
    ⟨L.K, K_mem_validUpperCutoffsGe L hhi⟩
  rw [dif_pos h_ne]
  have hmin : (validUpperCutoffsGe L hi).min' h_ne ∈ validUpperCutoffsGe L hi :=
    Finset.min'_mem _ h_ne
  exact (mem_validUpperCutoffsGe.mp hmin).1.1

/-- **Window `OrdinalDecomp` constructor — derived form**
(`step8.tex:3112-3116`).

Given a layered decomposition `L` and elements `x, y : α`, builds the
maximal-`B_lo` / minimal-`B_hi` window `OrdinalDecomp` containing
both `x` and `y` in its `Mid`.

The cutoffs are:

* `B_lo := lowerCutoff L (min (L.band x) (L.band y))` — the maximal
  valid lower cutoff `≤ min(L.band x, L.band y)`,
* `B_hi := upperCutoff L (max (L.band x) (L.band y))` — the minimal
  valid upper cutoff `≥ max(L.band x, L.band y)`.

Both `1` and `L.K` are unconditionally valid, so the constructor
unconditionally produces some `OrdinalDecomp α`. The constructor
produces a degenerate `Mid = α` decomposition when `α` has no
`L.w`-band empty gaps outside `[L.band x, L.band y]`; the F3 step's
Case C1 dispatch then routes to the C2-leaf path. -/
noncomputable def OrdinalDecomp.windowOfPairAt
    (L : LayeredDecomposition α) (x y : α) : OneThird.OrdinalDecomp α :=
  let lo := min (L.band x) (L.band y)
  let hi := max (L.band x) (L.band y)
  have hlo : 1 ≤ lo := by
    have hx_pos := L.band_pos x; have hy_pos := L.band_pos y
    change 1 ≤ min _ _; omega
  have hhi : hi ≤ L.K := by
    have hx_le := L.band_le x; have hy_le := L.band_le y
    change max _ _ ≤ L.K; omega
  have h_le : lowerCutoff L lo ≤ upperCutoff L hi := by
    have h1 := lowerCutoff_le L hlo
    have h2 := upperCutoff_ge L hhi
    have h3 : lo ≤ hi := min_le_max
    omega
  OrdinalDecomp.ofLayeredCutoffs L (lowerCutoff L lo) (upperCutoff L hi)
    (lowerCutoff_isValid L hlo) (upperCutoff_isValid L hhi) h_le

/-- The first element `x` lies in the `Mid` of `windowOfPairAt L x y`. -/
lemma OrdinalDecomp.windowOfPairAt_mem_mid_left
    (L : LayeredDecomposition α) (x y : α) :
    x ∈ (OrdinalDecomp.windowOfPairAt L x y).Mid := by
  classical
  unfold OrdinalDecomp.windowOfPairAt
  apply OrdinalDecomp.mem_mid_ofLayeredCutoffs
  · -- lowerCutoff ≤ L.band x: lowerCutoff ≤ min(band x, band y) ≤ band x.
    have hlo : 1 ≤ min (L.band x) (L.band y) := by
      have hx_pos := L.band_pos x; have hy_pos := L.band_pos y
      omega
    have h := lowerCutoff_le L hlo
    have : min (L.band x) (L.band y) ≤ L.band x := min_le_left _ _
    omega
  · -- L.band x ≤ upperCutoff: band x ≤ max(band x, band y) ≤ upperCutoff.
    have hhi : max (L.band x) (L.band y) ≤ L.K := by
      have hx_le := L.band_le x; have hy_le := L.band_le y
      omega
    have h := upperCutoff_ge L hhi
    have : L.band x ≤ max (L.band x) (L.band y) := le_max_left _ _
    omega

/-- The second element `y` lies in the `Mid` of `windowOfPairAt L x y`. -/
lemma OrdinalDecomp.windowOfPairAt_mem_mid_right
    (L : LayeredDecomposition α) (x y : α) :
    y ∈ (OrdinalDecomp.windowOfPairAt L x y).Mid := by
  classical
  unfold OrdinalDecomp.windowOfPairAt
  apply OrdinalDecomp.mem_mid_ofLayeredCutoffs
  · have hlo : 1 ≤ min (L.band x) (L.band y) := by
      have hx_pos := L.band_pos x; have hy_pos := L.band_pos y
      omega
    have h := lowerCutoff_le L hlo
    have : min (L.band x) (L.band y) ≤ L.band y := min_le_right _ _
    omega
  · have hhi : max (L.band x) (L.band y) ≤ L.K := by
      have hx_le := L.band_le x; have hy_le := L.band_le y
      omega
    have h := upperCutoff_ge L hhi
    have : L.band y ≤ max (L.band x) (L.band y) := le_max_right _ _
    omega

end Step8
end OneThird
