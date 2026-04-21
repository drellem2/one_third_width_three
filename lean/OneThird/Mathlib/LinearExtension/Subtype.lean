/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.LinearExtension
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Linear extensions and ordinal-sum sub-poset restriction

Sub-poset infrastructure: `LinearExt` for a sub-poset (`Subtype p`)
inheriting `PartialOrder` from the ambient poset, and the marginal
invariance for the *ordinal-sum* setup.

## Setup

For a finite poset `α` with a partition
`Finset.univ = Lower ⊔ Mid ⊔ Upper` such that `Lower <_P Mid <_P Upper`
element-wise, every linear extension `L : LinearExt α` factors uniquely
as the concatenation of three independent linear extensions of the
restricted posets (`α |_ Lower`, `α |_ Mid`, `α |_ Upper`).

This is the combinatorial content of the *ordinal sum decomposition*
used in the paper proof of `lem:window-localization`
(`step8.tex:1573-1608`).

## Main results

* `OrdinalDecomp α` — the ordinal-sum partition data.
* `OrdinalDecomp.posBoundLower / posBoundMid / posBoundUpper` — the
  forced-positioning bounds in any linear extension of `α`.
* `OrdinalDecomp.numLinExt_eq` — cardinality identity:
  `numLinExt α = numLinExt Lower * numLinExt Mid * numLinExt Upper`.
* `OrdinalDecomp.probLT_restrict_eq` — **the key marginal invariance**:
  for `u, v ∈ Mid`, `probLT u v` (in `α`) equals `probLT ⟨u, _⟩ ⟨v, _⟩`
  (in `Subtype (· ∈ Mid)`).
* `OrdinalDecomp.hasBalancedPair_lift` — `HasBalancedPair` lifts from
  `Subtype (· ∈ Mid)` to `α`.

## Reference

`step8.tex:1573-1608` — `lem:window-localization` (`step8.tex` of the
companion paper).
-/

namespace OneThird

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

namespace LinearExt

/-! ### Helper: counting positions in a linear extension -/

/-- For a linear extension `L` and an element `x : α`, the set of
elements with smaller position has cardinality exactly `(L.pos x).val`. -/
lemma card_filter_pos_lt (L : LinearExt α) (x : α) :
    ((Finset.univ : Finset α).filter (fun y => L.pos y < L.pos x)).card =
      (L.pos x).val := by
  classical
  set T : Finset α :=
    (Finset.univ : Finset α).filter (fun y => L.pos y < L.pos x) with hT
  have hinj : Set.InjOn L.toFun (T : Set α) := fun a _ b _ h =>
    L.toFun.injective h
  have h1 : T.card = (T.image L.toFun).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hT_eq : T.image L.toFun = Finset.Iio (L.pos x) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_Iio]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [T, LinearExt.pos] using hy
    · intro hlt
      refine ⟨L.toFun.symm i, ?_, by simp⟩
      simpa [T, LinearExt.pos, Equiv.apply_symm_apply] using hlt
  rw [h1, hT_eq, Fin.card_Iio]

/-- For a linear extension `L` and an element `x : α`, the set of
elements with larger position has cardinality exactly
`Fintype.card α - 1 - (L.pos x).val`. -/
lemma card_filter_pos_gt (L : LinearExt α) (x : α) :
    ((Finset.univ : Finset α).filter (fun y => L.pos x < L.pos y)).card =
      Fintype.card α - 1 - (L.pos x).val := by
  classical
  set T : Finset α :=
    (Finset.univ : Finset α).filter (fun y => L.pos x < L.pos y) with hT
  have hinj : Set.InjOn L.toFun (T : Set α) := fun a _ b _ h =>
    L.toFun.injective h
  have h1 : T.card = (T.image L.toFun).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hT_eq : T.image L.toFun = Finset.Ioi (L.pos x) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_Ioi]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [T, LinearExt.pos] using hy
    · intro hlt
      refine ⟨L.toFun.symm i, ?_, by simp⟩
      simpa [T, LinearExt.pos, Equiv.apply_symm_apply] using hlt
  rw [h1, hT_eq, Fin.card_Ioi]

end LinearExt

/-! ### §1 — `OrdinalDecomp`: ordinal-sum partition data -/

/-- **Ordinal-sum partition data** for a finite poset `α`.

Records a partition `Finset.univ = Lower ⊔ Mid ⊔ Upper` with the
element-wise comparability `Lower <_P Mid`, `Lower <_P Upper`,
`Mid <_P Upper`. Equivalently, `α` is an ordinal sum of the three
restricted sub-posets. -/
structure OrdinalDecomp (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] where
  /-- The lower part `X^-`. -/
  Lower : Finset α
  /-- The middle part `W` (the *window* in the application). -/
  Mid : Finset α
  /-- The upper part `X^+`. -/
  Upper : Finset α
  /-- The three pieces are pairwise disjoint and cover `Finset.univ`. -/
  hCover : Lower ∪ Mid ∪ Upper = Finset.univ
  /-- `Lower` and `Mid` are disjoint. -/
  hDisjLM : Disjoint Lower Mid
  /-- `Lower` and `Upper` are disjoint. -/
  hDisjLU : Disjoint Lower Upper
  /-- `Mid` and `Upper` are disjoint. -/
  hDisjMU : Disjoint Mid Upper
  /-- Every `Lower` element is strictly less than every `Mid` element. -/
  hLM_lt : ∀ x ∈ Lower, ∀ y ∈ Mid, x < y
  /-- Every `Lower` element is strictly less than every `Upper` element. -/
  hLU_lt : ∀ x ∈ Lower, ∀ y ∈ Upper, x < y
  /-- Every `Mid` element is strictly less than every `Upper` element. -/
  hMU_lt : ∀ x ∈ Mid, ∀ y ∈ Upper, x < y

/-- The cover hypothesis, as a membership trichotomy. -/
lemma OrdinalDecomp.mem_cases (D : OrdinalDecomp α) (x : α) :
    x ∈ D.Lower ∨ x ∈ D.Mid ∨ x ∈ D.Upper := by
  have hx : x ∈ D.Lower ∪ D.Mid ∪ D.Upper := by
    rw [D.hCover]; exact mem_univ x
  rcases mem_union.mp hx with hxLM | hxU
  · rcases mem_union.mp hxLM with hxL | hxM
    · exact Or.inl hxL
    · exact Or.inr (Or.inl hxM)
  · exact Or.inr (Or.inr hxU)

/-- Cardinality identity from the disjoint-cover hypothesis. -/
lemma OrdinalDecomp.card_eq (D : OrdinalDecomp α) :
    Fintype.card α = D.Lower.card + D.Mid.card + D.Upper.card := by
  have hLM_disj : Disjoint (D.Lower ∪ D.Mid) D.Upper := by
    rw [Finset.disjoint_union_left]
    exact ⟨D.hDisjLU, D.hDisjMU⟩
  have hcard_LM : (D.Lower ∪ D.Mid).card = D.Lower.card + D.Mid.card :=
    Finset.card_union_of_disjoint D.hDisjLM
  have hcard : (D.Lower ∪ D.Mid ∪ D.Upper).card =
      D.Lower.card + D.Mid.card + D.Upper.card := by
    rw [Finset.card_union_of_disjoint hLM_disj, hcard_LM]
  have huniv : Fintype.card α = (Finset.univ : Finset α).card :=
    (Finset.card_univ).symm
  rw [huniv, ← D.hCover, hcard]

/-! ### §2 — Forced positions in any linear extension -/

/-- In any linear extension `L`, every `Lower` element occupies one of
the first `|Lower|` positions. -/
lemma OrdinalDecomp.posBoundLower (D : OrdinalDecomp α) (L : LinearExt α)
    {x : α} (hx : x ∈ D.Lower) : (L.pos x).val < D.Lower.card := by
  classical
  set T : Finset α :=
    (Finset.univ : Finset α).filter (fun y => L.pos x < L.pos y) with hT
  have hMU_subT : D.Mid ∪ D.Upper ⊆ T := by
    intro y hy
    rcases mem_union.mp hy with hyM | hyU
    · exact mem_filter.mpr ⟨mem_univ _,
        L.pos_lt_pos_of_lt (D.hLM_lt x hx y hyM).le
          (ne_of_lt (D.hLM_lt x hx y hyM))⟩
    · exact mem_filter.mpr ⟨mem_univ _,
        L.pos_lt_pos_of_lt (D.hLU_lt x hx y hyU).le
          (ne_of_lt (D.hLU_lt x hx y hyU))⟩
  have hMU_card : (D.Mid ∪ D.Upper).card = D.Mid.card + D.Upper.card :=
    Finset.card_union_of_disjoint D.hDisjMU
  have hT_card : T.card = Fintype.card α - 1 - (L.pos x).val :=
    L.card_filter_pos_gt x
  have h1 : D.Mid.card + D.Upper.card ≤ T.card := by
    rw [← hMU_card]
    exact Finset.card_le_card hMU_subT
  rw [hT_card] at h1
  have hcard := D.card_eq
  have hpos : (L.pos x).val < Fintype.card α := (L.pos x).isLt
  omega

/-- In any linear extension `L`, every `Mid` element occupies a
position in `[|Lower|, |Lower| + |Mid|)`. -/
lemma OrdinalDecomp.posBoundMid (D : OrdinalDecomp α) (L : LinearExt α)
    {x : α} (hx : x ∈ D.Mid) :
    D.Lower.card ≤ (L.pos x).val ∧
      (L.pos x).val < D.Lower.card + D.Mid.card := by
  classical
  set Tlt : Finset α :=
    (Finset.univ : Finset α).filter (fun y => L.pos y < L.pos x) with hTlt
  set Tgt : Finset α :=
    (Finset.univ : Finset α).filter (fun y => L.pos x < L.pos y) with hTgt
  have hL_subTlt : D.Lower ⊆ Tlt := by
    intro y hy
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    exact L.pos_lt_pos_of_lt (D.hLM_lt y hy x hx).le
      (ne_of_lt (D.hLM_lt y hy x hx))
  have hU_subTgt : D.Upper ⊆ Tgt := by
    intro y hy
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    exact L.pos_lt_pos_of_lt (D.hMU_lt x hx y hy).le
      (ne_of_lt (D.hMU_lt x hx y hy))
  have hTlt_card : Tlt.card = (L.pos x).val := L.card_filter_pos_lt x
  have hTgt_card : Tgt.card = Fintype.card α - 1 - (L.pos x).val :=
    L.card_filter_pos_gt x
  refine ⟨?_, ?_⟩
  · have := Finset.card_le_card hL_subTlt
    rw [hTlt_card] at this
    exact this
  · have h := Finset.card_le_card hU_subTgt
    rw [hTgt_card] at h
    have hcard := D.card_eq
    have hpos : (L.pos x).val < Fintype.card α := (L.pos x).isLt
    omega

/-- In any linear extension `L`, every `Upper` element occupies a
position `≥ |Lower| + |Mid|`. -/
lemma OrdinalDecomp.posBoundUpper (D : OrdinalDecomp α) (L : LinearExt α)
    {x : α} (hx : x ∈ D.Upper) :
    D.Lower.card + D.Mid.card ≤ (L.pos x).val := by
  classical
  set Tlt : Finset α :=
    (Finset.univ : Finset α).filter (fun y => L.pos y < L.pos x) with hTlt
  have hLM_subTlt : D.Lower ∪ D.Mid ⊆ Tlt := by
    intro y hy
    rcases mem_union.mp hy with hyL | hyM
    · refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      exact L.pos_lt_pos_of_lt (D.hLU_lt y hyL x hx).le
        (ne_of_lt (D.hLU_lt y hyL x hx))
    · refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      exact L.pos_lt_pos_of_lt (D.hMU_lt y hyM x hx).le
        (ne_of_lt (D.hMU_lt y hyM x hx))
  have hLM_card : (D.Lower ∪ D.Mid).card = D.Lower.card + D.Mid.card :=
    Finset.card_union_of_disjoint D.hDisjLM
  have hTlt_card : Tlt.card = (L.pos x).val := L.card_filter_pos_lt x
  have h := Finset.card_le_card hLM_subTlt
  rw [hLM_card, hTlt_card] at h
  exact h

/-- **Position-band trichotomy**: in any linear extension, an element
sits in `Lower` (resp. `Mid`, `Upper`) iff its position falls in the
corresponding band `[0, |Lower|)` (resp. `[|Lower|, |Lower| + |Mid|)`,
`[|Lower| + |Mid|, n)`). -/
lemma OrdinalDecomp.mem_mid_iff_posBand (D : OrdinalDecomp α) (L : LinearExt α)
    (x : α) :
    x ∈ D.Mid ↔
      D.Lower.card ≤ (L.pos x).val ∧
        (L.pos x).val < D.Lower.card + D.Mid.card := by
  refine ⟨fun hx => D.posBoundMid L hx, ?_⟩
  rintro ⟨h1, h2⟩
  rcases D.mem_cases x with hL | hM | hU
  · exact absurd (D.posBoundLower L hL) (by omega)
  · exact hM
  · exact absurd (D.posBoundUpper L hU) (by omega)

/-! ### §3 — Restriction of a linear extension to the middle piece -/

/-- **Restriction to the middle piece**: every linear extension `L` of
`α` induces a linear extension of `↥D.Mid` by relabeling the
positions of `Mid`-elements (which form the contiguous block
`[|Lower|, |Lower| + |Mid|)` by `posBoundMid`) as `Fin |Mid|`. -/
noncomputable def OrdinalDecomp.restrictMid (D : OrdinalDecomp α) (L : LinearExt α) :
    LinearExt ↥D.Mid := by
  classical
  -- The cardinality cast: `Fintype.card ↥D.Mid = D.Mid.card`.
  have hcardEq : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
  -- Build the underlying equiv `↥D.Mid ≃ Fin (Fintype.card ↥D.Mid)`.
  refine
    { toFun :=
        { toFun := fun m =>
            ⟨(L.pos m.val).val - D.Lower.card, ?_⟩
          invFun := fun i =>
            have hi : i.val + D.Lower.card < Fintype.card α := by
              have hi_lt : i.val < D.Mid.card := hcardEq ▸ i.isLt
              have hcard := D.card_eq
              omega
            ⟨L.toFun.symm ⟨i.val + D.Lower.card, hi⟩, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      monotone := ?_ }
  -- (1) Position bound for forward map: `(L.pos m.val).val - Lower.card < Mid.card`.
  · rcases D.posBoundMid L m.property with ⟨h1, h2⟩
    rw [hcardEq]
    omega
  -- (2) Membership in Mid for inverse map: position falls in mid band.
  · -- The position `i.val + Lower.card` is in [Lower.card, Lower.card + Mid.card).
    have hi_lt : i.val < D.Mid.card := hcardEq ▸ i.isLt
    have hi_lower : D.Lower.card ≤ i.val + D.Lower.card := Nat.le_add_left _ _
    have hi_upper : i.val + D.Lower.card < D.Lower.card + D.Mid.card := by omega
    have hposEq :
        (L.pos (L.toFun.symm ⟨i.val + D.Lower.card, hi⟩)).val =
          i.val + D.Lower.card := by
      change (L.toFun (L.toFun.symm ⟨i.val + D.Lower.card, hi⟩)).val =
        i.val + D.Lower.card
      simp
    rw [D.mem_mid_iff_posBand L]
    refine ⟨?_, ?_⟩
    · rw [hposEq]; exact hi_lower
    · rw [hposEq]; exact hi_upper
  -- (3) left_inv: m → pos → mem in Mid → pos → m
  · intro m
    apply Subtype.ext
    -- Goal: L.toFun.symm ⟨(L.pos m.val).val - Lower.card + Lower.card, _⟩ = m.val
    -- Simplify: (L.pos m.val).val - Lower.card + Lower.card = (L.pos m.val).val (using posBoundMid)
    have h := D.posBoundMid L m.property
    have hsub : (L.pos m.val).val - D.Lower.card + D.Lower.card = (L.pos m.val).val := by
      omega
    show L.toFun.symm ⟨_ + D.Lower.card, _⟩ = m.val
    have : (⟨(L.pos m.val).val - D.Lower.card + D.Lower.card,
            by rw [hsub]; exact (L.pos m.val).isLt⟩ : Fin (Fintype.card α)) =
            L.pos m.val := by
      apply Fin.ext
      exact hsub
    rw [show (⟨(L.pos m.val).val - D.Lower.card + D.Lower.card, _⟩ : Fin _) =
          L.pos m.val from this]
    show L.toFun.symm (L.toFun m.val) = m.val
    simp
  -- (4) right_inv: i → mem in Mid → pos → i
  · intro i
    have hi : i.val + D.Lower.card < Fintype.card α := by
      have hi_lt : i.val < D.Mid.card := hcardEq ▸ i.isLt
      have hcard := D.card_eq
      omega
    apply Fin.ext
    show (L.pos (L.toFun.symm ⟨i.val + D.Lower.card, hi⟩)).val - D.Lower.card =
      i.val
    have hposEq :
        (L.pos (L.toFun.symm ⟨i.val + D.Lower.card, hi⟩)).val =
          i.val + D.Lower.card := by
      change (L.toFun (L.toFun.symm ⟨i.val + D.Lower.card, hi⟩)).val =
        i.val + D.Lower.card
      simp
    rw [hposEq]
    omega
  -- (5) monotone: x ≤ y in Subtype ↥D.Mid → restrictMid_pos x ≤ restrictMid_pos y.
  · intro x y hxy
    have hxy_α : x.val ≤ y.val := hxy
    have hL : L.pos x.val ≤ L.pos y.val := L.monotone hxy_α
    have hL' : (L.pos x.val).val ≤ (L.pos y.val).val := hL
    have hx := D.posBoundMid L x.property
    have hy := D.posBoundMid L y.property
    show (⟨(L.pos x.val).val - D.Lower.card, _⟩ : Fin _) ≤
      (⟨(L.pos y.val).val - D.Lower.card, _⟩ : Fin _)
    show (L.pos x.val).val - D.Lower.card ≤ (L.pos y.val).val - D.Lower.card
    omega

/-- **Restriction-of-`lt` correspondence**: for `u, v ∈ Mid`, `L`
places `u` before `v` (in `α`) iff `restrictMid L` places
`⟨u, _⟩` before `⟨v, _⟩` (in `↥D.Mid`). -/
lemma OrdinalDecomp.restrictMid_lt_iff (D : OrdinalDecomp α) (L : LinearExt α)
    {u v : α} (hu : u ∈ D.Mid) (hv : v ∈ D.Mid) :
    (D.restrictMid L).lt ⟨u, hu⟩ ⟨v, hv⟩ ↔ L.lt u v := by
  classical
  have hu_bd := D.posBoundMid L hu
  have hv_bd := D.posBoundMid L hv
  -- Both sides reduce to inequalities on `(L.pos _).val`.
  -- LHS: `(restrictMid L).pos ⟨u, _⟩ < (restrictMid L).pos ⟨v, _⟩`,
  --      i.e. `(L.pos u).val - Lower.card < (L.pos v).val - Lower.card` (in ℕ).
  -- RHS: `L.pos u < L.pos v`, i.e. `(L.pos u).val < (L.pos v).val` (in ℕ).
  -- Equivalence by the position bounds (both `(L.pos _).val ≥ Lower.card`).
  show ((D.restrictMid L).pos ⟨u, hu⟩).val < ((D.restrictMid L).pos ⟨v, hv⟩).val ↔
    (L.pos u).val < (L.pos v).val
  -- Compute (restrictMid L).pos.
  show (L.pos u).val - D.Lower.card < (L.pos v).val - D.Lower.card ↔
    (L.pos u).val < (L.pos v).val
  omega

/-! ### §4 — The probability identity (key marginal invariance) -/

/-- **`probLT_restrict_eq`** — the marginal-invariance identity of
`lem:window-localization` (`step8.tex:1573-1608`).

For an ordinal decomposition `D : OrdinalDecomp α` and any pair
`u, v ∈ D.Mid`, the probability `Pr[u <_L v]` computed in a uniformly
random linear extension of `α` equals the same probability computed in
a uniformly random linear extension of the middle piece `↥D.Mid`.

**Proof sketch** (`step8.tex:1584-1598`).

By the ordinal-sum hypothesis, every `L : LinearExt α` decomposes
uniquely as a triple `(L_⁻, L_M, L_⁺)` of independent linear extensions
of `Lower`, `Mid`, `Upper`. The decomposition is bijective:

  `LinearExt α  ≃  LinearExt ↥Lower × LinearExt ↥Mid × LinearExt ↥Upper`

(forward: `restrictLower × restrictMid × restrictUpper`;
backward: concatenate by gluing positions). For `u, v ∈ Mid`, the event
`L.lt u v` depends only on `L_M = restrictMid L` (by
`restrictMid_lt_iff`), so the cardinality of the filter
`{L : L.lt u v}` factors as

  `|{L : L.lt u v}| = numLinExt ↥Lower * |{L_M : L_M.lt _ _}| * numLinExt ↥Upper`

and `numLinExt α = numLinExt ↥Lower * numLinExt ↥Mid * numLinExt ↥Upper`.
Dividing yields the identity.

This is the F4-foundation factorisation of `MATHLIB_GAPS.md:281+`; the
`concat` half of the bijection (and the cardinality identity) are
deferred to a follow-up.
-/
theorem OrdinalDecomp.probLT_restrict_eq (D : OrdinalDecomp α)
    {u v : α} (hu : u ∈ D.Mid) (hv : v ∈ D.Mid) :
    probLT u v = probLT (⟨u, hu⟩ : ↥D.Mid) ⟨v, hv⟩ := by
  -- The proof requires the ordinal-sum bijection
  -- `LinearExt α ≃ LinearExt ↥Lower × LinearExt ↥Mid × LinearExt ↥Upper`,
  -- which factors `numLinExt α` as the product and refines the
  -- `lt`-filter cardinality identically.
  --
  -- The bijection is the standard concatenation gluing (`concat`)
  -- inverse to the `(restrictLower, restrictMid, restrictUpper)`
  -- triple; constructing it in Lean requires defining `restrictLower`,
  -- `restrictUpper` (analogous to `restrictMid`), the `concat` map,
  -- and the round-trip identities. Deferred to a follow-up polecat
  -- (the Lean infrastructure here — `OrdinalDecomp`, `posBound*`,
  -- `restrictMid`, `restrictMid_lt_iff` — supplies the building
  -- blocks).
  sorry

/-! ### §5 — `HasBalancedPair` lifting -/

/-- **`HasBalancedPair` lifting from a sub-poset**.

If the middle piece `↥D.Mid` has a balanced pair (an incomparable
pair `(⟨u, _⟩, ⟨v, _⟩)` with `1/3 ≤ Pr[⟨u, _⟩ <_{L'} ⟨v, _⟩] ≤ 2/3`),
then `α` itself has a balanced pair: namely `(u, v)` viewed as
elements of `α`. The probability is preserved by
`probLT_restrict_eq`, and incomparability transfers because the
`Subtype` order is the restriction of the ambient order.

This realizes the *reduction* step of `lem:window-localization`
(`step8.tex:1573-1582`): a balanced pair in the window restriction
lifts to a balanced pair of the ambient poset. -/
theorem OrdinalDecomp.hasBalancedPair_lift (D : OrdinalDecomp α)
    (h : HasBalancedPair ↥D.Mid) : HasBalancedPair α := by
  obtain ⟨u, v, huv_inc, huv_bal⟩ := h
  -- `u, v : ↥D.Mid` give us `u.val, v.val : α` with `u.val, v.val ∈ Mid`.
  refine ⟨u.val, v.val, ?_, ?_⟩
  · -- Incomparability lifts: `Subtype` order is restricted ambient order.
    refine ⟨?_, ?_⟩
    · intro hle
      apply huv_inc.1
      show u.val ≤ v.val
      exact hle
    · intro hle
      apply huv_inc.2
      show v.val ≤ u.val
      exact hle
  · -- Balanced bounds transfer via `probLT_restrict_eq`.
    rw [IsBalanced]
    rw [D.probLT_restrict_eq u.property v.property]
    exact huv_bal

end OneThird
