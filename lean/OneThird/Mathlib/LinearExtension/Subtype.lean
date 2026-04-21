/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.LinearExtension
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

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

/-- **Position-band trichotomy, lower**: `x ∈ Lower` iff the position
of `x` (in any linear extension) is strictly below `|Lower|`. -/
lemma OrdinalDecomp.mem_lower_iff_pos_lt (D : OrdinalDecomp α) (L : LinearExt α)
    (x : α) : x ∈ D.Lower ↔ (L.pos x).val < D.Lower.card := by
  refine ⟨fun hx => D.posBoundLower L hx, ?_⟩
  intro h
  rcases D.mem_cases x with hL | hM | hU
  · exact hL
  · exact absurd (D.posBoundMid L hM).1 (by omega)
  · exact absurd (D.posBoundUpper L hU) (by omega)

/-- **Position-band trichotomy, upper**: `x ∈ Upper` iff the position
of `x` (in any linear extension) is at least `|Lower| + |Mid|`. -/
lemma OrdinalDecomp.mem_upper_iff_pos_ge (D : OrdinalDecomp α) (L : LinearExt α)
    (x : α) :
    x ∈ D.Upper ↔ D.Lower.card + D.Mid.card ≤ (L.pos x).val := by
  refine ⟨fun hx => D.posBoundUpper L hx, ?_⟩
  intro h
  rcases D.mem_cases x with hL | hM | hU
  · exact absurd (D.posBoundLower L hL) (by omega)
  · exact absurd (D.posBoundMid L hM).2 (by omega)
  · exact hU

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

/-! ### §3b — Restrictions to lower and upper pieces -/

/-- **Restriction to the lower piece**: every linear extension `L` of
`α` induces a linear extension of `↥D.Lower` by relabeling the
positions of `Lower`-elements (which occupy `[0, |Lower|)` by
`posBoundLower`) as `Fin |Lower|`. -/
noncomputable def OrdinalDecomp.restrictLower (D : OrdinalDecomp α) (L : LinearExt α) :
    LinearExt ↥D.Lower := by
  classical
  have hcardEq : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
  refine
    { toFun :=
        { toFun := fun m =>
            ⟨(L.pos m.val).val, ?_⟩
          invFun := fun i =>
            have hi : i.val < Fintype.card α := by
              have hi_lt : i.val < D.Lower.card := hcardEq ▸ i.isLt
              have hcard := D.card_eq
              omega
            ⟨L.toFun.symm ⟨i.val, hi⟩, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      monotone := ?_ }
  -- forward bound: position < Lower.card
  · have h := D.posBoundLower L m.property
    rw [hcardEq]
    exact h
  -- inverse lands in Lower
  · have hi_lt : i.val < D.Lower.card := hcardEq ▸ i.isLt
    have hposEq :
        (L.pos (L.toFun.symm ⟨i.val, hi⟩)).val = i.val := by
      change (L.toFun (L.toFun.symm ⟨i.val, hi⟩)).val = i.val
      simp
    rw [D.mem_lower_iff_pos_lt L, hposEq]
    exact hi_lt
  -- left_inv
  · intro m
    apply Subtype.ext
    have hsub :
        (⟨(L.pos m.val).val, (L.pos m.val).isLt⟩ : Fin (Fintype.card α)) =
          L.pos m.val := Fin.ext rfl
    change L.toFun.symm ⟨(L.pos m.val).val, _⟩ = m.val
    rw [show (⟨(L.pos m.val).val, _⟩ : Fin _) = L.pos m.val from hsub]
    change L.toFun.symm (L.toFun m.val) = m.val
    simp
  -- right_inv
  · intro i
    apply Fin.ext
    change (L.pos (L.toFun.symm ⟨i.val, _⟩)).val = i.val
    change (L.toFun (L.toFun.symm ⟨i.val, _⟩)).val = i.val
    simp
  -- monotone
  · intro x y hxy
    have hxy_α : x.val ≤ y.val := hxy
    have hL : L.pos x.val ≤ L.pos y.val := L.monotone hxy_α
    have hL' : (L.pos x.val).val ≤ (L.pos y.val).val := hL
    show (⟨(L.pos x.val).val, _⟩ : Fin _) ≤ (⟨(L.pos y.val).val, _⟩ : Fin _)
    show (L.pos x.val).val ≤ (L.pos y.val).val
    exact hL'

/-- **Restriction to the upper piece**: every linear extension `L` of
`α` induces a linear extension of `↥D.Upper` by relabeling the
positions of `Upper`-elements (which occupy `[|Lower|+|Mid|, n)` by
`posBoundUpper`) as `Fin |Upper|`. -/
noncomputable def OrdinalDecomp.restrictUpper (D : OrdinalDecomp α) (L : LinearExt α) :
    LinearExt ↥D.Upper := by
  classical
  have hcardEq : Fintype.card ↥D.Upper = D.Upper.card := Fintype.card_coe _
  refine
    { toFun :=
        { toFun := fun m =>
            ⟨(L.pos m.val).val - D.Lower.card - D.Mid.card, ?_⟩
          invFun := fun i =>
            have hi : i.val + D.Lower.card + D.Mid.card < Fintype.card α := by
              have hi_lt : i.val < D.Upper.card := hcardEq ▸ i.isLt
              have hcard := D.card_eq
              omega
            ⟨L.toFun.symm ⟨i.val + D.Lower.card + D.Mid.card, hi⟩, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      monotone := ?_ }
  -- forward bound
  · have h := D.posBoundUpper L m.property
    have hlt : (L.pos m.val).val < Fintype.card α := (L.pos m.val).isLt
    have hcard := D.card_eq
    rw [hcardEq]
    omega
  -- inverse lands in Upper
  · have hi_lt : i.val < D.Upper.card := hcardEq ▸ i.isLt
    have hposEq :
        (L.pos (L.toFun.symm ⟨i.val + D.Lower.card + D.Mid.card, hi⟩)).val =
          i.val + D.Lower.card + D.Mid.card := by
      change (L.toFun (L.toFun.symm _)).val = _
      simp
    rw [D.mem_upper_iff_pos_ge L, hposEq]
    omega
  -- left_inv
  · intro m
    apply Subtype.ext
    have h := D.posBoundUpper L m.property
    have hsub :
        (L.pos m.val).val - D.Lower.card - D.Mid.card + D.Lower.card + D.Mid.card =
          (L.pos m.val).val := by omega
    change L.toFun.symm
        ⟨(L.pos m.val).val - D.Lower.card - D.Mid.card + D.Lower.card + D.Mid.card, _⟩
        = m.val
    have heq :
        (⟨(L.pos m.val).val - D.Lower.card - D.Mid.card + D.Lower.card + D.Mid.card,
            by rw [hsub]; exact (L.pos m.val).isLt⟩ : Fin (Fintype.card α)) =
          L.pos m.val := Fin.ext hsub
    rw [heq]
    change L.toFun.symm (L.toFun m.val) = m.val
    simp
  -- right_inv
  · intro i
    have hi : i.val + D.Lower.card + D.Mid.card < Fintype.card α := by
      have hi_lt : i.val < D.Upper.card := hcardEq ▸ i.isLt
      have hcard := D.card_eq
      omega
    apply Fin.ext
    show (L.pos (L.toFun.symm ⟨i.val + D.Lower.card + D.Mid.card, hi⟩)).val
        - D.Lower.card - D.Mid.card = i.val
    have hposEq :
        (L.pos (L.toFun.symm ⟨i.val + D.Lower.card + D.Mid.card, hi⟩)).val =
          i.val + D.Lower.card + D.Mid.card := by
      change (L.toFun (L.toFun.symm _)).val = _
      simp
    rw [hposEq]
    omega
  -- monotone
  · intro x y hxy
    have hxy_α : x.val ≤ y.val := hxy
    have hL : L.pos x.val ≤ L.pos y.val := L.monotone hxy_α
    have hL' : (L.pos x.val).val ≤ (L.pos y.val).val := hL
    have hx := D.posBoundUpper L x.property
    have hy := D.posBoundUpper L y.property
    show (⟨(L.pos x.val).val - D.Lower.card - D.Mid.card, _⟩ : Fin _) ≤
      (⟨(L.pos y.val).val - D.Lower.card - D.Mid.card, _⟩ : Fin _)
    show (L.pos x.val).val - D.Lower.card - D.Mid.card ≤
      (L.pos y.val).val - D.Lower.card - D.Mid.card
    omega

/-! ### §4 — Concatenation: gluing three linear extensions -/

/-- **Forward concat map** on elements: given three piece-linear
extensions, assign to each `x : α` a position in `Fin (Fintype.card α)`
according to the membership piece. -/
noncomputable def OrdinalDecomp.concatForward (D : OrdinalDecomp α)
    (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid) (LU : LinearExt ↥D.Upper)
    (x : α) : Fin (Fintype.card α) := by
  classical
  have hcardL : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
  have hcardM : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
  have hcardU : Fintype.card ↥D.Upper = D.Upper.card := Fintype.card_coe _
  have hcardEq : Fintype.card α = D.Lower.card + D.Mid.card + D.Upper.card := D.card_eq
  exact
    if hL : x ∈ D.Lower then
      ⟨(LL.pos ⟨x, hL⟩).val, by
        have h1 : (LL.pos ⟨x, hL⟩).val < Fintype.card ↥D.Lower := (LL.pos ⟨x, hL⟩).isLt
        omega⟩
    else if hM : x ∈ D.Mid then
      ⟨(LM.pos ⟨x, hM⟩).val + D.Lower.card, by
        have h1 : (LM.pos ⟨x, hM⟩).val < Fintype.card ↥D.Mid := (LM.pos ⟨x, hM⟩).isLt
        omega⟩
    else
      have hU : x ∈ D.Upper :=
        (D.mem_cases x).resolve_left hL |>.resolve_left hM
      ⟨(LU.pos ⟨x, hU⟩).val + D.Lower.card + D.Mid.card, by
        have h1 : (LU.pos ⟨x, hU⟩).val < Fintype.card ↥D.Upper := (LU.pos ⟨x, hU⟩).isLt
        omega⟩

/-- **Backward concat map**: given a position `i : Fin n`, recover
the element in the appropriate piece by inverting the relevant
piece-linear extension. -/
noncomputable def OrdinalDecomp.concatBackward (D : OrdinalDecomp α)
    (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid) (LU : LinearExt ↥D.Upper)
    (i : Fin (Fintype.card α)) : α := by
  classical
  have hcardL : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
  have hcardM : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
  have hcardU : Fintype.card ↥D.Upper = D.Upper.card := Fintype.card_coe _
  have hcardEq : Fintype.card α = D.Lower.card + D.Mid.card + D.Upper.card := D.card_eq
  exact
    if h1 : i.val < D.Lower.card then
      (LL.toFun.symm ⟨i.val, by omega⟩ : ↥D.Lower).val
    else if h2 : i.val < D.Lower.card + D.Mid.card then
      (LM.toFun.symm ⟨i.val - D.Lower.card, by omega⟩ : ↥D.Mid).val
    else
      (LU.toFun.symm ⟨i.val - D.Lower.card - D.Mid.card, by
        have := i.isLt
        omega⟩ : ↥D.Upper).val

/-- `.val`-level unfold of `concatForward` on `Lower`. -/
lemma OrdinalDecomp.concatForward_val_of_mem_lower
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {x : α} (hx : x ∈ D.Lower) :
    (D.concatForward LL LM LU x).val = (LL.pos ⟨x, hx⟩).val := by
  classical
  unfold OrdinalDecomp.concatForward
  rw [dif_pos hx]

/-- `.val`-level unfold of `concatForward` on `Mid`. -/
lemma OrdinalDecomp.concatForward_val_of_mem_mid
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {x : α} (hx : x ∈ D.Mid) :
    (D.concatForward LL LM LU x).val = (LM.pos ⟨x, hx⟩).val + D.Lower.card := by
  classical
  have hL : x ∉ D.Lower := Finset.disjoint_right.mp D.hDisjLM hx
  unfold OrdinalDecomp.concatForward
  rw [dif_neg hL, dif_pos hx]

/-- `.val`-level unfold of `concatForward` on `Upper`. -/
lemma OrdinalDecomp.concatForward_val_of_mem_upper
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {x : α} (hx : x ∈ D.Upper) :
    (D.concatForward LL LM LU x).val =
      (LU.pos ⟨x, hx⟩).val + D.Lower.card + D.Mid.card := by
  classical
  have hL : x ∉ D.Lower := Finset.disjoint_right.mp D.hDisjLU hx
  have hM : x ∉ D.Mid := Finset.disjoint_right.mp D.hDisjMU hx
  unfold OrdinalDecomp.concatForward
  rw [dif_neg hL, dif_neg hM]

/-- Concat position bound: `concatForward x` has `.val < Lower.card` iff `x ∈ Lower`. -/
lemma OrdinalDecomp.concatForward_mem_lower_iff
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) (x : α) :
    (D.concatForward LL LM LU x).val < D.Lower.card ↔ x ∈ D.Lower := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases D.mem_cases x with hL | hM | hU
    · exact hL
    · rw [D.concatForward_val_of_mem_mid _ _ _ hM] at h; omega
    · rw [D.concatForward_val_of_mem_upper _ _ _ hU] at h; omega
  · intro hx
    rw [D.concatForward_val_of_mem_lower _ _ _ hx]
    have h1 : (LL.pos ⟨x, hx⟩).val < Fintype.card ↥D.Lower := (LL.pos ⟨x, hx⟩).isLt
    have hcardL : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
    omega

/-- Concat position bound: `concatForward x` has `.val < Lower.card + Mid.card` iff
`x ∈ Lower ∨ x ∈ Mid`. -/
lemma OrdinalDecomp.concatForward_lt_lower_add_mid_iff
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) (x : α) :
    (D.concatForward LL LM LU x).val < D.Lower.card + D.Mid.card ↔
      (x ∈ D.Lower ∨ x ∈ D.Mid) := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases D.mem_cases x with hL | hM | hU
    · exact Or.inl hL
    · exact Or.inr hM
    · rw [D.concatForward_val_of_mem_upper _ _ _ hU] at h; omega
  · rintro (hx | hx)
    · rw [D.concatForward_val_of_mem_lower _ _ _ hx]
      have h1 : (LL.pos ⟨x, hx⟩).val < Fintype.card ↥D.Lower := (LL.pos ⟨x, hx⟩).isLt
      have hcardL : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
      omega
    · rw [D.concatForward_val_of_mem_mid _ _ _ hx]
      have h1 : (LM.pos ⟨x, hx⟩).val < Fintype.card ↥D.Mid := (LM.pos ⟨x, hx⟩).isLt
      have hcardM : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
      omega

/-- `.val`-level unfold of `concatBackward` in the lower range. -/
lemma OrdinalDecomp.concatBackward_of_lt_lower
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {i : Fin (Fintype.card α)} (h : i.val < D.Lower.card) :
    D.concatBackward LL LM LU i =
      (LL.toFun.symm ⟨i.val, by
        have : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
        omega⟩ : ↥D.Lower).val := by
  classical
  unfold OrdinalDecomp.concatBackward
  rw [dif_pos h]

/-- `concatBackward` lands in `Lower` when position is below `Lower.card`. -/
lemma OrdinalDecomp.concatBackward_mem_lower
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {i : Fin (Fintype.card α)} (h : i.val < D.Lower.card) :
    D.concatBackward LL LM LU i ∈ D.Lower := by
  rw [D.concatBackward_of_lt_lower _ _ _ h]
  exact (LL.toFun.symm _).property

/-- `.val`-level unfold of `concatBackward` in the mid range. -/
lemma OrdinalDecomp.concatBackward_of_mem_mid_band
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {i : Fin (Fintype.card α)}
    (h1 : ¬ i.val < D.Lower.card) (h2 : i.val < D.Lower.card + D.Mid.card) :
    D.concatBackward LL LM LU i =
      (LM.toFun.symm ⟨i.val - D.Lower.card, by
        have : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
        omega⟩ : ↥D.Mid).val := by
  classical
  unfold OrdinalDecomp.concatBackward
  rw [dif_neg h1, dif_pos h2]

/-- `concatBackward` lands in `Mid` in the mid band. -/
lemma OrdinalDecomp.concatBackward_mem_mid
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {i : Fin (Fintype.card α)}
    (h1 : ¬ i.val < D.Lower.card) (h2 : i.val < D.Lower.card + D.Mid.card) :
    D.concatBackward LL LM LU i ∈ D.Mid := by
  rw [D.concatBackward_of_mem_mid_band _ _ _ h1 h2]
  exact (LM.toFun.symm _).property

/-- `.val`-level unfold of `concatBackward` in the upper range. -/
lemma OrdinalDecomp.concatBackward_of_not_lt_lm
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {i : Fin (Fintype.card α)}
    (h1 : ¬ i.val < D.Lower.card) (h2 : ¬ i.val < D.Lower.card + D.Mid.card) :
    D.concatBackward LL LM LU i =
      (LU.toFun.symm ⟨i.val - D.Lower.card - D.Mid.card, by
        have hc : Fintype.card ↥D.Upper = D.Upper.card := Fintype.card_coe _
        have := i.isLt
        have := D.card_eq
        omega⟩ : ↥D.Upper).val := by
  classical
  unfold OrdinalDecomp.concatBackward
  rw [dif_neg h1, dif_neg h2]

/-- `concatBackward` lands in `Upper` in the upper band. -/
lemma OrdinalDecomp.concatBackward_mem_upper
    (D : OrdinalDecomp α) (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid)
    (LU : LinearExt ↥D.Upper) {i : Fin (Fintype.card α)}
    (h1 : ¬ i.val < D.Lower.card) (h2 : ¬ i.val < D.Lower.card + D.Mid.card) :
    D.concatBackward LL LM LU i ∈ D.Upper := by
  rw [D.concatBackward_of_not_lt_lm _ _ _ h1 h2]
  exact (LU.toFun.symm _).property

/-- **Concat**: build a linear extension of `α` from piece-linear
extensions of `Lower`, `Mid`, `Upper`. -/
noncomputable def OrdinalDecomp.concat (D : OrdinalDecomp α)
    (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid) (LU : LinearExt ↥D.Upper) :
    LinearExt α := by
  classical
  refine
    { toFun :=
        { toFun := D.concatForward LL LM LU
          invFun := D.concatBackward LL LM LU
          left_inv := ?_
          right_inv := ?_ }
      monotone := ?_ }
  -- left_inv : ∀ x, concatBackward (concatForward x) = x
  · intro x
    rcases D.mem_cases x with hx | hx | hx
    · -- x ∈ Lower
      have hval : (D.concatForward LL LM LU x).val < D.Lower.card :=
        (D.concatForward_mem_lower_iff _ _ _ _).mpr hx
      rw [D.concatBackward_of_lt_lower _ _ _ hval]
      have hposEq :
          (⟨(D.concatForward LL LM LU x).val, by
              rw [Fintype.card_coe]; exact hval⟩ :
              Fin (Fintype.card ↥D.Lower)) = LL.pos ⟨x, hx⟩ := by
        apply Fin.ext
        show (D.concatForward LL LM LU x).val = (LL.pos ⟨x, hx⟩).val
        exact D.concatForward_val_of_mem_lower _ _ _ hx
      rw [hposEq]
      show (LL.toFun.symm (LL.toFun ⟨x, hx⟩) : ↥D.Lower).val = x
      simp
    · -- x ∈ Mid
      have hnotL : ¬ (D.concatForward LL LM LU x).val < D.Lower.card := by
        rw [D.concatForward_val_of_mem_mid _ _ _ hx]; omega
      have hlt_sum : (D.concatForward LL LM LU x).val < D.Lower.card + D.Mid.card :=
        (D.concatForward_lt_lower_add_mid_iff _ _ _ _).mpr (Or.inr hx)
      rw [D.concatBackward_of_mem_mid_band _ _ _ hnotL hlt_sum]
      have hposEq :
          (⟨(D.concatForward LL LM LU x).val - D.Lower.card, by
              rw [Fintype.card_coe]; omega⟩ :
              Fin (Fintype.card ↥D.Mid)) = LM.pos ⟨x, hx⟩ := by
        apply Fin.ext
        show (D.concatForward LL LM LU x).val - D.Lower.card = (LM.pos ⟨x, hx⟩).val
        rw [D.concatForward_val_of_mem_mid _ _ _ hx]
        omega
      rw [hposEq]
      show (LM.toFun.symm (LM.toFun ⟨x, hx⟩) : ↥D.Mid).val = x
      simp
    · -- x ∈ Upper
      have hnotL : ¬ (D.concatForward LL LM LU x).val < D.Lower.card := by
        rw [D.concatForward_val_of_mem_upper _ _ _ hx]; omega
      have hnotM : ¬ (D.concatForward LL LM LU x).val < D.Lower.card + D.Mid.card := by
        rw [D.concatForward_val_of_mem_upper _ _ _ hx]; omega
      rw [D.concatBackward_of_not_lt_lm _ _ _ hnotL hnotM]
      have hposEq :
          (⟨(D.concatForward LL LM LU x).val - D.Lower.card - D.Mid.card, by
              rw [Fintype.card_coe]
              have := (D.concatForward LL LM LU x).isLt
              have := D.card_eq
              omega⟩ :
              Fin (Fintype.card ↥D.Upper)) = LU.pos ⟨x, hx⟩ := by
        apply Fin.ext
        show (D.concatForward LL LM LU x).val - D.Lower.card - D.Mid.card =
          (LU.pos ⟨x, hx⟩).val
        rw [D.concatForward_val_of_mem_upper _ _ _ hx]
        omega
      rw [hposEq]
      show (LU.toFun.symm (LU.toFun ⟨x, hx⟩) : ↥D.Upper).val = x
      simp
  -- right_inv : ∀ i, concatForward (concatBackward i) = i
  · intro i
    by_cases h1 : i.val < D.Lower.card
    · apply Fin.ext
      -- First rewrite concatBackward; result has (LL.toFun.symm ⟨i.val, _⟩).val
      -- which lives in D.Lower via .property.
      rw [D.concatBackward_of_lt_lower LL LM LU h1]
      set y : ↥D.Lower := LL.toFun.symm ⟨i.val, by
        have : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
        omega⟩ with hy_def
      rw [D.concatForward_val_of_mem_lower LL LM LU y.property]
      change (LL.toFun ⟨y.val, y.property⟩ : Fin _).val = i.val
      have hsub : (⟨y.val, y.property⟩ : ↥D.Lower) = y := Subtype.ext rfl
      rw [hsub, hy_def]
      change (LL.toFun (LL.toFun.symm _)).val = i.val
      rw [Equiv.apply_symm_apply]
    · by_cases h2 : i.val < D.Lower.card + D.Mid.card
      · apply Fin.ext
        rw [D.concatBackward_of_mem_mid_band LL LM LU h1 h2]
        set y : ↥D.Mid := LM.toFun.symm ⟨i.val - D.Lower.card, by
          have : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
          omega⟩ with hy_def
        rw [D.concatForward_val_of_mem_mid LL LM LU y.property]
        change (LM.toFun ⟨y.val, y.property⟩ : Fin _).val + D.Lower.card = i.val
        have hsub : (⟨y.val, y.property⟩ : ↥D.Mid) = y := Subtype.ext rfl
        rw [hsub, hy_def]
        change (LM.toFun (LM.toFun.symm _)).val + D.Lower.card = i.val
        rw [Equiv.apply_symm_apply]
        show (i.val - D.Lower.card) + D.Lower.card = i.val
        omega
      · apply Fin.ext
        rw [D.concatBackward_of_not_lt_lm LL LM LU h1 h2]
        set y : ↥D.Upper := LU.toFun.symm ⟨i.val - D.Lower.card - D.Mid.card, by
          have : Fintype.card ↥D.Upper = D.Upper.card := Fintype.card_coe _
          have := i.isLt
          have := D.card_eq
          omega⟩ with hy_def
        rw [D.concatForward_val_of_mem_upper LL LM LU y.property]
        change (LU.toFun ⟨y.val, y.property⟩ : Fin _).val + D.Lower.card +
          D.Mid.card = i.val
        have hsub : (⟨y.val, y.property⟩ : ↥D.Upper) = y := Subtype.ext rfl
        rw [hsub, hy_def]
        change (LU.toFun (LU.toFun.symm _)).val + D.Lower.card + D.Mid.card = i.val
        rw [Equiv.apply_symm_apply]
        have := i.isLt
        have := D.card_eq
        show (i.val - D.Lower.card - D.Mid.card) + D.Lower.card + D.Mid.card = i.val
        omega
  -- monotone
  · intro x y hxy
    show (D.concatForward LL LM LU x).val ≤ (D.concatForward LL LM LU y).val
    rcases D.mem_cases x with hxL | hxM | hxU <;>
      rcases D.mem_cases y with hyL | hyM | hyU
    -- x ∈ Lower, y ∈ Lower
    · rw [D.concatForward_val_of_mem_lower _ _ _ hxL,
          D.concatForward_val_of_mem_lower _ _ _ hyL]
      have : LL.pos ⟨x, hxL⟩ ≤ LL.pos ⟨y, hyL⟩ := LL.monotone hxy
      exact this
    -- x ∈ Lower, y ∈ Mid
    · rw [D.concatForward_val_of_mem_lower _ _ _ hxL,
          D.concatForward_val_of_mem_mid _ _ _ hyM]
      have h1 : (LL.pos ⟨x, hxL⟩).val < Fintype.card ↥D.Lower :=
        (LL.pos ⟨x, hxL⟩).isLt
      have hcardL : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
      omega
    -- x ∈ Lower, y ∈ Upper
    · rw [D.concatForward_val_of_mem_lower _ _ _ hxL,
          D.concatForward_val_of_mem_upper _ _ _ hyU]
      have h1 : (LL.pos ⟨x, hxL⟩).val < Fintype.card ↥D.Lower :=
        (LL.pos ⟨x, hxL⟩).isLt
      have hcardL : Fintype.card ↥D.Lower = D.Lower.card := Fintype.card_coe _
      omega
    -- x ∈ Mid, y ∈ Lower: contradiction (y < x)
    · have hlt : y < x := D.hLM_lt y hyL x hxM
      exact absurd (lt_of_lt_of_le hlt hxy) (lt_irrefl _)
    -- x ∈ Mid, y ∈ Mid
    · rw [D.concatForward_val_of_mem_mid _ _ _ hxM,
          D.concatForward_val_of_mem_mid _ _ _ hyM]
      have : LM.pos ⟨x, hxM⟩ ≤ LM.pos ⟨y, hyM⟩ := LM.monotone hxy
      have hle : (LM.pos ⟨x, hxM⟩).val ≤ (LM.pos ⟨y, hyM⟩).val := this
      omega
    -- x ∈ Mid, y ∈ Upper
    · rw [D.concatForward_val_of_mem_mid _ _ _ hxM,
          D.concatForward_val_of_mem_upper _ _ _ hyU]
      have h1 : (LM.pos ⟨x, hxM⟩).val < Fintype.card ↥D.Mid :=
        (LM.pos ⟨x, hxM⟩).isLt
      have hcardM : Fintype.card ↥D.Mid = D.Mid.card := Fintype.card_coe _
      omega
    -- x ∈ Upper, y ∈ Lower: contradiction
    · have hlt : y < x := D.hLU_lt y hyL x hxU
      exact absurd (lt_of_lt_of_le hlt hxy) (lt_irrefl _)
    -- x ∈ Upper, y ∈ Mid: contradiction
    · have hlt : y < x := D.hMU_lt y hyM x hxU
      exact absurd (lt_of_lt_of_le hlt hxy) (lt_irrefl _)
    -- x ∈ Upper, y ∈ Upper
    · rw [D.concatForward_val_of_mem_upper _ _ _ hxU,
          D.concatForward_val_of_mem_upper _ _ _ hyU]
      have : LU.pos ⟨x, hxU⟩ ≤ LU.pos ⟨y, hyU⟩ := LU.monotone hxy
      have hle : (LU.pos ⟨x, hxU⟩).val ≤ (LU.pos ⟨y, hyU⟩).val := this
      omega

/-! ### §5 — Round-trip: restrict ↔ concat -/

/-- `restrictLower` of `concat` is the Lower piece. -/
lemma OrdinalDecomp.restrictLower_concat (D : OrdinalDecomp α)
    (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid) (LU : LinearExt ↥D.Upper) :
    D.restrictLower (D.concat LL LM LU) = LL := by
  apply LinearExt.ext
  apply Equiv.ext
  intro m
  apply Fin.ext
  -- LHS: ((restrictLower (concat ...)).toFun m).val
  --    = ((concat...).pos m.val).val = (concatForward m.val).val
  -- RHS: (LL.toFun m).val
  change ((D.concat LL LM LU).pos m.val).val = (LL.toFun m).val
  change (D.concatForward LL LM LU m.val).val = (LL.toFun m).val
  rw [D.concatForward_val_of_mem_lower _ _ _ m.property]
  rfl

/-- `restrictMid` of `concat` is the Mid piece. -/
lemma OrdinalDecomp.restrictMid_concat (D : OrdinalDecomp α)
    (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid) (LU : LinearExt ↥D.Upper) :
    D.restrictMid (D.concat LL LM LU) = LM := by
  apply LinearExt.ext
  apply Equiv.ext
  intro m
  apply Fin.ext
  change ((D.concat LL LM LU).pos m.val).val - D.Lower.card = (LM.toFun m).val
  change (D.concatForward LL LM LU m.val).val - D.Lower.card = (LM.toFun m).val
  rw [D.concatForward_val_of_mem_mid _ _ _ m.property]
  show (LM.pos ⟨m.val, m.property⟩).val + D.Lower.card - D.Lower.card = (LM.toFun m).val
  show (LM.toFun m).val + D.Lower.card - D.Lower.card = (LM.toFun m).val
  omega

/-- `restrictUpper` of `concat` is the Upper piece. -/
lemma OrdinalDecomp.restrictUpper_concat (D : OrdinalDecomp α)
    (LL : LinearExt ↥D.Lower) (LM : LinearExt ↥D.Mid) (LU : LinearExt ↥D.Upper) :
    D.restrictUpper (D.concat LL LM LU) = LU := by
  apply LinearExt.ext
  apply Equiv.ext
  intro m
  apply Fin.ext
  change ((D.concat LL LM LU).pos m.val).val - D.Lower.card - D.Mid.card =
    (LU.toFun m).val
  change (D.concatForward LL LM LU m.val).val - D.Lower.card - D.Mid.card =
    (LU.toFun m).val
  rw [D.concatForward_val_of_mem_upper _ _ _ m.property]
  show (LU.pos ⟨m.val, m.property⟩).val + D.Lower.card + D.Mid.card - D.Lower.card
      - D.Mid.card = (LU.toFun m).val
  show (LU.toFun m).val + D.Lower.card + D.Mid.card - D.Lower.card - D.Mid.card =
    (LU.toFun m).val
  omega

/-- Inverse direction: `concat (restrictLower L) (restrictMid L) (restrictUpper L) = L`. -/
lemma OrdinalDecomp.concat_restrict (D : OrdinalDecomp α) (L : LinearExt α) :
    D.concat (D.restrictLower L) (D.restrictMid L) (D.restrictUpper L) = L := by
  apply LinearExt.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (D.concatForward (D.restrictLower L) (D.restrictMid L)
      (D.restrictUpper L) x).val = (L.toFun x).val
  rcases D.mem_cases x with hx | hx | hx
  · rw [D.concatForward_val_of_mem_lower _ _ _ hx]
    -- (restrictLower L).pos ⟨x, hx⟩ = ⟨(L.pos x).val, _⟩
    change ((D.restrictLower L).toFun ⟨x, hx⟩ : Fin _).val = (L.toFun x).val
    rfl
  · rw [D.concatForward_val_of_mem_mid _ _ _ hx]
    change ((D.restrictMid L).toFun ⟨x, hx⟩ : Fin _).val + D.Lower.card = (L.toFun x).val
    -- (restrictMid L).toFun ⟨x, hx⟩ = ⟨(L.pos x).val - Lower.card, _⟩
    show ((L.pos x).val - D.Lower.card) + D.Lower.card = (L.toFun x).val
    have := (D.posBoundMid L hx).1
    show (L.pos x).val - D.Lower.card + D.Lower.card = (L.pos x).val
    omega
  · rw [D.concatForward_val_of_mem_upper _ _ _ hx]
    change ((D.restrictUpper L).toFun ⟨x, hx⟩ : Fin _).val + D.Lower.card +
        D.Mid.card = (L.toFun x).val
    show ((L.pos x).val - D.Lower.card - D.Mid.card) + D.Lower.card + D.Mid.card =
      (L.toFun x).val
    have := D.posBoundUpper L hx
    show (L.pos x).val - D.Lower.card - D.Mid.card + D.Lower.card + D.Mid.card =
      (L.pos x).val
    omega

/-! ### §6 — Bijection and cardinality factorization -/

/-- **Triple Equiv**: `LinearExt α` decomposes as a product of piece-linear
extensions. -/
noncomputable def OrdinalDecomp.tripleEquiv (D : OrdinalDecomp α) :
    LinearExt α ≃ LinearExt ↥D.Lower × LinearExt ↥D.Mid × LinearExt ↥D.Upper where
  toFun L := ⟨D.restrictLower L, D.restrictMid L, D.restrictUpper L⟩
  invFun p := D.concat p.1 p.2.1 p.2.2
  left_inv L := D.concat_restrict L
  right_inv p := by
    rcases p with ⟨LL, LM, LU⟩
    simp only [Prod.mk.injEq]
    exact ⟨D.restrictLower_concat LL LM LU,
           D.restrictMid_concat LL LM LU,
           D.restrictUpper_concat LL LM LU⟩

/-- **numLinExt factorization**: `numLinExt α = numLinExt Lower * numLinExt Mid *
numLinExt Upper`. -/
theorem OrdinalDecomp.numLinExt_eq (D : OrdinalDecomp α) :
    numLinExt α = numLinExt ↥D.Lower * numLinExt ↥D.Mid * numLinExt ↥D.Upper := by
  unfold numLinExt
  rw [Fintype.card_congr D.tripleEquiv,
      Fintype.card_prod, Fintype.card_prod, ← mul_assoc]

/-! ### §7 — The probability identity (key marginal invariance) -/

/-- **`probLT_restrict_eq`** — the marginal-invariance identity of
`lem:window-localization` (`step8.tex:1573-1608`).

For an ordinal decomposition `D : OrdinalDecomp α` and any pair
`u, v ∈ D.Mid`, the probability `Pr[u <_L v]` computed in a uniformly
random linear extension of `α` equals the same probability computed in
a uniformly random linear extension of the middle piece `↥D.Mid`.

**Proof sketch** (`step8.tex:1584-1598`).

By the ordinal-sum hypothesis, the triple Equiv

  `LinearExt α  ≃  LinearExt ↥Lower × LinearExt ↥Mid × LinearExt ↥Upper`

via `(restrictLower, restrictMid, restrictUpper)` and `concat` factors
`numLinExt α` as the product and refines the `lt`-filter identically
(`L.lt u v ↔ (restrictMid L).lt ⟨u⟩ ⟨v⟩`). Division yields the
identity. -/
theorem OrdinalDecomp.probLT_restrict_eq (D : OrdinalDecomp α)
    {u v : α} (hu : u ∈ D.Mid) (hv : v ∈ D.Mid) :
    probLT u v = probLT (⟨u, hu⟩ : ↥D.Mid) ⟨v, hv⟩ := by
  classical
  -- Let e be the tripleEquiv; then the filter on LinearExt α is equivalent
  -- to the middle filter times LinearExt Lower × LinearExt Upper.
  -- Step 1: filter cardinality factorization via tripleEquiv
  have hfilter_card :
      (Finset.univ.filter (fun L : LinearExt α => L.lt u v)).card =
        numLinExt ↥D.Lower *
          (Finset.univ.filter
              (fun LM : LinearExt ↥D.Mid => LM.lt ⟨u, hu⟩ ⟨v, hv⟩)).card *
          numLinExt ↥D.Upper := by
    -- Via the equivalence of subtypes
    set S : Finset (LinearExt α) :=
      Finset.univ.filter (fun L : LinearExt α => L.lt u v)
    set T : Finset (LinearExt ↥D.Mid) :=
      Finset.univ.filter (fun LM : LinearExt ↥D.Mid => LM.lt ⟨u, hu⟩ ⟨v, hv⟩)
    -- Build an Equiv {L // L.lt u v} ≃ LinearExt Lower × {LM // LM.lt ..} × LinearExt Upper
    let e :
        {L : LinearExt α // L.lt u v} ≃
          LinearExt ↥D.Lower × {LM : LinearExt ↥D.Mid // LM.lt ⟨u, hu⟩ ⟨v, hv⟩} ×
            LinearExt ↥D.Upper := by
      refine
        { toFun := fun L => ⟨D.restrictLower L.val,
            ⟨D.restrictMid L.val, ?_⟩,
            D.restrictUpper L.val⟩
          invFun := fun p => ⟨D.concat p.1 p.2.1.val p.2.2, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      -- (1) property preserved forward
      · exact (D.restrictMid_lt_iff L.val hu hv).mpr L.property
      -- (2) property preserved backward
      · rcases p with ⟨LL, ⟨LM, hLM⟩, LU⟩
        show (D.concat LL LM LU).lt u v
        have : (D.restrictMid (D.concat LL LM LU)).lt ⟨u, hu⟩ ⟨v, hv⟩ := by
          rw [D.restrictMid_concat LL LM LU]; exact hLM
        exact (D.restrictMid_lt_iff _ hu hv).mp this
      -- (3) left_inv
      · intro L
        apply Subtype.ext
        exact D.concat_restrict L.val
      -- (4) right_inv
      · intro p
        rcases p with ⟨LL, ⟨LM, hLM⟩, LU⟩
        apply Prod.ext
        · exact D.restrictLower_concat LL LM LU
        apply Prod.ext
        · apply Subtype.ext
          exact D.restrictMid_concat LL LM LU
        · exact D.restrictUpper_concat LL LM LU
    -- Cardinalities
    have hS : S.card = Fintype.card {L : LinearExt α // L.lt u v} := by
      rw [Fintype.card_subtype]
    have hT : T.card = Fintype.card {LM : LinearExt ↥D.Mid // LM.lt ⟨u, hu⟩ ⟨v, hv⟩} := by
      rw [Fintype.card_subtype]
    rw [hS, Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, ← hT]
    unfold numLinExt
    ring
  -- Step 2: numLinExt factorization
  have hnum := D.numLinExt_eq
  -- Step 3: divide
  unfold probLT
  rw [hfilter_card, hnum]
  have hL_pos : (numLinExt ↥D.Lower : ℚ) ≠ 0 := by exact_mod_cast numLinExt_ne_zero
  have hM_pos : (numLinExt ↥D.Mid : ℚ) ≠ 0 := by exact_mod_cast numLinExt_ne_zero
  have hU_pos : (numLinExt ↥D.Upper : ℚ) ≠ 0 := by exact_mod_cast numLinExt_ne_zero
  push_cast
  field_simp

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
