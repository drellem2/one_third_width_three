/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset
import OneThird.Mathlib.LinearExtension.Fintype

/-!
# Linear extensions of a `RelationPoset α`

This file mirrors the typeclass-based linear-extension API
(`OneThird.Mathlib.LinearExtension.Fintype`) for the data-version
`RelationPoset α` (`OneThird.Mathlib.RelationPoset`):

* `RelationPoset.LinearExt' Q` — the type of linear extensions of a
  `Q : RelationPoset α`, defined as a bijection `α ≃ Fin n` that respects
  `Q.le`. Multiple `RelationPoset α` values can coexist on the same
  ground set, so `LinearExt' Q` is a per-value notion (in contrast to
  `LinearExt α`, which is parametrised by the `[PartialOrder α]`
  typeclass).
* `RelationPoset.numLinExt' Q := Fintype.card (LinearExt' Q)` and
  `RelationPoset.probLT' Q x y := |{L : Q.lt x y in L}| / numLinExt' Q`
  — the data-version counting and probability primitives.
* `RelationPoset.LinearExt'.szpilrajn` — Szpilrajn for data posets:
  every `RelationPoset α` admits at least one linear extension. Reduced
  to the typeclass version via `Q.asPartialOrder`.
* `RelationPoset.linearExtEquiv` — when `Q = ofPartialOrder α` for an
  ambient `[PartialOrder α]`, `LinearExt α ≃ LinearExt' Q`. From this
  we derive `numLinExt'_ofPartialOrder` and
  `probLT'_ofPartialOrder` showing the data-version primitives agree
  with the typeclass-based ones, so results proved at one side
  transport to the other.

## Downstream

Used by `OneThird.Mathlib.RelationPoset.FKG` (A8-S2-cont-3) for the
FKG monotonicity-under-augmentation lemma, which couples linear
extensions of `Q` and `Q' := addRel Q a b _` on the same ground set.

## Reference

* `step8.tex` `prop:in-situ-balanced` Case 2 (`3001-3032`).
* `OneThird.Mathlib.LinearExtension.Fintype` — the typeclass-based
  parent API mirrored here.
-/

namespace OneThird

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — `Q.asPartialOrder`: typeclass view of a data poset -/

/-- View a `Q : RelationPoset α` as a `PartialOrder α`. This is a
*definition*, not an instance: multiple `RelationPoset α` values can
coexist on the same ground set `α`, and they would otherwise produce
conflicting global typeclass instances. Use this via `letI` to
locally activate the typeclass. -/
@[reducible] def asPartialOrder (Q : RelationPoset α) : PartialOrder α where
  le := Q.le
  lt := Q.lt
  le_refl := Q.le_refl
  le_trans := fun _ _ _ => Q.le_trans
  le_antisymm := fun _ _ => Q.le_antisymm
  lt_iff_le_not_ge := fun x y => by
    refine ⟨?_, ?_⟩
    · rintro ⟨hxy, hne⟩
      refine ⟨hxy, fun hyx => hne ?_⟩
      exact Q.le_antisymm hxy hyx
    · rintro ⟨hxy, hnyx⟩
      refine ⟨hxy, ?_⟩
      rintro rfl
      exact hnyx hxy

@[simp] lemma asPartialOrder_le (Q : RelationPoset α) (x y : α) :
    (haveI : PartialOrder α := Q.asPartialOrder; (x ≤ y)) ↔ Q.le x y :=
  Iff.rfl

/-! ### §2 — `LinearExt' Q`: linear extensions of a data poset -/

/-- A *linear extension* of a finite data poset `Q : RelationPoset α`
is an order-preserving bijection `α ≃ Fin (Fintype.card α)`. Distinct
`Q : RelationPoset α` values give distinct types `LinearExt' Q`
(parametrised at the value level), which is the property we need for
the cross-poset coupling argument of `prop:in-situ-balanced` Case 2. -/
structure LinearExt' (Q : RelationPoset α) where
  /-- Underlying bijection to `Fin n`. -/
  toFun : α ≃ Fin (Fintype.card α)
  /-- The bijection respects `Q.le`. -/
  monotone : ∀ {x y : α}, Q.le x y → toFun x ≤ toFun y

namespace LinearExt'

variable {Q : RelationPoset α}

/-- Two linear extensions with equal underlying equivalences are equal. -/
@[ext]
lemma ext {L₁ L₂ : LinearExt' Q} (h : L₁.toFun = L₂.toFun) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

lemma toFun_injective :
    Function.Injective (fun L : LinearExt' Q => L.toFun) :=
  fun _ _ h => ext h

/-- Position of `x` under a linear extension `L`. -/
def pos (L : LinearExt' Q) (x : α) : Fin (Fintype.card α) := L.toFun x

/-- `L.lt x y` iff `x` precedes `y` in the linear extension `L`. -/
def lt (L : LinearExt' Q) (x y : α) : Prop := L.pos x < L.pos y

instance instDecidableEq : DecidableEq (LinearExt' Q) := fun L₁ L₂ =>
  decidable_of_iff (L₁.toFun = L₂.toFun) ⟨ext, fun h => h ▸ rfl⟩

/-- `LinearExt' Q` is a `Fintype`: it injects into the finite type
`α ≃ Fin (Fintype.card α)`. -/
noncomputable instance instFintype (Q : RelationPoset α) :
    Fintype (LinearExt' Q) :=
  Fintype.ofInjective (fun L : LinearExt' Q => L.toFun) toFun_injective

instance instDecidableLt (L : LinearExt' Q) (x y : α) :
    Decidable (L.lt x y) :=
  inferInstanceAs (Decidable (L.pos x < L.pos y))

lemma pos_injective (L : LinearExt' Q) : Function.Injective L.pos :=
  L.toFun.injective

lemma pos_lt_pos_of_lt (L : LinearExt' Q) {x y : α} (hle : Q.le x y)
    (hne : x ≠ y) : L.pos x < L.pos y :=
  _root_.lt_of_le_of_ne (L.monotone hle) (fun h => hne (L.pos_injective h))

lemma lt_of_lt (L : LinearExt' Q) {x y : α} (h : Q.lt x y) : L.lt x y :=
  L.pos_lt_pos_of_lt h.1 h.2

lemma lt_irrefl (L : LinearExt' Q) (x : α) : ¬ L.lt x x :=
  fun h => _root_.lt_irrefl _ h

lemma lt_asymm (L : LinearExt' Q) {x y : α} (h : L.lt x y) : ¬ L.lt y x :=
  fun h' => _root_.lt_irrefl _ (h.trans h')

/-- **Szpilrajn for data posets**: every `Q : RelationPoset α` admits
a linear extension. Reduces to the typeclass version
`LinearExt.szpilrajn` after activating `Q.asPartialOrder` as a local
instance via `letI`. -/
noncomputable def szpilrajn (Q : RelationPoset α) : LinearExt' Q :=
  letI : PartialOrder α := Q.asPartialOrder
  let L : LinearExt α := LinearExt.szpilrajn α
  { toFun := L.toFun
    monotone := fun {x y} h => L.monotone (show x ≤ y from h) }

instance instNonempty (Q : RelationPoset α) : Nonempty (LinearExt' Q) :=
  ⟨szpilrajn Q⟩

end LinearExt'

/-! ### §3 — `numLinExt' Q`: counting linear extensions -/

/-- Number of linear extensions of `Q : RelationPoset α`. -/
noncomputable def numLinExt' (Q : RelationPoset α) : ℕ :=
  Fintype.card (LinearExt' Q)

lemma one_le_numLinExt' (Q : RelationPoset α) : 1 ≤ numLinExt' Q :=
  Fintype.card_pos

lemma numLinExt'_pos (Q : RelationPoset α) : 0 < numLinExt' Q :=
  one_le_numLinExt' Q

lemma numLinExt'_ne_zero (Q : RelationPoset α) : numLinExt' Q ≠ 0 :=
  (numLinExt'_pos Q).ne'

/-! ### §4 — `probLT' Q x y`: probability of `x <_L y` -/

/-- `probLT' Q x y = Pr[x <_L y]` in a uniformly random linear
extension of `Q`. -/
noncomputable def probLT' (Q : RelationPoset α) (x y : α) : ℚ :=
  ((Finset.univ.filter (fun L : LinearExt' Q => L.lt x y)).card : ℚ)
    / (numLinExt' Q : ℚ)

lemma probLT'_nonneg (Q : RelationPoset α) (x y : α) :
    0 ≤ probLT' Q x y := by
  unfold probLT'
  positivity

lemma filter_lt_card_le_numLinExt' (Q : RelationPoset α) (x y : α) :
    (Finset.univ.filter (fun L : LinearExt' Q => L.lt x y)).card ≤
      numLinExt' Q := by
  unfold numLinExt'
  exact (Finset.card_filter_le _ _).trans (Finset.card_univ.le)

lemma probLT'_le_one (Q : RelationPoset α) (x y : α) :
    probLT' Q x y ≤ 1 := by
  unfold probLT'
  rw [div_le_one (by exact_mod_cast numLinExt'_pos Q)]
  exact_mod_cast filter_lt_card_le_numLinExt' Q x y

lemma probLT'_self (Q : RelationPoset α) (x : α) :
    probLT' Q x x = 0 := by
  have hempty :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt x x)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro L _ hlt
    exact LinearExt'.lt_irrefl L x hlt
  simp [probLT', hempty]

/-- On `Q.lt x y`, every linear extension places `x` before `y`,
so `probLT' Q x y = 1`. -/
lemma probLT'_of_lt (Q : RelationPoset α) {x y : α} (h : Q.lt x y) :
    probLT' Q x y = 1 := by
  have hfilter :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt x y)) =
      Finset.univ := by
    apply Finset.filter_true_of_mem
    intro L _
    exact L.lt_of_lt h
  have hpos : (numLinExt' Q : ℚ) ≠ 0 := by
    exact_mod_cast numLinExt'_ne_zero Q
  unfold probLT'
  rw [hfilter, Finset.card_univ]
  exact div_self hpos

/-- On `Q.lt y x`, no linear extension places `x` before `y`,
so `probLT' Q x y = 0`. -/
lemma probLT'_of_gt (Q : RelationPoset α) {x y : α} (h : Q.lt y x) :
    probLT' Q x y = 0 := by
  have hfilter :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt x y)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro L _ hlt
    exact L.lt_asymm hlt (L.lt_of_lt h)
  simp [probLT', hfilter]

/-- For distinct `x` and `y`, the two one-sided probabilities sum to
one: each linear extension contributes to exactly one of the filters. -/
lemma probLT'_add_probLT'_of_ne (Q : RelationPoset α) {x y : α}
    (hxy : x ≠ y) : probLT' Q x y + probLT' Q y x = 1 := by
  have hdisj :
      Disjoint (Finset.univ.filter (fun L : LinearExt' Q => L.lt x y))
               (Finset.univ.filter (fun L : LinearExt' Q => L.lt y x)) := by
    rw [Finset.disjoint_left]
    intro L hL hL'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      LinearExt'.lt] at hL hL'
    exact absurd (hL.trans hL') (_root_.lt_irrefl _)
  have hunion :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt x y)) ∪
        (Finset.univ.filter (fun L : LinearExt' Q => L.lt y x)) =
      (Finset.univ : Finset (LinearExt' Q)) := by
    ext L
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, LinearExt'.lt]
    rcases _root_.lt_trichotomy (L.pos x) (L.pos y) with h | h | h
    · exact ⟨fun _ => True.intro, fun _ => Or.inl h⟩
    · exact absurd (L.pos_injective h) hxy
    · exact ⟨fun _ => True.intro, fun _ => Or.inr h⟩
  have hcard :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt x y)).card +
        (Finset.univ.filter (fun L : LinearExt' Q => L.lt y x)).card =
      numLinExt' Q := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rfl
  have hpos : (numLinExt' Q : ℚ) ≠ 0 := by
    exact_mod_cast numLinExt'_ne_zero Q
  unfold probLT'
  rw [← add_div, ← Nat.cast_add, hcard]
  exact div_self hpos

/-! ### §5 — Compatibility with `LinearExt α` for `Q = ofPartialOrder α`

When the data poset `Q` is `ofPartialOrder α` for an ambient
`[PartialOrder α]` typeclass, `LinearExt' Q` is canonically
in bijection with `LinearExt α`, and the data-version counting and
probability primitives reduce to the typeclass-based ones. This
lets the FKG monotonicity-under-augmentation lemma (proved on
`RelationPoset α`) transport back to the typeclass-based setting. -/

section ofPartialOrderCompat

variable [PartialOrder α] [DecidableLE α]

/-- The natural map `LinearExt α → LinearExt' (ofPartialOrder α)`. -/
def linearExtToLinearExt' (L : LinearExt α) :
    LinearExt' (ofPartialOrder α) where
  toFun := L.toFun
  monotone := fun h => L.monotone ((ofPartialOrder_le_iff α).mp h)

/-- The natural map `LinearExt' (ofPartialOrder α) → LinearExt α`. -/
def linearExt'ToLinearExt (L : LinearExt' (ofPartialOrder α)) :
    LinearExt α where
  toFun := L.toFun
  monotone := fun h => L.monotone ((ofPartialOrder_le_iff α).mpr h)

@[simp]
lemma linearExtToLinearExt'_toFun (L : LinearExt α) :
    (linearExtToLinearExt' L).toFun = L.toFun := rfl

@[simp]
lemma linearExt'ToLinearExt_toFun (L : LinearExt' (ofPartialOrder α)) :
    (linearExt'ToLinearExt L).toFun = L.toFun := rfl

/-- The bijection `LinearExt α ≃ LinearExt' (ofPartialOrder α)`. -/
def linearExtEquiv : LinearExt α ≃ LinearExt' (ofPartialOrder α) where
  toFun := linearExtToLinearExt'
  invFun := linearExt'ToLinearExt
  left_inv L := by apply LinearExt.ext; rfl
  right_inv L := by apply LinearExt'.ext; rfl

@[simp]
lemma linearExtEquiv_toFun (L : LinearExt α) :
    (linearExtEquiv L).toFun = L.toFun := rfl

@[simp]
lemma linearExtEquiv_pos (L : LinearExt α) (x : α) :
    (linearExtEquiv L).pos x = L.pos x := rfl

@[simp]
lemma linearExtEquiv_lt (L : LinearExt α) (x y : α) :
    (linearExtEquiv L).lt x y ↔ L.lt x y := Iff.rfl

@[simp]
lemma linearExtEquiv_symm_toFun (L : LinearExt' (ofPartialOrder α)) :
    (linearExtEquiv.symm L).toFun = L.toFun := rfl

@[simp]
lemma linearExtEquiv_symm_lt (L : LinearExt' (ofPartialOrder α)) (x y : α) :
    (linearExtEquiv.symm L).lt x y ↔ L.lt x y := Iff.rfl

/-- The data-version count agrees with the typeclass-based count when
the data poset comes from the typeclass. -/
lemma numLinExt'_ofPartialOrder :
    numLinExt' (ofPartialOrder α) = numLinExt α := by
  unfold numLinExt' numLinExt
  exact Fintype.card_congr linearExtEquiv.symm

/-- The filter on `LinearExt' (ofPartialOrder α)` equals the image of
the filter on `LinearExt α` under `linearExtEquiv`. -/
private lemma filter_lt_eq_image (x y : α) :
    (Finset.univ.filter
        (fun L : LinearExt' (ofPartialOrder α) => L.lt x y)) =
      ((Finset.univ.filter
          (fun L : LinearExt α => L.lt x y)).image
        linearExtEquiv) := by
  ext L
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · intro hL
    refine ⟨linearExtEquiv.symm L, ?_, by simp⟩
    show (linearExtEquiv.symm L).lt x y
    rw [linearExtEquiv_symm_lt]
    exact hL
  · rintro ⟨L₀, hL₀, rfl⟩
    show (linearExtEquiv L₀).lt x y
    exact hL₀

/-- The data-version `probLT'` agrees with the typeclass-based
`probLT` when the data poset comes from the typeclass. -/
lemma probLT'_ofPartialOrder (x y : α) :
    probLT' (ofPartialOrder α) x y = probLT x y := by
  have hcard :
      (Finset.univ.filter
          (fun L : LinearExt' (ofPartialOrder α) => L.lt x y)).card =
      (Finset.univ.filter (fun L : LinearExt α => L.lt x y)).card := by
    rw [filter_lt_eq_image]
    exact Finset.card_image_of_injective _ linearExtEquiv.injective
  unfold probLT' probLT
  rw [show (numLinExt' (ofPartialOrder α) : ℚ) = (numLinExt α : ℚ) by
        exact_mod_cast numLinExt'_ofPartialOrder,
      show ((Finset.univ.filter
              (fun L : LinearExt' (ofPartialOrder α) => L.lt x y)).card : ℚ)
          = ((Finset.univ.filter (fun L : LinearExt α => L.lt x y)).card : ℚ)
          by exact_mod_cast hcard]

end ofPartialOrderCompat

/-! ### §6 — Subseteq monotonicity for `LinearExt'`

If `Q.Subseteq Q'`, then every linear extension of `Q'` is a linear
extension of `Q`: the bijection respects `Q'.le`, hence respects
`Q.le ⊆ Q'.le`. This is the key structural fact for the FKG
monotonicity-under-augmentation lemma. -/

/-- Restrict a linear extension along a sub-poset relation `Q ⊆ Q'`:
every linear extension of `Q'` is a linear extension of `Q`. -/
def LinearExt'.restrict {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (L : LinearExt' Q') : LinearExt' Q where
  toFun := L.toFun
  monotone := fun h => L.monotone (hQQ'.le_of_le h)

@[simp]
lemma LinearExt'.restrict_toFun {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') (L : LinearExt' Q') :
    (L.restrict hQQ').toFun = L.toFun := rfl

@[simp]
lemma LinearExt'.restrict_pos {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') (L : LinearExt' Q') (x : α) :
    (L.restrict hQQ').pos x = L.pos x := rfl

@[simp]
lemma LinearExt'.restrict_lt {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') (L : LinearExt' Q') (x y : α) :
    (L.restrict hQQ').lt x y ↔ L.lt x y := Iff.rfl

/-- The restriction map `LinearExt' Q' → LinearExt' Q` along
`Q.Subseteq Q'` is injective. -/
lemma LinearExt'.restrict_injective {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') :
    Function.Injective (LinearExt'.restrict hQQ' : LinearExt' Q' → LinearExt' Q) := by
  intro L₁ L₂ h
  apply LinearExt'.ext
  -- (restrict hQQ' Lᵢ).toFun = Lᵢ.toFun by `rfl`, so the equality
  -- on restrictions descends to `L₁.toFun = L₂.toFun`.
  have h' : (LinearExt'.restrict hQQ' L₁).toFun =
            (LinearExt'.restrict hQQ' L₂).toFun :=
    congrArg LinearExt'.toFun h
  exact h'

/-- Sub-poset relation on data posets gives `numLinExt'` monotonicity
in the *opposite* direction: a larger relation has *fewer* linear
extensions. -/
lemma numLinExt'_le_of_subseteq {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') : numLinExt' Q' ≤ numLinExt' Q := by
  unfold numLinExt'
  exact Fintype.card_le_of_injective _ (LinearExt'.restrict_injective hQQ')

end RelationPoset

end OneThird
