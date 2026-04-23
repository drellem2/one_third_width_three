/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.BrightwellAxiom
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Single-element deletion coupling (F6a, `lem:one-elem-perturb`)

This file ports `lem:one-elem-perturb` of `step8.tex:911-1023` into Lean:
for a finite poset `γ` with `|γ| = m ≥ 2`, a distinguished element
`z : γ`, and two distinct `x, y : {a : γ // a ≠ z}`,
```
  |probLT x.val y.val − probLT ⟨x⟩ ⟨y⟩|  ≤  2 / m.
```

## Strategy

Let `α := {a : γ // a ≠ z}`.

1. **Restriction** `π : LinearExt γ → LinearExt α`: delete `z` and
   reduce positions past `L.pos z` by one.
2. **Insertion** `insertAt L' r : LinearExt γ`: given `L' ∈ LinearExt α`
   and valid 1-indexed rank `r ∈ (P(L'), S(L')]`, insert `z` at rank
   `r`.
3. **Fiber bijection**: `L ↦ (π L, (L.pos z).val + 1)` is a bijection
   onto the dependent sum `Σ L', validRank L'`.
4. **Fiber-sum identities** (for pred/succ finsets on `α`):
   * `Fintype.card (LinearExt γ) = ∑ L', fiberSize …`
   * `#{L : L.lt x y} = ∑ L' ∈ A, fiberSize …`
5. **Brightwell sharp centred bound** closes the integer inequality;
   dividing by `N · N' > 0` gives the rational target.

## Reference

`step8.tex:911-1023`.
-/

namespace OneThird
namespace LinearExt

open Finset

variable {γ : Type*} [PartialOrder γ] [Fintype γ] [DecidableEq γ]

/-! ### §1 — Pred/succ finsets on `{a : γ // a ≠ z}` -/

/-- Predecessors of `z` in `γ`, realized inside `{a : γ // a ≠ z}`. -/
noncomputable def predNe (z : γ) : Finset {a : γ // a ≠ z} := by
  classical
  exact (Finset.univ : Finset {a : γ // a ≠ z}).filter (fun x => x.val < z)

/-- Successors of `z` in `γ`, realized inside `{a : γ // a ≠ z}`. -/
noncomputable def succNe (z : γ) : Finset {a : γ // a ≠ z} := by
  classical
  exact (Finset.univ : Finset {a : γ // a ≠ z}).filter (fun x => z < x.val)

lemma mem_predNe {z : γ} {x : {a : γ // a ≠ z}} :
    x ∈ predNe z ↔ x.val < z := by
  classical
  unfold predNe; simp

lemma mem_succNe {z : γ} {x : {a : γ // a ≠ z}} :
    x ∈ succNe z ↔ z < x.val := by
  classical
  unfold succNe; simp

lemma predNe_disjoint_succNe (z : γ) :
    Disjoint (predNe (γ := γ) z) (succNe z) := by
  rw [Finset.disjoint_left]
  intro x hxp hxs
  rw [mem_predNe] at hxp; rw [mem_succNe] at hxs
  exact lt_asymm hxp hxs

lemma predNe_le_succNe (z : γ) :
    ∀ u ∈ predNe (γ := γ) z, ∀ v ∈ succNe z, u ≤ v := by
  intro u hu v hv
  rw [mem_predNe] at hu; rw [mem_succNe] at hv
  exact (hu.trans hv).le

lemma card_subtype_ne (z : γ) :
    Fintype.card {a : γ // a ≠ z} = Fintype.card γ - 1 := by
  classical
  rw [Fintype.card_subtype_compl]
  have h : Fintype.card {x : γ // x = z} = 1 := by
    rw [Fintype.card_subtype, Finset.filter_eq']
    simp
  omega

/-! ### §2 — Restriction `restrictNe : LinearExt γ → LinearExt {a // a ≠ z}` -/

private def restrictPosVal (z : γ) (L : LinearExt γ)
    (a : {b : γ // b ≠ z}) : ℕ :=
  if (L.pos a.val).val < (L.pos z).val then (L.pos a.val).val
  else (L.pos a.val).val - 1

private lemma pos_val_ne (L : LinearExt γ) {a : γ} {z : γ} (hne : a ≠ z) :
    (L.pos a).val ≠ (L.pos z).val := fun h =>
  hne (L.pos_injective (Fin.ext h))

private lemma restrictPosVal_lt_card_pred (z : γ) (L : LinearExt γ)
    (a : {b : γ // b ≠ z}) (hcard : 1 ≤ Fintype.card γ) :
    restrictPosVal z L a < Fintype.card γ - 1 := by
  have hne : (L.pos a.val).val ≠ (L.pos z).val := pos_val_ne L a.2
  have hbd : (L.pos a.val).val < Fintype.card γ := (L.pos a.val).isLt
  have hbz : (L.pos z).val < Fintype.card γ := (L.pos z).isLt
  unfold restrictPosVal
  split_ifs <;> omega

private lemma restrictPosVal_injective (z : γ) (L : LinearExt γ) :
    Function.Injective (restrictPosVal (γ := γ) z L) := by
  intro a b heq
  have hne_a : (L.pos a.val).val ≠ (L.pos z).val := pos_val_ne L a.2
  have hne_b : (L.pos b.val).val ≠ (L.pos z).val := pos_val_ne L b.2
  have : (L.pos a.val).val = (L.pos b.val).val := by
    unfold restrictPosVal at heq; split_ifs at heq <;> omega
  exact Subtype.ext (L.pos_injective (Fin.ext this))

private lemma restrictPosVal_lt_iff (z : γ) (L : LinearExt γ)
    {a b : {c : γ // c ≠ z}} :
    restrictPosVal z L a < restrictPosVal z L b ↔
      (L.pos a.val).val < (L.pos b.val).val := by
  have hne_a : (L.pos a.val).val ≠ (L.pos z).val := pos_val_ne L a.2
  have hne_b : (L.pos b.val).val ≠ (L.pos z).val := pos_val_ne L b.2
  unfold restrictPosVal
  split_ifs <;> omega

/-- Auxiliary: the restricted-position function as a `Fin`. -/
private noncomputable def restrictPos (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ)
    (a : {b : γ // b ≠ z}) :
    Fin (Fintype.card {b : γ // b ≠ z}) :=
  ⟨restrictPosVal z L a, by
    rw [card_subtype_ne]; exact restrictPosVal_lt_card_pred z L a hcard⟩

private lemma restrictPos_injective (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) :
    Function.Injective (restrictPos z L hcard) := fun a b h =>
  restrictPosVal_injective z L (Fin.mk.inj_iff.mp h)

private noncomputable def restrictPosEquiv (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) :
    {b : γ // b ≠ z} ≃ Fin (Fintype.card {b : γ // b ≠ z}) := by
  classical
  refine Equiv.ofBijective (restrictPos z L hcard) ?_
  refine (Fintype.bijective_iff_injective_and_card _).mpr ?_
  refine ⟨restrictPos_injective z L hcard, ?_⟩
  simp

/-- Restriction of a linear extension of `γ` to `{a // a ≠ z}`. -/
noncomputable def restrictNe (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) : LinearExt {a : γ // a ≠ z} where
  toFun := restrictPosEquiv z L hcard
  monotone := by
    intro a b hab
    show restrictPosEquiv z L hcard a ≤ restrictPosEquiv z L hcard b
    unfold restrictPosEquiv
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq; exact le_refl _
    · have hne_ab : a.val ≠ b.val :=
        fun h => (ne_of_lt hlt) (Subtype.ext h)
      have hpos_lt : (L.pos a.val).val < (L.pos b.val).val :=
        L.pos_lt_pos_of_lt hlt.le hne_ab
      have hr_lt := (restrictPosVal_lt_iff z L (a := a) (b := b)).mpr hpos_lt
      show (restrictPos z L hcard a) ≤ restrictPos z L hcard b
      exact Fin.mk_le_mk.mpr hr_lt.le

@[simp] lemma restrictNe_pos_val (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) (a : {b : γ // b ≠ z}) :
    ((restrictNe z L hcard).pos a).val = restrictPosVal z L a := by
  show (restrictPosEquiv z L hcard a).val = restrictPosVal z L a
  unfold restrictPosEquiv
  rfl

lemma restrictNe_lt_iff (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) (a b : {c : γ // c ≠ z}) :
    (restrictNe z L hcard).lt a b ↔ L.lt a.val b.val := by
  show ((restrictNe z L hcard).pos a).val < ((restrictNe z L hcard).pos b).val
    ↔ (L.pos a.val).val < (L.pos b.val).val
  rw [restrictNe_pos_val, restrictNe_pos_val, restrictPosVal_lt_iff]

lemma restrictNe_pos_val_of_lt {z : γ} (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) {a : {b : γ // b ≠ z}}
    (h : (L.pos a.val).val < (L.pos z).val) :
    ((restrictNe z L hcard).pos a).val = (L.pos a.val).val := by
  simp [restrictPosVal, h]

lemma restrictNe_pos_val_of_gt {z : γ} (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) {a : {b : γ // b ≠ z}}
    (h : (L.pos z).val < (L.pos a.val).val) :
    ((restrictNe z L hcard).pos a).val = (L.pos a.val).val - 1 := by
  have hnot : ¬ (L.pos a.val).val < (L.pos z).val := by omega
  simp [restrictPosVal, hnot]

/-! ### §3 — Valid insertion interval for `z` -/

lemma maxPredPos_restrictNe_le_pos_z {z : γ} (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) :
    maxPredPos (predNe z) (restrictNe z L hcard) ≤ (L.pos z).val := by
  unfold maxPredPos
  apply Finset.sup_le
  intro a ha
  rw [mem_predNe] at ha
  have hne_az : a.val ≠ z := a.2
  have hlt : (L.pos a.val) < L.pos z :=
    L.pos_lt_pos_of_lt ha.le (ne_of_lt ha)
  have hlt_val : (L.pos a.val).val < (L.pos z).val := hlt
  show (restrictNe z L hcard).posAux a ≤ (L.pos z).val
  unfold posAux
  rw [restrictNe_pos_val_of_lt L hcard hlt_val]
  omega

lemma pos_z_lt_minSuccPos_restrictNe {z : γ} (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) :
    (L.pos z).val + 1 ≤ minSuccPos (succNe z) (restrictNe z L hcard) := by
  unfold minSuccPos
  split_ifs with hne
  · apply Finset.le_inf'
    intro a ha
    rw [mem_succNe] at ha
    have hne : z ≠ a.val := ne_of_lt ha
    have hlt : (L.pos z) < (L.pos a.val) :=
      L.pos_lt_pos_of_lt ha.le hne
    have hlt_val : (L.pos z).val < (L.pos a.val).val := hlt
    show (L.pos z).val + 1 ≤ (restrictNe z L hcard).posAux a
    unfold posAux
    rw [restrictNe_pos_val_of_gt L hcard hlt_val]
    omega
  · have : (L.pos z).val < Fintype.card γ := (L.pos z).isLt
    rw [card_subtype_ne]
    omega

lemma pos_z_in_valid_interval (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) :
    maxPredPos (predNe z) (restrictNe z L hcard) < (L.pos z).val + 1 ∧
      (L.pos z).val + 1 ≤ minSuccPos (succNe z) (restrictNe z L hcard) := by
  have h1 := maxPredPos_restrictNe_le_pos_z (z := z) L hcard
  have h2 := pos_z_lt_minSuccPos_restrictNe (z := z) L hcard
  exact ⟨by omega, h2⟩

/-! ### §4 — Injectivity of the joint forward map -/

lemma eq_of_restrictNe_and_pos_z (z : γ) (hcard : 1 ≤ Fintype.card γ)
    (L₁ L₂ : LinearExt γ)
    (hrestr : restrictNe z L₁ hcard = restrictNe z L₂ hcard)
    (hpos : L₁.pos z = L₂.pos z) :
    L₁ = L₂ := by
  classical
  apply LinearExt.ext
  refine Equiv.ext ?_
  intro b
  apply Fin.ext
  by_cases hbz : b = z
  · subst hbz; exact Fin.val_eq_of_eq hpos
  · have hres_eq : (restrictNe z L₁ hcard).pos ⟨b, hbz⟩ =
        (restrictNe z L₂ hcard).pos ⟨b, hbz⟩ := by rw [hrestr]
    have hval_eq : restrictPosVal z L₁ ⟨b, hbz⟩ = restrictPosVal z L₂ ⟨b, hbz⟩ := by
      have := Fin.val_eq_of_eq hres_eq
      simpa using this
    have hne₁ : (L₁.pos b).val ≠ (L₁.pos z).val := pos_val_ne L₁ hbz
    have hne₂ : (L₂.pos b).val ≠ (L₂.pos z).val := pos_val_ne L₂ hbz
    have hposz_eq : (L₁.pos z).val = (L₂.pos z).val := Fin.val_eq_of_eq hpos
    show (L₁.pos b).val = (L₂.pos b).val
    unfold restrictPosVal at hval_eq
    change
      (if (L₁.pos b).val < (L₁.pos z).val then (L₁.pos b).val
        else (L₁.pos b).val - 1) =
        (if (L₂.pos b).val < (L₂.pos z).val then (L₂.pos b).val
          else (L₂.pos b).val - 1) at hval_eq
    split_ifs at hval_eq <;> omega

/-! ### §5 — Insertion map `insertAt` -/

/-- Given `L' : LinearExt {a // a ≠ z}` and a valid 1-indexed insertion
rank `r`, produce the position function `γ → Fin (Fintype.card γ)`. -/
noncomputable def insertPosFun (z : γ) (L' : LinearExt {a : γ // a ≠ z})
    (r : ℕ) (hcard : 1 ≤ Fintype.card γ) (hr_pos : 1 ≤ r)
    (hr_le : r ≤ Fintype.card γ)
    (b : γ) : Fin (Fintype.card γ) := by
  classical
  by_cases hbz : b = z
  · exact ⟨r - 1, by omega⟩
  · have hcardEq : Fintype.card {a : γ // a ≠ z} = Fintype.card γ - 1 :=
      card_subtype_ne z
    have hlt : (L'.pos ⟨b, hbz⟩).val < Fintype.card γ - 1 := by
      have := (L'.pos ⟨b, hbz⟩).isLt
      omega
    by_cases hvlt : (L'.pos ⟨b, hbz⟩).val + 1 < r
    · exact ⟨(L'.pos ⟨b, hbz⟩).val, by omega⟩
    · exact ⟨(L'.pos ⟨b, hbz⟩).val + 1, by omega⟩

lemma insertPosFun_z (z : γ) (L' : LinearExt {a : γ // a ≠ z})
    (r : ℕ) (hcard : 1 ≤ Fintype.card γ) (hr_pos : 1 ≤ r)
    (hr_le : r ≤ Fintype.card γ) :
    (insertPosFun z L' r hcard hr_pos hr_le z).val = r - 1 := by
  unfold insertPosFun; simp

lemma insertPosFun_ne (z : γ) (L' : LinearExt {a : γ // a ≠ z})
    (r : ℕ) (hcard : 1 ≤ Fintype.card γ) (hr_pos : 1 ≤ r)
    (hr_le : r ≤ Fintype.card γ) (a : {b : γ // b ≠ z}) :
    (insertPosFun z L' r hcard hr_pos hr_le a.val).val =
      if (L'.pos a).val + 1 < r then (L'.pos a).val
      else (L'.pos a).val + 1 := by
  unfold insertPosFun
  simp only [dif_neg a.2]
  split_ifs <;> rfl

/-- Given `L' : LinearExt {a // a ≠ z}` and a valid 1-indexed insertion
rank `r`, build the linear extension of `γ` with `z` at 0-indexed
position `r - 1`. -/
noncomputable def insertAt (z : γ) (L' : LinearExt {a : γ // a ≠ z})
    (r : ℕ) (hcard : 1 ≤ Fintype.card γ) (hr_pos : 1 ≤ r)
    (hr_le : r ≤ Fintype.card γ)
    (hvalid_P : maxPredPos (predNe z) L' < r)
    (hvalid_S : r ≤ minSuccPos (succNe z) L') :
    LinearExt γ := by
  classical
  set f : γ → Fin (Fintype.card γ) := insertPosFun z L' r hcard hr_pos hr_le
    with hfdef
  have f_inj : Function.Injective f := by
    intro b₁ b₂ h
    by_cases hb₁ : b₁ = z
    · by_cases hb₂ : b₂ = z
      · rw [hb₁, hb₂]
      · exfalso
        have h1val : (f b₁).val = r - 1 := by
          rw [hb₁]; exact insertPosFun_z z L' r hcard hr_pos hr_le
        have h2val : (f b₂).val =
            if (L'.pos ⟨b₂, hb₂⟩).val + 1 < r then (L'.pos ⟨b₂, hb₂⟩).val
            else (L'.pos ⟨b₂, hb₂⟩).val + 1 :=
          insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₂, hb₂⟩
        have hEq : (f b₁).val = (f b₂).val := by rw [h]
        rw [h1val, h2val] at hEq
        split_ifs at hEq <;> omega
    · by_cases hb₂ : b₂ = z
      · exfalso
        have h1val : (f b₁).val =
            if (L'.pos ⟨b₁, hb₁⟩).val + 1 < r then (L'.pos ⟨b₁, hb₁⟩).val
            else (L'.pos ⟨b₁, hb₁⟩).val + 1 :=
          insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₁, hb₁⟩
        have h2val : (f b₂).val = r - 1 := by
          rw [hb₂]; exact insertPosFun_z z L' r hcard hr_pos hr_le
        have hEq : (f b₁).val = (f b₂).val := by rw [h]
        rw [h1val, h2val] at hEq
        split_ifs at hEq <;> omega
      · have h1val : (f b₁).val =
            if (L'.pos ⟨b₁, hb₁⟩).val + 1 < r then (L'.pos ⟨b₁, hb₁⟩).val
            else (L'.pos ⟨b₁, hb₁⟩).val + 1 :=
          insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₁, hb₁⟩
        have h2val : (f b₂).val =
            if (L'.pos ⟨b₂, hb₂⟩).val + 1 < r then (L'.pos ⟨b₂, hb₂⟩).val
            else (L'.pos ⟨b₂, hb₂⟩).val + 1 :=
          insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₂, hb₂⟩
        have hEq : (f b₁).val = (f b₂).val := by rw [h]
        rw [h1val, h2val] at hEq
        have hval : (L'.pos ⟨b₁, hb₁⟩).val = (L'.pos ⟨b₂, hb₂⟩).val := by
          split_ifs at hEq <;> omega
        have hpos_eq : L'.pos ⟨b₁, hb₁⟩ = L'.pos ⟨b₂, hb₂⟩ := Fin.ext hval
        exact Subtype.mk.inj (L'.pos_injective hpos_eq)
  have f_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f_inj, by simp⟩
  refine
    { toFun := Equiv.ofBijective f f_bij
      monotone := ?_ }
  intro b₁ b₂ hb
  show (Equiv.ofBijective f f_bij b₁ : Fin _).val ≤ (Equiv.ofBijective f f_bij b₂).val
  by_cases hb₁z : b₁ = z
  · by_cases hb₂z : b₂ = z
    · rw [hb₁z, hb₂z]
    · have hzb : z < b₂ := by rw [hb₁z] at hb; exact lt_of_le_of_ne hb (Ne.symm hb₂z)
      have hmemS : (⟨b₂, hb₂z⟩ : {a : γ // a ≠ z}) ∈ succNe z := by
        rw [mem_succNe]; exact hzb
      have hne_succ : (succNe z : Finset _).Nonempty := ⟨_, hmemS⟩
      have hposS : r ≤ (L'.pos ⟨b₂, hb₂z⟩).val + 1 := by
        have hval_S : minSuccPos (succNe z) L' =
            (succNe z).inf' hne_succ L'.posAux := by
          unfold minSuccPos; rw [dif_pos hne_succ]
        have h1 : (succNe z).inf' hne_succ L'.posAux ≤ L'.posAux ⟨b₂, hb₂z⟩ :=
          Finset.inf'_le _ hmemS
        rw [hval_S] at hvalid_S
        exact hvalid_S.trans h1
      have h1val : (Equiv.ofBijective f f_bij b₁).val = r - 1 := by
        show (f b₁).val = r - 1
        rw [hb₁z]
        exact insertPosFun_z z L' r hcard hr_pos hr_le
      have h2val : (Equiv.ofBijective f f_bij b₂).val =
          if (L'.pos ⟨b₂, hb₂z⟩).val + 1 < r then (L'.pos ⟨b₂, hb₂z⟩).val
          else (L'.pos ⟨b₂, hb₂z⟩).val + 1 := by
        show (f b₂).val = _
        exact insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₂, hb₂z⟩
      rw [h1val, h2val]
      split_ifs with hlt
      · omega
      · omega
  · by_cases hb₂z : b₂ = z
    · have hb₁z' : b₁ < z := by rw [hb₂z] at hb; exact lt_of_le_of_ne hb hb₁z
      have hmemP : (⟨b₁, hb₁z⟩ : {a : γ // a ≠ z}) ∈ predNe z := by
        rw [mem_predNe]; exact hb₁z'
      have hbound : L'.posAux ⟨b₁, hb₁z⟩ ≤ maxPredPos (predNe z) L' :=
        Finset.le_sup hmemP
      have hbnd2 : (L'.pos ⟨b₁, hb₁z⟩).val + 1 < r := by
        have h1 : (L'.pos ⟨b₁, hb₁z⟩).val + 1 = L'.posAux ⟨b₁, hb₁z⟩ := rfl
        rw [h1]; exact lt_of_le_of_lt hbound hvalid_P
      have h1val : (Equiv.ofBijective f f_bij b₁).val =
          if (L'.pos ⟨b₁, hb₁z⟩).val + 1 < r then (L'.pos ⟨b₁, hb₁z⟩).val
          else (L'.pos ⟨b₁, hb₁z⟩).val + 1 := by
        show (f b₁).val = _
        exact insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₁, hb₁z⟩
      have h2val : (Equiv.ofBijective f f_bij b₂).val = r - 1 := by
        show (f b₂).val = r - 1
        rw [hb₂z]
        exact insertPosFun_z z L' r hcard hr_pos hr_le
      rw [h1val, h2val]
      split_ifs <;> omega
    · have hab : (⟨b₁, hb₁z⟩ : {a : γ // a ≠ z}) ≤ ⟨b₂, hb₂z⟩ := hb
      have hL'val : (L'.pos ⟨b₁, hb₁z⟩).val ≤ (L'.pos ⟨b₂, hb₂z⟩).val :=
        L'.monotone hab
      have h1val : (Equiv.ofBijective f f_bij b₁).val =
          if (L'.pos ⟨b₁, hb₁z⟩).val + 1 < r then (L'.pos ⟨b₁, hb₁z⟩).val
          else (L'.pos ⟨b₁, hb₁z⟩).val + 1 := by
        show (f b₁).val = _
        exact insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₁, hb₁z⟩
      have h2val : (Equiv.ofBijective f f_bij b₂).val =
          if (L'.pos ⟨b₂, hb₂z⟩).val + 1 < r then (L'.pos ⟨b₂, hb₂z⟩).val
          else (L'.pos ⟨b₂, hb₂z⟩).val + 1 := by
        show (f b₂).val = _
        exact insertPosFun_ne z L' r hcard hr_pos hr_le ⟨b₂, hb₂z⟩
      rw [h1val, h2val]
      split_ifs <;> omega

/-! #### Positions in `insertAt` -/

lemma insertAt_pos_z_val {z : γ} {L' : LinearExt {a : γ // a ≠ z}}
    {r : ℕ} {hcard : 1 ≤ Fintype.card γ} {hr_pos : 1 ≤ r}
    {hr_le : r ≤ Fintype.card γ}
    {hvalid_P : maxPredPos (predNe z) L' < r}
    {hvalid_S : r ≤ minSuccPos (succNe z) L'} :
    ((insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).pos z).val = r - 1 := by
  show ((insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).toFun z).val = r - 1
  unfold insertAt
  simp only [Equiv.ofBijective_apply]
  exact insertPosFun_z z L' r hcard hr_pos hr_le

lemma insertAt_pos_ne_val {z : γ} {L' : LinearExt {a : γ // a ≠ z}}
    {r : ℕ} {hcard : 1 ≤ Fintype.card γ} {hr_pos : 1 ≤ r}
    {hr_le : r ≤ Fintype.card γ}
    {hvalid_P : maxPredPos (predNe z) L' < r}
    {hvalid_S : r ≤ minSuccPos (succNe z) L'}
    (a : {b : γ // b ≠ z}) :
    ((insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).pos a.val).val =
      if (L'.pos a).val + 1 < r then (L'.pos a).val
      else (L'.pos a).val + 1 := by
  show ((insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).toFun a.val).val = _
  unfold insertAt
  simp only [Equiv.ofBijective_apply]
  exact insertPosFun_ne z L' r hcard hr_pos hr_le a

/-- `restrictNe` is a left-inverse of `insertAt`. -/
lemma restrictNe_insertAt {z : γ} (L' : LinearExt {a : γ // a ≠ z})
    (r : ℕ) (hcard : 1 ≤ Fintype.card γ) (hr_pos : 1 ≤ r)
    (hr_le : r ≤ Fintype.card γ)
    (hvalid_P : maxPredPos (predNe z) L' < r)
    (hvalid_S : r ≤ minSuccPos (succNe z) L') :
    restrictNe z (insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S) hcard
      = L' := by
  classical
  apply LinearExt.ext
  ext a : 1
  show (restrictNe z _ hcard).toFun a = L'.toFun a
  apply Fin.ext
  set L := insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S
  have hposz : (L.pos z).val = r - 1 := insertAt_pos_z_val
  have hposa : (L.pos a.val).val =
      if (L'.pos a).val + 1 < r then (L'.pos a).val
      else (L'.pos a).val + 1 :=
    insertAt_pos_ne_val a
  show ((restrictNe z L hcard).toFun a).val = (L'.toFun a).val
  -- Left side = restrictPosVal, which uses L.pos a.val and L.pos z.
  have hres : ((restrictNe z L hcard).toFun a : Fin _).val = restrictPosVal z L a := by
    show ((restrictNe z L hcard).pos a).val = _
    exact restrictNe_pos_val z L hcard a
  rw [hres]
  show restrictPosVal z L a = (L'.pos a).val
  unfold restrictPosVal
  rw [hposa, hposz]
  split_ifs with h1 h2 h2'
  · rfl
  · omega
  · omega
  · omega

/-- Insertion preserves `lt` for elements ≠ `z`. -/
lemma insertAt_lt_iff_of_ne {z : γ} (L' : LinearExt {a : γ // a ≠ z})
    (r : ℕ) (hcard : 1 ≤ Fintype.card γ) (hr_pos : 1 ≤ r)
    (hr_le : r ≤ Fintype.card γ)
    (hvalid_P : maxPredPos (predNe z) L' < r)
    (hvalid_S : r ≤ minSuccPos (succNe z) L')
    (a b : {c : γ // c ≠ z}) :
    (insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).lt a.val b.val ↔
      L'.lt a b := by
  show ((insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).pos a.val).val <
        ((insertAt z L' r hcard hr_pos hr_le hvalid_P hvalid_S).pos b.val).val
    ↔ (L'.pos a).val < (L'.pos b).val
  rw [insertAt_pos_ne_val a, insertAt_pos_ne_val b]
  split_ifs <;> omega

/-! ### §6 — The joint bijection

We package `L ↦ (restrictNe L, (L.pos z).val + 1)` as a bijection onto
the dependent sum `Σ L', validRank L'`. -/

/-- The valid 1-indexed insertion rank interval for `z` above `L'`,
represented as `P + 1, P + 2, …, S` via `Finset.range (S − P)` shifted
by `P`. -/
noncomputable def validRank (z : γ) (L' : LinearExt {a : γ // a ≠ z}) :
    Finset ℕ :=
  (Finset.range (minSuccPos (succNe z) L' - maxPredPos (predNe z) L')).image
    (fun i => i + maxPredPos (predNe z) L' + 1)

lemma mem_validRank {z : γ} {L' : LinearExt {a : γ // a ≠ z}} {r : ℕ} :
    r ∈ validRank z L' ↔
      maxPredPos (predNe z) L' < r ∧ r ≤ minSuccPos (succNe z) L' := by
  classical
  unfold validRank
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨by omega, by omega⟩
  · intro ⟨h1, h2⟩
    refine ⟨r - maxPredPos (predNe z) L' - 1, by omega, by omega⟩

lemma validRank_pos {z : γ} {L' : LinearExt {a : γ // a ≠ z}} {r : ℕ}
    (hr : r ∈ validRank z L') : 1 ≤ r := by
  rw [mem_validRank] at hr; omega

lemma validRank_le_card {z : γ} (L' : LinearExt {a : γ // a ≠ z}) {r : ℕ}
    (hr : r ∈ validRank z L') (hcard : 1 ≤ Fintype.card γ) :
    r ≤ Fintype.card γ := by
  rw [mem_validRank] at hr
  have hS : minSuccPos (succNe z) L' ≤ Fintype.card {a : γ // a ≠ z} + 1 := by
    unfold minSuccPos
    split_ifs with hne
    · obtain ⟨a, ha⟩ := hne
      calc (succNe z).inf' ⟨a, ha⟩ L'.posAux
          ≤ L'.posAux a := Finset.inf'_le _ ha
        _ ≤ Fintype.card {a : γ // a ≠ z} := L'.posAux_le_card a
        _ ≤ Fintype.card {a : γ // a ≠ z} + 1 := Nat.le_succ _
    · exact le_refl _
  rw [card_subtype_ne] at hS
  omega

lemma card_validRank (z : γ) (L' : LinearExt {a : γ // a ≠ z}) :
    (validRank z L').card = fiberSize (predNe z) (succNe z) L' := by
  classical
  unfold validRank fiberSize
  rw [Finset.card_image_of_injective _ (fun a b h => by
        simp at h; omega : Function.Injective _)]
  simp

/-! ### §7 — Fiber-sum identities via the bijection

The joint pair `(restrictNe L, (L.pos z).val + 1)` is a bijection
onto `Σ L' : LinearExt α, validRank L'`. We prove this as a cardinality
equality on `Finset`s. -/

/-- Every `L : LinearExt γ` is in the preimage of its restriction. -/
lemma pos_z_plus_one_mem_validRank (z : γ) (L : LinearExt γ)
    (hcard : 1 ≤ Fintype.card γ) :
    (L.pos z).val + 1 ∈ validRank z (restrictNe z L hcard) := by
  rw [mem_validRank]
  exact pos_z_in_valid_interval z L hcard

/-- **Total fiber-sum identity**: `|LinearExt γ| = Σ L', fiberSize L'`. -/
theorem card_linExt_eq_fiberSum (z : γ) (hcard : 1 ≤ Fintype.card γ) :
    Fintype.card (LinearExt γ) =
      ∑ L' : LinearExt {a : γ // a ≠ z},
        fiberSize (predNe z) (succNe z) L' := by
  classical
  -- Strategy:
  -- |LinearExt γ| = |Finset.univ.sigma (fun L' => validRank L')|
  -- via the bijection L ↦ ⟨restrictNe L, (L.pos z).val + 1⟩.
  -- RHS = Σ L', |validRank L'| = Σ L', fiberSize L'.
  have hbij : (Finset.univ : Finset (LinearExt γ)).card =
      ((Finset.univ : Finset (LinearExt {a : γ // a ≠ z})).sigma
        (fun L' => validRank z L')).card := by
    refine Finset.card_bij
      (fun L _ => ⟨restrictNe z L hcard, (L.pos z).val + 1⟩)
      (fun L _ => ?_) (fun L₁ _ L₂ _ h => ?_) (fun ⟨L', r⟩ hmem => ?_)
    · simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
      exact pos_z_plus_one_mem_validRank z L hcard
    · -- Injectivity
      have hfst := congrArg Sigma.fst h
      have hsnd := congrArg Sigma.snd h
      simp only at hfst hsnd
      have h3 : (L₁.pos z).val = (L₂.pos z).val := by
        have : (L₁.pos z).val + 1 = (L₂.pos z).val + 1 := hsnd
        omega
      exact eq_of_restrictNe_and_pos_z z hcard L₁ L₂ hfst (Fin.ext h3)
    · -- Surjectivity
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hmem
      have hmem' := (mem_validRank (L' := L') (r := r)).mp hmem
      have hr_pos : 1 ≤ r := validRank_pos hmem
      have hr_le : r ≤ Fintype.card γ := validRank_le_card L' hmem hcard
      refine ⟨insertAt z L' r hcard hr_pos hr_le hmem'.1 hmem'.2,
              Finset.mem_univ _, ?_⟩
      have hrestr : restrictNe z (insertAt z L' r hcard hr_pos hr_le hmem'.1
          hmem'.2) hcard = L' :=
        restrictNe_insertAt L' r hcard hr_pos hr_le hmem'.1 hmem'.2
      have hposz : ((insertAt z L' r hcard hr_pos hr_le hmem'.1 hmem'.2).pos z).val
          + 1 = r := by
        rw [insertAt_pos_z_val]; omega
      -- Goal: f (insertAt L' r ...) _ = ⟨L', r⟩
      show (⟨restrictNe z _ hcard, _⟩ : Σ _ : LinearExt {a : γ // a ≠ z}, ℕ)
        = ⟨L', r⟩
      apply Sigma.ext hrestr
      exact heq_of_eq hposz
  -- Finish
  have h : (Fintype.card (LinearExt γ) : ℕ) =
      (Finset.univ : Finset (LinearExt γ)).card := by
    rw [Finset.card_univ]
  rw [h, hbij, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro L' _
  exact card_validRank z L'

/-- **A-fiber-sum identity**: `#{L : L.lt x.val y.val} = Σ L' ∈ A, fiberSize L'`. -/
theorem card_filter_lt_eq_fiberSum_A (z : γ) (hcard : 1 ≤ Fintype.card γ)
    (x y : {a : γ // a ≠ z}) :
    ((Finset.univ : Finset (LinearExt γ)).filter (fun L => L.lt x.val y.val)).card =
      ∑ L' ∈ brightwellA (α := {a : γ // a ≠ z}) x y,
        fiberSize (predNe z) (succNe z) L' := by
  classical
  -- Same bijection but restricted to the "x < y" subset.
  -- LHS = |{L | L.lt x y}|
  --     = |{(L', r) | (insertAt L' r).lt x y}|   -- via bijection
  --     = |{(L', r) | L'.lt ⟨x⟩ ⟨y⟩, r ∈ validRank L'}|  -- by insertAt_lt_iff_of_ne
  --     = Σ_{L' ∈ A} |validRank L'|
  --     = Σ_{L' ∈ A} fiberSize L'
  have hbij :
      ((Finset.univ : Finset (LinearExt γ)).filter (fun L => L.lt x.val y.val)).card =
      ((brightwellA (α := {a : γ // a ≠ z}) x y).sigma
        (fun L' => validRank z L')).card := by
    refine Finset.card_bij
      (fun L _ => ⟨restrictNe z L hcard, (L.pos z).val + 1⟩)
      (fun L hL => ?_) (fun L₁ _ L₂ _ h => ?_) (fun ⟨L', r⟩ hmem => ?_)
    · -- L is in the LHS ⇒ target in sigma
      simp only [Finset.mem_sigma, mem_brightwellA]
      refine ⟨?_, pos_z_plus_one_mem_validRank z L hcard⟩
      -- Need: (restrictNe z L hcard).lt x y
      rw [restrictNe_lt_iff z L hcard]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL
      exact hL
    · -- Injectivity (same as before)
      have hfst := congrArg Sigma.fst h
      have hsnd := congrArg Sigma.snd h
      simp only at hfst hsnd
      have h3 : (L₁.pos z).val = (L₂.pos z).val := by
        have : (L₁.pos z).val + 1 = (L₂.pos z).val + 1 := hsnd
        omega
      exact eq_of_restrictNe_and_pos_z z hcard L₁ L₂ hfst (Fin.ext h3)
    · -- Surjectivity
      simp only [Finset.mem_sigma, mem_brightwellA] at hmem
      obtain ⟨hA, hv⟩ := hmem
      have hmem' := (mem_validRank (L' := L') (r := r)).mp hv
      have hr_pos : 1 ≤ r := validRank_pos hv
      have hr_le : r ≤ Fintype.card γ := validRank_le_card L' hv hcard
      refine ⟨insertAt z L' r hcard hr_pos hr_le hmem'.1 hmem'.2, ?_, ?_⟩
      · -- L is in filter
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [insertAt_lt_iff_of_ne L' r hcard hr_pos hr_le hmem'.1 hmem'.2]
        exact hA
      · have hrestr : restrictNe z (insertAt z L' r hcard hr_pos hr_le hmem'.1
            hmem'.2) hcard = L' :=
          restrictNe_insertAt L' r hcard hr_pos hr_le hmem'.1 hmem'.2
        have hposz : ((insertAt z L' r hcard hr_pos hr_le hmem'.1 hmem'.2).pos z).val
            + 1 = r := by
          rw [insertAt_pos_z_val]; omega
        -- Goal: ⟨restrictNe (insertAt ..), ((insertAt ..).pos z).val + 1⟩ = ⟨L', r⟩
        show (⟨restrictNe z _ hcard, _⟩ : Σ _ : LinearExt {a : γ // a ≠ z}, ℕ)
          = ⟨L', r⟩
        apply Sigma.ext hrestr
        exact heq_of_eq hposz
  rw [hbij, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro L' _
  exact card_validRank z L'

/-! ### §8 — Main theorem: single-element perturbation bound -/

/-- **Single-element deletion coupling** (`lem:one-elem-perturb`,
`step8.tex:911-1023`). For a finite poset `γ` with `|γ| ≥ 2`, a
distinguished element `z : γ`, and two elements `x, y : {a : γ // a ≠ z}`,
```
  |probLT x.val y.val − probLT x y|  ≤  2 / |γ|.
```
Proof via the Brightwell sharp centred bound axiom, the fiber-sum
identities, and arithmetic rearrangement. -/
theorem one_elem_perturb (z : γ) (hcard : 2 ≤ Fintype.card γ)
    (x y : {a : γ // a ≠ z}) :
    |probLT x.val y.val - probLT x y| ≤ 2 / (Fintype.card γ : ℚ) := by
  classical
  have hcard1 : 1 ≤ Fintype.card γ := by omega
  let α' := {a : γ // a ≠ z}
  -- Apply Brightwell axiom with α := {a // a ≠ z} and m := Fintype.card γ.
  have hmQ : Fintype.card γ = Fintype.card α' + 1 := by
    rw [card_subtype_ne]; omega
  have hsharp := brightwell_sharp_centred (α := α')
    (predNe z) (succNe z) (predNe_disjoint_succNe z) (predNe_le_succNe z)
    (Fintype.card γ) hmQ hcard x y
  -- The axiom's N := Σ fiberSize L' over LinearExt α'.
  -- The axiom's N' := |LinearExt α'|.
  -- We identify N with numLinExt γ = |LinearExt γ|.
  set Nint : ℤ := ∑ L : LinearExt α', (fiberSize (predNe z) (succNe z) L : ℤ)
    with hNint
  set Npint : ℤ := (Fintype.card (LinearExt α') : ℤ) with hNpint
  have hN_card : Nint = (Fintype.card (LinearExt γ) : ℤ) := by
    rw [hNint]
    have heq := card_linExt_eq_fiberSum z hcard1
    have : ((∑ L' : LinearExt α',
        fiberSize (predNe z) (succNe z) L' : ℕ) : ℤ) =
      (Fintype.card (LinearExt γ) : ℤ) := by
      exact_mod_cast heq.symm
    push_cast at this ⊢
    linarith
  have hA_eq : (∑ L ∈ (Finset.univ : Finset (LinearExt α')).filter
        (fun L => L.lt x y), (fiberSize (predNe z) (succNe z) L : ℤ)) =
      (((Finset.univ : Finset (LinearExt γ)).filter
          (fun L => L.lt x.val y.val)).card : ℤ) := by
    have heq := card_filter_lt_eq_fiberSum_A z hcard1 x y
    -- brightwellA = the filter set (by defn)
    have : (((Finset.univ : Finset (LinearExt γ)).filter
        (fun L => L.lt x.val y.val)).card : ℤ) =
      ((∑ L' ∈ brightwellA (α := α') x y,
        fiberSize (predNe z) (succNe z) L' : ℕ) : ℤ) := by
      exact_mod_cast heq
    rw [show brightwellA (α := α') x y = (Finset.univ : Finset (LinearExt α')).filter
        (fun L => L.lt x y) from rfl] at this
    push_cast at this ⊢
    linarith
  -- brightwellA = the filter set (by defn)
  set numA_γ : ℤ := (((Finset.univ : Finset (LinearExt γ)).filter
      (fun L => L.lt x.val y.val)).card : ℤ) with hnumAγ
  set numA_α' : ℤ := (((Finset.univ : Finset (LinearExt α')).filter
      (fun L => L.lt x y)).card : ℤ) with hnumAα'
  have hbrightA_card :
      ((brightwellA (α := α') x y).card : ℤ) = numA_α' := rfl
  -- Integer inequality from the axiom:
  -- m · |N' · (sum over A_{α'} of f L') - |A_{α'}| · N| ≤ 2 · N · N'
  have hineq_raw :
      (Fintype.card γ : ℤ) *
        |Npint *
            (∑ L ∈ (Finset.univ : Finset (LinearExt α')).filter
              (fun L => L.lt x y), (fiberSize (predNe z) (succNe z) L : ℤ))
          - numA_α' * Nint|
      ≤ 2 * Nint * Npint := by
    have := hsharp
    simp only [hnumAα', hNpint, hNint] at this
    convert this using 2
  -- Rewrite: using hA_eq and hN_card.
  rw [hA_eq, hN_card] at hineq_raw
  -- Now: m · |N' · numA_γ - numA_α' · |LinearExt γ|| ≤ 2 · |LinearExt γ| · N'
  -- Cast to ℚ and divide by (|LinearExt γ| · N') > 0 to get the probLT bound.
  have hNpint_pos : 0 < Npint := by
    rw [hNpint]; exact_mod_cast numLinExt_pos
  have hLE_pos : 0 < (Fintype.card (LinearExt γ) : ℤ) := by
    exact_mod_cast (numLinExt_pos : (0 : ℕ) < _)
  have hm_pos : 0 < (Fintype.card γ : ℤ) := by positivity
  -- Cast to ℚ
  have hineq_q :
      (Fintype.card γ : ℚ) *
        |(Npint : ℚ) * (numA_γ : ℚ) - (numA_α' : ℚ) * (Fintype.card (LinearExt γ) : ℚ)|
      ≤ 2 * (Fintype.card (LinearExt γ) : ℚ) * (Npint : ℚ) := by
    have := hineq_raw
    have : ((Fintype.card γ : ℤ) : ℚ) *
        ((|Npint * numA_γ - numA_α' * (Fintype.card (LinearExt γ) : ℤ)| : ℤ) : ℚ) ≤
        ((2 * (Fintype.card (LinearExt γ) : ℤ) * Npint : ℤ) : ℚ) := by
      exact_mod_cast this
    simpa [Int.cast_abs, Int.cast_sub, Int.cast_mul] using this
  -- Unfold probLT.
  unfold probLT
  have hNγ_ne : (Fintype.card (LinearExt γ) : ℚ) ≠ 0 := by
    exact_mod_cast (numLinExt_ne_zero (α := γ))
  have hNα'_ne : (Fintype.card (LinearExt α') : ℚ) ≠ 0 := by
    exact_mod_cast (numLinExt_ne_zero (α := α'))
  have hm_ne : (Fintype.card γ : ℚ) ≠ 0 := by positivity
  have hNγ_pos : 0 < (Fintype.card (LinearExt γ) : ℚ) := by positivity
  have hNα'_pos : 0 < (Fintype.card (LinearExt α') : ℚ) := by positivity
  have hm_posq : 0 < (Fintype.card γ : ℚ) := by positivity
  have hnumLinExt_γ : (numLinExt γ : ℚ) = (Fintype.card (LinearExt γ) : ℚ) := by
    unfold numLinExt; rfl
  have hnumLinExt_α' : (numLinExt α' : ℚ) = (Fintype.card (LinearExt α') : ℚ) := by
    unfold numLinExt; rfl
  rw [hnumLinExt_γ, hnumLinExt_α']
  -- We want: |a/p - b/q| ≤ 2/m  where
  --   p = N_γ, q = N_α', m = card γ, a = numA_γ, b = numA_α'
  -- Rewrite a/p - b/q = (aq - bp)/(pq)
  -- Goal is now: | numA_γ/NE_γ - numA_α'/NE_α' | ≤ 2 / card γ
  -- where numA_γ and numA_α' in the goal are filter cards.
  have hgoal_eq :
      (numA_γ : ℚ) / (Fintype.card (LinearExt γ) : ℚ) -
      (numA_α' : ℚ) / (Fintype.card (LinearExt α') : ℚ) =
      ((Fintype.card (LinearExt α') : ℚ) * (numA_γ : ℚ) -
        (numA_α' : ℚ) * (Fintype.card (LinearExt γ) : ℚ)) /
        ((Fintype.card (LinearExt γ) : ℚ) * (Fintype.card (LinearExt α') : ℚ)) := by
    field_simp
  have habs_prod :
      |(Fintype.card (LinearExt γ) : ℚ) * (Fintype.card (LinearExt α') : ℚ)| =
      (Fintype.card (LinearExt γ) : ℚ) * (Fintype.card (LinearExt α') : ℚ) :=
    abs_of_pos (by positivity)
  have hNpint_val : (Npint : ℚ) = (Fintype.card (LinearExt α') : ℚ) := by
    rw [hNpint]; exact_mod_cast rfl
  -- Cast hineq_q via hNpint_val to phrase with Fintype.card (LinearExt α').
  rw [hNpint_val] at hineq_q
  -- |num_γ/NE_γ - num_α'/NE_α'| = | ... | / (NE_γ * NE_α')
  have hfinal :
      |(numA_γ : ℚ) / (Fintype.card (LinearExt γ) : ℚ) -
        (numA_α' : ℚ) / (Fintype.card (LinearExt α') : ℚ)| ≤
      2 / (Fintype.card γ : ℚ) := by
    rw [hgoal_eq, abs_div, habs_prod, div_le_div_iff₀ (by positivity) hm_posq]
    nlinarith [hineq_q,
      abs_nonneg ((Fintype.card (LinearExt α') : ℚ) * numA_γ -
        numA_α' * (Fintype.card (LinearExt γ) : ℚ))]
  exact hfinal

end LinearExt
end OneThird
