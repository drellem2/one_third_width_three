/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.LinearExt
import OneThird.Mathlib.LinearExtension.Birkhoff

/-!
# Birkhoff correspondence for `RelationPoset α`

For a finite data poset `Q : RelationPoset α` with `n = Fintype.card α`,
every linear extension `L : LinearExt' Q` induces a saturated chain
of order ideals (lower sets w.r.t. `Q.le`)

  `∅ = I'_0 ⊆ I'_1 ⊆ ⋯ ⊆ I'_n = α`

with `|I'_k| = k`. The map `L ↦ (k ↦ L.initialIdeal' k)` is the data
analogue of `LinearExt.toIdealChain`.

This file mirrors `OneThird.Mathlib.LinearExtension.Birkhoff` but on
`RelationPoset α` instead of `[PartialOrder α]`. It is the foundation
for the data-version FKG monotonicity-under-augmentation of A8-S2-cont-3
(used in `OneThird.Mathlib.RelationPoset.FKG`).

## Main declarations

* `LinearExt'.initialIdeal' L k` — `{x | (L.pos x).val < k}` as a
  `Finset α`.
* `LinearExt'.initialIdeal'_isLowerSet` — closed under `Q.le`-down.
* `LinearExt'.initialIdeal'_card_le`, `_succ`, `_mono`, `_zero`,
  `_card_univ` — the standard chain bookkeeping.
* `RelationPoset.IdealChain' Q` — the type of saturated `Q`-ideal
  chains.
* `LinearExt'.toIdealChain'` / `IdealChain'.toLinearExt'` — bijection.
* `LinearExt'.equivIdealChain' : LinearExt' Q ≃ IdealChain' Q`.

## Reference

* `OneThird.Mathlib.LinearExtension.Birkhoff` — the typeclass-based
  parent file mirrored here.
-/

namespace OneThird

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

namespace LinearExt'

variable {Q : RelationPoset α}

/-! ### §1 — Initial ideals as `Finset α` -/

/-- The **initial ideal** of `L : LinearExt' Q` at level `k`: the
positions strictly below `k`. -/
def initialIdeal' (L : LinearExt' Q) (k : ℕ) : Finset α :=
  (Finset.univ : Finset α).filter (fun x => (L.pos x).val < k)

@[simp] lemma mem_initialIdeal' {L : LinearExt' Q} {k : ℕ} {x : α} :
    x ∈ L.initialIdeal' k ↔ (L.pos x).val < k := by
  simp [initialIdeal']

@[simp] lemma initialIdeal'_zero (L : LinearExt' Q) :
    L.initialIdeal' 0 = ∅ := by
  ext x; simp [initialIdeal']

/-- At level `n = Fintype.card α`, the initial ideal is all of `α`. -/
lemma initialIdeal'_card_univ (L : LinearExt' Q) :
    L.initialIdeal' (Fintype.card α) = (Finset.univ : Finset α) := by
  ext x
  simp only [mem_initialIdeal', Finset.mem_univ, iff_true]
  exact (L.pos x).isLt

/-- Any level `k ≥ n` gives the full universe. -/
lemma initialIdeal'_of_card_le (L : LinearExt' Q) {k : ℕ}
    (hk : Fintype.card α ≤ k) :
    L.initialIdeal' k = (Finset.univ : Finset α) := by
  ext x
  simp only [mem_initialIdeal', Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (L.pos x).isLt hk

/-- **Lower-set property**: `initialIdeal' L k` is closed under
`Q.le`-down. -/
lemma initialIdeal'_isLowerSet (L : LinearExt' Q) (k : ℕ) {x y : α}
    (hxy : Q.le x y) (hy : y ∈ L.initialIdeal' k) :
    x ∈ L.initialIdeal' k := by
  simp only [mem_initialIdeal'] at hy ⊢
  exact lt_of_le_of_lt (L.monotone hxy) hy

/-- The chain is weakly increasing in the level. -/
lemma initialIdeal'_mono (L : LinearExt' Q) {k k' : ℕ} (h : k ≤ k') :
    L.initialIdeal' k ⊆ L.initialIdeal' k' := by
  intro x hx
  simp only [mem_initialIdeal'] at hx ⊢
  exact lt_of_lt_of_le hx h

/-! ### §2 — Cardinality -/

/-- The cardinality of the `k`-th initial ideal is exactly `k`,
for `k ≤ n`. -/
lemma initialIdeal'_card_le (L : LinearExt' Q) {k : ℕ}
    (hk : k ≤ Fintype.card α) :
    (L.initialIdeal' k).card = k := by
  classical
  have hinj : Set.InjOn L.toFun ((L.initialIdeal' k : Finset α) : Set α) :=
    fun a _ b _ h => L.toFun.injective h
  have hcard_img : (L.initialIdeal' k).card =
      ((L.initialIdeal' k).image L.toFun).card :=
    (Finset.card_image_of_injOn hinj).symm
  rcases lt_or_eq_of_le hk with hklt | hkeq
  · -- k < n: image = `Finset.Iio ⟨k, hklt⟩`.
    have himg :
        (L.initialIdeal' k).image L.toFun =
          Finset.Iio (⟨k, hklt⟩ : Fin (Fintype.card α)) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_Iio, mem_initialIdeal']
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, rfl⟩
        change (L.toFun x).val < k
        exact hx
      · intro hi
        refine ⟨L.toFun.symm i, ?_, by simp⟩
        change ((L.pos (L.toFun.symm i))).val < k
        simp only [LinearExt'.pos, Equiv.apply_symm_apply]
        exact hi
    rw [hcard_img, himg, Fin.card_Iio]
  · -- k = n: image is univ.
    subst hkeq
    rw [initialIdeal'_card_univ, Finset.card_univ]

/-! ### §3 — Successor step -/

/-- The element at position `k` (for `k < n`). -/
def atPos' (L : LinearExt' Q) {k : ℕ} (hk : k < Fintype.card α) : α :=
  L.toFun.symm ⟨k, hk⟩

@[simp] lemma pos_atPos' (L : LinearExt' Q) {k : ℕ}
    (hk : k < Fintype.card α) :
    (L.pos (L.atPos' hk)).val = k := by
  simp [atPos', LinearExt'.pos]

lemma atPos'_notMem_initialIdeal' (L : LinearExt' Q) {k : ℕ}
    (hk : k < Fintype.card α) :
    L.atPos' hk ∉ L.initialIdeal' k := by
  simp [mem_initialIdeal', pos_atPos']

lemma atPos'_mem_initialIdeal'_succ (L : LinearExt' Q) {k : ℕ}
    (hk : k < Fintype.card α) :
    L.atPos' hk ∈ L.initialIdeal' (k + 1) := by
  simp [mem_initialIdeal', pos_atPos']

/-- **Successor step**: `initialIdeal' L (k+1) = insert (atPos' k) (initialIdeal' L k)`. -/
lemma initialIdeal'_succ (L : LinearExt' Q) {k : ℕ}
    (hk : k < Fintype.card α) :
    L.initialIdeal' (k + 1) = insert (L.atPos' hk) (L.initialIdeal' k) := by
  ext x
  simp only [mem_initialIdeal', Finset.mem_insert]
  constructor
  · intro hx
    rcases Nat.lt_or_ge (L.pos x).val k with hlt | hge
    · exact Or.inr hlt
    · have heq : (L.pos x).val = k := by omega
      left
      apply L.pos_injective
      apply Fin.ext
      rw [heq, pos_atPos']
  · rintro (rfl | hx)
    · rw [pos_atPos']; exact Nat.lt_succ_self k
    · exact Nat.lt_succ_of_lt hx

lemma initialIdeal'_succ_sdiff (L : LinearExt' Q) {k : ℕ}
    (hk : k < Fintype.card α) :
    L.initialIdeal' (k + 1) \ L.initialIdeal' k = {L.atPos' hk} := by
  rw [initialIdeal'_succ L hk, Finset.insert_sdiff_of_notMem _
    (atPos'_notMem_initialIdeal' L hk), Finset.sdiff_self]
  rfl

/-! ### §4 — Determinism -/

lemma ext_of_initialIdeal'_eq {L₁ L₂ : LinearExt' Q}
    (h : ∀ k ≤ Fintype.card α, L₁.initialIdeal' k = L₂.initialIdeal' k) :
    L₁ = L₂ := by
  apply LinearExt'.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (L₁.pos x).val = (L₂.pos x).val
  set k₁ : ℕ := (L₁.pos x).val with hk₁
  set k₂ : ℕ := (L₂.pos x).val with hk₂
  have hk₁_lt : k₁ < Fintype.card α := (L₁.pos x).isLt
  have hk₂_lt : k₂ < Fintype.card α := (L₂.pos x).isLt
  have hx₁_mem : x ∈ L₁.initialIdeal' (k₁ + 1) := by
    rw [mem_initialIdeal']; exact Nat.lt_succ_self _
  have hx₂_mem : x ∈ L₂.initialIdeal' (k₂ + 1) := by
    rw [mem_initialIdeal']; exact Nat.lt_succ_self _
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exfalso
    have hle : k₁ + 1 ≤ Fintype.card α := hk₁_lt
    have heq12 : L₁.initialIdeal' (k₁ + 1) = L₂.initialIdeal' (k₁ + 1) := h _ hle
    rw [heq12, mem_initialIdeal'] at hx₁_mem
    omega
  · exact heq
  · exfalso
    have hle : k₂ + 1 ≤ Fintype.card α := hk₂_lt
    have heq21 : L₁.initialIdeal' (k₂ + 1) = L₂.initialIdeal' (k₂ + 1) := h _ hle
    rw [← heq21, mem_initialIdeal'] at hx₂_mem
    omega

end LinearExt'

/-! ### §5 — `IdealChain' Q`: saturated `Q`-ideal chains -/

/-- A **`Q`-ideal chain** is a saturated chain of `Q`-lower-sets:
`Fin (Fintype.card α + 1) → Finset α` with each level a `Q`-lower-set,
nesting, and linear cardinality. -/
structure IdealChain' (Q : RelationPoset α) where
  /-- Underlying sequence of ideals. -/
  toFun : Fin (Fintype.card α + 1) → Finset α
  /-- Each `toFun k` is a `Q`-lower-set. -/
  isLowerSet : ∀ k, ∀ {x y : α}, Q.le x y → y ∈ toFun k → x ∈ toFun k
  /-- Cardinality grows linearly. -/
  card_eq : ∀ k, (toFun k).card = k.val
  /-- Nesting. -/
  mono : Monotone toFun

namespace IdealChain'

variable {Q : RelationPoset α}

lemma toFun_zero (C : IdealChain' Q) : C.toFun 0 = ∅ := by
  rw [← Finset.card_eq_zero]
  simpa using C.card_eq 0

lemma toFun_card (C : IdealChain' Q) :
    C.toFun ⟨Fintype.card α, Nat.lt_succ_self _⟩ = (Finset.univ : Finset α) := by
  apply Finset.eq_univ_of_card
  rw [C.card_eq]

lemma sdiff_succ_card (C : IdealChain' Q) (k : Fin (Fintype.card α)) :
    (C.toFun k.succ \ C.toFun k.castSucc).card = 1 := by
  have hmono : C.toFun k.castSucc ⊆ C.toFun k.succ :=
    C.mono (by change k.val ≤ k.val + 1; exact Nat.le_succ _)
  rw [Finset.card_sdiff_of_subset hmono, C.card_eq k.succ, C.card_eq k.castSucc]
  change k.val + 1 - k.val = 1
  omega

@[ext] lemma ext' {C₁ C₂ : IdealChain' Q}
    (h : ∀ k, C₁.toFun k = C₂.toFun k) : C₁ = C₂ := by
  cases C₁; cases C₂
  congr 1
  funext k
  exact h k

end IdealChain'

/-! ### §6 — Forward map: `LinearExt' Q → IdealChain' Q` -/

namespace LinearExt'

variable {Q : RelationPoset α}

/-- Chain of initial ideals of a `LinearExt'`, packaged as `IdealChain'`. -/
def toIdealChain' (L : LinearExt' Q) : IdealChain' Q where
  toFun := fun k => L.initialIdeal' k.val
  isLowerSet := fun _ {_ _} hxy hy => L.initialIdeal'_isLowerSet _ hxy hy
  card_eq := fun k =>
    L.initialIdeal'_card_le (by exact Nat.le_of_lt_succ k.isLt)
  mono := fun _ _ hk => L.initialIdeal'_mono hk

@[simp] lemma toIdealChain'_toFun (L : LinearExt' Q)
    (k : Fin (Fintype.card α + 1)) :
    L.toIdealChain'.toFun k = L.initialIdeal' k.val := rfl

lemma toIdealChain'_injective :
    Function.Injective (toIdealChain' : LinearExt' Q → IdealChain' Q) := by
  intro L₁ L₂ h
  apply LinearExt'.ext_of_initialIdeal'_eq
  intro k hk
  have := congrArg (fun (C : IdealChain' Q) => C.toFun ⟨k, Nat.lt_succ_of_le hk⟩) h
  simpa [toIdealChain'] using this

end LinearExt'

/-! ### §7 — Inverse map: `IdealChain' Q → LinearExt' Q` -/

namespace IdealChain'

variable {Q : RelationPoset α}

/-- The element added at step `k`. -/
noncomputable def stepElt (C : IdealChain' Q) (k : Fin (Fintype.card α)) : α := by
  classical
  have h : (C.toFun k.succ \ C.toFun k.castSucc).card = 1 :=
    C.sdiff_succ_card k
  exact (Finset.card_eq_one.mp h).choose

lemma stepElt_spec (C : IdealChain' Q) (k : Fin (Fintype.card α)) :
    C.toFun k.succ \ C.toFun k.castSucc = {C.stepElt k} := by
  classical
  have h : (C.toFun k.succ \ C.toFun k.castSucc).card = 1 :=
    C.sdiff_succ_card k
  exact (Finset.card_eq_one.mp h).choose_spec

lemma stepElt_mem_succ (C : IdealChain' Q) (k : Fin (Fintype.card α)) :
    C.stepElt k ∈ C.toFun k.succ := by
  have hmem : C.stepElt k ∈ C.toFun k.succ \ C.toFun k.castSucc := by
    rw [C.stepElt_spec]; exact Finset.mem_singleton.mpr rfl
  exact (Finset.mem_sdiff.mp hmem).1

lemma stepElt_notMem_castSucc (C : IdealChain' Q) (k : Fin (Fintype.card α)) :
    C.stepElt k ∉ C.toFun k.castSucc := by
  have hmem : C.stepElt k ∈ C.toFun k.succ \ C.toFun k.castSucc := by
    rw [C.stepElt_spec]; exact Finset.mem_singleton.mpr rfl
  exact (Finset.mem_sdiff.mp hmem).2

lemma stepElt_injective (C : IdealChain' Q) :
    Function.Injective C.stepElt := by
  intro k₁ k₂ heq
  classical
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : C.stepElt k₁ ∈ C.toFun k₁.succ := C.stepElt_mem_succ k₁
    have hle : (k₁.succ : Fin (Fintype.card α + 1)) ≤ k₂.castSucc := by
      change (k₁.val + 1 : ℕ) ≤ k₂.val
      exact hlt
    have h2 : C.stepElt k₁ ∈ C.toFun k₂.castSucc := C.mono hle h1
    rw [heq] at h2
    exact C.stepElt_notMem_castSucc k₂ h2
  · have h1 : C.stepElt k₂ ∈ C.toFun k₂.succ := C.stepElt_mem_succ k₂
    have hle : (k₂.succ : Fin (Fintype.card α + 1)) ≤ k₁.castSucc := by
      change (k₂.val + 1 : ℕ) ≤ k₁.val
      exact hgt
    have h2 : C.stepElt k₂ ∈ C.toFun k₁.castSucc := C.mono hle h1
    rw [← heq] at h2
    exact C.stepElt_notMem_castSucc k₁ h2

lemma stepElt_surjective (C : IdealChain' Q) :
    Function.Surjective C.stepElt := by
  classical
  intro x
  let S : Finset (Fin (Fintype.card α + 1)) :=
    (Finset.univ : Finset (Fin (Fintype.card α + 1))).filter
      (fun m => x ∈ C.toFun m)
  have hS_ne : S.Nonempty := by
    refine ⟨⟨Fintype.card α, Nat.lt_succ_self _⟩, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [toFun_card]
    exact Finset.mem_univ _
  set m_min : Fin (Fintype.card α + 1) := S.min' hS_ne with hm_def
  have hm_mem : m_min ∈ S := S.min'_mem hS_ne
  have hx_at_min : x ∈ C.toFun m_min := (Finset.mem_filter.mp hm_mem).2
  have hm_val_pos : 0 < m_min.val := by
    by_contra h0
    have h0' : m_min.val = 0 := Nat.eq_zero_of_not_pos h0
    have h0_eq : m_min = (0 : Fin (Fintype.card α + 1)) := Fin.ext h0'
    rw [h0_eq, toFun_zero] at hx_at_min
    exact Finset.notMem_empty _ hx_at_min
  have hk_lt : m_min.val - 1 < Fintype.card α := by
    have : m_min.val < Fintype.card α + 1 := m_min.isLt
    omega
  refine ⟨⟨m_min.val - 1, hk_lt⟩, ?_⟩
  set k : Fin (Fintype.card α) := ⟨m_min.val - 1, hk_lt⟩ with hk_def
  have hk_succ : (k.succ : Fin (Fintype.card α + 1)) = m_min := by
    apply Fin.ext
    change k.val + 1 = m_min.val
    change (m_min.val - 1) + 1 = m_min.val
    omega
  have hx_notIn_cs : x ∉ C.toFun k.castSucc := by
    intro hh
    have hcs_mem : k.castSucc ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
    have hle : m_min ≤ k.castSucc := S.min'_le _ hcs_mem
    have : m_min.val ≤ m_min.val - 1 := hle
    omega
  have hx_mem_sdiff : x ∈ C.toFun k.succ \ C.toFun k.castSucc := by
    refine Finset.mem_sdiff.mpr ⟨?_, hx_notIn_cs⟩
    rw [hk_succ]; exact hx_at_min
  rw [C.stepElt_spec] at hx_mem_sdiff
  exact (Finset.mem_singleton.mp hx_mem_sdiff).symm

noncomputable def stepEquiv (C : IdealChain' Q) : Fin (Fintype.card α) ≃ α :=
  Equiv.ofBijective C.stepElt ⟨C.stepElt_injective, C.stepElt_surjective⟩

@[simp] lemma stepEquiv_apply (C : IdealChain' Q) (k : Fin (Fintype.card α)) :
    C.stepEquiv k = C.stepElt k := rfl

lemma mem_toFun_iff (C : IdealChain' Q) (x : α) (m : Fin (Fintype.card α + 1)) :
    x ∈ C.toFun m ↔ (C.stepEquiv.symm x).val < m.val := by
  classical
  set k : Fin (Fintype.card α) := C.stepEquiv.symm x with hk_def
  have hstep : C.stepElt k = x := by
    have : C.stepEquiv k = x := Equiv.apply_symm_apply _ _
    simpa [stepEquiv_apply] using this
  refine ⟨?_, ?_⟩
  · intro hxm
    by_contra hge
    rw [not_lt] at hge
    have hle : m ≤ (k.castSucc : Fin (Fintype.card α + 1)) := by
      change m.val ≤ k.val; exact hge
    have hmono : C.toFun m ⊆ C.toFun k.castSucc := C.mono hle
    have : x ∈ C.toFun k.castSucc := hmono hxm
    rw [← hstep] at this
    exact C.stepElt_notMem_castSucc k this
  · intro hlt
    have hle : (k.succ : Fin (Fintype.card α + 1)) ≤ m := by
      change k.val + 1 ≤ m.val; exact hlt
    have hmono : C.toFun k.succ ⊆ C.toFun m := C.mono hle
    have hmem_succ : x ∈ C.toFun k.succ := by
      rw [← hstep]; exact C.stepElt_mem_succ k
    exact hmono hmem_succ

/-- **Inverse map**: build a `LinearExt' Q` from an ideal chain. -/
noncomputable def toLinearExt' (C : IdealChain' Q) : LinearExt' Q where
  toFun := C.stepEquiv.symm
  monotone := by
    classical
    intro x y hxy
    set kx : Fin (Fintype.card α) := C.stepEquiv.symm x with hkx_def
    set ky : Fin (Fintype.card α) := C.stepEquiv.symm y with hky_def
    change kx ≤ ky
    by_contra hlt
    rw [not_le] at hlt
    have hy_mem : y ∈ C.toFun ky.succ := by
      rw [mem_toFun_iff]
      change ky.val < ky.val + 1
      exact Nat.lt_succ_self _
    -- Use the lower-set property: y ∈ C.toFun ky.succ and Q.le x y → x ∈ C.toFun ky.succ.
    have hx_mem : x ∈ C.toFun ky.succ := C.isLowerSet ky.succ hxy hy_mem
    rw [mem_toFun_iff] at hx_mem
    have h1 : kx.val < ky.val + 1 := hx_mem
    have h2 : ky.val < kx.val := hlt
    omega

@[simp] lemma toLinearExt'_toFun (C : IdealChain' Q) :
    C.toLinearExt'.toFun = C.stepEquiv.symm := rfl

@[simp] lemma toLinearExt'_pos (C : IdealChain' Q) (x : α) :
    C.toLinearExt'.pos x = C.stepEquiv.symm x := rfl

end IdealChain'

/-! ### §8 — Round trips and the bijection -/

namespace LinearExt'

variable {Q : RelationPoset α}

lemma toLinearExt'_toIdealChain' (L : LinearExt' Q) :
    L.toIdealChain'.toLinearExt' = L := by
  classical
  apply LinearExt'.ext
  apply Equiv.ext
  intro x
  apply L.toIdealChain'.stepEquiv.symm_apply_eq.mpr
  change x = L.toIdealChain'.stepEquiv (L.toFun x)
  rw [IdealChain'.stepEquiv_apply]
  have hstep := L.toIdealChain'.stepElt_spec (L.toFun x)
  have hx_mem : x ∈
      L.toIdealChain'.toFun (L.toFun x).succ \
        L.toIdealChain'.toFun (L.toFun x).castSucc := by
    simp only [toIdealChain'_toFun, Finset.mem_sdiff, mem_initialIdeal']
    refine ⟨?_, ?_⟩
    · change (L.pos x).val < (L.toFun x).succ.val
      change (L.pos x).val < (L.toFun x).val + 1
      rw [show (L.toFun x).val = (L.pos x).val from rfl]
      exact Nat.lt_succ_self _
    · change ¬ (L.pos x).val < (L.toFun x).castSucc.val
      change ¬ (L.pos x).val < (L.toFun x).val
      rw [show (L.toFun x).val = (L.pos x).val from rfl]
      exact Nat.lt_irrefl _
  rw [hstep] at hx_mem
  exact Finset.mem_singleton.mp hx_mem

end LinearExt'

namespace IdealChain'

variable {Q : RelationPoset α}

lemma toIdealChain'_toLinearExt' (C : IdealChain' Q) :
    C.toLinearExt'.toIdealChain' = C := by
  apply IdealChain'.ext'
  intro k
  apply Finset.ext
  intro x
  simp only [LinearExt'.toIdealChain'_toFun, LinearExt'.mem_initialIdeal']
  rw [IdealChain'.mem_toFun_iff]
  rfl

end IdealChain'

namespace LinearExt'

variable {Q : RelationPoset α}

/-- **Birkhoff correspondence (data version)**: `LinearExt' Q ≃ IdealChain' Q`. -/
noncomputable def equivIdealChain' : LinearExt' Q ≃ IdealChain' Q where
  toFun := LinearExt'.toIdealChain'
  invFun := IdealChain'.toLinearExt'
  left_inv := LinearExt'.toLinearExt'_toIdealChain'
  right_inv := IdealChain'.toIdealChain'_toLinearExt'

end LinearExt'

/-! ### §9 — Finite type and card of `IdealChain'` -/

namespace IdealChain'

variable {Q : RelationPoset α}

instance instNonempty (Q : RelationPoset α) : Nonempty (IdealChain' Q) :=
  ⟨(Classical.arbitrary (LinearExt' Q)).toIdealChain'⟩

noncomputable instance instFintype (Q : RelationPoset α) :
    Fintype (IdealChain' Q) :=
  Fintype.ofEquiv (LinearExt' Q) LinearExt'.equivIdealChain'

lemma card_eq_numLinExt' (Q : RelationPoset α) :
    Fintype.card (IdealChain' Q) = numLinExt' Q := by
  classical
  exact Fintype.card_congr LinearExt'.equivIdealChain'.symm

end IdealChain'

/-! ### §10 — Sum-transport -/

namespace LinearExt'

variable {Q : RelationPoset α}

lemma sum_toIdealChain' {β : Type*} [AddCommMonoid β]
    (f : IdealChain' Q → β) :
    ∑ C : IdealChain' Q, f C =
      ∑ L : LinearExt' Q, f (L.toIdealChain') := by
  classical
  refine (Finset.sum_equiv LinearExt'.equivIdealChain' ?_ ?_).symm
  · intro L; simp
  · intro L _; rfl

lemma sum_equivIdealChain' {β : Type*} [AddCommMonoid β]
    (g : LinearExt' Q → β) :
    ∑ L : LinearExt' Q, g L =
      ∑ C : IdealChain' Q, g C.toLinearExt' := by
  classical
  refine Finset.sum_equiv LinearExt'.equivIdealChain' ?_ ?_
  · intro L; simp
  · intro L _
    change g L = g L.toIdealChain'.toLinearExt'
    rw [LinearExt'.toLinearExt'_toIdealChain']

/-- **Birkhoff sum-transport at level `k`** (data version). -/
lemma sum_initialIdeal'_birkhoff {β : Type*} [AddCommMonoid β]
    (k : Fin (Fintype.card α + 1)) (F : Finset α → β) :
    ∑ L : LinearExt' Q, F (L.initialIdeal' k.val) =
      ∑ C : IdealChain' Q, F (C.toFun k) := by
  classical
  rw [sum_toIdealChain' (fun C => F (C.toFun k))]
  rfl

end LinearExt'

end RelationPoset

end OneThird
