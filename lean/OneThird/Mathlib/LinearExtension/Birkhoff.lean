/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Fintype
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.Interval.Finset.Fin

/-!
# Birkhoff correspondence: linear extensions ↔ chains of order ideals

For a finite poset `α` with `n = Fintype.card α` elements, every
linear extension `L : LinearExt α` induces a sequence of order ideals

  `∅ = I_0 ⊆ I_1 ⊆ ⋯ ⊆ I_n = α`

with `|I_k| = k` for every `0 ≤ k ≤ n`, where `I_k = L.initialIdeal k`
is the set of elements placed in the first `k` positions by `L`.

The map `L ↦ (k ↦ L.initialIdeal k)` is a bijection between
`LinearExt α` and the set of such *saturated chains* of order ideals.
This is the **Birkhoff correspondence** specialised to linear
extensions: linear extensions of `α` are in bijection with maximal
chains in the distributive lattice `LowerSet α`.

## Main declarations

* `LinearExt.initialIdeal L k` — the set `{x : α | (L.pos x).val < k}`
  of elements at positions below `k` under `L`.
* `LinearExt.initialIdeal_isLowerSet` — `initialIdeal L k` is a lower
  set (order ideal) of `α`.
* `LinearExt.initialIdeal_card_le` — `|initialIdeal L k| = k`
  when `k ≤ Fintype.card α`.
* `LinearExt.initialIdeal_mono` — the sequence is monotone in `k`.
* `LinearExt.initialIdeal_succ` — `initialIdeal L (k+1) = insert x (initialIdeal L k)`.
* `IdealChain α` — the type of saturated chains of order ideals of `α`.
* `LinearExt.toIdealChain` / `IdealChain.toLinearExt` — the bijection.
* `LinearExt.equivIdealChain : LinearExt α ≃ IdealChain α`.
* `LinearExt.initialLowerSet L k : LowerSet α` — same ideal, packaged
  as an element of the distributive lattice `LowerSet α` (the ambient
  target for FKG transport).

## Downstream use

FKG transport (F6-prereq-2) applies mathlib's `four_functions_theorem`
to functions on `LowerSet α` (or a product thereof) and pulls back
along `toIdealChain` / at a specific slice to recover a correlation
inequality on `LinearExt α`.

## References

* G. Birkhoff, *Rings of sets*, 1937 — the lattice of lower sets is a
  distributive lattice.
* R. P. Stanley, *Enumerative Combinatorics I*, §3.5 — linear
  extensions of a finite poset correspond to maximal chains in its
  lattice of order ideals.
-/

namespace OneThird

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

namespace LinearExt

/-! ### §1 — Initial ideals as `Finset α` -/

/-- The **initial ideal** of `L : LinearExt α` at level `k`: the set
of elements placed at positions strictly below `k` by `L`.

As `k` runs over `0, …, n`, the initial ideals form a saturated chain

  `∅ = initialIdeal L 0 ⊆ initialIdeal L 1 ⊆ ⋯ ⊆ initialIdeal L n = α`

in the distributive lattice `LowerSet α`. -/
def initialIdeal (L : LinearExt α) (k : ℕ) : Finset α :=
  (Finset.univ : Finset α).filter (fun x => (L.pos x).val < k)

@[simp] lemma mem_initialIdeal {L : LinearExt α} {k : ℕ} {x : α} :
    x ∈ L.initialIdeal k ↔ (L.pos x).val < k := by
  simp [initialIdeal]

@[simp] lemma initialIdeal_zero (L : LinearExt α) : L.initialIdeal 0 = ∅ := by
  ext x; simp [initialIdeal]

/-- At level `n = Fintype.card α`, the initial ideal is all of `α`. -/
lemma initialIdeal_card_univ (L : LinearExt α) :
    L.initialIdeal (Fintype.card α) = (Finset.univ : Finset α) := by
  ext x
  simp only [mem_initialIdeal, Finset.mem_univ, iff_true]
  exact (L.pos x).isLt

/-- Any level `k ≥ n` gives the full universe. -/
lemma initialIdeal_of_card_le (L : LinearExt α) {k : ℕ} (hk : Fintype.card α ≤ k) :
    L.initialIdeal k = (Finset.univ : Finset α) := by
  ext x
  simp only [mem_initialIdeal, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (L.pos x).isLt hk

/-- **Lower-set property**: `initialIdeal L k` is an order ideal
(lower set) of `α`. -/
lemma initialIdeal_isLowerSet (L : LinearExt α) (k : ℕ) :
    IsLowerSet ((L.initialIdeal k : Finset α) : Set α) := by
  intro x y hxy hy
  simp only [Finset.coe_filter, initialIdeal, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at hy ⊢
  -- If y ≤ x in α and x is in the ideal (pos < k), then pos(y) ≤ pos(x).
  have hmono : L.pos y ≤ L.pos x := L.monotone hxy
  exact lt_of_le_of_lt hmono hy

/-- The chain is weakly increasing in the level. -/
lemma initialIdeal_mono (L : LinearExt α) {k k' : ℕ} (h : k ≤ k') :
    L.initialIdeal k ⊆ L.initialIdeal k' := by
  intro x hx
  simp only [mem_initialIdeal] at hx ⊢
  exact lt_of_lt_of_le hx h

/-! ### §2 — Cardinality -/

/-- The cardinality of the `k`-th initial ideal is exactly `k`, for
`k ≤ n`: `L.toFun` restricted to this set is a bijection to
`Finset.Iio ⟨k, hk⟩` in `Fin n`. -/
lemma initialIdeal_card_le (L : LinearExt α) {k : ℕ}
    (hk : k ≤ Fintype.card α) :
    (L.initialIdeal k).card = k := by
  classical
  have hinj : Set.InjOn L.toFun ((L.initialIdeal k : Finset α) : Set α) :=
    fun a _ b _ h => L.toFun.injective h
  have hcard_img : (L.initialIdeal k).card = ((L.initialIdeal k).image L.toFun).card :=
    (Finset.card_image_of_injOn hinj).symm
  rcases lt_or_eq_of_le hk with hklt | hkeq
  · -- k < n: image = `Finset.Iio ⟨k, hklt⟩`.
    have himg :
        (L.initialIdeal k).image L.toFun =
          Finset.Iio (⟨k, hklt⟩ : Fin (Fintype.card α)) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_Iio, mem_initialIdeal]
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, rfl⟩
        change (L.toFun x).val < k
        exact hx
      · intro hi
        refine ⟨L.toFun.symm i, ?_, by simp⟩
        change ((L.pos (L.toFun.symm i))).val < k
        simp only [LinearExt.pos, Equiv.apply_symm_apply]
        exact hi
    rw [hcard_img, himg, Fin.card_Iio]
  · -- k = n: image is univ.
    subst hkeq
    rw [initialIdeal_card_univ, Finset.card_univ]

/-! ### §3 — Successor step -/

/-- The element at position `k` (for `k < n`). -/
def atPos (L : LinearExt α) {k : ℕ} (hk : k < Fintype.card α) : α :=
  L.toFun.symm ⟨k, hk⟩

@[simp] lemma pos_atPos (L : LinearExt α) {k : ℕ} (hk : k < Fintype.card α) :
    (L.pos (L.atPos hk)).val = k := by
  simp [atPos, LinearExt.pos]

/-- The element at position `k` is NOT in `initialIdeal L k`
(its position equals `k`, not less). -/
lemma atPos_notMem_initialIdeal (L : LinearExt α) {k : ℕ}
    (hk : k < Fintype.card α) :
    L.atPos hk ∉ L.initialIdeal k := by
  simp [mem_initialIdeal, pos_atPos]

/-- The element at position `k` is in `initialIdeal L (k+1)`. -/
lemma atPos_mem_initialIdeal_succ (L : LinearExt α) {k : ℕ}
    (hk : k < Fintype.card α) :
    L.atPos hk ∈ L.initialIdeal (k + 1) := by
  simp [mem_initialIdeal, pos_atPos]

/-- **Successor step**: `initialIdeal L (k+1) = insert (atPos k) (initialIdeal L k)`. -/
lemma initialIdeal_succ (L : LinearExt α) {k : ℕ} (hk : k < Fintype.card α) :
    L.initialIdeal (k + 1) = insert (L.atPos hk) (L.initialIdeal k) := by
  ext x
  simp only [mem_initialIdeal, Finset.mem_insert]
  constructor
  · intro hx
    rcases Nat.lt_or_ge (L.pos x).val k with hlt | hge
    · exact Or.inr hlt
    · have heq : (L.pos x).val = k := by omega
      left
      apply L.pos_injective
      apply Fin.ext
      rw [heq, pos_atPos]
  · rintro (rfl | hx)
    · rw [pos_atPos]; exact Nat.lt_succ_self k
    · exact Nat.lt_succ_of_lt hx

/-- The difference between two consecutive initial ideals is exactly
`{atPos L k}`. -/
lemma initialIdeal_succ_sdiff (L : LinearExt α) {k : ℕ} (hk : k < Fintype.card α) :
    L.initialIdeal (k + 1) \ L.initialIdeal k = {L.atPos hk} := by
  rw [initialIdeal_succ L hk, Finset.insert_sdiff_of_notMem _
    (atPos_notMem_initialIdeal L hk), Finset.sdiff_self]
  rfl

/-! ### §4 — Determinism -/

/-- Two linear extensions with the same chain of initial ideals
agree at every level: if `L₁.initialIdeal k = L₂.initialIdeal k` for
all `k ≤ n`, then `L₁ = L₂`. -/
lemma ext_of_initialIdeal_eq {L₁ L₂ : LinearExt α}
    (h : ∀ k ≤ Fintype.card α, L₁.initialIdeal k = L₂.initialIdeal k) :
    L₁ = L₂ := by
  apply LinearExt.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (L₁.pos x).val = (L₂.pos x).val
  set k₁ : ℕ := (L₁.pos x).val with hk₁
  set k₂ : ℕ := (L₂.pos x).val with hk₂
  have hk₁_lt : k₁ < Fintype.card α := (L₁.pos x).isLt
  have hk₂_lt : k₂ < Fintype.card α := (L₂.pos x).isLt
  have hx₁_mem : x ∈ L₁.initialIdeal (k₁ + 1) := by
    rw [mem_initialIdeal]; exact Nat.lt_succ_self _
  have hx₂_mem : x ∈ L₂.initialIdeal (k₂ + 1) := by
    rw [mem_initialIdeal]; exact Nat.lt_succ_self _
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exfalso
    have hle : k₁ + 1 ≤ Fintype.card α := hk₁_lt
    have heq12 : L₁.initialIdeal (k₁ + 1) = L₂.initialIdeal (k₁ + 1) := h _ hle
    rw [heq12, mem_initialIdeal] at hx₁_mem
    omega
  · exact heq
  · exfalso
    have hle : k₂ + 1 ≤ Fintype.card α := hk₂_lt
    have heq21 : L₁.initialIdeal (k₂ + 1) = L₂.initialIdeal (k₂ + 1) := h _ hle
    rw [← heq21, mem_initialIdeal] at hx₂_mem
    omega

end LinearExt

/-! ### §5 — `IdealChain α`: saturated ideal chains -/

/-- An **ideal chain** on `α` is a saturated chain of order ideals of
`α`: a function `toFun : Fin (Fintype.card α + 1) → Finset α` such
that each `toFun k` is an order ideal, `|toFun k| = k`, and the
chain is monotone. The endpoints are determined by these
conditions: `toFun 0 = ∅` and `toFun n = univ`.

This is the Birkhoff-correspondence target: `LinearExt α` is in
bijection with `IdealChain α`, which is a subset of the
distributive lattice `Fin (n + 1) → LowerSet α`. -/
structure IdealChain (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] where
  /-- The underlying sequence of ideals. -/
  toFun : Fin (Fintype.card α + 1) → Finset α
  /-- Each `toFun k` is a lower set. -/
  isLowerSet : ∀ k, IsLowerSet ((toFun k : Finset α) : Set α)
  /-- Cardinality grows linearly: `|toFun k| = k.val`. -/
  card_eq : ∀ k, (toFun k).card = k.val
  /-- Nesting: `toFun k ⊆ toFun k'` for `k ≤ k'`. -/
  mono : Monotone toFun

namespace IdealChain

variable (C : IdealChain α)

/-- Endpoint: the 0-th ideal is empty. -/
lemma toFun_zero : C.toFun 0 = ∅ := by
  rw [← Finset.card_eq_zero]
  simpa using C.card_eq 0

/-- Endpoint: the `n`-th ideal is all of `α`. -/
lemma toFun_card : C.toFun ⟨Fintype.card α, Nat.lt_succ_self _⟩ =
    (Finset.univ : Finset α) := by
  apply Finset.eq_univ_of_card
  rw [C.card_eq]

/-- For `k : Fin n`, the difference `C.toFun k.succ \ C.toFun k.castSucc`
has cardinality 1 (here `k.castSucc, k.succ : Fin (n+1)` with values
`k.val` and `k.val + 1`). -/
lemma sdiff_succ_card (C : IdealChain α) (k : Fin (Fintype.card α)) :
    (C.toFun k.succ \ C.toFun k.castSucc).card = 1 := by
  have hmono : C.toFun k.castSucc ⊆ C.toFun k.succ :=
    C.mono (by
      change k.val ≤ k.val + 1
      exact Nat.le_succ _)
  rw [Finset.card_sdiff_of_subset hmono, C.card_eq k.succ, C.card_eq k.castSucc]
  change k.val + 1 - k.val = 1
  omega

/-- Two ideal chains are equal iff they agree on every level. -/
@[ext] lemma ext' {C₁ C₂ : IdealChain α} (h : ∀ k, C₁.toFun k = C₂.toFun k) :
    C₁ = C₂ := by
  cases C₁; cases C₂
  congr 1
  funext k
  exact h k

end IdealChain

/-! ### §6 — Forward map: `LinearExt α → IdealChain α` -/

namespace LinearExt

/-- The chain of initial ideals of a linear extension, packaged as
an `IdealChain`. -/
def toIdealChain (L : LinearExt α) : IdealChain α where
  toFun := fun k => L.initialIdeal k.val
  isLowerSet := fun k => L.initialIdeal_isLowerSet _
  card_eq := fun k =>
    L.initialIdeal_card_le (by exact Nat.le_of_lt_succ k.isLt)
  mono := fun _ _ hk => L.initialIdeal_mono hk

@[simp] lemma toIdealChain_toFun (L : LinearExt α)
    (k : Fin (Fintype.card α + 1)) :
    L.toIdealChain.toFun k = L.initialIdeal k.val := rfl

/-- The forward map is injective. -/
lemma toIdealChain_injective :
    Function.Injective (toIdealChain : LinearExt α → IdealChain α) := by
  intro L₁ L₂ h
  apply LinearExt.ext_of_initialIdeal_eq
  intro k hk
  have := congrArg (fun (C : IdealChain α) => C.toFun ⟨k, Nat.lt_succ_of_le hk⟩) h
  simpa [toIdealChain] using this

end LinearExt

/-! ### §7 — Inverse map: `IdealChain α → LinearExt α` -/

namespace IdealChain

variable (C : IdealChain α)

/-- The element added at step `k`: the unique element of
`C.toFun k.succ \ C.toFun k.castSucc`. -/
noncomputable def stepElt (C : IdealChain α) (k : Fin (Fintype.card α)) : α := by
  classical
  have h : (C.toFun k.succ \ C.toFun k.castSucc).card = 1 :=
    C.sdiff_succ_card k
  exact (Finset.card_eq_one.mp h).choose

lemma stepElt_spec (C : IdealChain α) (k : Fin (Fintype.card α)) :
    C.toFun k.succ \ C.toFun k.castSucc = {C.stepElt k} := by
  classical
  have h : (C.toFun k.succ \ C.toFun k.castSucc).card = 1 :=
    C.sdiff_succ_card k
  exact (Finset.card_eq_one.mp h).choose_spec

lemma stepElt_mem_succ (C : IdealChain α) (k : Fin (Fintype.card α)) :
    C.stepElt k ∈ C.toFun k.succ := by
  have hmem : C.stepElt k ∈ C.toFun k.succ \ C.toFun k.castSucc := by
    rw [C.stepElt_spec]; exact Finset.mem_singleton.mpr rfl
  exact (Finset.mem_sdiff.mp hmem).1

lemma stepElt_notMem_castSucc (C : IdealChain α) (k : Fin (Fintype.card α)) :
    C.stepElt k ∉ C.toFun k.castSucc := by
  have hmem : C.stepElt k ∈ C.toFun k.succ \ C.toFun k.castSucc := by
    rw [C.stepElt_spec]; exact Finset.mem_singleton.mpr rfl
  exact (Finset.mem_sdiff.mp hmem).2

/-- Different steps produce different elements. -/
lemma stepElt_injective (C : IdealChain α) :
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

/-- Every element of `α` appears as some `stepElt k`. -/
lemma stepElt_surjective (C : IdealChain α) :
    Function.Surjective C.stepElt := by
  classical
  intro x
  -- Consider the set of levels m : Fin (n+1) where x ∈ C.toFun m. Nonempty (level n), find min.
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
  -- m_min is not the zero level (else x ∈ ∅).
  have hm_val_pos : 0 < m_min.val := by
    by_contra h0
    have h0' : m_min.val = 0 := Nat.eq_zero_of_not_pos h0
    have h0_eq : m_min = (0 : Fin (Fintype.card α + 1)) := Fin.ext h0'
    rw [h0_eq, toFun_zero] at hx_at_min
    exact Finset.notMem_empty _ hx_at_min
  -- m_min.val ≤ n, so m_min.val - 1 < n.
  have hk_lt : m_min.val - 1 < Fintype.card α := by
    have : m_min.val < Fintype.card α + 1 := m_min.isLt
    omega
  refine ⟨⟨m_min.val - 1, hk_lt⟩, ?_⟩
  -- Show x = stepElt ⟨m_min.val - 1, _⟩.
  set k : Fin (Fintype.card α) := ⟨m_min.val - 1, hk_lt⟩ with hk_def
  -- k.succ.val = m_min.val, k.castSucc.val = m_min.val - 1.
  have hk_succ : (k.succ : Fin (Fintype.card α + 1)) = m_min := by
    apply Fin.ext
    change k.val + 1 = m_min.val
    change (m_min.val - 1) + 1 = m_min.val
    omega
  -- x ∉ C.toFun k.castSucc by minimality.
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

/-- Bijection `Fin n → α` from the chain via `stepElt`. -/
noncomputable def stepEquiv (C : IdealChain α) : Fin (Fintype.card α) ≃ α :=
  Equiv.ofBijective C.stepElt ⟨C.stepElt_injective, C.stepElt_surjective⟩

@[simp] lemma stepEquiv_apply (C : IdealChain α) (k : Fin (Fintype.card α)) :
    C.stepEquiv k = C.stepElt k := rfl

/-- `x ∈ C.toFun m` iff the step-index `C.stepEquiv.symm x` is `< m.val`. -/
lemma mem_toFun_iff (C : IdealChain α) (x : α) (m : Fin (Fintype.card α + 1)) :
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

/-- **Inverse map**: construct a linear extension from an ideal chain
via the step-equivalence. -/
noncomputable def toLinearExt (C : IdealChain α) : LinearExt α where
  toFun := C.stepEquiv.symm
  monotone := by
    classical
    intro x y hxy
    -- Goal: C.stepEquiv.symm x ≤ C.stepEquiv.symm y.
    set kx : Fin (Fintype.card α) := C.stepEquiv.symm x with hkx_def
    set ky : Fin (Fintype.card α) := C.stepEquiv.symm y with hky_def
    change kx ≤ ky
    by_contra hlt
    rw [not_le] at hlt
    -- hlt : ky < kx. So y at step ky < kx.
    -- Then y ∈ C.toFun ky.succ (level ky.val+1), and x ≤ y since hxy : x ≤ y.
    -- Wait: hxy is x ≤ y. We need to go from y ∈ lower set to x ∈ lower set
    -- — but lower set is closed under going DOWN, so we need x ≤ y and y ∈ S
    -- to get x ∈ S.
    -- However, here `C.isLowerSet` is about going down: if a ≤ b and b ∈ S, a ∈ S.
    have hy_mem : y ∈ C.toFun ky.succ := by
      rw [mem_toFun_iff]
      change ky.val < ky.val + 1
      exact Nat.lt_succ_self _
    have hLS := C.isLowerSet ky.succ
    have hx_mem : x ∈ (C.toFun ky.succ : Set α) := hLS hxy (by exact_mod_cast hy_mem)
    rw [Finset.mem_coe, mem_toFun_iff] at hx_mem
    -- hx_mem : kx.val < ky.succ.val = ky.val + 1; combined with hlt : ky.val < kx.val gives
    -- contradiction.
    have h1 : kx.val < ky.val + 1 := hx_mem
    have h2 : ky.val < kx.val := hlt
    omega

@[simp] lemma toLinearExt_toFun (C : IdealChain α) :
    C.toLinearExt.toFun = C.stepEquiv.symm := rfl

@[simp] lemma toLinearExt_pos (C : IdealChain α) (x : α) :
    C.toLinearExt.pos x = C.stepEquiv.symm x := rfl

end IdealChain

/-! ### §8 — Round trips and the bijection -/

namespace LinearExt

/-- Round-trip: a linear extension recovered from its ideal chain
equals the original. -/
lemma toLinearExt_toIdealChain (L : LinearExt α) :
    L.toIdealChain.toLinearExt = L := by
  classical
  apply LinearExt.ext
  apply Equiv.ext
  intro x
  -- Goal: C.toLinearExt.toFun x = L.toFun x, i.e. C.stepEquiv.symm x = L.toFun x.
  -- Equivalently (applying stepEquiv to both sides):
  --   x = C.stepEquiv (L.toFun x) = C.stepElt (L.toFun x).
  apply L.toIdealChain.stepEquiv.symm_apply_eq.mpr
  change x = L.toIdealChain.stepEquiv (L.toFun x)
  rw [IdealChain.stepEquiv_apply]
  -- Now show x = L.toIdealChain.stepElt (L.toFun x).
  have hstep := L.toIdealChain.stepElt_spec (L.toFun x)
  have hx_mem : x ∈
      L.toIdealChain.toFun (L.toFun x).succ \
        L.toIdealChain.toFun (L.toFun x).castSucc := by
    simp only [toIdealChain_toFun, Finset.mem_sdiff, mem_initialIdeal]
    refine ⟨?_, ?_⟩
    · change (L.pos x).val < (L.toFun x).succ.val
      change (L.pos x).val < (L.toFun x).val + 1
      rw [show (L.toFun x).val = (L.pos x).val from rfl]
      exact Nat.lt_succ_self _
    · change ¬ (L.pos x).val < (L.toFun x).castSucc.val
      change ¬ (L.pos x).val < (L.toFun x).val
      rw [show (L.toFun x).val = (L.pos x).val from rfl]
      exact lt_irrefl _
  rw [hstep] at hx_mem
  exact Finset.mem_singleton.mp hx_mem

end LinearExt

namespace IdealChain

/-- Round-trip: an ideal chain recovered from its linear extension
equals the original. -/
lemma toIdealChain_toLinearExt (C : IdealChain α) :
    C.toLinearExt.toIdealChain = C := by
  apply IdealChain.ext'
  intro k
  apply Finset.ext
  intro x
  simp only [LinearExt.toIdealChain_toFun, LinearExt.mem_initialIdeal]
  rw [IdealChain.mem_toFun_iff]
  rfl

end IdealChain

namespace LinearExt

/-- **Birkhoff correspondence**: `LinearExt α` is in bijection with
`IdealChain α`, the type of saturated chains of order ideals of `α`. -/
noncomputable def equivIdealChain : LinearExt α ≃ IdealChain α where
  toFun := LinearExt.toIdealChain
  invFun := IdealChain.toLinearExt
  left_inv := LinearExt.toLinearExt_toIdealChain
  right_inv := IdealChain.toIdealChain_toLinearExt

/-! ### §9 — `LowerSet α`-valued ideal chain -/

/-- `initialIdeal L k`, packaged as a term of the distributive lattice
`LowerSet α`. -/
def initialLowerSet (L : LinearExt α) (k : ℕ) : LowerSet α :=
  ⟨(L.initialIdeal k : Finset α), L.initialIdeal_isLowerSet k⟩

@[simp] lemma coe_initialLowerSet (L : LinearExt α) (k : ℕ) :
    (L.initialLowerSet k : Set α) = (L.initialIdeal k : Finset α) := rfl

@[simp] lemma mem_initialLowerSet (L : LinearExt α) (k : ℕ) (x : α) :
    x ∈ L.initialLowerSet k ↔ (L.pos x).val < k := by
  change x ∈ ((L.initialIdeal k : Finset α) : Set α) ↔ _
  rw [Finset.mem_coe, mem_initialIdeal]

/-- The `LowerSet`-valued chain is monotone in the level. In mathlib
`LowerSet α` is ordered by set inclusion (`s ≤ t ↔ s.carrier ⊆ t.carrier`),
so a growing chain of ideals is an *increasing* chain in `LowerSet α`. -/
lemma initialLowerSet_mono (L : LinearExt α) :
    Monotone (L.initialLowerSet) := by
  intro k k' hk
  change (L.initialLowerSet k : Set α) ⊆ L.initialLowerSet k'
  simp only [coe_initialLowerSet, Finset.coe_subset]
  exact L.initialIdeal_mono hk

end LinearExt

/-! ### §10 — Finite type and card of `IdealChain` -/

namespace IdealChain

instance instNonempty : Nonempty (IdealChain α) :=
  ⟨(Classical.arbitrary (LinearExt α)).toIdealChain⟩

/-- `IdealChain α` is a finite type (via the bijection with
`LinearExt α`). -/
noncomputable instance instFintype : Fintype (IdealChain α) :=
  Fintype.ofEquiv (LinearExt α) LinearExt.equivIdealChain

/-- `Fintype.card (IdealChain α) = numLinExt α`. -/
lemma card_eq_numLinExt :
    Fintype.card (IdealChain α) = numLinExt α := by
  classical
  exact Fintype.card_congr LinearExt.equivIdealChain.symm

end IdealChain

/-! ### §11 — Sum-transport -/

namespace LinearExt

/-- **Sum-transport** via the Birkhoff bijection, from ideal chains
to linear extensions. -/
lemma sum_toIdealChain {β : Type*} [AddCommMonoid β] (f : IdealChain α → β) :
    ∑ C : IdealChain α, f C =
      ∑ L : LinearExt α, f (L.toIdealChain) := by
  classical
  refine (Finset.sum_equiv LinearExt.equivIdealChain ?_ ?_).symm
  · intro L; simp
  · intro L _; rfl

/-- **Sum-transport** via the Birkhoff bijection, from linear
extensions to ideal chains. -/
lemma sum_equivIdealChain {β : Type*} [AddCommMonoid β]
    (g : LinearExt α → β) :
    ∑ L : LinearExt α, g L =
      ∑ C : IdealChain α, g C.toLinearExt := by
  classical
  refine Finset.sum_equiv LinearExt.equivIdealChain ?_ ?_
  · intro L; simp
  · intro L _
    change g L = g L.toIdealChain.toLinearExt
    rw [LinearExt.toLinearExt_toIdealChain]

end LinearExt

end OneThird
