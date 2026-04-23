/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.OneElemPerturb
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Exceptional-set perturbation bound (F6b, `lem:exc-perturb`)

Iteration of F6a (`lem:one-elem-perturb`). For a finite poset `α` with
`|α| = n`, a `Finset S ⊆ α` with `k := S.card` and `n - k ≥ 2`, and
`x, y ∉ S`:
```
  |probLT x y − probLT (⟨x⟩ : {a // a ∉ S}) ⟨y⟩|  ≤  2k / (n − k + 1).
```

## Strategy

* **§1** — `probLT_orderIso` transports the probability along an order
  isomorphism of posets, via the induced bijection `LinearExt α ≃ LinearExt β`.
* **§2** — `nestedFlatOrderIso` exhibits the order iso
  `{a : α // a ∉ insert z S}  ≃o  {b : {a // a ∉ S} // b ≠ ⟨z, _⟩}`
  between the "flat" and "nested" deletions.
* **§3** — **Main theorem.** Induct on `S`: the base case `S = ∅` is
  `probLT_orderIso` applied to `α ≃o {a : α // a ∉ ∅}`; the step
  `S → insert z S` combines the IH with `one_elem_perturb` applied on
  the ambient subtype `{a : α // a ∉ S}`, transported via
  `nestedFlatOrderIso`.

## Reference

`step8.tex:1025-1062`.
-/

namespace OneThird
namespace LinearExt

open Finset

/-! ### §1 — `probLT` transport along an order isomorphism -/

section OrderIsoTransport
variable {α β : Type*}
  [PartialOrder α] [Fintype α] [DecidableEq α]
  [PartialOrder β] [Fintype β] [DecidableEq β]

/-- Transport a linear extension of `α` to a linear extension of `β`
along an order isomorphism `e : α ≃o β`. -/
noncomputable def ofOrderIso (e : α ≃o β) (L : LinearExt α) :
    LinearExt β :=
  let hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e.toEquiv
  { toFun := (e.symm.toEquiv.trans L.toFun).trans (finCongr hcard)
    monotone := by
      intro b₁ b₂ h
      have h1 : e.symm b₁ ≤ e.symm b₂ := e.symm.monotone h
      have h2 : L.toFun (e.symm b₁) ≤ L.toFun (e.symm b₂) := L.monotone h1
      show (finCongr hcard) (L.toFun (e.symm b₁))
            ≤ (finCongr hcard) (L.toFun (e.symm b₂))
      rw [finCongr_apply, finCongr_apply, Fin.le_def]
      simp only [Fin.coe_cast]
      exact h2 }

@[simp] lemma ofOrderIso_pos_val (e : α ≃o β) (L : LinearExt α) (b : β) :
    ((L.ofOrderIso e).pos b).val = (L.pos (e.symm b)).val := by
  show ((L.ofOrderIso e).toFun b).val = _
  unfold ofOrderIso
  simp only [Equiv.trans_apply, finCongr_apply, Fin.coe_cast]
  rfl

lemma ofOrderIso_lt_iff (e : α ≃o β) (L : LinearExt α) (a a' : α) :
    (L.ofOrderIso e).lt (e a) (e a') ↔ L.lt a a' := by
  show ((L.ofOrderIso e).pos (e a)).val < ((L.ofOrderIso e).pos (e a')).val
    ↔ (L.pos a).val < (L.pos a').val
  rw [ofOrderIso_pos_val, ofOrderIso_pos_val, e.symm_apply_apply, e.symm_apply_apply]

/-- Round-trip identity: transporting twice (via `e` then `e.symm`)
recovers the original linear extension. -/
lemma ofOrderIso_symm_ofOrderIso (e : α ≃o β) (L : LinearExt α) :
    (L.ofOrderIso e).ofOrderIso e.symm = L := by
  apply LinearExt.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  show (((L.ofOrderIso e).ofOrderIso e.symm).pos a).val = (L.pos a).val
  rw [ofOrderIso_pos_val]
  show ((L.ofOrderIso e).pos (e.symm.symm a)).val = (L.pos a).val
  rw [show e.symm.symm = e from rfl, ofOrderIso_pos_val, e.symm_apply_apply]

lemma ofOrderIso_ofOrderIso_symm (e : α ≃o β) (M : LinearExt β) :
    (M.ofOrderIso e.symm).ofOrderIso e = M := by
  have := ofOrderIso_symm_ofOrderIso e.symm M
  rwa [show e.symm.symm = e from rfl] at this

/-- The `ofOrderIso` construction defines a bijection
`LinearExt α ≃ LinearExt β`. -/
noncomputable def linExtCongr (e : α ≃o β) : LinearExt α ≃ LinearExt β where
  toFun L := L.ofOrderIso e
  invFun M := M.ofOrderIso e.symm
  left_inv L := ofOrderIso_symm_ofOrderIso e L
  right_inv M := ofOrderIso_ofOrderIso_symm e M

/-- Transport of `lt` for an extension pulled back via `e.symm`. -/
lemma ofOrderIso_symm_lt_iff (e : α ≃o β) (M : LinearExt β) (a a' : α) :
    (M.ofOrderIso e.symm).lt a a' ↔ M.lt (e a) (e a') := by
  have := ofOrderIso_lt_iff e.symm M (e a) (e a')
  rwa [e.symm_apply_apply, e.symm_apply_apply] at this

/-- **Transport of `probLT` along an order iso.** -/
theorem probLT_orderIso (e : α ≃o β) (x y : α) :
    probLT x y = probLT (e x) (e y) := by
  classical
  unfold probLT
  have hnum : numLinExt α = numLinExt β := by
    unfold numLinExt
    exact Fintype.card_congr (linExtCongr e)
  have hfilter :
      (Finset.univ.filter (fun L : LinearExt α => L.lt x y)).card =
      (Finset.univ.filter (fun M : LinearExt β => M.lt (e x) (e y))).card := by
    refine Finset.card_bij
      (fun L _ => L.ofOrderIso e)
      (fun L hL => ?_)
      (fun L₁ _ L₂ _ h => ?_)
      (fun M hM => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
      exact (ofOrderIso_lt_iff e L x y).mpr hL
    · exact (linExtCongr e).injective h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      refine ⟨M.ofOrderIso e.symm, ?_, ofOrderIso_ofOrderIso_symm e M⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (ofOrderIso_symm_lt_iff e M x y).mpr hM
  rw [hfilter, hnum]

end OrderIsoTransport

/-! ### §2 — Nested-flat order iso for `insert z S` -/

section NestedFlat
variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **Nested–flat order iso.** The "flat" deletion subtype
`{a : α // a ∉ insert z S}` is order-isomorphic to the "nested" deletion
subtype `{b : {a : α // a ∉ S} // b ≠ ⟨z, hzS⟩}`. -/
def nestedFlatOrderIso {S : Finset α} {z : α} (hzS : z ∉ S) :
    {a : α // a ∉ insert z S} ≃o
      {b : {a : α // a ∉ S} // b ≠ ⟨z, hzS⟩} where
  toFun := fun x =>
    have hxS : x.val ∉ S := fun h => x.2 (Finset.mem_insert.mpr (Or.inr h))
    have hxne : x.val ≠ z := fun h =>
      x.2 (Finset.mem_insert.mpr (Or.inl h))
    ⟨⟨x.val, hxS⟩, fun hEq => hxne (Subtype.mk.inj hEq)⟩
  invFun := fun y =>
    have hne : y.val.val ≠ z := fun h => y.2 (Subtype.ext h)
    have hnS : y.val.val ∉ S := y.val.2
    ⟨y.val.val, fun hmem => by
      rcases Finset.mem_insert.mp hmem with heq | hS
      · exact hne heq
      · exact hnS hS⟩
  left_inv := fun x => rfl
  right_inv := fun y => by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_rel_iff' := Iff.rfl

end NestedFlat

/-! ### §3 — Main theorem: the exceptional-set perturbation bound -/

section ExcPerturb
variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **Empty-deletion order iso.** The subtype `{a : α // a ∉ ∅}` is
order-isomorphic to `α`. -/
def emptyDeletionOrderIso : α ≃o {a : α // a ∉ (∅ : Finset α)} where
  toFun := fun a => ⟨a, Finset.notMem_empty a⟩
  invFun := fun x => x.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_rel_iff' := Iff.rfl

/-- Arithmetic helper: for `k n : ℕ` with `k + 2 ≤ n`,
`2k / (n - k + 1) + 2 / (n - k) ≤ 2(k+1) / (n - k)` over `ℚ`. -/
lemma exc_step_arith (n k : ℕ) (hk : k + 2 ≤ n) :
    (2 * k / ((n : ℚ) - k + 1) + 2 / ((n : ℚ) - k)) ≤
      2 * (k + 1) / ((n : ℚ) - k) := by
  have hnk : (2 : ℚ) ≤ (n : ℚ) - k := by
    have : (k + 2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hk
    linarith
  have hnk_pos : 0 < (n : ℚ) - k := by linarith
  have hnk1_pos : 0 < (n : ℚ) - k + 1 := by linarith
  have hk_nn : 0 ≤ (k : ℚ) := by positivity
  -- 2k/(n-k+1) ≤ 2k/(n-k), because (n-k) ≤ (n-k+1).
  have h1 : 2 * (k : ℚ) / ((n : ℚ) - k + 1) ≤ 2 * (k : ℚ) / ((n : ℚ) - k) := by
    rw [div_le_div_iff₀ hnk1_pos hnk_pos]
    nlinarith
  -- 2k/(n-k) + 2/(n-k) = 2(k+1)/(n-k).
  have h2 : 2 * (k : ℚ) / ((n : ℚ) - k) + 2 / ((n : ℚ) - k) =
      2 * (k + 1) / ((n : ℚ) - k) := by
    field_simp
  linarith [h1, h2]

/-- **Exceptional-set perturbation bound — quantified form.**

Inner statement used for the induction on `S` in `exc_perturb`. -/
theorem exc_perturb_aux (S : Finset α) :
    S.card + 2 ≤ Fintype.card α →
    ∀ x y : {a : α // a ∉ S},
      |probLT x.val y.val - probLT x y| ≤
        2 * (S.card : ℚ) / (Fintype.card α - S.card + 1 : ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ x y
    -- Base case: |probLT x.val y.val - probLT x y| ≤ 0/(n+1) = 0.
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
    -- Use `probLT_orderIso` with emptyDeletionOrderIso.
    have hprob :
        probLT x.val y.val = probLT x y := by
      have := probLT_orderIso (emptyDeletionOrderIso (α := α)) x.val y.val
      -- (emptyDeletionOrderIso x.val) = ⟨x.val, _⟩ = x by Subtype.ext (since x.2 is trivial).
      have hx : (emptyDeletionOrderIso (α := α)) x.val = x := by
        apply Subtype.ext; rfl
      have hy : (emptyDeletionOrderIso (α := α)) y.val = y := by
        apply Subtype.ext; rfl
      rw [hx, hy] at this
      exact this
    rw [hprob, sub_self, abs_zero]
  | insert z0 S' hzS ih =>
    intro hcard x y
    -- hcard : (insert z0 S').card + 2 ≤ Fintype.card α
    -- ih : S'.card + 2 ≤ Fintype.card α →
    --       ∀ x y, |probLT x.val y.val - probLT x y| ≤ 2*k'/(n-k'+1)
    -- Goal: |probLT x.val y.val - probLT x y| ≤ 2*(k'+1)/(n-k'-1+1) = 2*(k'+1)/(n-k')
    have hcardS' : S'.card + 2 ≤ Fintype.card α := by
      rw [Finset.card_insert_of_notMem hzS] at hcard
      omega
    -- Define x̃, ỹ : {a : α // a ∉ S'} (via x.val ∉ S').
    have hxS' : x.val ∉ S' := fun h =>
      x.2 (Finset.mem_insert.mpr (Or.inr h))
    have hyS' : y.val ∉ S' := fun h =>
      y.2 (Finset.mem_insert.mpr (Or.inr h))
    let xmid : {a : α // a ∉ S'} := ⟨x.val, hxS'⟩
    let ymid : {a : α // a ∉ S'} := ⟨y.val, hyS'⟩
    -- IH bound on S': |probLT xmid.val ymid.val - probLT xmid ymid| ≤ 2*k'/(n-k'+1).
    have hIH := ih hcardS' xmid ymid
    -- Apply one_elem_perturb on β := {a // a ∉ S'} with zB := ⟨z0, hzS⟩.
    have hcardβ : Fintype.card {a : α // a ∉ S'} = Fintype.card α - S'.card := by
      rw [Fintype.card_subtype_compl (fun a : α => a ∈ S')]
      congr 1
      exact Fintype.card_coe S'
    have hcardβ_ge : 2 ≤ Fintype.card {a : α // a ∉ S'} := by
      rw [hcardβ]; omega
    let zB : {a : α // a ∉ S'} := ⟨z0, hzS⟩
    have hx_ne_z : xmid ≠ zB := by
      intro hEq
      have : x.val = z0 := congrArg Subtype.val hEq
      exact x.2 (Finset.mem_insert.mpr (Or.inl this))
    have hy_ne_z : ymid ≠ zB := by
      intro hEq
      have : y.val = z0 := congrArg Subtype.val hEq
      exact y.2 (Finset.mem_insert.mpr (Or.inl this))
    let xnested : {b : {a : α // a ∉ S'} // b ≠ zB} := ⟨xmid, hx_ne_z⟩
    let ynested : {b : {a : α // a ∉ S'} // b ≠ zB} := ⟨ymid, hy_ne_z⟩
    have h_one_elem : |probLT (xnested.val) (ynested.val) -
        probLT xnested ynested| ≤
        2 / (Fintype.card {a : α // a ∉ S'} : ℚ) :=
      one_elem_perturb (γ := {a : α // a ∉ S'}) zB hcardβ_ge xnested ynested
    -- Identify xnested.val = xmid and xnested.val.val = x.val (rfl).
    -- Translate probLT xnested ynested to probLT x y via nestedFlatOrderIso.
    have hNestFlat :
        probLT (α := {a : α // a ∉ insert z0 S'}) x y =
        probLT xnested ynested := by
      have hnest := probLT_orderIso (nestedFlatOrderIso (S := S') (z := z0) hzS) x y
      have hex : (nestedFlatOrderIso (S := S') (z := z0) hzS) x = xnested := by
        apply Subtype.ext; apply Subtype.ext; rfl
      have hey : (nestedFlatOrderIso (S := S') (z := z0) hzS) y = ynested := by
        apply Subtype.ext; apply Subtype.ext; rfl
      rw [hex, hey] at hnest
      exact hnest
    -- Triangle inequality:
    -- |probLT x.val y.val - probLT x y|
    --   ≤ |probLT x.val y.val - probLT xmid ymid|
    --       + |probLT xmid ymid - probLT x y|
    have htri :
        |probLT x.val y.val - probLT x y| ≤
          |probLT x.val y.val - probLT xmid ymid| +
            |probLT xmid ymid - probLT x y| := by
      have := abs_sub_le (probLT x.val y.val) (probLT xmid ymid) (probLT x y)
      exact this
    -- Step bound (second term of triangle): via one-elem and nestedFlat.
    have hstep :
        |probLT xmid ymid - probLT x y| ≤
          2 / ((Fintype.card α : ℚ) - S'.card) := by
      rw [hNestFlat]
      have h1 : |probLT (xnested.val) (ynested.val) -
          probLT xnested ynested| ≤
          2 / (Fintype.card {a : α // a ∉ S'} : ℚ) := h_one_elem
      rw [hcardβ] at h1
      have hnk_eq : ((Fintype.card α - S'.card : ℕ) : ℚ) =
          (Fintype.card α : ℚ) - (S'.card : ℚ) := by
        have hle : S'.card ≤ Fintype.card α := by omega
        rw [Nat.cast_sub hle]
      rw [hnk_eq] at h1
      -- xnested.val = xmid, ynested.val = ymid (rfl)
      exact h1
    -- Combine via arithmetic.
    have hk_final : (insert z0 S').card = S'.card + 1 := by
      rw [Finset.card_insert_of_notMem hzS]
    rw [hk_final]
    push_cast
    -- Goal: |probLT x.val y.val - probLT x y| ≤ 2 * (S'.card + 1) / (n - (S'.card + 1) + 1)
    --       = 2 * (S'.card + 1) / (n - S'.card).
    have hrhs_eq :
        2 * ((S'.card : ℚ) + 1) / ((Fintype.card α : ℚ) - ((S'.card : ℚ) + 1) + 1) =
        2 * ((S'.card : ℚ) + 1) / ((Fintype.card α : ℚ) - S'.card) := by
      congr 1; ring
    rw [hrhs_eq]
    -- Apply triangle + IH + step + arith.
    have harith :=
      exc_step_arith (Fintype.card α) S'.card (by omega)
    -- harith : 2*S'.card/(n - S'.card + 1) + 2/(n - S'.card) ≤ 2*(S'.card+1)/(n - S'.card)
    calc |probLT x.val y.val - probLT x y|
        ≤ |probLT x.val y.val - probLT xmid ymid| +
            |probLT xmid ymid - probLT x y| := htri
      _ ≤ 2 * (S'.card : ℚ) / (Fintype.card α - S'.card + 1 : ℚ) +
            2 / (Fintype.card α - S'.card : ℚ) := by
          gcongr
      _ ≤ 2 * ((S'.card : ℚ) + 1) / ((Fintype.card α : ℚ) - S'.card) := by
          have := harith
          push_cast at this ⊢
          linarith

/-- **Exceptional-set perturbation bound** (`lem:exc-perturb`,
`step8.tex:1025-1062`).

For a finite poset `α` on `n` elements, a `Finset S ⊆ α` of size `k`
with `n - k ≥ 2`, and two elements `x, y ∉ S`:
```
  |probLT x.val y.val − probLT x y|  ≤  2k / (n − k + 1).
```

Proof via `exc_perturb_aux` by induction on `S`; single step via
`one_elem_perturb` on the ambient subtype `{a : α // a ∉ S}`. -/
theorem exc_perturb (S : Finset α)
    (hcard : S.card + 2 ≤ Fintype.card α)
    (x y : {a : α // a ∉ S}) :
    |probLT x.val y.val - probLT x y| ≤
      2 * (S.card : ℚ) / (Fintype.card α - S.card + 1 : ℚ) :=
  exc_perturb_aux S hcard x y

end ExcPerturb

end LinearExt
end OneThird
