/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Mathlib.LinearExtension.Subtype
import OneThird.Step8.LayeredReduction

/-!
# Step 8 — Layer-ordinal-sum reducibility (F1 foundation)

Formalises the paper's *layer-ordinal reducible* predicate and the
data required by downstream Step 8 items (F2–F5 of `sec:g4-balanced-pair`).

## Main definitions

* `Step8.LayerOrdinalReducible L k` — the predicate at
  `step8.tex:1612-1618`: a layered poset `Q` is *layer-ordinal reducible
  at band index `k`* if every cross-pair `(u, v)` with `L.band u ≤ k`
  and `k < L.band v` satisfies `u <_Q v`. Equivalently,
  `Q = (M_1 ∪ ⋯ ∪ M_k) ⊕ (M_{k+1} ∪ ⋯ ∪ M_r)` as posets.

* `Step8.OrdinalDecompOfReducible L k h` — the *witness constructor*:
  from a reducibility hypothesis `h`, package the band-split
  `Q_1 := L_{≤k}`, `Q_2 := L_{>k}` as an `OrdinalDecomp α` with empty
  middle piece.

* `Step8.linExtEquivOfReducible` — the *factorisation transfer*
  `LinearExt α ≃ LinearExt ↥Q_1 × LinearExt ↥Q_2` as a `Fintype`
  bijection. Lean version of the paper's `L(Q) ≃ L(Q_1) × L(Q_2)`
  (`step8.tex:1619-1621`), derived from
  `OrdinalDecomp.tripleEquiv` by stripping the trivial middle factor.

* `Step8.numLinExt_factorOfReducible` — the counting corollary:
  `numLinExt α = numLinExt ↥Q_1 * numLinExt ↥Q_2`.

## Reference

`step8.tex` §`sec:g4-balanced-pair` (`step8.tex:1612-1625`), paper
Definition *layer-ordinal-sum reducible* added in A1 (mg-17e1).
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

namespace Step8

/-! ### §1 — The predicate -/

/-- **Layer-ordinal reducible** (`step8.tex:1612-1618`).

A layered poset `Q = M_1 ⊔ ⋯ ⊔ M_r` (presented here as a
`LayeredDecomposition α`) is *layer-ordinal reducible at index `k`*
if every cross-pair `(u, v)` with `u ∈ M_i, v ∈ M_j`, `i ≤ k < j`,
satisfies `u <_Q v`. Equivalently,
`Q = (M_1 ∪ ⋯ ∪ M_k) ⊕ (M_{k+1} ∪ ⋯ ∪ M_r)` as posets.

In the `LayeredDecomposition` representation, `i ≤ k < j` reads as
`L.band u ≤ k` and `k < L.band v`. -/
def LayerOrdinalReducible (L : LayeredDecomposition α) (k : ℕ) : Prop :=
  ∀ u v : α, L.band u ≤ k → k < L.band v → u < v

/-! ### §2 — `OrdinalDecomp α` from a reducibility witness -/

/-- **Reducibility witness → `OrdinalDecomp α`**
(paper `Q = Q_1 ⊕ Q_2` factorisation, `step8.tex:1614-1618`).

From a `LayerOrdinalReducible L k` witness, package the two
band-split pieces
* `Q_1 := {z : α | L.band z ≤ k}` (the `Lower` part),
* `Q_2 := {z : α | k < L.band z}` (the `Upper` part),

as an `OrdinalDecomp α` whose middle piece is empty. The
reducibility hypothesis discharges the `Lower < Upper` element-wise
comparability field; the band-trichotomy on `L.band z` discharges
cover and disjointness. -/
def OrdinalDecompOfReducible (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) : OrdinalDecomp α where
  Lower := (Finset.univ : Finset α).filter (fun z => L.band z ≤ k)
  Mid := ∅
  Upper := (Finset.univ : Finset α).filter (fun z => k < L.band z)
  hCover := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      Finset.notMem_empty, true_and, or_false, iff_true]
    omega
  hDisjLM := Finset.disjoint_empty_right _
  hDisjLU := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    omega
  hDisjMU := Finset.disjoint_empty_left _
  hLM_lt := fun _ _ _ hyM => absurd hyM (Finset.notMem_empty _)
  hLU_lt := by
    intro u hu v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact h u v hu hv
  hMU_lt := fun _ hx _ _ => absurd hx (Finset.notMem_empty _)

/-- Convenience: under `OrdinalDecompOfReducible`, the middle piece is
`∅` by definition. -/
@[simp]
lemma OrdinalDecompOfReducible_Mid (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) :
    (OrdinalDecompOfReducible L k h).Mid = (∅ : Finset α) := rfl

/-- Membership in the `Lower` (= `Q_1`) piece. -/
@[simp]
lemma mem_OrdinalDecompOfReducible_Lower (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) (z : α) :
    z ∈ (OrdinalDecompOfReducible L k h).Lower ↔ L.band z ≤ k := by
  simp only [OrdinalDecompOfReducible, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Membership in the `Upper` (= `Q_2`) piece. -/
@[simp]
lemma mem_OrdinalDecompOfReducible_Upper (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) (z : α) :
    z ∈ (OrdinalDecompOfReducible L k h).Upper ↔ k < L.band z := by
  simp only [OrdinalDecompOfReducible, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-! ### §3 — Factorisation transfer `L(Q) ≃ L(Q_1) × L(Q_2)` -/

/-- **Factorisation transfer `L(Q) ≃ L(Q_1) × L(Q_2)`**
(`step8.tex:1619-1621`).

The `Fintype`-bijection Lean version of the paper's
`L(Q) = L(Q_1) × L(Q_2)` identity for a layer-ordinal reducible
layered poset `Q`. Built from `OrdinalDecomp.tripleEquiv` by
stripping the trivial middle factor (the unique linear extension
of the empty sub-poset).

The forward direction sends a linear extension `L` of `α` to the
pair of restrictions `(L|_{Q_1}, L|_{Q_2})`; the backward direction
concatenates two linear extensions via `OrdinalDecomp.concat`, using
any fixed linear extension of the empty middle piece (which is
unique up to equality, so well-defined). -/
noncomputable def linExtEquivOfReducible
    (L : LayeredDecomposition α) (k : ℕ) (h : LayerOrdinalReducible L k) :
    LinearExt α ≃
      LinearExt ↥(OrdinalDecompOfReducible L k h).Lower ×
        LinearExt ↥(OrdinalDecompOfReducible L k h).Upper := by
  classical
  set D := OrdinalDecompOfReducible L k h with hD_def
  -- The middle piece `D.Mid` is `∅`, so `LinearExt ↥D.Mid` is a
  -- subsingleton (unique up to equality, by vacuous extensionality on
  -- the empty subtype). Use `szpilrajn` to pick a canonical element,
  -- and `concat_restrict` to identify it with the restriction of any
  -- given linear extension.
  have hMid_sub : Subsingleton (LinearExt ↥D.Mid) := by
    refine ⟨fun a b => ?_⟩
    apply LinearExt.ext
    apply Equiv.ext
    intro x
    -- `x : ↥D.Mid = ↥∅`; its membership property is `x.val ∈ ∅`, absurd.
    exact absurd x.property (Finset.notMem_empty _)
  let eMid : LinearExt ↥D.Mid := LinearExt.szpilrajn _
  refine
    { toFun := fun Lext => ⟨D.restrictLower Lext, D.restrictUpper Lext⟩
      invFun := fun p => D.concat p.1 eMid p.2
      left_inv := ?_
      right_inv := ?_ }
  · -- left_inv: `concat (restrictLower L) eMid (restrictUpper L) = L`.
    -- Use `concat_restrict` after identifying `eMid` with
    -- `restrictMid L` via the subsingleton.
    intro Lext
    have heq : eMid = D.restrictMid Lext := @Subsingleton.elim _ hMid_sub _ _
    rw [heq]
    exact D.concat_restrict Lext
  · -- right_inv: restricting the `concat` recovers the original pair.
    intro p
    rcases p with ⟨LL, LU⟩
    simp only [Prod.mk.injEq]
    exact ⟨D.restrictLower_concat LL eMid LU,
           D.restrictUpper_concat LL eMid LU⟩

/-- **Counting factorisation** (`step8.tex:1619-1621`, corollary).

The number of linear extensions of `α` factors as the product of
the counts on the two pieces `Q_1` and `Q_2` of a layer-ordinal
reducible decomposition. -/
theorem numLinExt_factorOfReducible
    (L : LayeredDecomposition α) (k : ℕ) (h : LayerOrdinalReducible L k) :
    numLinExt α =
      numLinExt ↥(OrdinalDecompOfReducible L k h).Lower *
        numLinExt ↥(OrdinalDecompOfReducible L k h).Upper := by
  unfold numLinExt
  rw [Fintype.card_congr (linExtEquivOfReducible L k h), Fintype.card_prod]

end Step8
end OneThird
