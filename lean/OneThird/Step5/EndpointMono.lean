/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Linarith

/-!
# Step 5 — Endpoint monotonicity (`lem:endpoint-mono`, `lem:interval-form`)

Formalises §5 G1 of `step5.tex`:

* `lem:interval-form` (`step5.tex:35`) — for any preorder `α`, any
  external element `x : α`, and any three elements `c₁ ≤ c₂ ≤ c₃` in
  `α`, if `c₁ ∥ x` and `c₃ ∥ x`, then `c₂ ∥ x`. Applied to a chain
  `C ⊆ α`, this shows the incomparability set
  `IC(x) := {c ∈ C : c ∥ x}` is order-convex inside `C`. The proof
  uses only transitivity of `≤`, not the `IsChain` hypothesis.

* `lem:endpoint-mono` (`step5.tex:257`) — exact monotonicity of the
  endpoint functions `α_i, β_i` on a Dilworth chain. Here `α_i` is the
  number of chain elements strictly below `a_i` and `β_i` is
  `|C| − |{c : a_i < c}|`, i.e. the position of the right endpoint of
  the incomparability interval. Both are weakly increasing in the
  poset order: if `x ≤ y`, then `alphaIdx C x ≤ alphaIdx C y` and
  `betaIdx C x ≤ betaIdx C y`.

  The paper's additive-error constant `E₁(T) = 0` and discard count
  `D₁(T) = 0` (`step5.tex:351-356`) are witnessed by the exact,
  unconditional monotonicity proved here.
-/

namespace OneThird
namespace Step5

open Finset

/-! ### `lem:interval-form` (`step5.tex:35`) -/

section IntervalForm

variable {α : Type*} [Preorder α]

/-- **`lem:interval-form` (core content, `step5.tex:40-43`).**

For any preorder `α`, any external element `x : α`, and any three
elements `c₁ ≤ c₂ ≤ c₃` in `α`: if both `c₁` and `c₃` are incomparable
to `x`, then so is `c₂`.

Applied with `c₁, c₂, c₃` running through a chain `C`, this shows the
incomparability set `IC(x) = {c ∈ C : c ∥ x}` is an interval
(order-convex) inside `C`. The proof uses only transitivity of `≤`; no
`IsChain` hypothesis is required.

Proof (`step5.tex:41-43`): if `c₂` were comparable to `x`, either
`c₂ ≤ x` (so `c₁ ≤ c₂ ≤ x`, contradicting `c₁ ∥ x`) or `x ≤ c₂` (so
`x ≤ c₂ ≤ c₃`, contradicting `c₃ ∥ x`). -/
theorem interval_form
    {c₁ c₂ c₃ x : α} (h12 : c₁ ≤ c₂) (h23 : c₂ ≤ c₃)
    (h1x : c₁ ∥ x) (h3x : c₃ ∥ x) : c₂ ∥ x :=
  ⟨fun hc2x => h1x.1 (h12.trans hc2x),
   fun hxc2 => h3x.2 (hxc2.trans h23)⟩

/-- **`lem:interval-form` (subset form).**

For a chain `C : Set α`, the incomparability set `{c ∈ C : c ∥ x}` is
closed under "betweenness" in the ambient order: if `c₁, c₃ ∈ C` are
incomparable to `x` and `c₂ ∈ C` satisfies `c₁ ≤ c₂ ≤ c₃`, then
`c₂ ∥ x`. -/
theorem interval_form_mem {C : Set α} (x : α)
    {c₁ c₂ c₃ : α} (_ : c₁ ∈ C) (_ : c₂ ∈ C) (_ : c₃ ∈ C)
    (h12 : c₁ ≤ c₂) (h23 : c₂ ≤ c₃)
    (h1x : c₁ ∥ x) (h3x : c₃ ∥ x) : c₂ ∥ x :=
  interval_form h12 h23 h1x h3x

end IntervalForm

/-! ### `lem:endpoint-mono` — underlying lower/upper-set facts -/

section EndpointMono

variable {α : Type*} [Preorder α]

/-- **Lower-set monotonicity.** If `x ≤ y` in `α`, the strict lower set
of `x` is contained in the strict lower set of `y`. Underlies the
inclusion `L_C(x) ⊆ L_C(y)` of `step5.tex:309-312`. -/
theorem lowerSet_subset_of_le {x y : α} (hxy : x ≤ y) :
    {c : α | c < x} ⊆ {c : α | c < y} := fun _ hc => lt_of_lt_of_le hc hxy

/-- **Upper-set antitone.** If `x ≤ y` in `α`, the strict upper set of
`y` is contained in the strict upper set of `x`. Underlies the
inclusion `U_C(y) ⊆ U_C(x)` of `step5.tex:317-320`. -/
theorem upperSet_subset_of_le {x y : α} (hxy : x ≤ y) :
    {c : α | y < c} ⊆ {c : α | x < c} := fun _ hc => lt_of_le_of_lt hxy hc

/-! ### Endpoint indices and their monotonicity -/

open Classical in
/-- The **α-index** of `x` on the chain `C`: the number of chain
elements strictly below `x`, i.e.\ `|L_C(x) ∩ C|`. In the 1-indexed
notation of `step5.tex:266` with `C = {c_1 < … < c_r}` and
`IC(x) = [α_i, β_i] ≠ ∅`, this equals `α_i − 1`. -/
noncomputable def alphaIdx (C : Finset α) (x : α) : ℕ :=
  (C.filter (· < x)).card

open Classical in
/-- The **β-index** of `x` on the chain `C`: `|C| − |U_C(x) ∩ C|`,
i.e.\ the number of chain elements not strictly above `x`. In the
1-indexed notation of `step5.tex:266`, equals `β_i` when `IC(x) ≠ ∅`. -/
noncomputable def betaIdx (C : Finset α) (x : α) : ℕ :=
  C.card - (C.filter (fun c => x < c)).card

/-- **`lem:endpoint-mono`, α-half.** On a fixed subset `C`, the
α-index is non-decreasing in the poset order. Corresponds to
"Monotonicity of α" in `step5.tex:307-312`. -/
theorem alphaIdx_mono_of_le
    (C : Finset α) {x y : α} (hxy : x ≤ y) :
    alphaIdx C x ≤ alphaIdx C y := by
  classical
  unfold alphaIdx
  apply Finset.card_le_card
  intro c hc
  rw [mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 hxy⟩

/-- **`lem:endpoint-mono`, β-half.** On a fixed subset `C`, the
β-index is non-decreasing in the poset order. Corresponds to
"Monotonicity of β" in `step5.tex:316-320`. -/
theorem betaIdx_mono_of_le
    (C : Finset α) {x y : α} (hxy : x ≤ y) :
    betaIdx C x ≤ betaIdx C y := by
  classical
  unfold betaIdx
  have hU : (C.filter (fun c => y < c)).card ≤
      (C.filter (fun c => x < c)).card := by
    apply Finset.card_le_card
    intro c hc
    rw [mem_filter] at hc ⊢
    exact ⟨hc.1, lt_of_le_of_lt hxy hc.2⟩
  have hUx : (C.filter (fun c => x < c)).card ≤ C.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hUy : (C.filter (fun c => y < c)).card ≤ C.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- **`lem:endpoint-mono` (packaged).** For any subset `C : Finset α`
and elements `x ≤ y` in `α`, both endpoint indices are weakly
increasing: `alphaIdx C x ≤ alphaIdx C y` and
`betaIdx C x ≤ betaIdx C y`.

This witnesses the paper's full `lem:endpoint-mono` with discard
count `D₁(T) = 0` and additive error `E₁(T) = 0` (`step5.tex:268-273`,
`step5.tex:351-356`). -/
theorem endpoint_mono
    (C : Finset α) {x y : α} (hxy : x ≤ y) :
    alphaIdx C x ≤ alphaIdx C y ∧ betaIdx C x ≤ betaIdx C y :=
  ⟨alphaIdx_mono_of_le C hxy, betaIdx_mono_of_le C hxy⟩

end EndpointMono

end Step5
end OneThird
