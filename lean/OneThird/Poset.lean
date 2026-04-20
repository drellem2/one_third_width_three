/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic

/-!
# Finite posets: width, antichains, common neighbors

Minimal scaffolding for finite posets, width, common-neighbor sets,
and the width-3 common-neighbor-chain lemma (proved in
`OneThird/Step1/CommonChain.lean`).
-/

namespace OneThird

variable {α : Type*} [PartialOrder α]

/-- A poset has *width at most* `k` if every antichain has at most
`k` elements. -/
def HasWidthAtMost (α : Type*) [PartialOrder α] (k : ℕ) : Prop :=
  ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ k

/-- A poset `P = (α, ≤)` is a *chain* (total order) iff every two
elements are comparable. -/
def IsChainPoset (α : Type*) [PartialOrder α] : Prop :=
  ∀ x y : α, x ≤ y ∨ y ≤ x

/-- A poset has *width* equal to `k` if every antichain has size `≤ k`
and some antichain has size exactly `k`. -/
def HasWidth (α : Type*) [PartialOrder α] (k : ℕ) : Prop :=
  HasWidthAtMost α k ∧
    ∃ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) ∧ s.card = k

/-- Common-neighbor set of an incomparable pair: elements incomparable
to both `x` and `y`. Corresponds to `N(x, y)` in the paper. -/
def commonNbhd (x y : α) : Set α :=
  {z | (z ∥ x) ∧ (z ∥ y)}

/-- Common-neighbor set as a `Finset`. -/
noncomputable def commonNbhdFinset [Fintype α] (x y : α) : Finset α := by
  classical
  exact (Finset.univ : Finset α).filter (fun z => (z ∥ x) ∧ (z ∥ y))

/-- Length of the common-neighbor chain for a pair `(x, y)`.
In the paper, `t(x, y)`. -/
noncomputable def commonNbhdLength [Fintype α] (x y : α) : ℕ :=
  (commonNbhdFinset x y).card

/-- A pair `(x, y)` is *rich* at threshold `T` if it is incomparable
and its common-neighbor chain has length at least `T`
(Definition `def:rich`, `step1.tex`). -/
def IsRich [Fintype α] (T : ℕ) (x y : α) : Prop :=
  (x ∥ y) ∧ T ≤ commonNbhdLength x y

/-- The set of rich pairs at threshold `T`. -/
def richPairs (α : Type*) [PartialOrder α] [Fintype α] (T : ℕ) :
    Set (α × α) :=
  {p | IsRich T p.1 p.2}

end OneThird
