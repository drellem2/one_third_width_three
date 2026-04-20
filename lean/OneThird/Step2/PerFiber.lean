/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step2.FiberAvg
import OneThird.Step2.WeakGrid
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 2 — Per-fiber staircase approximation (`prop:per-fiber`)

This file formalises the second main product of Step 2
(`step2.tex` Proposition `prop:per-fiber`): combining the weak grid
stability lemma (`OneThird.Step2.WeakGrid.weak_grid_exists`) with the
fiber boundary averaging tail bound
(`OneThird.Step2.FiberAvg.fiber_avg_tail_weight`) yields a per-fiber
staircase approximation on a mass-fraction `(1 − o(1))` of the rich
good fibers.

## Abstract form

The statement is split into two independent pieces — a tail bound and
a per-fiber staircase witness — each abstracted over the ambient data:

* a finite collection `R : Finset α` of fibers;
* a finite collection `B : Finset β` of BK-edges, with a decidable
  "edge-is-internal-to-fiber" relation `internal : α → β → Prop` and
  bounded multiplicity `K` (the Step 1 (S1.6) output);
* a per-fiber domain `D : α → Finset (ℤ × ℤ)` and subset
  `A : α → Finset (ℤ × ℤ)` with `A r ⊆ D r` (the local-coordinate
  image of `S ∩ fib_r`, obtained via (S1.4));
* a mass function `fibMass : α → ℕ` with `(D r).card = fibMass r`
  (which holds because the local coordinate `π_{x,y}` is a bijection
  `fib_{x,y} → D_{x,y}`).

The two conclusions are then:

* **Bad-fiber mass bound.** `FiberAvg.fiber_avg_tail_weight` gives
  `η · Σ_{bad r} fibMass r ≤ K · |B|`, which after the standard
  `|B| ≤ κ|S|` substitution becomes the paper's
  `Σ_{bad} |fib| ≤ Kκ|S|/η`.

* **Per-fiber staircase witness.** `WeakGrid.weak_grid_exists` gives,
  for every `r ∈ R`, a monotone staircase `M_r` inside `D r` with
  `|A r Δ M_r| ≤ |D r|`. This is the trivially-correct `δ = 1` form
  of `lem:weak-grid`; the paper's `δ(ε) = O(ε^{1/3})` form is the
  subject of follow-up quantitative work.

## Main result

* `per_fiber_staircase` — the combined statement: the tail inequality
  on bad fibers together with a per-fiber staircase witness for every
  fiber in `R`.

Downstream, Step 2's conclusion (`thm:step2` in `Conclusion.lean`)
repackages this into the form consumed by Steps 3–6.
-/

namespace OneThird
namespace Step2
namespace PerFiber

open Finset OneThird.Step2

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The **bad-fiber set** at threshold `η` and mass function
`fibMass`: the fibers `r ∈ R` whose per-fiber BK-internal count
exceeds `η · fibMass r`. Paper symbol: `R ∖ G`. -/
def badFiberSet (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) : Finset α :=
  R.filter (fun r => η * fibMass r < FiberAvg.internalCount B internal r)

/-- The **good-fiber set** at threshold `η` and mass function
`fibMass`: the fibers `r ∈ R` whose per-fiber BK-internal count is
at most `η · fibMass r`. Paper symbol: `G`. -/
def goodFiberSet (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) : Finset α :=
  R.filter (fun r => FiberAvg.internalCount B internal r ≤ η * fibMass r)

lemma badFiberSet_subset (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) :
    badFiberSet R B internal η fibMass ⊆ R := by
  intro r hr
  exact (mem_filter.mp hr).1

lemma goodFiberSet_subset (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) :
    goodFiberSet R B internal η fibMass ⊆ R := by
  intro r hr
  exact (mem_filter.mp hr).1

lemma mem_badFiberSet {R : Finset α} {B : Finset β}
    {internal : α → β → Prop} [DecidableRel internal]
    {η : ℕ} {fibMass : α → ℕ} {r : α} :
    r ∈ badFiberSet R B internal η fibMass ↔
      r ∈ R ∧ η * fibMass r < FiberAvg.internalCount B internal r := by
  unfold badFiberSet; rw [mem_filter]

lemma mem_goodFiberSet {R : Finset α} {B : Finset β}
    {internal : α → β → Prop} [DecidableRel internal]
    {η : ℕ} {fibMass : α → ℕ} {r : α} :
    r ∈ goodFiberSet R B internal η fibMass ↔
      r ∈ R ∧ FiberAvg.internalCount B internal r ≤ η * fibMass r := by
  unfold goodFiberSet; rw [mem_filter]

lemma good_bad_disjoint (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) :
    Disjoint (goodFiberSet R B internal η fibMass)
             (badFiberSet R B internal η fibMass) := by
  rw [Finset.disjoint_left]
  intro r hg hb
  rw [mem_goodFiberSet] at hg
  rw [mem_badFiberSet] at hb
  omega

lemma good_union_bad (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) :
    goodFiberSet R B internal η fibMass ∪
      badFiberSet R B internal η fibMass = R := by
  ext r
  simp only [mem_union, mem_goodFiberSet, mem_badFiberSet]
  constructor
  · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
  · intro hr
    by_cases h : FiberAvg.internalCount B internal r ≤ η * fibMass r
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr ⟨hr, by omega⟩

/-- **Bad-fiber mass bound** (part (i) of `prop:per-fiber`). Under
the bounded-multiplicity hypothesis from Step 1 (S1.6), the total
mass of bad fibers is bounded by `K · |B| / η`. Substituting the
global conductance bound `|B| ≤ κ · |S|` recovers the paper's
`Σ_{bad} |fib| ≤ Kκ|S|/η`. -/
theorem badFiberSet_mass_bound
    (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    {K : ℕ} (hK : FiberAvg.BoundedMultiplicity R B internal K)
    {η : ℕ} (hη : 0 < η)
    (fibMass : α → ℕ) :
    η * (∑ r ∈ badFiberSet R B internal η fibMass, fibMass r) ≤ K * B.card := by
  refine FiberAvg.fiber_avg_tail_weight R B internal hη fibMass hK
    (badFiberSet R B internal η fibMass)
    (badFiberSet_subset R B internal η fibMass) ?_
  intro r hr
  rw [mem_badFiberSet] at hr
  exact le_of_lt hr.2

/-- **Per-fiber staircase witness** (part (ii) of `prop:per-fiber`,
in the trivially-correct `δ = 1` form supplied by
`WeakGrid.weak_grid_exists`). For every fiber `r ∈ R`, there is a
`+`-staircase `M_r ⊆ D r` with `|A r Δ M_r| ≤ |D r|`. The
quantitative `δ = O(ε^{1/3})` form is the content of follow-up work;
the statement here is the interface downstream files consume. -/
theorem exists_staircase_per_fiber
    (R : Finset α)
    (D A : α → Finset (ℤ × ℤ))
    (hAD : ∀ r ∈ R, A r ⊆ D r) :
    ∀ r ∈ R, ∃ M : Finset (ℤ × ℤ),
      WeakGrid.IsStaircasePlus (D r) M ∧
      (symmDiff (A r) M).card ≤ (D r).card := by
  intro r hr
  exact WeakGrid.weak_grid_exists (D r) (A r) (hAD r hr)

/-- **`prop:per-fiber` (combined form).** The per-fiber staircase
approximation theorem, combining the bad-fiber mass bound and the
per-fiber staircase witness. Consumed by `Conclusion.lean` to
produce `thm:step2`.

The statement packages the two parts:

* *(i) Bad-fiber mass bound.* `η · Σ_{bad} fibMass ≤ K · |B|`.
* *(ii) Per-fiber staircase.* For every `r ∈ R` there is a
  `+`-staircase `M_r ⊆ D r` with `|A r Δ M_r| ≤ |D r|`.
-/
theorem per_fiber_staircase
    (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    {K : ℕ} (hK : FiberAvg.BoundedMultiplicity R B internal K)
    {η : ℕ} (hη : 0 < η)
    (D A : α → Finset (ℤ × ℤ))
    (hAD : ∀ r ∈ R, A r ⊆ D r)
    (fibMass : α → ℕ) :
    η * (∑ r ∈ badFiberSet R B internal η fibMass, fibMass r) ≤ K * B.card ∧
    (∀ r ∈ R, ∃ M : Finset (ℤ × ℤ),
      WeakGrid.IsStaircasePlus (D r) M ∧
      (symmDiff (A r) M).card ≤ (D r).card) :=
  ⟨badFiberSet_mass_bound R B internal hK hη fibMass,
   exists_staircase_per_fiber R D A hAD⟩

end PerFiber
end Step2
end OneThird
