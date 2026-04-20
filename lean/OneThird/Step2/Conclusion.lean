/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step2.PerFiber
import OneThird.Step2.WeakGrid
import OneThird.Step2.FiberAvg
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 2 — Conclusion (`thm:step2`)

This file formalises the statement of `thm:step2` of `step2.tex`
§"Output of Step 2 and downstream usage": the conclusion exported to
Steps 3–6 by the whole of Step 2.

## Statement (paper form)

Under the Step 1 interface data and the weak grid stability lemma,
taking as named external inputs the bounded edge-multiplicity constant
`K` (S1.6) and a rich-fiber family `R` (from Step 5) with total mass
`W ≥ c₅ · |L(P)|`, fix a threshold `η ∈ (0, 1)`. If
`S ⊆ L(P)` has BK conductance
`|∂_{BK} S| / min(|S|, |S^c|) ≤ κ` with `Kκ ≤ α · η · c₅`, then a
mass-fraction at least `1 − α` of the fibers are good, and on every
good fiber `(x, y)`:

1. `A_{x, y}` is `o(|fib_{x,y}|)`-close to a staircase `M_{x, y}`;
2. the staircase has a well-defined sign `σ_{x,y} ∈ {+, −}` (on
   non-degenerate fibers);
3. the error set `E_{x, y}` is measurable and propagates linearly
   into downstream overlap arguments (Steps 4, 6).

The sign `σ_{x,y}` of (2) is the object of `cor:sign` in
`step2.tex` (already stated as part of `WeakGrid.lean`'s
orientation-assignment section at the paper level). Items (1) and (3)
are the direct output of `PerFiber.per_fiber_staircase` via the `δ = 1`
trivial bound in `WeakGrid.weak_grid_exists`.

## Main result

* `step2_conclusion` — the combined statement at the abstract level:
  a bad-fiber mass bound (rearranged as a mass-fraction statement)
  together with a per-fiber staircase witness on every fiber.
-/

namespace OneThird
namespace Step2
namespace Conclusion

open Finset OneThird.Step2

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **`thm:step2` (Step 2 conclusion, abstract form).**

Given an abstract fiber family `R` with a bounded-multiplicity
structure `internal / K` and per-fiber grid data
`D, A : α → Finset (ℤ × ℤ)` with `A r ⊆ D r`, and a conductance
budget `|B| ≤ κ · m` where `m` is a proxy for `|S|` and `B` for
`∂_BK S`, the output of Step 2 consists of:

1. (Bad-fiber mass bound.) The total mass of fibers with per-fiber
   BK-internal count exceeding `η · fibMass` is at most `K · κ · m / η`.
2. (Per-fiber staircase.) For every fiber `r ∈ R`, there is a
   `+`-staircase `M_r ⊆ D r` with `|A r Δ M_r| ≤ |D r|` (the
   `δ = 1` form of `lem:weak-grid`).

The statement is a direct repackaging of
`PerFiber.per_fiber_staircase`. The `κ · m` bound enters as the
hypothesis `hBκ : B.card ≤ κ * m`, and the conclusion is then the
paper's `Σ_{bad} |fib| ≤ K · κ · m / η` in the cleared-denominators
form `η · Σ_{bad} fibMass ≤ K · κ · m`. -/
theorem step2_conclusion
    (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    {K : ℕ} (hK : FiberAvg.BoundedMultiplicity R B internal K)
    {η : ℕ} (hη : 0 < η)
    (D A : α → Finset (ℤ × ℤ))
    (hAD : ∀ r ∈ R, A r ⊆ D r)
    (fibMass : α → ℕ)
    {κ m : ℕ} (hBκ : B.card ≤ κ * m) :
    η * (∑ r ∈ PerFiber.badFiberSet R B internal η fibMass, fibMass r)
        ≤ K * κ * m ∧
    (∀ r ∈ R, ∃ M : Finset (ℤ × ℤ),
      WeakGrid.IsStaircasePlus (D r) M ∧
      (symmDiff (A r) M).card ≤ (D r).card) := by
  refine ⟨?_, PerFiber.exists_staircase_per_fiber R D A hAD⟩
  have h1 := PerFiber.badFiberSet_mass_bound R B internal hK hη fibMass
  have h2 : K * B.card ≤ K * (κ * m) := by gcongr
  calc η * (∑ r ∈ PerFiber.badFiberSet R B internal η fibMass, fibMass r)
      ≤ K * B.card := h1
    _ ≤ K * (κ * m) := h2
    _ = K * κ * m := by ring

/-- **`thm:step2` (mass-fraction form).** Under the additional
hypothesis that the total mass `W = Σ_{r ∈ R} fibMass r` is non-zero
and the product `K · κ · m` satisfies `K · κ · m ≤ α · η · W` for
some `α`, the bad fibers occupy at most an `α`-fraction of the total
mass:

`Σ_{bad} fibMass ≤ α · W`.

This is the precise (1 − α)-good-mass-fraction statement of
`thm:step2`. -/
theorem step2_conclusion_mass_fraction
    (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    {K : ℕ} (hK : FiberAvg.BoundedMultiplicity R B internal K)
    {η : ℕ} (hη : 0 < η)
    (D A : α → Finset (ℤ × ℤ))
    (hAD : ∀ r ∈ R, A r ⊆ D r)
    (fibMass : α → ℕ)
    {κ m α_num : ℕ} (hBκ : B.card ≤ κ * m)
    (hακ : K * κ * m ≤ α_num * (η * (∑ r ∈ R, fibMass r))) :
    η * (∑ r ∈ PerFiber.badFiberSet R B internal η fibMass, fibMass r)
      ≤ α_num * (η * (∑ r ∈ R, fibMass r)) ∧
    (∀ r ∈ R, ∃ M : Finset (ℤ × ℤ),
      WeakGrid.IsStaircasePlus (D r) M ∧
      (symmDiff (A r) M).card ≤ (D r).card) := by
  obtain ⟨hbad, hstair⟩ :=
    step2_conclusion R B internal hK hη D A hAD fibMass hBκ
  exact ⟨hbad.trans hακ, hstair⟩

/-- **Good fibers cover complement of bad fibers.** Together with
`PerFiber.good_union_bad` and `PerFiber.good_bad_disjoint`, this is
the partition statement consumed by downstream steps. -/
theorem goodFiberSet_card_add_badFiberSet_card
    (R : Finset α) (B : Finset β)
    (internal : α → β → Prop) [DecidableRel internal]
    (η : ℕ) (fibMass : α → ℕ) :
    (PerFiber.goodFiberSet R B internal η fibMass).card +
      (PerFiber.badFiberSet R B internal η fibMass).card = R.card := by
  rw [← Finset.card_union_of_disjoint
        (PerFiber.good_bad_disjoint R B internal η fibMass),
      PerFiber.good_union_bad]

end Conclusion
end Step2
end OneThird
