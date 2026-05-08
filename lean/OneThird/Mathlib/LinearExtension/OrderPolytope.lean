/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# Order polytope `O(α)`

The **order polytope** `O(α)` of a finite poset `α` is the set of
order-preserving maps `α → [0,1] ⊆ ℝ`, viewed as a subset of `α → ℝ`:

```
  O(α) = { f : α → ℝ | (∀ x, 0 ≤ f x ≤ 1) ∧ (∀ x ≤ y, f x ≤ f y) }.
```

This is the basic geometric object underlying the chamber-decomposition
arc (Path A, sub-α-C, EX-3 through EX-7) per
`docs/path-alpha-execution-arc/path-A-vs-path-B-fork-resolution.md`
(mg-163f, commit `9e6edcd`).

## Scope of this file (EX-3)

Per mg-163f §5.2, this file populates only the basic structural
properties of `OrderPolytope`:

* `OrderPolytope.convex` — `O(α)` is convex.
* `OrderPolytope.isClosed` — `O(α)` is closed in the product topology
  on `α → ℝ`.
* `OrderPolytope.isBounded` — `O(α)` is bornologically bounded in
  `α → ℝ`.
* `OrderPolytope.isCompact` — assuming `[Fintype α]`, `O(α)` is compact
  (closed subset of the compact cube `[0,1]^α`).
* `OrderPolytope.measurableSet` — assuming `[Fintype α]`, `O(α)` is
  Borel-measurable (finite intersection of measurable half-spaces).

The vertex characterisation `vertices(O(α)) = {1_I : I ∈ J(α)}`
(Stanley 1986), the chamber simplices `σ_L`, the chamber decomposition
`O(α) = ⋃ σ_L`, and the volume formula `Vol(O(α)) = e(α) / n!` are
intentionally **out of scope**; they are the EX-4 / EX-5 deliverables
per mg-163f §5.5.

## Implementation note

The fork-resolution doc mg-163f §5.3 sketched these properties as
`instance`s, but `Convex`, `IsClosed`, `IsCompact`, `Bornology.IsBounded`,
and `MeasurableSet` are all `Prop`-valued predicates on a fixed `Set`,
not type-class arguments. They are therefore stated as named theorems
(`OrderPolytope.convex`, etc.) rather than instances. Downstream
EX-4/EX-5 consumers can invoke them by name; no `instance` resolution
is needed.

## Hand-verified instance: discrete 3-antichain

For a discrete poset `α` (no nontrivial order relations beyond
reflexivity), the order-preserving condition is vacuously satisfied,
so `OrderPolytope α` collapses to the cube `[0,1]^α`. The lemma
`OrderPolytope.eq_cube_of_discrete` records this in full generality;
the canonical mg-163f §5 example `α = {a, b, c}` discrete 3-antichain
gives `O(α) = [0,1]^3` as an immediate consequence (see the `example`
on `Three` at the end of this file).

## References

* R. P. Stanley, *Two poset polytopes*, Discrete Comput. Geom.
  **1** (1986), 9–23. — original definition, vertex theorem, chamber
  decomposition, volume formula.
* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  (1999), §4. — drops headline (Daykin–Saks 1981) via the chamber
  decomposition + continuous FKG/AD on `[0,1]^n`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace OneThird
namespace LinearExt

open Set

variable {α : Type*}

/-- The **order polytope** of a poset `α`: the set of order-preserving
maps `α → [0,1] ⊆ ℝ`, viewed as a subset of `α → ℝ`.

```
  O(α) = { f : α → ℝ | (∀ x, 0 ≤ f x ≤ 1) ∧ (∀ x ≤ y, f x ≤ f y) }.
```
-/
def OrderPolytope (α : Type*) [PartialOrder α] : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, x ≤ y → f x ≤ f y) }

namespace OrderPolytope

variable [PartialOrder α]

/-- Membership in `OrderPolytope α` unfolds to the conjunction of the
pointwise unit-interval condition and the order-preserving condition. -/
lemma mem_iff {f : α → ℝ} :
    f ∈ OrderPolytope α ↔
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x y, x ≤ y → f x ≤ f y) :=
  Iff.rfl

/-- The order polytope is contained in the cube `[0,1]^α`. -/
lemma subset_cube :
    OrderPolytope α ⊆ Set.univ.pi (fun _ : α => Set.Icc (0 : ℝ) 1) :=
  fun _ hf x _ => hf.1 x

/-! ### §1 — Convexity -/

/-- The **order polytope is convex**.

A convex combination of two functions `f, g ∈ O(α)` lies in `O(α)`
because both defining conditions — pointwise membership in `[0,1]`
and order-preservation — are preserved under non-negative linear
combinations. -/
theorem convex : Convex ℝ (OrderPolytope α) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · -- Pointwise membership in `Icc 0 1`.
    have hfx : f x ∈ Set.Icc (0 : ℝ) 1 := hf.1 x
    have hgx : g x ∈ Set.Icc (0 : ℝ) 1 := hg.1 x
    rw [Set.mem_Icc] at hfx hgx
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · -- 0 ≤ a • f x + b • g x
      have h0 : 0 ≤ a * f x := mul_nonneg ha hfx.1
      have h1 : 0 ≤ b * g x := mul_nonneg hb hgx.1
      change 0 ≤ a • f x + b • g x
      simp only [smul_eq_mul]
      linarith
    · -- a • f x + b • g x ≤ 1
      have h0 : a * f x ≤ a * 1 := mul_le_mul_of_nonneg_left hfx.2 ha
      have h1 : b * g x ≤ b * 1 := mul_le_mul_of_nonneg_left hgx.2 hb
      change a • f x + b • g x ≤ 1
      simp only [smul_eq_mul]
      have : a * f x + b * g x ≤ a + b := by linarith
      linarith [hab]
  · -- Order-preservation under convex combination.
    have hfxy : f x ≤ f y := hf.2 x y hxy
    have hgxy : g x ≤ g y := hg.2 x y hxy
    change a • f x + b • g x ≤ a • f y + b • g y
    have h0 : a * f x ≤ a * f y := mul_le_mul_of_nonneg_left hfxy ha
    have h1 : b * g x ≤ b * g y := mul_le_mul_of_nonneg_left hgxy hb
    simp only [smul_eq_mul]
    linarith

/-! ### §2 — Closedness -/

/-- The **order polytope is closed** in the product topology on
`α → ℝ`.

It is the intersection of the closed sets
`{f | f x ∈ [0,1]}` (one for each `x : α`) and
`{f | f x ≤ f y}` (one for each pair `x ≤ y`); each is closed because
the evaluation `f ↦ f x` is continuous and `[0,1]`, `{f x ≤ f y}` are
preimages of closed sets in `ℝ`. -/
theorem isClosed : IsClosed (OrderPolytope α) := by
  -- Set up the two pieces of the intersection.
  have hA : IsClosed { f : α → ℝ | ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 } := by
    have heq :
        { f : α → ℝ | ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 } =
          ⋂ x, (fun f : α → ℝ => f x) ⁻¹' Set.Icc (0 : ℝ) 1 := by
      ext f
      simp [Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact isClosed_iInter
      fun x => isClosed_Icc.preimage (continuous_apply x)
  have hB : IsClosed { f : α → ℝ | ∀ x y, x ≤ y → f x ≤ f y } := by
    have heq :
        { f : α → ℝ | ∀ x y, x ≤ y → f x ≤ f y } =
          ⋂ x, ⋂ y, ⋂ _ : x ≤ y, { f : α → ℝ | f x ≤ f y } := by
      ext f; simp [Set.mem_iInter]
    rw [heq]
    refine isClosed_iInter fun x =>
      isClosed_iInter fun y => isClosed_iInter fun _ => ?_
    exact isClosed_le (continuous_apply x) (continuous_apply y)
  -- Combine the two pieces.
  have heq :
      OrderPolytope α =
        { f : α → ℝ | ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 } ∩
          { f : α → ℝ | ∀ x y, x ≤ y → f x ≤ f y } := by
    ext f; rfl
  rw [heq]
  exact hA.inter hB

/-! ### §3 — Boundedness -/

/-- The **order polytope is bornologically bounded** in `α → ℝ`.

It is contained in the cube `[0,1]^α`, which is bounded as a product
of the bounded sets `[0,1] ⊆ ℝ`. -/
theorem isBounded : Bornology.IsBounded (OrderPolytope α) :=
  (Bornology.IsBounded.pi (fun _ : α => Metric.isBounded_Icc (0 : ℝ) 1)).subset
    subset_cube

/-! ### §4 — Compactness (requires `[Fintype α]`) -/

/-- The **order polytope is compact** when `α` is finite.

Proof: `O(α)` is a closed subset of the compact cube `[0,1]^α`
(Tychonoff for finite products of compact intervals). Compactness of
a closed subset of a compact set is the standard
`IsCompact.of_isClosed_subset`. -/
theorem isCompact [Fintype α] : IsCompact (OrderPolytope α) :=
  (isCompact_univ_pi (fun _ : α => isCompact_Icc)).of_isClosed_subset
    isClosed subset_cube

/-! ### §5 — Measurability (requires `[Fintype α]`) -/

/-- The **order polytope is Borel-measurable** when `α` is finite.

It is a finite intersection of measurable half-spaces:
`{f | f x ∈ [0,1]}` (preimage of a measurable interval under the
measurable evaluation `f ↦ f x`) and `{f | f x ≤ f y}` (Borel measurable
in `ℝ` via `measurableSet_le`). -/
theorem measurableSet [Fintype α] : MeasurableSet (OrderPolytope α) := by
  haveI : Countable α := Finite.to_countable
  have hA : MeasurableSet { f : α → ℝ | ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 } := by
    have heq :
        { f : α → ℝ | ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 } =
          ⋂ x, (fun f : α → ℝ => f x) ⁻¹' Set.Icc (0 : ℝ) 1 := by
      ext f
      simp [Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact MeasurableSet.iInter
      (fun x => measurableSet_Icc.preimage (measurable_pi_apply x))
  have hB : MeasurableSet { f : α → ℝ | ∀ x y, x ≤ y → f x ≤ f y } := by
    have heq :
        { f : α → ℝ | ∀ x y, x ≤ y → f x ≤ f y } =
          ⋂ x, ⋂ y, ⋂ _ : x ≤ y, { f : α → ℝ | f x ≤ f y } := by
      ext f; simp [Set.mem_iInter]
    rw [heq]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (measurable_pi_apply x) (measurable_pi_apply y)
  -- Combine the two pieces.
  have heq :
      OrderPolytope α =
        { f : α → ℝ | ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 } ∩
          { f : α → ℝ | ∀ x y, x ≤ y → f x ≤ f y } := by
    ext f; rfl
  rw [heq]
  exact hA.inter hB

/-! ### §6 — Hand-verified instance: discrete 3-antichain

For a discrete poset (the only `≤` relations are reflexive), the
order-preserving condition collapses to a vacuous statement and the
order polytope equals the cube `[0,1]^α`. Setting `α = {a, b, c}`
gives `O(α) = [0,1]^3`, the canonical example from
mg-163f §5 + Brightwell §4. -/

/-- For a poset whose `≤` relation is just equality (i.e. a discrete
poset / antichain), the order polytope equals the cube `[0,1]^α`. -/
lemma eq_cube_of_discrete (h : ∀ x y : α, x ≤ y → x = y) :
    OrderPolytope α = Set.univ.pi (fun _ : α => Set.Icc (0 : ℝ) 1) := by
  ext f
  refine ⟨fun hf x _ => hf.1 x, fun hf => ⟨fun x => hf x (Set.mem_univ x), ?_⟩⟩
  intro x y hxy
  rw [h x y hxy]

end OrderPolytope

/-! ### §7 — Discrete 3-antichain `example`

A small concrete check that the spec's canonical
`α = {a, b, c}` discrete-3-antichain instance reduces to `[0,1]^3`. -/

/-- Three-element type for the canonical discrete 3-antichain check. -/
inductive Three : Type
  | a : Three
  | b : Three
  | c : Three
  deriving DecidableEq

namespace Three

/-- The discrete partial order on `Three`: `x ≤ y` iff `x = y`. -/
instance : PartialOrder Three where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ hxy hyz := hxy.trans hyz
  le_antisymm _ _ hxy _ := hxy

end Three

/-- **Discrete 3-antichain check.** Under the discrete order on
`Three = {a, b, c}`, the order polytope is exactly the cube
`[0,1]^Three`. This is the hand-verification asked for by
mg-163f §5 / EX-3 brief §2.3. -/
example : OrderPolytope Three =
    Set.univ.pi (fun _ : Three => Set.Icc (0 : ℝ) 1) :=
  OrderPolytope.eq_cube_of_discrete fun _ _ h => h

end LinearExt
end OneThird
