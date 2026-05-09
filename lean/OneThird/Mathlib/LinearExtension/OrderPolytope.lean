/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import OneThird.Mathlib.LinearExtension.Fintype

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
set_option linter.unusedDecidableInType false

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

/-! ### §7 — Stanley vertex theorem (Stanley 1986, Theorem 1.2)

The extreme points of the order polytope `O(α)` are exactly the {0,1}-indicator
functions `1_I` indexed by upper sets `I : UpperSet α`:

```
  Set.extremePoints ℝ (OrderPolytope α)
    = { f : α → ℝ | ∃ I : UpperSet α, f = Set.indicator (I : Set α) (1 : α → ℝ) }.
```

Both directions are proved here.

* **Direction 1** (`indicator_upperSet_isExtreme`). For any `I : UpperSet α`, the
  {0,1}-indicator `1_I` lies in `O(α)` and is an extreme point. Direct
  convex-combination pinning: if `1_I = a • f + b • g` with `a, b > 0` and
  `f, g ∈ O(α)`, then on `x ∈ I` the [0,1]-bound forces `f x = g x = 1`, and on
  `x ∉ I` the non-negativity bound forces `f x = g x = 0`.

* **Direction 2** (`extremePoint_eq_indicator_upperSet`, requires `[Fintype α]`).
  Every extreme point is `1_I` for some `I : UpperSet α`. Contrapositive +
  explicit `±ε`-perturbation on the level set `{x : f x = c}` for `c ∈ (0, 1)`
  in the range of `f`: for sufficiently small `ε > 0`, both
  `f_ε^± := f ± ε · 1_{f^{-1}(c)}` lie in `O(α)`, are distinct, and average to
  `f`, contradicting `f` extreme. Hence every extreme `f` takes only values in
  `{0, 1}`, and `f^{-1}(1)` is automatically an upper set.

References: see `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`
(mg-4831) for the latex writeup, mathlib API mapping, and the
LowerSet → UpperSet spec correction; mg-163f for the Path-A commitment;
Stanley 1986, *Two poset polytopes*, Discrete Comput. Geom. **1**, Thm 1.2. -/

/-! #### §7.1 — Direction 1: `1_I` is an extreme point. -/

/-- For an upper set `I ⊆ α`, the {0,1}-indicator `1_I` lies in
`OrderPolytope α`. -/
lemma indicator_upperSet_mem (I : UpperSet α) :
    Set.indicator (I : Set α) (1 : α → ℝ) ∈ OrderPolytope α := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · -- pointwise membership in [0, 1]
    by_cases h : x ∈ (I : Set α)
    · rw [Set.indicator_of_mem h]
      simp [Set.mem_Icc]
    · rw [Set.indicator_of_notMem h]
      simp [Set.mem_Icc]
  · -- order-preservation: upper-set property
    by_cases hx : x ∈ (I : Set α)
    · have hy : y ∈ (I : Set α) := I.upper hxy hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) y

/-- **Stanley vertex theorem, Direction 1.** For an upper set `I ⊆ α`, the
{0,1}-indicator `1_I` is an extreme point of `OrderPolytope α`. -/
theorem indicator_upperSet_isExtreme (I : UpperSet α) :
    Set.indicator (I : Set α) (1 : α → ℝ) ∈
      Set.extremePoints ℝ (OrderPolytope α) := by
  refine ⟨indicator_upperSet_mem I, ?_⟩
  intro f hf g _hg hseg
  obtain ⟨a, b, ha, hb, hab, hconv⟩ := hseg
  funext x
  -- Pointwise consequence: a * f x + b * g x = (1_I) x.
  have hpw : a * f x + b * g x = Set.indicator (I : Set α) (1 : α → ℝ) x := by
    have hfun := congrFun hconv x
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hfun
  have hfx_in : f x ∈ Set.Icc (0 : ℝ) 1 := hf.1 x
  have hgx_in : g x ∈ Set.Icc (0 : ℝ) 1 := _hg.1 x
  rw [Set.mem_Icc] at hfx_in hgx_in
  by_cases hx : x ∈ (I : Set α)
  · -- value 1 case: f x = 1 = (1_I) x
    rw [Set.indicator_of_mem hx] at hpw
    have hpw' : a * f x + b * g x = 1 := by simpa using hpw
    have h2 : 0 ≤ a * (1 - f x) := mul_nonneg ha.le (by linarith)
    have h3 : 0 ≤ b * (1 - g x) := mul_nonneg hb.le (by linarith)
    have h4 : a * (1 - f x) + b * (1 - g x) = 0 := by nlinarith [hab]
    have h5 : a * (1 - f x) = 0 := le_antisymm (by linarith) h2
    have h6 : 1 - f x = 0 := by
      rcases mul_eq_zero.mp h5 with h | h
      · exact (ha.ne' h).elim
      · exact h
    rw [Set.indicator_of_mem hx]
    have : f x = 1 := by linarith
    simp [this]
  · -- value 0 case: f x = 0 = (1_I) x
    rw [Set.indicator_of_notMem hx] at hpw
    have h1 : 0 ≤ a * f x := mul_nonneg ha.le hfx_in.1
    have h2 : 0 ≤ b * g x := mul_nonneg hb.le hgx_in.1
    have h3 : a * f x = 0 := le_antisymm (by linarith) h1
    have hfx0 : f x = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact (ha.ne' h).elim
      · exact h
    rw [Set.indicator_of_notMem hx, hfx0]

/-! #### §7.2 — Direction 2: every extreme point is `1_I`.

Auxiliary: a `±ε`-perturbation of `f` on its level set `f^{-1}(c)`. -/

/-- The level-set perturbation of `f` adding `ε` on `{x : f x = c}`,
realised as `f` plus `ε · 1_{f^{-1}(c)}` (using `Set.indicator`). -/
private noncomputable def perturbUp (f : α → ℝ) (c ε : ℝ) : α → ℝ :=
  fun x => f x + Set.indicator {y : α | f y = c} (fun _ => ε) x

/-- The level-set perturbation of `f` subtracting `ε` on `{x : f x = c}`. -/
private noncomputable def perturbDown (f : α → ℝ) (c ε : ℝ) : α → ℝ :=
  fun x => f x - Set.indicator {y : α | f y = c} (fun _ => ε) x

private lemma perturbUp_apply_of_eq {f : α → ℝ} (c ε : ℝ) {x : α} (hx : f x = c) :
    perturbUp f c ε x = f x + ε := by
  simp [perturbUp, Set.indicator_of_mem (show x ∈ {y : α | f y = c} from hx)]

private lemma perturbUp_apply_of_ne {f : α → ℝ} (c ε : ℝ) {x : α} (hx : f x ≠ c) :
    perturbUp f c ε x = f x := by
  simp [perturbUp, Set.indicator_of_notMem (show x ∉ {y : α | f y = c} from hx)]

private lemma perturbDown_apply_of_eq {f : α → ℝ} (c ε : ℝ) {x : α} (hx : f x = c) :
    perturbDown f c ε x = f x - ε := by
  simp [perturbDown, Set.indicator_of_mem (show x ∈ {y : α | f y = c} from hx)]

private lemma perturbDown_apply_of_ne {f : α → ℝ} (c ε : ℝ) {x : α} (hx : f x ≠ c) :
    perturbDown f c ε x = f x := by
  simp [perturbDown, Set.indicator_of_notMem (show x ∉ {y : α | f y = c} from hx)]

/-- Pointwise convex average: `(perturbUp + perturbDown) / 2 = f`. -/
private lemma half_perturbUp_add_half_perturbDown (f : α → ℝ) (c ε : ℝ) :
    (1/2 : ℝ) • perturbUp f c ε + (1/2 : ℝ) • perturbDown f c ε = f := by
  funext y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hy : f y = c
  · rw [perturbUp_apply_of_eq c ε hy, perturbDown_apply_of_eq c ε hy]
    ring
  · rw [perturbUp_apply_of_ne c ε hy, perturbDown_apply_of_ne c ε hy]
    ring

/-- Existence of a positive `ε` satisfying the gap conditions for the
perturbation argument: `ε ≤ c`, `ε ≤ 1 - c`, and `ε ≤ |f x - c|` whenever
`f x ≠ c`. Requires `[Fintype α]` so the gap is a finite minimum. -/
private lemma exists_perturbation_eps [Fintype α] (f : α → ℝ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ c ∧ ε ≤ 1 - c ∧
      ∀ x : α, f x ≠ c → ε ≤ |f x - c| := by
  classical
  by_cases hex : ∃ x : α, f x ≠ c
  case neg =>
    refine ⟨min c (1 - c), lt_min hc0 (sub_pos.mpr hc1),
      min_le_left _ _, min_le_right _ _, ?_⟩
    intro x hx
    exact (hex ⟨x, hx⟩).elim
  case pos =>
    set s : Finset α := (Finset.univ : Finset α).filter (fun x => f x ≠ c) with hs_def
    have hs_ne : s.Nonempty := by
      obtain ⟨x, hx⟩ := hex
      exact ⟨x, by simp [hs_def, hx]⟩
    set m : ℝ := s.inf' hs_ne (fun x => |f x - c|) with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def, Finset.lt_inf'_iff]
      intro x hx
      have hxne : f x ≠ c := by
        have := (Finset.mem_filter.mp hx).2
        exact this
      exact abs_pos.mpr (sub_ne_zero.mpr hxne)
    refine ⟨min (min c (1 - c)) m, ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min hc0 (sub_pos.mpr hc1)) hm_pos
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · intro x hx
      have hxs : x ∈ s := by
        simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx
      have hm_le : m ≤ |f x - c| := by
        rw [hm_def]
        exact Finset.inf'_le _ hxs
      exact (min_le_right _ _).trans hm_le

/-- The up-perturbation `perturbUp f c ε` lies in `OrderPolytope α` when
`ε > 0` is small relative to the gap conditions. -/
private lemma perturbUp_mem {f : α → ℝ} (hf : f ∈ OrderPolytope α) {c : ℝ}
    (hc0 : 0 < c) (_hc1 : c < 1) {ε : ℝ} (hε_pos : 0 < ε)
    (_hε_c : ε ≤ c) (hε_1c : ε ≤ 1 - c)
    (hε_gap : ∀ x : α, f x ≠ c → ε ≤ |f x - c|) :
    perturbUp f c ε ∈ OrderPolytope α := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · -- pointwise [0, 1]
    by_cases hx : f x = c
    · rw [perturbUp_apply_of_eq c ε hx, hx, Set.mem_Icc]
      exact ⟨by linarith, by linarith⟩
    · rw [perturbUp_apply_of_ne c ε hx]
      exact hf.1 x
  · -- monotonicity
    have hfxy : f x ≤ f y := hf.2 x y hxy
    by_cases hx : f x = c
    · by_cases hy : f y = c
      · rw [perturbUp_apply_of_eq c ε hx, perturbUp_apply_of_eq c ε hy, hx, hy]
      · -- f x = c, f y ≠ c. Monotone: c = f x ≤ f y, plus f y ≠ c, gives c < f y.
        rw [perturbUp_apply_of_eq c ε hx, perturbUp_apply_of_ne c ε hy, hx]
        have hfyc : c < f y :=
          lt_of_le_of_ne (hx ▸ hfxy) (Ne.symm hy)
        have habs : |f y - c| = f y - c := abs_of_pos (sub_pos.mpr hfyc)
        have : ε ≤ f y - c := habs ▸ hε_gap y hy
        linarith
    · by_cases hy : f y = c
      · -- f x ≠ c, f y = c. Monotone: f x ≤ f y = c, plus f x ≠ c, gives f x < c.
        rw [perturbUp_apply_of_ne c ε hx, perturbUp_apply_of_eq c ε hy, hy]
        have hfxc : f x < c :=
          lt_of_le_of_ne (hy ▸ hfxy) hx
        linarith
      · -- f x ≠ c, f y ≠ c. Same as f.
        rw [perturbUp_apply_of_ne c ε hx, perturbUp_apply_of_ne c ε hy]
        exact hfxy

/-- The down-perturbation `perturbDown f c ε` lies in `OrderPolytope α` when
`ε > 0` is small relative to the gap conditions. -/
private lemma perturbDown_mem {f : α → ℝ} (hf : f ∈ OrderPolytope α) {c : ℝ}
    (_hc0 : 0 < c) (hc1 : c < 1) {ε : ℝ} (hε_pos : 0 < ε)
    (hε_c : ε ≤ c) (_hε_1c : ε ≤ 1 - c)
    (hε_gap : ∀ x : α, f x ≠ c → ε ≤ |f x - c|) :
    perturbDown f c ε ∈ OrderPolytope α := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · -- pointwise [0, 1]
    by_cases hx : f x = c
    · rw [perturbDown_apply_of_eq c ε hx, hx, Set.mem_Icc]
      exact ⟨by linarith, by linarith⟩
    · rw [perturbDown_apply_of_ne c ε hx]
      exact hf.1 x
  · -- monotonicity
    have hfxy : f x ≤ f y := hf.2 x y hxy
    by_cases hx : f x = c
    · by_cases hy : f y = c
      · rw [perturbDown_apply_of_eq c ε hx, perturbDown_apply_of_eq c ε hy, hx, hy]
      · -- f x = c, f y ≠ c. c < f y. Goal: c - ε ≤ f y. Trivial.
        rw [perturbDown_apply_of_eq c ε hx, perturbDown_apply_of_ne c ε hy, hx]
        have hfyc : c < f y :=
          lt_of_le_of_ne (hx ▸ hfxy) (Ne.symm hy)
        linarith
    · by_cases hy : f y = c
      · -- f x ≠ c, f y = c. f x < c. Goal: f x ≤ c - ε.
        rw [perturbDown_apply_of_ne c ε hx, perturbDown_apply_of_eq c ε hy, hy]
        have hfxc : f x < c :=
          lt_of_le_of_ne (hy ▸ hfxy) hx
        have habs : |f x - c| = c - f x := by
          rw [abs_sub_comm]; exact abs_of_pos (sub_pos.mpr hfxc)
        have : ε ≤ c - f x := habs ▸ hε_gap x hx
        linarith
      · -- f x ≠ c, f y ≠ c. Same as f.
        rw [perturbDown_apply_of_ne c ε hx, perturbDown_apply_of_ne c ε hy]
        exact hfxy

/-- **Direction 2 (boolean lemma).** Every extreme point of `OrderPolytope α`
takes only values in `{0, 1}`. -/
private lemma extremePoint_isBoolean [Fintype α]
    {f : α → ℝ} (hf : f ∈ Set.extremePoints ℝ (OrderPolytope α)) :
    ∀ x : α, f x = 0 ∨ f x = 1 := by
  intro x₀
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h0, h1⟩ := hne
  have hbd : f x₀ ∈ Set.Icc (0 : ℝ) 1 := hf.1.1 x₀
  rw [Set.mem_Icc] at hbd
  have hc0 : 0 < f x₀ := lt_of_le_of_ne hbd.1 (Ne.symm h0)
  have hc1 : f x₀ < 1 := lt_of_le_of_ne hbd.2 h1
  obtain ⟨ε, hε_pos, hε_c, hε_1c, hε_gap⟩ :=
    exists_perturbation_eps f (f x₀) hc0 hc1
  have hUp_mem : perturbUp f (f x₀) ε ∈ OrderPolytope α :=
    perturbUp_mem hf.1 hc0 hc1 hε_pos hε_c hε_1c hε_gap
  have hDown_mem : perturbDown f (f x₀) ε ∈ OrderPolytope α :=
    perturbDown_mem hf.1 hc0 hc1 hε_pos hε_c hε_1c hε_gap
  have hseg : f ∈ openSegment ℝ (perturbUp f (f x₀) ε) (perturbDown f (f x₀) ε) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    exact half_perturbUp_add_half_perturbDown f (f x₀) ε
  have heq : perturbUp f (f x₀) ε = f := hf.2 hUp_mem hDown_mem hseg
  have happ : perturbUp f (f x₀) ε x₀ = f x₀ := congrFun heq x₀
  rw [perturbUp_apply_of_eq (f x₀) ε rfl] at happ
  linarith

/-- The 1-level set of an order polytope element is an upper set
(any function in `OrderPolytope α` is monotone, so `f x = 1` and `x ≤ y`
combined with `f y ≤ 1` force `f y = 1`). -/
private lemma onePreimage_isUpperSet
    {f : α → ℝ} (hf : f ∈ OrderPolytope α) :
    IsUpperSet { x : α | f x = 1 } := by
  intro x y hxy hx
  -- hx : f x = 1; want f y = 1.
  change f y = 1
  have hxle : f x ≤ f y := hf.2 x y hxy
  have hy_le : f y ≤ 1 := (hf.1 y).2
  have h1y : (1 : ℝ) ≤ f y := hx ▸ hxle
  linarith

/-- **Stanley vertex theorem, Direction 2.** Every extreme point of
`OrderPolytope α` is the indicator of an upper set. -/
theorem extremePoint_eq_indicator_upperSet [Fintype α]
    {f : α → ℝ} (hf : f ∈ Set.extremePoints ℝ (OrderPolytope α)) :
    ∃ I : UpperSet α, f = Set.indicator (I : Set α) (1 : α → ℝ) := by
  let I : UpperSet α := ⟨{x | f x = 1}, onePreimage_isUpperSet hf.1⟩
  have hI_coe : (I : Set α) = {x | f x = 1} := rfl
  refine ⟨I, ?_⟩
  funext x
  rw [hI_coe]
  by_cases hx : f x = 1
  · rw [Set.indicator_of_mem (show x ∈ ({y | f y = 1} : Set α) from hx)]
    simp [hx]
  · rw [Set.indicator_of_notMem (show x ∉ ({y | f y = 1} : Set α) from hx)]
    rcases extremePoint_isBoolean hf x with h0 | h1
    · exact h0
    · exact (hx h1).elim

/-! #### §7.3 — Stanley vertex theorem (main statement). -/

/-- **Stanley 1986 Theorem 1.2.** For a finite poset `α`, the extreme points
of the order polytope `O(α)` are exactly the `{0, 1}`-indicators of upper
sets of `α`. -/
theorem extremePoints_eq [Fintype α] :
    Set.extremePoints ℝ (OrderPolytope α) =
      { f : α → ℝ | ∃ I : UpperSet α, f = Set.indicator (I : Set α) (1 : α → ℝ) } := by
  ext f
  refine ⟨fun hf => extremePoint_eq_indicator_upperSet hf, ?_⟩
  rintro ⟨I, rfl⟩
  exact indicator_upperSet_isExtreme I

/-! ### §8 — Chamber simplex `σ_L` (Stanley 1986 Theorem 1.4)

For `L : LinearExt α`, the **chamber simplex** indexed by `L` is
the position-monotone subset of the unit cube:

```
  σ_L := { f : α → ℝ | (∀ x, 0 ≤ f x ≤ 1) ∧ (∀ x y, L.pos x ≤ L.pos y → f x ≤ f y) }.
```

The chamber lies inside the order polytope (every `L`-respecting `f` is
α-monotone, since `L` is a linear extension), and Stanley 1986 (1.5)
asserts `Vol(σ_L) = 1/n!` for every `L : LinearExt α`. The proof here
follows the latex strategy of `docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md`
(mg-79a9): push σ_L forward to the standard ordered cube `Δ_n ⊆ Fin n → ℝ`
via the measure-preserving relabel `MeasurableEquiv.piCongrLeft`, then
prove `Vol(Δ_n) = 1/n!` by S_n-tiling. -/

/-! #### §8.1 — Chamber definition and basic properties. -/

/-- The **chamber simplex** indexed by a linear extension `L : LinearExt α`:
the set of `α → ℝ` functions with values in `[0, 1]` that are non-decreasing
along `L`'s linear order. -/
def chamber [Fintype α] [DecidableEq α] (L : OneThird.LinearExt α) : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) }

lemma mem_chamber [Fintype α] [DecidableEq α] {L : OneThird.LinearExt α} {f : α → ℝ} :
    f ∈ chamber L ↔
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) := Iff.rfl

/-- Every chamber lies inside the order polytope: a function
non-decreasing along `L`'s linear order is automatically α-monotone,
because `L` is a linear extension of α. -/
theorem chamber_subset_orderPolytope [Fintype α] [DecidableEq α]
    (L : OneThird.LinearExt α) : chamber L ⊆ OrderPolytope α := by
  intro f hf
  refine ⟨hf.1, fun x y hxy => ?_⟩
  exact hf.2 x y (L.monotone hxy)

end OrderPolytope

/-! ### §9 — The standard ordered cube `Δ_n ⊆ Fin n → ℝ`

The **standard ordered cube** is the simplex of monotone functions
`y : Fin n → ℝ` with values in `[0, 1]`:

```
  Δ_n := { y : Fin n → ℝ | (∀ i, 0 ≤ y i ≤ 1) ∧ (∀ i j, i ≤ j → y i ≤ y j) }.
```

This file proves `Vol(Δ_n) = 1/n!` (Stanley 1986 (1.5), specialised to
`α = Fin n` with the natural order). The proof uses the symmetric
`S_n`-tiling of the cube `[0,1]^n`: each `y ∈ [0,1]^n` is mapped into the
chamber `Δ_n^σ` by the unique sorting permutation `σ = Tuple.sort y`,
and the chambers `Δ_n^σ` for `σ : Equiv.Perm (Fin n)` cover `[0,1]^n`
with pairwise null overlaps (each contained in a `{y k = y k'}` hyperplane).

This lemma is the **DH-5 mathlib upstream candidate** identified in
`docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md` §6.3.
-/

namespace OrderedCube

open MeasureTheory
open scoped Function ENNReal

variable {n : ℕ}

/-- The **standard ordered cube** `Δ_n ⊆ Fin n → ℝ`: monotone functions
with values in `[0, 1]`. -/
def orderedCube (n : ℕ) : Set (Fin n → ℝ) :=
  { y : Fin n → ℝ |
      (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i j : Fin n, i ≤ j → y i ≤ y j) }

/-- The σ-permuted ordered cube `Δ_n^σ`: those `y` for which `y ∘ σ`
sits in the standard ordered cube. -/
def orderedCubePerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  { y : Fin n → ℝ |
      (∀ i, y (σ i) ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i j : Fin n, i ≤ j → y (σ i) ≤ y (σ j)) }

lemma orderedCubePerm_refl : orderedCubePerm n (Equiv.refl _) = orderedCube n := rfl

/-- `orderedCubePerm n σ` is the preimage of `orderedCube n` under
post-composition with `σ`. -/
lemma orderedCubePerm_eq_preimage (σ : Equiv.Perm (Fin n)) :
    orderedCubePerm n σ = (fun y : Fin n → ℝ => y ∘ σ) ⁻¹' orderedCube n := by
  ext y
  rfl

lemma orderedCubePerm_subset_cube (σ : Equiv.Perm (Fin n)) :
    orderedCubePerm n σ ⊆ Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  intro y hy i _
  -- y i ∈ Icc 0 1: use that σ is a bijection.
  have : σ (σ.symm i) = i := σ.apply_symm_apply i
  exact this ▸ hy.1 (σ.symm i)

lemma orderedCube_subset_cube :
    orderedCube n ⊆ Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  simpa using orderedCubePerm_subset_cube (Equiv.refl _)

/-! #### §9.1 — Measurability of `orderedCube` and `orderedCubePerm`. -/

lemma measurableSet_orderedCubePerm (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (orderedCubePerm n σ) := by
  have hA : MeasurableSet { y : Fin n → ℝ | ∀ i, y (σ i) ∈ Set.Icc (0 : ℝ) 1 } := by
    have heq :
        { y : Fin n → ℝ | ∀ i, y (σ i) ∈ Set.Icc (0 : ℝ) 1 } =
          ⋂ i, (fun y : Fin n → ℝ => y (σ i)) ⁻¹' Set.Icc (0 : ℝ) 1 := by
      ext y; simp [Set.mem_iInter]
    rw [heq]
    exact MeasurableSet.iInter
      fun i => measurableSet_Icc.preimage (measurable_pi_apply (σ i))
  have hB : MeasurableSet
      { y : Fin n → ℝ | ∀ i j : Fin n, i ≤ j → y (σ i) ≤ y (σ j) } := by
    have heq :
        { y : Fin n → ℝ | ∀ i j : Fin n, i ≤ j → y (σ i) ≤ y (σ j) } =
          ⋂ i, ⋂ j, ⋂ _ : i ≤ j, { y : Fin n → ℝ | y (σ i) ≤ y (σ j) } := by
      ext y; simp [Set.mem_iInter]
    rw [heq]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
  have heq :
      orderedCubePerm n σ =
        { y : Fin n → ℝ | ∀ i, y (σ i) ∈ Set.Icc (0 : ℝ) 1 } ∩
          { y : Fin n → ℝ | ∀ i j : Fin n, i ≤ j → y (σ i) ≤ y (σ j) } := by
    ext y; rfl
  rw [heq]
  exact hA.inter hB

lemma measurableSet_orderedCube : MeasurableSet (orderedCube n) := by
  simpa using measurableSet_orderedCubePerm (Equiv.refl (Fin n))

/-! #### §9.2 — The σ-action on `Fin n → ℝ` is measure-preserving.

For each `σ : Equiv.Perm (Fin n)`, the relabelling `y ↦ y ∘ σ` is the
measurable equivalence `MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ.symm`,
which is measure-preserving by `volume_measurePreserving_piCongrLeft`. -/

/-- The relabelling `y ↦ y ∘ σ : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ)`, realised as
`(MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ).symm` so that the apply-form
`relabelEquiv σ y j = y (σ j)` follows from the `@[simp]` lemma
`Equiv.piCongrLeft_symm_apply`. -/
def relabelEquiv (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).symm

@[simp] lemma relabelEquiv_apply (σ : Equiv.Perm (Fin n)) (y : Fin n → ℝ) (j : Fin n) :
    relabelEquiv σ y j = y (σ j) := by
  -- Via `MeasurableEquiv.coe_piCongrLeft` the coercion of `M.piCongrLeft P σ` is
  -- `Equiv.piCongrLeft P σ`; its `.symm` evaluated by `Equiv.piCongrLeft_symm_apply`.
  change ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).symm : (Fin n → ℝ) → _) y j
    = y (σ j)
  rfl

lemma volume_measurePreserving_relabelEquiv (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (relabelEquiv σ)
      (volume : Measure (Fin n → ℝ)) (volume : Measure (Fin n → ℝ)) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ).symm

lemma volume_orderedCubePerm (σ : Equiv.Perm (Fin n)) :
    volume (orderedCubePerm n σ) = volume (orderedCube n) := by
  rw [orderedCubePerm_eq_preimage]
  -- Show `(· ∘ σ) ⁻¹' orderedCube n = relabelEquiv σ ⁻¹' orderedCube n`.
  have hpre : (fun y : Fin n → ℝ => y ∘ σ) ⁻¹' orderedCube n
      = relabelEquiv σ ⁻¹' orderedCube n := by
    ext y
    refine Iff.rfl.trans ?_
    constructor <;> intro hy
    · refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · simpa [relabelEquiv_apply] using hy.1 i
      · simpa [relabelEquiv_apply] using hy.2 i j hij
    · refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · simpa [relabelEquiv_apply] using hy.1 i
      · simpa [relabelEquiv_apply] using hy.2 i j hij
  rw [hpre]
  exact (volume_measurePreserving_relabelEquiv σ).measure_preimage_equiv (orderedCube n)

/-! #### §9.3 — The chambers cover the cube.

For each `y ∈ [0,1]^n`, the sorting permutation `σ := Tuple.sort y`
satisfies `y ∈ orderedCubePerm n σ`. -/

lemma cube_subset_iUnion_orderedCubePerm :
    Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) ⊆
      ⋃ σ : Equiv.Perm (Fin n), orderedCubePerm n σ := by
  intro y hy
  refine Set.mem_iUnion.mpr ⟨Tuple.sort y, ?_, ?_⟩
  · intro i
    -- Tuple.sort is a permutation, so `(Tuple.sort y) i` ranges over Fin n,
    -- and `y ∈ univ.pi (Icc 0 1)` means `y k ∈ Icc 0 1` for all k.
    exact hy ((Tuple.sort y) i) (Set.mem_univ _)
  · intro i j hij
    -- `Tuple.monotone_sort` says `y ∘ Tuple.sort y` is monotone.
    exact Tuple.monotone_sort y hij

lemma iUnion_orderedCubePerm_subset_cube :
    (⋃ σ : Equiv.Perm (Fin n), orderedCubePerm n σ) ⊆
      Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  rw [Set.iUnion_subset_iff]
  intro σ
  exact orderedCubePerm_subset_cube σ

lemma cube_eq_iUnion_orderedCubePerm :
    Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) =
      ⋃ σ : Equiv.Perm (Fin n), orderedCubePerm n σ := by
  apply Set.Subset.antisymm
  · exact cube_subset_iUnion_orderedCubePerm
  · exact iUnion_orderedCubePerm_subset_cube

/-! #### §9.4 — Pairwise overlaps lie in a hyperplane and have measure zero. -/

/-- The hyperplane `{y | y k = y k'}`, realised as a `Submodule ℝ (Fin n → ℝ)`. -/
def equalCoordSubmodule (k k' : Fin n) : Submodule ℝ (Fin n → ℝ) where
  carrier := { y : Fin n → ℝ | y k = y k' }
  zero_mem' := by change (0 : Fin n → ℝ) k = (0 : Fin n → ℝ) k'; simp
  add_mem' {a b} ha hb := by
    change (a + b) k = (a + b) k'
    simp only [Pi.add_apply]
    rw [show a k = a k' from ha, show b k = b k' from hb]
  smul_mem' c a ha := by
    change (c • a) k = (c • a) k'
    simp only [Pi.smul_apply]
    rw [show a k = a k' from ha]

lemma mem_equalCoordSubmodule {k k' : Fin n} {y : Fin n → ℝ} :
    y ∈ equalCoordSubmodule k k' ↔ y k = y k' := Iff.rfl

lemma equalCoordSubmodule_ne_top {k k' : Fin n} (h : k ≠ k') :
    equalCoordSubmodule k k' ≠ ⊤ := by
  intro hEq
  -- The function `f i := if i = k then 1 else 0` has `f k = 1`, `f k' = 0`,
  -- so `f k ≠ f k'` and `f` cannot lie in `equalCoordSubmodule k k'`.
  let f : Fin n → ℝ := fun i => if i = k then 1 else 0
  have hf_in : f ∈ equalCoordSubmodule k k' := by
    rw [hEq]; trivial
  rw [mem_equalCoordSubmodule] at hf_in
  have hk : f k = 1 := if_pos rfl
  have hk' : f k' = 0 := if_neg h.symm
  rw [hk, hk'] at hf_in
  exact one_ne_zero hf_in

lemma volume_equalCoordSubmodule {k k' : Fin n} (h : k ≠ k') :
    volume (equalCoordSubmodule k k' : Set (Fin n → ℝ)) = 0 :=
  Measure.addHaar_submodule volume _ (equalCoordSubmodule_ne_top h)

/-- For `σ ≠ τ`, the two chambers' intersection lies in a hyperplane,
hence has Lebesgue measure zero. -/
lemma volume_inter_orderedCubePerm_of_ne {σ τ : Equiv.Perm (Fin n)} (h : σ ≠ τ) :
    volume (orderedCubePerm n σ ∩ orderedCubePerm n τ) = 0 := by
  -- σ ≠ τ as Equiv.Perm, so ∃ i₀, σ i₀ ≠ τ i₀.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, σ i₀ ≠ τ i₀ := by
    by_contra hAll
    push_neg at hAll
    exact h (Equiv.ext hAll)
  set k := σ i₀ with hk_def
  set k' := τ i₀ with hk'_def
  have hkne : k ≠ k' := hi₀
  -- Show `orderedCubePerm n σ ∩ orderedCubePerm n τ ⊆ equalCoordSubmodule k k'`.
  have hsub : orderedCubePerm n σ ∩ orderedCubePerm n τ ⊆
      (equalCoordSubmodule k k' : Set (Fin n → ℝ)) := by
    intro y hy
    obtain ⟨hyσ, hyτ⟩ := hy
    -- both `y ∘ σ` and `y ∘ τ` are monotone.
    have hmσ : Monotone (fun i => y (σ i)) := fun i j hij => hyσ.2 i j hij
    have hmτ : Monotone (fun i => y (τ i)) := fun i j hij => hyτ.2 i j hij
    have heq : (fun i => y (σ i)) = (fun i => y (τ i)) :=
      Tuple.unique_monotone hmσ hmτ
    have happ : y (σ i₀) = y (τ i₀) := congrFun heq i₀
    -- Goal: y ∈ ↑(equalCoordSubmodule k k') = {y | y k = y k'}.
    -- By `set`, `k = σ i₀` and `k' = τ i₀` definitionally.
    show y k = y k'
    exact happ
  -- Apply addHaar_submodule via measure monotonicity.
  refine measure_mono_null hsub ?_
  exact volume_equalCoordSubmodule hkne

/-! #### §9.5 — Volume of the ordered cube. -/

/-- **DH-5 candidate** (Stanley 1986 (1.5)). The standard ordered cube
`Δ_n ⊆ Fin n → ℝ` has Lebesgue volume `1 / n!`.

Proof: use the symmetric `S_n`-tiling
`[0,1]^n = ⋃_{σ ∈ S_n} Δ_n^σ` (each `y` lands in the chamber indexed by
its sorting permutation `Tuple.sort y`); each `Δ_n^σ` has the same
volume as `Δ_n` (by the measure-preserving relabel
`MeasurableEquiv.piCongrLeft`); pairwise overlaps `Δ_n^σ ∩ Δ_n^τ` for
`σ ≠ τ` lie in a hyperplane `{y k = y k'}` and have measure zero
(`Measure.addHaar_submodule`). Combining, `n! · Vol(Δ_n) = Vol([0,1]^n) = 1`. -/
theorem volume_orderedCube (n : ℕ) :
    volume (orderedCube n) = ENNReal.ofReal (1 / (Nat.factorial n : ℝ)) := by
  -- Step 1: volume of `[0,1]^n` is 1.
  have hCube : volume (Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
      = 1 := by
    rw [volume_pi_pi]; simp
  -- Step 2: AE-disjoint family of chambers via `measure_biUnion_finset₀`.
  have hMble : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      NullMeasurableSet (orderedCubePerm n σ) volume :=
    fun σ _ => (measurableSet_orderedCubePerm σ).nullMeasurableSet
  have hAE : Set.Pairwise ((Finset.univ : Finset (Equiv.Perm (Fin n))) : Set _)
      (AEDisjoint volume on orderedCubePerm n) := by
    intro σ _ τ _ h
    -- `AEDisjoint μ s t` unfolds to `μ (s ∩ t) = 0` by definition.
    exact volume_inter_orderedCubePerm_of_ne h
  have hUnion :
      volume (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), orderedCubePerm n σ) =
        ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), volume (orderedCubePerm n σ) :=
    measure_biUnion_finset₀ hAE hMble
  -- Step 3: convert the bi-union to an i-union and substitute via the cover.
  have hUnionEq :
      (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), orderedCubePerm n σ) =
        Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    rw [show (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), orderedCubePerm n σ)
          = ⋃ σ : Equiv.Perm (Fin n), orderedCubePerm n σ by
          ext y; simp]
    exact (cube_eq_iUnion_orderedCubePerm).symm
  rw [hUnionEq, hCube] at hUnion
  -- hUnion : 1 = ∑ σ ∈ univ, volume (orderedCubePerm n σ).
  -- Step 4: rewrite each summand using `volume_orderedCubePerm`.
  have hSum :
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), volume (orderedCubePerm n σ)) =
        (Nat.factorial n : ℝ≥0∞) * volume (orderedCube n) := by
    simp only [volume_orderedCubePerm, Finset.sum_const, Finset.card_univ,
               Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [hSum] at hUnion
  -- hUnion : 1 = (n! : ℝ≥0∞) * volume (orderedCube n).
  -- Step 5: solve for volume (orderedCube n) and convert to ENNReal.ofReal form.
  have hfact_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfact_ne : (Nat.factorial n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos n).ne'
  have hfact_ne_top : (Nat.factorial n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  -- From `1 = (n! : ℝ≥0∞) * v`, deduce `v = 1 / n!` via `eq_div_iff`.
  -- ENNReal.eq_div_iff: `b = c / a ↔ a * b = c` (when a ≠ 0, a ≠ ∞).
  have hsolve : volume (orderedCube n) = (1 : ℝ≥0∞) / (Nat.factorial n : ℝ≥0∞) := by
    rw [ENNReal.eq_div_iff hfact_ne hfact_ne_top]
    exact hUnion.symm
  rw [hsolve, ENNReal.ofReal_div_of_pos hfact_pos, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast]

end OrderedCube

/-! ### §10 — Chamber volume `Vol(σ_L) = 1/n!`

For any linear extension `L : LinearExt α`, the chamber `σ_L` has the
same Lebesgue volume as the standard ordered cube `Δ_n`, namely `1/n!`.
The proof: push `σ_L` forward to `Δ_n` via the measure-preserving
relabelling `Φ_L : (α → ℝ) ≃ᵐ (Fin n → ℝ)` defined by composition
with `L.toFun.symm`. -/

namespace OrderPolytope

open MeasureTheory OrderedCube

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- The relabelling `Φ_L : (α → ℝ) ≃ᵐ (Fin n → ℝ)` defined by post-composing
with `L.toFun.symm`. Measure-preserving by `volume_measurePreserving_piCongrLeft`. -/
def chamberRelabel (L : OneThird.LinearExt α) :
    (α → ℝ) ≃ᵐ (Fin (Fintype.card α) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card α) => ℝ) L.toFun

@[simp] lemma chamberRelabel_apply (L : OneThird.LinearExt α) (f : α → ℝ)
    (i : Fin (Fintype.card α)) : chamberRelabel L f i = f (L.toFun.symm i) := by
  have h := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin (Fintype.card α) => ℝ)
    (e := L.toFun) (f := fun a : α => f a) (a := L.toFun.symm i)
  simp only [Equiv.apply_symm_apply] at h
  exact h

lemma volume_measurePreserving_chamberRelabel (L : OneThird.LinearExt α) :
    MeasurePreserving (chamberRelabel L)
      (volume : Measure (α → ℝ)) (volume : Measure (Fin (Fintype.card α) → ℝ)) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card α) => ℝ) L.toFun

/-- The chamber `σ_L` is the preimage of the standard ordered cube under
the relabelling `Φ_L`. -/
lemma chamber_eq_preimage_orderedCube (L : OneThird.LinearExt α) :
    chamber L = chamberRelabel L ⁻¹' orderedCube (Fintype.card α) := by
  ext f
  constructor
  · intro hf
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · -- chamberRelabel L f i = f (L.toFun.symm i) ∈ Icc 0 1
      simpa [chamberRelabel_apply] using hf.1 (L.toFun.symm i)
    · -- chamberRelabel L f i ≤ chamberRelabel L f j when i ≤ j
      simp only [chamberRelabel_apply]
      apply hf.2
      -- L.pos (L.toFun.symm i) ≤ L.pos (L.toFun.symm j)
      -- L.pos x = L.toFun x; L.toFun (L.toFun.symm i) = i.
      change L.toFun (L.toFun.symm i) ≤ L.toFun (L.toFun.symm j)
      rw [L.toFun.apply_symm_apply, L.toFun.apply_symm_apply]
      exact hij
  · intro hf
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · -- f x ∈ Icc 0 1: use hf.1 with i = L.pos x
      have h := hf.1 (L.toFun x)
      simp only [chamberRelabel_apply, L.toFun.symm_apply_apply] at h
      exact h
    · -- f x ≤ f y given L.pos x ≤ L.pos y
      have h := hf.2 (L.toFun x) (L.toFun y) hxy
      simp only [chamberRelabel_apply, L.toFun.symm_apply_apply] at h
      exact h

/-- **Stanley 1986 Theorem 1.4 (volume part).** Each chamber `σ_L` has
Lebesgue volume `1/n!` where `n = |α|`. -/
theorem chamber_volume (L : OneThird.LinearExt α) :
    volume (chamber L) = ENNReal.ofReal (1 / (Nat.factorial (Fintype.card α) : ℝ)) := by
  rw [chamber_eq_preimage_orderedCube]
  rw [(volume_measurePreserving_chamberRelabel L).measure_preimage_equiv]
  exact volume_orderedCube _

/-- The chamber `σ_L` is Borel-measurable: it is the preimage of the
measurable `orderedCube` under the measurable equivalence `chamberRelabel L`. -/
theorem measurableSet_chamber (L : OneThird.LinearExt α) :
    MeasurableSet (chamber L) := by
  rw [chamber_eq_preimage_orderedCube]
  exact (chamberRelabel L).measurableSet_preimage.mpr measurableSet_orderedCube

end OrderPolytope

/-! ### §11 — Chamber cover, measure-zero overlap, and master volume

This section completes Stanley 1986 Theorem 1.4 by showing:

* the chambers `σ_L` cover the order polytope `O(α)`
  (`OrderPolytope.chamber_cover`);
* pairwise intersections `σ_L ∩ σ_{L'}` have Lebesgue measure zero
  for `L ≠ L'` (`OrderPolytope.chamber_inter_meas_zero`);
* combining with `chamber_volume`, the master volume formula
  `Vol(O(α)) = e(α) / n!` (`OrderPolytope.orderPolytope_volume`).

Cover: per the latex deliverable `docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md`
(mg-79a9) §3, given `f ∈ O(α)`, sort α by lex key `(f x, S.pos x)` where
`S` is a fixed Szpilrajn linear extension used to break ties. The lex key
is injective on α (since `S.pos` is), so the resulting sort permutation is
unique; the chamber-membership argument follows from `Tuple.monotone_sort`.

Overlap: per the deliverable §4, for `L ≠ L'` extract a witness `x : α`
with `L.toFun x ≠ L'.toFun x`; setting `y := L.toFun.symm (L'.toFun x)`
gives `x ≠ y`. On the intersection both `f ∘ L.toFun.symm` and
`f ∘ L'.toFun.symm` are monotone `Fin n → ℝ` functions, hence equal by
`Tuple.unique_monotone`; evaluating at `L'.toFun x` gives `f x = f y`.
The hyperplane `{f | f x = f y}` is the kernel of the linear functional
`f ↦ f x - f y`, a strict submodule of `α → ℝ`, so Lebesgue-null by
`addHaar_submodule`.

Master volume: combine the cover, AE-disjointness from the overlap lemma,
and the per-chamber volume `1/n!` via `measure_biUnion_finset₀`. -/

namespace OrderPolytope

open MeasureTheory OrderedCube
open scoped Function ENNReal

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! #### §11.1 — Cover via lex sort `(f x, S.pos x)`. -/

/-- Auxiliary: the lex sort key `Fin n → Lex (ℝ × Fin n)` indexed by a
linear extension `S` (used as the Szpilrajn tie-breaker), defined by
`i ↦ toLex (f (S.toFun.symm i), i)`. -/
private def coverKey (f : α → ℝ) (S : OneThird.LinearExt α) :
    Fin (Fintype.card α) → Lex (ℝ × Fin (Fintype.card α)) :=
  fun i => toLex (f (S.toFun.symm i), i)

/-- Auxiliary: the sort permutation of the lex key. -/
private noncomputable def coverPerm (f : α → ℝ) (S : OneThird.LinearExt α) :
    Equiv.Perm (Fin (Fintype.card α)) :=
  Tuple.sort (coverKey f S)

/-- For any `f ∈ OrderPolytope α`, the linear extension `L_f : LinearExt α`
constructed by sorting α by the lex key `(f x, S.pos x)`, where `S` is a
fixed Szpilrajn extension used for tie-breaking. The construction satisfies
`f ∈ chamber L_f` (see `mem_chamber_linearExtFromOrderPreserving`). -/
noncomputable def linearExtFromOrderPreserving {f : α → ℝ}
    (hf : f ∈ OrderPolytope α) : OneThird.LinearExt α :=
  let S : OneThird.LinearExt α := OneThird.LinearExt.szpilrajn α
  let σ : Equiv.Perm (Fin (Fintype.card α)) := coverPerm f S
  { toFun := S.toFun.trans σ.symm
    monotone := fun {x y} hxy => by
      change σ.symm (S.toFun x) ≤ σ.symm (S.toFun y)
      by_contra hneg
      push_neg at hneg
      -- hneg : σ.symm (S.toFun y) < σ.symm (S.toFun x).
      have hmono : coverKey f S (σ (σ.symm (S.toFun y))) ≤
          coverKey f S (σ (σ.symm (S.toFun x))) :=
        Tuple.monotone_sort (coverKey f S) (le_of_lt hneg)
      rw [σ.apply_symm_apply, σ.apply_symm_apply] at hmono
      simp only [coverKey, Equiv.symm_apply_apply] at hmono
      -- hmono : toLex (f y, S.toFun y) ≤ toLex (f x, S.toFun x).
      rw [Prod.Lex.toLex_le_toLex'] at hmono
      obtain ⟨h1, h2⟩ := hmono
      have hfxy : f x ≤ f y := hf.2 x y hxy
      have hSxy : S.toFun x ≤ S.toFun y := S.monotone hxy
      have hfeq : f y = f x := le_antisymm h1 hfxy
      have hSeq : S.toFun y ≤ S.toFun x := h2 hfeq
      have hSeq' : S.toFun y = S.toFun x := le_antisymm hSeq hSxy
      have hxy_eq : x = y := S.toFun.injective hSeq'.symm
      rw [hxy_eq] at hneg
      exact lt_irrefl _ hneg }

/-- The constructed linear extension contains `f` in its chamber. -/
lemma mem_chamber_linearExtFromOrderPreserving {f : α → ℝ}
    (hf : f ∈ OrderPolytope α) :
    f ∈ chamber (linearExtFromOrderPreserving hf) := by
  refine ⟨hf.1, ?_⟩
  intro x y hpos
  -- (linearExtFromOrderPreserving hf).pos x ≤ (linearExtFromOrderPreserving hf).pos y.
  let S : OneThird.LinearExt α := OneThird.LinearExt.szpilrajn α
  let σ : Equiv.Perm (Fin (Fintype.card α)) := coverPerm f S
  change σ.symm (S.toFun x) ≤ σ.symm (S.toFun y) at hpos
  have hmono : coverKey f S (σ (σ.symm (S.toFun x))) ≤
      coverKey f S (σ (σ.symm (S.toFun y))) :=
    Tuple.monotone_sort (coverKey f S) hpos
  rw [σ.apply_symm_apply, σ.apply_symm_apply] at hmono
  simp only [coverKey, Equiv.symm_apply_apply] at hmono
  rw [Prod.Lex.toLex_le_toLex'] at hmono
  exact hmono.1

/-- **Stanley 1986 Theorem 1.4 (cover part).** The order polytope `O(α)`
is the union of all chambers `σ_L` over linear extensions of `α`. -/
theorem chamber_cover :
    (OrderPolytope α : Set (α → ℝ)) = ⋃ L : OneThird.LinearExt α, chamber L := by
  refine Set.Subset.antisymm (fun f hf => ?_) (fun f hf => ?_)
  · exact Set.mem_iUnion.mpr
      ⟨linearExtFromOrderPreserving hf, mem_chamber_linearExtFromOrderPreserving hf⟩
  · rw [Set.mem_iUnion] at hf
    obtain ⟨L, hL⟩ := hf
    exact chamber_subset_orderPolytope L hL

/-! #### §11.2 — Pairwise overlaps lie in a hyperplane and have measure zero. -/

/-- The hyperplane `{f : α → ℝ | f x = f y}`, realised as a
`Submodule ℝ (α → ℝ)`. -/
def equalCoordSubmoduleAlpha (x y : α) : Submodule ℝ (α → ℝ) where
  carrier := { f : α → ℝ | f x = f y }
  zero_mem' := by change (0 : α → ℝ) x = (0 : α → ℝ) y; simp
  add_mem' {a b} ha hb := by
    change (a + b) x = (a + b) y
    simp only [Pi.add_apply]
    rw [show a x = a y from ha, show b x = b y from hb]
  smul_mem' c a ha := by
    change (c • a) x = (c • a) y
    simp only [Pi.smul_apply]
    rw [show a x = a y from ha]

lemma mem_equalCoordSubmoduleAlpha {x y : α} {f : α → ℝ} :
    f ∈ equalCoordSubmoduleAlpha x y ↔ f x = f y := Iff.rfl

lemma equalCoordSubmoduleAlpha_ne_top {x y : α} (h : x ≠ y) :
    (equalCoordSubmoduleAlpha (α := α) x y) ≠ ⊤ := by
  intro hEq
  -- The function which is 1 at `x` and 0 elsewhere violates `f x = f y`.
  let f : α → ℝ := fun i => if i = x then 1 else 0
  have hf_in : f ∈ equalCoordSubmoduleAlpha x y := by rw [hEq]; trivial
  rw [mem_equalCoordSubmoduleAlpha] at hf_in
  have hx : f x = 1 := if_pos rfl
  have hy : f y = 0 := if_neg (Ne.symm h)
  rw [hx, hy] at hf_in
  exact one_ne_zero hf_in

lemma volume_equalCoordSubmoduleAlpha {x y : α} (h : x ≠ y) :
    volume (equalCoordSubmoduleAlpha (α := α) x y : Set (α → ℝ)) = 0 :=
  Measure.addHaar_submodule volume _ (equalCoordSubmoduleAlpha_ne_top h)

/-- **Stanley 1986 Theorem 1.4 (overlap part).** For `L ≠ L'`, the chambers
`σ_L` and `σ_{L'}` intersect in a Lebesgue-null set.

Proof: extract `x : α` with `L.toFun x ≠ L'.toFun x` from `L ≠ L'`; set
`y := L.toFun.symm (L'.toFun x)`. On the intersection, both
`f ∘ L.toFun.symm` and `f ∘ L'.toFun.symm` are monotone `Fin n → ℝ`,
hence equal by `Tuple.unique_monotone`; evaluating at `L'.toFun x` gives
`f x = f y` with `x ≠ y`. The hyperplane `{f | f x = f y}` is null by
`addHaar_submodule`. -/
theorem chamber_inter_meas_zero {L L' : OneThird.LinearExt α} (h : L ≠ L') :
    volume (chamber L ∩ chamber L') = 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : α, L.toFun x ≠ L'.toFun x := by
    by_contra hAll
    push_neg at hAll
    exact h (OneThird.LinearExt.ext (Equiv.ext hAll))
  set y : α := L.toFun.symm (L'.toFun x) with hy_def
  have hxy_ne : x ≠ y := by
    intro heq
    apply hx
    have : L.toFun y = L'.toFun x := L.toFun.apply_symm_apply (L'.toFun x)
    rw [← heq] at this
    exact this
  -- Show `chamber L ∩ chamber L' ⊆ {f | f x = f y}`.
  have hsub : chamber L ∩ chamber L' ⊆
      (equalCoordSubmoduleAlpha (α := α) x y : Set (α → ℝ)) := by
    rintro f ⟨hfL, hfL'⟩
    -- Both `f ∘ L.toFun.symm` and `f ∘ L'.toFun.symm` are monotone Fin n → ℝ.
    have hmono_L : Monotone (fun i : Fin (Fintype.card α) => f (L.toFun.symm i)) := by
      intro i j hij
      apply hfL.2
      change L.toFun (L.toFun.symm i) ≤ L.toFun (L.toFun.symm j)
      rw [L.toFun.apply_symm_apply, L.toFun.apply_symm_apply]
      exact hij
    have hmono_L' : Monotone (fun i : Fin (Fintype.card α) => f (L'.toFun.symm i)) := by
      intro i j hij
      apply hfL'.2
      change L'.toFun (L'.toFun.symm i) ≤ L'.toFun (L'.toFun.symm j)
      rw [L'.toFun.apply_symm_apply, L'.toFun.apply_symm_apply]
      exact hij
    -- Apply Tuple.unique_monotone with the same target tuple `f ∘ L.toFun.symm`
    -- and the two perms `id` and `L.toFun ∘ L'.toFun.symm` (as Fin n → Fin n).
    let F : Fin (Fintype.card α) → ℝ := fun i => f (L.toFun.symm i)
    let τ : Equiv.Perm (Fin (Fintype.card α)) := L'.toFun.symm.trans L.toFun
    have hτ_apply : ∀ i, F (τ i) = f (L'.toFun.symm i) := by
      intro i
      change f (L.toFun.symm (L.toFun (L'.toFun.symm i))) = f (L'.toFun.symm i)
      rw [L.toFun.symm_apply_apply]
    have hF_id_mono : Monotone (F ∘ (Equiv.refl (Fin (Fintype.card α)))) := by
      simpa using hmono_L
    have hF_τ_mono : Monotone (F ∘ τ) := by
      intro i j hij
      simp only [Function.comp_apply, hτ_apply]
      exact hmono_L' hij
    have hEq : F ∘ (Equiv.refl _) = F ∘ τ :=
      Tuple.unique_monotone hF_id_mono hF_τ_mono
    have hEvAt : (F ∘ (Equiv.refl (Fin (Fintype.card α)))) (L'.toFun x) =
        (F ∘ τ) (L'.toFun x) := congrFun hEq (L'.toFun x)
    -- LHS of hEvAt: F (L'.toFun x) = f (L.toFun.symm (L'.toFun x)) = f y.
    -- RHS of hEvAt: F (τ (L'.toFun x)) = f (L'.toFun.symm (L'.toFun x)) = f x.
    have hLHS_eq_fy : (F ∘ (Equiv.refl (Fin (Fintype.card α)))) (L'.toFun x) = f y := rfl
    have hRHS_eq_fx : (F ∘ τ) (L'.toFun x) = f x := by
      change F (τ (L'.toFun x)) = f x
      rw [hτ_apply, L'.toFun.symm_apply_apply]
    change f x = f y
    -- f x = (F ∘ τ) (L'.toFun x) = (F ∘ id) (L'.toFun x) = f y.
    rw [← hRHS_eq_fx, ← hEvAt, hLHS_eq_fy]
  exact measure_mono_null hsub (volume_equalCoordSubmoduleAlpha hxy_ne)

/-! #### §11.3 — Master volume theorem `Vol(O(α)) = e(α) / n!`. -/

/-- **Stanley 1986 Corollary 1.4.** The Lebesgue volume of the order polytope
`O(α)` equals `e(α) / n!`, where `e(α) := numLinExt α` is the number of
linear extensions of `α` and `n := |α|`.

Proof: by `chamber_cover`, `O(α)` is the union of the chambers; the family
is AE-disjoint by `chamber_inter_meas_zero` and each chamber is measurable
(`measurableSet_chamber`); summing gives `numLinExt α · (1 / n!)` via
`measure_biUnion_finset₀` and `chamber_volume`. -/
theorem orderPolytope_volume :
    volume (OrderPolytope α : Set (α → ℝ)) =
      ENNReal.ofReal ((numLinExt α : ℝ) /
        (Nat.factorial (Fintype.card α) : ℝ)) := by
  classical
  rw [chamber_cover]
  -- Convert the type-level i-union to a finset bi-union.
  rw [show (⋃ L : OneThird.LinearExt α, chamber L) =
      ⋃ L ∈ (Finset.univ : Finset (OneThird.LinearExt α)), chamber L by
      ext f; simp]
  -- AE-disjoint family.
  have hAE : Set.Pairwise ((Finset.univ : Finset (OneThird.LinearExt α)) :
        Set (OneThird.LinearExt α))
      (AEDisjoint volume on (chamber : OneThird.LinearExt α → Set (α → ℝ))) :=
    fun L _ L' _ hLL' => chamber_inter_meas_zero hLL'
  have hMble : ∀ L ∈ (Finset.univ : Finset (OneThird.LinearExt α)),
      NullMeasurableSet (chamber L) volume :=
    fun L _ => (measurableSet_chamber L).nullMeasurableSet
  rw [measure_biUnion_finset₀ hAE hMble]
  -- Sum each chamber's volume = 1/n!.
  simp only [chamber_volume]
  rw [Finset.sum_const, Finset.card_univ]
  -- Reduce `card • ENNReal.ofReal (1/n!)` to `ENNReal.ofReal (numLinExt / n!)`.
  unfold numLinExt
  rw [nsmul_eq_mul]
  have hcard_nn : (0 : ℝ) ≤ (Fintype.card (OneThird.LinearExt α) : ℝ) :=
    Nat.cast_nonneg _
  rw [show ((Fintype.card (OneThird.LinearExt α) : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((Fintype.card (OneThird.LinearExt α) : ℝ)) from
      (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_mul hcard_nn]
  congr 1
  ring

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

instance : Fintype Three := ⟨{Three.a, Three.b, Three.c}, by intro x; cases x <;> decide⟩

/-- **Hand-verification: discrete 3-antichain chamber volume.** For
`Three = {a, b, c}` discrete, each of the `3! = 6` chambers has volume
`1/6 = 1/3!`. -/
example (L : OneThird.LinearExt Three) :
    MeasureTheory.volume (OrderPolytope.chamber L) =
      ENNReal.ofReal (1 / 6) := by
  rw [OrderPolytope.chamber_volume]
  rfl

/-- **Hand-verification: discrete 3-antichain order polytope volume.** For
`Three = {a, b, c}` discrete with `numLinExt Three = 3! = 6`, the order
polytope has volume `6 / 6 = 1`, matching `Vol([0,1]^3) = 1`. -/
example : MeasureTheory.volume (OrderPolytope Three : Set (Three → ℝ)) =
    ENNReal.ofReal ((numLinExt Three : ℝ) / 6) := by
  rw [OrderPolytope.orderPolytope_volume]
  rfl

end LinearExt
end OneThird
