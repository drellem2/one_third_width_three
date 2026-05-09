/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.Order.Group.Indicator

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
