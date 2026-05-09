/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Lattice

/-!
# Continuous FKG / Ahlswede–Daykin on `[0,1]^n` (Session B prelude)

This file ports the discrete Fortuin–Kastelyn–Ginibre (FKG) and
Ahlswede–Daykin (4FT) inequalities from a finite distributive lattice
to the dyadic-style sub-lattice `D_N^n := {0, 1/N, …, 1}^n ⊂ [0,1]^n`,
canonically isomorphic to `(Fin (N+1))^n`. It then introduces the
step-function approximation `stepLower` of a function on the cube and
proves the basic monotonicity / sandwich properties that bridge the
discrete sums to the Lebesgue integral.

This is Session B of the **EX-6 continuous FKG** arc (sub-α-C):
Session A was the latex-first scoping (`docs/path-alpha-execution-arc/
ex6-continuous-fkg-scoping.md`); Session C will close the Riemann-sum
limit via dominated convergence to give the master continuous-FKG
theorem on `[0,1]^n`.

## Main declarations

* `OneThird.ContinuousFKG.gridFn` — restriction of `f : (Fin n → ℝ) →
  ℝ` to the dyadic-style grid, evaluated at index
  `k : Fin n → Fin (N+1)`.
* `OneThird.ContinuousFKG.gridFn_monotone` — pointwise monotonicity of
  `gridFn` follows from monotonicity of `f` (Session B prelude).
* `OneThird.ContinuousFKG.gridFn_inf` / `gridFn_sup` — the lattice
  operations on the grid commute with `gridFn` (i.e., grid evaluation
  is a lattice homomorphism).
* `OneThird.ContinuousFKG.fkg_discrete_pi` — **Discrete FKG on
  `(Fin (N+1))^n` for the uniform measure**, the Riemann-sum form.
  Specialisation of mathlib `fkg` with `μ ≡ 1`. **(§5.1 deliverable.)**
* `OneThird.ContinuousFKG.ad_discrete_pi` — Discrete AD (4FT) on
  `(Fin (N+1))^n`, specialisation of mathlib
  `four_functions_theorem_univ`.
* `OneThird.ContinuousFKG.stepRetract` — the lower-corner retraction
  `p_N : (Fin n → ℝ) → (Fin n → ℝ)`, `p_N(x)_i = ⌊N x_i⌋ / N` (clipped
  to the cube on the upper face).
* `OneThird.ContinuousFKG.stepLower` — `stepLower N f x := f
  (stepRetract N x)`, the lower step-function approximation.
* `OneThird.ContinuousFKG.stepLower_le_self` — sandwich on the cube:
  `stepLower N f x ≤ f x` for monotone `f`.

## Source location and upstream PR target

This file is structured for upstream extraction to mathlib as
`Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean` (DH-4 candidate;
see `docs/path-alpha-execution-arc/ex6-continuous-fkg-scoping.md` §7).
The sub-namespace `OneThird.ContinuousFKG` is the in-tree placeholder
for the upstream `Analysis.MeanInequalities.ContinuousFKG` namespace.

## References

* [Preston1974] C. J. Preston, *Spatial birth-and-death processes*,
  Adv. Appl. Probab. **6** (1974), 391–403, Theorem 5.4.
* [AD78] R. Ahlswede and D. E. Daykin, *An inequality for the weights
  of two families of sets, their unions and intersections*, Z. Wahrsch.
  verw. Gebiete **43** (1978), 183–185.
* [Brightwell1999] G. R. Brightwell, *Balanced pairs in partial orders*,
  Discrete Math. **201** (1999), 25–52, §4.
-/

namespace OneThird.ContinuousFKG

open MeasureTheory Finset

variable {n : ℕ}

/-! ### §1 — The grid restriction `gridFn` and its properties -/

section GridFn

/-- Restriction of a function `f : (Fin n → ℝ) → ℝ` to the
dyadic-style grid `D_N^n = {0, 1/N, …, 1}^n`, evaluated at the index
`k : Fin n → Fin (N+1)`.

For `N = 0` the grid is the singleton `{0}^n` (every `Fin 1` value
maps to `0/0 = 0` by `Real`-division convention). The interesting
range is `N ≥ 1`, in which case the image of `gridFn N` covers
`D_N^n ⊂ [0,1]^n`. -/
noncomputable def gridFn (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → Fin (N + 1)) → ℝ :=
  fun k => f (fun i => (k i : ℝ) / (N : ℝ))

/-- The grid index point as a real-valued vector. -/
noncomputable def gridPoint (N : ℕ) (k : Fin n → Fin (N + 1)) : Fin n → ℝ :=
  fun i => (k i : ℝ) / (N : ℝ)

@[simp] lemma gridFn_apply (N : ℕ) (f : (Fin n → ℝ) → ℝ)
    (k : Fin n → Fin (N + 1)) :
    gridFn N f k = f (gridPoint N k) := rfl

@[simp] lemma gridPoint_apply (N : ℕ) (k : Fin n → Fin (N + 1)) (i : Fin n) :
    gridPoint N k i = (k i : ℝ) / (N : ℝ) := rfl

/-- The cast `Fin (N+1) → ℕ` commutes with `min` (i.e. `⊓` on the
`LinearOrder Fin (N+1)`). -/
private lemma fin_val_inf {N : ℕ} (a b : Fin (N + 1)) :
    ((a ⊓ b : Fin (N + 1)) : ℕ) = min (a : ℕ) (b : ℕ) := by
  rcases le_total a b with h | h
  · simp [inf_eq_left.mpr h, min_eq_left (Fin.le_iff_val_le_val.mp h)]
  · simp [inf_eq_right.mpr h, min_eq_right (Fin.le_iff_val_le_val.mp h)]

/-- The cast `Fin (N+1) → ℕ` commutes with `max` (i.e. `⊔` on the
`LinearOrder Fin (N+1)`). -/
private lemma fin_val_sup {N : ℕ} (a b : Fin (N + 1)) :
    ((a ⊔ b : Fin (N + 1)) : ℕ) = max (a : ℕ) (b : ℕ) := by
  rcases le_total a b with h | h
  · simp [sup_eq_right.mpr h, max_eq_right (Fin.le_iff_val_le_val.mp h)]
  · simp [sup_eq_left.mpr h, max_eq_left (Fin.le_iff_val_le_val.mp h)]

/-- The lattice operation `⊓` on `Fin (N+1)` (which is `min`) commutes
with `gridPoint`: the inf of two grid indices maps to the pointwise
min of the corresponding grid points. -/
lemma gridPoint_inf (N : ℕ) (k l : Fin n → Fin (N + 1)) :
    gridPoint N (k ⊓ l) = gridPoint N k ⊓ gridPoint N l := by
  funext i
  simp only [gridPoint_apply, Pi.inf_apply]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- (((k ⊓ l) i : ℕ) : ℝ)/N = min ((k i : ℕ) : ℝ)/N ((l i : ℕ) : ℝ)/N
  rw [show ((((k i ⊓ l i : Fin (N + 1)) : ℕ) : ℝ)) = ((min (k i : ℕ) (l i : ℕ) : ℕ) : ℝ) by
        rw [fin_val_inf]]
  rcases le_total (k i : ℕ) (l i : ℕ) with hle | hle
  · have hcast : ((k i : ℕ) : ℝ) ≤ ((l i : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.min_eq_left hle]
    rw [min_eq_left]
    exact div_le_div_of_nonneg_right hcast hN'.le
  · have hcast : ((l i : ℕ) : ℝ) ≤ ((k i : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.min_eq_right hle]
    rw [min_eq_right]
    exact div_le_div_of_nonneg_right hcast hN'.le

/-- The lattice operation `⊔` on `Fin (N+1)` (which is `max`) commutes
with `gridPoint`. -/
lemma gridPoint_sup (N : ℕ) (k l : Fin n → Fin (N + 1)) :
    gridPoint N (k ⊔ l) = gridPoint N k ⊔ gridPoint N l := by
  funext i
  simp only [gridPoint_apply, Pi.sup_apply]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [show ((((k i ⊔ l i : Fin (N + 1)) : ℕ) : ℝ)) = ((max (k i : ℕ) (l i : ℕ) : ℕ) : ℝ) by
        rw [fin_val_sup]]
  rcases le_total (k i : ℕ) (l i : ℕ) with hle | hle
  · have hcast : ((k i : ℕ) : ℝ) ≤ ((l i : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.max_eq_right hle]
    rw [max_eq_right]
    exact div_le_div_of_nonneg_right hcast hN'.le
  · have hcast : ((l i : ℕ) : ℝ) ≤ ((k i : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.max_eq_left hle]
    rw [max_eq_left]
    exact div_le_div_of_nonneg_right hcast hN'.le

/-- `gridFn` of a non-negative function is non-negative. -/
lemma gridFn_nonneg {N : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : 0 ≤ f) : 0 ≤ gridFn N f := fun _ => hf _

/-- `gridFn` is monotone whenever `f` is monotone (componentwise on
`Fin n → ℝ`). The proof transports the order:
`k ≤ l` (componentwise on `Fin (N+1)`) ⟹
`(k i : ℝ)/N ≤ (l i : ℝ)/N` for each `i`. -/
lemma gridFn_monotone {N : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Monotone f) : Monotone (gridFn N f) := by
  intro k l hkl
  apply hf
  intro i
  have hi : (k i : ℕ) ≤ (l i : ℕ) := Fin.le_iff_val_le_val.mp (hkl i)
  have hi' : ((k i : ℕ) : ℝ) ≤ ((l i : ℕ) : ℝ) := by exact_mod_cast hi
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hN' : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
    exact div_le_div_of_nonneg_right hi' hN'

/-- `gridFn` distributes over multiplication: `gridFn N (f * g) =
gridFn N f * gridFn N g`. (Pointwise: both sides evaluate `f` and `g`
at the same grid point.) -/
@[simp] lemma gridFn_mul (N : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    gridFn N (f * g) = gridFn N f * gridFn N g := by
  funext k; simp [gridFn, Pi.mul_apply]

/-- `gridFn` distributes over the lattice operation `f ⊓ g`. -/
@[simp] lemma gridFn_inf (N : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    gridFn N (f ⊓ g) = gridFn N f ⊓ gridFn N g := by
  funext k; simp [gridFn, Pi.inf_apply]

/-- `gridFn` distributes over the lattice operation `f ⊔ g`. -/
@[simp] lemma gridFn_sup (N : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    gridFn N (f ⊔ g) = gridFn N f ⊔ gridFn N g := by
  funext k; simp [gridFn, Pi.sup_apply]

end GridFn

/-! ### §2 — Discrete FKG / AD on `(Fin (N+1))^n` (§5.1 deliverable) -/

section DiscreteFKG

/-- **Discrete FKG on `(Fin (N+1))^n` (uniform measure, Riemann-sum
form).** For non-negative monotone `f, g : (Fin n → ℝ) → ℝ`,

```
(∑ k, gridFn N f k) · (∑ k, gridFn N g k)
    ≤ (N+1)^n · (∑ k, (gridFn N f k) · (gridFn N g k)).
```

This is mathlib `fkg` specialised to the uniform measure `μ ≡ 1` on
the finite distributive lattice `Fin n → Fin (N+1)`. After dividing
both sides by `(N+1)^{2n}`, this is the Riemann-sum form of FKG with
`(N+1)^n` quadrature points; the `N → ∞` limit (Session C) gives
continuous FKG on `[0,1]^n`. -/
theorem fkg_discrete_pi {N : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ k : Fin n → Fin (N + 1), gridFn N f k) *
        (∑ k : Fin n → Fin (N + 1), gridFn N g k)
    ≤ ((N + 1 : ℝ) ^ n) *
        (∑ k : Fin n → Fin (N + 1), gridFn N f k * gridFn N g k) := by
  classical
  -- Apply mathlib `fkg` with μ ≡ 1.
  have hcard : Fintype.card (Fin n → Fin (N + 1)) = (N + 1) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h := fkg (μ := fun _ : Fin n → Fin (N + 1) => (1 : ℝ))
                (gridFn N f) (gridFn N g)
                (fun _ => zero_le_one) (gridFn_nonneg hf₀) (gridFn_nonneg hg₀)
                (gridFn_monotone hf) (gridFn_monotone hg)
                (fun _ _ => by simp)
  -- Simplify `μ = 1`: `Σ μ * h = Σ h`, `Σ μ = card = (N+1)^n`.
  simp only [one_mul] at h
  have hsum : (∑ _ : Fin n → Fin (N + 1), (1 : ℝ)) = ((N + 1 : ℝ) ^ n) := by
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one]
    push_cast; rfl
  rw [hsum] at h
  exact h

/-- **Discrete Ahlswede–Daykin (4FT) on `(Fin (N+1))^n` (uniform
measure form).** For non-negative `f₁, f₂, f₃, f₄ : (Fin n → ℝ) → ℝ`
satisfying the AD lattice hypothesis on the cube,

```
(∑ k, gridFn N f₁ k) · (∑ k, gridFn N f₂ k)
    ≤ (∑ k, gridFn N f₃ k) · (∑ k, gridFn N f₄ k).
```

The lattice hypothesis transports from `(Fin n → ℝ)` (the cube)
to `(Fin n → Fin (N+1))` (the grid index) via the `gridPoint`
lattice homomorphism (`gridPoint_inf`, `gridPoint_sup`). -/
theorem ad_discrete_pi {N : ℕ}
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (hf₃ : 0 ≤ f₃) (hf₄ : 0 ≤ f₄)
    (hAD : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∑ k : Fin n → Fin (N + 1), gridFn N f₁ k) *
        (∑ k : Fin n → Fin (N + 1), gridFn N f₂ k)
    ≤ (∑ k : Fin n → Fin (N + 1), gridFn N f₃ k) *
        (∑ k : Fin n → Fin (N + 1), gridFn N f₄ k) := by
  classical
  -- Apply mathlib `four_functions_theorem_univ` to the grid restrictions.
  -- The lattice hypothesis transports via `gridPoint_inf` / `gridPoint_sup`.
  refine four_functions_theorem_univ
    (gridFn N f₁) (gridFn N f₂) (gridFn N f₃) (gridFn N f₄)
    (gridFn_nonneg hf₁) (gridFn_nonneg hf₂) (gridFn_nonneg hf₃) (gridFn_nonneg hf₄)
    (fun k l => ?_)
  -- Translate the lattice hypothesis on the cube to the grid.
  have hkl_inf : gridPoint N (k ⊓ l) = gridPoint N k ⊓ gridPoint N l :=
    gridPoint_inf N k l
  have hkl_sup : gridPoint N (k ⊔ l) = gridPoint N k ⊔ gridPoint N l :=
    gridPoint_sup N k l
  simp only [gridFn_apply, hkl_inf, hkl_sup]
  exact hAD (gridPoint N k) (gridPoint N l)

end DiscreteFKG

/-! ### §3 — The lower-step retraction `stepRetract` and step
function `stepLower` (§5.2 prelude) -/

section StepFunction

/-- The lower-corner retraction `p_N : (Fin n → ℝ) → (Fin n → ℝ)`,
sending `x` to its lower-corner grid point in `D_N^n = {0, 1/N, …,
1}^n`. Componentwise:

```
stepRetract N x i = (min ⌊N x_i⌋ N : ℝ) / N,
```

with the `min ⌊N x_i⌋ N` clipping ensuring that `x_i = 1` (or
slightly above) is mapped to `1` (i.e., `N/N`) rather than past the
upper face. -/
noncomputable def stepRetract (N : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ((min (Nat.floor (N * x i)) N : ℕ) : ℝ) / (N : ℝ)

/-- The **lower-step approximation** of `f` at refinement `N`. -/
noncomputable def stepLower (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => f (stepRetract N x)

@[simp] lemma stepLower_apply (N : ℕ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    stepLower N f x = f (stepRetract N x) := rfl

/-- For `x ∈ [0,1]^n` and `N ≥ 1`, the retracted point lies coordinate-
wise below `x`: `stepRetract N x i ≤ x i`. This is the lower-half of
the sandwich `stepLower N f x ≤ f x ≤ stepUpper N f x` for monotone
`f`. -/
lemma stepRetract_le_self {N : ℕ} (hN : 1 ≤ N) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (i : Fin n) :
    stepRetract N x i ≤ x i := by
  -- Two cases on `min (Nat.floor (N * x i)) N`.
  obtain ⟨hxi₀, hxi₁⟩ := hx i
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNx_nn : 0 ≤ (N : ℝ) * x i := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le N) hxi₀
  have hfloor_le : ((Nat.floor ((N : ℝ) * x i) : ℕ) : ℝ) ≤ (N : ℝ) * x i :=
    Nat.floor_le hNx_nn
  unfold stepRetract
  -- `min (Nat.floor (N * x i)) N : ℕ` cast to ℝ is at most the floor.
  have : ((min (Nat.floor ((N : ℝ) * x i)) N : ℕ) : ℝ)
        ≤ ((Nat.floor ((N : ℝ) * x i) : ℕ) : ℝ) := by
    exact_mod_cast Nat.min_le_left _ _
  calc ((min (Nat.floor ((N : ℝ) * x i)) N : ℕ) : ℝ) / (N : ℝ)
      ≤ ((Nat.floor ((N : ℝ) * x i) : ℕ) : ℝ) / (N : ℝ) := by
            exact div_le_div_of_nonneg_right this hN'.le
    _ ≤ ((N : ℝ) * x i) / (N : ℝ) := by
            exact div_le_div_of_nonneg_right hfloor_le hN'.le
    _ = x i := by field_simp

/-- For `x ∈ [0,1]^n` and `N ≥ 1`, the retracted point lies in the
unit cube: `0 ≤ stepRetract N x i ≤ 1`. -/
lemma stepRetract_mem_cube {N : ℕ} (hN : 1 ≤ N) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (i : Fin n) :
    0 ≤ stepRetract N x i ∧ stepRetract N x i ≤ 1 := by
  obtain ⟨hxi₀, hxi₁⟩ := hx i
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · unfold stepRetract
    exact div_nonneg (by exact_mod_cast Nat.zero_le _) hN'.le
  · unfold stepRetract
    have : ((min (Nat.floor ((N : ℝ) * x i)) N : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.min_le_right _ _
    rw [div_le_one hN']; exact this

/-- **Sandwich (lower half).** For `x ∈ [0,1]^n` and `N ≥ 1`, if `f`
is coordinate-monotone on `Fin n → ℝ`, then `stepLower N f x ≤ f x`. -/
lemma stepLower_le_self {N : ℕ} (hN : 1 ≤ N) {f : (Fin n → ℝ) → ℝ}
    (hf : Monotone f) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    stepLower N f x ≤ f x := by
  apply hf
  intro i
  exact stepRetract_le_self hN hx i

/-- The retracted point is non-negative on the cube. -/
lemma stepRetract_nonneg {N : ℕ} (hN : 1 ≤ N) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ stepRetract N x := fun i => (stepRetract_mem_cube hN hx i).1

/-- For non-negative monotone `f`, the lower step is non-negative. -/
lemma stepLower_nonneg {N : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (x : Fin n → ℝ) :
    0 ≤ stepLower N f x := hf₀ _

/-- **Boundedness on the cube.** For monotone non-negative `f` and
`x ∈ [0,1]^n`, `stepLower N f x ≤ f 1`. (Combined with `0 ≤
stepLower`, this gives the L∞ bound used in the dominated-convergence
limit, Session C.) -/
lemma stepLower_le_top {N : ℕ} (hN : 1 ≤ N) {f : (Fin n → ℝ) → ℝ}
    (hf : Monotone f) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    stepLower N f x ≤ f (fun _ => 1) := by
  apply hf
  intro i
  exact (stepRetract_mem_cube hN hx i).2

end StepFunction

/-! ### §4 — Riemann-sum identity (Option A; integer sub-grid)

The lower-step integral on the cube equals the left-endpoint Riemann
sum at the `N^n`-grid `(Fin N)^n` modulo a measure-zero correction at
the upper face `x_i = 1`. The full proof of the integral identity is
deferred to Session C; we record here the supporting cell-decomposition
infrastructure and the Riemann-sum statement.

The key fact for the Session C limit argument is that, modulo a
volume-zero correction at the upper face, the lower-step integrand
`stepLower N f` is constant on each open cell

```
C_k := { x ∈ (0,1)^n | k_i / N ≤ x_i < (k_i + 1) / N for k_i : Fin N }
```

with value `f (k/N)`, and the cells partition `(0,1)^n` (a full-volume
subset of `[0,1]^n`). The integral therefore equals
`Σ_{k ∈ (Fin N)^n} f(k/N) · vol(C_k) = (1/N)^n · Σ_{k} f(k/N)`. -/

section RiemannSum

/-- **Cell volume identity.** For `N ≥ 1` and `k : Fin n → Fin N`, the
half-open cell `∏_i [k_i/N, (k_i+1)/N)` has Lebesgue volume `(1/N)^n`.

This is the per-cell building block of the Riemann-sum identity; it
specialises `MeasureTheory.volume_pi_pi` + `Real.volume_Ico` to a
cell of width `1/N` in each coordinate. -/
lemma volume_cell {N : ℕ} (hN : 1 ≤ N) (k : Fin n → Fin N) :
    (volume : Measure (Fin n → ℝ))
        (Set.univ.pi (fun i => Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N)))
      = ENNReal.ofReal (1 / (N : ℝ) ^ n) := by
  classical
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [volume_pi_pi]
  -- Each factor has volume (1/N) on ℝ.
  have hfac : ∀ i, volume (Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N))
                = ENNReal.ofReal (1 / (N : ℝ)) := by
    intro i
    rw [Real.volume_Ico]
    congr 1
    rw [show (((k i : ℝ) + 1) / (N : ℝ)) - ((k i : ℝ) / (N : ℝ))
            = ((k i : ℝ) + 1 - (k i : ℝ)) / (N : ℝ) by ring]
    ring_nf
  simp_rw [hfac]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [div_pow, one_pow]

/-- **Floor-on-cell identity.** For `N ≥ 1`, if `(k : ℝ)/N ≤ x` and
`x < (k+1)/N` for `k : Fin N`, then `Nat.floor (N · x) = k`. -/
private lemma floor_mul_eq_of_mem_cell {N : ℕ} (hN : 1 ≤ N) (k : Fin N)
    {x : ℝ} (hx_lo : ((k : ℝ) / N) ≤ x) (hx_hi : x < (((k : ℝ) + 1) / N)) :
    Nat.floor ((N : ℝ) * x) = (k : ℕ) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkN : ((k : ℕ) : ℝ) ≤ (N : ℝ) * x := by
    have hmul := mul_le_mul_of_nonneg_left hx_lo hN'.le
    have hsimp : ((N : ℝ) * (((k : ℕ) : ℝ) / (N : ℝ))) = ((k : ℕ) : ℝ) := by
      field_simp
    rw [hsimp] at hmul
    exact hmul
  have hkNlt : (N : ℝ) * x < (((k : ℕ) : ℝ) + 1) := by
    have hmul := mul_lt_mul_of_pos_left hx_hi hN'
    have hsimp : ((N : ℝ) * ((((k : ℕ) : ℝ) + 1) / (N : ℝ))) = (((k : ℕ) : ℝ) + 1) := by
      field_simp
    rw [hsimp] at hmul
    exact hmul
  have hxnn : (0 : ℝ) ≤ (N : ℝ) * x :=
    le_trans (by exact_mod_cast (Nat.zero_le _ : 0 ≤ (k : ℕ))) hkN
  rw [Nat.floor_eq_iff hxnn]
  refine ⟨hkN, ?_⟩
  exact_mod_cast hkNlt

/-- **Step-retract on cell.** For `N ≥ 1`, if `x` lies in the open cell
`∏_i [k_i/N, (k_i+1)/N)` with `k : Fin n → Fin N`, then
`stepRetract N x = (k/N : Fin n → ℝ)` componentwise. -/
lemma stepRetract_eq_of_mem_cell
    {N : ℕ} (hN : 1 ≤ N) (k : Fin n → Fin N) {x : Fin n → ℝ}
    (hx : ∀ i, ((k i : ℝ) / N) ≤ x i ∧ x i < (((k i : ℝ) + 1) / N))
    (i : Fin n) :
    stepRetract N x i = ((k i : ℝ) / N) := by
  obtain ⟨hxi_lo, hxi_hi⟩ := hx i
  have hfloor : Nat.floor ((N : ℝ) * x i) = ((k i : Fin N) : ℕ) :=
    floor_mul_eq_of_mem_cell hN (k i) hxi_lo hxi_hi
  have hki_lt : ((k i : Fin N) : ℕ) < N := (k i).isLt
  unfold stepRetract
  rw [hfloor, min_eq_left hki_lt.le]

/-- **Constancy of `stepLower` on each cell.** For `N ≥ 1`, if `x` lies
in the cell `∏_i [k_i/N, (k_i+1)/N)` with `k : Fin n → Fin N`, then
`stepLower N f x = f(k/N)`.

The cell-decomposition core: each grid cell of width `1/N` retracts
to the same lower-corner grid point under `stepRetract N`. The
floor-on-cell identity (`floor_mul_eq_of_mem_cell`) does the work;
clipping on the upper face is unnecessary because `(k : ℕ) ≤ N - 1 <
N` for `k : Fin N`. -/
lemma stepLower_eq_of_mem_cell
    {N : ℕ} (hN : 1 ≤ N) (f : (Fin n → ℝ) → ℝ)
    (k : Fin n → Fin N) {x : Fin n → ℝ}
    (hx : ∀ i, ((k i : ℝ) / N) ≤ x i ∧ x i < (((k i : ℝ) + 1) / N)) :
    stepLower N f x = f (fun i => ((k i : ℝ) / N)) := by
  unfold stepLower
  congr 1
  funext i
  exact stepRetract_eq_of_mem_cell hN k hx i

/-- **1D cell tiling.** For `N ≥ 1`, the unit half-open interval
`[0,1)` is the disjoint union of the `N` half-open cells
`[j/N, (j+1)/N)` for `j : Fin N`. -/
private lemma Ico_zero_one_eq_iUnion_cells {N : ℕ} (hN : 1 ≤ N) :
    Set.Ico (0 : ℝ) 1
      = ⋃ j : Fin N, Set.Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  ext x
  simp only [Set.mem_Ico, Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  · rintro ⟨hx0, hx1⟩
    have hNxnn : 0 ≤ (N : ℝ) * x := mul_nonneg hN'.le hx0
    have hfloor_lt_N : Nat.floor ((N : ℝ) * x) < N := by
      rw [Nat.floor_lt hNxnn]
      have : (N : ℝ) * x < (N : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 hN'
      simpa using this
    refine ⟨⟨Nat.floor ((N : ℝ) * x), hfloor_lt_N⟩, ?_, ?_⟩
    · -- (j : ℝ)/N ≤ x
      have hj_le : ((Nat.floor ((N : ℝ) * x) : ℕ) : ℝ) ≤ (N : ℝ) * x :=
        Nat.floor_le hNxnn
      change ((((⟨Nat.floor ((N : ℝ) * x), hfloor_lt_N⟩ : Fin N) : ℕ) : ℝ)) / (N : ℝ) ≤ x
      rw [div_le_iff₀ hN']
      linarith
    · -- x < (j+1)/N
      have hj_gt : (N : ℝ) * x < (Nat.floor ((N : ℝ) * x) : ℕ) + 1 :=
        Nat.lt_floor_add_one _
      change x < ((((⟨Nat.floor ((N : ℝ) * x), hfloor_lt_N⟩ : Fin N) : ℕ) : ℝ) + 1) / (N : ℝ)
      rw [lt_div_iff₀ hN']
      linarith
  · rintro ⟨j, hjlow, hjhi⟩
    refine ⟨?_, ?_⟩
    · -- 0 ≤ x
      exact le_trans (div_nonneg (by exact_mod_cast Nat.zero_le _) hN'.le) hjlow
    · -- x < 1
      have hj_le_N : ((j : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
        have : (j : ℕ) + 1 ≤ N := j.isLt
        exact_mod_cast this
      have h_one : (((j : ℕ) : ℝ) + 1) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hN']; exact hj_le_N
      linarith

/-- **Cell pairwise disjointness.** For distinct `k, l : Fin n → Fin N`
with `N ≥ 1`, the cells `∏_i [k_i/N, (k_i+1)/N)` and
`∏_i [l_i/N, (l_i+1)/N)` are disjoint. -/
private lemma cell_disjoint {N : ℕ} (hN : 1 ≤ N) :
    Pairwise (Function.onFun Disjoint
      (fun k : Fin n → Fin N =>
        Set.univ.pi (fun i =>
          Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N)))) := by
  intro k l hkl
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by
    by_contra hall
    apply hkl
    funext i
    exact not_not.mp (fun hne => hall ⟨i, hne⟩)
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hk hl
  have hki := hk i
  have hli := hl i
  have hi_val : (k i : ℕ) ≠ (l i : ℕ) := fun h => hi (Fin.ext h)
  rcases lt_or_gt_of_ne hi_val with h | h
  · -- (k i : ℕ) < (l i : ℕ): so (k i + 1) ≤ l i, so (k i+1)/N ≤ l i/N.
    have h_succ : ((k i : ℕ) : ℝ) + 1 ≤ ((l i : ℕ) : ℝ) := by exact_mod_cast h
    have hx_lt : x i < (((k i : ℕ) : ℝ) + 1) / N := hki.2
    have hx_ge : ((l i : ℕ) : ℝ) / N ≤ x i := hli.1
    have hsucc_le : (((k i : ℕ) : ℝ) + 1) / N ≤ ((l i : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right h_succ hN'.le
    linarith
  · have h_succ : ((l i : ℕ) : ℝ) + 1 ≤ ((k i : ℕ) : ℝ) := by exact_mod_cast h
    have hx_lt : x i < (((l i : ℕ) : ℝ) + 1) / N := hli.2
    have hx_ge : ((k i : ℕ) : ℝ) / N ≤ x i := hki.1
    have hsucc_le : (((l i : ℕ) : ℝ) + 1) / N ≤ ((k i : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right h_succ hN'.le
    linarith

/-- **Riemann sum identity.** For `N ≥ 1`, the
left-endpoint Riemann sum of `f` over the `N^n`-grid `(Fin N)^n`
equals the integral of the step function `stepLower N f` over the
half-open cube `[0,1)^n`:

```
∫_{x ∈ [0,1)^n} stepLower N f x ∂volume
  = (1/N^n) · ∑_{k : Fin n → Fin N} f(k/N).
```

The proof decomposes `[0,1)^n` into the disjoint cells `C_k`
(`k : Fin n → Fin N`), each of volume `(1/N)^n`, on each of which the
step function `stepLower N f` is constant with value `f(k/N)`. -/
theorem integral_stepLower_eq_riemann
    {N : ℕ} (hN : 1 ≤ N) (f : (Fin n → ℝ) → ℝ) :
    ∫ x in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
        stepLower N f x ∂volume
      = (1 / (N : ℝ) ^ n) *
          ∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N) := by
  classical
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- The cell map.
  set cellSet : (Fin n → Fin N) → Set (Fin n → ℝ) := fun k =>
    Set.univ.pi (fun i => Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N))
    with hcellSet_def
  -- Cells are measurable.
  have hcell_meas : ∀ k, MeasurableSet (cellSet k) :=
    fun k => MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  -- Cells are pairwise disjoint.
  have hcell_disj : Pairwise (Function.onFun Disjoint cellSet) := cell_disjoint hN
  -- Cells union to [0,1)^n.
  have hcell_union :
      (⋃ k, cellSet k)
        = Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
    ext x
    simp only [hcellSet_def, Set.mem_iUnion, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ico]
    constructor
    · rintro ⟨k, hk⟩ i
      have := (Ico_zero_one_eq_iUnion_cells (N := N) hN).symm
      have hxi : x i ∈ ⋃ j : Fin N, Set.Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
        refine Set.mem_iUnion.mpr ⟨k i, ?_⟩
        have := hk i
        simpa [Set.mem_Ico] using this
      rw [this] at hxi
      simpa [Set.mem_Ico] using hxi
    · intro hx
      have hxi : ∀ i, ∃ j : Fin N,
          x i ∈ Set.Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
        intro i
        have hi : x i ∈ Set.Ico (0 : ℝ) 1 := by
          simp only [Set.mem_Ico]; exact hx i
        rw [Ico_zero_one_eq_iUnion_cells (N := N) hN] at hi
        exact Set.mem_iUnion.mp hi
      choose K hK using hxi
      refine ⟨K, fun i => ?_⟩
      simpa [Set.mem_Ico] using hK i
  -- On each cell, stepLower is the constant `f(k/N)`.
  have hsl_const : ∀ (k : Fin n → Fin N) {x : Fin n → ℝ}, x ∈ cellSet k →
      stepLower N f x = f (fun i => (k i : ℝ) / N) := by
    intro k x hx
    rw [hcellSet_def] at hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hx
    exact stepLower_eq_of_mem_cell hN f k hx
  -- Each cell has volume `1/N^n`.
  have hcell_vol : ∀ k, (volume : Measure (Fin n → ℝ)) (cellSet k)
                          = ENNReal.ofReal (1 / (N : ℝ) ^ n) :=
    fun k => volume_cell hN k
  have hcell_vol_real : ∀ k, (volume : Measure (Fin n → ℝ)).real (cellSet k)
                              = 1 / (N : ℝ) ^ n := by
    intro k
    rw [Measure.real, hcell_vol k, ENNReal.toReal_ofReal]
    positivity
  -- stepLower is integrable on each cell (it equals a constant there).
  have hsl_int : ∀ k, IntegrableOn (stepLower N f) (cellSet k) volume := by
    intro k
    haveI : IsFiniteMeasure (volume.restrict (cellSet k)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, hcell_vol k]
      exact ENNReal.ofReal_lt_top
    refine (integrable_const (f (fun i => (k i : ℝ) / N))).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' (hcell_meas k)]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (hsl_const k hx).symm
  -- Apply finite additivity of the integral over the cell decomposition.
  rw [← hcell_union]
  rw [integral_iUnion_fintype hcell_meas hcell_disj hsl_int]
  -- Each cell integral equals f(k/N) · vol(cell).
  have h_each : ∀ k, ∫ x in cellSet k, stepLower N f x ∂volume
                  = f (fun i => (k i : ℝ) / N) * (1 / (N : ℝ) ^ n) := by
    intro k
    rw [setIntegral_congr_fun (hcell_meas k) (fun x hx => hsl_const k hx)]
    rw [setIntegral_const, smul_eq_mul, hcell_vol_real k]
    ring
  simp_rw [h_each]
  rw [← Finset.sum_mul, mul_comm]

/-- `stepLower N f` is integrable on the half-open cube `[0,1)^n` for
any function `f`. The cell decomposition makes it a finite sum of
constants on cells of finite volume. -/
lemma integrableOn_stepLower_cube {N : ℕ} (hN : 1 ≤ N)
    (f : (Fin n → ℝ) → ℝ) :
    IntegrableOn (stepLower N f)
      (Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) volume := by
  classical
  set cellSet : (Fin n → Fin N) → Set (Fin n → ℝ) := fun k =>
    Set.univ.pi (fun i => Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N))
  have hcell_meas : ∀ k, MeasurableSet (cellSet k) :=
    fun k => MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  have hcell_vol : ∀ k, (volume : Measure (Fin n → ℝ)) (cellSet k)
                          = ENNReal.ofReal (1 / (N : ℝ) ^ n) :=
    fun k => volume_cell hN k
  have hsl_const : ∀ (k : Fin n → Fin N) {x : Fin n → ℝ}, x ∈ cellSet k →
      stepLower N f x = f (fun i => (k i : ℝ) / N) := by
    intro k x hx
    simp only [cellSet, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hx
    exact stepLower_eq_of_mem_cell hN f k hx
  have hsl_int : ∀ k, IntegrableOn (stepLower N f) (cellSet k) volume := by
    intro k
    haveI : IsFiniteMeasure (volume.restrict (cellSet k)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, hcell_vol k]
      exact ENNReal.ofReal_lt_top
    refine (integrable_const (f (fun i => (k i : ℝ) / N))).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' (hcell_meas k)]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (hsl_const k hx).symm
  -- Cells union to [0,1)^n.
  have hcell_union :
      (⋃ k, cellSet k)
        = Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
    ext x
    simp only [cellSet, Set.mem_iUnion, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ico]
    constructor
    · rintro ⟨k, hk⟩ i
      have hxi : x i ∈ ⋃ j : Fin N, Set.Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
        refine Set.mem_iUnion.mpr ⟨k i, ?_⟩
        have := hk i
        simpa [Set.mem_Ico] using this
      rw [(Ico_zero_one_eq_iUnion_cells (N := N) hN).symm] at hxi
      simpa [Set.mem_Ico] using hxi
    · intro hx
      have hxi : ∀ i, ∃ j : Fin N,
          x i ∈ Set.Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
        intro i
        have hi : x i ∈ Set.Ico (0 : ℝ) 1 := by
          simp only [Set.mem_Ico]; exact hx i
        rw [Ico_zero_one_eq_iUnion_cells (N := N) hN] at hi
        exact Set.mem_iUnion.mp hi
      choose K hK using hxi
      refine ⟨K, fun i => ?_⟩
      simpa [Set.mem_Ico] using hK i
  rw [← hcell_union]
  exact integrableOn_finite_iUnion.mpr hsl_int

end RiemannSum

/-! ### §5 — Discrete FKG on `(Fin (N))^n` (Riemann-form variant)

The `fkg_discrete_pi` theorem uses index range `Fin (N+1)` (grid
`{0, 1/N, …, 1}`). For the half-open Riemann sum (consumed by the
limit argument) we need the parallel inequality with index range
`Fin N` (grid `{0, 1/N, …, (N-1)/N}`); the cube boundary `x_i = 1` is
absorbed into the half-open cell `[0,1)`, which is a measure-zero
deviation. The proof structure mirrors `fkg_discrete_pi`. -/

section DiscreteFKGFinN

/-- Restriction to the half-open grid `{0, 1/N, …, (N-1)/N}^n ⊂
[0,1)^n`, indexed by `Fin n → Fin N` with divisor `N`. -/
noncomputable def gridFnN (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → Fin N) → ℝ :=
  fun k => f (fun i => (k i : ℝ) / (N : ℝ))

@[simp] lemma gridFnN_apply (N : ℕ) (f : (Fin n → ℝ) → ℝ)
    (k : Fin n → Fin N) :
    gridFnN N f k = f (fun i => (k i : ℝ) / (N : ℝ)) := rfl

lemma gridFnN_nonneg {N : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : 0 ≤ f) :
    0 ≤ gridFnN N f := fun _ => hf _

lemma gridFnN_monotone {N : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Monotone f) :
    Monotone (gridFnN N f) := by
  intro k l hkl
  apply hf
  intro i
  have hi : (k i : ℕ) ≤ (l i : ℕ) := Fin.le_iff_val_le_val.mp (hkl i)
  have hi' : ((k i : ℕ) : ℝ) ≤ ((l i : ℕ) : ℝ) := by exact_mod_cast hi
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hN' : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
    exact div_le_div_of_nonneg_right hi' hN'

@[simp] lemma gridFnN_mul (N : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    gridFnN N (f * g) = gridFnN N f * gridFnN N g := by
  funext k; simp [gridFnN, Pi.mul_apply]

/-- **Discrete FKG on `(Fin N)^n`**, index range `Fin N` variant. -/
theorem fkg_discrete_pi_finN {N : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ k : Fin n → Fin N, gridFnN N f k) *
        (∑ k : Fin n → Fin N, gridFnN N g k)
    ≤ ((N : ℝ) ^ n) *
        (∑ k : Fin n → Fin N, gridFnN N f k * gridFnN N g k) := by
  classical
  have hcard : Fintype.card (Fin n → Fin N) = N ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h := fkg (μ := fun _ : Fin n → Fin N => (1 : ℝ))
                (gridFnN N f) (gridFnN N g)
                (fun _ => zero_le_one) (gridFnN_nonneg hf₀) (gridFnN_nonneg hg₀)
                (gridFnN_monotone hf) (gridFnN_monotone hg)
                (fun _ _ => by simp)
  simp only [one_mul] at h
  have hsum : (∑ _ : Fin n → Fin N, (1 : ℝ)) = ((N : ℝ) ^ n) := by
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one]
    push_cast; rfl
  rw [hsum] at h
  exact h

end DiscreteFKGFinN

/-! ### §6 — `stepUpper` approximation, sandwich, and Riemann identity -/

section StepUpper

/-- The **upper-step approximation** of `f` at refinement `N`:
shifts the lower retraction by `1/N` in each coordinate before
evaluating `f`. On a cell `∏_i [k_i/N, (k_i+1)/N)` of the half-open
cube `[0,1)^n` (`k : Fin n → Fin N`), `stepUpper N f x = f((k+1)/N)`
is the upper-corner value. -/
noncomputable def stepUpper (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => f (fun i => stepRetract N x i + 1 / (N : ℝ))

@[simp] lemma stepUpper_apply (N : ℕ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    stepUpper N f x = f (fun i => stepRetract N x i + 1 / (N : ℝ)) := rfl

/-- **Upper sandwich.** For `x ∈ [0,1)^n` and `N ≥ 1`, if `f` is
coordinate-monotone, `f x ≤ stepUpper N f x`. -/
lemma le_stepUpper_self {N : ℕ} (hN : 1 ≤ N) {f : (Fin n → ℝ) → ℝ}
    (hf : Monotone f) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) :
    f x ≤ stepUpper N f x := by
  apply hf
  intro i
  obtain ⟨hxi₀, hxi₁⟩ := hx i
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNx_nn : 0 ≤ (N : ℝ) * x i := mul_nonneg hN'.le hxi₀
  have hfloor_lt_N : Nat.floor ((N : ℝ) * x i) < N := by
    rw [Nat.floor_lt hNx_nn]
    calc (N : ℝ) * x i < (N : ℝ) * 1 := mul_lt_mul_of_pos_left hxi₁ hN'
      _ = (N : ℝ) := mul_one _
  have hfloor_gt : (N : ℝ) * x i < ((Nat.floor ((N : ℝ) * x i) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  change x i ≤ stepRetract N x i + 1 / (N : ℝ)
  unfold stepRetract
  have hmin_eq : (min (Nat.floor ((N : ℝ) * x i)) N : ℕ) = Nat.floor ((N : ℝ) * x i) :=
    min_eq_left hfloor_lt_N.le
  rw [hmin_eq]
  -- Goal: x i ≤ (⌊N x i⌋ : ℝ)/N + 1/N
  rw [show ((Nat.floor ((N : ℝ) * x i) : ℕ) : ℝ) / (N : ℝ) + 1 / (N : ℝ)
        = (((Nat.floor ((N : ℝ) * x i) : ℕ) : ℝ) + 1) / (N : ℝ) by ring]
  rw [le_div_iff₀ hN', mul_comm (x i) (N : ℝ)]
  linarith

/-- **stepUpper Riemann identity.** The integral of `stepUpper N f`
over the half-open cube `[0,1)^n` equals the upper-corner Riemann sum. -/
theorem integral_stepUpper_eq_riemann
    {N : ℕ} (hN : 1 ≤ N) (f : (Fin n → ℝ) → ℝ) :
    ∫ x in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
        stepUpper N f x ∂volume
      = (1 / (N : ℝ) ^ n) *
          ∑ k : Fin n → Fin N, f (fun i => ((k i : ℝ) + 1) / N) := by
  -- stepUpper N f x = stepLower N (shifted f) x; then apply
  -- integral_stepLower_eq_riemann.
  set fSh : (Fin n → ℝ) → ℝ := fun y => f (fun i => y i + 1 / (N : ℝ))
    with hfSh_def
  have heq : (fun x => stepUpper N f x) = (fun x => stepLower N fSh x) := by
    funext x; rfl
  rw [show (fun x => stepUpper N f x) = (fun x => stepLower N fSh x) from heq]
  rw [integral_stepLower_eq_riemann hN]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change f (fun i => (k i : ℝ) / N + 1 / (N : ℝ)) = f (fun i => ((k i : ℝ) + 1) / N)
  congr 1
  funext i
  field_simp

/-- `stepUpper N f` is integrable on the half-open cube. -/
lemma integrableOn_stepUpper_cube {N : ℕ} (hN : 1 ≤ N)
    (f : (Fin n → ℝ) → ℝ) :
    IntegrableOn (stepUpper N f)
      (Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) volume := by
  set fSh : (Fin n → ℝ) → ℝ := fun y => f (fun i => y i + 1 / (N : ℝ))
  have heq : (fun x => stepUpper N f x) = (fun x => stepLower N fSh x) := by
    funext x; rfl
  rw [show (stepUpper N f) = (stepLower N fSh) from heq]
  exact integrableOn_stepLower_cube hN fSh

end StepUpper

/-! ### §7 — Riemann-sum convergence for monotone integrable functions

For `f ≥ 0` monotone on `(Fin n → ℝ)`, the lower-step Riemann
approximation `stepLower N f` converges to `f` in the integral sense:
`∫_{[0,1)^n} stepLower N f → ∫_{[0,1]^n} f` as `N → ∞`. The proof
uses the sandwich `stepLower ≤ f ≤ stepUpper` (`stepLower_le_self`,
`le_stepUpper_self`) plus the finite-additivity bound

```
∫ stepUpper N f - ∫ stepLower N f
  = (1/N^n) [∑ f((k+1)/N) - ∑ f(k/N)]
  ≤ n · M / N
```

where `M := f(1,…,1)`. The bound on the sum-difference (the
`sum_step_diff_bound` lemma below) is the substantive piece — it
factors out via reindexing into `Fin (N+1)^n` and applying the
inclusion `Fin N ↪ Fin (N+1)` (twice, via `Fin.castSucc` and
`Fin.succ`); the cancellation of common indices in `{1,…,N-1}^n`
leaves a residual of size `(N+1)^n − N^n ≤ n(N+1)^{n-1}`. -/

section RiemannLimit

/-- Sum-difference bound used in the squeeze argument. The bound

```
∑_{k : Fin n → Fin N} f((k+1)/N) − ∑_{k : Fin n → Fin N} f(k/N)
  ≤ n · (N+1)^{n-1} · M
```

(or equivalently after dividing by `N^n`, the `∫ stepUpper - ∫
stepLower ≤ n M / N` form once the prefactor is absorbed). The
deferred proof uses `Finset.sum_bij` along the embeddings
`Fin.castSucc : Fin N ↪ Fin (N+1)` and `Fin.succ : Fin N ↪ Fin (N+1)`,
followed by cancellation of the common image
`{l : ∀ i, 1 ≤ l_i.val ∧ l_i.val < N}` and bounding the residual
`{l : ∃ i, l_i.val = N}` via `(N+1)^n - N^n`. -/
private lemma sum_step_diff_bound {N : ℕ} (hN : 1 ≤ N)
    {f : (Fin n → ℝ) → ℝ} (hf₀ : 0 ≤ f) (hf : Monotone f) :
    (∑ k : Fin n → Fin N, f (fun i => ((k i : ℝ) + 1) / N))
      - (∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N))
    ≤ ((N + 1 : ℝ) ^ n - (N : ℝ) ^ n) * f (fun _ => 1) := by
  classical
  set M : ℝ := f (fun _ => 1) with hM_def
  have hM_nn : 0 ≤ M := hf₀ _
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- Pointwise upper bound: for `l : Fin n → Fin (N+1)`, each coordinate
  -- `(l i).val ≤ N`, so `(l i)/N ≤ 1` and by monotonicity `f(l/N) ≤ M`.
  have h_le_M : ∀ l : Fin n → Fin (N + 1),
      f (fun i => (((l i) : ℕ) : ℝ) / (N : ℝ)) ≤ M := by
    intro l
    apply hf
    intro i
    rw [div_le_one hN']
    have : ((l i) : ℕ) ≤ N := Nat.lt_succ_iff.mp (l i).isLt
    exact_mod_cast this
  -- The two reindexing maps: `φ` shifts each coord by `+1` via `Fin.succ`,
  -- `ψ` keeps each coord the same via `Fin.castSucc`.
  let φ : (Fin n → Fin N) → (Fin n → Fin (N + 1)) := fun k i => (k i).succ
  let ψ : (Fin n → Fin N) → (Fin n → Fin (N + 1)) := fun k i => (k i).castSucc
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    funext i
    have h := congr_fun hab i
    exact Fin.succ_injective _ h
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    funext i
    have h := congr_fun hab i
    exact Fin.castSucc_injective _ h
  -- Step (A): rewrite the first sum (`f((k+1)/N)`) as a sum over
  -- `Finset.univ.image φ ⊆ (Fin n → Fin (N+1))`.
  have hA :
      (∑ k : Fin n → Fin N, f (fun i => ((k i : ℝ) + 1) / N))
        = ∑ l ∈ (Finset.univ : Finset (Fin n → Fin N)).image φ,
            f (fun i => (((l i) : ℕ) : ℝ) / (N : ℝ)) := by
    rw [Finset.sum_image (fun a _ b _ hab => hφ_inj hab)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine congrArg f (funext fun i => ?_)
    show ((k i : ℝ) + 1) / (N : ℝ) = (((φ k i) : ℕ) : ℝ) / (N : ℝ)
    have : (((φ k i) : ℕ) : ℝ) = ((k i : ℕ) : ℝ) + 1 := by
      simp [φ, Fin.val_succ]
    rw [this]
  -- Step (B): rewrite the second sum (`f(k/N)`) as a sum over
  -- `Finset.univ.image ψ`.
  have hB :
      (∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N))
        = ∑ l ∈ (Finset.univ : Finset (Fin n → Fin N)).image ψ,
            f (fun i => (((l i) : ℕ) : ℝ) / (N : ℝ)) := by
    rw [Finset.sum_image (fun a _ b _ hab => hψ_inj hab)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine congrArg f (funext fun i => ?_)
    show (k i : ℝ) / (N : ℝ) = (((ψ k i) : ℕ) : ℝ) / (N : ℝ)
    simp [ψ, Fin.val_castSucc]
  -- Step (C): split the universal sum on `Fin n → Fin (N+1)` two ways:
  -- via the partition `image φ ⊔ (univ \ image φ)` and via
  -- `image ψ ⊔ (univ \ image ψ)`. This gives `A − B = comp_B − comp_A`
  -- where `comp_X := ∑ l ∈ univ \ X, g l`.
  set A_im : Finset (Fin n → Fin (N + 1)) :=
    (Finset.univ : Finset (Fin n → Fin N)).image φ with hA_im_def
  set B_im : Finset (Fin n → Fin (N + 1)) :=
    (Finset.univ : Finset (Fin n → Fin N)).image ψ with hB_im_def
  set g : (Fin n → Fin (N + 1)) → ℝ :=
    fun l => f (fun i => (((l i) : ℕ) : ℝ) / (N : ℝ)) with hg_def
  have hA_compl :
      (∑ l ∈ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ A_im), g l)
        = (∑ l : Fin n → Fin (N + 1), g l) - (∑ l ∈ A_im, g l) := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
  have hB_compl :
      (∑ l ∈ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ B_im), g l)
        = (∑ l : Fin n → Fin (N + 1), g l) - (∑ l ∈ B_im, g l) := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
  -- Step (D): the residual `(univ \ B_im)` has cardinality `(N+1)^n − N^n`.
  -- Each `g l ≤ M` by `h_le_M`, hence `∑ ≤ ((N+1)^n − N^n) · M`.
  have hN_pow_le : N ^ n ≤ (N + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ _) n
  have h_card_univ : (Finset.univ : Finset (Fin n → Fin (N + 1))).card = (N + 1) ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_card_B_im : B_im.card = N ^ n := by
    rw [hB_im_def, Finset.card_image_of_injective _ hψ_inj,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_card_compl_B :
      ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ B_im).card
        = (N + 1) ^ n - N ^ n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h_card_univ, h_card_B_im]
  have h_compl_B_bound :
      (∑ l ∈ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ B_im), g l)
        ≤ ((N + 1 : ℝ) ^ n - (N : ℝ) ^ n) * M := by
    have hbd : ∀ l ∈ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ B_im),
        g l ≤ M := fun l _ => h_le_M l
    calc (∑ l ∈ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ B_im), g l)
        ≤ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ B_im).card • M :=
            Finset.sum_le_card_nsmul _ _ M hbd
      _ = ((N + 1) ^ n - N ^ n : ℕ) • M := by rw [h_card_compl_B]
      _ = ((N + 1 : ℝ) ^ n - (N : ℝ) ^ n) * M := by
            rw [nsmul_eq_mul, Nat.cast_sub hN_pow_le]
            push_cast
            ring
  have h_compl_A_nonneg :
      0 ≤ ∑ l ∈ ((Finset.univ : Finset (Fin n → Fin (N + 1))) \ A_im), g l :=
    Finset.sum_nonneg (fun _ _ => hf₀ _)
  -- Step (E): combine. The LHS of the goal equals `A − B`, which by
  -- `hA_compl` and `hB_compl` rewrites to `(comp_B + ∑) − (comp_A + ∑)`
  -- = `comp_B − comp_A ≤ comp_B ≤ ((N+1)^n − N^n) M`.
  rw [hA, hB]
  -- After rewriting we have `∑_{l ∈ A_im} g l - ∑_{l ∈ B_im} g l ≤ ...`.
  -- From hA_compl: ∑ univ = comp_A + ∑ A_im.
  -- From hB_compl: ∑ univ = comp_B + ∑ B_im.
  -- Hence ∑ A_im - ∑ B_im = comp_B - comp_A.
  linarith

/-- For monotone `f` on `(Fin n → ℝ)`, the L¹ "gap" between
`stepLower N f` and `stepUpper N f` on the half-open cube is at most
`((N+1)^n - N^n) M / N^n ≤ n · (1 + 1/N)^(n-1) · M / N`, going to
`0` as `N → ∞`. -/
private lemma integral_stepUpper_sub_stepLower_bound
    {N : ℕ} (hN : 1 ≤ N)
    {f : (Fin n → ℝ) → ℝ} (hf₀ : 0 ≤ f) (hf : Monotone f) :
    (∫ x in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
        stepUpper N f x ∂volume)
      - (∫ x in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
        stepLower N f x ∂volume)
    ≤ ((N + 1 : ℝ) ^ n / (N : ℝ) ^ n - 1) * f (fun _ => 1) := by
  rw [integral_stepUpper_eq_riemann hN, integral_stepLower_eq_riemann hN]
  rw [show (1 / (N : ℝ) ^ n) *
        ∑ k : Fin n → Fin N, f (fun i => ((k i : ℝ) + 1) / N)
      - (1 / (N : ℝ) ^ n) *
        ∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N)
      = (1 / (N : ℝ) ^ n) *
          ((∑ k : Fin n → Fin N, f (fun i => ((k i : ℝ) + 1) / N))
            - ∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N)) by ring]
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNn_pos : 0 < (N : ℝ) ^ n := by positivity
  have h_diff := sum_step_diff_bound (n := n) hN hf₀ hf
  calc (1 / (N : ℝ) ^ n) *
        ((∑ k : Fin n → Fin N, f (fun i => ((k i : ℝ) + 1) / N))
          - ∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N))
      ≤ (1 / (N : ℝ) ^ n) *
          (((N + 1 : ℝ) ^ n - (N : ℝ) ^ n) * f (fun _ => 1)) := by
            gcongr
    _ = ((N + 1 : ℝ) ^ n / (N : ℝ) ^ n - 1) * f (fun _ => 1) := by
            field_simp

end RiemannLimit

/-! ### §8 — Master continuous FKG / AD on `[0,1]^n` (signatures + status)

The master theorems `continuous_fkg` and `continuous_ad` follow the
discrete-FKG inequality `fkg_discrete_pi_finN` on the half-open cube
combined with the Riemann-sum convergence of the lower-step
approximations to `∫ f`. The convergence step `tendsto_integral_stepLower`
depends on `sum_step_diff_bound` (deferred Session D). The signatures
are recorded here for the downstream consumer (EX-7+); the bodies
reduce to the squeeze on `∫ stepLower N` modulo the deferred bound. -/

section MasterTheorems

variable {n : ℕ}

/-- **Riemann-sum convergence (lower-step → integral).** For `f ≥ 0`
monotone integrable on `[0,1]^n`, the lower-step Riemann integrals
on `[0,1)^n` converge to `∫_{[0,1]^n} f` as `N → ∞`. -/
theorem tendsto_integral_stepLower
    {f : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hf : Monotone f)
    (hfL1 : IntegrableOn f (Set.Icc (0 : Fin n → ℝ) 1)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∫ x in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            stepLower N f x ∂volume)
      Filter.atTop
      (nhds (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f x ∂volume)) := by
  -- DEFERRED (Session D): squeeze ∫ stepLower N f ≤ ∫ f ≤ ∫ stepUpper N f
  -- using `integral_stepUpper_sub_stepLower_bound` (which depends on
  -- `sum_step_diff_bound`). The bound `((N+1)/N)^n - 1 → 0` gives the
  -- Tendsto via `Tendsto.sub_zero` + `Filter.Tendsto.mono_right`.
  sorry

/-- **Continuous FKG on `[0,1]^n`** (Brightwell 1999 §4 source). For
non-negative coordinate-monotone `f, g, fg` integrable on the cube:

```
(∫ f) (∫ g) ≤ (∫ f g) · vol([0,1]^n) = ∫ f g.
```
-/
theorem continuous_fkg
    {f g : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g)
    (hfL1 : IntegrableOn f (Set.Icc (0 : Fin n → ℝ) 1))
    (hgL1 : IntegrableOn g (Set.Icc (0 : Fin n → ℝ) 1))
    (hfgL1 : IntegrableOn (f * g) (Set.Icc (0 : Fin n → ℝ) 1)) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, g x ∂volume)
    ≤ (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f x * g x ∂volume) *
      (volume (Set.Icc (0 : Fin n → ℝ) 1)).toReal := by
  -- Discrete FKG `fkg_discrete_pi_finN` on `(Fin n → Fin N)` with
  -- divisor `N` gives, after dividing both sides by `N^(2n)`:
  --   (∫ stepLower N f)(∫ stepLower N g) ≤ ∫ stepLower N (f*g)
  -- (Riemann identity, plus stepLower N (f*g) = stepLower N f * stepLower N g
  -- pointwise; use integral_stepLower_eq_riemann to convert sums.)
  -- Take `N → ∞` via `tendsto_integral_stepLower` for `f`, `g`, and `f*g`,
  -- then conclude via `Filter.Tendsto.mul` and `le_of_tendsto`.
  -- `f * g` is non-neg monotone integrable (product of non-neg monotone).
  -- DEFERRED (Session D): assembly modulo `tendsto_integral_stepLower`.
  sorry

/-- **Continuous Ahlswede–Daykin (4FT) on `[0,1]^n`**. -/
theorem continuous_ad
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hf₁₀ : 0 ≤ f₁) (hf₂₀ : 0 ≤ f₂) (hf₃₀ : 0 ≤ f₃) (hf₄₀ : 0 ≤ f₄)
    (hf₁L1 : IntegrableOn f₁ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₂L1 : IntegrableOn f₂ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₃L1 : IntegrableOn f₃ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₄L1 : IntegrableOn f₄ (Set.Icc (0 : Fin n → ℝ) 1))
    (hAD : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₁ x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₂ x ∂volume)
    ≤ (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₃ x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₄ x ∂volume) := by
  -- Same pattern as `continuous_fkg`: apply `ad_discrete_pi` (via `gridFnN`-
  -- form, paralleling `fkg_discrete_pi_finN`) at each `N`, divide by `N^(2n)`,
  -- recognise sums as `∫ stepLower N`, and pass to `N → ∞`. Hypothesis
  -- `hAD` transports through `gridFnN` because the lattice ops on
  -- `(Fin n → Fin N)` map (under `(k_i : ℝ)/N`) to the cube lattice ops
  -- (`gridPoint_inf`, `gridPoint_sup` analogues).
  -- DEFERRED (Session D): assembly modulo `tendsto_integral_stepLower`.
  sorry

end MasterTheorems

end OneThird.ContinuousFKG
