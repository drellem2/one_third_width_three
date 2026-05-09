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

/-- **Riemann sum identity (statement form).** For `N ≥ 1`, the
left-endpoint Riemann sum of `f` over the `N^n`-grid `(Fin N)^n`
equals the integral of the step function `stepLower N f` over the
half-open cube `[0,1)^n`:

```
∫_{x ∈ [0,1)^n} stepLower N f x ∂volume
  = (1/N^n) · ∑_{k : Fin n → Fin N} f(k/N).
```

The proof decomposes `[0,1)^n` into the disjoint cells `C_k`
(`k : Fin n → Fin N`), each of volume `(1/N)^n`, on each of which the
step function `stepLower N f` is constant with value `f(k/N)`.

**Status (Session B).** The statement is recorded here; the full proof
(cell decomposition + finite additivity of the integral) is deferred
to Session C alongside the dominated-convergence limit argument. The
volume-of-cell identity (`volume_cell`) is the Session B
contribution; the assembly is Session C. -/
theorem integral_stepLower_eq_riemann
    {N : ℕ} (_hN : 1 ≤ N) (f : (Fin n → ℝ) → ℝ)
    (_hfm : Measurable f) :
    ∫ x in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
        stepLower N f x ∂volume
      = (1 / (N : ℝ) ^ n) *
          ∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N) := by
  -- The full assembly (cell decomposition + finite additivity) is the
  -- substantive Session C contribution; the cell-volume identity
  -- `volume_cell` and the constancy of `stepLower N f` on each cell
  -- are the per-cell ingredients prepared in Session B.
  sorry

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
  -- Now apply `Nat.floor_eq_iff` for nonneg reals and Nat.
  have hxnn : (0 : ℝ) ≤ (N : ℝ) * x :=
    le_trans (by exact_mod_cast (Nat.zero_le _ : 0 ≤ (k : ℕ))) hkN
  -- Use `Nat.floor_eq_iff` (nonneg form).
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
  -- `min (Nat.floor (N * x_i)) N = (k i : ℕ)` since `(k i : ℕ) < N`.
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

end RiemannSum

end OneThird.ContinuousFKG
