/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step3.LocalSign
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Signed-threshold normal form (`lem:signed-threshold`)

This file formalises the signed-threshold normalisation of Step 2's
staircase region, `step7.tex` §`sec:normalize`
(`step7.tex:127-230`, `lem:signed-threshold`).

## Paper statement

For each `S`-good rich interface `e`, Step 2's per-fiber staircase
(`step2.tex:prop:per-fiber`) produces a monotone staircase
`M_e ⊆ fib_e` with small symmetric-difference error.  Step 7
normalises this into the explicit signed-threshold form

  `1_S(L) = 1{ σ_e · (j(L) - i(L)) ≥ τ_e } + O(ε_2)`,

where `σ_e ∈ {±1}` is an oriented direction and `τ_e ∈ ℤ` is a
scalar threshold.  The normalisation proceeds in two steps
(`step7.tex:156-229`):

1. **Collapsing the column threshold to a constant.**  Step 2's
   staircase has the affine form
   `M_e = {(i, j) ∈ D_e : i + sigTil · j ≤ phi(i - sigTil · j)}`,
   and the BK-boundary cost forces the transverse spread of `phi` to
   be `O(ε₂ · t_e)`.  Replacing `phi` by its median `tauBar` yields
   the *collapsed affine half-plane*
   `hat M_e = {(i, j) ∈ D_e : i + sigTil · j ≤ tauBar}`
   at a symmetric-difference cost `O(ε₂ · |fib_e|)`.

2. **Writing `hat M_e` as a signed half-plane.**  A direct algebraic
   rewrite in the case `sigTil = -1` (and the reflection
   `(i, j) ↦ (i, t - j)` in the case `sigTil = +1`) yields the
   signed-threshold form `{(i, j) : σ · (j - i) ≥ τ}` with explicit
   values of `(σ, τ)`.

## Lean formalisation

We formalise the content in cleared-denominator abstract form:

* `signedHalfPlane σ τ D` — the set
  `{(i, j) ∈ D : τ ≤ σ.toInt · (j - i)}`.
* `affineHalfPlane sigTil tauBar D` — the *collapsed* affine
  half-plane `{(i, j) ∈ D : i + sigTil.toInt · j ≤ tauBar}`
  (post-collapse output of Step 2's staircase).
* `reflectJ t` — the single-axis reflection
  `(i, j) ↦ (i, t - j)` of `step7.tex:202-210`.

The main results are:

* `affineHalfPlane_false_eq_signedHalfPlane` — for `sigTil = false`
  (Step 3 `false ↔ -1`, the paper's `σ̃ = -1` case), the affine
  half-plane equals the signed half-plane with `σ = true`
  (`σ.toInt = +1`) and `τ = -tauBar`, directly.
* `affineHalfPlane_true_eq_signedHalfPlane_reflect` — for
  `sigTil = true` (paper's `σ̃ = +1` case), after applying
  `reflectJ t`, the affine half-plane becomes a signed half-plane
  with `σ = true` and `τ = t - tauBar`.

Combined, these yield `signed_threshold_normal_form`: every
collapsed affine half-plane equals, possibly after the
single-axis reflection, a signed-threshold half-plane.

Downstream, `lem:cocycle` consumes the pair `(σ_e, τ_e)` through
the signed-threshold form.
-/

namespace OneThird
namespace Step7

open Finset OneThird.Step3

/-! ### §1 — Signed-threshold half-plane (`step7.tex:eq:signed-threshold`) -/

/-- **Signed-threshold half-plane** (`step7.tex:46-50`,
`eq:signed-threshold`).

Given a sign `σ ∈ {+1, -1}` and a threshold `τ ∈ ℤ`, the associated
half-plane on the grid `D ⊆ ℤ × ℤ` is

  `{(i, j) ∈ D : τ ≤ σ.toInt · (j - i)}`.

We use the Step 3 sign encoding (`OneThird.Step3.Sign`, i.e. `Bool`
with `true ↦ +1`, `false ↦ -1`), so that
`σ.toInt = +1` gives `{j - i ≥ τ}` and
`σ.toInt = -1` gives `{i - j ≥ τ}`. -/
def signedHalfPlane (σ : Sign) (τ : ℤ) (D : Finset (ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  D.filter (fun p => τ ≤ σ.toInt * (p.2 - p.1))

lemma mem_signedHalfPlane {σ : Sign} {τ : ℤ} {D : Finset (ℤ × ℤ)}
    {p : ℤ × ℤ} :
    p ∈ signedHalfPlane σ τ D ↔ p ∈ D ∧ τ ≤ σ.toInt * (p.2 - p.1) := by
  unfold signedHalfPlane
  rw [Finset.mem_filter]

lemma signedHalfPlane_subset (σ : Sign) (τ : ℤ) (D : Finset (ℤ × ℤ)) :
    signedHalfPlane σ τ D ⊆ D := Finset.filter_subset _ _

/-- The complement within `D` of a signed half-plane is itself a
signed half-plane with the opposite sign and flipped threshold.
(`step7.tex:195-213`, the canonical sign-swap.)

Concretely, `D ∖ signedHalfPlane σ τ D` is the strict complement
`{(i, j) ∈ D : σ.toInt · (j - i) < τ}`. -/
theorem signedHalfPlane_compl_eq
    (σ : Sign) (τ : ℤ) (D : Finset (ℤ × ℤ)) :
    D \ signedHalfPlane σ τ D =
      D.filter (fun p => σ.toInt * (p.2 - p.1) < τ) := by
  ext p
  simp only [Finset.mem_sdiff, mem_signedHalfPlane, Finset.mem_filter]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    by_contra hle
    exact h ⟨hp, not_lt.mp hle⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rintro ⟨_, hle⟩
    exact absurd hle (not_le.mpr h)

/-! ### §2 — Affine half-plane (collapsed Step 2 staircase) -/

/-- **Affine half-plane** (`step7.tex:185-186`, `hat M_e`).

The post-collapse form of Step 2's staircase: the set
`{(i, j) ∈ D : i + sigTil.toInt · j ≤ tauBar}`.

This is the output of Step 7 §1 of the paper's proof — the median
replacement of the column threshold `phi` by a constant `tauBar`. -/
def affineHalfPlane (sigTil : Sign) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  D.filter (fun p => p.1 + sigTil.toInt * p.2 ≤ tauBar)

lemma mem_affineHalfPlane {sigTil : Sign} {tauBar : ℤ}
    {D : Finset (ℤ × ℤ)} {p : ℤ × ℤ} :
    p ∈ affineHalfPlane sigTil tauBar D ↔
      p ∈ D ∧ p.1 + sigTil.toInt * p.2 ≤ tauBar := by
  unfold affineHalfPlane
  rw [Finset.mem_filter]

lemma affineHalfPlane_subset (sigTil : Sign) (tauBar : ℤ)
    (D : Finset (ℤ × ℤ)) :
    affineHalfPlane sigTil tauBar D ⊆ D := Finset.filter_subset _ _

/-! ### §3 — Formula unfolding in each sign case -/

/-- Unfolded form of `affineHalfPlane` in the `sigTil = false` case:
`i + (-1)·j ≤ tauBar` ↔ `i - j ≤ tauBar`. -/
lemma affineHalfPlane_false_formula {tauBar : ℤ}
    {D : Finset (ℤ × ℤ)} {p : ℤ × ℤ} :
    p ∈ affineHalfPlane false tauBar D ↔
      p ∈ D ∧ p.1 - p.2 ≤ tauBar := by
  rw [mem_affineHalfPlane]
  have hint : Sign.toInt false = -1 := rfl
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [hint] at h
    linarith
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [hint]
    linarith

/-- Unfolded form of `affineHalfPlane` in the `sigTil = true` case:
`i + (+1)·j ≤ tauBar` ↔ `i + j ≤ tauBar`. -/
lemma affineHalfPlane_true_formula {tauBar : ℤ}
    {D : Finset (ℤ × ℤ)} {p : ℤ × ℤ} :
    p ∈ affineHalfPlane true tauBar D ↔
      p ∈ D ∧ p.1 + p.2 ≤ tauBar := by
  rw [mem_affineHalfPlane]
  have hint : Sign.toInt true = 1 := rfl
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [hint] at h
    linarith
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [hint]
    linarith

/-! ### §4 — Case `sigTil = false` (paper's "σ̃ = -1") -/

/-- **Signed-threshold normal form, `sigTil = false`**
(`step7.tex:198-200`).

The collapsed affine half-plane `{(i, j) ∈ D : i - j ≤ tauBar}`
equals the signed half-plane `{(i, j) ∈ D : (j - i) ≥ -tauBar}`,
i.e. with the Step 3 encoding `σ = true` (`+1`), `τ = -tauBar`. -/
theorem affineHalfPlane_false_eq_signedHalfPlane
    (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    affineHalfPlane false tauBar D = signedHalfPlane true (-tauBar) D := by
  ext p
  rw [affineHalfPlane_false_formula, mem_signedHalfPlane]
  have hint : Sign.toInt true = 1 := rfl
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [hint]; linarith
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [hint] at h
    linarith

/-! ### §5 — Single-axis reflection and `sigTil = true` case -/

/-- **Single-axis reflection** (`step7.tex:202`): the affine
isomorphism `(i, j) ↦ (i, t - j)` of the order-convex grid
`[0, t] × [0, t]`.  It preserves unit BK moves (permuting
`{±e_1, ±e_2}`) and is absorbed into the coordinate chart `π_e`
at the cost of a sign flip of `sigTil`. -/
def reflectJ (t : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1, t - p.2)

@[simp] lemma reflectJ_apply (t : ℤ) (p : ℤ × ℤ) :
    reflectJ t p = (p.1, t - p.2) := rfl

@[simp] lemma reflectJ_invol (t : ℤ) (p : ℤ × ℤ) :
    reflectJ t (reflectJ t p) = p := by
  ext <;> simp [reflectJ]

/-- The reflection `reflectJ t` is injective: it is an involution
(`reflectJ_invol`), hence a bijection of `ℤ × ℤ` onto itself. -/
lemma reflectJ_injective (t : ℤ) :
    Function.Injective (reflectJ t) := by
  intro p q h
  have := congrArg (reflectJ t) h
  simpa [reflectJ_invol] using this

/-- The reflection of a grid `D` under `reflectJ t`: the image
`D.image (reflectJ t)`. -/
def reflectGrid (t : ℤ) (D : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  D.image (reflectJ t)

lemma mem_reflectGrid {t : ℤ} {D : Finset (ℤ × ℤ)} {p : ℤ × ℤ} :
    p ∈ reflectGrid t D ↔ reflectJ t p ∈ D := by
  unfold reflectGrid
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have : reflectJ t p = q := by
      have hinv := congrArg (reflectJ t) hqp
      simpa [reflectJ_invol] using hinv.symm
    rw [this]; exact hq
  · intro h
    exact ⟨reflectJ t p, h, by simp⟩

/-- **Signed-threshold normal form, `sigTil = true`**
(`step7.tex:201-210`).

For `sigTil = true` (Step 3 `true ↦ +1`, `sigTil.toInt = 1`), the
collapsed affine half-plane `{(i, j) ∈ D : i + j ≤ tauBar}`, pushed
through the reflection `(i, j) ↦ (i, t - j)`, equals the signed
half-plane `{(i, j') ∈ reflectGrid t D : (j' - i) ≥ t - tauBar}`,
i.e. with `σ = true` and `τ = t - tauBar` (in the reflected
frame). -/
theorem affineHalfPlane_true_eq_signedHalfPlane_reflect
    (tauBar t : ℤ) (D : Finset (ℤ × ℤ)) :
    (affineHalfPlane true tauBar D).image (reflectJ t) =
      signedHalfPlane true (t - tauBar) (reflectGrid t D) := by
  classical
  ext q
  rw [Finset.mem_image, mem_signedHalfPlane, mem_reflectGrid]
  have htrue : Sign.toInt true = 1 := rfl
  constructor
  · rintro ⟨p, hp, hpq⟩
    rw [affineHalfPlane_true_formula] at hp
    obtain ⟨hpD, haff⟩ := hp
    -- `q = (p.1, t - p.2)`, so `reflectJ t q = (p.1, t - (t - p.2)) = p`.
    have hqp : reflectJ t q = p := by
      rw [← hpq]; exact reflectJ_invol t p
    refine ⟨by rw [hqp]; exact hpD, ?_⟩
    have hq1 : q.1 = p.1 := by rw [← hpq]; rfl
    have hq2 : q.2 = t - p.2 := by rw [← hpq]; rfl
    rw [htrue, hq1, hq2]
    linarith
  · rintro ⟨hqD, hsigned⟩
    -- Build p = reflectJ t q; it lies in D by hqD, and p.1 + p.2 ≤ tauBar.
    refine ⟨reflectJ t q, ?_, ?_⟩
    · rw [affineHalfPlane_true_formula]
      refine ⟨hqD, ?_⟩
      have hp1 : (reflectJ t q).1 = q.1 := rfl
      have hp2 : (reflectJ t q).2 = t - q.2 := rfl
      rw [hp1, hp2]
      rw [htrue] at hsigned
      linarith
    · exact reflectJ_invol t q

/-! ### §6 — Main theorem: signed-threshold normal form -/

/-- **`lem:signed-threshold` — signed-threshold normal form**
(`step7.tex:127-230`).

Every collapsed affine half-plane equals a signed-threshold
half-plane, possibly after applying the single-axis reflection
`reflectJ t`.

Concretely:

* if `sigTil = false` (paper's "σ̃ = -1"), then
  `affineHalfPlane false tauBar D = signedHalfPlane true (-tauBar) D`
  (`§4`, no reflection needed);
* if `sigTil = true` (paper's "σ̃ = +1"), then
  `(affineHalfPlane true tauBar D).image (reflectJ t) =
      signedHalfPlane true (t - tauBar) (reflectGrid t D)`
  (`§5`, with reflection on the `j`-axis).

This is the signed-threshold form `1_S(L) = 1{σ_e·(j(L)-i(L)) ≥ τ_e}`
of `eq:signed-threshold` in the paper; the `O(ε_2)` error term is
accounted for at the upstream symmetric-difference step of
Step 2 (`thm:step2`, `step2_conclusion`), independently of this
algebraic rewrite. -/
theorem signed_threshold_normal_form
    (sigTil : Sign) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    (sigTil = false ∧
      affineHalfPlane sigTil tauBar D = signedHalfPlane true (-tauBar) D) ∨
      (sigTil = true ∧ ∀ t : ℤ,
        (affineHalfPlane sigTil tauBar D).image (reflectJ t) =
          signedHalfPlane true (t - tauBar) (reflectGrid t D)) := by
  cases sigTil
  · left
    refine ⟨rfl, ?_⟩
    exact affineHalfPlane_false_eq_signedHalfPlane tauBar D
  · right
    refine ⟨rfl, ?_⟩
    intro t
    exact affineHalfPlane_true_eq_signedHalfPlane_reflect tauBar t D

/-- **Existence form of `lem:signed-threshold`** (`step7.tex:127`).

For every collapsed affine half-plane `affineHalfPlane sigTil tauBar D`
there exist a sign `σ_e ∈ Sign`, a threshold `τ_e ∈ ℤ`, a reflection
map `φ : ℤ × ℤ → ℤ × ℤ`, and a (possibly reflected) grid
`D' : Finset (ℤ × ℤ)` such that

  `(image of affineHalfPlane) = signedHalfPlane σ_e τ_e D'`.

The output parameters `(σ_e, τ_e)` are the paper's signed-threshold
data; `D'` is the possibly reflected coordinate grid (absorbed into
the chart `π_e`). -/
theorem signed_threshold_exists
    (sigTil : Sign) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    ∃ (sigE : Sign) (tauE : ℤ) (φ : (ℤ × ℤ) → (ℤ × ℤ))
      (D' : Finset (ℤ × ℤ)),
      (affineHalfPlane sigTil tauBar D).image φ =
        signedHalfPlane sigE tauE D' := by
  rcases signed_threshold_normal_form sigTil tauBar D with
    ⟨_, h⟩ | ⟨_, h⟩
  · refine ⟨true, -tauBar, id, D, ?_⟩
    simp [Finset.image_id, h]
  · refine ⟨true, -tauBar, reflectJ 0, reflectGrid 0 D, ?_⟩
    have := h 0
    simpa using this

end Step7
end OneThird
