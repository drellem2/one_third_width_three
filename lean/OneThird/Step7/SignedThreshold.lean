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

/-! ### §7 — Grounded form: from a Step 2 staircase to signed-threshold

This section closes the *grounding* gap left by §§ 1-6: there the
input was the abstract collapsed half-plane `affineHalfPlane sigTil
tauBar D` (the paper's `\hat M_e`), with no link back to the Step 2
staircase `M_e` that produces it. Here we expose the connection.

The paper's `eq:affine-staircase` writes Step 2's per-fiber staircase
in the affine form
`M_e = {(i, j) ∈ D : i + σ̃·j ≤ φ(i - σ̃·j)}`,
where `σ̃ ∈ {±1}` is the staircase type (Step 3
`local_sign_exists`) and `φ : ℤ → ℤ` is the transverse-axis
column-threshold function (Step 2
`PerFiber.exists_staircase_per_fiber` + Step 3 `IsStaircaseType`).
The collapsed `\hat M_e := affineHalfPlane σ̃ τ̄ D` replaces `φ`
by its median `τ̄`, at a symmetric-difference cost bounded by the
*transverse spread* of `φ` on the transverse range `V_e`.

We formalise three pieces:

* `affineStaircase σTil φ D` — the Step 2 staircase in the paper's
  affine form (concrete `Finset (ℤ × ℤ)` parametric in `(σ̃, φ, D)`).
* `affineStaircase_const_eq_affineHalfPlane` — when `φ` is constant
  with value `tauBar`, `affineStaircase σTil (fun _ => tauBar) D
  = affineHalfPlane σTil tauBar D` (the `spread(φ) = 0` extreme of
  the collapse).
* `affineStaircase_symmDiff_affineHalfPlane_le_spread` — the
  cleared-denominator symmetric-difference bound: the size of
  `affineStaircase σTil φ D Δ affineHalfPlane σTil tauBar D` is
  bounded by `∑_{p ∈ D} 1{φ(p.1 - σ̃·p.2) ≠ tauBar}`, which in turn
  is bounded by `|D|` (trivially) and, more sharply, by
  `(transverse spread of φ on D) · |D|` (paper's spread bound).

The downstream consumer (`signed_threshold_grounded`) chains these
with `signed_threshold_normal_form` to deliver a signed-threshold
half-plane equality `M_e ≈ signedHalfPlane σ_e τ_e D'` modulo a
bounded symmetric-difference set, which is the `O(ε_2)` error term
of `lem:signed-threshold` in the cleared-denominator form.

The grounding is *non-quantitative* in the spread bound: we record
that the symmetric difference is point-wise *zero* on the
constant-`φ` (`spread = 0`) sub-region of `D`, and bounded by `|D|`
in general. The quantitative `spread = O(ε₂ · t_e)` bound — i.e.,
the cleared-denominator BK-boundary count argument of the paper
(`step7.tex:171-181`) — is a separate Step 2/Step 7 conductance
hypothesis recorded as `AffineStaircaseSpreadHyp` below; it is
*consumed* by the grounded form, not re-derived.
-/

section Grounded

variable {D : Finset (ℤ × ℤ)}

/-- **Affine-form Step 2 staircase** (`step7.tex:147-150`,
`eq:affine-staircase`).

The set `{(i, j) ∈ D : i + σ̃·j ≤ φ(i - σ̃·j)}` parametric in
the staircase type `σTil ∈ Sign`, the per-transverse-line
column-threshold function `φ : ℤ → ℤ`, and the grid `D`. This is
the **concrete input shape** for `lem:signed-threshold`: Step 2's
`PerFiber.per_fiber_staircase` produces, for each rich good fiber
`e`, an `IsStaircasePlus`-staircase that rewrites into this affine
form via the change of variables in `eq:affine-staircase`. -/
def affineStaircase (σTil : Sign) (φ : ℤ → ℤ) (D : Finset (ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  D.filter (fun p => p.1 + σTil.toInt * p.2 ≤ φ (p.1 - σTil.toInt * p.2))

lemma mem_affineStaircase {σTil : Sign} {φ : ℤ → ℤ}
    {D : Finset (ℤ × ℤ)} {p : ℤ × ℤ} :
    p ∈ affineStaircase σTil φ D ↔
      p ∈ D ∧ p.1 + σTil.toInt * p.2 ≤ φ (p.1 - σTil.toInt * p.2) := by
  unfold affineStaircase
  rw [Finset.mem_filter]

lemma affineStaircase_subset (σTil : Sign) (φ : ℤ → ℤ)
    (D : Finset (ℤ × ℤ)) :
    affineStaircase σTil φ D ⊆ D := Finset.filter_subset _ _

/-- **Constant-`φ` collapse** (`step7.tex:155-179`).

When the transverse-axis column-threshold function `φ` is the
constant `tauBar`, the affine staircase equals the affine half-plane
`affineHalfPlane σTil tauBar D` exactly (no symmetric-difference
error). This is the `spread(φ) = 0` extreme of the paper's
median-replacement step. -/
theorem affineStaircase_const_eq_affineHalfPlane
    (σTil : Sign) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    affineStaircase σTil (fun _ => tauBar) D =
      affineHalfPlane σTil tauBar D := by
  ext p
  rw [mem_affineStaircase, mem_affineHalfPlane]

/-- **Pointwise spread predicate**: at the point `p ∈ D`, the
column-threshold function `φ` deviates from the candidate
constant `tauBar` enough to flip the half-plane membership of `p`
between `affineStaircase σTil φ D` and `affineHalfPlane σTil tauBar D`.

Equivalently, `min(φ v, tauBar) < i + σTil·j ≤ max(φ v, tauBar)`
where `v := i - σTil·j`. The complement (`flipped = false` for `p`)
records that `p`'s membership is **stable** under the replacement
`φ ↦ tauBar`. -/
def isFlippedBy (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ)
    (p : ℤ × ℤ) : Prop :=
  let v := p.1 - σTil.toInt * p.2
  let h := p.1 + σTil.toInt * p.2
  ¬ ((h ≤ φ v) ↔ (h ≤ tauBar))

instance (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ) (p : ℤ × ℤ) :
    Decidable (isFlippedBy σTil φ tauBar p) := by
  unfold isFlippedBy
  infer_instance

/-- The symmetric-difference set `affineStaircase Δ affineHalfPlane`
is exactly the set of points of `D` where the column-threshold `φ` at
the transverse line through `p` *flips* the half-plane membership of
`p` relative to the candidate constant `tauBar`. -/
theorem affineStaircase_symmDiff_eq_flipped
    (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    symmDiff (affineStaircase σTil φ D) (affineHalfPlane σTil tauBar D)
      = D.filter (fun p => isFlippedBy σTil φ tauBar p) := by
  classical
  ext p
  simp only [Finset.mem_symmDiff, mem_affineStaircase,
    mem_affineHalfPlane, Finset.mem_filter, isFlippedBy]
  constructor
  · rintro (⟨⟨hpD, h1⟩, h2⟩ | ⟨⟨hpD, h1⟩, h2⟩)
    · refine ⟨hpD, ?_⟩
      intro heq
      apply h2
      refine ⟨hpD, ?_⟩
      rw [heq] at h1; exact h1
    · refine ⟨hpD, ?_⟩
      intro heq
      apply h2
      refine ⟨hpD, ?_⟩
      rw [← heq] at h1; exact h1
  · rintro ⟨hpD, hne⟩
    by_cases h : p.1 + σTil.toInt * p.2 ≤ φ (p.1 - σTil.toInt * p.2)
    · -- staircase: yes. half-plane: must be no, since they disagree.
      left
      refine ⟨⟨hpD, h⟩, ?_⟩
      rintro ⟨_, hhp⟩
      apply hne
      exact iff_of_true h hhp
    · -- staircase: no. half-plane: must be yes.
      right
      have hhp : p.1 + σTil.toInt * p.2 ≤ tauBar := by
        by_contra hhpno
        apply hne
        exact iff_of_false h hhpno
      refine ⟨⟨hpD, hhp⟩, ?_⟩
      rintro ⟨_, hsno⟩; exact h hsno

/-- **Symmetric-difference is bounded by the count of flipped points**
(`step7.tex:171-181`, cleared-denominator).

The cardinality of `affineStaircase Δ affineHalfPlane` equals the
number of points of `D` flipped by the replacement `φ ↦ tauBar`. -/
theorem affineStaircase_symmDiff_card
    (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    (symmDiff (affineStaircase σTil φ D)
        (affineHalfPlane σTil tauBar D)).card =
      (D.filter (fun p => isFlippedBy σTil φ tauBar p)).card := by
  rw [affineStaircase_symmDiff_eq_flipped]

/-- **Trivial cardinality bound**: the symmetric difference is
bounded above by `|D|` (every flipped point lies in `D`). -/
theorem affineStaircase_symmDiff_le_D
    (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ) (D : Finset (ℤ × ℤ)) :
    (symmDiff (affineStaircase σTil φ D)
        (affineHalfPlane σTil tauBar D)).card ≤ D.card := by
  rw [affineStaircase_symmDiff_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **Spread hypothesis** (`step7.tex:171-181`, cleared-denominator
form of paper's `spread(φ_e) ≤ O(ε₂·t_e)`).

The number of `p ∈ D` whose membership is flipped by replacing
`φ` with the constant `tauBar` is bounded by `spread_n · |D|` (in
the cleared-denominator form `1 · #flipped ≤ spread_n · |D|`).

In the paper, `spread_n` plays the role of `O(ε₂)` after the
`|D| = |fib_e| ≈ t_e²` and `|V_e| = O(t_e)` reductions: the BK-boundary
argument gives `spread(φ_e) ≤ O(ε₂·t_e)`, and the flipped-point count
is at most `spread(φ_e) · |V_e| ≤ O(ε₂·t_e²) = O(ε₂)·|D|`.

This is recorded here as an **input hypothesis**; the upstream Step 2
BK-boundary derivation (paper `step7.tex:158-170`) is the substance
that *produces* this bound and is the next-level engineering target. -/
def AffineStaircaseSpreadHyp (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ)
    (D : Finset (ℤ × ℤ)) (spread_n spread_d : ℕ) : Prop :=
  spread_d * (D.filter (fun p => isFlippedBy σTil φ tauBar p)).card ≤
    spread_n * D.card

/-- **Symmetric-difference under the spread hypothesis** —
cleared-denominator. Combines `affineStaircase_symmDiff_card` with
the spread hypothesis to deliver
`spread_d · |M_e Δ \hat M_e| ≤ spread_n · |D|`. -/
theorem affineStaircase_symmDiff_le_spread
    (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ) (D : Finset (ℤ × ℤ))
    (spread_n spread_d : ℕ)
    (hSpread : AffineStaircaseSpreadHyp σTil φ tauBar D spread_n spread_d) :
    spread_d *
        (symmDiff (affineStaircase σTil φ D)
          (affineHalfPlane σTil tauBar D)).card ≤
      spread_n * D.card := by
  rw [affineStaircase_symmDiff_card]
  exact hSpread

/-- **`lem:signed-threshold` — grounded form** (`step7.tex:124-230`).

Given a Step 2 affine staircase `M_e = affineStaircase σTil φ D`,
a candidate constant threshold `tauBar` (the paper's `τ̄_e`,
chosen as the median of `φ` on the transverse range `V_e`), and the
cleared-denominator spread hypothesis bounding the
symmetric-difference cost of the median collapse, conclude that there
exist signed-threshold data `(σ_e, τ_e)` and a (possibly reflected)
grid `D'` such that, after applying the single-axis reflection
`reflectJ` in the `σTil = true` case, the **collapsed** staircase
`affineHalfPlane σTil tauBar D` equals the signed half-plane
`signedHalfPlane σ_e τ_e D'`. The full staircase `M_e` thus
agrees with `signedHalfPlane σ_e τ_e D'` modulo a symmetric difference
of cleared-denominator size `≤ spread_n · |D| / spread_d`.

This is the cleared-denominator form of the paper's
`1_S(L) = 1{σ_e·(j(L)-i(L)) ≥ τ_e} + O(ε_2)` conclusion of
`lem:signed-threshold` (`step7.tex:130-134`). -/
theorem signed_threshold_grounded
    (σTil : Sign) (φ : ℤ → ℤ) (tauBar : ℤ) (D : Finset (ℤ × ℤ))
    (spread_n spread_d : ℕ)
    (hSpread : AffineStaircaseSpreadHyp σTil φ tauBar D spread_n spread_d) :
    ∃ (sigE : Sign) (tauE : ℤ) (ψ : (ℤ × ℤ) → (ℤ × ℤ))
      (D' : Finset (ℤ × ℤ)),
      (affineHalfPlane σTil tauBar D).image ψ =
        signedHalfPlane sigE tauE D' ∧
      spread_d *
          (symmDiff (affineStaircase σTil φ D)
            (affineHalfPlane σTil tauBar D)).card ≤
        spread_n * D.card := by
  obtain ⟨sigE, tauE, ψ, D', hψ⟩ :=
    signed_threshold_exists σTil tauBar D
  exact ⟨sigE, tauE, ψ, D', hψ,
    affineStaircase_symmDiff_le_spread σTil φ tauBar D spread_n spread_d
      hSpread⟩

end Grounded

end Step7
end OneThird
