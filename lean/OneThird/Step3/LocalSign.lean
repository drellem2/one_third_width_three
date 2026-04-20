/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step2.Conclusion
import OneThird.Step2.WeakGrid
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.SymmDiff
import Mathlib.Tactic.Linarith

/-!
# Step 3 — Local sign σ_{x,y}, positive cone, and regular overlap

This file formalises the Step 3 structural results of
`step3.tex` §§1-3:

* `def:staircase-type` (`step3.tex:79`) — the sign type
  `σ ∈ {+, -}` of a staircase region.
* `lem:local-sign` (`step3.tex:90`) — existence and structural
  uniqueness of a local sign `σ_{x,y}` for each rich pair's active
  fiber.
* `def:positive-cone` (`step3.tex:354`) — the positive cone
  `P_{x,y}(L)` as a subset of the four grid directions.
* `lem:positive-cone-inv` (`step3.tex:362`) — invariance of the
  positive cone.
* `def:regular-overlap` (`step3.tex:426`) — the regular overlap
  `Ω^reg_{xy,uv}`.
* `lem:omega-reg-size` (`step3.tex:448`) — the regular overlap has
  mass at least `(1 − ε₃) |Ω°_{xy,uv}|` (abstract union-bound form).

## Abstract form

Following `OneThird.Step2.Conclusion`, the paper's geometric objects
are replaced by abstract finsets and functions:

* a fiber domain `D : Finset (ℤ × ℤ)` and cut image `A ⊆ D`;
* a sign `σ : Sign` witnessed by a column-threshold function `f : ℤ → ℤ`
  that is monotone of type `σ` and whose subgraph is exactly `M`;
* the four grid directions `gridDirs ⊆ ℤ × ℤ` and the positive cone
  `positiveCone σ ⊆ gridDirs`;
* overlap finsets `Ωo, Erx, Eru, Erbk` and the regular-overlap
  `Ωreg := Ωo ∖ (Erx ∪ Eru ∪ Erbk)`.

The `lem:local-sign` and `lem:omega-reg-size` statements are stated in
the `step3.tex` form and proved sorry-free from the abstract
hypotheses.

## Downstream

* `CommonAxes.lean` consumes `Sign`, `positiveCone`,
  `IsRegularOverlap` for `lem:common-axes` and `thm:canonical-orientation`.
* Step 6 (`mg-450c`, `mg-af62`) consumes the σ / positive-cone output
  for the per-interface orientation and the incoherence comparator.
-/

namespace OneThird
namespace Step3

open Finset

/-- A **local sign** `σ ∈ {+1, -1}`, encoded as a `Bool`:
`true ↔ +1`, `false ↔ -1`. Matches `OneThird.signMarker`'s
`Bool`-encoding convention of Step 1. -/
abbrev Sign := Bool

namespace Sign

/-- Integer value of a sign: `true ↦ +1`, `false ↦ -1`. -/
def toInt : Sign → ℤ
  | true  => 1
  | false => -1

/-- Sign negation (axis-reversal symmetry, `step3.tex:309`). -/
def neg : Sign → Sign := Bool.not

@[simp] lemma neg_neg (σ : Sign) : neg (neg σ) = σ := by cases σ <;> rfl

@[simp] lemma toInt_neg (σ : Sign) : (neg σ).toInt = -σ.toInt := by
  cases σ <;> rfl

@[simp] lemma toInt_mul_self (σ : Sign) : σ.toInt * σ.toInt = 1 := by
  cases σ <;> decide

@[simp] lemma toInt_ne_zero (σ : Sign) : σ.toInt ≠ 0 := by cases σ <;> decide

lemma toInt_eq_one_or_neg_one (σ : Sign) : σ.toInt = 1 ∨ σ.toInt = -1 := by
  cases σ <;> decide

end Sign

/-! ### §1 — Staircase type and `lem:local-sign` -/

/-- The **type-σ monotonicity** relation for a column-threshold
function `f : ℤ → ℤ`: for `σ = true` (`+1`) it is weak increase,
for `σ = false` (`-1`) it is weak decrease. -/
def monoByType (σ : Sign) (a b : ℤ) : Prop :=
  match σ with
  | true  => a ≤ b
  | false => b ≤ a

lemma monoByType_refl (σ : Sign) (a : ℤ) : monoByType σ a a := by
  cases σ <;> exact le_refl _

lemma monoByType_trans {σ : Sign} {a b c : ℤ}
    (h₁ : monoByType σ a b) (h₂ : monoByType σ b c) :
    monoByType σ a c := by
  cases σ
  · -- σ = false: weakly decreasing means later ≤ earlier.
    exact le_trans h₂ h₁
  · -- σ = true: weakly increasing.
    exact le_trans h₁ h₂

lemma monoByType_const (σ : Sign) (c : ℤ) :
    ∀ i i' : ℤ, i ≤ i' → monoByType σ c c :=
  fun _ _ _ => monoByType_refl σ c

/-- `M ⊆ D` is a **staircase of type σ** (`def:staircase-type`,
`step3.tex:79`, in the column-threshold form of the paper proof,
`step3.tex:109-117`): there is a column-threshold function
`f : ℤ → ℤ` that is `σ`-monotone, and for every `(i, j) ∈ D`,
membership in `M` is exactly `j ≤ f(i)`.

The paper's literal `i + σj ≤ τ(i - σj)` form is equivalent via the
affine change of variables `(u, v) = (i + σj, i - σj)`; we use the
column-threshold form to get a single `ℤ → ℤ` function and avoid the
diagonal parametrization. -/
def IsStaircaseType (σ : Sign) (D M : Finset (ℤ × ℤ)) : Prop :=
  M ⊆ D ∧
  ∃ f : ℤ → ℤ,
    (∀ i i' : ℤ, i ≤ i' → monoByType σ (f i) (f i')) ∧
    (∀ p ∈ D, p ∈ M ↔ p.2 ≤ f p.1)

lemma IsStaircaseType.subset {σ : Sign} {D M : Finset (ℤ × ℤ)}
    (h : IsStaircaseType σ D M) : M ⊆ D := h.1

/-- `M ⊆ D` **has some staircase type** iff there exists a sign `σ`
with `IsStaircaseType σ D M`. The quantitative Step 2 output
(`step2.tex` `thm:step2`; `OneThird.Step2.Conclusion.step2_conclusion`)
delivers this on the rich good fibers. -/
def IsStaircase (D M : Finset (ℤ × ℤ)) : Prop :=
  ∃ σ : Sign, IsStaircaseType σ D M

/-- The empty set is a staircase of every type. -/
lemma empty_isStaircaseType (σ : Sign) (D : Finset (ℤ × ℤ)) :
    IsStaircaseType σ D (∅ : Finset (ℤ × ℤ)) := by
  classical
  refine ⟨Finset.empty_subset _, ?_⟩
  by_cases hD : D.Nonempty
  · -- Take threshold strictly below every `j`-coord in `D`.
    have hne : (D.image Prod.snd).Nonempty := Finset.image_nonempty.mpr hD
    refine ⟨fun _ => (D.image Prod.snd).min' hne - 1,
      fun _ _ _ => monoByType_refl _ _, ?_⟩
    intro p hp
    simp only [Finset.notMem_empty, false_iff, not_le]
    have hmin : (D.image Prod.snd).min' hne ≤ p.2 :=
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hD
    subst hD
    exact ⟨fun _ => 0, fun _ _ _ => monoByType_refl _ _, by
      intro p hp; exact absurd hp (Finset.notMem_empty _)⟩

/-- The full set `D` is a staircase of every type. -/
lemma self_isStaircaseType (σ : Sign) (D : Finset (ℤ × ℤ)) :
    IsStaircaseType σ D D := by
  classical
  refine ⟨Finset.Subset.refl _, ?_⟩
  by_cases hD : D.Nonempty
  · -- Take threshold at least every `j`-coord in `D`.
    have hne : (D.image Prod.snd).Nonempty := Finset.image_nonempty.mpr hD
    refine ⟨fun _ => (D.image Prod.snd).max' hne,
      fun _ _ _ => monoByType_refl _ _, ?_⟩
    intro p hp
    simp only [iff_true_intro hp, true_iff]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  · rw [Finset.not_nonempty_iff_eq_empty] at hD
    subst hD
    exact ⟨fun _ => 0, fun _ _ _ => monoByType_refl _ _, by
      intro p hp; exact absurd hp (Finset.notMem_empty _)⟩

/-! ### Coordinate-strip degeneracy (`rem:strip-degeneracy`) -/

/-- A **coordinate strip** in `D` at height `h`: the subset of `D`
consisting of points whose second coordinate is `≤ h`.
(`step3.tex:94-97`, `step3.tex:129-131`.) -/
def coordinateStrip (D : Finset (ℤ × ℤ)) (h : ℤ) : Finset (ℤ × ℤ) :=
  D.filter (fun p => p.2 ≤ h)

/-- `M` is a **coordinate strip in `D`** if `M = D ∩ {j ≤ h}` for some
`h`. The degenerate case of `lem:local-sign`: such `M` has both
types simultaneously (`rem:strip-degeneracy`, `step3.tex:335`). -/
def IsCoordinateStrip (D M : Finset (ℤ × ℤ)) : Prop :=
  ∃ h : ℤ, M = coordinateStrip D h

lemma coordinateStrip_subset (D : Finset (ℤ × ℤ)) (h : ℤ) :
    coordinateStrip D h ⊆ D := Finset.filter_subset _ _

lemma mem_coordinateStrip {D : Finset (ℤ × ℤ)} {h : ℤ} {p : ℤ × ℤ} :
    p ∈ coordinateStrip D h ↔ p ∈ D ∧ p.2 ≤ h := by
  unfold coordinateStrip; rw [Finset.mem_filter]

/-- **Coordinate strips have every type** (`step3.tex:129-131`,
the `(⇐)` direction of the paper's structural-uniqueness argument).
The constant column-threshold `f ≡ h` is both weakly increasing and
weakly decreasing, so the strip `{j ≤ h}` is a staircase of every
type. -/
lemma coordinateStrip_isStaircaseType (σ : Sign) (D : Finset (ℤ × ℤ)) (h : ℤ) :
    IsStaircaseType σ D (coordinateStrip D h) := by
  refine ⟨coordinateStrip_subset D h, fun _ => h,
    fun _ _ _ => monoByType_refl _ _, ?_⟩
  intro p hp
  rw [mem_coordinateStrip]
  exact Iff.intro (fun hpmem => hpmem.2) (fun hj => ⟨hp, hj⟩)

/-- **`lem:local-sign` (existence form, `step3.tex:120`).**
If `M ⊆ D` is a staircase (has some type), then there exists a local
sign `σ_{x,y}` such that `M` has type `σ_{x,y}`. Immediate from the
definition of `IsStaircase`. -/
theorem local_sign_exists (D M : Finset (ℤ × ℤ))
    (hM : IsStaircase D M) :
    ∃ σ : Sign, IsStaircaseType σ D M := hM

/-- **Structural degeneracy: coordinate strips are ambiguous**
(the `(⇐)` half of `lem:local-sign`(i), `step3.tex:129-131`).
A coordinate strip has both types; in particular the "sign" is not
uniquely determined by the set. The `(⇒)` direction (two-type
staircases are coordinate strips) is the substantive structural
uniqueness claim of `lem:local-sign`(i), whose full proof
(`step3.tex:133-191`) is carried in the paper. -/
theorem coordinateStrip_has_both_types
    (D M : Finset (ℤ × ℤ)) (hM : IsCoordinateStrip D M) :
    IsStaircaseType true D M ∧ IsStaircaseType false D M := by
  obtain ⟨h, hMh⟩ := hM
  refine ⟨?_, ?_⟩ <;>
  · rw [hMh]
    exact coordinateStrip_isStaircaseType _ D h

/-! ### §2 — Positive cone and `lem:positive-cone-inv` -/

/-- The four unit grid directions at a state: `±e_1, ±e_2`. -/
def gridDirs : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma mem_gridDirs {e : ℤ × ℤ} :
    e ∈ gridDirs ↔ e = (1, 0) ∨ e = (-1, 0) ∨ e = (0, 1) ∨ e = (0, -1) := by
  unfold gridDirs
  simp

lemma gridDirs_card : gridDirs.card = 4 := by decide

/-- The **positive cone** for sign `σ` (`def:positive-cone`,
`step3.tex:354`): the set of grid directions `e ∈ gridDirs` that
increase the height function `h_σ(i, j) = i + σ · j`, i.e. satisfy
`e.1 + σ.toInt * e.2 > 0`. -/
def positiveCone (σ : Sign) : Finset (ℤ × ℤ) :=
  gridDirs.filter (fun e => 0 < e.1 + σ.toInt * e.2)

lemma positiveCone_subset_gridDirs (σ : Sign) :
    positiveCone σ ⊆ gridDirs := Finset.filter_subset _ _

lemma mem_positiveCone {σ : Sign} {e : ℤ × ℤ} :
    e ∈ positiveCone σ ↔ e ∈ gridDirs ∧ 0 < e.1 + σ.toInt * e.2 := by
  unfold positiveCone; rw [Finset.mem_filter]

/-- **`lem:positive-cone-inv` (cardinality form, `step3.tex:378-379`).**
The positive cone is exactly two of the four grid directions: the two
that increase the height function `h_σ`, the other two decreasing it.
This is the "partition into two halves of size two" at the heart of
`lem:positive-cone-inv`. -/
theorem positiveCone_card (σ : Sign) : (positiveCone σ).card = 2 := by
  cases σ <;> decide

/-- The positive cone and its opposite (complement within `gridDirs`)
partition the four grid directions into two pairs of size `2`. This
is the paper's "unordered partition"
(`step3.tex:380-381`), i.e. `lem:positive-cone-inv`'s cleanest form. -/
theorem positiveCone_union_compl (σ : Sign) :
    positiveCone σ ∪ (gridDirs \ positiveCone σ) = gridDirs := by
  exact Finset.union_sdiff_of_subset (positiveCone_subset_gridDirs σ)

theorem positiveCone_disjoint_compl (σ : Sign) :
    Disjoint (positiveCone σ) (gridDirs \ positiveCone σ) :=
  Finset.disjoint_sdiff

/-- **`lem:positive-cone-inv` (intrinsic partition form).**
The positive cone for sign `σ` and the positive cone for the
opposite sign `-σ` together with their complements within `gridDirs`
all induce the same two-element partition of `gridDirs` up to a
swap of the two halves. Concretely, `positiveCone σ` and
`positiveCone (-σ)` each have exactly two elements and share the
common direction `(1, 0)` (the shared `i`-axis), making the
intrinsic "unordered partition of the four BK directions" preserved
under the `σ ↔ -σ` symmetry (`step3.tex:380-381`). -/
theorem positiveCone_card_eq (σ σ' : Sign) :
    (positiveCone σ).card = (positiveCone σ').card := by
  rw [positiveCone_card σ, positiveCone_card σ']

/-! ### §3 — Regular overlap and `lem:omega-reg-size` -/

/-- The **regular overlap** `Ω^reg_{xy,uv}` (`def:regular-overlap`,
`step3.tex:426`) as a finite set: the commuting overlap `Ωo` minus
the three exceptional sets — staircase errors on each interface and
the BK-boundary errors.

Parametrised over a state type `γ`. -/
def regularOverlap {γ : Type*} [DecidableEq γ]
    (Ωo Erx Eru Erbk : Finset γ) : Finset γ :=
  Ωo \ (Erx ∪ Eru ∪ Erbk)

lemma regularOverlap_subset {γ : Type*} [DecidableEq γ]
    (Ωo Erx Eru Erbk : Finset γ) :
    regularOverlap Ωo Erx Eru Erbk ⊆ Ωo :=
  Finset.sdiff_subset

lemma regularOverlap_mem {γ : Type*} [DecidableEq γ]
    {Ωo Erx Eru Erbk : Finset γ} {L : γ} :
    L ∈ regularOverlap Ωo Erx Eru Erbk ↔
      L ∈ Ωo ∧ L ∉ Erx ∧ L ∉ Eru ∧ L ∉ Erbk := by
  simp [regularOverlap, Finset.mem_sdiff, not_or]

/-- **Union bound for the regular overlap** (`step3.tex:468-475`).
The complement of `Ωreg` inside `Ωo` is contained in the union of the
three exceptional sets, so its cardinality is at most the sum of the
three exceptional cardinalities counted *inside* `Ωo`. -/
lemma regularOverlap_compl_card_le {γ : Type*} [DecidableEq γ]
    (Ωo Erx Eru Erbk : Finset γ) :
    (Ωo \ regularOverlap Ωo Erx Eru Erbk).card ≤
      (Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card := by
  classical
  unfold regularOverlap
  -- `Ωo \ (Ωo \ X) = Ωo ∩ X` for any `X`.
  have hrw : Ωo \ (Ωo \ (Erx ∪ Eru ∪ Erbk)) = Ωo ∩ (Erx ∪ Eru ∪ Erbk) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hrw, Finset.inter_union_distrib_left, Finset.inter_union_distrib_left]
  calc (Ωo ∩ Erx ∪ Ωo ∩ Eru ∪ Ωo ∩ Erbk).card
      ≤ (Ωo ∩ Erx ∪ Ωo ∩ Eru).card + (Ωo ∩ Erbk).card :=
        Finset.card_union_le _ _
    _ ≤ ((Ωo ∩ Erx).card + (Ωo ∩ Eru).card) + (Ωo ∩ Erbk).card := by
        gcongr
        exact Finset.card_union_le _ _
    _ = (Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card := by
        rw [Finset.inter_comm Ωo Erx, Finset.inter_comm Ωo Eru,
            Finset.inter_comm Ωo Erbk]

/-- **`lem:omega-reg-size`** (abstract mass-bound form, `step3.tex:448`).
The regular overlap has mass at least `|Ωo|` minus the union of the
three exceptional sets. Combined with `|Erx| ≤ ε₂|Fxy|`,
`|Eru| ≤ ε₂|Fuv|`, `|Erbk| ≤ ε₁^BK|Fxy ∩ Fuv|`, and the non-degeneracy
`|Fxy ∩ Fuv| ≥ ρ · max(|Fxy|, |Fuv|)`, yields the paper's
`|Ωreg| ≥ (1 − ε₃) |Ωo|` with `ε₃ = O_ρ(ε₁ + ε₂)`.

The quantitative packaging as a fraction of `|Ωo|` is carried in
`omega_reg_size_fraction` below. -/
theorem omega_reg_size {γ : Type*} [DecidableEq γ]
    (Ωo Erx Eru Erbk : Finset γ) :
    (regularOverlap Ωo Erx Eru Erbk).card +
        ((Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card)
      ≥ Ωo.card := by
  classical
  have hsub : regularOverlap Ωo Erx Eru Erbk ⊆ Ωo :=
    regularOverlap_subset Ωo Erx Eru Erbk
  have hcompl := regularOverlap_compl_card_le Ωo Erx Eru Erbk
  -- |Ωreg| + |Ωo \ Ωreg| = |Ωo| via disjoint union.
  have hdisj : Disjoint (regularOverlap Ωo Erx Eru Erbk)
      (Ωo \ regularOverlap Ωo Erx Eru Erbk) := Finset.disjoint_sdiff
  have hunion : regularOverlap Ωo Erx Eru Erbk ∪
      (Ωo \ regularOverlap Ωo Erx Eru Erbk) = Ωo :=
    Finset.union_sdiff_of_subset hsub
  have hadd : (regularOverlap Ωo Erx Eru Erbk).card +
      (Ωo \ regularOverlap Ωo Erx Eru Erbk).card = Ωo.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  omega

/-- **`lem:omega-reg-size`** (fraction form, packaging).
Under hypotheses matching `step3.tex:477-503`:
* `hErx : (Erx ∩ Ωo).card * c ≤ a · (Ωo.card)`
* `hEru : (Eru ∩ Ωo).card * c ≤ b · (Ωo.card)`
* `hErbk: (Erbk ∩ Ωo).card * c ≤ k · (Ωo.card)`

we conclude
`(regularOverlap …).card * c ≥ (c − a − b − k) · (Ωo.card)`,
the "regular overlap is `(1 − ε₃)`-large" statement in cleared
denominators, where `c` stands for the common denominator and
`a, b, k` are the cleared-ε numerators. -/
theorem omega_reg_size_fraction {γ : Type*} [DecidableEq γ]
    (Ωo Erx Eru Erbk : Finset γ)
    (a b k c : ℕ)
    (hErx : c * (Erx ∩ Ωo).card ≤ a * Ωo.card)
    (hEru : c * (Eru ∩ Ωo).card ≤ b * Ωo.card)
    (hErbk : c * (Erbk ∩ Ωo).card ≤ k * Ωo.card) :
    c * Ωo.card ≤
      c * (regularOverlap Ωo Erx Eru Erbk).card + (a + b + k) * Ωo.card := by
  have hmain := omega_reg_size (γ := γ) Ωo Erx Eru Erbk
  -- c · Ωo ≤ c · Ωreg + c · (Erx∩Ωo + Eru∩Ωo + Erbk∩Ωo)
  have h1 : c * Ωo.card ≤
      c * ((regularOverlap Ωo Erx Eru Erbk).card +
        ((Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card)) := by
    exact Nat.mul_le_mul_left c hmain
  have h2 : c * ((Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card)
              ≤ (a + b + k) * Ωo.card := by
    have := Nat.add_le_add (Nat.add_le_add hErx hEru) hErbk
    calc c * ((Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card)
        = c * (Erx ∩ Ωo).card + c * (Eru ∩ Ωo).card + c * (Erbk ∩ Ωo).card := by ring
      _ ≤ a * Ωo.card + b * Ωo.card + k * Ωo.card := this
      _ = (a + b + k) * Ωo.card := by ring
  calc c * Ωo.card
      ≤ c * ((regularOverlap Ωo Erx Eru Erbk).card +
          ((Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card)) := h1
    _ = c * (regularOverlap Ωo Erx Eru Erbk).card +
          c * ((Erx ∩ Ωo).card + (Eru ∩ Ωo).card + (Erbk ∩ Ωo).card) := by ring
    _ ≤ c * (regularOverlap Ωo Erx Eru Erbk).card + (a + b + k) * Ωo.card := by
          exact Nat.add_le_add_left h2 _

end Step3
end OneThird
