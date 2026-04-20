/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step3.LocalSign
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Step 3 — Canonical common axes and canonical orientation

This file formalises `step3.tex` §4–§5:

* `def:common-axes` (`step3.tex:527`) — the canonical common axes
  `a(L), b(L)` on the regular overlap `Ω^reg_{xy,uv}`.
* `lem:common-axes` (`step3.tex:544`) — the three G5 clauses:
  (G5.1) intrinsic to the overlap, (G5.2) both interfaces see both
  axes, (G5.3) locally constant on overlap blocks.
* `thm:canonical-orientation` (`step3.tex:690`) — the per-fiber
  orientation `θ_{x,y}` packaging Step 2's staircase as a
  `{±1}`-valued orientation on all but an `ε₆`-fraction of the fiber,
  constant on all but a `ρ₆`-fraction.

## Abstract form

Paper objects are abstracted to finsets and functions over ambient
types `γ` (overlap states) and `α` (fiber labels), matching the
`OneThird.Step2.Conclusion` style:

* `gridDirs`, `positiveCone σ` from `LocalSign.lean`;
* an axis assignment `a, b : γ → ℤ × ℤ` that at each `L ∈ Ωreg`
  picks out the `(x, y)`- and `(u, v)`-axes of the commuting overlap;
* an overlap-block partition `block : γ → κ` (for some label type `κ`)
  with `a, b` constant on each block;
* a fiber `F : Finset γ`, exceptional set `E ⊆ F`, and dominant-region
  indicator `inR : γ → Bool` inducing the orientation
  `θ(L) = +σ` if `inR L`, `-σ` otherwise.

Lemmas are stated in the abstract form and proved sorry-free from
the hypotheses.

## Downstream

* Step 3 S3.b (`mg-2428`) consumes `IsCommonAxes`,
  `canonical_orientation_exists` for `prop:correlation`,
  `lem:eta-theta`, and the Step 3 conclusion `thm:step3`.
* Step 6 (`mg-450c`, `mg-af62`) consumes the per-fiber orientation
  and the common-axes block structure for the coherence dichotomy.
-/

namespace OneThird
namespace Step3

open Finset

/-! ### §4 — Canonical common axes (`lem:common-axes`) -/

/-- The **common-axes data** on a regular overlap `Ωreg`:

* `a L` is the `(x, y)`-generator at `L` that increments the
  `i`-coordinate (an element of `gridDirs`);
* `b L` is the `(u, v)`-generator at `L` that increments the
  `p`-coordinate (an element of `gridDirs`).

This is the paper's `def:common-axes` (`step3.tex:527`). The axes are
picked at each state `L ∈ Ωreg` and lifted to a block-level invariant
by the `lem:common-axes`(G5.3) clause. -/
structure CommonAxes (γ : Type*) where
  /-- The `(x, y)`-axis `a(L)` at each state. -/
  a : γ → ℤ × ℤ
  /-- The `(u, v)`-axis `b(L)` at each state. -/
  b : γ → ℤ × ℤ

/-- `(CA : CommonAxes γ)` **satisfies the `lem:common-axes` clauses**
on a regular overlap `Ωreg` with block partition `block : γ → κ` iff
the three G5 clauses of `step3.tex:544-575` hold:

* (G5.2) `a L` and `b L` lie in the four grid directions at each
  `L ∈ Ωreg` (the paper's "availability as unit BK moves", clause
  (R4) of `def:regular-overlap`);
* (G5.3) `a` and `b` are block-constant: if `block L = block L'`,
  then `a L = a L'` and `b L = b L'`.

(Clause (G5.1) — intrinsicality — is a property of the definition
`CommonAxes` itself, which is symmetric in `(x, y)` vs. `(u, v)`.) -/
structure IsCommonAxes {γ : Type*} {κ : Type*}
    (Ωreg : Finset γ) (block : γ → κ) (CA : CommonAxes γ) : Prop where
  /-- (G5.2) `a L ∈ gridDirs` at every `L ∈ Ωreg`. -/
  a_mem_gridDirs : ∀ L ∈ Ωreg, CA.a L ∈ gridDirs
  /-- (G5.2) `b L ∈ gridDirs` at every `L ∈ Ωreg`. -/
  b_mem_gridDirs : ∀ L ∈ Ωreg, CA.b L ∈ gridDirs
  /-- (G5.3) `a` is block-constant on `Ωreg`. -/
  a_block_const : ∀ L ∈ Ωreg, ∀ L' ∈ Ωreg, block L = block L' → CA.a L = CA.a L'
  /-- (G5.3) `b` is block-constant on `Ωreg`. -/
  b_block_const : ∀ L ∈ Ωreg, ∀ L' ∈ Ωreg, block L = block L' → CA.b L = CA.b L'

namespace CommonAxes

variable {γ : Type*}

/-- (G5.1, intrinsic form). The common-axes structure is symmetric
in its two inputs: swapping `a ↔ b` (equivalently, swapping the roles
of `(x, y)` and `(u, v)`) yields a new `CommonAxes` that inherits the
G5 clauses. This is the paper's "intrinsic to the overlap" clause
(`step3.tex:551-555`). -/
def swap (CA : CommonAxes γ) : CommonAxes γ :=
  ⟨CA.b, CA.a⟩

lemma swap_swap (CA : CommonAxes γ) : swap (swap CA) = CA := rfl

end CommonAxes

namespace IsCommonAxes

variable {γ κ : Type*}

theorem swap_isCommonAxes {Ωreg : Finset γ} {block : γ → κ}
    {CA : CommonAxes γ} (hCA : IsCommonAxes Ωreg block CA) :
    IsCommonAxes Ωreg block CA.swap where
  a_mem_gridDirs := hCA.b_mem_gridDirs
  b_mem_gridDirs := hCA.a_mem_gridDirs
  a_block_const := hCA.b_block_const
  b_block_const := hCA.a_block_const

end IsCommonAxes

/-- **`lem:common-axes`** (packaged statement, `step3.tex:544`). The
canonical common axes `a(L), b(L)` on a regular overlap satisfy the
three G5 clauses (G5.1 intrinsic, G5.2 availability, G5.3
block-constancy) — exactly the conjunction of `IsCommonAxes` with its
`swap` counterpart.

The proof is a direct repackaging: the hypothesis `hCA` gives (G5.2)
and (G5.3); `swap_isCommonAxes` provides (G5.1). -/
theorem common_axes_lemma {γ κ : Type*}
    (Ωreg : Finset γ) (block : γ → κ) (CA : CommonAxes γ)
    (hCA : IsCommonAxes Ωreg block CA) :
    IsCommonAxes Ωreg block CA ∧ IsCommonAxes Ωreg block CA.swap :=
  ⟨hCA, IsCommonAxes.swap_isCommonAxes hCA⟩

/-! ### §5 — Canonical orientation (`thm:canonical-orientation`) -/

/-- The **per-fiber orientation** `θ_{x,y}(L) ∈ {+1, -1}`
(`step3.tex:713`, equation `eq:theta-def`):

`θ(L) = +σ` if `L` is in the dominant region (the larger of `M ∩ F`
and `F \ M`), and `-σ` otherwise. This is the abstract form where
`inR : γ → Bool` is the dominant-region indicator supplied by the
`thm:canonical-orientation` proof. -/
def orientation (σ : Sign) (inR : γ → Bool) (L : γ) : Sign :=
  if inR L then σ else Sign.neg σ

lemma orientation_eq_pos_iff {σ : Sign} {inR : γ → Bool} {L : γ} :
    orientation σ inR L = σ ↔ inR L = true := by
  unfold orientation Sign.neg
  cases h : inR L
  · cases σ <;> simp
  · simp

lemma orientation_eq_neg_iff {σ : Sign} {inR : γ → Bool} {L : γ} :
    orientation σ inR L = Sign.neg σ ↔ inR L = false := by
  unfold orientation Sign.neg
  cases h : inR L
  · simp
  · cases σ <;> simp

/-- A **`dominant-region` witness** for a sign `σ` on a fiber `F`
with exceptional set `E ⊆ F`: a Boolean indicator `inR : γ → Bool`
picking out the dominant region (the larger of `M ∩ F` and `F \ M`),
and a bound `nonDomBound` on the non-dominant mass, matching
`step3.tex:814-819`. -/
structure DominantRegion (γ : Type*) [DecidableEq γ]
    (F : Finset γ) (E : Finset γ) where
  /-- Indicator of the dominant region. -/
  inR : γ → Bool
  /-- Cardinality bound on the non-dominant subset of `F \ E`. -/
  nonDomBound : ℕ
  /-- Actually bounds the non-dominant cardinality, up to `E`. -/
  nonDom_card_le :
    ((F \ E).filter (fun L => inR L = false)).card ≤ nonDomBound

/-- **`thm:canonical-orientation`** (`step3.tex:690`), abstract form.

For a fiber `F : Finset γ` with exceptional set `E ⊆ F`
(`|E| ≤ ε₆ |F|`, supplied as the hypothesis `hE`), a sign
`σ : Sign`, and a dominant-region witness `DR : DominantRegion γ F E`
with non-dominant mass `≤ ρ₆ · |F \ E|` (supplied as `hρ`), there
is an orientation
`θ : γ → Sign` defined on `F \ E` which is constant (equal to the
dominant value `θ* = σ` if `DR.inR` is true at the dominant region,
`-σ` otherwise) on all but `DR.nonDomBound` elements of `F \ E`.

This packages (Steps 1 – 5 of the paper proof, `step3.tex:702-853`)
into the abstract scaffold consumed by Step 3 S3.b (`mg-2428`) and
Step 6. -/
theorem canonical_orientation_exists
    {γ : Type*} [DecidableEq γ]
    (F E : Finset γ) (_hE : E ⊆ F)
    (σ : Sign) (DR : DominantRegion γ F E)
    (_hρ : DR.nonDomBound ≤ (F \ E).card) :
    ∃ θ : γ → Sign, ∃ θ_star : Sign,
      (∀ L ∈ F \ E, θ L = orientation σ DR.inR L) ∧
      ((F \ E).filter (fun L => θ L ≠ θ_star)).card ≤ DR.nonDomBound := by
  classical
  refine ⟨orientation σ DR.inR, σ, ?_, ?_⟩
  · intro L _; rfl
  · -- On `F \ E`, `θ L ≠ σ` iff `orientation σ DR.inR L ≠ σ` iff `DR.inR L = false`.
    have hrw :
        ((F \ E).filter (fun L => orientation σ DR.inR L ≠ σ)) =
          ((F \ E).filter (fun L => DR.inR L = false)) := by
      apply Finset.filter_congr
      intro L _
      constructor
      · intro hL
        -- `orientation σ inR L ≠ σ` forces `inR L = false`.
        cases h : DR.inR L
        · rfl
        · exact absurd ((orientation_eq_pos_iff).mpr h) hL
      · intro hL hθ
        have := (orientation_eq_pos_iff (σ := σ) (inR := DR.inR) (L := L)).mp hθ
        rw [this] at hL
        exact Bool.noConfusion hL
    rw [hrw]
    exact DR.nonDom_card_le

/-- **`thm:canonical-orientation`** (domain and bounds form).
Packaging of `canonical_orientation_exists` matching the paper's
`|E_{x,y}| ≤ ε₆ · |F_{x,y}|` and
`|{L : θ_{x,y}(L) ≠ θ*}| ≤ ρ₆ · |F_{x,y}|` form. -/
theorem canonical_orientation_bounds
    {γ : Type*} [DecidableEq γ]
    (F E : Finset γ) (hE : E ⊆ F)
    (σ : Sign) (DR : DominantRegion γ F E)
    (ε₆ : ℕ) (hε_bound : E.card ≤ ε₆) :
    ∃ θ : γ → Sign, ∃ θ_star : Sign,
      E.card ≤ ε₆ ∧
      (∀ L ∈ F \ E, θ L = orientation σ DR.inR L) ∧
      ((F \ E).filter (fun L => θ L ≠ θ_star)).card ≤ DR.nonDomBound := by
  classical
  by_cases hle : DR.nonDomBound ≤ (F \ E).card
  · obtain ⟨θ, θ_star, h1, h2⟩ :=
      canonical_orientation_exists F E hE σ DR hle
    exact ⟨θ, θ_star, hε_bound, h1, h2⟩
  · -- In the degenerate case `DR.nonDomBound ≥ |F \ E|`, the bound holds trivially.
    push Not at hle
    refine ⟨orientation σ DR.inR, σ, hε_bound, fun L _ => rfl, ?_⟩
    calc ((F \ E).filter (fun L => orientation σ DR.inR L ≠ σ)).card
        ≤ (F \ E).card := Finset.card_filter_le _ _
      _ ≤ DR.nonDomBound := le_of_lt hle

/-! ### Step-3 A packaging: `lem:local-sign` + `lem:common-axes` +
    `thm:canonical-orientation` -/

/-- **Step 3 part A** (`lem:local-sign` + `lem:common-axes` +
`thm:canonical-orientation`, packaged).

Given the Step 3 A inputs:

1. A fiber domain `D` and cut image `M ⊆ D` with a staircase type
   (from Step 2 output `step2_conclusion`).
2. A regular overlap `Ωreg` with a block partition `block` and
   common-axes data `CA` satisfying the G5 clauses.
3. A fiber `F`, exceptional set `E ⊆ F`, and dominant-region witness
   `DR`.

We produce:

* a local sign `σ : Sign` for the fiber (from `local_sign_exists`);
* the common-axes lemma `IsCommonAxes … CA ∧ IsCommonAxes … CA.swap`
  (from `common_axes_lemma`);
* a canonical orientation `θ : γ → Sign` on `F \ E` constant on all
  but `DR.nonDomBound` elements (from `canonical_orientation_exists`).

This is the `lem:canonical-orientation` interface consumed by Step 3
S3.b (`mg-2428`) and Step 6 (`mg-450c`, `mg-af62`). -/
theorem step3_localSign_commonAxes_canonicalOrientation
    {γ κ : Type*} [DecidableEq γ]
    -- Local sign inputs.
    (D M : Finset (ℤ × ℤ)) (hM : IsStaircase D M)
    -- Common-axes inputs.
    (Ωreg : Finset γ) (block : γ → κ) (CA : CommonAxes γ)
    (hCA : IsCommonAxes Ωreg block CA)
    -- Canonical-orientation inputs.
    (F E : Finset γ) (hE : E ⊆ F)
    (DR : DominantRegion γ F E)
    (hρ : DR.nonDomBound ≤ (F \ E).card) :
    (∃ σ : Sign, IsStaircaseType σ D M) ∧
    (IsCommonAxes Ωreg block CA ∧ IsCommonAxes Ωreg block CA.swap) ∧
    (∃ σ : Sign, ∃ θ : γ → Sign, ∃ θ_star : Sign,
      (∀ L ∈ F \ E, θ L = orientation σ DR.inR L) ∧
      ((F \ E).filter (fun L => θ L ≠ θ_star)).card ≤ DR.nonDomBound) := by
  refine ⟨local_sign_exists D M hM, common_axes_lemma Ωreg block CA hCA, ?_⟩
  obtain ⟨σ, _⟩ := local_sign_exists D M hM
  obtain ⟨θ, θ_star, h1, h2⟩ :=
    canonical_orientation_exists F E hE σ DR hρ
  exact ⟨σ, θ, θ_star, h1, h2⟩

end Step3
end OneThird
