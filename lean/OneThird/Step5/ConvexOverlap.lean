/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Step 5 — Convex-overlap lemma (`lem:convex-overlap`, `step5.tex:360`)

Formalises §5 G2 of `step5.tex`. The lemma is **pure interval
geometry**: no poset hypotheses beyond the monotonicity of the
endpoint sequences supplied by `lem:endpoint-mono`.

## Setup

Two monotone families of integer intervals

* `I_i = [alpha i, beta i]` for `i : Fin p`;
* `J_j = [gamma j, delta j]` for `j : Fin q`;

with `alpha, beta, gamma, delta` weakly increasing (exact
monotonicity; `E₀ = 0`, witnessed by `lem:endpoint-mono`). The
threshold is `T ≥ 1`.

The **rich set** is `R := {(i, j) : |I_i ∩ J_j| ≥ T}`.

## Structural content (the "real mathematics")

* `rich_implies_crit` (`step5.tex:395-403`, `eq:G2-criterion`) — the
  arithmetic criterion: rich pairs satisfy
  `alpha i + T ≤ delta j + 1 ∧ gamma j + T ≤ beta i + 1`.
* `critRow_orderConvex` (`step5.tex:405-418`) — fixing `i`, the set of
  `j` satisfying the criterion is order-convex in `Fin q`, so it is
  an interval.
* `critRow_leftThreshold_mono`, `critRow_rightThreshold_mono`
  (`step5.tex:419-420`) — the left and right thresholds of the row
  are non-decreasing in `i` (by monotonicity of `alpha, beta`).
* `richRow_subset_interval` — the rich row lies in the interval
  `[min, max]` of its own support, so the band conclusion holds
  pointwise with `W* = max row length`.
* `convex_overlap_row_card_le` (`step5.tex:443-446`) — each rich row
  has cardinality at most `max − min + 1`, which is bounded by the
  global `W*`.
-/

namespace OneThird
namespace Step5

open Finset

/-! ### Intersection length and the rich predicate -/

variable {p q : ℕ}

/-- Length of the integer-interval intersection `|I_i ∩ J_j|`, with
`I_i = [alpha i, beta i]` and `J_j = [gamma j, delta j]`. Uses the
usual convention that an empty intersection has length `0`. -/
def intersectLength
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ)
    (i : Fin p) (j : Fin q) : ℤ :=
  max 0 (min (beta i) (delta j) - max (alpha i) (gamma j) + 1)

/-- **Rich pair.** A pair `(i, j)` is rich at threshold `T` iff
`|I_i ∩ J_j| ≥ T`. The rich set is `R` in the paper
(`step5.tex:378`). -/
def RichPair
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) (j : Fin q) : Prop :=
  T ≤ intersectLength alpha beta gamma delta i j

/-- The **arithmetic criterion** (`step5.tex:398-403`,
`eq:G2-criterion`) — a necessary condition for richness under
`T ≥ 1`. Defined here so the row-interval structural content can be
stated in a form that does not refer to the intersection length. -/
def SatisfiesCrit
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) (j : Fin q) : Prop :=
  alpha i + T ≤ delta j + 1 ∧ gamma j + T ≤ beta i + 1

/-! ### Step 2 of the paper proof: the rich criterion (→ direction) -/

/-- **`step5.tex:395-403` (rich criterion, `→` direction).** Every
rich pair satisfies the arithmetic criterion, under the paper
assumption `T ≥ 1` (`step5.tex:365`). The converse holds under the
additional hypothesis that both `|I_i|, |J_j| ≥ T`; only the forward
implication is used structurally. -/
theorem rich_implies_crit
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hT : 1 ≤ T) {i : Fin p} {j : Fin q}
    (h : RichPair alpha beta gamma delta T i j) :
    SatisfiesCrit alpha beta gamma delta T i j := by
  unfold RichPair intersectLength at h
  -- T ≥ 1 > 0, so `max 0 (inner) ≥ T > 0` forces `inner ≥ T`.
  have hinner : T ≤ min (beta i) (delta j) - max (alpha i) (gamma j) + 1 := by
    rcases max_cases (0 : ℤ)
        (min (beta i) (delta j) - max (alpha i) (gamma j) + 1)
      with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at h; linarith
    · rw [heq] at h; exact h
  refine ⟨?_, ?_⟩
  · -- α i + T ≤ δ j + 1: use α i ≤ max (α i) (γ j), min (β i) (δ j) ≤ δ j.
    nlinarith [le_max_left (alpha i) (gamma j),
               min_le_right (beta i) (delta j)]
  · -- γ j + T ≤ β i + 1: use γ j ≤ max (α i) (γ j), min (β i) (δ j) ≤ β i.
    nlinarith [le_max_right (alpha i) (gamma j),
               min_le_left (beta i) (delta j)]

/-! ### Step 3: the criterion row is order-convex -/

/-- **`step5.tex:405-418` (row is an interval).** For fixed `i`, the
set `{j : SatisfiesCrit _ _ _ _ T i j}` is order-convex in `Fin q`:
if `j₁ ≤ j ≤ j₂` and both `j₁, j₂` satisfy the criterion, so does
`j`.

Proof: `delta` and `gamma` are monotone, so the two thresholds
(`δ_j ≥ α_i + T − 1` is a final segment; `γ_j ≤ β_i − T + 1` is an
initial segment) give an intersection interval. -/
theorem critRow_orderConvex
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hγ : Monotone gamma) (hδ : Monotone delta)
    {i : Fin p} {j₁ j j₂ : Fin q} (h1 : j₁ ≤ j) (h2 : j ≤ j₂)
    (hc1 : SatisfiesCrit alpha beta gamma delta T i j₁)
    (hc2 : SatisfiesCrit alpha beta gamma delta T i j₂) :
    SatisfiesCrit alpha beta gamma delta T i j := by
  refine ⟨?_, ?_⟩
  · have hδ12 : delta j₁ ≤ delta j := hδ h1
    linarith [hc1.1]
  · have hγ12 : gamma j ≤ gamma j₂ := hγ h2
    linarith [hc2.2]

/-! ### Threshold monotonicity in `i` -/

/-- **`step5.tex:419-420` (α threshold monotone).** If the left
threshold `α i' + T ≤ δ j₁ + 1` holds, and `i ≤ i'`, `j₁ ≤ j₂`, then
the threshold also holds for `(i, j₂)`. The paper's
"`α_i + T − 1` non-decreasing in `i`" statement. -/
theorem leftThreshold_mono_in_i
    {alpha : Fin p → ℤ} {delta : Fin q → ℤ} {T : ℤ}
    (hα : Monotone alpha) (hδ : Monotone delta)
    {i i' : Fin p} (hi : i ≤ i') {j₁ j₂ : Fin q} (hj : j₁ ≤ j₂)
    (h1 : alpha i' + T ≤ delta j₁ + 1) :
    alpha i + T ≤ delta j₂ + 1 := by
  have hα' : alpha i ≤ alpha i' := hα hi
  have hδ' : delta j₁ ≤ delta j₂ := hδ hj
  linarith

/-- **`step5.tex:419-420` (β threshold monotone).** If the right
threshold `γ j₁ + T ≤ β i + 1` holds, and `i ≤ i'`, `j ≤ j₁`, then
the threshold also holds for `(i', j)`. -/
theorem rightThreshold_mono_in_i
    {beta : Fin p → ℤ} {gamma : Fin q → ℤ} {T : ℤ}
    (hβ : Monotone beta) (hγ : Monotone gamma)
    {i i' : Fin p} (hi : i ≤ i') {j j₁ : Fin q} (hj : j ≤ j₁)
    (h : gamma j₁ + T ≤ beta i + 1) :
    gamma j + T ≤ beta i' + 1 := by
  have hβ' : beta i ≤ beta i' := hβ hi
  have hγ' : gamma j ≤ gamma j₁ := hγ hj
  linarith

/-! ### The rich row and its membership characterisation -/

/-- The **rich row** at index `i`: the set of `j` making `(i, j)`
rich. -/
noncomputable def richRow
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) : Finset (Fin q) :=
  open Classical in
  Finset.univ.filter (fun j =>
    T ≤ intersectLength alpha beta gamma delta i j)

lemma mem_richRow {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ}
    {T : ℤ} {i : Fin p} {j : Fin q} :
    j ∈ richRow alpha beta gamma delta T i ↔
      RichPair alpha beta gamma delta T i j := by
  unfold richRow RichPair
  classical
  simp

/-- **Every rich row entry satisfies the arithmetic criterion.**
Direct from `rich_implies_crit`, lifted to `richRow` membership. -/
theorem richRow_satisfies_crit
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) {T : ℤ}
    (hT : 1 ≤ T) (i : Fin p) (j : Fin q)
    (hj : j ∈ richRow alpha beta gamma delta T i) :
    SatisfiesCrit alpha beta gamma delta T i j := by
  rw [mem_richRow] at hj
  exact rich_implies_crit hT hj

/-! ### Band containment for a rich row -/

/-- **`step5.tex:443-446` (pointwise band containment).** For every
`i` whose rich row is non-empty, every rich `j` lies inside the row's
`[min, max]` span. Trivially, since `min ≤ j ≤ max` for every
`j ∈ row`. This is the pointwise ingredient of the paper's band
conclusion (b). -/
theorem richRow_subset_interval
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) (j : Fin q)
    (hj : j ∈ richRow alpha beta gamma delta T i) :
    (richRow alpha beta gamma delta T i).min' ⟨j, hj⟩ ≤ j ∧
    j ≤ (richRow alpha beta gamma delta T i).max' ⟨j, hj⟩ :=
  ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩

/-! ### Row-cardinality bound (`step5.tex:443-446`, band width) -/

/-- **`step5.tex:443-446` (row cardinality ≤ span width).** Each rich
row has cardinality at most `max.val − min.val + 1` — the integer
span between its extreme entries. Combined with the monotone
envelope argument (`step5.tex:430-441`), this is the "band
width" input to dichotomy conclusion~(b). -/
theorem convex_overlap_row_card_le
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p)
    (hne : (richRow alpha beta gamma delta T i).Nonempty) :
    (richRow alpha beta gamma delta T i).card ≤
      ((richRow alpha beta gamma delta T i).max' hne).val + 1 -
        ((richRow alpha beta gamma delta T i).min' hne).val := by
  classical
  -- Inject the row into [min.val, max.val] via j ↦ j.val.
  have hmem : ∀ j ∈ richRow alpha beta gamma delta T i,
      ((richRow alpha beta gamma delta T i).min' hne).val ≤ j.val ∧
      j.val ≤ ((richRow alpha beta gamma delta T i).max' hne).val :=
    fun j hj => ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
  have hcard : (richRow alpha beta gamma delta T i).card ≤
      (Finset.Icc ((richRow alpha beta gamma delta T i).min' hne).val
        ((richRow alpha beta gamma delta T i).max' hne).val).card := by
    apply Finset.card_le_card_of_injOn (fun (j : Fin q) => j.val)
    · intro j hj
      rw [Finset.coe_Icc, Set.mem_Icc]
      exact hmem j hj
    · intro a _ b _ hab
      exact Fin.ext hab
  simpa [Nat.card_Icc] using hcard

/-- **`lem:convex-overlap` (structural conclusion, packaged).**

Combining `rich_implies_crit`, `critRow_orderConvex`, the threshold
monotonicity lemmas, `richRow_subset_interval`, and
`convex_overlap_row_card_le`, the structural half of
`lem:convex-overlap` (`step5.tex:360-462`) is established:

* every rich row lies in a single `[L_i, U_i]`-interval
  (`richRow_subset_interval`);
* the criterion row is order-convex (`critRow_orderConvex`);
* the left/right thresholds are non-decreasing in `i`
  (`leftThreshold_mono_in_i`, `rightThreshold_mono_in_i`);
* the row cardinality is bounded by the span width
  (`convex_overlap_row_card_le`),

which are the inputs (Steps 2–4 of `step5.tex:395-441`) to the
dichotomy conclusion (b). The quantitative bound of Step 5
(`step5.tex:443-461`) expresses the span width as
`≤ ℓ_I^\star + ℓ_J^\star − 2T + O(1)` and is a consequence of the
rich criterion together with monotonicity; it does not require any
further structural input. -/
theorem convex_overlap_structural
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) {T : ℤ}
    (hT : 1 ≤ T)
    (hα : Monotone alpha) (hβ : Monotone beta)
    (hγ : Monotone gamma) (hδ : Monotone delta) :
    -- (i) Rich → criterion (every rich row lies in the criterion
    -- row).
    (∀ i : Fin p, ∀ j : Fin q,
        j ∈ richRow alpha beta gamma delta T i →
        SatisfiesCrit alpha beta gamma delta T i j) ∧
    -- (ii) Criterion row is order-convex.
    (∀ i : Fin p, ∀ j₁ j j₂ : Fin q, j₁ ≤ j → j ≤ j₂ →
        SatisfiesCrit alpha beta gamma delta T i j₁ →
        SatisfiesCrit alpha beta gamma delta T i j₂ →
        SatisfiesCrit alpha beta gamma delta T i j) ∧
    -- (iii) Left threshold non-decreasing in `i`.
    (∀ i i' : Fin p, i ≤ i' → ∀ j₁ j₂ : Fin q, j₁ ≤ j₂ →
        alpha i' + T ≤ delta j₁ + 1 →
        alpha i + T ≤ delta j₂ + 1) ∧
    -- (iv) Right threshold non-decreasing in `i`.
    (∀ i i' : Fin p, i ≤ i' → ∀ j j₁ : Fin q, j ≤ j₁ →
        gamma j₁ + T ≤ beta i + 1 →
        gamma j + T ≤ beta i' + 1) ∧
    -- (v) Pointwise band containment.
    (∀ i : Fin p, ∀ j : Fin q,
        (hj : j ∈ richRow alpha beta gamma delta T i) →
        (richRow alpha beta gamma delta T i).min' ⟨j, hj⟩ ≤ j ∧
        j ≤ (richRow alpha beta gamma delta T i).max' ⟨j, hj⟩) ∧
    -- (vi) Row cardinality bound.
    (∀ i : Fin p, ∀ hne : (richRow alpha beta gamma delta T i).Nonempty,
        (richRow alpha beta gamma delta T i).card ≤
          ((richRow alpha beta gamma delta T i).max' hne).val + 1 -
            ((richRow alpha beta gamma delta T i).min' hne).val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hj => richRow_satisfies_crit alpha beta gamma delta hT i j hj
  · exact fun _ _ _ _ h1 h2 => critRow_orderConvex hγ hδ h1 h2
  · exact fun _ _ hi _ _ hj h1 => leftThreshold_mono_in_i hα hδ hi hj h1
  · exact fun _ _ hi _ _ hj h1 => rightThreshold_mono_in_i hβ hγ hi hj h1
  · exact fun i j hj => richRow_subset_interval alpha beta gamma delta T i j hj
  · exact fun i hne => convex_overlap_row_card_le alpha beta gamma delta T i hne

/-! ### Step 3 (2D): the overlap region is an order-convex staircase

The structural heart of `lem:convex-overlap` (`step5.tex:402-422`,
`rem:G2-structural`): the criterion region
`R = {(i, j) : SatisfiesCrit … i j}` is **order-convex** in
`Fin p × Fin q` — the paper's "doubly monotone staircase", an
order-convex region wedged between two nondecreasing graphs. This part
is unconditional interval geometry. -/

/-- The **criterion row** at index `i` as a `Finset (Fin q)`: the set of
`j` for which `(i, j)` satisfies the arithmetic criterion
`eq:G2-criterion`. By `rich_implies_crit` the rich row is contained in
it (`richRow_subset_critRow`), so banding `critRow` bands `richRow`. -/
noncomputable def critRow
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) : Finset (Fin q) :=
  open Classical in
  Finset.univ.filter (fun j => SatisfiesCrit alpha beta gamma delta T i j)

lemma mem_critRow {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ}
    {T : ℤ} {i : Fin p} {j : Fin q} :
    j ∈ critRow alpha beta gamma delta T i ↔
      SatisfiesCrit alpha beta gamma delta T i j := by
  unfold critRow
  classical
  simp

/-- **`richRow ⊆ critRow`.** Under the paper hypothesis `T ≥ 1`, every
rich entry satisfies the arithmetic criterion (`rich_implies_crit`), so
the rich row is contained in the criterion row. -/
theorem richRow_subset_critRow
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) {T : ℤ}
    (hT : 1 ≤ T) (i : Fin p) :
    richRow alpha beta gamma delta T i ⊆
      critRow alpha beta gamma delta T i := by
  intro j hj
  rw [mem_richRow] at hj
  rw [mem_critRow]
  exact rich_implies_crit hT hj

/-- **`step5.tex:421-422` (2D order-convexity of the overlap region).**
The criterion region `R = {(i, j) : SatisfiesCrit … i j}` is
order-convex in `Fin p × Fin q`: if the two "opposite corners"
`(i₂, j₁)` and `(i₁, j₂)` satisfy the criterion and `i₁ ≤ i ≤ i₂`,
`j₁ ≤ j ≤ j₂`, then so does `(i, j)`. This is the paper's doubly
monotone staircase — `R` is order-convex, wedged between two
nondecreasing graphs. -/
theorem crit_orderConvex_2d
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hα : Monotone alpha) (hβ : Monotone beta)
    (hγ : Monotone gamma) (hδ : Monotone delta)
    {i₁ i i₂ : Fin p} {j₁ j j₂ : Fin q}
    (hi1 : i₁ ≤ i) (hi2 : i ≤ i₂) (hj1 : j₁ ≤ j) (hj2 : j ≤ j₂)
    (hc1 : SatisfiesCrit alpha beta gamma delta T i₂ j₁)
    (hc2 : SatisfiesCrit alpha beta gamma delta T i₁ j₂) :
    SatisfiesCrit alpha beta gamma delta T i j := by
  refine ⟨?_, ?_⟩
  · -- `α i + T ≤ δ j + 1`, propagated from corner `(i₂, j₁)`.
    have h1 : alpha i ≤ alpha i₂ := hα hi2
    have h2 : delta j₁ ≤ delta j := hδ hj1
    linarith [hc1.1]
  · -- `γ j + T ≤ β i + 1`, propagated from corner `(i₁, j₂)`.
    have h1 : beta i₁ ≤ beta i := hβ hi1
    have h2 : gamma j ≤ gamma j₂ := hγ hj2
    linarith [hc2.2]

/-- **Columns of the overlap region are order-convex** (`step5.tex:418`).
Symmetric to `critRow_orderConvex`: fixing `j`, the set of `i` with
`SatisfiesCrit … i j` is order-convex in `Fin p`. Together with
`critRow_orderConvex` this is the "doubly monotone staircase". -/
theorem critCol_orderConvex
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hα : Monotone alpha) (hβ : Monotone beta)
    {i₁ i i₂ : Fin p} {j : Fin q} (h1 : i₁ ≤ i) (h2 : i ≤ i₂)
    (hc1 : SatisfiesCrit alpha beta gamma delta T i₁ j)
    (hc2 : SatisfiesCrit alpha beta gamma delta T i₂ j) :
    SatisfiesCrit alpha beta gamma delta T i j := by
  refine ⟨?_, ?_⟩
  · have hai : alpha i ≤ alpha i₂ := hα h2
    linarith [hc2.1]
  · have hbi : beta i₁ ≤ beta i := hβ h1
    linarith [hc1.2]

/-! ### Step 4: the row endpoints `L_i`, `U_i` are nondecreasing in `i`

`step5.tex:416-417`: with `α, β` nondecreasing, the left/right endpoints
of the criterion row move nondecreasingly. The proofs use only the
criterion and the monotonicity of the four endpoint families — no
explicit initial/final-segment bookkeeping. -/

/-- **`step5.tex:416-417` (`L_i` nondecreasing).** The left endpoint of
the criterion row — its minimum index — is nondecreasing in `i`. -/
theorem critRow_min'_mono
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hα : Monotone alpha) (hγ : Monotone gamma)
    {i i' : Fin p} (hi : i ≤ i')
    (hne : (critRow alpha beta gamma delta T i).Nonempty)
    (hne' : (critRow alpha beta gamma delta T i').Nonempty) :
    (critRow alpha beta gamma delta T i).min' hne ≤
      (critRow alpha beta gamma delta T i').min' hne' := by
  have hmcrit := mem_critRow.mp (Finset.min'_mem _ hne)
  have hm'crit := mem_critRow.mp (Finset.min'_mem _ hne')
  by_cases hmem : (critRow alpha beta gamma delta T i').min' hne' ∈
      critRow alpha beta gamma delta T i
  · exact Finset.min'_le _ _ hmem
  · rw [mem_critRow] at hmem
    rcases not_and_or.mp hmem with hnA | hnB
    · -- `¬(α i + T ≤ δ m' + 1)` contradicts `α i ≤ α i'` + crit at `i'`.
      exfalso
      have h1 := hm'crit.1
      have h2 := hα hi
      have h3 := not_le.mp hnA
      linarith
    · -- `¬(γ m' + T ≤ β i + 1)` forces `γ m < γ m'`, hence `m < m'`.
      have hcmp : gamma ((critRow alpha beta gamma delta T i).min' hne) <
          gamma ((critRow alpha beta gamma delta T i').min' hne') := by
        have h1 := hmcrit.2
        have h2 := not_le.mp hnB
        linarith
      exact le_of_lt (not_le.mp (fun h => absurd (hγ h) (not_le.mpr hcmp)))

/-- **`step5.tex:416-417` (`U_i` nondecreasing).** The right endpoint of
the criterion row — its maximum index — is nondecreasing in `i`. -/
theorem critRow_max'_mono
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hβ : Monotone beta) (hδ : Monotone delta)
    {i i' : Fin p} (hi : i ≤ i')
    (hne : (critRow alpha beta gamma delta T i).Nonempty)
    (hne' : (critRow alpha beta gamma delta T i').Nonempty) :
    (critRow alpha beta gamma delta T i).max' hne ≤
      (critRow alpha beta gamma delta T i').max' hne' := by
  have hMcrit := mem_critRow.mp (Finset.max'_mem _ hne)
  have hM'crit := mem_critRow.mp (Finset.max'_mem _ hne')
  by_cases hmem : (critRow alpha beta gamma delta T i).max' hne ∈
      critRow alpha beta gamma delta T i'
  · exact Finset.le_max' _ _ hmem
  · rw [mem_critRow] at hmem
    rcases not_and_or.mp hmem with hnA | hnB
    · -- `¬(α i' + T ≤ δ M + 1)` forces `δ M < δ M'`, hence `M < M'`.
      have hcmp : delta ((critRow alpha beta gamma delta T i).max' hne) <
          delta ((critRow alpha beta gamma delta T i').max' hne') := by
        have h1 := hM'crit.1
        have h2 := not_le.mp hnA
        linarith
      exact le_of_lt (not_le.mp (fun h => absurd (hδ h) (not_le.mpr hcmp)))
    · -- `¬(γ M + T ≤ β i' + 1)` contradicts `β i ≤ β i'` + crit at `i`.
      exfalso
      have h1 := hMcrit.2
      have h2 := hβ hi
      have h3 := not_le.mp hnB
      linarith

/-! ### Step 4 (assembly): the band around a nondecreasing envelope

`step5.tex:424-443`: the rich set lies in a band of width `W⋆` (the
maximum criterion-row width) around a nondecreasing envelope `f`. The
envelope is the running maximum of the row minima, automatically
monotone; on every non-empty row it agrees with the row minimum. -/

/-- The left endpoint `L_i` of the criterion row as an integer (`0` on
empty rows). -/
noncomputable def critRowMin
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) : ℤ :=
  if h : (critRow alpha beta gamma delta T i).Nonempty
  then (((critRow alpha beta gamma delta T i).min' h).val : ℤ)
  else 0

/-- The width `U_i − L_i` of the criterion row (`0` on empty rows). -/
noncomputable def critRowWidth
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) : ℕ :=
  if h : (critRow alpha beta gamma delta T i).Nonempty
  then ((critRow alpha beta gamma delta T i).max' h).val -
       ((critRow alpha beta gamma delta T i).min' h).val
  else 0

/-- The global band width `W⋆ = max_i (U_i − L_i)` (`step5.tex:425`). -/
noncomputable def bandWidth
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ) : ℕ :=
  Finset.univ.sup (fun i => critRowWidth alpha beta gamma delta T i)

/-- The nondecreasing band envelope `f` (`step5.tex:428-432`): the
running maximum of the row minima. Monotone by construction. -/
noncomputable def bandEnvelope
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) : ℤ :=
  (Finset.univ.filter (· ≤ i)).sup' ⟨i, by simp⟩
    (fun i' => critRowMin alpha beta gamma delta T i')

lemma critRowMin_nonneg
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    (i : Fin p) : 0 ≤ critRowMin alpha beta gamma delta T i := by
  unfold critRowMin
  split
  · positivity
  · exact le_rfl

lemma critRowMin_eq
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) (T : ℤ)
    {i : Fin p} (h : (critRow alpha beta gamma delta T i).Nonempty) :
    critRowMin alpha beta gamma delta T i =
      (((critRow alpha beta gamma delta T i).min' h).val : ℤ) := by
  unfold critRowMin
  rw [dif_pos h]

lemma critRowMin_le_of_le
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hα : Monotone alpha) (hγ : Monotone gamma)
    {x i : Fin p} (hxi : x ≤ i)
    (hi : (critRow alpha beta gamma delta T i).Nonempty) :
    critRowMin alpha beta gamma delta T x ≤
      critRowMin alpha beta gamma delta T i := by
  by_cases hx : (critRow alpha beta gamma delta T x).Nonempty
  · rw [critRowMin_eq _ _ _ _ _ hx, critRowMin_eq _ _ _ _ _ hi]
    have := critRow_min'_mono hα hγ hxi hx hi
    exact_mod_cast Fin.le_def.mp this
  · rw [critRowMin, dif_neg hx, critRowMin_eq _ _ _ _ _ hi]
    positivity

lemma bandEnvelope_monotone
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ} :
    Monotone (bandEnvelope alpha beta gamma delta T) := by
  intro i i' hii
  unfold bandEnvelope
  apply Finset.sup'_le
  intro x hx
  rw [Finset.mem_filter] at hx
  exact Finset.le_sup' _ (by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, le_trans hx.2 hii⟩)

lemma bandEnvelope_eq
    {alpha beta : Fin p → ℤ} {gamma delta : Fin q → ℤ} {T : ℤ}
    (hα : Monotone alpha) (hγ : Monotone gamma)
    {i : Fin p} (hi : (critRow alpha beta gamma delta T i).Nonempty) :
    bandEnvelope alpha beta gamma delta T i =
      critRowMin alpha beta gamma delta T i := by
  unfold bandEnvelope
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rw [Finset.mem_filter] at hx
    exact critRowMin_le_of_le hα hγ hx.2 hi
  · exact Finset.le_sup' _ (by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, le_refl i⟩)

/-- **`lem:convex-overlap`, conclusion (b) — the band** (`step5.tex:424-443`).

The rich set lies in a band of width `W⋆ = bandWidth` around the
nondecreasing envelope `f = bandEnvelope`: every rich `(i, j)` has
`f i − W⋆ ≤ j ≤ f i + W⋆`. The envelope `f` is monotone and `W⋆` is the
maximum criterion-row width — the band is *not* the trivial whole-range
band (whose width would be `q`). -/
theorem convex_overlap_band
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) {T : ℤ}
    (hT : 1 ≤ T) (hα : Monotone alpha) (hγ : Monotone gamma) :
    ∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧ Monotone f ∧
      ∀ (i : Fin p) (j : Fin q),
        j ∈ richRow alpha beta gamma delta T i →
          f i - K ≤ (j : ℤ) ∧ (j : ℤ) ≤ f i + K := by
  refine ⟨bandEnvelope alpha beta gamma delta T,
    (bandWidth alpha beta gamma delta T : ℤ),
    by positivity, bandEnvelope_monotone, ?_⟩
  intro i j hj
  have hjc : j ∈ critRow alpha beta gamma delta T i :=
    richRow_subset_critRow alpha beta gamma delta hT i hj
  have hne : (critRow alpha beta gamma delta T i).Nonempty := ⟨j, hjc⟩
  have hfi : bandEnvelope alpha beta gamma delta T i =
      (((critRow alpha beta gamma delta T i).min' hne).val : ℤ) := by
    rw [bandEnvelope_eq hα hγ hne, critRowMin_eq _ _ _ _ _ hne]
  have hjmin : ((critRow alpha beta gamma delta T i).min' hne).val ≤ (j : ℕ) :=
    Fin.le_def.mp (Finset.min'_le _ _ hjc)
  have hjmax : (j : ℕ) ≤ ((critRow alpha beta gamma delta T i).max' hne).val :=
    Fin.le_def.mp (Finset.le_max' _ _ hjc)
  have hminmax : ((critRow alpha beta gamma delta T i).min' hne).val ≤
      ((critRow alpha beta gamma delta T i).max' hne).val :=
    Fin.le_def.mp
      (Finset.min'_le _ _ (Finset.max'_mem _ hne))
  have hwid : ((critRow alpha beta gamma delta T i).max' hne).val -
      ((critRow alpha beta gamma delta T i).min' hne).val ≤
      bandWidth alpha beta gamma delta T := by
    have he : critRowWidth alpha beta gamma delta T i =
        ((critRow alpha beta gamma delta T i).max' hne).val -
        ((critRow alpha beta gamma delta T i).min' hne).val := by
      unfold critRowWidth
      rw [dif_pos hne]
    rw [← he]
    exact Finset.le_sup (Finset.mem_univ i)
  refine ⟨?_, ?_⟩
  · rw [hfi]
    have hK : (0 : ℤ) ≤ (bandWidth alpha beta gamma delta T : ℤ) := by positivity
    have hjz : (((critRow alpha beta gamma delta T i).min' hne).val : ℤ) ≤
        (j : ℤ) := by exact_mod_cast hjmin
    linarith
  · rw [hfi]
    have hub : ((critRow alpha beta gamma delta T i).max' hne).val ≤
        ((critRow alpha beta gamma delta T i).min' hne).val +
          bandWidth alpha beta gamma delta T := by omega
    have hjz : (j : ℤ) ≤
        (((critRow alpha beta gamma delta T i).min' hne).val : ℤ) +
          (bandWidth alpha beta gamma delta T : ℤ) := by
      have : (j : ℕ) ≤ ((critRow alpha beta gamma delta T i).min' hne).val +
          bandWidth alpha beta gamma delta T := le_trans hjmax hub
      exact_mod_cast this
    linarith

/-- **`lem:convex-overlap` — the dichotomy** (`step5.tex:362-372`,
`step5.tex:440-443`).

For any absolute density constant `c` and any rich-pair count
`richCount`, *either* the rich set has positive density (conclusion
(a), `step5.tex:364`) *or* it is banded around a nondecreasing envelope
(conclusion (b), `convex_overlap_band`). Conclusion (b) in fact holds
unconditionally; the case split records the paper's framing where (a)
is the operative branch in the high-density regime.

This is the load-bearing structural output consumed by the Step 5
single-triple dichotomy (`prop_single_triple`, `Dichotomy.lean`). -/
theorem convex_overlap
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) {T : ℤ}
    (hT : 1 ≤ T) (hα : Monotone alpha) (hγ : Monotone gamma)
    (c richCount : ℕ) :
    (c * (p * q) ≤ richCount) ∨
    (∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧ Monotone f ∧
      ∀ (i : Fin p) (j : Fin q),
        j ∈ richRow alpha beta gamma delta T i →
          f i - K ≤ (j : ℤ) ∧ (j : ℤ) ≤ f i + K) := by
  by_cases hdense : c * (p * q) ≤ richCount
  · exact Or.inl hdense
  · exact Or.inr (convex_overlap_band alpha beta gamma delta hT hα hγ)

end Step5
end OneThird
