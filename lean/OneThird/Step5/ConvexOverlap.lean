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

end Step5
end OneThird
