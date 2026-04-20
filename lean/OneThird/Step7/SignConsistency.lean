/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step3.LocalSign
import OneThird.Step6.Assembly
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 7 — Sign consistency (`lem:sign-consistency`)

This file formalises `lem:sign-consistency` of `step7.tex`
(`step7.tex:243-369`), the global upgrade of Step 6's pointwise
coherence (Corollary B, `cor:pointwise`) to a refined sign
assignment on a mass-dominant subset of `Rich⋆` with per-active-pair
overlap compatibility.

## Paper statement

Assume the coherence case of Step 6.  There is a set
`E⋆ ⊆ Rich⋆` of rich interfaces carrying `(1 - o(1))` of the
rich-interface incidence mass, and a choice of refined signs
`σ̃_α ∈ {±1}` for `α ∈ E⋆`, such that:

1. `σ̃_α = σ_α` for all but an `o(1)`-fraction of overlap incidence;
2. for every active pair `(α, β) ∈ E⋆ × E⋆`, `σ̃_α = σ̃_β` on the
   common overlap.

## Proof outline (`step7.tex:260-357`)

Let `s : LinExt → Sign` be the Step 6 pointwise reference sign
(output of `cor:pointwise`), `Ω ⊆ LinExt` the pointwise-coherent
set, and for each `α ∈ Rich⋆`:

* `μ_α := |Fgood α|` (good-fiber mass);
* `m_α := |{L ∈ Fgood α ∩ Ω : σ_α = s(L)}|` (aligned mass);
* `η_α := |Fgood α ∖ Ω|` (out-of-Ω mass);
* `ε_α := +1` if `2·m_α ≥ μ_α`, else `-1`;
* `σ̃_α := ε_α · σ_α` (refined sign).

Double counting `cor:pointwise` gives the mismatch bound

  `η_d · ∑_α (μ_α - m_α - η_α) ≤ η_n · M₀`    (eq:db-count)

with `η_n / η_d = √δ` and `M₀ = ∑_α μ_α`.  Combined with
`η_d · ∑_α η_α ≤ η_n · M₀` (Step 6 pointwise control of
`Ω`-complement mass), this gives the *total mismatch bound*
`η_d · ∑_α (μ_α - m_α) ≤ 2·η_n · M₀`.

On `{α : ε_α = -1}`, `μ_α - m_α ≥ μ_α / 2`, yielding the
**flipped-weight bound** of condition (1):

  `η_d · ∑_{ε_α=-1} μ_α ≤ 4·η_n · M₀`.

Markov on the total mismatch defines the *refined set* `E⋆` of
strongly dominant interfaces; the complement `Rich⋆ \ E⋆` has
mass `≤ δ^{1/4} · M₀ = o(M₀)`, giving condition on `|E⋆|`.

Finally, for active pairs `(e, f) ∈ E⋆ × E⋆` with overlap weight
`w_{ef} ≥ δ^{1/4} · min(μ_e, μ_f)` (active threshold), a union
bound on the `E⋆`-disagreement sets yields the **overlap
compatibility** of condition (2).

## Lean formalisation

We formalise the content in cleared-denominator abstract form,
parametric in the combinatorial inputs:

* `mu α` := `(Fgood α).card`;
* `alignedSet α` := `L ∈ Fgood α ∩ Ω` with `σ α = s L`;
* `alignedCount α` := `|alignedSet α|`;
* `outsideCount α` := `|Fgood α ∖ Ω|`;
* `flippedSet` := `{α : 2 · alignedCount α < mu α}`
  (the paper's `{α : ε_α = -1}`);
* `refinedSign` — the paper's `σ̃_α`.

Key theorems:

* `total_mismatch_bound` — `η_d · ∑ (μ - m - η) + η_d · ∑ η
  ≤ η_n · M₀ + η_d · ∑ η` (restated as `η_d · ∑ (μ - m) ≤ …`).
* `flipped_weight_bound` — cleared-denominator form of condition (1).
* `refinedSign_disagree_eq_flip` — on `Fgood α`, `refinedSign α`
  disagrees with `s L` iff `σ α` is flipped by `ε_α`.
* `overlap_agree_of_active_pair` — cleared-denominator form of
  condition (2): on an active pair `(e, f) ∈ E⋆ × E⋆`, the
  disagreement mass on the overlap is bounded by the sum of the
  individual `E⋆`-slack.

Downstream, `lem:cocycle` (`step7.tex:391`, S7.b) consumes
`refinedSign` as its per-interface orientation data.
-/

namespace OneThird
namespace Step7

open Finset OneThird.Step3
open scoped BigOperators

/-! ### §1 — Combinatorial set-up -/

section Counts

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Good-fiber mass** `μ_α := |Fgood α|`
(`step7.tex:273`, `μ_α := μ(fib_α ∖ B_α)`). -/
def mu (Fgood : Pair → Finset LinExt) (α : Pair) : ℕ :=
  (Fgood α).card

/-- **Aligned subset** at `α`
(`step7.tex:275-278`, `{L ∈ fib_α ∩ Ω : σ_α = s(L)}`). -/
def alignedSet (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    Finset LinExt :=
  (Fgood α ∩ Ω).filter (fun L => σ α = s L)

/-- **Aligned count** `m_α := |{L ∈ Fgood α ∩ Ω : σ_α = s(L)}|`
(`step7.tex:276`). -/
def alignedCount (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) : ℕ :=
  (alignedSet Fgood Ω σ s α).card

/-- **Mismatched subset** on `Fgood α ∩ Ω`: the complement of
`alignedSet` inside `Fgood α ∩ Ω`, i.e. `{L ∈ Fgood α ∩ Ω :
σ_α ≠ s(L)}`. -/
def mismatchSet (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    Finset LinExt :=
  (Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)

/-- **Mismatch count** on `Fgood α ∩ Ω`
(`step7.tex:287-293`, the integrand of `eq:db-count`). -/
def mismatchCount (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) : ℕ :=
  (mismatchSet Fgood Ω σ s α).card

/-- **Outside-Ω subset** at `α`: `Fgood α ∖ Ω`
(`step7.tex:301`, the `η_α` region). -/
def outsideSet (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (α : Pair) : Finset LinExt :=
  Fgood α \ Ω

/-- **Outside-Ω count** `η_α := |Fgood α ∖ Ω|`
(`step7.tex:301`). -/
def outsideCount (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (α : Pair) : ℕ :=
  (outsideSet Fgood Ω α).card

/-- `Fgood α` decomposes as the disjoint union of the aligned,
mismatched, and outside-Ω parts. -/
theorem Fgood_decomposition
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    alignedCount Fgood Ω σ s α + mismatchCount Fgood Ω σ s α +
        outsideCount Fgood Ω α
      = mu Fgood α := by
  classical
  unfold alignedCount mismatchCount outsideCount mu
  unfold alignedSet mismatchSet outsideSet
  -- Decompose `Fgood α` as `(Fgood α ∩ Ω) ∪ (Fgood α \ Ω)`,
  -- and `(Fgood α ∩ Ω)` as its `σ = s` and `σ ≠ s` partitions.
  have hdisj1 :
      Disjoint
        ((Fgood α ∩ Ω).filter (fun L => σ α = s L))
        ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)) := by
    rw [Finset.disjoint_filter]
    intros _ _ h1 h2
    exact h2 h1
  have hunion1 :
      (Fgood α ∩ Ω).filter (fun L => σ α = s L) ∪
          (Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)
        = Fgood α ∩ Ω := by
    ext L
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hσ : σ α = s L
      · exact Or.inl ⟨h, hσ⟩
      · exact Or.inr ⟨h, hσ⟩
  have hcard1 :
      (alignedSet Fgood Ω σ s α).card +
          (mismatchSet Fgood Ω σ s α).card = (Fgood α ∩ Ω).card := by
    unfold alignedSet mismatchSet
    rw [← Finset.card_union_of_disjoint hdisj1, hunion1]
  have hdisj2 : Disjoint (Fgood α ∩ Ω) (Fgood α \ Ω) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext L
    simp [Finset.mem_inter, Finset.mem_sdiff]
  have hunion2 : (Fgood α ∩ Ω) ∪ (Fgood α \ Ω) = Fgood α := by
    ext L
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hΩ : L ∈ Ω
      · exact Or.inl ⟨h, hΩ⟩
      · exact Or.inr ⟨h, hΩ⟩
  have hcard2 :
      (Fgood α ∩ Ω).card + (Fgood α \ Ω).card = (Fgood α).card := by
    rw [← Finset.card_union_of_disjoint hdisj2, hunion2]
  -- Combine.
  have : (alignedSet Fgood Ω σ s α).card +
            (mismatchSet Fgood Ω σ s α).card +
            (Fgood α \ Ω).card
         = (Fgood α).card := by
    rw [hcard1]; exact hcard2
  -- Unfold the outsideSet cardinality.
  change (alignedSet Fgood Ω σ s α).card +
      (mismatchSet Fgood Ω σ s α).card +
      (Fgood α \ Ω).card = (Fgood α).card
  exact this

/-- `mu α = alignedCount + mismatchCount + outsideCount`, stated as
a subtraction identity `mu α - alignedCount - outsideCount =
mismatchCount` (for later use in the double-counting bound). -/
theorem mu_sub_aligned_sub_outside_eq_mismatch
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    mu Fgood α - alignedCount Fgood Ω σ s α -
        outsideCount Fgood Ω α
      = mismatchCount Fgood Ω σ s α := by
  have := Fgood_decomposition Fgood Ω σ s α
  omega

end Counts

/-! ### §2 — Double counting and total mismatch bound -/

section DoubleCount

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Double-counting identity** (`step7.tex:289-293`, `eq:db-count`).

The sum over `α ∈ richStar` of mismatched mass on `Fgood α ∩ Ω`
equals the "off-reference" integral
`∑_{α : L ∈ Fgood α, L ∈ Ω, σ_α ≠ s(L)} 1`, i.e. the total incidence
of `σ_α ≠ s(L)` across `richStar × Ω`. -/
theorem mismatch_sum_eq_incidence
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign) :
    ∑ α ∈ richStar, mismatchCount Fgood Ω σ s α =
      ∑ L ∈ Ω, (richStar.filter
          (fun α => L ∈ Fgood α ∧ σ α ≠ s L)).card := by
  classical
  unfold mismatchCount mismatchSet
  -- Reindex via the double-sum / double-counting lemma.
  have :
      ∀ α ∈ richStar,
        ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)).card =
          ∑ L ∈ Ω, if L ∈ Fgood α ∧ σ α ≠ s L then 1 else 0 := by
    intro α _
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    apply Finset.sum_bij (fun L _ => L)
    · intro L hL
      rw [Finset.mem_filter] at hL ⊢
      obtain ⟨hL1, hne⟩ := hL
      rw [Finset.mem_inter] at hL1
      exact ⟨hL1.2, hL1.1, hne⟩
    · intros; assumption
    · intro L hL
      rw [Finset.mem_filter] at hL
      refine ⟨L, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_inter]
      exact ⟨⟨hL.2.1, hL.1⟩, hL.2.2⟩
    · intros; rfl
  rw [Finset.sum_congr rfl this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L _
  rw [← Finset.sum_filter]
  rw [Finset.card_eq_sum_ones]

/-- **Double-counting bound** (`step7.tex:289-296`, cleared-denominator).

The cleared-denominator input from Step 6 `cor:pointwise`: the total
mismatch mass is bounded by `(η_n / η_d) · M₀`, i.e.

  `η_d · ∑ α, mismatchCount α ≤ η_n · M₀`.

This is the paper's
`∫_Ω #{α ∈ Rich_L : σ_α ≠ s(L)} ≤ √δ · M₀`
(`step7.tex:293-295`), via `mismatch_sum_eq_incidence`. -/
def DoubleCountHyp
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (η_n η_d M₀ : ℕ) : Prop :=
  η_d * ∑ α ∈ richStar, mismatchCount Fgood Ω σ s α ≤ η_n * M₀

/-- **Outside-Ω mass bound** (`step7.tex:303-306`).

The outside-Ω incidence mass is also bounded by `(η_n / η_d) · M₀`
(directly from `μ(LE(P) ∖ Ω) ≤ √δ · M₀` in Step 6's output, summed
against `|Rich_L|`). -/
def OutsideMassHyp
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (η_n η_d M₀ : ℕ) : Prop :=
  η_d * ∑ α ∈ richStar, outsideCount Fgood Ω α ≤ η_n * M₀

/-- **Total mismatch bound** (`step7.tex:307-314`,
`μ_α - m_α = mismatch_α + η_α` already; summing).

Under the double-counting hypothesis and the outside-Ω mass bound,
the total off-aligned mass satisfies

  `η_d · ∑ α, (μ_α - m_α) ≤ 2·η_n · M₀`.

This is the cleared-denominator form of the paper's eq. (30)
combined with the `∑ η_α`-absorption sentence at line 313. -/
theorem total_mismatch_bound
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (η_n η_d M₀ : ℕ)
    (hDC : DoubleCountHyp richStar Fgood Ω σ s η_n η_d M₀)
    (hOut : OutsideMassHyp richStar Fgood Ω η_n η_d M₀) :
    η_d * ∑ α ∈ richStar,
        (mu Fgood α - alignedCount Fgood Ω σ s α) ≤
      2 * η_n * M₀ := by
  classical
  -- `DoubleCountHyp` and `OutsideMassHyp` are reducible definitions; use directly.
  change η_d * ∑ α ∈ richStar, mismatchCount Fgood Ω σ s α ≤ η_n * M₀ at hDC
  change η_d * ∑ α ∈ richStar, outsideCount Fgood Ω α ≤ η_n * M₀ at hOut
  -- Pointwise: μ α - aligned α = mismatch α + outside α (by Fgood_decomposition).
  have hpt : ∀ α ∈ richStar,
      mu Fgood α - alignedCount Fgood Ω σ s α =
        mismatchCount Fgood Ω σ s α + outsideCount Fgood Ω α := by
    intro α _
    have := Fgood_decomposition Fgood Ω σ s α
    omega
  have hsum :
      ∑ α ∈ richStar,
          (mu Fgood α - alignedCount Fgood Ω σ s α) =
        ∑ α ∈ richStar, mismatchCount Fgood Ω σ s α +
          ∑ α ∈ richStar, outsideCount Fgood Ω α := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpt
  rw [hsum]
  have h1 :
      η_d * (∑ α ∈ richStar, mismatchCount Fgood Ω σ s α +
          ∑ α ∈ richStar, outsideCount Fgood Ω α) =
        η_d * ∑ α ∈ richStar, mismatchCount Fgood Ω σ s α +
        η_d * ∑ α ∈ richStar, outsideCount Fgood Ω α := by
    rw [Nat.mul_add]
  rw [h1]
  have : η_d * ∑ α ∈ richStar, mismatchCount Fgood Ω σ s α +
         η_d * ∑ α ∈ richStar, outsideCount Fgood Ω α ≤
         η_n * M₀ + η_n * M₀ := Nat.add_le_add hDC hOut
  linarith

end DoubleCount

/-! ### §3 — Refined sign and flipped-weight bound -/

section RefinedSign

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Flip indicator** `ε_α ∈ {±1}` (`step7.tex:279-280`).

`ε_α = +1` (encoded as `true`) if the aligned mass `m_α` is at
least half the good-fiber mass `μ_α`; otherwise `ε_α = -1`
(encoded as `false`). -/
def flipIndicator (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) : Bool :=
  decide (mu Fgood α ≤ 2 * alignedCount Fgood Ω σ s α)

/-- **Refined sign** `σ̃_α := ε_α · σ_α` (`step7.tex:281`).

If `ε_α = +1`, `σ̃_α = σ_α`.  If `ε_α = -1`, `σ̃_α` is the
negation of `σ_α`. -/
def refinedSign (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) : Sign :=
  if flipIndicator Fgood Ω σ s α then σ α else Sign.neg (σ α)

/-- **Flipped set** `{α : ε_α = -1}` (`step7.tex:307-311`). -/
def flippedSet (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign) :
    Finset Pair :=
  richStar.filter
    (fun α => 2 * alignedCount Fgood Ω σ s α < mu Fgood α)

lemma mem_flippedSet {richStar : Finset Pair}
    {Fgood : Pair → Finset LinExt} {Ω : Finset LinExt}
    {σ : Pair → Sign} {s : LinExt → Sign} {α : Pair} :
    α ∈ flippedSet richStar Fgood Ω σ s ↔
      α ∈ richStar ∧
        2 * alignedCount Fgood Ω σ s α < mu Fgood α := by
  unfold flippedSet
  rw [Finset.mem_filter]

lemma flippedSet_subset
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign) :
    flippedSet richStar Fgood Ω σ s ⊆ richStar :=
  Finset.filter_subset _ _

/-- On flipped interfaces, `μ_α - m_α ≥ μ_α / 2`, equivalently
`μ_α ≤ 2 · (μ_α - m_α)` (the key inequality for the flipped-weight
bound, `step7.tex:307-309`). -/
lemma mu_le_two_mul_sub_aligned_of_flipped
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    {α : Pair} (hα : α ∈ flippedSet richStar Fgood Ω σ s) :
    mu Fgood α ≤
      2 * (mu Fgood α - alignedCount Fgood Ω σ s α) := by
  rw [mem_flippedSet] at hα
  obtain ⟨_, hlt⟩ := hα
  -- Aligned count ≤ μ, so μ - aligned is well-defined subtraction.
  have halign_le :
      alignedCount Fgood Ω σ s α ≤ mu Fgood α := by
    have := Fgood_decomposition Fgood Ω σ s α
    omega
  omega

/-- **Flipped-weight bound (Lemma A, condition 1)** — cleared
denominator (`step7.tex:307-314`).

Under the double-counting and outside-Ω hypotheses,

  `η_d · ∑_{α ∈ flippedSet} μ_α ≤ 4·η_n · M₀`.

This is the paper's "flipped weight ≤ 4√δ · M₀" (`step7.tex:314`)
in cleared-denominator form. -/
theorem flipped_weight_bound
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (η_n η_d M₀ : ℕ)
    (hDC : DoubleCountHyp richStar Fgood Ω σ s η_n η_d M₀)
    (hOut : OutsideMassHyp richStar Fgood Ω η_n η_d M₀) :
    η_d * ∑ α ∈ flippedSet richStar Fgood Ω σ s, mu Fgood α ≤
      4 * η_n * M₀ := by
  classical
  -- Pointwise: for α flipped, μ α ≤ 2 · (μ α - aligned α).
  have hpt : ∀ α ∈ flippedSet richStar Fgood Ω σ s,
      mu Fgood α ≤
        2 * (mu Fgood α - alignedCount Fgood Ω σ s α) := by
    intro α hα
    exact mu_le_two_mul_sub_aligned_of_flipped
      richStar Fgood Ω σ s hα
  have hsum :
      ∑ α ∈ flippedSet richStar Fgood Ω σ s, mu Fgood α ≤
        2 * ∑ α ∈ flippedSet richStar Fgood Ω σ s,
          (mu Fgood α - alignedCount Fgood Ω σ s α) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hrestrict :
      ∑ α ∈ flippedSet richStar Fgood Ω σ s,
          (mu Fgood α - alignedCount Fgood Ω σ s α) ≤
        ∑ α ∈ richStar,
          (mu Fgood α - alignedCount Fgood Ω σ s α) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (flippedSet_subset richStar Fgood Ω σ s)
    intros; exact Nat.zero_le _
  have hTotal : η_d *
      ∑ α ∈ richStar,
          (mu Fgood α - alignedCount Fgood Ω σ s α) ≤
      2 * η_n * M₀ :=
    total_mismatch_bound richStar Fgood Ω σ s η_n η_d M₀ hDC hOut
  calc η_d * ∑ α ∈ flippedSet richStar Fgood Ω σ s, mu Fgood α
      ≤ η_d * (2 * ∑ α ∈ flippedSet richStar Fgood Ω σ s,
            (mu Fgood α - alignedCount Fgood Ω σ s α)) :=
        Nat.mul_le_mul_left _ hsum
    _ = 2 * (η_d * ∑ α ∈ flippedSet richStar Fgood Ω σ s,
            (mu Fgood α - alignedCount Fgood Ω σ s α)) := by ring
    _ ≤ 2 * (η_d * ∑ α ∈ richStar,
            (mu Fgood α - alignedCount Fgood Ω σ s α)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrestrict)
    _ ≤ 2 * (2 * η_n * M₀) := Nat.mul_le_mul_left _ hTotal
    _ = 4 * η_n * M₀ := by ring

end RefinedSign

/-! ### §4 — Refined set `E⋆` and its mass bound -/

section RefinedSet

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Dominant mass at `α`** (`step7.tex:319-322`).

The larger of the aligned and anti-aligned masses at `α`, i.e.
`max(m_α, μ_α - m_α - η_α)` using `Fgood α ∩ Ω` rather than
`Fgood α`.  We use the cleaner `max(m_α, μ_α - m_α)` which differs
by at most `η_α` and gives the paper's `E⋆` up to `O(η_α)`
absorption (a paper inequality, cf. `step7.tex:345-346`). -/
def dominantCount (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) : ℕ :=
  max (alignedCount Fgood Ω σ s α)
      (mu Fgood α - alignedCount Fgood Ω σ s α)

/-- **Refined set** `E⋆ = {α ∈ Rich⋆ : dominance ≥ (1 - δ₁) · μ_α}`
(`step7.tex:319-322`), cleared-denominator:

  `δ₁_d · dominantCount α ≥ (δ₁_d - δ₁_n) · μ_α`.

Here `δ₁ = δ₁_n / δ₁_d` plays the role of the paper's `δ^{1/4}`. -/
def refinedSet
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (δ₁_n δ₁_d : ℕ) : Finset Pair :=
  richStar.filter
    (fun α =>
      (δ₁_d - δ₁_n) * mu Fgood α ≤
        δ₁_d * dominantCount Fgood Ω σ s α)

lemma mem_refinedSet
    {richStar : Finset Pair} {Fgood : Pair → Finset LinExt}
    {Ω : Finset LinExt} {σ : Pair → Sign} {s : LinExt → Sign}
    {δ₁_n δ₁_d : ℕ} {α : Pair} :
    α ∈ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d ↔
      α ∈ richStar ∧
        (δ₁_d - δ₁_n) * mu Fgood α ≤
          δ₁_d * dominantCount Fgood Ω σ s α := by
  unfold refinedSet
  rw [Finset.mem_filter]

lemma refinedSet_subset
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (δ₁_n δ₁_d : ℕ) :
    refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d ⊆ richStar :=
  Finset.filter_subset _ _

/-- On the complement of `E⋆` (non-dominant interfaces), the
anti-dominance condition gives a lower bound on the mismatch mass
`μ_α - dominance ≥ δ₁ · μ_α` (cleared-denominator):

  `δ₁_n · μ_α ≤ δ₁_d · (μ_α - dominantCount α)`. -/
lemma mu_sub_dominant_lower_of_not_refined
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (δ₁_n δ₁_d : ℕ)
    {α : Pair}
    (hα : α ∈ richStar)
    (hnotE : α ∉ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d)
    (hδ : δ₁_n ≤ δ₁_d) :
    δ₁_n * mu Fgood α ≤
      δ₁_d * (mu Fgood α - dominantCount Fgood Ω σ s α) := by
  -- `mem_refinedSet` fails => (δ₁_d - δ₁_n)·μ > δ₁_d · dominance.
  rw [mem_refinedSet] at hnotE
  push_neg at hnotE
  have hgt := hnotE hα
  -- dominance ≤ μ, so the subtraction is ordinary Nat subtraction.
  have hdomle : dominantCount Fgood Ω σ s α ≤ mu Fgood α := by
    unfold dominantCount
    have halign_le :
        alignedCount Fgood Ω σ s α ≤ mu Fgood α := by
      have := Fgood_decomposition Fgood Ω σ s α
      omega
    omega
  -- (δ₁_d - δ₁_n)·μ > δ₁_d · dominance
  --   ⇔ δ₁_d·μ - δ₁_n·μ > δ₁_d · dominance
  --   ⇔ δ₁_n · μ < δ₁_d · (μ - dominance).
  have hsub : (δ₁_d - δ₁_n) * mu Fgood α
                = δ₁_d * mu Fgood α - δ₁_n * mu Fgood α := by
    rw [Nat.sub_mul]
  have hgt' :
      δ₁_d * dominantCount Fgood Ω σ s α <
        δ₁_d * mu Fgood α - δ₁_n * mu Fgood α := by
    rw [hsub] at hgt; exact hgt
  have hlin :
      δ₁_n * mu Fgood α + δ₁_d * dominantCount Fgood Ω σ s α <
        δ₁_d * mu Fgood α := by
    have h1 : δ₁_n * mu Fgood α ≤ δ₁_d * mu Fgood α :=
      Nat.mul_le_mul_right _ hδ
    omega
  have hmul :
      δ₁_d * (mu Fgood α - dominantCount Fgood Ω σ s α) =
        δ₁_d * mu Fgood α - δ₁_d * dominantCount Fgood Ω σ s α :=
    Nat.mul_sub _ _ _
  -- From hlin: δ₁_n · μ ≤ δ₁_d · μ - δ₁_d · dominance = δ₁_d · (μ - dominance).
  have : δ₁_n * mu Fgood α ≤
           δ₁_d * mu Fgood α - δ₁_d * dominantCount Fgood Ω σ s α := by
    have hle : δ₁_d * dominantCount Fgood Ω σ s α ≤
               δ₁_d * mu Fgood α := Nat.mul_le_mul_left _ hdomle
    omega
  rw [hmul]; exact this

/-- **Dominance is at least half of `μ`**
(`step7.tex:279-281`, `ε_α` covers the majority side). -/
lemma two_mul_dominant_ge_mu
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    mu Fgood α ≤ 2 * dominantCount Fgood Ω σ s α := by
  unfold dominantCount
  have halign_le :
      alignedCount Fgood Ω σ s α ≤ mu Fgood α := by
    have := Fgood_decomposition Fgood Ω σ s α
    omega
  by_cases h : mu Fgood α ≤ 2 * alignedCount Fgood Ω σ s α
  · -- aligned is dominant.
    have hmax :
        max (alignedCount Fgood Ω σ s α)
            (mu Fgood α - alignedCount Fgood Ω σ s α) ≥
          alignedCount Fgood Ω σ s α := le_max_left _ _
    omega
  · -- anti-aligned is dominant.
    have hmax :
        max (alignedCount Fgood Ω σ s α)
            (mu Fgood α - alignedCount Fgood Ω σ s α) ≥
          mu Fgood α - alignedCount Fgood Ω σ s α := le_max_right _ _
    omega

/-- `μ_α - dominantCount α ≤ μ_α - alignedCount α` — the
mismatch-from-dominance is bounded by the mismatch-from-aligned
(since dominance ≥ aligned). -/
lemma mu_sub_dominant_le_mu_sub_aligned
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    mu Fgood α - dominantCount Fgood Ω σ s α ≤
      mu Fgood α - alignedCount Fgood Ω σ s α := by
  have h : alignedCount Fgood Ω σ s α ≤
           dominantCount Fgood Ω σ s α := by
    unfold dominantCount; exact le_max_left _ _
  omega

/-- **Markov bound on `Rich⋆ \ E⋆`** — cleared denominator
(`step7.tex:322-325`).

Under the total-mismatch bound `η_d · ∑ (μ - aligned) ≤ 2η_n · M₀`
(from `total_mismatch_bound`) and `δ₁_n ≤ δ₁_d`, the mass of the
non-refined interfaces satisfies

  `δ₁_n · η_d · ∑_{α ∉ E⋆} μ_α ≤ 2 δ₁_d · η_n · M₀`.

The paper's form is `|Rich⋆ \ E⋆| · mass ≤ δ^{1/4} · M₀`; after
clearing denominators and using `δ^{1/4} · δ^{1/2} = δ^{3/4}`
the coefficient becomes `2`. -/
theorem notRefined_mass_bound
    (richStar : Finset Pair) (Fgood : Pair → Finset LinExt)
    (Ω : Finset LinExt) (σ : Pair → Sign) (s : LinExt → Sign)
    (η_n η_d δ₁_n δ₁_d M₀ : ℕ)
    (hDC : DoubleCountHyp richStar Fgood Ω σ s η_n η_d M₀)
    (hOut : OutsideMassHyp richStar Fgood Ω η_n η_d M₀)
    (hδ : δ₁_n ≤ δ₁_d) :
    δ₁_n * η_d * ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
        mu Fgood α ≤
      2 * δ₁_d * η_n * M₀ := by
  classical
  -- Pointwise: for α ∉ E⋆, δ₁_n · μ ≤ δ₁_d · (μ - dominance) ≤ δ₁_d · (μ - aligned).
  have hpt : ∀ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
      δ₁_n * mu Fgood α ≤
        δ₁_d * (mu Fgood α - alignedCount Fgood Ω σ s α) := by
    intro α hα
    rw [Finset.mem_sdiff] at hα
    obtain ⟨hRich, hnotE⟩ := hα
    have h1 : δ₁_n * mu Fgood α ≤
        δ₁_d * (mu Fgood α - dominantCount Fgood Ω σ s α) :=
      mu_sub_dominant_lower_of_not_refined
        richStar Fgood Ω σ s δ₁_n δ₁_d hRich hnotE hδ
    have h2 : δ₁_d * (mu Fgood α - dominantCount Fgood Ω σ s α) ≤
        δ₁_d * (mu Fgood α - alignedCount Fgood Ω σ s α) :=
      Nat.mul_le_mul_left _
        (mu_sub_dominant_le_mu_sub_aligned Fgood Ω σ s α)
    exact h1.trans h2
  -- Sum the pointwise bound.
  have hsum :
      δ₁_n * ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
            mu Fgood α ≤
        δ₁_d * ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
            (mu Fgood α - alignedCount Fgood Ω σ s α) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  -- Restrict: the sum over the complement is ≤ the sum over richStar.
  have hrestrict :
      ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
            (mu Fgood α - alignedCount Fgood Ω σ s α) ≤
        ∑ α ∈ richStar,
            (mu Fgood α - alignedCount Fgood Ω σ s α) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intros; exact Nat.zero_le _
  -- Total mismatch bound.
  have hTotal : η_d *
      ∑ α ∈ richStar,
          (mu Fgood α - alignedCount Fgood Ω σ s α) ≤
      2 * η_n * M₀ :=
    total_mismatch_bound richStar Fgood Ω σ s η_n η_d M₀ hDC hOut
  -- Chain.
  calc δ₁_n * η_d *
      ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
          mu Fgood α
      = η_d * (δ₁_n *
            ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
              mu Fgood α) := by ring
    _ ≤ η_d * (δ₁_d *
            ∑ α ∈ richStar \ refinedSet richStar Fgood Ω σ s δ₁_n δ₁_d,
              (mu Fgood α - alignedCount Fgood Ω σ s α)) :=
        Nat.mul_le_mul_left _ hsum
    _ ≤ η_d * (δ₁_d *
            ∑ α ∈ richStar,
              (mu Fgood α - alignedCount Fgood Ω σ s α)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrestrict)
    _ = δ₁_d * (η_d *
            ∑ α ∈ richStar,
              (mu Fgood α - alignedCount Fgood Ω σ s α)) := by ring
    _ ≤ δ₁_d * (2 * η_n * M₀) := Nat.mul_le_mul_left _ hTotal
    _ = 2 * δ₁_d * η_n * M₀ := by ring

end RefinedSet

/-! ### §5 — Overlap compatibility for active pairs in `E⋆ × E⋆` -/

section OverlapAgree

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Disagreement-with-`s` set for the refined sign**: at `α`, the
set `{L ∈ Fgood α : refinedSign α ≠ s(L)}`. -/
def refinedDisagreeSet
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    Finset LinExt :=
  (Fgood α).filter (fun L => refinedSign Fgood Ω σ s α ≠ s L)

/-- The disagreement set of the refined sign is contained in the
union of: the aligned-and-flipped set, the mismatched-and-unflipped
set, and the outside-Ω set — a crude bound that avoids the
refined-set machinery but is enough for union-bound overlap
compatibility. -/
lemma refinedDisagreeSet_card_le
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (α : Pair) :
    (refinedDisagreeSet Fgood Ω σ s α).card ≤
      (mu Fgood α - dominantCount Fgood Ω σ s α) +
        outsideCount Fgood Ω α := by
  classical
  unfold refinedDisagreeSet
  -- Decompose Fgood α into (aligned) ∪ (mismatched) ∪ (outside).
  have hdom :
      (Fgood α).filter (fun L =>
            refinedSign Fgood Ω σ s α ≠ s L) ⊆
        (Fgood α).filter (fun L => L ∉ Ω) ∪
          ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L) ∪
            (Fgood α ∩ Ω).filter (fun L => σ α = s L)) := by
    intro L hL
    rw [Finset.mem_filter] at hL
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter,
        Finset.mem_filter, Finset.mem_filter]
    by_cases hΩ : L ∈ Ω
    · right
      by_cases hσ : σ α = s L
      · right
        exact ⟨Finset.mem_inter.mpr ⟨hL.1, hΩ⟩, hσ⟩
      · left
        exact ⟨Finset.mem_inter.mpr ⟨hL.1, hΩ⟩, hσ⟩
    · left
      exact ⟨hL.1, hΩ⟩
  -- The actual claim uses dominantCount, which is ≥ aligned or ≥ (μ - aligned).
  -- We use the coarser bound: #disagree ≤ #mismatch + #outside + #(minority side).
  -- A slicker argument: the refined sign disagrees with s(L) on the
  -- minority side of α within Ω, plus the outside-Ω mass.
  -- We'll use a direct bound via alignedCount / (μ - aligned).
  by_cases hflip : flipIndicator Fgood Ω σ s α
  · -- ε_α = +1, so refinedSign α = σ α. Disagree ↔ σ α ≠ s L.
    -- On Ω: disagree is mismatchCount α.
    -- On (Fgood α \ Ω): disagree is ≤ outsideCount.
    -- In this branch, aligned ≥ μ / 2, so mu - aligned ≤ aligned, so
    -- dominantCount = aligned, and mu - dominantCount = mu - aligned = mismatch + outside.
    -- Strictly, we just need #disagree ≤ mismatch + outside ≤ (mu-dominant) + outside.
    have hrefined :
        ∀ L ∈ Fgood α,
          (refinedSign Fgood Ω σ s α ≠ s L) ↔ (σ α ≠ s L) := by
      intro L _
      unfold refinedSign; rw [if_pos hflip]
    have hsub :
        (Fgood α).filter (fun L => refinedSign Fgood Ω σ s α ≠ s L) =
          (Fgood α).filter (fun L => σ α ≠ s L) := by
      ext L
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hL, hne⟩
        exact ⟨hL, (hrefined L hL).mp hne⟩
      · rintro ⟨hL, hne⟩
        exact ⟨hL, (hrefined L hL).mpr hne⟩
    rw [hsub]
    -- Now bound (Fgood α).filter (σ α ≠ s L).card ≤ mismatchCount + outsideCount.
    have hle :
        (Fgood α).filter (fun L => σ α ≠ s L) ⊆
          ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)) ∪
            (Fgood α \ Ω) := by
      intro L hL
      rw [Finset.mem_filter] at hL
      rw [Finset.mem_union]
      by_cases hΩ : L ∈ Ω
      · left
        rw [Finset.mem_filter, Finset.mem_inter]
        exact ⟨⟨hL.1, hΩ⟩, hL.2⟩
      · right
        rw [Finset.mem_sdiff]; exact ⟨hL.1, hΩ⟩
    have hcardle :
        ((Fgood α).filter (fun L => σ α ≠ s L)).card ≤
          ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)).card +
            (Fgood α \ Ω).card := by
      calc ((Fgood α).filter (fun L => σ α ≠ s L)).card
          ≤ (((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)) ∪
              (Fgood α \ Ω)).card := Finset.card_le_card hle
        _ ≤ ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)).card +
              (Fgood α \ Ω).card := Finset.card_union_le _ _
    -- mismatchCount + outsideCount ≤ (μ - aligned) + outside = (μ - dominant) + outside
    -- since dominant = aligned in this branch.
    have halign_le :
        alignedCount Fgood Ω σ s α ≤ mu Fgood α := by
      have := Fgood_decomposition Fgood Ω σ s α
      omega
    have hflip' : mu Fgood α ≤ 2 * alignedCount Fgood Ω σ s α := by
      unfold flipIndicator at hflip
      exact of_decide_eq_true hflip
    have hdomEq : dominantCount Fgood Ω σ s α =
                    alignedCount Fgood Ω σ s α := by
      unfold dominantCount
      exact max_eq_left (by omega)
    have hmismatch :
        ((Fgood α ∩ Ω).filter (fun L => σ α ≠ s L)).card =
          mismatchCount Fgood Ω σ s α := by
      unfold mismatchCount mismatchSet; rfl
    have houtside : (Fgood α \ Ω).card = outsideCount Fgood Ω α := by
      unfold outsideCount outsideSet; rfl
    rw [hmismatch, houtside] at hcardle
    have hdecomp :
        mismatchCount Fgood Ω σ s α =
          mu Fgood α - alignedCount Fgood Ω σ s α -
            outsideCount Fgood Ω α := by
      have := Fgood_decomposition Fgood Ω σ s α
      omega
    have hdomsubeq :
        mu Fgood α - dominantCount Fgood Ω σ s α =
          mu Fgood α - alignedCount Fgood Ω σ s α := by
      rw [hdomEq]
    have houtcount_le :
        outsideCount Fgood Ω α ≤ mu Fgood α := by
      have := Fgood_decomposition Fgood Ω σ s α
      omega
    omega
  · -- ε_α = -1, so refinedSign α = neg (σ α). Disagree with s(L) ↔ σ α = s(L).
    have hrefined :
        ∀ L ∈ Fgood α,
          (refinedSign Fgood Ω σ s α ≠ s L) ↔ (σ α = s L) := by
      intro L _
      unfold refinedSign; rw [if_neg hflip]
      unfold Sign.neg
      constructor
      · intro h
        cases hsL : s L <;> cases hσ : σ α <;> simp_all
      · intro h
        cases hsL : s L <;> cases hσ : σ α <;> simp_all
    have hsub :
        (Fgood α).filter (fun L => refinedSign Fgood Ω σ s α ≠ s L) =
          (Fgood α).filter (fun L => σ α = s L) := by
      ext L
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hL, hne⟩
        exact ⟨hL, (hrefined L hL).mp hne⟩
      · rintro ⟨hL, heq⟩
        exact ⟨hL, (hrefined L hL).mpr heq⟩
    rw [hsub]
    have hle :
        (Fgood α).filter (fun L => σ α = s L) ⊆
          (alignedSet Fgood Ω σ s α) ∪ (Fgood α \ Ω) := by
      intro L hL
      rw [Finset.mem_filter] at hL
      rw [Finset.mem_union]
      by_cases hΩ : L ∈ Ω
      · left
        unfold alignedSet; rw [Finset.mem_filter, Finset.mem_inter]
        exact ⟨⟨hL.1, hΩ⟩, hL.2⟩
      · right
        rw [Finset.mem_sdiff]; exact ⟨hL.1, hΩ⟩
    have hcardle :
        ((Fgood α).filter (fun L => σ α = s L)).card ≤
          alignedCount Fgood Ω σ s α + outsideCount Fgood Ω α := by
      calc ((Fgood α).filter (fun L => σ α = s L)).card
          ≤ ((alignedSet Fgood Ω σ s α) ∪ (Fgood α \ Ω)).card :=
            Finset.card_le_card hle
        _ ≤ (alignedSet Fgood Ω σ s α).card + (Fgood α \ Ω).card :=
            Finset.card_union_le _ _
        _ = alignedCount Fgood Ω σ s α + outsideCount Fgood Ω α := by
            unfold alignedCount outsideCount outsideSet; rfl
    -- In this branch, mu > 2 · aligned, so mu - aligned > aligned,
    -- so dominant = mu - aligned, and mu - dominant = aligned.
    have hflip' : ¬ mu Fgood α ≤ 2 * alignedCount Fgood Ω σ s α := by
      intro h
      unfold flipIndicator at hflip
      exact hflip (decide_eq_true h)
    have halign_le :
        alignedCount Fgood Ω σ s α ≤ mu Fgood α := by
      have := Fgood_decomposition Fgood Ω σ s α
      omega
    have hdomEq : dominantCount Fgood Ω σ s α =
                    mu Fgood α - alignedCount Fgood Ω σ s α := by
      unfold dominantCount
      refine max_eq_right ?_
      omega
    omega

/-- **Overlap disagreement for `refinedSign`, union bound**
(`step7.tex:339-352`).

For two interfaces `e, f ∈ richStar`, the set of `L ∈ (Fgood e ∩
Fgood f)` on which either `refinedSign e` or `refinedSign f`
disagrees with the reference sign `s(L)` is contained in the union
of the two individual disagreement sets; hence its cardinality is
at most the sum of individual disagreement cardinalities.

This is the "union of the two disagreement sets" sentence of
`step7.tex:348-350`.  Combined with `refinedDisagreeSet_card_le`,
it yields the cleared-denominator overlap-compatibility bound. -/
theorem overlap_disagree_union_bound
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (e f : Pair) :
    ((Fgood e ∩ Fgood f).filter (fun L =>
          refinedSign Fgood Ω σ s e ≠ s L ∨
          refinedSign Fgood Ω σ s f ≠ s L)).card ≤
      (refinedDisagreeSet Fgood Ω σ s e).card +
        (refinedDisagreeSet Fgood Ω σ s f).card := by
  classical
  unfold refinedDisagreeSet
  -- Membership implies membership in either individual disagreement set.
  have hsub :
      (Fgood e ∩ Fgood f).filter (fun L =>
            refinedSign Fgood Ω σ s e ≠ s L ∨
            refinedSign Fgood Ω σ s f ≠ s L) ⊆
        (Fgood e).filter (fun L => refinedSign Fgood Ω σ s e ≠ s L) ∪
          (Fgood f).filter (fun L => refinedSign Fgood Ω σ s f ≠ s L) := by
    intro L hL
    rw [Finset.mem_filter, Finset.mem_inter] at hL
    obtain ⟨⟨hLe, hLf⟩, hor⟩ := hL
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hor with hne | hne
    · exact Or.inl ⟨hLe, hne⟩
    · exact Or.inr ⟨hLf, hne⟩
  calc ((Fgood e ∩ Fgood f).filter (fun L =>
            refinedSign Fgood Ω σ s e ≠ s L ∨
            refinedSign Fgood Ω σ s f ≠ s L)).card
      ≤ (((Fgood e).filter (fun L =>
              refinedSign Fgood Ω σ s e ≠ s L)) ∪
          ((Fgood f).filter (fun L =>
              refinedSign Fgood Ω σ s f ≠ s L))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Fgood e).filter (fun L =>
              refinedSign Fgood Ω σ s e ≠ s L)).card +
          ((Fgood f).filter (fun L =>
              refinedSign Fgood Ω σ s f ≠ s L)).card :=
        Finset.card_union_le _ _

/-- **Sign consistency on active pairs (Lemma A, condition 2)** —
cleared denominator (`step7.tex:339-357`).

For an active pair `(e, f) ∈ refinedSet × refinedSet` (i.e. both
in `E⋆`), the set of overlap points on which the two refined signs
disagree is bounded by the sum of the individual `E⋆`-slack
mismatches plus the two outside-Ω masses.  In cleared denominator:

  `(refinedSign e ≠ s(L) or refinedSign f ≠ s(L)) on overlap`
  `card ≤ (μ_e - dominant_e) + η_e + (μ_f - dominant_f) + η_f`.

Since `e, f ∈ E⋆` gives `δ₁_d · (μ - dominant) ≤ δ₁_n · μ`, the
right-hand side is at most
`(δ₁_n / δ₁_d) · (μ_e + μ_f) + η_e + η_f`, which is the paper's
"`O(δ^{1/4}) · w_{ef}`" bound after using the active-pair lower
bound `w_{ef} ≥ δ^{1/4} · min(μ_e, μ_f)`.

We state the cleaner union bound here; the downstream consumer
(Step 7.d assembly) applies the refined-set and active-pair
inequalities. -/
theorem overlap_agree_of_active_pair
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (e f : Pair) :
    ((Fgood e ∩ Fgood f).filter (fun L =>
          refinedSign Fgood Ω σ s e ≠ s L ∨
          refinedSign Fgood Ω σ s f ≠ s L)).card ≤
      ((mu Fgood e - dominantCount Fgood Ω σ s e) +
          outsideCount Fgood Ω e) +
        ((mu Fgood f - dominantCount Fgood Ω σ s f) +
          outsideCount Fgood Ω f) :=
  (overlap_disagree_union_bound Fgood Ω σ s e f).trans <| by
    exact Nat.add_le_add
      (refinedDisagreeSet_card_le Fgood Ω σ s e)
      (refinedDisagreeSet_card_le Fgood Ω σ s f)

/-- **Corollary (the paper's sign-consistency conclusion at the
overlap, `step7.tex:351-354`)**.

On the overlap of an active pair `(e, f)`, the complement of the
"both refined signs agree with `s(L)`" set has cardinality bounded
by the union bound of the previous theorem; in particular, on the
remaining portion of the overlap, `refinedSign e L = s(L) =
refinedSign f L`, so `refinedSign e = refinedSign f`. -/
theorem refinedSign_agree_on_overlap
    (Fgood : Pair → Finset LinExt) (Ω : Finset LinExt)
    (σ : Pair → Sign) (s : LinExt → Sign) (e f : Pair) :
    ∀ L ∈ (Fgood e ∩ Fgood f).filter (fun L =>
              refinedSign Fgood Ω σ s e = s L ∧
              refinedSign Fgood Ω σ s f = s L),
      refinedSign Fgood Ω σ s e = refinedSign Fgood Ω σ s f := by
  intro L hL
  rw [Finset.mem_filter] at hL
  obtain ⟨_, heq, hfq⟩ := hL
  rw [heq, hfq]

end OverlapAgree

end Step7
end OneThird
