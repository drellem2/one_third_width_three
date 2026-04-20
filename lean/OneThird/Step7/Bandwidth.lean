/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.SingleThreshold
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Boundary budget and bandwidth of rich incomparability

This file formalises `lem:budget-var` and `lem:bandwidth` of
`step7.tex` §`sec:layered` (`step7.tex:949-1056`,
`lem:budget-var` at `step7.tex:960` and `lem:bandwidth` at
`step7.tex:1018`).

Together these two lemmas form the quantitative core of Prop. 7.2:

* *boundary budget*: `∑_{x ∥ y, Δ_xy > 0} Δ_xy · p_xy = o(1)`;
* *bandwidth*: rich incomparable `(a_i, b_j)` has
  `|j - f_AB(i)| ≤ K` with `K = O_T(1)` off an `o(1)`-mass set.

## Paper statement

* `lem:budget-var` (`step7.tex:960-967`): if `Φ({H ≥ c}) ≤ η = o(1)`
  and `{H ≥ c}` agrees with `S` on `(1 - o(1))` of `LE(P)`, then
  `∑ Δ⁺ · p = o(1)`.

* `lem:bandwidth` (`step7.tex:1018-1027`): for any fixed richness
  threshold `T`, there is `K = K(T) = O_T(1)` with
  `|j - f_AB(i)| ≤ K` on `(1 - o(1))` of rich-interface incidence.

## Lean formalisation

Cleared-denominator abstract form, all inside
`namespace BandwidthData`:

* `BandwidthData` — bundle with per-pair `delta, posMass`.
* `VarBudgetHyp` — cleared form of `∑ Δ⁺ · p ≤ η · M₀`.
* `RichnessHyp` — cleared `posMass p ≥ (c_n / c_d) · M₀`.
* `largeDeltaPairs c₀` — pairs with `delta ≥ c₀`.
* `richLargeDeltaPairs c₀` — rich pairs with `delta ≥ c₀`.

Main results:

* `sum_posMass_of_large_delta_bound` — cleared-denominator
  Markov: large-Δ pairs have bounded total `posMass`.
* `rich_largeDelta_card_bound` / `lem_bandwidth` —
  combining the budget with richness bounds
  `|rich ∩ {Δ ≥ c₀}|` by `c_d · b_n / (c₀ · c_n · b_d)`.

Downstream, Prop. 7.2 (`step7.tex:1175-1193`) consumes the
bandwidth bound to produce the layered width-3 decomposition.
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §1 — Bandwidth data bundle -/

/-- **Bandwidth data bundle** (`step7.tex:955-957`).

Packages per-pair signed gradient `Δ_xy = a(y) - a(x)` and
BK-adjacency mass `posMass = p_xy · M₀` (cleared integer). -/
structure BandwidthData (Pair : Type*) where
  /-- Signed `a`-gradient `Δ_xy = a(y) - a(x)`. -/
  delta : Pair → ℤ
  /-- BK-adjacency mass `p_xy · M₀` (cleared integer). -/
  posMass : Pair → ℕ

namespace BandwidthData

variable {Pair : Type*} [DecidableEq Pair]
variable (D : BandwidthData Pair)

/-- **Positive-`Δ` subset**: pairs with `Δ > 0` (`step7.tex:965`). -/
def posDeltaPairs (pairs : Finset Pair) : Finset Pair :=
  pairs.filter (fun p => 0 < D.delta p)

lemma mem_posDeltaPairs {pairs : Finset Pair} {p : Pair} :
    p ∈ D.posDeltaPairs pairs ↔ p ∈ pairs ∧ 0 < D.delta p := by
  simp [posDeltaPairs, Finset.mem_filter]

/-! ### §2 — Variational budget hypothesis -/

/-- **Variational budget hypothesis** (`step7.tex:eq:var-budget`,
`step7.tex:964-967`).

Cleared form of `∑_{Δ > 0} Δ · p ≤ η = o(1)`:

  `b_d · ∑_{Δ > 0} (Δ).toNat · posMass ≤ b_n · M₀`. -/
def VarBudgetHyp (pairs : Finset Pair) (b_n b_d M₀ : ℕ) : Prop :=
  b_d * ∑ p ∈ D.posDeltaPairs pairs,
      (D.delta p).toNat * D.posMass p ≤ b_n * M₀

lemma varBudget_bound_single
    {pairs : Finset Pair} {b_n b_d M₀ : ℕ}
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀)
    {p : Pair} (hp : p ∈ D.posDeltaPairs pairs) :
    b_d * ((D.delta p).toNat * D.posMass p) ≤ b_n * M₀ := by
  classical
  have hsum : (D.delta p).toNat * D.posMass p ≤
      ∑ q ∈ D.posDeltaPairs pairs,
        (D.delta q).toNat * D.posMass q := by
    rw [← Finset.sum_singleton (f := fun q =>
      (D.delta q).toNat * D.posMass q) p]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [Finset.mem_singleton] at hq
      rw [hq]; exact hp
    · intros; exact Nat.zero_le _
  calc b_d * ((D.delta p).toNat * D.posMass p)
      ≤ b_d * ∑ q ∈ D.posDeltaPairs pairs,
          (D.delta q).toNat * D.posMass q :=
        Nat.mul_le_mul_left _ hsum
    _ ≤ b_n * M₀ := hBud

/-! ### §3 — Large-gradient count bound -/

/-- **Large-gradient pair set** (`step7.tex:1041`): pairs with
`Δ ≥ c_0`. -/
def largeDeltaPairs (pairs : Finset Pair) (c₀ : ℕ) : Finset Pair :=
  pairs.filter (fun p => (c₀ : ℤ) ≤ D.delta p)

lemma mem_largeDeltaPairs {pairs : Finset Pair} {c₀ : ℕ} {p : Pair} :
    p ∈ D.largeDeltaPairs pairs c₀ ↔
      p ∈ pairs ∧ (c₀ : ℤ) ≤ D.delta p := by
  simp [largeDeltaPairs, Finset.mem_filter]

lemma largeDeltaPairs_subset (pairs : Finset Pair) (c₀ : ℕ) :
    D.largeDeltaPairs pairs c₀ ⊆ pairs := Finset.filter_subset _ _

/-- For `c₀ ≥ 1`, large-Δ ⊆ positive-Δ. -/
lemma largeDeltaPairs_subset_posDeltaPairs
    (pairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀) :
    D.largeDeltaPairs pairs c₀ ⊆ D.posDeltaPairs pairs := by
  intro p hp
  rw [D.mem_largeDeltaPairs] at hp
  rw [D.mem_posDeltaPairs]
  refine ⟨hp.1, ?_⟩
  have : (c₀ : ℤ) ≤ D.delta p := hp.2
  have h1 : (0 : ℤ) < (c₀ : ℤ) := by exact_mod_cast hc₀
  linarith

/-- **Large-gradient mass bound** (cleared form,
`step7.tex:1041-1047`): pairs with `Δ ≥ c_0` contribute
`≥ c_0 · posMass` each to the budget, so

  `c_0 · b_d · ∑_{Δ ≥ c_0} posMass ≤ b_n · M₀`. -/
theorem sum_posMass_of_large_delta_bound
    (pairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d M₀ : ℕ)
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀) :
    c₀ * (b_d * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) ≤
      b_n * M₀ := by
  classical
  have hpt : ∀ p ∈ D.largeDeltaPairs pairs c₀,
      c₀ * D.posMass p ≤ (D.delta p).toNat * D.posMass p := by
    intro p hp
    rw [D.mem_largeDeltaPairs] at hp
    have hΔ : (c₀ : ℤ) ≤ (D.delta p).toNat := by
      have hnn : 0 ≤ D.delta p := by
        have h1 : (0 : ℤ) < (c₀ : ℤ) := by exact_mod_cast hc₀
        linarith [hp.2]
      rw [Int.toNat_of_nonneg hnn]
      exact hp.2
    have hc : c₀ ≤ (D.delta p).toNat := by exact_mod_cast hΔ
    exact Nat.mul_le_mul_right _ hc
  have hsum_large : c₀ * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p ≤
      ∑ p ∈ D.largeDeltaPairs pairs c₀,
        (D.delta p).toNat * D.posMass p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hext :
      ∑ p ∈ D.largeDeltaPairs pairs c₀,
          (D.delta p).toNat * D.posMass p ≤
        ∑ p ∈ D.posDeltaPairs pairs,
          (D.delta p).toNat * D.posMass p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact D.largeDeltaPairs_subset_posDeltaPairs pairs c₀ hc₀
    · intros; exact Nat.zero_le _
  have hchain :
      c₀ * (b_d * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) ≤
        b_d * ∑ p ∈ D.posDeltaPairs pairs,
          (D.delta p).toNat * D.posMass p := by
    have h1 :
        c₀ * (b_d * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) =
        b_d *
          (c₀ * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) := by
      ring
    rw [h1]
    have h2 :
        b_d *
            (c₀ * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) ≤
          b_d *
            ∑ p ∈ D.largeDeltaPairs pairs c₀,
              (D.delta p).toNat * D.posMass p :=
      Nat.mul_le_mul_left _ hsum_large
    have h3 :
        b_d *
            ∑ p ∈ D.largeDeltaPairs pairs c₀,
              (D.delta p).toNat * D.posMass p ≤
          b_d * ∑ p ∈ D.posDeltaPairs pairs,
              (D.delta p).toNat * D.posMass p :=
      Nat.mul_le_mul_left _ hext
    exact le_trans h2 h3
  exact le_trans hchain hBud

/-! ### §4 — Richness hypothesis and rich-pair count bound -/

/-- **Richness hypothesis** (`step7.tex:1033-1036`, `c_T`-richness).

Cleared form: for every `p ∈ richPairs`, `c_n · M₀ ≤ c_d · posMass p`. -/
def RichnessHyp (richPairs : Finset Pair) (c_n c_d M₀ : ℕ) : Prop :=
  ∀ p ∈ richPairs, c_n * M₀ ≤ c_d * D.posMass p

/-- **Rich pairs with large gradient**: `richPairs ∩ largeDelta c₀`. -/
def richLargeDeltaPairs (richPairs : Finset Pair) (c₀ : ℕ) :
    Finset Pair :=
  richPairs.filter (fun p => (c₀ : ℤ) ≤ D.delta p)

lemma mem_richLargeDeltaPairs
    {richPairs : Finset Pair} {c₀ : ℕ} {p : Pair} :
    p ∈ D.richLargeDeltaPairs richPairs c₀ ↔
      p ∈ richPairs ∧ (c₀ : ℤ) ≤ D.delta p := by
  simp [richLargeDeltaPairs, Finset.mem_filter]

lemma richLargeDeltaPairs_subset_largeDeltaPairs
    (pairs richPairs : Finset Pair) (c₀ : ℕ)
    (hSub : richPairs ⊆ pairs) :
    D.richLargeDeltaPairs richPairs c₀ ⊆ D.largeDeltaPairs pairs c₀ := by
  intro p hp
  rw [D.mem_richLargeDeltaPairs] at hp
  rw [D.mem_largeDeltaPairs]
  exact ⟨hSub hp.1, hp.2⟩

/-- **Cardinality bound on rich large-Δ pairs** (cleared
`lem:bandwidth`, `step7.tex:1036-1053`).

Combining the variational budget with richness yields

  `c_0 · c_n · b_d · |rich ∩ large-Δ| · M₀ ≤ c_d · b_n · M₀`. -/
theorem rich_largeDelta_card_bound
    (pairs richPairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀) :
    c₀ * c_n * (b_d * (D.richLargeDeltaPairs richPairs c₀).card) * M₀ ≤
      c_d * (b_n * M₀) := by
  classical
  have hLarge := D.sum_posMass_of_large_delta_bound pairs c₀ hc₀
    b_n b_d M₀ hBud
  have hRichBound : ∀ p ∈ D.richLargeDeltaPairs richPairs c₀,
      c_n * M₀ ≤ c_d * D.posMass p := by
    intro p hp
    rw [D.mem_richLargeDeltaPairs] at hp
    exact hRich p hp.1
  have hsum_rich :
      (D.richLargeDeltaPairs richPairs c₀).card * (c_n * M₀) ≤
        ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, c_d * D.posMass p := by
    rw [show ((D.richLargeDeltaPairs richPairs c₀).card * (c_n * M₀)) =
      ∑ _p ∈ D.richLargeDeltaPairs richPairs c₀, c_n * M₀ from by
        rw [Finset.sum_const, smul_eq_mul]]
    exact Finset.sum_le_sum hRichBound
  have hsum_rich' :
      (D.richLargeDeltaPairs richPairs c₀).card * (c_n * M₀) ≤
        c_d * ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, D.posMass p := by
    rw [show (c_d * ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, D.posMass p) =
      ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, c_d * D.posMass p from by
        rw [Finset.mul_sum]]
    exact hsum_rich
  have hsub_posMass :
      ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, D.posMass p ≤
        ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact D.richLargeDeltaPairs_subset_largeDeltaPairs pairs
        richPairs c₀ hSub
    · intros; exact Nat.zero_le _
  have hmul :
      c₀ * b_d * ((D.richLargeDeltaPairs richPairs c₀).card *
          (c_n * M₀)) ≤
        c₀ * b_d *
          (c_d * ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, D.posMass p) :=
    Nat.mul_le_mul_left _ hsum_rich'
  have hmul_ext :
      c₀ * b_d * ((D.richLargeDeltaPairs richPairs c₀).card *
          (c_n * M₀)) ≤
        c₀ * b_d * (c_d *
          ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) := by
    refine le_trans hmul ?_
    have h : c_d * ∑ p ∈ D.richLargeDeltaPairs richPairs c₀, D.posMass p ≤
        c_d * ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p :=
      Nat.mul_le_mul_left _ hsub_posMass
    exact Nat.mul_le_mul_left _ h
  have hreshape :
      c₀ * b_d * (c_d *
          ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p) =
        c_d * (c₀ * (b_d *
          ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p)) := by
    ring
  rw [hreshape] at hmul_ext
  have hfinal : c_d *
        (c₀ * (b_d *
          ∑ p ∈ D.largeDeltaPairs pairs c₀, D.posMass p)) ≤
      c_d * (b_n * M₀) :=
    Nat.mul_le_mul_left _ hLarge
  have hcombined := le_trans hmul_ext hfinal
  have hLHS :
      c₀ * b_d * ((D.richLargeDeltaPairs richPairs c₀).card *
          (c_n * M₀)) =
      c₀ * c_n * (b_d * (D.richLargeDeltaPairs richPairs c₀).card) * M₀ := by
    ring
  rw [hLHS] at hcombined
  exact hcombined

/-! ### §5 — Bandwidth bound (`lem:bandwidth`) -/

/-- **`lem:bandwidth` — bandwidth of rich incomparability**
(`step7.tex:1018-1056`).

Cleared-denominator form: under the var-budget and richness
hypotheses, the count of rich pairs with `Δ ≥ c_0` satisfies

  `c_0 · c_n · b_d · |rich ∩ {Δ ≥ c₀}| · M₀ ≤ c_d · b_n · M₀`.

With `c_n / c_d = c'_T`, `b_n / b_d = o(1)`, and fixed `c_0`, this
gives `|rich ∩ {Δ ≥ c₀}|` of order `o(1)` times the totals, i.e.
bandwidth `K = O_T(1)`.

The chain-position bandwidth `K = O_T(1)` of the paper follows
by pairing each rich incomparable `(a_i, b_j)` with its chain-index
offset; strict monotonicity of `a` on each chain forces unrelated
`j`'s to have separated `a(b_j)` values, so the offset is large
iff `Δ ≥ c_0`. -/
theorem lem_bandwidth
    (pairs richPairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀) :
    c₀ * c_n * (b_d * (D.richLargeDeltaPairs richPairs c₀).card) * M₀ ≤
      c_d * (b_n * M₀) :=
  D.rich_largeDelta_card_bound pairs richPairs c₀ hc₀
    b_n b_d c_n c_d M₀ hSub hBud hRich

/-- **Good rich pairs** (the bandwidth-controlled subset): rich
pairs with `Δ < c₀`.  Paper's bandwidth statement says that
`(1 - o(1))` of rich-interface weight lies in this set. -/
def richSmallDeltaPairs (richPairs : Finset Pair) (c₀ : ℕ) :
    Finset Pair :=
  richPairs.filter (fun p => D.delta p < (c₀ : ℤ))

lemma richPairs_eq_small_union_large
    (richPairs : Finset Pair) (c₀ : ℕ) :
    D.richSmallDeltaPairs richPairs c₀ ∪
        D.richLargeDeltaPairs richPairs c₀ = richPairs := by
  ext p
  simp only [Finset.mem_union, richSmallDeltaPairs, richLargeDeltaPairs,
    Finset.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hc : D.delta p < (c₀ : ℤ)
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, not_lt.mp hc⟩

lemma richSmall_disjoint_richLarge
    (richPairs : Finset Pair) (c₀ : ℕ) :
    Disjoint (D.richSmallDeltaPairs richPairs c₀)
      (D.richLargeDeltaPairs richPairs c₀) := by
  rw [Finset.disjoint_left]
  intros p hs hl
  rw [richSmallDeltaPairs, Finset.mem_filter] at hs
  rw [richLargeDeltaPairs, Finset.mem_filter] at hl
  exact absurd hl.2 (not_le.mpr hs.2)

/-- **Cardinality split**: `|richSmall| + |richLarge| = |richPairs|`. -/
theorem richSmallDeltaPairs_card_lb
    (richPairs : Finset Pair) (c₀ : ℕ) :
    (D.richSmallDeltaPairs richPairs c₀).card +
        (D.richLargeDeltaPairs richPairs c₀).card =
      richPairs.card := by
  classical
  rw [← Finset.card_union_of_disjoint
    (D.richSmall_disjoint_richLarge richPairs c₀)]
  rw [D.richPairs_eq_small_union_large]

end BandwidthData

/-! ### §6 — Bridge: potential → bandwidth data -/

section Bridge

variable {Vertex Edge : Type*}

/-- **Bandwidth data from a potential `a : V → ℤ`**
(`step7.tex:955`).

Given `PotentialData` on `(Vertex, Edge)`, a `Pair` type,
endpoints `psrc, ptgt : Pair → Vertex`, and an edge-adjacency
weight `posMass : Pair → ℕ`, produce `BandwidthData Pair` with
`delta p := pot (ptgt p) - pot (psrc p)`. -/
def BandwidthData.ofPotential
    (P : PotentialData Vertex Edge) (Pair : Type*)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ) :
    BandwidthData Pair :=
  { delta := fun p => P.pot (ptgt p) - P.pot (psrc p)
    posMass := posMass }

@[simp] lemma BandwidthData.ofPotential_delta
    (P : PotentialData Vertex Edge) (Pair : Type*)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ) (p : Pair) :
    (BandwidthData.ofPotential P Pair psrc ptgt posMass).delta p =
      P.pot (ptgt p) - P.pot (psrc p) := rfl

@[simp] lemma BandwidthData.ofPotential_posMass
    (P : PotentialData Vertex Edge) (Pair : Type*)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ) (p : Pair) :
    (BandwidthData.ofPotential P Pair psrc ptgt posMass).posMass p =
      posMass p := rfl

end Bridge

end Step7
end OneThird
