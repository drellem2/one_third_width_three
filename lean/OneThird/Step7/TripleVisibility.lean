/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step5.SecondMoment
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Active-triple visibility (`lem:triple-visibility`)

This file formalises `lem:triple-visibility` of `step7.tex`
(`step7.tex:1376-1482`, sub-arc S7-B / G3 per `mg-6ab8` Phase E
spec), the active-triple visibility lemma that promotes Step 5's
second-moment visibility bound into a non-vacuous triple-overlap
mass bound (the *triple-density* input of `lem:cocycle`).

## Paper statement (`step7.tex:1376-1406`)

Assume the rich case (R) of Step 5 with richness constant `c_T`,
together with the bad-set bound `|B_α| ≤ C·t_α` of Step 1.
Writing `I(L) := #{α ∈ Rich⋆ : L ∈ F*_α}` for the visibility count
(where `F*_α := fib_α \ B_α` is the *cleaned* good fiber), the
lemma asserts three identities:

* **(a) Third moment.**
  `∑_{L ∈ LE(P)} I(L)^3 ≥ c_T^{(3)} · |LE(P)|`
  with `c_T^{(3)} := (c_T/2)^3` — Jensen on the convex function
  `x ↦ x^3` lifted from the first-moment richness lower bound.
* **(b) Triple-overlap mass = visibility cube.**
  Writing `w_{αβγ} := |F*α ∩ F*β ∩ F*γ|`, the Fubini identity
  `∑_{(α,β,γ) ∈ Rich⋆³} w_{αβγ} = ∑_{L} I(L)^3`,
  combined with (a), yields the triple-overlap mass lower bound.
* **(c) Edge fraction in triples.**
  Setting `M := ∑_{α≠β} w_{αβ} = ∑_L I(L)·(I(L)-1)` (the ordered
  active-pair mass), the failure weight from `I(L) ≤ 2` extensions
  is at most `2·|LE(P)|`, while `M` is bounded below by Step 5's
  second-moment `c² · |LE(P)| ≤ ∑ I²`.  In the cleared-denominator
  form (`step7.tex:1437-1453`):
    `2·M + |LE(P)| ≥ c²·|LE(P)|` (equivalently `M ≥ (c²-1)/2 · |LE(P)|`),
  giving failure fraction `≤ 4/(c²-1) = O(1/c')` as `c → ∞`.

## Lean formalisation

We follow the cleared-denominator parametric pattern used by
`SignedThreshold.lean` and `SignConsistency.lean`:

* `tripleOverlap Fstar α β γ` — the cleaned triple-overlap set
  `F*α ∩ F*β ∩ F*γ` as a `Finset LinExt`.
* `tripleOverlapMass Fstar α β γ` — its cardinality `w_{αβγ}`.
* `Step5.visibility richStar Fstar L` — the visibility count `I(L)`
  (re-used directly from Step 5).
* `edgeMass richStar Fstar LP` — the ordered active-pair mass
  `M := ∑_L I(L)·(I(L)-1)`.
* `failureWeight richStar Fstar LP` — the *low-visibility* edge
  mass `∑_{L:I(L)≤2} I(L)·(I(L)-1)`.

The main theorems are:

* `triple_overlap_mass_sum_eq_visibility_cube` — Fubini identity
  for (b): `∑ w_{αβγ} = ∑_L I(L)^3`.
* `third_moment_visibility` — Jensen lower bound (a):
  `c³·|LP| ≤ ∑_L I(L)^3`, from the first-moment input
  `c·|LP| ≤ ∑_α |F*_α|`.
* `triple_overlap_mass_lower_bound` — combination (a)+(b):
  `c³·|LP| ≤ ∑_{αβγ} w_{αβγ}`.
* `failure_weight_le_two_card` — pointwise bound for (c):
  `failure_weight ≤ 2·|LP|`.
* `edge_mass_lower_bound_via_second_moment` — Step-5-second-moment
  feed-through for (c):
  `c²·|LP| ≤ 2·edgeMass + |LP|`
  (equivalently `2·M + |LP| ≥ c²·|LP|`).
* `edge_fraction_in_triples_failure_bound` — cleared-denominator
  (c) bound: `(c²-1)·failureWeight ≤ 4·edgeMass`, i.e. the failure
  fraction is at most `4/(c²-1)`.

Downstream, `lem:cocycle` consumes the triple-overlap mass via the
abstract `TripleData.weight T` field of `Cocycle.lean`; the
edge-fraction-in-triples bound feeds the
`(1 - o(1))`-fraction premise of `lem:cocycle` proper.
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §1 — Triple-overlap mass and Fubini cube identity -/

section TripleOverlap

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Cleaned triple-overlap set** (`step7.tex:1387-1389`,
`w_{αβγ}` numerator).

The set of linear extensions in the cleaned good fibers of all
three rich pairs `α, β, γ`:
`tripleOverlap F* α β γ := F*α ∩ F*β ∩ F*γ`.

By convention `Fstar α := fib_α \ B_α` is the cleaned good fiber
(`step5.tex` notation), so the bad-set subtraction
`\ (B_α ∪ B_β ∪ B_γ)` of the paper is already baked into the
intersection. -/
def tripleOverlap (Fstar : Pair → Finset LinExt) (α β γ : Pair) :
    Finset LinExt :=
  Fstar α ∩ Fstar β ∩ Fstar γ

lemma mem_tripleOverlap {Fstar : Pair → Finset LinExt}
    {α β γ : Pair} {L : LinExt} :
    L ∈ tripleOverlap Fstar α β γ ↔
      L ∈ Fstar α ∧ L ∈ Fstar β ∧ L ∈ Fstar γ := by
  unfold tripleOverlap
  simp [Finset.mem_inter, and_assoc]

/-- **Triple-overlap mass** (`step7.tex:1387-1389`,
`w_{αβγ}`). -/
def tripleOverlapMass (Fstar : Pair → Finset LinExt) (α β γ : Pair) :
    ℕ :=
  (tripleOverlap Fstar α β γ).card

/-- **Cube-visibility Fubini identity** (`lem:triple-visibility`
part (b), `step7.tex:1387-1395`).

`∑_{(α,β,γ) ∈ Rich⋆³} w_{αβγ} = ∑_{L ∈ LP} I(L)^3`,

where the left-hand sum is over ordered triples of rich pairs.

Proof (`step7.tex:1418-1428`).  Both sides count the cardinality of

  `{(α, β, γ, L) ∈ richStar³ × LP : L ∈ F*α ∩ F*β ∩ F*γ}`

via the indicator expansion `I(L)^3 = ∑_{(α,β,γ)} 𝟙[L ∈ F*α ∩
F*β ∩ F*γ]`.  The hypothesis `hsub` (`F*α ⊆ LP` for each rich
pair) ensures the `LP`-side sum captures all contributions.

The proof is pure double-counting; it does not consume any of the
analytic Step 5 / Step 6 hypotheses. -/
theorem triple_overlap_mass_sum_eq_visibility_cube
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP) :
    ∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar,
        tripleOverlapMass Fstar αβγ.1 αβγ.2.1 αβγ.2.2 =
      ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 := by
  classical
  -- Strategy: rewrite both sides as the common 4-tuple sum
  --   `∑_{(αβγ) ∈ richStar³} ∑_{L ∈ LP} 𝟙[L ∈ F*α ∩ F*β ∩ F*γ]`,
  -- which counts the cardinality of
  --   `{(α, β, γ, L) ∈ richStar³ × LP : L ∈ F*α ∩ F*β ∩ F*γ}`.
  -- The LHS-side groups by `(α, β, γ)` (and uses `F*α ⊆ LP` to drop the
  -- `L ∈ LP` restriction); the RHS-side groups by `L` (and expands
  -- `I(L)^3` via the cube of indicators).
  -- ----- LHS = common form -----
  have hLHS :
      ∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar,
          tripleOverlapMass Fstar αβγ.1 αβγ.2.1 αβγ.2.2 =
        ∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar, ∑ L ∈ LP,
          (if L ∈ Fstar αβγ.1 ∧ L ∈ Fstar αβγ.2.1 ∧ L ∈ Fstar αβγ.2.2
            then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    rintro ⟨α, β, γ⟩ habg
    rw [Finset.mem_product, Finset.mem_product] at habg
    obtain ⟨hα, hβ, hγ⟩ := habg
    have hsubα : Fstar α ⊆ LP := hsub α hα
    have hsubO : tripleOverlap Fstar α β γ ⊆ LP := by
      intro L hL; rw [mem_tripleOverlap] at hL; exact hsubα hL.1
    -- tripleOverlapMass = card = sum-of-1s; extend the sum to LP via subset.
    unfold tripleOverlapMass
    rw [Finset.card_eq_sum_ones]
    rw [show (∑ _ ∈ tripleOverlap Fstar α β γ, (1 : ℕ)) =
        ∑ L ∈ LP, (if L ∈ tripleOverlap Fstar α β γ then (1 : ℕ) else 0) from ?_]
    · apply Finset.sum_congr rfl; intro L _
      by_cases h : L ∈ Fstar α ∧ L ∈ Fstar β ∧ L ∈ Fstar γ
      · have hL : L ∈ tripleOverlap Fstar α β γ := by
          rw [mem_tripleOverlap]; exact h
        simp [h, hL]
      · have hL : L ∉ tripleOverlap Fstar α β γ := by
          rw [mem_tripleOverlap]; exact h
        simp [h, hL]
    · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr hsubO]
  -- ----- RHS = common form (with α-β-γ ↔ L order swapped) -----
  have hRHS :
      (∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3) =
        ∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar, ∑ L ∈ LP,
          (if L ∈ Fstar αβγ.1 ∧ L ∈ Fstar αβγ.2.1 ∧ L ∈ Fstar αβγ.2.2
            then (1 : ℕ) else 0) := by
    -- Step 1: pointwise: I(L)^3 = #{(αβγ) ∈ richStar^3 : L ∈ all three}.
    have hpt : ∀ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 =
        ∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar,
          (if L ∈ Fstar αβγ.1 ∧ L ∈ Fstar αβγ.2.1 ∧ L ∈ Fstar αβγ.2.2
            then (1 : ℕ) else 0) := by
      intro L _
      unfold Step5.visibility
      set S : Finset Pair := richStar.filter (fun α => L ∈ Fstar α)
      -- (richStar^3).filter (all three) = S × S × S
      have hSSS : ((richStar ×ˢ richStar ×ˢ richStar).filter
          (fun αβγ => L ∈ Fstar αβγ.1 ∧ L ∈ Fstar αβγ.2.1 ∧ L ∈ Fstar αβγ.2.2)) =
          S ×ˢ S ×ˢ S := by
        ext ⟨α, β, γ⟩
        simp only [Finset.mem_filter, Finset.mem_product, S]
        tauto
      have hcard3 : S.card ^ 3 = (S ×ˢ S ×ˢ S).card := by
        rw [Finset.card_product, Finset.card_product]; ring
      rw [hcard3, ← hSSS, Finset.card_filter]
    rw [Finset.sum_congr rfl hpt]
    -- Step 2: swap L ↔ (αβγ) at the top level (single Finset.sum_comm).
    rw [Finset.sum_comm]
  -- Conclude.
  rw [hLHS, hRHS]

end TripleOverlap

/-! ### §2 — Third-moment lower bound (Jensen) -/

section ThirdMoment

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Third-moment Jensen inequality** for ℕ-valued sums
(`step7.tex:1410-1416`).

For any `f : LinExt → ℕ` on a finite set `LP`,
`(∑ f)^3 ≤ |LP|^2 · ∑ f^3`.

This is a direct specialisation of `Finset.pow_sum_le_card_mul_sum_pow`
(mathlib's `Mathlib.Algebra.Order.Chebyshev`) at `n = 2`, applied to
`ℕ`-valued `f` (all values are nonneg by `Nat.zero_le`). -/
private lemma sum_pow3_le_card_sq_mul_sum_pow3
    (LP : Finset LinExt) (f : LinExt → ℕ) :
    (∑ L ∈ LP, f L) ^ 3 ≤ LP.card ^ 2 * ∑ L ∈ LP, (f L) ^ 3 := by
  have h := pow_sum_le_card_mul_sum_pow (s := LP) (f := f)
    (fun _ _ => Nat.zero_le _) 2
  -- `h : (∑ L ∈ LP, f L) ^ (2 + 1) ≤ LP.card ^ 2 * ∑ L ∈ LP, f L ^ (2 + 1)`
  simpa using h

/-- **Third-moment visibility bound** (`lem:triple-visibility`
part (a), `step7.tex:1385-1416`).

From a first-moment Richness lower bound
`c · |LP| ≤ ∑_α |F*_α|`
together with `F*_α ⊆ LP` for every rich pair, Jensen on `x ↦ x^3`
yields
`c³ · |LP| ≤ ∑_{L ∈ LP} I(L)^3`.

Proof (`step7.tex:1408-1416`).
1. By `Step5.visibility_sum_eq_fiber_mass`, `∑_L I(L) = ∑_α |F*_α|`.
2. The first-moment hypothesis gives `c · |LP| ≤ ∑ I`.
3. Cubing: `c³ · |LP|³ ≤ (∑ I)³`.
4. By `sum_pow3_le_card_sq_mul_sum_pow3`,
   `(∑ I)³ ≤ |LP|² · ∑ I³`.
5. Combine: `c³ · |LP|³ ≤ |LP|² · ∑ I³`.  When `|LP| > 0`, cancel
   `|LP|²` to get `c³ · |LP| ≤ ∑ I³`.  When `|LP| = 0`, both sides
   are 0.

The cleared-denominator form `c³ · |LP| ≤ ∑ I³` is exact in ℕ. -/
theorem third_moment_visibility
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card) :
    c ^ 3 * LP.card ≤
      ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 := by
  classical
  -- Step 1: ∑ I(L) ≥ c * |LP|.
  have hfirstI : c * LP.card ≤
      ∑ L ∈ LP, Step5.visibility richStar Fstar L := by
    rw [Step5.visibility_sum_eq_fiber_mass richStar Fstar LP hsub]
    exact hfirst
  -- Step 2: Jensen on x → x^3.
  have hJ : (∑ L ∈ LP, Step5.visibility richStar Fstar L) ^ 3 ≤
      LP.card ^ 2 * ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 :=
    sum_pow3_le_card_sq_mul_sum_pow3 LP _
  -- Step 3: cube the first-moment bound.
  have hcube : (c * LP.card) ^ 3 ≤
      (∑ L ∈ LP, Step5.visibility richStar Fstar L) ^ 3 :=
    Nat.pow_le_pow_left hfirstI 3
  -- Step 4: chain.
  have hcombo : c ^ 3 * LP.card ^ 3 ≤
      LP.card ^ 2 * ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 := by
    calc c ^ 3 * LP.card ^ 3
        = (c * LP.card) ^ 3 := by ring
      _ ≤ (∑ L ∈ LP, Step5.visibility richStar Fstar L) ^ 3 := hcube
      _ ≤ LP.card ^ 2 * ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 :=
          hJ
  -- Step 5: cancel |LP|^2.
  rcases Nat.eq_zero_or_pos LP.card with hzero | hpos
  · rw [hzero]; simp
  · have hsqpos : 0 < LP.card ^ 2 := pow_pos hpos 2
    have hrw : c ^ 3 * LP.card ^ 3 =
        LP.card ^ 2 * (c ^ 3 * LP.card) := by ring
    rw [hrw] at hcombo
    exact Nat.le_of_mul_le_mul_left hcombo hsqpos

/-- **Triple-overlap mass lower bound** — combination of
`lem:triple-visibility` (a) and (b) (`step7.tex:1387-1395`).

`c³ · |LP| ≤ ∑_{(α,β,γ) ∈ Rich⋆³} w_{αβγ}`.

This is the *triple-density* input consumed downstream by
`lem:cocycle` (`step7.tex:391`): without it, the cocycle
integration is over an empty graph (cf. `step7.tex:1373-1374`). -/
theorem triple_overlap_mass_lower_bound
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card) :
    c ^ 3 * LP.card ≤
      ∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar,
        tripleOverlapMass Fstar αβγ.1 αβγ.2.1 αβγ.2.2 := by
  rw [triple_overlap_mass_sum_eq_visibility_cube richStar Fstar LP hsub]
  exact third_moment_visibility richStar Fstar LP c hsub hfirst

end ThirdMoment

/-! ### §3 — Edge fraction in active triples -/

section EdgeFraction

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **Edge mass** `M := ∑_L I(L)·(I(L)-1) = ∑_{α ≠ β} w_{αβ}`
(`step7.tex:1396-1397`).

The total mass of ordered pairs `(L, α, β)` with `α ≠ β` and
`L ∈ F*α ∩ F*β`; equivalently the second factorial moment of the
visibility count `I(L)` summed over `LP`. -/
def edgeMass (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) : ℕ :=
  ∑ L ∈ LP,
    Step5.visibility richStar Fstar L *
      (Step5.visibility richStar Fstar L - 1)

/-- **Failure weight** — the edge mass contributed by linear
extensions with low visibility (`step7.tex:1435-1440`).

A pair `(L, α, β)` *fails* to extend to an active triple iff
`I(L) ≤ 2`; the total failure mass is

  `failureWeight := ∑_{L : I(L) ≤ 2} I(L)·(I(L)-1)`.

For `I ∈ {0, 1, 2}` we have `I·(I-1) ∈ {0, 0, 2}`, so the pointwise
failure-mass contribution is at most `2`. -/
def failureWeight (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) : ℕ :=
  ∑ L ∈ LP.filter (fun L => Step5.visibility richStar Fstar L ≤ 2),
    Step5.visibility richStar Fstar L *
      (Step5.visibility richStar Fstar L - 1)

/-- Pointwise: `I·(I-1) ≤ 2` for `I ≤ 2` (`step7.tex:1438`). -/
private lemma mul_pred_le_two_of_le_two (I : ℕ) (h : I ≤ 2) :
    I * (I - 1) ≤ 2 := by
  match I, h with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide

/-- **Failure-weight bound** (`step7.tex:1437-1440`).

`failureWeight ≤ 2·|LP|`: each `L` with `I(L) ≤ 2` contributes
at most `2` to the failure mass, and there are at most `|LP|` such
extensions. -/
theorem failure_weight_le_two_card
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) :
    failureWeight richStar Fstar LP ≤ 2 * LP.card := by
  classical
  unfold failureWeight
  -- Each term ≤ 2 by mul_pred_le_two_of_le_two, count ≤ |LP|.
  calc ∑ L ∈ LP.filter (fun L => Step5.visibility richStar Fstar L ≤ 2),
          Step5.visibility richStar Fstar L *
            (Step5.visibility richStar Fstar L - 1)
      ≤ ∑ _ ∈ LP.filter (fun L => Step5.visibility richStar Fstar L ≤ 2),
          (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro L hL
        rw [Finset.mem_filter] at hL
        exact mul_pred_le_two_of_le_two _ hL.2
    _ = 2 * (LP.filter (fun L => Step5.visibility richStar Fstar L ≤ 2)).card := by
        rw [Finset.sum_const]
        ring
    _ ≤ 2 * LP.card := by
        exact Nat.mul_le_mul_left _
          (Finset.card_le_card (Finset.filter_subset _ _))

/-- **Pointwise lower bound** for the high-visibility sliver:
`2·I·(I-1) ≥ I²` whenever `I ≥ 2`.

Used in the proof of `edge_mass_lower_bound_via_second_moment`:
on the set `{L : I(L) ≥ 2}`, `2·I·(I-1) ≥ I²`, which lets us
bound `2·M` below by `∑_{L:I(L)≥2} I²`. -/
private lemma two_mul_mul_pred_ge_sq_of_two_le (I : ℕ) (h : 2 ≤ I) :
    I ^ 2 ≤ 2 * (I * (I - 1)) := by
  -- Rewrite `I - 1` in ℤ-land: since I ≥ 2, I = (I - 1) + 1, so
  -- 2·I·(I-1) = 2·((I-1)+1)·(I-1) = 2·(I-1)² + 2·(I-1).
  -- I² = ((I-1)+1)² = (I-1)² + 2·(I-1) + 1.
  -- Diff: 2·I·(I-1) - I² = (I-1)² - 1 = (I-2)·I ≥ 0 since I ≥ 2.
  obtain ⟨k, rfl⟩ : ∃ k, I = k + 2 := ⟨I - 2, by omega⟩
  -- Now I = k + 2, I - 1 = k + 1.
  show (k + 2) ^ 2 ≤ 2 * ((k + 2) * ((k + 2) - 1))
  have hk : (k + 2) - 1 = k + 1 := by omega
  rw [hk]
  ring_nf
  nlinarith [sq_nonneg k]

/-- **Edge-mass lower bound via second moment**
(`step7.tex:1441-1450`).

From a first-moment Richness lower bound `c·|LP| ≤ ∑_α |F*_α|`,
Step 5's `second_moment_visibility` gives `c²·|LP| ≤ ∑ I²`, and
the pointwise inequality `2·I·(I-1) ≥ I²` on `{L : I(L) ≥ 2}`
combined with `I² ≤ 1` on `{L : I(L) ≤ 1}` yields

  `c² · |LP| ≤ 2 · edgeMass + |LP|`.

Equivalently `2·M ≥ (c² - 1)·|LP|`.

This is the second-moment route to a positive lower bound on the
edge mass `M`, the denominator of the `lem:triple-visibility` (c)
failure-fraction bound. -/
theorem edge_mass_lower_bound_via_second_moment
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card) :
    c ^ 2 * LP.card ≤ 2 * edgeMass richStar Fstar LP + LP.card := by
  classical
  -- Step 1: Step 5 second-moment bound: c² · |LP| ≤ ∑ I².
  have h2 : c ^ 2 * LP.card ≤
      ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 2 :=
    Step5.second_moment_visibility richStar Fstar LP c hsub hfirst
  -- Step 2: split ∑ I² = ∑_{I≥2} I² + ∑_{I≤1} I².
  let S₁ : Finset LinExt := LP.filter
    (fun L => 2 ≤ Step5.visibility richStar Fstar L)
  let S₂ : Finset LinExt := LP.filter
    (fun L => Step5.visibility richStar Fstar L ≤ 1)
  have hpart : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_filter]
    intro L _ h1 h2
    omega
  have hunion : S₁ ∪ S₂ = LP := by
    ext L
    simp only [Finset.mem_union, Finset.mem_filter, S₁, S₂]
    constructor
    · rintro (⟨hL, _⟩ | ⟨hL, _⟩) <;> exact hL
    · intro hL
      by_cases hI : 2 ≤ Step5.visibility richStar Fstar L
      · left; exact ⟨hL, hI⟩
      · right; exact ⟨hL, by omega⟩
  have hsplit :
      ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 2 =
        (∑ L ∈ S₁, (Step5.visibility richStar Fstar L) ^ 2) +
        (∑ L ∈ S₂, (Step5.visibility richStar Fstar L) ^ 2) := by
    rw [← Finset.sum_union hpart, hunion]
  -- Step 3: on S₁, I² ≤ 2·I·(I-1).
  have hS₁ : ∑ L ∈ S₁, (Step5.visibility richStar Fstar L) ^ 2 ≤
      2 * ∑ L ∈ S₁, Step5.visibility richStar Fstar L *
        (Step5.visibility richStar Fstar L - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro L hL
    rw [Finset.mem_filter] at hL
    exact two_mul_mul_pred_ge_sq_of_two_le _ hL.2
  -- Step 4: on S₂, I² ≤ 1 (since I ≤ 1).
  have hS₂ : ∑ L ∈ S₂, (Step5.visibility richStar Fstar L) ^ 2 ≤ S₂.card := by
    calc ∑ L ∈ S₂, (Step5.visibility richStar Fstar L) ^ 2
        ≤ ∑ _ ∈ S₂, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro L hL
          rw [Finset.mem_filter] at hL
          have : Step5.visibility richStar Fstar L ≤ 1 := hL.2
          nlinarith [Nat.zero_le (Step5.visibility richStar Fstar L)]
      _ = S₂.card := by rw [Finset.sum_const]; ring
  -- Step 5: enlarge S₁'s edge-mass sum to LP.
  have hS₁_le_edge :
      ∑ L ∈ S₁, Step5.visibility richStar Fstar L *
        (Step5.visibility richStar Fstar L - 1) ≤
      edgeMass richStar Fstar LP := by
    unfold edgeMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intros; exact Nat.zero_le _
  -- Step 6: chain bounds.
  have hbound :
      ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 2 ≤
        2 * edgeMass richStar Fstar LP + LP.card := by
    calc ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 2
        = (∑ L ∈ S₁, (Step5.visibility richStar Fstar L) ^ 2) +
            (∑ L ∈ S₂, (Step5.visibility richStar Fstar L) ^ 2) := hsplit
      _ ≤ 2 * (∑ L ∈ S₁, Step5.visibility richStar Fstar L *
              (Step5.visibility richStar Fstar L - 1)) + S₂.card := by
          exact Nat.add_le_add hS₁ hS₂
      _ ≤ 2 * edgeMass richStar Fstar LP + LP.card := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left _ hS₁_le_edge
          · exact Finset.card_le_card (Finset.filter_subset _ _)
  exact h2.trans hbound

/-- **Edge fraction in active triples — cleared-denominator bound**
(`lem:triple-visibility` part (c), `step7.tex:1451-1455`).

Combining `failure_weight_le_two_card` (`failureWeight ≤ 2·|LP|`)
with `edge_mass_lower_bound_via_second_moment`
(`2·edgeMass ≥ (c² - 1)·|LP|`) yields

  `(c² - 1) · failureWeight ≤ 4 · edgeMass`.

Interpreted as a fraction: failure fraction `≤ 4 / (c² - 1)`,
which is `O(1/c²) → 0` as the richness constant `c → ∞`.

The hypothesis `1 ≤ c² · |LP|` (i.e. `c · |LP| ≥ 1`) is the
non-vacuity condition; in the paper's regime it follows from
`c ≥ 1` and `|LP| ≥ 1`, both of which hold for any non-trivial
poset with positive richness. -/
theorem edge_fraction_in_triples_failure_bound
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card) :
    (c ^ 2 - 1) * failureWeight richStar Fstar LP ≤
      4 * edgeMass richStar Fstar LP := by
  -- (c² - 1) · |LP| ≤ 2 · edgeMass            [from edge_mass_lower_bound]
  -- failureWeight ≤ 2 · |LP|                  [from failure_weight_le_two_card]
  -- Multiply: (c² - 1) · failureWeight ≤ (c² - 1) · 2 · |LP| ≤ 2 · 2 · edgeMass
  --        = 4 · edgeMass.
  have hEdge := edge_mass_lower_bound_via_second_moment richStar Fstar LP c
    hsub hfirst
  -- hEdge : c² · |LP| ≤ 2 · edgeMass + |LP|, equivalently (c² - 1) · |LP| ≤ 2 · edgeMass
  -- (when c² ≥ 1, with ℕ truncated subtraction).
  have hFail : failureWeight richStar Fstar LP ≤ 2 * LP.card :=
    failure_weight_le_two_card richStar Fstar LP
  -- Key intermediate: (c² - 1) · |LP| ≤ 2 · edgeMass.
  have hSub : (c ^ 2 - 1) * LP.card ≤ 2 * edgeMass richStar Fstar LP := by
    rcases Nat.lt_or_ge (c ^ 2) 1 with hlt | hge
    · -- c² = 0, so (c²-1) = 0 in ℕ.
      have : c ^ 2 = 0 := by omega
      simp [this]
    · -- c² ≥ 1; use Nat.sub_mul + Nat.sub_add_cancel.
      have hexp : (c ^ 2 - 1) * LP.card + LP.card = c ^ 2 * LP.card := by
        rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel]
        exact Nat.le_mul_of_pos_left _ (by omega)
      omega
  -- Chain:
  calc (c ^ 2 - 1) * failureWeight richStar Fstar LP
      ≤ (c ^ 2 - 1) * (2 * LP.card) := Nat.mul_le_mul_left _ hFail
    _ = 2 * ((c ^ 2 - 1) * LP.card) := by ring
    _ ≤ 2 * (2 * edgeMass richStar Fstar LP) := Nat.mul_le_mul_left _ hSub
    _ = 4 * edgeMass richStar Fstar LP := by ring

end EdgeFraction

/-! ### §4 — Grounded `lem:triple-visibility` (paper-faithful packaging)

This section packages parts (a), (b), (c) into a single statement
matching the paper's `lem:triple-visibility` signature
(`step7.tex:1376-1406`).  The grounded form takes the Step 5
first-moment Richness lower bound as the sole nontrivial input
(plus the trivial subset-of-`LP` hypothesis).

Downstream (`lem:cocycle`, `step7.tex:391`) consumes the
triple-overlap mass lower bound `(a)+(b)` via the abstract
`TripleData.weight` field; the edge-fraction-in-triples bound `(c)`
feeds the `(1 - o(1))`-fraction premise on active triples. -/

section Grounded

variable {Pair LinExt : Type*} [DecidableEq Pair] [DecidableEq LinExt]

/-- **`lem:triple-visibility` — grounded form** (`step7.tex:1376-1406`).

Bundled three-part output `(a)+(b)+(c)` of the active-triple
visibility lemma, packaged for downstream consumption by
`lem:cocycle` and `lem:sign-consistency`'s OutsideMass discharge.

Input: a Step 5 Richness first-moment lower bound `c · |LP| ≤ ∑_α
|F*_α|` and the universal containment `F*_α ⊆ LP`.

Output: three cleared-denominator bounds covering parts (a), (b),
(c) of `lem:triple-visibility`.  The output is a conjunction so
callers can destructure to use only the parts they need (the
triple-overlap mass bound is consumed by `lem:cocycle`; the
edge-fraction bound is consumed at the active-pair level). -/
theorem triple_visibility_grounded
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card) :
    -- (a) Third moment:
    c ^ 3 * LP.card ≤
        ∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3 ∧
    -- (b) Triple-overlap mass identity:
    (∑ αβγ ∈ richStar ×ˢ richStar ×ˢ richStar,
        tripleOverlapMass Fstar αβγ.1 αβγ.2.1 αβγ.2.2) =
      (∑ L ∈ LP, (Step5.visibility richStar Fstar L) ^ 3) ∧
    -- (c) Edge fraction in triples (cleared-denominator):
    (c ^ 2 - 1) * failureWeight richStar Fstar LP ≤
      4 * edgeMass richStar Fstar LP := by
  refine ⟨?_, ?_, ?_⟩
  · exact third_moment_visibility richStar Fstar LP c hsub hfirst
  · exact triple_overlap_mass_sum_eq_visibility_cube richStar Fstar LP hsub
  · exact edge_fraction_in_triples_failure_bound richStar Fstar LP c hsub hfirst

end Grounded

end Step7
end OneThird
