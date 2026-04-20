/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Step 2 — Fiber boundary averaging

This file formalises the second half of Step 2 (`step2.tex`
§"From global conductance to per-fiber boundary"): a pure
double-counting argument that translates a *global* conductance bound
`|∂S| ≤ κ|S|` into a *per-fiber* average boundary bound on the fibers
of a rich-pair cover.

The key lemma (`lem:fiber-avg`) and its tail bound (`cor:fiber-avg-tail`)
are essentially abstract:

> Let `B` be a finite set of "edges" and `R` a finite collection of
> "fibers". For each fiber `r ∈ R` and edge `e ∈ B`, say `e` is
> **internal to** `r` via a decidable predicate `internal r e`.
> Assume the bounded-multiplicity hypothesis
> `∀ e ∈ B, #{r ∈ R : internal r e} ≤ K`.
> Then `∑_{r ∈ R} #{e ∈ B : internal r e} ≤ K · |B|`.

The Step 2 application instantiates `B := ∂_BK S` (the BK-boundary of
`S`) and `R` as the rich-good-fiber family with `internal` being
Definition `def:edge-internal`. The `κ|S|` factor appears by bounding
`|B| ≤ κ|S|`.

## Main results

* `double_counting_bounded_multiplicity` --- `lem:fiber-avg` in
  abstract form.
* `fiber_avg_tail_count` --- `cor:fiber-avg-tail` in abstract form:
  the number of fibers whose internal count exceeds `η · w r` (where
  `w r` is the per-fiber mass) is controlled by `K · |B| / η`
  (Markov-type inequality).
-/

namespace OneThird
namespace Step2
namespace FiberAvg

open Finset

section DoubleCounting

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (R : Finset α) (B : Finset β) (internal : α → β → Prop)
variable [DecidableRel internal]

/-- The "bounded-multiplicity" hypothesis: every edge is internal to at
most `K` fibers. -/
def BoundedMultiplicity (K : ℕ) : Prop :=
  ∀ e ∈ B, (R.filter (fun r => internal r e)).card ≤ K

/-- The per-fiber count of "internal" boundary edges. -/
def internalCount (r : α) : ℕ := (B.filter (fun e => internal r e)).card

/-- **`lem:fiber-avg` (abstract form).** Double counting: under the
bounded-multiplicity hypothesis, the total count of (fiber, internal
edge) pairs is at most `K · |B|`. -/
theorem double_counting_bounded_multiplicity {K : ℕ}
    (hK : BoundedMultiplicity R B internal K) :
    ∑ r ∈ R, internalCount B internal r ≤ K * B.card := by
  -- Rewrite each side as the cardinality of a Finset of pairs.
  classical
  unfold internalCount
  -- Σ_r #{e : internal r e} = Σ_e #{r : internal r e}  (double counting / Fubini)
  have hfubini : ∑ r ∈ R, (B.filter (fun e => internal r e)).card
      = ∑ e ∈ B, (R.filter (fun r => internal r e)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hfubini]
  -- Now bound by K * |B|.
  calc ∑ e ∈ B, (R.filter (fun r => internal r e)).card
      ≤ ∑ _e ∈ B, K := by
        gcongr with e he
        exact hK e he
    _ = K * B.card := by
        simp [Finset.sum_const, mul_comm]

/-- **`cor:fiber-avg-tail` (abstract form).** For any positive real
threshold, the number of fibers whose `internalCount` exceeds
`η · w r` (for a weight `w`) is controlled by a Markov-type
inequality.

We state it in the clean form: the sum of `w r` over the "heavy"
fibers is bounded by `(K · |B|) / η`.

We use natural-number arithmetic with `η : ℕ` playing the role of a
rational multiplier `η ∈ ℕ_{>0}`; the real-valued formulation of
`step2.tex` follows by choosing `η` large enough to clear
denominators. -/
theorem fiber_avg_tail_weight {K η : ℕ} (hη : 0 < η)
    (w : α → ℕ) (hK : BoundedMultiplicity R B internal K)
    (heavy : Finset α) (hheavy_sub : heavy ⊆ R)
    (hheavy_cond : ∀ r ∈ heavy, η * w r ≤ internalCount B internal r) :
    η * (∑ r ∈ heavy, w r) ≤ K * B.card := by
  classical
  -- η · Σ_{heavy} w r ≤ Σ_{heavy} internalCount r ≤ Σ_R internalCount r ≤ K · |B|.
  have h1 : η * (∑ r ∈ heavy, w r) ≤ ∑ r ∈ heavy, internalCount B internal r := by
    rw [Finset.mul_sum heavy w η]
    gcongr with r hr
    exact hheavy_cond r hr
  have h2 : ∑ r ∈ heavy, internalCount B internal r
      ≤ ∑ r ∈ R, internalCount B internal r :=
    Finset.sum_le_sum_of_subset_of_nonneg hheavy_sub
      (fun _ _ _ => Nat.zero_le _)
  exact h1.trans (h2.trans (double_counting_bounded_multiplicity R B internal hK))

/-- Simpler counting corollary: the number of heavy fibers, each
contributing weight `≥ 1`, is bounded by `K · |B| / η`.
Phrased integrally: `η · #heavy ≤ K · |B|` when each heavy fiber has
an internal count `≥ η`. -/
theorem fiber_avg_tail_count {K η : ℕ}
    (hK : BoundedMultiplicity R B internal K)
    (heavy : Finset α) (hheavy_sub : heavy ⊆ R)
    (hheavy_cond : ∀ r ∈ heavy, η ≤ internalCount B internal r) :
    η * heavy.card ≤ K * B.card := by
  classical
  have h1 : η * heavy.card ≤ ∑ r ∈ heavy, internalCount B internal r := by
    calc η * heavy.card
        = ∑ _r ∈ heavy, η := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ r ∈ heavy, internalCount B internal r := by
          gcongr with r hr
          exact hheavy_cond r hr
  have h2 : ∑ r ∈ heavy, internalCount B internal r
      ≤ ∑ r ∈ R, internalCount B internal r :=
    Finset.sum_le_sum_of_subset_of_nonneg hheavy_sub
      (fun _ _ _ => Nat.zero_le _)
  exact h1.trans (h2.trans (double_counting_bounded_multiplicity R B internal hK))

end DoubleCounting

end FiberAvg
end Step2
end OneThird
