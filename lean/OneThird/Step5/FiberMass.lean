/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 5 — Chain-decomposition selection and fiber-mass conversion

Formalises §§5 G3–G4 of `step5.tex`.

* `lem:decomp-selection` (`step5.tex:421`) — the bookkeeping statement
  that the three per-triple endpoint-monotonicity conclusions hold
  simultaneously. Under the exact-monotone form of
  `lem:endpoint-mono` (additive error `0`, zero discards;
  cf. `EndpointMono.lean`), the proof is trivial — the same monotone
  sequences witness monotonicity for each of the triples
  `(A,B | C)`, `(A,C | B)`, `(B,C | A)` with empty exception set
  (`step5.tex:431-444` makes exactly this remark).

* `lem:fiber-mass` (`step5.tex:539`) — abstract pairs-to-fibers mass
  transfer. The per-pair bulk bound supplied by Step 1
  (`step5.tex:593-594`, the "up to `O(t)`-thin bad fibers" form)
  is taken as a hypothesis `∀ α ∈ richPairs, 2 · fiberSize α ≥ LP`.
  The averaged conclusion
  `∑_{α ∈ Rich} fiberSize α ≥ (Rich.card · LP) / 2` and the
  "in particular" richness conclusion
  `|Rich| ≥ c · |A| · |B| ⇒ ∑ fiberSize ≥ (c / 2) · LP` are then
  pure arithmetic.
-/

namespace OneThird
namespace Step5

open Finset
open scoped BigOperators

/-! ### G3: `lem:decomp-selection` (`step5.tex:421`) -/

section DecompSelection

/-- **Bounded-error monotonicity record.** A convenience bundle for
the four weakly-increasing endpoint sequences attached to a single
ordered triple `(X, Y | Z)`. Under the exact-monotone form of
`lem:endpoint-mono` each of these is genuinely `Monotone`, so the
record reduces to a four-fold conjunction. -/
structure TripleMono {p q : ℕ}
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ) : Prop where
  alpha_mono : Monotone alpha
  beta_mono  : Monotone beta
  gamma_mono : Monotone gamma
  delta_mono : Monotone delta

/-- **`lem:decomp-selection`, packaged** (`step5.tex:421`).

Under the exact-monotone form of `lem:endpoint-mono` proved in
`EndpointMono.lean`, the three ordered-triple monotonicity conclusions
hold simultaneously under the trivial partition with empty exception
set. No chain refinement is needed (`step5.tex:431-444`: *"the trivial
partition works and `E := ∅` suffices for all three ordered triples
simultaneously."*). -/
theorem decomp_selection {p q r : ℕ}
    {alphaAB betaAB : Fin p → ℤ} {gammaAB deltaAB : Fin q → ℤ}
    {alphaAC betaAC : Fin p → ℤ} {gammaAC deltaAC : Fin r → ℤ}
    {alphaBC betaBC : Fin q → ℤ} {gammaBC deltaBC : Fin r → ℤ}
    (hAB : TripleMono alphaAB betaAB gammaAB deltaAB)
    (hAC : TripleMono alphaAC betaAC gammaAC deltaAC)
    (hBC : TripleMono alphaBC betaBC gammaBC deltaBC) :
    TripleMono alphaAB betaAB gammaAB deltaAB ∧
    TripleMono alphaAC betaAC gammaAC deltaAC ∧
    TripleMono alphaBC betaBC gammaBC deltaBC :=
  ⟨hAB, hAC, hBC⟩

/-- **Exception-set union is bounded by the sum** (`step5.tex:507-508`).

Even in the over-built form of the paper's G3 proof — where each
triple carries a per-triple exception set `E_{AB}, E_{AC}, E_{BC}` of
size at most `c₁(T)` — the union satisfies `|E| ≤ 3 · c₁(T)`. Under
the proved G1 with `c₁(T) = 0`, this is `|E| ≤ 0`, recovering
`E = ∅`. -/
theorem exception_union_card_le
    {α : Type*} [DecidableEq α]
    (E_AB E_AC E_BC : Finset α) (c₁ : ℕ)
    (hAB : E_AB.card ≤ c₁) (hAC : E_AC.card ≤ c₁) (hBC : E_BC.card ≤ c₁) :
    (E_AB ∪ E_AC ∪ E_BC).card ≤ 3 * c₁ := by
  have h1 : (E_AB ∪ E_AC ∪ E_BC).card ≤
      E_AB.card + E_AC.card + E_BC.card := by
    calc (E_AB ∪ E_AC ∪ E_BC).card
        ≤ (E_AB ∪ E_AC).card + E_BC.card :=
          Finset.card_union_le _ _
      _ ≤ (E_AB.card + E_AC.card) + E_BC.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  linarith

end DecompSelection

/-! ### G4: `lem:fiber-mass` (`step5.tex:539`) -/

section FiberMass

variable {Pair : Type*}

/-- **Per-pair bulk lower bound, summed** (`step5.tex:604-611`, Step 2
of the paper proof).

Given the per-pair Step-1 bulk bound `2 · fiberSize α ≥ LP` for every
rich pair `α` (`step5.tex:593-594`, the "up to `O(t)`-thin bad
fibers" form), summing over `Rich` gives
`∑_{α ∈ Rich} 2 · fiberSize α ≥ Rich.card · LP`.

This is the averaged bound in Step 2 of `step5.tex`. The sharper
"in particular" clause is `fiber_mass_richness_conclusion` below. -/
theorem fiber_mass_sum_lower_bound
    (richPairs : Finset Pair) (fiberSize : Pair → ℕ) (LP : ℕ)
    (hper : ∀ α ∈ richPairs, 2 * fiberSize α ≥ LP) :
    2 * ∑ α ∈ richPairs, fiberSize α ≥ richPairs.card * LP := by
  have hsum : ∑ α ∈ richPairs, 2 * fiberSize α ≥
      ∑ _α ∈ richPairs, LP :=
    Finset.sum_le_sum hper
  have hconst : ∑ _α ∈ richPairs, LP = richPairs.card * LP :=
    Finset.sum_const_nat (fun _ _ => rfl)
  have hmul : ∑ α ∈ richPairs, 2 * fiberSize α =
      2 * ∑ α ∈ richPairs, fiberSize α := by
    simp [Finset.mul_sum]
  linarith

/-- **`lem:fiber-mass` richness conclusion** (`step5.tex:615-628`,
Step 3 of the paper proof).

If the rich set is a positive-density subset of `A × B`
(`|Rich| ≥ rho * sigma` with `sigma := |A| · |B|`), then the total
fiber mass is a positive-density subset of `LP`
(`∑ fiberSize ≥ (rho / 2) · LP`). In cleared-denominator form:

`2 · sigma · ∑ fiberSize ≥ rho · sigma · LP` becomes
`2 · ∑ fiberSize ≥ rho · LP` after cancelling `sigma` (note the
paper uses `|A|·|B| ≥ 1`, `step5.tex:611`, which we express as the
side hypothesis `sigma ≥ 1`). -/
theorem fiber_mass_richness_conclusion
    (richPairs : Finset Pair) (fiberSize : Pair → ℕ) (LP : ℕ)
    (hper : ∀ α ∈ richPairs, 2 * fiberSize α ≥ LP)
    (rho sigma : ℕ) (hsigma : 1 ≤ sigma)
    (hrich : rho * sigma ≤ richPairs.card) :
    2 * sigma * ∑ α ∈ richPairs, fiberSize α ≥ rho * sigma * LP := by
  have h1 : 2 * ∑ α ∈ richPairs, fiberSize α ≥ richPairs.card * LP :=
    fiber_mass_sum_lower_bound richPairs fiberSize LP hper
  have h2 : richPairs.card * LP ≥ rho * sigma * LP :=
    Nat.mul_le_mul_right LP hrich
  have key : 2 * sigma * ∑ α ∈ richPairs, fiberSize α ≥
      sigma * (rho * sigma * LP) := by
    have step1 : sigma * (2 * ∑ α ∈ richPairs, fiberSize α) ≥
        sigma * (rho * sigma * LP) := by
      have h12 : 2 * ∑ α ∈ richPairs, fiberSize α ≥ rho * sigma * LP := by
        linarith
      exact Nat.mul_le_mul_left sigma h12
    have heq : 2 * sigma * ∑ α ∈ richPairs, fiberSize α =
        sigma * (2 * ∑ α ∈ richPairs, fiberSize α) := by ring
    linarith
  have h4 : sigma * (rho * sigma * LP) ≥ rho * sigma * LP := by
    have : sigma * (rho * sigma * LP) = rho * sigma * (sigma * LP) := by ring
    rw [this]
    have : sigma * LP ≥ LP := Nat.le_mul_of_pos_left LP hsigma
    exact Nat.mul_le_mul_left _ this
  linarith

/-- **Averaged form of `lem:fiber-mass`** (`step5.tex:541-545`).

The paper states the averaged bound
`∑ fiberSize ≥ c_T · |Rich| · LP / (|A| · |B|)`. In cleared-denominator
form: the per-pair bulk bound `2 · fiberSize ≥ LP` and the trivial
observation `|A|·|B| ≥ 1` (`step5.tex:611`) yield

`2 · sigma · ∑_{α ∈ Rich} fiberSize α ≥ |Rich| · LP`.

This is the paper's averaged form with `c_T = 1/2`. -/
theorem fiber_mass_averaged
    (richPairs : Finset Pair) (fiberSize : Pair → ℕ) (LP : ℕ)
    (hper : ∀ α ∈ richPairs, 2 * fiberSize α ≥ LP)
    (sigma : ℕ) (hsigma : 1 ≤ sigma) :
    2 * sigma * ∑ α ∈ richPairs, fiberSize α ≥ richPairs.card * LP := by
  have h1 : 2 * ∑ α ∈ richPairs, fiberSize α ≥ richPairs.card * LP :=
    fiber_mass_sum_lower_bound richPairs fiberSize LP hper
  have h2 : sigma * (2 * ∑ α ∈ richPairs, fiberSize α) ≥
      sigma * (richPairs.card * LP) := Nat.mul_le_mul_left sigma h1
  have h3 : sigma * (richPairs.card * LP) ≥ 1 * (richPairs.card * LP) :=
    Nat.mul_le_mul_right _ hsigma
  have heq : 2 * sigma * ∑ α ∈ richPairs, fiberSize α =
      sigma * (2 * ∑ α ∈ richPairs, fiberSize α) := by ring
  linarith

end FiberMass

end Step5
end OneThird
