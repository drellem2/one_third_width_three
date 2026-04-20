/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
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
# Step 5 — Third-chain product identity and second-moment visibility

Formalises the two identities of `step5.tex` §§"Useful counting identity"
and "What feeds Step 6":

* `prop:counting` (`step5.tex:1065`) — the third-chain product identity:
  `∑_{(a,b) ∈ A × B} t(a,b) = ∑_c d_A(c) · d_B(c)`, where
  `t(a,b) := |{c ∈ C : a ∥ c ∧ b ∥ c}|` is the triple-overlap count and
  `d_A(c) := |{a ∈ A : a ∥ c}|`, `d_B(c)` are the chain-side degrees.
  The proof is pure double-counting of triples `(a, b, c)` with the
  pair-incomparability predicates `R_AC, R_BC`.

* `cor:second-moment` (`step5.tex:1110`) — the second-moment visibility
  bound: from a first-moment Richness lower bound
  `∑_α |F*_α| ≥ c · |LP|`, Cauchy–Schwarz yields
  `∑_L I(L)² ≥ c² · |LP|`, where
  `I(L) := |{α ∈ Rich : L ∈ F*_α}|`.

The second-moment statement is the "strengthening of (R)" consumed by
Step 6. The paper's rescaling `c₅(T) = (c₅⋆/4)²` (`step5.tex:1160`)
falls out by taking `c = c₅⋆/2` in the input and reading off
`c² = (c₅⋆/2)² = (c₅⋆)²/4`; the stronger `(c₅⋆/4)²` form of the paper
reflects a further factor of `1/2` from the bad-fiber subtraction.
The abstract bound here takes `c` as a caller-supplied constant and
delivers the cleanest `c² · |LP| ≤ ∑ I²` statement.
-/

namespace OneThird
namespace Step5

open Finset
open scoped BigOperators

/-! ### `prop:counting` (`step5.tex:1065`) -/

section Counting

variable {α β γ : Type*}

/-- **Third-chain triple-overlap count** (`step5.tex:1072`).
`t(a,b) := |{c ∈ C : R_AC a c ∧ R_BC b c}|` measures the number of
elements of the reference chain `C` that are incomparable to both
`a` and `b` (paper: `|IC(a) ∩ IC(b)|`). -/
def tripleCount (C : Finset γ)
    (R_AC : α → γ → Prop) [∀ a c, Decidable (R_AC a c)]
    (R_BC : β → γ → Prop) [∀ b c, Decidable (R_BC b c)]
    (a : α) (b : β) : ℕ :=
  (C.filter (fun c => R_AC a c ∧ R_BC b c)).card

/-- **Chain-A degree** (`step5.tex:1068`).
`d_A(c) := |{a ∈ A : R_AC a c}|`. -/
def degA (A : Finset α)
    (R_AC : α → γ → Prop) [∀ a c, Decidable (R_AC a c)]
    (c : γ) : ℕ :=
  (A.filter (fun a => R_AC a c)).card

/-- **Chain-B degree** (`step5.tex:1068`).
`d_B(c) := |{b ∈ B : R_BC b c}|`. -/
def degB (B : Finset β)
    (R_BC : β → γ → Prop) [∀ b c, Decidable (R_BC b c)]
    (c : γ) : ℕ :=
  (B.filter (fun b => R_BC b c)).card

/-- **`prop:counting` (third-chain product identity, `step5.tex:1065`).**

For a fixed triple `(A, B, C)` of index sets and pairwise
incomparability predicates `R_AC : α → γ → Prop`,
`R_BC : β → γ → Prop`:

  `∑_{(a,b) ∈ A × B} t(a,b) = ∑_{c ∈ C} d_A(c) · d_B(c)`,

where `t`, `d_A`, `d_B` are the triple-overlap count and chain-side
degrees defined above.

Proof (`step5.tex:1077-1081`): both sides count the cardinality of

  `{(a, b, c) ∈ A × B × C : R_AC a c ∧ R_BC b c}`

(the LHS grouping by `(a, b)`, the RHS grouping by `c`). -/
theorem third_chain_product_identity
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (R_AC : α → γ → Prop) [∀ a c, Decidable (R_AC a c)]
    (R_BC : β → γ → Prop) [∀ b c, Decidable (R_BC b c)] :
    ∑ ab ∈ A ×ˢ B, tripleCount C R_AC R_BC ab.1 ab.2 =
      ∑ c ∈ C, degA A R_AC c * degB B R_BC c := by
  classical
  -- Let S = (A ×ˢ B) ×ˢ C, with the triple predicate.
  -- Both sides equal |S.filter predicate|.
  -- LHS: regroup by (a,b); RHS: regroup by c using card_product.
  have key : ∀ c ∈ C,
      degA A R_AC c * degB B R_BC c
        = ((A ×ˢ B).filter (fun ab => R_AC ab.1 c ∧ R_BC ab.2 c)).card := by
    intro c _
    unfold degA degB
    rw [← Finset.card_product]
    congr 1
    ext ⟨a, b⟩
    simp [Finset.mem_filter, Finset.mem_product, and_assoc, and_left_comm]
  rw [Finset.sum_congr rfl key]
  -- Now both sides count triples (a,b,c) in different groupings.
  -- LHS: ∑_{(a,b)} |{c ∈ C : P ab c}|
  -- RHS: ∑_c |{(a,b) ∈ A×B : P ab c}|
  -- Swap via Finset.sum_comm on indicators.
  unfold tripleCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

end Counting

/-! ### `cor:second-moment` (`step5.tex:1110`) -/

section SecondMoment

variable {Pair LinExt : Type*}

/-- **Visibility count** `I(L)` (`step5.tex:1107`).
`I(L) := |{α ∈ Rich : L ∈ F*_α}|` counts, for a fixed linear extension
`L`, the number of rich pairs whose good fiber contains `L`. -/
def visibility (richPairs : Finset Pair) (Fstar : Pair → Finset LinExt)
    [∀ L α, Decidable (L ∈ Fstar α)]
    (L : LinExt) : ℕ :=
  (richPairs.filter (fun α => L ∈ Fstar α)).card

/-- **Fubini/double-counting for visibility** (`step5.tex:1145-1146`).

Under the assumption that each good fiber `F*_α` lies inside the
universe `LP` of linear extensions,

  `∑_{L ∈ LP} I(L) = ∑_{α ∈ Rich} |F*_α|`.

This is the first-moment identity that converts the paper's "fiber
mass" lower bound into a lower bound on the mean visibility. -/
theorem visibility_sum_eq_fiber_mass
    [DecidableEq LinExt]
    (richPairs : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt)
    (hsub : ∀ α ∈ richPairs, Fstar α ⊆ LP) :
    ∑ L ∈ LP, visibility richPairs Fstar L =
      ∑ α ∈ richPairs, (Fstar α).card := by
  classical
  unfold visibility
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  -- ∑_{L ∈ LP} [L ∈ Fstar α] = |Fstar α|
  -- Since Fstar α ⊆ LP, the inclusion gives us the count.
  have hsubα : Fstar α ⊆ LP := hsub α hα
  calc (∑ L ∈ LP, if L ∈ Fstar α then (1 : ℕ) else 0)
      = (LP.filter (fun L => L ∈ Fstar α)).card := by
        rw [Finset.card_filter]
    _ = (Fstar α).card := by
        congr 1
        apply Finset.Subset.antisymm
        · intro L hL
          rw [Finset.mem_filter] at hL
          exact hL.2
        · intro L hL
          rw [Finset.mem_filter]
          exact ⟨hsubα hL, hL⟩

/-- **`cor:second-moment` (second-moment visibility bound,
`step5.tex:1110`).**

From a first-moment Richness lower bound

  `c · |LP| ≤ ∑_{α ∈ Rich} |F*_α|`

together with the containment `F*_α ⊆ LP` for every rich pair,
Cauchy–Schwarz yields

  `c² · |LP| ≤ ∑_{L ∈ LP} I(L)²`.

Proof (`step5.tex:1150-1155`): by `visibility_sum_eq_fiber_mass`,
`∑ I = ∑ |F*|`, so `c · |LP| ≤ ∑ I`. Squaring and applying
`sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz on the uniform measure
on `LP`) gives `(c · |LP|)² ≤ (∑ I)² ≤ |LP| · ∑ I²`, and the `|LP|`
factor cancels.

The cleared-denominator form `c² · |LP| ≤ ∑ I²` is exact in ℕ; no
positivity hypothesis on `|LP|` is needed because if `|LP| = 0` the
first-moment hypothesis gives `c · 0 = 0 ≤ ∑ I = 0`, and both sides
of the conclusion are 0. -/
theorem second_moment_visibility
    [DecidableEq LinExt]
    (richPairs : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richPairs, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richPairs, (Fstar α).card) :
    c ^ 2 * LP.card ≤ ∑ L ∈ LP, (visibility richPairs Fstar L) ^ 2 := by
  classical
  -- Step 1: ∑ I(L) ≥ c * |LP|.
  have hfirstI : c * LP.card ≤ ∑ L ∈ LP, visibility richPairs Fstar L := by
    rw [visibility_sum_eq_fiber_mass richPairs Fstar LP hsub]
    exact hfirst
  -- Step 2: Cauchy–Schwarz on LP.
  have hCS : (∑ L ∈ LP, visibility richPairs Fstar L) ^ 2 ≤
      LP.card * ∑ L ∈ LP, (visibility richPairs Fstar L) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- Step 3: square the first-moment bound.
  have hsq : (c * LP.card) ^ 2 ≤
      (∑ L ∈ LP, visibility richPairs Fstar L) ^ 2 :=
    Nat.pow_le_pow_left hfirstI 2
  -- Step 4: chain.
  have hcombo : c ^ 2 * LP.card ^ 2 ≤
      LP.card * ∑ L ∈ LP, (visibility richPairs Fstar L) ^ 2 := by
    calc c ^ 2 * LP.card ^ 2
        = (c * LP.card) ^ 2 := by ring
      _ ≤ (∑ L ∈ LP, visibility richPairs Fstar L) ^ 2 := hsq
      _ ≤ LP.card * ∑ L ∈ LP, (visibility richPairs Fstar L) ^ 2 := hCS
  -- Step 5: cancel |LP|.
  rcases Nat.eq_zero_or_pos LP.card with hzero | hpos
  · rw [hzero]; simp
  · have hrw : c ^ 2 * LP.card ^ 2 = LP.card * (c ^ 2 * LP.card) := by ring
    rw [hrw] at hcombo
    exact Nat.le_of_mul_le_mul_left hcombo hpos

end SecondMoment

end Step5
end OneThird
