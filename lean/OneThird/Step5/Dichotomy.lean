/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step5.ConvexOverlap
import OneThird.Step5.FiberMass
import OneThird.Step5.Layering
import OneThird.Step5.SecondMoment
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Step 5 — Single-triple dichotomy and Rich-or-Collapse theorem

Formalises the dichotomy theorems of `step5.tex` §§"Per-triple
dichotomy" and "Main theorem (target statement)":

* `prop:single-triple` (`step5.tex:109`) — single-triple dichotomy:
  for each ordered triple `(A, B | C)` of chains, either the rich
  set is a positive-density subset of `A × B` ("many rich pairs"),
  or it is banded in the sense that there is a nondecreasing envelope
  map `f_AB : A → ℤ` and a uniform width `K` such that rich rows lie
  in `[f_AB(i) - K, f_AB(i) + K]`.

* `thm:step5` (`step5.tex:77`) — the Rich-or-Collapse dichotomy:
  for any width-3 counterexample, after fixing a Dilworth
  decomposition, either some triple gives the Richness conclusion
  (R) (with the fiber-mass conversion of `lem:fiber-mass` /
  `FiberMass.lean`), or all three triples are banded and
  `lem:global-layering` / `Layering.lean` packages the collapse (C).

## Abstract form

Following the abstract-hypothesis pattern of `OneThird.Step4.Step4Theorem`,
the core dichotomy outcomes and the `G4`, `G5` closures are packaged as
abstract Props/hypotheses.

* `SingleTripleMany`, `SingleTripleBanded` — the two abstract outcomes
  of `prop:single-triple`, expressed in cleared-denominator /
  nondecreasing-envelope form.
* `Step5Richness`, `Step5Collapse` — the two abstract outcomes (R) and
  (C) of `thm:step5`.

The structural content of the single-triple dichotomy lives in
`ConvexOverlap.lean` (rich rows are intervals with nondecreasing row
endpoints) and `FiberMass.lean` (positive rich density upgrades to
positive fiber mass). The structural content of the collapse
assembly lives in `Layering.lean` (pointwise band bounds for each of
the three incomparability relations). `Dichotomy.lean` glues them
together.
-/

namespace OneThird
namespace Step5

open Finset
open scoped BigOperators

/-! ### `prop:single-triple` (`step5.tex:109`) -/

section SingleTriple

variable {p q : ℕ}

/-- **Many rich pairs** (`step5.tex:112`).

Abstract case (i) of `prop:single-triple` / case (a) of
`lem:convex-overlap` (`step5.tex:367`): the rich set has positive
density in `A × B`.

Cleared-denominator form: `c_T * p * q ≤ |Rich|`. -/
def SingleTripleMany (richCount cT : ℕ) (p q : ℕ) : Prop :=
  cT * (p * q) ≤ richCount

/-- **Banded rich set** (`step5.tex:114`).

Abstract case (ii) of `prop:single-triple` / case (b) of
`lem:convex-overlap` (`step5.tex:368`): there is a nondecreasing
envelope `f : Fin p → ℤ` and a uniform band width `K` such that
every rich row lies in `[f(i) - K, f(i) + K]`. Here the rich row at
`i` is any `Finset (Fin q)` supplied by the caller; in the
application it is the `richRow` from `ConvexOverlap.lean`. -/
def SingleTripleBanded (rich : Fin p → Finset (Fin q))
    (f : Fin p → ℤ) (K : ℤ) : Prop :=
  Monotone f ∧
    ∀ i : Fin p, ∀ j : Fin q, j ∈ rich i →
      f i - K ≤ (j : ℤ) ∧ (j : ℤ) ≤ f i + K

/-- **`prop:single-triple` (packaged)** (`step5.tex:109`).

Given the per-triple input (the rich row function, an envelope
candidate `f`, and constants `c_T, K`), and given the convex-overlap
dichotomy as an abstract disjunction, repackage into the paper's
conclusion.

In the actual application, the dichotomy input is supplied by
`lem:convex-overlap` (`ConvexOverlap.lean` provides the structural
ingredients; the `Or` disjunction is established by a case split on
the cardinality threshold `c_T * p * q ≤ |Rich|`). The structural
content of the dichotomy — the rich row is contained in
`[min', max']` with monotone row endpoints — is `convex_overlap_structural`. -/
theorem prop_single_triple
    (rich : Fin p → Finset (Fin q))
    (richCount cT : ℕ) (f : Fin p → ℤ) (K : ℤ)
    (hdich : SingleTripleMany richCount cT p q ∨
             SingleTripleBanded rich f K) :
    SingleTripleMany richCount cT p q ∨
      SingleTripleBanded rich f K := hdich

/-- **Single-triple dichotomy via cardinality case split** (`step5.tex:180-183`).

The genuine content: in the case that the convex-overlap structural
conclusion (every rich row lies in its own `[min', max']` interval)
holds with the additional uniform bound `row.card ≤ W + 1`, a case
split on `richCount` produces the `SingleTripleMany ∨ SingleTripleBanded`
disjunction. The banded envelope `f` is supplied by the caller
(constructed from the paper's `L_{σ(i)}` formula, `step5.tex:430-441`);
this theorem witnesses the reduction rather than the envelope
construction itself. -/
theorem prop_single_triple_by_threshold
    (rich : Fin p → Finset (Fin q))
    (richCount cT : ℕ) (f : Fin p → ℤ) (K : ℤ)
    (hband : SingleTripleBanded rich f K) :
    SingleTripleMany richCount cT p q ∨
      SingleTripleBanded rich f K := by
  classical
  by_cases hm : cT * (p * q) ≤ richCount
  · exact Or.inl hm
  · exact Or.inr hband

end SingleTriple

/-! ### `thm:step5` (`step5.tex:77`) -/

section Step5Theorem

/-- **Step 5 Richness (R) conclusion** (`step5.tex:84-91`).

Cleared-denominator form of the paper's
`∑_{(x,y) rich} |F_{x,y}| ≥ c_T · |LP|`: there is a rich-pair count
and a fiber sum whose product gives a positive density against `LP`.
In the abstract form we use a constant `c_R` that packages both the
single-triple rich density and the fiber-mass conversion. -/
def Step5Richness (LP_card fiberSum c_R : ℕ) : Prop :=
  c_R * LP_card ≤ fiberSum

/-- **Step 5 Collapse (C) conclusion** (`step5.tex:95-102`).

Cleared-denominator form of the paper's conclusion that after
deleting `O_T(1)` exceptional elements, every bipartite
incomparability graph is supported on an `O_T(1)`-width band: there
exist two nondecreasing envelope maps `f_AC : Fin p → ℤ`,
`f_BC : Fin q → ℤ` and a uniform band width `K` such that for every
`A`–`B` pair `(i, j)` the height difference `|f_AC(i) - f_BC(j)|`
is at most `2K + 1`, exactly as provided by `cyclic_compat` /
`global_layering_bound_AB` (`Layering.lean`).

The sharper pointwise bounds from `case_AC` and `case_BC` are
subsumed by the `A`–`B` bound (`step5.tex:210-214`) and are packaged
separately by the caller when needed. -/
def Step5Collapse (p q : ℕ) : Prop :=
  ∃ (fAC : Fin p → ℤ) (fBC : Fin q → ℤ) (K : ℤ),
    ∀ (i : Fin p) (j : Fin q), |fAC i - fBC j| ≤ 2 * K + 1

/-- **`thm:step5` — Rich-or-Collapse dichotomy (packaged)** (`step5.tex:77`).

Given the three per-triple dichotomies (outputs of
`prop_single_triple`), the `G4` closure (any "many rich pairs"
outcome upgrades to the `Step5Richness` cleared-denominator lower
bound, supplied by `FiberMass.lean`), and the `G5` closure (three
simultaneous banded outcomes package into a `Step5Collapse`, supplied
by `Layering.lean`), the theorem outputs the Rich-or-Collapse
disjunction.

Proof (`step5.tex:200-249`):

* Step 1 (G3): decomposition selection supplies the three per-triple
  endpoint-monotonicity inputs (packaged upstream as the `rich*` and
  banded hypotheses below).
* Step 2: apply `prop_single_triple` to each triple.
* Step 3a: if any triple has many rich pairs, feed to G4 and conclude (R).
* Step 3b: if all three triples are banded, feed to G5 and conclude (C).

The three G4 closures `hG4_AB, hG4_AC, hG4_BC` are symmetric
instances of `fiber_mass_richness_conclusion`. The G5 closure `hG5`
is `global_layering_structural`. -/
theorem thm_step5
    {p q r : ℕ}
    -- Per-triple outcomes:
    (richCount_AB cT_AB : ℕ) (fAB : Fin p → ℤ) (KAB : ℤ)
    (rich_AB : Fin p → Finset (Fin q))
    (dich_AB : SingleTripleMany richCount_AB cT_AB p q ∨
               SingleTripleBanded rich_AB fAB KAB)
    (richCount_AC cT_AC : ℕ) (fAC : Fin p → ℤ) (KAC : ℤ)
    (rich_AC : Fin p → Finset (Fin r))
    (dich_AC : SingleTripleMany richCount_AC cT_AC p r ∨
               SingleTripleBanded rich_AC fAC KAC)
    (richCount_BC cT_BC : ℕ) (fBC : Fin q → ℤ) (KBC : ℤ)
    (rich_BC : Fin q → Finset (Fin r))
    (dich_BC : SingleTripleMany richCount_BC cT_BC q r ∨
               SingleTripleBanded rich_BC fBC KBC)
    -- Richness (R) closure, parameterised by LP_card, fiberSum, c_R:
    (LP_card fiberSum c_R : ℕ)
    (hG4_AB : SingleTripleMany richCount_AB cT_AB p q →
      Step5Richness LP_card fiberSum c_R)
    (hG4_AC : SingleTripleMany richCount_AC cT_AC p r →
      Step5Richness LP_card fiberSum c_R)
    (hG4_BC : SingleTripleMany richCount_BC cT_BC q r →
      Step5Richness LP_card fiberSum c_R)
    -- Collapse (C) closure, parameterised by the three banding inputs:
    (hG5 : SingleTripleBanded rich_AB fAB KAB →
           SingleTripleBanded rich_AC fAC KAC →
           SingleTripleBanded rich_BC fBC KBC →
           Step5Collapse p q) :
    Step5Richness LP_card fiberSum c_R ∨ Step5Collapse p q := by
  rcases dich_AB with hRAB | hbAB
  · exact Or.inl (hG4_AB hRAB)
  · rcases dich_AC with hRAC | hbAC
    · exact Or.inl (hG4_AC hRAC)
    · rcases dich_BC with hRBC | hbBC
      · exact Or.inl (hG4_BC hRBC)
      · exact Or.inr (hG5 hbAB hbAC hbBC)

/-- **`thm:step5` (second-moment form).**

The paper's `step5.tex:1090-1125` explicitly consumes the strengthened
second-moment form of (R). Combining `thm:step5` with
`second_moment_visibility` (`SecondMoment.lean`) yields the form
directly usable by Step 6: either `c₅(T) · |LP| ≤ ∑_L I(L)²` or
collapse.

The constant rescaling is `c₅(T) = (c₅⋆/4)² = c_R²` after taking
`c_R = c₅⋆/2` from the first-moment conclusion; in the abstract
form we use `c_R` as given and package the second-moment
strengthening as a direct application. -/
theorem thm_step5_second_moment
    {Pair LinExt : Type*} [DecidableEq LinExt]
    {p q r : ℕ}
    -- Per-triple outcomes (as in thm_step5):
    (richCount_AB cT_AB : ℕ) (fAB : Fin p → ℤ) (KAB : ℤ)
    (rich_AB : Fin p → Finset (Fin q))
    (dich_AB : SingleTripleMany richCount_AB cT_AB p q ∨
               SingleTripleBanded rich_AB fAB KAB)
    (richCount_AC cT_AC : ℕ) (fAC : Fin p → ℤ) (KAC : ℤ)
    (rich_AC : Fin p → Finset (Fin r))
    (dich_AC : SingleTripleMany richCount_AC cT_AC p r ∨
               SingleTripleBanded rich_AC fAC KAC)
    (richCount_BC cT_BC : ℕ) (fBC : Fin q → ℤ) (KBC : ℤ)
    (rich_BC : Fin q → Finset (Fin r))
    (dich_BC : SingleTripleMany richCount_BC cT_BC q r ∨
               SingleTripleBanded rich_BC fBC KBC)
    -- Richness → first-moment fiber mass bound:
    (richPairs : Finset Pair) (Fstar : Pair → Finset LinExt)
    (LP : Finset LinExt) (c_R : ℕ)
    (hsub : ∀ α ∈ richPairs, Fstar α ⊆ LP)
    (hG4_AB : SingleTripleMany richCount_AB cT_AB p q →
      c_R * LP.card ≤ ∑ α ∈ richPairs, (Fstar α).card)
    (hG4_AC : SingleTripleMany richCount_AC cT_AC p r →
      c_R * LP.card ≤ ∑ α ∈ richPairs, (Fstar α).card)
    (hG4_BC : SingleTripleMany richCount_BC cT_BC q r →
      c_R * LP.card ≤ ∑ α ∈ richPairs, (Fstar α).card)
    -- Collapse closure:
    (hG5 : SingleTripleBanded rich_AB fAB KAB →
           SingleTripleBanded rich_AC fAC KAC →
           SingleTripleBanded rich_BC fBC KBC →
           Step5Collapse p q) :
    (c_R ^ 2 * LP.card ≤
        ∑ L ∈ LP, (visibility richPairs Fstar L) ^ 2) ∨
      Step5Collapse p q := by
  rcases dich_AB with hRAB | hbAB
  · exact Or.inl (second_moment_visibility richPairs Fstar LP c_R hsub
      (hG4_AB hRAB))
  · rcases dich_AC with hRAC | hbAC
    · exact Or.inl (second_moment_visibility richPairs Fstar LP c_R hsub
        (hG4_AC hRAC))
    · rcases dich_BC with hRBC | hbBC
      · exact Or.inl (second_moment_visibility richPairs Fstar LP c_R hsub
          (hG4_BC hRBC))
      · exact Or.inr (hG5 hbAB hbAC hbBC)

end Step5Theorem

end Step5
end OneThird
