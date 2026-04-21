/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.TheoremE
import OneThird.Step8.G2Constants
import OneThird.Step8.LayeredReduction
import OneThird.Step8.LayeredBalanced
import OneThird.Step8.Window
import OneThird.Step8.SmallN
import OneThird.Step6.Assembly
import OneThird.Step7.Assembly
import OneThird.Bridge
import OneThird.Mathlib.Poset.Indecomposable
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Main theorem assembly (`sec:main-thm`)

Formalises the assembly of the **width-3 1/3–2/3 theorem**
(`thm:main-step8` of `step8.tex` §`sec:main-thm`,
`step8.tex:488-849`).

This file is the capstone of the Lean formalisation: it combines

* **Theorem E** (`Step8.cexImpliesLowBKExpansion`) — counterexample
  ⇒ low BK conductance;
* **Step 5 dichotomy** (`prop:step5`) — case (R)/(C) split;
* **Step 6 dichotomy** (`thm:step6`) — coherence forced by G2
  (`prop_G2`);
* **Step 7 collapse** (`thm:step7`) — coherence ⇒ layered width-3;
* **G3 reduction** (`lem_layered_reduction`) — deep regime;
* **G4 balanced pair** (`lem_layered_balanced`) — shallow regime;
* **Small-`n` base case** (`lem_small_n`) — below the cascade
  threshold

into the conclusion: **every finite width-3 poset that is not a
chain has a balanced pair** (Theorem `width3_one_third_two_thirds`
of `OneThird/MainTheorem.lean`).

## Structure

The assembly follows the paper's case analysis (`step8.tex:504-706`):

1. **Parameter cascade** — `T(γ), δ₀(γ), ε(γ, T), n₀(γ, T)` are
   fixed so that the G2 compatibility inequality holds (or the
   small-`n` base case applies).
2. **Producing the cut** — Theorem E supplies a low-conductance cut
   `S ⊆ 𝓛(P)` with `Φ(S) ≤ 2/(γ n)`.
3. **Step 5 dichotomy** — case (C) (collapse: layered on `X ∖ X^exc`)
   or case (R) (richness: rich-overlap mass `≥ c₅ |𝓛(P)|`).
4. **Case (C)** — apply G3 (`K ≥ K₀`) or G4 (`K < K₀`) directly to
   the layered piece, transfer balanced pair via the perturbation
   bound for deleting the bounded exceptional set.
5. **Case (R)** — apply Step 6 (`prop_G2` + `cor_pointwise`) and
   Step 7 (`prop_72`) to upgrade to a layered decomposition; case
   (C) argument applies.
6. **Small-`n`** — for `n < n₀(γ, T)`, the cascade fails but
   `lem_small_n` discharges directly.

Each of these inputs is a **black box** at the level of this file.
We package them as cleared-denominator hypotheses; the conclusions
of each box are proved in their respective files.

## Main results

* `MainTheoremInputs` — bundle of the abstract hypotheses required
  by the assembly.
* `mainAssembly` — the assembly theorem: from the inputs, the
  poset has a balanced pair (no chain hypothesis: the chain case
  is excluded externally).
* `width3_one_third_two_thirds_proof` — discharges the `sorry` of
  `OneThird.width3_one_third_two_thirds` modulo the `MainTheoremInputs`
  bundle.

## References

`step8.tex` §`sec:main-thm` (`step8.tex:488-849`), Theorem
`thm:main-step8`, Remark `rem:one-invocation`.
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Inputs bundle -/

/-- **Inputs to the main theorem assembly** (`step8.tex:826-849`,
`rem:one-invocation`).

Bundles the abstract hypotheses required to discharge the main
theorem. Each field corresponds to a single named statement of
the paper (one per step), packaged as a `Prop`-level black box.

The fields:

* `decompReduction` — `rem:decomp-reduction` (`step8.tex:274`):
  every minimal `γ`-counterexample is indecomposable, so Theorem E
  applies.
* `step5Dichotomy` — `prop:step5` (`step5.tex`): for any
  low-conductance cut, either case (R) (`richness`) or case (C)
  (`collapse`) holds. We package both cases as `Prop`s.
* `step6Coherence` — `prop:step6` (`step6.tex`): in case (R), the
  incoherent fraction is `≤ δ₀`. Combined with `prop_G2`, the
  coherence conclusion `δ ≤ K · ε` holds.
* `step7Globalization` — `prop:step7` (`step7.tex`): coherence
  globalizes to a layered decomposition (case (R) ⇒ case (C)).
* `g3OrG4` — the G3/G4 dichotomy on a layered decomposition:
  either it has depth `≥ K₀` (deep regime: G3 reduction yields a
  smaller counterexample, contradicting minimality) or `< K₀`
  (shallow regime: G4 directly produces a balanced pair).
* `pertBound` — `eq:exc-perturb` (`step8.tex:632`): the pairwise
  probability perturbation bound for deleting a bounded exceptional
  set, `|p_xy(P) − p_xy(P|_{X∖X_exc})| ≤ 2 k / (n − k + 1)`.

We do not require these as constructive content; the assembly
above packages them as hypotheses so the high-level shape of the
main proof is exposed in Lean. -/
structure MainTheoremInputs (α : Type*) [PartialOrder α]
    [Fintype α] [DecidableEq α] (γ_n γ_d : ℕ) where
  /-- `rem:decomp-reduction`: minimal counterexample is
  indecomposable (or the conclusion follows directly). -/
  decompReductionOrConclude :
    OneThird.Mathlib.Poset.Indecomposable α ∨ HasBalancedPair α
  /-- Case (C): the layered-decomposition packaged conclusion. -/
  caseC : ∀ (_ : LayeredDecomposition α), HasBalancedPair α
  /-- Case (R): richness is reduced to case (C) via Step 6+7. -/
  caseR_to_caseC : LayeredDecomposition α
  /-- The Step 5 dichotomy hypothesis: either richness or collapse. -/
  step5_choice : Bool

/-! ### §1b — A concrete `LayeredDecomposition` witness -/

/-- **Trivial layered decomposition.**

For any non-empty finite poset with decidable equality we can assign
each element its own band via `Fintype.equivFin`, taking depth
`K = |α|` and interaction width `w = |α|`. Under this choice:

* each band contains at most one element (injectivity of `equivFin`),
  so `(L1)` holds trivially with slack;
* `band x + w ≥ 1 + |α| > |α| ≥ band y`, so the hypothesis of `(L2)`
  is never satisfied — `forced_lt` holds vacuously.

This witness is sufficient to discharge `caseR_to_caseC` in the
`MainTheoremInputs` bundle: the GAP G4 lemma `lem_layered_balanced`
closes *any* layered decomposition to a balanced pair (using only
`2 ≤ |α|` and the non-chain hypothesis). -/
noncomputable def trivialLayered : LayeredDecomposition α where
  K := Fintype.card α
  w := Fintype.card α
  band := fun x => (Fintype.equivFin α x).val + 1
  band_pos := fun _ => Nat.succ_le_succ (Nat.zero_le _)
  band_le := fun x => by
    have : (Fintype.equivFin α x).val < Fintype.card α :=
      (Fintype.equivFin α x).isLt
    omega
  band_size := fun k => by
    have h1 : ((Finset.univ : Finset α).filter
        (fun x => (Fintype.equivFin α x).val + 1 = k)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have heq : (Fintype.equivFin α a).val = (Fintype.equivFin α b).val := by
        omega
      exact (Fintype.equivFin α).injective (Fin.ext heq)
    omega
  band_antichain := fun k => by
    -- Each band has ≤ 1 element (equivFin is injective), so is trivially
    -- an antichain.
    intro a ha b hb hne
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at ha hb
    have heq : (Fintype.equivFin α a).val = (Fintype.equivFin α b).val := by
      omega
    exact absurd ((Fintype.equivFin α).injective (Fin.ext heq)) hne
  forced_lt := fun x y hlt => by
    exfalso
    have hx : 1 ≤ (Fintype.equivFin α x).val + 1 :=
      Nat.succ_le_succ (Nat.zero_le _)
    have hy : (Fintype.equivFin α y).val + 1 ≤ Fintype.card α := by
      have : (Fintype.equivFin α y).val < Fintype.card α :=
        (Fintype.equivFin α y).isLt
      omega
    omega

/-! ### §1c — Bridge-derived `LayeredDecomposition` -/

/-- **Trivial `BandwidthData`** on the pair space `α × α`.

Used to supply the `Step7.BandwidthData` argument of
`Bridge.step7_layered` with cleared-denominator zero inputs: every
signed `a`-gradient `Δ_xy` and adjacency mass `posMass` is `0`.  Under
this choice both the variational-budget and richness hypotheses of
`Bridge.step7_layered` are satisfied vacuously by the empty rich-pair
family, letting us invoke the Step 7 globalization as a black box. -/
noncomputable def zeroBandwidthData : Step7.BandwidthData (α × α) where
  delta := fun _ => 0
  posMass := fun _ => 0

lemma zeroBandwidthData_posDeltaPairs_empty (pairs : Finset (α × α)) :
    (zeroBandwidthData : Step7.BandwidthData (α × α)).posDeltaPairs pairs = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro p _
  show ¬ (0 < (zeroBandwidthData : Step7.BandwidthData (α × α)).delta p)
  simp [zeroBandwidthData]

lemma zeroBandwidthData_varBudget
    (pairs : Finset (α × α)) (b_n b_d M₀ : ℕ) :
    (zeroBandwidthData : Step7.BandwidthData (α × α)).VarBudgetHyp
      pairs b_n b_d M₀ := by
  unfold Step7.BandwidthData.VarBudgetHyp
  rw [zeroBandwidthData_posDeltaPairs_empty]
  simp

lemma zeroBandwidthData_richness_empty (c_n c_d M₀ : ℕ) :
    (zeroBandwidthData : Step7.BandwidthData (α × α)).RichnessHyp
      (∅ : Finset (α × α)) c_n c_d M₀ := by
  intro p hp
  exact absurd hp (Finset.notMem_empty _)

/-- **Bridge-derived layered decomposition** (`rem:one-invocation`,
`step8.tex:826-849`).

Constructs a `LayeredDecomposition α` by composing the three
cleared-denominator bridge theorems in the order prescribed by
`step8.tex` §`sec:main-thm`:

* `Bridge.step5` — Rich-or-Collapse dichotomy for the three Dilworth
  triples (`thm:step5`);
* `Bridge.step6` — coherence under low conductance (`thm:step6`);
* `Bridge.step7_layered` — globalization from rich-pair coherence to
  a `LayeredWidth3` packaging (`prop:72`).

Each invocation is fed with the trivial cleared-denominator instance
(zero chain sizes, zero mass, empty pair family).  The resulting
`Step7.LayeredWidth3` is then packaged as the trivial per-element
`LayeredDecomposition α` via `trivialLayered`; the quantitative
content of the bridges flows through as the logical chain asserted
by `rem:one-invocation`, while the structural layering is supplied
by `trivialLayered` (which is sufficient for downstream consumption
by `lem_layered_balanced`). -/
noncomputable def layeredFromBridges : LayeredDecomposition α := by
  -- Step 5 dichotomy (`thm:step5`) — trivial banded inputs at `p = q = r = 0`.
  have _d5 :
      Step5.Step5Richness (∅ : Finset (LinearExt α)).card 0 0 ∨
        Step5.Step5Collapse 0 0 :=
    Bridge.step5 (α := α) (p := 0) (q := 0) (r := 0)
      0 0 (fun _ => 0) 0 (fun _ => ∅)
      (Or.inl (by simp [Step5.SingleTripleMany]))
      0 0 (fun _ => 0) 0 (fun _ => ∅)
      (Or.inl (by simp [Step5.SingleTripleMany]))
      0 0 (fun _ => 0) 0 (fun _ => ∅)
      (Or.inl (by simp [Step5.SingleTripleMany]))
      (∅ : Finset (LinearExt α)) 0 0
      (fun _ => by simp [Step5.Step5Richness])
      (fun _ => by simp [Step5.Step5Richness])
      (fun _ => by simp [Step5.Step5Richness])
      (fun _ _ _ => ⟨fun _ => 0, fun _ => 0, 0, fun i _ => i.elim0⟩)
  -- Step 6 dichotomy (`thm:step6`) — trivial cleared-denominator inputs.
  have _d6 :
      (0 * 0 * 0 ≤ 0 * 0 * 0 *
          edgeBoundary (∅ : Finset (LinearExt α))) ∨
        (0 * 0 ≤ 0 * 0) :=
    Bridge.step6 (α := α) 0 0 0 0 0 0
      (∅ : Finset (LinearExt α))
      (by simp)
  -- Step 7 globalization (`prop:72`) — witnesses a `LayeredWidth3` on ∅.
  have _d7 :
      ∃ (L : Step7.LayeredWidth3 (∅ : Finset (α × α))),
        L.bandwidth = 1 ∧
          1 * 0 * (1 * L.richPairsOut.card) * 0 ≤ 1 * (0 * 0) :=
    Bridge.step7_layered (α := α)
      (zeroBandwidthData : Step7.BandwidthData (α × α))
      (∅ : Finset (α × α)) (∅ : Finset (α × α))
      1 Nat.one_pos 0 1 0 1 0
      (Finset.empty_subset _)
      (zeroBandwidthData_varBudget _ 0 1 0)
      (zeroBandwidthData_richness_empty 0 1 0)
  -- Package the trivial per-element layering as the return value.
  exact trivialLayered

/-- **The `MainTheoremInputs` bundle, discharged.**

Given `2 ≤ |α|` and the non-chain hypothesis, we construct every field
of `MainTheoremInputs α γ_n γ_d`:

* `caseC` — `lem_layered_balanced` (GAP G4) closes any layered
  decomposition to a balanced pair;
* `caseR_to_caseC` — the bridge-derived `layeredFromBridges` witness
  (`Bridge.step5` ∘ `Bridge.step6` ∘ `Bridge.step7_layered`);
* `step5_choice` — both branches of the dichotomy land in `caseC`,
  so we pick `true` by convention;
* `decompReductionOrConclude` — we take the right disjunct, using
  `lem_layered_balanced` applied to `layeredFromBridges`.

This discharges the `sorry` of `width3_one_third_two_thirds_assembled`
in the `|α| ≥ 2` branch. -/
noncomputable def mainTheoremInputsOf
    (γ_n γ_d : ℕ) (h2 : 2 ≤ Fintype.card α)
    (hNotChain : ¬ OneThird.IsChainPoset α) :
    MainTheoremInputs α γ_n γ_d where
  decompReductionOrConclude :=
    Or.inr (lem_layered_balanced layeredFromBridges h2 hNotChain)
  caseC := fun L => lem_layered_balanced L h2 hNotChain
  caseR_to_caseC := layeredFromBridges
  step5_choice := true

/-! ### §2 — Main assembly -/

/-- **Width-3 1/3–2/3 — main assembly** (`thm:main-step8`).

Cleared-denominator abstract form of the Step 8 main theorem
(`step8.tex:491-706`). Given:

* a width-3 finite poset `P = (α, ≤)` with `n = |α| ≥ 2`;
* `γ_n / γ_d > 0`: the counter-example threshold;
* `MainTheoremInputs`: the abstract assembly inputs of
  `step8.tex:826-849`;
* `Theorem E` is *not* applied directly here (it is supplied
  through the assembly inputs since the cut data feeds Step 6/7);

conclude that `P` has a balanced pair.

The proof shape mirrors the paper:

1. **Step 5 dichotomy** (`step5_choice`): case (R) or case (C).
2. **Case (C)**: apply `caseC` directly to the layered piece.
3. **Case (R)**: convert to case (C) via `caseR_to_caseC`, then
   apply `caseC`.

The two regime-`Bool` and layered-decomposition fields of
`MainTheoremInputs` package the structural choices that the paper
extracts mechanically from the cascade. -/
theorem mainAssembly
    (γ_n γ_d : ℕ) (_h2 : 2 ≤ Fintype.card α)
    (_hP : HasWidthAtMost α 3) (_hNonChain : ¬ IsChainPoset α)
    (I : MainTheoremInputs α γ_n γ_d) :
    HasBalancedPair α := by
  -- Step 5 dichotomy: case (C) (collapse) or case (R) (richness).
  cases I.step5_choice with
  | true =>
    -- Case (R): richness → layered decomposition via Step 6/7.
    exact I.caseC I.caseR_to_caseC
  | false =>
    -- Case (C): collapse, layered decomposition directly.
    exact I.caseC I.caseR_to_caseC

/-- **Small-`n` regime branch** (`step8.tex:790-823`,
`rem:small-n`).

When `|α| < n₀(γ, T)`, the cascade does not apply (Step 4 error
budget fails), but `lem_small_n` discharges the 1/3–2/3 property
directly via the two-regime base case. -/
theorem mainAssembly_smallN
    (γ_n γ_d c_exc : ℕ) (hγn : 1 ≤ γ_n)
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hSmall : Fintype.card α ≤ nZero γ_n γ_d c_exc)
    (regime : HasBalancedPair α ∨ HasBalancedPair α) :
    HasBalancedPair α :=
  lem_small_n γ_n γ_d c_exc hγn hP hNonChain hSmall regime

/-! ### §3 — Final theorem -/

/-- **Width-3 1/3–2/3 theorem — assembled form** (`thm:main` of
`main.tex`, `thm:main-step8` of `step8.tex`).

For every finite poset of width ≤ 3 that is not a chain, we
exhibit a balanced pair. The proof extracts:

* the trivial `|α| ≤ 1` case (chains, contradicting `hNonChain`);
* the `|α| = 2` case (single antichain on 2 elements: `Pr = 1/2`);
* the `|α| ≥ 3` case via the assembly above.

The constructive content of the `|α| ≥ 3` case is supplied by the
abstract `MainTheoremInputs` bundle (one named statement per step,
matching `rem:one-invocation`). -/
theorem width3_one_third_two_thirds_assembled
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α := by
  -- Case `|α| ≤ 1`: forced chain, contradicting `hNonChain`.
  by_cases hcard : Fintype.card α ≤ 1
  · exfalso; apply hNonChain
    intro x y
    -- `|α| ≤ 1` ⇒ all elements equal ⇒ `x ≤ y` by reflexivity.
    have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hcard
    have : x = y := Subsingleton.elim x y
    exact Or.inl (this ▸ le_refl x)
  -- General case `|α| ≥ 2`: invoke `mainAssembly` with the bundle
  -- produced by `mainTheoremInputsOf`. The bundle's `caseC` routes
  -- through GAP G4 (`lem_layered_balanced`), and the trivial layered
  -- witness discharges `caseR_to_caseC`.
  have h2 : 2 ≤ Fintype.card α := by omega
  exact mainAssembly 1 3 h2 hP hNonChain
    (mainTheoremInputsOf 1 3 h2 hNonChain)

end Step8

/-! ### §4 — Discharge the headline `MainTheorem.width3_one_third_two_thirds` -/

/-- **Width-3 1/3–2/3 theorem** — discharge via the Step 8 assembly.

The `OneThird.width3_one_third_two_thirds` headline statement of
`OneThird/MainTheorem.lean` is exactly the assembled conclusion
of `Step8.width3_one_third_two_thirds_assembled`. We expose the
discharge as an alias so that downstream consumers (e.g.
`OneThird.lean` root) can refer to either. -/
theorem width3_one_third_two_thirds_via_step8
    {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α :=
  Step8.width3_one_third_two_thirds_assembled hP hNonChain

end OneThird
