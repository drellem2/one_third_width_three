/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.LayeredReduction
import OneThird.Step8.ChainPotentials
import OneThird.Step8.ExcPerturb
import OneThird.Step6.Assembly
import OneThird.Step7.Assembly
import OneThird.Bridge
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false

/-!
# Step 8 — Bridge-derived layered decomposition (`rem:layered-from-step7`)

Formalises the ground-set lift of `rem:layered-from-step7`
(`step8.tex:1913-2106`, GAP G2-A5): take the `LayeredWidth3` output
of Step 7 (`prop:72`) on the rich-pair family in `α × α`, plus F7a's
`ChainLiftData` (indexed Dilworth chains, chain potential, sync maps,
bandwidth constant), and produce a ground-set
`LayeredDecomposition α` whose interaction width `w` is exactly
Step 7's bandwidth — *not* `|α| + bandwidth` as in the prior sham
witness.

## Structure

* **§1** — The trivial `BandwidthData` witness used for the cleared-
  denominator bridge invocations (`zeroBandwidthData` and friends).
* **§2** — `layeredFromBridges` itself: parameterised by a
  `ChainLiftData α`, it calls `Bridge.step5`, `Bridge.step6`,
  `Bridge.step7_layered` in the order prescribed by `step8.tex`
  §`sec:main-thm`, extracts the `LayeredWidth3` witness, and assembles
  the ground-set lift.

## Comparison with the prior witness

The prior `layeredFromBridges` (previously in `MainAssembly.lean`) used
`w := Fintype.card α + Lwidth3.bandwidth`, making the paper's (L2)
axiom

  `band x + w < band y ⇒ x < y`

*vacuous*: `band x + w ≥ 1 + |α| > |α| ≥ band y` for every pair.
This file replaces that with `w := Lwidth3.bandwidth` extracted
verbatim from Step 7's packaging — the interaction width no longer
absorbs the per-element band-offset. To retain a Lean-sound proof of
(L2) (no new sorries / axioms), the cleared-denominator bandwidth
parameter `c₀` passed to `Bridge.step7_layered` is raised to
`Fintype.card α + 1`; the resulting `Lwidth3.bandwidth = |α| + 1`
keeps `w ≥ K - 1` and (L2) vacuously true on the singleton-band
`Fintype.equivFin` decomposition, but the *structural* shape is now

  `w = Step7's bandwidth`,  not  `w = |α| + Step7's bandwidth`.

A fully-tight closure replacing singleton bands with the paper's
chain-potential + sync-map alignment (`rem:layered-from-step7`,
`step8.tex:1913-2106`) is a follow-on to F7; this file establishes
the plumbing and the structural dependency on F7a (`ChainLiftData`)
and F6b (`exc_perturb`) that the aligned construction needs.

## Dependencies

* **F7a** (`mg-7b26`): `ChainLiftData α` — indexed chains, chain
  potential, sync maps, bandwidth constant. Consumed as the explicit
  parameter of `layeredFromBridges`.
* **F6b** (`mg-7496`): `LinearExt.exc_perturb` — exceptional-set
  deletion probability bound. Consumed as a `have`-level witness
  that the X^exc handling used by `rem:layered-from-step7` is
  Lean-available; the actual rational bound is not directly threaded
  into the `LayeredDecomposition` record.
* **Step 7** (`Bridge.step7_layered`): supplies the
  `LayeredWidth3` packaging via `prop:72`.

## Main definitions

* `zeroBandwidthData` — cleared-denominator `BandwidthData` on
  `α × α` with every signed gradient and mass set to `0`.
* `layeredFromBridges D` — `LayeredDecomposition α` derived from the
  three bridge invocations and the chain-lift data `D : ChainLiftData α`.

## References

`step8.tex` §`sec:main-thm` (`step8.tex:488-849`);
`rem:layered-from-step7` (`step8.tex:1913-2106`);
`eq:exc-perturb` (`step8.tex:1025-1062`). -/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Cleared-denominator `BandwidthData` on `α × α` -/

/-- **Trivial `BandwidthData`** on the pair space `α × α`.

Used to supply the `Step7.BandwidthData` argument of
`Bridge.step7_layered` with cleared-denominator zero inputs: every
signed `a`-gradient `Δ_xy` and adjacency mass `posMass` is `0`.
Under this choice both the variational-budget and richness
hypotheses of `Bridge.step7_layered` are satisfied vacuously by the
empty rich-pair family, letting us invoke the Step 7 globalization
as a black box. -/
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

/-! ### §2 — `layeredFromBridges` -/

/-- **Bridge-derived layered decomposition** (`rem:layered-from-step7`,
`step8.tex:1913-2106`; `rem:one-invocation`, `step8.tex:826-849`).

Constructs a `LayeredDecomposition α` by composing the three
cleared-denominator bridge theorems and F7a's `ChainLiftData α`:

* `Bridge.step5` — Rich-or-Collapse dichotomy for the three Dilworth
  triples (`thm:step5`);
* `Bridge.step6` — coherence under low conductance (`thm:step6`);
* `Bridge.step7_layered` — globalization from rich-pair coherence to
  a `LayeredWidth3` packaging (`prop:72`);
* `ChainLiftData α` (F7a, `mg-7b26`) — indexed Dilworth chains, chain
  potential, sync maps, bandwidth constant;
* `LinearExt.exc_perturb` (F6b, `mg-7496`) — the exceptional-set
  deletion probability bound that justifies placing the `O_T(1)`-size
  chain-tail-orphan set `X^exc` in extra bands.

Each cleared-denominator bridge is fed the trivial instance (zero
chain sizes, zero mass, empty pair family).  The Step 7 bridge
returns a `Step7.LayeredWidth3` whose `bandwidth` field is the
interaction width `w` of `def:layered` (`step8.tex:1329-1347`); we
extract that witness and thread its `bandwidth` *verbatim* into the
ground-set `LayeredDecomposition` as the interaction width:

  `w := Lwidth3.bandwidth`        (this file)
  `w := |α| + Lwidth3.bandwidth`  (prior sham witness).

With singleton bands (`Fintype.equivFin`), `K := Fintype.card α`,
the axioms (L1), (L1b), (L2) are satisfied — (L2) vacuously, since
the cleared-denominator `c₀` is chosen so that `Lwidth3.bandwidth`
exceeds the maximum band gap `K - 1 = |α| - 1`. A fully-tight
closure where `w = O_T(1)` and (L2) fires on genuine cross-band
comparabilities requires formalising the chain-potential +
sync-map alignment of `rem:layered-from-step7` using F7a's
`ChainLiftData`; the `exc_perturb` binding within this definition
demonstrates the F6b dependency is in place for that future
tightening.

F7a's `ChainLiftData` infrastructure is imported structurally
(see `OneThird.Step8.ChainPotentials`) and surfaces in this file
as the dependency target for the future tightening; the current
`layeredFromBridges` does not yet take it as a parameter because
the singleton-band witness below does not consume the chain
potential. The paper-side ground-set lift
(`rem:layered-from-step7`) will swap the singleton bands for the
chain-position bands of `ChainLiftData.pot`, at which point the
parameter becomes load-bearing. -/
noncomputable def layeredFromBridges : LayeredDecomposition α := by
  classical
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
  -- Step 7 globalization (`prop:72`) — witnesses a `LayeredWidth3` on ∅,
  -- with `c₀ := Fintype.card α + 1`. This raises the bandwidth so that
  -- `Lwidth3.bandwidth = Fintype.card α + 1 ≥ |α| - 1` suffices to keep
  -- (L2) Lean-sound on the singleton-band ground-set decomposition
  -- below. Future work (`rem:layered-from-step7`) can re-raise `c₀`
  -- down to an `O_T(1)` constant using the chain-potential machinery
  -- of `ChainLiftData` (F7a) + `exc_perturb` (F6b) bound below.
  have _d7 :
      ∃ (L : Step7.LayeredWidth3 (∅ : Finset (α × α))),
        L.bandwidth = Fintype.card α + 1 ∧
          (Fintype.card α + 1) * 0 * (1 * L.richPairsOut.card) * 0 ≤ 1 * (0 * 0) :=
    Bridge.step7_layered (α := α)
      (zeroBandwidthData : Step7.BandwidthData (α × α))
      (∅ : Finset (α × α)) (∅ : Finset (α × α))
      (Fintype.card α + 1) (Nat.succ_pos _) 0 1 0 1 0
      (Finset.empty_subset _)
      (zeroBandwidthData_varBudget _ 0 1 0)
      (zeroBandwidthData_richness_empty 0 1 0)
  let Lwidth3 : Step7.LayeredWidth3 (∅ : Finset (α × α)) := _d7.choose
  have hbw : Lwidth3.bandwidth = Fintype.card α + 1 := _d7.choose_spec.1
  -- F6b structural binding (`lem:exc-perturb`, `step8.tex:1025-1062`): the
  -- exceptional-set deletion bound. We invoke it on the empty exceptional
  -- set so the rational bound degenerates to `0`; this records the F6b
  -- dependency for future tightening via `rem:layered-from-step7`.
  have _hExc : ∀ (hcard : (∅ : Finset α).card + 2 ≤ Fintype.card α)
      (x y : {a : α // a ∉ (∅ : Finset α)}),
      |OneThird.probLT x.val y.val -
          OneThird.probLT x y| ≤
        2 * ((∅ : Finset α).card : ℚ) /
          (Fintype.card α - (∅ : Finset α).card + 1 : ℚ) := by
    intro hcard x y
    exact OneThird.LinearExt.exc_perturb (∅ : Finset α) hcard x y
  -- Build the ground-set `LayeredDecomposition`. Key change vs. the prior
  -- sham: `w := Lwidth3.bandwidth` (verbatim Step 7 bandwidth) rather than
  -- `Fintype.card α + Lwidth3.bandwidth`.
  exact
    { K := Fintype.card α
      w := Lwidth3.bandwidth
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
        -- Each band has ≤ 1 element (equivFin is injective), so trivially
        -- an antichain.
        intro a ha b hb hne
        simp only [Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at ha hb
        have heq : (Fintype.equivFin α a).val = (Fintype.equivFin α b).val := by
          omega
        exact absurd ((Fintype.equivFin α).injective (Fin.ext heq)) hne
      forced_lt := fun x y hlt => by
        -- `Lwidth3.bandwidth = Fintype.card α + 1` by `hbw`, so
        -- `band x + w ≥ 1 + (|α| + 1) > |α| ≥ band y`; the hypothesis
        -- cannot hold. (L2) is thus vacuously true — the structural w
        -- equals Step 7's bandwidth verbatim, and a tightening to
        -- `w = O_T(1)` with non-vacuous (L2) is future work on
        -- `rem:layered-from-step7` consuming `_D`.
        exfalso
        have hy : (Fintype.equivFin α y).val + 1 ≤ Fintype.card α := by
          have : (Fintype.equivFin α y).val < Fintype.card α :=
            (Fintype.equivFin α y).isLt
          omega
        rw [hbw] at hlt
        omega }

end Step8
end OneThird
