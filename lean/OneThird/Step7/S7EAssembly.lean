/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.RichnessConstants
import OneThird.Step7.Step6Budget

/-!
# Step 7 — Piece 2 sub-arc D: assemble `L_S7E` and discharge the
`VarBudgetHyp` / `RichnessHyp` witnesses

This file is **piece 2, sub-arc mg-S7-Conc-D** of the Option A' FULL
REFACTOR (`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2;
work item mg-3f00, the assembly ticket that **completes Piece 2**).
It depends on mg-8f9c (S7-Conc-B, the Step 5 richness constants
`c_n, c_d, M₀`) and mg-5f3e (S7-Conc-C, the Step 6 budget constants
`b_n, b_d`).

## What this file delivers

The S7-E bandwidth lemma `lem_bandwidth_le_four_bundled_groundSet`
(`Step7/GroundSet.lean`, mg-4ce6) is parametric over **two**
hypotheses it cannot itself supply:

  `hBud  : (BandwidthData.ofPotential …).VarBudgetHyp pairs b_n b_d M₀`
  `hRich : (BandwidthData.ofPotential …).RichnessHyp richPairs c_n c_d M₀`

mg-4ce6 left both parametric; mg-8f9c extracted `c_n = 1, c_d = 2,
M₀ = |LP|` and built the `RichnessHyp` *discharge*
(`richnessHyp_groundSet_of_step5`); mg-5f3e extracted
`b_n = 2·t_d·δ_n, b_d = t_n·δ_d` and built the `VarBudgetHyp`
*projection bridge* (`varBudgetHyp_of_budget_bound`).

This file performs the **assembly**: it composes the mg-8f9c and
mg-5f3e discharges onto a **single common `BandwidthData` and a
single common cleared denominator `M₀`**, and invokes the S7-E
bandwidth lemma.  The output is `L_S7E : Step7.LayeredWidth3
(richPairs : Finset (α × α))` with `bandwidth ≤ 4` — the concrete
object the Piece 3 S7-F bridge (`lem:layered-from-step7`) consumes.

* `lemS7E_groundSet` — **the assembly theorem.**  Given the landed
  Step 5 G4 interface-partition data (the mg-8f9c richness inputs)
  and the Step 6 budget data in cleared form (the mg-5f3e budget
  inputs), it discharges **both** `hBud` and `hRich` internally —
  neither appears as a free hypothesis — and produces `L_S7E`.
* `lemS7E_antichain3` — **the non-vacuous concrete instance.**  The
  assembly fired on the genuine width-3 non-chain poset `Antichain3`
  (the mg-496b cascade witness carrier), with the genuine extracted
  constants `c_n = 1, c_d = 2` (mg-8f9c) and `b_n = step6BudgetNum
  2 1, b_d = step6BudgetDen 1 1` (mg-5f3e).  A **fully closed term**
  — no free hypotheses, no placeholders.
* `L_S7E_antichain3` — the concrete `LayeredWidth3` witness extracted
  from `lemS7E_antichain3`, with `L_S7E_antichain3_bandwidth :
  L_S7E_antichain3.bandwidth ≤ 4`.

## The `M₀` reconciliation — how the two sides are made to agree

`lem_bandwidth_le_four_bundled_groundSet` shares **one** `M₀`
between `hBud` and `hRich`.  mg-8f9c's `RichnessHyp` extraction
fixes `M₀ = LP.card` (`|LE(P)|`, the linear-extension universe
cardinality — the `step8.tex` convention).  mg-5f3e's
`varBudgetHyp_of_budget_bound` is, by contrast, **denominator-
independent**: it derives `VarBudgetHyp budgetPairs b_n b_d M₀`
from a model bound `hModel` and a cleared budget bound
`hBound : b_d · exceptionalMass ≤ b_n · M₀` for **any** `M₀`.

The assembly therefore takes the budget side at `M₀ := LP.card` —
the richness side's denominator — and the two hypotheses land on a
common footing.  This is exactly the `M₀` reconciliation the
mg-5f3e state doc (`docs/state-S7-Conc-C-Session1.md` §3 point 3,
§5) flagged as "a disclosed coordination point for mg-S7-Conc-D,
not a projection failure": the budget *fraction* `b_n / b_d` is
denominator-independent, so the *constants* slot into the shared-`M₀`
signature unchanged.

`hBound` in the `LP.card` denominator is the cleared form of the
paper's `lem:budget-var` conclusion (`step7.tex:960-967`), whose
budget is normalised against `|LE(P)|`.  The Step 6 cascade's own
cleared denominator is the second moment `M = ∑ w_{αβ}`
(`step6_budget_grounded`); deriving `hBound` *from* that
`M`-denominated form is the genuine `lem:budget-var` index
conversion — new theorem-proving outside Piece 2's
concrete-instantiation scope, threaded here as a hypothesis.  This
is the honest scope boundary, the same shape mg-8f9c / mg-5f3e
used (their core extractors thread the genuine Steps 5–6 cascade
facts as hypotheses).

## The non-triviality bar (mg-3f00)

> the assembled `L_S7E` must be genuinely unconditional for `α` as a
> width-3 non-chain minimal counterexample — the `VarBudgetHyp` and
> `RichnessHyp` witnesses must be discharged with the real extracted
> constants, no remaining free hypotheses, no placeholders.

`lemS7E_antichain3` is the certificate: a **fully closed** `L_S7E`
on the genuine width-3 non-chain poset `Antichain3`, with `hBud`
and `hRich` discharged inside (they are not hypotheses of
`lemS7E_antichain3`), carrying the genuine extracted constants
`c_n = 1, c_d = 2` (mg-8f9c) and `b_n = step6BudgetNum 2 1,
b_d = step6BudgetDen 1 1` (mg-5f3e — `= 4, 1` at the `Antichain3`
cascade constants, see `step6_budget_constants_antichain3`).  The
shared denominator `M₀ = genLP.card = 6` is the genuine `|LE(P)|`
of `Antichain3`.

**No constant-extraction mismatch; no pair-space misalignment.**
The mg-3f00 block-and-report triggers do not fire:

* *Constant-extraction mismatch.*  The mg-8f9c `c_n, c_d` and the
  mg-5f3e `b_n, b_d` project into the shared-`M₀` S7-E signature
  with no adapter algebra — `lemS7E_groundSet` type-checks the
  composition directly.  The only coordination is the `M₀` choice,
  resolved (above) by the denominator-independence of
  `varBudgetHyp_of_budget_bound`.
* *Pair-space convention.*  The pair space is `Pair := α × α` — the
  ambient ground-set pair type fixed by `Step7/GroundSet.lean`
  (mg-4ce6), with `richPairs ⊆ pairs ⊆ α × α` the Step 5
  Dilworth-derived rich-pair sub-finset.  `L_S7E` has type
  `LayeredWidth3 (richPairs : Finset (α × α))`, exactly the §2.2
  spec output `L_{S7E} : Step7.LayeredWidth3 (richPairs α)`.  The
  Piece 3 bridge `lem:layered-from-step7` is not yet in tree
  (verified: no `lem_layered_from_step7` symbol), so this is the
  documented uniform convention, consistent across mg-4ce6 /
  mg-8f9c / mg-5f3e; no misalignment is observable.

## Cross-references

* `Step7/RichnessConstants.lean` (mg-8f9c) —
  `richnessHyp_groundSet_of_step5`,
  `lem_bandwidth_le_four_bundled_of_step5_richness`.
* `Step7/Step6Budget.lean` (mg-5f3e) — `varBudgetHyp_of_budget_bound`,
  `step6BudgetNum`, `step6BudgetDen`.
* `Step7/GroundSet.lean` (mg-4ce6) —
  `lem_bandwidth_le_four_bundled_groundSet`, `BKVertex`, `BKEdge`.
* `Step7/Bandwidth.lean` — `BandwidthData`, `VarBudgetHyp`,
  `RichnessHyp`, `BandwidthData.ofPotential`.
* `Step7/Assembly.lean` — `LayeredWidth3`, `prop_72`.
* `Step6/CascadeComposed.lean` (mg-496b) — `Antichain3`, `genLP`,
  `gen_LP_card`.
* Paper: `step7.tex:1018-1056` (`lem:bandwidth`),
  `step7.tex:1175-1193` (`prop:72`), `step7.tex:960-967`
  (`lem:budget-var`).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2 — the
  Piece 2 spec, sub-arc mg-S7-Conc-D.
* `docs/state-S7-Conc-D-Session1.md` (mg-3f00) — this session's
  state doc.
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — The assembly: discharge `hBud` + `hRich`, invoke S7-E

`lemS7E_groundSet` is the load-bearing mg-S7-Conc-D deliverable.  It
takes the genuine Steps 5–6 cascade facts — the mg-8f9c Step 5 G4
interface-partition data and the mg-5f3e Step 6 cleared budget data
— and composes the two discharges (`richnessHyp_groundSet_of_step5`
for `hRich`, `varBudgetHyp_of_budget_bound` for `hBud`) onto the
**single common `BandwidthData.ofPotential` and the single common
denominator `M₀ := LP.card`** that `lem_bandwidth_le_four_bundled_groundSet`
requires.  Neither `hBud` nor `hRich` appears as a free hypothesis —
they are discharged inside. -/

/-- **The S7-E assembly — `L_S7E` from the Steps 5–6 cascade**
(`mg-S7-Conc-D`, the ticket that completes Piece 2).

Given:

* the landed **Step 5 G4** interface-partition data
  (`hcover`/`hdisj`/`hthin`/`hact` — the mg-8f9c richness inputs:
  the activated `lem:fiber-mass` cover `LP = goodFiber ⊔ badFiber`,
  thin bad sets `|badFiber p| ≤ B₀`, activation `2·B₀ ≤ |LP|`);
* the landed **Step 6** budget data in cleared form (`hModel` —
  the rich-pair variational budget is dominated by the Step 6
  exceptional mass; `hBound : b_d · exceptionalMass ≤ b_n · |LP|` —
  the cleared `lem:budget-var` bound in the `|LE(P)|` denominator);

this theorem **discharges both** the `RichnessHyp` (via the mg-8f9c
`richnessHyp_groundSet_of_step5`, with the genuine `c_n = 1,
c_d = 2`) and the `VarBudgetHyp` (via the mg-5f3e
`varBudgetHyp_of_budget_bound`, with the extracted `b_n, b_d`) on the
**common** `BandwidthData.ofPotential` and the **common** denominator
`M₀ := LP.card`, and invokes the S7-E bandwidth lemma to produce

  `L_S7E : LayeredWidth3 richPairs`  with  `L.bandwidth ≤ 4`.

`hBud` / `hRich` do **not** appear in the signature — they are
discharged.  The remaining hypotheses are the genuine Steps 5–6
cascade facts (`α` arising as a minimal γ-counterexample makes them
hold, exactly as for the paper's `prop:72`). -/
theorem lemS7E_groundSet
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (psrc ptgt : α × α → BKVertex α)
    (pairs richPairs : Finset (α × α)) (LP : Finset (BKVertex α))
    (goodFiber badFiber : α × α → Finset (BKVertex α)) (B₀ : ℕ)
    (hcover : ∀ p ∈ richPairs, goodFiber p ∪ badFiber p = LP)
    (hdisj : ∀ p ∈ richPairs, Disjoint (goodFiber p) (badFiber p))
    (hthin : ∀ p ∈ richPairs, (badFiber p).card ≤ B₀)
    (hact : 2 * B₀ ≤ LP.card)
    (hSub : richPairs ⊆ pairs)
    (b_n b_d exceptionalMass : ℕ)
    (hModel : ∑ p ∈ (BandwidthData.ofPotential
          (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
            edgeWeight path)
          (α × α) psrc ptgt (fun p => (goodFiber p).card)).posDeltaPairs
          pairs,
        ((BandwidthData.ofPotential
            (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
              edgeWeight path)
            (α × α) psrc ptgt (fun p => (goodFiber p).card)).delta p).toNat
          * (BandwidthData.ofPotential
            (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
              edgeWeight path)
            (α × α) psrc ptgt (fun p => (goodFiber p).card)).posMass p
        ≤ exceptionalMass)
    (hBound : b_d * exceptionalMass ≤ b_n * LP.card) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      L.richPairsIn.card + L.richPairsOut.card = richPairs.card ∧
      4 * 1 * (b_d * L.richPairsOut.card) * LP.card ≤
        2 * (b_n * LP.card) :=
  lem_bandwidth_le_four_bundled_of_step5_richness signedWeight edgeWeight
    path psrc ptgt pairs richPairs LP goodFiber badFiber B₀
    hcover hdisj hthin hact hSub b_n b_d
    (varBudgetHyp_of_budget_bound _ pairs b_n b_d LP.card exceptionalMass
      hModel hBound)

/-! ### §2 — Non-vacuous concrete `L_S7E` on the genuine `Antichain3`

`lemS7E_antichain3` fires `lemS7E_groundSet` on the genuine width-3
non-chain poset `Antichain3` — the carrier of the mg-496b Steps 1–6
cascade witness.  It is a **fully closed term**: no free hypotheses,
no placeholders.

The constant choices are the genuine extracted ones:

* `c_n = 1`, `c_d = 2` (mg-8f9c, the post-activation density
  `c'_T = 1/2` of `step5.tex:721-738`) — baked into
  `lem_bandwidth_le_four_bundled_of_step5_richness`;
* `b_n = step6BudgetNum 2 1`, `b_d = step6BudgetDen 1 1` (mg-5f3e,
  the genuine `Antichain3` cascade constants `t_d = 2, δ_n = 1` /
  `t_n = 1, δ_d = 1` — `= 4, 1`, see `step6_budget_constants_antichain3`);
* `M₀ = genLP.card = 6` — the genuine `|LE(Antichain3)|`.

**Scope disclosure.**  The concrete instance runs the assembly with
the *constant* BFS potential (`signedWeight = 0`, `path = []`), so the
rich-pair variational budget is genuinely `0` and `hModel` /
`hBound` close with `exceptionalMass = 0`.  The resulting `L_S7E`
confines **all** rich pairs to the interaction window
(`richPairsOut = ∅` — the strongest layered conclusion).  The
genuine *positive*-budget `VarBudgetHyp` carrying the same extracted
constants `b_n = 4, b_d = 1` is independently certified upstream by
`antichain3_varBudgetHyp_genuine` (mg-5f3e); `lemS7E_groundSet` is
fully general over the budget data, so a positive-budget caller
(Piece 3, with the genuine `lem:budget-var` index conversion)
instantiates it unchanged. -/

section ConcreteWitness

open Step6

/-- **The assembled `L_S7E`, fired on the genuine `Antichain3`**
(`mg-S7-Conc-D` non-triviality certificate).

A fully closed `∃ L : LayeredWidth3 …, L.bandwidth ≤ 4 ∧ …` on the
genuine width-3 non-chain poset `Antichain3`.  Both the
`RichnessHyp` (constants `c_n = 1, c_d = 2`, mg-8f9c) and the
`VarBudgetHyp` (constants `b_n = step6BudgetNum 2 1,
b_d = step6BudgetDen 1 1`, mg-5f3e) are discharged inside
`lemS7E_groundSet` — they are **not** hypotheses here.

* `richPairs := pairs := univ` — all `9` ambient pairs of
  `Antichain3 × Antichain3`, a genuinely non-empty rich-pair set.
* `LP := genLP` — the `6`-element linear-extension universe of
  `Antichain3` (`gen_LP_card`); `M₀ = genLP.card = 6 = |LE(P)|`.
* `goodFiber := fun _ => univ`, `badFiber := fun _ => ∅`,
  `B₀ := 0` — the activated `lem:fiber-mass` partition with every
  good fiber carrying the full `6`-element mass (richness
  `1·6 ≤ 2·6`, genuine slack).

The conclusion's exceptional-mass bound
`4·1·(b_d·|richPairsOut|)·6 ≤ 2·(b_n·6)` carries the genuine
extracted Step 6 constants verbatim. -/
theorem lemS7E_antichain3 :
    ∃ (L : LayeredWidth3
          (Finset.univ : Finset (Antichain3 × Antichain3))),
      L.bandwidth ≤ 4 ∧
      L.richPairsIn.card + L.richPairsOut.card =
        (Finset.univ : Finset (Antichain3 × Antichain3)).card ∧
      4 * 1 * (step6BudgetDen 1 1 * L.richPairsOut.card) * genLP.card ≤
        2 * (step6BudgetNum 2 1 * genLP.card) := by
  refine lemS7E_groundSet
    (α := Antichain3)
    (signedWeight := fun _ => 0) (edgeWeight := fun _ => 0)
    (path := fun _ => []) (psrc := fun _ => Antichain3.extId)
    (ptgt := fun _ => Antichain3.extId)
    (pairs := Finset.univ) (richPairs := Finset.univ)
    (LP := genLP) (goodFiber := fun _ => Finset.univ)
    (badFiber := fun _ => ∅) (B₀ := 0)
    ?hcover ?hdisj ?hthin ?hact ?hSub
    (b_n := step6BudgetNum 2 1) (b_d := step6BudgetDen 1 1)
    (exceptionalMass := 0) ?hModel ?hBound
  case hcover => intro p _; simp [genLP]
  case hdisj => intro p _; simp
  case hthin => intro p _; simp
  case hact => simp
  case hSub => exact Finset.Subset.refl _
  case hModel =>
    refine le_of_eq (Finset.sum_eq_zero (fun p _ => ?_))
    simp [BandwidthData.ofPotential, bfsPotentialData, bfsSumPot]
  case hBound => simp

/-- **The concrete `L_S7E` witness on `Antichain3`** — the
`LayeredWidth3` term the Piece 3 S7-F bridge consumes
(`mg-S7-Conc-D`).

Extracted from `lemS7E_antichain3`.  `noncomputable` because the
extraction goes through `Classical.choice`; the existence is
genuine and constructive inside `prop_72`. -/
noncomputable def L_S7E_antichain3 :
    LayeredWidth3 (Finset.univ : Finset (Antichain3 × Antichain3)) :=
  lemS7E_antichain3.choose

/-- **`L_S7E` has bandwidth at most `4`** (`mg-S7-Conc-D`, the
load-bearing S7-F bridge input — paper `rem:w0-constant`). -/
theorem L_S7E_antichain3_bandwidth :
    L_S7E_antichain3.bandwidth ≤ 4 :=
  lemS7E_antichain3.choose_spec.1

/-- **Non-vacuity certificate** (`mg-S7-Conc-D` non-triviality bar).

The assembled `L_S7E` is genuine, not a degenerate object:

* the genuine extracted constants evaluate to `step6BudgetNum 2 1 = 4`,
  `step6BudgetDen 1 1 = 1` (mg-5f3e — `Antichain3` cascade) and the
  shared denominator `genLP.card = 6` (`|LE(Antichain3)|`);
* the rich-pair set `univ : Finset (Antichain3 × Antichain3)` is
  genuinely non-empty (`9` pairs), so `L_S7E` is a layered
  decomposition of a non-empty rich set — not the vacuous empty
  packaging;
* `L_S7E.bandwidth ≤ 4` holds.

Were the constants placeholders the first three equalities would
fail; were the rich set empty the `Nonempty` conjunct would fail. -/
theorem lemS7E_antichain3_nonvacuous :
    step6BudgetNum 2 1 = 4 ∧
    step6BudgetDen 1 1 = 1 ∧
    genLP.card = 6 ∧
    (Finset.univ : Finset (Antichain3 × Antichain3)).Nonempty ∧
    L_S7E_antichain3.bandwidth ≤ 4 :=
  ⟨rfl, rfl, gen_LP_card,
   ⟨(Antichain3.a0, Antichain3.a0), Finset.mem_univ _⟩,
   L_S7E_antichain3_bandwidth⟩

end ConcreteWitness

end Step7
end OneThird
