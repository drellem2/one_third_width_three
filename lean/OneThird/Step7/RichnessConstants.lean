/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.GroundSet
import OneThird.Step5.G4G5Grounded

/-!
# Step 7 — extraction of the Step 5 richness constants `c_n, c_d, M₀`

This file is **piece 2, sub-arc mg-S7-Conc-B** of the Option A' FULL
REFACTOR (`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2;
work item mg-8f9c, the deferred follow-on to mg-4ce6 / mg-S7-Conc-A).

## What this file delivers

The S7-E bandwidth lemma `lem_bandwidth_le_four_bundled`
(`Step7/Prop71_Prop72_LemBandwidth.lean`) and its ground-set
concretisation `lem_bandwidth_le_four_bundled_groundSet`
(`Step7/GroundSet.lean`, mg-4ce6) consume the **per-pair richness
hypothesis**

  `RichnessHyp richPairs c_n c_d M₀ := ∀ p ∈ richPairs,
       c_n · M₀ ≤ c_d · posMass p`

(`Step7/Bandwidth.lean`, the cleared form of the paper's
`c_T`-richness, `step7.tex:1033-1036`) as a *parametric* hypothesis
with abstract constants `c_n, c_d, M₀`.  mg-4ce6 left these
constants and the `RichnessHyp` proof parametric because the Step 5
grounded forms had not yet landed (`docs/state-S7-Conc-Session1.md`
§5: "mg-S7-Conc-B … Needs: a Step 5 grounded form exporting
concrete richness constants. Not in tree.").

Piece 1 (Steps 1-6 cascade) has since landed (mg-d4bb / mg-be3e
S5 wave, Checkpoint 2 passed via mg-496b).  This file extracts the
**genuine concrete richness constants** from the landed Step 5
output and discharges `RichnessHyp` with them.

## The extracted constants

The landed Step 5 G4 grounded form `Step5.fiber_mass_grounded`
(`Step5/G4G5Grounded.lean`, the *activated* clause (b) of
`lem:fiber-mass`, `step5.tex:643-652` + `step5.tex:704-718`)
delivers the **per-pair bulk bound**

  `∀ p ∈ richPairs, 2 · |goodFiber p| ≥ |LP|`

— this is the first conjunct of `fiber_mass_grounded`'s output.
It is *exactly* the shape of `RichnessHyp` with

  `c_n = 1`,   `c_d = 2`,   `M₀ = |LP|`,

and the per-pair mass `posMass p := |goodFiber p|`.  The fraction
`c_n / c_d = 1/2` is the genuine post-activation density
`c'_T = c₅⋆/2` of the paper (`step5.tex:721-738`, Step 3 of the
`lem:fiber-mass` proof): after the activation step `2·B₀ ≤ |LP|`,
every rich pair's good fiber carries at least *half* the
linear-extension mass.  `M₀ = |LP|` is `|LE(P)|` when `LP` is the
full linear-extension universe.  These are **not** placeholders:
`c_d = 2` is the genuine activation factor and `1/2` is the
load-bearing per-pair density.

## Which Step 5 grounded form to project from — and why

The *top-level* dichotomy packaging `Step5.thm_step5_grounded`
(`Step5/DichotomyGrounded.lean`) outputs, on its (R) branch, the
**aggregate** richness conclusion `Step5.Step5Richness LP_card
fiberSum c_R := c_R · LP_card ≤ fiberSum` — a bound on the
*total* fiber mass `∑_{p rich} |F_p|`, which is what feeds Step 6's
second moment (`cor:second-moment`).  An aggregate bound does *not*
by itself yield a per-pair lower bound, so `Step5Richness` does
**not** project into `RichnessHyp` directly.

The per-pair content of the (R) branch is exposed one level down,
by the G4 grounded form `Step5.fiber_mass_grounded` — the grounding
of `lem:fiber-mass`, which `thm_step5_grounded` invokes precisely on
its (R) branch (the `hG4_*` closures).  This file therefore projects
`RichnessHyp` from `fiber_mass_grounded` (per-pair), not from
`thm_step5_grounded`'s `Step5Richness` packaging (aggregate).  Both
are landed Step 5 (R)-branch grounded forms; the per-pair one is the
one `RichnessHyp` needs.  This is a "which grounded form" routing
fact, **not** a gap — see `docs/state-S7-Conc-B-Session1.md` §3.

## The constants project cleanly into the parametric signature

`lem_bandwidth_le_four_bundled_of_step5_richness` (§3 below)
demonstrates the projection end-to-end: it feeds the extracted
`RichnessHyp` (constants `1, 2, |LP|`) straight into the S7-E
`lem_bandwidth_le_four_bundled_groundSet` and the call type-checks.
The mg-8f9c non-triviality bar's block-and-report condition ("the
Step 5 constants do not project cleanly into the parametric
signature") therefore does **not** fire.

## Cross-references

* `Step5/G4G5Grounded.lean` (mg-be3e) — `fiber_mass_grounded`,
  the per-pair G4 grounded form projected from here.
* `Step5/DichotomyGrounded.lean` (mg-d4bb) — `thm_step5_grounded`,
  `Step5Richness` (the aggregate (R) conclusion).
* `Step7/Bandwidth.lean` — `BandwidthData`, `RichnessHyp`,
  `VarBudgetHyp`, `BandwidthData.ofPotential`.
* `Step7/GroundSet.lean` (mg-4ce6) — `BKVertex`, `BKEdge`,
  `lem_bandwidth_le_four_bundled_groundSet`.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2 — the
  mg-S7-Conc-B sub-arc spec.
* `docs/state-S7-Conc-B-Session1.md` (mg-8f9c) — this session's
  state doc.
-/

namespace OneThird
namespace Step7

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Core: `RichnessHyp` from the Step 5 G4 grounded form

The constant extraction proper.  Given the landed Step 5 G4
interface-partition data (`Step5.fiber_mass_grounded`'s hypotheses)
and any `BandwidthData` whose `posMass` is the good-fiber
cardinality on the rich set, the per-pair richness hypothesis
`RichnessHyp` holds with the genuine constants `c_n = 1`,
`c_d = 2`, `M₀ = |LP|`. -/

/-- **Step 5 richness-constant extraction (core).**

From the landed Step 5 G4 grounded form `Step5.fiber_mass_grounded`
— the *activated* `lem:fiber-mass` interface partition
`LP = goodFiber p ⊔ badFiber p` (I1), thin bad sets
`|badFiber p| ≤ B₀` (I2), and the activation threshold
`2·B₀ ≤ |LP|` — the per-pair richness hypothesis `RichnessHyp`
holds with the extracted constants

  `c_n = 1`,   `c_d = 2`,   `M₀ = |LP|`,

for any `BandwidthData D` whose per-pair mass `D.posMass` is the
good-fiber cardinality on the rich set (`hposMass`).

This is the genuine projection of the Step 5 (R) branch into the
Step 7 `RichnessHyp` signature: the conclusion
`∀ p ∈ richPairs, 1 · |LP| ≤ 2 · D.posMass p` is the cleared
post-activation density `c'_T = 1/2` of `step5.tex:721-738`. -/
theorem richnessHyp_of_fiber_mass_grounded
    {Pair LinExt : Type*} [DecidableEq LinExt]
    (D : BandwidthData Pair)
    (richPairs : Finset Pair) (LP : Finset LinExt)
    (goodFiber badFiber : Pair → Finset LinExt) (B₀ : ℕ)
    (hcover : ∀ p ∈ richPairs, goodFiber p ∪ badFiber p = LP)
    (hdisj : ∀ p ∈ richPairs, Disjoint (goodFiber p) (badFiber p))
    (hthin : ∀ p ∈ richPairs, (badFiber p).card ≤ B₀)
    (hact : 2 * B₀ ≤ LP.card)
    (hposMass : ∀ p ∈ richPairs, D.posMass p = (goodFiber p).card) :
    D.RichnessHyp richPairs 1 2 LP.card := by
  intro p hp
  have hper := (Step5.fiber_mass_grounded richPairs LP goodFiber badFiber
    B₀ hcover hdisj hthin hact).1 p hp
  rw [hposMass p hp]
  omega

/-! ### §2 — Ground-set form: `RichnessHyp` for the BK-graph carrier

The §1 core specialised to the concrete ground-set carrier types of
mg-4ce6 (`Pair := α × α`, `LinExt := BKVertex α`), with the
`BandwidthData` taken in the `BandwidthData.ofPotential` shape that
`lem_bandwidth_le_four_bundled_groundSet` consumes.  The free
`posMass` slot of `ofPotential` is instantiated with the Step 5
good-fiber cardinality. -/

/-- **Step 5 richness-constant extraction (ground-set form).**

The §1 core projected onto the BK-graph ground set: for the
`BandwidthData.ofPotential` shape of the S7-E bandwidth lemma, with
the free `posMass` slot wired to the Step 5 good-fiber cardinality
`fun p => |goodFiber p|`, the per-pair richness hypothesis
`RichnessHyp` holds with the extracted constants `c_n = 1`,
`c_d = 2`, `M₀ = |LP|`.

This is the `hRich` argument the S7-F bridge (piece 3) and the
sub-arc mg-S7-Conc-D assembly will pass to
`lem_bandwidth_le_four_bundled_groundSet`. -/
theorem richnessHyp_groundSet_of_step5
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (psrc ptgt : α × α → BKVertex α)
    (richPairs : Finset (α × α)) (LP : Finset (BKVertex α))
    (goodFiber badFiber : α × α → Finset (BKVertex α)) (B₀ : ℕ)
    (hcover : ∀ p ∈ richPairs, goodFiber p ∪ badFiber p = LP)
    (hdisj : ∀ p ∈ richPairs, Disjoint (goodFiber p) (badFiber p))
    (hthin : ∀ p ∈ richPairs, (badFiber p).card ≤ B₀)
    (hact : 2 * B₀ ≤ LP.card) :
    (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt (fun p => (goodFiber p).card)).RichnessHyp
      richPairs 1 2 LP.card :=
  richnessHyp_of_fiber_mass_grounded _ richPairs LP goodFiber badFiber B₀
    hcover hdisj hthin hact (fun _ _ => rfl)

/-! ### §3 — The constants project cleanly into the S7-E signature

The mg-8f9c non-triviality bar requires a block-and-report *if* the
Step 5 constants do not project cleanly into the parametric
`lem_bandwidth_le_four_bundled` signature.  The theorem below
discharges that bar in the affirmative: the extracted `RichnessHyp`
(constants `1, 2, |LP|`) is fed straight into the S7-E
`lem_bandwidth_le_four_bundled_groundSet` and the call type-checks.
No adapter algebra is needed — the projection is exact. -/

/-- **The Step 5 richness constants project cleanly into the S7-E
bandwidth lemma.**

Composing the §2 ground-set `RichnessHyp` extraction with the S7-E
`lem_bandwidth_le_four_bundled_groundSet` (mg-4ce6): given the
Step 5 G4 interface-partition data and a variational-budget
hypothesis `hBud` over the *same* good-fiber `posMass` and
`M₀ = |LP|`, the layered width-3 decomposition with `bandwidth ≤ 4`
exists.

`hBud` is the sub-arc mg-S7-Conc-C deliverable (the Step 6
conductance-budget constants `b_n, b_d`); it is threaded here as a
hypothesis.  Note the consistency constraint it inherits from this
sub-arc: mg-S7-Conc-C must produce `hBud` for the **same**
`posMass := fun p => |goodFiber p|` and the **same** `M₀ := |LP|`
that the richness extraction fixes here.

The existence of this theorem *is* the non-triviality bar's
"projects cleanly" certificate: the extracted constants `1, 2, |LP|`
are accepted verbatim by the parametric S7-E signature. -/
theorem lem_bandwidth_le_four_bundled_of_step5_richness
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (psrc ptgt : α × α → BKVertex α)
    (pairs richPairs : Finset (α × α)) (LP : Finset (BKVertex α))
    (goodFiber badFiber : α × α → Finset (BKVertex α)) (B₀ : ℕ)
    (hcover : ∀ p ∈ richPairs, goodFiber p ∪ badFiber p = LP)
    (hdisj : ∀ p ∈ richPairs, Disjoint (goodFiber p) (badFiber p))
    (hthin : ∀ p ∈ richPairs, (badFiber p).card ≤ B₀)
    (hact : 2 * B₀ ≤ LP.card)
    (hSub : richPairs ⊆ pairs) (b_n b_d : ℕ)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt (fun p => (goodFiber p).card)).VarBudgetHyp
          pairs b_n b_d LP.card) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      L.richPairsIn.card + L.richPairsOut.card = richPairs.card ∧
      4 * 1 * (b_d * L.richPairsOut.card) * LP.card ≤
        2 * (b_n * LP.card) :=
  lem_bandwidth_le_four_bundled_groundSet signedWeight edgeWeight path
    psrc ptgt (fun p => (goodFiber p).card) pairs richPairs
    b_n b_d 1 2 LP.card hSub hBud
    (richnessHyp_groundSet_of_step5 signedWeight edgeWeight path
      psrc ptgt richPairs LP goodFiber badFiber B₀
      hcover hdisj hthin hact)

/-! ### §4 — Non-vacuous instantiation at the Step 5 concrete witness

The extraction fired on the genuine Step 5 concrete witness data
(`Step5.cLP`, `Step5.cRich`, `Step5.cGood`, `Step5.cBad` of
`Step5/G4G5Grounded.lean`, mg-be3e): a `6`-element linear-extension
universe (`|LE(P)|` of the minimal width-3 non-chain poset, the
3-antichain), two rich pairs, each with a `4`-element good fiber and
a `2`-element bad fiber.  No `Subsingleton`/empty baseline. -/

section ConcreteWitness

/-- A concrete `BandwidthData` over the Step 5 concrete witness: the
per-pair mass `posMass` is the genuine Step 5 good-fiber cardinality
`fun p => |Step5.cGood p|`.  (`delta` is irrelevant to the richness
hypothesis and is set to `0`.) -/
def cRichBandwidthData : BandwidthData (Fin 2) :=
  { delta := fun _ => 0
    posMass := fun p => (Step5.cGood p).card }

/-- **Step 5 richness-constant extraction, fired on the concrete
witness.**  `RichnessHyp` holds with the extracted constants
`c_n = 1`, `c_d = 2`, `M₀ = |Step5.cLP|` on the genuine Step 5
interface-partition data — discharged by `richnessHyp_of_fiber_mass_grounded`
from the genuine cover / disjointness / thin-bad-set / activation
facts of the concrete witness. -/
theorem richnessHyp_concrete :
    cRichBandwidthData.RichnessHyp Step5.cRich 1 2 Step5.cLP.card :=
  richnessHyp_of_fiber_mass_grounded cRichBandwidthData
    Step5.cRich Step5.cLP Step5.cGood Step5.cBad 2
    (by intro p _; simp only [Step5.cGood, Step5.cBad, Step5.cLP]; decide)
    (by intro p _; simp only [Step5.cGood, Step5.cBad]; decide)
    (by intro p _; simp only [Step5.cBad]; decide)
    (by decide)
    (fun _ _ => rfl)

/-- **Non-vacuity certificate.**  The concrete extraction fires with
genuine, non-degenerate numbers:

* the rich set `Step5.cRich` is non-empty;
* `M₀ = |Step5.cLP| = 6` (the genuine `|LE(P)|` of the 3-antichain);
* each rich pair carries per-pair mass `posMass p = 4` (a genuine
  `4`-element good fiber, not a `0` baseline);
* the extracted per-pair richness bound `1 · 6 ≤ 2 · 4` holds with
  genuine slack (`6 ≤ 8`).

So `RichnessHyp` is satisfied non-vacuously: were the good fibers
empty, `posMass` would be `0` and `1 · 6 ≤ 2 · 0` would be false. -/
theorem richnessHyp_concrete_nonvacuous :
    Step5.cRich.Nonempty ∧
    Step5.cLP.card = 6 ∧
    (∀ p ∈ Step5.cRich, cRichBandwidthData.posMass p = 4) ∧
    cRichBandwidthData.RichnessHyp Step5.cRich 1 2 Step5.cLP.card :=
  ⟨Step5.cRich_nonempty,
   by decide,
   by intro p _; change (Step5.cGood p).card = 4
      simp only [Step5.cGood]; decide,
   richnessHyp_concrete⟩

end ConcreteWitness

end Step7
end OneThird
