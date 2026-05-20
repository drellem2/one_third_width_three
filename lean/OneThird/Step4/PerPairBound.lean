/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step4.WitnessGrounded
import OneThird.Step4.DensityRegularization

/-!
# Step 4 — grounded port, part 2: density regularization + per-pair bound aggregation

This file is the **FULL REFACTOR Piece 1, Wave-3 S4-B** grounded port of
`step4.tex` part 2.  Where S4-A (`OneThird.Step4.WitnessGrounded`) ported
the **statement** of `thm:step4` and **constructed** the BK-edge witness
family `E_{α,β}` in the incoherent locus, this file **completes the
per-pair incompatibility bound**: it aggregates the per-block rectangle
incompatibility into the BK-boundary lower bound

  `|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|`

(`step4.tex:93`, `thm:step4`), discharging the `hWitLB` hypothesis of the
S4-A reduction `thm_step4_grounded_witness`.

## What this file delivers (S4-B scope)

* `witnessFamily_card_eq_sum` — **`prop:G1.2` grounded** (`step4.tex:152`,
  multiplicity 1): when the conflict squares of the incoherent locus
  occupy disjoint blocks, `E_{α,β}` is a *disjoint* union, so its
  cardinality is the sum of the per-square cut-edge counts.
* `cutEdgesOfSquare_disjoint_of_squareEdges_disjoint` — the structural
  fact that conflict squares with disjoint BK-edge sets contribute
  disjoint cut edges; the discharge route for the disjointness
  hypothesis from the `prop:G1` block partition.
* `prop_G5_witnessFamily` — **`prop:G5` density regularization grounded**
  (`step4.tex:999`): aggregates the per-incoherent-block cut-edge lower
  bound into a lower bound on `|E_{α,β}|`.  Routes through the abstract
  `OneThird.Step4.prop_G5_caseA`.
* `markov_incoherent_mass` — **the Markov-style aggregation arithmetic**
  (`step4.tex:1140`): the incoherent blocks (η-disagreement on a
  `≥ ½`-fraction of block mass) carry, up to the `|Ω°|` Markov slack,
  the bulk of the pointwise disagreement.
* `incoherent_mass_lower_bound` — its operative corollary
  `δ·|Ω°| ≤ 2·M_inc`.
* `step4_perPair_bound` — **the full per-pair witness discharge**: from
  the grounded per-block rectangle incompatibility, the block-disjointness
  of the witness family, and the Markov incoherent-mass bound, delivers
  the grounded `Step4Conclusion` (`thm:step4`).
* `perPairBound_nonvacuous` / `markov_incoherent_mass_nonvacuous` — the
  S4-B non-vacuity acceptance witnesses at the genuine width-3 non-chain
  grid poset `Fin 3 × Fin 3`.

## What this consumes

* **S4-A** (`OneThird.Step4.WitnessGrounded`) — `witnessFamily`,
  `cutEdgesOfSquare`, `bkBoundary`, `lem22_bk`, `Step4Conclusion`,
  `thm_step4_grounded_witness`, and the non-vacuity scaffold
  (`gridSquare`, `witnessGrounded_nonvacuous`).
* **Step 4 abstract scaffold** (`OneThird.Step4.DensityRegularization`)
  — the abstract `prop:G5` case-A aggregation `prop_G5_caseA`; this file
  grounds it on the concrete BK witness family.

## Scope boundary (honest)

This file ports the **aggregation** half of Step 4 part 2: the density
regularization sum, the Markov-style incoherent-mass arithmetic, and the
witness→boundary discharge.  The deepest geometric input — the per-block
rectangle 2×2 incompatibility count of `lem:rect-stable-area`
(`step4.tex:543`) — is **already formalised abstractly** in
`OneThird.Step4.RectangleModel` (`rect_stable_area_nonconst_lb`); the
per-block lower bound `c·|R_B| ≤ |E_B| + C·ε·|R_B|` it produces enters
`step4_perPair_bound` as the named hypothesis `hPerBlock`, in the
abstract-hypothesis style of the entire Step 4 scaffold.  The non-vacuity
witness discharges `hPerBlock` *concretely* at the grid poset via the
S4-A `lem:22` (`lem22_bk`): a genuine conflict square contributes a
genuine BK cut edge.
-/

namespace OneThird
namespace Step4

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## §1 — The witness family as a disjoint union (`prop:G1.2`)

`step4.tex:152` (G1.2): the rectangles `R_B` have multiplicity exactly
`1` — every state belongs to at most one block.  Hence conflict squares
in distinct blocks occupy disjoint rectangles, their BK edges are
disjoint, and the witness family `E_{α,β} = ⊔_B {cut edges of conflict
squares in R_B}` is a genuine *disjoint* union (`step4.tex:1167`, the
`⊔`).  Under that disjointness, `|E_{α,β}|` is the sum of the per-square
cut-edge counts — the identity the density-regularization aggregation
of §2 consumes. -/

/-- Conflict squares whose four-edge sets are disjoint contribute
disjoint **cut**-edge sets: `cutEdgesOfSquare S q ⊆ squareEdges q`, so
disjointness of the `squareEdges` propagates.  This is the discharge
route for the disjointness hypothesis of `witnessFamily_card_eq_sum`
from the `prop:G1` block partition: squares in distinct blocks have
disjoint rectangles, hence disjoint BK edges. -/
theorem cutEdgesOfSquare_disjoint_of_squareEdges_disjoint
    (S : Finset (LinearExt α)) {q q' : BKSquare α}
    (h : Disjoint (squareEdges q) (squareEdges q')) :
    Disjoint (cutEdgesOfSquare S q) (cutEdgesOfSquare S q') := by
  unfold cutEdgesOfSquare
  exact Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left h)

/-- **`prop:G1.2` grounded — the witness family is a disjoint union.**
When the cut-edge sets of the incoherent conflict squares are pairwise
disjoint (guaranteed by the block partition, `step4.tex:152` (G1.2)),
the witness-family cardinality is exactly the sum of the per-square
cut-edge counts.  This is the cardinality identity the density
regularization of §2 sums against. -/
theorem witnessFamily_card_eq_sum {ι : Type*}
    (S : Finset (LinearExt α)) (squares : Finset ι) (crn : ι → BKSquare α)
    (inIncoherent : ι → Prop) [DecidablePred inIncoherent]
    (hdisj : ∀ i ∈ squares.filter inIncoherent,
      ∀ j ∈ squares.filter inIncoherent, i ≠ j →
        Disjoint (cutEdgesOfSquare S (crn i)) (cutEdgesOfSquare S (crn j))) :
    (witnessFamily S squares crn inIncoherent).card =
      ∑ i ∈ squares.filter inIncoherent, (cutEdgesOfSquare S (crn i)).card := by
  classical
  unfold witnessFamily
  exact Finset.card_biUnion hdisj

/-! ## §2 — `prop:G5` density regularization, grounded (`step4.tex:999`)

`prop:G5` converts the per-block rectangle incompatibility into the
global BK-boundary lower bound.  Grounded: the abstract case-A
aggregation `OneThird.Step4.prop_G5_caseA` is instantiated with the
per-square cut-edge count as the per-block boundary contribution and the
disjoint-union identity of §1 as the summation step. -/

/-- **`prop:G5` density regularization, grounded on the witness family
(`step4.tex:999`).**  Given, for every conflict square `i` in an
incoherent block, the per-block rectangle-incompatibility lower bound

  `c·|R_i| ≤ |cut edges of square i| + C·ε·|R_i|`

(the `lem:rect-stable-area` output, `step4.tex:543`) and the
block-disjointness of the cut-edge sets, the incoherent overlap mass
`∑_i |R_i|` is paid for in the witness family:

  `c·(∑_i |R_i|) ≤ |E_{α,β}| + C·ε·(∑_i |R_i|)`.

The proof routes through the abstract `prop_G5_caseA` of
`OneThird.Step4.DensityRegularization`. -/
theorem prop_G5_witnessFamily {ι : Type*}
    (S : Finset (LinearExt α)) (squares : Finset ι) (crn : ι → BKSquare α)
    (inIncoherent : ι → Prop) [DecidablePred inIncoherent]
    (Rsize : ι → ℕ) (c cnst eps : ℕ)
    (hdisj : ∀ i ∈ squares.filter inIncoherent,
      ∀ j ∈ squares.filter inIncoherent, i ≠ j →
        Disjoint (cutEdgesOfSquare S (crn i)) (cutEdgesOfSquare S (crn j)))
    (hPerBlock : ∀ i ∈ squares.filter inIncoherent,
      c * Rsize i ≤ (cutEdgesOfSquare S (crn i)).card + cnst * eps * Rsize i) :
    c * (∑ i ∈ squares.filter inIncoherent, Rsize i) ≤
      (witnessFamily S squares crn inIncoherent).card +
        cnst * eps * (∑ i ∈ squares.filter inIncoherent, Rsize i) := by
  classical
  have hcard := witnessFamily_card_eq_sum S squares crn inIncoherent hdisj
  have hG5 := prop_G5_caseA (squares.filter inIncoherent) Rsize
    (fun i => (cutEdgesOfSquare S (crn i)).card) c 1 cnst eps
    (by
      intro B hB
      have h := hPerBlock B hB
      simpa [Nat.mul_one] using h)
    (witnessFamily S squares crn inIncoherent).card
    (le_of_eq hcard.symm)
  simpa [Nat.mul_one] using hG5

/-! ## §3 — The Markov-style aggregation arithmetic (`step4.tex:1140`)

`step4.tex:1140` (proof of `thm:step4`): *"Call a block `B` incoherent
if `η_{x,y} ≠ η_{u,v}` on a `≥ ½`-fraction of `B`-mass; by Markov,
incoherent blocks account for `≥ δ/2·|Ω°|`."*

In cleared-denominator integer form: with per-block pointwise
disagreement count `dis B` and block mass `m B` (so `dis B ≤ m B`), a
block is **incoherent** exactly when `m B ≤ 2·dis B` — matching the S4-A
`BlockIncoherent` `½`-threshold (`WitnessGrounded.lean`, `step4.tex:1142`).
The Markov bound says the incoherent blocks carry, up to one `|Ω°|`
slack, twice the total disagreement. -/

/-- **The Markov-style aggregation arithmetic (`step4.tex:1140`).**

With per-block pointwise-disagreement count `dis B` and block mass `m B`
(`dis B ≤ m B`, since the disagreement set is a subset of the block),
declare a block **incoherent** when `m B ≤ 2·dis B` (the S4-A
`BlockIncoherent` `½`-threshold, `step4.tex:1142`).  Then

  `2·(∑_B dis B) ≤ 2·(∑_{incoherent B} m B) + ∑_B m B`,

i.e. the incoherent blocks' mass `M_inc := ∑_{inc} m B` carries — up to
the `∑_B m B = |Ω°|` Markov slack — twice the total disagreement.  This
is the genuine Markov split: on a *coherent* block the disagreement is
`< ½·m B`, so the coherent blocks together lose at most `½·|Ω°|` of the
disagreement, leaving the rest concentrated on the incoherent mass. -/
theorem markov_incoherent_mass {ι : Type*}
    (blocks : Finset ι) (dis m : ι → ℕ)
    (hle : ∀ B ∈ blocks, dis B ≤ m B) :
    2 * (∑ B ∈ blocks, dis B) ≤
      2 * (∑ B ∈ blocks.filter (fun B => m B ≤ 2 * dis B), m B) +
        ∑ B ∈ blocks, m B := by
  classical
  -- Split the total disagreement into incoherent + coherent blocks.
  have hsplit :
      ∑ B ∈ blocks, dis B =
        (∑ B ∈ blocks.filter (fun B => m B ≤ 2 * dis B), dis B) +
        ∑ B ∈ blocks.filter (fun B => ¬ (m B ≤ 2 * dis B)), dis B :=
    (Finset.sum_filter_add_sum_filter_not blocks _ dis).symm
  -- On incoherent blocks: `dis B ≤ m B`.
  have hinc :
      2 * (∑ B ∈ blocks.filter (fun B => m B ≤ 2 * dis B), dis B) ≤
        2 * (∑ B ∈ blocks.filter (fun B => m B ≤ 2 * dis B), m B) :=
    Nat.mul_le_mul_left 2
      (Finset.sum_le_sum (by
        intro B hB
        rw [Finset.mem_filter] at hB
        exact hle B hB.1))
  -- On coherent blocks: `¬ (m B ≤ 2·dis B)`, i.e. `2·dis B ≤ m B`.
  have hcoh :
      2 * (∑ B ∈ blocks.filter (fun B => ¬ (m B ≤ 2 * dis B)), dis B) ≤
        ∑ B ∈ blocks.filter (fun B => ¬ (m B ≤ 2 * dis B)), m B := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro B hB
    rw [Finset.mem_filter] at hB
    omega
  -- The coherent-block mass is a sub-sum of the total mass.
  have hcoh_le :
      ∑ B ∈ blocks.filter (fun B => ¬ (m B ≤ 2 * dis B)), m B ≤
        ∑ B ∈ blocks, m B :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

/-- **Operative corollary of the Markov split.**  If the global
incoherence parameter `δ` is calibrated, in cleared-denominator integer
form, by `δ·|Ω°| + |Ω°| ≤ 2·(∑_B dis B)` — equivalently `δ·|Ω°|` does
not exceed twice the total disagreement minus the Markov slack `|Ω°|` —
then the incoherent blocks carry `δ·|Ω°| ≤ 2·M_inc` of the mass.  This
is the `step4.tex:1140` *"incoherent blocks account for ≥ δ/2·|Ω°|"*
statement in the integer normalisation. -/
theorem incoherent_mass_lower_bound {ι : Type*}
    (blocks : Finset ι) (dis m : ι → ℕ) (delta omegaCard : ℕ)
    (hle : ∀ B ∈ blocks, dis B ≤ m B)
    (homega : omegaCard = ∑ B ∈ blocks, m B)
    (hglob : delta * omegaCard + omegaCard ≤ 2 * (∑ B ∈ blocks, dis B)) :
    delta * omegaCard ≤
      2 * (∑ B ∈ blocks.filter (fun B => m B ≤ 2 * dis B), m B) := by
  have hmk := markov_incoherent_mass blocks dis m hle
  omega

/-! ## §4 — The full per-pair witness discharge (`thm:step4`)

Assembling §2 + §3: the density-regularization aggregation lifts the
per-block rectangle incompatibility to a lower bound on `|E_{α,β}|`; the
Markov split feeds the incoherent overlap mass; together they discharge
the `hWitLB` hypothesis of the S4-A reduction `thm_step4_grounded_witness`
and deliver the grounded `thm:step4` conclusion. -/

/-- **The full S4-B per-pair witness discharge (`thm:step4`,
`step4.tex:93`).**

Inputs (all on the concrete grounded objects):

* `hdisj` — the conflict squares of the incoherent locus occupy disjoint
  blocks (`prop:G1.2`), so their cut-edge sets are pairwise disjoint;
* `hPerBlock` — the per-block rectangle incompatibility
  `c·|R_i| ≤ |cut edges of square i| + C·ε·|R_i|` (`lem:rect-stable-area`,
  `step4.tex:543`; the absolute density `α₀` of `lem:rect-stable` is
  folded into `c`);
* `hMarkov` — the incoherent overlap mass dominates `δ·|Ω°|` up to the
  Markov factor `2` (`incoherent_mass_lower_bound` / `step4.tex:1140`);
* `hMass` — the incoherent mass is a sub-mass of `|Ω°|`.

Conclusion: the grounded `Step4Conclusion`, i.e.

  `c·δ·|Ω°| ≤ 2·|∂_BK S| + 2·C·ε·|Ω°|`,

the cleared-denominator form of `|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|`.  The
factor `2` is exactly the Markov loss on incoherent-block mass
(`step4.tex:1156`).

Every hypothesis is load-bearing: `hdisj`+`hPerBlock` drive the density
regularization, `hMarkov` injects the incoherence mass, `hMass` clears
the residual error term, and the result is routed through the S4-A
reduction `thm_step4_grounded_witness`. -/
theorem step4_perPair_bound {ι : Type*}
    (S : Finset (LinearExt α)) (squares : Finset ι) (crn : ι → BKSquare α)
    (inIncoherent : ι → Prop) [DecidablePred inIncoherent]
    (Rsize : ι → ℕ) (c cnst delta eps omegaCard : ℕ)
    (hdisj : ∀ i ∈ squares.filter inIncoherent,
      ∀ j ∈ squares.filter inIncoherent, i ≠ j →
        Disjoint (cutEdgesOfSquare S (crn i)) (cutEdgesOfSquare S (crn j)))
    (hPerBlock : ∀ i ∈ squares.filter inIncoherent,
      c * Rsize i ≤ (cutEdgesOfSquare S (crn i)).card + cnst * eps * Rsize i)
    (hMarkov : delta * omegaCard ≤
      2 * (∑ i ∈ squares.filter inIncoherent, Rsize i))
    (hMass : (∑ i ∈ squares.filter inIncoherent, Rsize i) ≤ omegaCard) :
    Step4Conclusion S c cnst delta eps omegaCard := by
  have hG5 := prop_G5_witnessFamily S squares crn inIncoherent Rsize c cnst eps
    hdisj hPerBlock
  set Minc := ∑ i ∈ squares.filter inIncoherent, Rsize i with hMinc
  set wf := (witnessFamily S squares crn inIncoherent).card with hwf
  -- hG5 : c * Minc ≤ wf + cnst * eps * Minc
  have hWitLB :
      c * delta * omegaCard ≤ 2 * wf + 2 * cnst * eps * omegaCard := by
    calc c * delta * omegaCard
        = c * (delta * omegaCard) := by ring
      _ ≤ c * (2 * Minc) := Nat.mul_le_mul_left c hMarkov
      _ = 2 * (c * Minc) := by ring
      _ ≤ 2 * (wf + cnst * eps * Minc) := Nat.mul_le_mul_left 2 hG5
      _ = 2 * wf + 2 * (cnst * eps * Minc) := by ring
      _ ≤ 2 * wf + 2 * (cnst * eps * omegaCard) := by
            have hmono := Nat.mul_le_mul_left (cnst * eps) hMass
            omega
      _ = 2 * wf + 2 * cnst * eps * omegaCard := by ring
  exact thm_step4_grounded_witness S squares crn inIncoherent c cnst delta eps
    omegaCard hWitLB

/-! ## §5 — Non-vacuity at the concrete width-3 non-chain poset

Per the S4-B acceptance bar, the aggregation instantiates non-vacuously
at the genuine width-3 non-chain grid poset `Fin 3 × Fin 3` of
`Step1/Overlap.lean` (the S4-A non-vacuity poset), with a *genuine* BK
conflict square `gridSquare` — no `Subsingleton`-on-empty baseline. -/

/-- The Markov-style aggregation arithmetic fires on a genuine block
family with a genuinely non-empty incoherent-block set: two blocks with
masses `(3, 4)` and disagreement counts `(2, 0)`, of which the first is
incoherent (`3 ≤ 2·2`) and the second coherent (`¬ 4 ≤ 2·0`).  The
Markov bound `2·(2+0) ≤ 2·3 + (3+4)` holds non-vacuously. -/
theorem markov_incoherent_mass_nonvacuous :
    (({0, 1} : Finset (Fin 2)).filter
        (fun B => (![3, 4] : Fin 2 → ℕ) B ≤ 2 * (![2, 0] : Fin 2 → ℕ) B)).Nonempty ∧
    2 * (∑ B ∈ ({0, 1} : Finset (Fin 2)), (![2, 0] : Fin 2 → ℕ) B) ≤
      2 * (∑ B ∈ (({0, 1} : Finset (Fin 2)).filter
          (fun B => (![3, 4] : Fin 2 → ℕ) B ≤ 2 * (![2, 0] : Fin 2 → ℕ) B)),
            (![3, 4] : Fin 2 → ℕ) B) +
        ∑ B ∈ ({0, 1} : Finset (Fin 2)), (![3, 4] : Fin 2 → ℕ) B := by
  refine ⟨?_, ?_⟩
  · -- block `0` is genuinely incoherent: `3 ≤ 2·2`.
    decide
  · exact markov_incoherent_mass ({0, 1} : Finset (Fin 2)) ![2, 0] ![3, 4]
      (by decide)

/-- **The S4-B non-vacuity acceptance witness.**

At the genuine width-3 non-chain grid poset `Fin 3 × Fin 3`, with the
singleton cut `S := {gridLinExt}` and the genuine BK conflict square
`gridSquare` (the S4-A non-vacuity scaffold):

* **(poset)** `Fin 3 × Fin 3` has width exactly `3` and is not a chain —
  reused from the S4-A `witnessGrounded_nonvacuous`;
* **(conflict square)** `gridSquare` is a *genuine* conflict square —
  reused from S4-A;
* **(density regularization)** `prop_G5_witnessFamily` fires: the
  per-block rectangle incompatibility (`hPerBlock`, discharged here
  *concretely* via `lem22_bk` — a genuine conflict square contributes a
  genuine BK cut edge) aggregates into a lower bound on the witness
  family;
* **(per-pair bound)** `step4_perPair_bound` fires with strictly
  positive `δ = 1`, `|Ω°| = 1`, delivering the grounded `thm:step4`
  conclusion `Step4Conclusion`.

The conflict square is genuine — a real commuting `2×2` BK square on a
poset with two disjoint incomparable pairs — so the discharge of
`hPerBlock` is non-vacuous: `lem22_bk` extracts a real BK cut edge. -/
theorem perPairBound_nonvacuous :
    -- (poset) genuine width-3 non-chain
    HasWidth (Fin 3 × Fin 3) 3 ∧
    ¬ IsChainPoset (Fin 3 × Fin 3) ∧
    -- (conflict square) genuine
    IsConflictSquare ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      gridSquare ∧
    -- (density regularization) prop:G5 fires on the grounded witness family
    1 * (∑ _i ∈ (({()} : Finset Unit).filter (fun _ => True)), (1 : ℕ)) ≤
      (witnessFamily ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
          ({()} : Finset Unit) (fun _ => gridSquare) (fun _ => True)).card +
        0 * 0 * (∑ _i ∈ (({()} : Finset Unit).filter (fun _ => True)), (1 : ℕ)) ∧
    -- (per-pair bound) the grounded thm:step4, delivered via step4_perPair_bound
    Step4Conclusion ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      1 0 1 0 1 := by
  -- Reuse the poset + conflict-square facts from the S4-A non-vacuity.
  obtain ⟨hw, hnc, hconf, _, _, _⟩ := witnessGrounded_nonvacuous
  set S : Finset (LinearExt (Fin 3 × Fin 3)) := {gridLinExt} with hS
  -- The conflict square contributes a genuine BK cut edge (`lem:22`).
  have hcut : (cutEdgesOfSquare S gridSquare).Nonempty := by
    have := lem22_bk hconf
    simpa [cutEdgesOfSquare] using this
  have hcutCard : 1 ≤ (cutEdgesOfSquare S gridSquare).card :=
    Finset.card_pos.mpr hcut
  -- The disjointness hypothesis is vacuous on the singleton index `Unit`.
  have hdisj : ∀ i ∈ (({()} : Finset Unit).filter (fun _ => True)),
      ∀ j ∈ (({()} : Finset Unit).filter (fun _ => True)), i ≠ j →
        Disjoint (cutEdgesOfSquare S ((fun _ => gridSquare) i))
          (cutEdgesOfSquare S ((fun _ => gridSquare) j)) := by
    intro i _ j _ hij
    exact absurd (Subsingleton.elim i j) hij
  -- The per-block rectangle incompatibility, discharged concretely.
  have hPerBlock : ∀ i ∈ (({()} : Finset Unit).filter (fun _ => True)),
      1 * (fun _ => (1 : ℕ)) i ≤
        (cutEdgesOfSquare S ((fun _ => gridSquare) i)).card +
          0 * 0 * (fun _ => (1 : ℕ)) i := by
    intro i _
    simpa using hcutCard
  refine ⟨hw, hnc, hconf, ?_, ?_⟩
  · -- prop:G5 density regularization fires
    exact prop_G5_witnessFamily S ({()} : Finset Unit) (fun _ => gridSquare)
      (fun _ => True) (fun _ => 1) 1 0 0 hdisj hPerBlock
  · -- step4_perPair_bound delivers the grounded thm:step4
    refine step4_perPair_bound S ({()} : Finset Unit) (fun _ => gridSquare)
      (fun _ => True) (fun _ => 1) 1 0 1 0 1 hdisj hPerBlock ?_ ?_
    · -- hMarkov : 1 * 1 ≤ 2 * (∑ over the one incoherent square of 1)
      simp
    · -- hMass : (∑ over the one incoherent square of 1) ≤ 1
      simp

end Step4
end OneThird
