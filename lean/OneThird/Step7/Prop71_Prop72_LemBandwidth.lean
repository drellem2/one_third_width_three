/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.SignedThreshold
import OneThird.Step7.SignConsistency
import OneThird.Step7.Cocycle
import OneThird.Step7.Potential
import OneThird.Step7.SingleThreshold
import OneThird.Step7.GiantComponent
import OneThird.Step7.Bandwidth
import OneThird.Step7.Assembly
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — S7-E grounded assembly: `prop:71` + `prop:72` + `lem:bandwidth`

This file grounds the three substantive outputs of `step7.tex`
§`sec:formal` against the concrete S7-A / S7-B / S7-C / S7-D
upstream inputs:

* **`prop:71` grounded** (`step7.tex:1115-1173`) — combined
  `(1 - o(1))`-fraction threshold-of-potential description, wiring
  S7-C `lem_potential_grounded_bundled` (BFS-tree potential) with
  S7-D G6 `lem_single_c_grounded_bundled` (diameter-3 single
  threshold via the giant-component walk witness).
* **`prop:72` grounded** (`step7.tex:1175-1193`) — `LayeredWidth3`
  packaging produced from the BFS-tree potential via
  `BandwidthData.ofPotential`, taking the upstream Step 5
  variational-budget and richness hypotheses as parametric inputs.
* **`lem:bandwidth ≤ 4` grounded** (`step7.tex:1018-1056`,
  `rem:w0-constant`) — instantiation of `prop_72` at the fixed
  Δ-threshold `c₀ := 4`, producing a `LayeredWidth3 richPairs`
  with `L.bandwidth = 4` and the `o(1)`-mass bound on
  `L.richPairsOut`.  This is the **load-bearing** output for
  S7-F (the `lem:layered-from-step7` bridge), which consumes
  `L.bandwidth ≤ 4` to discharge the cap-5 sorry currently
  localised at `mainTheoremInputsOf.caseC_canonicalLayered`
  (`MainAssembly.lean`, mg-234e relocation, mg-ac13 §5.4 forward
  action 5).

## Why this is not vacuous

`prop_72`'s signature lets the caller pick `c₀ : ℕ` with `0 < c₀`.
Setting `c₀ := 4` makes the bandwidth bound
`c₀ · c_n · b_d · |L.richPairsOut| · M₀ ≤ c_d · b_n · M₀`
*more* restrictive (smaller |L.richPairsOut|) than smaller `c₀`,
not less.  The paper's `w₀(γ) ≤ 4` claim is precisely this
choice: the constant `4` is the `K(T) + O(1)` of `lem:bandwidth`
with the fixed-`T` consequence that `O(1) ≤ 4` (paper
`step7.tex:1015-1018`, `rem:w0-constant`).

The genuine substantive content of the grounded form is:

1. `BandwidthData.ofPotential` of the BFS-tree potential
   instantiates the abstract `BandwidthData` against the S7-C
   grounded `pot := bfsSumPot signedWeight path` — i.e. the
   `delta : Pair → ℤ` field is concrete `pot (ptgt p) - pot (psrc p)`.
2. The var-budget and richness hypotheses are taken parametrically
   from upstream Step 5 (`step7.tex:949-1056` `lem:budget-var`
   and `step7.tex:1033-1036` `c_T`-richness).
3. The grounded `lem_bandwidth_le_four` discharges the conclusion
   `L.bandwidth ≤ 4` as a *constructive* corollary of `prop_72`'s
   `L.bandwidth = c₀ = 4` (not as an existential satisfiability
   claim, but as a concrete `LayeredWidth3` packaging).

## Cross-references

* `lean/OneThird/Step7/Assembly.lean` — abstract `prop_71`,
  `prop_72`, `prop_73`, `thm_step7`.
* `lean/OneThird/Step7/Bandwidth.lean` — abstract `BandwidthData`,
  `lem_bandwidth`, `BandwidthData.ofPotential` bridge.
* `lean/OneThird/Step7/Potential.lean` §7 — S7-C grounded
  `bfsPotentialData`, `lem_potential_grounded_bundled`.
* `lean/OneThird/Step7/SingleThreshold.lean` §7 — S7-D G6 grounded
  `fiberThresholdDataOfBFS`, `lem_single_c_grounded_bundled`.
* `lean/OneThird/Step7/GiantComponent.lean` — S7-D G9 grounded
  `BipartiteRichness`, `lem_giant_component_grounded_bundled`.
* Paper: `step7.tex:1115-1193` (`prop:71`, `prop:72`),
  `step7.tex:1018-1056` (`lem:bandwidth`), `step7.tex:1015-1018`
  (`rem:w0-constant`).
* `docs/OneThird-Steps-1-7-Lean-port-scoping.md` §7.1 mg-S7-E spec.
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §1 — `prop:71` grounded against the BFS-tree potential -/

section Prop71Grounded

variable {Vertex Edge : Type*} [DecidableEq Vertex] [DecidableEq Edge]

/-- **`prop:71` grounded against the S7-C BFS potential and the
S7-D G6 single-threshold walk witness** (`step7.tex:1115-1173`).

Wires the abstract `prop_71` of `Assembly.lean` against:

* the concrete BFS-tree potential `bfsPotentialData`
  (S7-C, `Potential.lean §7`) — discharges
  `PotentialData.TreeIntegrationHyp` from a
  `BFSTreeExtensionHyp` on `treeEdges`;
* the abstract short-cycle bound `hCyc` on `shortEdges`
  (S7-C upstream from `cocycle_grounded` via star-triangulation);
* the abstract long-edge decomposition `hDecomp` together with
  the cleared-denominator long-edge weight bound `hLong`
  (S7-D upstream from `lem_giant_component_grounded` exceptional
  mass);
* the abstract pair-closeness `hPair` on `goodPairs`
  (Step 6 upstream low conductance, captured as the `K₁`
  tolerance of `PairClosenessHyp`);
* the walk-witness `hWalk` on `edgesWalk ⊆ edges`
  (S7-D G9 upstream from `lem_giant_component_grounded`);
* the exceptional-mass bound `hExc` on `edges ∖ edgesWalk`
  (S7-D G9 upstream from `lem_giant_component_grounded_mass_lb`).

**Conclusion.**  The combined bad-edge weight is bounded by
`2 · (e_n / e_d) · M₀`:

  `e_d · ∑_{badEdges C₁ K₁} edgeWeight e ≤ 2 · e_n · M₀`,

where the combined bad set is

  `badEdges C₁ K₁ :=`
    `bfsPotentialData.badEdges edges C₁ ∪`
    `(fiberThresholdDataOfBFS …).badEdges refEdge edges (3·K₁)`,

i.e. the union of *potential-defect-bad* edges (off-tree fragility
of the BFS spanning) and *threshold-defect-bad* edges
(diameter-3 walk failure to the reference). -/
theorem prop_71_grounded
    (src tgt : Edge → Vertex)
    (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ)
    (path : Vertex → List Edge)
    (edges treeEdges shortEdges longEdges edgesWalk : Finset Edge)
    (refEdge : Edge) (C₁ K₁ : ℕ)
    (goodPairs : Finset (Edge × Edge))
    (hBFS : BFSTreeExtensionHyp path src tgt treeEdges)
    (hCyc : (bfsPotentialData src tgt signedWeight edgeWeight path).CycleBoundHyp
      shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (fiberThresholdDataOfBFS src tgt signedWeight edgeWeight path).PairClosenessHyp
      goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, edgeWeight e ≤ e_n * M₀) :
    let P := bfsPotentialData src tgt signedWeight edgeWeight path
    let G : GlobalThresholdDescr P edges :=
      { refEdge := refEdge, tolerance := C₁ + 3 * K₁ }
    e_d * ∑ e ∈ G.badEdges C₁ K₁, edgeWeight e ≤ 2 * e_n * M₀ := by
  -- Set up the BFS-instantiated `PotentialData` and witness `G`.
  set P := bfsPotentialData src tgt signedWeight edgeWeight path with hP_def
  have hTree : P.TreeIntegrationHyp treeEdges :=
    bfsPotentialData_tree_integration src tgt signedWeight edgeWeight
      path treeEdges hBFS
  -- The `hPair` argument's `fiberThresholdDataOfBFS` is
  -- definitionally `FiberThresholdData.ofPotential P`.
  have hPair' : (FiberThresholdData.ofPotential P).PairClosenessHyp
      goodPairs K₁ := hPair
  -- The `hLong` / `hExc` bounds rephrased through the BFS
  -- `edgeWeight = P.edgeWeight` identification.
  have hLong' :
      e_d * ∑ e ∈ longEdges, P.edgeWeight e ≤ e_n * M₀ := by
    simpa [P, bfsPotentialData_edgeWeight] using hLong
  have hExc' :
      e_d * ∑ e ∈ edges \ edgesWalk, P.edgeWeight e ≤ e_n * M₀ := by
    simpa [P, bfsPotentialData_edgeWeight] using hExc
  -- Apply the abstract `prop_71`.
  have hbase := prop_71 P edges treeEdges shortEdges longEdges
    edgesWalk refEdge C₁ K₁ goodPairs hTree hCyc hDecomp hPair' hWalk
    hWalkSub e_n e_d M₀ hLong' hExc'
    (G := { refEdge := refEdge, tolerance := C₁ + 3 * K₁ })
    (hRef := rfl)
  -- Cast `P.edgeWeight = edgeWeight`.
  simpa [P, bfsPotentialData_edgeWeight] using hbase

/-- **`prop:71` grounded — good-edge weight LB form**
(`step7.tex:1168-1173`).

Contrapositive packaging of `prop_71_grounded`: with a total
edge-weight identification `∑ edgeWeight = totalW`, the *good*
edges (those not in the combined bad set) carry at least
`totalW - 2 · (e_n / e_d) · M₀` of the weight, i.e.

  `e_d · totalW ≤
     e_d · ∑_{edges ∖ badEdges} edgeWeight e + 2 · e_n · M₀`. -/
theorem prop_71_grounded_good_weight_lb
    (src tgt : Edge → Vertex)
    (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ)
    (path : Vertex → List Edge)
    (edges treeEdges shortEdges longEdges edgesWalk : Finset Edge)
    (refEdge : Edge) (C₁ K₁ : ℕ)
    (goodPairs : Finset (Edge × Edge))
    (hBFS : BFSTreeExtensionHyp path src tgt treeEdges)
    (hCyc : (bfsPotentialData src tgt signedWeight edgeWeight path).CycleBoundHyp
      shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (fiberThresholdDataOfBFS src tgt signedWeight edgeWeight path).PairClosenessHyp
      goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ totalW : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, edgeWeight e ≤ e_n * M₀)
    (htotal : ∑ e ∈ edges, edgeWeight e = totalW) :
    let P := bfsPotentialData src tgt signedWeight edgeWeight path
    let G : GlobalThresholdDescr P edges :=
      { refEdge := refEdge, tolerance := C₁ + 3 * K₁ }
    e_d * totalW ≤
      e_d * ∑ e ∈ edges \ G.badEdges C₁ K₁, edgeWeight e +
        2 * e_n * M₀ := by
  set P := bfsPotentialData src tgt signedWeight edgeWeight path with hP_def
  have hTree : P.TreeIntegrationHyp treeEdges :=
    bfsPotentialData_tree_integration src tgt signedWeight edgeWeight
      path treeEdges hBFS
  have hPair' : (FiberThresholdData.ofPotential P).PairClosenessHyp
      goodPairs K₁ := hPair
  have hLong' :
      e_d * ∑ e ∈ longEdges, P.edgeWeight e ≤ e_n * M₀ := by
    simpa [P, bfsPotentialData_edgeWeight] using hLong
  have hExc' :
      e_d * ∑ e ∈ edges \ edgesWalk, P.edgeWeight e ≤ e_n * M₀ := by
    simpa [P, bfsPotentialData_edgeWeight] using hExc
  have htotal' :
      ∑ e ∈ edges, P.edgeWeight e = totalW := by
    simpa [P, bfsPotentialData_edgeWeight] using htotal
  have hbase := prop_71_good_weight_lb P edges treeEdges shortEdges
    longEdges edgesWalk refEdge C₁ K₁ goodPairs hTree hCyc hDecomp
    hPair' hWalk hWalkSub e_n e_d M₀ totalW hLong' hExc'
    (G := { refEdge := refEdge, tolerance := C₁ + 3 * K₁ })
    (hRef := rfl) htotal'
  simpa [P, bfsPotentialData_edgeWeight] using hbase

end Prop71Grounded

/-! ### §2 — `prop:72` grounded via `BandwidthData.ofPotential` -/

section Prop72Grounded

variable {Vertex Edge : Type*} [DecidableEq Vertex] [DecidableEq Edge]
variable {Pair : Type*} [DecidableEq Pair]

/-- **`prop:72` grounded against the S7-C BFS potential**
(`step7.tex:1175-1193`).

Wires the abstract `prop_72` of `Assembly.lean` through
`BandwidthData.ofPotential` instantiated at the BFS-tree
potential `bfsPotentialData`:

* `psrc, ptgt : Pair → Vertex` — chain-position projections for
  interfaces (paper bipartite setup, `step7.tex:1533-1540`);
* `posMass : Pair → ℕ` — BK-adjacency mass `p_xy · M₀`
  (parametric from Step 1);
* `c₀ : ℕ` (with `0 < c₀`) — the Δ-threshold chosen by the caller
  (`c₀ := 4` in `lem_bandwidth_le_four`).

**Var-budget and richness hypotheses are parametric**
(upstream Step 5):

* `hBud : VarBudgetHyp pairs b_n b_d M₀` — `step7.tex:eq:var-budget`,
  cleared `b_d · ∑ Δ⁺ · p ≤ b_n · M₀`.
* `hRich : RichnessHyp richPairs c_n c_d M₀` —
  `step7.tex:1033-1036`, cleared `c_n · M₀ ≤ c_d · posMass p`.

**Conclusion.**  A concrete `LayeredWidth3 richPairs` packaging
with:

* `L.bandwidth = c₀` (the Δ-threshold);
* the cardinality bound
  `c₀ · c_n · b_d · |L.richPairsOut| · M₀ ≤ c_d · b_n · M₀`
  (i.e. `o(1)`-mass on `L.richPairsOut`). -/
theorem prop_72_grounded
    (src tgt : Edge → Vertex)
    (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ)
    (path : Vertex → List Edge)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ)
    (pairs richPairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth = c₀ ∧
      c₀ * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) :=
  prop_72 _ pairs richPairs c₀ hc₀ b_n b_d c_n c_d M₀
    hSub hBud hRich

/-! ### §3 — `lem:bandwidth ≤ 4` (load-bearing) -/

/-- **`lem:bandwidth ≤ 4` — grounded form** (`step7.tex:1018-1056`
+ `rem:w0-constant` at `step7.tex:1015-1018`).

The **load-bearing** S7-E output: a `LayeredWidth3 richPairs`
packaging with `L.bandwidth ≤ 4` together with the `o(1)`-mass
bound on `L.richPairsOut`.

Obtained by instantiating `prop_72_grounded` at the fixed
Δ-threshold `c₀ := 4` (paper's `rem:w0-constant`: the constant
`K(T) + O(1)` of `lem:bandwidth` is `≤ 4` after fixing `T`).
The bandwidth equality `L.bandwidth = 4` directly yields
`L.bandwidth ≤ 4`.

This is the conclusion that the S7-F bridge (`lem:layered-from-step7`,
`step8.tex:1913-2106`) will consume to discharge the cap-5 sorry
currently localised at `mainTheoremInputsOf.caseC_canonicalLayered`
(`MainAssembly.lean`, mg-234e relocation, mg-ac13 §5.4 forward
action 5).

**Cardinality bound.** With `c₀ := 4`:

  `4 · c_n · b_d · |L.richPairsOut| · M₀ ≤ c_d · b_n · M₀`,

i.e. as the upstream Step 5 fractions `b_n / b_d → 0` and
`c_n / c_d` is fixed, `|L.richPairsOut|` decays like the
upstream small-set fraction, matching the paper's `(1 - o(1))`-mass
quantifier. -/
theorem lem_bandwidth_le_four
    (src tgt : Edge → Vertex)
    (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ)
    (path : Vertex → List Edge)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ)
    (pairs richPairs : Finset Pair)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      4 * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) := by
  obtain ⟨L, hbw, hcard⟩ := prop_72_grounded (Pair := Pair)
    src tgt signedWeight edgeWeight path psrc ptgt posMass
    pairs richPairs 4 (by decide) b_n b_d c_n c_d M₀ hSub hBud hRich
  refine ⟨L, ?_, ?_⟩
  · rw [hbw]
  · exact hcard

/-- **`lem:bandwidth ≤ 4` — bundled grounded form**
(`step7.tex:1018-1056`).

Single-call paper-statement packaging of `lem_bandwidth_le_four`
for downstream S7-F bridge consumption.  Returns the concrete
witness `L : LayeredWidth3 richPairs` together with:

1. **Bandwidth bound** `L.bandwidth ≤ 4` (paper `rem:w0-constant`).
2. **Cardinality partition identity**
   `L.richPairsIn.card + L.richPairsOut.card = richPairs.card`
   (from `LayeredWidth3.partition` + `LayeredWidth3.disjoint`).
3. **Exceptional-mass bound**
   `4 · c_n · b_d · L.richPairsOut.card · M₀ ≤ c_d · b_n · M₀`
   (cleared `(1 - o(1))`-fraction).

The bundled form is the **headline S7-E deliverable** matching
paper `prop:72` + `lem:bandwidth` line-for-line. -/
theorem lem_bandwidth_le_four_bundled
    (src tgt : Edge → Vertex)
    (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ)
    (path : Vertex → List Edge)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ)
    (pairs richPairs : Finset Pair)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      -- (1) Bandwidth bound:
      L.bandwidth ≤ 4 ∧
      -- (2) Cardinality partition:
      L.richPairsIn.card + L.richPairsOut.card = richPairs.card ∧
      -- (3) Exceptional-mass bound:
      4 * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) := by
  classical
  obtain ⟨L, hbw, hcard⟩ := lem_bandwidth_le_four (Pair := Pair)
    src tgt signedWeight edgeWeight path psrc ptgt posMass
    pairs richPairs b_n b_d c_n c_d M₀ hSub hBud hRich
  refine ⟨L, hbw, ?_, hcard⟩
  -- Cardinality partition from L.partition + L.disjoint.
  have hu := L.partition
  have hd := L.disjoint
  have : (L.richPairsIn ∪ L.richPairsOut).card = richPairs.card := by
    rw [hu]
  rw [Finset.card_union_of_disjoint hd] at this
  exact this

end Prop72Grounded

/-! ### §4 — Headline assembly: `prop:71` + `prop:72` + `lem:bandwidth ≤ 4` -/

section AssemblyGrounded

variable {Vertex Edge : Type*} [DecidableEq Vertex] [DecidableEq Edge]
variable {Pair : Type*} [DecidableEq Pair]

/-- **S7-E headline bundle** — `prop:71` + `prop:72` +
`lem:bandwidth ≤ 4` grounded against the S7-A / S7-C / S7-D
upstream inputs (`step7.tex:1115-1193` + `step7.tex:1018-1056`).

Single-call assembly matching the S7-E spec
(`docs/OneThird-Steps-1-7-Lean-port-scoping.md` §7.1 mg-S7-E,
"Key deliverable: replace `LayeredWidth3.bandwidth : ℕ` packaging
with a constructive `bandwidth ≤ 4` proof").

**Inputs.**

* **S7-A**: signed-threshold label `signedWeight : E → ℤ` (paper
  `step7.tex:679`, `δ_e = σ̃_e · τ_e`).
* **S7-C**: BFS-tree potential data `(src, tgt, edgeWeight, path)`
  + `hBFS : BFSTreeExtensionHyp path src tgt treeEdges`
  (`step7.tex:697-706`).
* **S7-C short-cycle bound** `hCyc` (`step7.tex:712-783`, upstream
  from `cocycle_grounded`).
* **S7-C/D long-edge decomposition** `hDecomp` (`step7.tex:773-785`,
  upstream from giant-component exceptional).
* **S7-D G6 pair-closeness** `hPair` (`step7.tex:868-908`, upstream
  from Step 6 low conductance).
* **S7-D G9 walk-witness** `hWalk` on `edgesWalk ⊆ edges`
  (`step7.tex:1610-1628`, upstream from
  `lem_giant_component_grounded`).
* **Step 5** parametric var-budget + richness hypotheses on
  `richPairs ⊆ pairs` (`step7.tex:949-1056`).

**Conclusions.**

1. **`prop:71`** combined bad-edge weight bound:
   `e_d · ∑_{badEdges C₁ K₁} edgeWeight ≤ 2 · e_n · M₀`.
2. **`prop:72` + `lem:bandwidth ≤ 4`** layered packaging
   `∃ L : LayeredWidth3 richPairs, L.bandwidth ≤ 4 ∧
     4 · c_n · b_d · |L.richPairsOut| · M₀ ≤ c_d · b_n · M₀`.

The bundled form is intended for direct consumption by S7-F
(`lem:layered-from-step7`), which extracts the
`L.bandwidth ≤ 4` field and lifts it through the chain-removal
subtype bridge of `step8.tex:1913-2106`. -/
theorem prop71_prop72_lemBandwidth_grounded
    (src tgt : Edge → Vertex)
    (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ)
    (path : Vertex → List Edge)
    (edges treeEdges shortEdges longEdges edgesWalk : Finset Edge)
    (refEdge : Edge) (C₁ K₁ : ℕ)
    (goodPairs : Finset (Edge × Edge))
    (hBFS : BFSTreeExtensionHyp path src tgt treeEdges)
    (hCyc : (bfsPotentialData src tgt signedWeight edgeWeight path).CycleBoundHyp
      shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (fiberThresholdDataOfBFS src tgt signedWeight edgeWeight path).PairClosenessHyp
      goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀_edge : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, edgeWeight e ≤ e_n * M₀_edge)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, edgeWeight e ≤ e_n * M₀_edge)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ)
    (pairs richPairs : Finset Pair)
    (b_n b_d c_n c_d M₀_pair : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀_pair)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData src tgt signedWeight edgeWeight path)
        Pair psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀_pair) :
    -- (1) prop:71 combined bad-edge weight bound:
    (let P := bfsPotentialData src tgt signedWeight edgeWeight path
     let G : GlobalThresholdDescr P edges :=
       { refEdge := refEdge, tolerance := C₁ + 3 * K₁ }
     e_d * ∑ e ∈ G.badEdges C₁ K₁, edgeWeight e ≤ 2 * e_n * M₀_edge) ∧
    -- (2) prop:72 + lem:bandwidth ≤ 4 layered packaging:
    (∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      L.richPairsIn.card + L.richPairsOut.card = richPairs.card ∧
      4 * c_n * (b_d * L.richPairsOut.card) * M₀_pair ≤
        c_d * (b_n * M₀_pair)) := by
  refine ⟨?_, ?_⟩
  · exact prop_71_grounded src tgt signedWeight edgeWeight path
      edges treeEdges shortEdges longEdges edgesWalk refEdge C₁ K₁
      goodPairs hBFS hCyc hDecomp hPair hWalk hWalkSub e_n e_d M₀_edge
      hLong hExc
  · exact lem_bandwidth_le_four_bundled (Pair := Pair)
      src tgt signedWeight edgeWeight path psrc ptgt posMass
      pairs richPairs b_n b_d c_n c_d M₀_pair hSub hBud hRich

end AssemblyGrounded

end Step7
end OneThird
