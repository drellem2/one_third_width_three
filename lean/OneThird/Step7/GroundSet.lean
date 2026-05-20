/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.Prop71_Prop72_LemBandwidth
import OneThird.Mathlib.BKGraph

/-!
# Step 7 — S7-A–E grounded forms concretised to the BK-graph ground set

This file is **piece 2 of the Option A' FULL REFACTOR**
(`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`, mg-d8c7 §2.2;
work item mg-4ce6).  It wires the *parametric* S7-A–E grounded
forms of `Step7/Prop71_Prop72_LemBandwidth.lean` (mg-516f) to the
**concrete ground set** of the headline theorem: a finite poset
`α` and its Bubley–Karzanov graph on `LinearExt α`.

## What "concretisation" means here

The S7-E grounded theorems (`lem_bandwidth_le_four`,
`lem_bandwidth_le_four_bundled`, `prop_72_grounded`,
`prop_71_grounded`, `prop71_prop72_lemBandwidth_grounded`) are
*parametric* over three carrier types — `Vertex`, `Edge`, `Pair` —
and over the data functions on them.  Downstream consumers (the
S7-F bridge of piece 3 and the `MainAssembly` refactor of piece 4)
need these forms at **concrete** carrier types so they can build a
`LayeredDecomposition α` on the ground set; a `LayeredWidth3`
packaging over an *abstract* `Pair` cannot be converted into a
ground-set `LayeredDecomposition α`.

This file fixes the three carrier types:

* `Vertex := BKVertex α := LinearExt α` — vertices of the BK graph;
* `Edge   := BKEdge α` — directed edges of the BK graph
  (`BKAdj`-adjacent ordered pairs of linear extensions);
* `Pair   := α × α` — the ambient ground-set pair space (the rich
  incomparable pairs `(a_i, b_j)` of the paper's interface live in
  `A × B ⊆ α × α`, where `A, B` come from the Step 5 Dilworth
  decomposition `X = A ⊔ B ⊔ C`).

and re-exports every S7-E deliverable at those types.  The
load-bearing output is `lem_bandwidth_le_four_bundled_groundSet`:
a `LayeredWidth3 (richPairs : Finset (α × α))` with
`bandwidth ≤ 4` — a *concrete* object the S7-F bridge can consume.

## What stays parametric — and why (no 8th vacuity-discovery)

The **data** carried on the BK graph stays parametric:
`signedWeight` (the S7-A signed-threshold label `δ_e`), `path`
(the S7-C BFS spanning tree), `posMass`, `psrc`, `ptgt`, the
rich-pair finset `richPairs`, the budget/richness constants
`b_n, b_d, c_n, c_d, M₀`, and the variational-budget /
richness hypotheses `hBud`, `hRich`.

This is **deliberate and honest**, not a gap.  Per the parent
scoping doc §2.2 + §7.3, those numerical constants and the
`VarBudgetHyp` / `RichnessHyp` *proofs* are the output of the
Steps 5–6 grounded forms — **piece 1** of the refactor, which is
not yet in tree (`Step5/`, `Step6/` ship only abstract
cleared-denominator scaffolding; no grounded constant extractors).
Concretising the *carrier types* while threading the Steps 5–6
outputs as *hypotheses* is exactly the form that lets piece 2 run
**in parallel with piece 1** (ticket mg-4ce6 "Parallelizes with
P1"): piece 1 later discharges `hBud` / `hRich`; piece 2 (this
file) commits the graph structure.

A skeptical re-audit against `PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #2's three checks:

1. *Satisfiability.* The concretised theorems are pure
   instantiations of the S7-E forms; the conclusion `∃ L, …` is
   constructed explicitly by `prop_72`.  Not vacuous.
2. *Discharge-coverage.* This file claims **no** discharge of
   `hBud` / `hRich`; they remain hypotheses.  No artefact is
   cited as discharging them.  No over-claim.
3. *Universal-quantifier truthfulness.* The `∃ L : LayeredWidth3
   richPairs` conclusion is witnessed concretely by `prop_72`; no
   false universal is introduced.

## Cross-references

* `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean` (mg-516f) —
  the parametric S7-E grounded forms re-exported here.
* `lean/OneThird/Step7/Bandwidth.lean` — `BandwidthData`,
  `BandwidthData.ofPotential`, `VarBudgetHyp`, `RichnessHyp`.
* `lean/OneThird/Step7/Assembly.lean` — `LayeredWidth3`,
  `GlobalThresholdDescr`.
* `lean/OneThird/Mathlib/BKGraph.lean` — `bkGraph`, `BKAdj`.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2 (mg-d8c7)
  — piece 2 spec.
* `docs/state-S7-Conc-Session1.md` (mg-4ce6) — this session's
  state doc.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Concrete BK-graph carrier types -/

/-- **Vertices of the ground-set BK graph**: linear extensions of `α`.

This is the concrete `Vertex` carrier the parametric S7 grounded
forms are instantiated at. -/
abbrev BKVertex (α : Type*) [PartialOrder α] [Fintype α] : Type _ :=
  LinearExt α

/-- **Directed edges of the ground-set BK graph**: an ordered pair
of `BKAdj`-adjacent linear extensions of `α`.

This is the concrete `Edge` carrier the parametric S7 grounded
forms are instantiated at.  The `isAdj` field records that the
edge is genuinely an edge of `bkGraph α` (see `BKEdge.bkGraph_adj`). -/
structure BKEdge (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] where
  /-- Source endpoint `x` of the directed edge `e = (x, y)`. -/
  src : BKVertex α
  /-- Target endpoint `y` of the directed edge `e = (x, y)`. -/
  tgt : BKVertex α
  /-- The endpoints are BK-adjacent. -/
  isAdj : BKAdj src tgt

/-- `BKEdge α` has decidable equality: two directed edges are equal
iff their endpoints agree (the `isAdj` field is proof-irrelevant). -/
instance : DecidableEq (BKEdge α) := fun e₁ e₂ =>
  decidable_of_iff (e₁.src = e₂.src ∧ e₁.tgt = e₂.tgt) <| by
    constructor
    · rintro ⟨h₁, h₂⟩
      cases e₁; cases e₂
      cases h₁; cases h₂; rfl
    · rintro rfl
      exact ⟨rfl, rfl⟩

/-- A `BKEdge` is genuinely an edge of `bkGraph α`: its two
endpoints are adjacent in the Bubley–Karzanov graph. -/
lemma BKEdge.bkGraph_adj (e : BKEdge α) :
    (bkGraph α).Adj e.src e.tgt :=
  e.isAdj

namespace Step7

open Finset
open scoped BigOperators

/-! ### §2 — `prop:72` concretised to the BK-graph ground set -/

/-- **`prop:72` grounded — concretised to the BK-graph ground set**
(`step7.tex:1175-1193`).

The S7-E `prop_72_grounded` instantiated at
`Vertex := BKVertex α`, `Edge := BKEdge α`, `Pair := α × α`, with
the structural endpoint maps fixed to the `BKEdge` projections
`BKEdge.src`, `BKEdge.tgt`.

The S7-A `signedWeight`, S7-C `path`, the chain-position
projections `psrc`/`ptgt`, the BK-adjacency mass `posMass`, the
rich-pair finset `richPairs ⊆ pairs ⊆ α × α`, and the Step 5/6
budget/richness data `(b_n, b_d, c_n, c_d, M₀, hBud, hRich)`
remain parametric — they are supplied by pieces 1 + 3 of the
refactor.  See the module docstring for why this is the honest
concretisation form. -/
theorem prop_72_groundSet
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (psrc ptgt : α × α → BKVertex α) (posMass : α × α → ℕ)
    (pairs richPairs : Finset (α × α)) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth = c₀ ∧
      c₀ * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) :=
  prop_72_grounded (Vertex := BKVertex α) (Edge := BKEdge α)
    (Pair := α × α)
    BKEdge.src BKEdge.tgt signedWeight edgeWeight path
    psrc ptgt posMass pairs richPairs c₀ hc₀ b_n b_d c_n c_d M₀
    hSub hBud hRich

/-! ### §3 — `lem:bandwidth ≤ 4` (load-bearing) concretised -/

/-- **`lem:bandwidth ≤ 4` grounded — concretised to the BK-graph
ground set** (`step7.tex:1018-1056` + `rem:w0-constant`).

The S7-E `lem_bandwidth_le_four` instantiated at the concrete
ground-set carrier types.  Produces a `LayeredWidth3` packaging on
the concrete rich-pair finset `richPairs : Finset (α × α)` with
`L.bandwidth ≤ 4`. -/
theorem lem_bandwidth_le_four_groundSet
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (psrc ptgt : α × α → BKVertex α) (posMass : α × α → ℕ)
    (pairs richPairs : Finset (α × α))
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      4 * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) :=
  lem_bandwidth_le_four (Vertex := BKVertex α) (Edge := BKEdge α)
    (Pair := α × α)
    BKEdge.src BKEdge.tgt signedWeight edgeWeight path
    psrc ptgt posMass pairs richPairs b_n b_d c_n c_d M₀
    hSub hBud hRich

/-- **`lem:bandwidth ≤ 4` bundled — concretised to the BK-graph
ground set** (`step7.tex:1018-1056`).

The **load-bearing piece-2 deliverable**: the S7-E
`lem_bandwidth_le_four_bundled` instantiated at the concrete
ground-set carrier types.  Returns a concrete witness
`L : LayeredWidth3 (richPairs : Finset (α × α))` together with:

1. **Bandwidth bound** `L.bandwidth ≤ 4` (paper `rem:w0-constant`).
2. **Cardinality partition identity**
   `L.richPairsIn.card + L.richPairsOut.card = richPairs.card`.
3. **Exceptional-mass bound**
   `4 · c_n · b_d · L.richPairsOut.card · M₀ ≤ c_d · b_n · M₀`.

This is the concrete object the S7-F bridge (piece 3,
`lem:layered-from-step7`) consumes to build a
`LayeredDecomposition α` with `w ≤ 4`. -/
theorem lem_bandwidth_le_four_bundled_groundSet
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (psrc ptgt : α × α → BKVertex α) (posMass : α × α → ℕ)
    (pairs richPairs : Finset (α × α))
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).VarBudgetHyp pairs b_n b_d M₀)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      L.richPairsIn.card + L.richPairsOut.card = richPairs.card ∧
      4 * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) :=
  lem_bandwidth_le_four_bundled (Vertex := BKVertex α)
    (Edge := BKEdge α) (Pair := α × α)
    BKEdge.src BKEdge.tgt signedWeight edgeWeight path
    psrc ptgt posMass pairs richPairs b_n b_d c_n c_d M₀
    hSub hBud hRich

/-! ### §4 — `prop:71` concretised to the BK-graph ground set -/

/-- **`prop:71` grounded — concretised to the BK-graph ground set**
(`step7.tex:1115-1173`).

The S7-E `prop_71_grounded` instantiated at the concrete
ground-set carrier types.  The combined bad-edge weight on the
concrete BK edge set is bounded by `2 · (e_n / e_d) · M₀`. -/
theorem prop_71_groundSet
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (edges treeEdges shortEdges longEdges edgesWalk :
      Finset (BKEdge α))
    (refEdge : BKEdge α) (C₁ K₁ : ℕ)
    (goodPairs : Finset (BKEdge α × BKEdge α))
    (hBFS : BFSTreeExtensionHyp path BKEdge.src BKEdge.tgt treeEdges)
    (hCyc : (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
        edgeWeight path).CycleBoundHyp shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (fiberThresholdDataOfBFS BKEdge.src BKEdge.tgt
        signedWeight edgeWeight path).PairClosenessHyp goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk
      goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, edgeWeight e ≤ e_n * M₀) :
    let P := bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
      edgeWeight path
    let G : GlobalThresholdDescr P edges :=
      { refEdge := refEdge, tolerance := C₁ + 3 * K₁ }
    e_d * ∑ e ∈ G.badEdges C₁ K₁, edgeWeight e ≤ 2 * e_n * M₀ :=
  prop_71_grounded (Vertex := BKVertex α) (Edge := BKEdge α)
    BKEdge.src BKEdge.tgt signedWeight edgeWeight path
    edges treeEdges shortEdges longEdges edgesWalk refEdge C₁ K₁
    goodPairs hBFS hCyc hDecomp hPair hWalk hWalkSub e_n e_d M₀
    hLong hExc

/-! ### §5 — S7-E headline assembly concretised -/

/-- **S7-E headline bundle — concretised to the BK-graph ground
set** (`step7.tex:1115-1193` + `step7.tex:1018-1056`).

The S7-E `prop71_prop72_lemBandwidth_grounded` instantiated at the
concrete ground-set carrier types: both `prop:71`'s combined
bad-edge weight bound and `prop:72` + `lem:bandwidth ≤ 4`'s
layered packaging, in one call.  This is the single-call S7-E
surface for the piece-4 `MainAssembly` refactor. -/
theorem prop71_prop72_lemBandwidth_groundSet
    (signedWeight : BKEdge α → ℤ) (edgeWeight : BKEdge α → ℕ)
    (path : BKVertex α → List (BKEdge α))
    (edges treeEdges shortEdges longEdges edgesWalk :
      Finset (BKEdge α))
    (refEdge : BKEdge α) (C₁ K₁ : ℕ)
    (goodPairs : Finset (BKEdge α × BKEdge α))
    (hBFS : BFSTreeExtensionHyp path BKEdge.src BKEdge.tgt treeEdges)
    (hCyc : (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
        edgeWeight path).CycleBoundHyp shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (fiberThresholdDataOfBFS BKEdge.src BKEdge.tgt
        signedWeight edgeWeight path).PairClosenessHyp goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk
      goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀_edge : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, edgeWeight e ≤ e_n * M₀_edge)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, edgeWeight e ≤
      e_n * M₀_edge)
    (psrc ptgt : α × α → BKVertex α) (posMass : α × α → ℕ)
    (pairs richPairs : Finset (α × α))
    (b_n b_d c_n c_d M₀_pair : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).VarBudgetHyp pairs b_n b_d
          M₀_pair)
    (hRich : (BandwidthData.ofPotential
        (bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
          edgeWeight path)
        (α × α) psrc ptgt posMass).RichnessHyp richPairs c_n c_d
          M₀_pair) :
    (let P := bfsPotentialData BKEdge.src BKEdge.tgt signedWeight
        edgeWeight path
     let G : GlobalThresholdDescr P edges :=
       { refEdge := refEdge, tolerance := C₁ + 3 * K₁ }
     e_d * ∑ e ∈ G.badEdges C₁ K₁, edgeWeight e ≤
       2 * e_n * M₀_edge) ∧
    (∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧
      L.richPairsIn.card + L.richPairsOut.card = richPairs.card ∧
      4 * c_n * (b_d * L.richPairsOut.card) * M₀_pair ≤
        c_d * (b_n * M₀_pair)) :=
  prop71_prop72_lemBandwidth_grounded (Vertex := BKVertex α)
    (Edge := BKEdge α) (Pair := α × α)
    BKEdge.src BKEdge.tgt signedWeight edgeWeight path
    edges treeEdges shortEdges longEdges edgesWalk refEdge C₁ K₁
    goodPairs hBFS hCyc hDecomp hPair hWalk hWalkSub
    e_n e_d M₀_edge hLong hExc
    psrc ptgt posMass pairs richPairs b_n b_d c_n c_d M₀_pair
    hSub hBud hRich

end Step7
end OneThird
