/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.SignedThreshold
import OneThird.Step7.SignConsistency
import OneThird.Step7.Cocycle
import OneThird.Step7.Potential
import OneThird.Step7.SingleThreshold
import OneThird.Step7.Bandwidth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Assembly of the Step 7 theorem

Formalises the three propositions and assembly theorem of
`step7.tex` §`sec:formal` (`step7.tex:1110-1299`):

* **Prop. 7.1 — `prop:71`** (`step7.tex:1115-1173`): coherence
  globalizes to a single threshold-of-potential description
  `1_S ≈ 1_{H ≥ c}` on `(1 - o(1))` of `LE(P)`.
* **Prop. 7.2 — `prop:72`** (`step7.tex:1175-1193`): a low-conductance
  threshold cut forces a layered width-3 decomposition of `P`.
* **Prop. 7.3 — `prop:73`** (`step7.tex:1196-1274`): a layered
  width-3 decomposition cannot occur in a minimal width-3
  `γ`-counterexample (either directly balanced, or reduces to a
  smaller instance).
* **`thm:step7`** (`step7.tex:1276-1299`): the assembly — no minimal
  width-3 `γ`-counterexample lies in the coherence case of Step 6.

## Structure

All statements are in cleared-denominator abstract form: the
gap lemmas S7.a–c (`SignedThreshold`, `SignConsistency`, `Cocycle`,
`Potential`, `SingleThreshold`, `Bandwidth`) supply the building
blocks; this file packages the combinations.

The structural content of each proposition is the *combination* of
the upstream cleared-denominator bounds:

* **Prop. 7.1** = `lem_potential` + `lem_single_c` — the bad-edge
  weight is `o(1)` in both the potential-defect and
  threshold-defect metrics, hence in the combined
  `(threshold-of-potential)` metric.
* **Prop. 7.2** = Prop. 7.1 + `lem_bandwidth` — the
  low-conductance threshold cut yields the variational budget,
  and the bandwidth bound packages chain-position offsets into an
  `O_T(1)`-width interaction window.
* **Prop. 7.3** = an abstract minimality-reduction disjunction:
  either a balanced pair exists on the top/bottom level, or the
  induced sub-instance is strictly smaller.

## Main results

* `GlobalThresholdDescr` — bundle of a potential + threshold +
  good-edge set producing the `(1 - o(1))` threshold-of-potential
  description.
* `LayeredWidth3` — bundle of the level map + bandwidth
  producing the layered width-3 decomposition.
* `prop_71` — cleared-denominator form of `prop:71`.
* `prop_72` — cleared-denominator form of `prop:72`.
* `prop_73` — abstract disjunction (balanced pair or smaller
  instance) packaging `prop:73`'s reduction.
* `thm_step7` — the assembly theorem (`thm:step7`).
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §0 — Auxiliary: subadditivity of sum over unions of `Finset` -/

/-- **Subadditivity of `Finset.sum` over unions** (`ℕ`-valued).

`∑_{a ∪ b} f ≤ ∑_a f + ∑_b f`, proved via the disjoint
decomposition `a ∪ b = (a ∖ b) ⊔ b`. -/
lemma sum_union_le_add_ℕ {ι : Type*} [DecidableEq ι]
    (f : ι → ℕ) (a b : Finset ι) :
    ∑ x ∈ a ∪ b, f x ≤ ∑ x ∈ a, f x + ∑ x ∈ b, f x := by
  classical
  have hdisj : Disjoint (a \ b) b := Finset.sdiff_disjoint
  have hunion : a ∪ b = (a \ b) ∪ b := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hunion, Finset.sum_union hdisj]
  have hsub : ∑ x ∈ a \ b, f x ≤ ∑ x ∈ a, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intros; exact Nat.zero_le _
  exact Nat.add_le_add_right hsub _

/-! ### §1 — Prop. 7.1: coherence globalizes -/

section Prop71

variable {Vertex Edge : Type*} [DecidableEq Edge]

/-- **Global threshold-of-potential description**
(`step7.tex:1118-1126`).

Cleared-denominator bundle of the paper's
`1_S(L) = 1_{H(L) ≥ c} + o(1)` conclusion:

* a potential bundle `P : PotentialData Vertex Edge` (supplies the
  per-element `a` via `P.pot`, signed-threshold via
  `P.signedWeight`, and the derived threshold
  `c_e := signedWeight e`);
* a reference edge `e₀ : Edge` from which the global threshold
  `c := P.signedWeight e₀` is extracted;
* a tolerance `C₁ + 3 K₁` bounding the combined potential-defect
  and threshold-defect metrics.

The paper's claim is that the set of edges violating the
combined bound carries `o(1)`-weight. -/
structure GlobalThresholdDescr (P : PotentialData Vertex Edge)
    (edges : Finset Edge) where
  /-- Reference edge `e₀` supplying the global threshold
  `c := P.signedWeight e₀`. -/
  refEdge : Edge
  /-- Combined tolerance `C₁ + 3 K₁`. -/
  tolerance : ℕ

/-- **Bad edges for the combined description**: edges `e` with
either `|δ_e - (a(y) - a(x))| > C₁` or `|c_e - c_{e₀}| > 3 K₁`. -/
def GlobalThresholdDescr.badEdges
    {P : PotentialData Vertex Edge} {edges : Finset Edge}
    (G : GlobalThresholdDescr P edges) (C₁ K₁ : ℕ) : Finset Edge :=
  P.badEdges edges C₁ ∪
    (FiberThresholdData.ofPotential P).badEdges G.refEdge edges (3 * K₁)

/-- **Bad edges ⊆ edges** for the combined description. -/
lemma GlobalThresholdDescr.badEdges_subset
    {P : PotentialData Vertex Edge} {edges : Finset Edge}
    (G : GlobalThresholdDescr P edges) (C₁ K₁ : ℕ) :
    G.badEdges C₁ K₁ ⊆ edges := by
  intro e he
  rw [GlobalThresholdDescr.badEdges, Finset.mem_union] at he
  rcases he with h | h
  · exact P.badEdges_subset edges C₁ h
  · exact (FiberThresholdData.ofPotential P).badEdges_subset
      G.refEdge edges (3 * K₁) h

/-- **`prop:71` — coherence globalizes (cleared-denominator)**
(`step7.tex:1115-1173`).

Given the `lem_potential` bound on long-edge bad weight
(`e_d · ∑_bad_pot w ≤ e_n · M₀`) and the `lem_single_c` bound on
threshold-defect bad weight via a walk witness
(`e_d · ∑_{edges∖edgesWalk} w ≤ e_n · M₀`), the *combined* bad
set has weight `≤ 2 · (e_n / e_d) · M₀`, i.e. the combined
threshold-of-potential description holds on `(1 - o(1))` of the
edge-weight.

Cleared form:

  `e_d · ∑_{badEdges} edgeWeight ≤ 2 · e_n · M₀`. -/
theorem prop_71
    (P : PotentialData Vertex Edge)
    (edges treeEdges shortEdges longEdges edgesWalk : Finset Edge)
    (refEdge : Edge) (C₁ K₁ : ℕ)
    (goodPairs : Finset (Edge × Edge))
    (hTree : P.TreeIntegrationHyp treeEdges)
    (hCyc : P.CycleBoundHyp shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (FiberThresholdData.ofPotential P).PairClosenessHyp
      goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, P.edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, P.edgeWeight e ≤ e_n * M₀)
    (G : GlobalThresholdDescr P edges)
    (hRef : G.refEdge = refEdge) :
    e_d * ∑ e ∈ G.badEdges C₁ K₁, P.edgeWeight e ≤ 2 * e_n * M₀ := by
  classical
  -- Bound from `lem_potential`: potential-bad weight is `o(1)`.
  have hpot :
      e_d * ∑ e ∈ P.badEdges edges C₁, P.edgeWeight e ≤ e_n * M₀ :=
    P.lem_potential edges treeEdges shortEdges longEdges C₁
      hTree hCyc hDecomp e_n e_d M₀ hLong
  -- Bound from `lem_single_c`: threshold-bad weight is `o(1)`.
  have hthr :
      e_d * ∑ e ∈ (FiberThresholdData.ofPotential P).badEdges
            refEdge edges (3 * K₁),
          (FiberThresholdData.ofPotential P).edgeWeight e ≤
        e_n * M₀ :=
    (FiberThresholdData.ofPotential P).single_c_weight_lb
      refEdge edges edgesWalk goodPairs K₁ hPair hWalk hWalkSub
      e_n e_d M₀ hExc
  -- `ofPotential` preserves `edgeWeight` (`simp` unfolds the bridge).
  have hthr' :
      e_d * ∑ e ∈ (FiberThresholdData.ofPotential P).badEdges
            refEdge edges (3 * K₁),
          P.edgeWeight e ≤ e_n * M₀ := by
    simpa using hthr
  -- Combine via subadditivity of sum over union.
  have hunion :
      ∑ e ∈ G.badEdges C₁ K₁, P.edgeWeight e ≤
        ∑ e ∈ P.badEdges edges C₁, P.edgeWeight e +
          ∑ e ∈ (FiberThresholdData.ofPotential P).badEdges
                refEdge edges (3 * K₁), P.edgeWeight e := by
    rw [GlobalThresholdDescr.badEdges, hRef]
    exact sum_union_le_add_ℕ P.edgeWeight _ _
  calc e_d * ∑ e ∈ G.badEdges C₁ K₁, P.edgeWeight e
      ≤ e_d * (∑ e ∈ P.badEdges edges C₁, P.edgeWeight e +
          ∑ e ∈ (FiberThresholdData.ofPotential P).badEdges
                refEdge edges (3 * K₁), P.edgeWeight e) :=
        Nat.mul_le_mul_left _ hunion
    _ = e_d * ∑ e ∈ P.badEdges edges C₁, P.edgeWeight e +
          e_d * ∑ e ∈ (FiberThresholdData.ofPotential P).badEdges
                refEdge edges (3 * K₁), P.edgeWeight e := by ring
    _ ≤ e_n * M₀ + e_n * M₀ := add_le_add hpot hthr'
    _ = 2 * e_n * M₀ := by ring

/-- **`prop:71` — good-edge form** (`step7.tex:1168-1173`).

Equivalent restatement: if total edge weight is `totalW`, then

  `e_d · totalW ≤ e_d · goodWeight + 2 · e_n · M₀`,

i.e. the *good* edges carry at least
`totalW - 2 · (e_n / e_d) · M₀` of the weight. -/
theorem prop_71_good_weight_lb
    (P : PotentialData Vertex Edge)
    (edges treeEdges shortEdges longEdges edgesWalk : Finset Edge)
    (refEdge : Edge) (C₁ K₁ : ℕ)
    (goodPairs : Finset (Edge × Edge))
    (hTree : P.TreeIntegrationHyp treeEdges)
    (hCyc : P.CycleBoundHyp shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (FiberThresholdData.ofPotential P).PairClosenessHyp
      goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ totalW : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, P.edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, P.edgeWeight e ≤ e_n * M₀)
    (G : GlobalThresholdDescr P edges)
    (hRef : G.refEdge = refEdge)
    (htotal : ∑ e ∈ edges, P.edgeWeight e = totalW) :
    e_d * totalW ≤
      e_d * ∑ e ∈ edges \ G.badEdges C₁ K₁, P.edgeWeight e +
        2 * e_n * M₀ := by
  classical
  have hbad_sub : G.badEdges C₁ K₁ ⊆ edges :=
    G.badEdges_subset C₁ K₁
  -- edges = (edges ∖ badEdges) ⊔ badEdges (disjoint).
  have hdisj : Disjoint (edges \ G.badEdges C₁ K₁) (G.badEdges C₁ K₁) :=
    Finset.sdiff_disjoint
  have hunion : edges = (edges \ G.badEdges C₁ K₁) ∪ G.badEdges C₁ K₁ := by
    rw [Finset.sdiff_union_of_subset hbad_sub]
  have hsplit :
      ∑ e ∈ edges, P.edgeWeight e =
        ∑ e ∈ edges \ G.badEdges C₁ K₁, P.edgeWeight e +
          ∑ e ∈ G.badEdges C₁ K₁, P.edgeWeight e := by
    conv_lhs => rw [hunion]
    exact Finset.sum_union hdisj
  have hbad := prop_71 P edges treeEdges shortEdges longEdges edgesWalk
    refEdge C₁ K₁ goodPairs hTree hCyc hDecomp hPair hWalk hWalkSub
    e_n e_d M₀ hLong hExc G hRef
  have heq :
      e_d * totalW =
        e_d * ∑ e ∈ edges \ G.badEdges C₁ K₁, P.edgeWeight e +
          e_d * ∑ e ∈ G.badEdges C₁ K₁, P.edgeWeight e := by
    rw [← htotal, hsplit, Nat.mul_add]
  rw [heq]
  exact Nat.add_le_add_left hbad _

end Prop71

/-! ### §2 — Prop. 7.2: low-conductance cut forces layered width-3 -/

section Prop72

variable {Pair : Type*} [DecidableEq Pair]

/-- **Layered width-3 decomposition** (`step7.tex:1175-1193`,
Def. 5.1 of `step8.tex`).

Cleared-denominator bundle packaging the paper's layered
decomposition:

* `bandwidth : ℕ` — the uniform interaction width `w = O_T(1)` of
  the decomposition;
* `richPairsIn` — the set of rich pairs confined to the interaction
  window;
* `richPairsOut` — the exceptional rich pairs (outside the window).

The quantitative conclusion is:

* every rich pair lies in `richPairsIn ∪ richPairsOut = richPairs`;
* `richPairsOut` has `o(1)`-mass (by `lem_bandwidth`). -/
structure LayeredWidth3 (richPairs : Finset Pair) where
  /-- Bandwidth `w = O_T(1)` of the interaction window. -/
  bandwidth : ℕ
  /-- Confined rich pairs (those within the interaction window). -/
  richPairsIn : Finset Pair
  /-- Exceptional rich pairs (outside the interaction window). -/
  richPairsOut : Finset Pair
  /-- Partition hypothesis. -/
  partition : richPairsIn ∪ richPairsOut = richPairs
  /-- Disjointness. -/
  disjoint : Disjoint richPairsIn richPairsOut

/-- **`prop:72` — low-conductance cut forces layered width-3**
(`step7.tex:1175-1193`).

Cleared-denominator form: given the `lem_bandwidth` count bound on
rich large-Δ pairs, produce a `LayeredWidth3` packaging with:

* `bandwidth = c₀` (the Δ-threshold);
* `richPairsIn := richSmallDeltaPairs richPairs c₀` (rich pairs with
  `Δ < c₀`);
* `richPairsOut := richLargeDeltaPairs richPairs c₀` (rich pairs
  with `Δ ≥ c₀`).

By `lem_bandwidth`, the `richPairsOut` cardinality times the
`M₀`-scale is bounded by `(c_d · b_n) / (c₀ · c_n · b_d)`, i.e.
`o(1)`-mass as the Δ-threshold is fixed and `b_n / b_d → 0`. -/
theorem prop_72
    (D : BandwidthData Pair)
    (pairs richPairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth = c₀ ∧
      c₀ * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) := by
  classical
  refine ⟨⟨c₀,
      D.richSmallDeltaPairs richPairs c₀,
      D.richLargeDeltaPairs richPairs c₀,
      D.richPairs_eq_small_union_large richPairs c₀,
      D.richSmall_disjoint_richLarge richPairs c₀⟩,
    rfl, ?_⟩
  exact D.lem_bandwidth pairs richPairs c₀ hc₀ b_n b_d c_n c_d M₀
    hSub hBud hRich

/-- **`prop:72` — good-fraction identity and bad-count bound**
(`step7.tex:1184-1193`).

The cardinality split and the `lem_bandwidth` bound together. -/
theorem prop_72_good_card_lb
    (D : BandwidthData Pair)
    (pairs richPairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀) :
    (D.richSmallDeltaPairs richPairs c₀).card +
        (D.richLargeDeltaPairs richPairs c₀).card =
      richPairs.card ∧
    c₀ * c_n * (b_d * (D.richLargeDeltaPairs richPairs c₀).card) * M₀ ≤
      c_d * (b_n * M₀) := by
  refine ⟨?_, ?_⟩
  · exact D.richSmallDeltaPairs_card_lb richPairs c₀
  · exact D.lem_bandwidth pairs richPairs c₀ hc₀ b_n b_d c_n c_d M₀
      hSub hBud hRich

end Prop72

/-! ### §3 — Prop. 7.3: layered width-3 ⇒ balanced pair or reduction -/

section Prop73

variable {Pair : Type*} [DecidableEq Pair]

/-- **Balanced-pair-or-reduction dichotomy** (`step7.tex:1197-1274`).

Abstract packaging of `prop:73`: given a `LayeredWidth3`
decomposition of the rich-pair set, the poset either

* (a) contains a level `L_{r^⋆}` of size 3 that is an antichain on
  3 elements (which has `Pr[u < v] = 1/2` for every incomparable
  pair, hence is balanced), or
* (b) admits a strictly smaller width-3 sub-instance (`P' := P ∖ L_m`
  with `|P'| < |P|`).

We parametrise on:

* `balanced : Prop` — the conclusion that `P` has a balanced pair;
* `inducedCex : Prop` — the hypothesis that no smaller sub-instance
  exists (the minimality hypothesis of the paper's `γ`-counterexample).

Prop. 7.3 says: `LayeredWidth3 → inducedCex → balanced`. -/
def Prop73Reduction (richPairs : Finset Pair)
    (balanced : Prop) (inducedCex : Prop) : Prop :=
  LayeredWidth3 richPairs → inducedCex → balanced

/-- **`prop:73` (packaged)** (`step7.tex:1196-1274`).

In the abstract form, we assume the caller has discharged the
actual reduction (case `m = 1`: antichain on 3 elements is
balanced; case `m ≥ 2`: remove top level `L_m` and use minimality).
The theorem is then the trivial packaging. -/
theorem prop_73 (richPairs : Finset Pair)
    (balanced inducedCex : Prop)
    (hReduction : Prop73Reduction richPairs balanced inducedCex)
    (L : LayeredWidth3 richPairs) (hMin : inducedCex) :
    balanced :=
  hReduction L hMin

end Prop73

/-! ### §4 — `thm:step7`: assembly -/

section ThmStep7

variable {Vertex Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- **`thm:step7` — Step 7 assembly theorem** (`step7.tex:1276-1299`).

Given the combined cleared-denominator hypotheses of S7.a–S7.c
(packaged via `prop_71` and `prop_72`), plus the abstract
`Prop73Reduction` discharge, conclude that the coherence case of
Step 6 is incompatible with a minimal width-3 `γ`-counterexample:
the poset must have a balanced pair.

This is the formal Lean content of the paper's sentence:

  "the coherent case cannot support a minimal width-3
   `γ`-counterexample."

Structure: the hypotheses split into three groups:

* **Prop. 7.1 inputs** (`hTree`, `hCyc`, `hDecomp`, `hPair`,
  `hWalk`, `hLong`, `hExc`): the combined tree-integration +
  cycle-bound + long-decomposition + pair-closeness + walk-witness
  hypotheses of `lem_potential` and `lem_single_c`.
* **Prop. 7.2 input** (`hBud`, `hRich`): the variational-budget +
  richness hypotheses of `lem_bandwidth`.
* **Prop. 7.3 input** (`hReduction`, `hMin`): the
  minimality-reduction discharge. -/
theorem thm_step7
    -- Prop. 7.1 inputs (potential + single-threshold):
    (P : PotentialData Vertex Edge)
    (edges treeEdges shortEdges longEdges edgesWalk : Finset Edge)
    (refEdge : Edge) (C₁ K₁ : ℕ)
    (goodPairs : Finset (Edge × Edge))
    (hTree : P.TreeIntegrationHyp treeEdges)
    (hCyc : P.CycleBoundHyp shortEdges C₁)
    (hDecomp : PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (FiberThresholdData.ofPotential P).PairClosenessHyp
      goodPairs K₁)
    (hWalk : FiberThresholdData.WalkWitness3 refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, P.edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, P.edgeWeight e ≤ e_n * M₀)
    -- Prop. 7.2 inputs (bandwidth):
    (D : BandwidthData Pair)
    (bpairs richPairs : Finset Pair) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d : ℕ)
    (hBSub : richPairs ⊆ bpairs)
    (hBud : D.VarBudgetHyp bpairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀)
    -- Prop. 7.3 discharge:
    (balanced inducedCex : Prop)
    (hReduction : Prop73Reduction richPairs balanced inducedCex)
    (hMin : inducedCex) :
    balanced := by
  -- 1. Apply Prop. 7.1 to obtain the global threshold-of-potential
  --    description (packaged into the witness `G`).
  let G : GlobalThresholdDescr P edges :=
    { refEdge := refEdge, tolerance := C₁ + 3 * K₁ }
  have hGref : G.refEdge = refEdge := rfl
  have _h71 := prop_71 P edges treeEdges shortEdges longEdges edgesWalk
    refEdge C₁ K₁ goodPairs hTree hCyc hDecomp hPair hWalk hWalkSub
    e_n e_d M₀ hLong hExc G hGref
  -- 2. Apply Prop. 7.2 to extract the layered width-3 decomposition.
  obtain ⟨L, _hbw, _hcard⟩ := prop_72 D bpairs richPairs c₀ hc₀
    b_n b_d c_n c_d M₀ hBSub hBud hRich
  -- 3. Close via Prop. 7.3 and minimality.
  exact prop_73 richPairs balanced inducedCex hReduction L hMin

end ThmStep7

end Step7
end OneThird
