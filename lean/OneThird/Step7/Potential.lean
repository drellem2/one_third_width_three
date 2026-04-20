/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.SignedThreshold
import OneThird.Step7.SignConsistency
import OneThird.Step7.Cocycle
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Vertex potential from the threshold cocycle (`lem:potential`)

This file formalises `lem:potential` of `step7.tex` §`sec:potential`
(`step7.tex:654-792`, `lem:potential` at `step7.tex:657`), the
*cocycle-to-potential* upgrade of Step 7.  It consumes the cocycle
output of S7.b (`lem:cocycle`) together with the signed thresholds
from S7.a, and produces a function `a : P → ℤ` such that, on a
`(1 - o(1))`-fraction of interfaces `e = (x, y) ∈ E⋆`,

  `σ̃_e · τ_e = a(y) - a(x) + O(1)`.

## Paper statement (`step7.tex:657-667`)

Assume `lem:sign-consistency` (S7.a) and `lem:cocycle` (S7.b) on
`E⋆` with a giant component of the triple graph.  There exists
`a : P → ℝ` such that for a `(1 - o(1))`-fraction of interfaces
`e = (x, y) ∈ E⋆`,

  `σ̃_e · τ_e = a(y) - a(x) + O(1)`.

## Proof outline (`step7.tex:669-792`)

1. **Element graph `G^P`.** Fix a weighted element graph on `P` with
   one edge per interface in `E⋆` and signed edge labels
   `δ_e := σ̃_e · τ_e`.  Restrict to the giant component `G^P_⋆⋆`
   after trimming the `B ⊂ E` of edges incident to `ω(1)`-weight
   of bad triples (`step7.tex:689-696`).

2. **Spanning-tree integration** (`step7.tex:698-710`).  Fix a base
   point `z₀` and a BFS tree `T`.  Define

     `a(z) := ∑_{e ∈ path_T(z₀ → z)} δ_e`,

   so `a(y) - a(x) = δ_e` exactly on every tree edge.

3. **Closing non-tree edges** (`step7.tex:711-733`).  For a non-tree
   edge `e = (x, y)` with fundamental cycle `γ_e` through `z₀`,

     `δ_e - (a(y) - a(x)) = ∮_{γ_e} δ`,

   and star-triangulating `γ_e` through `z₀`, every *good* triangle
   contributes `O(1)` by `lem:cocycle`.

4. **Constant diameter** (`step7.tex:735-777`).  The diameter-3
   bound ensures `ℓ(e) ≤ 7` for all but `o(1)`-weight of non-tree
   edges.

## Lean formalisation

We formalise the content in *cleared-denominator abstract form*.
Key abstractions, all inside `namespace PotentialData`:

* `PotentialData` — bundle with vertex set `V`, edge set `E`,
  endpoints, signed weight, potential, incidence weight.
* `potentialDefect e := signedWeight e - (pot (tgt e) - pot (src e))`.
* `TreeIntegrationHyp` — tree edges integrate exactly.
* `CycleBoundHyp` — short-cycle edges have bounded defect.
* `LongDecompositionHyp` — `edges = treeEdges ∪ shortEdges ∪ longEdges`.
* `badEdges C` — edges with `|potentialDefect e| > C`.
* `goodEdges C` — edges with `|potentialDefect e| ≤ C`.

Main results:

* `treeEdges_subset_goodEdges` — tree edges are good.
* `shortEdges_subset_goodEdges` — short-cycle edges are good.
* `badEdges_subset_longEdges` — bad edges are concentrated in the
  `o(1)`-weight long-edge set.
* `lem_potential` — cleared-denominator form of the paper's
  `(1 - o(1))` statement on the weighted bad-edge mass.

Downstream, `lem:single-c` (`step7.tex:820`) consumes the potential
to synchronize per-fiber thresholds into a single global `c ∈ ℤ`.
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §1 — Potential data bundle -/

/-- **Potential data bundle** (`step7.tex:669-710`).

Packages:

* `src, tgt : E → V` — interface endpoints (`step7.tex:672-673`);
* `signedWeight : E → ℤ` — signed edge label `δ_e = σ̃_e · τ_e`
  (`step7.tex:679`);
* `pot : V → ℤ` — vertex potential `a(z)` (`step7.tex:701-706`);
* `edgeWeight : E → ℕ` — interface incidence weight. -/
structure PotentialData (Vertex Edge : Type*) where
  /-- Source endpoint `x` of an interface edge `e = (x, y)`. -/
  src : Edge → Vertex
  /-- Target endpoint `y` of an interface edge `e = (x, y)`. -/
  tgt : Edge → Vertex
  /-- Signed edge label `δ_e = σ̃_e · τ_e`. -/
  signedWeight : Edge → ℤ
  /-- Vertex potential `a : P → ℤ`. -/
  pot : Vertex → ℤ
  /-- Incidence weight of an interface edge. -/
  edgeWeight : Edge → ℕ

namespace PotentialData

variable {Vertex Edge : Type*} [DecidableEq Edge]
variable (D : PotentialData Vertex Edge)

/-- **Potential defect** at an edge (`step7.tex:716`):

  `δ_e - (a(y) - a(x))`.

On `(1 - o(1))` of interfaces, `|potentialDefect| = O(1)`. -/
def potentialDefect (e : Edge) : ℤ :=
  D.signedWeight e - (D.pot (D.tgt e) - D.pot (D.src e))

/-- **Good edges at tolerance `C`** (`step7.tex:789`):
interfaces with `|potentialDefect e| ≤ C`. -/
def goodEdges (edges : Finset Edge) (C : ℕ) : Finset Edge :=
  edges.filter (fun e => |D.potentialDefect e| ≤ (C : ℤ))

/-- **Bad edges at tolerance `C`**: complement of `goodEdges`. -/
def badEdges (edges : Finset Edge) (C : ℕ) : Finset Edge :=
  edges.filter (fun e => (C : ℤ) < |D.potentialDefect e|)

lemma mem_goodEdges {edges : Finset Edge} {C : ℕ} {e : Edge} :
    e ∈ D.goodEdges edges C ↔
      e ∈ edges ∧ |D.potentialDefect e| ≤ (C : ℤ) := by
  simp [goodEdges, Finset.mem_filter]

lemma mem_badEdges {edges : Finset Edge} {C : ℕ} {e : Edge} :
    e ∈ D.badEdges edges C ↔
      e ∈ edges ∧ (C : ℤ) < |D.potentialDefect e| := by
  simp [badEdges, Finset.mem_filter]

lemma goodEdges_subset (edges : Finset Edge) (C : ℕ) :
    D.goodEdges edges C ⊆ edges := Finset.filter_subset _ _

lemma badEdges_subset (edges : Finset Edge) (C : ℕ) :
    D.badEdges edges C ⊆ edges := Finset.filter_subset _ _

/-- `goodEdges` and `badEdges` are disjoint. -/
lemma goodEdges_disjoint_badEdges (edges : Finset Edge) (C : ℕ) :
    Disjoint (D.goodEdges edges C) (D.badEdges edges C) := by
  rw [Finset.disjoint_left]
  intro e hgood hbad
  rw [D.mem_goodEdges] at hgood
  rw [D.mem_badEdges] at hbad
  exact absurd hbad.2 (not_lt.mpr hgood.2)

/-- `goodEdges ∪ badEdges = edges`. -/
lemma goodEdges_union_badEdges (edges : Finset Edge) (C : ℕ) :
    D.goodEdges edges C ∪ D.badEdges edges C = edges := by
  ext e
  simp only [Finset.mem_union, mem_goodEdges, mem_badEdges]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro he
    by_cases h : |D.potentialDefect e| ≤ (C : ℤ)
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, not_le.mp h⟩

/-- Cardinality partition: `|goodEdges| + |badEdges| = |edges|`. -/
lemma card_good_add_card_bad (edges : Finset Edge) (C : ℕ) :
    (D.goodEdges edges C).card + (D.badEdges edges C).card =
      edges.card := by
  rw [← Finset.card_union_of_disjoint (D.goodEdges_disjoint_badEdges edges C)]
  rw [D.goodEdges_union_badEdges]

/-- Weight-sum partition: `∑ w = ∑_good w + ∑_bad w`. -/
lemma sum_edgeWeight_split (edges : Finset Edge) (C : ℕ) :
    ∑ e ∈ edges, D.edgeWeight e =
      ∑ e ∈ D.goodEdges edges C, D.edgeWeight e +
        ∑ e ∈ D.badEdges edges C, D.edgeWeight e := by
  rw [← Finset.sum_union (D.goodEdges_disjoint_badEdges edges C)]
  rw [D.goodEdges_union_badEdges]

/-! ### §2 — Tree-edge integration identity -/

/-- **Tree-edge integration hypothesis** (`step7.tex:708-710`).

On the spanning tree `T`, `a` is defined as the signed-weight sum
along the unique `T`-path from the basepoint, so
`a(tgt e) - a(src e) = signedWeight e` exactly on every tree
edge. -/
def TreeIntegrationHyp (treeEdges : Finset Edge) : Prop :=
  ∀ e ∈ treeEdges, D.potentialDefect e = 0

/-- Tree edges are good for any nonnegative tolerance. -/
theorem treeEdges_subset_goodEdges
    (edges treeEdges : Finset Edge) (C : ℕ)
    (hTree : D.TreeIntegrationHyp treeEdges)
    (hSub : treeEdges ⊆ edges) :
    treeEdges ⊆ D.goodEdges edges C := by
  intro e he
  rw [D.mem_goodEdges]
  refine ⟨hSub he, ?_⟩
  rw [hTree e he]
  simp

/-! ### §3 — Cycle bound on short non-tree edges -/

/-- **Cycle-bound hypothesis** (`step7.tex:712-783`).

Non-tree edges `e` with short fundamental cycle `ℓ(e) = O(1)`
satisfy `|potentialDefect e| ≤ C₁` by star-triangulation through
`lem:cocycle` (`step7.tex:783`). -/
def CycleBoundHyp (shortEdges : Finset Edge) (C₁ : ℕ) : Prop :=
  ∀ e ∈ shortEdges, |D.potentialDefect e| ≤ (C₁ : ℤ)

/-- Short-cycle non-tree edges are good at tolerance `C₁`. -/
theorem shortEdges_subset_goodEdges
    (edges shortEdges : Finset Edge) (C₁ : ℕ)
    (hCyc : D.CycleBoundHyp shortEdges C₁)
    (hSub : shortEdges ⊆ edges) :
    shortEdges ⊆ D.goodEdges edges C₁ := by
  intro e he
  rw [D.mem_goodEdges]
  exact ⟨hSub he, hCyc e he⟩

/-- **Combined tree + short-cycle = good at tolerance `C₁`**. -/
theorem tree_union_short_subset_goodEdges
    (edges treeEdges shortEdges : Finset Edge) (C₁ : ℕ)
    (hTree : D.TreeIntegrationHyp treeEdges)
    (hCyc : D.CycleBoundHyp shortEdges C₁)
    (hTreeSub : treeEdges ⊆ edges)
    (hShortSub : shortEdges ⊆ edges) :
    treeEdges ∪ shortEdges ⊆ D.goodEdges edges C₁ := by
  intro e he
  rw [Finset.mem_union] at he
  rcases he with h | h
  · exact D.treeEdges_subset_goodEdges edges treeEdges C₁ hTree hTreeSub h
  · exact D.shortEdges_subset_goodEdges edges shortEdges C₁ hCyc hShortSub h

/-! ### §4 — Bad edges localize to the long-cycle set -/

/-- **Long-edge decomposition hypothesis** (`step7.tex:773-785`).

The paper decomposes `E⋆ = treeEdges ⊔ shortEdges ⊔ longEdges`,
with `longEdges` carrying `o(1)`-weight (diameter-3 exception
set). -/
def LongDecompositionHyp (edges treeEdges shortEdges longEdges : Finset Edge) :
    Prop :=
  edges ⊆ treeEdges ∪ shortEdges ∪ longEdges

/-- **Bad-edge localization** (`step7.tex:785-790`):

Under the long-edge decomposition + tree-integration + cycle-bound
hypotheses, every bad edge at tolerance `C₁` lies in `longEdges`. -/
theorem badEdges_subset_longEdges
    (edges treeEdges shortEdges longEdges : Finset Edge) (C₁ : ℕ)
    (hTree : D.TreeIntegrationHyp treeEdges)
    (hCyc : D.CycleBoundHyp shortEdges C₁)
    (hDecomp : LongDecompositionHyp edges treeEdges shortEdges longEdges) :
    D.badEdges edges C₁ ⊆ longEdges := by
  intro e he
  rw [D.mem_badEdges] at he
  obtain ⟨heE, hdef⟩ := he
  have := hDecomp heE
  rw [Finset.mem_union] at this
  rcases this with h | h
  · rw [Finset.mem_union] at h
    rcases h with h | h
    · have hzero : D.potentialDefect e = 0 := hTree e h
      rw [hzero] at hdef
      simp only [abs_zero] at hdef
      exact absurd hdef (by exact_mod_cast Nat.not_lt_zero C₁)
    · have hbnd : |D.potentialDefect e| ≤ (C₁ : ℤ) := hCyc e h
      exact absurd hbnd (not_le.mpr hdef)
  · exact h

/-- **Summed bad-weight bound via long edges** (`step7.tex:785-790`).

Total bad-edge weight is bounded by total long-edge weight. -/
theorem sum_bad_weight_le_long
    (edges treeEdges shortEdges longEdges : Finset Edge) (C₁ : ℕ)
    (hTree : D.TreeIntegrationHyp treeEdges)
    (hCyc : D.CycleBoundHyp shortEdges C₁)
    (hDecomp : LongDecompositionHyp edges treeEdges shortEdges longEdges) :
    ∑ e ∈ D.badEdges edges C₁, D.edgeWeight e ≤
      ∑ e ∈ longEdges, D.edgeWeight e := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact D.badEdges_subset_longEdges edges treeEdges shortEdges longEdges
      C₁ hTree hCyc hDecomp
  · intros; exact Nat.zero_le _

/-! ### §5 — Main theorem `lem:potential` -/

/-- **`lem:potential` — vertex potential representation**
(`step7.tex:657-667`).

Cleared-denominator form: under the structural hypotheses
(tree integration, short-cycle bound, long decomposition), if the
long-edge weight satisfies `e_d · ∑_long w ≤ e_n · M₀`, then so
does the bad-edge weight — equivalently, a `(1 - o(1))`-fraction
of interfaces satisfy `|σ̃_e · τ_e - (a(y) - a(x))| ≤ C₁`. -/
theorem lem_potential
    (edges treeEdges shortEdges longEdges : Finset Edge) (C₁ : ℕ)
    (hTree : D.TreeIntegrationHyp treeEdges)
    (hCyc : D.CycleBoundHyp shortEdges C₁)
    (hDecomp : LongDecompositionHyp edges treeEdges shortEdges longEdges)
    (e_n e_d M₀ : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, D.edgeWeight e ≤ e_n * M₀) :
    e_d * ∑ e ∈ D.badEdges edges C₁, D.edgeWeight e ≤ e_n * M₀ := by
  have hmono : ∑ e ∈ D.badEdges edges C₁, D.edgeWeight e ≤
      ∑ e ∈ longEdges, D.edgeWeight e :=
    D.sum_bad_weight_le_long edges treeEdges shortEdges longEdges
      C₁ hTree hCyc hDecomp
  calc e_d * ∑ e ∈ D.badEdges edges C₁, D.edgeWeight e
      ≤ e_d * ∑ e ∈ longEdges, D.edgeWeight e :=
        Nat.mul_le_mul_left _ hmono
    _ ≤ e_n * M₀ := hLong

/-- **Good-edge weight lower bound** (`step7.tex:786-790`).

Equivalent form: the `C₁`-good edges carry `(1 - o(1))` of total
weight.  If `∑ edgeWeight = totalW` and
`e_d · ∑_long w ≤ e_n · M₀`, then

  `e_d · (totalW - ∑_good w) ≤ e_n · M₀`. -/
theorem good_edge_weight_lb
    (edges treeEdges shortEdges longEdges : Finset Edge) (C₁ : ℕ)
    (hTree : D.TreeIntegrationHyp treeEdges)
    (hCyc : D.CycleBoundHyp shortEdges C₁)
    (hDecomp : LongDecompositionHyp edges treeEdges shortEdges longEdges)
    (e_n e_d M₀ totalW : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, D.edgeWeight e ≤ e_n * M₀)
    (htotal : ∑ e ∈ edges, D.edgeWeight e = totalW) :
    e_d * (totalW - ∑ e ∈ D.goodEdges edges C₁, D.edgeWeight e) ≤
      e_n * M₀ := by
  have hsplit := D.sum_edgeWeight_split edges C₁
  have hsub :
      totalW - ∑ e ∈ D.goodEdges edges C₁, D.edgeWeight e =
        ∑ e ∈ D.badEdges edges C₁, D.edgeWeight e := by
    rw [← htotal, hsplit]
    omega
  rw [hsub]
  exact D.lem_potential edges treeEdges shortEdges longEdges C₁
    hTree hCyc hDecomp e_n e_d M₀ hLong

/-! ### §6 — Test-function consequence: `H(L)` after rich BK swaps -/

/-- **`H`-difference across a rich interface** (`step7.tex:794-807`):
`a(y) - a(x) = signedWeight e - potentialDefect e`. -/
theorem H_diff_eq_pot_diff_mod_defect (e : Edge) :
    D.pot (D.tgt e) - D.pot (D.src e) =
      D.signedWeight e - D.potentialDefect e := by
  unfold potentialDefect
  ring

/-- **Sign-agreement on good edges** (`step7.tex:803-807`):

On `C₁`-good edges, `|σ̃_e · τ_e - (a(y) - a(x))| ≤ C₁`. -/
theorem good_edge_sign_agreement
    {edges : Finset Edge} {C₁ : ℕ} {e : Edge}
    (he : e ∈ D.goodEdges edges C₁) :
    |D.signedWeight e - (D.pot (D.tgt e) - D.pot (D.src e))| ≤
      (C₁ : ℤ) := by
  rw [D.mem_goodEdges] at he
  exact he.2

end PotentialData

end Step7
end OneThird
