/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.Potential
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Single global threshold (`lem:single-c`)

This file formalises `lem:single-c` of `step7.tex` §`sec:global-c`
(`step7.tex:810-943`, `lem:single-c` at `step7.tex:820`): the
synchronization of the per-fiber thresholds `c_e` induced by
`{H ≥ c_e} ∩ fib_e = S ∩ fib_e` into a *single* global constant
`c ∈ ℝ` such that, on `(1 - o(1))` of interfaces `e ∈ E⋆`,

  `1_S(L) = 1_{H(L) ≥ c} + o(1)` on `fib_e ∖ B_e`.

## Paper statement (`step7.tex:820-832`)

Assume Step 6 (low conductance) and `lem:potential`.  There is
`c ∈ ℝ` such that for `(1 - o(1))` of interfaces `e ∈ E⋆`,
`1_S = 1_{H ≥ c} + o(1)` on `fib_e ∖ B_e`, equivalently
`|c_e - c| = O(1)` on the giant component.

## Proof outline (`step7.tex:834-943`)

1. **Per-fiber threshold** (`step7.tex:838-856`).  On
   `fib_e ∖ B_e`, `lem:signed-threshold` + `lem:potential` give a
   well-defined per-fiber threshold `c_e`.

2. **Pairwise closeness from low conductance**
   (`step7.tex:858-908`).  For every active pair `(e, f)`,
   discrepancy `|c_e - c_f|` produces a BK boundary of mass
   `≳ (|c_e - c_f|/A) · w_{ef}/t_{max}`.  Step 6 low conductance
   then forces `|c_e - c_f| ≤ K₁ = O(1)` on `(1 - o(1))` of pairs.

3. **Diameter-3 globalization** (`step7.tex:910-942`).  On the
   giant component, every `e` admits a length-`≤ 3` walk
   `e₀ ↔ g₁ ↔ g₂ ↔ e` through active pairs.  If every hop is
   good, the triangle inequality gives `|c_e - c_{e₀}| ≤ 3 K₁`.

## Lean formalisation

Cleared-denominator abstract form, all inside
`namespace FiberThresholdData`:

* `FiberThresholdData` — bundle of per-fiber thresholds `c_e`.
* `PairClosenessHyp` — pairwise closeness on good active pairs.
* `WalkWitness3` — length-`≤ 3` walks of good hops.
* `goodEdges K` — edges with `|c_e - c_{e₀}| ≤ K`.

Main results:

* `walk3_triangle_bound` — triangle inequality along a good walk.
* `lem_single_c` — cleared-denominator form of the paper's
  conclusion: walks + closeness ⇒ `3 K₁`-goodness.
* `single_c_weight_lb` — good-edge set carries `(1 - o(1))` of
  total weight, given a walk-supporting subset hypothesis.

Downstream, `lem:budget-var` and `lem:bandwidth`
(`step7.tex:960, 1018`) consume the global threshold `c` to
derive Prop. 7.2's layered decomposition.
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §1 — Fiber threshold data -/

/-- **Fiber-threshold data** (`step7.tex:844-856`).

For each interface `e ∈ E⋆`, `lem:signed-threshold` + `lem:potential`
produce a per-fiber threshold `c_e ∈ ℝ` such that
`1_S = 1_{H ≥ c_e}` on `fib_e ∖ B_e`.  This bundle packages the
per-fiber thresholds together with the interface incidence weight. -/
structure FiberThresholdData (Edge : Type*) where
  /-- Per-fiber threshold `c_e`. -/
  c : Edge → ℤ
  /-- Incidence weight of an interface edge. -/
  edgeWeight : Edge → ℕ

namespace FiberThresholdData

variable {Edge : Type*} [DecidableEq Edge]
variable (D : FiberThresholdData Edge)

/-- **Pairwise defect** `c_e - c_f` between two interfaces. -/
def pairDefect (e f : Edge) : ℤ := D.c e - D.c f

lemma pairDefect_self (e : Edge) : D.pairDefect e e = 0 := by
  unfold pairDefect
  ring

/-- `|c_e - c_f|` is symmetric: `|pairDefect e f| = |pairDefect f e|`. -/
lemma abs_pairDefect_symm (e f : Edge) :
    |D.pairDefect e f| = |D.pairDefect f e| := by
  unfold pairDefect
  rw [show D.c f - D.c e = -(D.c e - D.c f) from by ring, abs_neg]

/-! ### §2 — Pairwise closeness hypothesis -/

/-- **Pairwise closeness hypothesis** (`step7.tex:868-908`,
`eq:pair-bdd`).

For every "good" active pair `(e, f) ∈ goodPairs`,
`|c_e - c_f| ≤ K₁`.  On the paper's `(1 - o(1))`-mass subset of
active pairs, Step 6 low conductance gives this Cheeger-type
bound. -/
def PairClosenessHyp (goodPairs : Finset (Edge × Edge)) (K₁ : ℕ) : Prop :=
  ∀ p ∈ goodPairs, |D.pairDefect p.1 p.2| ≤ (K₁ : ℤ)

lemma pairCloseness_bound
    {goodPairs : Finset (Edge × Edge)} {K₁ : ℕ}
    (hGood : D.PairClosenessHyp goodPairs K₁)
    {e f : Edge} (hef : (e, f) ∈ goodPairs) :
    |D.pairDefect e f| ≤ (K₁ : ℤ) :=
  hGood (e, f) hef

/-! ### §3 — Diameter-3 walks through good pairs -/

/-- **Good-walk witness of length ≤ 3** (`step7.tex:921-930`).

For each edge `e ∈ edges`, an intermediate triple `(g₁, g₂)` such
that `(refEdge, g₁)`, `(g₁, g₂)`, `(g₂, e)` all lie in `goodPairs`.
The paper's diameter-3 argument supplies such a walk on
`(1 - o(1))` of edges. -/
def WalkWitness3 (refEdge : Edge) (edges : Finset Edge)
    (goodPairs : Finset (Edge × Edge)) : Prop :=
  ∀ e ∈ edges, ∃ g₁ g₂ : Edge,
    (refEdge, g₁) ∈ goodPairs ∧
    (g₁, g₂) ∈ goodPairs ∧
    (g₂, e) ∈ goodPairs

/-- **Triangle inequality along a length-3 walk** (`step7.tex:931-935`).

If every hop of a length-3 walk `e₀ → g₁ → g₂ → e` has pairwise
threshold defect `≤ K₁`, then

  `|c_e - c_{e₀}| ≤ 3 K₁`. -/
theorem walk3_triangle_bound (e₀ g₁ g₂ e : Edge) (K₁ : ℕ)
    (h01 : |D.pairDefect e₀ g₁| ≤ (K₁ : ℤ))
    (h12 : |D.pairDefect g₁ g₂| ≤ (K₁ : ℤ))
    (h23 : |D.pairDefect g₂ e| ≤ (K₁ : ℤ)) :
    |D.pairDefect e₀ e| ≤ 3 * (K₁ : ℤ) := by
  have hdecomp : D.pairDefect e₀ e =
      D.pairDefect e₀ g₁ + D.pairDefect g₁ g₂ + D.pairDefect g₂ e := by
    unfold pairDefect
    ring
  rw [hdecomp]
  have htri := abs_add_three (D.pairDefect e₀ g₁)
    (D.pairDefect g₁ g₂) (D.pairDefect g₂ e)
  calc |D.pairDefect e₀ g₁ + D.pairDefect g₁ g₂ + D.pairDefect g₂ e|
      ≤ |D.pairDefect e₀ g₁| + |D.pairDefect g₁ g₂| +
          |D.pairDefect g₂ e| := htri
    _ ≤ (K₁ : ℤ) + (K₁ : ℤ) + (K₁ : ℤ) := by
        exact add_le_add (add_le_add h01 h12) h23
    _ = 3 * (K₁ : ℤ) := by ring

/-! ### §4 — Good-edge set at tolerance `K` -/

/-- **`c`-good edges at tolerance `K`** relative to a reference
`e₀`: interfaces with `|c_e - c_{e₀}| ≤ K`. -/
def goodEdges (refEdge : Edge) (edges : Finset Edge) (K : ℕ) :
    Finset Edge :=
  edges.filter (fun e => |D.pairDefect refEdge e| ≤ (K : ℤ))

/-- **`c`-bad edges at tolerance `K`**: complement. -/
def badEdges (refEdge : Edge) (edges : Finset Edge) (K : ℕ) :
    Finset Edge :=
  edges.filter (fun e => (K : ℤ) < |D.pairDefect refEdge e|)

lemma mem_goodEdges {refEdge : Edge} {edges : Finset Edge} {K : ℕ}
    {e : Edge} :
    e ∈ D.goodEdges refEdge edges K ↔
      e ∈ edges ∧ |D.pairDefect refEdge e| ≤ (K : ℤ) := by
  simp [goodEdges, Finset.mem_filter]

lemma mem_badEdges {refEdge : Edge} {edges : Finset Edge} {K : ℕ}
    {e : Edge} :
    e ∈ D.badEdges refEdge edges K ↔
      e ∈ edges ∧ (K : ℤ) < |D.pairDefect refEdge e| := by
  simp [badEdges, Finset.mem_filter]

lemma goodEdges_subset (refEdge : Edge) (edges : Finset Edge) (K : ℕ) :
    D.goodEdges refEdge edges K ⊆ edges := Finset.filter_subset _ _

lemma badEdges_subset (refEdge : Edge) (edges : Finset Edge) (K : ℕ) :
    D.badEdges refEdge edges K ⊆ edges := Finset.filter_subset _ _

/-- `goodEdges ∪ badEdges = edges`. -/
lemma goodEdges_union_badEdges
    (refEdge : Edge) (edges : Finset Edge) (K : ℕ) :
    D.goodEdges refEdge edges K ∪ D.badEdges refEdge edges K = edges := by
  ext e
  simp only [Finset.mem_union, mem_goodEdges, mem_badEdges]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro he
    by_cases h : |D.pairDefect refEdge e| ≤ (K : ℤ)
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, not_le.mp h⟩

lemma goodEdges_disjoint_badEdges
    (refEdge : Edge) (edges : Finset Edge) (K : ℕ) :
    Disjoint (D.goodEdges refEdge edges K) (D.badEdges refEdge edges K) := by
  rw [Finset.disjoint_left]
  intro e hgood hbad
  rw [D.mem_goodEdges] at hgood
  rw [D.mem_badEdges] at hbad
  exact absurd hbad.2 (not_lt.mpr hgood.2)

/-! ### §5 — Main theorem `lem:single-c` -/

/-- **`lem:single-c` — single global threshold**
(`step7.tex:820-942`).

Cleared-denominator form: under `PairClosenessHyp` and
`WalkWitness3`, every edge with a walk-witness is `3 K₁`-close to
the reference threshold `c := c_{e₀}`, i.e.

  `edges ⊆ goodEdges e₀ edges (3 K₁)`. -/
theorem lem_single_c
    (refEdge : Edge) (edges : Finset Edge)
    (goodPairs : Finset (Edge × Edge)) (K₁ : ℕ)
    (hPair : D.PairClosenessHyp goodPairs K₁)
    (hWalk : WalkWitness3 refEdge edges goodPairs) :
    edges ⊆ D.goodEdges refEdge edges (3 * K₁) := by
  intro e he
  rw [D.mem_goodEdges]
  refine ⟨he, ?_⟩
  obtain ⟨g₁, g₂, h01, h12, h23⟩ := hWalk e he
  have hb01 := D.pairCloseness_bound hPair h01
  have hb12 := D.pairCloseness_bound hPair h12
  have hb23 := D.pairCloseness_bound hPair h23
  have hbnd := D.walk3_triangle_bound refEdge g₁ g₂ e K₁ hb01 hb12 hb23
  push_cast
  linarith

/-- **Good-edge weight lower bound from walk-supporting subset**
(`step7.tex:928-930`).

If `edgesWalk ⊆ edges` admits `WalkWitness3` and the exceptional
weight `∑_{edges ∖ edgesWalk}` is bounded by `(e_n / e_d) · M₀`,
then so is the bad-edge weight. -/
theorem single_c_weight_lb
    (refEdge : Edge) (edges edgesWalk : Finset Edge)
    (goodPairs : Finset (Edge × Edge)) (K₁ : ℕ)
    (hPair : D.PairClosenessHyp goodPairs K₁)
    (hWalk : WalkWitness3 refEdge edgesWalk goodPairs)
    (_hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ : ℕ)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, D.edgeWeight e ≤ e_n * M₀) :
    e_d * ∑ e ∈ D.badEdges refEdge edges (3 * K₁), D.edgeWeight e ≤
      e_n * M₀ := by
  classical
  have hbad_sub :
      D.badEdges refEdge edges (3 * K₁) ⊆ edges \ edgesWalk := by
    intro e he
    rw [D.mem_badEdges] at he
    rw [Finset.mem_sdiff]
    obtain ⟨heE, hdef⟩ := he
    refine ⟨heE, ?_⟩
    intro heW
    have hgood : e ∈ D.goodEdges refEdge edgesWalk (3 * K₁) :=
      D.lem_single_c refEdge edgesWalk goodPairs K₁ hPair hWalk heW
    rw [D.mem_goodEdges] at hgood
    exact absurd hgood.2 (not_le.mpr hdef)
  have hsum_sub :
      ∑ e ∈ D.badEdges refEdge edges (3 * K₁), D.edgeWeight e ≤
        ∑ e ∈ edges \ edgesWalk, D.edgeWeight e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hbad_sub
    intros; exact Nat.zero_le _
  calc e_d * ∑ e ∈ D.badEdges refEdge edges (3 * K₁), D.edgeWeight e
      ≤ e_d * ∑ e ∈ edges \ edgesWalk, D.edgeWeight e :=
        Nat.mul_le_mul_left _ hsum_sub
    _ ≤ e_n * M₀ := hExc

end FiberThresholdData

/-! ### §6 — Bridge to `PotentialData`: threshold of a potential -/

section Bridge

variable {Vertex Edge : Type*}

/-- **Induced fiber-threshold data from a potential** (`step7.tex:841-845`).

Given a `PotentialData` on `(Vertex, Edge)`, the per-fiber
threshold `c_e` is (up to `O(1)` from `lem:potential`) the
signed-threshold label `τ_e`.  Concretely we bind `c_e` to
`signedWeight e`; the `O(1)` correction is absorbed into the
tolerance `K₁` of `PairClosenessHyp`. -/
def FiberThresholdData.ofPotential
    (P : PotentialData Vertex Edge) :
    FiberThresholdData Edge :=
  { c := P.signedWeight
    edgeWeight := P.edgeWeight }

@[simp] lemma FiberThresholdData.ofPotential_c
    (P : PotentialData Vertex Edge) (e : Edge) :
    (FiberThresholdData.ofPotential P).c e = P.signedWeight e := rfl

@[simp] lemma FiberThresholdData.ofPotential_edgeWeight
    (P : PotentialData Vertex Edge) (e : Edge) :
    (FiberThresholdData.ofPotential P).edgeWeight e = P.edgeWeight e := rfl

end Bridge

end Step7
end OneThird
