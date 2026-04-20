/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.SimpleGraph.EdgeBoundary
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Dirichlet form of a finite reversible chain and the indicator Cheeger inequality

For a finite simple graph `G` on a vertex type `V`, interpreted as the
transition graph of the uniform reversible chain, the **Dirichlet form**
(or Dirichlet energy) of a function `f : V → ℚ` is

```
𝓔(f) := ∑_{e = {u,v} ∈ E(G)} (f u − f v)²,
```

i.e. the sum of squared discrepancies across each (unordered) edge.
When `G` is the transition graph of a reversible Markov chain with
uniform stationary distribution `π`, this equals the classical
`𝓔(f) = ½ 𝔼_π[(f(X) − f(Y))²]` up to a scalar factor determined by the
overall edge multiplicity. The probabilistic normalisation factor
`1/((n−1) · |𝓛(P)|)` used in Step 8 is left to the caller.

## Main definitions

* `SimpleGraph.dirichletForm G f` — the Dirichlet form of `f : V → ℚ`
  on a finite simple graph `G`, expressed as a `Finset.sum` over
  `G.edgeFinset`.

## Main results

* `SimpleGraph.dirichletForm_indicator` — for `f = 𝟙_S` the Dirichlet
  energy equals the edge-boundary cardinality,
  `𝓔(𝟙_S) = (G.edgeBoundary S).card`.

* `Finset.card_mul_card_sdiff_le_card_univ_mul_min` — the elementary
  cardinality inequality underlying the indicator Cheeger bound:
  `|S| · |Sᶜ| ≤ |V| · min(|S|, |Sᶜ|)`.

* `SimpleGraph.cheeger_indicator` — the **indicator Cheeger
  inequality** (`step8.tex` Lemma `lem:dirichlet-conductance`). The
  conductance ratio `|∂S| / min(|S|, |Sᶜ|)` is bounded above by the
  Dirichlet–variance ratio `𝓔(𝟙_S) · |V| / (|S| · |Sᶜ|)`. In the
  rearranged form stated here,
  `|∂S| · |S| · |Sᶜ| ≤ 𝓔(𝟙_S) · |V| · min(|S|, |Sᶜ|)`. This is the
  "easy half" of Cheeger for uniform-reversible chains; it requires
  no spectral machinery.

## References

Step 8 (`step8.tex` §`lem:dirichlet-conductance`) of the width-3
1/3–2/3 proof.
-/

open Finset

namespace Finset

/-- Elementary cardinality inequality used in the indicator Cheeger
bound: for any finset `S` of a finite type `V`,
`|S| · |Sᶜ| ≤ |V| · min(|S|, |Sᶜ|)`. -/
theorem card_mul_card_sdiff_le_card_univ_mul_min
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    S.card * (Finset.univ \ S).card ≤
      Fintype.card V * min S.card (Finset.univ \ S).card := by
  set s := S.card with hs_def
  set t := (Finset.univ \ S : Finset V).card with ht_def
  have hsum : s + t = Fintype.card V := by
    have h : t + s = (Finset.univ : Finset V).card :=
      Finset.card_sdiff_add_card_eq_card S.subset_univ
    simpa [Nat.add_comm, Finset.card_univ] using h
  rcases le_total s t with hle | hle
  · -- `min = s`
    calc
      s * t = t * s := Nat.mul_comm s t
      _ ≤ (s + t) * s := Nat.mul_le_mul_right s (Nat.le_add_left t s)
      _ = Fintype.card V * s := by rw [hsum]
      _ = Fintype.card V * min s t := by rw [min_eq_left hle]
  · -- `min = t`
    calc
      s * t ≤ (s + t) * t := Nat.mul_le_mul_right t (Nat.le_add_right s t)
      _ = Fintype.card V * t := by rw [hsum]
      _ = Fintype.card V * min s t := by rw [min_eq_right hle]

end Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Symmetric function on pairs `u, v : V` giving the squared difference
of `f : V → ℚ`; lifts to `Sym2 V` via `Sym2.lift` and is the basic
summand of the Dirichlet form. -/
private def sqDiff (f : V → ℚ) : { g : V → V → ℚ // ∀ a b, g a b = g b a } :=
  ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩

/-- The **Dirichlet form** (reversible-chain energy) of a function
`f : V → ℚ` on a finite simple graph, defined as the sum of squared
differences across unordered edges:

`dirichletForm G f = ∑_{e = {u,v} ∈ E(G)} (f u − f v)²`.

This is the symmetric-chain Dirichlet energy; under the uniform
stationary measure `π` and the transition kernel
`P(u, v) = 𝟙[u ∼ v] / deg u`, it coincides with
`½ 𝔼_π[(f X − f Y)²]` up to a scalar factor depending on the overall
edge multiplicity. In Step 8 (`step8.tex`) the factor
`1/((n−1) · |𝓛(P)|)` is supplied by the caller after instantiating
this definition. -/
def dirichletForm (f : V → ℚ) : ℚ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift (sqDiff f) e

variable {G}

/-- For an indicator `𝟙_S` evaluated on an edge `e = {u, v} ∈ G`, the
squared-difference summand `(𝟙_S u − 𝟙_S v)²` equals `1` when the edge
crosses the cut `(S, Sᶜ)` and `0` otherwise. -/
private lemma sqDiff_indicator_apply
    (S : Finset V) {u v : V} (huv : G.Adj u v) :
    Sym2.lift (sqDiff (fun w => if w ∈ S then (1 : ℚ) else 0)) s(u, v) =
      if s(u, v) ∈ G.edgeBoundary S then (1 : ℚ) else 0 := by
  simp only [sqDiff, Sym2.lift_mk]
  by_cases hu : u ∈ S
  · by_cases hv : v ∈ S
    · have hnot : s(u, v) ∉ G.edgeBoundary S := by
        rw [mk_mem_edgeBoundary_iff]
        rintro ⟨_, hc | hc⟩
        · exact hc.2 hv
        · exact hc.1 hu
      simp [hu, hv, hnot]
    · have hin : s(u, v) ∈ G.edgeBoundary S :=
        (mk_mem_edgeBoundary_iff).mpr ⟨huv, Or.inl ⟨hu, hv⟩⟩
      simp [hu, hv, hin]
  · by_cases hv : v ∈ S
    · have hin : s(u, v) ∈ G.edgeBoundary S :=
        (mk_mem_edgeBoundary_iff).mpr ⟨huv, Or.inr ⟨hu, hv⟩⟩
      simp [hu, hv, hin]
    · have hnot : s(u, v) ∉ G.edgeBoundary S := by
        rw [mk_mem_edgeBoundary_iff]
        rintro ⟨_, hc | hc⟩
        · exact hu hc.1
        · exact hv hc.2
      simp [hu, hv, hnot]

/-- **Indicator Dirichlet formula.** The Dirichlet energy of the
indicator `𝟙_S` equals the edge-boundary cardinality:
`dirichletForm G 𝟙_S = (G.edgeBoundary S).card`. -/
theorem dirichletForm_indicator (S : Finset V) :
    dirichletForm G (fun v => if v ∈ S then (1 : ℚ) else 0) =
      ((G.edgeBoundary S).card : ℚ) := by
  classical
  have hcongr :
      dirichletForm G (fun v => if v ∈ S then (1 : ℚ) else 0) =
        ∑ e ∈ G.edgeFinset, if e ∈ G.edgeBoundary S then (1 : ℚ) else 0 := by
    unfold dirichletForm
    refine Finset.sum_congr rfl ?_
    intro e he
    induction e with
    | h u v =>
      have huv : G.Adj u v := by rwa [mem_edgeFinset, mem_edgeSet] at he
      exact sqDiff_indicator_apply S huv
  rw [hcongr, Finset.sum_boole]
  have hfilter :
      G.edgeFinset.filter (fun e => e ∈ G.edgeBoundary S) = G.edgeBoundary S := by
    ext e
    refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => ?_⟩
    exact Finset.mem_filter.mpr ⟨G.edgeBoundary_subset_edgeFinset S h, h⟩
  rw [hfilter]

variable (G)

/-- **Indicator Cheeger inequality** (`step8.tex`
`lem:dirichlet-conductance`). For a finset `S ⊆ V`, the conductance-like
ratio `|∂S| / min(|S|, |Sᶜ|)` is bounded above by the
Dirichlet–variance ratio `𝓔(𝟙_S) · |V| / (|S| · |Sᶜ|)`. Here we state
the inequality in its cleared form:

`|∂S| · |S| · |Sᶜ| ≤ 𝓔(𝟙_S) · |V| · min(|S|, |Sᶜ|)`.

Combined with `dirichletForm_indicator` (which rewrites `𝓔(𝟙_S) = |∂S|`),
this reduces to the elementary cardinality bound
`|S| · |Sᶜ| ≤ |V| · min(|S|, |Sᶜ|)`. The factorisation is preserved so
the statement remains useful after multiplying through by an arbitrary
probabilistic normalisation. -/
theorem cheeger_indicator (S : Finset V) :
    ((G.edgeBoundary S).card : ℚ) *
        ((S.card : ℚ) * ((Finset.univ \ S).card : ℚ))
      ≤ dirichletForm G (fun v => if v ∈ S then (1 : ℚ) else 0) *
          ((Fintype.card V : ℚ) *
            ((min S.card (Finset.univ \ S).card : ℕ) : ℚ)) := by
  rw [dirichletForm_indicator]
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast (Nat.zero_le _))
  exact_mod_cast Finset.card_mul_card_sdiff_le_card_univ_mul_min S

end SimpleGraph
