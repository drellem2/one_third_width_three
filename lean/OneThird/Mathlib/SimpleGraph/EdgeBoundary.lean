/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Edge boundary of a vertex set in a `SimpleGraph`

For a `SimpleGraph G` and a `Finset` of vertices `S`, the *edge boundary*
`G.edgeBoundary S` is the finite set of edges with one endpoint in `S`
and the other in `Sᶜ`. This is the `C3` entry of `MATHLIB_GAPS.md` and
is the object denoted `E(S, Sᶜ)` or `∂S` in the Step 8 conductance work.

## Main definitions

* `SimpleGraph.edgeBoundary G S` — edges of `G` crossing the cut
  `(S, Sᶜ)`, as a `Finset (Sym2 V)`.

## Main results

* `SimpleGraph.edgeBoundary_compl` — `G.edgeBoundary Sᶜ = G.edgeBoundary S`;
  crossing `(S, Sᶜ)` is the same as crossing `(Sᶜ, S)`.
* `SimpleGraph.card_edgeBoundary_compl` — cardinality version of
  `edgeBoundary_compl`.
* `SimpleGraph.edgeBoundary_empty`, `edgeBoundary_univ` — the boundary
  of `∅` or `Finset.univ` is empty.
* `SimpleGraph.edgeBoundary_subset_edgeFinset` — every boundary edge is
  an edge of `G`.
* `SimpleGraph.edgeBoundary_biUnion_incidenceFinset` — the boundary is
  contained in the union of incidence sets over `S`; restricting to a
  single `v ∈ S` gives `G.neighborFinset v \ S` up to `s(v, ·)`.

All proofs close cleanly (no `sorry`); `lake build` is green.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section EdgeBoundary

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The edge boundary `∂S` of a vertex set `S` in a simple graph `G`:
the finset of edges having exactly one endpoint in `S`.

This is an unordered-edge (`Sym2 V`) version of the cut `E(S, Sᶜ)`. -/
def edgeBoundary (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion fun v => (G.neighborFinset v \ S).image fun w => s(v, w)

variable {G}

theorem mem_edgeBoundary {S : Finset V} {e : Sym2 V} :
    e ∈ G.edgeBoundary S ↔
      ∃ u v, e = s(u, v) ∧ G.Adj u v ∧ u ∈ S ∧ v ∉ S := by
  simp only [edgeBoundary, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff,
    mem_neighborFinset]
  constructor
  · rintro ⟨u, huS, w, ⟨huw, hwS⟩, rfl⟩
    exact ⟨u, w, rfl, huw, huS, hwS⟩
  · rintro ⟨u, v, rfl, huv, huS, hvS⟩
    exact ⟨u, huS, v, ⟨huv, hvS⟩, rfl⟩

theorem mk_mem_edgeBoundary_iff {S : Finset V} {u v : V} :
    s(u, v) ∈ G.edgeBoundary S ↔
      G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) := by
  rw [mem_edgeBoundary]
  constructor
  · rintro ⟨a, b, hab, hGab, haS, hbS⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hGab, Or.inl ⟨haS, hbS⟩⟩
    · exact ⟨hGab.symm, Or.inr ⟨hbS, haS⟩⟩
  · rintro ⟨hGuv, huvS | huvS⟩
    · exact ⟨u, v, rfl, hGuv, huvS.1, huvS.2⟩
    · exact ⟨v, u, Sym2.eq_swap, hGuv.symm, huvS.2, huvS.1⟩

variable (G)

theorem edgeBoundary_subset_edgeFinset (S : Finset V) :
    G.edgeBoundary S ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨u, v, rfl, huv, _, _⟩ := mem_edgeBoundary.mp he
  rwa [mem_edgeFinset, mem_edgeSet]

@[simp]
theorem edgeBoundary_empty : G.edgeBoundary (∅ : Finset V) = ∅ := by
  simp [edgeBoundary]

@[simp]
theorem edgeBoundary_univ : G.edgeBoundary (Finset.univ : Finset V) = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  obtain ⟨_, v, _, _, _, hvS⟩ := mem_edgeBoundary.mp he
  exact hvS (Finset.mem_univ v)

/-- The edge boundary is symmetric under taking complements: the set
of edges crossing `(S, Sᶜ)` is the same as those crossing `(Sᶜ, S)`. -/
theorem edgeBoundary_compl (S : Finset V) :
    G.edgeBoundary Sᶜ = G.edgeBoundary S := by
  ext e
  simp only [mem_edgeBoundary]
  constructor
  · rintro ⟨u, v, rfl, huv, huS, hvS⟩
    refine ⟨v, u, Sym2.eq_swap, huv.symm, ?_, ?_⟩
    · simpa using hvS
    · simpa using huS
  · rintro ⟨u, v, rfl, huv, huS, hvS⟩
    refine ⟨v, u, Sym2.eq_swap, huv.symm, ?_, ?_⟩
    · simpa using hvS
    · simpa using huS

theorem card_edgeBoundary_compl (S : Finset V) :
    (G.edgeBoundary Sᶜ).card = (G.edgeBoundary S).card := by
  rw [edgeBoundary_compl]

/-- The boundary of `S` is contained in the union, over vertices of `S`,
of the incidence sets at each such vertex. -/
theorem edgeBoundary_subset_biUnion_incidenceFinset (S : Finset V) :
    G.edgeBoundary S ⊆ S.biUnion (fun v => G.incidenceFinset v) := by
  intro e he
  obtain ⟨u, v, rfl, huv, huS, _⟩ := mem_edgeBoundary.mp he
  refine Finset.mem_biUnion.mpr ⟨u, huS, ?_⟩
  rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff]
  exact ⟨huv, Or.inl rfl⟩

end EdgeBoundary

end SimpleGraph
