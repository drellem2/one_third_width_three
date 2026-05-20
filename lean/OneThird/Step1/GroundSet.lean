/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step1.LocalCoords
import OneThird.Step1.CommonChain
import OneThird.Step1.Corollaries
import OneThird.RichPair

/-!
# Step 1 — coordinate map and raw-fiber decomposition, grounded on the BK graph

This file is **part 1 of the Step 1 Lean port** of the Option A' FULL
REFACTOR (`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`, mg-d8c7
§2.1; work item mg-30e3, ticket OneThird-S1-A).  It delivers the first
two parts of the paper's *local interface theorem* `thm:interface`
(`step1.tex:144-195`) — the **coordinate map** `π_{x,y}` (part (i),
`part:coords`) and the **raw-fiber decomposition** `L(P) = F_{x,y} ⊔
Bad_{x,y}` (part (ii), `part:goodfiber`) — *grounded on the concrete
Bubley–Karzanov graph* `bkGraph α`.

## What "grounded on the BK graph" means here

The core Step 1 definitions (`localCoord`, `signMarker`, `rawFiber`,
`IsGoodFiber`, `goodFiberSet`, `badSet`) already live in
`OneThird/Step1/LocalCoords.lean` directly on `LinearExt α` — which *is*
the vertex set of the Bubley–Karzanov graph `bkGraph α`
(`OneThird/Mathlib/BKGraph.lean`).  Unlike the Step 7 grounded forms
(which were parametric over abstract carrier types and had to be
concretised by `Step7/GroundSet.lean`, mg-4ce6), the Step 1 carriers are
*already* concrete.  "Grounding" here therefore means making the BK-graph
structure **explicit**:

* the coordinate map's domain is `LinearExt α = V(bkGraph α)`;
* the good-fiber edge classification (paper Def. `def:good-fiber`
  clause (G3)) is phrased against `(bkGraph α).Adj`, i.e. the *unit grid
  moves inside a good fiber are exactly the edges of `bkGraph α`*;
* the raw fibers partition `V(bkGraph α)`.

## Main results

* `localCoord_mem_grid` — every linear extension's local coordinate lies
  in the `(t+1) × (t+1)` grid `{0,…,t}²` (paper part (i)).
* `goodFiber_bkGraph_adj_iff` — inside a good fiber, the edges of
  `bkGraph α` are exactly the unit grid moves of the local coordinates
  (paper Def. `def:good-fiber` clause (G3), BK-graph-grounded).
* `localInterface_coordMap_groundSet` — part (i): the coordinate map is
  well-defined into `{0,…,t}²`, and (the width-3 content) the
  common-neighbour set is a chain.
* `localInterface_rawFiber_groundSet` — part (ii): the raw fibers cover
  `V(bkGraph α)`, and `F_{x,y}` / `Bad_{x,y}` partition it.
* `localInterface_groundSet` — parts (i) + (ii) bundled.

## Non-triviality witness (`Antichain3`)

Per the mg-30e3 acceptance bar — *the port must instantiate
non-vacuously at a concrete width-3 non-chain `α`; no
Subsingleton-on-empty baselines* — the namespace `Antichain3` builds the
minimal concrete witness: the **3-element antichain** (`Fin 3` with the
discrete order).  `Antichain3.localInterface_nonvacuous` proves, at this
concrete poset:

* it is genuinely **width 3** (`HasWidth Antichain3 3` — an antichain of
  size exactly 3 exists) and genuinely **not a chain**;
* the rich-pair hypothesis is **satisfiable**: `IsRich 1 a0 a1` holds
  with common-neighbour-chain length `t(a0,a1) = 1 > 0`, so the
  coordinate codomain `{0,…,t}²` is the genuine `2 × 2` grid `{0,1}²` —
  not a degenerate single point;
* `2 ≤ numLinExt Antichain3`: the linear-extension set the raw fibers
  decompose is **not a subsingleton** — explicitly rebutting the
  "Subsingleton-on-empty" degenerate baseline;
* the grounded interface theorem `localInterface_groundSet` fires and
  delivers its part-(i)/(ii) conclusions concretely.

## Scope boundary

This file ports paper parts (i) + (ii) only.  Parts (iii) (BK-move
classification) and (iv) (bad-set strip decomposition), together with
the quantitative bad-set bounds, are the sibling tickets S1-B/C/D and
are out of scope here (their scaffold lives in
`OneThird/Step1/Corollaries.lean`).

## Cross-references

* `step1.tex:91-142` — `def:local-coords`, `def:good-fiber`.
* `step1.tex:144-195` — `thm:interface`; parts `part:coords`,
  `part:goodfiber` are the targets of this file.
* `step1.tex:35-58` — `lem:CNchain-width3`, the width-3 common-neighbour
  chain (Lean: `commonNbhd_isChain_of_width3`).
* `OneThird/Step1/LocalCoords.lean` — the underlying definitions.
* `OneThird/RichPair.lean` — `localInterfaceTheorem`, the parts-(i)+(ii)
  existence statement this file grounds and extends.
* `OneThird/Mathlib/BKGraph.lean` — `bkGraph`, `BKAdj`, `bkGraph_adj`.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.1 — piece-1 spec.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — The coordinate map grounded on the BK-graph vertex set

The vertices of `bkGraph α` are the linear extensions `LinearExt α`, and
the coordinate map `π_{x,y} = localCoord x y` is a map on exactly that
vertex set.  Paper part (i) (`step1.tex` `part:coords`) asserts it is
well-defined into the grid `{0,…,t}²`. -/

/-- **Coordinate map into the grid** (paper `thm:interface` part (i),
`step1.tex:148-150`).  Every linear extension of `α` — i.e. every vertex
of `bkGraph α` — has local coordinate `π_{x,y}(L) = (i(L), j(L))` inside
the `(t+1) × (t+1)` grid `{0,…,t}²`, where `t = t(x,y)` is the
common-neighbour-chain length.

This is the BK-graph-grounded form of the part-(i) coordinate bounds
`iCoord_le_commonNbhdLength` / `jCoord_le_commonNbhdLength`. -/
theorem localCoord_mem_grid (x y : α) (L : LinearExt α) :
    localCoord x y L ∈
      (Finset.range (commonNbhdLength x y + 1)) ×ˢ
        (Finset.range (commonNbhdLength x y + 1)) := by
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (localCoord_fst_le x y L),
         Nat.lt_succ_of_le (localCoord_snd_le x y L)⟩

/-! ### §2 — Good-fiber edges grounded on `bkGraph α`

Paper Def. `def:good-fiber` clause (G3) (`step1.tex:127-130`) says that
inside a good fiber the BK edges are exactly the unit grid moves of
`(i, j)` with sign preserved.  The Lean predicate `IsGoodFiber` already
encodes this with the raw adjacency `BKAdj`; the lemma below restates it
against `(bkGraph α).Adj`, making the grounding on the graph explicit. -/

/-- **Good-fiber edges are BK-graph edges = unit grid moves + sign flip**
(paper Def. `def:good-fiber` clause (G3), `step1.tex:123-127`, grounded
on `bkGraph α`).

For a good fiber `F` and two of its members `L₁, L₂`, the pair is an
edge of the Bubley–Karzanov graph `bkGraph α` **iff** either the two
share a sign and their local coordinates differ by a single unit grid
step `±e₁` / `±e₂`, or they carry opposite sign with `π_{x,y}`
unchanged on the diagonal `i = j` (the `{x, y}`-swap of paper part
(iii) case (b)). -/
theorem goodFiber_bkGraph_adj_iff {x y : α} {F : Finset (LinearExt α)}
    (hF : IsGoodFiber x y F) {L₁ L₂ : LinearExt α}
    (h₁ : L₁ ∈ F) (h₂ : L₂ ∈ F) :
    (bkGraph α).Adj L₁ L₂ ↔
      ((signMarker x y L₁ = signMarker x y L₂ ∧
        ((iCoord x y L₁ = iCoord x y L₂ + 1 ∧
              jCoord x y L₁ = jCoord x y L₂) ∨
         (iCoord x y L₂ = iCoord x y L₁ + 1 ∧
              jCoord x y L₁ = jCoord x y L₂) ∨
         (jCoord x y L₁ = jCoord x y L₂ + 1 ∧
              iCoord x y L₁ = iCoord x y L₂) ∨
         (jCoord x y L₂ = jCoord x y L₁ + 1 ∧
              iCoord x y L₁ = iCoord x y L₂))) ∨
       (signMarker x y L₁ = ! signMarker x y L₂ ∧
        iCoord x y L₁ = iCoord x y L₂ ∧
        jCoord x y L₁ = jCoord x y L₂ ∧
        iCoord x y L₁ = jCoord x y L₁)) :=
  bkGraph_adj.trans (hF.2.2 L₁ h₁ L₂ h₂)

/-! ### §3 — Part (i): coordinate map, grounded -/

/-- **Local interface theorem, part (i) — coordinate map**
(paper `thm:interface` `part:coords`, `step1.tex:148-150`), grounded on
the BK graph.

For a width-3 poset `α` and a rich pair `(x, y)`:

1. the common-neighbour set `N(x, y)` is a **chain** (this is the
   width-3 content — paper `lem:CNchain-width3`, the input that makes
   the coordinate map "encode positions in the sorted common chain");
2. the coordinate map `π_{x,y}` sends every vertex of `bkGraph α` into
   the grid `{0,…,t}²`.

The width hypothesis `hP` and the incomparability `hxy.1` are both
load-bearing: they feed `commonNbhd_isChain_of_width3` for clause (1). -/
theorem localInterface_coordMap_groundSet
    (hP : HasWidthAtMost α 3) (T : ℕ) (x y : α) (hxy : IsRich T x y) :
    IsChain (· ≤ ·) (commonNbhd x y) ∧
    (∀ L : LinearExt α,
        localCoord x y L ∈
          (Finset.range (commonNbhdLength x y + 1)) ×ˢ
            (Finset.range (commonNbhdLength x y + 1))) :=
  ⟨commonNbhd_isChain_of_width3 hP hxy.1, fun L => localCoord_mem_grid x y L⟩

/-! ### §4 — Part (ii): raw-fiber decomposition, grounded -/

/-- **Local interface theorem, part (ii) — raw-fiber decomposition**
(paper `thm:interface` `part:goodfiber`, `step1.tex:153-154`), grounded
on the BK graph.

The vertex set `V(bkGraph α) = LinearExt α` decomposes as:

1. the **raw fibers cover** every vertex: each linear extension lies in
   the raw fiber anchored at itself with its own sign;
2. the **good/bad partition** `L(P) = F_{x,y} ⊔ Bad_{x,y}` holds — the
   good-fiber set and the bad set cover all vertices and are disjoint.

Per the paper, the part-(ii) partition is "by definition" (the raw
fibers are the classes of an equivalence relation, and `Bad_{x,y}` is
the complement of `F_{x,y}`), so it needs no width hypothesis. -/
theorem localInterface_rawFiber_groundSet (x y : α) :
    ((Finset.univ : Finset (LinearExt α)).biUnion
        (fun L₀ => rawFiber x y L₀) = Finset.univ) ∧
    (goodFiberSet x y ∪ badSet x y = Finset.univ) ∧
    (Disjoint (goodFiberSet x y) (badSet x y)) :=
  ⟨rawFiber_biUnion_univ x y, goodFiberSet_union_badSet x y,
   goodFiberSet_disjoint_badSet x y⟩

/-! ### §5 — Parts (i) + (ii) bundled -/

/-- **Local interface theorem, parts (i) + (ii)**, grounded on the BK
graph (paper `thm:interface` `part:coords` + `part:goodfiber`,
`step1.tex:144-195`).

The single-call grounded surface bundling
`localInterface_coordMap_groundSet` (the coordinate map into `{0,…,t}²`
plus the width-3 common-neighbour chain) with
`localInterface_rawFiber_groundSet` (the raw-fiber cover and the
good/bad partition of `V(bkGraph α)`).

This is the part-1 deliverable of the Step 1 cascade port; it extends
`OneThird.localInterfaceTheorem` (`RichPair.lean`) by adding the
BK-graph-grounded grid form of part (i), the common-neighbour-chain
clause, and the raw-fiber cover. -/
theorem localInterface_groundSet
    (hP : HasWidthAtMost α 3) (T : ℕ) (x y : α) (hxy : IsRich T x y) :
    (IsChain (· ≤ ·) (commonNbhd x y) ∧
     ∀ L : LinearExt α,
       localCoord x y L ∈
         (Finset.range (commonNbhdLength x y + 1)) ×ˢ
           (Finset.range (commonNbhdLength x y + 1))) ∧
    ((Finset.univ : Finset (LinearExt α)).biUnion
        (fun L₀ => rawFiber x y L₀) = Finset.univ ∧
     goodFiberSet x y ∪ badSet x y = Finset.univ ∧
     Disjoint (goodFiberSet x y) (badSet x y)) :=
  ⟨localInterface_coordMap_groundSet hP T x y hxy,
   localInterface_rawFiber_groundSet x y⟩

/-! ### §6 — Non-triviality witness: the 3-element antichain

Per the mg-30e3 acceptance bar, the port must instantiate
non-vacuously at a concrete width-3 non-chain poset, with no
Subsingleton-on-empty degeneracy.  The minimal such poset is the
**3-element antichain** `Antichain3`: carrier `Fin 3`, discrete order
(`a ≤ b ↔ a = b`), so all three elements are pairwise incomparable and
the width is exactly `3`. -/

/-- The non-triviality witness: a 3-element antichain.  Carrier type
`Fin 3`; the order is **discrete** (`a ≤ b ↔ a = b`), so all three
elements are pairwise incomparable, the poset has width exactly `3`,
and it is not a chain. -/
def Antichain3 : Type := Fin 3

namespace Antichain3

instance : DecidableEq Antichain3 := inferInstanceAs (DecidableEq (Fin 3))

instance : Fintype Antichain3 := inferInstanceAs (Fintype (Fin 3))

/-- The discrete partial order on `Antichain3`: `a ≤ b` iff `a = b`. -/
instance : PartialOrder Antichain3 where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ h₁ h₂ => h₁.trans h₂
  le_antisymm := fun _ _ h _ => h

/-- The three elements of the antichain. -/
abbrev a0 : Antichain3 := (0 : Fin 3)
/-- The three elements of the antichain. -/
abbrev a1 : Antichain3 := (1 : Fin 3)
/-- The three elements of the antichain. -/
abbrev a2 : Antichain3 := (2 : Fin 3)

/-- On `Antichain3` the order relation is literally equality. -/
lemma le_iff_eq {x y : Antichain3} : x ≤ y ↔ x = y := Iff.rfl

/-- On `Antichain3`, two elements are incomparable iff they are
distinct: the order is discrete, so every distinct pair forms an
antichain. -/
lemma incomp_iff_ne {x y : Antichain3} : x ∥ y ↔ x ≠ y := by
  constructor
  · intro h heq
    exact h.1 (le_iff_eq.mpr heq)
  · intro h
    exact ⟨fun hle => h (le_iff_eq.mp hle),
           fun hle => h (le_iff_eq.mp hle).symm⟩

/-- `Antichain3` has exactly three elements. -/
lemma card_eq : Fintype.card Antichain3 = 3 := by decide

/-- Every equivalence `Antichain3 ≃ Fin (card)` is a linear extension:
the discrete order imposes no constraint, since `x ≤ y` forces `x = y`
and hence `e x = e y`. -/
def linExtOfEquiv (e : Antichain3 ≃ Fin (Fintype.card Antichain3)) :
    LinearExt Antichain3 where
  toFun := e
  monotone := fun {x y} h => le_of_eq (by rw [le_iff_eq.mp h])

/-- `linExtOfEquiv` is injective: the underlying equivalence is recovered
as the `toFun` field. -/
lemma linExtOfEquiv_injective : Function.Injective linExtOfEquiv := by
  intro e₁ e₂ h
  have h' : (linExtOfEquiv e₁).toFun = (linExtOfEquiv e₂).toFun :=
    congrArg LinearExt.toFun h
  exact h'

/-- **`Antichain3` is genuinely width-3 bounded.**  Every antichain has
at most three elements (indeed every finset does, since `|Antichain3| =
3`). -/
lemma hasWidthAtMost : HasWidthAtMost Antichain3 3 := by
  intro s _
  calc s.card ≤ Fintype.card Antichain3 := Finset.card_le_univ s
    _ = 3 := card_eq

/-- **`Antichain3` has width exactly 3.**  The full set is an antichain
of size `3`, so the width is not merely `≤ 3` but exactly `3` — the
witness is genuinely a width-3 poset, not a degenerate lower-width one. -/
lemma hasWidth : HasWidth Antichain3 3 := by
  refine ⟨hasWidthAtMost, Finset.univ, ?_, ?_⟩
  · intro a _ b _ hab hle
    exact hab (le_iff_eq.mp hle)
  · rw [Finset.card_univ, card_eq]

/-- **`Antichain3` is not a chain.**  The elements `a0` and `a1` are
incomparable, so the poset is genuinely non-chain. -/
lemma not_isChainPoset : ¬ IsChainPoset Antichain3 := by
  intro h
  rcases h a0 a1 with hle | hle
  · exact absurd (le_iff_eq.mp hle) (by decide)
  · exact absurd (le_iff_eq.mp hle) (by decide)

/-- The common-neighbour set of the rich pair `(a0, a1)` is the
singleton `{a2}`: `a2` is the unique element incomparable to both. -/
lemma commonNbhdFinset_a0_a1 :
    commonNbhdFinset a0 a1 = {a2} := by
  classical
  ext z
  unfold commonNbhdFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, incomp_iff_ne]
  exact (by decide : ∀ w : Antichain3, (w ≠ a0 ∧ w ≠ a1) ↔ w = a2) z

/-- The common-neighbour-chain length of the rich pair `(a0, a1)` is
`t(a0, a1) = 1`: a genuinely positive length, so the coordinate
codomain `{0,…,t}²` is the honest `2 × 2` grid `{0,1}²`. -/
lemma commonNbhdLength_a0_a1 : commonNbhdLength a0 a1 = 1 := by
  unfold commonNbhdLength
  rw [commonNbhdFinset_a0_a1, Finset.card_singleton]

/-- `(a0, a1)` is a **genuine rich pair** at threshold `1`: it is an
incomparable pair, and its common-neighbour chain has length
`1 ≥ 1`. -/
lemma isRich_a0_a1 : IsRich 1 a0 a1 :=
  ⟨incomp_iff_ne.mpr (by decide), le_of_eq commonNbhdLength_a0_a1.symm⟩

/-- **`Antichain3` has at least two linear extensions.**  Hence the
linear-extension set that the raw fibers decompose is genuinely *not a
subsingleton* — this explicitly rebuts a "Subsingleton-on-empty"
degenerate baseline.

The proof exhibits two distinct linear extensions: a base extension
`linExtOfEquiv e` (any bijection is order-preserving on the discrete
order) and the one obtained by post-composing with a transposition of
two index positions. -/
lemma two_le_numLinExt : 2 ≤ numLinExt Antichain3 := by
  classical
  have hcard : Fintype.card Antichain3 = 3 := card_eq
  -- two distinct index positions in `Fin (card Antichain3)`
  let p0 : Fin (Fintype.card Antichain3) := ⟨0, by rw [hcard]; omega⟩
  let p1 : Fin (Fintype.card Antichain3) := ⟨1, by rw [hcard]; omega⟩
  have hp : p0 ≠ p1 := by
    intro h
    have hv : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  -- a base linear extension and the transposed one
  let e : Antichain3 ≃ Fin (Fintype.card Antichain3) := Fintype.equivFin Antichain3
  let L0 : LinearExt Antichain3 := linExtOfEquiv e
  let L1 : LinearExt Antichain3 := linExtOfEquiv (e.trans (Equiv.swap p0 p1))
  have hL : L0 ≠ L1 := by
    intro hL01
    have htf : e = e.trans (Equiv.swap p0 p1) :=
      linExtOfEquiv_injective hL01
    have happ := congrArg
      (fun f : Antichain3 ≃ Fin (Fintype.card Antichain3) => f (e.symm p0)) htf
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.swap_apply_left] at happ
    exact hp happ
  -- so there are at least two linear extensions
  have hpair : ({L0, L1} : Finset (LinearExt Antichain3)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hL]), Finset.card_singleton]
  have hle : ({L0, L1} : Finset (LinearExt Antichain3)).card ≤
      Fintype.card (LinearExt Antichain3) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  change 2 ≤ Fintype.card (LinearExt Antichain3)
  omega

/-- **The Step 1 coordinate map + raw-fiber decomposition instantiate
non-vacuously at a concrete width-3 non-chain poset.**

This is the mg-30e3 (OneThird-S1-A) acceptance witness.  At the concrete
3-element antichain `Antichain3` with rich pair `(a0, a1)`:

* the poset has **width exactly 3** and is **genuinely not a chain** —
  the hypotheses of `localInterface_groundSet` are satisfiable, not
  vacuously quantified;
* `IsRich 1 a0 a1` holds with `t(a0, a1) = 1`, so the coordinate
  codomain `{0,…,t}²` is the honest `2 × 2` grid `{0,1}²` — a genuine
  two-dimensional codomain, not a degenerate single point;
* `2 ≤ numLinExt Antichain3`: the linear-extension set decomposed by the
  raw fibers is **not a subsingleton** — no Subsingleton-on-empty
  degeneracy;
* the width-3 common-neighbour-chain conclusion fires
  (`IsChain (· ≤ ·) (commonNbhd a0 a1)`);
* the part-(i) coordinate map lands in the `2 × 2` grid and the
  part-(ii) good/bad partition holds.

All of these are obtained by *actually firing* the grounded interface
theorem `localInterface_groundSet`, confirming it is non-vacuous. -/
theorem localInterface_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    IsRich 1 a0 a1 ∧
    commonNbhdLength a0 a1 = 1 ∧
    2 ≤ numLinExt Antichain3 ∧
    IsChain (· ≤ ·) (commonNbhd a0 a1) ∧
    (∀ L : LinearExt Antichain3,
        localCoord a0 a1 L ∈ (Finset.range 2) ×ˢ (Finset.range 2)) ∧
    (goodFiberSet a0 a1 ∪ badSet a0 a1 = Finset.univ ∧
     Disjoint (goodFiberSet a0 a1) (badSet a0 a1)) := by
  obtain ⟨⟨hchain, hgrid⟩, _hcover, hpart, hdisj⟩ :=
    localInterface_groundSet hasWidthAtMost 1 a0 a1 isRich_a0_a1
  refine ⟨hasWidth, not_isChainPoset, isRich_a0_a1, commonNbhdLength_a0_a1,
    two_le_numLinExt, hchain, ?_, hpart, hdisj⟩
  intro L
  have hL := hgrid L
  rwa [commonNbhdLength_a0_a1] at hL

end Antichain3

end OneThird
