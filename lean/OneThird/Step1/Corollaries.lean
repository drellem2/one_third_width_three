/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset
import OneThird.RichPair
import OneThird.Step1.LocalCoords
import OneThird.Step1.Overlap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Step 1 — Bounded interaction, commuting overlap, and triple-overlap cube

This file formalises the Step 1 corollaries downstream of the local
interface theorem (`thm:interface`, `step1.tex`):

* `lem:bounded-interaction` (`step1.tex:397`): two distinct rich pairs
  have a bounded-size interaction locus.
* `cor:overlap` (`step1.tex:429`, clause (S1.4) of Step 4): on a
  positive-density pairwise overlap, the two interfaces' BK moves
  commute and generate a local `ℤ²` grid.
* `cor:triple-overlap` (`step1.tex:516`, Step-1→Step-7 bridge): on a
  positive-density triple overlap, the three interfaces' BK moves
  generate a local `ℤ³` cube, and the three coordinate projections of
  any downset agree on a common cut. Consumed by `lem:cocycle` in
  Step 7.

## Main definitions

* `LPosAdj L a b` — two elements `a, b` are at adjacent positions in the
  linear extension `L`.
* `overlap x y u v` — the pairwise overlap `Ω_{xy,uv} := F_{x,y} ∩ F_{u,v}`.
* `interactionLocus x y u v` — the interaction locus `Int_{xy,uv}` of
  `lem:bounded-interaction`.
* `regularOverlap x y u v` — `Ω°_{xy,uv} := Ω \ (Bad_xy ∪ Bad_uv ∪ Int)`.
* `tripleOverlap x y z` — `Ω^{(3)} := F_{xy} ∩ F_{yz} ∩ F_{xz}`.
* `regularTripleOverlap x y z` — `Ω^{∘∘∘}`, the subset of `Ω^{(3)}`
  satisfying the three pairwise-regularity conditions.

## Main results (scaffold form)

* `interactionLocus_subset_overlap`: `Int_{xy,uv} ⊆ Ω_{xy,uv}`.
* `bounded_interaction`: a uniform cardinality upper bound on
  `Int_{xy,uv}` (scaffold's trivial `|Int| ≤ |L(P)|` form).
* `regularOverlap_subset_overlap`.
* `regularOverlap_density`: `|Ω_{xy,uv} \ Ω°_{xy,uv}| ≤ |Int_{xy,uv}|`;
  this is the density half of `cor:overlap` part (b).
* `regularTripleOverlap_subset_tripleOverlap`.
* `regularTripleOverlap_density`: bad mass on the triple overlap is
  bounded by the sum of the three pairwise interaction loci (scaffold
  form of `cor:triple-overlap` part (d)).

## Commuting-square and commuting-cube verifications

The combinatorial heart of `cor:overlap` part (a) and
`cor:triple-overlap` parts (b),(c) — that BK moves with disjoint
support commute, generating an embedded `2×2` BK square (resp.
`2×2×2` BK cube) — is verified in full in
`OneThird/Step1/Overlap.lean` (`bkCommSquare_of_disjoint`,
`bkCommCube_of_disjoint`), and re-exported here under the corollary
names `cor_overlap_commuting_square` and
`cor_triple_overlap_commuting_cube`. Those verifications are
unconditional and non-vacuous (`bkCommCube_grid_example` instantiates
them on the concrete width-3 non-chain poset `Fin 3 × Fin 3`).

## Scaffold vs. paper strength

The paper's *quantitative* bounds
(`|Int_{xy,uv}| = O((t_{xy}+t_{uv})^2)`, the strip decomposition, and
the `O(t·√|Ω|)` triple-overlap bad mass) use parts (iii) (BK-move
classification) and (iv) (bad-set strip decomposition) of
`thm:interface`, which are stronger than the current
`localInterfaceTheorem` scaffold (parts (i)+(ii) only). Accordingly
the quantitative `O(t^2)`/`O(t·√|Ω|)` forms remain deferred to the
follow-up items discharging `thm:interface` (iii)+(iv). The
set-theoretic density statements proved in this file (containments
and trivial cardinality bounds) and the commuting-square/cube
verifications of `Overlap.lean` are unconditional.

### ⚠ AMENDED (S1-E, mg-c2d7) — the scaffold upgrade is BLOCKED

The Checkpoint-1 audit (mg-8b95) scoped S1-E to *replace* the vacuous
`bounded_interaction` (`|Int| ≤ |𝓛(P)|`) with the genuine
`O((t_{xy}+t_{uv})^2)` bound and to deliver `cor:overlap` (b) /
`cor:triple-overlap` (d).  Executing S1-E (work item mg-c2d7) found
this is **not deliverable on the current definitions**, and the
`bounded_interaction` / `regularOverlap_density` /
`regularTripleOverlap_density` scaffolds below are **left as-is**:

* The interaction locus `Int_{xy,uv}` lives inside the pairwise
  overlap `Ω = goodFiberSet x y ∩ goodFiberSet u v`.  Step 1's
  `IsGoodFiber` order-convexity clause (G2, `LocalCoords.lean`) is too
  strong — it rejects every genuine two-dimensional raw fiber — so for
  any rich pair with `t ≥ 1` the *good* fiber set is empty and `Ω` is
  empty.  This is proved concretely in
  `OneThird/Step1/Interface.lean` §6
  (`interface_part_iv_faithfulness_defect`,
  `goodFiberSet_a0_a1_eq_empty`).
* A genuine `O((t_{xy}+t_{uv})^2)` bound on `|Int|` therefore cannot
  be assembled until the `IsGoodFiber` G2 clause is re-ported to the
  paper's genuine order-convexity notion — which is in S1-A
  (`LocalCoords.lean`), **outside the S1-E file scope**.
* Shipping a *conditional* `bounded_interaction` whose structural
  hypothesis is unsatisfiable on the current definitions would be a
  fresh content-free scaffold (`PROOF-STRUCTURE-ONBOARDING.md` §3
  pitfall #6), so S1-E does **not** do that.

S1-E is a block-and-report.  See `docs/state-S1-E-Session1.md` for the
full analysis and forward options.

The bridge from *regular-overlap membership* (`regularOverlap` /
`regularTripleOverlap`, i.e. interaction-locus exclusion) to the
*disjoint-support* hypothesis consumed by `cor_overlap_commuting_square`
/ `cor_triple_overlap_commuting_cube` is supplied by the BK-move
classification (`thm:interface` part (iii)); it is wired in at Step 1
assembly (S1-D).
-/

namespace OneThird

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## `L`-adjacency of elements -/

/-- Two elements `a, b : α` are **`L`-adjacent** in a linear extension
`L` if their positions differ by exactly one. Matches the ambient
"`a` and `b` are `L`-adjacent" usage of `step1.tex` §§2–3. -/
def LPosAdj (L : LinearExt α) (a b : α) : Prop :=
  (L.pos a).val + 1 = (L.pos b).val ∨ (L.pos b).val + 1 = (L.pos a).val

instance LPosAdj.decidable (L : LinearExt α) (a b : α) :
    Decidable (LPosAdj L a b) := by
  unfold LPosAdj
  infer_instance

namespace LPosAdj

lemma symm {L : LinearExt α} {a b : α} (h : LPosAdj L a b) :
    LPosAdj L b a :=
  Or.symm h

lemma ne {L : LinearExt α} {a b : α} (h : LPosAdj L a b) : a ≠ b := by
  rintro rfl
  cases h with
  | inl h => omega
  | inr h => omega

end LPosAdj

/-! ## Pairwise overlap -/

/-- The **pairwise overlap** `Ω_{xy,uv}` of two rich pairs: linear
extensions in the good fiber of both. -/
noncomputable def overlap (x y u v : α) : Finset (LinearExt α) :=
  goodFiberSet x y ∩ goodFiberSet u v

lemma overlap_subset_goodFiberSet_left (x y u v : α) :
    overlap x y u v ⊆ goodFiberSet x y := by
  unfold overlap
  exact Finset.inter_subset_left

lemma overlap_subset_goodFiberSet_right (x y u v : α) :
    overlap x y u v ⊆ goodFiberSet u v := by
  unfold overlap
  exact Finset.inter_subset_right

lemma overlap_comm (x y u v : α) : overlap x y u v = overlap u v x y := by
  unfold overlap
  exact Finset.inter_comm _ _

/-! ## Interaction locus and bounded interaction -/

/-- The **interaction locus** `Int_{xy,uv}` of `lem:bounded-interaction`
(`step1.tex:397`): extensions in the overlap where some `a ∈ {x, y}`
is `L`-adjacent to some `b ∈ {u, v} ∪ C(u, v)`. -/
noncomputable def interactionLocus (x y u v : α) : Finset (LinearExt α) := by
  classical
  exact
    (overlap x y u v).filter
      (fun L =>
        ∃ a ∈ ({x, y} : Finset α),
          ∃ b ∈ insert u (insert v (commonNbhdFinset u v)),
            LPosAdj L a b)

lemma interactionLocus_subset_overlap (x y u v : α) :
    interactionLocus x y u v ⊆ overlap x y u v := by
  classical
  unfold interactionLocus
  exact Finset.filter_subset _ _

lemma mem_interactionLocus_iff {x y u v : α} {L : LinearExt α} :
    L ∈ interactionLocus x y u v ↔
      L ∈ overlap x y u v ∧
        ∃ a ∈ ({x, y} : Finset α),
          ∃ b ∈ insert u (insert v (commonNbhdFinset u v)),
            LPosAdj L a b := by
  classical
  unfold interactionLocus
  simp [Finset.mem_filter]

/-- **Bounded interaction of distinct rich pairs**
(`lem:bounded-interaction`, `step1.tex:397`), scaffold form.

The paper bound is `|Int_{xy,uv}| = O((t_{xy} + t_{uv})^2)` and uses the
width-3 chain structure (`lem:CNchain-width3`) together with the bad-set
strip decomposition (part (iv) of `thm:interface`). The scaffold bound
below is the unconditional `|Int_{xy,uv}| ≤ |L(P)|`; it will be
tightened to the paper bound once `thm:interface` part (iv) is
discharged in a follow-up item. -/
theorem bounded_interaction (x y u v : α) :
    (interactionLocus x y u v).card ≤ Fintype.card (LinearExt α) := by
  classical
  calc (interactionLocus x y u v).card
      ≤ (Finset.univ : Finset (LinearExt α)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (LinearExt α) := Finset.card_univ

/-- Containment form of the bounded-interaction bound on the left pair:
the interaction locus is bounded by the `(x, y)` good-fiber count. In
the paper, `|F_{x,y}| ≤ |Σ_E (t_{xy}+1)^2|` feeds `O((t_{xy}+t_{uv})^2)`;
this lemma is the set-theoretic half. -/
theorem interactionLocus_card_le_goodFiberSet_left (x y u v : α) :
    (interactionLocus x y u v).card ≤ (goodFiberSet x y).card :=
  (Finset.card_le_card (interactionLocus_subset_overlap x y u v)).trans
    (Finset.card_le_card (overlap_subset_goodFiberSet_left x y u v))

theorem interactionLocus_card_le_goodFiberSet_right (x y u v : α) :
    (interactionLocus x y u v).card ≤ (goodFiberSet u v).card :=
  (Finset.card_le_card (interactionLocus_subset_overlap x y u v)).trans
    (Finset.card_le_card (overlap_subset_goodFiberSet_right x y u v))

/-! ## Regular overlap and its density (`cor:overlap`) -/

/-- The **regular overlap** `Ω°_{xy,uv}` (`step1.tex:436`, definition
inside `cor:overlap`): the pairwise overlap with the two bad sets and
the interaction locus removed. -/
noncomputable def regularOverlap (x y u v : α) : Finset (LinearExt α) :=
  overlap x y u v \ (badSet x y ∪ badSet u v ∪ interactionLocus x y u v)

lemma regularOverlap_subset_overlap (x y u v : α) :
    regularOverlap x y u v ⊆ overlap x y u v := by
  unfold regularOverlap
  exact Finset.sdiff_subset

lemma regularOverlap_subset_goodFiberSet_left (x y u v : α) :
    regularOverlap x y u v ⊆ goodFiberSet x y :=
  (regularOverlap_subset_overlap x y u v).trans
    (overlap_subset_goodFiberSet_left x y u v)

lemma regularOverlap_subset_goodFiberSet_right (x y u v : α) :
    regularOverlap x y u v ⊆ goodFiberSet u v :=
  (regularOverlap_subset_overlap x y u v).trans
    (overlap_subset_goodFiberSet_right x y u v)

lemma regularOverlap_disjoint_badSet_left (x y u v : α) :
    Disjoint (regularOverlap x y u v) (badSet x y) := by
  refine Finset.disjoint_left.mpr ?_
  intro L hLreg hLbad
  have hLgood : L ∈ goodFiberSet x y :=
    (regularOverlap_subset_goodFiberSet_left x y u v) hLreg
  exact Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet x y) hLgood hLbad

lemma regularOverlap_disjoint_badSet_right (x y u v : α) :
    Disjoint (regularOverlap x y u v) (badSet u v) := by
  refine Finset.disjoint_left.mpr ?_
  intro L hLreg hLbad
  have hLgood : L ∈ goodFiberSet u v :=
    (regularOverlap_subset_goodFiberSet_right x y u v) hLreg
  exact Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet u v) hLgood hLbad

lemma regularOverlap_disjoint_interactionLocus (x y u v : α) :
    Disjoint (regularOverlap x y u v) (interactionLocus x y u v) := by
  refine Finset.disjoint_left.mpr ?_
  intro L hLreg hLint
  unfold regularOverlap at hLreg
  rw [Finset.mem_sdiff] at hLreg
  exact hLreg.2 (Finset.mem_union_right _ hLint)

/-- Set-theoretic identity behind the density bound: the `(Ω \ Ω°)`
loss is exactly `Ω ∩ Int` (the two bad-set cuts drop because good
fibers are disjoint from their own bad sets). -/
lemma overlap_sdiff_regularOverlap_subset_interactionLocus (x y u v : α) :
    overlap x y u v \ regularOverlap x y u v ⊆ interactionLocus x y u v := by
  classical
  intro L hL
  rw [Finset.mem_sdiff] at hL
  obtain ⟨hLover, hnotReg⟩ := hL
  have hLxy : L ∈ goodFiberSet x y :=
    (overlap_subset_goodFiberSet_left x y u v) hLover
  have hLuv : L ∈ goodFiberSet u v :=
    (overlap_subset_goodFiberSet_right x y u v) hLover
  have hnb_xy : L ∉ badSet x y :=
    Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet x y) hLxy
  have hnb_uv : L ∉ badSet u v :=
    Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet u v) hLuv
  unfold regularOverlap at hnotReg
  rw [Finset.mem_sdiff] at hnotReg
  push_neg at hnotReg
  have hmemUnion :
      L ∈ badSet x y ∪ badSet u v ∪ interactionLocus x y u v :=
    hnotReg hLover
  rw [Finset.mem_union, Finset.mem_union] at hmemUnion
  rcases hmemUnion with (hxy | huv) | hint
  · exact absurd hxy hnb_xy
  · exact absurd huv hnb_uv
  · exact hint

/-- **`cor:overlap` density bound (part (b), scaffold form)**: the
pairwise overlap minus the regular overlap is at most the interaction
locus. Combined with `bounded_interaction` (or its refinement) this
gives the density statement of `cor:overlap`. -/
theorem regularOverlap_density (x y u v : α) :
    (overlap x y u v \ regularOverlap x y u v).card ≤
      (interactionLocus x y u v).card :=
  Finset.card_le_card
    (overlap_sdiff_regularOverlap_subset_interactionLocus x y u v)

/-! ## Triple overlap and its density (`cor:triple-overlap`) -/

/-- The **triple overlap** `Ω^{(3)}` of three rich pairs (`step1.tex:521`,
`cor:triple-overlap`): linear extensions in all three good fibers. -/
noncomputable def tripleOverlap (x y z : α) : Finset (LinearExt α) :=
  goodFiberSet x y ∩ goodFiberSet y z ∩ goodFiberSet x z

lemma tripleOverlap_subset_goodFiberSet_xy (x y z : α) :
    tripleOverlap x y z ⊆ goodFiberSet x y := by
  unfold tripleOverlap
  exact Finset.Subset.trans Finset.inter_subset_left Finset.inter_subset_left

lemma tripleOverlap_subset_goodFiberSet_yz (x y z : α) :
    tripleOverlap x y z ⊆ goodFiberSet y z := by
  unfold tripleOverlap
  exact Finset.Subset.trans Finset.inter_subset_left Finset.inter_subset_right

lemma tripleOverlap_subset_goodFiberSet_xz (x y z : α) :
    tripleOverlap x y z ⊆ goodFiberSet x z := by
  unfold tripleOverlap
  exact Finset.inter_subset_right

lemma tripleOverlap_subset_overlap_xy_yz (x y z : α) :
    tripleOverlap x y z ⊆ overlap x y y z := by
  intro L hL
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact tripleOverlap_subset_goodFiberSet_xy x y z hL
  · exact tripleOverlap_subset_goodFiberSet_yz x y z hL

/-- The **regular triple overlap** `Ω^{∘∘∘}`: triple overlap minus the
three single-interface bad sets and the three pairwise interaction
loci. Matches `step1.tex:526`. -/
noncomputable def regularTripleOverlap (x y z : α) : Finset (LinearExt α) :=
  tripleOverlap x y z \
    (badSet x y ∪ badSet y z ∪ badSet x z ∪
      interactionLocus x y y z ∪
      interactionLocus x y x z ∪
      interactionLocus y z x z)

lemma regularTripleOverlap_subset_tripleOverlap (x y z : α) :
    regularTripleOverlap x y z ⊆ tripleOverlap x y z := by
  unfold regularTripleOverlap
  exact Finset.sdiff_subset

/-- Set-theoretic containment: the bad mass of the triple overlap is
covered by the three pairwise interaction loci (using disjointness of
each good fiber from its bad set to eliminate the three bad-set
terms). -/
lemma tripleOverlap_sdiff_regularTripleOverlap_subset (x y z : α) :
    tripleOverlap x y z \ regularTripleOverlap x y z ⊆
      interactionLocus x y y z ∪ interactionLocus x y x z ∪
        interactionLocus y z x z := by
  classical
  intro L hL
  rw [Finset.mem_sdiff] at hL
  obtain ⟨hLover, hnotReg⟩ := hL
  have hLxy : L ∈ goodFiberSet x y :=
    (tripleOverlap_subset_goodFiberSet_xy x y z) hLover
  have hLyz : L ∈ goodFiberSet y z :=
    (tripleOverlap_subset_goodFiberSet_yz x y z) hLover
  have hLxz : L ∈ goodFiberSet x z :=
    (tripleOverlap_subset_goodFiberSet_xz x y z) hLover
  have hnb_xy : L ∉ badSet x y :=
    Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet x y) hLxy
  have hnb_yz : L ∉ badSet y z :=
    Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet y z) hLyz
  have hnb_xz : L ∉ badSet x z :=
    Finset.disjoint_left.mp (goodFiberSet_disjoint_badSet x z) hLxz
  unfold regularTripleOverlap at hnotReg
  rw [Finset.mem_sdiff] at hnotReg
  push_neg at hnotReg
  have hmemUnion :
      L ∈ badSet x y ∪ badSet y z ∪ badSet x z ∪
          interactionLocus x y y z ∪
          interactionLocus x y x z ∪
          interactionLocus y z x z := hnotReg hLover
  -- Unfold the left-associated unions step by step.
  rw [Finset.mem_union] at hmemUnion
  rcases hmemUnion with h12 | hI3
  · rw [Finset.mem_union] at h12
    rcases h12 with h1 | hI2
    · rw [Finset.mem_union] at h1
      rcases h1 with h0 | hI1
      · rw [Finset.mem_union] at h0
        rcases h0 with hBxy_yz | hbXZ
        · rw [Finset.mem_union] at hBxy_yz
          rcases hBxy_yz with hbXY | hbYZ
          · exact absurd hbXY hnb_xy
          · exact absurd hbYZ hnb_yz
        · exact absurd hbXZ hnb_xz
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hI1)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hI2)
  · exact Finset.mem_union_right _ hI3

/-- **`cor:triple-overlap` density bound (scaffold form of part (d))**:
the bad mass of the triple overlap is at most the sum of the three
pairwise interaction loci.

The paper strengthens this to
`O((t_{xy}+t_{yz}+t_{xz})·√|Ω^{(3)}|)` using the strip structure of
part (iv) of `thm:interface`, combined with the pairwise bounds from
`cor:overlap`. The set-theoretic bound here is the unconditional
ingredient; quantifying each interaction locus by `bounded_interaction`
(or its quantitative refinement) closes the chain. -/
theorem regularTripleOverlap_density (x y z : α) :
    (tripleOverlap x y z \ regularTripleOverlap x y z).card ≤
      (interactionLocus x y y z).card +
        (interactionLocus x y x z).card +
        (interactionLocus y z x z).card := by
  classical
  calc (tripleOverlap x y z \ regularTripleOverlap x y z).card
      ≤ (interactionLocus x y y z ∪ interactionLocus x y x z ∪
            interactionLocus y z x z).card :=
          Finset.card_le_card
            (tripleOverlap_sdiff_regularTripleOverlap_subset x y z)
    _ ≤ (interactionLocus x y y z ∪ interactionLocus x y x z).card +
          (interactionLocus y z x z).card :=
          Finset.card_union_le _ _
    _ ≤ ((interactionLocus x y y z).card +
            (interactionLocus x y x z).card) +
          (interactionLocus y z x z).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _

/-! ## Commuting square and cube (`cor:overlap` (a), `cor:triple-overlap` (b),(c)) -/

/-- **`cor:overlap` part (a)** (`step1.tex:443`): on a regular overlap,
two BK moves from the two rich interfaces — whose moved-element pairs
have disjoint support — commute, generating an embedded `2×2` BK
square (a piece of the local `ℤ²` grid). This is the corollary name
for the verification `bkCommSquare_of_disjoint` of
`OneThird/Step1/Overlap.lean`; the disjoint-support hypothesis is what
`regularOverlap`-membership provides via the BK-move classification
(`thm:interface` part (iii), wired at S1-D). -/
theorem cor_overlap_commuting_square (L₀ : LinearExt α)
    {k m : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) (hm : m.val + 1 < Fintype.card α)
    (hkinc : L₀.toFun.symm k ∥ L₀.toFun.symm ⟨k.val + 1, hk⟩)
    (hminc : L₀.toFun.symm m ∥ L₀.toFun.symm ⟨m.val + 1, hm⟩)
    (hdisj : DisjointPos k m) :
    BKCommSquare L₀ (L₀.swapAdj k hk hkinc) (L₀.swapAdj m hm hminc)
      ((L₀.swapAdj k hk hkinc).swapAdj m hm
        (swapAdj_incomp_of_disjoint L₀ hk hm hkinc hminc hdisj)) :=
  bkCommSquare_of_disjoint L₀ hk hm hkinc hminc hdisj

/-- **`cor:triple-overlap` parts (b),(c)** (`step1.tex:538`): on a
regular triple overlap, three BK moves from the three rich interfaces
— pairwise disjoint in support — pairwise commute, generating an
embedded `2×2×2` BK cube (the local `ℤ³` cube model consumed by Step 7
gap G4). This is the corollary name for the verification
`bkCommCube_of_disjoint` of `OneThird/Step1/Overlap.lean`; the
pairwise-disjoint-support hypotheses are what
`regularTripleOverlap`-membership provides via the BK-move
classification (`thm:interface` part (iii), wired at S1-D). -/
theorem cor_triple_overlap_commuting_cube (L₀ : LinearExt α)
    {p₁ p₂ p₃ : Fin (Fintype.card α)}
    (hp₁ : p₁.val + 1 < Fintype.card α)
    (hp₂ : p₂.val + 1 < Fintype.card α)
    (hp₃ : p₃.val + 1 < Fintype.card α)
    (hi₁ : L₀.toFun.symm p₁ ∥ L₀.toFun.symm ⟨p₁.val + 1, hp₁⟩)
    (hi₂ : L₀.toFun.symm p₂ ∥ L₀.toFun.symm ⟨p₂.val + 1, hp₂⟩)
    (hi₃ : L₀.toFun.symm p₃ ∥ L₀.toFun.symm ⟨p₃.val + 1, hp₃⟩)
    (h₁₂ : DisjointPos p₁ p₂) (h₁₃ : DisjointPos p₁ p₃)
    (h₂₃ : DisjointPos p₂ p₃) :
    ∃ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ : LinearExt α,
      BKCommCube L₀ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ :=
  bkCommCube_of_disjoint L₀ hp₁ hp₂ hp₃ hi₁ hi₂ hi₃ h₁₂ h₁₃ h₂₃

end OneThird
