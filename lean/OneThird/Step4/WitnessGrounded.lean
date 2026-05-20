/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step1.Overlap
import OneThird.Step1.BKMoves
import OneThird.Step3.LocalSignGrounded
import OneThird.Mathlib.SimpleGraph.EdgeBoundary

/-!
# Step 4 — grounded port, part 1: `thm:step4` statement + BK-edge witness family

This file is the **FULL REFACTOR Piece 1, Wave-3 S4-A** grounded port of
`step4.tex` part 1.  Where the abstract Step 4 scaffold
(`OneThird.Step4.RectangleModel`, `OneThird.Step4.Step4Theorem`)
modelled the BK graph by an opaque type `Edge` and the witness families
by an opaque `witness : Pair → Pair → Finset Edge`, this file **grounds
those objects on the concrete Bubley–Karzanov graph** `bkGraph α`:

* the BK boundary `∂_BK S` is the genuine `SimpleGraph.edgeBoundary` of
  `bkGraph α` — a `Finset (Sym2 (LinearExt α))` of real BK edges;
* a *conflict `2×2` square* is a genuine commuting BK square
  (`BKCommSquare`, the Step 1 `cor:overlap` output) on which the cut
  indicator `1_S` is non-constant;
* the *witness family* `E_{α,β}` of `step4.tex:1167` is the union of the
  cut edges of the conflict squares lying in **incoherent blocks**,
  where incoherence is the Step 3 `def:coherent`/`def:eta` notion.

## What this file delivers (S4-A scope)

`step4.tex` Step 4 splits across three Wave-3 tickets.  S4-A ports the
**statement** of `thm:step4` and **constructs the witness family**; the
per-block incompatibility proof (`lem:rect-stable-area`, `lem:22`) is
S4-B and the global counting / density regularization (`prop:G5`,
`lem:G6`) is S4-C.

* `bkBoundary` — the BK boundary `∂_BK S`, grounded on `edgeBoundary`.
* `BKSquare` / `squareEdges` / `IsConflictSquare` — the conflict-square
  notion, grounded on `BKCommSquare`.
* `lem22_bk` — `lem:22` (`step4.tex:687`) grounded: a conflict square
  has a cut edge among its four BK edges.
* `witnessFamily` — **the construction**: the BK-edge witness family in
  the incoherent locus, `E_{α,β}` of `step4.tex:1167`.
* `witnessFamily_subset_bkBoundary` — every witness edge is a genuine
  BK cut edge (the structural fact S4-C's `lem:G6` double-counting
  needs).
* `BlockIncoherent` — the *incoherent block* predicate
  (`step4.tex:1142`), grounded on the Step 3 `def:eta` η.
* `Step4Conclusion` / `thm_step4_grounded` — **the statement** of
  `thm:step4` (`step4.tex:93`), grounded, plus the witness→boundary
  reduction `c·(δ−Cε)·|Ω°| ≤ |E_{α,β}| ⇒ thm:step4`.
* `witnessGrounded_nonvacuous` — the S4-A non-vacuity acceptance
  witness at the genuine width-3 non-chain grid poset `Fin 3 × Fin 3`.

## What `consumes`

* **Step 1** — `BKCommSquare` / `bkCommSquare_of_disjoint`
  (`cor:overlap` (a), the overlap-commutation output): the conflict
  squares *are* commuting BK squares.
* **Step 2** — the per-fiber staircase error `ε` of
  `thm:step2-cited`; it enters `thm:step4` as the `eps` slack term.
  (S4-A ports the *statement*; `ε` is a parameter here, threaded
  concretely by S4-B/C.)
* **Step 3** — `etaOnState` / `disagreeSet` / `IncoherentPair`
  (`def:eta` + `def:coherent`): the incoherent-locus filter.

## Downstream

* S4-B (`lem:rect-stable-area`) lower-bounds `|E_{α,β}|` on each
  incoherent block; S4-C sums it (`prop:G5`) and feeds the per-pair
  bound into `thm_step4_grounded`.
* Step 6 consumes the witness family through `lem:G6`.
-/

namespace OneThird
namespace Step4

open Finset
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- BK-adjacency on `bkGraph α` is decidable (classically): the witness
family / boundary constructions are `Finset`s over the noncomputable
`Fintype (LinearExt α)`, so this instance only feeds the `Finset`
machinery; it is never `decide`d. -/
noncomputable instance bkAdjDecidable :
    DecidableRel ((bkGraph α).Adj) :=
  fun a b => Classical.propDecidable ((bkGraph α).Adj a b)

/-! ## §1 — The BK boundary `∂_BK S`, grounded on `edgeBoundary`

`step4.tex:24`: for a cut `S ⊆ 𝓛(P)`, `∂_BK S` is the set of BK edges
with exactly one endpoint in `S`.  Grounded: this is exactly the
`SimpleGraph.edgeBoundary` of the Bubley–Karzanov graph `bkGraph α`. -/

/-- The **BK boundary** `∂_BK S` of a cut `S ⊆ 𝓛(P)`: the finset of
edges of `bkGraph α` with exactly one endpoint in `S`
(`step4.tex:24`). -/
noncomputable def bkBoundary (S : Finset (LinearExt α)) :
    Finset (Sym2 (LinearExt α)) :=
  (bkGraph α).edgeBoundary S

/-- Membership in `∂_BK S`: a BK edge `s(L, L')` crosses the cut iff
`L, L'` are BK-adjacent and exactly one of them lies in `S`. -/
theorem mem_bkBoundary {S : Finset (LinearExt α)} {L L' : LinearExt α} :
    s(L, L') ∈ bkBoundary S ↔
      BKAdj L L' ∧ ((L ∈ S ∧ L' ∉ S) ∨ (L ∉ S ∧ L' ∈ S)) := by
  unfold bkBoundary
  rw [mk_mem_edgeBoundary_iff, bkGraph_adj]

/-- Every boundary edge is genuinely a BK edge: it has the form
`s(L, L')` with `L, L'` BK-adjacent. -/
theorem bkAdj_of_mem_bkBoundary {S : Finset (LinearExt α)}
    {e : Sym2 (LinearExt α)} (he : e ∈ bkBoundary S) :
    ∃ L L', e = s(L, L') ∧ BKAdj L L' := by
  unfold bkBoundary at he
  obtain ⟨u, v, rfl, huv, _, _⟩ := mem_edgeBoundary.mp he
  exact ⟨u, v, rfl, bkGraph_adj.mp huv⟩

/-! ## §2 — Conflict `2×2` squares, grounded on `BKCommSquare`

`step4.tex:687` (`lem:22`): a `2×2` BK square `{L₀,L₁,L₂,L₃}` on which
the cut indicator `1_S` is non-constant has a cut edge.  Grounded: the
square is a genuine commuting BK square (`BKCommSquare`, the Step 1
`cor:overlap` (a) output, `Step1/Overlap.lean`). -/

/-- The four corners of a `2×2` BK square, in the `BKCommSquare`
naming: `c0–c1`, `c0–c2`, `c1–c3`, `c2–c3` are the four edges. -/
structure BKSquare (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] where
  /-- The base corner. -/
  c0 : LinearExt α
  /-- The corner reached by the first generator. -/
  c1 : LinearExt α
  /-- The corner reached by the second generator. -/
  c2 : LinearExt α
  /-- The apex corner. -/
  c3 : LinearExt α

/-- The four BK edges of a `2×2` square, as a `Finset (Sym2 _)`. -/
def squareEdges (q : BKSquare α) : Finset (Sym2 (LinearExt α)) :=
  {s(q.c0, q.c1), s(q.c0, q.c2), s(q.c1, q.c3), s(q.c2, q.c3)}

/-- The cut indicator `1_S` is **constant along the four edges** of the
square: no edge of `q` is a cut edge for `S`.  This is the negation of
"`q` is a conflict square" (`step4.tex:693`, clause (Q.1)). -/
def CutConstant (S : Finset (LinearExt α)) (q : BKSquare α) : Prop :=
  (q.c0 ∈ S ↔ q.c1 ∈ S) ∧ (q.c0 ∈ S ↔ q.c2 ∈ S) ∧
    (q.c1 ∈ S ↔ q.c3 ∈ S) ∧ (q.c2 ∈ S ↔ q.c3 ∈ S)

/-- A **conflict `2×2` square** for the cut `S` (`step4.tex:687`): a
genuine commuting BK square (`BKCommSquare`) on which the cut indicator
`1_S` is non-constant. -/
structure IsConflictSquare (S : Finset (LinearExt α)) (q : BKSquare α) :
    Prop where
  /-- The four corners form a genuine commuting `2×2` BK square. -/
  square : BKCommSquare q.c0 q.c1 q.c2 q.c3
  /-- The cut indicator is non-constant on the square. -/
  nonconstant : ¬ CutConstant S q

/-- **`lem:22` grounded (`step4.tex:687`).**  A conflict `2×2` square
has a cut edge: at least one of its four BK edges crosses the cut `S`.

This is the BK-graph form of `lem_22_contrapositive`
(`OneThird.Step4.RectangleModel`): the four edges connect the four
corners, so if no edge crossed the cut the indicator would be constant
on the whole square. -/
theorem lem22_bk {S : Finset (LinearExt α)} {q : BKSquare α}
    (h : IsConflictSquare S q) :
    (squareEdges q ∩ bkBoundary S).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply h.nonconstant
  -- An edge of `q` that is BK-adjacent but does not cross the cut
  -- forces its endpoints to agree on membership in `S`.
  have key : ∀ L L', BKAdj L L' → s(L, L') ∈ squareEdges q →
      (L ∈ S ↔ L' ∈ S) := by
    intro L L' hadj hmem
    by_contra hne
    have hcross : s(L, L') ∈ squareEdges q ∩ bkBoundary S := by
      rw [Finset.mem_inter]
      refine ⟨hmem, ?_⟩
      rw [mem_bkBoundary]
      exact ⟨hadj, by tauto⟩
    rw [hempty] at hcross
    simp at hcross
  refine ⟨key q.c0 q.c1 h.square.bkAdj01 ?_,
          key q.c0 q.c2 h.square.bkAdj02 ?_,
          key q.c1 q.c3 h.square.bkAdj13 ?_,
          key q.c2 q.c3 h.square.bkAdj23 ?_⟩
  all_goals (unfold squareEdges; simp)

/-! ## §3 — The BK-edge witness family in the incoherent locus

`step4.tex:1167` defines, for an ordered rich pair `(α,β)`,
`E_{α,β} := ⊔_B {cut edges of conflict 2×2 squares in R_B}` where `B`
ranges over the blocks of `Ω°_{α,β}`.  S4-A constructs the
**incoherent-locus** version: the union runs over the conflict squares
lying in *incoherent* blocks (`step4.tex:1142`).

The construction takes an indexed family of conflict squares
(`squares : Finset ι`, `crn : ι → BKSquare α`) together with a flag
`inIncoherent : ι → Prop` selecting the squares in incoherent blocks. -/

/-- The **cut edges of a single square**: the BK edges of `q` that
cross the cut `S`. -/
noncomputable def cutEdgesOfSquare (S : Finset (LinearExt α))
    (q : BKSquare α) : Finset (Sym2 (LinearExt α)) :=
  squareEdges q ∩ bkBoundary S

theorem cutEdgesOfSquare_subset_bkBoundary (S : Finset (LinearExt α))
    (q : BKSquare α) : cutEdgesOfSquare S q ⊆ bkBoundary S :=
  Finset.inter_subset_right

/-- **The BK-edge witness family `E_{α,β}` in the incoherent locus**
(`step4.tex:1167`).  Given an indexed family of conflict squares
`crn : ι → BKSquare α` over `squares : Finset ι`, with `inIncoherent`
selecting the squares whose block is incoherent, the witness family is
the union of the cut edges of the incoherent-block squares. -/
noncomputable def witnessFamily {ι : Type*} (S : Finset (LinearExt α))
    (squares : Finset ι) (crn : ι → BKSquare α)
    (inIncoherent : ι → Prop) [DecidablePred inIncoherent] :
    Finset (Sym2 (LinearExt α)) :=
  (squares.filter inIncoherent).biUnion (fun i => cutEdgesOfSquare S (crn i))

theorem mem_witnessFamily {ι : Type*} {S : Finset (LinearExt α)}
    {squares : Finset ι} {crn : ι → BKSquare α}
    {inIncoherent : ι → Prop} [DecidablePred inIncoherent]
    {e : Sym2 (LinearExt α)} :
    e ∈ witnessFamily S squares crn inIncoherent ↔
      ∃ i, i ∈ squares ∧ inIncoherent i ∧ e ∈ cutEdgesOfSquare S (crn i) := by
  unfold witnessFamily
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.1, hi.2, he⟩
  · rintro ⟨i, hi, hinc, he⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hinc⟩, he⟩

/-- **Every witness edge is a genuine BK cut edge** (`step4.tex:1172`).
`E_{α,β} ⊆ ∂_BK S`: this is the structural fact the Step 6
double-counting (`cor:step6-input`, via `lem:G6`) consumes — the
witness family lives inside the BK boundary, so its cardinality lower-
bounds `|∂_BK S|`. -/
theorem witnessFamily_subset_bkBoundary {ι : Type*}
    (S : Finset (LinearExt α)) (squares : Finset ι) (crn : ι → BKSquare α)
    (inIncoherent : ι → Prop) [DecidablePred inIncoherent] :
    witnessFamily S squares crn inIncoherent ⊆ bkBoundary S := by
  unfold witnessFamily
  refine Finset.biUnion_subset.mpr ?_
  intro i _
  exact cutEdgesOfSquare_subset_bkBoundary S (crn i)

/-- Every witness edge is, concretely, a BK edge `s(L, L')` of the
Bubley–Karzanov graph — so it has a well-defined *swap pair* via
`BKAdj.swapPair`.  This is `step4.tex:1188` Step 1 of `lem:G6`
("one interface is pinned") at the grounded level: the abstract
`swapPair` hypothesis of `OneThird.Step4.Step4Theorem.lem_G6` is, on
the ground set, the genuine BK-move swap pair. -/
theorem witnessEdge_bkAdj {ι : Type*} {S : Finset (LinearExt α)}
    {squares : Finset ι} {crn : ι → BKSquare α} {inIncoherent : ι → Prop}
    [DecidablePred inIncoherent] {e : Sym2 (LinearExt α)}
    (he : e ∈ witnessFamily S squares crn inIncoherent) :
    ∃ L L', e = s(L, L') ∧ BKAdj L L' :=
  bkAdj_of_mem_bkBoundary
    (witnessFamily_subset_bkBoundary S squares crn inIncoherent he)

/-- The witness family is **non-empty** whenever the family contains a
conflict square in an incoherent block: by `lem22_bk` that square
contributes a cut edge.  This is what makes the construction
non-vacuous — the witness family genuinely captures incoherent overlap
mass. -/
theorem witnessFamily_nonempty_of_conflict {ι : Type*}
    {S : Finset (LinearExt α)} {squares : Finset ι} {crn : ι → BKSquare α}
    {inIncoherent : ι → Prop} [DecidablePred inIncoherent] {i : ι}
    (hi : i ∈ squares) (hinc : inIncoherent i)
    (hconf : IsConflictSquare S (crn i)) :
    (witnessFamily S squares crn inIncoherent).Nonempty := by
  obtain ⟨e, he⟩ := lem22_bk hconf
  refine ⟨e, ?_⟩
  rw [mem_witnessFamily]
  exact ⟨i, hi, hinc, he⟩

/-! ## §4 — The incoherent locus, grounded on Step 3 `def:coherent`

`step4.tex:1142`: a block `B` is *incoherent* if the two induced local
signs `η_{x,y}, η_{u,v}` disagree on a `≥ ½`-fraction of `B`-mass.
Grounded on the Step 3 `def:eta` `etaOnState` and the `disagreeSet`
correlation bookkeeping. -/

/-- **Incoherent block** (`step4.tex:1142`).  A block `B` (a finset of
overlap states) is incoherent for the interfaces with local signs
`σxy, σuv` and common axes `axy, buv` when the Step 3 `def:eta` signs
`η_{x,y}, η_{u,v}` disagree on at least half of `B`. -/
def BlockIncoherent (B : Finset (LinearExt α)) (σxy σuv : Step3.Sign)
    (axy buv : LinearExt α → ℤ × ℤ) : Prop :=
  B.card ≤ 2 * (Step3.disagreeSet B
    (Step3.etaOnState σxy axy) (Step3.etaOnState σuv buv)).card

/-- The incoherent-block predicate is **implied by the Step 3
`IncoherentPair` dichotomy** once the incoherence fraction clears the
`½` threshold (`d ≤ 2·cinc`).  This is the bridge from `def:coherent`
(`step3.tex`) to the `step4.tex:1142` per-block Markov split: a pair
that is `IncoherentPair` at fraction `cinc/d ≥ ½` makes every block
that realises that fraction an incoherent block. -/
theorem blockIncoherent_of_incoherentPair
    (B : Finset (LinearExt α)) (σxy σuv : Step3.Sign)
    (axy buv : LinearExt α → ℤ × ℤ) (cinc d : ℕ)
    (hcinc : 0 < cinc) (hhalf : d ≤ 2 * cinc)
    (h : Step3.IncoherentPair B σxy σuv axy buv cinc d) :
    BlockIncoherent B σxy σuv axy buv := by
  unfold Step3.IncoherentPair Step3.Incoherent at h
  unfold BlockIncoherent
  -- `h : d * |disagree| ≥ cinc * |B|`; `hhalf : d ≤ 2·cinc`.
  set D := (Step3.disagreeSet B (Step3.etaOnState σxy axy)
    (Step3.etaOnState σuv buv)).card with hD
  -- `cinc * |B| ≤ d * D ≤ 2·cinc · D`, cancel `cinc`.
  have h1 : cinc * B.card ≤ d * D := h
  have h2 : d * D ≤ 2 * cinc * D := Nat.mul_le_mul hhalf (le_refl D)
  have h3 : cinc * B.card ≤ cinc * (2 * D) := by
    calc cinc * B.card ≤ d * D := h1
      _ ≤ 2 * cinc * D := h2
      _ = cinc * (2 * D) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hcinc

/-! ## §5 — The statement of `thm:step4`, grounded

`step4.tex:93` (`thm:step4`): `|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|`.  In
cleared-denominator integer form (matching the abstract
`OneThird.Step4.Step4Theorem.thm_step4`, the factor `2` absorbing the
Markov loss on incoherent-block mass, `step4.tex:1156`):

`c·δ·|Ω°| ≤ 2·|∂_BK S| + 2·C·ε·|Ω°|`. -/

/-- **`thm:step4` conclusion (`step4.tex:93`), grounded.**  The
cleared-denominator two-interface incompatibility inequality: the BK
boundary of the cut is at least proportional to the incoherent overlap
mass `δ·|Ω°|`, up to the Step-2 staircase noise `C·ε·|Ω°|`.

`δ` (`delta`) is the incoherence count of `def:coherence-cited`, `ε`
(`eps`) the Step-2 staircase error of `thm:step2-cited`, `|Ω°|`
(`omegaCard`) the commuting-overlap mass. -/
def Step4Conclusion (S : Finset (LinearExt α))
    (c cnst delta eps omegaCard : ℕ) : Prop :=
  c * delta * omegaCard ≤
    2 * (bkBoundary S).card + 2 * cnst * eps * omegaCard

/-- **`thm:step4` (`step4.tex:93`), grounded — the witness→boundary
reduction.**  Given any finset `W` of BK edges contained in the BK
boundary (`hW`, discharged for the constructed `witnessFamily` by
`witnessFamily_subset_bkBoundary`), a lower bound `c·δ·|Ω°| ≤ 2|W| +
2Cε|Ω°|` on the witness count lifts to the `thm:step4` inequality on
`|∂_BK S|`.

This is the **S4-A half** of `thm:step4`: it reduces the theorem to the
per-block incompatibility lower bound on `|W| = |E_{α,β}|`, which is
the S4-B (`lem:rect-stable-area`) + S4-C (`prop:G5` global counting)
deliverable.  The proof is genuinely load-bearing: it uses
`W ⊆ ∂_BK S ⇒ |W| ≤ |∂_BK S|`. -/
theorem thm_step4_grounded (S : Finset (LinearExt α))
    (W : Finset (Sym2 (LinearExt α))) (hW : W ⊆ bkBoundary S)
    (c cnst delta eps omegaCard : ℕ)
    (hWitLB : c * delta * omegaCard ≤
      2 * W.card + 2 * cnst * eps * omegaCard) :
    Step4Conclusion S c cnst delta eps omegaCard := by
  unfold Step4Conclusion
  have hcard : W.card ≤ (bkBoundary S).card := Finset.card_le_card hW
  omega

/-- **`thm:step4` (`step4.tex:93`), grounded — assembled from the
constructed witness family.**  Specialises `thm_step4_grounded` to
`W := witnessFamily …`, the actual `E_{α,β}` of `step4.tex:1167`: a
per-block incompatibility lower bound on `|E_{α,β}|` discharges
`thm:step4`. -/
theorem thm_step4_grounded_witness {ι : Type*} (S : Finset (LinearExt α))
    (squares : Finset ι) (crn : ι → BKSquare α) (inIncoherent : ι → Prop)
    [DecidablePred inIncoherent]
    (c cnst delta eps omegaCard : ℕ)
    (hWitLB : c * delta * omegaCard ≤
      2 * (witnessFamily S squares crn inIncoherent).card +
        2 * cnst * eps * omegaCard) :
    Step4Conclusion S c cnst delta eps omegaCard :=
  thm_step4_grounded S (witnessFamily S squares crn inIncoherent)
    (witnessFamily_subset_bkBoundary S squares crn inIncoherent)
    c cnst delta eps omegaCard hWitLB

/-! ## §6 — Non-vacuity at the concrete width-3 non-chain poset

Per the S4-A acceptance bar, the port instantiates non-vacuously at a
genuine width-3 non-chain `α` — the grid poset `Fin 3 × Fin 3` of
`Step1/Overlap.lean` — with no `Subsingleton`-on-empty baseline.

A genuine `2×2` BK conflict square needs two BK moves at disjoint
positions, hence a poset with at least four elements supporting two
disjoint incomparable pairs; `Fin 3 × Fin 3` does (its anti-diagonal
linear extension `gridLinExt` carries BK moves at the disjoint
positions `1` and `3`), so the witness construction fires here on a
*genuine* conflict square — not a degenerate one. -/

/-- The conflict square on the grid poset: the commuting `2×2` BK
square spanned by the BK moves at the disjoint positions `1`, `3` of
the anti-diagonal extension `gridLinExt`. -/
def gridSquare : BKSquare (Fin 3 × Fin 3) where
  c0 := gridLinExt
  c1 := gridLinExt.swapAdj 1 (by decide) ⟨by decide, by decide⟩
  c2 := gridLinExt.swapAdj 3 (by decide) ⟨by decide, by decide⟩
  c3 := (gridLinExt.swapAdj 1 (by decide) ⟨by decide, by decide⟩).swapAdj 3
          (by decide) ⟨by decide, by decide⟩

/-- `gridSquare` is a genuine commuting `2×2` BK square: the two BK
moves at positions `1` and `3` of `gridLinExt` have disjoint support
(`cor:overlap` (a), `bkCommSquare_of_disjoint`). -/
theorem gridSquare_isCommSquare :
    BKCommSquare gridSquare.c0 gridSquare.c1 gridSquare.c2 gridSquare.c3 :=
  bkCommSquare_of_disjoint gridLinExt (k := 1) (m := 3)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide)

/-- **The S4-A non-vacuity acceptance witness.**

At the genuine width-3 non-chain grid poset `Fin 3 × Fin 3`:

* **(poset)** `Fin 3 × Fin 3` has width exactly `3` and is not a
  chain — no `Subsingleton`-on-empty baseline;
* **(conflict square)** with the singleton cut `S := {gridLinExt}`,
  `gridSquare` is a *genuine* conflict square: a real commuting `2×2`
  BK square whose four corners are split by the cut;
* **(witness family)** the constructed `witnessFamily` over the
  one-square incoherent family is non-empty — `lem22_bk` extracts a
  genuine BK cut edge, so the construction is non-vacuous;
* **(`thm:step4`)** `thm_step4_grounded_witness` fires with strictly
  positive `δ = 1`, `|Ω°| = 1`, delivering the `thm:step4` inequality;
* **(incoherent locus)** `BlockIncoherent` holds non-vacuously on a
  genuine two-element block where the Step 3 `def:eta` signs disagree. -/
theorem witnessGrounded_nonvacuous :
    -- (poset) genuine width-3 non-chain
    HasWidth (Fin 3 × Fin 3) 3 ∧
    ¬ IsChainPoset (Fin 3 × Fin 3) ∧
    -- (conflict square) a genuine conflict square for S = {gridLinExt}
    IsConflictSquare ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      gridSquare ∧
    -- (witness family) the constructed witness family is non-empty
    (witnessFamily ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      ({()} : Finset Unit) (fun _ => gridSquare) (fun _ => True)).Nonempty ∧
    -- (thm:step4) the grounded statement fires with positive δ, |Ω°|
    Step4Conclusion ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      1 0 1 0 1 ∧
    -- (incoherent locus) BlockIncoherent fires on a genuine 2-element block
    BlockIncoherent
      ({gridLinExt, gridSquare.c1} : Finset (LinearExt (Fin 3 × Fin 3)))
      true true (fun _ => (1, 0)) (fun _ => (-1, 0)) := by
  -- The cut and the conflict square.
  set S : Finset (LinearExt (Fin 3 × Fin 3)) := {gridLinExt} with hS
  have hsq := gridSquare_isCommSquare
  -- `gridSquare.c0 = gridLinExt ∈ S`.
  have hc0S : gridSquare.c0 ∈ S := by
    rw [hS]; exact Finset.mem_singleton_self _
  -- `gridSquare.c1 ∉ S`: BK-adjacency gives `c1 ≠ c0 = gridLinExt`.
  have hc1ne : gridSquare.c1 ≠ gridLinExt := (BKAdj.ne hsq.bkAdj01).symm
  have hc1S : gridSquare.c1 ∉ S := by
    rw [hS, Finset.mem_singleton]; exact hc1ne
  -- The conflict square: the cut splits corner `c0` from corner `c1`.
  have hconf : IsConflictSquare S gridSquare := by
    refine ⟨hsq, ?_⟩
    intro hconst
    exact hc1S (hconst.1.mp hc0S)
  refine ⟨?_, ?_, hconf, ?_, ?_, ?_⟩
  · -- width exactly 3: anti-diagonal `{(0,2),(1,1),(2,0)}` is a 3-antichain
    refine ⟨grid_hasWidthAtMost_three, {(0, 2), (1, 1), (2, 0)}, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | (intro hle; exact absurd hle (by decide))
    · decide
  · exact grid_not_chain
  · -- the witness family is non-empty
    exact witnessFamily_nonempty_of_conflict (S := S) (squares := {()})
      (crn := fun _ => gridSquare) (inIncoherent := fun _ => True) (i := ())
      (Finset.mem_singleton_self ()) trivial hconf
  · -- thm:step4 fires: δ = 1, |Ω°| = 1 are positive
    refine thm_step4_grounded_witness S ({()} : Finset Unit)
      (fun _ => gridSquare) (fun _ => True) 1 0 1 0 1 ?_
    obtain ⟨e, he⟩ := witnessFamily_nonempty_of_conflict (S := S)
      (squares := {()}) (crn := fun _ => gridSquare)
      (inIncoherent := fun _ => True) (i := ())
      (Finset.mem_singleton_self ()) trivial hconf
    have hpos : 0 < (witnessFamily S ({()} : Finset Unit)
        (fun _ => gridSquare) (fun _ => True)).card :=
      Finset.card_pos.mpr ⟨e, he⟩
    omega
  · -- BlockIncoherent on the genuine 2-element block {c0, c1}
    unfold BlockIncoherent
    set B : Finset (LinearExt (Fin 3 × Fin 3)) := {gridLinExt, gridSquare.c1}
      with hB
    -- the Step 3 `def:eta` signs disagree on every state of `B`
    have hdis : Step3.disagreeSet B
        (Step3.etaOnState true (fun _ => ((1 : ℤ), (0 : ℤ))))
        (Step3.etaOnState true (fun _ => ((-1 : ℤ), (0 : ℤ)))) = B := by
      unfold Step3.disagreeSet
      apply Finset.filter_true_of_mem
      intro L _
      simp [Step3.etaOnState, Step3.etaOfDir_e1, Step3.etaOfDir_neg_e1]
    rw [hdis]
    omega

end Step4
end OneThird

