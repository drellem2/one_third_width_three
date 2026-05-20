# OneThird-S1-C — Step 1 Lean port part 3: overlap and triple-overlap corollaries

**Work item:** mg-bcf2 (FULL REFACTOR Phase 2, Wave-1; Piece-1 / Steps 1-6
cascade port). **Depends on:** mg-faf8 (corrected MA-Sig signature
contract). **Sibling wave-1 tickets:** mg-30e3 (S1-A coords + raw
fibers), mg-2e24 (S1-B BK-move classification + bad-set bounds),
mg-794c (S1-D assembly). **Status:** GREEN — commuting-square and
commuting-cube verifications landed, non-vacuous.

---

## §1. Scope delivered

Per scoping-doc §2.1 (S1 deliverables), the S1-C slice is
`cor:overlap` (2×2 commuting squares) and `cor:triple-overlap`
(Z³ commuting cube) of `step1.tex`. This session delivers the
**combinatorial core** of both corollaries: the verification that BK
moves with disjoint support commute, generating an embedded `2×2` BK
square (resp. `2×2×2` BK cube).

New file `lean/OneThird/Step1/Overlap.lean` (self-contained, depends
only on `OneThird/Mathlib/BKGraph.lean` + `OneThird/Poset.lean`):

* `swap_trans_swap_comm` — disjoint-support transpositions commute.
* `DisjointPos` — the disjoint-position-interval predicate, with the
  four `Fin`-distinctness projections and a `Decidable` instance.
* `swapAdj_toFun_symm_eq`, `swapAdj_incomp_of_disjoint` — a `swapAdj`
  fixes elements outside its position interval, so a BK move at a
  disjoint position stays enabled.
* `swapAdj_comm` — `swapAdj` at disjoint positions commutes.
* `BKCommSquare` (structure) + `bkCommSquare_of_disjoint` — **the
  `cor:overlap` part (a) verification**: two BK moves at disjoint
  positions span a commuting `2×2` BK square.
* `exists_swapAdj_of_bkAdj` — every `BKAdj` edge is a `swapAdj`.
* `swapAdj_congr`, `BKCommCube` (structure), `bkCommCube_of_disjoint`
  — **the `cor:triple-overlap` parts (b),(c) verification**: three BK
  moves at pairwise-disjoint positions span a commuting `2×2×2` BK
  cube (eight subset-vertices, six commuting faces).
* `gridLinExt`, `grid_hasWidthAtMost_three`, `grid_not_chain`,
  `bkCommCube_grid_example` — **the non-triviality witness** (see §3).

Modified `lean/OneThird/Step1/Corollaries.lean`: re-exports the two
verifications under the corollary names `cor_overlap_commuting_square`
and `cor_triple_overlap_commuting_cube`; module docstring updated
(commuting structure no longer "deferred"). The pre-existing
set-theoretic density scaffold (`bounded_interaction`,
`regularOverlap_density`, `regularTripleOverlap_density`) is retained
unchanged — it is faithful and remains the home of the bad-mass
bounds.

Modified `lean/OneThird.lean`: imports `OneThird.Step1.Overlap`.

---

## §2. The mathematical content (faithful to `step1.tex`)

The paper's `cor:overlap` (a) proof (`step1.tex:471-481`) and
`cor:triple-overlap` (b) proof (`step1.tex:602-631`) both reduce to
one sentence: *disjoint transpositions commute*. A unit `(x,y)`-move
swaps an interface element with an adjacent chain element; off the
interaction locus the moved elements of two (resp. three) interfaces
are all distinct, the transpositions have disjoint support, hence
commute, and the BK squares / cubes close.

`Overlap.lean` proves exactly this, on the abstract `bkGraph`:
disjoint *position intervals* `{k,k+1}`, `{m,m+1}` (4 distinct
points) ⇒ the two `Equiv.swap`s commute ⇒ the two `swapAdj` moves
commute ⇒ the `2×2` square (`bkCommSquare_of_disjoint`); three
pairwise-disjoint moves ⇒ the `2×2×2` cube (`bkCommCube_of_disjoint`),
assembled from the three faces through the base, the apex face, and
the twelfth edge obtained by commuting the moves.

The hypotheses are all load-bearing — there is no decorative routing.
`swapAdj` ignores its incomparability argument up to definitional
proof-irrelevance, which is what makes the eight cube vertices
identify cleanly across the six faces.

---

## §3. Non-triviality bar — discharged

The ticket's non-triviality bar requires a **non-vacuous
instantiation at a concrete width-3 non-chain α**, with no
Subsingleton-on-empty baseline.

`bkCommCube_grid_example` instantiates `bkCommCube_of_disjoint` on the
grid poset `Fin 3 × Fin 3`:

* `grid_hasWidthAtMost_three : HasWidthAtMost (Fin 3 × Fin 3) 3` — the
  grid is width-3 (an antichain meets each first-coordinate chain
  fibre at most once).
* `grid_not_chain : ¬ IsChainPoset (Fin 3 × Fin 3)` — `(0,1) ∥ (1,0)`.
* `gridLinExt` — the anti-diagonal linear extension; it carries three
  BK moves at the pairwise-disjoint positions `1`, `3`, `6`
  (anti-diagonal order is what gives three disjoint adjacent
  incomparable pairs; the lexicographic order would give only two).
* `bkCommCube_grid_example` — the commuting cube exists on this
  concrete poset.

So the verifications are genuine theorems with satisfiable
hypotheses, instantiated at a real width-3 non-chain poset — not a
vacuous routing.

No ill-posed target and no missing mathlib dependency surfaced;
nothing to block-and-report.

---

## §4. Interface for S1-D (assembly)

`Overlap.lean`'s commuting square/cube take a **disjoint-support
hypothesis** (`DisjointPos` on the move positions). They do *not*
take overlap-membership: commutation of disjoint moves is a universal
`bkGraph` fact, independent of the rich-pair / good-fiber structure.

The paper's corollaries state the squares/cubes on the *regular*
overlap `Ω°` / triple overlap `Ω°°°` (interaction-locus exclusion).
The bridge `regularOverlap`-membership ⇒ `DisjointPos` requires the
**BK-move classification** of `thm:interface` part (iii) — that a unit
grid move of an interface is the swap of an interface element with an
adjacent chain element, so off the interaction locus the moved
elements of the two/three interfaces sit at disjoint positions. That
classification is the **S1-B deliverable** (mg-2e24). S1-D (mg-794c)
should wire it: consume S1-B's classification to discharge
`DisjointPos` from `regularOverlap` / `regularTripleOverlap`
membership, then feed `cor_overlap_commuting_square` /
`cor_triple_overlap_commuting_cube`.

This decomposition keeps S1-C decoupled from the in-flight S1-A/S1-B
work: `Overlap.lean` depends only on already-landed
`BKGraph.lean` + `Poset.lean`, so it cannot be broken by sibling
tickets, and `Corollaries.lean`'s pre-existing API surface is
untouched apart from the two added re-export theorems.

---

## §5. Build status

`lake build OneThird` clean (warnings only — the repo-wide
`unusedDecidableInType` / `unusedSectionVars` linter notes shared by
the existing Step 1 files). No `sorry`, no new axiom.
