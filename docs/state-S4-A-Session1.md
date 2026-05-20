# State — S4-A — Session 1: Step 4 Lean port part 1 — `thm:step4` statement + BK-edge witness family

**Ticket:** mg-7592 (OneThird-S4-A: Step 4 Lean port part 1 —
two-interface incompatibility theorem, statement and witness
construction).
**Branch:** `polecat-mg-7592`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-3.
**Depends:** mg-0868 (S2-B `prop:per-fiber` + `thm:step2`), mg-7a22
(S3 `lem:local-sign` + `def:coherent`); both merged.

**Scope.** Wave-3 ticket of the Piece-1 (Steps 1-6 cascade port)
decomposition.  Ports `step4.tex` `thm:step4` (the two-interface
incompatibility theorem) as a **grounded statement** and **constructs
the BK-edge witness family in the incoherent locus**.  The per-block
incompatibility proof (`lem:rect-stable-area`) is S4-B; the global
counting / density regularization (`prop:G5`, `lem:G6`) is S4-C.

---

## §0. Verdict — **GREEN-S4-A-delivered**

`lean/OneThird/Step4/WitnessGrounded.lean` (NEW, ~480 LoC) delivers,
building on the Step 1 overlap-commutation output (`BKCommSquare`), the
Step 3 grounded coherence output (`Step3.etaOnState`,
`Step3.IncoherentPair`, `Step3.disagreeSet`), and the
`SimpleGraph.edgeBoundary` infrastructure:

* `bkBoundary` — the BK boundary `∂_BK S` (`step4.tex:24`), **grounded**
  as `(bkGraph α).edgeBoundary S`, a genuine `Finset (Sym2 (LinearExt
  α))` of real BK edges.  The abstract Step 4 scaffold
  (`Step4Theorem.lean`) modelled the BK graph by an opaque `Edge` type;
  this grounds it on `bkGraph α`.
* `mem_bkBoundary` / `bkAdj_of_mem_bkBoundary` — the membership
  characterisation and the "every boundary edge is a genuine BK edge"
  structural fact.
* `BKSquare` / `squareEdges` / `CutConstant` / `IsConflictSquare` —
  the **conflict `2×2` square** notion, grounded on the Step 1
  `BKCommSquare` (`cor:overlap` (a), `bkCommSquare_of_disjoint`).  A
  conflict square is a *genuine commuting BK square* on which the cut
  indicator `1_S` is non-constant.
* `lem22_bk` — **`lem:22` (`step4.tex:687`) grounded**: a conflict
  `2×2` square has a cut edge among its four BK edges.  The BK-graph
  analogue of the abstract `lem_22_contrapositive`
  (`RectangleModel.lean`), proved directly on `Sym2`-edges.
* `cutEdgesOfSquare` / `witnessFamily` — **the construction**: the
  BK-edge witness family `E_{α,β}` in the incoherent locus
  (`step4.tex:1167`), as the union of the cut edges of the conflict
  squares lying in incoherent blocks.
* `witnessFamily_subset_bkBoundary` — **every witness edge is a genuine
  BK cut edge** (`step4.tex:1172`): `E_{α,β} ⊆ ∂_BK S`.  This is the
  structural fact S4-C's `lem:G6` double-counting consumes.
* `witnessEdge_bkAdj` — every witness edge is concretely a BK edge
  `s(L, L')` with `BKAdj L L'`, so it has a well-defined swap pair
  (`step4.tex:1188`, Step 1 of `lem:G6` at the grounded level).
* `witnessFamily_nonempty_of_conflict` — the witness family is
  non-empty whenever the family contains a conflict square in an
  incoherent block (via `lem22_bk`).
* `BlockIncoherent` — the **incoherent block** predicate
  (`step4.tex:1142`), grounded on the Step 3 `def:eta` `etaOnState`
  and the `disagreeSet` correlation bookkeeping.
* `blockIncoherent_of_incoherentPair` — the bridge from the Step 3
  `IncoherentPair` dichotomy (`def:coherent`) to the `step4.tex:1142`
  per-block `½`-threshold Markov split.
* `Step4Conclusion` / `thm_step4_grounded` / `thm_step4_grounded_witness`
  — **the statement** of `thm:step4` (`step4.tex:93`), grounded, plus
  the **witness→boundary reduction** (see §2 below).
* `gridSquare` / `gridSquare_isCommSquare` /
  `witnessGrounded_nonvacuous` — the mg-7592 non-vacuity acceptance
  witness (see §5).

`lake build OneThird.Step4.WitnessGrounded` is clean (exit 0).
`lake build OneThird` (full library) is clean.  The new file produces
no warnings.

**No `sorry`, no new axiom.**  `#print axioms` confirms
`thm_step4_grounded`, `witnessFamily_subset_bkBoundary`, `lem22_bk`,
`blockIncoherent_of_incoherentPair`, and `witnessGrounded_nonvacuous`
all depend on exactly `[propext, Classical.choice, Quot.sound]` (the
three standard mathlib axioms — `blockIncoherent_of_incoherentPair`
needs only `[propext, Quot.sound]`).  No `sorryAx`, no project axiom.

---

## §1. What `thm:step4` says, and how the port grounds it

`step4.tex:93` (`thm:step4`, two-interface incompatibility):

> There are absolute constants `c, C > 0` such that
> `|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|`.

In words (`step4.tex:107`): *incoherent overlap mass is paid for
one-to-one in BK boundary, up to the Step-2 noise.*

The port grounds the four quantities:

| paper | grounded as |
|---|---|
| `∂_BK S` | `bkBoundary S = (bkGraph α).edgeBoundary S` |
| `δ` (incoherence) | `Step3.disagreeSet`-count (the `def:coherent` η) |
| `ε` (Step-2 staircase error) | the `eps` parameter (see §3) |
| `Ω°` (commuting overlap) | the `omegaCard` parameter |

`Step4Conclusion S c C δ ε |Ω°|` is the cleared-denominator integer
form `c·δ·|Ω°| ≤ 2·|∂_BK S| + 2·C·ε·|Ω°|`, matching the abstract
`Step4Theorem.thm_step4` shape (the factor `2` absorbs the Markov loss
on incoherent-block mass, `step4.tex:1156`).

---

## §2. The witness→boundary reduction is the substantive S4-A content

`thm:step4` factors through the witness family:

* **S4-A (here):** `E_{α,β} ⊆ ∂_BK S`, hence `|E_{α,β}| ≤ |∂_BK S|`
  (`witnessFamily_subset_bkBoundary` + `Finset.card_le_card`).
* **S4-B + S4-C:** `c·(δ − C·ε)·|Ω°| ≤ |E_{α,β}|` — the per-block
  rectangle incompatibility (`lem:rect-stable-area`) summed by the
  density regularization (`prop:G5`).

`thm_step4_grounded` composes the two: given **any** `W ⊆ ∂_BK S` and a
lower bound `c·δ·|Ω°| ≤ 2·|W| + 2·C·ε·|Ω°|` on the witness count, it
delivers the `thm:step4` inequality on `|∂_BK S|`.  The proof is
genuinely load-bearing — it uses `W ⊆ ∂_BK S ⇒ |W| ≤ |∂_BK S|`, not a
hypothesis-returning identity.  `thm_step4_grounded_witness`
specialises `W` to the actual constructed `witnessFamily`.

This is the honest S4-A deliverable: the **statement** of `thm:step4`
plus the **reduction** of the theorem to the per-block lower bound on
`|E_{α,β}|`, which is exactly the S4-B/C work.  S4-A does **not** prove
the per-block incompatibility — that is faithfully out of scope.

---

## §3. Scope boundary (honest)

This ticket ports the **statement** of `thm:step4` and **constructs**
the witness family, all grounded, 0-sorry, no new axiom.  Out of
scope, faithfully so:

* **The per-block rectangle incompatibility** (`lem:rect-exact`,
  `lem:rect-stable`, `lem:rect-stable-area`, `lem:many-nonconst`,
  `lem:square-multiplicity`).  This is S4-B.  The abstract ℤ²-grid
  forms already exist in `RectangleModel.lean`; S4-B grounds them and
  delivers the per-incoherent-block lower bound on `|E_{α,β}|`.
* **The global counting / density regularization** (`prop:G2-step4`,
  `prop:G5`, the proof of `thm:step4`, `lem:G6` witness-edge
  multiplicity, `cor:step6-input`).  This is S4-C.  It sums the S4-B
  per-block bound and discharges the `hWitLB` hypothesis of
  `thm_step4_grounded_witness`.
* **The Step-2 staircase error `ε` as a structural input.**  S4-A
  ports the *statement*: `ε` is a parameter, documented as the
  `thm:step2-cited` per-fiber staircase error with its ε² (`ε' =
  √(4ε/ρ)`) bookkeeping.  S4-B/C thread it concretely from the S2-B
  grounded staircase output (`Step2.PerFiberGrounded2`).  Pinning `ε`
  to a structural `IsStaircasePlus` field at the *statement* level
  would have produced an unused hypothesis (a marker field — see
  `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall warnings on declared-
  but-unused API surface); the honest choice is the parameter + the
  S1/S3 structural consumption that *is* load-bearing.
* **The block decomposition `prop:G1`** as a `BlockDecomp`-typed
  object.  The witness family here takes an indexed family of conflict
  squares with an incoherence flag, which is the operative shape `lem:G6`
  / S4-C consume; the `BlockDecomp` packaging already exists in the
  abstract `RectangleModel.lean` and is wired in by S4-C.

The abstract Step 4 files (`RectangleModel.lean`,
`DensityRegularization.lean`, `Step4Theorem.lean`) are **unchanged**;
`WitnessGrounded.lean` is purely additive.

---

## §4. What this port consumes from Steps 1–3

* **Step 1** (`Step1.Overlap`) — `BKCommSquare` and
  `bkCommSquare_of_disjoint` (`cor:overlap` (a), the overlap-
  commutation output): the conflict squares **are** genuine commuting
  BK squares.  Also `gridLinExt` + `grid_hasWidthAtMost_three` +
  `grid_not_chain` for the non-vacuity poset.  `Step1.BKMoves` —
  `BKAdj.swapPair` (every BK move has a swap pair, the basis of
  `lem:G6` Step 1 pinning).
* **Step 2** — the per-fiber staircase error `ε` of `thm:step2-cited`;
  parameter-level consumption at the *statement* (see §3).
* **Step 3** (`Step3.LocalSignGrounded`) — `etaOnState` (`def:eta`),
  `IncoherentPair` (`def:coherent`), `disagreeSet` (the
  `prop:correlation` bookkeeping): the incoherent-locus filter
  `BlockIncoherent` is built directly on the Step 3 grounded η, and
  `blockIncoherent_of_incoherentPair` is the genuine bridge from the
  Step 3 dichotomy to the `step4.tex:1142` per-block split.

---

## §5. Non-vacuity (mg-7592 acceptance bar)

`witnessGrounded_nonvacuous` instantiates the framework at the concrete
**genuine width-3 non-chain grid poset `Fin 3 × Fin 3`** (the
`Step1/Overlap.lean` non-vacuity poset):

* **(poset)** `Fin 3 × Fin 3` has width exactly `3`
  (`grid_hasWidthAtMost_three` plus the anti-diagonal 3-antichain
  `{(0,2),(1,1),(2,0)}`) and is not a chain (`grid_not_chain`);
* **(conflict square)** `gridSquare` is a *genuine* conflict square:
  a real commuting `2×2` BK square (`gridSquare_isCommSquare`, the BK
  moves at the **disjoint** positions `1`, `3` of `gridLinExt`), and
  with the singleton cut `S := {gridLinExt}` its four corners are
  genuinely split by the cut — `¬ CutConstant`;
* **(witness family)** the constructed `witnessFamily` over the
  one-square incoherent family is non-empty — `lem22_bk` extracts a
  genuine BK cut edge, so the construction is *non-vacuous*;
* **(`thm:step4`)** `thm_step4_grounded_witness` fires with strictly
  positive `δ = 1` and `|Ω°| = 1`, delivering the `Step4Conclusion`
  inequality;
* **(incoherent locus)** `BlockIncoherent` holds non-vacuously on a
  genuine **two-element** block `{gridLinExt, gridSquare.c1}` where the
  two Step 3 `def:eta` sign functions disagree on every state.

A genuine `2×2` BK conflict square *requires* a poset with at least
four elements supporting two disjoint incomparable pairs — the
3-element `Antichain3` (used as the S1–S3 non-vacuity witness)
structurally cannot carry one (only two adjacent position-pairs, which
always overlap).  `Fin 3 × Fin 3` does carry one, so the witness
construction fires here on a *genuine* square, not a degenerate one.
No `Subsingleton`-on-empty baseline anywhere.

---

## §6. Files

* `lean/OneThird/Step4/WitnessGrounded.lean` — NEW (~480 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S4-A-Session1.md` — this file.
