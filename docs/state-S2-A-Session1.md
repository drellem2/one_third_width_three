# State — S2-A — Session 1: Step 2 port part 1 — `lem:weak-grid` + initial per-fiber transport

**Ticket:** mg-0893 (OneThird-S2-A: Step 2 Lean port part 1 — weak-grid
isoperimetric stability lemma plus initial per-fiber transport).
**Branch:** `polecat-0893`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-2.
**Depends:** mg-794c (S1-D, `thm:interface` assembled), mg-28fe (F6a,
single-orientation weak-grid core), mg-6b23 (F6b, completed
`lem:weak-grid`); all merged.

**Scope.** Wave-2 ticket of the Piece-1 (Steps 1-6 cascade port)
decomposition.  Ports `step2.tex` Lemma `lem:weak-grid` as a Step 2
statement and the **initial per-fiber transport** — the grounding of
the planar weak grid stability lemma on the Step 1 interface's
good-fiber data, routing a global cut `S ⊆ LinearExt α` through the
`def:step1-data` clause (S1.4) BK-boundary ↔ grid-boundary identity so
that `weak_grid` applies fiber-by-fiber.

---

## §0. Verdict — **GREEN-S2-A-delivered**

`lean/OneThird/Step2/PerFiberGrounded.lean` (NEW, ~610 LoC) delivers:

* `weakGridRate` + `weakGridRate_nonneg` / `_mono` / `_le_of_le` —
  the explicit stability rate `δ(ε) = 4ε/c` and the `δ(ε) → 0`
  qualitative content of `lem:weak-grid`;
* `lem_weak_grid` — `step2.tex` Lemma `lem:weak-grid` as a Step 2
  statement, with the named rate (re-exposes the F6a/F6b planar
  deliverable `OneThird.Step2.WeakGrid.weak_grid`);
* `fiberGrid` / `fiberCut` — the per-fiber grid domain `D_{x,y}` and
  transported cut `A_{x,y}`, grounded on a Step 1 good fiber;
* `fiberGrid_isOrdConvex`, `fiberGrid_box`, `fiberCut_subset`,
  `fiberGrid_card` — the planar shape facts `weak_grid` consumes,
  transported from the Step 1 `IsGoodFiber` clauses;
* `fiberBKBdy` + `fiberBKBdy_card_eq_gridBdy_card` — the
  `def:step1-data` clause (S1.4) transport: the per-fiber BK-boundary
  of a cut is in cardinality-bijection with the grid boundary of its
  coordinate image;
* `per_fiber_staircase_of_gridBdy` / `per_fiber_weak_grid` — the
  initial per-fiber transport: a good fiber with a small per-fiber
  BK-boundary admits a staircase approximation with error
  `≤ δ(ε)·|D_{x,y}|`;
* `per_fiber_grounded_nonvacuous` — the mg-0893 acceptance witness.

`lake build OneThird.Step2.PerFiberGrounded` is clean (exit 0,
`✔ [1057/1057] Built OneThird.Step2.PerFiberGrounded`).  `lake build
OneThird` (full library) is clean.  The only warnings on the new file
are `linter.unusedSectionVars` / `linter.unusedDecidableInType`
notices — the same class flagged as pre-existing-and-tolerated in the
S1-A…S1-D ports (a few lemma *types* do not mention every section
typeclass).  No `linter.style.show` or other new warning class.

**No `sorry`, no new axiom.**  `#print axioms` confirms
`lem_weak_grid`, `per_fiber_weak_grid`,
`fiberBKBdy_card_eq_gridBdy_card` and `per_fiber_grounded_nonvacuous`
all depend on exactly `[propext, Classical.choice, Quot.sound]` — the
three standard mathlib axioms, no `sorryAx`, no project axiom.

**Non-triviality bar met — no Subsingleton-on-empty baseline.**
`per_fiber_grounded_nonvacuous` instantiates the port at the concrete
3-element antichain `Antichain3` (`Fin 3`, discrete order):

* `HasWidth Antichain3 3` and `¬ IsChainPoset Antichain3` — width
  **exactly 3**, genuinely non-chain;
* `commonNbhdLength a0 a1 = 1` — the rich pair `(a0, a1)` has a
  genuinely positive common-neighbour-chain length `t = 1`, so the
  coordinate codomain is the honest `{0,1}²` grid;
* `lem_weak_grid` **fires on a genuine multi-cell grid**: the `2 × 2`
  block `grid2x2` with the corner cut `A = {(0,0)}` (grid boundary
  exactly `2`) admits a staircase approximation — the planar weak grid
  lemma is exercised on a four-cell domain with a non-empty boundary,
  not on an empty or one-point degenerate region;
* `per_fiber_weak_grid` **fires at a concrete good fiber on
  `Antichain3`**: a non-empty fiber on the genuine 6-element
  `LinearExt Antichain3`, with `IsGoodFiber a0 a1` and the grid
  domain `fiberGrid a0 a1` non-empty, the transport delivers a
  per-fiber staircase approximation.

**No new vacuity-discovery surfaced.**  The F6a/F6b planar deliverable
and the Step 1 `IsGoodFiber` interface compose cleanly into the
per-fiber transport; no fresh paper-side rigour gap arose.  The (S1.4)
BK-boundary ↔ grid-boundary identity ports verbatim — `step2.tex`
`prop:per-fiber` proof of part (ii) is exactly this identity followed
by `lem:weak-grid`.

---

## §1. What landed

New file `lean/OneThird/Step2/PerFiberGrounded.lean`, registered in
`lean/OneThird.lean` (import added after `OneThird.Step2.Conclusion`).

### §1.1. `lem:weak-grid` as a Step 2 statement (§1 of the file)

* `weakGridRate c ε := 4 * ε / c` — the explicit stability rate
  `δ(ε)` of `step2.tex` Lemma `lem:weak-grid`.  The F6 proof obtains
  this linear rate (better than the crudely-claimed `O(ε^{1/3})`).
* `weakGridRate_nonneg`, `weakGridRate_mono` (monotone in `ε`),
  `weakGridRate_le_of_le` — the `δ(ε) → 0` content: `ε ≤ ρ·c/4`
  forces `weakGridRate c ε ≤ ρ`, so the staircase-approximation error
  can be made arbitrarily small.
* `lem_weak_grid` — the Step 2 statement of `lem:weak-grid`: for an
  order-convex `D ⊆ [0,t]²` with `|D| ≥ c·t²` and `A ⊆ D` with grid
  boundary `≤ ε·t`, there is a `+`-staircase `M` with
  `|A △ M| ≤ weakGridRate c ε · |D|`.  Direct re-exposition of the
  F6a/F6b planar deliverable `OneThird.Step2.WeakGrid.weak_grid`.

### §1.2. Per-fiber grid data, grounded on a good fiber (§2 of the file)

* `toGrid : ℕ × ℕ → ℤ × ℤ` — the lattice embedding; `toGrid_injective`.
* `fiberGrid x y F` — the per-fiber grid domain `D_{x,y}`, the
  `localCoord`-image of the good fiber `F` cast into the ambient
  lattice `ℤ²` (`def:step1-data` clause (S1.2)).
* `fiberCut x y F S` — the transported cut `A_{x,y} = π_{x,y}(S ∩ F)`.
* `localCoord_injOn` — clause G1 + constant sign ⇒ `localCoord`
  injective on `F`.
* `fiberGrid_box` — every cell of `D_{x,y}` lies in `[0, t]²`
  (clause (S1.2)), from `localCoord_{fst,snd}_le`.
* `fiberGrid_isOrdConvex` — the **order-convexity transport**: clause
  G2 of `IsGoodFiber` gives order-convexity of the `ℕ²` coordinate
  image; this transports it through `toGrid` to the ambient `ℤ²`
  lattice, the hypothesis `weak_grid` needs.
* `fiberCut_subset` — `A_{x,y} ⊆ D_{x,y}`.
* `fiberGrid_card` — `|D_{x,y}| = |F|`: the coordinate map is a
  bijection `F ≃ D_{x,y}` (`def:step1-data` clause (S1.3)).

### §1.3. The per-fiber transport: BK-boundary = grid-boundary (§3)

* `fiberBKBdy F S` — the per-fiber BK-boundary of a cut `S`
  (`step2.tex` Definition `def:edge-internal`, edges internal to `F`),
  in directed form: ordered BK-edges `(L, L')` with `L ∈ F ∩ S`,
  `L' ∈ F ∖ S`.  Each undirected boundary edge contributes one
  directed pair.
* `unitMove_iff_l1dist` — the clause-G3 description of a BK move (one
  coordinate shifts by `±1`) is exactly `ℓ¹`-distance `1` between the
  `toGrid`-images.
* `fiberBKBdy_card_eq_gridBdy_card` — the **`def:step1-data` clause
  (S1.4) transport**: `|∂_BK(S ∩ F)| = |∂_{D_{x,y}} A_{x,y}|`.  Proved
  by an explicit `Finset.card_bij`: the bijection sends a directed
  BK-edge `(L, L')` to the directed grid pair `(π L, π L')`; the
  forward direction uses G1 (injectivity, to place `π L'` outside the
  cut image) and G3 (to turn the BK move into a unit grid move), the
  reverse direction inverts both.

### §1.4. The initial per-fiber transport (§4)

* `per_fiber_staircase_of_gridBdy` — intermediate form: with the
  *grid* boundary bounded directly, `weak_grid` applies on a good
  fiber.
* `per_fiber_weak_grid` — the headline of the ticket: a good fiber
  `F` with constant sign, shape hypothesis `|D_{x,y}| ≥ c·t²`, and a
  small per-fiber BK-boundary `|∂_BK(S ∩ F)| ≤ ε·t` admits a
  staircase approximation `|A_{x,y} △ M| ≤ δ(ε)·|D_{x,y}|`.  This is
  `step2.tex` `prop:per-fiber` part (ii), per-fiber core: it chains
  the (S1.4) identity into `lem:weak-grid`.

### §1.5. Non-vacuity witness (§5)

* `isGoodFiber_singleton` — a singleton `{L}` is always a good fiber
  (all three `IsGoodFiber` clauses hold trivially).
* `grid2x2` + `grid2x2_isOrdConvex` — the concrete order-convex
  `2 × 2` block used to exercise `lem_weak_grid`.
* `per_fiber_grounded_nonvacuous` — the mg-0893 capstone (see §0).

---

## §2. Why the port is not a marker

Every theorem consumes its hypotheses honestly:

* `lem_weak_grid` is the genuine planar weak grid stability lemma —
  its proof is `weak_grid`, the F6a/F6b deliverable, whose 0-`sorry`
  proof runs the full `step2.tex` `lem:weak-grid` argument (row/column
  cleanup, four-orientation reduction, `δ = 4ε/c` rate).
* `fiberGrid_isOrdConvex` genuinely *transports* order-convexity:
  clause G2 of `IsGoodFiber` is the operative input, applied to a
  `ℕ²` point recovered from the `ℤ²` interval point by `Int.toNat`.
  It is not a re-statement — the `ℕ²`→`ℤ²` cast is real content
  (`weak_grid` lives on `ℤ²`; `IsGoodFiber` G2 lives on `ℕ²`).
* `fiberBKBdy_card_eq_gridBdy_card` is the load-bearing transport: the
  `Finset.card_bij` consumes clause G1 (injectivity of `localCoord`
  on the constant-sign fiber — used in *both* the "`π L'` outside the
  cut" step and the bijection's own injectivity) and clause G3 (the
  BK-move ↔ unit-grid-move equivalence — used in *both* directions).
  Drop either clause and the proof fails.  The constant-sign
  hypothesis `hsign` is genuinely load-bearing: G1 only gives
  `(localCoord, signMarker)`-injectivity, and the transport needs
  `localCoord` alone injective.
* `per_fiber_weak_grid` threads a global cut `S ⊆ LinearExt α`
  through `fiberBKBdy_card_eq_gridBdy_card` into `lem_weak_grid` — it
  is `prop:per-fiber` part (ii) verbatim.

---

## §3. Skeptical re-audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2)

1. **Satisfiability.**  Every hypothesis of `lem_weak_grid` and
   `per_fiber_weak_grid` is satisfiable at a concrete instance —
   explicitly witnessed by `per_fiber_grounded_nonvacuous`: a genuine
   `2 × 2` grid with a non-empty boundary for the planar lemma, and a
   concrete non-empty good fiber on `Antichain3` (width-3, non-chain,
   `t = 1`) for the per-fiber transport.  The fiber and grid domains
   are non-empty; no vacuous routing.
2. **Discharge-coverage.**  No external artefact is cited as a
   discharge.  `lem_weak_grid`'s proof is the F6 `weak_grid` lemma
   itself (in tree, 0-`sorry`); the per-fiber transport's proof is the
   `card_bij` plus `lem_weak_grid`, both proved here from the Step 1
   `IsGoodFiber` clauses.
3. **Universal-quantifier truthfulness.**  No `∀ … ∃ …` existence
   claim over an unbounded family is introduced.  `per_fiber_weak_grid`
   is universally quantified over a *good fiber* `F` (an `IsGoodFiber`
   hypothesis, not a free `∃`) with a per-fiber conclusion; the
   `∃ M` is the staircase witness `weak_grid` constructs, not an
   unverified existence claim.  No false universal-existence shape.

---

## §4. Scope boundary (honest)

This ticket ports `lem:weak-grid` (Step 2 statement) and the **initial
per-fiber transport** — the per-fiber application of weak grid
stability, grounded through the (S1.4) BK-boundary identity.  Out of
scope, faithfully so, and left for **S2-B**:

* The **global double-counting** `lem:fiber-avg` /
  `cor:fiber-avg-tail` *grounded on the BK graph* — the abstract
  double-counting already lives in `Step2/FiberAvg.lean`
  (`double_counting_bounded_multiplicity`, `fiber_avg_tail_weight`);
  its instantiation at the concrete BK edge boundary of a cut, with
  the Step 1 (S1.6) bounded-multiplicity constant `K`, is the
  *global → per-fiber averaging* half of `prop:per-fiber` (part (i)),
  naturally an S2-B item.
* The full `prop:per-fiber` **assembly** (combining the bad-fiber
  mass bound with the per-fiber staircase across a fiber family) and
  `thm:step2` (the Step 2 conclusion exported to Steps 3–6) — S2-B.
* The **sign assignment** `cor:sign` / `σ(A)` — Step 3 consumption.

The existing Step 2 files (`OneD.lean`, `RowDecomp.lean`,
`WeakGrid.lean`, `WeakGridFull.lean`, `FiberAvg.lean`, `PerFiber.lean`,
`Conclusion.lean`) and the Step 1 files are **unchanged**;
`PerFiberGrounded.lean` is purely additive.  In particular the
abstract `PerFiber.lean` / `Conclusion.lean` still use the trivial
`δ = 1` form `weak_grid_exists`; `PerFiberGrounded.lean` is the
quantitative, Step-1-grounded replacement that S2-B's `prop:per-fiber`
assembly will build on.

---

## §5. Files

* `lean/OneThird/Step2/PerFiberGrounded.lean` — NEW (~610 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S2-A-Session1.md` — this file.
