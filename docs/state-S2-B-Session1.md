# State — S2-B — Session 1: Step 2 port part 2 — `prop:per-fiber` staircase approximation + density bookkeeping

**Ticket:** mg-0868 (OneThird-S2-B: Step 2 Lean port part 2 — per-fiber
staircase approximation plus density bookkeeping).
**Branch:** `polecat-mg-0868`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-2.
**Depends:** mg-0893 (S2-A, `lem:weak-grid` + initial per-fiber
transport); merged.

**Scope.** Wave-2 ticket of the Piece-1 (Steps 1-6 cascade port)
decomposition.  Completes Step 2 by porting `step2.tex`
`prop:per-fiber` (the per-fiber staircase approximation, quantitative
form) and `thm:step2` (the Step 2 conclusion exported to Steps 3–6),
plus the global double-counting `lem:fiber-avg` / `cor:fiber-avg-tail`
grounded on the BK graph and the `ε₂` density bookkeeping the
downstream Step 6 consumes.

---

## §0. Verdict — **GREEN-S2-B-delivered**

`lean/OneThird/Step2/PerFiberGrounded2.lean` (NEW, ~714 LoC) delivers,
building directly on the S2-A namespace `OneThird.Step2.PerFiberGrounded`:

* `globalBKBdy` + `mem_globalBKBdy` / `globalBKBdy_empty` — the
  ambient directed BK-boundary of a cut `S` (`step2.tex`
  `def:edge-internal` ambient form), one directed pair per undirected
  boundary edge, matching the S2-A directed `fiberBKBdy` convention;
* `fiberBKBdy_eq_filter_globalBKBdy` / `fiberBKBdy_subset_globalBKBdy`
  — the per-fiber boundary is the fiber-internal restriction of the
  global boundary (the observation opening `lem:fiber-avg`'s proof);
* `RichFamily` — the rich-good-fiber family `𝓡` of `prop:per-fiber`:
  a `Finset` of rich pairs, each carrying a good fiber of constant
  sign;
* `edgeInternal` + `internalCount_eq` — the `def:edge-internal`
  incidence relation, with the abstract `FiberAvg.internalCount`
  identified with the per-fiber boundary count;
* `lem_fiber_avg` / `lem_fiber_avg_conductance` — `step2.tex`
  `lem:fiber-avg` **grounded on the BK graph**: instantiates the
  abstract `FiberAvg.double_counting_bounded_multiplicity` at
  `globalBKBdy S`, giving `Σ |∂_BK(S∩fib)| ≤ K·|∂_BK S| ≤ K·κ·|S|`;
* `badFibers` / `goodFibers` + membership/partition lemmas — the
  good-fiber set `𝓖` of `prop:per-fiber` and its complement;
* `cor_fiber_avg_tail` — `step2.tex` `cor:fiber-avg-tail` grounded:
  the Markov tail `η·Σ_{bad}|fib| ≤ K·κ·|S|`;
* `fiberStaircaseRate` + `_nonneg` / `_le_of_le` — the explicit
  per-fiber `ε₂ = ε₂(γ)` constant and its `ε₂ → 0` qualitative
  content;
* `prop_per_fiber_bad_mass` / `prop_per_fiber_staircase` /
  `prop_per_fiber` — `step2.tex` `prop:per-fiber`: (i) the bad-fiber
  mass bound `Σ_{bad}|fib| ≤ K·κ·|S|/η` and (ii) the per-fiber
  staircase across the whole good-fiber family;
* `thm_step2` — `step2.tex` `thm:step2`: the Step 2 conclusion stated
  with the uniform `ε₂` bookkeeping (downstream signature match);
* `step2_good_mass_fraction` — the `(1-α)`-mass-fraction corollary
  (`prop:per-fiber`'s "consequently" clause / `thm:step2`'s `1-o(1)`);
* `antichain3Family` + `per_fiber_grounded2_nonvacuous` — the mg-0868
  acceptance witness.

`lake build OneThird.Step2.PerFiberGrounded2` is clean (exit 0,
`✔ Built OneThird.Step2.PerFiberGrounded2`).  `lake build OneThird`
(full library) is clean.  The new file produces **no warnings** —
no `linter.unusedSectionVars`, no `linter.unusedDecidableInType`, no
`linter.style.show`.  (The warnings still emitted by the toolchain
are all on pre-existing files — `PerFiberGrounded.lean` (S2-A),
`Step6/ErrorControl.lean`, `Case3WitnessProof.lean` — unchanged here.)

**No `sorry`, no new axiom.**  `#print axioms` confirms `thm_step2`,
`lem_fiber_avg`, `cor_fiber_avg_tail`, `step2_good_mass_fraction` and
`per_fiber_grounded2_nonvacuous` all depend on exactly
`[propext, Classical.choice, Quot.sound]` — the three standard
mathlib axioms, no `sorryAx`, no project axiom.

---

## §1. What `prop:per-fiber` + `thm:step2` say, and how the port grounds them

`step2.tex` Step 2 has two halves.  S2-A delivered the first
(`lem:weak-grid` + the per-fiber *core* `per_fiber_weak_grid`).  S2-B
delivers the second: the **global-to-per-fiber transport** and the
**assembly**.

### §1.1 `lem:fiber-avg` — the double-counting (grounded)

`step2.tex` `lem:fiber-avg`: if `|∂_BK S| ≤ κ|S|` and every BK-edge
is internal to at most `K` fibers of the family `𝓡`, then
`Σ_{(x,y)∈𝓡} |∂_BK(S∩fib_{x,y})| ≤ K·κ·|S|`.

The abstract double-counting already lived in `Step2/FiberAvg.lean`
(`double_counting_bounded_multiplicity`, a pure Fubini argument over
`Finset`s).  The S2-B grounding instantiates it at the **concrete BK
boundary**:

* `globalBKBdy S` is the directed BK-boundary `{(L,L') : L∈S, L'∉S,
  BKAdj L L'}` — cardinality-equal to the undirected `∂_BK S`, and
  matching the S2-A directed convention for `fiberBKBdy`;
* `fiberBKBdy_eq_filter_globalBKBdy` proves the per-fiber boundary is
  exactly `(globalBKBdy S).filter (both endpoints in fib)` — this is
  the `lem:fiber-avg`-proof observation "the [one-endpoint-in-`S`]
  condition depends only on `S` and `e`, not on the fiber";
* `internalCount_eq` then identifies `FiberAvg.internalCount` with the
  per-fiber boundary count, so `lem_fiber_avg` is the abstract lemma
  read off at `B := globalBKBdy S`, `R := Fam.carrier`,
  `internal := edgeInternal`.

`lem_fiber_avg_conductance` folds in `|globalBKBdy S| ≤ κ|S|`.

### §1.2 `cor:fiber-avg-tail` — the Markov tail (grounded)

`cor_fiber_avg_tail`: `η·Σ_{bad}|fib| ≤ K·κ·|S|`, by
`η·Σ_{bad}|fib| ≤ Σ_{bad}|∂_BK(S∩fib)| ≤ Σ_{𝓡}|∂_BK(S∩fib)| ≤
K·κ·|S|`.  `prop_per_fiber_bad_mass` rearranges this to the
mass form `Σ_{bad}|fib| ≤ K·κ·|S|/η`.

### §1.3 `prop:per-fiber` — the assembly

`prop_per_fiber` bundles the two parts of `step2.tex`
`prop:per-fiber`:

* **(i)** `prop_per_fiber_bad_mass`: bad-fiber mass `≤ K·κ·|S|/η`;
* **(ii)** `prop_per_fiber_staircase`: every good fiber `(x,y)∈𝓖`
  admits a monotone staircase `M_{x,y}` with error
  `|A_{x,y} △ M_{x,y}| ≤ fiberStaircaseRate · |D_{x,y}|`.

Part (ii) is the family-level instance of the S2-A per-fiber
transport `per_fiber_weak_grid`.

### §1.4 `thm:step2` — the Step 2 conclusion

`thm_step2` is the Step 2 output exported to Steps 3–6, stated with
the explicit `ε₂` bookkeeping.  `step2_good_mass_fraction` is the
`(1-α)`-mass-fraction "consequently" clause.

---

## §2. The `ε₂` bookkeeping (mg-0868 downstream signature match)

The mg-0868 ticket flags (per mg-6ab8 §2.2): *the `ε₂ = ε₂(γ)`
constant must enter quantitatively into the Step 2 staircase
statement, with the exact shape Step 6 consumes; the S2-B output
signature must match Step 6 input hypotheses (Checkpoint 2 verifies).*

How this port discharges that requirement:

* **`fiberStaircaseRate c η |fib| t`** is the **named, explicit**
  per-fiber `ε₂`.  It is the S2-A weak-grid rate `weakGridRate`
  (`δ(ε)=4ε/c`) evaluated at the boundary budget `η·|fib|/t` of a
  good fiber.  `step2.tex` `prop:per-fiber` (ii) writes the per-fiber
  staircase rate as `δ(ε_{x,y})` with `ε_{x,y} = η·t_{x,y}`; the
  grounded port uses the slightly sharper boundary-budget parameter
  `η·|fib_{x,y}|/t_{x,y}` (a good fiber satisfies
  `|∂_BK(S∩fib)| ≤ η·|fib|`, so this is exactly the `ε` with
  `|∂| ≤ ε·t`).  The paper's coarser `ε_{x,y}=η·t` is the same up to
  `|fib| ≤ t²`; the sharper form avoids needing the cruder
  `|fib| ≤ t²` estimate and is `≤ η·t` whenever `|fib| ≤ t²`.

* **`thm_step2` takes `ε₂` as an explicit parameter** with the
  hypothesis `huniform : ∀ good fiber, fiberStaircaseRate … ≤ ε₂`,
  and concludes the **uniform** per-fiber error
  `|A_{x,y} △ M_{x,y}| ≤ ε₂·|D_{x,y}|`.  This is exactly the shape
  `step6.tex` `lem:most-good` consumes: a single threshold constant
  `ε₂` on the per-fiber error, the good fibers being those at error
  `≤ ε₂·|fib|`.

* **`fiberStaircaseRate_le_of_le`** records the `ε₂ → 0` qualitative
  content (`step2.tex` `lem:weak-grid`'s `δ(ε)→0`): taking the
  density threshold `η` small enough drives `ε₂` below any target
  `ρ > 0`.  This is the bookkeeping Step 6 relies on to push `ε₂`
  under its dichotomy threshold (`step6.tex` `lem:most-good`'s
  `Φ₀`-vs-`ε₂` choice).

**Honest note for Checkpoint 2.**  `step6.tex` `lem:most-good`'s
good/bad split is on the per-fiber *error set* `B_α` (`|B_α| ≤ ε₂|F|`);
this port's split (faithful to `step2.tex` `prop:per-fiber`) is on the
per-fiber *boundary* `|∂_BK(S∩fib)| ≤ η|fib|`.  Good in the
boundary sense ⇒ small error (via `per_fiber_weak_grid`) ⇒ good in
the error sense, so the two are compatible; the exact reconciliation
of the constants (`step6.tex`'s `C₂'` vs this port's `K·κ/η`) is a
genuine Step-6-porting concern and is what Checkpoint 2 (after S6
lands) is for.  The shapes already match: bad-fiber mass
`≤ (constant)·|S|/(threshold)`, good-fiber error `≤ ε₂·|fib|`.

---

## §3. Non-vacuity (mg-0868 acceptance bar)

`per_fiber_grounded2_nonvacuous` instantiates the assembly at the
concrete width-3 non-chain poset `Antichain3`:

* `Antichain3` is genuinely width-3 (`HasWidth Antichain3 3`) and
  non-chain (`¬ IsChainPoset Antichain3`);
* `antichain3Family L` is a genuine non-empty `RichFamily` carried by
  the rich pair `(a0,a1)` (common-neighbour-chain length `t = 1`),
  with a singleton good fiber `{L}` for a genuine
  `L : LinearExt Antichain3`;
* `lem_fiber_avg` fires (the grounded double-counting applies);
* the good-fiber set `𝓖` is genuinely non-empty — `(a0,a1) ∈ 𝓖`;
* `thm_step2` fires — both the bad-fiber mass bound (i) and a genuine
  per-fiber staircase (ii) on the good fiber, with the explicit
  `ε₂ = fiberStaircaseRate 1 1 1 1` bookkeeping.

No Subsingleton-on-empty baseline: the family, the fiber, and the
good-fiber set are all non-empty, on a genuinely width-3 non-chain
poset.  (Consistent with the S2-A `per_fiber_grounded_nonvacuous`
witness, which also used a singleton good fiber on `Antichain3`.)

---

## §4. Scope boundary (honest)

This ticket completes Step 2: `lem:fiber-avg`, `cor:fiber-avg-tail`,
`prop:per-fiber` and `thm:step2` are all ported, grounded, 0-sorry,
no new axiom.  Out of scope, faithfully so:

* The **sign assignment** `cor:sign` / `σ_{x,y} ∈ {±,−}` of
  `thm:step2` clause (2) — this is Step 3 consumption
  (`step3.tex` `lem:local-sign`), explicitly an S3 item (mg-6ab8
  §2.3); `thm_step2` here delivers clauses (1) (staircase) and (3)
  (error set with linear bookkeeping), and the sign is read off the
  staircase type downstream.
* The **Step 6 reconciliation** of the `ε₂` / `C₂'` constants — a
  Checkpoint 2 / S6-porting concern (see §2 honest note).

The S2-A file `PerFiberGrounded.lean` and the abstract Step 2 files
(`OneD.lean`, `RowDecomp.lean`, `WeakGrid.lean`, `WeakGridFull.lean`,
`FiberAvg.lean`, `PerFiber.lean`, `Conclusion.lean`) are **unchanged**;
`PerFiberGrounded2.lean` is purely additive and reuses
`FiberAvg.double_counting_bounded_multiplicity` (the abstract
double-counting) and the S2-A per-fiber transport.

---

## §5. Files

* `lean/OneThird/Step2/PerFiberGrounded2.lean` — NEW (~714 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S2-B-Session1.md` — this file.
