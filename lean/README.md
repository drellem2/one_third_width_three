# OneThird — Lean 4 formalization

This directory holds the Lean 4 / mathlib formalization of the proof
of the width-3 case of the 1/3–2/3 conjecture developed in the LaTeX
sources (`../step1.tex` through `../step8.tex`). See `../README.md`
for the mathematical outline and `../main.pdf` for the full paper.

## Status

**`lake build` succeeds (1347 jobs, clean).** Every paper theorem
statement has a Lean counterpart; Steps 1–7 and the Step 8 spine —
including the previously-accepted Dilworth's theorem and the
`fkg_case_output` axiom (now `bipartite_balanced_enum`) — compile
without adding new axioms.

**One declaration in the project still carries `sorry`**: the
single-token `(by sorry)` inside `lem_layered_balanced` (Case
`K ≥ 2`) that supplies the `hw_zero : L.w = 0` hypothesis to
`lem_layered_balanced_subtype`.  The previously-listed sorry in
`OrdinalDecomp.probLT_restrict_eq` was closed in mg-ed86 (commit
`f3e1a32`).

### Remaining `sorry` — 1 token, 1 declaration

| # | File:line | In declaration | Category |
|---|-----------|----------------|----------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:728` | `lem_layered_balanced` (Case `K ≥ 2`) | Iterated ordinal-sum reduction of the window `W(i, j)`; closure depends on `lem:enum` (`step8.tex:2731-2748`) for `w ≥ 1` depth ≥ 3, the base case of the strong-induction proof (`step8.tex:2752-2805`). See §"Gap analysis" below and §"Q1 re-read checkpoint" for the remaining A8 dependency. |

### Gap analysis: what closing the sorry requires

Closing this one token is **not** a single-step formalisation.
Three items the paper asserts but does not fully prove (**M**), two
items of Lean infrastructure that do not exist yet (**L**), and
one sibling issue that makes the G4 lemma vacuously invoked on the
main theorem path even when closed (**M-c**). Together these
define Option A — the paper-faithful iterated ordinal-sum.

**M-a — Transitivity lemma.** *(paper-side closed by mg-ec58.)*
Stated and proved as `lem:irr-adjacent` at `step8.tex:2461-2478`:
if every adjacent band-pair were fully comparable, transitivity
forces every cross-pair comparable, contradicting irreducibility.
Lean image is F2 (mg-7946), still pending.

**M-b — Inner window localisation does not isolate.**
*(paper-side closed by mg-ec58.)* The inner-window pitfall is
documented as `rem:inner-window-pitfall` (`step8.tex:2481-2503`);
the fix is a strong induction on `|X|` replacing the
"window-reduce-window" pipeline, proved at
`step8.tex:2752-2805` with `rem:old-vs-new` at
`step8.tex:2807-2836`. Base case is `prop:in-situ-balanced`
(`step8.tex:2646-2729`); its `w ≥ 1`, depth ≥ 3 enumeration step
(`prop:in-situ-balanced` Case 3 + `lem:enum`) is still
under-spelled — tracked as **mg-A8** in the Q1 checkpoint below.
Lean image is F3 (mg-063d), still pending.

**M-c — `layeredFromBridges` is a sham witness.** The ground-set
layered decomposition fed into `caseC` on the main theorem path
has `w = |α| + bandwidth`, making (L2) vacuous
(`band x + w > |α| ≥ band y` always). Even full closure of M-a
and M-b yields a G4 lemma whose invocation is vacuous on input
on the main path. Closing this requires the Step 8 perturbation
bound `eq:exc-perturb` (now stated and proved as `lem:exc-perturb`,
`step8.tex:1025-1062`, landed via mg-d0e4/A6) for deleting the
bounded exceptional set `X^exc`; the corresponding Lean Replacement
is F7 (mg-f1b7), still pending.

**L-γ — Well-founded recursion framework.** Once M-b resolves,
Lean needs a recursion over band count (or band count +
interaction width) capturing the iteration. Not set up.

**L-δ — Chained balanced-pair lift.** Each iteration step produces
an `OrdinalDecomp`; the balanced pair in the terminal irreducible
piece must lift through the entire chain via
`OrdinalDecomp.hasBalancedPair_lift` (base case exists). The
chain induction does not.

**L-ε — Perturbation-bound formalisation.** Consumer of M-c in
Lean.

The partial helper `lem_layered_balanced_subtype`
(`LayeredBalanced.lean:376`, proven under `hw_zero : L.w = 0`) is
**not a base case** of the general argument. Under `w = 0`, α is
forced to be an ordinal sum of antichains of size ≤ 3 — a strict
subset of width-3 non-chain posets. The `2 + 2` poset is a concrete
width-3 non-chain that admits no layered decomposition with `w = 0`.

### Axioms

```
#print axioms OneThird.width3_one_third_two_thirds
-- [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` reflects the single remaining sorry at
`LayeredBalanced.lean:728`; the other three are the mathlib-standard
classical foundations. Closing the sorry requires items M-a, M-b,
L-γ, L-δ (math + Lean infrastructure) together, not a single local
edit.

### Closing the sorry — phased mg plan

Phase 1 (math, rewrite `step8.tex`):
* **mg-A1** — formalise "layer-ordinal reducible" Definition +
  factorisation Lemma. *(landed)*
* **mg-A2** — prove M-a (transitivity → adjacent incomparable).
  *(content landed via mg-ec58 as `lem:irr-adjacent`)*
* **mg-A3** — resolve M-b (nested iteration or `K^⋆ = 2` or
  alternative argument). *(landed as strong induction on `|X|`,
  `rem:inner-window-pitfall` / `rem:old-vs-new`)*
* **mg-A4** — chained balanced-pair lift Lemma statement + proof.
  *(landed as `lem:chained-lift`)*
* **mg-A5** — flesh out `rem:layered-from-step7` into an explicit
  proof sketch. *(landed as `lem:layered-from-step7`)*
* **mg-A6** — fully formalise `eq:exc-perturb` proof. *(landed as
  `lem:exc-perturb` + `lem:one-elem-perturb`)*
* **mg-A7** — arithmetic-richness honesty: main theorem restricted
  to `Hypothesis hyp:arith`; all `rem:*` reflect the restricted
  scope. *(landed)*

Phase 2 (QA):
* **mg-Q1** — independent review of A1–A7 *(re-read pass pc-4a4b,
  2026-04-21: two new items filed, see checkpoint below)*.
* **mg-Q2** — audit every `rem:*` in `step8.tex` for similar
  under-spelled claims. *(landed; produced mg-A7)*
* **mg-Q3** — cross-reference paper vs. Lean signatures.

#### Q1 re-read checkpoint (pc-4a4b, 2026-04-21)

Polecat `pc-4a4b` re-read §`sec:g4-balanced-pair` and §`sec:main-thm`
after A1–A7 landed. A1, A2, A4, A5, A6, A7 verified consistent and
proof-bearing at the paper level. Two new under-spelled claims
surfaced:

* **mg-A8** (high) — `prop:in-situ-balanced` Case 3 ("width-3 profile
  antichain", `step8.tex:2714-2728`) and `lem:enum`
  (`step8.tex:2731-2748`) defer the `w ≥ 1`, depth ≥ 3 base case
  to a "machine-checked enumeration" that is neither carried out in
  the paper nor linked to an external artefact. The w = 0 fragment is
  covered by the existing Lean helper `lem_layered_balanced_subtype`,
  so F5 still needs A8's output to discharge `hw_zero`.
* **mg-A9** (discharged, 2026-04-21) — exposition of
  `lem:one-elem-perturb`'s "second factor" bound
  `|p_{xy}(Q) - Pr(A | \bar B)| ≤ 2/(m-1)` (`step8.tex:997-1013`)
  rewritten with a direct computation on the weighted means
  `F_A, |A|, \bar f`: closed form
  `p_{xy}(Q) - Pr(A|\bar B) = (m/(m-\bar f))(p_{xy}(Q) - p_{xy}(Q-z))`
  makes `eq:second-factor` a corollary of the main bound
  `eq:one-elem-perturb`, and the main bound is established via the
  $1$-Lipschitz property of $f$ on the adjacent-transposition Cayley
  graph combined with a Brightwell-style single-element perturbation
  argument (cited to `Brightwell1999`, `KahnSaks1984`,
  `AhlswedeDaykin1978`/`FKG1971`).

F1–F6 Lean items blocked on Q1 stay blocked on A8 (F3/F5 in
particular); A9 is decoupled from the Lean closure.

Phase 3 (Lean formalisation):
* **mg-F1/F2/F3/F4** — consume A1/A2/A3/A4 into Lean definitions
  and lemmas.
* **mg-F5** — close the sorry at `LayeredBalanced.lean:728` using
  F1..F4.
* **mg-F6** — formalise `eq:exc-perturb` in Lean (consumes A6).
* **mg-F7** — replace `layeredFromBridges` with the tight bounded-`w`
  witness (consumes F6, A5).
* **mg-F8** — final verification: sorry count = 0,
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
  `caseC layeredFromBridges` is non-vacuous on input.

### Import closure of the main theorem

The transitive import closure of `OneThird.width3_one_third_two_thirds`
covers at least one file from each of Steps 1–7 and the full Step 8
spine (`TheoremE`, `FrozenPair`, `G2Constants`, `LayeredReduction`,
`LayeredBalanced`, `Window`, `SmallN`, `BipartiteEnum`,
`MainAssembly`). The `OneThird.Bridge` module wires the Steps 1–7
top-level abstract theorems to poset-level statements usable by the
Step 8 assembly.

## Project structure — `OneThird.Mathlib.*` vs. `OneThird.*`

All Lean source lives in this directory — nothing is pushed to
mathlib from here. Files are partitioned so that the
mathlib-general results can be extracted later without restructuring:

- **`OneThird/Mathlib/`** — results general enough to be contributed
  back to mathlib eventually (poset width, Dilworth's theorem,
  `Fintype (LinearExt α)`, edge boundary for `SimpleGraph`,
  Bubley–Karzanov graph, conductance / Dirichlet form, 2D-grid
  isoperimetry on top of `YoungDiagram`, …). These modules depend
  only on mathlib, not on anything specific to the 1/3–2/3 proof.
- **`OneThird/StepN/`** — the proof-specific lemmas from
  `stepN.tex`. These may depend on `OneThird/Mathlib/*` and on
  earlier `OneThird/StepM/*`.
- **`OneThird/MainTheorem.lean`** — the top-level assembly.

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager). It will pick up `lean-toolchain` automatically and install the
matching Lean version on first use.

## Build

```sh
cd lean
lake exe cache get   # fetch prebuilt mathlib olean cache
lake build
```

`lake exe cache get` is optional but strongly recommended — building mathlib
from source takes hours, whereas the cache downloads in a few minutes.

Expected output: `lake build` succeeds with two `sorry` warnings
(`lem_layered_balanced_subtype` and
`OrdinalDecomp.probLT_restrict_eq`) and several hundred benign
linter warnings
(`unusedDecidableInType`, `unusedSectionVars`). There should be no
errors.

## File inventory

Top-level:

- `lakefile.toml` — Lake project config, pins `mathlib` to `v4.29.1`.
- `lean-toolchain` — pinned Lean version (`leanprover/lean4:v4.29.1`).
- `OneThird.lean` — library root; re-exports all submodules.
- `OneThird/Basic.lean` — shared imports and the `Incomp` predicate.
- `OneThird/Poset.lean` — width, antichains, common-neighbor chain,
  rich pairs.
- `OneThird/LinearExtension.lean` — project-specific layer on top of
  `Mathlib/LinearExtension/Fintype`: the Bubley–Karzanov graph,
  balance / counterexample definitions, BK conductance.
- `OneThird/RichPair.lean` — local coordinates, external-ordering
  equivalence, good/raw/bad fibers, the Step 1 local interface
  theorem.
- `OneThird/MainTheorem.lean` — the main width-3 1/3–2/3 theorem and
  Theorem E (`counterexample ⇒ low BK expansion`).
- `OneThird/Bridge.lean` — poset-level re-statements of each Step 1–7
  top-level abstract theorem.
- `MATHLIB_GAPS.md` — mathlib-coverage audit for the eight-step proof.
- `../.github/workflows/lean.yml` — CI for `lake build`.

`OneThird/Mathlib/*`: poset `Width`, `Dilworth`,
`Indecomposable`; `SimpleGraph.EdgeBoundary`; `BKGraph`; `DirichletForm`;
`Grid2D`; `LinearExtension/Fintype`.

`OneThird/Step1/*`: `CommonChain`, `Corollaries`, `LocalCoords`.
`OneThird/Step2/*`: `OneD`, `RowDecomp`, `FiberAvg`, `WeakGrid`,
`PerFiber`, `Conclusion`.
`OneThird/Step3/*`: `LocalSign`, `CommonAxes`, `Step3Theorem`.
`OneThird/Step4/*`: `RectangleModel`, `DensityRegularization`,
`Step4Theorem`.
`OneThird/Step5/*`: `EndpointMono`, `ConvexOverlap`, `FiberMass`,
`Layering`, `SecondMoment`, `Dichotomy`.
`OneThird/Step6/*`: `ErrorControl`, `CommutingSquare`, `RichnessBound`,
`Incoherence`, `OverlapCounting`, `Assembly`.
`OneThird/Step7/*`: `SignedThreshold`, `SignConsistency`, `Cocycle`,
`Potential`, `SingleThreshold`, `Bandwidth`, `Assembly`.
`OneThird/Step8/*`: `TheoremE`, `FrozenPair`, `G2Constants`,
`LayeredReduction`, `LayeredBalanced`, `Window`, `SmallN`,
`BipartiteEnum`, `MainAssembly`.

## Updating mathlib

Bump `rev` in `lakefile.toml` and `lean-toolchain` to the matching Lean
release, then run `lake update && lake exe cache get && lake build`.

## Contributing

- Prefer the smallest self-contained commit: one lemma or one
  definition + its glue lemmas.
- If a result is mathlib-flavored (no project-specific combinatorics),
  place it in `OneThird/Mathlib/` so it can be extracted later.
- Keep existing `sorry`s visible: deleting a `sorry` without proving
  it is a review red flag.
- Do **not** push anything to mathlib from this repo — all code
  stays here until a separate upstreaming effort is organized.
