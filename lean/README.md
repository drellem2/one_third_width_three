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
`sorry`- and axiom-free.

**One declaration in the project still carries `sorry`**: the
`hw_zero : L.w = 0` obligation in `lem_layered_balanced` Case
`K ≥ 2` (`step8.tex:1768-1795`), threaded into the subtype helper
`lem_layered_balanced_subtype`. The F4-foundation probability
invariance `OrdinalDecomp.probLT_restrict_eq` was closed in
`mg-ed86` (via `tripleEquiv`), and the subtype helper itself was
closed in `mg-f292` under the tight-L hypothesis.

### The remaining `sorry` — structurally undischargeable as-is

Line numbers below are for the `sorry` token itself.

| # | File:line | In declaration | Category |
|---|-----------|----------------|----------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:710` | `lem_layered_balanced` (K ≥ 2 branch) | `L.w = 0` tight-L obligation for a generic `LayeredDecomposition α` passed into the subtype helper |

**`mg-46a7` analysis (2026-04-21): this sorry is *not* a one-step
plumbing gap — it is a structural divergence from the paper.** The
previous formalization chain introduced `hw_zero : L.w = 0` as a
simplification of the paper's `w ≥ 0` proof, reducing the subtype
helper's residual content to a single-step band stratification
(`mg-f292`). The caller `lem_layered_balanced` then inherits the
obligation to supply `L.w = 0` for the decomposition it receives.

For the `mainTheoremInputsOf` chain, that decomposition is
`layeredFromBridges`, which would need to be constructed with
`w = 0` for every finite non-chain width-≤ 3 poset. **This is
structurally impossible.** A `LayeredDecomposition α` with `w = 0`
forces `α` to be an ordinal sum of antichains of size ≤ 3 (by
`(L2)` specialised to `w = 0` combined with `(L1a)`). Counterexample:
the 2+2 poset `{a, b, c, d}` with `a < c`, `b < d`, all other pairs
incomparable is non-chain width-2 (hence width-≤ 3) but admits no
such decomposition.

**The paper proof is fine** — `lem:layered-balanced`
(`step8.tex:1768-1795`) handles arbitrary `w ≥ 0` via iterated
ordinal-sum reduction inside the window `W(i, j)`. The Lean gap
is purely formalisation plumbing:

1. **Iterated ordinal-sum recursion in the subtype helper.** Replace
   the `hw_zero` shortcut with a well-founded recursion on "number
   of bands in the residual irreducible layered piece" that uses
   `probLT_restrict_eq` at each split. Currently the
   `OrdinalDecomp` API gives the single-split factorisation; the
   iteration needs to be built on top.
2. **Window-based `OrdinalDecomp` construction.** Fit `W(i, j)`
   into the Lower/Mid/Upper shape of `OrdinalDecomp`, which requires
   `w + 1`-wide buffer zones for `(L2)` to fire on the Lower<Mid
   and Mid<Upper bands. This is not directly available from the
   layered axioms; it needs the Step 5(C) / Step 7 band-index
   refinement.
3. **Tight `layeredFromBridges`.** Replace the singleton-band
   stub with a real construction that packages Step 7's
   `LayeredWidth3` (with its `bandwidth` field giving the paper's
   `w`) into a ground-set `LayeredDecomposition α` where `w =
   Lwidth3.bandwidth` (not `|α| + bandwidth`). This is the paper's
   `rem:layered-from-step7` (`step8.tex:1349-1360`) ground-set lift,
   which also absorbs the `O_T(1)`-size exceptional set `X^{exc}`
   into a γ/2 slack.

Pieces 1, 2, 3 are workmanlike Lean plumbing (not research), but
together they are multi-week scope — not a single polecat. Follow-up
mg items scoped from `mg-46a7` track the three pieces.

### Axioms

```
#print axioms OneThird.width3_one_third_two_thirds
-- [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` reflects the single remaining `sorry` above; the other
three are the mathlib-standard classical foundations. Closing the
three plumbing pieces listed above would drop `sorryAx` and leave
only `[propext, Classical.choice, Quot.sound]`.

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
