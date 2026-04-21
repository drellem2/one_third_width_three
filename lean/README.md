# OneThird — Lean 4 formalization

This directory holds the Lean 4 / mathlib formalization of the proof
of the width-3 case of the 1/3–2/3 conjecture developed in the LaTeX
sources (`../step1.tex` through `../step8.tex`). See `../README.md`
for the mathematical outline and `../main.pdf` for the full paper.

## Status

**`lake build` succeeds (1334 jobs, clean).** Every paper theorem
statement has a Lean counterpart; Steps 1–7 and the Step 8 spine —
including the previously-accepted Dilworth's theorem and the
`fkg_case_output` axiom (now `bipartite_balanced_enum`) — compile
`sorry`- and axiom-free.

**Two declarations in the project still carry `sorry`**: the G4
reduction glue `lem_layered_balanced` (Case `K ≥ 2`, the paper's
reduction from an arbitrary non-chain layered width-3 poset to the
bipartite case via ordinal-sum decomposition + sub-poset restriction,
`step8.tex:1768-1796`), and the F4-foundation marginal-invariance
identity `OrdinalDecomp.probLT_restrict_eq` for ordinal-sum sub-poset
restriction. The Case `K = 1` branch (`step8.tex:1763-1766`) and the
bipartite conclusion `bipartite_balanced_enum` are `sorry`-free.

### Remaining `sorry`s — 2 tokens, 2 declarations

Line numbers below are for the `sorry` token itself.

| # | File:line | In declaration | Category |
|---|-----------|----------------|----------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:468` | `lem_layered_balanced` (Case `K ≥ 2`) | G4 reduction glue — ordinal-sum decomposition + sub-poset restriction to realise the bipartite reduct (`step8.tex:1768-1795`) |
| 2 | `OneThird/Mathlib/LinearExtension/Subtype.lean` (in `OrdinalDecomp.probLT_restrict_eq`) | sub-poset marginal-invariance | F4-foundation: bijection `LinearExt α ≃ LinearExt ↥Lower × LinearExt ↥Mid × LinearExt ↥Upper` for ordinal-sum decompositions (`step8.tex:1584-1598`) |

Both are *single-step* gaps: #1 is reduction glue, #2 is the
combinatorial concatenation/factorisation of linear extensions over
an ordinal sum (the only missing F4 foundation item). The heavy
machinery they feed into (`windowLocalization`,
`bipartite_balanced_enum`, `bipartiteBalanced`, Dilworth, FKG
enumeration, `OrdinalDecomp` + `restrictMid` + position bounds) is
already `sorry`-free.

### Axioms

```
#print axioms OneThird.width3_one_third_two_thirds
-- [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` reflects the two `sorry`s above; the other three are the
mathlib-standard classical foundations. Closing
`lem_layered_balanced` would drop `sorryAx` and leave only
`[propext, Classical.choice, Quot.sound]`.

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
(`lem_layered_balanced` Case `K ≥ 2` and
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
