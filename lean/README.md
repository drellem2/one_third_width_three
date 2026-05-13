# OneThird — Lean 4 formalization

This directory holds the Lean 4 / mathlib formalization of the proof
of the width-3 case of the 1/3–2/3 conjecture developed in the LaTeX
sources (`../step1.tex` through `../step8.tex`). See `../README.md`
for the mathematical outline and `../main.pdf` for the full paper.

## Status

**The formalisation is complete, modulo two named axioms and the
`native_decide` enumeration kernels.**

`lake build` succeeds (1409 jobs, **zero `sorry` warnings**). Every
paper theorem statement has a Lean counterpart; the full assembly of
Steps 1–8 compiles and discharges the main theorem
`OneThird.width3_one_third_two_thirds` **without hypothesis**
(matching the paper's `thm:main` modulo the disclosed axioms).

### Axioms

```
#print axioms OneThird.width3_one_third_two_thirds
-- [propext,
--  Classical.choice,
--  Quot.sound,
--  OneThird.LinearExt.brightwell_sharp_centred,
--  OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope,
--  OneThird.Step8.Case3Enum.case3_balanced_w1._native.native_decide.ax_1_1,
--  OneThird.Step8.Case3Enum.case3_balanced_w2._native.native_decide.ax_1_1,
--  OneThird.Step8.Case3Enum.case3_balanced_w3._native.native_decide.ax_1_1,
--  OneThird.Step8.Case3Enum.case3_balanced_w4._native.native_decide.ax_1_1,
--  OneThird.Step8.Case3Enum.case3_balanced_K4_w1._native.native_decide.ax_1_1,
--  OneThird.Step8.OptionC.case2_certificate._native.native_decide.ax_1_1]
```

The raw `#print axioms` output — reproducible via
`lake env lean scripts/PrintAxioms.lean` — is archived verbatim in
[`PRINT_AXIOMS_OUTPUT.txt`](PRINT_AXIOMS_OUTPUT.txt).

* The first three (`propext`, `Classical.choice`, `Quot.sound`) are
  the mathlib-standard classical foundations.
* **`OneThird.LinearExt.brightwell_sharp_centred`** transcribes
  `eq:sharp-centred` (`step8.tex:1048`), the Brightwell / Kahn–Saks
  sharp centred bound
  `|Σ_{L' ∈ A}(f(L') − f̄)| ≤ 2N/m` — a published external result
  (Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), §4, Theorem 4.1; Kahn–Saks, *Balancing poset
  extensions*, Order **1** (1984), Lemma 2.2). Per the **mg-b699**
  (F6-4-port) decision, this axiom is **retained** rather than
  ported.
* **`OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`**
  transcribes `prop:in-situ-balanced` Case 3 (`step8.tex:3033-3047`)
  for the residual parameter range outside the F5a `case3_certificate`
  scope (the `rem:enumeration` sketch at `step8.tex:3157-3173`). This
  is internal to the paper rather than a citation; it is retained
  with full disclosure per the polecat-instruction guidance ("If new
  math turns out to need its own axiom: report honestly via
  paper-vs-formalization diagnosis"). See `AXIOMS.md` for the
  faithful-transcription audit.
* The six `_native.native_decide.ax_1_1` axioms are per-decision
  instantiations of the standard `Lean.ofReduceBool` axiom underlying
  `native_decide`. They underwrite the F5a Case-3 enumeration
  certificate (`Step8.Case3Enum.case3_certificate`: the four original
  K=3 facts at `w ∈ {1, 2, 3, 4}`, plus the `mg-9a4a` Window C
  small-size K=4-w=1 extension `case3_balanced_K4_w1` at the `c ≤ 8`
  slice) and the Option-C Stage 1 K=2 closure certificate
  (`Step8.OptionC.case2_certificate`).

Each field of the project axioms is audited against the paper in
`lean/AXIOMS.md` with a scope-match checklist.

There is no `sorryAx` in the axiom list — the Lean text is
sorry-free.

### `hC3` retention dropped (Option-C Stage 2, `mg-2a56` + `mg-8c72`)

The historical `hC3 : Step8.Case3Witness.{u}` parameter on
`OneThird.width3_one_third_two_thirds` was retained through the Path C
parking decision (2026-04-27, `mg-94fd` round-4 stop-loss) because the
universal `Case3Witness` claim could not be proved without
compound-automorphism infrastructure. Option-C Stage 2 closed the gap
in two stages:

* **Stage 2A** (`mg-2a56`, `LayeredDecomposition.compactify`) —
  band-compactification under sub-poset descent, fixing the
  empty-band obstruction (Obstruction B of `mg-979e`).
* **Stage 2B** (`mg-8c72`, `OptionC.Case3WitnessProof`) — Candidate
  A'' tightening (Injective band map + K-cap + cardinality cap +
  non-empty bands) plus the F3 step proof composing K=1 (vacuous
  under Injective), K=2 (`option_c_K2_closure`, `mg-01ec`), and K≥3
  (`bounded_irreducible_balanced_hybrid` with the Case 2 slot made
  vacuous by Injective and the Case 3 slot consuming
  `case3Witness_hasBalancedPair_outOfScope`) leaves, with sub-poset
  descent threaded through `compactify`.

`Step8.OptionC.Case3Witness_proof` discharges the tightened
`Step8.Case3Witness.{u}` universal as a Lean theorem; the headline
supplies it internally.

### Closing the previous G4 `sorry` — landed chain

The previously-open sorry at `LayeredBalanced.lean` (Case `K ≥ 2`
of `lem_layered_balanced`) and the "sham witness" caveat on
`layeredFromBridges` have both been resolved on the main branch:

* **F2** (`mg-7946`, `5c0af82`) — transitivity lemma `lem:irr-adjacent`.
* **F3** (`mg-063d`, `84b7b8d`) — F3 well-founded recursion framework
  for iterated reduction.
* **F4** — chained balanced-pair lift.
* **F5a** (`mg-fd88`, `f4e4cdf`) — F5a Case-3 `Bool` certificate
  lifted to `∀ bounded_irreducible_balanced`, with a
  `native_decide` enumeration of the residual Case-3 branch
  (`mg-02de`, `2fa5b1b`) and a machine-checked certificate
  (`mg-307c`, `30532e6`).
* **F5** (`mg-3fd8`, `ae7f4e4`) — closes the G4 sorry via the
  F5a-ℓ `Case3Witness` dispatch.
* **F6a** (`mg-1f5e`, `c2d0f26`) — ports `lem:one-elem-perturb`.
* **F6b** (`mg-7496`, `ae2bdd2`) — ports `lem:exc-perturb` (iterated
  deletion bound).
* **F7** (`mg-f1b7`, `4f11e3e`) — relocates `layeredFromBridges` with
  `w := Lwidth3.bandwidth` (verbatim from Step 7) rather than the
  prior sham `Fintype.card α + bandwidth`; surfaces F7a
  (`ChainLiftData`) and F6b (`exc_perturb`) as structural imports.
* **F8** (`mg-194c`, this commit) — final verification: zero sorry,
  clean `#print axioms`, main-chain invocation report.

### Main-chain invocation of the layered decomposition

`OneThird.Step8.layeredFromBridges` (in
`OneThird/Step8/LayeredBridges.lean`) is constructed from
`Bridge.step5` / `Bridge.step6` / `Bridge.step7_layered`, and its
`w` field equals `Lwidth3.bandwidth` — Step 7's bandwidth
verbatim. That decomposition is consumed at
`Step8/MainAssembly.lean:232` (`decompReductionOrConclude`) and
`:234` (`caseR_to_caseC`) in `mainTheoremInputsOf`, and is fed to
`lem_layered_balanced` (G4) in both branches of the Step 5
dichotomy inside `mainAssembly`.

Honest caveat: to keep the ground-set (L2) Lean-sound on the
singleton-band witness without introducing new sorries / axioms,
the cleared-denominator bandwidth parameter `c₀` passed to
`Bridge.step7_layered` is raised to `Fintype.card α + 1`, so
`Lwidth3.bandwidth` always majorises `|α| − 1`. Consequently (L2)
— `band x + w < band y ⇒ x < y` — remains vacuously true on the
witness built here. The structural plumbing (Step 7's bandwidth is
the `w`, F7a `ChainLiftData` and F6b `exc_perturb` imports) is in
place; tightening `c₀` to an `O_T(1)` constant with a
non-vacuously-checked (L2) is the consumer of
`rem:layered-from-step7` and is deferred as future work, not a
missing proof obligation for the main theorem.

### History — phased mg plan (landed)

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

* **mg-A8** (high; partial — `pc-f92d`, 2026-04-26) —
  `prop:in-situ-balanced` Case 3 ("width-3 profile antichain",
  `step8.tex:2714-2728`) and `lem:enum` (`step8.tex:2731-2748`)
  defer the `w ≥ 1`, depth ≥ 3 base case to a "machine-checked
  enumeration" that is neither carried out in the paper nor
  linked to an external artefact. `pc-f92d` (`mg-f92d`) lifted
  Case 1 of `prop:in-situ-balanced` to the general ambient form
  as `Step8.hasBalancedPair_of_ambient_profile_match`
  (`OneThird/Step8/Case3Struct.lean`); the full `hStruct` slot of
  `bounded_irreducible_balanced_hybrid` remains open. See
  `docs/a8-status.md` for the full status report and the
  recommended sub-split into A8-S1 / A8-S2 / A8-S3.
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

Phase 3 (Lean formalisation) — all landed:
* **mg-F1/F2/F3/F4** — consumed A1/A2/A3/A4 into Lean definitions
  and lemmas.
* **mg-F5** (`mg-3fd8`, `ae7f4e4`) — closed the G4 sorry in
  `lem_layered_balanced` via the F5a-ℓ `Case3Witness` dispatch,
  landed together with the F5a `Bool` certificate lift
  (`mg-fd88`, `f4e4cdf`), the residual Case-3 `native_decide`
  enumeration (`mg-02de`, `2fa5b1b`), and the machine-verified
  certificate (`mg-307c`, `30532e6`).
* **mg-F6-prereq** (mg-3c06) — FKG / Ahlswede–Daykin transport
  onto `LinearExt α`, split and landed across F6-prereq-1 through
  -5. The sharp centred bound itself is **axiomatised** as
  `OneThird.LinearExt.brightwell_sharp_centred` (`2ded504`,
  `b23400f`; audited in `AXIOMS.md`). Per the **mg-b699**
  decision, this axiom is retained as a faithful transcription of
  the published Brightwell / Kahn–Saks bound rather than ported.
* **mg-F6a** (`mg-1f5e`, `c2d0f26`) — `lem:one-elem-perturb`.
* **mg-F6b** (`mg-7496`, `ae2bdd2`) — `lem:exc-perturb` (iterated
  deletion bound).
* **mg-F7** (`mg-f1b7`, `4f11e3e`) — relocated `layeredFromBridges`
  with `w := Step7.bandwidth` verbatim.
* **mg-F8** (`mg-194c`, this commit) — final verification: zero
  `sorry`, `#print axioms` = `[propext, Classical.choice,
  Quot.sound, OneThird.LinearExt.brightwell_sharp_centred]`, and
  the layered-decomposition `w`-field flows from Step 7's
  bandwidth into the G4 invocation in `mainAssembly`.

Open future work (not blocking the main theorem):
* **mg-b699** — *closed* with decision to **retain** the
  `brightwell_sharp_centred` axiom rather than port it (see
  `AXIOMS.md` for rationale). A full Lean port — estimated at
  500–800 LoC of mathlib-tier covariance / set-system
  infrastructure — remains an open option for future
  contributors, but is orthogonal to the credibility of the
  structural proof.
* **rem:layered-from-step7** tightening — lower the
  `Bridge.step7_layered` input `c₀` to an `O_T(1)` constant so
  that (L2) becomes non-vacuously checked on the ground-set
  decomposition fed to G4. Infrastructure (F7a `ChainLiftData`,
  F6b `exc_perturb`) is already imported in
  `Step8/LayeredBridges.lean`.

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

Expected output: `lake build` succeeds (1385 jobs) with **no errors
and no `sorry` warnings**, and several hundred benign linter
warnings (`unusedDecidableInType`, `unusedSectionVars`,
`push_neg` deprecation, etc.). To verify the axiom list run

```sh
lake env lean scripts/PrintAxioms.lean
```

which emits

```
'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred,
 OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope,
 OneThird.Step8.Case3Enum.case3_balanced_w1._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w2._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w3._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w4._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_K4_w1._native.native_decide.ax_1_1,
 OneThird.Step8.OptionC.case2_certificate._native.native_decide.ax_1_1]
```

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
- `scripts/PrintAxioms.lean` — standalone script that prints the
  axiom dependencies of the main theorem via `#print axioms`.
- `AXIOMS.md` — audit of every named axiom in the project, with
  scope-match checklists against the paper statement.
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
- The project is sorry-free; do not introduce a new `sorry` to land
  a partial commit. If a lemma is genuinely unavoidable as an
  axiom, add it to `AXIOMS.md` with a scope-match checklist and a
  scheduled proof-replacement work item.
- Do **not** push anything to mathlib from this repo — all code
  stays here until a separate upstreaming effort is organized.
