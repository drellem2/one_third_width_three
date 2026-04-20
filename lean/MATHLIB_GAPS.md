# Mathlib coverage audit for the width-3 1/3–2/3 proof

**Scope.** This document surveys the mathematical prerequisites of the
eight-step proof (`step1.tex`–`step8.tex`, assembled via `main.tex`) and
reports, for each, whether the supporting definition/theorem is already
formalized in Mathlib (as of the research pass on 2026-04-19). It is
intended as a pre-formalization scoping doc: an estimate of "how much
scaffolding do we already get for free, and how much would we have to
build from scratch before the width-3 argument itself can be written in
Lean."

The document is research-only — no Lean source is written, and the
audit does not attempt to prove anything. Difficulty estimates are
expressed relative to a Mathlib contributor of average experience,
working with the Step-N source files as a target specification.

**Upstreaming policy (2026-04-19).** All Lean source stays in this
repo; nothing is pushed to mathlib from here. The repo layout
(`OneThird/Mathlib/*` vs. `OneThird/StepN/*` — see `README.md`) is a
separation of concerns so that the mathlib-flavored results *can* be
extracted later, not a commitment to do so now.

**Status of this audit after the statement-only scaffold.** The
scaffold merged on 2026-04-19 (mg-8d16, mg-b6aa, mg-8196) realizes the
initial definitions (§2 Bucket B3 `LinearExt`, B4 `probLT`, C4
`BKAdj`, C5 `volume`, C6 `Phi`, …) as Lean statements-with-`sorry`.
The §5 "Minimal dependency chain" below therefore becomes the work-item
partition for the formalization project itself: each numbered block in
§5 corresponds to a cluster of mg items tagged `one-third, lean`.

Terminology convention below:

- **IN MATHLIB** — usable as-is, with a cited file path.
- **PARTIAL** — the ambient objects or a weaker form are present, but
  the named result/API the proof would cite is missing.
- **NOT IN MATHLIB** — would need to be formalized from scratch for
  this project.

---

## 1. What the proof actually depends on

Reading the step files (`step1.tex`–`step8.tex`) and `main.tex`, the
proof invokes the following mathematical objects and external results.
They fall into six buckets; each bucket is audited in detail in §2.

| Bucket | Used in | Representative citations |
|---|---|---|
| A. Poset foundations | all steps | `PartialOrder`, `IsChain`, `IsAntichain` |
| B. Width, Dilworth, linear extensions as a combinatorial object | Steps 1, 5, 8 | `L(P)`, width, Dilworth decomposition, indecomposability |
| C. BK graph + graph-theoretic combinatorics | Steps 1, 2, 4, 6, 7, 8 | BK graph on `L(P)`, edge boundary, conductance Φ(S) |
| D. Reversible Markov chain / Cheeger / Dirichlet form | Step 8 (Theorem E), some of Step 7 | Dirichlet form `E(f)`, variance, conductance inequality |
| E. Correlation inequalities | §intro historical context only | FKG, Ahlswede–Daykin, XYZ |
| F. Discrete / planar isoperimetry | Step 2 (weak grid stability), Step 7 | order-convex regions of `Z²`, staircase regions, edge-isoperimetric bound |

Buckets A, E, and parts of D (variance) are well-covered. B, C, the
Markov-chain pieces of D, and F are the substantive formalization work.

---

## 2. Item-by-item audit

### A. Poset foundations

| # | Object / result | Status | Location |
|---|---|---|---|
| A1 | `PartialOrder`, `Preorder`, `LinearOrder` | IN MATHLIB | `Mathlib.Order.Defs.PartialOrder` |
| A2 | Chains (`IsChain`) | IN MATHLIB | `Mathlib.Order.Chain` |
| A3 | Antichains (`IsAntichain`) | IN MATHLIB | `Mathlib.Order.Antichain` |
| A4 | Order-theoretic duals, upper/lower sets | IN MATHLIB | `Mathlib.Order.UpperLower.Basic` |
| A5 | Finite poset infrastructure, `Fintype`/`Finset` | IN MATHLIB | ambient |
| A6 | Szpilrajn / linear-extension existence | IN MATHLIB | `Mathlib.Order.Extension.Linear` (`extend_partialOrder`, `LinearExtension α`) |

**Assessment.** Enough for all day-to-day order-theoretic manipulations
the proof performs (incomparability, chains, antichains, comparability
graphs, ordinal sums as `Sum.Lex`). No gap here.

### B. Width, Dilworth, the space of linear extensions

These are the combinatorial carriers of the proof. All have significant
gaps.

| # | Object / result | Status | Notes |
|---|---|---|---|
| B1 | `w(P)` as the cardinality of a maximum antichain | NOT IN MATHLIB | No `Order.width` definition; must be built as `sSup { s.card | IsAntichain s } : ℕ` with existence in the finite case. **Difficulty: low** (a few screens of code, mostly `Finset.sup`/`Finset.sup'` glue). |
| B2 | Dilworth's theorem: `w(P) = min k, P = C₁ ⊔ ⋯ ⊔ Cₖ chain partition` | NOT IN MATHLIB | Not formalized in any form I could locate (Sperner and LYM are in `Mathlib.Combinatorics.SetFamily.LYM`, but Dilworth is absent). The proof is standard (König's theorem / bipartite matching or induction on `\|P\|`), widely taught. **Difficulty: medium.** ~2–3 weeks of work for a Mathlib-level proof; not research-grade but real combinatorial API to wrangle. This is used non-trivially in Step 5 (`step5.tex` §Setup, "`P = A ⊔ B ⊔ C`") and in the width-3 hypothesis of every step. |
| B3 | `L(P)` as a `Finset` / `Fintype` enumerating linear extensions | NOT IN MATHLIB | `extend_partialOrder` only proves *existence* of one linear extension. We need the set of all such extensions, with `Fintype` structure, cardinality `\|L(P)\|`, and the uniform probability measure on it. **Difficulty: medium.** API-heavy but straightforward: define as `{ le : LinearOrder α // ∀ x y, x ≤_P y → x ≤ y }` with `Fintype` via `Fintype.ofEquiv` from a finite subtype; then wire the uniform `Finset.sum`/`Finset.card` interface. ~1–2 weeks. |
| B4 | `Pr_L[x <_L y]` — the proof's central probability | NOT IN MATHLIB | Follows immediately from B3: `(L(P).filter (fun L => L x y)).card / L(P).card` as `ℚ` or `ℝ`. Trivial after B3. |
| B5 | Balanced-pair statement `δ(P) ≥ 1/3` | project-level | This is the conjecture itself; no prior formalization of even the problem statement. After B1–B4 it is a one-line definition. |
| B6 | Indecomposable poset (no non-trivial ordinal-sum decomposition) | NOT IN MATHLIB | `Mathlib.SetTheory.Ordinal.Principal` handles indecomposable *ordinals*, a different concept. The poset version (`P ≠ Q ⊕ R` for any non-trivial `Q, R`) needs to be stated afresh. Used in Step 8 `lem:indec-incompairs` and the Theorem-E reduction. **Difficulty: low** (definition plus the "every element has an incomparable partner" lemma — the latter has a 10-line proof, see `step8.tex:175–192`). |
| B7 | Ordinal sum `P ⊕ Q` of posets | PARTIAL | `Sum.Lex` and `Order.Lex` give the lex / ordinal sum at the type level; packaging `P ⊕ Q` for two finite posets as another finite poset, and the decomposition lemma used in B6, is a short additional step. |
| B8 | Random-linear-extension Markov chain / uniform sampling | NOT IN MATHLIB | Discrete-time Markov chain on `L(P)`. Follows from the BK graph (C4) plus `Mathlib.Probability.Kernel` infrastructure; but no reversibility/detailed-balance/spectral-gap API is in place (see §D). |

**Assessment.** B1, B2, B3 are three chunky prerequisite PRs before the
Step 1 scaffolding can even be written in Lean. Everything else in
Bucket B is short once those land. This is the single biggest cluster
of missing foundations.

### C. BK graph + graph-theoretic combinatorics

| # | Object / result | Status | Notes |
|---|---|---|---|
| C1 | `SimpleGraph` base API | IN MATHLIB | `Mathlib.Combinatorics.SimpleGraph.Basic`, `.Finite`, `.Connectivity`, … |
| C2 | `SimpleGraph.Adj`, `degree`, `edgeFinset` | IN MATHLIB | `Mathlib.Combinatorics.SimpleGraph.Finite` |
| C3 | Edge boundary `E(S, Sᶜ)` of a vertex set | PARTIAL | `SimpleGraph` has `incidenceSet`, `neighborFinset`, `deleteEdges`, but no named `edgeBoundary S : Finset (Sym2 V)` with the "one endpoint in S" convention the proof uses. **Difficulty: low** (one definition + five glue lemmas, matches existing `incidenceSet` shape). |
| C4 | The BK graph on `L(P)` | NOT IN MATHLIB | To be defined after B3: vertex set `L(P)`, edge `L ~ L'` iff they differ by an adjacent transposition of incomparable elements. **Difficulty: low–medium.** Conceptually one definition; the useful lemmas (connectivity by Bubley–Karzanov, degree bound `≤ n-1`) are straightforward. |
| C5 | Volume `vol(S) = \|S\|(n-1)` in the Dirichlet/lazy-chain normalization | NOT IN MATHLIB | Tied to C4 edge convention; a 3-line definition. |
| C6 | Conductance `Φ(S) = \|∂S\| / min(vol(S), vol(Sᶜ))` | NOT IN MATHLIB | One definition on top of C3+C5. The full `isoperimetricNumber`/`Cheeger constant` theory for finite graphs is absent from Mathlib. **Difficulty: low** once C3, C4, C5 land. |
| C7 | Connectivity of the BK graph (Bubley–Karzanov) | NOT IN MATHLIB | Used implicitly by Step 7's gradient-integration argument (`lem:potential`) — a connected weighted graph admits a potential iff its cocycle vanishes. Standard result. **Difficulty: low** for the connectivity half (induction on sorting); the potential-integration lemma is a generic graph-theoretic statement (B9 below). |

**Assessment.** C3, C4, C5, C6 are small but necessary. Nothing here is
research-depth. Roughly 2 weeks of steady API work.

### D. Reversible Markov chains, Cheeger, Dirichlet form

This is where Theorem E of Step 8 lives. The proof in Step 8 is
*self-contained* (it gives an explicit averaging argument — see
`step8.tex:206–250`), so it does not actually call a
Cheeger-inequality lemma out of a library. But the Dirichlet form
and variance are used as objects, and the normalized pair-function
Dirichlet energy bound (`E(f_{xy}) ≤ 1/2` summed over pairs) uses the
standard reversible-chain formula.

| # | Object / result | Status | Notes |
|---|---|---|---|
| D1 | `Variance` of a function on a finite probability space | IN MATHLIB | `Mathlib.Probability.Moments.Variance` (`ProbabilityTheory.variance`, `evariance`) |
| D2 | Dirichlet form `E(f) = ½ E[(f(X) − f(τX))²]` for a reversible chain | NOT IN MATHLIB | Directly: no. Indirectly: can be written as an explicit `Finset.sum` over edges once C4 is in place. **Difficulty: low** — essentially notation. |
| D3 | Cheeger inequality (`λ₂ ≤ 2Φ`, `Φ² / 2 ≤ λ₂`) | NOT IN MATHLIB | **Not needed** by Step 8 as currently written — Step 8 proves the conductance-variance inequality directly for indicators (`lem:dirichlet-conductance`, lines 114–152), which is the *easy* half of Cheeger and takes 30 lines. **Difficulty: low** for the easy half; the full Cheeger inequality is medium and would be a substantial independent contribution to Mathlib. |
| D4 | Conductance/Dirichlet inequality for indicator functions | NOT IN MATHLIB | Stated as `lem:dirichlet-conductance` in `step8.tex:114`. Short: `Φ(S) ≤ E(1_S) / Var(1_S)`. **Difficulty: low** — literally the lemma already written in Step 8; porting is ~30 lines. |
| D5 | Spectral gap / Poincaré inequality | NOT IN MATHLIB | Not used by the main theorem as written (the averaging proof of `lem:frozen-pair-existence` avoids it entirely). Listed here because the *old* version of Theorem E needed it — the F3 resolution (mg-893b) removed the dependency. |
| D6 | Reversible-chain infrastructure (detailed balance, stationary uniform measure) | PARTIAL | `Mathlib.Probability.Kernel.*` has Markov kernels and compositions, but no reversible-chain API. Again, not strictly needed for Step 8 as written. |

**Assessment.** Surprisingly light, because the F3-resolved Step 8
bypasses the heavy spectral machinery. The only load-bearing piece is
D4 (the easy conductance/Dirichlet inequality for indicators), which
is ~30 lines, plus D2 as a notational wrapper on C4. The full Cheeger
inequality (D3, D5) is **not needed**.

### E. Correlation inequalities (historical context only)

These appear in `main.tex:140–150` (history/prior-art) but are **not
used** by the Step 1–8 proof. Included for completeness.

| # | Object / result | Status |
|---|---|---|
| E1 | FKG inequality | IN MATHLIB (`Mathlib.Combinatorics.SetFamily.FourFunctions`, theorem `fkg`) |
| E2 | Ahlswede–Daykin (four functions theorem) | IN MATHLIB (same file: `four_functions_theorem`, `holley`) |
| E3 | Kahn–Saks log-concavity of rank probabilities | NOT IN MATHLIB |
| E4 | XYZ / Fishburn–Shepp inequality | NOT IN MATHLIB |

**Assessment.** The present proof's methodological novelty is precisely
that it avoids E3, E4. We do not need them formalized.

### F. Discrete / planar isoperimetry

This is the Step 2 weak grid stability lemma and its downstream
consumers in Steps 6–7.

| # | Object / result | Status | Notes |
|---|---|---|---|
| F1 | `ℤ²` as a lattice with product order | IN MATHLIB | `Mathlib.Order.Lex` etc.; ambient `ℤ × ℤ` works. |
| F2 | Order-convex subsets of `ℤ²` | PARTIAL | Generic `Set.OrdConnected` is in `Mathlib.Order.Interval.Set.OrdConnected`. Applying it to `ℤ × ℤ` is immediate but no 2D-specialized API. **Difficulty: low** as a thin specialization layer. |
| F3 | Lower sets / `IsLowerSet` | IN MATHLIB | `Mathlib.Order.UpperLower.Basic`. |
| F4 | Monotone staircase region of a 2D grid (lower set in `≤₊` or `≤₋`) | PARTIAL | `Mathlib.Combinatorics.Young.YoungDiagram` is exactly a finite lower set of `ℕ × ℕ` with substantial API: cells, row/column lengths, corners. This is very close to the "staircase" object of `step2.tex` Definition 2.1. Adapting to `[0,t]² ⊂ ℤ²` with the four orientations (`±` of each axis) is a short wrapper. **Difficulty: low.** The existing Young-diagram infrastructure is a lucky hit. |
| F5 | Grid edge boundary `∂_D A` (Definition `def:grid-bdy` in `step2.tex`) | NOT IN MATHLIB | One definition on top of F4: `{(u,v) : u ∈ A, v ∈ D\A, \|u−v\|₁ = 1}`. **Difficulty: low.** |
| F6 | Weak grid stability lemma (`\|A△M\| ≤ δ\|D\|` when `∂_D A ≤ εt`) | NOT IN MATHLIB | **This is the Step 2 core content** (`lem:weak-grid` in `step2.tex:135`) and is the first non-trivial Mathlib contribution required. The proof is currently written out in `step2.tex` across ~200 lines and is elementary (row/column cleanup + monotone rearrangement + anchor reduction). **Difficulty: medium.** Not research-deep, but 500–1000 lines of Lean, with 6–8 auxiliary lemmas (`lem:row-decomp`, `cor:most-rows-intervals`, `lem:1d-components`, etc. all enumerated in `step2.tex` §3–4). |
| F7 | Triple-overlap / Z³ cube corollary | NOT IN MATHLIB | The Step 1 Corollary 4.x feeding Step 7's cocycle lemma. Specific to this project; no generic Mathlib hook. Formalization cost is bounded by the LaTeX writeup (~4 pages in `step1.tex`). **Difficulty: medium.** |

**Assessment.** F4–F5 are light thanks to `YoungDiagram`. F6 (Step 2
weak grid stability) and F7 (triple overlap) are the two real pieces
of non-trivial combinatorial content that would have to be
formalized *before* touching the BK-dynamics arguments of Steps 3–7.

---

## 3. Core new lemmas of the program (no Mathlib shortcut)

These are specific to this proof and will not come from any external
formalization. They must be formalized alongside the rest. Estimates
are for a Mathlib-level writeup given the existing LaTeX source.

| Lemma | Source | Difficulty |
|---|---|---|
| Step 1 local interface theorem (`thm:interface`) | `step1.tex` ~1k lines | medium; requires C4, B3 |
| Step 2 weak grid stability (`lem:weak-grid`) | `step2.tex` ~200 lines of proof | medium; see F6 |
| Step 3 canonical axes / sign `η_{xy}` | `step3.tex` | low–medium |
| Step 4 two-interface incompatibility (`thm:step4`) | `step4.tex` | medium |
| Step 5 Rich/Collapse dichotomy (`thm:step5`) | `step5.tex` | medium; requires Dilworth B2 |
| Step 6 dichotomy assembly (`thm:step6`) | `step6.tex` | medium |
| **Step 7 G4 triple-overlap cocycle (`lem:cocycle`)** | `step7.tex:389` | **high** — the "core new lemma" of the program; the `summary.md` grades this as 2 weeks–2 months of genuine math depending on whether the "Expected approach" holds up. Any Lean formalization would face the same depth. |
| Step 7 potential integration (`lem:potential`) | `step7.tex:600` | medium (gradient on connected graph, standard) |
| Step 7 single global threshold (`lem:single-c`) | `step7.tex` | medium |
| Step 8 Dirichlet→conductance (`lem:dirichlet-conductance`) | `step8.tex:114` | low (~30 lines) |
| Step 8 Frozen-pair existence (`lem:frozen-pair-existence`) | `step8.tex:194` | low–medium (~80 lines, elementary averaging) |
| Step 8 Layered reduction (`lem:layered-reduction`) | `step8.tex` | medium |
| Step 8 Layered balanced pair (`lem:layered-balanced`) | `step8.tex` | medium |

---

## 4. Summary table

### Present in Mathlib and usable as-is
- Partial orders, preorders, linear orders, `IsChain`, `IsAntichain`,
  `IsLowerSet`, `IsUpperSet`, `Set.OrdConnected`, `Sum.Lex`.
- Szpilrajn linear-extension existence (one extension, not the set).
- `ProbabilityTheory.variance`, `evariance`.
- `SimpleGraph` base, `edgeFinset`, `incidenceSet`, `degree`.
- FKG inequality, Ahlswede–Daykin four-functions theorem
  (`Mathlib.Combinatorics.SetFamily.FourFunctions`) — *not needed* by
  this proof but present.
- `YoungDiagram`: finite lower sets of `ℕ²` (usable as
  staircase-region API for the 2D grid isoperimetry).

### Missing but easy (each 1–3 weeks, straightforward Mathlib contribution)
- B1 width `w(P)`.
- B3 `L(P)` as a `Fintype`.
- B4 `Pr_L[x <_L y]`.
- B6 indecomposable poset.
- C3 `SimpleGraph.edgeBoundary`.
- C4 BK graph on `L(P)`.
- C5 volume `vol(S) = \|S\|(n−1)`.
- C6 conductance `Φ(S)`.
- D2 Dirichlet form (notational).
- D4 conductance-variance indicator inequality (`lem:dirichlet-conductance`).
- F2, F4, F5 2D-grid isoperimetric scaffolding (orientation-closed
  staircase regions, grid boundary).

### Missing and medium (1–2 months each)
- B2 Dilworth's theorem (Mathlib-worthy lemma in its own right).
- F6 Step 2 weak grid stability lemma.
- F7 Step 1 triple-overlap `Z³` cube corollary.
- Steps 1, 3, 4, 5, 6 main propositions (each a few hundred lines of
  Lean after prerequisites).
- Step 7 `lem:potential`, `lem:single-c`, `prop:72`, `prop:73`.

### Missing and hard
- **Step 7 `lem:cocycle` (triple-overlap cocycle).** The core new
  combinatorial content. `summary.md` notes that the LaTeX itself has
  only a three-bullet sketch at `step7.tex:§sec:gap-cocycle`; until the
  math is actually worked out on paper, any Lean formalization is
  blocked on the mathematical writeup.

### Not needed (despite appearing in the proof's historical context)
- Cheeger inequality (`λ₂ ≤ 2Φ`). The current Step 8 bypasses it.
- Full spectral-gap / Poincaré machinery on reversible Markov chains.
- XYZ / Fishburn–Shepp, Kahn–Saks log-concavity. The methodological
  novelty is avoiding these.

---

## 5. Minimal dependency chain for a Lean formalization

A plausible PR ordering (each block depends on the blocks above):

1. **Foundations (2–3 weeks):** B1 width, B3 `L(P)` `Fintype`, B4
   `Pr_L[x <_L y]`, B6 indecomposable, C3 `edgeBoundary`, C4 BK graph,
   C5 volume, C6 conductance, D2 Dirichlet-form notation.
2. **Prerequisite theorems (1–2 months):** B2 Dilworth's theorem, D4
   conductance-variance indicator inequality, F2/F4/F5 grid
   scaffolding on top of `YoungDiagram`.
3. **Step 1 (1 month):** fiber construction, local coordinates, Step 1
   corollaries including F7 triple-overlap.
4. **Step 2 (1 month):** F6 weak grid stability, per-fiber staircase.
5. **Steps 3, 4, 5, 6 (2–3 months each, partly parallel):** coherence,
   incompatibility, richness, dichotomy assembly.
6. **Step 7 (indefinite):** blocked on the mathematical completion of
   `lem:cocycle`. Once that LaTeX writeup exists, Lean formalization is
   a 1–2 month job.
7. **Step 8 (2 weeks after Step 7):** assembly, Theorem E
   (self-contained), layered reduction / balanced pair, main theorem.

Total: a 6–12 month Lean formalization project assuming the LaTeX
proof holds up to external review (flagged concerns in `summary.md`
notwithstanding).

---

## 5a. Current Lean scaffold (2026-04-19)

The following definitions and theorem *statements* are already in the
repo (all proofs `sorry`). This audit re-categorizes them by whether
they belong to the mathlib-extraction tier (`OneThird/Mathlib/*`) or
the project-specific tier (`OneThird/StepN/*`):

| Name (scaffold) | Tier | Corresponds to |
|---|---|---|
| `OneThird.Incomp` (`Basic.lean`) | Mathlib | convenience predicate |
| `HasWidthAtMost`, `HasWidth` (`Poset.lean`) | Mathlib | B1 |
| `commonNbhd`, `commonNbhdFinset`, `commonNbhdLength` (`Poset.lean`) | project | §step1 `N(x,y)` |
| `commonNbhd_isChain_of_width3` (`Step1/CommonChain.lean`) | project | `lem:CNchain-width3` |
| `IsRich`, `richPairs` (`Poset.lean`) | project | `def:rich` |
| `LinearExt` (`LinearExtension.lean`) | Mathlib | B3 (type; `Fintype` instance is `sorry`) |
| `numLinExt`, `probLT` (`LinearExtension.lean`) | Mathlib | B3–B4 |
| `IsBalanced`, `HasBalancedPair`, `IsGammaCounterexample` (`LinearExtension.lean`) | project | B5 |
| `BKAdj`, `BKAdj.symm`/`.irrefl` (`LinearExtension.lean`) | Mathlib | C4 |
| `edgeBoundary`, `volume`, `Phi` (`LinearExtension.lean`) | Mathlib | C3+C5+C6 |
| `signMarker`, `iCoord`, `jCoord`, `localCoord` (`RichPair.lean`) | project | `def:local-coords` |
| `ExternalEquiv`, `rawFiber`, `IsGoodFiber`, `goodFiberSet`, `badSet` (`RichPair.lean`) | project | §step1 fiber defs |
| `localInterfaceTheorem` (`RichPair.lean`) | project | `thm:interface` |
| `IsChainPoset` (`MainTheorem.lean`) | Mathlib (trivial) | |
| `width3_one_third_two_thirds` (`MainTheorem.lean`) | project | `thm:main` |
| `counterexample_implies_low_BK_expansion` (`MainTheorem.lean`) | project | `thm:cex-implies-low-expansion` |

Missing entirely from the scaffold and needed downstream:

- Dilworth's theorem (B2), indecomposability (B6/B7), linear-extension
  `Fintype` proof (currently `sorry`), BK connectivity (C7),
  Dirichlet form (D2), indicator Cheeger (D4), planar grid
  infrastructure (F2/F4/F5), weak grid stability (F6), triple-overlap
  cube (F7), and essentially every lemma of Steps 1–8 beyond the
  bare statement of `thm:interface` and the main theorem.

---

## 5b. Work-item partition (filed under tag `one-third, lean`)

The Lean formalization has been partitioned into self-contained
polecat work items. Each item corresponds to a cluster of closely
related lemmas in `step1.tex`–`step8.tex`, plus (for the foundations
cluster) one mathlib-flavored module. Dependencies mirror the
mathematical dependency chain; the item IDs are not linearized in
this file — see `mg list --tag one-third --tag lean` for the current
status.

Clusters (§5b is a map, not a plan; difficulty estimates are in §2):

1. **Foundations (Mathlib tier; parallelizable):** poset width,
   Dilworth, `LinearExt` `Fintype`, indecomposability, SimpleGraph
   edge boundary, BK graph + connectivity, Dirichlet form,
   2D-grid isoperimetric scaffolding on top of `YoungDiagram`.
2. **Step 1:** common-neighbor chain, local coordinates + fiber
   structure, interface theorem, bounded interaction / commuting
   overlap / triple overlap.
3. **Step 2:** weak grid stability, per-fiber staircase, step-2
   conclusion.
4. **Step 3:** local sign + common axes, step-3 theorem.
5. **Step 4:** rectangle model + density regularization, step-4
   theorem.
6. **Step 5:** endpoint monotonicity + convex overlap, fiber mass +
   global layering, second moment, step-5 dichotomy.
7. **Step 6:** error control + commuting square + richness bound,
   step-6 assembly.
8. **Step 7:** signed threshold + sign consistency + cocycle (the
   hard lemma), potential + single threshold, step-7 assembly.
9. **Step 8:** Theorem E (Dirichlet-conductance + frozen-pair),
   G2 constants + layered reduction + layered balanced, small-$n$
   + main-theorem assembly.

---

## 6. Caveats and notes

- This audit was performed on 2026-04-19 against the Mathlib docs as
  surveyed at that time. Mathlib evolves; revisit before starting
  substantive formalization work.
- Step 7's `lem:cocycle` is, per `summary.md` and the inline
  `QA-FLAG` at `step7.tex:622,1587`, currently a proof *sketch* rather
  than a written proof. Any Lean estimate for that node assumes the
  mathematical content is filled in first.
- All "difficulty" estimates are Mathlib-relative, not research-relative.
  The research-level difficulty of the proof itself is not assessed
  here — this is a formalization scoping document.
- The Step 8 resolution of Theorem E (mg-893b, 2026-04-18) replaced a
  pair-Poincaré / rigid-spine argument (which would have required the
  full Cheeger/spectral-gap package in Mathlib) with an elementary
  averaging argument. This significantly lowers the Mathlib
  prerequisite bar: no Cheeger inequality, no spectral gap, no
  representation theory needed.
- The statement-only scaffold (merged 2026-04-19, mg-8d16 + mg-b6aa +
  mg-8196) contains one load-bearing `sorry` outside the
  mathematical lemmas: the `Fintype (LinearExt α)` instance in
  `OneThird/LinearExtension.lean` depends on a finiteness argument
  (subtype of `α ≃ Fin n` cut out by monotonicity) that is currently
  `sorry`. The foundation item for B3 (`Mathlib.LinearExtension.Fintype`)
  is responsible for discharging that first, since every downstream
  item about linear extensions manipulates `Finset (LinearExt α)`.
