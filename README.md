# The 1/3–2/3 conjecture for width-3 posets

> **Theorem.** Let `P` be a finite poset of width `≤ 3` that is not
> a chain. Then `P` admits a pair of incomparable elements `x, y`
> with `1/3 ≤ Pr[x <_L y] ≤ 2/3`, where `L` is a uniformly random
> linear extension of `P`.

The Lean formalization in [`lean/`](lean/) proves this **modulo a
documented case-3 residual hypothesis** (`hC3 : Step8.Case3Witness`)
and one named axiom transcribing a published external bound; see
[`docs/lean-forum-publication-readiness.md`](docs/lean-forum-publication-readiness.md)
for the side-by-side reading and the build-and-verify instructions.

**📄 Paper (PDF):** **[`main.pdf`](main.pdf)** &nbsp;·&nbsp;
**2-page summary:** [`summary.pdf`](summary.pdf) &nbsp;·&nbsp;
**LaTeX source:** [`main.tex`](main.tex) (Theorem 1.1 / `thm:main`) &nbsp;·&nbsp;
**Lean 4 formalization:** [`lean/`](lean/) &nbsp;·&nbsp;
**Contact:** [d.miller@hey.com](mailto:d.miller@hey.com)

[![Lean build](https://github.com/drellem2/one_third_width_three/actions/workflows/lean.yml/badge.svg)](https://github.com/drellem2/one_third_width_three/actions/workflows/lean.yml)
![Release](https://img.shields.io/badge/release-v0.1--candidate-yellow)
![License](https://img.shields.io/badge/paper-CC%20BY%204.0-blue)
![License](https://img.shields.io/badge/code-MIT-blue)

## Summary

The **1/3–2/3 conjecture** of Kislitsyn (1968), Fredman (1976), and
Linial (1984) asks whether every finite non-chain poset contains an
incomparable pair `(x, y)` whose linear-extension probability
`Pr[x <_L y]` is bounded strictly between 1/3 and 2/3. The best
unconditional constant in place of 1/3 is currently
`δ* ≥ 0.2764…` (Kahn–Linial), and the sharp 1/3 bound is known for
width 2, semiorders, and 2-dimensional posets. This repository
contains a proof of the **full width-3 case**. The argument departs
from the correlation-inequality tradition: it operates on the
**Bubley–Karzanov (BK) random walk** on linear extensions and shows,
via a Cheeger-type dichotomy, that a width-3 counterexample would
force a low-conductance cut that a **2-dimensional interface
geometry** forbids. The width-3 hypothesis enters through that
2D fiber picture and a three-chain Dilworth dichotomy; extending
beyond width 3 requires genuinely new ingredients. This is a
**proof candidate**: it has not yet been refereed or read end-to-end
by an external expert — see the "Please read this before citing"
section below.

## What to read first

Different readers want different entry points.

- **Skeptical mathematician** — open [`main.pdf`](main.pdf), read §1
  for the overview and statement, then go directly to
  [`step7.tex`](step7.tex) (coherence ⇒ collapse), the single most
  load-bearing step. Step 4 and Step 5 are the other two places the
  argument could plausibly break.
- **Curious non-specialist** — read the Summary above, then the
  [`summary.pdf`](summary.pdf) 2-page overview for the two key proof
  ideas (BK conductance + 2D local geometry), skim the one-line step
  summaries under "The mathematical proof" below, and then read
  [`generalization.md`](generalization.md) for an honest account of
  where the argument is specifically width-3 and what would (and
  would not) carry over.
- **Lean / formal-methods reader** — go straight to
  [`lean/README.md`](lean/README.md). Build status, exact `sorry`
  inventory, and per-file audit live there. For the publication-
  readiness companion (Lean vs paper headline side-by-side, the
  `hC3 : Step8.Case3Witness` residual hypothesis, `#print axioms`
  baseline, and the `brightwell_sharp_centred` axiom rationale),
  see [`docs/lean-forum-publication-readiness.md`](docs/lean-forum-publication-readiness.md).
- **"Is this for real?" reader** — read the disclosures in
  "Please read this before citing" immediately below. The short
  version: the author is unaffiliated, the work was written with
  substantial AI assistance, and no external referee has signed
  off yet.

## Please read this before citing

This README is deliberately candid about what this repository is and
is not. Before citing, extending, or formalizing anything here, you
should know:

- **Author.** The work was undertaken by an unaffiliated individual
  without a formal background in combinatorics or order theory. I am
  not a research mathematician and have no institutional affiliation.
  I am releasing this publicly so that people with the relevant
  expertise can read it, criticize it, and decide whether it holds
  up.
- **AI assistance.** The LaTeX proof and the Lean formalization were
  developed with substantial assistance from Anthropic's Claude
  (Claude Code / Claude Opus and Sonnet 4.x family models), used
  interactively across many sessions, including in a multi-agent
  orchestration setup that parallelized audits, gap-filling, and
  Lean scaffolding. Claude produced drafts of proof steps, Lean
  files, audits, and this README. I directed, reviewed, edited, and
  am responsible for the final content; but the contribution of AI
  to the writing and structuring of the argument is substantial and
  I am not hiding that. If you consider AI-assisted mathematics a
  categorical disqualifier, you should stop here.
- **No external review yet.** As of this writing, the proof has not
  been refereed, read end-to-end by any external expert, or
  submitted to a journal. External review is the next step, not a
  finished gate.
- **Lean residuals.** The Lean formalization's headline theorem
  `OneThird.width3_one_third_two_thirds`
  ([`lean/OneThird/MainTheorem.lean`](lean/OneThird/MainTheorem.lean))
  carries one Prop-level hypothesis `hC3 : Step8.Case3Witness` —
  the universally-quantified discharge of the within-band antichain
  Case 3 of the paper's `prop:in-situ-balanced` — and depends, via
  the Step 8 assembly, on one named project axiom
  `OneThird.LinearExt.brightwell_sharp_centred`, transcribing the
  combined Brightwell 1999 §4 + Kahn–Saks 1984 Lemma 2.2 sharp
  centred bound (a peer-reviewed published external result). The
  `hC3` hypothesis is parked open math: closing it requires
  compound-automorphism infrastructure (~300–500 LoC) that does not
  exist in the tree, per pm-onethird's option (δ) park decision
  (2026-04-27); the audit trail is in
  [`docs/path-c-cleanup-roadmap.md`](docs/path-c-cleanup-roadmap.md).
  The Brightwell axiom is retained per `mg-b699` decision, with a
  documented replacement path in [`lean/AXIOMS.md`](lean/AXIOMS.md).
  The full side-by-side reading and the verification recipe is in
  [`docs/lean-forum-publication-readiness.md`](docs/lean-forum-publication-readiness.md).
- **Known in-tree issue: mg-27c2 `Case2FKGSubClaim` direction was
  reversed.** A 3-element counterexample (polecat `pc-a79e`, commit
  `64f2d87`,
  [`docs/a8-path-b-block-and-report-status.md`](docs/a8-path-b-block-and-report-status.md))
  shows that mg-27c2's `Case2FKGSubClaim` (a hypothesis structure
  used by the Case 2 within-band ⪯-chain dispatch in
  `lean/OneThird/Step8/Case2Rotation.lean`) is **provably false**
  on natural Case 2 inputs: the SubClaim's `pair` field asserts
  `1/2 ≤ probLT a a'` but the counterexample (`α = {a, a', y}`,
  `a' < y`, `K = 2`, `w = 1`) gives `probLT a a' = 1/3`. The
  conditional theorems `case2Witness_balanced_under_FKG` and
  `strictCase2Witness_m2_balanced` predicated on this SubClaim are
  technically-correct-but-vacuous implications on a false antecedent;
  the headline `width3_one_third_two_thirds` is **unaffected** —
  it consumes `hC3` rather than `Case2FKGSubClaim` and the
  `#print axioms` baseline is current. The fix (η₄, `mg-b0de`) is
  in flight: restate the SubClaim with the correct direction
  (`probLT a a' ≤ 1/2`, equivalent to chain swap and already a
  theorem) and combine with a separate `≤ 2/3` upper bound from
  Brightwell covariance. See
  [`docs/lean-forum-publication-readiness.md`](docs/lean-forum-publication-readiness.md)
  §5 "Known in-tree issue" for the full disclosure.

## The mathematical proof (LaTeX / PDF)

The built paper is [`main.pdf`](main.pdf). The LaTeX source is
organized in eight steps across
[`step1.tex`](step1.tex)–[`step8.tex`](step8.tex), assembled by
[`main.tex`](main.tex).

1. **Step 1 — Local interface theorem** ([`step1.tex`](step1.tex)):
   for each incomparable *rich* pair `(x, y)` (sharing many common
   neighbors), linear extensions fiber over a 2-dimensional grid
   region, and Bubley–Karzanov moves within a fiber are unit grid
   moves.
2. **Step 2 — Weak grid stability** ([`step2.tex`](step2.tex)):
   a subset of a grid with small edge boundary is close to a
   monotone staircase; applied fiberwise.
3. **Step 3 — Coherence of interfaces** ([`step3.tex`](step3.tex)):
   canonical sign and axis on each rich pair.
4. **Step 4 — Two-interface incompatibility**
   ([`step4.tex`](step4.tex)): two incoherent rich interfaces force
   many BK-boundary crossings.
5. **Step 5 — Richness** ([`step5.tex`](step5.tex)): a width-3
   counterexample has enough rich interfaces.
6. **Step 6 — Dichotomy** ([`step6.tex`](step6.tex)): either many
   rich interfaces are incoherent (immediate contradiction) or
   almost all are coherent.
7. **Step 7 — Coherence ⇒ collapse** ([`step7.tex`](step7.tex)): in
   the coherent branch `P` admits a global axis, forcing a layered
   1-dimensional form.
8. **Step 8 — Conclusion** ([`step8.tex`](step8.tex)): packages
   Theorem E (counterexample ⇒ low BK-expansion), the parameter
   cascade, and a small-`n` base case (Linial + Kahn–Linial +
   explicit finite enumeration) into a contradiction.

A discussion of what the argument does and does not generalize to is
at [`generalization.md`](generalization.md).

## The Lean 4 formalization

A Lean 4 / mathlib formalization lives in [`lean/`](lean/). See
[`lean/README.md`](lean/README.md) for the full per-file audit. The
status is:

- `lake build` succeeds (1334 jobs, clean).
- **Every paper theorem statement has a Lean counterpart.** Steps 1–7
  and the Step 8 spine — including Dilworth's theorem and the finite
  bipartite enumeration (`bipartite_balanced_enum`) — compile
  `sorry`- and axiom-free.
- **One declaration still carries `sorry`:** the G4 reduction glue
  `lem_layered_balanced` at `OneThird/Step8/LayeredBalanced.lean`,
  whose two `sorry` tokens (Case `K = 1` antichain symmetry and
  Case `K ≥ 2` sub-poset restriction) implement the paper's
  reduction from an arbitrary non-chain layered width-3 poset to
  the bipartite case that `bipartite_balanced_enum` discharges
  (`step8.tex:1760-1796`). Both are scaffolding glue, not
  foundation items; the heavy machinery they feed into is
  `sorry`-free.

`#print axioms OneThird.width3_one_third_two_thirds` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; closing
`lem_layered_balanced` would drop `sorryAx` and leave only
the mathlib-standard classical foundations.

See [`lean/README.md`](lean/README.md) for the per-file audit and
[`lean/MATHLIB_GAPS.md`](lean/MATHLIB_GAPS.md) for a catalogue of the
mathlib coverage gaps relevant to completing the formalization.

## Building

### LaTeX

The LaTeX source uses standard AMS packages (`amsmath`, `amsthm`,
`amssymb`, `enumitem`, `geometry`, `hyperref`). Any recent TeX Live
or MacTeX distribution should be sufficient.

```sh
# from the repository root
pdflatex main.tex
pdflatex main.tex   # run twice so the TOC and \ref cross-references resolve
```

There is no bibliography processing step: `main.tex` uses an inline
`thebibliography` environment, not BibTeX. No `latexmk` configuration
or Makefile is provided; `pdflatex` directly on `main.tex` is the
only supported workflow. A pre-built [`main.pdf`](main.pdf) is
checked in for convenience.

### Lean 4

The Lean project lives under [`lean/`](lean/). It requires
[`elan`](https://github.com/leanprover/elan) — the Lean toolchain
manager — which will install the matching Lean version
(`leanprover/lean4:v4.29.1`, pinned in `lean/lean-toolchain`) on
first use.

```sh
cd lean
lake exe cache get   # fetch prebuilt mathlib .olean cache (strongly recommended)
lake build
```

`lake exe cache get` is strongly recommended — without it, the first
build compiles mathlib from source, which takes hours instead of a
few minutes.

Expected output: `lake build` succeeds with a single `sorry`
warning (from `lem_layered_balanced`) and several hundred benign
linter warnings (`unusedDecidableInType`, `unusedSectionVars`).
There should be no errors.

## Repository layout

```
main.tex                 top-level LaTeX document
main.pdf                 pre-built PDF of the paper
step1.tex … step8.tex    per-step proof files
summary.tex              2-page intuitive summary (source)
summary.pdf              2-page intuitive summary (pre-built PDF)
generalization.md        where width-3 is essential, and what generalizes
lean/                    Lean 4 / mathlib formalization
.github/workflows/       CI (Lean build)
LICENSE                  dual license: CC BY 4.0 (writing) + MIT (code)
```

## How to engage with this

If you are a mathematician reading this out of curiosity or
skepticism, the most useful things you can do are:

1. Read [`main.pdf`](main.pdf) (or [`main.tex`](main.tex)) for the
   full argument.
2. Pick a step — **Step 4, Step 5, or Step 7** are the load-bearing
   ones — and try to break it.
3. File an issue against specific line numbers in the step files, or
   open a pull request if you have a fix or reformulation.

I am genuinely interested in being corrected. If the argument has a
hole, the point of making this public is to find out.

## License

Dual-licensed:

- **Mathematical writing** (`*.tex`, `*.md`, `main.pdf`) —
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
- **Code** (everything under `lean/` and the CI workflows) — MIT.

See [`LICENSE`](LICENSE) for the full text.

## Contact

- **Email:** [d.miller@hey.com](mailto:d.miller@hey.com)
- **Issues and pull requests** on this repository are also welcome
  and are the preferred channel for anything proof-specific (so the
  discussion is public and line-number-anchored).
