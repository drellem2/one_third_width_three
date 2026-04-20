# The 1/3–2/3 conjecture for width-3 posets

This repository contains a proof of the **1/3–2/3 conjecture** of
Kislitsyn (1968), Fredman (1976), and Linial (1984) in the special
case of posets of **width at most 3**.

> **Theorem.** Let `P` be a finite poset of width `≤ 3` that is not
> a chain. Then `P` admits a pair of incomparable elements `x, y`
> with `1/3 ≤ Pr[x <_L y] ≤ 2/3`, where `L` is a uniformly random
> linear extension of `P`.

For the full statement and surrounding context, see
[`main.tex`](main.tex) (Theorem 1.1 / `thm:main`). The built PDF is
[`main.pdf`](main.pdf).

## Please read this first

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

With those caveats stated, the rest of this README describes what is
in the repository.

## What is actually here

### The mathematical proof (LaTeX / PDF)

The built paper is [`main.pdf`](main.pdf). The LaTeX source is
organized in eight steps, distributed across the files
[`step1.tex`](step1.tex) through [`step8.tex`](step8.tex), assembled
by [`main.tex`](main.tex).

1. **Step 1 — Local interface theorem** ([`step1.tex`](step1.tex)):
   for each incomparable *rich* pair `(x, y)` (sharing many common
   neighbors), linear extensions fiber over a 2-dimensional grid
   region, and Bubley–Karzanov (BK) moves within a fiber are unit
   grid moves.
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

### The Lean 4 formalization (partial)

A Lean 4 / mathlib formalization lives in [`lean/`](lean/). It is a
**structural scaffold, not a complete formalization**. The audit at
[`lean/README.md`](lean/README.md) is detailed and candid. Summary:

- `lake build` succeeds.
- **10 `sorry`s remain**, categorized there by file and kind.
- Two of the ten are genuine external dependencies (Dilworth's
  theorem for finite posets; Bubley–Karzanov connectivity) that are
  classical, accepted, and not yet in mathlib.
- Two are "base-case" prerequisites (Kahn–Linial 1991; a finite
  enumeration of small-`n` width-3 posets).
- The remaining **six are load-bearing gaps in the formalization
  itself**: Theorem E, the G4 layered-balanced lemma, the final
  assembly's `MainTheoremInputs` construction, the window-localization
  bound, `bipartiteBalanced`, and the high-level G4 disjunction
  (`lem_layered_balanced`).

Concretely: the Lean `OneThird.width3_one_third_two_thirds` has the
correct statement matching the paper's `thm:main`, but the proof
reduces via `sorry` to an abstract `MainTheoremInputs` bundle that
is never constructed. Steps 1–7 have theorem statements that
discharge their *abstract numeric* hypotheses sorry-free, but the
bridge from those abstract hypotheses to statements about an actual
finite poset `α` is not yet formalized.

**Please do not cite the Lean directory as a "machine-verified
proof."** It is best described as a work-in-progress formalization
whose *statements* are faithful to the paper but whose *proofs of
the main results are not yet complete*.

See [`lean/MATHLIB_GAPS.md`](lean/MATHLIB_GAPS.md) for a catalogue
of the mathlib coverage gaps relevant to completing the
formalization.

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
`thebibliography` environment, not BibTeX.

No `latexmk` configuration or Makefile is provided; `pdflatex`
directly on `main.tex` is the only supported workflow. A pre-built
[`main.pdf`](main.pdf) is checked in for convenience.

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

`lake exe cache get` is optional but strongly recommended — without
it, the first build compiles mathlib from source, which takes hours
instead of a few minutes.

Expected output: `lake build` succeeds with 10 `sorry` warnings and
several hundred benign linter warnings (`unusedDecidableInType`,
`unusedSectionVars`). There should be no errors. See
[`lean/README.md`](lean/README.md) for per-file details.

## Repository layout

```
main.tex                 top-level LaTeX document
main.pdf                 pre-built PDF of the paper
step1.tex … step8.tex    per-step proof files
generalization.md        where width-3 is essential, and what generalizes
lean/                    Lean 4 / mathlib formalization (partial)
.github/workflows/       CI (Lean build)
```

## How to engage with this

If you are a mathematician reading this out of curiosity or
skepticism, the most useful things you can do are:

1. Read [`main.pdf`](main.pdf) (or [`main.tex`](main.tex)) for the
   full argument.
2. Pick a step (Step 4, Step 5, or Step 7 are the load-bearing
   ones) and try to break it.
3. File issues against specific line numbers in the step files.

I am genuinely interested in being corrected. If the argument has a
hole, the goal of making this public is to find out.

## License

The mathematical writing (`*.tex`, `*.md`, `main.pdf`) is released
under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The
code (everything under `lean/` and the CI workflows) is released
under the MIT license. See [`LICENSE`](LICENSE).

## Contact

Issues and pull requests against this repository are the preferred
channel. Email is on my GitHub profile.
