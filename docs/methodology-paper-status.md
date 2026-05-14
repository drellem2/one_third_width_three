# Methodology paper — draft status (F12, mg-59d0)

**Artifact:** `docs/methodology-paper-draft.tex`
**Spine:** F10 `docs/general-n-proof-synthesis.md` §9 (mg-8216, GREEN-conditional).
**Verdict:** **AMBER-partial-draft** — all 11 sections substantive, LaTeX
compiles clean (17 pp), ready for Daniel review; polish deferred.
**Cumulative state ledger:** `docs/state-F12.md`.

## How to build

```sh
cd docs && pdflatex methodology-paper-draft.tex && pdflatex methodology-paper-draft.tex
```

Two passes (table of contents + cross-references + bibliography).
Standard TeX Live; packages: `amsart`, `amsmath`, `amssymb`, `amsthm`,
`mathtools`, `geometry`, `enumitem`, `booktabs`, `array`, `hyperref` —
all in a default TeX Live install. Verified to compile with 0 errors,
0 undefined references, 69 labels resolved (TeX Live 2019).

Build artifacts (`.aux`, `.log`, `.out`, `.toc`, `.pdf`) are
`.gitignore`d except `.pdf` — only `methodology-paper-draft.tex` is
committed (source-only convention, matching the existing LaTeX
`.gitignore` block).

## Per-section status

| § | Title | Status | Notes |
|---|-------|--------|-------|
| 1 | Introduction | **draft-complete** | the conjecture; width-2 done / width-3 open; the cohomological reformulation; 4-point contribution list; status & scope |
| 2 | Background + trust surface | **draft-complete** | PPF_n, Δ_n, S_n-action; (H-Cox)/(sgn)/(BF-Cox); the established n≤6 table; trust-surface independence from the Lean artifact; the 3 trip-wire pre-checks |
| 3 | Statement of the conditional theorem | **draft-complete** | Thm 3.1 preview; the 3-part decomposition; final form repeated as Thm 7.5 in §7.7 |
| 4 | Mechanism M1 — cofiber discrete Morse | **draft-complete** | Lemma 4.1 (downward-closed-subcomplex, with proof) + Prop 4.2 (M1-uniform); the n-uniform (proven) vs n-dependent (open beyond n=3→4) split |
| 5 | Mechanism M2 — FI rep-stability | **draft-complete** | presentation-degree-0 claim + its honest conditional content; the cofiber LES as the synthesis bridge; §5.5 n=6 Euler-term honesty note |
| 6 | ICOP framework + n-uniform reduction | **draft-complete** | ICOP definition (Def 6.1); the ι-tower (F8' multiplicativity); (ICOP-step) Hyp 6.2 |
| 7 | The proof — M1+M2+ICOP combined | **draft-complete** | §7.2 gap-free cofiber-LES diagram chase; (UCC) Hyp 7.1; Thm 7.2 (core); §7.4 M1+M2 convergence; §7.5 base case proven; §7.6 width-3 specialisation; Thm 7.5 final form (§7.7) |
| 8 | The single open gap — (FG-Cofiber) | **draft-complete** | §8.2.a–d: geometric diagonal is not a naive co-FI-module; degree-shift-aware object; (FG-Cofiber) Hyp 8.1; why CEF/Patzt-Putman is not off-the-shelf; the 3 routes; §8.3 width-3 bridge; §8.4 summary table |
| 9 | A documented obstruction — Plan-H | **draft-complete** | the direct constructive route; closes the inductive step at n=5,6; Findings A (super-polynomial count) + B (near-diagonal degrades) at n=7; the lesson for the framework |
| 10 | Empirical anchor — n=3,4,5,6 | **draft-complete** | m_sgn=1 throughout; (UCC) proven n=3→4; 16/16 ICOP per-step BFT-sharp; the n=6 DP-deferred Euler-term honesty note; cross-mechanism consistency |
| 11 | References | **draft-complete** | 12-item literature list (Kahn–Saks, BFT, Linial, Forman, Kozlov, CEF, CEFN, Ramos, Putman, Patzt, Sundaram–Wachs, Quillen) |
| A | Lean formalisation roadmap | **draft-complete** | L0–L3 staged; recommend no port pre-(UCC); independence of the in-tree Lean artifact restated |

**Nothing is stubbed.** Every section has substantive mathematical
content drawn verbatim-faithfully from the F-series in-tree docs. The
AMBER verdict is about *polish*, not *coverage* — see below.

## What is draft-complete vs what remains

**Draft-complete (the substance):**
- The full logical spine: conditional theorem → (UCC) → (FG-Cofiber),
  with the §6.2 diagram chase written out in full.
- The two-mechanisms-one-crux structure (M1, M2, their convergence).
- The documented obstruction (§9) — why the direct route fails.
- The empirical anchor with all honesty notes (n=6 Euler term).
- Compiles clean.

**Remains (polish, deferred — see `state-F12.md` "Optional Session 2"):**
- **Figures.** Three would help: the cofiber pair Δ_n ⊂ Δ_{n+1}; the
  cofiber LES diagram; a two-mechanisms-one-crux schematic. The draft
  is currently all prose + tables.
- **§9 verbatim table.** The F9 Session-2 §0.2 headline table
  (n=5/6/7 quantities, ψ-coefficient sets, anomaly counts) could be
  reproduced verbatim rather than summarised.
- **§7.3 lineage.** The width-3 reduction (step 1 of the F8 skeleton)
  is stated at the level F8 left it; the F4 five-obstruction-map
  lineage could be spelled out.
- **Front matter.** Author block, MSC codes (06A07 / 55U10 / 20C30),
  acknowledgements are placeholder.
- **Exposition pass.** Not yet read end-to-end by a mathematician for
  flow; that is what Daniel review is for.

None of the "remains" items are load-bearing or change the
mathematics; they are editorial.

## Venue thoughts

The paper is, per Daniel's 2026-05-13 directive, intended to be
publication-class *even with partial results* — its value is the
**complete reduction** of a conjecture open since 1984 to a single
precisely-stated representation-stability crux, plus the
two-mechanisms-converge structure. Candidate venues, in rough order of
fit:

1. **Combinatorial-topology / algebraic-combinatorics specialist
   journals** — *Journal of Combinatorial Theory Series A*, *Order*
   (the journal where Kahn–Saks and BFT both appeared — natural home,
   strong topical fit), *Electronic Journal of Combinatorics*. The
   cohomological-framework angle and the explicit reduction make this
   a good fit for *Order* in particular.
2. **Representation-stability-aware venues** — if the (FG-Cofiber)
   framing is foregrounded, a venue whose readership includes the
   FI-module community (*Algebraic & Geometric Topology*,
   *Journal of Topology*) would value the "correct degree-shift-aware
   object" sharpening (§7.2) as a contribution in its own right.
3. **Survey/methodology framing** — if positioned as a methodology
   paper (the framework + the documented obstruction + the open
   problem), a survey-friendly venue or an extended preprint
   (arXiv first, then a journal) suits the "two mechanisms, one crux"
   narrative.

**Recommendation:** arXiv preprint first (math.CO + math.AT
cross-list), targeting *Order* or *JCTA* for the journal version.
The documented obstruction (§9) and the precise open-problem statement
(§8) are genuine contributions that survive regardless of whether
(FG-Cofiber) is later closed; if F11 (mg-b352) does close it before
submission, the localized revision (see `state-F12.md` F11
coordination note) upgrades the core from conditional to unconditional
and the venue calculus shifts upward accordingly.

## Coordination

- **Independent of F11 (mg-b352).** F11 attacks (FG-Cofiber); F12 is
  this write-up. If F11 closes (FG-Cofiber), §7–§8 upgrade
  conditional→unconditional — a localized revision (abstract, §1.3, §3,
  §7.7, §8.1–§8.2), not a rewrite. See `state-F12.md`.
- No new axioms, no Lean changes, no new computation were introduced
  (mg-59d0 constraints).
