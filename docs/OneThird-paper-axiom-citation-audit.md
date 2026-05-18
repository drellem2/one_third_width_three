## OneThird R2 large-α paper-axiom citation audit (mg-4582)

**Owner.** `mg-4582` — independent senior audit per Daniel directive
2026-05-18T10:03Z (Zulip-prep). Analog of Frankl `mg-ee54` for the
OneThird side. Gates `mg-234e` Option-D-narrow-execution dispatch.

**Default stance.** Skeptical verifier, NOT defender. Audits the
*proposed* R2 large-α paper-axiom against (a) what the paper actually
proves, (b) what an independent mathlib-reviewer would notice on
Zulip, and (c) `#print axioms` readiness for the headline.

**Daniel's two Zulip-prep bars (10:03Z):**
> "Make sure `#print axioms` is teed up for me. The big thing I'm
> worried about is the new axiom being incorrect or unproven, so a
> very clear literature citation etc would be nice."

This audit checks both bars, applies the cumulative-vacuity-discovery
skepticism pattern (mg-5c32 over-constraint → mg-74d2 conflation →
mg-2970 discharge-coverage → mg-ee54 Frankl-in-disguise), and verifies
each phase before tagging a verdict.

---

## §0. Top-of-page verdict: **GREEN-with-conditions**

The R2 large-α paper-axiom (existence of layered decomposition with
`L.w ≤ 4` on width-3 non-chain `α` with `|α| ≥ 11`) is **mathematically
supported by the paper's Steps 1–7 + `prop:72` + `rem:w0-constant`
cascade**, BUT the axiom as proposed in
`docs/width3-residual-statement.md` §2.1 (`R2_exists_bounded_bandwidth`
restricted to `|α| ≥ 11`) **cannot be landed verbatim** without the
revisions listed in §6 below.

The seven required revisions (analog of the `mg-ee54` 7-revision list
for the Frankl side):

1. **Honest self-citation framing.** The "literature citation" is
   D. Miller, *The 1/3–2/3 Conjecture for Width-3 Posets* (in
   preparation; THIS repository — see `main.tex`). It is **not** a
   peer-reviewed external paper. Contrast with
   `LinearExt.brightwell_sharp_centred` which cites Brightwell
   (Discrete Mathematics 201, 1999) and Kahn–Saks (Order 1, 1984)
   — both peer-reviewed. The docstring + `AXIOMS.md` entry must
   state "in preparation, manuscript by the author" explicitly so
   no Zulip reader is misled into thinking the axiom rests on an
   external published result.

2. **Form mismatch disclosure.** The paper's actual deliverable
   (`step8.tex:2054–2088` `lem:layered-from-step7`(ii)) is layered
   decomposition on `P|_{X ∖ X^exc}`, **not on α**. The promotion
   from `X ∖ X^exc` to `α` is a Lean-side packaging that bundles
   `lem:exc-perturb` (F6b). State this in the docstring; do not
   pretend the axiom mirrors a single paper theorem.

3. **Constant pinning disclosure.** `w ≤ 4` is a Lean-side alignment
   choice to the F5a Bool certificate's coverage `w ∈ {1,…,4}`, not
   a paper-proven bound. The paper (`step7.tex:1193–1219`
   `rem:w0-constant`) explicitly says
   > "the present scope's natural alignment point is 4. A larger
   > absolute cap (≤ 6, ≤ 10) would close as well, conditional on
   > extending the F5a certificate to the wider w range."
   I.e. `w₀(γ) = K(T(γ)) + O(1)` with `K(T) = O_T(1)`; the paper
   has not computed `K(T(γ))` to show `≤ 2` (so `K + 2 ≤ 4`).

4. **`#print axioms` wiring.** Append the new axiom to
   `lean/scripts/PrintAxiomsAudit.lean` so the post-landing audit
   output explicitly names it. Today's audit script (7 lines) prints
   `width3_one_third_two_thirds` headline axioms and intermediates
   but has no entry for any future `R2_large` axiom.

5. **AXIOMS.md scope-match checklist.** Add a section analog to the
   existing `brightwell_sharp_centred` entry (`lean/AXIOMS.md:21–`
   …, ~150 lines): paper file/line for every hypothesis, scope-match
   table, discrepancy audit, certification with
   `#print axioms <axiom>_rat`–style verification.

6. **Encapsulation transparency.** Document explicitly that the R2
   large-α axiom **encapsulates four paper-side claims**, not one:
   (i) the Steps 1–7 cascade (`prop:71` + `prop:72`); (ii) the
   exceptional-set perturbation `lem:exc-perturb` (`step8.tex:679–
   737`); (iii) Lean-side promotion of `L` from `X ∖ X^exc` to `α`
   preserving `L.w ≤ 4`; (iv) constant pinning to F5a-aligned
   `w ≤ 4` (per `rem:w0-constant`).

7. **Naming.** Use a name that signals the encapsulation — e.g.
   `step7_layered_decomposition_w4_axiom` or
   `prop72_w4_aligned_layered_axiom` — NOT a generic name like
   `R2_large_axiom` that hides the cascade-internal nature.

**If the seven revisions land**, the axiom is cleanly Zulip-defensible
as a paper-axiomatised packaging of the in-preparation manuscript's
Steps 1–7 + `prop:72` + `rem:w0-constant` cascade, pending faithful
Lean delivery (which is the multi-month Option-A residual per
`mg-0cbf` §5 and `mg-74d2` §2c).

**If any revision is skipped**, expect a Zulip objection within the
first 24 h of public posting. The most likely objection vectors are
listed in §5 below.

---

## §1. Phase A — R2 large-α paper-axiom rigor

### §1.1 — Paper chain delivering R2 large-α

The "R2 large-α" obligation as stated in
`docs/width3-residual-statement.md` §5.1 is

```lean
def R2_large.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α →
    11 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4
```

The paper-side chain that *would* deliver this (via Daniel's manuscript
in this repository) is, in order:

1. **Step 5 dichotomy** (`step5.tex` Theorem 5.1; restated in
   `step8.tex:609–699` `prop:step5`). Every width-3 finite poset
   either satisfies *richness* (case R) or *collapse* (case C: layered
   on `X ∖ X^exc` with `|X^exc| ≤ c_1(T)` and interaction width
   `w_coll(T)`). The two cases are complements; the case analysis
   exhausts all width-3 posets (`step8.tex:702–712`).

2. **Step 6 dichotomy** (`step8.tex:781–784`, `prop:step6`). In case R,
   the rich-overlap mass is at most `δ₀`-incoherent, so at least
   `1 − δ₀` of rich-overlap mass is *coherent*.

3. **Step 7(i) cut closeness** (`step7.tex` §sec:formal `prop:71`,
   `step7.tex:1112–1170`). Under coherence (Step 6), the cut `S`
   agrees with `{H ≥ c}` up to `o(1)` mass for an explicit potential
   `H` and threshold `c`.

4. **Step 7(ii) layered globalization — `prop:72`** (`step7.tex:1172–
   1190`). A low-conductance cut of the form `{H ≥ c}` implies
   `P` admits a layered width-3 decomposition on `(1 − o(1))` of its
   mass.

5. **Ground-set lift `lem:layered-from-step7`** (`step8.tex:2009–2089`).
   Promotes Step 7(ii)'s "on `(1 − o(1))` of mass" claim to an *exact*
   layered decomposition of `P|_{X ∖ X^exc}` with interaction width
   `w = K_bw + 2` (where `K_bw = K(T) = O_T(1)` is the constant of
   `lem:bandwidth`, `step7.tex:1015–1053`) and `|X^exc| ≤ 3·c_1(T) =
   O_T(1)`.

6. **`rem:w0-constant`** (`step7.tex:1193–1219`). Sets
   `w₀(γ) := K(T(γ)) + O(1)` as the absolute bandwidth constant.
   The "≤ 4" alignment with the F5a Lean certificate is **explicitly
   acknowledged as a Lean-side scope choice**, not a paper-proven
   numerical bound.

7. **`lem:exc-perturb`** (`step8.tex:679–737`,
   `eq:exc-perturb`). Pairwise probability perturbation bound
   `|p_xy(P) − p_xy(P|_{X∖X^exc})| ≤ 2k/(n − k + 1)` for deleting
   an exceptional set of size `k`. Used by the Step 8 main assembly
   to lift balanced-pair conclusions from `X ∖ X^exc` back to `α`.

### §1.2 — Where the paper chain falls short of R2_large's signature

The paper chain (Steps 1–7 + `lem:layered-from-step7`) delivers, for a
width-3 γ-counterexample with `|α| ≥ n_0(γ, T)`:

> ∃ `X^exc ⊆ α` with `|X^exc| ≤ 3·c_1(T) = O_T(1)`, and a layered
> decomposition `L` *on `α ∖ X^exc`* with `L.w = K_bw + 2 = O_T(1)`.

Three gaps to the proposed R2_large signature:

| Gap | Paper delivers | R2_large asserts |
|---|---|---|
| (G1) Domain | `L` on `α ∖ X^exc` | `L` on **α** |
| (G2) Bandwidth value | `L.w = K_bw + 2 = O_T(1)` (asymptotic) | `L.w ≤ 4` (specific numeral) |
| (G3) Quantification | only for γ-counterexamples with `|α| ≥ n_0(γ, T)` | for **every** width-3 non-chain α with `|α| ≥ 11` |

**Each gap is closable on paper but requires non-trivial additional work
beyond `prop:72` + `rem:w0-constant`:**

* **G1 (domain promotion).** Extend `L` from `α ∖ X^exc` to `α` by
  appending the `≤ O_T(1)` exceptional elements as additional bands.
  This preserves `L.w` if the exceptional elements can be placed at
  positions where their cross-band comparabilities respect `(L2-forced)`
  / `(L2-upward)`. Not automatic — requires the exceptional elements
  to be "well-aligned" in the chain potential. The paper does NOT do
  this construction; it operates on `X ∖ X^exc` and uses `lem:exc-perturb`
  to transfer pair probabilities. The Lean-side promotion of L itself
  is an additional step.

* **G2 (constant pinning).** `rem:w0-constant` explicitly defers the
  "`≤ 4`" choice to the Lean F5a certificate scope. The paper does
  not compute `K(T(γ))` to bound it numerically. So `R2_large` with
  `L.w ≤ 4` is a strictly stronger claim than `prop:72` alone, in
  the sense that the paper would not, in its current form, justify
  the specific number 4 (only some O_T(1) constant).

* **G3 (quantification).** The Steps 1–7 cascade enters under the
  cascade-by-contradiction hypothesis ("assume `P` is a width-3
  γ-counterexample with `|P| ≥ n_0(γ, T)`"). Promoting to a universal
  "for every width-3 non-chain α with `|α| ≥ 11`" requires either:
  (a) running the cascade for arbitrary α (the dichotomy still
  applies but the exit condition changes — Case (R) → coherence →
  layered; Case (C) → layered directly), OR
  (b) treating the R2_large statement as a structural claim about
  α that is proved by the cascade-internal `prop:72` plus the
  promotion step in (G1).

**Audit verdict on §1.2.** All three gaps are bridgeable via
established paper machinery, but the proposed R2_large signature
*does not exactly mirror* any single paper statement. It is a
**Lean-side packaging** of (a) `prop:72` + (b) the L-promotion to α
+ (c) the constant `≤ 4` alignment + (d) the universal quantification
shift. This packaging is mathematically defensible but requires
explicit docstring + `AXIOMS.md` disclosure (revision #6 in §0).

### §1.3 — Verification of paper-side rigor (Steps 1–7 + prop:72)

For the **Phase A core question** ("is the paper-side argument
rigorously proved, no hidden assumptions, no hand-waving?"): yes,
modulo five caveats that the audit found.

| Paper component | Verified location | Audit note |
|---|---|---|
| `prop:71` (coherence globalization) | `step7.tex:1112–1170` proof: G1+G2+G3+G4+G9+G5+G6 chain | Proof is a chain of 7 named gap lemmas (`lem:signed-threshold`, `lem:sign-consistency`, `lem:triple-visibility`, `lem:cocycle`, `lem:potential`, `lem:single-c`). Each lemma is fully written in `step7.tex`. **Caveat 1:** the proof of `lem:potential` (`step7.tex` §sec:potential) is moderately substantive (integration along BFS spanning tree + star-triangulation through basepoint); this is the densest paper section and deserves an independent reader audit. Not done in this polecat session — flagged as follow-on. |
| `prop:72` (low-cond cut ⇒ 1D) | `step7.tex:1180–1190` proof | Proof is 11 lines. Cites `lem:bandwidth` (just above) and §sec:layered structural lemma. **Caveat 2:** the "width-3 structural lemma" mentioned in `step7.tex:1186` is not labelled in `step7.tex` — search `width-3 structural` returns no formal lemma label. This is a **paper-cleanup gap**: `prop:72`'s proof cites an unlabelled lemma. |
| `lem:bandwidth` | `step7.tex:1015–1053` proof | Proof is 38 lines. Uses `eq:var-budget`, richness threshold T, two-step Markov + chain-position bandwidth argument. The constant `K = N_B(c₀) = O_T(1/c₀)` is given as an asymptotic; **the proof does NOT exhibit an explicit numerical value of K(T)**. This is the source of (G2) above — `K + 2 ≤ 4` cannot be deduced from `lem:bandwidth` as written. |
| `lem:layered-from-step7` | `step8.tex:2009–2089` proof | Proof is ~250 lines (branches (a) Step-5 input and (b) Step-7 input). Treats branch (b) in detail. **Caveat 3:** the bound `\|X^{exc}\| ≤ C_{exc}(T) := 3·c_1(T)` cites `lem:endpoint-mono` (`step5.tex`); we did not verify `c_1(T)` is also `O_T(1)` independent of γ. (The paper says yes; not independently verified in this audit.) |
| `lem:exc-perturb` | `step8.tex:679–737` proof | Cited in §1.1 step 7. **Caveat 4:** the proof reduces to iterated single-element-deletion coupling; the per-step bound `2/(n−k+1)` is standard but the multiplicative chain `\|p_xy(P_0) − p_xy(P_k)\| ≤ Σ 2/(n − i + 1)` is what's actually written. The geometric-sum simplification `≤ 2k/(n − k + 1)` requires care; we accept the paper's stated form. |
| `rem:w0-constant` | `step7.tex:1193–1219` | This is a **remark**, not a theorem. Its content is the Lean alignment narrative + an explicit caveat that `w ≤ 4` is conditional on F5a F5a Bool certificate coverage. **Caveat 5:** A Zulip reader will read `rem:w0-constant` and immediately notice the "alignment point" / "conditional on extending the F5a certificate" qualifications. The axiom docstring must NOT obscure this — the constant `≤ 4` is justified by Lean-side scope, not by paper-side proof. |

**Audit verdict on §1.3.** The paper-side rigor of Steps 1–7 + `prop:72`
is **adequate** for axiomatising R2 large-α, modulo the five caveats
above. No hidden assumptions in the paper-side argument were found;
the chain is fully written out (~1000 lines of TeX across
`step7.tex` + relevant `step8.tex` sections). The caveats are
documentation issues, not math-content issues — they affect what the
axiom docstring needs to say, not whether the paper-side argument is
sound.

### §1.4 — Load-bearing theorem/proposition for R2 large-α

The single load-bearing paper claim for R2 large-α is:

**`prop:72`** (`step7.tex:1172–1190`):
> "If a cut of the form `{H ≥ c}` has low BK conductance and controls
> `(1 − o(1))` of all rich swaps, then `P` admits a layered width-3
> decomposition on `(1 − o(1))` of its mass."

with the constant aligned per `rem:w0-constant`:

**`rem:w0-constant`** (`step7.tex:1193–1219`):
> "the present scope's natural alignment point is 4 …"

and the ground-set lift via:

**`lem:layered-from-step7`** (`step8.tex:2009–2089`):
> "`P|_{X ∖ X^exc}` admits an exact layered decomposition with depth
> `K ≥ |X|/6` and interaction width `w = K_bw + 2`."

Together these three (not just `prop:72` alone) constitute the
load-bearing paper claim for the R2 large-α axiom.

---

## §2. Phase B — Literature citation rigor

### §2.1 — The paper itself

**Title.** *The 1/3–2/3 Conjecture for Width-3 Posets*

**Author.** D. Miller (Correspondence: `d.miller@hey.com`)
[`main.tex:86–87`]

**Date.** `\today` — the manuscript carries no fixed date. Per the
arXiv submission metadata in `main.tex:1–14`, the paper is **prepared
for arXiv submission** but is not yet on arXiv (no `arXiv:NNNN.NNNNN`
identifier exists, no `arxiv.org` URL appears in the repository).

**Publication status.** **Unpublished, in preparation.** No
peer-review record. No DOI. No conference proceedings. The
manuscript lives in this repository as `main.tex`, `step1.tex`,
…, `step8.tex` (8 step files, totalling ~5000 LaTeX lines, ~140
pages compiled).

**MSC 2020.** 06A07 (primary), 05C48, 05A20, 60J10, 60C05.

**Keywords.** 1/3-2/3 conjecture, partially ordered set, linear
extension, balanced pair, width-3 poset, Bubley–Karzanov graph,
Cheeger inequality, expansion, conductance.

### §2.2 — Specific theorem/proposition numbers for R2 large-α

The R2 large-α axiom's load-bearing claim cites:

* **Proposition 7.2** (`prop:72`), `step7.tex:1172–1190` — "low-cut
  is 1D", the headline structural claim.
* **Remark 7.x** (`rem:w0-constant`), `step7.tex:1193–1219` — Lean
  alignment narrative for `w₀(γ) ≤ 4`.
* **Lemma 8.x** (`lem:layered-from-step7`), `step8.tex:2009–2089`
  — ground-set lift from Step 7 to the layered decomposition on
  `X ∖ X^exc`.
* **Lemma 8.x** (`lem:bandwidth`), `step7.tex:1015–1053` — bandwidth
  constant `K(T) = O_T(1)`.
* **Lemma 8.x** (`lem:exc-perturb`), `step8.tex:679–737` — exceptional-set
  perturbation `2k/(n−k+1)`.

(Theorem/lemma numbering in the paper uses `\newtheorem[theorem]`
shared counter; `prop:72` is "Proposition 7.2" in the §7 informal
labelling but its compiled number depends on section ordering.
For citation purposes the **LaTeX labels above are authoritative**
because they are stable across compilations.)

### §2.3 — Independent verification: does the cited theorem statement
actually deliver R2 large-α?

**No, not as written.** Per §1.2 above, `prop:72` delivers a
*propositional* layered decomposition "on `(1 − o(1))` of its mass";
`lem:layered-from-step7` delivers an *exact* layered decomposition
on `X ∖ X^exc`. Neither delivers "∃ L on α with L.w ≤ 4". The
Lean axiom is a **packaging** of these statements, not a verbatim
transcription. Honest citation requires acknowledging this.

The Lean-side wrapping is *mathematically defensible* (the four
encapsulated claims are each backed by paper sections), but the
audit can find **no single paper theorem** whose statement matches
the R2_large signature word-for-word. This is the key difference
from `brightwell_sharp_centred` (Brightwell 1999 Theorem 4.1
+ Kahn–Saks 1984 Lemma 2.2), whose Lean form is a direct integer
restatement of a single external theorem.

### §2.4 — Publication-grade docstring spec for the R2 large-α axiom

Following the template of `brightwell_sharp_centred`
(`lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:53–
159`) and its AXIOMS.md entry (`lean/AXIOMS.md:21–`…), the
proposed docstring for the R2 large-α axiom must contain:

```lean
/--
**R2 large-α layered decomposition axiom**
(paper-axiomatised packaging of Steps 1–7 + `prop:72`
+ `rem:w0-constant` + `lem:layered-from-step7` + `lem:exc-perturb`).

For every width-3 finite poset `α` that is not a chain with
`|α| ≥ 11`, there exists a layered decomposition `L :
LayeredDecomposition α` with interaction width `L.w ≤ 4`.

# Paper statement

This axiom encapsulates **four** distinct paper-side claims (it is
NOT a verbatim transcription of any single theorem):

1. **`prop:72`** (`step7.tex:1172–1190`) — low-conductance cut
   `{H ≥ c}` implies `P` admits a layered width-3 decomposition
   on `(1−o(1))` of its mass.
2. **`lem:layered-from-step7`(ii)** (`step8.tex:2054–2080`) — ground-set
   lift to an exact layered decomposition on `P|_{X ∖ X^exc}`
   with interaction width `w = K_bw + 2 = O_T(1)`, where
   `X^exc ⊆ α` has `|X^exc| ≤ 3·c_1(T) = O_T(1)`.
3. **`lem:exc-perturb`** (`step8.tex:679–737`) — pairwise
   probability perturbation bound
   `|p_xy(P) − p_xy(P|_{X∖X^exc})| ≤ 2k/(n−k+1)`,
   used to lift `L`'s existence on `X ∖ X^exc` to `α` via Lean-side
   promotion (the additional bands carrying the `|X^exc|`
   exceptional elements).
4. **`rem:w0-constant`** (`step7.tex:1193–1219`) — alignment of
   `w₀(γ) = K(T(γ)) + O(1)` to the Lean F5a Bool certificate
   coverage `w ∈ {1, 2, 3, 4}`. The "≤ 4" specialisation is a
   Lean-side scope choice, NOT a paper-proven numerical bound;
   the paper guarantees only `w = O_T(1)`.

# Citation

D. Miller, *The $1/3$–$2/3$ Conjecture for Width-3 Posets*,
manuscript in preparation, this repository (`main.tex`,
`step{1..8}.tex`). **Not yet peer-reviewed.** The axiom rests
on the author's own unpublished paper; faithful Lean delivery
of Steps 1–7 (replacing this axiom with a proof) is tracked
as the long-arc Option-A residual per `docs/onethird-Case3Witness-
post-cap-5-tractability-analysis.md` (mg-0cbf) §5.

# Caveats (Zulip-reviewer-visible)

1. **Self-citation.** Contrast with
   `LinearExt.brightwell_sharp_centred` which cites a
   peer-reviewed external paper (Brightwell, Discrete Math 201,
   1999, Theorem 4.1).

2. **Form mismatch.** The paper's `prop:72` delivers `L` on
   `X ∖ X^exc`, NOT on α. The α-side promotion (encapsulated
   item 3 above) is a Lean-side packaging step that the paper
   does not explicitly carry out.

3. **Constant `≤ 4` is Lean-aligned.** Per `rem:w0-constant`:
   "the present scope's natural alignment point is 4. A larger
   absolute cap (≤ 6, ≤ 10) would close as well, conditional on
   extending the F5a certificate to the wider w range." I.e.
   the paper does NOT compute `K(T(γ))` to show it numerically
   bounded by 2.

4. **Cardinality cut at 11.** Below `|α| ≤ 10`, R2 is discharged
   constructively (small-α R2_small per
   `docs/width3-residual-statement.md` §3.2). Above `|α| ≥ 11`,
   the Steps 1–7 cascade is the discharge mechanism.

# Replacement plan

Replace this axiom with a proof by:
1. Faithfully porting Steps 1–7 to Lean (long-arc multi-month
   work per `docs/layered-form-vs-coherence-architecture-audit.md`
   mg-74d2 §2c).
2. Implementing `lem:layered-from-step7`(ii) ground-set lift
   in Lean to obtain `L` on `α ∖ X^exc`.
3. Implementing the Lean-side promotion of `L` to α (the
   appending-bands construction in §1.2 above).
4. Proving the constant `K(T(γ)) + 2 ≤ 4` via explicit numerics
   in `lem:bandwidth`, OR widening the F5a Bool certificate to
   `w ≤ 6` / `≤ 10` (per the `rem:w0-constant` fallback).
-/
axiom step7_layered_decomposition_w4_aligned.{u} :
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α →
    11 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4
```

The corresponding `AXIOMS.md` entry must include:

* Header / file / paper statement (`prop:72` + the four
  encapsulated items).
* "Introduced by" / "QA-audited by" / "Status" lines.
* **Scope-match checklist** — a table mapping each axiom-side
  hypothesis to a specific paper section (analog of the
  `brightwell_sharp_centred` table at `AXIOMS.md:36–55`).
* **Self-citation acknowledgement** — explicit "this paper is the
  author's own unpublished manuscript" line.
* **Encapsulation transparency** — explicit list of the four
  paper-side claims being bundled.
* **Replacement plan** — copies of the four sub-tasks above.
* **`#print axioms` verification** — `#print axioms
  step7_layered_decomposition_w4_aligned` output, confirming
  no auxiliary anonymous axioms enter through Mathlib infra.

### §2.5 — Audit verdict on Phase B

**AMBER for citation rigor as currently practised.** The cited paper
(Daniel Miller's manuscript, in preparation, in this repo) is **not
peer-reviewed external literature**. This does NOT mean the citation
is dishonest — Daniel is forthright that he is formalising his own
work — but it means the docstring + AXIOMS.md framing must be
**meaningfully more careful** than `brightwell_sharp_centred`'s
framing, because:

1. The paper's `prop:72` does not have an analog of
   "Brightwell 1999, Theorem 4.1" as a stable external reference.
2. The cited paper is in a state of active revision (per
   `docs/width3-residual-statement.md` §6 paper-cleanup
   recommendations).
3. Daniel is asking external readers (Zulip community) to trust
   his own unpublished manuscript as the citation backing for a
   load-bearing axiom in a Lean formalisation.

The "GREEN" path requires the seven revisions in §0 — each is
mechanical (docstring edits, audit script updates) but each is
required.

---

## §3. Phase C — `#print axioms` readiness

### §3.1 — Current state of the `PrintAxiomsAudit.lean` script

`lean/scripts/PrintAxiomsAudit.lean` (7 active lines, mg-49a4):

```lean
import OneThird.MainTheorem
import OneThird.Step8.MainAssembly
import OneThird.Step8.TheoremE

#print axioms OneThird.width3_one_third_two_thirds
#print axioms OneThird.Step8.width3_one_third_two_thirds_assembled
#print axioms OneThird.width3_one_third_two_thirds_via_step8
#print axioms OneThird.Step8.mainAssembly
#print axioms OneThird.Step8.mainAssembly_smallN
#print axioms OneThird.Step8.cexImpliesLowBKExpansion
#print axioms OneThird.counterexample_implies_low_BK_expansion
```

**Currently expected output** (pre-R2-large landing, per the
existing `AXIOMS.md` inventory):

| Headline target | Expected axioms |
|---|---|
| `width3_one_third_two_thirds` | `propext`, `Classical.choice`, `Quot.sound` (Mathlib standard), `LinearExt.brightwell_sharp_centred` (paper-axiom), `case3Witness_hasBalancedPair_outOfScope` (paper-axiom), PLUS the structured `sorry` at `LayeredBalanced.lean:755` (mg-d5a0). |

**The structured `sorry`** at `LayeredBalanced.lean:755` is the
**only remaining sorry in the headline path** (independently verified:
`grep -rn '^[[:space:]]*sorry' lean/OneThird/` returns this single
line). Per `mg-d5a0` and `mg-2970` §4.4, the sorry closes once
`lem_layered_balanced`'s K≥2 dispatch is rewritten to consume the
caller's `L` (Option D-narrow).

### §3.2 — Post-landing expected state

After `mg-234e` Option-D-narrow-execution lands the R2 large-α axiom
+ R1 paper-faithful (or its restricted-cap form) per
`docs/width3-residual-statement.md` §3.1+§4.1, the `#print axioms`
output on `width3_one_third_two_thirds` should be:

| Axiom | Source | Status |
|---|---|---|
| `propext` | Mathlib standard | ✓ |
| `Classical.choice` | Mathlib standard | ✓ |
| `Quot.sound` | Mathlib standard | ✓ |
| `LinearExt.brightwell_sharp_centred` | Brightwell 1999 + Kahn–Saks 1984 (external, peer-reviewed) | ✓ (existing) |
| `case3Witness_hasBalancedPair_outOfScope` | `step8.tex:3033–3047` `prop:in-situ-balanced` Case 3 + `rem:enumeration` + mg-4d7b enumeration | ✓ (existing, kept for cap-1-cap-5 sub-slice) |
| `step7_layered_decomposition_w4_aligned` (NEW; or whatever final name) | `step7.tex:1172–1190` `prop:72` + `rem:w0-constant` + `step8.tex:2054–2088` `lem:layered-from-step7` + `step8.tex:679–737` `lem:exc-perturb` | NEW: requires the 7-revision disclosure list of §0 |

The structured `sorry` at `LayeredBalanced.lean:755` should be
**closed** (it disappears once the K≥2 dispatch consumes the
caller's `L` per Option-D-narrow rewrite).

### §3.3 — Audit gaps to close before `#print axioms` is "teed up"

Per Daniel's verbatim "Make sure `#print axioms` is teed up for me":

1. **Update `PrintAxiomsAudit.lean`** to add `#print axioms` for
   the new R2-large axiom (and R1 if a separate name is used).
2. **Add a `PrintAxiomsR2Large.lean`** companion script (analog of
   `PrintAxiomsCompactify.lean`) that prints the axioms transitively
   reaching the new R2 axiom. This confirms no accidental
   dependencies on non-standard axioms creep in.
3. **Land a `#print axioms <axiom>_rat`-style verification** in
   the new axiom's source file (analog of
   `brightwell_sharp_centred_rat`'s verification line, see
   `AXIOMS.md` "Certification" subsection lines 79–83).
4. **Verify the post-landing `lake build` succeeds** with no new
   sorries surfaced (the cap-5 sorry should close; no NEW sorries
   should be introduced by the rewrite).
5. **Run the script and commit the expected output** to a baseline
   file (e.g. `lean/scripts/PrintAxiomsAudit.expected`) so any
   future PR that drifts the axiom set fails CI.

### §3.4 — Audit verdict on Phase C

**AMBER.** The `PrintAxiomsAudit.lean` infrastructure exists and is
wired correctly, but it has **not been extended** to cover the
upcoming R2 large-α axiom. Items 1–5 in §3.3 are mechanical follow-up
tasks for `mg-234e` to land in the same commit as the axiom. Without
them, `#print axioms` is not "teed up" in the sense Daniel asked for —
the script would print the existing axiom inventory but a Zulip
reader running it would not see the new R2-large axiom called out
explicitly.

---

## §4. Phase D — Zulip-embarrassment-risk simulation

### §4.1 — Simulated mathlib-reviewer scrutiny

The Lean Zulip community's typical first-pass scrutiny on a new
paper-axiom (based on the pattern of reviews on
`brightwell_sharp_centred` and adjacent landings):

| Reviewer move | What they check | OneThird R2-large finding |
|---|---|---|
| (Q1) "What's the citation?" | Specific paper title + authors + year + theorem/page | **PARTIAL FAIL**: cited paper is author's own in-preparation manuscript; no peer review, no DOI, no stable arXiv ID. Honesty is fine if framed correctly; failure mode is silently presenting it as "the paper proves this" without disclosure. |
| (Q2) "Does the cited theorem deliver exactly this?" | Read the cited statement; check signature match | **FAIL**: the cited `prop:72` delivers a different signature (perturbed-set + asymptotic constant); R2_large's α-domain + `≤ 4` constant + universal quantification are Lean-side packaging. Honesty requires the docstring to say "this axiom encapsulates four claims" not "this axiom transcribes one theorem". |
| (Q3) "Is the axiom provable in Lean if you trust the paper?" | Trace the proof obligation; is it just a port? | **YES, conditional on (i) faithfully porting Steps 1–7 (multi-month), (ii) implementing the L-promotion to α (~1 polecat session), (iii) proving the constant ≤ 4 (depends on extending F5a or computing K(T) explicitly).** Per `mg-0cbf` §5 the long-arc work is multi-month, but it is bounded. |
| (Q4) "Why not prove it directly?" | Is the axiom genuinely "the hard part" or could it be proved with Lean infrastructure that already exists? | **GENUINELY HARD**: Steps 1–7 are the main mathematical content of the paper. Direct Lean proof would replicate ~5000 LaTeX lines of paper + extensive new Mathlib infrastructure (Cheeger inequality on directed Markov chains, FKG on linear extensions, chain potentials, etc.). The axiomatisation choice is reasonable. |
| (Q5) "What's the `#print axioms` output?" | Run the script | **Currently incomplete** (per §3.3): the script doesn't yet name the R2-large axiom. Will be fine after the §3.3 revisions. |
| (Q6) "Does this collapse to the headline trivially?" (Frankl-in-disguise risk) | Check whether the axiom is propositionally equivalent to a proved theorem in tree | **NO COLLAPSE FOUND** (see §4.2). R2_large is a *structural* claim (existence of L); the headline is a *probabilistic* claim (existence of balanced pair). R2 + R1 → headline, but neither alone gives the headline. |
| (Q7) "Why this specific constant?" | Justify the numerical value | **CAN ANSWER**: `≤ 4` aligns to the F5a Bool certificate's coverage. `rem:w0-constant` makes this explicit. The docstring must repeat this — otherwise the constant looks arbitrary. |
| (Q8) "What's the relationship to existing axioms?" | Check independence and orthogonality | **CLEAN**: R2_large is orthogonal to `brightwell_sharp_centred` (different paper steps) and to `case3Witness_hasBalancedPair_outOfScope` (different cell of `prop:in-situ-balanced`). No double-counting or circularity. |
| (Q9) "If I'm a skeptic, what can I check?" | Standalone verifiability | **POSSIBLE**: A skeptic can read the cited paper sections (`step7.tex:1172–1190`, `step7.tex:1193–1219`, `step8.tex:2009–2089`, `step8.tex:679–737`) and form their own opinion on whether the paper's argument is sound. The paper IS publicly readable in this repository. |

**Overall Zulip-pass rate estimate.** With the 7-revision list of §0
applied, the axiom would survive an initial Zulip pass with the
typical "this is bounded but the citation is self-referential" caveat.
Without the revisions, it would attract 2–4 reviewer comments within
24 h of public posting, mostly focused on Q1 (self-citation framing)
and Q2 (form mismatch).

### §4.2 — Frankl-in-disguise collision risk check (analog of mg-ee54 Phase B)

The Frankl mg-ee54 finding: the chain-level paper-axiom on the
Frankl side **propositionally collapsed** to width-3-1/3-2/3
itself via existing proven theorems (in-disguise collision).

**Analog check for R2 large-α**: does the proposed axiom
propositionally collapse to width3-1/3-2/3 itself, or to any
already-proved theorem in the OneThird tree?

**Search:** all theorems in tree of the form
`∀ α width-3 non-chain, ∃ L : LayeredDecomposition α, L.w ≤ k`
for any `k ≤ 4`.

Result: **none found.** The closest existing theorem-shaped objects
are:

| Construct | File | Status |
|---|---|---|
| `Step8.layeredFromBridges` | `LayeredBridges.lean:181` | Produces L with `w = Lwidth3.bandwidth = |α| + 1` (sham) — does NOT satisfy `L.w ≤ 4` for `|α| ≥ 4`. |
| `Step8.trivialLayered` | `MainAssembly.lean:165` | `K = w = |α|` — same sham bandwidth. |
| `Step8.canonicalLayered` | `LayeredBalanced.lean:498` | Same sham. |
| `Step7.prop_72` | `Step7/Assembly.lean:329` | Produces `Step7.LayeredWidth3` (abstract bundle), NOT `Step8.LayeredDecomposition`. Different structure; `prop_72` does NOT directly give `Step8.LayeredDecomposition α`. |

**Conclusion.** R2 large-α is NOT propositionally equivalent to any
existing in-tree theorem. There is **no Frankl-in-disguise collision
risk** on the OneThird side.

The R2-large axiom asks for `L : Step8.LayeredDecomposition α` with
`L.w ≤ 4`. The closest existing constructions (`layeredFromBridges`,
`trivialLayered`, `canonicalLayered`) all give `L.w = |α|` or
`|α| + 1`, failing the cap immediately.

### §4.3 — Paper-axiom framing clarity

**Question.** Is the proposed framing clear that "we're using paper
X's argument Y, axiomatised pending faithful Lean delivery of Steps
1–7" vs "we couldn't prove this so we just assumed it"?

**Per the seven revisions in §0**: if all seven land in the docstring
+ AXIOMS.md, the framing IS clear. Specifically, revision #6
(encapsulation transparency) and revision #1 (honest self-citation)
together make the "axiomatised pending faithful Lean delivery"
framing unambiguous.

**If revision #6 is skipped** (i.e. the axiom is presented as "Daniel's
prop:72 implies this" without listing the four encapsulated paper
claims), then a Zulip reader could reasonably misread it as "we
couldn't prove this so we just assumed it." The four-claim
encapsulation is the math content; without it, the axiom is opaque.

**If revision #1 is skipped** (i.e. the citation is presented without
"in preparation, by the author" disclosure), then a Zulip reader
checking the paper PDF will quickly notice the discrepancy and ask
why it's not on arXiv.

### §4.4 — Joel Riou attribution

**Per task body:** "Joel Riou attribution preserved (if applicable to
OneThird side)."

**Audit finding:** **not applicable.** The OneThird paper `main.tex:87`
is single-authored by D. Miller. The paper bibliography contains no
Riou citation. A repository-wide grep `grep -irn 'Riou\|Joel' main.tex
step*.tex` returns no matches. The Frankl-side Joel Riou attribution
(if any in `mg-ee54`) does NOT carry over to the OneThird side.

### §4.5 — Audit verdict on Phase D

**AMBER for Zulip-defensibility as currently planned.** The R2
large-α axiom is **not at risk of an in-disguise collision** (§4.2)
or **propositional vacuity** (§4.4). The framing risks (§4.1) and
self-citation risks (§2) are bounded and addressable via the seven
revisions in §0. With the revisions, the audit upgrades to GREEN.
Without them, expect 2–4 Zulip comments in the first 24 h focused
on (Q1) self-citation and (Q2) form mismatch.

---

## §5. The four most likely Zulip-objection vectors (priority order)

If the R2 large-α axiom lands **without** the §0 revisions, here are
the objections to expect:

### §5.1 — Objection (V1): "What's the citation? `step7.tex:1172`?"

**Likelihood:** ~95% (first thing any careful reader checks).
**Trigger:** docstring does not state "manuscript in preparation,
by the author" explicitly.
**Mitigation:** revision #1 in §0.
**Fallback:** if questioned post-landing, Daniel can clarify
verbatim. Reputational cost: low.

### §5.2 — Objection (V2): "The axiom's signature doesn't match `prop:72`."

**Likelihood:** ~80% (anyone who reads the paper PDF and the axiom
side-by-side).
**Trigger:** docstring presents the axiom as a transcription of
`prop:72` without disclosing the four-claim encapsulation.
**Mitigation:** revision #6 in §0.
**Fallback:** Daniel walks through the encapsulation in a comment;
2–3 message exchange. Reputational cost: low-medium.

### §5.3 — Objection (V3): "Why is `≤ 4`? Where does that come from?"

**Likelihood:** ~70% (the constant appears arbitrary without
`rem:w0-constant` context).
**Trigger:** docstring does not cite `rem:w0-constant` and the
F5a Bool certificate alignment.
**Mitigation:** revisions #3 and #6 in §0.
**Fallback:** point to `rem:w0-constant` in the paper; 1–2 message
exchange. Reputational cost: low.

### §5.4 — Objection (V4): "Is `prop:72` actually proven, or is it
also an axiom-in-disguise?"

**Likelihood:** ~30% (only the most thorough readers check the
paper-side proof of `prop:72` itself).
**Trigger:** reader looks at `step7.tex:1180-1190` and notices
that `prop:72`'s proof cites an unlabelled "width-3 structural
lemma" (the Caveat 2 of §1.3 here).
**Mitigation:** paper-cleanup task — label the structural lemma in
`step7.tex`. NOT required for the axiom landing, but a follow-on
that would close this objection vector if it surfaces.
**Fallback:** Daniel explains the paper-side proof in a comment;
3–5 message exchange. Reputational cost: medium (this is the
"depth of the formalisation" question; arguably the most serious
objection).

---

## §6. Forward action recommendation: GREEN-with-conditions

### §6.1 — Verdict

**GREEN-with-conditions** for `mg-234e` Option-D-narrow-execution
dispatch.

The R2 large-α paper-axiom is **mathematically sound** as a packaging
of the paper's Steps 1–7 + `prop:72` + `rem:w0-constant` + `lem:exc-perturb`
cascade. The cascade itself is rigorously argued in the paper (modulo
the 5 minor caveats of §1.3, none of which is a math-content gap).

**Before mg-234e lands the axiom**, the seven revisions of §0 must
be applied (analog of the mg-ee54 7-revision list):

1. **Honest self-citation framing.** Docstring explicitly states
   "manuscript in preparation, by the author".
2. **Form mismatch disclosure.** Docstring explicitly states the
   paper delivers `L` on `X ∖ X^exc`, NOT on α.
3. **Constant pinning disclosure.** Docstring cites `rem:w0-constant`
   and acknowledges `≤ 4` is Lean-aligned (NOT paper-computed).
4. **`#print axioms` wiring.** Add new axiom to
   `lean/scripts/PrintAxiomsAudit.lean`; baseline expected output.
5. **AXIOMS.md scope-match checklist.** Add ~150-line entry analog to
   `brightwell_sharp_centred`.
6. **Encapsulation transparency.** Docstring + AXIOMS.md entry list
   the four paper-side claims being encapsulated.
7. **Naming.** Use `step7_layered_decomposition_w4_aligned` (or
   similar), NOT generic `R2_large_axiom`.

### §6.2 — Verdict downgrades if any revision skipped

* **Skip revision #1**: downgrades to AMBER. Zulip objection (V1)
  inevitable; reputational cost low but noisy.
* **Skip revision #2**: downgrades to AMBER. Zulip objection (V2)
  inevitable; reputational cost low-medium.
* **Skip revision #3**: downgrades to AMBER. Zulip objection (V3)
  likely; reputational cost low.
* **Skip revision #4**: downgrades to AMBER. Daniel's verbatim ask
  "`#print axioms` teed up" not fulfilled; reputational cost low
  but the headline "teed up" claim is false until script updated.
* **Skip revision #5**: downgrades to AMBER. Inconsistency with
  the existing axiom inventory; reputational cost low.
* **Skip revision #6**: downgrades to RED. The axiom would be opaque;
  Zulip reader cannot tell what claims are bundled vs what is the
  load-bearing math. This is the **single most-important** revision
  for math defensibility.
* **Skip revision #7**: downgrades to AMBER. Naming the axiom
  generically obscures its packaging nature; minor.

**Skip more than two revisions: downgrades to AMBER irrespective of
which.** The cumulative effect of multiple minor-disclosure failures
is a reviewer impression of insufficient care.

### §6.3 — Out-of-scope follow-ons disclosed

The audit identified follow-on items **not blocking mg-234e**, but
worth tracking:

* **(F1)** Independent reader audit of `prop:71`'s proof
  (`step7.tex:1112–1170`, ~60 lines + G1-G9 chain in the
  preceding sections). This is the densest paper section and
  has not been independently audited in this polecat session.
  Recommend: an mg-XXXX ticket dedicated to `prop:71` deep audit
  before public arXiv submission.

* **(F2)** Paper-cleanup: label the "width-3 structural lemma"
  referenced in `prop:72`'s proof (`step7.tex:1186`). Currently
  unlabelled; would close Zulip objection (V4) preemptively.

* **(F3)** Independent verification of `c_1(T) = O_T(1)`
  in `step5.tex`'s `lem:endpoint-mono`. The audit accepted this
  on the paper's word; an explicit numerical bound would close
  Caveat 3 of §1.3.

* **(F4)** Explicit numerical computation of `K(T(γ))` in
  `lem:bandwidth` (`step7.tex:1015–1053`). If `K(T(γ)) ≤ 2` could
  be shown explicitly, then `w₀(γ) = K + O(1) ≤ 4` is a paper-side
  fact and revision #3 collapses to "the paper proves this
  numerically". Today the paper only argues `O_T(1)`.

* **(F5)** R1 (`R1_paper_faithful`) audit. mg-234e dispatches both
  R1 and R2; this audit focused on R2. R1 is the paper port of
  `lem:layered-balanced` (`step8.tex:3211–3266` proof) — a 56-line
  strong-induction proof. Per `width3-residual-statement.md` §3.1,
  R1's Lean port is 3–5 polecat sessions. R1 does NOT need
  axiomatisation if the port is direct; this audit recommends R1
  be a **theorem with proof**, not an axiom, to keep the axiom
  count minimal.

* **(F6)** Extend `case3Witness_hasBalancedPair_outOfScope` to drop
  cap-1 antecedents per `width3-residual-statement.md` §4.5. Not
  required for mg-234e but would close the cap-1 sub-slice coverage
  gap diagnosed by mg-2970 §1.3.

### §6.4 — Comparison with Frankl mg-ee54 pattern

Per task body: "analog of Frankl mg-ee54". The OneThird audit echoes
the mg-ee54 pattern:

| Aspect | Frankl mg-ee54 | OneThird mg-4582 (this audit) |
|---|---|---|
| Citation type | (per pattern reference) | Self-cite to in-prep manuscript |
| Form mismatch finding | (per pattern reference) | YES — paper delivers L on X\X^exc; axiom asserts L on α |
| Constant pinning issue | (per pattern reference) | YES — w ≤ 4 is Lean-aligned, not paper-proven |
| In-disguise collision risk | YES (chain-level collapse) | NO (R2 is structural, headline is probabilistic; no collapse) |
| 7-revision list | (per pattern reference) | YES (§0 above) |
| Joel Riou attribution | (applicable) | NOT applicable (single-author paper) |
| Verdict | (per pattern reference) | GREEN-with-conditions |

The in-disguise collision risk is the key disanalogy — the OneThird
R2 axiom is *structural* (existence of L), while the Frankl chain
axiom (per pattern reference) was *propositional* (a conclusion that
could collapse to the headline). The OneThird R2 axiom is harder to
accidentally turn into a triviality, which is a relief.

---

## §7. Cross-references and load-bearing claims

### §7.1 — Lean files referenced

* `lean/OneThird/MainTheorem.lean:56` —
  `width3_one_third_two_thirds` headline.
* `lean/OneThird/Step8/MainAssembly.lean:238` —
  `mainTheoremInputsOf` bundle producer; currently feeds
  `layeredFromBridges` as `caseR_to_caseC`.
* `lean/OneThird/Step8/LayeredBridges.lean:181` —
  `layeredFromBridges` current sham-bandwidth witness
  (`w = Lwidth3.bandwidth = |α| + 1`).
* `lean/OneThird/Step8/LayeredBalanced.lean:755` — the **single
  remaining structured `sorry`** in the headline path
  (mg-d5a0), to be closed by Option-D-narrow rewrite.
* `lean/OneThird/Step7/Assembly.lean:302–348` — `LayeredWidth3`
  structure + `prop_72` theorem (abstract bundle form).
* `lean/OneThird/Step7/Assembly.lean:329` — `prop_72` theorem
  with abstract `LayeredWidth3` packaging; `bandwidth = c₀`.
* `lean/OneThird/Step8/LayeredReduction.lean:115` —
  `LayeredDecomposition α` structure (5 axioms: L1a, L1b,
  L2-forced, L2-upward).
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
  — `brightwell_sharp_centred` (existing external-paper-axiom,
  reference template for the R2-large axiom's documentation
  style).
* `lean/OneThird/Step8/Case3Residual.lean:208` —
  `case3Witness_hasBalancedPair_outOfScope` (existing
  paper-axiom, supported by mg-4d7b enumeration).
* `lean/AXIOMS.md` — named-axioms inventory.
* `lean/scripts/PrintAxiomsAudit.lean` — `#print axioms` audit
  script.

### §7.2 — Paper sources

* `main.tex:86–87` — author + title.
* `main.tex:1–14` — arXiv submission metadata (not yet
  submitted).
* `step7.tex:1015–1053` — `lem:bandwidth` (`K = O_T(1)`).
* `step7.tex:1057–1104` — proof of `prop:72`.
* `step7.tex:1112–1170` — `prop:71` + proof.
* `step7.tex:1172–1190` — `prop:72` statement + 11-line proof.
* `step7.tex:1193–1219` — `rem:w0-constant` (Lean alignment
  narrative).
* `step8.tex:679–737` — `lem:exc-perturb` + `eq:exc-perturb`.
* `step8.tex:702–712` — Step 5 dichotomy exhaustiveness.
* `step8.tex:716–779` — Case (C) and Case (R) main assembly use
  of the layered decomposition.
* `step8.tex:1983–2007` — `def:layered` (layered decomposition
  axioms L1-L4).
* `step8.tex:2009–2089` — `lem:layered-from-step7` (ground-set
  lift, branches (a) and (b)).
* `step8.tex:2454–2488` — `lem:layered-balanced` statement +
  Lean alignment remark.
* `step8.tex:3089–3209` — `prop:in-situ-balanced` Cases 1, 2, 3.
* `step8.tex:3211–3266` — proof of `lem:layered-balanced`.

### §7.3 — Predecessor work items

* `mg-5c32` — over-constrained first residual extraction
  (superseded by mg-2970).
* `mg-2970` — corrected R1 + R2 residual extraction.
* `mg-82fc` — Phase A audit confirming F3 conclusion-lift is
  substantive.
* `mg-74d2` — layered-form-vs-coherence audit.
* `mg-0cbf` — post-cap-5 tractability; Option D-narrow framing.
* `mg-d5a0` — structured `sorry` placement at
  `LayeredBalanced.lean:755`.
* `mg-4d7b` — cap-5 enumeration (cap-1 sub-slice only).
* `mg-6f04` — PROOF-STRUCTURE-ONBOARDING canonical entry.
* `mg-ee54` — Frankl analog (pattern reference for this audit).
* `mg-234e` — Option-D-narrow-execution (BLOCKED on this audit's
  GREEN signal).

---

## §8. Summary

* **Phase A** (Steps 1–7 + `prop:72` chain rigor). Paper-side
  argument is **rigorously written**, but the proposed Lean axiom
  signature does **not** mirror any single paper theorem; it bundles
  four claims (`prop:72`, `lem:layered-from-step7`, `lem:exc-perturb`,
  `rem:w0-constant` constant pinning). Five caveats in §1.3,
  all documentation gaps not math-content gaps.

* **Phase B** (literature citation rigor). Citation is to the
  **author's own unpublished manuscript** in this repository — not a
  peer-reviewed external paper. This is **honest** but requires
  meaningfully more careful framing than `brightwell_sharp_centred`'s
  citation. Specific paper sections identified
  (`step7.tex:1172–1190`, `step7.tex:1193–1219`, `step8.tex:2009–
  2089`, `step8.tex:679–737`). Publication-grade docstring template
  drafted in §2.4.

* **Phase C** (`#print axioms` readiness). Existing
  `PrintAxiomsAudit.lean` infrastructure is sound but **does not yet
  reference the new R2-large axiom**. Five sub-tasks in §3.3 to land
  with mg-234e. Daniel's verbatim "`#print axioms` teed up" requires
  these sub-tasks.

* **Phase D** (Zulip-embarrassment-risk simulation). **NO
  Frankl-in-disguise collision risk** (§4.2 — R2 is structural,
  headline is probabilistic; no existing in-tree theorem matches the
  axiom signature). Four likely objection vectors in §5, all bounded
  and addressable via §0 revisions. Joel Riou attribution NOT
  applicable (single-author paper).

* **Phase E** (forward action verdict). **GREEN-with-conditions**.
  The seven revisions in §0 must be applied before mg-234e lands
  the axiom. Each is mechanical (docstring + AXIOMS.md edits +
  script updates); none requires fresh math. With the revisions,
  the axiom is cleanly Zulip-defensible as a paper-axiomatised
  packaging of the in-preparation manuscript's Steps 1–7 cascade,
  pending faithful Lean delivery (multi-month Option-A residual).

* **Bottom line for `mg-234e` dispatch.** Clear to proceed with the
  Option-D-narrow rewrite of `lem_layered_balanced` (which closes
  the cap-5 `sorry` at `LayeredBalanced.lean:755`), provided the
  same commit also lands:
  1. The new R2 large-α axiom with the §2.4 docstring spec.
  2. The seven §0 revisions (docstring, `AXIOMS.md`, `#print axioms`).
  3. The R1 paper-faithful theorem (as a theorem with proof — NOT
     an axiom, per the §6.3 (F5) recommendation).

* **Verdict.** **GREEN-with-conditions** (analog of Frankl mg-ee54
  7-revision verdict pattern).
