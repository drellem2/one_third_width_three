# Documentation consistency check (Validation D, mg-5cd8)

**Audit date.** 2026-05-06.
**HEAD audited.** `0df0bc4`.
**Audited by.** `cat-mg-5cd8` polecat.
**Verdict.** **AMBER.** The two forum-disclosure documents
(`docs/lean-forum-publication-readiness.md` and
`docs/lean-forum-post-template.md`) are pre-Stage-2B and describe
the headline as carrying an `hC3 : Step8.Case3Witness` Prop-level
hypothesis. After Option-C Stage 2B (`mg-8c72`, 2026-05-05), `hC3`
was discharged as a theorem (`OptionC.Case3Witness_proof`) and the
public headline `OneThird.width3_one_third_two_thirds` is now
**unconditional** modulo `hP : HasWidthAtMost α 3` and `hNonChain :
¬ IsChainPoset α`. Both forum-disclosure documents must be
refreshed before forum send. **Per ticket trip-wire 5, the
verdict is AMBER not RED — propose specific fixes, do not
block.**

The audit also surfaces two minor polish items in
`lean/AXIOMS.md` (also pre-Stage-2B) that could be improved at the
same time as the disclosure-doc refresh, but neither is a
substantive faithfulness issue. Per `mg-5cd8` ticket "What this
ticket does NOT do" — _"Does not refresh the forum post template's
disclosure language. PM files a small ticket for that
post-validation."_ — the doc-refresh is **out of scope for this
ticket**. The recommended PM follow-on is sketched at the end of
this document.

## Scope

The four disclosure surfaces named in the `mg-5cd8` ticket
"Validation D (implicit)" subsection:

* `lean/AXIOMS.md`
* `docs/lean-forum-publication-readiness.md`
* `docs/lean-forum-post-template.md`
* `README.md` "Please read this before citing" section

Each is checked against current main HEAD (`0df0bc4`) for
consistency with the post-Stage-2B axiom inventory and headline
shape.

## Per-document audit

### `README.md` — root

**Last touched.** `0df0bc4` (`mg-0dd2`, 2026-05-05) — explicitly
calibrated to post-Stage-2B.

**Status.** **CURRENT.** ✅

The "Please read this before citing" section (lines 83-189)
correctly reflects the post-Stage-2B headline shape:

> The historical `hC3 : Step8.Case3Witness` parameter — retained
> as a hypothesis on the Lean headline through the option (δ) park
> decision (2026-04-27) and the Path C cleanup-track block-and-report
> (2026-05-04) — was closed by `OptionC.Case3Witness_proof`
> (Option-C Stage 2B, `mg-8c72`, 2026-05-05) … (line 116-119)
>
> The headline now stands, after the Stage 2B closure plus the
> Step-8 main assembly, on **two named project axioms**:
> `OneThird.LinearExt.brightwell_sharp_centred` (transcribing the
> Brightwell 1999 §4 / Kahn–Saks 1984 single-element perturbation
> bound) and
> `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`
> (the residual half of the paper's `prop:in-situ-balanced` Case 3
> outside the F5a Bool-certified `InCase3Scope` parameter range).
> (line 122-128)

The `#print axioms` listing (line 250-263 area) matches
`lean/PRINT_AXIOMS_OUTPUT.txt`. ✅

### `lean/README.md` — Lean tree disclosure

**Last touched.** `16d26ef` (`mg-8c72`, 2026-05-05) — touched by
the Stage 2B commit itself.

**Status.** **CURRENT.** ✅

* The `#print axioms` listing (lines 22-30) shows the full 10-entry
  expanded inventory (mathlib trio + Brightwell + outOfScope + 5
  native_decide instances). Matches `PRINT_AXIOMS_OUTPUT.txt`. ✅
* Line 72 explicitly notes `"hC3" retention dropped (Option-C
  Stage 2, mg-2a56 + mg-8c72)`. ✅
* The five `_native.native_decide.ax_1_1` axioms are correctly
  identified as instances of `Lean.ofReduceBool` (lines 59-60). ✅

### `lean/AXIOMS.md` — named project axioms catalog

**Last touched.** `eaa9166` (`mg-7377`, pre-Stage-2B 2026-05-04).

**Status.** **CURRENT on faithfulness; minor polish stale.** 🟡

* Both project axiom entries (`brightwell_sharp_centred` and
  `case3Witness_hasBalancedPair_outOfScope`) are still
  **faithful** — neither axiom statement, nor its hypothesis
  profile, nor its scope-match checklist, has changed since
  `mg-7377`. The QA verdict ("**Axiom is faithful.**") still
  applies. ✅
* The `case3Witness_hasBalancedPair_outOfScope` entry's
  hypothesis-profile table (line 250-275) lists `hC3 :
  Case3Witness L` as a **hypothesis of the axiom statement**, not
  as a hypothesis of the headline. This is unchanged — the axiom
  itself still takes `hC3` as part of its hypothesis profile.
  Reading the table as describing the axiom's statement (which it
  is), the entry remains accurate. ✅
* **Minor polish — Forum-post disclosure subsection.** Lines
  358-377 describe the forum-post draft requirements (mentioning
  `case3Witness_hasBalancedPair_outOfScope` and `brightwell_sharp_centred`
  in `#print axioms` output) but do **not** mention that the
  output also lists 5 `_native.native_decide.ax_1_1` instances
  (each an instance of `Lean.ofReduceBool`). The `lean/README.md`
  disclosure (current) does cover this; the AXIOMS.md disclosure
  subsection lags. **Not a faithfulness issue** — the AXIOMS.md
  scope is project axioms, and the native_decide entries are not
  project axioms. **Recommended polish:** add one sentence to the
  Forum-post disclosure subsection noting the
  `_native.native_decide.ax_1_1` entries as additional
  trust-surface line items per the `lean/README.md` framing.

### `docs/lean-forum-publication-readiness.md` — public-facing
disclosure

**Last touched.** `bc81243` (`mg-cda8`, pre-Stage-2B). **STALE.**
🔴

Specific stale claims (post-Stage-2B inaccurate as written):

1. **Line 14-19.** Status block reads:
   > **Status as of 2026-05-04.** Build is clean; the headline
   > depends on one named project axiom (Brightwell, transcribing
   > a published external result) plus Lean's standard
   > classical-foundations trio, and carries one Prop-level
   > hypothesis (`hC3`) that pins a parametrically-quantified
   > discharge of the paper's `prop:in-situ-balanced` Case 3.

   **Stale on three counts.** (i) Date is 2026-05-04, pre-Stage-2B;
   (ii) headline depends on **two** named project axioms now
   (Brightwell + `case3Witness_hasBalancedPair_outOfScope`), not
   one; (iii) headline does **not** carry `hC3` as a hypothesis
   anymore.

2. **Line 90-99.** "Lean headline (`width3_one_third_two_thirds`,
   `lean/OneThird/MainTheorem.lean:52-57`)" code snippet shows the
   pre-Stage-2B signature with `(hC3 : Step8.Case3Witness.{u})`.
   The current public signature (post-Stage-2B) drops `hC3`.

3. **Line 101-189.** Section **§2 What `hC3 : Case3Witness` is
   and why it is parked** describes `hC3` as an open Prop-level
   hypothesis. After Stage 2B, `hC3` is **discharged** by
   `OptionC.Case3Witness_proof`; the residual axiom
   `case3Witness_hasBalancedPair_outOfScope` is the trust footprint
   that replaces the parking discussion.

4. **Lines 220-262** describe the F3 `[0.276, 1/3)` gap as the
   structural obstruction blocking `hC3` discharge. Still
   substantively correct as a forum-relevant point about why the
   `case3Witness_hasBalancedPair_outOfScope` axiom is genuinely
   under-developed in the LaTeX source — but the framing should
   shift from "`hC3` is parked" to "the `outOfScope` axiom is
   retained as a faithful transcription of `rem:enumeration`'s
   sketch and a future replacement requires the band-restricted
   FKG sub-coupling."

5. **Lines 358-524** discuss `Case2FKGSubClaim` as a parked
   sub-issue inside `hC3`'s universal. After Stage 2B, this
   Case-2 leaf was either subsumed by `option_c_K2_closure` (`mg-01ec`)
   or left embedded inside the `outOfScope` axiom's hypothesis
   profile (`Case3Witness L = ¬ Case1 ∧ ¬ Case2Witness L`). The
   discussion is still relevant for explaining the LaTeX-source
   gap, but the framing should align with the post-Stage-2B trust
   surface.

**Recommended refresh scope.** Update the §1 status block, §1b
code snippet, §2 framing, and §3 `Case2FKGSubClaim` discussion to
reflect the post-Stage-2B unconditional headline + retained
`outOfScope` axiom. The substantive math content (the structural
obstruction and the deferred A8-S2-cont infrastructure) remains
accurate.

### `docs/lean-forum-post-template.md` — paste-able forum
announcement

**Last touched.** `bc81243` (`mg-cda8`, pre-Stage-2B). **STALE.**
🔴

Specific stale claims:

1. **Lines 17-26.** Calibration paragraph cites the option (δ)
   park decision (2026-04-27), the η₅ park of `Case2FKGSubClaim`
   (`mg-457c`), and the 2026-05-04 Path C closure — all pre-Stage-2B.
   Stage 2B subsequently closed `hC3` as a theorem; the calibration
   needs a 2026-05-05 update line.

2. **Lines 53-152.** Template body reads:
   > Its statement is paper-faithful **modulo a documented Prop-level
   > hypothesis `hC3 : Step8.Case3Witness`** — the universally-quantified
   > discharge of the within-band antichain Case 3 of the paper's
   > `prop:in-situ-balanced` — which a consumer of the headline must
   > supply or carry.

   After Stage 2B, the consumer no longer supplies `hC3`. The
   template paragraph should be rewritten as:

   > Its statement is paper-faithful (modulo width-3, non-chain
   > hypotheses matching the paper's `thm:main`). The trust
   > footprint: two named project axioms — Brightwell sharp
   > centred (a transcription of Brightwell 1999 §4 + Kahn–Saks
   > 1984), and `case3Witness_hasBalancedPair_outOfScope` (a
   > transcription of `rem:enumeration`'s residual sketch outside
   > the F5a Bool-certified `InCase3Scope` parameter range) — plus
   > the standard `Lean.ofReduceBool` for `native_decide`-backed
   > Case-3 / Case-2 enumeration certificates.

3. **Lines 88-152.** Discussion of "Closing `hC3` therefore now
   requires …" is now misframed. After Stage 2B, `hC3` is closed.
   The relevant gap is now "**replacing the
   `case3Witness_hasBalancedPair_outOfScope` axiom requires**: (i)
   the deferred A8-S2-cont infrastructure (~2000-3500 LoC); (ii)
   …" — same revival routes as before, but applied to the axiom
   replacement rather than `hC3` closure. Per `mg-5cd8` disposition
   B amendment, the port itself is **deferred indefinitely**, so
   the framing should foreground "axiom is retained, here is the
   honest disclosure of what its replacement requires" rather than
   "this is parked open math."

**Recommended refresh scope.** Same as the publication-readiness
doc: §0 calibration paragraph, §1 template body's `hC3` framing,
and §2 closure-routes discussion. Headline should foreground
"two named axioms + standard compiler trust" as the trust surface,
with the `outOfScope` axiom honestly disclosed as a transcription
of an under-developed paper sketch.

## Aggregate verdict — Validation D

**AMBER.** Two of four disclosure surfaces
(`docs/lean-forum-publication-readiness.md` and
`docs/lean-forum-post-template.md`) are pre-Stage-2B and need
refresh before forum send. The drift is **substantive in the
sense of `mg-5cd8` trip-wire 5** ("readiness doc still references
the old axiom inventory" — here, the docs reference an old
*hypothesis* `hC3` rather than the post-Stage-2B unconditional
headline, which is the analogous failure mode), so trip-wire 5 is
triggered: AMBER, propose specific fixes, do not block.

The other two surfaces (`README.md` root + `lean/README.md`) are
both current. `lean/AXIOMS.md` is faithful on its core scope
(named project axioms) but its Forum-post disclosure subsection
could use a polish update mentioning the `_native.native_decide`
entries; this is non-blocking.

## Recommended PM follow-on ticket

Per `mg-5cd8` ticket scope ("**What this ticket does NOT do** —
Does not refresh the forum post template's disclosure language. PM
files a small ticket for that post-validation."), the PM should
file a **doc-refresh follow-on ticket** with the following
deliverables:

* **Refresh `docs/lean-forum-publication-readiness.md`:**
  - Update §1 status block to cite Stage 2B (`mg-8c72`, 2026-05-05)
    and reflect that the headline is unconditional.
  - Update §1b code snippet to drop `(hC3 : Step8.Case3Witness.{u})`.
  - Rewrite §2 ("What `hC3 : Case3Witness` is and why it is
    parked") as "**What the `case3Witness_hasBalancedPair_outOfScope`
    axiom is and why it is retained**", inheriting the `mg-7377`
    QA verdict and the `mg-5cd8` disposition-B-amendment
    deferred-port decision.
  - Reframe §3 (`Case2FKGSubClaim` discussion) as a historical
    note on the pre-Stage-2B parking, with a forward pointer to
    the post-Stage-2B `option_c_K2_closure` Case-2 closure.
* **Refresh `docs/lean-forum-post-template.md`:**
  - Update calibration paragraph (lines 17-26) with a 2026-05-05
    Stage 2B closure line.
  - Rewrite template body's §2 paragraph (lines 53-152) to
    foreground "two named axioms + standard compiler trust" as the
    trust surface.
  - Update §3 ("Closing `hC3` therefore now requires …") as
    "**Replacing the `outOfScope` axiom requires …**".
* **Polish `lean/AXIOMS.md`:**
  - Add a sentence in the
    `case3Witness_hasBalancedPair_outOfScope` Forum-post disclosure
    subsection (line 358-377) noting the `_native.native_decide.ax_1_1`
    entries as additional trust-surface line items, per the
    `lean/README.md` framing.

The substantive math content — the F3 structural obstruction, the
cleanup-track audits, the deferred A8-S2-cont infrastructure — is
all still accurate and should be preserved. Only the framing and
`hC3`-vs-`outOfScope`-axiom shift needs an update.

**Estimated scope.** ~150-300 lines of doc edits across two files
plus a one-paragraph addition to `lean/AXIOMS.md`. Single polecat
ticket. No Lean source changes.

## Cross-references

* Doc surfaces audited:
  - `README.md` (root)
  - `lean/README.md`
  - `lean/AXIOMS.md`
  - `docs/lean-forum-publication-readiness.md`
  - `docs/lean-forum-post-template.md`
* Stage 2B closure: `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean`,
  commit `16d26ef` (`mg-8c72`).
* Disposition-B amendment source: `mg-5cd8` ticket text, pm-onethird
  mail 1778024525633630000.
* Trip-wire reference: `mg-5cd8` ticket "Trip-wires" §5.
