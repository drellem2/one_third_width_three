# Formalization-completeness audit (2026-04-27)

**Filed by** `pc-49a4` polecat under `mg-49a4`. Six-step sweep of both
`one_third_width_three` (primary) and `one_third` (secondary) Lean trees,
plus a paper-vs-Lean cross-reference and orphan-infrastructure check.

## §1 TL;DR

The primary repo `one_third_width_three` is **structurally complete**:
the headline theorem `OneThird.width3_one_third_two_thirds` builds clean
with **zero `sorry`/`admit`** in any production code path, **two named
project axioms** (one transcribing an external published result, the
other a temporarily orphan piece of parked Path C wiring), and the
paper's main step-level theorems (`thm:step1`–`thm:step7`,
`thm:cex-implies-low-expansion`, `thm:main-step8`) all have in-tree
counterparts.

**Verdict.** The proof is formalized, modulo:

1. **`brightwell_sharp_centred`** — paper-faithful transcription of an
   external published bound (Brightwell 1999 §4 + Kahn–Saks 1984
   Lemma 2.2). Retained by deliberate `mg-b699` decision; replacement
   path documented in `lean/AXIOMS.md`.
2. **Path C parked work** (`hC3 : Step8.Case3Witness` retained as a
   hypothesis on the headline). Comprehensively documented in
   `docs/path-c-cleanup-roadmap.md`. The `case3Witness_hasBalancedPair_outOfScope`
   axiom that would close Path C is in tree but currently
   semi-orphan (no consumer reachable from the headline).

**Non-trivial actionable gaps surfaced:** **0**. Every observation
below is either (a) already known parked work tracked in the Path C
roadmap, (b) a stale research-only doc whose predictions have been
overtaken by completed work, or (c) a per-occurrence note for the
secondary (older / public-release) `one_third` repo, which has its own
status doc and is not on the active development path.

The secondary repo `one_third` is a public-release scaffold that
retains the same structural claims via two **accepted external
sorries** (`Dilworth.hasChainCover_of_hasWidth` and
`Step8.LayeredBalanced.bipartiteBalanced` for FKG/GYY); see its own
`lean/README.md` for that disposition.

---

## §2 `sorry` / `admit` inventory

### Primary repo (`one_third_width_three`)

`find lean -name '*.lean' | xargs grep -nE '\b(sorry|admit)\b'` returned
ten matches; **zero** are real code-level occurrences. Every match is
inside a docstring, a comment, or a `\admit` mathematical-English usage
("`P` admits a balanced pair").

| File:line | Match | Classification |
|---|---|---|
| `Bridge.lean:65` | "All proofs are sorry-free." | docstring |
| `Step3/LocalSign.lean:46` | "proved sorry-free from the abstract" | docstring |
| `Step3/Step3Theorem.lean:42` | "proved sorry-free from" | docstring |
| `Step3/CommonAxes.lean:40` | "proved sorry-free from" | docstring |
| `Mathlib/Grid2D.lean:492` | "p ≤ q both inside the rectangle admit a monotone…" | English "admits" |
| `Step8/Case2FKG.lean:240` | "We do **not** introduce a `theorem` stub with `sorry`" | comment about avoidance |
| `Step8/Case3Residual.lean:119` | "introduces no new `sorry`'s, additional axioms…" | comment about avoidance |
| `Step8/LayeredBalanced.lean:433` | "the N-poset does not admit. Closing the gap…" | English "admit" |
| `Step8/MainAssembly.lean:233` | "discharges the `sorry` of `width3_one_third_two_thirds_assembled`" | historical docstring (no current sorry) |
| `Mathlib/SimpleGraph/EdgeBoundary.lean:34` | "no `sorry`; `lake build` is green." | docstring |

**Result:** 0 real `sorry`/`admit` in the primary tree.

### Secondary repo (`one_third`)

Two real `sorry` occurrences, both **accepted external dependencies**
documented in `lean/README.md`:

| File:line | Declaration | Disposition |
|---|---|---|
| `Mathlib/Poset/Dilworth.lean:134` | `hasChainCover_of_hasWidth` | classical Dilworth, accepted external |
| `Step8/LayeredBalanced.lean:348` | `bipartiteBalanced` | FKG / Graham–Yao–Yao, accepted external |

**Note.** The primary repo `one_third_width_three` has independently
formalized both: Dilworth lives at `Mathlib/Poset/Dilworth.lean`
(`hasChainCover_of_hasWidth`, sorry-free, ~770 lines) and the FKG
infrastructure lives at `Mathlib/RelationPoset/FKG.lean` and
`Mathlib/LinearExtension/FKG.lean`. The secondary repo's two sorries
are not gaps in the active development line — they are the public
scaffold's accepted-deferral disposition.

---

## §3 Custom axiom inventory

### Primary repo

`grep -E '^axiom '` returns **2** named project axioms; both are
exhaustively documented in `lean/AXIOMS.md`.

| Axiom | File | Source | Status | Consumers |
|---|---|---|---|---|
| `OneThird.LinearExt.brightwell_sharp_centred` | `Mathlib/LinearExtension/BrightwellAxiom.lean:159` | external (Brightwell 1999 §4 + Kahn–Saks 1984 Lemma 2.2) | retained per `mg-b699` decision | `lem:one-elem-perturb`, `lem:exc-perturb`, transitively the headline |
| `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope` | `Step8/Case3Residual.lean:208` | internal (paper's `rem:enumeration` sketch, residual half of `prop:in-situ-balanced`) | retained per Path C parked decision (`mg-7261`) | `hasBalancedPair_of_case3_outOfScope` (same file) → `hStruct_of_case2_discharge` (same file); **not currently reachable from the headline `width3_one_third_two_thirds`** (see §6) |

Justification, scope-match checklists, and replacement paths are
recorded per-axiom in `lean/AXIOMS.md`. QA audits: `mg-a6a1`
(brightwell), `mg-7377` (case3Witness).

### Secondary repo

`grep -E '^axiom '` in `/Users/daniel/research/one_third/lean/` returns
**0** custom axioms.

---

## §4 Headline `#print axioms` audit

Regenerated 2026-04-27 via `lean/scripts/PrintAxiomsAudit.lean` (this
audit ships an extended version of `lean/scripts/PrintAxioms.lean`
covering all headline-shaped theorems; see also the unchanged
single-theorem baseline `lean/PRINT_AXIOMS_OUTPUT.txt`).

| Theorem | Axioms |
|---|---|
| `OneThird.width3_one_third_two_thirds` | `propext`, `Classical.choice`, `Quot.sound`, `OneThird.LinearExt.brightwell_sharp_centred` |
| `OneThird.Step8.width3_one_third_two_thirds_assembled` | `propext`, `Classical.choice`, `Quot.sound`, `OneThird.LinearExt.brightwell_sharp_centred` |
| `OneThird.width3_one_third_two_thirds_via_step8` | `propext`, `Classical.choice`, `Quot.sound`, `OneThird.LinearExt.brightwell_sharp_centred` |
| `OneThird.Step8.mainAssembly` | `propext`, `Classical.choice`, `Quot.sound` |
| `OneThird.Step8.mainAssembly_smallN` | `propext`, `Classical.choice`, `Quot.sound` |
| `OneThird.Step8.cexImpliesLowBKExpansion` | `propext`, `Classical.choice`, `Quot.sound` |
| `OneThird.counterexample_implies_low_BK_expansion` | `propext`, `Classical.choice`, `Quot.sound` |

**Observations:**

1. The recorded baseline `lean/PRINT_AXIOMS_OUTPUT.txt` (which only
   captures `width3_one_third_two_thirds`) **matches** the regenerated
   output for that theorem — no drift.
2. **`case3Witness_hasBalancedPair_outOfScope` does NOT appear in any
   headline's axiom set.** It is in tree (axiom + helper theorem
   `hasBalancedPair_of_case3_outOfScope` + composite
   `hStruct_of_case2_discharge`) but the call chain through
   `width3_one_third_two_thirds` does not reach it. The case-3 dispatch
   is currently parked behind the `hC3 : Case3Witness` *hypothesis* on
   the headline (Path C `option (δ)`); the axiom would only enter the
   transitive closure if Path C were re-attempted and the dispatch
   wired through.
3. The *intermediate* `mainAssembly`, `mainAssembly_smallN`,
   `cexImpliesLowBKExpansion`, and `counterexample_implies_low_BK_expansion`
   theorems depend only on the standard Mathlib trio. The brightwell
   axiom only enters the transitive closure when the
   `MainTheoremInputs` bundle is constructed via `mainTheoremInputsOf`
   (see `Step8/MainAssembly.lean`).

**Recommendation.** Update `lean/PRINT_AXIOMS_OUTPUT.txt` to also
record `width3_one_third_two_thirds_assembled` and
`width3_one_third_two_thirds_via_step8` as belt-and-braces tracking;
this audit's `lean/scripts/PrintAxiomsAudit.lean` is the canonical
extended form. **Not actionable as a separate `mg`** — handled by the
present audit's own commit.

---

## §5 Paper-vs-Lean cross-reference

Method: extracted all 103 LaTeX `\label{(thm|lem|prop|cor):*}` from
`step1.tex`–`step8.tex`, then `grep`'d for each label across the
primary `lean/OneThird/` tree.

**Coverage: 93 of 103 labels referenced** (90%). The 10 uncovered
labels are listed below, classified.

| Label | Source | Classification |
|---|---|---|
| `lem:1d-components` | `step2.tex` (1D component count) | auxiliary 1D lemma feeding `lem:weak-grid`'s proof; subsumed by Lean's grid infrastructure (`Mathlib/Grid2D.lean`); not separately cited |
| `lem:activation-absorb` | `step5.tex` (G4 closure) | absorbed into Step 5's bridge layer (`Step5/*.lean`); not separately cited |
| `lem:giant-component` | `step7.tex` (cocycle infrastructure) | auxiliary input to `lem:cocycle`; absorbed into Step 7 bridge |
| `lem:triple-visibility` | `step7.tex` (active-triple visibility) | auxiliary input to `lem:cocycle`; absorbed into Step 7 bridge |
| `prop:counterexample` | `step2.tex` (Striped counterexample) | paper-only negative example showing why 1D fails; not a positive claim, no Lean target |
| `prop:step6-informal` | `step6.tex` (informal version) | rhetorical informal restatement; the formal `prop:step6` is in tree |
| `prop:step7-informal` | `step7.tex` (informal version) | rhetorical informal restatement; the formal `prop:step7` is in tree |
| `sec:prop73-proof` | `step7.tex` | section anchor paired with `prop:73`, which is in tree |
| `thm:step1-cited` | `step4.tex` | re-citation of `thm:interface` from inside Step 4; original is in tree |
| `thm:step2-cited` | `step4.tex` | re-citation of `thm:step2` from inside Step 4; original is in tree |

**Coverage of headline-shaped paper claims:**

| Paper | Lean |
|---|---|
| `thm:main` (`main.tex`) | `OneThird.width3_one_third_two_thirds` |
| `thm:conclusion-main` | `OneThird.width3_one_third_two_thirds` (same statement, different name) |
| `thm:main-step8` | `OneThird.Step8.width3_one_third_two_thirds_assembled` |
| `thm:cex-implies-low-expansion` | `OneThird.counterexample_implies_low_BK_expansion` + `OneThird.Step8.cexImpliesLowBKExpansion` |
| `thm:interface` (Step 1) | `OneThird.localInterfaceTheorem` (`RichPair.lean`) |
| `thm:step2` | `OneThird.Step2.thm_step2` (`Step2/`) |
| `thm:step3` | `OneThird.Step3.thm_step3` (`Step3/Step3Theorem.lean`) |
| `thm:step4` | `OneThird.Step4.thm_step4` (`Step4/`) |
| `thm:step5` | `OneThird.Step5.thm_step5` (`Step5/`) |
| `thm:step6` | `OneThird.Step6.thm_step6` (`Step6/`) |
| `thm:step7` | `OneThird.Step7.thm_step7` (`Step7/`) |

All paper-level theorems and the named step-level propositions
(`prop:G1`, `prop:G2`, `prop:G2-step4`, `prop:step5`, `prop:step6`,
`prop:step7`) are covered. **No paper claim missing in tree.**

---

## §6 Orphan infrastructure

These items are **expected per the spec** as "Path C arc's parked work
(e.g., `mg-27c2`'s `Case2FKGSubClaim`) is expected to surface as
semi-orphan; that's fine and should be noted, not flagged as a bug."

The complete set of currently-orphan (i.e., defined and built but with
no consumer reachable from `width3_one_third_two_thirds`) declarations
that came from the Path C arc:

| Declaration | File:line | Source ticket | Disposition |
|---|---|---|---|
| `case3Witness_hasBalancedPair_outOfScope` (axiom) | `Step8/Case3Residual.lean:208` | `mg-b846` (A8-S3) | parked Path C; would re-enter call chain if `hC3` were dropped |
| `hasBalancedPair_of_case3_outOfScope` (theorem) | `Step8/Case3Residual.lean:228` | `mg-b846` | direct re-export of the axiom |
| `hStruct_of_case2_discharge` (theorem) | `Step8/Case3Residual.lean:265` | `mg-b846` | composed dispatch (Case 1 / Case 2 / Case 3) |
| `Case2FKGSubClaim` (structure) | `Step8/Case2Rotation.lean:772` | `mg-27c2` | bundled chain-form FKG sub-claim |
| `strictCase2Witness_balanced_under_FKG` | `Step8/Case2Rotation.lean:870` | `mg-27c2` | conditional Case 2 discharge under FKG sub-claim |
| `case2Witness_balanced_under_FKG` | `Step8/Case2Rotation.lean:894` | `mg-27c2` | the `Case2Witness L → HasBalancedPair α` form expected by `hStruct_of_case2_discharge` |
| `OrdinalDecomp.windowOfPairAt` (def) | `Step8/WindowDecomp.lean:375` | `mg-2e58` | maximal-valid window cutoff selector |
| `OrdinalDecomp.windowOfPairAt_mem_mid_left/_right` | `Step8/WindowDecomp.lean:394`, `:416` | `mg-2e58` | membership lemmas for the window |
| `OrdinalDecomp.hasBalancedPair_lift_lower/_upper` | `Mathlib/LinearExtension/Subtype.lean:1227`, `:1237` | `mg-7f06` | symmetric lifts (the `Mid` lift was already wired) |
| `Step8.hasBalancedPair_of_layered_strongInduction_width3` | `Step8/LayerOrdinal.lean:472` | `mg-a735` | F3 framework width-3-threaded |
| `_le` corollary | `Step8/LayerOrdinal.lean:521` | `mg-a735` | bound-form variant |
| `Case3Enum.allBalanced_imp_enumPosetsFor` (outer-loop bridge) | `Step8/Case3Enum/AllBalancedBridge.lean:218` | `mg-26bb` | Bool→Prop bridge unrolling F5a's outer `bandSizesGen` loop |

**Disposition.** All twelve are documented in
`docs/path-c-cleanup-roadmap.md` §4 ("Infrastructure that landed and
remains useful") as "independently useful for future Step-8 / layered-
poset work and should not be reverted." Their orphan status reflects
the parked Path C decision (`option (δ)`), not a build/audit oversight.

**No recommended action.** Per the spec, these are noted, not flagged.

---

## §7 `MATHLIB_GAPS.md` cross-check

Both repos carry an identical `lean/MATHLIB_GAPS.md`. The document is
explicitly self-described as a **research-only** snapshot dated
**2026-04-19** ("a pre-formalization scoping doc") and **predates** the
substantial scaffold + proof landings in 2026-04-19→2026-04-27.

The doc's predictions vs. current state:

| Item | Doc's claim | Current primary state |
|---|---|---|
| B1 `width(P)` | NOT IN MATHLIB | **Closed.** `Mathlib/Poset/Width.lean` |
| B2 Dilworth | NOT IN MATHLIB | **Closed.** `Mathlib/Poset/Dilworth.lean` (`hasChainCover_of_hasWidth`, sorry-free, ~770 lines) |
| B3 `LinearExt` `Fintype` | NOT IN MATHLIB | **Closed.** `Mathlib/LinearExtension/Fintype.lean` |
| B4 `probLT` | NOT IN MATHLIB | **Closed.** `LinearExtension.lean` |
| B6 indecomposable poset | NOT IN MATHLIB | **Closed.** `Mathlib/Poset/Indecomposable.lean` |
| B7 ordinal sum | PARTIAL | **Closed.** Used throughout Step 8 |
| C3 `edgeBoundary` | PARTIAL | **Closed.** `Mathlib/SimpleGraph/EdgeBoundary.lean` |
| C4 BK graph | NOT IN MATHLIB | **Closed.** `Mathlib/BKGraph.lean` + `LinearExtension.lean` |
| C5 volume / C6 conductance | NOT IN MATHLIB | **Closed.** `LinearExtension.lean` |
| C7 BK connectivity | NOT IN MATHLIB | **Closed.** `Mathlib/BKGraph.lean` |
| D2 Dirichlet form | NOT IN MATHLIB | **Closed.** `Mathlib/DirichletForm.lean` |
| D4 indicator Cheeger | NOT IN MATHLIB | **Closed.** Step 8 (`lem:dirichlet-conductance`) |
| F2/F4/F5/F6/F7 | NOT IN MATHLIB / PARTIAL | **Closed.** `Mathlib/Grid2D.lean` |
| Step 7 `lem:cocycle` | "hard, blocked on math writeup" | **Closed.** Step 7 in tree |
| All step-level theorems | "missing entirely from scaffold" | **Closed.** All in tree |

**Drift verdict.** The document's predictions have been comprehensively
overtaken by completed work. No claim in `MATHLIB_GAPS.md` is currently
load-bearing as a **gap tracker**; it survives only as a historical
research snapshot of the 2026-04-19 scoping pass.

**Recommendation.** Either (a) leave as-is with a one-line preamble
noting "snapshot dated 2026-04-19; predictions superseded by subsequent
scaffold + proof work, see `lean/AXIOMS.md` and
`docs/path-c-cleanup-roadmap.md` for current state," or (b) move to
`docs/historical/MATHLIB_GAPS-2026-04-19.md` for archival. **Not
actionable as a follow-on `mg`** — this is a documentation hygiene
choice for the maintainer; either disposition preserves the historical
record.

---

## §8 Recommendations

This audit produced **zero non-trivial actionable gaps**. The
six-step sweep confirms that the primary repo
`one_third_width_three` is structurally complete in the sense
articulated by the spec ("If the audit shows the proof IS complete
modulo the parked Path C cleanup, that's the meaningful deliverable
— file the audit doc and the work item is done.").

### Already-known non-actionable observations (no `mg` filed)

These are recorded for context, not for follow-on dispatch:

* **`brightwell_sharp_centred` retained.** `mg-b699` decision; replacement
  path `lean/AXIOMS.md` documents the route (Kahn–Saks per-term covariance
  + FKG transport, ~500–800 LoC). Not a blocker for any current consumer.
* **Path C cleanup parked.** `option (δ)` per `mg-7261` /
  `docs/path-c-cleanup-roadmap.md`. The `case3Witness_hasBalancedPair_outOfScope`
  axiom is in tree but currently semi-orphan (no consumer reaches
  it from the headline). Re-attempt blocked on ~300–500 LoC of
  compound-automorphism / K=2 finite-enumerator infrastructure.
* **MATHLIB_GAPS.md is stale.** Documentation hygiene choice;
  either preface with a note or archive. No follow-on ticket.
* **Secondary repo `one_third` retains 2 accepted external sorries.**
  Documented in `lean/README.md`; not on the active development line.

### One-line documentation update (handled by this commit)

* **Extend `lean/PRINT_AXIOMS_OUTPUT.txt` baseline coverage.** Add
  `width3_one_third_two_thirds_assembled` and
  `width3_one_third_two_thirds_via_step8` alongside the existing
  `width3_one_third_two_thirds` entry; ship the audit's
  `lean/scripts/PrintAxiomsAudit.lean` as the extended-form generator.
  Done in this commit.

### Follow-on `mg` tickets

**None.** The "one `mg` per non-trivial gap" provision of the spec
applies to actionable gaps surfaced by the audit; this audit surfaces
none. The two known parked items (Brightwell port, Path C cleanup) are
already tracked under `mg-b699` and `mg-5f0c` respectively.

---

## Appendix A — Audit method

* **§2 sorry/admit:** `find lean -name '*.lean' | xargs grep -nE '\b(sorry|admit)\b'` in both repos, manual classification.
* **§3 axioms:** `grep -nE '^axiom |^[[:space:]]+axiom '` in both repos, cross-ref against `lean/AXIOMS.md`.
* **§4 #print axioms:** `lean/scripts/PrintAxiomsAudit.lean` (this commit), run via `lake env lean`. `lake build OneThird` rebuilds clean (1403 jobs).
* **§5 paper-vs-Lean:** extracted all `\label{(thm|lem|prop|cor):*}` from `step1.tex`–`step8.tex`; cross-ref against `grep -E "(thm|lem|prop|cor):"` over `lean/OneThird/`.
* **§6 orphan check:** for each Path C–era theorem/def, `grep -rn` for external consumers; flagged where the only reference is internal docstring or self-citation.
* **§7 MATHLIB_GAPS.md:** read both repos' copies (identical), compared each predicted item to current `lean/OneThird/Mathlib/` and `lean/OneThird/Step*/`.
* **Build-time:** `lake build OneThird` ~3 min wall after `lake exe cache get` (3 already-decompressed mathlib oleans, 8226 fetched).

## Appendix B — Files touched by this audit

* `docs/formalization-completeness-audit.md` — this document.
* `lean/scripts/PrintAxiomsAudit.lean` — extended `#print axioms` script for headline-shaped theorems.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — extended baseline (now also records `_assembled` and `_via_step8`).
