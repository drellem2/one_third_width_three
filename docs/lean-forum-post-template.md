# Forum-post template

A paste-able 3-5 paragraph forum / Zulip announcement for the
[`one_third_width_three`](https://github.com/drellem2/one_third_width_three)
repository. Lightly edit the salutation / venue framing as
appropriate; the body below is calibrated to the actual claim shape
and matches the disclosures in
[`docs/lean-forum-publication-readiness.md`](lean-forum-publication-readiness.md)
and in the README's "Please read this before citing" section.

The claim shape, axiom count, and build instructions in the
template are calibrated to the **post-Option-C-Stage-2B**
(`mg-8c72`, commit `16d26ef`, 2026-05-05) state, in which the
historical `hC3 : Step8.Case3Witness` Prop-level parameter has
been discharged as a Lean theorem
(`Step8.OptionC.Case3Witness_proof`) and the public headline
`OneThird.width3_one_third_two_thirds` is **unconditional**
modulo `hP : HasWidthAtMost α 3` and `hNonChain : ¬ IsChainPoset
α` (matching the paper's `thm:main` signature exactly). The
trust surface is the four-category list in the post body below:
mathlib classical foundations + the Brightwell external bound +
the paper-internal `rem:enumeration` Case-3 residual sketch +
Lean's `native_decide` compiler trust on five finite enumerations.

Calibration provenance:

* **Option-C Stage 2A — `LayeredDecomposition.compactify`**
  (`mg-2a56`, commit `e4ffe2d`, 2026-05-05).
* **Option-C K=2 substantive closure — `option_c_K2_closure`**
  (`mg-01ec`, commit `c403216`, 2026-05-05). The K=2 leaf of the
  F3 K-dispatch is a finite `native_decide`-backed Bool
  certificate (`case2_certificate`) plus a Bool→Prop bridge,
  bypassing the provably-false mg-27c2 `Case2FKGSubClaim`
  defect entirely.
* **Option-C Stage 2B — `Case3WitnessProof`** (`mg-8c72`,
  commit `16d26ef`, 2026-05-05). Candidate A''-tightened
  `Step8.Case3Witness.{u}` discharged as a Lean theorem;
  K ≥ 3 leaves consume `case3Witness_hasBalancedPair_outOfScope`
  (paper-internal axiom, faithful transcription of
  `rem:enumeration`).
* **Forum-readiness validation — `mg-5cd8`** (commit `ddbb933`,
  2026-05-06). Build green (1409 jobs, 632 s cold);
  `#print axioms` matches `lean/PRINT_AXIOMS_OUTPUT.txt`
  byte-for-byte; all five `native_decide` invocations audited
  faithful; AMBER on doc-drift only (this template's
  pre-Stage-2B framing). Disposition-B amendment confirms
  `case3Witness_hasBalancedPair_outOfScope` STAYS as a named
  project axiom; replacement port is **deferred indefinitely**.

If a future change to the Lean tree changes the headline
signature, drops or replaces either project axiom, removes any
`native_decide` certificate, or closes the SubClaim defect, revise
this template before posting.

---

## Template (paste verbatim or lightly edit)

> **A Lean 4 formalization of a structural proof of the 1/3–2/3 conjecture for width-3 posets**
>
> I have a Lean 4 formalization of a candidate structural proof of
> the width-3 case of the 1/3–2/3 conjecture (Kislitsyn 1968 /
> Fredman 1976 / Linial 1984 — every finite non-chain poset has an
> incomparable pair `(x, y)` with `1/3 ≤ Pr[x <_L y] ≤ 2/3` under
> the uniform linear-extension measure). The repository is at
> [github.com/drellem2/one_third_width_three](https://github.com/drellem2/one_third_width_three).
> The argument operates on the Bubley–Karzanov random walk on linear
> extensions and uses a Cheeger-type dichotomy to rule out a
> low-conductance cut that any width-3 counterexample would have to
> produce; the LaTeX paper is in [`main.pdf`](https://github.com/drellem2/one_third_width_three/blob/main/main.pdf).
> I'm posting here primarily for Lean-side eyes on the formalization;
> mathematical critique on the LaTeX is also welcome through GitHub
> issues.
>
> **What the Lean side proves and what it does not.** The headline
> theorem is `OneThird.width3_one_third_two_thirds` in
> [`lean/OneThird/MainTheorem.lean`](https://github.com/drellem2/one_third_width_three/blob/main/lean/OneThird/MainTheorem.lean).
> The Lean theorem matches the paper's `thm:main` signature exactly
> (modulo `[Fintype]` / `[DecidableEq]`): width ≤ 3 plus non-chain
> implies a balanced incomparable pair. There is no Prop-level
> hypothesis to supply — the formalization is **hypothesis-free** as
> of Option-C Stage 2B (`mg-8c72`, 2026-05-05), which discharged the
> historical `Step8.Case3Witness` universal as a Lean theorem.
>
> The trust surface for this headline factors into four categories:
>
> * **Mathlib classical foundations** (`propext`, `Classical.choice`,
>   `Quot.sound`) — the standard foundations underlying essentially
>   every classical mathlib theorem.
> * **External published bound — Brightwell 1999 §4 + Kahn–Saks 1984
>   Lemma 2.2.** The named project axiom
>   `OneThird.LinearExt.brightwell_sharp_centred` transcribes the
>   sharp centred bound `|Σ_{L' ∈ A}(f(L') − f̄)| ≤ 2N/m`, derived
>   in the paper at `step8.tex:1046–1276` from FKG / Ahlswede–Daykin
>   plus the Kahn–Saks per-term covariance step. The axiom matches a
>   peer-reviewed published result (Brightwell, *Discrete Mathematics*
>   201 (1999), §4, Theorem 4.1, combined with Kahn–Saks, *Order* 1
>   (1984), Lemma 2.2); transcription is faithful, with QA-fixed
>   off-by-one issues recorded in
>   [`lean/AXIOMS.md`](https://github.com/drellem2/one_third_width_three/blob/main/lean/AXIOMS.md)
>   §1. Retained as an axiom per `mg-b699`; replacement (a per-term
>   Kahn–Saks covariance bound on the product distributive lattice
>   `L(α) × {1, …, m}`, ~500–800 LoC of mathlib-tier infrastructure)
>   is open future work, orthogonal to the structural proof.
> * **Paper-internal `rem:enumeration` Case-3 residual sketch.** The
>   second named project axiom
>   `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`
>   transcribes this paper's own `rem:enumeration` sketch
>   (`step8.tex:3157-3173`) for the residual `¬ InCase3Scope`
>   parameter range of `prop:in-situ-balanced` Case 3. Unlike the
>   Brightwell axiom this is **paper-internal**, not an external
>   citation — the paper sketch is genuinely a sketch (not a
>   fleshed-out proof), and replacing the axiom with a Lean proof
>   requires the band-restricted Case 2 FKG sub-coupling sketched in
>   `rem:enumeration` (the same probability-form cross-poset FKG
>   infrastructure deferred under A8-S2-cont, `mg-8801`, ~2000–3500
>   LoC of paper-tier mathematical work). The QA verdict (`mg-7377`)
>   is **axiom is faithful**: the hypotheses match
>   `Step8.bounded_irreducible_balanced_hybrid` restricted to
>   `¬ InCase3Scope` (with the F5 C2-leaf size cap `|α| ≤ 6w + 6`
>   strictly tighter than the paper's `|Q| ≤ 9w + 3`, so the axiom
>   is no stronger than the paper's claim), and the conclusion
>   matches `prop:in-situ-balanced` exactly. Per the `mg-5cd8`
>   forum-readiness disposition-B amendment, the port is deferred
>   indefinitely; the replacement path is open future work in
>   [`lean/AXIOMS.md`](https://github.com/drellem2/one_third_width_three/blob/main/lean/AXIOMS.md)
>   §2. A separate latex-first artifact (`mg-75ef`, 2026-05-06)
>   provides a structured math-side filling-in of the
>   `rem:enumeration` sketch modulo the deferred FKG infrastructure;
>   it forward-cites for any future replacement effort but does not
>   retire the axiom. Disclosure tone: this is honestly a
>   paper-internal sketch with rigorous filling-in deferred at the
>   FKG-infrastructure level, not an "axiom we couldn't prove" — and
>   the port is parked indefinitely, not awaiting an upcoming
>   committed effort.
> * **Lean compiler trust on five finite enumerations
>   (`native_decide`, standard Lean practice).** The headline's
>   `#print axioms` output additionally lists five
>   `_native.native_decide.ax_1_1` entries — per-decision instances
>   of the standard `Lean.ofReduceBool` axiom underlying
>   `native_decide`. They underwrite the F5a Case-3 enumeration
>   certificate (`Step8.Case3Enum.case3_certificate`, four
>   `native_decide` invocations at `w ∈ {1, 2, 3, 4}`) and the
>   Option-C Stage-1 K=2 closure certificate
>   (`Step8.OptionC.case2_certificate`, one invocation). All five
>   were independently audited as faithful Bool encodings of the
>   underlying math claims by the `mg-5cd8` forum-readiness pass
>   (no Bool-predicate-vs-math mismatch of the mg-a79e form). Trust
>   surface: "the Lean compiler evaluates Bool decidable predicates
>   correctly," same standing as `decide` for any tree using
>   `native_decide` to discharge a finite case analysis.
>
> The verbatim `#print axioms` output (matching
> [`lean/PRINT_AXIOMS_OUTPUT.txt`](https://github.com/drellem2/one_third_width_three/blob/main/lean/PRINT_AXIOMS_OUTPUT.txt)
> byte-for-byte from a fresh build):
>
> ```
> 'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
>  Classical.choice,
>  Quot.sound,
>  OneThird.LinearExt.brightwell_sharp_centred,
>  OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope,
>  OneThird.Step8.Case3Enum.case3_balanced_w1._native.native_decide.ax_1_1,
>  OneThird.Step8.Case3Enum.case3_balanced_w2._native.native_decide.ax_1_1,
>  OneThird.Step8.Case3Enum.case3_balanced_w3._native.native_decide.ax_1_1,
>  OneThird.Step8.Case3Enum.case3_balanced_w4._native.native_decide.ax_1_1,
>  OneThird.Step8.OptionC.case2_certificate._native.native_decide.ax_1_1]
> ```
>
> No `sorryAx` or unaudited project axiom appears anywhere in the
> headline's dependencies. The full side-by-side reading of the
> Lean signature against the paper's `thm:main`, plus the
> per-axiom scope-match checklist, is in
> [`docs/lean-forum-publication-readiness.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/lean-forum-publication-readiness.md)
> and
> [`lean/AXIOMS.md`](https://github.com/drellem2/one_third_width_three/blob/main/lean/AXIOMS.md).
>
> A note on the historical `hC3` parameter: prior versions of the
> headline carried `hC3 : Step8.Case3Witness` as a Prop-level
> hypothesis — a universally-quantified Case-3 discharge that the
> paper's `prop:in-situ-balanced` Case 3 was parametrically
> reduced to. That parameter was retained through the option (δ)
> park decision (2026-04-27, `mg-94fd`) because no in-tree
> simpler discharge survived three independent scoping arcs (the
> F1 / F2 / F3 structural reasons — cardinality obstruction at
> case-2-strict; Brightwell `|Q| ≤ 6` vacuity at K=2; the
> published `[0.276, 1/3)` Kahn–Linial gap — are synthesised in
> [`docs/why-hC3-is-structural.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/why-hC3-is-structural.md)).
> Option-C Stage 2A (`mg-2a56`, `LayeredDecomposition.compactify`)
> and Stage 2B (`mg-8c72`, `Case3WitnessProof`) closed the *outer*
> universal as a Lean theorem by routing the residual leaves
> through the `case3Witness_hasBalancedPair_outOfScope` axiom for
> K ≥ 3, the `option_c_K2_closure` Bool certificate (`mg-01ec`)
> for K = 2, and the vacuous K = 1 case under Candidate A''
> "Injective band map". The same F1 / F2 / F3 framework now
> explains why the `outOfScope` axiom is *retained* rather than
> ported — the substantive math content needed for a Lean port is
> the deferred A8-S2-cont scope.
>
> **Known in-tree issue (forum reader caveat):** mg-27c2
> `Case2FKGSubClaim` is direction-reversed; **bypassed** by the
> Option-C Stage 2B Case3WitnessProof (the K=2 leaf is now
> discharged by the `option_c_K2_closure` Bool certificate
> `mg-01ec`, not by the SubClaim path). Headline
> `width3_one_third_two_thirds` is unaffected. See
> [`lean-forum-publication-readiness.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/lean-forum-publication-readiness.md)
> §5 "Known in-tree issue". In more detail: an earlier audit
> (polecat `pc-a79e`, commit `64f2d87`,
> [`docs/a8-path-b-block-and-report-status.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/a8-path-b-block-and-report-status.md))
> identified that `Case2FKGSubClaim` (a hypothesis structure on the
> Case 2 within-band ⪯-chain dispatch in
> [`lean/OneThird/Step8/Case2Rotation.lean`](https://github.com/drellem2/one_third_width_three/blob/main/lean/OneThird/Step8/Case2Rotation.lean))
> is **provably false** on natural inputs (a 3-element
> counterexample with `K = 2`, `w = 1` gives `probLT a a' = 1/3`,
> violating the SubClaim's `1/2 ≤ probLT a a'`). An η₄ restate
> attempt (`mg-b0de`, commit `8f97133`,
> [`docs/a8-s2-restate-block-and-report-status.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/a8-s2-restate-block-and-report-status.md))
> blocked because the ≤ 2/3 upper bound from chain-swap requires
> `|Q| ≥ 12` but K=2 has `|Q| ≤ 6`. The conditional theorems
> `case2Witness_balanced_under_FKG` and
> `strictCase2Witness_m2_balanced` predicated on this SubClaim are
> therefore technically-correct-but-vacuous implications on a false
> antecedent, and remain in tree as legacy artifacts. **The
> headline `width3_one_third_two_thirds` is unaffected** — its K=2
> leaf is the `option_c_K2_closure` Bool certificate (a
> `native_decide` enumeration plus Bool→Prop bridge), not the
> SubClaim path; its K ≥ 3 leaves consume the
> `case3Witness_hasBalancedPair_outOfScope` axiom directly. The
> `#print axioms` baseline above is current. Please do not cite
> mg-27c2's conditional Case 2 theorems as unconditional results.
>
> **Build and verify.** `lake build OneThird` succeeds in roughly
> 10 minutes wall (~ 3 min after `lake exe cache get`) on Lean
> `v4.29.1` (pinned in `lean/lean-toolchain`). The most recent
> end-to-end build (forum-readiness validation pass `mg-5cd8`,
> 2026-05-06,
> [`docs/forum-readiness-validation/build-verification.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/forum-readiness-validation/build-verification.md))
> reports 1409 lake jobs, 552 s build wall (632 s including clone
> + cache get), zero errors, zero `sorry` warnings, fresh-build
> `#print axioms` matching
> [`lean/PRINT_AXIOMS_OUTPUT.txt`](https://github.com/drellem2/one_third_width_three/blob/main/lean/PRINT_AXIOMS_OUTPUT.txt)
> byte-for-byte. The same pass independently audited all five
> `native_decide` invocations as faithful Bool encodings of the
> underlying math claims
> ([`docs/forum-readiness-validation/native-decide-audit.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/forum-readiness-validation/native-decide-audit.md)).
> Recipe:
>
> ```sh
> git clone https://github.com/drellem2/one_third_width_three.git
> cd one_third_width_three/lean
> lake exe cache get
> lake build OneThird
> ```
>
> The companion doc
> [`docs/lean-forum-publication-readiness.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/lean-forum-publication-readiness.md)
> reads the paper headline and the Lean headline side by side, pastes
> the verbatim `#print axioms` baseline, and links into the per-file
> audit in [`lean/README.md`](https://github.com/drellem2/one_third_width_three/blob/main/lean/README.md).
>
> **Status disclosures (please read before citing).** This is a
> proof candidate, not a refereed result. The author is unaffiliated
> and without a formal background in combinatorics or order theory;
> both the LaTeX proof and the Lean formalization were developed
> with substantial Anthropic-Claude assistance in a multi-agent
> orchestration setup (drafts of proof steps, Lean files, audits,
> and documentation), with the author directing, reviewing, editing,
> and bearing responsibility for the final content; if you consider
> AI-assisted mathematics a categorical disqualifier you should
> stop here. The proof has not been read end-to-end by an external
> expert or submitted to a journal. External review is the next step,
> not a finished gate; the README is candid about all of the above
> ([`README.md` § "Please read this before citing"](https://github.com/drellem2/one_third_width_three/blob/main/README.md#please-read-this-before-citing)).
> The most useful response from this venue is Lean-side critique:
> issues on the GitHub repo, anchored to a file and line, are the
> preferred channel.
