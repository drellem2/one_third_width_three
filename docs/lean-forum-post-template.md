# Forum-post template

A paste-able 3-5 paragraph forum / Zulip announcement for the
[`one_third_width_three`](https://github.com/drellem2/one_third_width_three)
repository. Lightly edit the salutation / venue framing as
appropriate; the body below is calibrated to the actual claim shape
and matches the disclosures in
[`docs/lean-forum-publication-readiness.md`](lean-forum-publication-readiness.md)
and in the README's "Please read this before citing" section.

The claim shape, axiom count, and build instructions in the template
are calibrated to the option (δ) park decision (2026-04-27) and the
formalization-completeness audit (`mg-49a4`, commit `6af280c`). If a
future change to the Lean tree drops `hC3` or the Brightwell axiom,
revise this template before posting.

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
> Its statement is paper-faithful **modulo a documented Prop-level
> hypothesis `hC3 : Step8.Case3Witness`** — the universally-quantified
> discharge of the within-band antichain Case 3 of the paper's
> `prop:in-situ-balanced` — which a consumer of the headline must
> supply or carry. Closing `hC3` inside the formalization is open
> math at the time of writing: it requires roughly 300–500 LoC of
> compound-automorphism infrastructure that does not exist in the
> tree (the minimal failing instance is the four-element N-poset, where
> the balanced-pair witness comes from a compound transposition that
> the in-tree rotation argument cannot produce). The cleanup arc that
> attempted the discharge across four polecat rounds is documented in
> [`docs/path-c-cleanup-roadmap.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/path-c-cleanup-roadmap.md);
> the parked decision is firm pending either a mathlib-side
> compound-automorphism primitive or a focused multi-week pass.
>
> **Axioms.** `#print axioms OneThird.width3_one_third_two_thirds`
> reports `[propext, Classical.choice, Quot.sound,
> OneThird.LinearExt.brightwell_sharp_centred]`. The first three are
> the mathlib-standard classical foundations; the fourth is the
> **only** project-specific axiom in the headline's transitive closure
> and is a faithful transcription of a published external bound
> (Brightwell 1999 §4 combined with Kahn–Saks 1984 Lemma 2.2,
> for the sharp centred bound `|Σ_{L' ∈ A}(f(L') - f̄)| ≤ 2N/m`
> derived in the paper via FKG / Ahlswede–Daykin + per-term
> covariance). It is retained as an axiom rather than ported per a
> deliberate decision (`mg-b699`); the per-axiom scope-match audit
> and the open replacement path are in
> [`lean/AXIOMS.md`](https://github.com/drellem2/one_third_width_three/blob/main/lean/AXIOMS.md).
> No `sorryAx` or unaudited project axiom appears anywhere in the
> headline's dependencies.
>
> **Build and verify.** `lake build OneThird` succeeds in roughly 3
> minutes wall after `lake exe cache get` on Lean
> `v4.29.1` (pinned in `lean/lean-toolchain`); a recent
> formalization-completeness audit (`mg-49a4`,
> [`docs/formalization-completeness-audit.md`](https://github.com/drellem2/one_third_width_three/blob/main/docs/formalization-completeness-audit.md))
> confirms zero `sorry`/`admit` in the production tree, two named
> project axioms in the repo (one of which is currently semi-orphan
> and not reachable from the headline), and full paper-vs-Lean
> coverage for every step-level theorem. Recipe:
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
