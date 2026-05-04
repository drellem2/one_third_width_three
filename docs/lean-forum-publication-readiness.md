# Lean forum publication readiness

This document records, in a single place and at the level of fidelity
appropriate for a public lean Zulip / forum announcement, exactly what
the Lean formalization in [`lean/`](../lean/) proves and what it does
not. It is the canonical companion to a forum post about this
repository: the [forum-post template](lean-forum-post-template.md)
quotes from this doc rather than restating the claim shape.

The intent is that a Lean / formal-methods reader can verify the
claim end-to-end without needing to reverse-engineer the discrepancy
between the paper's `thm:main` and the Lean-side headline theorem.

**Status as of 2026-05-04.** Build is clean; the headline depends on
one named project axiom (Brightwell, transcribing a published
external result) plus Lean's standard classical-foundations trio,
and carries one Prop-level hypothesis (`hC3`) that pins a
parametrically-quantified discharge of the paper's `prop:in-situ-balanced`
Case 3. Both residuals are documented below and disclosed verbatim
in the forum-post template.

**Update relative to the 2026-04-27 calibration.** Two parallel
cleanup tracks closed on 2026-05-04, both block-and-reporting and
both confirming that PATH A (ship the documented narrower public
claim under the reframed wording established in `mg-9e50` / `mg-457c`)
is the **settled** outcome — not just the default after a single
park decision. The fresh evidence:

* **Track 1 (`mg-b666`, compound-automorphism extension on `main`,
  commit `5dff5e4`,
  [`docs/path-c-track-1-status-1.md`](path-c-track-1-status-1.md)).**
  Found a structural cardinality obstruction (§2 of that doc): no
  order-preserving permutation `σ : α ≃ α` with `σ a = a'` can
  exist when `upper(a) ⊊ upper(a')` strictly, because such a `σ`
  would restrict to a bijection forcing `|upper(a)| = |upper(a')|`.
  This rules out compound-automorphism extension to case-2-strict
  for **any** construction — triple-orbit, partial-injection, and
  different-pair variants all fail. The obstruction is structural,
  not effort-bound.
* **Track 2 (`mg-80ab`, math-simp arc 2.0 on branch
  `math-simp-arc-2.0`, commit `b1ac92b`,
  [`docs/math-simp-arc-2.0/scoping.md`](math-simp-arc-2.0/scoping.md)).**
  Scoped four candidate fresh framings (audit-bar revisit / direct
  probability bound / restrict-and-dispatch / alternate proof
  program) and found **zero GREEN framings** within polecat scoping
  authority. The probability-bound route is also blocked: the
  in-tree Brightwell sharp centred bound is vacuous at `|α| ≤ 6`,
  which is exactly the K=2 regime where the obstruction lives.

The Future-revival pathways in §5 below are unchanged in substance
(A8-S2-cont infrastructure, math-simplification experiment in a
future product cycle), but the math-simplification pathway is now
narrower than the 2026-04-27 framing implied: the natural fresh
framings have been surveyed and found wanting, so any successful
future math-simp must come from outside the four candidates already
audited. The §5 wording has been updated accordingly (see §5 of
this doc).

---

## 1. The two headline statements, side by side

### 1a. Paper headline (`thm:main`, `main.tex:230-241`)

```latex
\begin{theorem}[Main theorem, conditional on Hypothesis~A]
\label{thm:main}
Assume the arithmetic richness Hypothesis~A of Step~8
(Hypothesis~\ref{hyp:arith}). Let $P$ be a finite poset of width at
most~$3$ that is not a chain. Then $P$ admits a pair $(x,y)$ of
incomparable elements with
\[
  \tfrac{1}{3} \;\le\; \Pr[x<y] \;\le\; \tfrac{2}{3}.
\]
Equivalently, $\delta(P)\ge 1/3$ for every non-chain poset $P$ of
width~$\le 3$, under Hypothesis~A.
\end{theorem}
```

The paper's residual is the **arithmetic-richness Hypothesis~A**
(`step8.tex:505-516`), an `n`-independent inequality on the
sealed Step 5/6/7 constants
$\gamma^2\, c_5(T)\, c_6\, \delta_0(\gamma) \ge 8$ that pins down
the large-`n` tail of the small-`γ` regime via the BK-expansion
cascade. The structural argument of the paper is unconditional on
the Kahn–Linial regime ($\gamma \ge 1/3 - \delta_{\mathrm{KL}}$) and
on the finite-`n` regime ($n \le n_0(\gamma, T)$); Hypothesis~A
covers the intermediate large-`n` small-`γ` band.

### 1b. Lean headline (`width3_one_third_two_thirds`, `lean/OneThird/MainTheorem.lean:52-57`)

```lean
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α :=
  Step8.width3_one_third_two_thirds_assembled hP hNonChain hC3
```

The Lean residual is the **Prop-level hypothesis `hC3 :
Step8.Case3Witness`**, a universally-quantified discharge of the
within-band antichain Case 3 of the paper's `prop:in-situ-balanced`
(`step8.tex:2965-3048`). The full definition is at
`lean/OneThird/Step8/LayeredBalanced.lean:438-444`:

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β
```

`HasBalancedPair α` (`lean/OneThird/Poset.lean`) unfolds to: there
exist incomparable `x y : α` with
`1/3 ≤ probLT (x, y) ≤ 2/3` under the uniform linear-extension
measure — the same conclusion as `thm:main`.

### 1c. Side-by-side reading

The Lean headline carries `hC3` as an additional Prop-level
hypothesis that the paper's `thm:main` does not carry; the paper's
`thm:main` carries Hypothesis~A as an arithmetic side condition that
the Lean headline does not carry. **The two residuals do not coincide
and one is not a routine translation of the other.**

* The paper's residual (Hypothesis~A) is an arithmetic-richness
  inequality on the Step 5/6/7 cascade constants. It is `n`-independent
  but `γ`-quantified, and it pins the large-`n` tail of the small-`γ`
  regime via BK expansion. It is open mathematically: not derived from
  Steps 1–7, not formally verified, not refuted.
* The Lean residual (`hC3`) is a universally-quantified Prop-level
  predicate over layered width-3 non-chain `β`'s, asserting that the
  Case 3 dispatch of `prop:in-situ-balanced` (within-band antichain)
  always produces a balanced pair. It is a constructive parametric
  hypothesis that any caller of the headline must supply.

In particular: **the Lean formalization is not a complete proof of
`thm:main` modulo Hypothesis~A**. The two trees parametrise the open
piece differently. A consumer of the Lean headline must independently
discharge `hC3`; the question of whether `hC3` follows from
Hypothesis~A (or vice versa) is not in scope of this formalization.

The honest summary, which the forum-post template uses, is:

> The structural argument of Steps 1–8 is fully formalized in Lean.
> The headline theorem `width3_one_third_two_thirds` is paper-faithful
> modulo (i) one named axiom transcribing a published external result
> (the Brightwell / Kahn–Saks sharp centred bound) and (ii) one
> documented Prop-level hypothesis `hC3 : Case3Witness` discharging
> the within-band antichain Case 3 of `prop:in-situ-balanced`. The
> paper's `thm:main` itself remains conditional on Hypothesis~A
> (arithmetic richness, an open mathematical condition); the Lean
> tree replaces that conditionality with the constructive parametric
> `hC3` rather than transcribing Hypothesis~A directly.

---

## 2. What `hC3 : Case3Witness` is and why it is parked

`Case3Witness` (`lean/OneThird/Step8/LayeredBalanced.lean:438-444`)
is the **universally quantified Case-3 discharge** for layered width-3
non-chain `β`. Operationally, it asserts that for every layered
decomposition `LB` of every type `β` satisfying the F5 entry conditions
(width ≤ 3, not a chain, `|β| ≥ 2`), `β` has a balanced pair. The
F5 strong-induction inside `lem_layered_balanced` recurses on
sub-posets via `L.restrict D.Mid`, so the Case-3 discharge has to
cover an entire `∀`-family of sub-types, not a single fixed `β`.

The discharge has been attempted across four polecat rounds (mg-4a5b
→ mg-072c → mg-0fa0 → mg-94fd) under Path C cleanup, plus a follow-on
compound-automorphism build-out (mg-84f2 / mg-c0c7 / mg-02c2) and a
2026-05-04 Track 1 attempt to extend that build-out (mg-b666). The
arc shipped six pieces of substantive infrastructure (mg-9568,
mg-7f06, mg-a735, mg-27c2, mg-2e58, mg-26bb — see
`docs/path-c-cleanup-roadmap.md` §4) plus the K=2 same-band
compound-automorphism kit (`CompoundSwap.lean`, `CompoundMatching.lean`,
`BipartiteEnumGeneral.lean` — mg-84f2 / mg-c0c7 / mg-02c2). After the
round-4 firm stop-loss, pm-onethird picked **option (δ): park** —
retain `hC3` as a named hypothesis on the headline, ship the audit
as the deliverable, and revisit if the underlying mathematical
infrastructure lands later. The retention is **structural, not
effort-bound**: three independent structural facts (cardinality
obstruction; Brightwell vacuity at K=2 / `|Q| ≤ 6`; the published
`[0.276, 1/3)` Kahn–Linial gap) converge on the residual K=2 +
irreducible + w ≥ 1 + |β| ≥ 3 family in such a way that no
in-tree-derivable simpler argument has survived 21 candidate
framings across three independent scoping arcs. The unified
explanation is in
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) — the
canonical "why is the formalization conditional" entry point. The
short version:

> **F1 — Cardinality obstruction.** Order-preserving permutations
> cannot swap a strict ⪯-pair: any `σ : α ≃ α` with `σ a = a'`
> restricts to a bijection `upper(a) → upper(a')`, forcing
> `|upper(a)| = |upper(a')|` and contradicting strict inclusion.
> This rules out compound-automorphism (and its triple-orbit /
> partial-injection / different-pair variants); the minimal
> counterexample `α = {a, a', y}` with `a' < y`, `K = 2`, `w = 1`
> has trivial automorphism group, so symmetry produces zero
> witnesses while `probLT a a' = 1/3` exactly by linear-extension
> count. Audit:
> [`docs/path-c-track-1-status-1.md`](path-c-track-1-status-1.md)
> §2 (mg-b666).
>
> **F2 — Brightwell vacuity at K=2 / `|Q| ≤ 6`.** The single-element
> bound from `brightwell_sharp_centred` is `2/|Q|`; clearing the
> `≤ 2/3` target via chain-swap collapse requires `|Q| ≥ 12`, but
> K=2 has `|Q| ≤ 6`. Iterating across multiple strictness witnesses
> only worsens the bound to a harmonic sum `2 H_{|Q|} ≈ 4.9`. The
> probability-normalised cross-poset FKG bound is the deferred
> A8-S2-cont scope (~2000–3500 LoC). Audit:
> [`docs/a8-s2-restate-block-and-report-status.md`](a8-s2-restate-block-and-report-status.md)
> §3 (mg-b0de).
>
> **F3 — Published `[0.276, 1/3)` gap.** The unconditional
> Kahn–Saks → Brightwell → Kahn–Linial line tops out at
> `δ* ≥ 0.276393…` and has not closed the `[0.276…, 1/3)` gap
> in 30+ years. The width-3 specialisation has not been achieved
> without going through a Cheeger-type or equivalently structural
> argument. Audit: `main.tex` §1 (Known results, Comparison with
> previous approaches).

So no additional LoC of compound-automorphism work — even with a
hypothetical mathlib-side `MultiOrbit.swap_preserves_le` primitive
— closes the gap. The closure now requires either (i) the deferred
A8-S2-cont probability-normalised cross-poset FKG infrastructure
(~2000–3500 LoC, paper-tier mathematical work; sketched in
`docs/a8-s2-status.md` §5), (ii) a width-3-specific tightening of
the Kahn–Linial covariance bound that would close the unconditional
`δ ≥ 0.276 → 1/3` gap, or (iii) an entirely different proof
program. None of those is a "polecat-doable" arc; closure is
multi-week external work or a research-arc commitment. The headline
retains `hC3` indefinitely under that disposition. Note: this is
"no in-tree-derivable simpler argument," strictly weaker than "no
simpler argument exists" — see
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) §
"What this doc does not claim".

The full audit trail is
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) (entry
point for the structural explanation),
`docs/path-c-cleanup-roadmap.md` (entry point for the cleanup arc),
`docs/path-c-track-1-status-1.md` (Track 1 structural
impossibility), `docs/math-simp-arc-2.0/scoping.md` (Track 2 fresh
framings), `docs/math-simp-arc-3.0/scoping.md` (Track 3 strategy
revisit), plus the five round-by-round status docs from the
original four-round arc:

* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — pins the
  closure target to chain-form FKG.
* `docs/a5-g3e-fkg-route-status.md` (mg-4a5b) — round 2.
* `docs/a5-g3e-path-c-wiring-v3-status.md` (mg-072c) — round 3.
* `docs/a5-g3e-path-c-wiring-v4-status.md` (mg-0fa0) — round 4.
* `docs/a5-g3e-path-c-wiring-v5-status.md` (mg-94fd) — firm round-4
  stop-loss; option (δ) trigger.

`hC3` retention is intentional under that decision; the docstring at
`lean/OneThird/MainTheorem.lean:39-51` and the `Case3Witness` def
docstring at `lean/OneThird/Step8/LayeredBalanced.lean:420-437` both
flag it as "do not attempt to drop without first reading the
roadmap".

---

## 3. `#print axioms` — current verbatim baseline

Reproducible from a clean clone via
`cd lean && lake exe cache get && lake build OneThird`, then
`lake env lean scripts/PrintAxiomsAudit.lean`. Archived at
[`lean/PRINT_AXIOMS_OUTPUT.txt`](../lean/PRINT_AXIOMS_OUTPUT.txt):

```
'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred]
'OneThird.Step8.width3_one_third_two_thirds_assembled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred]
'OneThird.width3_one_third_two_thirds_via_step8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred]
'OneThird.Step8.mainAssembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'OneThird.Step8.mainAssembly_smallN' depends on axioms: [propext, Classical.choice, Quot.sound]
'OneThird.Step8.cexImpliesLowBKExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'OneThird.counterexample_implies_low_BK_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three of these (`propext`, `Classical.choice`, `Quot.sound`) are the
mathlib-standard classical foundations that are also depended on by
essentially every classical mathlib theorem; the fourth,
`OneThird.LinearExt.brightwell_sharp_centred`, is the only
project-specific axiom in the headline's transitive closure.

The intermediate theorems (`mainAssembly`, `mainAssembly_smallN`,
`cexImpliesLowBKExpansion`, `counterexample_implies_low_BK_expansion`)
depend only on the mathlib trio: the Brightwell axiom enters the
transitive closure only when `MainTheoremInputs` is constructed via
`mainTheoremInputsOf` for the headline assembly.

---

## 4. The `brightwell_sharp_centred` axiom

**File.** `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`

**Paper statement.** `step8.tex:1048`, `eq:sharp-centred`:
$$
\Bigl|\sum_{L' \in A}(f(L') - \bar f)\Bigr| \;\le\; \frac{2N}{m}.
$$

The paper derivation at `step8.tex:1046–1276` is itself a transcription
of two published external results combined via FKG / Ahlswede–Daykin:

* G. Brightwell, *Balanced pairs in partial orders*, Discrete
  Mathematics **201** (1999), §4, Theorem 4.1 (`main.tex:557`,
  `\bibitem{Brightwell1999}`).
* J. Kahn and M. Saks, *Balancing poset extensions*, Order **1**
  (1984), Lemma 2.2 — the single-element-perturbation lemma
  (`main.tex:530`, `\bibitem{KahnSaks1984}`).

The axiom transcribes the conclusion of the combined Brightwell /
Kahn–Saks per-term covariance argument; it does not transcribe a
novel claim of this paper. It is **retained** rather than ported,
per `mg-b699` decision recorded in
[`lean/AXIOMS.md`](../lean/AXIOMS.md), with a documented replacement
path (the per-term Kahn–Saks / Brightwell covariance bound on the
product distributive lattice $\mathcal L(\alpha) \times \{1, \dots,
m\}$, estimated at 500–800 LoC of mathlib-tier covariance / set-system
infrastructure). A scope-match checklist verifying the axiom statement
against the paper hypotheses, conclusion, and constants is in
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §1.

The decision to retain rather than port follows the standard
"import an external published bound" pattern: the structural /
combinatorial proof of the width-3 case is the credibility artifact
of this work; an independent Lean port of a 1999 published lemma
(plus the 1984 Kahn–Saks per-term covariance step) is an
infrastructure project orthogonal to the structural claim.

The axiom is auditable: every field of its Lean statement matches a
clause of the paper proof, and the QA discrepancy audit (`mg-a6a1`,
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §1.4 "Discrepancy audit") fixed
two off-by-one issues during transcription before the axiom landed.

A second named project axiom,
`OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`,
exists in the tree but is **not** reachable from the headline
`width3_one_third_two_thirds` (see §6 of the formalization-completeness
audit, `docs/formalization-completeness-audit.md`): under option (δ),
the Case-3 discharge is parked behind the `hC3` hypothesis rather than
wired through the dispatch that would consume that axiom. It is
documented in [`lean/AXIOMS.md`](../lean/AXIOMS.md) §2 for completeness.

---

## 5. Known in-tree issue: mg-27c2 `Case2FKGSubClaim` direction-reversed (η₅ park — not being fixed this iteration)

A third disclosure item, distinct from `hC3` (parked open math, §2)
and the two named project axioms (Brightwell external retain;
`case3Witness_hasBalancedPair_outOfScope` semi-orphan, §4): a
**conditional theorem** in the tree,
`case2Witness_balanced_under_FKG`
(`lean/OneThird/Step8/Case2Rotation.lean:894`, mg-27c2), and the
companion `strictCase2Witness_m2_balanced`
(`lean/OneThird/Step8/Case2Rotation.lean:813`), are predicated on
the hypothesis structure `Case2FKGSubClaim L`
(`lean/OneThird/Step8/Case2Rotation.lean:772`) whose `pair` field
is **provably false** on the natural Case 2 inputs the dispatch is
supposed to fire on. The implications themselves are technically
correct (anything follows from a false antecedent), but they are
vacuous on the strict within-band ⪯-chain pairs they target. A
forum reader auditing `Case2Rotation.lean` would absolutely spot
this; this section flags it explicitly.

**The finding.** Audited end-to-end by polecat `pc-a79e`
(commit `64f2d87`, mg-a79e); see
[`docs/a8-path-b-block-and-report-status.md`](a8-path-b-block-and-report-status.md)
for the full status doc. The `pair` field of `Case2FKGSubClaim L`
asserts `1/2 ≤ probLT a a'` for a within-band ⪯-chain pair
`(a, a')` with `upper(a) ⊆ upper(a')` and `lower(a') ⊆ lower(a)`.
`pc-a79e` constructed an explicit 3-element layered counterexample
(`α = {a, a', y}` with `a' < y`, `K = 2`, `w = 1`) satisfying every
Lean-level hypothesis of `Case2FKGSubClaim.pair` yet giving
`probLT a a' = 1/3 < 1/2` by direct enumeration of α's three valid
linear extensions. The SubClaim's `pair` field is therefore false
on natural inputs.

**Root cause: direction reversal vs `step8.tex:2855-2875`.** The
paper's chain-form FKG argument actually proves the *opposite*
direction: the chain hypothesis "`a'` has more upper edges and
fewer lower edges than `a`" gives `probLT a a' ≤ 1/2` (chain swap;
`probLT_le_half_of_chain` at
`lean/OneThird/Step8/Case2Rotation.lean:629`, already a theorem in
tree, mg-ba0c). The Lean SubClaim's `pair` field bakes in the
reverse inequality `1/2 ≤ probLT a a'`, and that direction is
mathematically wrong on the strict case. Three independent in-tree
audits had previously flagged the issue from different angles
([`docs/a8-s2-rotation-residual-status.md`](a8-s2-rotation-residual-status.md)
mg-ba0c §3,
[`docs/a8-s2-strict-witness-status.md`](a8-s2-strict-witness-status.md)
mg-43f3, plus the new mg-a79e doc); `pc-a79e` converted those
audits into an explicit counterexample and the block-and-report
verdict.

**Reachability from the headline.** `case2Witness_balanced_under_FKG`
and `strictCase2Witness_m2_balanced` are conditional on
`hFKG : Case2FKGSubClaim L`. The headline
`width3_one_third_two_thirds` does **not** consume `hFKG`: under
option (δ), the K=2 dispatch reaches the Case 2 leaf via the
parked-`hC3` path (which subsumes Case 2 inside the universally
quantified `Case3Witness` discharge), rather than via a
`hFKG`-conditional discharge. The false-antecedent theorems are
therefore **not** in the headline's transitive closure, and the
verbatim `#print axioms` baseline (§3 above) is unaffected. They
are nonetheless visible to a reader auditing `Case2Rotation.lean`,
and they would matter the moment any future wiring tried to thread
a constructed `hFKG` through the K=2 leaf.

**Iteration disposition: PARKED via η₅ — the SubClaim defect is
not being fixed in this iteration.** An η₄ restate attempt
(`mg-b0de`, filed under Daniel OVERRIDE `mg-602e`) tried to fix
the issue by (i) flipping `Case2FKGSubClaim.pair` to the correct
direction (`probLT a a' ≤ 1/2`, equivalent to chain swap and
already a theorem in tree as `probLT_le_half_of_chain` at
`lean/OneThird/Step8/Case2Rotation.lean:629`, mg-ba0c) and
(ii) deriving a separate `≤ 2/3` upper bound from Brightwell
covariance, combining the two to produce the balanced pair via
`(a', a)` rather than `(a, a')`. **The η₄ attempt blocked**: the
≤ 2/3 upper bound is not discharge-able from the existing
Brightwell + chain-swap infrastructure. The Brightwell sharp
centred bound `|p(Q) − p(Q−z)| ≤ 2/|Q|` (single-element
perturbation; `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`)
gives `Pr_Q[a < a'] ∈ [1/2 − 2/|Q|, 1/2 + 2/|Q|]`, so the
upper bound `1/2 + 2/|Q| ≤ 2/3` requires `|Q| ≥ 12`. **K=2 has
`|Q| = |α| ≤ 6`** (sum of two band sizes, each ≤ 3 by width-3
hypothesis), so the existing Brightwell bound is too weak by a
factor of 2 in the K=2 regime. The in-tree `Case2BipartiteBound`
is K=2 / w=0 only and does not cover the strict within-band ⪯-pair
case the SubClaim targets. Full audit:
[`docs/a8-s2-restate-block-and-report-status.md`](a8-s2-restate-block-and-report-status.md)
(commit `8f97133`, mg-b0de).

The pre-committed PM pivot **η₅** (drop the SubClaim discharge
path entirely; keep `hC3` on the headline) fired on receipt of
the η₄ block-and-report. The defect remains in tree and is
disclosed honestly, but no in-iteration fix is shipping.

**Future-revival pathways.** Two routes existed at η₅ park time
(2026-04-27) for closing the SubClaim defect in a later product
cycle. Both have been **further narrowed** by the 2026-05-04
closures of Tracks 1 and 2:

* **A8-S2-cont (`mg-8801`, ~2000-3500 LoC):** the deferred
  probability-form cross-poset FKG infrastructure
  (probability-normalised Pr_Q vs absolute counts; cross-poset
  monotonicity for adding/removing strictness witnesses;
  the `≤ 2/3` upper bound at K=2 follows from this scope but
  not from the existing Brightwell + chain-swap kit). This is a
  multi-week multi-polecat arc if pursued; the audit at
  `docs/a8-s3-status.md` and the rotation-residual status
  (`docs/a8-s2-rotation-residual-status.md`, mg-ba0c) sketch
  the scope. **Status as of 2026-05-04:** unchanged — still the
  primary in-tree path, still out of scope for any single
  polecat session. Track 1 (`mg-b666`) confirmed that no
  compound-automorphism shortcut bypasses this scope: the
  case-2-strict regime is genuinely a probability-bound
  question, and the in-tree probability machinery does not
  reach it at `|α| ≤ 6`.
* **Math-simplification experiment.** Per Daniel's 2026-04-27
  directive on changing strategy in the difficult-to-formalize
  region, a parallel arc was authorised to seek a structurally
  simpler discharge of Case 2 / case-2-strict. Two scoping
  passes ran:
    * **Arc 1.0 (`mg-3e53`,
      `docs/math-simplification-scoping.md`, 2026-05-02).**
      Surveyed four candidates (A: ε-close-to-ordinal-sum
      reductio; B: layered-reduction cleanup; C: finite-enum
      certificate; D: width-3 Kahn–Linial tightening).
      Recommended A; A1 RED-fallback'd
      (`docs/math-simplification-A1-feasibility.md`, `mg-3d9d`);
      B1 shipped as a parallel cleanup (`mg-805c`); A2/A3/A4
      not commissioned.
    * **Arc 2.0 (`mg-80ab`,
      `docs/math-simp-arc-2.0/scoping.md`, 2026-05-04).**
      Re-scoped under fresh framings (audit-bar revisit /
      direct probability bound / restrict-and-dispatch /
      alternate proof) post-mg-a79e/mg-b0de. **Zero GREEN
      framings found.** The 2026-04-27 mg-a79e and mg-b0de
      findings *contracted* the viable frame space for math
      simplification rather than expanding it.
  **Status as of 2026-05-04:** the in-scope math-simplification
  search has been exhausted. Any future revival here is either
  (i) a width-3 Kahn–Linial-tightening research arc (Track 2's
  framing 2b / arc-1.0 candidate D, paper-level math discovery,
  out of polecat scope), (ii) a fresh axiom under a Daniel-only
  audit-bar override (Track 2's framing 1, currently RED on two
  audit-bar conditions), or (iii) an alternate proof program
  (Track 2's framing 4, multi-week external collaboration).
  None of these is a polecat-doable arc.

A third pathway, not on the original η₅ list but raised by
Track 2 §6.4.4 as an explicit fallback: **finite-enumeration
certificate for K=2 case-2-strict** (Track 2's framing 3 /
sub-option B2, ~300–500 LoC). This is mechanical, not aesthetic;
narrows but does not obviate `Case3Witness`; competes with
rather than complements the structural infrastructure that
already landed (`CompoundSwap.lean` etc.). Track 2 records it as
**AMBER as a Track 1 fallback only**. Since Track 1 closed
RED (structural impossibility, not effort-bound), B2 might be
filed as a separate ticket if PM later wants to mechanically
shrink the gap; not currently planned.

**Reachability — the headline is unaffected.** The headline
`width3_one_third_two_thirds` does **not** consume `hFKG :
Case2FKGSubClaim L`. Under option (δ), the K=2 dispatch reaches
the Case 2 leaf via the parked-`hC3` path: `Case3Witness` is
universally quantified over layered width-3 non-chain `β`'s
satisfying the F5 entry conditions, and that quantification
**subsumes Case 2 strict witnessing** as one of the sub-types it
discharges (the strict within-band ⪯-pair regime sits inside the
`HasWidthAtMost β 3 ∧ ¬ IsChainPoset β ∧ 2 ≤ Fintype.card β`
class that any consumer of `hC3` must cover). The
false-antecedent theorems `case2Witness_balanced_under_FKG` and
`strictCase2Witness_m2_balanced` are therefore not in the
headline's transitive closure and do not affect the
`#print axioms` baseline reproduced in §3. The headline's truth
under its `hC3` hypothesis is unaffected by the SubClaim defect
for the formalized statement: this is a paper-internal arithmetic
issue worth disclosing, but it does not invalidate the existing
PATH A claim ("structurally complete formalization modulo case-3
residual").

**What a forum reader should do.**

1. **Do not cite mg-27c2's `case2Witness_balanced_under_FKG`,
   `strictCase2Witness_m2_balanced`, or downstream consumers of
   `Case2FKGSubClaim` (e.g., the Case 2 branch of mg-02c2's
   `bipartite_balanced_enum_general` at
   `lean/OneThird/Step8/BipartiteEnumGeneral.lean:210`) as
   unconditional results.** They are technically-true implications
   on a false antecedent — vacuous in the natural Case 2 regime,
   not load-bearing on the headline.
2. **The headline is unaffected.** `width3_one_third_two_thirds`
   does not consume these conditional theorems; it carries `hC3`
   instead, and `hC3`'s universal quantification subsumes Case 2
   strict witnessing. The §3 `#print axioms` baseline and the
   side-by-side reading in §1 are accurate as stated.
3. **If you are auditing the tree:** treat the Case 2 conditional
   theorems as parked alongside `hC3` itself, and cite the
   in-tree theorems alongside this disclosure (and the audit-trail
   docs
   [`a8-path-b-block-and-report-status.md`](a8-path-b-block-and-report-status.md)
   for the SubClaim-falsifying counterexample,
   [`a8-s2-restate-block-and-report-status.md`](a8-s2-restate-block-and-report-status.md)
   for the η₄-blocked technical reasoning) so the antecedent's
   status is not buried.

This disclosure is additive: the mg-9e50 PATH A reframe still
correctly characterises `hC3` and the Brightwell axiom; this
section flags an *additional* in-tree caveat that the original
PATH A docs did not surface, with iteration disposition now
finalized as parked.

---

## 6. Build and verify

A third-party reader can reproduce the claim end-to-end as follows:

```sh
git clone https://github.com/drellem2/one_third_width_three.git
cd one_third_width_three/lean
lake exe cache get   # fetch prebuilt mathlib oleans (strongly recommended)
lake build OneThird
```

Expected: `lake build OneThird` succeeds in roughly 3 minutes wall
clock after `lake exe cache get`, with zero `sorry` warnings and
several hundred benign linter warnings (`unusedDecidableInType`,
`unusedSectionVars`). No errors.

The most recent end-to-end build was performed by the
formalization-completeness audit `mg-49a4` on 2026-04-27 (commit
`6af280c`), which reports "1403 jobs, ~3 min wall after cache get;
0 sorries; clean" and regenerates the `#print axioms` baseline above.

To inspect the headline's axiom dependencies directly:

```sh
cd lean
lake env lean scripts/PrintAxiomsAudit.lean
```

This prints the table reproduced verbatim in §3 above. The single-theorem
form (just `width3_one_third_two_thirds`) is at
`lean/scripts/PrintAxioms.lean` and matches
[`PRINT_AXIOMS_OUTPUT.txt`](../lean/PRINT_AXIOMS_OUTPUT.txt).

To inspect the headline statement and its `hC3` hypothesis:

```sh
cd lean
lake env lean -e '#check @OneThird.width3_one_third_two_thirds'
```

`Lean version pinned at `leanprover/lean4:v4.29.1` via
[`lean/lean-toolchain`](../lean/lean-toolchain); mathlib is pinned via
[`lean/lake-manifest.json`](../lean/lake-manifest.json).

---

## 7. Acknowledged caveats

There are two residuals on the headline that a forum-post reader
needs to internalise before drawing conclusions about what is and
is not "formalized" (plus the §5 in-tree-issue caveat on a
non-headline conditional theorem):

### 7a. The `hC3` Prop-level hypothesis (open math, settled park)

The headline carries `hC3 : Step8.Case3Witness` as a Prop-level
hypothesis. Discharging it inside the formalization is open math.
Path C cleanup attempted the discharge across four polecat rounds
followed by a compound-automorphism infrastructure build-out
(mg-84f2 / mg-c0c7 / mg-02c2, in tree) and was parked under
option (δ) per pm-onethird's firm round-4 stop-loss
(`docs/path-c-cleanup-roadmap.md`). On 2026-05-04 a Track 1 attempt
to extend the landed infrastructure to case-2-strict block-and-
reported under a structural cardinality obstruction
(`docs/path-c-track-1-status-1.md` §2): no order-preserving
permutation `σ` with `σ a = a'` can exist in the strict-pair regime,
because such a `σ` would force `|upper(a)| = |upper(a')|`. Parallel
Track 2 (`mg-80ab`, `docs/math-simp-arc-2.0/scoping.md`) and
Track 3 (`mg-65e1`, `docs/math-simp-arc-3.0/scoping.md`) scoping
passes found no GREEN alternate framings across 21 candidates.
The park is now **structurally settled** rather than
effort-conditional; the unified F1 / F2 / F3 explanation is in
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) (the
canonical "why is the formalization conditional" doc); revisit
triggers are listed in `docs/path-c-cleanup-roadmap.md` §7.

A consumer of `width3_one_third_two_thirds` must either supply `hC3`
themselves or treat the conclusion as conditional on it. The
parametrically-quantified shape of `Case3Witness`
(`lean/OneThird/Step8/LayeredBalanced.lean:438-444`) makes the
hypothesis explicit; it is not buried inside another lemma or
discharged by an unannotated axiom.

### 7b. The `brightwell_sharp_centred` axiom (external, retained)

The headline depends on the named project axiom
`OneThird.LinearExt.brightwell_sharp_centred`, which transcribes a
combined Brightwell 1999 §4 + Kahn–Saks 1984 Lemma 2.2 bound — a
peer-reviewed published external result — into Lean. The axiom is
**retained as an axiom** rather than ported, per `mg-b699` decision;
the replacement path is documented in
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §1 and is estimated at 500–800
LoC of mathlib-tier covariance / set-system infrastructure orthogonal
to the structural proof.

Filing such a port is **not** a prerequisite for any downstream
consumer: the Lean tree treats the bound as a black box exactly as
the LaTeX source does. Within the scope of this paper's
contribution — the structural / combinatorial argument of Steps 1–7
and the layered Step 8 dispatch — the formalization is sorry- and
project-axiom-free.

---

## 8. Pointers

* **Paper:** [`main.pdf`](../main.pdf), [`main.tex`](../main.tex)
  (`thm:main` at `main.tex:230-241`).
* **Lean entry point:** [`lean/OneThird/MainTheorem.lean`](../lean/OneThird/MainTheorem.lean)
  (lines 52-57 for the headline, 28-51 for the docstring).
* **Lean per-file audit:** [`lean/README.md`](../lean/README.md).
* **Axiom rationale:** [`lean/AXIOMS.md`](../lean/AXIOMS.md) (per-axiom
  scope-match checklist, replacement path).
* **`#print axioms` baseline:** [`lean/PRINT_AXIOMS_OUTPUT.txt`](../lean/PRINT_AXIOMS_OUTPUT.txt).
* **Path C parked-work audit:** [`docs/path-c-cleanup-roadmap.md`](path-c-cleanup-roadmap.md).
* **Formalization-completeness audit:** [`docs/formalization-completeness-audit.md`](formalization-completeness-audit.md).
* **mg-27c2 `Case2FKGSubClaim` direction-reversed audit (§5):**
  [`docs/a8-path-b-block-and-report-status.md`](a8-path-b-block-and-report-status.md)
  (commit `64f2d87`, mg-a79e); related earlier audits
  [`docs/a8-s2-rotation-residual-status.md`](a8-s2-rotation-residual-status.md)
  (mg-ba0c) and
  [`docs/a8-s2-strict-witness-status.md`](a8-s2-strict-witness-status.md)
  (mg-43f3).
* **Forum-post template (paste-able):** [`docs/lean-forum-post-template.md`](lean-forum-post-template.md).

---

## 9. Provenance

This document was filed under `mg-9e50` ("Reframe public claim for
lean-forum publication readiness — PATH A — docs-only") by polecat
`pc-9e50` on 2026-04-27, in response to the parent ticket `mg-edb8`
(Daniel's lean-forum publication-readiness ask). PATH A is the
docs-only reframe that aligns the public framing with the actual
Lean claim shape; PATH B (unparking the Path C compound-automorphism
arc to drop `hC3` from the headline) is parked behind a Daniel
OVERRIDE.

This doc supersedes any earlier informal "fully formalized" framing
that pre-dated the option (δ) park decision (2026-04-27). Where this
doc and an earlier README phrase disagree, this doc and the audit
docs it cites are the canonical record of what is currently proven.

§5 ("Known in-tree issue: mg-27c2 `Case2FKGSubClaim` direction-reversed")
was added under `mg-8f59` ("PATH A disclosure update — mg-27c2
hypothesis was provably false") by polecat `pc-8f59` on 2026-04-27
(commit `a7ae06d`), in response to the `pc-a79e` block-and-report
finding (commit `64f2d87`, mg-a79e). The η₄ restate attempt
(`mg-b0de`, filed under Daniel OVERRIDE `mg-602e`) subsequently
blocked: the ≤ 2/3 upper bound is not discharge-able from existing
Brightwell + chain-swap infrastructure in the K=2 regime
(|Q| ≤ 6 < 12); see audit at `docs/a8-s2-restate-block-and-report-status.md`
(commit `8f97133`). The pre-committed PM pivot η₅ (drop SubClaim
discharge path; keep `hC3`) fired on receipt of that
block-and-report. §5 was amended to its current η₅-park final-state
framing under `mg-457c` ("PATH A disclosure final-state amendment —
η₅ park") by polecat `pc-457c` on 2026-04-27.

The 2026-05-04 Status / §2 / §5 / §7a refresh (this revision) was
landed under `mg-721a` ("Lean-forum publication post — prep + venue
selection") by polecat `p721a`, in response to the 2026-05-04
PATH A pivot after both Path C cleanup tracks block-and-reported.
The fresh evidence is Track 1 (`mg-b666`, structural cardinality
obstruction on case-2-strict, commit `5dff5e4`,
`docs/path-c-track-1-status-1.md`) and Track 2 (`mg-80ab`, math-simp
arc 2.0 zero-GREEN scoping verdict, commit `b1ac92b` on branch
`math-simp-arc-2.0`, `docs/math-simp-arc-2.0/scoping.md`). The
substantive change vs. the 2026-04-27 calibration: the option (δ)
park is now **structurally settled** rather than awaiting either
more compound-automorphism work or a math-simplification arc. The
companion forum-post template (`docs/lean-forum-post-template.md`)
was refreshed in the same commit.
