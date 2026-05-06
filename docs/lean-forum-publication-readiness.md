# Lean forum publication readiness

This document records, in a single place and at the level of fidelity
appropriate for a public lean Zulip / forum announcement, exactly what
the Lean formalization in [`lean/`](../lean/) proves and what it does
not. It is the canonical companion to a forum post about this
repository: the [forum-post template](lean-forum-post-template.md)
quotes from this doc rather than restating the claim shape.

The intent is that a Lean / formal-methods reader can verify the
claim end-to-end and audit the trust surface without needing to
reverse-engineer the relationship between the paper's `thm:main`
and the Lean-side headline theorem.

**Status as of 2026-05-06.** Build is clean (1409 lake jobs, 632 s
cold). The headline `OneThird.width3_one_third_two_thirds` is
**unconditional** — its signature carries only `hP : HasWidthAtMost
α 3` and `hNonChain : ¬ IsChainPoset α`, exactly matching the
paper's `thm:main` (modulo the paper's separate `Hypothesis~A`
arithmetic-richness side condition, on which `thm:main` itself
remains conditional). The trust surface is the four-category list
disclosed below and reproduced verbatim in the forum-post template:

1. mathlib's classical-foundations trio (`propext`,
   `Classical.choice`, `Quot.sound`);
2. one external published bound transcribed as the project axiom
   `OneThird.LinearExt.brightwell_sharp_centred` (Brightwell 1999
   §4 + Kahn–Saks 1984 Lemma 2.2);
3. one paper-internal sketch transcribed as the project axiom
   `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`
   (the residual `¬ InCase3Scope` half of `prop:in-situ-balanced`
   Case 3, faithful transcription of `rem:enumeration` per the
   `mg-7377` QA verdict; replacement deferred indefinitely per the
   `mg-5cd8` disposition-B amendment);
4. Lean's `Lean.ofReduceBool` axiom (standard `native_decide`
   compiler-trust), instantiated five times for the F5a Case-3
   enumeration certificate (`case3_balanced_w{1,2,3,4}`) and the
   Option-C Stage-1 K=2 closure (`case2_certificate`).

**Update relative to 2026-05-04.** The 2026-05-04 calibration
characterised the headline as carrying an `hC3 : Step8.Case3Witness`
Prop-level hypothesis under the option (δ) park decision
(2026-04-27). That parameter has since been **closed**: the
Option-C arc landed Stage 2A (`mg-2a56`,
`LayeredDecomposition.compactify`, commit `e4ffe2d`, 2026-05-05) —
band-compactification under sub-poset descent, removing the
empty-band obstruction — and Stage 2B (`mg-8c72`,
`OptionC.Case3WitnessProof`, commit `16d26ef`, 2026-05-05), which
discharges a Candidate A''-tightened `Step8.Case3Witness.{u}`
universal as a Lean theorem (composing the K=1 vacuous case under
Injective, the K=2 closure of `mg-01ec` /
`Step8.OptionC.option_c_K2_closure` via the
`case2_certificate` `native_decide` enumeration, and the K ≥ 3
leaves consuming `case3Witness_hasBalancedPair_outOfScope`, with
sub-poset descent threaded through `compactify`). The headline now
supplies the witness internally; the public signature drops `hC3`.

The forum-readiness validation pass `mg-5cd8` (2026-05-06,
[`docs/forum-readiness-validation/verdict.md`](forum-readiness-validation/verdict.md))
audited the post-Stage-2B state and returned **AMBER on doc-drift
only**: the build is green, the axiom inventory matches
disposition-B expectations, all five `native_decide` audits are
clean, and the only finding was that this doc and the forum-post
template had not yet been refreshed for the unconditional headline.
This refresh closes that finding (mg-d7fd; AMBER → GREEN).

The substantive math content of §5 (the F1 / F2 / F3 structural
analysis of why a simpler in-tree discharge of Case 3 was not
available) and §7a (the published `[0.276, 1/3)` Kahn–Linial gap)
remains accurate as historical context for **why the
`case3Witness_hasBalancedPair_outOfScope` axiom is retained** as a
faithful transcription of `rem:enumeration` rather than fleshed
out into a Lean proof. The replacement-path framing has shifted
from "park `hC3`" to "retain the axiom, port deferred indefinitely
per `mg-5cd8` disposition B".

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

### 1b. Lean headline (`width3_one_third_two_thirds`, `lean/OneThird/MainTheorem.lean`)

```lean
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α :=
  Step8.width3_one_third_two_thirds_assembled hP hNonChain
    Step8.OptionC.Case3Witness_proof
```

The Lean signature is the same as the paper's `thm:main` modulo
the standard `[Fintype]` / `[DecidableEq]` instances: width ≤ 3
plus non-chain implies a balanced pair. There is no Prop-level
`hC3` parameter; the universal Case-3 discharge is supplied
internally by `Step8.OptionC.Case3Witness_proof` (Option-C Stage 2B,
`mg-8c72`, `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean`).

`HasBalancedPair α` (`lean/OneThird/Poset.lean`) unfolds to: there
exist incomparable `x y : α` with
`1/3 ≤ probLT (x, y) ≤ 2/3` under the uniform linear-extension
measure — the same conclusion as `thm:main`.

### 1c. Side-by-side reading

The Lean signature and the paper's `thm:main` signature now match.
The differences are entirely on the disclosure side: the paper
proves `thm:main` conditional on Hypothesis~A (arithmetic richness,
an open mathematical condition), whereas the Lean tree proves the
same conclusion without arithmetic richness as a hypothesis but
with two named project axioms in the headline's transitive closure
plus a small set of `Lean.ofReduceBool`-backed `native_decide`
certificates. **The two residual surfaces do not coincide and are
not a routine translation of one another.**

* The paper's `thm:main` residual (Hypothesis~A) is an
  arithmetic-richness inequality on the Step 5/6/7 cascade constants.
  It is `n`-independent but `γ`-quantified, and it pins the
  large-`n` tail of the small-`γ` regime via BK expansion. It is
  open mathematically: not derived from Steps 1–7, not formally
  verified, not refuted.
* The Lean tree replaces the arithmetic-richness conditionality
  with concrete trust line items. The structurally interesting one
  is `case3Witness_hasBalancedPair_outOfScope`, which transcribes
  the paper's own `rem:enumeration` sketch
  (`step8.tex:3157-3173`) for the residual `¬ InCase3Scope`
  parameter range; this is internal to the paper, not an external
  citation, and the paper's sketch is genuinely a sketch rather
  than a fleshed-out proof. The other (`brightwell_sharp_centred`)
  is the published external Brightwell / Kahn–Saks bound and
  is the standard "import an external published result" pattern.

The honest summary, which the forum-post template uses, is:

> The headline theorem `OneThird.width3_one_third_two_thirds` has
> the same hypothesis profile as the paper's `thm:main` (width ≤ 3,
> non-chain). The proof is paper-faithful modulo a four-category
> trust surface: the mathlib classical-foundations trio; one
> project axiom transcribing the published Brightwell / Kahn–Saks
> sharp centred bound; one project axiom transcribing the paper's
> own `rem:enumeration` Case-3 residual sketch; and Lean's
> `Lean.ofReduceBool` for five `native_decide`-backed Case-3 /
> Case-2 enumeration certificates. The paper's `thm:main` itself
> remains conditional on Hypothesis~A (arithmetic richness, an open
> mathematical condition); the Lean tree does not transcribe
> Hypothesis~A.

---

## 2. What `case3Witness_hasBalancedPair_outOfScope` is and why it is retained

The `case3Witness_hasBalancedPair_outOfScope` axiom
(`lean/OneThird/Step8/Case3Residual.lean`, audited in
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §2) discharges the
**residual `¬ InCase3Scope` half** of the paper's
`prop:in-situ-balanced` Case 3 (`step8.tex:3033-3047`) — the
parameter range outside the F5a Bool-certified `case3_certificate`.
The paper's argument for this regime is the `rem:enumeration`
sketch (`step8.tex:3157-3173`); the axiom transcribes that
sketch's conclusion at the polecat-instruction-blessed level of
fidelity ("If new math turns out to need its own axiom: report
honestly"). The `mg-7377` QA verdict
([`lean/AXIOMS.md`](../lean/AXIOMS.md) §2 "QA verdict (mg-7377)")
is **axiom is faithful**: every hypothesis matches the wider
profile of `Step8.bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean`) restricted to `¬ InCase3Scope`,
plus the typed Case 3 witness produced by A8-S1's
`case1_dispatch_inScope`; the size cap `|α| ≤ 6w + 6` is strictly
tighter than the paper's `|Q| ≤ 9w + 3` (so the axiom is no
stronger than the paper's claim).

The axiom is consumed inside `Step8.OptionC.Case3Witness_proof`
(Option-C Stage 2B, `mg-8c72`), which discharges the
Candidate A''-tightened `Step8.Case3Witness.{u}` universal as a
Lean theorem and is supplied internally by the headline. The
public signature of `width3_one_third_two_thirds` no longer
mentions `Case3Witness` or any related Prop-level hypothesis.

Per the `mg-5cd8` disposition-B amendment (2026-05-06,
[`docs/forum-readiness-validation/verdict.md`](forum-readiness-validation/verdict.md)
"Disposition-B amendment note"), the axiom is **retained as
specified**, with the port deferred indefinitely. The replacement
path — pigeonhole on shared profile coordinates plus a
band-restricted Case 2 FKG sub-coupling plus a reduction back to
Case 1 / Case 2 — is recorded in
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §2 "Replacement path
(open)", but its substantive new mathematical content is the same
band-restricted probability-form FKG sub-coupling that the
deferred A8-S2-cont scope already targets, and is not currently
planned as a polecat-doable arc. The mg-75ef latex-first artifact
(2026-05-06; new file produced after `mg-5cd8`'s validation pass)
fleshes out the paper's `rem:enumeration` sketch into a structured
multi-step argument modulo the deferred cross-poset
probability-form FKG infrastructure, providing a forward-citeable
math-side scaffolding for any future replacement effort; it does
not retire the axiom.

### Why discharging this in tree is structurally hard (historical context)

This subsection summarises why a simpler in-tree discharge of the
residual Case 3 was not available before Option-C, and why the
axiom transcription is the honest framing rather than a stopgap.
The pre-Option-C parking decision (option (δ), 2026-04-27) and
the 2026-05-04 Track 1 / Track 2 closures had already established
that no compound-automorphism build-out and no fresh in-tree
proof framing closed the gap; Option-C Stages 2A + 2B then
discharged the *outer* universal `Step8.Case3Witness` as a Lean
theorem **by routing the residual leaves through the
`outOfScope` axiom**, leaving the axiom itself as the trust line
item.

The unified F1 / F2 / F3 explanation is in
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) (the
canonical "why is the residual sketch retained" entry point;
written under the pre-Stage-2B `hC3`-parking framing but
substantively unchanged in its structural content). The short
version:

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
— produces an in-tree discharge of the residual without the
deferred FKG infrastructure. A future replacement of
`case3Witness_hasBalancedPair_outOfScope` requires either (i) the
deferred A8-S2-cont probability-normalised cross-poset FKG
infrastructure (~2000–3500 LoC, paper-tier mathematical work;
sketched in `docs/a8-s2-status.md` §5), (ii) a width-3-specific
tightening of the Kahn–Linial covariance bound that would close
the unconditional `δ ≥ 0.276 → 1/3` gap, or (iii) an entirely
different proof program. None of those is a polecat-doable arc;
the disposition-B amendment of `mg-5cd8` records the retention as
indefinite. Note: this is "no in-tree-derivable simpler argument,"
strictly weaker than "no simpler argument exists" — see
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) §
"What this doc does not claim".

The full audit trail is
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) (entry
point for the structural explanation; pre-Stage-2B framing,
substantively current),
`docs/path-c-cleanup-roadmap.md` (entry point for the pre-Option-C
cleanup arc),
`docs/path-c-track-1-status-1.md` (Track 1 structural
impossibility, mg-b666), the math-simp arc 2.0 scoping pass
(`mg-80ab`, four candidate fresh framings, zero GREEN found), and
the math-simp arc 3.0 strategy revisit (`mg-65e1`), plus the five
round-by-round status docs from the original four-round arc:

* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — pins the
  closure target to chain-form FKG.
* `docs/a5-g3e-fkg-route-status.md` (mg-4a5b) — round 2.
* `docs/a5-g3e-path-c-wiring-v3-status.md` (mg-072c) — round 3.
* `docs/a5-g3e-path-c-wiring-v4-status.md` (mg-0fa0) — round 4.
* `docs/a5-g3e-path-c-wiring-v5-status.md` (mg-94fd) — firm round-4
  stop-loss; option (δ) trigger.

As of Stage 2B (`mg-8c72`, 2026-05-05) the `hC3` parameter is no
longer on the headline; the `Step8.Case3Witness` universal is
discharged internally by `Step8.OptionC.Case3Witness_proof`
(`lean/OneThird/Step8/OptionC/Case3WitnessProof.lean`), and the
`outOfScope` axiom carries the residual disclosure. The
`MainTheorem.lean` docstring records the closure history; the
`Step8.Case3Witness.{u}` definition has been tightened to the
Candidate A''-restricted universal that `Case3Witness_proof`
discharges as a Lean theorem. The above F1 / F2 / F3 framework
remains a faithful description of why the residual is not closer
to the surface — the same structural facts now explain why the
`outOfScope` axiom is *retained* rather than ported in tree.

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
 OneThird.LinearExt.brightwell_sharp_centred,
 OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope,
 OneThird.Step8.Case3Enum.case3_balanced_w1._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w2._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w3._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w4._native.native_decide.ax_1_1,
 OneThird.Step8.OptionC.case2_certificate._native.native_decide.ax_1_1]
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

Three of these (`propext`, `Classical.choice`, `Quot.sound`) are
the mathlib-standard classical foundations that are also depended
on by essentially every classical mathlib theorem.
`OneThird.LinearExt.brightwell_sharp_centred` and
`OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`
are the two named project axioms (§4 below). The five
`_native.native_decide.ax_1_1` entries are per-decision instances
of the standard `Lean.ofReduceBool` axiom underlying
`native_decide`; they underwrite the F5a Case-3 enumeration
certificate `Step8.Case3Enum.case3_certificate` (four facts at
`w ∈ {1, 2, 3, 4}`, faithfully audited in
[`docs/forum-readiness-validation/native-decide-audit.md`](forum-readiness-validation/native-decide-audit.md))
and the Option-C Stage-1 K=2 closure certificate
`Step8.OptionC.case2_certificate` consumed by `mg-01ec`'s
`option_c_K2_closure`.

The intermediate theorems (`mainAssembly`, `mainAssembly_smallN`,
`cexImpliesLowBKExpansion`, `counterexample_implies_low_BK_expansion`)
depend only on the mathlib trio: the Brightwell axiom, the
`outOfScope` axiom, and the `native_decide` instances enter the
headline closure only when `MainTheoremInputs` is constructed via
`mainTheoremInputsOf` and `Case3Witness_proof` is supplied for the
headline assembly.

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

After Option-C Stage 2B (`mg-8c72`, 2026-05-05), the second named
project axiom
`OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope` is
**reachable** from the headline `width3_one_third_two_thirds` —
the headline supplies `Step8.Case3Witness` internally via
`Step8.OptionC.Case3Witness_proof`, which threads the residual
`¬ InCase3Scope` leaves of the F3 K-dispatch through that axiom.
This is the standard "import a published external bound" pattern
applied to the paper's own `rem:enumeration` sketch (paper-internal,
not external); the QA verdict and full audit are in
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §2 (`mg-7377`, "Axiom is
faithful"); see also §2 above. The retention is firm under the
`mg-5cd8` disposition-B amendment; replacement is deferred
indefinitely.

---

## 5. Known in-tree issue: mg-27c2 `Case2FKGSubClaim` direction-reversed (now bypassed by Option-C K=2 closure; left in tree for forum-reader transparency)

A disclosure item distinct from the two named project axioms (§4):
a **conditional theorem** in the tree,
`case2Witness_balanced_under_FKG`
(`lean/OneThird/Step8/Case2Rotation.lean:894`, mg-27c2), and the
companion `strictCase2Witness_m2_balanced`
(`lean/OneThird/Step8/Case2Rotation.lean:813`), are predicated on
the hypothesis structure `Case2FKGSubClaim L`
(`lean/OneThird/Step8/Case2Rotation.lean:772`) whose `pair` field
is **provably false** on the natural Case 2 inputs the original
dispatch was supposed to fire on. The implications themselves are
technically correct (anything follows from a false antecedent),
but they are vacuous on the strict within-band ⪯-chain pairs they
target. A forum reader auditing `Case2Rotation.lean` would
absolutely spot this; this section flags it explicitly.

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
`width3_one_third_two_thirds` does **not** consume `hFKG`: after
Option-C Stage 2B, the K=2 dispatch reaches the Case 2 leaf via
`Step8.OptionC.option_c_K2_closure` (`mg-01ec`, commit `c403216`),
which is a finite-enumeration Bool certificate
(`Step8.OptionC.case2_certificate`, decided by `native_decide` and
audited in
[`docs/forum-readiness-validation/native-decide-audit.md`](forum-readiness-validation/native-decide-audit.md))
plus a Bool→Prop bridge — so the K=2 closure now bypasses the
provably-false SubClaim entirely. The K ≥ 3 leaves of the F3
K-dispatch consume the
`case3Witness_hasBalancedPair_outOfScope` axiom rather than any
`hFKG`-conditional theorem. The false-antecedent SubClaim
theorems are therefore **not** in the headline's transitive
closure, and the verbatim `#print axioms` baseline (§3 above) is
unaffected. They are nonetheless visible to a reader auditing
`Case2Rotation.lean`, and they would matter the moment any future
wiring tried to thread a constructed `hFKG` through the K=2 leaf.

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

**Post-Stage-2B status (2026-05-05).** Option-C Stage 2B
(`mg-8c72`) discharged the outer `Step8.Case3Witness` universal
without depending on a fixed SubClaim: the K=2 Case 2 leaf is
covered by `option_c_K2_closure` (`mg-01ec`, finite-enumeration
Bool certificate), and the K ≥ 3 leaves consume the
`case3Witness_hasBalancedPair_outOfScope` axiom directly. The
SubClaim defect therefore remains in tree as a paper-internal
direction-reversal flag for `Case2Rotation.lean` readers but no
longer parks any path to the headline closure.

**Future-revival pathways for the SubClaim direction-fix itself
(orthogonal to the headline).** Two routes existed at η₅ park
time (2026-04-27); both were **further narrowed** by the
2026-05-04 closures of Tracks 1 and 2 and remain
relevant only if a future contributor wants to *fix* the SubClaim
defect rather than bypass it (the headline is already routed
around it post-Stage-2B):

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
    * **Arc 2.0 (`mg-80ab`, 2026-05-04).** Re-scoped under
      fresh framings (audit-bar revisit / direct probability
      bound / restrict-and-dispatch / alternate proof)
      post-mg-a79e/mg-b0de. **Zero GREEN framings found.** The
      2026-04-27 mg-a79e and mg-b0de findings *contracted* the
      viable frame space for math simplification rather than
      expanding it.
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
Case2FKGSubClaim L`. After Option-C Stage 2B, the K=2 leaf is
discharged by `option_c_K2_closure` (Bool certificate, `mg-01ec`)
and the K ≥ 3 leaves by the `case3Witness_hasBalancedPair_outOfScope`
axiom; neither path threads `hFKG`. The false-antecedent theorems
`case2Witness_balanced_under_FKG` and
`strictCase2Witness_m2_balanced` are therefore not in the
headline's transitive closure and do not affect the
`#print axioms` baseline reproduced in §3. The unconditional
post-Stage-2B headline is unaffected by the SubClaim defect: this
is a paper-internal direction-reversal worth disclosing, but it
does not invalidate the formalized statement.

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
   does not consume these conditional theorems; the K=2 leaf is
   discharged by the `option_c_K2_closure` Bool certificate
   (`mg-01ec`), and the K ≥ 3 leaves consume the
   `case3Witness_hasBalancedPair_outOfScope` axiom. The §3
   `#print axioms` baseline and the side-by-side reading in §1
   are accurate as stated.
3. **If you are auditing the tree:** treat the SubClaim
   conditional theorems as legacy artifacts that the
   Stage 2B Option-C closure routes around, and cite the
   in-tree theorems alongside this disclosure (and the audit-trail
   docs
   [`a8-path-b-block-and-report-status.md`](a8-path-b-block-and-report-status.md)
   for the SubClaim-falsifying counterexample,
   [`a8-s2-restate-block-and-report-status.md`](a8-s2-restate-block-and-report-status.md)
   for the η₄-blocked direction-fix attempt) so the antecedent's
   status is not buried.

This disclosure flags an in-tree caveat that does not affect the
post-Stage-2B headline closure but is visible to anyone reading
`Case2Rotation.lean`. The mg-9e50 PATH A reframe history is
preserved in §9 (Provenance).

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
`unusedSectionVars`, plus a handful of `push_neg`-style
deprecations recorded in
[`docs/forum-readiness-validation/build-verification.md`](forum-readiness-validation/build-verification.md)).
No errors.

The most recent end-to-end build was performed by the
forum-readiness validation pass `mg-5cd8` on 2026-05-06 against
HEAD `0df0bc4`, which reports "1409 lake jobs, 552 s build wall
(632 s including clone + cache get); 0 sorries; clean" and confirms
the fresh-build `#print axioms` matches
[`PRINT_AXIOMS_OUTPUT.txt`](../lean/PRINT_AXIOMS_OUTPUT.txt)
byte-for-byte. See
[`docs/forum-readiness-validation/build-verification.md`](forum-readiness-validation/build-verification.md)
for the full reproduction trace.

To inspect the headline's axiom dependencies directly:

```sh
cd lean
lake env lean scripts/PrintAxioms.lean
```

This prints the table reproduced verbatim in §3 above and
matches [`PRINT_AXIOMS_OUTPUT.txt`](../lean/PRINT_AXIOMS_OUTPUT.txt).

To inspect the headline statement (now hypothesis-free modulo
`hP` and `hNonChain`):

```sh
cd lean
lake env lean -e '#check @OneThird.width3_one_third_two_thirds'
```

`Lean version pinned at `leanprover/lean4:v4.29.1` via
[`lean/lean-toolchain`](../lean/lean-toolchain); mathlib is pinned via
[`lean/lake-manifest.json`](../lean/lake-manifest.json).

---

## 7. Acknowledged caveats

There are three trust line items on the headline that a forum-post
reader needs to internalise before drawing conclusions about what
is and is not "formalized" (plus the §5 in-tree-issue caveat on a
non-headline conditional theorem):

### 7a. The historical `hC3` Prop-level hypothesis — discharged in Stage 2B

**The `hC3 : Step8.Case3Witness` hypothesis was discharged as a
theorem in Option-C Stage 2B (`mg-8c72`, commit `16d26ef`,
2026-05-05). The headline is unconditional.** The public signature
of `OneThird.width3_one_third_two_thirds` carries only `hP :
HasWidthAtMost α 3` and `hNonChain : ¬ IsChainPoset α`, exactly
matching the paper's `thm:main` modulo the standard `[Fintype]` /
`[DecidableEq]` instances. The `Step8.Case3Witness` universal is
supplied internally by `Step8.OptionC.Case3Witness_proof`
(`lean/OneThird/Step8/OptionC/Case3WitnessProof.lean`).

This subsection records the closure history because the question
"why does this Lean formalization carry the
`case3Witness_hasBalancedPair_outOfScope` axiom?" goes through it.
Pre-Stage-2B, `hC3` was **parked open math**, retained as a
Prop-level hypothesis on the headline under pm-onethird's option
(δ) decision (2026-04-27, `mg-94fd`). Path C cleanup attempted
the discharge across four polecat rounds followed by a
compound-automorphism infrastructure build-out (mg-84f2 /
mg-c0c7 / mg-02c2, in tree). On 2026-05-04 a Track 1 attempt to
extend the landed infrastructure to case-2-strict block-and-
reported under a structural cardinality obstruction
([`docs/path-c-track-1-status-1.md`](path-c-track-1-status-1.md)
§2): no order-preserving permutation `σ` with `σ a = a'` can
exist in the strict-pair regime, because such a `σ` would force
`|upper(a)| = |upper(a')|`. Parallel Track 2 (`mg-80ab`) and
Track 3 (`mg-65e1`) scoping passes found no GREEN alternate
framings across 21 candidates. The unified F1 / F2 / F3
explanation of why a simpler in-tree discharge was not available
is in
[`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md) (the
canonical "why is the residual sketch retained" doc; written
under the pre-Stage-2B `hC3`-parking framing but substantively
unchanged in its structural content).

Option-C Stage 2A (`mg-2a56`, commit `e4ffe2d`,
`LayeredDecomposition.compactify`) and Stage 2B (`mg-8c72`,
commit `16d26ef`) then closed the *outer* `Case3Witness`
universal as a Lean theorem, by routing the residual leaves
through the `case3Witness_hasBalancedPair_outOfScope` axiom (§7c
below) for K ≥ 3 and through the `option_c_K2_closure` Bool
certificate (`mg-01ec`, commit `c403216`) for K = 2. The K = 1
case is vacuous under the Candidate A'' "Injective band map"
tightening, and sub-poset descent is threaded through
`compactify`. The structural F1 / F2 / F3 obstruction now
explains why the `outOfScope` axiom is *retained* rather than
ported in tree.

A consumer of `width3_one_third_two_thirds` no longer supplies
`hC3` and does not need to treat the conclusion as conditional
on a Prop-level hypothesis; the trust footprint is the four-category
list in §3 / §1.

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
the LaTeX source does.

### 7c. The `case3Witness_hasBalancedPair_outOfScope` axiom (paper-internal, retained)

The headline also depends on the named project axiom
`OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`,
which transcribes the **paper's own** `rem:enumeration` sketch
(`step8.tex:3157-3173`) for the residual `¬ InCase3Scope`
parameter range of `prop:in-situ-balanced` Case 3. Unlike the
Brightwell axiom, this is paper-internal rather than an external
citation: the paper sketch is genuinely a sketch (not a
fleshed-out proof), and the substantive new mathematical content
needed for a Lean port is the band-restricted Case 2 FKG
sub-coupling (the same probability-form cross-poset FKG
infrastructure deferred under A8-S2-cont, `mg-8801`).

The QA verdict (`mg-7377`,
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §2 "QA verdict") is **axiom
is faithful**: every hypothesis in the axiom statement matches
the wider profile of `Step8.bounded_irreducible_balanced_hybrid`
restricted to `¬ InCase3Scope`, the size cap `|α| ≤ 6w + 6` is
strictly tighter than the paper's `|Q| ≤ 9w + 3` (so the axiom
is no stronger than the paper's claim), and the conclusion
matches `prop:in-situ-balanced`'s Case 3 conclusion exactly.
The axiom is reachable from the headline post-Stage-2B (it is
consumed by `Step8.OptionC.Case3Witness_proof`'s K ≥ 3 leaves);
the disposition-B amendment of `mg-5cd8` records the retention
as **deferred indefinitely**. The mg-75ef latex-first artifact
(2026-05-06) provides a forward-citeable structured sketch of the
math-side argument that any future replacement effort would
flesh out.

The mg-75ef artifact is on a polecat branch and not yet on
`main`; the math-side replacement scope is documented in
[`lean/AXIOMS.md`](../lean/AXIOMS.md) §2 "Replacement path
(open)".

---

## 8. Pointers

* **Paper:** [`main.pdf`](../main.pdf), [`main.tex`](../main.tex)
  (`thm:main` at `main.tex:230-241`).
* **Lean entry point:** [`lean/OneThird/MainTheorem.lean`](../lean/OneThird/MainTheorem.lean)
  (the headline plus its docstring; signature is
  `(hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)`).
* **Lean per-file audit:** [`lean/README.md`](../lean/README.md).
* **Axiom rationale:** [`lean/AXIOMS.md`](../lean/AXIOMS.md)
  (per-axiom scope-match checklist, replacement path; covers both
  `brightwell_sharp_centred` (§1) and
  `case3Witness_hasBalancedPair_outOfScope` (§2)).
* **`#print axioms` baseline:** [`lean/PRINT_AXIOMS_OUTPUT.txt`](../lean/PRINT_AXIOMS_OUTPUT.txt).
* **Forum-readiness validation pass (mg-5cd8, AMBER on doc-drift):**
  [`docs/forum-readiness-validation/verdict.md`](forum-readiness-validation/verdict.md)
  with sub-audits in
  [`build-verification.md`](forum-readiness-validation/build-verification.md),
  [`native-decide-audit.md`](forum-readiness-validation/native-decide-audit.md),
  [`axiom-inventory-verification.md`](forum-readiness-validation/axiom-inventory-verification.md),
  and [`doc-consistency.md`](forum-readiness-validation/doc-consistency.md).
* **Option-C Stage 2A status (compactify):**
  [`docs/option-c-execution-arc/stage-2a-compactify-status.md`](option-c-execution-arc/stage-2a-compactify-status.md)
  (mg-2a56, commit `e4ffe2d`).
* **Option-C Stage 2B status (Case3Witness_proof):**
  [`docs/option-c-execution-arc/stage-2b-status.md`](option-c-execution-arc/stage-2b-status.md)
  (mg-8c72, commit `16d26ef`).
* **Option-C K=2 closure status:**
  [`docs/option-c-execution-arc/k2-closure-status.md`](option-c-execution-arc/k2-closure-status.md)
  (mg-01ec, commit `c403216`).
* **Path C parked-work audit:** [`docs/path-c-cleanup-roadmap.md`](path-c-cleanup-roadmap.md).
* **Why-hC3-is-structural synthesis:** [`docs/why-hC3-is-structural.md`](why-hC3-is-structural.md)
  (mg-cda8, F1 / F2 / F3 framework).
* **case3Witness operational-consumption audit:**
  [`docs/case3witness-operational-audit.md`](case3witness-operational-audit.md)
  (mg-e0b8).
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

The 2026-05-04 Status / §2 / §5 / §7a refresh was landed under
`mg-721a` ("Lean-forum publication post — prep + venue selection")
by polecat `p721a`, in response to the 2026-05-04 PATH A pivot
after both Path C cleanup tracks block-and-reported. The fresh
evidence at that point was Track 1 (`mg-b666`, structural
cardinality obstruction on case-2-strict, commit `5dff5e4`,
[`docs/path-c-track-1-status-1.md`](path-c-track-1-status-1.md))
and Track 2 (`mg-80ab`, math-simp arc 2.0 zero-GREEN scoping
verdict).

The 2026-05-06 Status / §1 / §2 / §3 / §4 / §5 / §7a / §7c / §8
refresh (this revision) was landed under `mg-d7fd` ("Doc-refresh:
post-Stage-2B forum-disclosure docs") in response to the
forum-readiness validation pass `mg-5cd8`
([`docs/forum-readiness-validation/verdict.md`](forum-readiness-validation/verdict.md))
returning **AMBER on doc-drift only** (build green, axiom
inventory matches disposition-B expectations, all five
`native_decide` audits clean; the only finding was that this doc
and the forum-post template still framed `hC3` as a live headline
hypothesis after Option-C Stage 2B closed it). The substantive
chain that justifies the post-Stage-2B framing:

* **Option-C Stage 2A — `LayeredDecomposition.compactify`**
  (`mg-2a56`, commit `e4ffe2d`, 2026-05-05;
  [`docs/option-c-execution-arc/stage-2a-compactify-status.md`](option-c-execution-arc/stage-2a-compactify-status.md)).
  Band-compactification under sub-poset descent, removing the
  empty-band obstruction (Obstruction B of `mg-979e`).
* **Option-C K=2 substantive closure — `option_c_K2_closure`**
  (`mg-01ec`, commit `c403216`, 2026-05-05;
  [`docs/option-c-execution-arc/k2-closure-status.md`](option-c-execution-arc/k2-closure-status.md)).
  Finite-enumeration Bool certificate `case2_certificate` plus
  Bool→Prop bridge for the K=2 leaves of the F3 K-dispatch.
* **Option-C Stage 2B — `Case3WitnessProof`** (`mg-8c72`, commit
  `16d26ef`, 2026-05-05;
  [`docs/option-c-execution-arc/stage-2b-status.md`](option-c-execution-arc/stage-2b-status.md)).
  Candidate A''-tightened `Step8.Case3Witness.{u}` discharged as
  a Lean theorem composing K=1 vacuous + K=2 closure +
  K ≥ 3 leaves through `case3Witness_hasBalancedPair_outOfScope`,
  with sub-poset descent threaded through `compactify`. Headline
  signature drops `hC3`.
* **Root README refresh** (`mg-0dd2`, commit `0df0bc4`,
  2026-05-05) — root README's "Please read this before citing"
  section calibrated to the post-Stage-2B unconditional headline.
* **Forum-readiness validation pass — AMBER on doc-drift only**
  (`mg-5cd8`, commit `ddbb933`, 2026-05-06;
  [`docs/forum-readiness-validation/verdict.md`](forum-readiness-validation/verdict.md)).
  Audited fresh-clone build, native_decide invocations, axiom
  inventory, and disclosure docs. Found this doc and the
  forum-post template stale; recommended a small PM-filed
  doc-refresh.
* **Disposition-B amendment** (recorded in the `mg-5cd8` ticket
  body, 2026-05-06; archived in
  [`docs/forum-readiness-validation/verdict.md`](forum-readiness-validation/verdict.md)
  "Disposition-B amendment note"). Confirms that
  `case3Witness_hasBalancedPair_outOfScope` STAYS as a named
  project axiom; its replacement port is **deferred indefinitely**.
  The trust surface around this axiom is honestly disclosed
  rather than ported in tree.
* **mg-75ef latex-first artifact** (2026-05-06; not on `main`).
  Per the `feedback_latex_first_for_math_simp` discipline,
  fleshes out the paper's `rem:enumeration` sketch into a
  structured multi-step argument modulo the deferred cross-poset
  probability-form FKG infrastructure. Provides forward-citeable
  math-side scaffolding for any future replacement effort but
  does not retire the axiom.

The substantive change vs. the 2026-05-04 framing: the headline
is **unconditional** (post-Stage-2B); the trust surface adds
`case3Witness_hasBalancedPair_outOfScope` and five
`Lean.ofReduceBool` instances; the axiom retention is firm under
the disposition-B amendment. The companion forum-post template
([`docs/lean-forum-post-template.md`](lean-forum-post-template.md))
was refreshed in the same commit.
