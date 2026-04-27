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

**Status as of 2026-04-27.** Build is clean; the headline depends on
one named project axiom (Brightwell, transcribing a published
external result) plus Lean's standard classical-foundations trio,
and carries one Prop-level hypothesis (`hC3`) that pins a
parametrically-quantified discharge of the paper's `prop:in-situ-balanced`
Case 3. Both residuals are documented below and disclosed verbatim
in the forum-post template.

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
→ mg-072c → mg-0fa0 → mg-94fd) under Path C cleanup. The arc shipped
six pieces of substantive infrastructure (mg-9568, mg-7f06, mg-a735,
mg-27c2, mg-2e58, mg-26bb — see `docs/path-c-cleanup-roadmap.md` §4)
but stopped at a named structural obstruction:

> The minimal failing instance is the **N-poset**:
> `α = {x₁, x₂, y₁, y₂}` with `x₁ < y₁` and `x₂ < y₂`,
> `band 1 = {x₁, x₂}`, `band 2 = {y₁, y₂}`, `K = 2`, `w = 1`. The
> pair `(x₁, x₂)` is balanced (`Pr[x₁ <_L x₂] = 1/2` by direct
> enumeration of N's six linear extensions), but the witness comes
> from the **compound** automorphism `σ := (x₁ x₂)(y₁ y₂)` — the
> single transposition `(x₁ x₂)` alone is not a poset automorphism.
> The existing in-tree rotation infrastructure operates on
> within-band ⪯-comparable pairs/chains; the N-poset has no such
> pair, so neither Case 1 (ambient match) nor Case 2 (within-band
> ⪯-pair) fires.

(`docs/a5-g3e-path-c-wiring-v5-status.md`, paraphrased)

Closing the gap requires roughly 300–500 LoC of compound-automorphism
math (a `MultiOrbit.swap_preserves_le`-style constructor + a structural
matching lemma + a generalised dispatch head) that does not exist in
the tree today. After the round-4 firm stop-loss, pm-onethird picked
**option (δ): park** — retain `hC3` as a named hypothesis on the
headline, ship the audit as the deliverable, and revisit if the
underlying mathematical infrastructure lands later.

The full audit trail is `docs/path-c-cleanup-roadmap.md` (entry
point) plus the five round-by-round status docs:

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

## 5. Known in-tree issue: mg-27c2 `Case2FKGSubClaim` direction-reversed (η₄ restate in flight via `mg-b0de`)

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

**The fix is η₄ (`mg-b0de`), in flight as of this disclosure.** The
pivot — filed under Daniel OVERRIDE (`mg-602e`) and running
independently of, in parallel with, this disclosure ticket — is to
(i) restate `Case2FKGSubClaim.pair` with the correct direction
(`probLT a a' ≤ 1/2`), at which point the SubClaim becomes
equivalent to chain swap and is *already a theorem* (no axiom or
new infrastructure required); (ii) redesign the consumer to combine
the now-true `≤ 1/2` (chain swap) with a separately-derived `≤ 2/3`
upper bound from Brightwell covariance to produce the balanced pair
via `(a', a)` rather than `(a, a')`. mg-b0de may or may not have
landed by the time you read this; if it has, the line numbers
above will have shifted and the SubClaim's `pair` field's
conclusion will read `probLT a a' ≤ 1/2`.

**What a forum reader should do.**

1. **Do not cite mg-27c2's `case2Witness_balanced_under_FKG`,
   `strictCase2Witness_m2_balanced`, or downstream consumers of
   `Case2FKGSubClaim` (e.g., the Case 2 branch of mg-02c2's
   `bipartite_balanced_enum_general` at
   `lean/OneThird/Step8/BipartiteEnumGeneral.lean:210`) as
   unconditional results.** They are technically-true implications
   on a false antecedent — vacuous in the natural Case 2 regime,
   not load-bearing.
2. **The headline is unaffected.** `width3_one_third_two_thirds`
   does not consume these conditional theorems; it carries `hC3`
   instead. The §3 `#print axioms` baseline and the side-by-side
   reading in §1 are accurate as stated.
3. **If you are auditing the tree:** wait for mg-b0de to land
   before treating the Case 2 leaf as proved, OR cite the in-tree
   theorems alongside this disclosure (and the
   [`pc-a79e` status doc](a8-path-b-block-and-report-status.md))
   so the antecedent's status is not buried.

This disclosure is additive: the mg-9e50 PATH A reframe still
correctly characterises `hC3` and the Brightwell axiom; this
section flags an *additional* in-tree caveat that the original
PATH A docs did not surface.

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

### 7a. The `hC3` Prop-level hypothesis (open math, parked)

The headline carries `hC3 : Step8.Case3Witness` as a Prop-level
hypothesis. Discharging it inside the formalization is open math at
the time of writing: it requires roughly 300–500 LoC of
compound-automorphism infrastructure that does not exist in the tree.
Path C cleanup attempted the discharge across four polecat rounds and
was parked under option (δ) per pm-onethird's firm round-4 stop-loss;
see `docs/path-c-cleanup-roadmap.md` (entry point) and the five
round-by-round status docs. The headline retains `hC3` as a documented
hypothesis under that decision.

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
hypothesis was provably false") by polecat `pc-8f59` on 2026-04-27,
in response to the `pc-a79e` block-and-report finding (commit
`64f2d87`, mg-a79e). The companion η₄ restate ticket is `mg-b0de`,
filed under Daniel OVERRIDE (`mg-602e`) and running in parallel
with this disclosure update.
