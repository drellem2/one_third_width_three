# Math-simp arc 2.0 — scoping pass

> **EXPLORATORY ONLY — NOT a live program.**
>
> This file is the deliverable for `mg-80ab` (Track 2 kickoff,
> 2026-05-04, branch `math-simp-arc-2.0`). It surveys candidate
> mathematical framings that could obviate
> `Step8.Case3Witness` (and so drop `hC3` from the headline
> `width3_one_third_two_thirds`). It is **not** a commission to
> execute any of them. The active execution track for `hC3` is
> `mg-b666` (Track 1, branch `main`, compound-automorphism
> extension of `mg-84f2 / mg-c0c7 / mg-02c2`).
>
> Months from now, treat this doc the same way `simplifications.md`
> should have been treated after the arc 1.0 close (2026-05-02):
> as a record of evaluations made under specific assumptions, not
> as a backlog. If a framing changes status because mathlib /
> in-tree infrastructure has moved, file a fresh ticket — do not
> reanimate this doc as if it were live.

---

## 1. Provenance

* **Filed under** `mg-80ab` (Track 2, math-simp arc 2.0 scoping).
  Polecat `p80ab`, 2026-05-04.
* **Sibling** `mg-b666` (Track 1, compound-automorphism extension on
  `main`). Both spawned 2026-05-04T17:12Z from Daniel's reminder
  `pm-onethird/1777914292578721000.5852.1000`:
  > *"on the main branch, try to complete formalization, your call
  > how. On a separate branch pursue mathematical simplifications
  > further in case formalization keeps exploding in complexity."*
* **Parent** `docs/math-simplification-scoping.md@638ad1e` (arc 1.0
  scoping pass under `mg-3e53`, 2026-05-02). That doc surveyed four
  candidates A/B/C/D, recommended A, and committed a 4-chunk plan.
  A1 RED-fallback'd (`docs/math-simplification-A1-feasibility.md`,
  `mg-3d9d`); B1 shipped as a parallel cleanup (`b6b6c3f`,
  `mg-805c`); A2/A3/A4 were never commissioned. Net effect on
  `hC3`: **unchanged** (per
  `feedback_distinguish_arc_chunk_outcomes`).

This Track 2 scoping is the re-attempt under different framings.

## 2. Constraints (carried over and reaffirmed)

These are unchanged from arc 1.0 and remain hard constraints.

1. **Headline signature.** `width3_one_third_two_thirds` is
   ```lean
   theorem width3_one_third_two_thirds.{u}
       {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
       (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
       (hC3 : Step8.Case3Witness.{u}) :
       HasBalancedPair α
   ```
   (`lean/OneThird/MainTheorem.lean:52-57`). Dropping `hC3` is the
   goal. Strengthening `hP`/`hNonChain`, weakening the conclusion,
   or replacing `hC3` with a *different* universal hypothesis that
   carries comparable mathematical burden is **NOT** progress.
2. **Audit-bar discipline** (`feedback_audit_bar_for_axioms`).
   Any new project axiom must pass the 4-condition test (external
   + difficult + clearly labelled + low-risk). All four conditions
   must hold; "external" includes paper-internal sketches IF
   labelled and with a concrete discharge path. New axioms are a
   Daniel-only call.
3. **No fresh paper-level math under scoping authority.** A
   framing that requires substantively new mathematics (rather
   than a re-organisation of existing content) escalates to PM /
   Daniel. Polecat does not pre-commit to the math.
4. **Latex-first** (`feedback_latex_first_for_math_simp`). This
   doc is the latex-rigor artifact. Lean changes are downstream
   of an *accepted* deliverable + a follow-on execution ticket.
5. **Stop-loss is a valid outcome.** "No good framing found this
   round; Track 1 remains the path" is the explicit allowed
   verdict in the brief. **This doc lands that verdict.** See §6.

## 3. What changed since arc 1.0

Arc 1.0 ran through 2026-05-02 with the world-state reflected in
`docs/math-simplification-scoping.md`. **Two findings since then
materially change the feasibility of framings 2 and 3 in the
current brief.** Both must be folded in before re-evaluating.

### 3.1 Finding F1 (mg-a79e, `64f2d87`, 2026-04-27)

The `Step8.InSitu.Case2FKGSubClaim` structure
(`Case2Rotation.lean:772`, mg-27c2) has its `pair` field's
direction **provably wrong**:

> The chain hypothesis says `upper(a) ⊆ upper(a')` and
> `lower(a') ⊆ lower(a)` — `a'` has more upper edges and fewer
> lower edges, so `a'` tends to come earlier in linear extensions,
> giving `Pr[a < a'] ≤ 1/2`. The SubClaim's `pair` field
> claims the opposite, `1/2 ≤ Pr[a < a']`. Combined with chain
> swap, the two force `Pr = 1/2` exactly (the symmetric collapse,
> already absorbed by `case2Witness_balanced_or_strict`). In the
> *strict* case the chain swap is a strict injection and the
> SubClaim's lower bound is **strictly violated**.

(Documented in `docs/a8-path-b-block-and-report-status.md` §§2-3
with a 3-element `(K=2, w=1, |α|=3)` counterexample.)

**Impact on framings.** Any framing that proposes to *prove* a
chain-form FKG sub-claim of the SubClaim's shape is dead in the
strict case — the claim is not just hard, it's false. This
eliminates the natural Route B reading of arc 1.0 framing 2.

### 3.2 Finding F2 (mg-b0de, `8f97133`, 2026-04-27)

Restating the SubClaim with the corrected direction
(`probLT a a' ≤ 1/2`) makes it provable from chain swap, but the
**downstream** `≤ 2/3` upper bound for `probLT a' a` (the strict
case 2 closure's load-bearing inequality) is **unprovable from
existing infrastructure** at K=2:

* Brightwell sharp centred (`BrightwellAxiom.lean:159`) gives
  `|p(Q) − p(Q − z)| ≤ 2/|Q|`. To clear `Pr ≥ 1/3` one needs
  `|Q| ≥ 12`. **At K=2 we have `|Q| = |α| ≤ 6`**, so the bound
  is vacuous in this regime.
* `Case2BipartiteBound.lean` (mg-ed4d) handles K=2, **w=0**; for
  `w ≥ 1` the bipartite-forced hypothesis `hAB` is not free.
* Cross-poset count-form FKG (`probLT'_count_div_le_of_relExt`,
  `RelationPoset/FKG.lean:521`) bounds count numerators across
  augmented posets but does NOT give the probability-normalised
  form. The probability form is the deferred A8-S2-cont scope
  (~2000-3500 LoC, `docs/a8-s2-status.md` §5).
* Iterating Brightwell across multiple strictness witnesses
  gives a harmonic-sum bound `2 · H_{|Q|} ≈ 4.9` for `|Q| = 6` —
  even weaker.

(Documented in `docs/a8-s2-restate-block-and-report-status.md`
§3.) Recommendation η₅ at the time (PM-pinned): drop SubClaim
path, retain `hC3`, park.

**Impact on framings.** This is the tighter version of arc 1.0
A1's RED-fallback specialised to the K=2 regime. Any framing that
hopes to discharge case-2-strict via a probability bound at small
`|Q|` runs into the same vacuity. This eliminates the obvious
"axiom-light" reading of framings 2 and 3 in the current brief.

### 3.3 What this means in aggregate

Two of the natural escape hatches that arc 1.0's scoping took
seriously — Brightwell-style coupling at the strict pair, FKG
sub-claim at the chain configuration — are now **provably**
closed off in the K=2 regime that is exactly where the
obstruction lives. The remaining viable path through the
in-tree probability machinery is the deferred A8-S2-cont scope
(2000-3500 LoC, probability-normalised cross-poset FKG). That is
not "math simplification" by any reading; it is large-scale
infrastructure work that does not match this arc's brief.

## 4. The four candidate framings — feasibility verdicts

The brief lists four candidate framings as the starting menu. The
polecat picks which to examine seriously. All four are evaluated
below; verdicts are GREEN (recommend execute) / AMBER (conditional
recommend) / RED-fallback (do not execute under polecat scoping
authority — escalate or shelve).

### Framing 1 — Audit-bar revisit (multi-element / ordinal-cut Brightwell variant)

**The proposal.** Introduce a new project axiom of the shape
"multi-element / ordinal-cut Brightwell variant" that delivers
`|Pr_P[x<y] − Pr_A[x<y]| ≤ f(ε(P))` with `f(ε) → 0` as `ε → 0`,
for cuts `(A, B)` of defect `ε`. With such an axiom, A1's
ε-close-to-ordinal-sum reductio (arc 1.0 Candidate A) becomes
viable: the near-ordinal case lifts via the new axiom, the
decomposable case lifts via existing `OrdinalDecomp.hasBalancedPair_lift_*`,
and the K=2 N-poset (which IS an ordinal sum) auto-discharges.
This drops `hC3` outright.

**4-condition audit-bar test.**

| Condition | Status | Reasoning |
|---|---|---|
| **External** | **FAIL** | The required bound is not a transcription of any published result. Brightwell 1989/1999 §4 gives single-element coupling; Kahn-Saks 1984 Lemma 2.2 is also single-element. The defect-aware multi-element form is *not* in the literature. Per arc 1.0 A1 §3.6: any in-tree non-axiom route to such a bound runs through the Steps 5–7 rigidity content — i.e., the bound is **mathematically equivalent** to the project's existing Step-8 G3 window-perturbation argument, which is a structural consequence of the layered decomposition's coherence, not a direct FKG/Brightwell consequence. Calling it an "axiom" would be inventing the math, not citing it. |
| **Difficult** | PASS | If the math existed, formalising it would be ~500-800 LoC mathlib-tier covariance / set-system work. |
| **Labeled** | PASS (could be done) | A `lean/AXIOMS.md` entry per the audit-bar template is mechanical. |
| **Low-risk** | **FAIL** | A forum reader looking at "we axiomatise an ε-aware multi-element Brightwell bound" with no citation would correctly read this as hiding unfinished proofs. The bound is the *content* of the existing rigidity argument — axiomatising it is not "external theorem retained" but "convenience axiom that hides Steps 5–7". `feedback_audit_bar_for_axioms` calls this out: "Convenience axioms that hide unfinished proofs = HIGH (do not retain)". |

**Verdict.** **RED-fallback.** Two of the four conditions fail.
Per `feedback_audit_bar_for_axioms`, axioms with any fail are
eliminated unless overridden by Daniel; this is a Daniel-only
call to override.

**Daniel-side framing if revisited.** The audit-bar relaxation
isn't "let one more axiom in" — it's "let *this particular*
internal-rigidity-argument-as-axiom in", which inverts the
project's discipline (the project's existing axioms are
external-published; this would be the first internal-content
axiom of paper-tier weight). Recommendation: **do not revisit**
under polecat scoping authority. If Daniel wants to revisit, the
appropriate venue is a `feedback_audit_bar_for_axioms` clarifier
mail, not a polecat ticket.

**Polecat-budget execution starting-point if Daniel overrides.**
Document the exact axiom signature in latex (~50k tokens), audit
bar entry (~30k tokens). Total ~80k tokens for the scoping
artefact alone. Lean implementation downstream
(perturbation lemma + trichotomy + decomposable-case lift +
near-ordinal-case lift) ~800-1300 LoC per arc 1.0 scoping doc §A.
Risk under override: same as arc 1.0 Candidate A's Risk 1 fired
at A2 instead of A1 — the far-from-ordinal closure is
illusory and re-derives Steps 5–7. Conditional recommendation:
**do not execute** even with the axiom override.

### Framing 2 — Direct probability bound bypassing FKG

**The proposal.** Bound `δ(P) ≥ 1/3` (or `Pr[x < y] ∈ [1/3, 2/3]`
for some incomparable `(x, y)`) via a direct correlation-
inequality argument that does not go through the existing FKG
sub-claim machinery. Three sub-options, each evaluated:

#### 2a — Brightwell-style covariance applied directly to the cross-poset case

**Math.** Apply the per-term Kahn-Saks / Brightwell covariance
bound on `LinearExt α × Fin (m+1)` directly (Route B of mg-a79e's
brief), treating cross-poset sub-couplings without a separate FKG
sub-claim layer.

**Status.** Already attempted under mg-a79e (Route B). Block-and-
reported case (a) — substantively new mathematical infrastructure
beyond Route-B-style probability-normalised cross-poset FKG. The
polecat audit found that the per-term covariance argument needed
turns out to be substantively novel, not derivable from the
in-tree primitives. F1 (Case2FKGSubClaim direction wrong) was the
surface manifestation; F2 (|Q| ≤ 6 vacuity for Brightwell)
is the deeper obstruction. The deferred A8-S2-cont scope
(2000-3500 LoC, probability-normalised cross-poset FKG) is *the*
viable in-tree path, but it is paper-tier mathematical work, not
"math simplification".

**Verdict.** **RED-fallback.** Already tried under mg-a79e; the
result is documented; polecat scoping authority cannot reverse it.

#### 2b — Kahn-Linial bound (δ ≥ 0.276 → δ ≥ 1/3 via width-3 specialisation)

**Math.** Tighten the unconditional Kahn-Linial covariance bound
`δ(P) ≥ 0.276` to `δ(P) ≥ 1/3` via a width-3-specific refinement
of the Dilworth-3-chain decomposition argument.

**Status.** This is arc 1.0 Candidate D, which arc 1.0 ruled
out-of-scope explicitly: *"This isn't a re-organization of the
existing argument; it's a fundamentally different proof. The brief
explicitly puts 'fundamentally new math' out of scope under
scoping authority and asks the polecat to escalate. … A 'width-3
tightening of Kahn-Linial' of this kind has presumably been
attempted by the original Kahn-Linial / Brightwell line of authors
and others over decades. If it were achievable by a routine
refinement of the existing covariance argument, it would likely
already exist."* (`docs/math-simplification-scoping.md` §1
Candidate D.)

The arc 1.0 verdict on D applies verbatim to 2b.

**Verdict.** **RED-fallback.** Out of polecat scoping authority.
Belongs in a "research arc" or external collaboration — see
framing 4.

#### 2c — Direct argument bypassing the FKG sub-claim machinery entirely

**Math.** Some new structural argument that closes case 2 (within-
band `⪯`-comparable two-sided profile pair) without going through
either the existing FKG sub-claim or chain swap.

**Status.** F1 (mg-a79e) is exactly the report that the natural
sub-claim direction is wrong. F2 (mg-b0de) is exactly the report
that the natural strict-case `≤ 2/3` bound has no in-tree path at
`|Q| ≤ 6`. Together, they say: any direct argument here either
(i) needs the deferred A8-S2-cont infrastructure (2000-3500 LoC,
not "simplification"), or (ii) introduces fresh mathematical
content (escalation). There is no third option known.

**Verdict.** **RED-fallback.** Same as 2a.

**Aggregate verdict on framing 2.** **RED-fallback.** All three
sub-options either (i) reproduce the deferred A8-S2-cont scope
(infrastructure, not simplification), (ii) are paper-level math
discovery (out of scoping authority), or (iii) are already
disposed-of by mg-a79e/mg-b0de.

### Framing 3 — Restrict-and-dispatch (clean dispatch boundary for case-2-strict?)

**The proposal.** Reframe the headline / `lem_layered_balanced`
proof so that the *obstructing* family — K=2 + irreducible +
w ≥ 1 + |β| ≥ 3 with no within-band `⪯`-pair (the N-poset family,
plus its siblings) — is dispatched via a *separate* path,
analogous to how mg-84f2/c0c7/02c2 split off K=2 case-3 with
compound-automorphism. The scoping question in the brief: is
there a *clean* dispatch boundary for **case-2-strict**?

#### 3.1 What "case-2-strict" denotes here

`prop:in-situ-balanced` Case 2 (`step8.tex:3001-3032`) has two
sub-cases under the chain swap analysis (`mg-ba0c`,
`Case2Rotation.lean:629`):

* **Symmetric-collapse case.** Chain swap is a bijection,
  forcing `probLT a a' = 1/2` exactly. Already absorbed into
  Case 1 by `case2Witness_balanced_or_strict` (mg-8801).
* **Strict case ("case-2-strict").** Chain swap is a strict
  injection — `probLT a a' < 1/2`. To close the balanced-pair
  goal we additionally need `probLT a' a ≤ 2/3`. The
  case-2-strict closure depends on this `≤ 2/3` upper bound.

#### 3.2 The dispatch boundary question

**Sub-question A.** Can the N-poset family be split off so that
the residual `Case3Witness` becomes provable for the rest?

This is essentially **Track 1's job** (`mg-b666` —
compound-automorphism extension of mg-84f2/c0c7/02c2). The
scoping doc for that work is `docs/path-c-cleanup-roadmap.md`
§6a. Track 2 should not duplicate it. If Track 1 lands, the
restricted residual `Case3Witness` is provable with the existing
(non-N-poset) structural arguments + finite enumeration for
inScope. If Track 1 stalls, the question reverts to the existing
park decision.

**Sub-question B.** Independent of Track 1, can case-2-strict be
made unconditional via a different dispatch? Three candidate
routes:

* **B1 — Probability-bound dispatch.** Discharge the `≤ 2/3`
  upper bound directly. F2 (mg-b0de, 2026-04-27) **closes this
  off**: at K=2 with |Q| ≤ 6 the Brightwell coupling is vacuous;
  iterated Brightwell is even weaker; bipartite enumeration is
  K=2 w=0 only; cross-poset count-form FKG gives the wrong
  normalisation. There is no in-tree path. **RED.**

* **B2 — Finite-enumeration certificate dispatch.** Build a Bool
  certificate (analogous to F5a's `case3_certificate`) for K=2,
  case-2-strict, parameter range `(w ∈ {1, 2, 3, 4}, |α| ≤ 6)`.
  The K=2 + width-3 + bounded-cardinality + irreducible
  isomorphism classes are finite and machine-enumerable. This
  is `docs/path-c-cleanup-roadmap.md` §6b ("K=2 finite
  enumerator alternative"). Estimated 300-500 LoC including
  the Bool→Prop bridge.

  **Tradeoff.** Mechanical, not aesthetic. It does **not**
  obviate `Case3Witness` by itself — Case3Witness's universal
  scope still includes layered configurations outside the K=2
  small-cardinality regime. It does narrow the residual gap
  enough that compound-automorphism (Track 1) becomes optional.
  But this *replaces* the structural argument (which has
  re-use value, per `path-c-cleanup-roadmap.md` §4) with raw
  enumeration, which has no re-use value beyond this case.

  **Overlap with Track 1.** Track 1 is targeting the same
  family via compound-automorphism. If Track 2 ships a finite-
  enumeration certificate for K=2 case-2-strict, it competes
  with rather than complements Track 1. PM judgement call.

  **Verdict on B2 considered as a Track 2 deliverable.**
  **AMBER as a Track 1 fallback** — sensible if Track 1
  block-and-reports with new infrastructure blockers
  (per `path-c-cleanup-roadmap.md` §7's revival-conditions
  framework). **Not aesthetic** in the brief's sense, so does
  not satisfy the math-simp arc's stated goal of finding a
  "fresh framing that obviates Case3Witness". Closer to arc 1.0
  Candidate C than to a math simplification.

* **B3 — Parametric refinement of the layered decomposition
  hypothesis.** Strengthen `LayeredDecomposition` to a richer
  structure that excludes the K=2 + irreducible + w ≥ 1 family
  by construction (e.g., "fully-coherent layered" requiring
  within-band ⪯-pairs to exist, with a separate proof that
  width-3 non-chains admit fully-coherent layered decompositions
  outside the named family).

  **Status.** The "separate proof" is the question. The named
  family *is* the obstruction precisely because it admits a
  layered decomposition but no within-band ⪯-pair. Strengthening
  the data structure does not change the underlying combinatorial
  fact; it just shifts where the obstruction lives in the proof.
  **RED — moves the burden, doesn't remove it.**

**Sub-question C.** The brief's literal phrasing — "is there a
*clean* dispatch boundary for case-2-strict?" — is asking
whether the dispatch *itself* (independent of how each branch
is closed) can be cleanly sliced. Yes: at the typed-witness
level, mg-8801 already cleanly splits case 2 into
symmetric-collapse vs. strict via `case2Witness_balanced_or_strict`
(`step8.tex:3001-3032`, `Case2Rotation.lean:686`). The
strict branch's *closure* is the open question, not its
*dispatch*.

#### 3.3 Aggregate verdict on framing 3

**RED-fallback as a stand-alone Track 2 deliverable.**

Reasons:

1. Sub-question A is Track 1's job; Track 2 should not duplicate.
2. Sub-question B's only viable route (B2, finite enumeration) is
   mechanical, not aesthetic, and competes with Track 1 rather
   than complementing it.
3. None of B1/B2/B3 obviates `Case3Witness` cleanly — at best they
   narrow its scope.

If Track 1 stalls and PM commissions a follow-on "shrink the gap
mechanically" arc, B2 is the right starting point. That is a
*future* PM call, not a current Track 2 deliverable.

### Framing 4 — Different proof entirely (Brightwell-pump / Kahn-Saks / Linial alternate route)

**The proposal.** Pursue an entirely different proof of the
width-3 1/3-2/3 conjecture that does not depend on the BK /
Cheeger / fiber / coherence / globalization / layered structure of
the current paper. Brightwell-pump research arc OR
Kahn-Saks / Linial alternate-route. The brief flags this as a
*"multi-week external collaboration; this ticket scopes only what
would be a polecat-doable starting point"*.

**Status.** Same as arc 1.0 Candidate D: paper-level math
discovery, out of polecat scoping authority. The `feedback_audit_bar_for_axioms`
discipline applies analogously to math-content axioms — we don't
introduce new content under scoping.

**Polecat-doable starting point.** A literature audit could fit
in ~100-200k tokens:

* Survey published refinements of Kahn-Linial 1991 in width-3 /
  width-bounded cases.
* Survey Brightwell 1989/1999 pump-style arguments and their
  successor literature.
* Document which results, if any, give bounds in the
  `[0.276, 1/3)` gap for width-bounded posets.
* Identify whether any published result, taken as a
  paper-internal axiom under audit-bar, would close the
  obstruction.

**Aggregate verdict on framing 4.** **RED-fallback as a Track 2
execution deliverable.** A literature audit is a sensible
*precursor* to a future research arc, but the deliverable of *this*
ticket is a feasibility verdict on framings, not a literature
survey. If PM wants a literature audit it should be a separate
`mg-*` ticket (~150k tokens, doc-only, latex-rigor).

## 5. Survey summary table

| Framing | Aesthetic | Drops `hC3`? | In scope under brief? | Verdict |
|---|---|---|---|---|
| **1** Audit-bar revisit (multi-elem Brightwell axiom) | High if works | YES | NO — fails 2/4 audit-bar conditions; Daniel-only override | **RED-fallback** |
| **2a** Direct cross-poset Brightwell covariance | Medium | YES if works | NO — mg-a79e block-and-report; A8-S2-cont scope is ~2000-3500 LoC | **RED-fallback** |
| **2b** Width-3 Kahn-Linial tightening | Highest if works | YES | NO — paper-level math discovery (= arc 1.0 D) | **RED-fallback** |
| **2c** Direct case-2 argument bypassing FKG | Medium | YES if works | NO — mg-b0de RED on `|Q| ≤ 6` regime | **RED-fallback** |
| **3 / sub-A** Compound-automorphism dispatch for N-poset | Good (structural) | YES | Track 1's job | **Out of scope (duplication with Track 1)** |
| **3 / sub-B2** Finite-enumeration certificate for K=2 case-2-strict | Low (mechanical) | Partially (narrows scope) | YES but off-criterion | **AMBER** as Track 1 fallback only |
| **3 / sub-B1, B3** Probability bound / refined data structure | — | — | NO — disposed of by mg-b0de | **RED** |
| **4** Brightwell-pump / Kahn-Saks alternate proof | Highest if works | YES | NO — multi-week external research; out of polecat scope | **RED-fallback** |

**Zero GREEN. One AMBER (3/B2) only as a Track 1 fallback, not
recommended as a standalone Track 2 deliverable.**

## 6. Verdict and recommendation

### 6.1 Headline verdict

**No good framing found this round; Track 1 remains the path.**

This is the explicit allowed stop-loss outcome from the brief
(*"a valid outcome and should be filed"*) and matches the
recommendation tier in `feedback_distinguish_arc_chunk_outcomes`'s
mixed-outcome framing rule.

### 6.2 Why Track 2 was right to scope but wrong to find a winner

The 2026-04-27 mg-a79e / mg-b0de findings (post-arc-1.0
block-and-reports landing during the η₃ / η₄ / η₅ pivot week)
**materially shrunk the search space** for math simplifications
relative to what arc 1.0's scoping doc evaluated. Specifically:

* Arc 1.0 evaluated framings 2a/2c under the assumption that
  cross-poset / FKG-sub-claim machinery had latent strength.
  mg-a79e (provably-false sub-claim) closed off the natural
  reading.
* Arc 1.0 evaluated framings 1/2 under the assumption that
  Brightwell-style coupling extends to the strict pair regime.
  mg-b0de (vacuous at `|Q| ≤ 6`) closed off that hope.

The brief's "fresh framings" phrasing assumed that since arc 1.0,
*new* math could become viable. The opposite happened: in the
window between arc 1.0 close (2026-05-02) and this scoping pass
(2026-05-04), two findings have *contracted* the viable frame
space, not expanded it.

### 6.3 What this means for headline `hC3` removal

**Track 1** (`mg-b666`, compound-automorphism extension on `main`)
remains the path. Per
`docs/path-c-cleanup-roadmap.md` §6a, the in-tree infrastructure
for K=2 same-band compound-automorphism already landed
(mg-84f2 / c0c7 / 02c2, `c513c8d`). The remaining work is
extending the structural matching lemma (mg-c0c7) and dispatch
(mg-02c2) to cover the residual K=2 + irreducible + w ≥ 1 +
|β| ≥ 3 N-poset family.

If Track 1 block-and-reports, the **only** Track-2-flavoured
fallback that does not require fresh axioms or fresh math is
**framing 3 sub-option B2** (finite-enumeration certificate for
K=2 case-2-strict, ~300-500 LoC, `docs/path-c-cleanup-roadmap.md`
§6b). That is mechanical, not aesthetic, and explicitly does not
obviate `Case3Witness` cleanly — it narrows the residual gap.
**File a separate ticket if Track 1 stalls; do not file under
this scoping doc.**

### 6.4 Recommended next chunk

**None.** The brief's GREEN-recommend-execute outcome is not met.

The brief's RED stop-loss outcome ("no good framing found this
round; Track 1 remains the path") **is** met, and is the
recommended PM action. Specifically:

1. **Close `math-simp-arc-2.0` after this scoping doc lands** — do
   not commission downstream chunks under this branch.
2. **Track 1 (`mg-b666`) on `main` carries the headline cleanup
   workload.** If it lands, `hC3` drops. If it stalls, escalate
   per Track 1's stop-loss.
3. **If Track 1 stalls AND PM wants an additional shrink-the-gap
   arc**, the only viable in-tree starting point is finite-
   enumeration B2 (per §6.3); file as a separate ticket under a
   new branch or directly on `main`. Estimated 300-500 LoC,
   single polecat session, mechanical.
4. **If Daniel chooses to override the audit-bar discipline** for
   framing 1's multi-element Brightwell axiom, that is a
   `feedback_audit_bar_for_axioms` clarifier-mail decision, not
   a polecat ticket. The polecat estimate under override is in
   §4 framing 1.
5. **Park research-arc framings 2b / 4** for indefinite future
   external collaboration. If a published result emerges that
   would close the `[0.276, 1/3)` gap in width 3, file a fresh
   audit-bar evaluation at that time.

## 7. Risk inventory

The brief asks for a risk inventory at minimum: axiom-bar,
signature-regression, scope creep. All apply to the framings
even though all RED out; they would have applied if any were
GREEN, and the asymmetry is itself informative.

### 7.1 Axiom-bar regression

Framings 1 and 2 (in their natural readings) introduce or
require new project axioms. The 4-condition test from
`feedback_audit_bar_for_axioms` flags both as failing — framing
1 explicitly (§4 audit table), framing 2 implicitly (the
"fresh paper-level math" version is exactly the kind of
"convenience axiom that hides unfinished proofs" the discipline
is meant to prevent). **Risk under any GREEN execution: forum
embarrassment.** This is the headline reason the audit-bar
discipline holds.

### 7.2 Signature regression

`feedback_signature_regressions` (the related discipline) holds
that *replacing* `hC3` with a different hypothesis of comparable
mathematical weight is **not** progress; it is signature
regression in disguise. Framing 3/B2 risks this by replacing
`hC3` with an `hEnum` certificate-output hypothesis — the
discharge would be parametric, not closed. (Modulo: B2 if fully
discharged via the Bool-certificate pattern stays closed; if
the certificate has a typed `hEnum` slot, it doesn't.)
`mg-26bb`'s outer-loop bridge pattern is the right reference.

**Risk under B2 execution as a fallback:** mid-arc finding that
the K=2 case-2-strict certificate has a typed-witness escape
hatch analogous to the one mg-3fd8 closed for case-3 in scope.
Mitigated by careful certificate scope design at chunk-1.

### 7.3 Scope creep

Framing 4's literature audit is the only framing with non-trivial
scope-creep risk. A literature audit can grow without bound. If
ever filed, the deliverable should be capped at ~150k tokens
with a "found / not found / inconclusive" verdict per cited
result, not an exhaustive survey.

### 7.4 Duplication with Track 1

Framing 3 sub-A is direct duplication with Track 1's
compound-automorphism work; framing 3 sub-B2 is partial
duplication (same family, different mechanism, same result on
that family). PM judgement call.

**Risk under simultaneous Track 1 + B2 execution:** the two
might solve the same family redundantly, with B2 shipping
mechanical close while Track 1 ships structural close. Net
effect: Track 1's compound-automorphism infrastructure becomes
unused for that family. Mitigated by holding B2 in reserve as a
Track 1 fallback only.

### 7.5 Research-arc lock-in

Framing 4 (literature audit), if it surfaces a viable published
result, could trigger a multi-month external collaboration
commitment. Daniel-only call to enter that mode.

## 8. Stop-loss verdict

Per the brief: *"If a framing recommends introducing a new project
axiom, STOP and escalate — Daniel-only call to relax the audit-bar
discipline."* Framing 1's audit-bar revisit triggers this stop-
loss verbatim. **Polecat does not propose the axiom.** This doc
records the analysis; PM relays to Daniel; Daniel decides whether
to override.

Per the brief: *"If polecat surfaces fundamentally new math
(paper-level discovery), STOP and escalate."* Framings 2b and 4
trigger this stop-loss verbatim. **Polecat does not pursue them.**

Per the brief: *"'No good framing found' is a valid outcome;
report as a status doc with explicit reasons per framing."*
**This is the verdict for the doc as a whole.** Reasons are
recorded per-framing in §4 and aggregated in §6.

## 9. References

### Code anchors

* `lean/OneThird/MainTheorem.lean:52-57` — current headline
  with `hC3 : Step8.Case3Witness` (intentional retention under
  option (δ); `hC3` retention preamble-doc lines 39-51).
* `lean/OneThird/Step8/LayeredBalanced.lean:438-444` —
  `Case3Witness` def, intentional `def`-not-theorem retention
  preamble-doc lines 420-437.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
  — the in-tree `brightwell_sharp_centred` axiom (single-element
  bound; the bound that arc 1.0 A1 found insufficient).
* `lean/OneThird/Step8/ExcPerturb.lean:351` — `exc_perturb`
  iterated bound `2k/(n−k+1)`; the `Θ(1)` bound on balanced cuts
  that is the load-bearing obstruction for any "axiom-light"
  framing 1 reading.
* `lean/OneThird/Step8/Case2Rotation.lean:686, 772` —
  `case2Witness_balanced_or_strict` (mg-8801) and
  `Case2FKGSubClaim` (mg-27c2; provably false in `pair` field
  per mg-a79e).
* `lean/OneThird/Step8/Case3Residual.lean` — A8-S3
  `case3Witness_hasBalancedPair_outOfScope` axiom (paper-internal
  per `rem:enumeration` sketch; passes audit-bar with explicit
  labelling).
* `lean/OneThird/Step8/Case3Struct.lean` —
  `hasBalancedPair_of_ambient_profile_match` (mg-f92d, Case 1
  general ambient form). Reusable for future case-1 dispatch.
* `lean/AXIOMS.md` — current axiom inventory and audit-bar
  disclosures.

### Doc anchors

* `docs/math-simplification-scoping.md@638ad1e` — arc 1.0 scoping
  pass (parent of this doc).
* `docs/math-simplification-A1-feasibility.md` — arc 1.0 A1
  RED-fallback verdict (Brightwell + exc_perturb cannot give
  `f(ε) → 0` for balanced cuts).
* `docs/path-c-cleanup-roadmap.md` — Track 1 reference; §6a/6b
  enumerate the in-tree paths for the K=2 N-poset family closure;
  §7 enumerates revival conditions; §10 enumerates code anchors.
* `docs/a8-path-b-block-and-report-status.md` (mg-a79e) — the
  Case2FKGSubClaim direction-wrong finding (F1 in this doc §3.1).
* `docs/a8-s2-restate-block-and-report-status.md` (mg-b0de) — the
  `≤ 2/3` upper bound vacuity finding (F2 in this doc §3.2).
* `docs/a8-s2-rotation-residual-status.md` (mg-ba0c) — the chain
  swap analysis underlying §3.1 / 3.2.
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — the strict
  case 2 closure pinned to the chain-form FKG sub-claim.
* `simplifications.md` (top-level repo file) — arc 1.0 Candidate B
  source; B1 shipped as `b6b6c3f` (mg-805c).

### Memory / discipline anchors

* `feedback_audit_bar_for_axioms` — the 4-condition test invoked
  in §4 framing 1 and §7.1.
* `feedback_latex_first_for_math_simp` — the discipline this doc
  follows.
* `feedback_distinguish_arc_chunk_outcomes` — the closure-framing
  discipline applied in §6.1 / §6.2 ("no GREEN found, Track 1
  remains the path", not "framing 3/B2 might work as a Track 1
  fallback").
* `feedback_signature_regressions` — the discipline applied in
  §7.2.

### Reminders

* Reminder `pm-onethird/1777914292578721000.5852.1000`
  (Daniel 2026-05-04T17:04Z) — the parent direction setting both
  Track 1 and Track 2.
* Reminder `pm-onethird/1777913883871871000.98139.2000`
  (Daniel 2026-05-04T17:58Z) — the framing-discipline
  course-correction that motivated
  `feedback_distinguish_arc_chunk_outcomes`.

## 10. Status close-out

* **Branch.** `math-simp-arc-2.0` (parallel to `main`, parent
  commit `203bb4f`). This commit is the Track 2 deliverable.
* **Outcome class** (per `feedback_distinguish_arc_chunk_outcomes`):
  **substantive scoping chunk = no good framing found.** The
  scoping is itself the deliverable; no parallel cleanup chunk
  is bundled. Headline `hC3` unchanged by Track 2.
* **PM action items.**
  1. Review this doc.
  2. Confirm Track 1 (`mg-b666`) is the live path for headline
     `hC3` removal.
  3. If Track 1 lands cleanly, archive Track 2 deliverable as
     "no GREEN framing found, Track 1 superseded the
     simplification effort."
  4. If Track 1 stalls, optionally commission a separate
     mechanical follow-on (B2 finite enumeration) per §6.4.4.
     Do **not** commission under `math-simp-arc-2.0`; new
     ticket, new branch.
* **Daniel-only escalation items** (per §8 stop-loss):
  - Override audit-bar discipline for framing 1 axiom (§4
    framing 1).
  - Authorise external research-arc commitment for framing 4
    (§4 framing 4).
  Both are explicit non-defaults; polecat does not propose
  either.
