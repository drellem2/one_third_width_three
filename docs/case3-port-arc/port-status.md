# `case3Witness_hasBalancedPair_outOfScope` axiom port — status report

**Work item:** `mg-e850` (polecat `pe850`).
**Branch:** `polecat-pe850` (target `case3-port-arc`).
**Verdict:** **STOP — trip-wire #4 fires.** No Lean source changes
landed. Recommend the ticket be re-scoped or rolled into the
deferred A8-S2-cont arc; a single-polecat 700k-token port of this
axiom is not feasible against the current in-tree FKG primitives.

---

## 1. Trip-wire diagnosis

The polecat brief lists seven explicit STOP triggers. The relevant
firing in this report:

> **Trip-wire #4.** A8-S2-cont infrastructure dependency surfaces.
> If step (2) requires the deferred ~2000-3500 LoC probability-form
> cross-poset FKG infrastructure rather than the existing in-tree
> primitives, STOP and escalate. That's a multi-week multi-polecat
> scope, not a single ticket.

This trip-wire fires. Detail in §3 below. Trip-wire #5 (paper sketch
genuinely under-developed) is borderline-firing as well — see §4.

The decision to STOP early was made after read-only investigation
(no Lean changes, no partial code), to avoid burning budget on a
provably-blocked path. Approximate token spend on the analysis:
~60k of the 700k budget.

## 2. Step 1 — pigeonhole on shared profile coordinates

**Status: feasible with current infrastructure.** Estimated
~80-150 LoC.

The pigeonhole argument from the paper sketch
(`step8.tex:3157-3173`): given a width-3 within-band antichain
`{a₁, a₂, a₃} ⊆ bandSet k` whose two-sided profiles are pairwise
`⪯`-incomparable, two of the three must agree on at least one
coordinate of the two-sided profile, using:

* (L1) `band_size : ∀ k, |bandSet k| ≤ 3`
* (L2-forced) `∀ x y, band x + w < band y → x < y`
* `|Q| ≤ 3 (3w+1) = 9w+3` (paper) → in-tree the tighter `|α| ≤ 6w+6`
  cap is hypothesised, which subsumes the paper bound for `w ≥ 1`
  (and matches at `w = 1`: `12 = 12`).

The (L1)/(L2) bookkeeping needed for this step is in tree
(`lean/OneThird/Step8/LayeredReduction.lean`, in particular
`band_size`, `forced_lt`, `cross_band_lt_upward`). The argument is
combinatorial counting on the joint codomain of the two-sided
profile.

Step 1 alone is not the deliverable (axiom must be removed entirely),
so writing it as a standalone lemma would constitute "parallel
cleanup" — the brief's `feedback_distinguish_arc_chunk_outcomes`
disallows this on a `substantive port chunk; no parallel cleanup`
assignment.

## 3. Step 2 — band-restricted Case 2 FKG sub-coupling — BLOCKED

**Status: blocked on missing probability-normalised cross-poset FKG
infrastructure.** This is the firing of trip-wire #4.

### 3.1 What the step needs

From a shared coordinate pair `(aᵢ, aⱼ)` whose profiles agree on Π⁺
but disagree on Π⁻ (or vice versa), build a Case 2 pair with aligned
one-sided profiles **restricted to the bands strictly above (or
strictly below) the antichain under consideration**. The FKG
monotonicity then needs to operate on this band-restricted
sub-context and yield a `probLT` bound usable by the Case 1 / Case 2
discharge.

The "yield a `probLT` bound" half is the substantive content. To
land a balanced pair in the original `α`, we need a
**probability-normalised** cross-poset comparison: roughly,

```
| probLT_Q[a < a']  −  probLT_{Q'}[a < a'] |  ≤  ε
```

for `Q ⊆ Q'` differing by the strict-`<` edges contributed by the
sub-band, with `ε` small enough to preserve the `[1/3, 2/3]`
balanced-pair window. The paper's sketch routes through a Daykin–
Saks-style FKG correlation in the sub-band lattice and lifts back
via this comparison.

### 3.2 What is actually in tree

The cross-poset FKG infrastructure that lands in tree
(`lean/OneThird/Mathlib/RelationPoset/FKG.lean`, mg-b088 and
predecessors):

| Lemma | Form | Suitable for step 2? |
|---|---|---|
| `sum_initialIdeal'_le_of_subseteq` (`:381`) | absolute (un-normalised) sum monotonicity under `Q ⊆ Q'` | ❌ — no probability normalisation |
| `probLT'_mono_of_relExt` (`:464`) | restricted-numerator: smaller count `/` *larger* denominator | ❌ — wrong denominator |
| `probLT'_count_div_le_of_relExt` (`:521`) | direct corollary of the above with the same denominator pathology | ❌ |

The file's own docstring on `probLT'_mono_of_relExt`
(`RelationPoset/FKG.lean:506-516`) is explicit:

> Strictly speaking, the displayed inequality compares the
> *restricted-numerator* probability — i.e. dividing the smaller
> count by the *larger* (`Q`-side) denominator `numLinExt' Q` —
> and is therefore weaker than the standard Daykin–Saks "drops"
> inequality between the two genuine averages. **The standard form
> requires FKG positive correlation between the `S`-event and the
> "`L` respects new `Q'`-comparabilities" event in the
> `LinearExt' Q` lattice, recorded as a follow-up in
> `docs/a8-s2-status.md`.**

I.e., the in-tree `probLT'_mono_of_relExt` is the count-form headline
only; the probability-normalised form needed for the case-3 step 2
sub-coupling is the explicitly-deferred follow-up.

### 3.3 What is deferred

`docs/a8-s2-status.md:159` (estimated cost), `:269` (named
"A8-S2-cont — Cross-poset coupling infrastructure (the actual
blocker)"), `:391-409` (Route B: tighter bounds from the
cross-poset coupling in probability-normalised form):

> **Estimated cost:** ~2000-3500 LOC. Cleaner-feeling but actually
> the probability-normalised form is dominated by the cross-poset
> infrastructure layer.

This is the deferred infrastructure. Step 2 of the case3 port is
not a smaller, distinct piece — it is one of the consumers that
A8-S2-cont's probability-normalised form would unblock. Without
A8-S2-cont, step 2 cannot be formalised against the existing
primitives.

### 3.4 Why this is not "just use the count form"

The count-form `probLT'_mono_of_relExt` gives:

```
|{L' ∈ LE Q' : S}|  ≤  |{L ∈ LE Q : S}|
```

Step 2 needs to derive a probability `probLT_Q[a < a'] ∈ [1/3, 2/3]`
on the *full* poset `Q` from a probability bound on a *sub-band*
poset `Q' ⊋ Q`. The count form's comparison is in the wrong
direction for that derivation; even when re-ordered (for the
appropriate `Q ⊆ Q'`), the absence of normalisation by
`numLinExt'` on both sides blocks the quotient that yields a
probability statement.

This is precisely the diagnosis F2 from
`docs/why-hC3-is-structural.md` §2 promotes to a structural fact
(in the K=2 setting). The K ≥ 3 + ¬InCase3Scope analogue is
exhibited here: the count-form is sharp for the un-normalised
inequality but vacuous for the probability-normalised target.

## 4. Trip-wire #5 — paper-sketch under-development (borderline)

The brief lists trip-wire #5 separately:

> 5. **Step (2) requires a new mathematical theorem not in
> `rem:enumeration`.** STOP — that means the paper's sketch is
> genuinely under-developed and porting requires filling in math
> the paper doesn't have. Daniel-only call.

The QA verdict on the axiom (`mg-7377`,
`lean/AXIOMS.md:379-454`) explicitly notes the paper's sketch is
"genuinely a sketch (not a fleshed-out proof)" but a "credible
structural argument". So:

* The *high-level argument* (pigeonhole + sub-coupling + Case 1/2
  reduction) is in `rem:enumeration`. Not new math.
* The *probability-normalised cross-poset FKG sub-coupling* is the
  detail the sketch defers. Filling it in is in spirit "fleshing
  out the paper sketch", not strictly inventing new math, since
  the paper appeals to standard FKG / Ahlswede–Daykin
  correlation. But it is "math the paper doesn't have" in the
  sense that the explicit sub-coupling construction is not
  written down.

This puts trip-wire #5 in a borderline state. Trip-wire #4 fires
unambiguously, so the STOP recommendation rests on #4; #5 is
recorded for completeness.

## 5. Step 3 — reduction back to Case 1 / Case 2

**Status: feasible if step 2 lands.** Estimated ~50-100 LoC.

With the sub-coupling in hand, exhibit the explicit balanced pair:
either via `Step8.hasBalancedPair_of_ambient_profile_match`
(`Case3Struct.lean`, mg-f92d) for the Case 1 reduction, or via
a A8-S2 `Case2Witness L → HasBalancedPair α` discharge for the
Case 2 reduction. Both consumers exist in tree and are pluggable.

This step is not on the critical path — it sits downstream of step
2 and inherits the block.

## 6. Bundle scope reality

Per `lean/AXIOMS.md:319-323`:

> Steps (1) and (3) are routine. Step (2) is the substantive new
> mathematical content of the axiom. The original A8 brief
> estimated "~300-600 LoC including the missing mathematical
> content"; in practice this is a lower bound, since
> `rem:enumeration` is a sketch rather than a fleshed-out proof.

The ~300-600 LoC estimate presumes the cross-poset FKG primitive
exists. With A8-S2-cont deferred, the realistic scope balloons to
~2000-3500 LoC (A8-S2-cont infrastructure) + 200-450 LoC (the
case-3-specific sub-coupling, pigeonhole, and reduction). That
exceeds the brief's 900 LoC trip-wire #7 by a factor of ~3-4 and
matches trip-wire #4's "multi-week multi-polecat" scope warning.

## 7. Why "do nothing" is the right call

Per `feedback_polecat_stop_runaway`:

> Each trip-wire fires `feedback_polecat_stop_runaway`: block,
> report, no auto-extension; PM mails Daniel; return to mg-344a
> workspace.

Per `feedback_audit_bar_for_axioms`:

> Goal is axiom-count reduction.

Landing partial code (step 1 only, as a standalone lemma) does
*not* eliminate the axiom — the deliverable is unchanged. Per the
brief's outcome-class line:

> **substantive port chunk; no parallel cleanup.** Lean module +
> axiom removal IS the deliverable.

A standalone step-1 lemma without axiom removal is parallel
cleanup, which the brief disallows on this assignment. The honest
disposition is therefore: zero Lean changes, status doc, escalate.

## 8. Recommendation

* **Do NOT re-spawn this ticket against the current tree.** The
  block is structural, not effort-bound; another polecat session
  would rediscover the same trip-wire.
* **Do** consider one of:
  * (A) Bundle this work into the A8-S2-cont arc. Once A8-S2-cont
    lands the probability-normalised cross-poset FKG, the case3
    port becomes an in-scope ~300-600 LoC follow-up.
  * (B) Defer indefinitely. The headline trust surface today is
    `[propext, Classical.choice, Quot.sound, brightwell_sharp_centred,
    case3Witness_hasBalancedPair_outOfScope, 5 × _native.native_decide]`
    (`lean/PRINT_AXIOMS_OUTPUT.txt`, post-mg-8c72). The
    `case3Witness_hasBalancedPair_outOfScope` axiom is honestly
    disclosed in `lean/AXIOMS.md:226-454` with a thorough
    paper-vs-formalisation diagnosis; the trust surface is
    publishable as-is.
  * (C) Replace the axiom with a stronger Injective-restricted
    variant. The sole consumer (`OptionC.Case3Witness_proof`,
    `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:494`)
    invokes the axiom under `Function.Injective LB.band`.
    Under Injective, `Case2Witness L` is vacuous. A custom
    consumer-side argument might close the residual without the
    axiom in this restricted regime — but it would still need
    the cross-poset FKG (or a substitute) for the Case 1 /
    Π⁺-Π⁻ asymmetry analysis.

Option (A) is the cleanest — the work is one substantive arc,
not two separate ones. Option (C) is a possible middle path but
requires a separate scoping pass on whether the Injective regime
admits a simpler argument.

## 9. References

* `lean/OneThird/Step8/Case3Residual.lean:208` — the axiom
  declaration (unchanged in this report).
* `lean/AXIOMS.md:226-454` — the existing axiom disclosure.
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:490-498` —
  the sole operational consumer (Injective-capped).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:381,464,521` — the
  in-tree cross-poset FKG primitives (count form only).
* `docs/a8-s2-status.md:159,269,391-409` — A8-S2-cont scope and
  the named "the actual blocker" call-out.
* `docs/why-hC3-is-structural.md` §2 (F2) — the K=2 sibling
  diagnosis; same probability-normalisation gap.
* `docs/case3witness-operational-audit.md` (mg-e0b8) — the prior
  consumer audit confirming the K ≥ 3 leaf coverage block.

## 10. Polecat protocol

* `mg claim mg-e850` — done.
* `pogo schedule … mail-check-mg-e850` — done.
* No Lean source changes — by trip-wire-induced design.
* This status doc — done (the deliverable on a STOP-and-report
  trip-wire firing).
* Mail to mayor — pending immediately after this doc is
  committed.
* `mg done` — **NOT** to be called; the ticket should remain in
  its claimed-but-blocked state pending Daniel's disposition
  (re-scope, defer, or re-route per §8).
* Stay alive — yes.
