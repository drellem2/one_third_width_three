# Cumulative state — Case3Witness architecture (interaction-radius bound)

Tracks the Case3Witness lemma architectural-analysis arc dispatched
by Daniel directive 2026-05-17T12:55Z. Companion to
`docs/case3witness-operational-audit.md` (mg-e0b8) and
`docs/why-hC3-is-structural.md`.

---

## Session 1 — mg-e2e9 (2026-05-17), polecat: math-paper + Step8 LayeredBalanced specialist

**Trigger.** Daniel re-reviewed the Case3Witness lemma supplied by
pm-onethird (mail 2026-05-17T00:42Z, the corrected post-mg-e0b8
analysis) and identified that the four-cap signature does not
bound the layered decomposition's interaction width `LB.w` from
above. Verbatim:

> "The interaction radius for instance is not bounded, and so we
> don't actually know that there is a meaningful layered structure
> and not just a trivial one. If the coherence-collapse case
> upstream is doing real work, imo there should be another bound
> here."

**Polecat dispatch.** Math-paper polecat + Step8 LayeredBalanced
specialization, paper-and-pencil, 300k single-session, no Lean
code changes (analysis-only ticket).

**Verdict.** **AMBER-missing-bound-fix-proposed.**

* Daniel's diagnosis verified mechanically: caps 2 (`K ≤ 2w+2`) and
  3 (`|β| ≤ 6w+6`) are *ratio* bounds, vacuous when `w` is
  unbounded. The operational call site
  (`LayeredBalanced.lean:668`) substitutes
  `canonicalLayered α` with `K = w = |α|`, making the
  (L2-forced) axiom literally vacuous. The universal
  `Case3Witness β` instantiated via `canonicalLayered β`
  satisfies caps 1-4 trivially for **every** finite width-3
  non-chain `β`, so `Case3Witness ⇔ headline theorem` (modulo
  K=1 which is independently closed).
* Missing bound: `LB.w ≤ W₀` (cap 5), with `W₀ = 4` the
  F5a-aligned constant (matches `InCase3Scope.w_mem`).
* With cap 5: `|β| ≤ 30`, `K ≤ 10`, `w ∈ {1, 2, 3, 4}` —
  finitely-decidable.
* Downstream: cap 5 invalidates the canonicalLayered substitution;
  the K ≥ 2 dispatch must be rewritten to use the upstream
  `layeredFromBridges`-supplied `L` (Option A), F3 strong-induction
  (Option B), or to drop `hC3` entirely (Option C). All three
  intersect the K=2 case-2-strict residual already parked under
  option (δ) per `why-hC3-is-structural.md`.
* No new mathematical obstructions; the fix is named at the lemma
  level; downstream blockers are previously disclosed.

**Architectural framing — the "real work" of coherence-collapse.**
The paper's Steps 1-7 (BK-Cheeger / fiber-coherence / staircase /
collapse) are *supposed* to deliver a layered decomposition with
`L.w ≤ w₀(γ)` constant in `|α|`. The current Lean
`layeredFromBridges` extractor returns `w = Lwidth3.bandwidth`
(threaded faithfully from Step 7), but Step 7 itself is not yet
proved with the bounded-bandwidth constant — the Step 7
existential is extracted at `bandwidth = |α| + 1` per the
`ChainPotentials` cleared-denominator audit. So the upstream
chain *intends* to deliver bounded `w`, but the in-Lean
realisation does not yet.

The K ≥ 2 dispatch in `lem_layered_balanced` *bypasses* the
upstream `L` entirely (via the canonicalLayered substitution).
Daniel's "interaction radius unbounded" diagnosis exactly names
this bypass. The fix (cap 5) forces the dispatch to *use* the
upstream `L` (or accept failure).

**Deliverables (this session).**

* `docs/onethird-Case3Witness-architecture-analysis.md` — the full
  Phase A-D analysis. 7 sections + verdict + cross-references.
  Identifies: (a) interaction radius = `L.w`; (b) the canonicalLayered
  substitution vacuity vector; (c) the circular reading
  `Case3Witness ⇔ headline`; (d) the cap-5 fix and its downstream
  consequences.
* `docs/state-Case3Witness-architecture.md` (this file) — cumulative
  state.

**No code changes** per ticket hard constraint.

**Recommended follow-on tickets** (priority order, *not* filed in
this session):

1. LEAN signature-restatement: add cap 5 to `Case3Witness.{u}`,
   propagate. Expected to surface the operational gap as a type
   error at `LayeredBalanced.lean:668` — the *intended* outcome.
   Est: 50-100 LoC for signature; weeks for dispatch rewrite (split).
2. LEAN residual-axiom-tightening: restate
   `case3Witness_hasBalancedPair_outOfScope` with `LB.w ≤ 4`. The
   residual claim becomes a small finite enumeration. Est:
   200-400 LoC.
3. LEAN operational-dispatch rewrite: replace canonicalLayered
   substitution with Option A/B/C. Multi-polecat, blocked on
   `path-c-cleanup-roadmap.md` items.
4. MATH paper-level: audit `w₀(γ)` constant from Steps 1-7; pin
   the upstream-derived `W₀` value. Math-paper polecat, 100-200k.

**Cross-reference.** Consistent with and a structural refinement
of:

* `docs/case3witness-operational-audit.md` (mg-e0b8) — the prior
  audit found the K-quantifier scope is unrestricted (`K = |α|`
  in the operational call); the present analysis extends to the
  `w`-quantifier scope and pins canonicalLayered as the vacuity
  vector.
* `docs/why-hC3-is-structural.md` — the option (δ) park rationale.
  The present analysis confirms the *concrete* form of the
  obstruction is the missing `w ≤ W₀` bound. F1/F2/F3 are the
  reasons that closing the cap-5-tightened gap is hard.
* `docs/path-c-track-1-status-1.md` (mg-b666) — the K=2
  case-2-strict cardinality obstruction. Blocks Options A and B
  of §3c of the analysis.

**Parallel work.** Concurrent Frankl Z-arc (cat-mg-103f) in
`union_closed` repo. No contention.

---

## Open questions for Daniel review

1. Is `W₀ = 4` the intended constant, or should we expect a larger
   absolute bound from a faithful in-Lean delivery of Steps 1-7?
   (The paper's `w₀(γ)` may not be `4` — `W₀ = 4` is the
   F5a-certified scope, which is *one possible choice* for the
   cap, not necessarily the paper's.)
2. Is the signature restatement (cap 5) authorised to file as a
   follow-on without further review, given that it will *expose*
   the operational gap as a type error at the call site? The
   surfacing is the intended outcome but it also makes the
   downstream dispatch failure visible in CI.
3. Does this analysis change the option (δ) park decision?
   `why-hC3-is-structural.md` (2026-05-04) argued that `hC3`
   retention is "structural, not effort-bound" based on F1/F2/F3.
   The present analysis confirms that the *concrete operational
   form* of the structural problem is the missing cap 5 — which
   makes the option (δ) park more *legible* (a named missing
   bound) but does not change the underlying difficulty.

End of session 1.

---

## Session 2 — mg-d5a0 (2026-05-17), polecat: Lean signature-refactor + structured-sorry placement

**Trigger.** Daniel directive 2026-05-17T15:43Z selecting alpha
(cap-5 fix) as the action on session 1's
AMBER-missing-bound-fix-proposed verdict.

**Polecat dispatch.** Lean-engineering polecat (signature-refactor
+ structured-sorry-placement specialisation), 250k single-session,
no canonicalLayered modification, no Subsingleton tricks, no fresh
axioms, no weakening of the existing 4 caps.

**Verdict.** **partial-GREEN cap-5 added + type errors surfaced +
structured sorries naming downstream blockers.**

**Code delta (summary).**

* `Step8.Case3Witness.{u}` (`LayeredBalanced.lean:451-462`
  post-edit): cap 5 `LB.w ≤ 4` added as the new 5th antecedent
  (between the bands-nonempty cap and the `HasWidthAtMost β 3`
  shape constraint). Docstring expanded to record the F5a-aligned
  W₀ = 4 choice and the architectural-debt framing.
* `Step8.OptionC.Case3Witness_proof`
  (`OptionC/Case3WitnessProof.lean`): strong-induction
  `suffices`-statement gains the extra `LB.w ≤ 4` hypothesis;
  both `compactify`-descent recursion arms (`D.Lower`, `D.Upper`)
  propagate the cap via `LayeredDecomposition.compactify_w_eq`.
  K = 1 contradiction, K = 2 `option_c_K2_closure` dispatch, and
  K ≥ 3 irreducible-`bounded_irreducible_balanced_hybrid` dispatch
  do not consume cap 5 directly, so the body is otherwise
  unchanged.
* `lem_layered_balanced` K ≥ 2 dispatch (`LayeredBalanced.lean:600s
  post-edit, formerly line 668`): the canonical substitution
  `L' := canonicalLayered α` is preserved; the cap 5 discharge is a
  structured `sorry` (line 626 post-edit), with an in-place block
  comment naming the two downstream blockers (mg-b666 K=2
  case-2-strict; Steps 1-7 `w₀(γ)`).

**Build status.** `lake build OneThird` exits successfully.
Exactly **one new sorry** (`LayeredBalanced.lean:626`,
`hLBw : L'.w ≤ 4`). No new project axioms. No removal/weakening
of the four pre-existing caps. `canonicalLayered` is unmodified.

**Session-1 deliverables (mg-e2e9) and their realisation in
session 2.**

| Session-1 recommendation | Session-2 realisation |
|--------------------------|-----------------------|
| LEAN signature-restatement (add cap 5) | ✅ delivered |
| Surface operational gap at K ≥ 2 dispatch as type error | ✅ delivered via structured sorry |
| Pin downstream blockers (Option B mg-b666; Option A Steps 1-7) | ✅ named in in-place block comment + state doc |
| LEAN residual-axiom-tightening | ⏭ out of scope (follow-on ticket) |
| LEAN operational-dispatch rewrite (Option A/B/C) | ⏭ out of scope (multi-polecat, blocked) |
| MATH paper-level `w₀(γ)` pin | ⏭ out of scope (math-paper polecat) |

**Outstanding session-1 open questions.**

1. **W₀ = 4 vs paper-derived constant** (session 1, open question 1).
   This session adopts `W₀ = 4` per ticket spec (F5a-aligned). If the
   paper-derived `w₀(γ)` from Steps 1-7 turns out larger, the cap
   value can be relaxed without touching the dispatch (cap 5 is
   strictly stronger than the paper bound only if the paper bound
   is `> 4`).

2. **Surfaced type-error CI visibility** (session 1, open question 2).
   The surfaced sorry is now visible to anyone running
   `#print axioms OneThird.width3_one_third_two_thirds` or
   `lake build OneThird` — the gap is no longer absorbed silently
   by the universal-quantifier proxy.

3. **Option (δ) park decision** (session 1, open question 3). The
   present session does not change the park; it makes the park
   *legible*. F1/F2/F3 are now re-localised to the dispatch's cap-5
   discharge rather than abstractly threaded through the
   universal quantifier.

**Deliverables (session 2).**

* Lean: cap-5 signature change + structured-sorry surfacing
  (2 files touched, ~3 net hypotheses added, 1 net sorry).
* Docs: `state-Case3Witness-cap5-fix.md` (per-session state) +
  this session 2 entry in `state-Case3Witness-architecture.md`
  (cumulative state).

**Cross-reference.** Closes the action item of the session 1
AMBER verdict. The architecture-analysis arc terminates here in
its lemma-level scope; downstream rewrite work (Options A/B/C)
is now blocked on the named items already on the roadmap.

End of session 2.

---

## Session 3 — mg-4d7b (2026-05-17), polecat: cap-5 enumeration (computation)

**Trigger.** Daniel directive 2026-05-17T20:55Z verbatim:

> "jesus if it's 10^4-10^6 then let's get a polecat to enumerate it
> top priority. if that's truly the only gap left for a proof then
> let's do the enumeration now. if it can be done in a lean-ready
> way for later that's great too. then if i understand correctly
> width 3 math is COMPLETE and that makes our job much easier, esp
> if the only sorry is basically this enumeration."

**Polecat dispatch.** Computation polecat with enumeration +
brute-force-verification specialisation. ~800k multi-phase budget
(sub-split allowed per ticket body).

**Scope.** Phases A-E per ticket body. Under all five Case3Witness
caps + cap 1 (injective) + cap 4 (nonempty), the universal
`∀ β, ∀ LB` restricts to **finite posets β with 2 ≤ |β| ≤ 10**
admitting a singletons-band `LayeredDecomposition` of interaction
width w ∈ {0..4}, width ≤ 3, non-chain. Phases A-B reduce to
verifying `HasBalancedPair β` for every such β.

**Verdict.** **GREEN-enumeration-substrate-shipped /
AMBER-headline-dispatch-still-blocked.**

* Phases A-B: ✅ — all (K, w) cells in cap-5 scope enumerated and
  verified balanced via `lean/scripts/enum_cap5.py` (single-thread)
  and `lean/scripts/enum_cap5_K10.py` (parallel). **No
  counterexamples found** across the full scope, confirming the
  Linial 1984 width-3 case on this concrete enumeration.
* Phase C: ✅ partial — Lean native_decide cells for K = 2 (w ∈
  {0, 1}), K = 4 (w ∈ {2, 3, 4}), K = 5..8 (w ∈ relevant) added to
  `lean/OneThird/Step8/Case3Enum/Cap5Singletons.lean`; K = 9 w = 4
  in dedicated file (`Cap5SingletonsK9.lean`, not imported into
  `OneThird.lean` due to native_decide top-of-budget); K = 10 w = 4
  certified externally (no Lean-level axiom introduced).
* Phase D: ✅ implicit — LB witnesses are the bitmask + band
  encoding; no separate construction needed for the proof obligation.
* Phase E: ❌ remains blocked — `LayeredBalanced.lean:751`
  structured sorry on `hLBw : L'.w ≤ 4` for `L' :=
  canonicalLayered α` is the named operational gap; closing it
  requires Steps 1-7 `w₀(γ)` delivery (Option A) or mg-b666 K=2
  case-2-strict residual (Option B) per session-2 disclosure.

**Architectural framing — what enumeration accomplishes.**

Before this session: `Case3Witness` (post-cap-5) was a
finitely-decidable Prop with effective content, but not yet
*proved* in Lean. Session 2 surfaced the structured `sorry` at the
operational dispatch; the `Case3Witness` Prop itself was held as a
hypothesis to be discharged later.

After this session: the enumeration *demonstrates* `Case3Witness`
holds on every (K, w, mask)-indexed config in scope (no
counterexamples). The Lean-level discharge of `Case3Witness` as a
theorem (via the native_decide cells + Bool↔Prop bridge) is the
named follow-up (`mg-4d7b-followup-case3witness-prop`); the
*substrate* (the per-cell native-decide certificates) is in place.

The operational dispatch sorry (`LayeredBalanced.lean:751`)
remains. Closing the headline theorem
`width3_one_third_two_thirds` requires either:

* the *dispatch* to be rewritten to consume a cap-5-satisfying L
  (Options A/B/C, all blocked on the previously-disclosed items), or
* an alternative argument for `|α| > 10` width-3 non-chain posets
  (e.g., Linial 1984 directly, packaged as a separate axiom).

**Files shipped (session 3).**

* `lean/scripts/enum_cap5.py` — full cap-5 scope enumerator (K = 2..9).
* `lean/scripts/enum_cap5_K10.py` — parallel K = 10 cell driver.
* `lean/scripts/enum_cap5_K2to8_certificate.json` — K = 2..8 cert.
* `lean/scripts/enum_cap5_certificate.json` — K = 9 cert (one cell).
* `lean/scripts/enum_cap5_K10_certificate.json` — K = 10 cert
  (one cell, parallel-worker per-shard counts).
* `lean/OneThird/Step8/Case3Enum/Cap5Singletons.lean` — per-cell
  native_decide for K = 2, 4..8.
* `lean/OneThird/Step8/Case3Enum/Cap5SingletonsK9.lean` — K = 9
  native_decide (separate file, not imported into `OneThird.lean`).
* `docs/state-Case3Witness-cap5-enumeration.md` — per-session state
  for this enumeration arc.
* `docs/state-Case3Witness-architecture.md` — session 3 entry (this).
* `lean/OneThird.lean` — added `Cap5Singletons` import (K = 9
  intentionally left out per file header).

**No new axioms.** No `LayeredBalanced.lean` source changes. The
existing structured `sorry` at line 751 (mg-d5a0) is unchanged.

**Cross-reference.**

* `docs/state-Case3Witness-cap5-enumeration.md` — full session log
  for the enumeration computation (mg-4d7b session 1).
* `lean/scripts/enum_case3.py` (mg-307c) — earlier K = 3 enumerator
  this session extends to the full cap-5 K range.
* `lean/OneThird/Step8/Case3Enum/Certificate.lean` (mg-307c +
  mg-9a4a) — the existing F5a certificate this session augments.

**Parallel work.** Concurrent with mg-0cbf post-cap-5 tractability
analysis (paper-only). mg-0cbf may identify a uniform F5a-based
argument (Option D1) that shelves mg-4d7b. If so, this session's
enumeration substrate stands as a sanity check on the proof
correctness for small instances.

End of session 3.
