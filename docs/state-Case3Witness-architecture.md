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
