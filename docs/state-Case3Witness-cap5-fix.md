# Cumulative state — Case3Witness cap-5 fix (mg-d5a0)

Tracks the Lean signature-restatement that adds cap 5
`LB.w ≤ 4` to `Step8.Case3Witness.{u}` per Daniel directive
2026-05-17T15:43Z (alpha choice), closing the
"paint-by-numbers vacuity" diagnosis of mg-e2e9 by surfacing the
operational gap at the K ≥ 2 dispatch as a structured `sorry`.

Companion to:

* `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9
  upstream analysis, AMBER-missing-bound-fix-proposed).
* `docs/state-Case3Witness-architecture.md` (cumulative state of
  the architecture analysis arc).
* `docs/case3witness-operational-audit.md` (mg-e0b8, the
  K-quantifier audit; cap 5 extends to the `w` quantifier).
* `docs/why-hC3-is-structural.md` (option (δ) park rationale; cap 5
  re-localises F1/F2/F3 to the call site).
* `docs/path-c-track-1-status-1.md` (mg-b666 K=2 case-2-strict
  obstruction; named downstream blocker for Option B).

---

## Session 1 — mg-d5a0 (2026-05-17), polecat: Lean signature-refactor + structured-sorry placement

**Trigger.** Daniel directive 2026-05-17T15:43Z selecting alpha
(cap-5 fix) as the response to mg-e2e9's AMBER analysis. Sister
ticket mg-e2e9 surfaced the architectural disconnect:
`Case3Witness.{u}`'s four caps are *ratio* bounds that do not
constrain the layered decomposition's interaction width `LB.w`
from above, and the operational `lem_layered_balanced` K ≥ 2
branch (`LayeredBalanced.lean:668`) substitutes
`canonicalLayered α` (with `K = w = |α|`) for the input layered
decomposition, making the layered axiom (L2-forced) literally
vacuous and collapsing `Case3Witness β` to the headline theorem
itself.

**Polecat dispatch.** Lean-engineering polecat with
signature-refactor + structured-sorry-placement specialisation.
250k single-session. Branch `polecat-cat-mg-d5a0`, default `main`.

**Verdict.** **partial-GREEN cap-5 added + type errors surfaced +
structured sorries naming downstream blockers.**

Specifically:

* Cap 5 `LB.w ≤ 4` added as the new 5th antecedent to
  `Step8.Case3Witness.{u}` (`LayeredBalanced.lean:451-462` post-edit).
  `W₀ = 4` is the F5a-aligned constant matching `InCase3Scope.w_mem`
  (`BoundedIrreducibleBalanced.lean:1498`); under cap 5 the four
  existing caps become honest finite-domain restrictions
  (`|β| ≤ 30`, `K ≤ 10`, `w ∈ {1, 2, 3, 4}`).
* `Step8.OptionC.Case3Witness_proof` (the producer of the universal
  witness) threads cap 5 through the strong induction. `compactify_w_eq`
  (`LayeredDecomposition/Compactify.lean:375`) carries cap 5
  unchanged through both the `D.Lower` and `D.Upper` descent
  branches. The body needs no other adaptation:
  `option_c_K2_closure` (K=2 path) and
  `bounded_irreducible_balanced_hybrid` (K ≥ 3 irreducible path)
  do not consume cap 5 directly.
* `lem_layered_balanced`'s K ≥ 2 dispatch
  (`LayeredBalanced.lean:600s post-edit, formerly line 668`) is
  the surfaced architectural debt. The dispatch still substitutes
  `canonicalLayered α`, but `canonicalLayered α` has
  `w = Fintype.card α`, which fails cap 5 for any `|α| ≥ 5`. The
  cap-5 hypothesis is admitted as a structured `sorry` localised
  to the `hLBw : L'.w ≤ 4` step (line 626 post-edit), with an
  in-place block comment naming the two downstream blockers:
  * **mg-b666** — K=2 case-2-strict residual cardinality
    obstruction (`docs/path-c-track-1-status-1.md`). Blocks
    Option B (F3 strong-induction with bounded-`w` leaves).
  * **Steps 1-7 `w₀(γ)` delivery** — the chain-potentials
    extractor (`ChainPotentials.lean`) currently produces
    `Lwidth3.bandwidth = |α| + 1`, not the paper's bounded
    `w₀(γ)`. Required for Option A (upstream `L`-threading).
* Build status: `lake build OneThird` exits successfully with
  **exactly one new sorry** (the targeted cap-5 admission at
  `LayeredBalanced.lean:626`). No new project axioms; no
  modification of `canonicalLayered`, `bounded_irreducible_balanced_hybrid`,
  `case3Witness_hasBalancedPair_outOfScope`, or any of the four
  pre-existing caps.

**What this delivers vs what the ticket required.**

| Ticket requirement | Status |
|--------------------|--------|
| Add cap 5 `LB.w ≤ W₀` (W₀ = 4) to Case3Witness signature | ✅ done (`LayeredBalanced.lean:458` post-edit) |
| Surface type error at LayeredBalanced.lean:668 K ≥ 2 dispatch | ✅ done; structured `sorry` at line 626 post-edit |
| Structured comments naming downstream blockers | ✅ done; in-place block comment names mg-b666 + Steps 1-7 `w₀(γ)` |
| `bounded_irreducible_balanced_hybrid` consumers | ⚠ Hybrid itself does not consume cap 5 directly; the only Case3Witness consumer that breaks is the K ≥ 2 dispatch (single sorry). `Case3Witness_proof` body threads cleanly. |
| Cap 5 = 4 (F5a-aligned) | ✅ done |
| Not factorial / not functorial | ✅ confirmed |
| No canonicalLayered modification | ✅ confirmed (only the `hLBw` discharge changes) |
| No Subsingleton tricks | ✅ confirmed |
| No silent type-error papering via fresh axioms | ✅ confirmed; sorry is named and bounded |
| No removal/weakening of existing 4 caps | ✅ confirmed |
| Cumulative state doc | ✅ this file + `state-Case3Witness-architecture.md` session 2 entry |

**Files touched.**

* `lean/OneThird/Step8/LayeredBalanced.lean` — cap 5 added to
  `Case3Witness.{u}` signature; docstring expanded; K ≥ 2 dispatch
  in `lem_layered_balanced` gains a structured `sorry` for the
  cap-5 discharge (with in-place comment naming downstream
  blockers); `exact hC3 α L' ...` updated to pass the new
  hypothesis position.
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean` — strong
  induction generalises with the extra `LB.w ≤ 4` hypothesis;
  both `compactify`-descent recursion calls propagate it via
  `compactify_w_eq`.
* `docs/state-Case3Witness-cap5-fix.md` (this file).
* `docs/state-Case3Witness-architecture.md` — session 2 cumulative
  entry.

**What this does NOT do (out of scope per ticket).**

* Does not rewrite the K ≥ 2 dispatch to consume a cap-5-satisfying
  `L` (Option A/B/C). All three options are blocked by the named
  downstream blockers and require multi-polecat scope.
* Does not tighten `case3Witness_hasBalancedPair_outOfScope`
  (`Case3Residual.lean:208`) to add `LB.w ≤ 4`. The residual axiom
  remains as previously stated; cap 5 narrows its *effective*
  operational domain (via Case3Witness threading) but the axiom
  signature is unchanged.
* Does not modify `bounded_irreducible_balanced_hybrid` —
  hybrid's wider profile is intentional per mg-A8 sub-split.
* Does not deliver `w₀(γ)` from Steps 1-7 (paper-level scope).
* Does not close mg-b666 K=2 case-2-strict residual.

**Architectural framing — what cap 5 has accomplished.**

Before cap 5: the K ≥ 2 dispatch silently composed
`canonicalLayered α` (Szpilrajn-derived, vacuous (L2-forced)) with
the universal `Case3Witness β`. Caps 1-4 were satisfied
trivially, so the dispatch type-checked but proved nothing the
headline didn't already claim. The architectural disconnect was
invisible to the compiler.

After cap 5: the K ≥ 2 dispatch *cannot* discharge cap 5 on
`canonicalLayered α` (since `w = |α|` is not bounded). The
compiler now flags exactly the operational dependency that mg-e2e9
diagnosed in prose. The dispatch is reduced to a single named
`sorry` whose proof obligation — find a cap-5-satisfying `L` in
this branch — is the precise structural ask. mg-b666 and the
Steps 1-7 `w₀(γ)` delivery are now positioned as the two paths
that would discharge this sorry; both intersect the option-(δ)
park already documented in `why-hC3-is-structural.md`.

**No change to overall headline-theorem provability.**
`OneThird.width3_one_third_two_thirds` still type-checks (via
`Case3Witness_proof` ∘ `lem_layered_balanced`), with the single
new sorry localised at the cap-5 discharge. The headline's
*provability* with respect to the rest of the project is
unchanged: before cap 5, the dispatch was vacuously circular;
after cap 5, it is honestly stuck on a named sorry. This is
the intended outcome per the mg-e2e9 verdict (AMBER-fix-proposed):
the lemma-level fix is clean, the execution-level blockers are
the previously disclosed residuals.

**Axiom audit.** No new project axioms. The only sorry is the
targeted cap-5 discharge at `LayeredBalanced.lean:626` (post-edit
line numbers).

**Cross-references.**

* mg-e2e9 — upstream architecture analysis (AMBER, cap-5 fix
  proposed).
* mg-e0b8 — K-quantifier audit; cap 5 extends to `w`.
* mg-b666 — K=2 case-2-strict residual (named blocker for Option B).
* mg-8c72 — Option-C Stage 2B (added the four pre-existing caps;
  cap 5 is the natural extension).
* mg-979e — Obstructions A and B; cap 5 re-localises Obstruction B
  to the call-site.

**Parallel work.** Concurrent z-arc work in `union_closed` repo
(cat-mg-103f, distinct repo). cat-mg-a298 (Z1b) just stopped
(GREEN) per dispatch context — no contention.

End of session 1.
