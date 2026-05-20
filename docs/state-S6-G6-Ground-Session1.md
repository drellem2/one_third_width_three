# State — OneThird S6-G6-Ground: ground G6 `lem:most-good`, wire the S2 `ε₂` bookkeeping into Step 6 (mg-aa02)

**Ticket:** mg-aa02 — OneThird-S6-G6-Ground: ground the G6 `lem:most-good`
lemma and wire the S2 `ε₂` bookkeeping into Step 6.
**Phase:** FULL REFACTOR Phase 2 — Checkpoint-2 follow-on, item 2 of 3.
**Depends:** mg-fc78 (S1-G2-Report — item 1, the HARD GATE: `goodFiberSet`
provably non-empty; landed), mg-e996 (S6-QA Checkpoint 2 audit; landed).
**Session:** 1.

---

## §0. Verdict — **GREEN — both scope items delivered**

> **G6 is grounded and the S2 `ε₂` bookkeeping is wired into Step 6.**
> The S6-QA Checkpoint-2 audit (`docs/state-S6-QA-Checkpoint2-Session1.md`
> §3.1) flagged two unfinished Step 6 grounding pieces; this session
> closes both, in `lean/OneThird/Step6/MostGoodGrounded.lean` (NEW,
> ~540 LoC), sorry-free and axiom-free.
>
> **1. G6 `lem:most-good` grounded.** `lem_most_good_grounded` is the
> `step6.tex:154` Markov argument run on the **genuine BK boundary**
> `globalBKBdy S` of `bkGraph α` (the directed `∂_BK S` of
> `Step2/PerFiberGrounded2.lean`).  From the summed Step-2 error
> `∑_α |B_α| ≤ C₂'·|∂_BK S|` and the low-conductance hypothesis
> `|∂_BK S| ≤ Φ₀·vol(S)` it delivers the bad-interface mass bound
> `ε₂·∑_{Rich∖Rich⋆}|F_α| ≤ C₂'·Φ₀·vol(S)`.  Unlike the abstract
> `Step6.lem_most_good`, the Markov antecedent `hBadMass` is **derived**
> from the explicit `ε₂` split (`sGoodInterfaces`, a `Finset.filter` on
> the `ε₂` threshold), not assumed.  `lem_most_good_grounded_good_mass`
> is the dual `(1-o(1))` good-mass form.
>
> **2. The S2 `ε₂` bookkeeping wired into Step 6.** Before this session
> `ε₂` appeared in **zero** Step 6 files (audit §3.1) and no Step 6
> file imported Step 2.  `MostGoodGrounded.lean` imports
> `OneThird.Step2.PerFiberGrounded2` and performs the `ε₂ ↔ C₂'`
> reconciliation S2-B §2 explicitly deferred to Checkpoint 2:
> `lem_most_good_grounded_of_thm_step2` consumes `step2.tex`
> `thm:step2` directly — clause (ii) supplies the per-fiber staircase
> exceptional set `B_r` with `|B_r| ≤ ε₂·|D_r|`, `ε₂` the uniform
> `fiberStaircaseRate` bound — and produces the G6 bad-mass bound.
> `ε₂` / `fiberStaircaseRate` now genuinely thread into the Step 6
> per-fiber aggregation (the `sGoodInterfaces ε₂` split).
>
> **Non-vacuity.** Both routes instantiate non-vacuously at concrete
> width-3 non-chain posets (§3), with no `Subsingleton`/empty
> baseline.

---

## §1. Scope and method

**Charter (ticket mg-aa02), two parts.**

1. **Ground G6** — port `lem:most-good` from its abstract-only form
   (`Step6/Assembly.lean:100`, the cleared-denominator `ℕ` Markov) to
   the genuine grounded form on the BK-graph foundation.
2. **Wire the S2 `ε₂` bookkeeping into Step 6** — perform the
   `ε₂ ↔ C₂'` reconciliation S2-B (`docs/state-S2-B-Session1.md` §2/§4)
   deferred to Checkpoint 2; `ε₂` must thread into the Step 6 per-fiber
   aggregation.

**Non-triviality bar.** The grounded G6 and the wired `ε₂` must be
genuine — instantiate non-vacuously at a concrete width-3 non-chain
poset; no content-free placeholders.

**Method.** Paper-first.  Read `step6.tex` `def:S-good`
(`step6.tex:148-152`) and `lem:most-good` (`:154-235`, proof
`:170-227`); the S6-QA Checkpoint-2 audit; the S2-B state doc and
`Step2/PerFiberGrounded2.lean` (`fiberStaircaseRate`, `thm_step2`,
`prop_per_fiber_bad_mass`, `globalBKBdy`, `goodFibers`/`badFibers`,
`RichFamily`); the S6-A/S6-B grounded files for the grounding style.
Built and machine-checked.

**Build state.** Worktree on `polecat-aa02`.  Mathlib build cache
reused from the source repo (memory note `lean-build-cache-reuse.md`).
`lake build OneThird` clean; the new file is sorry-free and
axiom-free.

---

## §2. What `lem:most-good` says, and how the port grounds it

`step6.tex` `lem:most-good` (G6): if the cut `S` has conductance
`Φ(S) ≤ Φ₀`, then `∑_{Rich⋆}|F_α| ≥ (1-o(1))∑_{Rich}|F_α|` — most
rich-interface mass is `S`-good.

The proof is a fiberwise Markov inequality:

* Step 2 produces, per rich interface `α`, an exceptional set `B_α`
  with the summed bound `∑_α|B_α| ≤ C₂'·|∂_BK S|`
  (`step6.tex` `eq:step2-summed`).
* `α` fails to be `S`-good iff `|B_α| > ε₂·|F_α|`
  (`step6.tex` `def:S-good`).
* Markov on `Rich^bad := Rich∖Rich⋆`:
  `∑_{Rich^bad}|F_α| < ε₂⁻¹∑_{Rich^bad}|B_α| ≤ ε₂⁻¹∑_{Rich}|B_α|
   ≤ ε₂⁻¹C₂'|∂_BK S| ≤ ε₂⁻¹C₂'Φ₀·vol(S)`.

### §2.1 G6 grounded — `lem_most_good_grounded`

The abstract `Step6.lem_most_good` (`Assembly.lean:100`) is the
cleared-denominator `ℕ` form of this Markov, with the
fail-to-be-`S`-good antecedent `hBadMass` taken as a **free
hypothesis** and the boundary an **opaque parameter**.  Two things
make the grounded form genuine:

* **The boundary is the genuine BK boundary.** `lem_most_good_grounded`
  takes a concrete cut `S : Finset (LinearExt α)` and uses
  `globalBKBdy S` — the directed `∂_BK S` of `bkGraph α`
  (`Step2/PerFiberGrounded2.lean`, the same boundary S2's
  `lem:fiber-avg` is grounded on).  `vol(S)` is `|S|`.
* **The `S`-good split is computed, not assumed.** `IsSGood` is
  `step6.tex` `def:S-good` (`|B_a| ≤ ε₂·|F_a|`); `sGoodInterfaces`
  is the explicit `Finset.filter` on that `ε₂` threshold.  The
  Markov antecedent (`a ∈ Rich∖Rich⋆ ⇒ ε₂·|F_a| < |B_a|`) is the
  **derived** `lt_excSize_of_mem_sdiff`, not a parameter.

The port works in `ℚ` (faithful to S2, which is `ℚ`-valued) — a fresh
`ℚ`-native proof of the same Markov chain, in the style of the S6-A
`thm_step6_grounded` re-proof.

### §2.2 The S2 `ε₂` wire — the `ε₂ ↔ C₂'` reconciliation

S2-B `docs/state-S2-B-Session1.md` §2 (honest note) flagged: the
Step-6 `S`-good split is on the per-fiber *error set* `B_α`
(`|B_α| ≤ ε₂|F|`), while the S2 port's split is on the per-fiber
*boundary* (`|∂_BK(S∩fib)| ≤ η|fib|`); *"the exact reconciliation of
the constants (`step6.tex`'s `C₂'` vs this port's `K·κ/η`) is … what
Checkpoint 2 … is for."*

The reconciliation, performed here:

* **boundary-good ⇒ error-good.** Every `step2.tex` boundary-good
  fiber (`goodFibers Fam S η`) is an `S`-good interface.  This is
  exactly what `thm:step2` clause (ii) delivers: a boundary-good
  fiber admits a monotone staircase with symmetric-difference error
  `|B_r| ≤ ε₂·|D_r|`, and the grid bijection `fiberGrid_card` (valid
  on a constant-sign good fiber, `RichFamily.good`/`.signConst`)
  converts `|D_r|` to `|F_r|`.
* **error-bad ⊆ boundary-bad.** Contrapositive: the `ε₂`-error-bad
  interfaces `Rich∖Rich⋆` are contained in the `η`-boundary-bad
  fibers `badFibers Fam S η`.
* **The G6 bad-mass bound is S2's own `prop_per_fiber_bad_mass`.**
  `∑_{Rich∖Rich⋆}|F_r| ≤ ∑_{badFibers}|fib| ≤ K·κ·|S|/η`.

So `step6.tex`'s `C₂'`-style bad-mass bound is, in the grounded port,
S2's constant `K·κ/η` — the reconciliation S2-B §2 named.  This is
`lem_most_good_grounded_step2`; `lem_most_good_grounded_of_thm_step2`
makes it end-to-end by consuming `thm:step2` directly (so
`fiberStaircaseRate` is genuinely consumed, not re-asserted).

---

## §3. Non-vacuity (mg-aa02 acceptance bar)

Two non-vacuity witnesses, both on genuine width-3 non-chain posets,
no `Subsingleton`/empty baseline.

* **`lem_most_good_grounded_nonvacuous` (Route A).** G6 fires at the
  genuine width-3 non-chain grid poset `Fin 3 × Fin 3` with the
  singleton cut `S = {gridLinExt}`.  The directed BK boundary
  `globalBKBdy gridCut` is genuinely **non-empty** — a real directed
  BK cut edge, `globalBKBdy_gridCut_nonempty`, extracted from the
  S6-A `grid_bkBoundary_pos`.  With one rich interface carrying a
  genuine non-empty good fiber `{gridLinExt}` and one unit of genuine
  exceptional mass, the `ε₂ = 1/2` split classifies the interface as
  **bad**: `Rich∖Rich⋆` is genuinely non-empty.  This exercises the
  Markov core of G6 with a populated bad set — *stronger* than the
  S6-A/S6-B grounded witnesses, which had empty bad-active sets.

* **`lem_most_good_step2_nonvacuous` (Route B — the full S2 wire).**
  `lem_most_good_grounded_of_thm_step2` fires at the genuine width-3
  non-chain poset `Antichain3` with the genuine rich-fiber family
  `antichain3Family` (the S2-B acceptance witness's family) and the
  **genuine uniform staircase rate** `ε₂ = fiberStaircaseRate 1 1 1 1`
  — the exact `ε₂` value of the S2-B `per_fiber_grounded2_nonvacuous`
  witness.  `thm:step2` is genuinely invoked and its hypotheses
  discharged; the genuine per-fiber exceptional-mass assignment is
  produced and the rich interface classified.

---

## §4. Scope boundary (honest)

* **G6 grounded is `ℚ`-native.** It does not call the abstract
  `ℕ`-cleared `Step6.lem_most_good`; it re-proves the Markov chain in
  `ℚ` on genuine data (the S6-A `thm_step6_grounded` precedent).  The
  abstract `lem_most_good` is a true `ℕ` lemma and is left untouched.
* **The cascade is not recomposed end-to-end.** S6-QA Checkpoint-2
  audit §6.1 item 3 (compose `cascade_steps_1_6_grounded` from the
  grounded producers with a genuine-object witness) is a **separate**
  Checkpoint-2 follow-on item, not in mg-aa02 scope.  The grounded G6
  here produces `Rich⋆` (`sGoodInterfaces`) as a genuine computed
  `Finset` consumable by the S6-A/S6-B grounded forms; wiring it into
  `cascade_steps_1_6_grounded` is the remaining item.
* **`C₂'` (`eq:step2-summed`) as a hypothesis.** `lem_most_good_grounded`
  takes the summed Step-2 error `∑|B_α| ≤ C₂'·|∂_BK S|` as a
  hypothesis.  Deriving `eq:step2-summed` itself from the per-fiber
  `eq:step2-per-fiber` + `lem:fiber-avg` is the alternate route; the
  *wired* form (`lem_most_good_grounded_step2`) instead routes through
  S2's `prop_per_fiber_bad_mass` directly, with constant `K·κ/η` — the
  genuine in-tree S2 deliverable.  Both routes are provided.

---

## §5. Files

* `lean/OneThird/Step6/MostGoodGrounded.lean` — NEW (~540 LoC).
  `IsSGood` / `sGoodInterfaces` (`def:S-good`); `lem_most_good_grounded`
  + `lem_most_good_grounded_good_mass` (G6 grounded);
  `lem_most_good_grounded_step2` + `lem_most_good_grounded_of_thm_step2`
  (the S2 `ε₂` wire); `globalBKBdy_gridCut_nonempty`,
  `lem_most_good_grounded_nonvacuous`, `lem_most_good_step2_nonvacuous`
  (non-vacuity).
* `lean/OneThird.lean` — +1 import line.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` — §0 mg-aa02 bullet.
* `docs/state-S6-G6-Ground-Session1.md` — this file (NEW).

---

## §6. Skeptical re-audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2)

1. **Satisfiability, not a type check.** Both deliverables rest on
   machine-checked theorems with non-vacuous instances: `Route A` at
   `Fin 3 × Fin 3` fires with a genuinely **non-empty** `Rich∖Rich⋆`
   (the Markov core is exercised, not a `0 ≤ 0` degeneracy); `Route B`
   at `Antichain3` genuinely invokes `thm:step2`.  `ε₂` genuinely
   appears in a Step 6 file — `grep "ε₂\|fiberStaircaseRate"
   Step6/MostGoodGrounded.lean` is non-empty, and the file imports
   `OneThird.Step2.PerFiberGrounded2`.
2. **Not a degenerate re-definition.** `IsSGood` is the literal
   `step6.tex` `def:S-good` (`|B_α| ≤ ε₂·|F_α|`); `sGoodInterfaces`
   computes the split rather than assuming it.  The grounded G6's
   `hBadMass` antecedent is *derived* (`lt_excSize_of_mem_sdiff`),
   which is strictly stronger than the abstract `lem_most_good`'s
   free hypothesis.
3. **Discharge-coverage of cited artefacts.** The wire genuinely
   consumes S2: `lem_most_good_grounded_step2` calls
   `prop_per_fiber_bad_mass`; `lem_most_good_grounded_of_thm_step2`
   calls `thm_step2`.  The `K·κ/η` constant is S2's own, not a
   re-asserted bound.
4. **No over-claim.** The cascade end-to-end recomposition is
   explicitly out of scope (§4) and flagged as the remaining
   Checkpoint-2 follow-on item.  G6 grounded is `ℚ`-native and does
   not claim to call the abstract `ℕ` `lem_most_good`.
