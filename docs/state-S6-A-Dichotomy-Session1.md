# OneThird-S6-A Session 1 state report — Step 6 low-conductance dichotomy grounded

**Ticket:** mg-9576 (FULL REFACTOR Phase 2, Wave-4; Piece-1 Steps-1-6
cascade port; scoped by mg-d8c7 §2.1 / §5.2 under S6; the final wave
of the Piece-1 cascade port).
**Verdict:** **GREEN — substantively landed.** The Step 6
low-conductance dichotomy (`thm:step6`, `step6.tex:477-503`) is ported
in *grounded* form: it is wired onto the genuine BK boundary
`Step4.bkBoundary S` and the genuine second moment of visibility
`M = ∑_L I(L)²`, with the closing low-conductance contradiction
(`rem:G5-closes-dichotomy`) delivered faithfully, and the whole
dichotomy is instantiated **non-vacuously** on a concrete width-3
non-chain poset. Full `lake build` clean; no new axioms, no `sorry`.

---

## §0. TL;DR

* **The abstract Step 6 scaffold already exists.** `lean/OneThird/Step6/`
  carries the full abstract cleared-denominator scaffold of `step6.tex`
  (G6-G10 + `thm:step6` + `cor:pointwise`), with no `sorry`:
  `ErrorControl.lean` (`prop:gap-g1`), `Incoherence.lean`
  (`def:incoherent-pair`), `CommutingSquare.lean` (`lem:gap3`),
  `OverlapCounting.lean` (`lem:overlap-counting`), `RichnessBound.lean`
  (`lem:gap-G5`), `Assembly.lean` (`lem:most-good`, `lem:sum-step4`,
  `thm:step6`, `cor:pointwise`). S4-C (mg-3bca) already grounded G9
  (`lem_sum_step4_grounded` on the genuine BK boundary).
* **This session grounds `thm:step6` itself.** New file
  `Step6/DichotomyGrounded.lean` wires the abstract dichotomy onto
  genuine BK-graph data — `Step4.bkBoundary S` and the genuine second
  moment `M = ∑_L I(L)²` — and delivers the closing low-conductance
  contradiction faithfully (`thm_step6_rich_closure_grounded`: a
  low-conductance cut cannot be in the expansion case, so its bad
  overlap mass is uniformly small — "expansion contradicts
  conductance").
* **One abstract-scaffold defect found and routed around (not a
  block).** The abstract `Step6.thm_step6` / `thm_step6_rich_closure`
  (`Assembly.lean`) carry a *single* variable `M`, but `step6.tex`
  uses `M` for **two distinct quantities** — the overlap-counting
  *multiplicity* constant of `lem:overlap-counting` and the overlap
  *mass* `∑_{α,β} w_{αβ}` of `thm:step6`. The grounded theorems carry
  **two distinct variables** (`mult` and the explicit `∑ pairOverlap`)
  and are therefore the faithful shape. See §4.
* **Non-vacuity bar met.** `thm_step6_grounded_concrete` instantiates
  the dichotomy on `Fin 3 × Fin 3` (the genuine width-3 non-chain
  9-element grid poset) with the singleton cut `S = {gridLinExt}`: the
  BK boundary is genuinely non-empty (`1 ≤ |∂_BK S|`), the genuine
  second moment is strictly positive (`M = ∑_L I(L)² = 1`, identity
  verified), the dichotomy forces the genuine expansion bound
  `1 ≤ 2·|∂_BK S|`, and the low-conductance closure fires. No
  `Subsingleton`/empty baseline anywhere.
* **No new axioms, no `sorry`, no headline-path change.** The new file
  is an import-only leaf; the abstract `Step6/*.lean` and all
  downstream modules are unaffected.

## §1. Inventory delta

```
Step6/DichotomyGrounded.lean   new   (grounded thm:step6 + concrete instance)
OneThird.lean                  +1 import line
```

`Step6/ErrorControl.lean`, `Incoherence.lean`, `CommutingSquare.lean`,
`OverlapCounting.lean`, `RichnessBound.lean`, `Assembly.lean` — all
unchanged.

## §2. What the grounding does

| Symbol | Role (`step6.tex`) |
|---|---|
| `secondMoment_grounded` | re-export of `lem:gap-G5`(i): the dichotomy's overlap mass `M` *is* the genuine second moment `∑_L I(L)²` |
| `thm_step6_grounded` | `thm:step6` (`step6.tex:477-503`) on genuine data: from the genuine summed Step-4 bound (G9) conclude *expansion* `c_n·δ_n·M ≤ c_d·mult·δ_d·\|∂_BK S\|` ∨ *coherence* `δ_d·∑_bad w ≤ δ_n·M` |
| `thm_step6_rich_closure_grounded` | `rem:G5-closes-dichotomy` (`step6.tex:561-567`): under the genuine rich-case lower bound `c_R²·\|S\| ≤ M` (G10) and a genuine low-conductance hypothesis, expansion is impossible — **only coherence survives** |
| `thm_step6_rich_closure_grounded_of_firstMoment` | the same closure with `hRich` discharged from the Step-5 first-moment richness via `pair_overlap_sum_ge_vol` (G10) — the full G9 + G10 assembly |
| `thm_step6_grounded_concrete` | the non-vacuous `Fin 3 × Fin 3` instantiation (mg-9576 acceptance bar) |

`thm_step6_rich_closure_grounded` is the substantive deliverable: it
is the genuine quantitative dichotomy of `step6.tex` Step E — a
low-conductance cut `S` (one whose BK boundary is small relative to
`|S|`) cannot be in the expansion case, because expansion would give
`c_n δ_n · M ≤ c_d·mult·δ_d·|∂_BK S| < c_n δ_n c_R²·|S| ≤ c_n δ_n · M`,
a contradiction. Hence its bad overlap mass `∑_bad w_{αβ}` is at most
a `δ`-fraction of the total mass `M`. The `_of_firstMoment` variant
discharges the rich-case lower bound from the genuine Step-5 (R)
output, so the full chain G9 (summed Step-4) + G10 (`lem:gap-G5`) is
assembled from structural inputs.

The five `step6.tex` technical lemmas G6-G10 are consumed as already
landed: G9 (`lem:overlap-counting`) is grounded by S4-C's
`lem_sum_step4_grounded` (produces the `hSum` input here); G10
(`lem:gap-G5`) is `RichnessBound.pair_overlap_sum_ge_vol` /
`second_moment_eq_pair_overlap_sum`, already on genuine
`Finset (LinearExt α)` data; G6 (`prop:gap-g1`), G7
(`def:incoherent-pair`), G8 (`lem:gap3`) are upstream/structural
inputs to the dichotomy (G6 is parametric in the Step-1/Step-2 F1-F3
inputs; G8 is already on the genuine Step-1 `overlap`/`regularOverlap`
objects). The dichotomy `thm:step6` is the assembly point and is the
S6-A deliverable; `cor:pointwise` (Conclusion B / "pointwise
coherence is uniform") is the abstract `Step6.Assembly.cor_pointwise`,
left for S6-B.

## §3. Non-vacuous instantiation (`mg-9576` acceptance bar)

`Fin 3 × Fin 3` (product order), the genuine width-3 non-chain
9-element grid poset, with the singleton cut `S = {gridLinExt}` (the
anti-diagonal linear extension of S4-A), one rich interface, and
bad-set-subtracted fiber `{gridLinExt}`. `thm_step6_grounded_concrete`
bundles, all proved (not assumed):

1. `HasWidth (Fin 3 × Fin 3) 3` and `¬ IsChainPoset (Fin 3 × Fin 3)`
   — genuine width *exactly* 3, non-chain (from
   `Step4.witnessGrounded_nonvacuous`);
2. `1 ≤ |∂_BK {gridLinExt}|` — the BK boundary is genuinely non-empty,
   there is a real BK cut edge;
3. the `lem:gap-G5`(i) identity `∑_L I(L)² = ∑_{α,β} w_{αβ}` holds on
   the genuine data, and the genuine second moment is strictly
   positive (`M = 1`);
4. the dichotomy `thm_step6_grounded` genuinely fires: with constants
   for which the coherence case reads `2 ≤ 1` (false), it forces the
   **expansion** bound `1 ≤ 2·|∂_BK S|` — a genuine quantitative
   boundary lower bound, the exact analogue of S4-A's `1 ≤ 2·|∂_BK S|`;
5. the low-conductance closure `thm_step6_rich_closure_grounded`
   fires, with a genuinely true strict low-conductance hypothesis and
   the genuine (tight) rich-case bound `1 ≤ M`, delivering coherence.

No `Subsingleton`-on-empty baseline; the poset has 9 elements, the cut
and its BK boundary are genuine, the second moment is genuinely
positive. The acceptance bar — "the dichotomy must instantiate
non-vacuously at a concrete width-3 non-chain α" — is met.

**Honest scope note.** At a 9-element poset with a singleton cut one
cannot exhibit the *asymptotic* regime (genuinely low conductance
*with* genuine bad overlap mass): the summed Step-4 bound `hSum` and
the low-conductance hypothesis `hLow` are jointly satisfiable with
`∑_bad w > 0` only for large `α`. The concrete instance therefore has
`∑_bad w = 0` (genuine — a singleton rich family carries no
incoherent pair: a sign function cannot disagree with itself) and the
closure lands in coherence. The genuine quantitative content — "low
conductance forces coherence with genuine bad mass" — is the theorem
`thm_step6_rich_closure_grounded` itself, whose proof genuinely runs
the expansion-contradiction argument. This matches the S4-A / S5-D
non-vacuity precedent (genuine poset + genuine non-degenerate objects
+ theorem fires).

## §4. Abstract-scaffold finding — the `M`-variable collision

Default-skeptical re-read of `step6.tex:477-567` (`thm:step6` +
`rem:G5-closes-dichotomy`) against the abstract `Step6.Assembly`
surfaced one defect in the abstract scaffold (not in the paper, and
not a blocker):

* `step6.tex` writes `M` for **two distinct quantities**: the
  overlap-counting *multiplicity* constant of `lem:overlap-counting`
  (`step6.tex:347`, a width-dependent `O(1)` constant — the paper's
  Step C of the `thm:step6` proof switches to the letter `K` for it),
  and the overlap *mass* `M = ∑_{α,β} w_{αβ}` of `thm:step6`
  (`step6.tex:488`, the genuine second moment).
* The abstract `Step6.thm_step6` / `thm_step6_rich_closure` carry a
  **single** `M` variable. They are true arithmetic facts, but they
  cannot be grounded faithfully against the cascade: the summed
  Step-4 bound `lem_sum_step4_grounded` (G9) forces that `M` to be the
  multiplicity, while the rich-case lower bound
  `pair_overlap_sum_ge_vol` (G10) forces it to be the overlap mass.
  Routing the genuine objects through the single-`M` abstract
  `thm_step6_rich_closure` would put the overlap mass `M` on the
  right-hand side of the low-conductance hypothesis, making `hLow` a
  mixed `boundary·M` statement rather than the clean "boundary small
  vs `|S|`" statement the paper intends.

This is the same class of issue as `PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #6 (a type-clean signature that does not say what the paper
says), at a much smaller scale and caught before any downstream use.
**It is not an ill-posed target and not a missing dependency** — the
paper `thm:step6` is well-posed; the grounded port simply uses **two
distinct variables** (`mult` for the multiplicity, the explicit
`∑ pairOverlap` for the mass), which is the faithful shape. The
abstract `Step6.thm_step6` / `thm_step6_rich_closure` are left
untouched (per "note other issues, don't fix them" — they have no
current downstream consumer, so the conflation is presently
harmless); the grounded layer is correct and is what S6-B / Step 7
should consume. Recommend a follow-on cleanup of the abstract
`thm_step6` to two variables if it ever acquires a consumer.

## §5. No gap-discovery on the paper side

The paper's `thm:step6` proof (`step6.tex:505-567`) is a clean
case split (Step D) plus a closing contradiction (Step E) on top of
G6-G10. The case split is `δ_d·∑_bad w ≤ δ_n·M` vs its negation; the
negation, fed the summed Step-4 bound, yields the expansion bound.
The closing contradiction uses `lem:gap-G5`(iii) `c_R²·vol(S) ≤ M`.
Both are pure cleared-denominator `ℕ`-arithmetic once the genuine
objects (`∂_BK S`, `∑ pairOverlap`) are in place. No width-3
essentialism beyond what G6-G10 already respect; no missing mathlib
dependency. The S1-E RED finding (`PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #8: the `IsGoodFiber` G2 clause is broken) does **not** block
this port: Step 6 consumes the Step-1/Step-2 bad-set and density
bounds (F1-F3) *parametrically* (G6 `prop_gap_g1` takes them as
hypotheses), so the grounded `thm:step6` dichotomy is independent of
whether S1 delivers `goodFiberSet` non-empty — that gap is localised
to the S1 re-port and does not propagate into the Step-6 dichotomy
layer.

## §6. Build

`lake build OneThird.Step6.DichotomyGrounded` clean (the new file
builds in ~2s on the reused mathlib cache). Full `lake build` clean —
the new file is an import-only leaf, no downstream module consumes it.
No new warnings attributable to the new file, no `sorry`, no new
axioms. (The pre-existing `[DecidableEq Pair]` unused-hypothesis
linter warnings in `Step6/Assembly.lean` are untouched scaffold, not
a regression.)
