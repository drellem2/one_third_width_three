# State — S7-Conc-C — Session 1: the Step 6 budget constants `b_n, b_d`

**Ticket:** mg-5f3e (OneThird-S7-Conc-C: Piece 2 follow-on — extract
the Step 6 budget constants `b_n, b_d`).
**Branch:** `polecat-5f3e`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.2 Piece 2,
sub-arc `mg-S7-Conc-C`.
**Depends:** Piece 1 (Steps 1–6 cascade port) — complete: mg-9576
(S6-A dichotomy), mg-65af (S6-B `cor:pointwise` + cascade), mg-aa02
(S6 G6), mg-fc78 (S1 G2 re-port), mg-496b (genuine cascade compose,
Checkpoint 2 passed). mg-4ce6 (S7-Conc-A, the BK-graph carrier types
+ `GroundSet.lean`).

**Scope.** Sub-arc C of Piece 2 (S7-A–E concretisation): extract the
Step 6 budget constants `b_n, b_d` — concretise the Step 6
conductance-to-coherence dichotomy witness (`thm:step6` +
`cor:pointwise`, landed in Piece 1) into specific edge-weight bound
constants feeding the Step 7 variational-budget hypothesis.

---

## §0. Verdict — **GREEN-constants-extracted-and-project-cleanly**

The Step 6 budget constants are extracted as genuine concrete values
from the landed Step 6 cascade output, and they project cleanly into
the parametric `BandwidthData.VarBudgetHyp` signature. **No
block-and-report.**

`lean/OneThird/Step7/Step6Budget.lean` (NEW, ~270 LoC incl.
docstrings) is sorry-free, axiom-free (only `propext` /
`Classical.choice` / `Quot.sound`), and `lake build OneThird` is
clean (1437 jobs).

**The extracted constants.** The assembled Steps 1–6 cascade
`Step6.cascade_steps_1_6_grounded` (`Step6/PointwiseGrounded.lean`,
mg-65af) has conclusion (Conclusion B, `step6.tex:735-760`)

```
t_n · δ_d · ∑_{L ∈ A} I(L)²  ≤  t_d · (2 · δ_n · M)
```

with `δ = δ_n/δ_d` the coherence fraction of the dichotomy `thm:step6`,
`t = t_n/t_d` the `I²`-weighted threshold of `cor:pointwise`, `A` the
"mostly-disagreeing" exceptional set, and `M = ∑_{α,β} w_{αβ}` the
genuine second moment / overlap mass. Re-associated, this is exactly
a cleared-denominator budget bound `b_d · X ≤ b_n · M₀`, so the
**genuine Step 6 budget constants are**

```
b_n  :=  step6BudgetNum t_d δ_n  =  2 · t_d · δ_n
b_d  :=  step6BudgetDen t_n δ_d  =  t_n · δ_d
```

These are read off the literal multiplicative structure of the
cascade conclusion — `step6_budget_grounded` *proves* the re-association
(`cascade_steps_1_6_grounded` + `le_of_eq (by ring)`), so they are
not placeholders: they are provably the coefficients the Step 6
output carries.

---

## §1. Context — what the parametric S7-E signature needs

The S7-E headline `lem_bandwidth_le_four_bundled`
(`Step7/Prop71_Prop72_LemBandwidth.lean:380`, mg-516f) consumes the
variational-budget hypothesis as a parameter

```lean
(b_n b_d M₀ : ℕ)
(hBud : (BandwidthData.ofPotential …).VarBudgetHyp pairs b_n b_d M₀)
```

`BandwidthData.VarBudgetHyp pairs b_n b_d M₀` (`Step7/Bandwidth.lean:99`)
is the cleared-denominator form

```
b_d · ∑_{p ∈ posDeltaPairs} Δ⁺(p) · posMass(p)  ≤  b_n · M₀
```

of the paper's `∑ Δ⁺ · p ≤ η = o(1)` (`step7.tex:960-967`,
`lem:budget-var`). Its budget fraction `η = b_n / b_d` is supplied
by Step 6 — the conductance-to-coherence dichotomy plus the pointwise
corollary. mg-4ce6 (`state-S7-Conc-Session1.md` §5) recorded
sub-arc C ("extract `b_n, b_d` from the Step 6 `thm:step6` +
`cor:pointwise` grounded form") as **gated on Piece 1**. Piece 1 is
now complete; this session executes sub-arc C.

---

## §2. What was built

### §2.1. Files

| File | Δ |
|---|---:|
| `lean/OneThird/Step7/Step6Budget.lean` | +270 (NEW) |
| `lean/OneThird.lean` | +1 (import) |
| `docs/state-S7-Conc-C-Session1.md` | +NEW |
| `docs/state-S7-Conc-Session1.md` | §5 / §7.5 update |
| `docs/PROOF-STRUCTURE-ONBOARDING.md` | §4 cross-ref update |

**`AXIOMS.md` delta: none.** No new axioms, none dropped, no `sorry`
introduced.

### §2.2. The deliverables in `Step6Budget.lean`

| Declaration | What it is |
|---|---|
| `step6BudgetNum t_d δ_n := 2·t_d·δ_n` | the extracted budget numerator `b_n` |
| `step6BudgetDen t_n δ_d := t_n·δ_d` | the extracted budget denominator `b_d` |
| `step6_budget_grounded` | **the extraction theorem**: from the `cascade_steps_1_6_grounded` hypotheses, the budget bound `b_d · ∑_A I² ≤ b_n · M` in the `VarBudgetHyp` cleared shape |
| `varBudgetHyp_of_budget_bound` | **clean-projection bridge**: any `BandwidthData` whose budget quantity is dominated by the Step 6 exceptional `I²`-mass satisfies `VarBudgetHyp` with the extracted constants |
| `step6_varBudgetHyp_grounded` | end-to-end wire: Step 6 cascade hypotheses ⟹ `BandwidthData.VarBudgetHyp …  (step6BudgetNum) (step6BudgetDen) M` |
| `step6_budget_constants_antichain3` | non-vacuous instance: extracts `b_n = 4`, `b_d = 1` at the genuine `Antichain3` cascade |
| `antichain3DisagreeBudget` + `antichain3_varBudgetHyp_genuine` | a genuine compiler-checked `BandwidthData.VarBudgetHyp` carrying `b_n = 4`, `b_d = 1` |

---

## §3. Why this projects cleanly — the non-triviality bar

The ticket's non-triviality bar: the extracted constants must be the
genuine concrete values from the landed Step 6 output, not
placeholders; **block-and-report if they do not project cleanly into
the parametric signature.**

**They do project cleanly. No block-and-report.** Three points:

1. **Genuine, not placeholder.** `step6_budget_grounded` *proves*
   `b_d · ∑_A I² ≤ b_n · M` by reducing it to
   `cascade_steps_1_6_grounded` via `le_of_eq (by ring)` — the
   `ring` step is precisely the re-association
   `t_d · (2·δ_n·M) = 2·t_d·δ_n·M`. So `b_n = 2·t_d·δ_n`,
   `b_d = t_n·δ_d` are *provably* the coefficients the landed Step 6
   cascade carries.

2. **Clean projection.** `varBudgetHyp_of_budget_bound` shows that
   for **any** `BandwidthData D` and budget index set whose budget
   quantity `∑ Δ⁺·posMass` is dominated by the Step 6 exceptional
   `I²`-mass, `D.VarBudgetHyp` holds with exactly the extracted
   `b_n, b_d` — no adapter algebra, the cleared-denominator shapes
   coincide. `step6_varBudgetHyp_grounded` is the composed wire.
   `antichain3_varBudgetHyp_genuine` exhibits a concrete,
   compiler-checked `VarBudgetHyp` term carrying `b_n = 4, b_d = 1`.

3. **`M₀` reconciliation is a disclosed coordination point, not a
   projection failure.** The Step 6 budget's natural cleared
   denominator is the second moment `M = ∑_{α,β} w_{αβ}` (it is the
   RHS factor of the cascade conclusion). The eventual
   `lem_bandwidth_le_four_bundled` call shares a single `M₀` between
   `VarBudgetHyp` and the Step 5 `RichnessHyp`, conventionally
   `|LE(P)|`. Reconciling these — and converting the budget index
   set from the linear-extension universe to the rich-pair finset
   via the paper `lem:budget-var` — is sub-arc `mg-S7-Conc-D` (the
   assembly) plus `mg-S7-Conc-B` (the Step 5 side). It is **not** a
   block: the extracted budget *fraction* `b_n / b_d` is
   denominator-independent, so the *constants* slot into the
   parametric signature unchanged. This is exactly the design the
   parent scoping doc anticipated (`OneThird-Option-A-FULL-REFACTOR-scoping.md`
   §2.2 hold-the-line risk 1, "constant-extraction mismatch … some
   adapter algebra may be needed"): the constants project, the
   index/denominator wiring is `-D`.

---

## §4. Vacuity-discovery audit (Daniel's skeptical lens)

Per `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks:

1. **Satisfiability.** `antichain3_varBudgetHyp_genuine` is a
   compiler-checked `VarBudgetHyp` term over the genuine `Antichain3`
   data with strictly-positive sums (`∑ Δ⁺·posMass = 24`,
   `M = 24`, the budget bound `1·24 ≤ 4·24`). The witness routes
   through `cascade_steps_1_6_grounded` on the genuine S1
   `goodFiberSet a0 a1` fiber (mg-496b) — every quantity would be
   `0` were that fiber empty (its provable pre-mg-fc78 state), so
   the file would not compile. Non-vacuous.

2. **Discharge-coverage.** The cited artefact
   `cascade_steps_1_6_grounded` (mg-65af) is consumed *with its full
   hypothesis set* — `step6_budget_grounded` threads all eight
   cascade hypotheses; `step6_budget_constants_antichain3` rebuilds
   the genuine `Antichain3` cascade hypotheses (matching
   `cascade_steps_1_6_grounded_genuine`, mg-496b) and routes through
   `step6_budget_grounded`. No over-claim of an artefact's scope.

3. **Universal-quantifier truthfulness.** The extraction theorems
   quantify universally over the cascade data and constants; the
   `VarBudgetHyp` conclusion is *conditional* on the cascade
   hypotheses plus the model bound `hModel`. No free-standing false
   `∀ α, ∃ L` universal is introduced.

**Verdict: no vacuity discovery.** The Step 6 grounded forms project
into the budget constants exactly as the parametric S7-E signature
anticipated.

---

## §5. What remains (post-C follow-on)

* **mg-S7-Conc-B** — extract `c_n, c_d, M₀` from the Step 5
  `thm:step5` (R)-branch grounded form. Independent of this session;
  dispatchable in parallel.
* **mg-S7-Conc-D** — the assembly. Consumes `step6_varBudgetHyp_grounded`
  (this session) to build the concrete `hBud : VarBudgetHyp` on the
  genuine `BandwidthData.ofPotential`, and invokes
  `lem_bandwidth_le_four_bundled_groundSet`. Two wiring tasks `-D`
  must do, both disclosed here and in the scoping doc:
  (a) the `lem:budget-var` index conversion (linear-extension
  universe ⟶ rich-pair finset for the budget quantity);
  (b) the uniform choice of `M₀` shared with the `-B` richness side.
  Neither is a projection failure — see §3 point 3.

---

## §6. Acceptance bars

- [x] `lake build OneThird.Step7.Step6Budget` clean.
- [x] `lake build OneThird` (full root) clean — 1437 jobs, 0 errors.
- [x] No `sorry` in `Step6Budget.lean`.
- [x] No new axioms — `#print axioms` on all five theorems shows
  only `propext` / `Classical.choice` / `Quot.sound`
  (`AXIOMS.md` unchanged).
- [x] Wired into `OneThird.lean` root.
- [x] Constants extracted as **genuine concrete values** —
  `step6_budget_grounded` proves `b_n = 2·t_d·δ_n`, `b_d = t_n·δ_d`
  are the cascade-conclusion coefficients (not placeholders).
- [x] Clean projection into `BandwidthData.VarBudgetHyp` verified
  (`varBudgetHyp_of_budget_bound`, `step6_varBudgetHyp_grounded`,
  `antichain3_varBudgetHyp_genuine`).
- [x] Non-vacuous concrete instance — `b_n = 4`, `b_d = 1` extracted
  at the genuine `Antichain3` cascade with positive sums.
- [x] Skeptical vacuity-discovery audit applied (§4) — no discovery.
- [x] `M₀`-reconciliation / index-conversion follow-on disclosed
  (§3 point 3, §5) — gated on `mg-S7-Conc-D`, not a block.

---

## §7. Cross-reference index

### §7.1. Lean (this work)

* `lean/OneThird/Step7/Step6Budget.lean` (NEW) — `step6BudgetNum`,
  `step6BudgetDen`, `step6_budget_grounded`,
  `varBudgetHyp_of_budget_bound`, `step6_varBudgetHyp_grounded`,
  `step6_budget_constants_antichain3`, `antichain3DisagreeBudget`,
  `antichain3_varBudgetHyp_genuine`.
* `lean/OneThird.lean` — `import OneThird.Step7.Step6Budget` added.

### §7.2. Lean (consumed, unmodified)

* `lean/OneThird/Step6/PointwiseGrounded.lean` (mg-65af) —
  `cascade_steps_1_6_grounded`, `cor_pointwise_grounded`,
  `disagreePairs`.
* `lean/OneThird/Step6/DichotomyGrounded.lean` (mg-9576) —
  `thm_step6_grounded`.
* `lean/OneThird/Step6/CascadeComposed.lean` (mg-496b) — the genuine
  S1-fiber cascade witness `cascade_steps_1_6_grounded_genuine` and
  its `gen_*` data (`genRich`, `genFstar`, `genSign`, `genLP`,
  `genCut`, `gen_M`, `gen_A_sum`, `gen_disagree_mass`,
  `gen_visibility`, `gen_LP_card`, `gen_step5_richness`).
* `lean/OneThird/Step7/Bandwidth.lean` — `BandwidthData`,
  `VarBudgetHyp`, `posDeltaPairs`.
* `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean` (mg-516f) —
  `lem_bandwidth_le_four_bundled` (the parametric `b_n, b_d`
  consumer).

### §7.3. Paper

* `step7.tex:960-967` — `lem:budget-var` (the `∑ Δ⁺·p ≤ η`
  variational budget).
* `step6.tex:477-503` — `thm:step6` (the conductance-to-coherence
  dichotomy).
* `step6.tex:583-713` — `cor:pointwise` (Conclusion B).
* `step6.tex:735-760` — the assembled Steps 1–6 cascade.

### §7.4. Predecessor docs

* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) — §2.2
  Piece 2 spec, sub-arc `mg-S7-Conc-C`.
* `docs/state-S7-Conc-Session1.md` (mg-4ce6) — S7-Conc-A, the
  BK-graph carrier types; §5 records sub-arc C as gated on Piece 1.
* `docs/state-S7-E-prop71-prop72-Session1.md` (mg-516f) — the
  parametric S7-E grounded forms consuming `b_n, b_d`.
* `docs/state-Cascade-Compose-Session1.md` (mg-496b) — Piece 1
  termination; the genuine cascade witness.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §3 pitfall #2
  (the three-check skeptical lens applied in §4).

### §7.5. Predecessor work items

mg-d8c7 (Option A' scoping), mg-4ce6 (S7-Conc-A), mg-516f (S7-E),
mg-65af (S6-B cascade), mg-9576 (S6-A dichotomy), mg-aa02 (S6 G6),
mg-fc78 (S1 G2), mg-496b (cascade compose), **mg-5f3e (this
session)**.

---

## §8. Maintenance contract

This file is the state record for sub-arc C (Step 6 budget constant
extraction) of Piece 2. Update it in the same commit as any change
that:

* Lands `mg-S7-Conc-D` (record the `lem:budget-var` index conversion
  and the `M₀` reconciliation against this file's §3 point 3 / §5).
* Changes the `step6BudgetNum` / `step6BudgetDen` definitions or the
  `Step6Budget.lean` extraction theorems.
* Re-extracts the Step 6 budget on a different cascade output shape
  (if `cascade_steps_1_6_grounded` is restated).
