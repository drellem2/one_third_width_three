# State — S7-Conc-D — Session 1: assemble `L_S7E`, discharge the `VarBudgetHyp` / `RichnessHyp` witnesses

**Ticket:** mg-3f00 (OneThird-S7-Conc-D: Piece 2 follow-on — assemble
`L_S7E` and discharge the `VarBudgetHyp` / `RichnessHyp` witnesses).
**Branch:** `polecat-3f00`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.2 Piece 2,
sub-arc mg-S7-Conc-D (the **assembly** ticket that completes Piece 2).
**Depends:** mg-8f9c (S7-Conc-B, Step 5 richness constants `c_n, c_d,
M₀` — landed `2c5b625`), mg-5f3e (S7-Conc-C, Step 6 budget constants
`b_n, b_d` — landed `61102fe`).

**Scope.** Wire the extracted constants `c_n, c_d, M₀` (mg-8f9c) and
`b_n, b_d` (mg-5f3e) into concrete `VarBudgetHyp` / `RichnessHyp`
witness proofs, then invoke `lem_bandwidth_le_four_bundled_groundSet`
to produce the concrete `L_S7E : Step7.LayeredWidth3` with
`bandwidth ≤ 4` — the object the Piece 3 S7-F bridge consumes. **When
this lands, Piece 2 is complete.**

---

## §0. Verdict — **GREEN-Piece-2-complete**

The assembly is delivered: `lean/OneThird/Step7/S7EAssembly.lean`
(NEW, ~290 LoC) composes the mg-8f9c richness discharge and the
mg-5f3e budget discharge onto a single common `BandwidthData` and a
single common cleared denominator `M₀`, and invokes the S7-E
bandwidth lemma.

* **`lemS7E_groundSet`** — the assembly theorem.  Discharges **both**
  `hBud` (via mg-5f3e `varBudgetHyp_of_budget_bound`, extracted
  `b_n, b_d`) and `hRich` (via mg-8f9c `richnessHyp_groundSet_of_step5`,
  extracted `c_n = 1, c_d = 2`) — neither is a free hypothesis — and
  produces `L_S7E : LayeredWidth3 richPairs` with `bandwidth ≤ 4`.
* **`lemS7E_antichain3`** — the non-vacuous concrete instance: the
  assembly fired on the genuine width-3 non-chain poset `Antichain3`,
  a **fully closed term** (no free hypotheses, no placeholders) with
  the genuine extracted constants and the shared denominator
  `M₀ = genLP.card = 6 = |LE(Antichain3)|`.
* **`L_S7E_antichain3`** — the concrete `LayeredWidth3` witness term,
  with `L_S7E_antichain3_bandwidth : L_S7E_antichain3.bandwidth ≤ 4`.

**No 9th vacuity-discovery.** The mg-3f00 block-and-report triggers —
constant-extraction mismatch, pair-space convention misalignment with
`lem:layered-from-step7` — do **not** fire.  See §4.

`lake build OneThird` clean; `S7EAssembly.lean` is sorry-free,
axiom-free (only `propext` / `Classical.choice` / `Quot.sound`).
`AXIOMS.md` unchanged.

---

## §1. Context — what mg-8f9c and mg-5f3e left for the assembly

The S7-E bandwidth lemma `lem_bandwidth_le_four_bundled_groundSet`
(`Step7/GroundSet.lean`, mg-4ce6) consumes **two** parametric
hypotheses, sharing one cleared denominator `M₀`:

```lean
(hBud  : (BandwidthData.ofPotential …).VarBudgetHyp  pairs     b_n b_d M₀)
(hRich : (BandwidthData.ofPotential …).RichnessHyp  richPairs c_n c_d M₀)
```

* **mg-8f9c** (S7-Conc-B) extracted `c_n = 1, c_d = 2, M₀ = |LP|` and
  built the richness *discharge* `richnessHyp_groundSet_of_step5`
  (`Step7/RichnessConstants.lean`) from the landed Step 5 G4 grounded
  form `Step5.fiber_mass_grounded`.  It also built
  `lem_bandwidth_le_four_bundled_of_step5_richness`, which discharges
  `hRich` and threads `hBud` — fixing the shared `M₀ = LP.card`.
* **mg-5f3e** (S7-Conc-C) extracted `b_n = 2·t_d·δ_n, b_d = t_n·δ_d`
  and built the budget projection bridge `varBudgetHyp_of_budget_bound`
  (`Step7/Step6Budget.lean`), which derives `VarBudgetHyp` from a
  model bound and a cleared budget bound — for **any** `M₀`.

Both state docs flagged the remaining assembly work and one explicit
coordination point:

* `state-S7-Conc-B-Session1.md` §4: "Sub-arc mg-S7-Conc-C must
  produce `hBud` for the **same** `posMass` and the **same**
  `M₀ := |LP|`."  → handled here.
* `state-S7-Conc-C-Session1.md` §3 point 3 / §5: "the uniform choice
  of `M₀` shared with the `-B` richness side … is sub-arc
  `mg-S7-Conc-D`.  Not a projection failure: the budget *fraction*
  `b_n / b_d` is denominator-independent."  → handled here.

---

## §2. What was built

### §2.1. Files

| File | Δ |
|---|---:|
| `lean/OneThird/Step7/S7EAssembly.lean` | +~290 (NEW) |
| `lean/OneThird.lean` | +1 (import) |
| `docs/state-S7-Conc-D-Session1.md` | +NEW |
| `docs/state-S7-Conc-Session1.md` | §5 update (mg-S7-Conc-D done) |
| `docs/PROOF-STRUCTURE-ONBOARDING.md` | §0 + §4 cross-ref update |

**`AXIOMS.md` delta: none.**  No new axioms, none dropped, no
`sorry`.

### §2.2. `lemS7E_groundSet` — the assembly theorem (§1 of the file)

Takes the genuine Steps 5–6 cascade facts:

* the **Step 5 G4** interface-partition data
  `hcover`/`hdisj`/`hthin`/`hact` (the mg-8f9c richness inputs);
* the **Step 6** budget data in cleared form: `hModel` (the rich-pair
  variational budget is dominated by the Step 6 exceptional mass)
  and `hBound : b_d · exceptionalMass ≤ b_n · LP.card` (the cleared
  `lem:budget-var` bound, in the `|LE(P)|` denominator).

It then:

1. discharges `hRich` via `richnessHyp_groundSet_of_step5` with the
   genuine `c_n = 1, c_d = 2, M₀ = LP.card`;
2. discharges `hBud` via `varBudgetHyp_of_budget_bound` with the
   extracted `b_n, b_d` at the **same** `M₀ := LP.card`;
3. invokes `lem_bandwidth_le_four_bundled_of_step5_richness` (the
   mg-8f9c clean-projection wrapper around
   `lem_bandwidth_le_four_bundled_groundSet`);

and concludes `∃ L : LayeredWidth3 richPairs, L.bandwidth ≤ 4 ∧
(cardinality partition) ∧ (exceptional-mass bound)`.  **Neither
`hBud` nor `hRich` appears in the signature** — they are discharged.

### §2.3. `lemS7E_antichain3` — the non-vacuous concrete `L_S7E` (§2)

Fires `lemS7E_groundSet` on the genuine width-3 non-chain poset
`Antichain3` (the mg-496b Steps 1–6 cascade carrier).  A **fully
closed term** — no free hypotheses.  Choices:

| Slot | Value | Genuineness |
|---|---|---|
| `c_n, c_d` | `1, 2` | mg-8f9c — post-activation density `c'_T = 1/2` |
| `b_n, b_d` | `step6BudgetNum 2 1, step6BudgetDen 1 1` (`= 4, 1`) | mg-5f3e — genuine `Antichain3` cascade constants |
| `M₀` | `genLP.card = 6` | genuine `|LE(Antichain3)|` (`gen_LP_card`) |
| `richPairs = pairs` | `univ` (9 pairs) | genuinely non-empty rich-pair set |
| `goodFiber` | `fun _ => univ` (6-elt fibers) | richness `1·6 ≤ 2·6`, genuine slack |

Companion: `L_S7E_antichain3` (the `LayeredWidth3` witness term),
`L_S7E_antichain3_bandwidth` (`bandwidth ≤ 4`),
`lemS7E_antichain3_nonvacuous` (the non-vacuity certificate —
constants evaluate to `4, 1, 6`; `richPairs` non-empty).

---

## §3. The `M₀` reconciliation — how the two sides were made to agree

`lem_bandwidth_le_four_bundled_groundSet` shares **one** `M₀`
between `hBud` and `hRich`.  The two sub-arcs delivered their
constants against different natural denominators:

* mg-8f9c richness: `M₀ = LP.card` (`|LE(P)|`, the `step8.tex`
  convention) — **fixed**, `RichnessHyp` is a per-pair cardinality
  bound `1·|LP| ≤ 2·|goodFiber p|`.
* mg-5f3e budget: the Step 6 cascade's own cleared denominator is the
  second moment `M = ∑ w_{αβ}` — but `varBudgetHyp_of_budget_bound`
  is **denominator-independent**: it derives `VarBudgetHyp
  budgetPairs b_n b_d M₀` for **any** `M₀` from a model bound and a
  cleared `hBound : b_d · exceptionalMass ≤ b_n · M₀`.

**The assembly takes the budget side at `M₀ := LP.card`** — the
richness side's denominator.  This is exactly the resolution the
mg-5f3e state doc anticipated: "the budget *fraction* `b_n / b_d` is
denominator-independent, so the *constants* slot into the parametric
signature unchanged."  No adapter algebra: `lemS7E_groundSet`
type-checks the composition directly.

`hBound` in the `LP.card` denominator is the cleared form of the
paper's `lem:budget-var` conclusion (`step7.tex:960-967`), whose
budget is normalised against `|LE(P)|`.  **Honest scope boundary:**
deriving `hBound` *from* `step6_budget_grounded`'s `M`-denominated
output is the genuine `lem:budget-var` index conversion — new
theorem-proving outside Piece 2's concrete-instantiation scope (§2.2
of the scoping doc: "concrete-instantiation engineering, not new
theorem proving").  It is threaded as a hypothesis of
`lemS7E_groundSet`, the same shape mg-8f9c / mg-5f3e used for their
genuine Steps 5–6 cascade inputs.  Discharging it is Piece 3 work.

---

## §4. Vacuity-discovery audit (Daniel's skeptical lens)

Per `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks, and
the two explicit mg-3f00 block-and-report triggers.

1. **Satisfiability.**  `lemS7E_antichain3` is a compiler-checked,
   **fully closed** `∃ L, L.bandwidth ≤ 4 ∧ …` on the genuine
   `Antichain3`.  `hBud` and `hRich` are discharged inside it (not
   hypotheses).  The rich-pair set `univ` has `9` elements,
   `M₀ = 6 > 0`, each good fiber has `6` elements — the richness
   `1·6 ≤ 2·6` holds with genuine slack.  Not vacuous.
2. **Discharge-coverage.**  The assembly cites exactly two artefacts
   as the discharges — mg-8f9c `richnessHyp_groundSet_of_step5` and
   mg-5f3e `varBudgetHyp_of_budget_bound` — each consumed with its
   full hypothesis set (`lemS7E_groundSet` threads the Step 5 G4 data
   and the Step 6 cleared budget data).  No over-claim of an
   artefact's scope.
3. **Universal-quantifier truthfulness.**  `lemS7E_groundSet`
   quantifies universally over the cascade data and constants; the
   `∃ L` conclusion is conditional on the genuine Steps 5–6 cascade
   facts, exactly as the paper's `prop:72` is conditional on the
   Step 5/6 budget.  No free-standing false `∀ α, ∃ L with L.w ≤ 4`
   universal (the form refuted by mg-ac13's 3-disjoint-chains
   counterexample).

**Block-and-report trigger A — constant-extraction mismatch:**
does not fire.  The mg-8f9c `c_n, c_d` and the mg-5f3e `b_n, b_d`
project into the shared-`M₀` S7-E signature with no adapter algebra;
the only coordination — the `M₀` choice — is resolved by the
denominator-independence of `varBudgetHyp_of_budget_bound` (§3).

**Block-and-report trigger B — pair-space convention misalignment
with `lem:layered-from-step7`:** does not fire.  The pair space is
`Pair := α × α` (the ambient ground-set pair type fixed by
`Step7/GroundSet.lean`, mg-4ce6), `richPairs ⊆ pairs ⊆ α × α` the
Step 5 Dilworth-derived rich-pair sub-finset.  `L_S7E` has type
`LayeredWidth3 (richPairs : Finset (α × α))` — exactly the §2.2 spec
output `L_{S7E} : Step7.LayeredWidth3 (richPairs α)`.  The Piece 3
bridge `lem:layered-from-step7` is **not yet in tree** (verified: no
`lem_layered_from_step7` symbol under `lean/`), so this is the
documented uniform convention, consistent across mg-4ce6 / mg-8f9c /
mg-5f3e; no misalignment is observable.

**Verdict:** no 9th vacuity-discovery.  The assembly is a pure
composition of two landed, sound discharge bridges; cumulative
count stays at 8 (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970,
mg-ac13, mg-5fbd, mg-0bd1).

---

## §5. Acceptance bars

- [x] `lake build OneThird` clean.
- [x] No `sorry` in `S7EAssembly.lean`.
- [x] No new axioms (`AXIOMS.md` unchanged).
- [x] `VarBudgetHyp` and `RichnessHyp` discharged with the real
  extracted constants (`c_n = 1, c_d = 2`; `b_n = step6BudgetNum 2 1,
  b_d = step6BudgetDen 1 1`) — neither is a free hypothesis of
  `lemS7E_groundSet`.
- [x] `lem_bandwidth_le_four_bundled_groundSet` invoked (via the
  mg-8f9c `lem_bandwidth_le_four_bundled_of_step5_richness` wrapper);
  output is `L_S7E : LayeredWidth3 (richPairs : Finset (α × α))` with
  `bandwidth ≤ 4`.
- [x] Non-vacuous, fully closed concrete `L_S7E` on the genuine
  width-3 non-chain poset `Antichain3` (`lemS7E_antichain3`,
  `L_S7E_antichain3`, `lemS7E_antichain3_nonvacuous`).
- [x] No constant-extraction mismatch; no pair-space misalignment
  (§4) — block-and-report does not fire.
- [x] Wired into `OneThird.lean` root.
- [x] Skeptical vacuity audit applied (§4) — no discovery.

---

## §6. What remains (Piece 2 complete; Piece 3 next)

**Piece 2 is complete.**  mg-S7-Conc-A (BK-graph carrier types,
mg-4ce6), -B (Step 5 richness constants, mg-8f9c), -C (Step 6 budget
constants, mg-5f3e), -D (assembly, this session) are all landed.

The Piece 3 S7-F bridge (`lem:layered-from-step7`,
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3) consumes
`L_S7E` and lifts it to a `Step8.LayeredDecomposition α`.  Two items
this session disclosed for Piece 3:

* **The `lem:budget-var` index conversion.**  `lemS7E_groundSet`
  threads `hModel` + `hBound` (the cleared `lem:budget-var` output in
  the `|LE(P)|` denominator).  Deriving these from
  `step6_budget_grounded`'s `M`-denominated cascade output is the
  genuine `lem:budget-var` port — new theorem-proving, deferred to
  Piece 3 (or a dedicated follow-on).  See §3.
* **A positive-budget instantiation.**  `lemS7E_antichain3` runs with
  the constant BFS potential (budget genuinely `0`,
  `richPairsOut = ∅`).  The genuine positive-budget `VarBudgetHyp`
  with the same `b_n = 4, b_d = 1` is independently certified by
  mg-5f3e's `antichain3_varBudgetHyp_genuine`; `lemS7E_groundSet` is
  fully general over the budget data, so Piece 3 instantiates it with
  a positive budget unchanged.

---

## §7. Cross-reference index

### §7.1. Lean (this work)

* `lean/OneThird/Step7/S7EAssembly.lean` (NEW) — `lemS7E_groundSet`,
  `lemS7E_antichain3`, `L_S7E_antichain3`, `L_S7E_antichain3_bandwidth`,
  `lemS7E_antichain3_nonvacuous`.
* `lean/OneThird.lean` — single-line `import OneThird.Step7.S7EAssembly`.

### §7.2. Lean (consumed, unmodified)

* `lean/OneThird/Step7/RichnessConstants.lean` (mg-8f9c) —
  `richnessHyp_groundSet_of_step5`,
  `lem_bandwidth_le_four_bundled_of_step5_richness`.
* `lean/OneThird/Step7/Step6Budget.lean` (mg-5f3e) —
  `varBudgetHyp_of_budget_bound`, `step6BudgetNum`, `step6BudgetDen`.
* `lean/OneThird/Step7/GroundSet.lean` (mg-4ce6) —
  `lem_bandwidth_le_four_bundled_groundSet`, `BKVertex`, `BKEdge`.
* `lean/OneThird/Step7/Bandwidth.lean` — `BandwidthData`,
  `VarBudgetHyp`, `RichnessHyp`, `BandwidthData.ofPotential`.
* `lean/OneThird/Step7/Assembly.lean` — `LayeredWidth3`, `prop_72`.
* `lean/OneThird/Step7/Potential.lean` — `bfsPotentialData`,
  `bfsSumPot`.
* `lean/OneThird/Step6/CascadeComposed.lean` (mg-496b) — `Antichain3`,
  `genLP`, `gen_LP_card`.

### §7.3. Paper

* `step7.tex:1018-1056` + `step7.tex:1015-1018` — `lem:bandwidth`,
  `rem:w0-constant`.
* `step7.tex:1175-1193` — `prop:72`.
* `step7.tex:960-967` — `lem:budget-var` (the `M₀`-reconciliation
  conversion disclosed in §3).
* `step8.tex:1983-2106` — `lem:layered-from-step7` (the Piece 3
  bridge consuming `L_S7E`).

### §7.4. Predecessor docs

* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) — §2.2
  Piece 2 spec, sub-arc mg-S7-Conc-D.
* `docs/state-S7-Conc-Session1.md` (mg-4ce6) — S7-Conc-A.
* `docs/state-S7-Conc-B-Session1.md` (mg-8f9c) — S7-Conc-B.
* `docs/state-S7-Conc-C-Session1.md` (mg-5f3e) — S7-Conc-C.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §3 pitfall #2
  (the three-check skeptical lens applied in §4).

### §7.5. Predecessor work items

mg-d8c7 (Option A' scoping), mg-a22b (MA-Sig), mg-6ab8 (Steps 1-7
scoping), mg-516f (S7-E), mg-4ce6 (S7-Conc-A), mg-8f9c (S7-Conc-B),
mg-5f3e (S7-Conc-C), **mg-3f00 (this session — S7-Conc-D, completes
Piece 2)**.

---

## §8. Maintenance contract

This file is the state record for Piece 2 sub-arc mg-S7-Conc-D
(the S7-E assembly) of the Option A' FULL REFACTOR.  Update it in the
same commit as any change that:

* Changes `lemS7E_groundSet`'s discharge composition (the `M₀`
  reconciliation, the `hModel` / `hBound` budget interface).
* Lands the genuine `lem:budget-var` index conversion (record how
  `hBound` is then derived from `step6_budget_grounded`).
* Re-fires the concrete `L_S7E` with a positive budget.

If Piece 3 (S7-F bridge) surfaces a mismatch between `L_S7E`'s output
shape (`LayeredWidth3 (richPairs : Finset (α × α))`) and what
`lem:layered-from-step7` consumes, record it here and re-scope.
