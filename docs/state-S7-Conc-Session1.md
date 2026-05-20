# State — S7-Conc — Session 1: S7-A–E grounded forms concretised to the BK-graph ground set

**Ticket:** mg-4ce6 (OneThird-Refactor-P2: S7-A-E scaffolding to
concrete ground-set).
**Branch:** `polecat-mg-4ce6`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.2 piece 2.
**Depends:** mg-516f (S7-E `lem_bandwidth_le_four_bundled` — landed
15a5308); mg-a22b (MA-Sig signature contract — landed 369a0a0).

**Scope.** Piece 2 of the 5-piece Option A' FULL REFACTOR: wire the
*parametric* S7-A–E grounded scaffolding to a **concrete BK-graph
ground-set** `α`, so that the S7-F bridge (piece 3) and the
`MainAssembly` refactor (piece 4) consume concrete objects rather
than abstract type variables.

---

## §0. Verdict — **GREEN-piece-2-type-concretisation-delivered**

The piece-1-independent core of piece 2 is delivered:
`lean/OneThird/Step7/GroundSet.lean` (NEW, ~330 LoC) fixes the
three S7 carrier types to the concrete BK-graph ground set and
re-exports every S7-E grounded deliverable at those types.

**No 8th vacuity-discovery.** The S7-E grounded forms (mg-516f)
concretise cleanly: the concretised theorems are pure
instantiations of the parametric S7-E theorems, and `lake build
OneThird` is clean. The skeptical re-audit
(`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks)
passes — see §4 below.

**Honest scope boundary.** Piece 2's full §2.2 spec has four
sub-arcs: mg-S7-Conc-A (BK-graph data), -B (Step 5 constants), -C
(Step 6 constants), -D (assembly). This session delivers **-A in
full** plus the **type-level half of -D** (the concretised
`lem_bandwidth_le_four_bundled`). Sub-arcs **-B and -C — extracting
the concrete numerical constants `c_n, c_d, b_n, b_d, M₀` and the
`VarBudgetHyp` / `RichnessHyp` *proofs* from the Steps 5–6 grounded
forms — are genuinely blocked on piece 1**, which is not yet in
tree. This is **not a gap discovered here**: the parent scoping
doc already records it (`OneThird-Option-A-FULL-REFACTOR-scoping.md`
§2.2 "Upstream dependencies: Piece 1 (Steps 5 + 6 grounded)"; §7.3
"Depends: piece 1"). The honest piece-2 form threads those
Steps 5–6 outputs as **hypotheses** (`hBud`, `hRich`) — which is
exactly what lets piece 2 land **in parallel with piece 1** (ticket
"Parallelizes with P1"). See §5 for the follow-on recommendation.

---

## §1. Context — what the S7-A–E pilot left parametric

The S7-A–E pilot (mg-4584 / 9331 / 1069 / d135 / 516f) landed the
Step 7 grounded forms. The headline S7-E deliverable
`lem_bandwidth_le_four_bundled`
(`Step7/Prop71_Prop72_LemBandwidth.lean:380`) has signature:

```lean
theorem lem_bandwidth_le_four_bundled
    {Vertex Edge : Type*} [DecidableEq Vertex] [DecidableEq Edge]
    {Pair : Type*} [DecidableEq Pair]
    (src tgt : Edge → Vertex) (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ) (path : Vertex → List Edge)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ)
    (pairs richPairs : Finset Pair)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : … .VarBudgetHyp pairs b_n b_d M₀)
    (hRich : … .RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : LayeredWidth3 richPairs), L.bandwidth ≤ 4 ∧ …
```

It is **parametric over three carrier types** `Vertex`, `Edge`,
`Pair`. The S7-E state doc (mg-516f) flagged this explicitly:

> "It delivers … `LayeredWidth3 richPairs` with a `bandwidth : ℕ`
> field … The S7-F bridge has the job of converting this into a
> `Step8.LayeredDecomposition α`."

The S7-F bridge (piece 3) **cannot** build a
`LayeredDecomposition α` from a `LayeredWidth3` over an *abstract*
`Pair` — it needs `Pair` related to the ground set `α`. Piece 2
(this session) closes that type-concretisation gap.

---

## §2. What was built

### §2.1. Files

| File | Δ |
|---|---:|
| `lean/OneThird/Step7/GroundSet.lean` | +330 (NEW) |
| `lean/OneThird.lean` | +1 (import) |
| `docs/state-S7-Conc-Session1.md` | +NEW |
| `docs/PROOF-STRUCTURE-ONBOARDING.md` | §4 cross-ref update |

**`AXIOMS.md` delta: none.** No new axioms, none dropped, no
`sorry` introduced.

### §2.2. The concrete carrier types (sub-arc mg-S7-Conc-A)

`GroundSet.lean` §1 fixes the three S7 carrier types:

| S7 carrier | Concrete type | Definition |
|---|---|---|
| `Vertex` | `BKVertex α` | `abbrev` for `LinearExt α` |
| `Edge` | `BKEdge α` | `structure` — `BKAdj`-adjacent ordered pair of linear extensions, with `src`, `tgt`, `isAdj` fields |
| `Pair` | `α × α` | the ambient ground-set pair space |

* `BKEdge α` carries a `DecidableEq` instance (endpoints decide
  equality; the `isAdj` field is proof-irrelevant).
* `BKEdge.bkGraph_adj` proves a `BKEdge` is genuinely an edge of
  `bkGraph α` — `(bkGraph α).Adj e.src e.tgt`.
* `Pair := α × α` is the honest concrete choice: the paper's rich
  incomparable pairs `(a_i, b_j)` live in `A × B ⊆ α × α`, where
  `A, B` come from the Step 5 Dilworth decomposition
  `X = A ⊔ B ⊔ C`. Fixing `Pair := A × B` would *itself* depend on
  piece 1 (the Dilworth split is a Step 5 output); `α × α` is the
  piece-1-independent ambient pair type, and `richPairs ⊆ pairs`
  stays a parameter for piece 1 to instantiate as the actual
  rich-pair finset.

### §2.3. The concretised S7-E surface (type-level sub-arc mg-S7-Conc-D)

`GroundSet.lean` §2–§5 re-exports every S7-E grounded deliverable
at the concrete carrier types, with the structural endpoint maps
fixed to the `BKEdge` projections `BKEdge.src` / `BKEdge.tgt`:

| Concretised theorem | Delegates to (mg-516f) |
|---|---|
| `prop_72_groundSet` | `prop_72_grounded` |
| `lem_bandwidth_le_four_groundSet` | `lem_bandwidth_le_four` |
| **`lem_bandwidth_le_four_bundled_groundSet`** | `lem_bandwidth_le_four_bundled` |
| `prop_71_groundSet` | `prop_71_grounded` |
| `prop71_prop72_lemBandwidth_groundSet` | `prop71_prop72_lemBandwidth_grounded` |

The **load-bearing piece-2 deliverable** is
`lem_bandwidth_le_four_bundled_groundSet`: it produces a concrete
`L : LayeredWidth3 (richPairs : Finset (α × α))` with
`L.bandwidth ≤ 4`, the cardinality partition, and the
exceptional-mass bound — a concrete object the S7-F bridge
(piece 3) can convert into a `LayeredDecomposition α`.

---

## §3. What stays parametric — and why it is honest, not a gap

The concretised theorems take, as **parameters / hypotheses**:

* `signedWeight : BKEdge α → ℤ` — the S7-A signed-threshold label
  `δ_e`; its concrete content is a Step 1/3 output.
* `path : BKVertex α → List (BKEdge α)` — the S7-C BFS spanning
  tree; concrete content is a Step 7 BFS construction.
* `psrc, ptgt : α × α → BKVertex α`, `posMass : α × α → ℕ` —
  chain-position projections + BK-adjacency mass; Step 1/5 outputs.
* `pairs, richPairs : Finset (α × α)` — the rich-pair finset; a
  Step 5 (R)-branch output.
* `b_n, b_d, c_n, c_d, M₀ : ℕ` — the budget/richness constants;
  Step 5/6 grounded-form outputs (sub-arcs -B, -C).
* `hBud : VarBudgetHyp …`, `hRich : RichnessHyp …` — the
  variational-budget and richness *proofs*; Step 5/6 outputs.

**This is the design, not a shortfall.** The S7-E grounded forms
were *correctly* parametric over exactly this data (mg-516f §"Why
this is not vacuous" — the var-budget + richness hypotheses "are
taken parametrically from upstream Step 5"). Piece 2's job is to
concretise the **carrier types**, not to fabricate the Steps 5–6
**data**. The `Step5/` and `Step6/` directories ship only abstract
cleared-denominator scaffolding — there are **no grounded
constant-extractor forms** in tree (verified: `grep` for
`grounded` / `Richness` / `VarBudget` in `Step5/`, `Step6/` —
nothing exports concrete `c_n`/`b_n`/etc.). Extracting those
constants is sub-arcs mg-S7-Conc-B / -C, which the parent scoping
doc §2.2 + §7.3 already gate on **piece 1**.

Threading the Steps 5–6 outputs as hypotheses is what makes piece 2
**parallelisable with piece 1** (ticket "Parallelizes with P1"):
this file commits the graph structure now; piece 1 later discharges
`hBud` / `hRich`.

---

## §4. Vacuity-discovery audit (Daniel's "7-times" lens)

Per `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks,
applied to the concretised forms:

1. **Satisfiability.** The concretised theorems are pure
   instantiations of the S7-E forms at concrete types; the
   conclusion `∃ L : LayeredWidth3 richPairs, …` is constructed
   explicitly inside the abstract `prop_72` (it builds `L` from
   `richSmallDeltaPairs` / `richLargeDeltaPairs`). Not vacuous.
2. **Discharge-coverage.** This file cites **no** artefact as
   discharging `hBud` / `hRich`. They remain hypotheses of every
   concretised theorem. No over-claim of the kind mg-5c32 made.
3. **Universal-quantifier truthfulness.** The concretised theorems
   quantify *universally* over the data (`signedWeight`, `path`,
   `richPairs`, the constants, `hBud`, `hRich`) and *existentially*
   over `L`. The `∃ L` is witnessed concretely. No false universal
   `∀ α, ∃ L with L.w ≤ 4` is introduced (the dangerous form
   refuted by mg-ac13's 3-disjoint-chains counterexample) — the
   conclusion is conditional on `hBud` / `hRich`, exactly as the
   paper's `prop:72` is conditional on the Step 5/6 budget.

**Verdict:** no 8th vacuity-discovery. The S7-E grounded forms hold
up under concretisation; the cumulative count remains at 7
(mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13, mg-5fbd).

---

## §5. What piece 2 still needs (post-piece-1 follow-on)

The remaining piece-2 work — genuinely blocked on piece 1:

* **mg-S7-Conc-B** — **DONE (mg-8f9c, 2026-05-21).** Piece 1 has
  landed (S5 wave mg-d4bb / mg-be3e; Checkpoint 2 passed mg-496b),
  so the Step 5 grounded forms exist. `c_n, c_d, M₀` extracted in
  `lean/OneThird/Step7/RichnessConstants.lean`: the genuine
  constants are `c_n = 1`, `c_d = 2`, `M₀ = |LP|` — the
  post-activation density `c'_T = c₅⋆/2` of `step5.tex:721-738`.
  The per-pair richness `RichnessHyp` is projected from the **G4**
  grounded form `Step5.fiber_mass_grounded` (per-pair clause), not
  from `thm_step5_grounded`'s aggregate `Step5Richness`. The
  constants project cleanly into the parametric S7-E signature
  (exhibited by `lem_bandwidth_le_four_bundled_of_step5_richness`).
  See `docs/state-S7-Conc-B-Session1.md`.
* **mg-S7-Conc-C** — extract `b_n, b_d` from the Step 6
  `thm:step6` + `cor:pointwise` grounded form. **Needs:** a Step 6
  grounded form exporting concrete budget constants. Not in tree.
* **mg-S7-Conc-D (discharge half)** — construct the concrete
  `hBud : VarBudgetHyp` and `hRich : RichnessHyp` witnesses from
  the -B / -C constants, and invoke
  `lem_bandwidth_le_four_bundled_groundSet` to produce an
  *unconditional* `L_{S7E} : LayeredWidth3 (richPairs α)` with
  `bandwidth ≤ 4` for `α` a minimal γ-counterexample.

**Recommendation.** Dispatch mg-S7-Conc-B / -C / -D-discharge as a
piece-2 follow-on **after piece 1 (Steps 1–6 cascade port) lands**,
per the parent scoping doc §5.2 dispatch order (Phase 3, after
checkpoint 2). The type-concretisation core (this session) unblocks
piece 3 (S7-F bridge) from the type side: piece 3 can be designed
and built against `lem_bandwidth_le_four_bundled_groundSet`'s
concrete signature now, with `hBud` / `hRich` threaded through as
hypotheses until piece 1 discharges them.

---

## §6. Acceptance bars

- [x] `lake build OneThird.Step7.GroundSet` clean (1308/1308 jobs).
- [x] `lake build OneThird` (full root) clean.
- [x] No `sorry` in `GroundSet.lean`.
- [x] No new axioms (`AXIOMS.md` unchanged).
- [x] No new mathlib gaps (the file is pure delegation +
  elementary structure/instance definitions).
- [x] Wired into `OneThird.lean` root
  (`import OneThird.Step7.GroundSet`).
- [x] Concrete carrier types `BKVertex α`, `BKEdge α`, `α × α`
  fixed; every S7-E grounded deliverable re-exported at them.
- [x] Load-bearing `lem_bandwidth_le_four_bundled_groundSet`
  produces a concrete `LayeredWidth3 (richPairs : Finset (α × α))`.
- [x] Skeptical vacuity-discovery audit applied (§4) — no 8th
  discovery.
- [x] Honest scope boundary documented (§0, §3, §5) — sub-arcs
  -B / -C / -D-discharge gated on piece 1.

---

## §7. Cross-reference index

### §7.1. Lean (this work)

* `lean/OneThird/Step7/GroundSet.lean` (NEW) — `BKVertex`,
  `BKEdge`, `BKEdge.bkGraph_adj`, `prop_72_groundSet`,
  `lem_bandwidth_le_four_groundSet`,
  `lem_bandwidth_le_four_bundled_groundSet`, `prop_71_groundSet`,
  `prop71_prop72_lemBandwidth_groundSet`.
* `lean/OneThird.lean` — single-line
  `import OneThird.Step7.GroundSet` added.

### §7.2. Lean (consumed, unmodified)

* `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean` (mg-516f) —
  the parametric S7-E grounded forms re-exported here.
* `lean/OneThird/Step7/Bandwidth.lean` — `BandwidthData`,
  `BandwidthData.ofPotential`, `VarBudgetHyp`, `RichnessHyp`.
* `lean/OneThird/Step7/Assembly.lean` — `LayeredWidth3`,
  `GlobalThresholdDescr`.
* `lean/OneThird/Step7/Potential.lean` — `bfsPotentialData`,
  `BFSTreeExtensionHyp`.
* `lean/OneThird/Mathlib/BKGraph.lean` — `bkGraph`, `BKAdj`,
  `bkGraph_adj`.

### §7.3. Paper

* `step7.tex:1115-1193` — `prop:71`, `prop:72`.
* `step7.tex:1018-1056` + `step7.tex:1015-1018` — `lem:bandwidth`,
  `rem:w0-constant`.
* `step8.tex:1983-2106` — `def:layered` + `lem:layered-from-step7`
  (the piece-3 target consuming this file's output).

### §7.4. Predecessor docs

* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) —
  §2.2 piece 2 spec.
* `docs/state-MA-Sig-Session1.md` (mg-a22b) — refactor signature
  contract.
* `docs/state-S7-E-prop71-prop72-Session1.md` (mg-516f) — the
  parametric S7-E grounded forms.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §3 pitfall #2
  (the three-check skeptical lens applied in §4).

### §7.5. Predecessor work items

mg-d8c7 (Option A' scoping), mg-a22b (MA-Sig), mg-6ab8 (Steps 1-7
scoping), mg-516f (S7-E), mg-d135/1069/9331/4584 (S7-A–D),
mg-5fbd (S7-F bridge audit), **mg-4ce6 (this session)**.

---

## §8. Maintenance contract

This file is the state record for piece 2 (S7-A–E ground-set
concretisation) of the Option A' FULL REFACTOR. Update it in the
same commit as any change that:

* Lands sub-arcs mg-S7-Conc-B / -C / -D-discharge (record the
  Steps 5–6 constant-extraction forms and the unconditional
  `L_{S7E}` construction).
* Changes the `GroundSet.lean` carrier-type choices (`BKEdge`
  representation, `Pair := α × α`).
* Re-exports additional S7 grounded forms at the concrete types.

If piece 3 (S7-F bridge) surfaces a mismatch between
`lem_bandwidth_le_four_bundled_groundSet`'s output shape and what
`lem:layered-from-step7` consumes, record it here and re-scope.
