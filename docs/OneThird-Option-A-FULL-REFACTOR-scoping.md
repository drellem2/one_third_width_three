# OneThird — Option A' FULL REFACTOR scoping

**Owner.** `mg-d8c7` (Daniel directive 2026-05-19T07:13Z verbatim:
*"Sounds like 1/3-2/3 the lean isn't set up right at all for our
proof yet so we need to refactor until it is."*).

**Type.** SCOPING ticket. Paper-and-pencil only. **No Lean code**
delivered here; the only artefacts are this document and the
pre-filed sub-ticket bodies in §7 (recorded as recommendations, not
filed by this polecat).

**Supersedes.** `mg-5fbd` Option (C') RED-STAY-PUT recommendation
(default if Daniel takes no action). Daniel's 07:13Z directive
selects Option (A') FULL REFACTOR instead.

**Builds on.** `mg-6ab8` Steps 1-7 Lean-port scoping (selected
Option B AMBER-NARROW-PILOT, pilot Step 7 alone). The S7-A-E pilot
landed (mg-4584, mg-9331, mg-1069, mg-d135, mg-516f) and the S7-F
bridge audit (mg-5fbd) discovered the architectural obstruction. The
present ticket scopes the *full* repair, not the pilot's narrow
slice.

**Inputs (read first; no facts asserted below without re-grepping the
source).**

- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical proof-tree,
  §3 pitfalls #1-#5.
- `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — the RED 7th
  vacuity discovery + the four §6.1 forward options. Recommendation
  there (Option C') is the status-quo; the 07:13Z directive selects
  Option A' enumerated alongside it.
- `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) — full
  per-step Phase A-E decomposition for the upstream Steps 1-7
  port. §2 paper-side audit, §3 per-step budget, §4 critical path,
  §5 mathlib dependencies, §6 forward action, §7 pre-filed
  sub-tickets. This document **re-uses** mg-6ab8's per-step budgets
  rather than re-deriving them; the marginal scoping here is
  exactly the pieces *beyond* Steps 1-7 alone (architectural
  refactor + ground-set lift + integration).
- `docs/coherence-collapse-case-extraction.md` (mg-ac13) — the
  paper-first case extraction; 3-disjoint-chains counterexample.
- `lean/OneThird/Step8/MainAssembly.lean` — current direct-construction
  call site (the refactor target).
- `lean/OneThird/Step7/Assembly.lean:302-413` — current
  `Step7.LayeredWidth3` packaging on `Pair` space (the lifted-to-α
  target).
- `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean` (mg-516f) —
  S7-E `lem_bandwidth_le_four_bundled`, the load-bearing
  bandwidth ≤ 4 deliverable consumed by the bridge.
- `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`
  structural data (F7a) the bridge consumes for the ground-set lift.
- `lean/OneThird/Step8/LayeredBridges.lean` — `layeredFromBridges`
  placeholder (the current sham-bandwidth bridge; vacuous body).
- `paper/step8.tex:1983-2106` — `def:layered` +
  `lem:layered-from-step7`.
- `paper/step8.tex:531-755` — `thm:main-step8` paper proof; the
  Steps 5-7 cascade dispatch the refactored Lean assembly will
  mirror.

---

## §0. Verdict (top-of-page) — **GREEN-scoping-delivered**

> **⚠ AMENDED (mg-0bd1) → CORRECTED (mg-faf8, 2026-05-20).** The
> piece-3 execution attempt (mg-0bd1) surfaced an **8th vacuity
> discovery**: the MA-Sig §4.2 §E bridge signature was
> structurally unsatisfiable for large α, and this decomposition
> was **missing a 6th piece** — the full Step 8 G4 port
> (`lem:layered-balanced`, statement `step8.tex:2453-2464`, proof
> `3211-3266`). **mg-faf8 has now applied the re-scope:** the
> MA-Sig contract is re-pinned (`docs/state-MA-Sig-Session1.md`
> §4.2 §E/§G, satisfiability-verified in its §10), and **Piece 6
> is recorded below as §2.6** — this is now a **6-piece**
> decomposition. The §0 budget table, §1.3 map, §3 critical
> path/budget, §4.1, and §7 sub-tickets are amended in place to
> match. See `docs/state-S7-F-bridge-Session2.md` §5-§8,
> `docs/state-MA-Sig-Session1.md` §9-§10, and
> `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #6.

**Six pieces** of the Option A' FULL REFACTOR scoped end-to-end
(originally five; **Piece 6 added by mg-faf8** per the mg-0bd1
8th vacuity discovery — see the AMENDED→CORRECTED banner above
and §2.6). **No paper-side gap surfaced** under default-skeptical
re-read; the 8th vacuity hit the *MA-Sig pinned signature shape*
(a contract artefact), not any paper construction — paper
`lem:layered-from-step7` and `lem:layered-balanced` are both
sound. The refactor is **structurally feasible**: every input the
new proof-by-contradiction setup needs is supplied by an
already-scoped piece (Steps 1-6 cascade, S7-A-E grounded forms,
S7-F bridge, full Step 8 G4, `exc_perturb`, `ChainLiftData`).

**Cumulative budget projection (Phase B; see §3.2).** Executive
estimate (post-mg-faf8, including Piece 6): **8.3M-14.6M tokens
cumulative, 37-57 polecat dispatches, 6-7 months calendar** at 1
polecat-per-day cadence. This sits at/just above the `mg-d8c7`
ticket-body envelope ("~7-12M / 5-7 months"); the +0.8M-1.6M
Piece 6 delta is the cost of the mg-0bd1 correction. The
decomposition is:

| Piece | Polecat sessions | Token budget | Source |
|---|---:|---:|---|
| 1. Steps 1-6 cascade Lean port | 22-32 | 5.0M-8.5M | mg-6ab8 §3.2 rows S1-S6 |
| 2. S7-A-E scaffolding → ground-set α concretisation | 3-5 | 0.5M-1.0M | new (§2.2 below) |
| 3. S7-F bridge (`lem:layered-from-step7`) | 4-6 | 1.0M-1.5M | mg-6ab8 §7.1 mg-S7-F + mg-5fbd §6.1 |
| 4. MainAssembly proof-by-contradiction refactor | 4-6 | 0.8M-1.5M | new (§2.4 below) |
| 5. Integration: close `MainAssembly.lean:265` sorry + retire `Step7.LayeredWidth3` paper-axiom | 1-2 | 0.2M-0.5M | new (§2.5 below) |
| 6. Full Step 8 G4 port (`lem_layered_balanced_full`) | 3-6 | 0.8M-1.6M | new (§2.6 below) — added mg-faf8 per mg-0bd1 |
| **Total** | **37-57** | **8.3M-14.6M** | (mid 10.3M / 6-7 months) |

The largest single contributor remains **Steps 1-6 cascade port**
(piece 1) at 5.0M-8.5M / 22-32 sessions, dominated by Step 7's
upstream-dependency satisfaction (mg-6ab8 §3.2 has Step 7 alone at
2.0M-3.0M; that work is folded into pieces 2 + 3 here because the
S7-A-E pilot has *already landed*, so what remains is concretisation
+ bridge). Pieces 4 + 5 are the **load-bearing architectural pieces**
(the "set it up right" content of the 07:13Z directive), at 1.0M-2.0M
total — a small fraction of the cumulative budget but the **only
pieces that cannot be parallelised** with the upstream cascade
port. **Piece 6** (full Step 8 G4) is the opposite: it has **no
upstream cascade dependency** (consumes only a
`LayeredDecomposition` with `L.w ≤ 4`; its inductive machinery
`lem_cut` / `windowLocalization` / `lem_layered_reduction` is
already in tree), so it parallelises freely with piece 1 and is
*not* on the critical path (§3.1).

**Risk watchlist (Phase D + §6).** Three new risks beyond mg-6ab8 §8:

1. **Vacuity-discovery on the architectural refactor itself.** The
   proof-by-contradiction translation of `width3_one_third_two_thirds_assembled`
   may surface a gap between the paper's "minimal γ-counterexample
   in the (R)+(coherent) regime" hypotheses and the Lean signature
   the refactor exposes. **Mitigation:** Phase-A audit before
   coding (analog of mg-5fbd § Phase D Checkpoint 3 audit) on the
   refactor signature alone — confirm the threaded contradiction
   hypothesis suffices to derive Step 5(R) richness or Step 5(C)
   collapse before any line of Lean is written.
2. **Hypothesis A (arithmetic richness, `step8.tex:511-525`) interaction
   with the refactor.** Paper's `thm:main-step8` is *conditional*
   on Hypothesis A. The Lean refactor must thread this hypothesis
   correctly — either as an explicit input to the headline (most
   honest) or as a project axiom analog of `brightwell_sharp_centred`.
   **Mitigation:** decide on the threading at the refactor's
   signature design step (piece 4 sub-arc M-A) before downstream
   work.
3. **Sub-split overhead exceeds 1.5× multiplier on pieces 1 + 3.**
   mg-6ab8's empirical sub-split rate was 1.5×; the Steps 1-6 sub-arc
   may run higher because no single-step pilot has yet landed.
   **Mitigation:** insert a hold-the-line checkpoint after pieces
   1.S1-S2 land (analog of mg-6ab8 §4.3 Checkpoint 1); re-scope if
   the empirical rate exceeds 2×.

**Forward action recommendation (Phase D; see §5).** **DO NOT** file
the execution sub-tickets without explicit Daniel sign-off
post-this-scoping. Per ticket constraint *"No premature execution
commitment without Daniel sign-off post-scoping"*, §7 of this
document records the proposed sub-ticket bodies as **recommendations
only**; this polecat does NOT call `mg new` for any of them.

Recommended dispatch order on approval (§5.2): pieces 4 (refactor
signature) → 1 (Steps 1-6 cascade) → 2 (S7-A-E concretisation) → 3
(S7-F bridge) → 5 (integration). Piece 4 first is **counter-intuitive
but correct**: the refactor's signature determines what shape the
downstream cascade port must deliver, and discovering this *after*
months of cascade work would be catastrophic re-scoping. Pre-flight
the architectural signature before scaling out the cascade.

---

## §1. Context — the post-mg-5fbd state

### §1.1. What is broken (the 07:13Z directive)

The headline `OneThird.width3_one_third_two_thirds`
(`MainTheorem.lean:56`) descends through:

```
MainTheorem.lean:56 width3_one_third_two_thirds
  └── MainAssembly.lean:353 width3_one_third_two_thirds_assembled
        └── MainAssembly.lean:308 mainAssembly  (DIRECT construction)
              └── I.caseC = mainTheoremInputsOf.caseC_canonicalLayered
                    └── MainAssembly.lean:236-267 caseC_canonicalLayered
                          ├── L := canonicalLayered α       (K = w = |α|)
                          ├── hInj, hKw, hCardw, hNonempty  (caps 1-4, ✓)
                          └── hLw : L.w ≤ 4 := by sorry     (cap 5, ✗)
```

The `sorry` at `MainAssembly.lean:265` (cap 5) is what `mg-5fbd`
Session 1 found to be **architecturally unclosable** under the
current direct-construction setup. Three independent obstructions
(mg-5fbd §2.2-§2.4; PROOF-STRUCTURE-ONBOARDING §3 pitfall #5):

1. **Five-cap unsatisfiability for `|α| ≥ 11`.** Caps 1+4 force
   singleton bands (`L.K = |α|`); caps 2+5 force `L.K ≤ 10`.
   No `L` satisfies all caps for `|α| ≥ 11`, irrespective of
   construction.
2. **Five-cap unsatisfiability for specific `|α| ≤ 10` α.**
   `α = 3 disjoint chains of length 3` (width 3, non-chain,
   `|α| = 9`) admits no satisfying `L` — cap 1 forces singletons,
   cap 5 forces `L.w = 4`, but (L2) then forces 10 pairs at
   band-distance ≥ 5 to be `<_P`-comparable while `P` has only
   9 comparable pairs total.
3. **Paper's `lem:layered-from-step7` is not free-standing on
   width-3 non-chain α.** It requires **either** Step 5(C)
   collapse data **or** Step 7(ii) globalization data
   (`step8.tex:2009-2027`) — both *cascade outputs* gated on
   α being a **minimal γ-counterexample in the (R)+(coherent)
   regime**. The current Lean call site offers neither.

The Lean architecture in `width3_one_third_two_thirds_assembled`
is **direct construction**: given `(α, hP, hNonChain, hC3)` it
builds the balanced pair directly. There is **no contradiction
hypothesis in scope** at the call site. There is **no Dilworth
chain data, no chain potential, no Steps 1-7 cascade output**.
These cannot be invented; the paper bridge fundamentally requires
them. Hence the 07:13Z directive: *"the lean isn't set up right at
all for our proof yet so we need to refactor until it is."*

### §1.2. What the paper actually does

Paper `thm:main-step8` (`step8.tex:531-552`) is the
proof-by-contradiction template:

> Assume Hypothesis~\ref{hyp:arith}. Then every finite width-3 poset
> that is not a chain has a balanced pair.

The proof (`step8.tex:553-755`) proceeds:

1. **Suppose for contradiction** `P = (X, ≤_P)` is a width-3 non-chain
   poset with no balanced pair (a *γ-counterexample*).
2. **Pick a minimal γ-counterexample** (minimal `|X|`). This is
   indecomposable (`rem:decomp-reduction`, F7).
3. **Theorem E (`step8.tex:36`):** the BK conductance `Φ(S)` on
   the level cut `S` of a minimal γ-counterexample is `< η =
   O_T(γ)` (the low-conductance hypothesis fed into Steps 1-7).
4. **Steps 1-7 cascade with low-conductance input:** Step 5
   dichotomy gives **either** (R) richness or (C) collapse;
   `prop_71+prop_72+lem_bandwidth` of `step7.tex` upgrades these
   to layered width-3 on `(1-o(1))` of `LE(P)` with bandwidth
   `≤ 4`.
5. **`lem:layered-from-step7` (`step8.tex:2009-2089`):** lifts the
   `(1-o(1))`-mass layering into an exact `def:layered` on
   `P|_{X \setminus X^{exc}}`, with `|X^{exc}| ≤ C_{exc}(T) = O_T(1)`.
6. **`lem:layered-balanced` (`step8.tex:2453`):** the layered
   subposet has a balanced pair (by the Lean-side strong induction).
7. **F6b `exc_perturb` (`step8.tex:1376-1396`):** lift
   `HasBalancedPair (X \setminus X^{exc})` back to `HasBalancedPair X`
   with perturbation `O(C_{exc}/|X|) = o(1)`.
8. **Contradiction** with the assumption that `P` has no balanced
   pair (step 1).

The Lean refactor needs to mirror this **proof shape**, not the
current direct-construction shape. The six pieces of mg-d8c7
(five original + Piece 6 added mg-faf8) are the engineering
content of that mirroring.

### §1.3. The six pieces — quick map

| Piece | Engineering content | Maps to paper step |
|---|---|---|
| 1 | Lean port of Steps 1-6 grounded forms | `step{1..6}.tex` proofs |
| 2 | Concretise S7-A-E grounded forms on ground-set α | bridges paper Step 6 ↔ S7-A-E grounded form inputs |
| 3 | S7-F bridge: `prop:72` output → `LayeredDecomposition α` on `X∖X^exc` (emits only `\|X^exc\| ≤ C_exc T`, band-nonempty, `L.w ≤ 4`) | `lem:layered-from-step7` (`step8.tex:2009-2089`) |
| 4 | `width3_one_third_two_thirds_assembled` proof-by-contradiction refactor | `thm:main-step8` proof setup |
| 5 | Integration: close `MainAssembly.lean:265` sorry, retire `Step7.LayeredWidth3` paper-axiom | `thm:main-step8` final assembly |
| 6 | Full Step 8 G4 port: `lem_layered_balanced_full` — strong induction on `\|β\|`, consumes only `L.w ≤ 4` | `lem:layered-balanced` (`step8.tex:2453-2464` / proof `3211-3266`) |

Pieces 1 + 2 + 3 are *bottom-up* (upstream cascade ports). Piece 4
is *top-down* (signature design + contradiction threading). Piece 5
is the *integration*. **Piece 6** (added mg-faf8) is *stand-alone*:
the full Step 8 G4, consuming only a `LayeredDecomposition` with
`L.w ≤ 4` — no upstream cascade dependency. Logically it sits
between piece 3 (the S7-F bridge, which produces the layered
decomposition) and piece 4-body (which lifts the resulting
balanced pair back to `α`): piece 3 → **piece 6** → piece 4-body.
But because it has no cascade dependency it can be **dispatched
early, in parallel with piece 1**, and is *not* on the critical
path. The dependency order on the critical path is
4-signature → 1 → 2 → 3 → 4-body → 5 (see §3.1), with piece 6
running off to the side.

---

## §2. Phase A — per-piece refactor scope

For each piece: substantive Lean content, polecat budget, sub-arcs,
upstream/downstream dependencies, hold-the-line risks.

### §2.1. Piece 1 — Steps 1-6 cascade Lean port

**Substantive content.** Faithful Lean port of `step{1..6}.tex`'s
grounded statements + proofs, replacing the present
cleared-denominator abstract scaffolding at
`lean/OneThird/Step{1..6}/` with **groundings on concrete BK-graph
data**. Each step's deliverables are unchanged from mg-6ab8 §2.1-2.6:

- **S1.** `thm:interface` four parts (coordinate map, raw-fiber
  decomposition, BK move classification, bad-set bound) +
  `cor:overlap` (2×2 commuting squares) + `cor:triple-overlap`
  (Z³ commuting cube).
- **S2.** `lem:weak-grid` planar stability + `prop:per-fiber`
  staircase approximation.
- **S3.** `lem:local-sign` orientation + coherence definition.
- **S4.** `thm:step4` two-interface incompatibility (BK boundary
  proportional to incoherent overlap mass).
- **S5.** G1-G5 of `step5.tex` (endpoint-mono, convex-overlap,
  decomp-selection, fiber-mass, global-layering) + the rich-or-collapse
  dichotomy `thm:step5`.
- **S6.** G6-G10 + `thm:step6` (the dichotomy from low conductance:
  expansion contradicts conductance, or pointwise coherence is
  uniform).

**Polecat budget.** Inherit mg-6ab8 §3.2 row-by-row: 22-32 polecat
sessions, 5.0M-8.5M tokens. The mid-estimate is **27 sessions /
6.5M tokens**.

**Sub-arc decomposition** (from mg-6ab8 §7.2 + §7.3):

- Wave 1 (parallel): mg-S1-A through mg-S1-D (4 tickets), mg-S5-A
  through mg-S5-E (5 tickets), mg-MathlibCheeger sub-arc (1-2
  tickets). ~9-11 tickets parallel.
- Wave 2 (sequential after S2 mathlib): mg-S2-A, mg-S2-B, mg-S3
  (~3-4 tickets).
- Wave 3 (sequential): mg-S4-A, mg-S4-B, mg-S4-C (~3 tickets).
- Wave 4 (sequential): mg-S6-A, mg-S6-B (~2-3 tickets).
- Plus inter-step QA scoping (Phase D checkpoints): mg-S1234-QA,
  mg-S6-QA (~2 tickets at 250k each).

**Critical-path waves.** S1 → S2 → S4 → S6 is strictly sequential
because each consumes the prior. S3 can fold inside the S2-S4 gap
(parallel with S4-A). S5 can run in parallel with S1-S4 entirely
since it consumes only S1's `thm:interface` outputs and the BK-graph
foundation.

**Upstream dependencies.** Already-in-tree mathlib infrastructure:
`Mathlib/BKGraph.lean`, `Mathlib/LinearExtension/*.lean`,
`Mathlib/Grid2D.lean` (partial), `Mathlib/DirichletForm.lean`,
`Mathlib/Poset/Dilworth.lean` (partial — Frankl-mathlib-copy-and-tweak
pattern may apply; see §4.2 below).

**New mathlib infrastructure.**

> **⚠ AMENDED (mg-dc4c, 2026-05-20).** The original table here
> inherited six rows from mg-6ab8 §5.2 with a 3.4M-5.9M subtotal. The
> mg-dc4c block-and-report audit verified the tree and found the
> **"Cheeger inequality on `bkGraph α`" row (1.5M-2.5M) is RETIRED**:
> the proof never consumes the full Cheeger inequality / spectral gap
> (MATHLIB_GAPS.md §D3/§D5/§4/§6 — the mg-893b Theorem-E resolution
> replaced the spectral argument with elementary averaging). The
> conductance↔boundary translation the cascade *does* use is already
> in tree, complete: `DirichletForm.lean` (`cheeger_indicator`),
> `BKGraph.lean`, `SimpleGraph/EdgeBoundary.lean`. mg-6ab8 §5 line 749
> itself phrased the requirement as "Cheeger/spectral-gap **or** the
> equivalent conductance↔boundary on finite graphs" — that equivalent
> is `cheeger_indicator`, done. The "Order-convex region API for `Z²`"
> row is likewise **SHIPPED** (`Grid2D.lean` `IsOrdConvex`). The
> revised subtotal is **0.9M-1.7M** (the remaining three rows).

| Prerequisite | Used by | Effort | Upstreamable |
|---|---|---|---|
| ~~Cheeger inequality on `bkGraph α` (weighted finite)~~ | ~~S2, S4, S6~~ | **RETIRED** — `cheeger_indicator` already in tree; full Cheeger/spectral-gap not needed (mg-dc4c) | — |
| Weak grid isoperimetric stability (planar) — quantitative F6 | S2 | 0.4M-0.7M (mg-dc4c re-scoped deliverable) | Yes |
| ~~Order-convex region API for `Z²`~~ | ~~S1, S2~~ | **SHIPPED** — `Grid2D.IsOrdConvex` (mg-dc4c) | — |
| Chain-removal subtype lift (extend `OrdinalDecomp.hasBalancedPair_lift`) | piece 3 (not piece 1) | 0.5M-1.0M | No (internal) |
| Discrete-Hodge cocycle integration | piece 2 (S7-C grounded form already lands this in S7-A-E pilot — already done) | (already paid) | Maybe |
| Markov-style giant-component for weighted graphs | piece 2 (similarly) | (already paid) | Yes |

**Downstream consumers.** Piece 2 (S7-A-E concretisation) consumes
S5 + S6 outputs directly. Piece 3 (S7-F bridge) consumes S5(C) and
S6+S7 cascade outputs.

**Hold-the-line risks.**

1. **Checkpoint 1 (after S1-S4 land, ~5-7 weeks):** does S1's
   `thm:interface` Lean port surface a paper-side rigour gap not
   caught in mg-6ab8 §2.1's audit? If yes, re-scope.
2. **Checkpoint 2 (after S6 lands, ~8-10 weeks):** is the abstract
   Step 6 cleared-denominator scaffold (already in tree, 1945 LoC,
   the most-built-out of S1-S6) actually consumable by grounded
   S2+S4+S5 outputs? If not, surface gap before piece 2.
3. **Mathlib Cheeger gap.** mg-6ab8 §8 row 2 estimated 60%
   probability that Cheeger inequality requires its own substantial
   sub-arc (+1.5M-2.5M). This is the single largest variance term
   in piece 1.

**Tag.** rigorous-but-substantial (same as mg-6ab8). No new
vacuity-discovery surfaced under default-skeptical re-audit; the
paper-side is unchanged from mg-6ab8 §2.

### §2.2. Piece 2 — S7-A-E scaffolding → ground-set α concretisation

**Substantive content.** The S7-A-E pilot (mg-4584/9331/1069/d135/516f,
landed) produces *grounded forms* on **parametric upstream hypotheses**
(the abstract `Edge / Vertex / Pair / src / tgt / path /
signedWeight / posMass / b_n / b_d / c_n / c_d / M₀` data + Step 5
var-budget + richness witnesses, per `Step7/Prop71_Prop72_LemBandwidth.lean`
`lem_bandwidth_le_four_bundled` signature). What S7-A-E **does not
do** is supply that concrete data **for the ground-set α of the
headline**.

Piece 2 closes that concretisation gap. Specifically: given α a
width-3 finite non-chain poset (the headline's input) plus Steps 1-6
cascade outputs (piece 1's deliverable), construct on the BK-graph
of α:

1. **`BKEdge α`, `BKVertex α`** — concrete graph data on
   `LinearExt α`.
2. **`Pair := A × B`** — the rich-pair space derived from
   Step 5's Dilworth decomposition `X = A ⊔ B ⊔ C`.
3. **`src, tgt, signedWeight, edgeWeight, path`** — wired to
   `bfsSumPot` / `bfsPotentialData` of S7-C (existing) on the
   actual BK-graph.
4. **`psrc, ptgt, posMass`** — rich-pair-to-vertex maps.
5. **`b_n, b_d, c_n, c_d, M₀`** — concrete constants from Steps
   5-6 outputs (`c_n, c_d` from Step 5 richness; `b_n, b_d` from
   Step 6 conductance bookkeeping; `M₀ := |LE(P)|`).
6. **`hSub, hBud, hRich`** — concrete `VarBudgetHyp` and
   `RichnessHyp` witnesses derived from the Step 5(R) richness
   conclusion + Step 6 second-moment outputs.

The output is a *concrete invocation* of
`lem_bandwidth_le_four_bundled` on α-specific data, producing
**`L_{S7E} : Step7.LayeredWidth3 (richPairs α)`** with
`L_{S7E}.bandwidth ≤ 4` for α arising as a minimal
γ-counterexample (the contradiction-hypothesis-induced cascade
state from piece 4).

**Polecat budget.** 3-5 sessions, **0.5M-1.0M tokens**. The work is
concrete-instantiation engineering, not new theorem proving — the
grounded forms exist, only their α-side wiring is missing.

**Sub-arc decomposition.**

- **mg-S7-Conc-A** (concrete BK-graph data): wire `Edge / Vertex`
  to `LinearExt α / BKAdj`; `path` from `bkGraph_connected`. ~1
  session, 200k.
- **mg-S7-Conc-B** (Step 5-derived constants): extract `c_n, c_d,
  M₀` from Step 5's `thm:step5` (R)-branch concrete output. ~1
  session, 200k.
- **mg-S7-Conc-C** (Step 6-derived constants): extract `b_n, b_d`
  from Step 6's `thm:step6` + `cor:pointwise`. ~1 session, 200k.
- **mg-S7-Conc-D** (assembly): invoke `lem_bandwidth_le_four_bundled`
  with the wired data; produce `L_{S7E}`. ~1-2 sessions, 200k-400k.

**Upstream dependencies.** Piece 1 (Steps 5 + 6 grounded). The
S7-A-E grounded forms themselves are already landed and unchanged
(mg-4584 et seq.).

**Downstream consumers.** Piece 3 (S7-F bridge) consumes `L_{S7E}`
as its input.

**Hold-the-line risks.**

1. **Constant-extraction mismatch.** Step 5's `c_n / c_d` and
   Step 6's `b_n / b_d` may not project cleanly into the
   parametric `lem_bandwidth_le_four_bundled` signature; some
   adapter algebra may be needed. Probability ~25%, magnitude
   +200k-400k.
2. **Pair-space definition.** `Pair := A × B` chooses one of three
   ordered triples (Step 5 uses (A,B|C), (A,C|B), (B,C|A)). The
   bridge needs a uniform choice that matches `lem:layered-from-step7`'s
   convention. Probability ~15%, magnitude +100k-200k (resolution
   is paper §sec:formal-step7 reading + alignment).

**Tag.** rigorous-but-narrow. Concrete-instantiation engineering on
top of an already-grounded abstract scaffold.

### §2.3. Piece 3 — S7-F bridge (`lem:layered-from-step7`)

> **⚠ AMENDED (mg-faf8).** Per the mg-0bd1 8th vacuity discovery,
> piece 3's bridge **must not** emit the five `Case3Witness` caps
> — that conclusion shape is unsatisfiable for large α. The
> bridge emits only **three** caps: `|X^exc| ≤ C_exc T`,
> band-nonempty, and `L.w ≤ 4` (MA-Sig §4.2 §E, re-pinned;
> `docs/state-MA-Sig-Session1.md` §10). Its downstream consumer
> is **Piece 6** (`lem_layered_balanced_full`, §2.6), **not** the
> bounded `lem_layered_balanced`. The §2.3 text below predates
> the re-pin: read "the input shape `lem_layered_balanced`
> consumes" as "the input shape **Piece 6** consumes", and ignore
> any implication that the bridge transcribes `Case3Witness`'s
> five caps.

**Substantive content.** Lean port of the paper's
`lem:layered-from-step7` (`step8.tex:2009-2089`): the *structural
ground-set lift* from "layered on the Pair space `(1-o(1))`-mass"
(piece 2's `L_{S7E}`) to "exact `def:layered` on the ground set
`X \setminus X^{exc}`" (the input shape Piece 6 — re-pinned
mg-faf8, was `lem_layered_balanced` — consumes).

Concretely, given:

- α a width-3 non-chain poset arising as a minimal γ-counterexample
  (the proof-by-contradiction state from piece 4),
- **Dilworth decomposition** `X = A ⊔ B ⊔ C` (from `Mathlib/Poset/Dilworth.lean`),
- **Either** Step 5(C) collapse data (`w_{coll}(T) = O_T(1)`) **or**
  Step 7(ii) globalization data (potential `a : X → ℝ`, threshold
  `c ∈ ℝ`, bandwidth `K_{bw} = K(T) ≤ 4`) — from piece 2's
  `L_{S7E}` together with piece 1's S5(C)/S7(ii) cascade outputs,
- `ChainLiftData α` (F7a, already in tree at
  `ChainPotentials.lean:328`, mg-7b26),
- `exc_perturb` (F6b, already in tree at `ExcPerturb.lean:351`,
  mg-7496),

construct:

1. **The exceptional set `X^{exc}`**
   (`step8.tex:2027-2055`):
   `X^{exc} := X^{exc}_{mono} ∪ X^{exc}_{band} ∪ X^{exc}_{sync}`
   with `|X^{exc}| ≤ C_{exc}(T) = O_T(1)` (paper item (i)).
2. **The synchronization maps `f_{AB}, f_{AC}, f_{BC}`** wherever
   defined (paper §sec:layered).
3. **The band assembly** `L_k := ⋃ \{chain elts whose synchronized
   image lies near level k\}` (`step8.tex:2070-2089`).
4. **The `LayeredDecomposition (X \setminus X^{exc})` witness** with
   `L.K ≥ (|X| − C_{exc}(T))/3 ≥ |X|/6` and `L.w = K_{bw} + 2 ≤ 4`
   (paper item (ii)).
5. **The perturbation lift** via `exc_perturb`: transfer
   `HasBalancedPair (X \setminus X^{exc})` to `HasBalancedPair X`
   with error `2·C_{exc}(T)/(|X| − C_{exc}(T) + 1) = o(1)` (paper
   item (iii)).

Mathlib gap: **chain-removal subtype lift** — extend
`OrdinalDecomp.hasBalancedPair_lift`
(`Mathlib/LinearExtension/Subtype.lean:1152`, currently scoped at
ordinal-sum decompositions) to the "delete `O_T(1)` exceptional
elements" variant. This is mg-6ab8 §5.2 row 4 (0.5M-1.0M); pieces
of the perturbation argument already in tree (`OneElemPerturb.lean`,
`ExcPerturb.lean`).

**Polecat budget.** 4-6 sessions, **1.0M-1.5M tokens** (mg-6ab8 §7.1
mg-S7-F + mg-5fbd §6.1 Option A' sub-arc 2). The sub-split risk on
this piece is the highest of the five (mg-6ab8 §3.3 row 5: 20%
probability of 7th vacuity-discovery at bridge construction).

**Sub-arc decomposition.**

- **mg-S7-F-A (exceptional-set construction):** define
  `X^{exc}_{mono}, X^{exc}_{band}, X^{exc}_{sync}` as `Finset α`
  and prove `|X^{exc}| ≤ C_{exc}(T) = O_T(1)`. ~1-2 sessions,
  250k-400k.
- **mg-S7-F-B (synchronization maps):** define `f_{AB}, f_{AC},
  f_{BC}` on `X \setminus X^{exc}` with monotonicity. ~1 session,
  250k.
- **mg-S7-F-C (band assembly):** construct
  `LayeredDecomposition (X \setminus X^{exc})` with `L.w ≤ 4`.
  ~1-2 sessions, 250k-400k. (The (L1)-(L4) verifications go here.)
- **mg-S7-F-D (chain-removal subtype lift):** extend
  `OrdinalDecomp.hasBalancedPair_lift` to the `exc_perturb`-driven
  exceptional-set lift. ~1-2 sessions, 250k-500k.
- **mg-S7-F-Z (integration + QA):** wire mg-S7-F-A..D together;
  produce `lem_layered_from_step7 : ∀ minimal-γ-cex α, ∃ L : LayeredDecomposition α-restricted-to-Xc, L.w ≤ 4 ∧ HasBalancedPair α-restricted → HasBalancedPair α`. ~1 session,
  200k-300k.

**Upstream dependencies.** Pieces 1 (S5(C) and S7(ii) cascade
outputs) + 2 (`L_{S7E}`). `ChainLiftData α` and `exc_perturb`
already in tree.

**Downstream consumers.** Piece 4 (refactor body) consumes the
bridge to derive the contradiction's `HasBalancedPair α`.

**Hold-the-line risks.**

1. **Mandatory hold-the-line audit** (mg-6ab8 §4.3 Checkpoint 3 +
   mg-5fbd §1) **before mg-S7-F-A starts:** does piece 2's
   `L_{S7E}` deliver the inputs the bridge actually consumes
   (synchronization maps' definedness, `o(1)`-mass non-monotonic
   set, etc.)? If not, surface and re-scope piece 2 before piece 3.
2. **Chain-tail orphans in `X^{exc}_{sync}`.** The paper says
   `f_{AB}` may be undefined at chain tails (`step8.tex:2050-2055`)
   and absorbs these into `X^{exc}_{sync}`. The Lean port has to
   make the "undefined" case decidable and the `|X^{exc}_{sync}| ≤
   K_{bw}` bound explicit. Probability of complication ~20%,
   magnitude +200k-400k.
3. **The L2 (`x ∈ L_i, y ∈ L_j, i < j − w ⇒ x <_P y`) verification.**
   This is where the 3-disjoint-chains-of-3 counterexample bites
   under the *old* call-site setup; under piece 4's
   proof-by-contradiction setup the *cascade outputs* supply the
   needed coherence, so L2 follows from S7(ii). But the verification
   threads the cascade hypotheses through cleanly is the most
   fragile bookkeeping step. Probability ~25%, magnitude
   +300k-500k.

**Tag.** rigorous-but-substantial. The single highest-variance
piece in the refactor.

### §2.4. Piece 4 — `MainAssembly.lean` proof-by-contradiction refactor

**Substantive content.** The architectural piece. Rewrite the call
chain `MainTheorem.lean → MainAssembly.lean →
caseC_canonicalLayered` from **direct construction** to
**proof by contradiction**:

- Current shape (`MainAssembly.lean:353`):
  ```lean
  theorem width3_one_third_two_thirds_assembled
      (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
      (hC3 : Step8.Case3Witness.{u}) : HasBalancedPair α := by
    by_cases hcard : Fintype.card α ≤ 1
    · …
    have h2 : 2 ≤ Fintype.card α := by omega
    exact mainAssembly 1 3 h2 hP hNonChain
      (mainTheoremInputsOf 1 3 h2 hNonChain hP hC3)
  ```

- Target shape (paper `thm:main-step8` proof, `step8.tex:553-755`):
  ```lean
  theorem width3_one_third_two_thirds_assembled
      (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
      (hC3 : Step8.Case3Witness.{u})
      (hArith : HypothesisArithmetic)   -- new: paper's hyp:arith
      : HasBalancedPair α := by
    by_contra hNoBP                                 -- (1) contradiction
    -- (2) Pick a minimal γ-counterexample
    obtain ⟨α', _instances, hP', hNonChain', hNoBP', hMin⟩ :=
      pickMinimalCounterexample α hP hNonChain hNoBP
    -- (3) Theorem E: low BK conductance on level cut
    have hLowCond : LowConductanceOn (bkGraph α') (levelCut α') :=
      theoremE hArith hP' hMin hNoBP'
    -- (4) Steps 1-7 cascade: rich-or-collapse + threshold-of-potential
    have hCascade : Step5R α' ∨ Step5C α' :=
      stepsOneToSevenCascade hP' hLowCond hMin
    -- (5) lem:layered-from-step7  [re-pinned mg-faf8: 3 caps]
    obtain ⟨Xexc, L, hXexc, hNonempty, hLw⟩ :=
      lem_layered_from_step7 hP' hCascade
    -- (6) PIECE 6 — full Step 8 G4 — on the subposet
    have hBP' : HasBalancedPair (α' \ Xexc) :=
      lem_layered_balanced_full L _ _ _ hLw
    -- (7) exc_perturb lift to full α'
    have hBP'' : HasBalancedPair α' :=
      excPerturbLift hBP' Xexc.card_le_C
    -- (8) Contradiction with minimal counterexample
    exact hNoBP' hBP''
  ```

The architectural deltas:

1. **Add `hArith : HypothesisArithmetic`** as an input — paper's
   `hyp:arith` (`step8.tex:511-525`) becomes a Lean hypothesis or
   project axiom (decided at sub-arc M-A signature design).
2. **Open with `by_contra hNoBP`** to introduce
   `hNoBP : ¬ HasBalancedPair α`.
3. **Pick a minimal counterexample** via
   `Nat.find` or `Finset.min'` over `Fintype.card α` (mathlib has
   minimal-element machinery; this is the `rem:decomp-reduction`
   F7 packaging).
4. **Wire Theorem E** as an explicit lemma producing low conductance
   on a level cut, consuming the minimal-counterexample + `hNoBP'`
   hypotheses (this is `step8.tex:36-181`; partially scaffolded in
   tree at `Step8/TheoremE.lean`).
5. **Wire the Steps 1-7 cascade** via piece 1's deliverables —
   `step_one_to_seven_cascade` consumes low-conductance + minimality
   and produces either Step 5(R) richness or Step 5(C) collapse
   data.
6. **Wire `lem_layered_from_step7`** (piece 3) on the cascade output
   to produce `(X^{exc}, L : LayeredDecomposition (α' \ X^{exc}),
   |X^exc| ≤ C_exc T, band-nonempty, hLw : L.w ≤ 4)` — **re-pinned
   mg-faf8: three caps, not five.**
7. **Apply `lem_layered_balanced_full`** (**PIECE 6** — full Step 8
   G4, §2.6; **not yet in tree**, NOT the bounded
   `lem_layered_balanced`) on the subposet `α' \ X^{exc}`,
   consuming only `hLw : L.w ≤ 4`.
8. **Lift via `exc_perturb`** (already in tree, `ExcPerturb.lean:351`)
   to `HasBalancedPair α'`.
9. **Contradict** the minimal-counterexample assumption.

`mainAssembly` and `mainTheoremInputsOf` are **deleted** in their
current shapes (the `step5_choice` Bool collapse, the
`caseC_canonicalLayered` placeholder, the `MainTheoremInputs`
bundle); their replacements are inlined into the new
`width3_one_third_two_thirds_assembled` body or factored into
genuine cascade-output bundles.

**Polecat budget.** 4-6 sessions, **0.8M-1.5M tokens**.

**Sub-arc decomposition.**

- **mg-MA-Sig (signature design + Hypothesis A threading).** Decide
  whether `hyp:arith` is a Lean hypothesis on the headline or a
  project axiom. Fix the signature of
  `width3_one_third_two_thirds_assembled`,
  `pickMinimalCounterexample`, `theoremE`,
  `stepsOneToSevenCascade`, `lem_layered_from_step7`, and
  `excPerturbLift`. Phase-A audit analog of mg-5fbd. ~1 session,
  200k-300k. **Pre-flight before all other refactor work.**
- **mg-MA-MinCex (minimal-counterexample picker).** Build
  `pickMinimalCounterexample` using `Nat.find` over
  `Fintype.card`. Prove minimality is preserved under
  width-3-non-chain-no-BP descent. ~1 session, 200k-300k.
- **mg-MA-ThmE (Theorem E wiring).** Wire the existing
  `Step8/TheoremE.lean` scaffold (or extend it) to produce
  `LowConductanceOn (bkGraph α) (levelCut α)` from
  `(¬ HasBalancedPair α) ∧ minimal counterexample`. ~1-2 sessions,
  200k-500k.
- **mg-MA-Cascade (Steps 1-7 cascade wiring).** Build
  `stepsOneToSevenCascade : Step5R α ∨ Step5C α` consuming
  `LowConductanceOn`. Calls into piece 1's outputs at S5 + S6 +
  piece 2's `L_{S7E}`. ~1 session, 200k-300k. (This sub-arc is
  "wiring" not "new mathematical content" — it pulls existing
  cascade pieces together.)
- **mg-MA-Body (the new `width3_one_third_two_thirds_assembled`).**
  Replace the existing body with the proof-by-contradiction shape;
  delete `mainAssembly`, `mainTheoremInputsOf`,
  `caseC_canonicalLayered`. Apply pieces 1-3's deliverables. ~1
  session, 200k-300k.

**Upstream dependencies.** The signature design (mg-MA-Sig) has
**no upstream dependencies** — it should be the **first sub-arc
dispatched** in the entire refactor. The body (mg-MA-Body) depends
on pieces 1, 2, 3 having landed.

**Downstream consumers.** Piece 5 (integration). The headline's
external API (`OneThird.width3_one_third_two_thirds`) is the only
downstream consumer; the new `hyp:arith` parameter (if chosen over
the project-axiom alternative) propagates one level up.

**Hold-the-line risks.**

1. **Hypothesis A threading is a fork.** Lean option A: thread
   `hyp:arith` as an explicit parameter on the headline ⇒ the
   `OneThird.width3_one_third_two_thirds` signature changes
   externally. Lean option B: declare `hyp:arith` as a project
   axiom in `AXIOMS.md` ⇒ headline signature unchanged but axiom
   count grows. **mg-MA-Sig must decide before mg-MA-Body
   starts.**
2. **Minimal-counterexample picker may surface
   `inducedCex`-flavored hypotheses (`step8.tex:rem:decomp-reduction`,
   F7).** Paper says minimal γ-counterexample is indecomposable;
   Lean port has to prove indecomposability is preserved under
   the descent. Probability ~20%, magnitude +200k-400k.
3. **`Theorem E` Lean scaffolding may be vacuous.** The current
   `Step8/TheoremE.lean` is partial scaffold; if its body is a
   marker (analog of `mainAssembly`'s `step5_choice` Bool
   collapse, M tag in PROOF-STRUCTURE-ONBOARDING §2), grounding
   it on the BK-graph foundation may be its own substantial
   sub-arc (analog of `step8.tex:36-181` Lean port). Probability
   ~30%, magnitude +500k-800k. **Audit at mg-MA-Sig signature
   design.**

**Tag.** rigorous-but-substantial. The architectural delta is the
"set up right" content of the 07:13Z directive; without it, pieces
1-3 are wired into nothing.

### §2.5. Piece 5 — Integration: close `MainAssembly.lean:265` sorry, retire `Step7.LayeredWidth3` paper-axiom

**Substantive content.** With pieces 1-4 landed, the
`MainAssembly.lean:265` `sorry` no longer exists (the
`caseC_canonicalLayered` helper is deleted in piece 4). The
remaining integration work:

1. **Delete `caseC_canonicalLayered`, `mainTheoremInputsOf`,
   `mainAssembly`, `MainTheoremInputs`.** These are residual
   scaffolding from the pre-refactor direct-construction shape.
2. **Verify `Step7.LayeredWidth3` is no longer load-bearing on the
   headline path.** With piece 3's
   `lem_layered_from_step7` producing `LayeredDecomposition α`
   directly, the paper-axiom interface
   (`Step7/Assembly.lean:302-348`) can be deprecated. Two
   sub-options:
   - **5A. Delete `Step7.LayeredWidth3` outright.** Aligned with
     the paper-axiom retirement principle; simplifies the API
     surface; the bandwidth-field packaging is no longer needed.
     Recommended.
   - **5B. Retain `Step7.LayeredWidth3` as a *bundle* for the
     `prop:72`-level output** (used internally by piece 2's
     concretisation; not on the headline path). Less aggressive
     deletion; keeps the bandwidth-field packaging available for
     diagnostic / intermediate use.
3. **`#print axioms width3_one_third_two_thirds`** verification:
   confirm that the headline's axiom output no longer lists
   `Step7.LayeredWidth3`-derived axioms (replaced by the
   genuine cascade port) and no longer carries the structured
   `sorry`. Update `lean/AXIOMS.md` accordingly: the only
   remaining project axiom on the headline path is
   `LinearExt.brightwell_sharp_centred`
   (and possibly the new `HypothesisArithmetic` if piece 4
   mg-MA-Sig chose the axiom route, sub-option B).
4. **Update `docs/PROOF-STRUCTURE-ONBOARDING.md`** §1 / §2 / §3
   to reflect the closed sorry + the new proof-by-contradiction
   shape + the retired paper-axiom. Add a §3 pitfall entry
   documenting the refactor's rationale (so future polecats don't
   try to "simplify" back to direct construction).
5. **Issue a `mg snapshot`** capturing the refactor's landing for
   the Zulip post.

**Polecat budget.** 1-2 sessions, **0.2M-0.5M tokens**.

**Sub-arc decomposition.**

- **mg-Int-A (cleanup):** delete residual scaffolding from
  `MainAssembly.lean` per item 1 above. ~0.5 session, 100k.
- **mg-Int-B (axioms audit + ONBOARDING update):** items 3-4
  above. ~0.5-1 session, 100k-300k.

**Upstream dependencies.** Pieces 1-4 all landed and integrated.

**Downstream consumers.** External: the Zulip post + manuscript
update.

**Hold-the-line risks.** Minimal — this piece is residual cleanup.
The single non-trivial risk is item 2's sub-option choice (5A vs.
5B); recommend 5A. Probability of revisit ~10%, magnitude +100k.

**Tag.** rigorous-and-narrow. Pure integration / cleanup.

### §2.6. Piece 6 — full Step 8 G4 (`lem_layered_balanced_full`)

**Added by mg-faf8** (2026-05-20) per the mg-0bd1 8th vacuity
discovery (`docs/state-S7-F-bridge-Session2.md`;
`docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #6). The original
5-piece decomposition listed the in-tree `lem_layered_balanced`
in §4.1 as "already-in-tree, usable" — the Step-8 endpoint that
piece 3's bridge feeds. mg-0bd1 proved that wrong: the in-tree
`lem_layered_balanced` / `Case3Witness` is — per its own
docstring (`LayeredBalanced.lean:447-450`) — the **bounded
`|β| ≤ 30`, `K ≤ 10` base sub-slice** of Step 8 G4, not the full
G4. Pinning the bridge to feed it forced the bridge conclusion to
emit `Case3Witness`'s five caps, two of which (band injectivity +
`L.K ≤ 2 L.w + 2`) bound `|α| ≤ 10 + C_exc T` — false for large
minimal γ-counterexamples. The repair is **a sixth piece**: the
faithful Lean port of the *full* Step 8 G4.

**Substantive content.** Lean port of paper `lem:layered-balanced`
(statement `step8.tex:2453-2464`; proof `step8.tex:3211-3266`):

```lean
theorem lem_layered_balanced_full.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :          -- ONLY the interaction-width cap
    HasBalancedPair β
```

For every finite width-3 non-chain poset `β` with `2 ≤ |β|`
admitting a `LayeredDecomposition L` with `L.w ≤ 4`, `β` has a
balanced pair. **No band-injectivity, no `L.K` bound, no `|β|`
bound** — paper `lem:layered-balanced` carries none of them. The
proof is a **strong induction on `|β|`** (`step8.tex:3211-3266`):

* **base `|β| = 2`** — non-chain ⇒ the two elements are
  incomparable, `Pr = 1/2` by the transposition automorphism;
* **Case A (`K = 1`)** — `β` is a single antichain, every pair
  `Pr = 1/2`;
* **Case B (layer-ordinal-reducible)** — `β = β₁ ⊕ β₂`; recurse
  on the non-chain factor, lift via
  `Corollary cor:reducibility-transfer` (in tree as the
  marginal-invariance `probLT_restrict_eq`);
* **Case C (irreducible, `K ≥ 2`)** — window-localise to
  `W = W(i,j)`, `|W| ≤ 3(3w+1)`; sub-case **C1** (`W ⊊ β`)
  recurses on `P|_W`; sub-case **C2** (`W = β`) is the
  **bounded base case** `|β| ≤ 3(3w+1) ≤ 39` (for `w ≤ 4`),
  depth `K ≤ 3w+1`, discharged by `prop:in-situ-balanced`.

**The in-tree `Case3Witness_proof` / `lem_layered_balanced` is
the C2 bounded base case** — *not* the whole of Piece 6. It is
itself a strong induction with `native_decide` enumeration leaves
covering the bounded slice. Piece 6 is therefore *largely wiring
already-built infrastructure into the headline path*: the
inductive-step lemmas `lem_cut`, `windowLocalization`,
`lem_layered_reduction` are already substantive Lean (currently
tagged **NC** "not consumed" in `PROOF-STRUCTURE-ONBOARDING.md`
§2 — they are exactly the missing inductive machinery), plus the
ordinal-reducibility transfer and the FKG / second-moment leaf of
`prop:in-situ-balanced`.

**Polecat budget.** 3-6 sessions, **0.8M-1.6M tokens** (mg-0bd1
§5 estimate by analogy with the mg-d8c7 per-piece budgets).

**Sub-arc decomposition** (recommendation; one sub-ticket
`mg-MA-G4-Full` or split into the four below):

- **mg-G4-A (induction skeleton):** state `lem_layered_balanced_full`;
  set up `Nat.strong_induction_on |β|`; dispatch base / Case A /
  Case B / Case C. ~1 session, 200k-300k.
- **mg-G4-B (Case B — ordinal reducibility):** wire
  `lem_layered_reduction` + `probLT_restrict_eq` marginal
  invariance for the reducible factor lift. ~1 session, 200k-300k.
- **mg-G4-C (Case C1 — window recursion):** wire `lem_cut` +
  `windowLocalization`; recurse on `P|_W` (`|W| < |β|`). ~1-2
  sessions, 250k-450k.
- **mg-G4-D (Case C2 — bounded base):** discharge `|β| ≤ 3(3w+1)`
  via the in-tree `Case3Witness_proof` machinery. **NOTE — the
  base-case coverage gap:** `Case3Witness_proof` covers only the
  cap-1 *singleton-band* sub-slice of `|β| ≤ 39`
  (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2.2: e.g.
  `3-antichain ⊕ 3-antichain`, `|β| = 6`, has no singleton-band
  width-`≤ 4` `L`). Piece 6's bounded base must additionally
  cover **non-singleton-band** bounded posets — either via the
  **mg-be48 cap-light enumeration extension**
  (`docs/state-Case3Witness-cap-light-enumeration.md`, already
  enumerates non-singleton bands for `nfree ≤ 25` cells) or a
  direct `prop:in-situ-balanced` port. ~1-2 sessions, 250k-550k.

**Upstream dependencies.** **None on the cascade.** Piece 6
consumes only an abstract `L : LayeredDecomposition β` with
`L.w ≤ 4`. Its inductive machinery (`lem_cut`,
`windowLocalization`, `lem_layered_reduction`,
`Case3Witness_proof`, `probLT_restrict_eq`) is **already in
tree**. Piece 6 can be dispatched **immediately, in parallel
with piece 1** (mg-0bd1 §8 Option (R2)).

**Downstream consumers.** Piece 3's S7-F bridge (re-pinned per
MA-Sig §4.2 §E to emit `L.w ≤ 4`) feeds Piece 6; Piece 6's
output `HasBalancedPair {a // a ∉ Xexc}` feeds `excPerturbLift`
in piece 4-body. So the consumption chain is
piece 3 → **piece 6** → piece 4-body.

**Hold-the-line risks.**

1. **Base-case coverage gap (the mg-G4-D note above).
   ⚠ MATERIALISED — mg-fdc2, 2026-05-20.** The
   `Case3Witness_proof` singleton-band restriction means the C2
   bounded base is not a drop-in. Probability the cap-light
   extension needs its own sub-arc ~35%, magnitude +300k-600k.
   **Mitigation:** mg-be48's enumeration already covers
   non-singleton bands within TIER A (`nfree ≤ 25`); confirm
   TIER A spans all `|β| ≤ 39` width-3 non-chain posets at
   mg-G4-D kickoff, before coding.

   **Update (mg-fdc2, Checkpoint 6 gate).** Risk 1 has
   materialised — and is *worse* than this estimate. The first
   Piece 6 execution attempt found it is **not a "needs its own
   sub-arc" cost overrun but a hard blocker**: `Case3Witness_proof`
   requires band injectivity in *every* branch, and the only
   in-tree discharge of the non-singleton-band irreducible base
   case (`bounded_irreducible_balanced_hybrid`'s out-of-scope
   branch) needs `Case2Witness L → HasBalancedPair β`, available
   only via the **provably-false** `Case2FKGSubClaim`. The
   cap-light mg-be48 enumeration is a *Python* certificate, not a
   Lean discharge, so it does not close the gap either.
   Additionally `windowLocalization` / `lem_layered_reduction`
   (the named inductive-step "wiring" lemmas) are **vacuous
   placeholders**. Piece 6 cannot be executed against the
   §4.2 §G routing. Full diagnosis + forward options (G1
   formalise honestly / G2 disclosed base-case axiom / G3
   status-quo) in `docs/state-Piece6-FullStep8G4-Session1.md`.
2. **`lem_cut` / `windowLocalization` re-targeting.** These NC
   lemmas were built for the abandoned size-minimal framing
   (mg-805c); re-targeting them onto the strong-induction
   headline path may surface signature drift. Probability ~25%,
   magnitude +200k-400k.
3. **Window-recursion termination.** Case C1 recurses on `P|_W`
   with `|W| < |β|`; the strict-descent measure must be threaded
   cleanly through `Nat.strong_induction_on`. Mechanical but
   fragile. Probability ~15%, magnitude +150k.

**Satisfiability.** Confirmed: `lem_layered_balanced_full` is a
faithful transcription of paper `lem:layered-balanced`, which is
a sound theorem with a paper proof. It consumes only `L.w ≤ 4`
(plus width-3, non-chain, `2 ≤ |β|`) — no unsatisfiable cap
combination. See `docs/state-MA-Sig-Session1.md` §10.6 for the
satisfiability check of the §4.2 §G consumer signature.

**Tag.** rigorous-but-substantial. Proof technique is known
(paper-proved strong induction); the in-tree gap is engineering,
not math (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2: *"the
in-tree gap is engineering, not math"*). The single non-trivial
risk is the base-case coverage gap (risk 1).

---

## §3. Phase B — end-to-end decomposition

### §3.1. Critical path

```
                       ┌──────── piece 4-Sig ──────────┐  (mg-MA-Sig)
                       │  (signature design + hyp:arith)│
                       │     1 session, 200-300k        │
                       └────────────┬───────────────────┘
                                    │   determines downstream signatures
                                    ▼
   ┌───────────────────────────────────────────────────────────────────┐
   │ piece 1 — Steps 1-6 cascade Lean port  (22-32 sessions, 5.0-8.5M) │
   │                                                                   │
   │   Wave 1 (parallel): mg-S1-A..D, mg-S5-A..E, mg-MathlibCheeger    │
   │   Wave 2 (sequential): mg-S2-A, mg-S2-B, mg-S3                    │
   │   Wave 3 (sequential): mg-S4-A, mg-S4-B, mg-S4-C                  │
   │   Wave 4 (sequential): mg-S6-A, mg-S6-B                           │
   │   QA: mg-S1234-QA, mg-S6-QA                                       │
   └────────────┬──────────────────────────────────────────────────────┘
                │                  ↑
                │                  │ checkpoints 1 + 2 (mg-6ab8 §4.3)
                ▼
   ┌───────────────────────────────────────────────────────────────────┐
   │ piece 2 — S7-A-E concretisation       (3-5 sessions, 0.5-1.0M)    │
   │   mg-S7-Conc-A / -B / -C / -D                                     │
   └────────────┬──────────────────────────────────────────────────────┘
                │
                ▼
   ┌───────────────────────────────────────────────────────────────────┐
   │ piece 3 — S7-F bridge                 (4-6 sessions, 1.0-1.5M)    │
   │   mg-S7-F-A (X^exc) / -B (sync) / -C (band assembly)              │
   │   mg-S7-F-D (chain-removal subtype lift)                          │
   │   mg-S7-F-Z (integration + QA)                                    │
   │   [emits L.w ≤ 4 + band-nonempty + |X^exc| ≤ C_exc T per         │
   │    MA-Sig §4.2 §E re-pinned by mg-faf8]                           │
   └────────────┬──────────────────────────────────────────────────────┘
                │
                ▼ (piece 3 → piece 6 → piece 4-Body)
   ┌───────────────────────────────────────────────────────────────────┐
   │ piece 4-Body — refactor body          (3-4 sessions, 0.6-1.2M)    │
   │   mg-MA-MinCex / mg-MA-ThmE / mg-MA-Cascade / mg-MA-Body          │
   │   ↑ consumes piece 6's HasBalancedPair output                    │
   └────────────┬──────────────────────────────────────────────────────┘
                │                  ↑ mandatory hold-the-line audit
                │                    (analog of mg-5fbd Checkpoint 3)
                ▼
   ┌───────────────────────────────────────────────────────────────────┐
   │ piece 5 — integration                 (1-2 sessions, 0.2-0.5M)    │
   │   mg-Int-A (cleanup) / mg-Int-B (axioms audit + ONBOARDING)       │
   └───────────────────────────────────────────────────────────────────┘

   ┌─── OFF THE CRITICAL PATH (dispatch in parallel with piece 1) ────┐
   │ piece 6 — full Step 8 G4              (3-6 sessions, 0.8-1.6M)    │
   │   mg-MA-G4-Full  (or mg-G4-A / -B / -C / -D)                      │
   │   NO upstream cascade dependency — consumes only an abstract     │
   │   LayeredDecomposition with L.w ≤ 4. Inductive machinery        │
   │   (lem_cut, windowLocalization, lem_layered_reduction) already  │
   │   in tree. Logically consumed: piece 3 → piece 6 → piece 4-Body.│
   └───────────────────────────────────────────────────────────────────┘
```

**Strict-sequential edges:**

- piece 4-Sig → everything else (piece 4-Sig fixes downstream signatures).
- piece 1 → piece 2 (S7-A-E concretisation needs Steps 5 + 6 grounded).
- piece 2 → piece 3 (bridge needs `L_{S7E}` input).
- piece 3 → **piece 6** → piece 4-Body (the bridge's
  `LayeredDecomposition` output is consumed by piece 6's full
  Step 8 G4; piece 6's `HasBalancedPair` output is consumed by
  piece 4-body's `excPerturbLift`).
- piece 4-Body → piece 5 (integration is residual cleanup).

**Piece 6 is NOT on the critical path** despite the logical
edge above: it has no upstream cascade dependency, so it can be
built any time before piece 4-Body needs it — recommended
dispatch is **early, in parallel with piece 1** (mg-0bd1 §8
Option (R2)). The piece 3 → piece 6 logical edge is satisfied
because piece 6's *signature* (consume `L.w ≤ 4`) is fixed by
MA-Sig §4.2 §G; piece 6 needs no piece-3 *artefact* to be built.

**Parallel arcs:**

- **PA-1.** mg-S1-A..D + mg-S5-A..E + mg-MathlibCheeger run in
  parallel after piece 4-Sig and the existing `Mathlib/BKGraph.lean`
  foundation. **Saves ~3-4 weeks calendar** at 5 polecats/week.
- **PA-2.** mg-S4-A..C and mg-S6-A..B run in parallel with the
  back-end of piece 1's wave 3-4. **Saves ~1-2 weeks calendar.**
- **PA-3.** mg-S7-F-A (X^exc) and mg-S7-F-B (sync) can run in
  parallel; mg-S7-F-C (band assembly) consumes both. **Saves ~3-5
  days calendar.**
- **PA-4.** mg-MA-MinCex and mg-MA-ThmE can run in parallel after
  piece 4-Sig. **Saves ~2-3 days calendar.**
- **PA-5 (added mg-faf8).** Piece 6 (mg-MA-G4-Full) runs **fully
  in parallel with piece 1** — it has no cascade dependency. Its
  3-6 sessions are entirely absorbed; **0 net calendar cost** as
  long as it lands before piece 4-Body. **Saves the full piece-6
  duration off the sequential total.**

**Parallelisation gain:** mid-estimate 5-6 weeks of calendar
savings off the strict-sequential 7-month baseline. **Realistic
calendar with parallelism: 5-6 months.**

### §3.2. Cumulative budget projection

Sequential session count (no parallelism, summing per-piece mids;
post-mg-faf8 including piece 6):
27 (piece 1) + 4 (piece 2) + 5 (piece 3) + 5 (piece 4) + 1
(piece 5) + 4 (piece 6) = **46 sessions** (mid).

Parallelism reduction: ~8-10 sessions absorbed into parallel waves
of piece 1, **plus piece 6's ~4 sessions fully absorbed** (PA-5).
**Realistic: 34-38 sessions** at the mid-estimate.

| Piece | Session mid | Token mid | Token range |
|---|---:|---:|---:|
| 4-Sig (pre-flight) | 1 | 250k | 200k-300k |
| 1 (Steps 1-6) | 27 | 6.5M | 5.0M-8.5M |
| 2 (S7-A-E concretisation) | 4 | 0.75M | 0.5M-1.0M |
| 3 (S7-F bridge) | 5 | 1.25M | 1.0M-1.5M |
| 4-Body | 4 | 1.0M | 0.6M-1.2M |
| 5 (integration) | 1 | 0.35M | 0.2M-0.5M |
| 6 (full Step 8 G4) — added mg-faf8 | 4 | 1.2M | 0.8M-1.6M |
| **Mid-estimate** | **46** (raw) / **34-38** (parallel) | **11.3M** | **8.3M-14.6M** |

**Calendar at 1 polecat/day:** raw 46 sessions = 9 weeks
single-track; with parallelism (piece 6 absorbed alongside
piece 1), **6 months** end-to-end including inter-step QA pauses
+ checkpoint audits + sub-split contingency.

**Planning ceiling (worst-case + contingency):** **13M-14.5M
tokens / 42-48 sessions / 7 months** — at/just above the
`mg-d8c7` ticket-body envelope; the overshoot is the mg-0bd1
correction cost (piece 6).

### §3.3. Strategic checkpoints (hold-the-line)

Six suggested go/no-go checkpoints (extends mg-6ab8 §4.3's three;
Checkpoint 6 added mg-faf8):

- **Checkpoint 0 (after piece 4-Sig lands, ~week 1).** Audit:
  does the proof-by-contradiction signature thread `hyp:arith`
  correctly? Does `pickMinimalCounterexample` produce a usable
  bundle? If the signature design surfaces an architectural gap
  (probability ~15%), re-scope before piece 1 starts.
- **Checkpoint 1 (after S1-S4 land, ~weeks 6-8).** mg-6ab8 §4.3
  Checkpoint 1: paper-side gap in S1 `thm:interface` port?
- **Checkpoint 2 (after S6 lands, ~weeks 10-12).** mg-6ab8 §4.3
  Checkpoint 2: abstract S6 scaffold consumable by grounded
  inputs?
- **Checkpoint 3 (before piece 3-S7-F-A starts, ~weeks 13-15).**
  mg-6ab8 §4.3 Checkpoint 3 + mg-5fbd Phase D audit replay: does
  piece 2's `L_{S7E}` deliver the bridge's input hypotheses
  concretely? **This is the highest-risk checkpoint** — the prior
  failure of this audit at the call-site architecture is exactly
  what triggered mg-d8c7.
- **Checkpoint 4 (after piece 3 lands, before piece 4-Body
  starts, ~weeks 18-20).** Audit: does the bridge's output have
  the shape the refactor body consumes? Specifically, is
  `lem_layered_from_step7` invokable on `(α, hMin, hCascade)`
  without intermediate adapters?
- **Checkpoint 6 (Piece 6 — before mg-G4-D / the C2 bounded base
  starts; added mg-faf8).** Audit: does the in-tree bounded
  machinery cover the **full** `|β| ≤ 3(3w+1) ≤ 39` width-3
  non-chain slice, or only the cap-1 singleton-band sub-slice?
  `Case3Witness_proof` covers only the latter
  (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2.2). Confirm the
  mg-be48 cap-light enumeration's TIER A (`nfree ≤ 25`) spans the
  rest, or scope a `prop:in-situ-balanced` port, **before**
  coding mg-G4-D. This is the §2.6 risk 1 gate — the one place
  Piece 6 could surface a 9th vacuity.

---

## §4. Phase C — dependencies + prerequisites

### §4.1. Already-in-tree (✓ usable)

Inheriting mg-6ab8 §5.1 + adding piece-specific items:

- **`Mathlib/BKGraph.lean`** (~550 LoC) — BK-graph foundation,
  consumed by pieces 1, 2.
- **`Mathlib/LinearExtension/*.lean`** — Fintype, Subtype, FiberSize,
  Birkhoff, FKG, BrightwellAxiom. Consumed by pieces 1, 2, 3, 4.
- **Pieces of `Mathlib/Grid2D.lean`, `DirichletForm.lean`,
  `Poset/Dilworth.lean`** — partial, consumed by piece 1.
- **`Step8/ExcPerturb.lean`** (mg-7496, F6b) — the `exc_perturb`
  perturbation bound (`step8.tex:1376-1396`). Consumed by piece 3.
- **`Step8/OneElemPerturb.lean`** (mg-1f5e, F6a) — the
  single-deletion perturbation bound (`step8.tex:964`). Consumed
  by piece 3.
- **`Step8/ChainPotentials.lean:328`** (mg-7b26, F7a) —
  `ChainLiftData α` structural data. Consumed by piece 3.
- **`Step7/{SignedThreshold, SignConsistency, TripleVisibility,
  Cocycle, Potential, SingleThreshold, GiantComponent,
  Prop71_Prop72_LemBandwidth}.lean`** — the S7-A-E pilot grounded
  forms (mg-4584, mg-9331, mg-1069, mg-d135, mg-516f). Consumed
  by piece 2.
- **`Step8/LayeredBalanced.lean:626/681`** (post-mg-234e) —
  `lem_layered_balanced` with caller's-`L` rewire. **AMENDED
  (mg-faf8):** this is **NOT** the Step-8 endpoint — it is the
  bounded `|β| ≤ 30` / `K ≤ 10` base sub-slice (its own docstring,
  `LayeredBalanced.lean:447-450`). It is **usable only as the
  bounded base case inside Piece 6** (§2.6), not as the §4.2 §E
  bridge's consumer. The Step-8 endpoint `lem_layered_balanced_full`
  is **NOT** already in tree — it is Piece 6's deliverable. (This
  line was the §4.1 error mg-0bd1 §0/§5 flagged.)
- **`Step8/OptionC/Case3WitnessProof.lean:256`** — the F3 strong
  induction inside `Case3Witness_proof`. **AMENDED (mg-faf8):**
  consumed by **Piece 6** as the C2 bounded-base discharge (paper
  `step8.tex:3260-3263`), *not* directly by piece 4. It covers
  the cap-1 singleton-band sub-slice of `|β| ≤ 39`; Piece 6's
  base case must extend it to non-singleton bands (§2.6 mg-G4-D,
  risk 1).

### §4.2. NEW infrastructure required (in scope)

Inheriting mg-6ab8 §5.2 + adding piece-specific items:

| Prerequisite | Used by | Estimated effort | Mathlib upstreamable? |
|---|---|---|---|
| Cheeger inequality / spectral-gap on `bkGraph α` | piece 1 (S2, S4, S6) | 1.5M-2.5M | **Yes** |
| Weak grid isoperimetric stability lemma | piece 1 (S2) | 0.4M-0.7M | **Yes** |
| Order-convex region API for `Z²` | piece 1 (S1, S2) | 0.1M-0.2M | Yes (small) |
| Chain-removal subtype lift extension | piece 3 (S7-F-D) | 0.5M-1.0M | Internal |
| Minimal-counterexample picker on width-3 non-chain finite posets | piece 4 (MA-MinCex) | 0.2M-0.3M | Internal (small utility, mathlib `Nat.find` based) |
| `HypothesisArithmetic` predicate or axiom | piece 4 (MA-Sig) | 0.05M-0.15M | n/a (project-specific) |
| BK-conductance `Φ(S)` definition + `LowConductanceOn` predicate on level cuts | piece 4 (MA-ThmE) | 0.2M-0.5M | Maybe — depends on generality |
| Theorem E grounded port (`step8.tex:36-181`) | piece 4 (MA-ThmE) | 0.5M-0.8M (contingent — see §2.4 risk #3) | No (project-specific) |

**Subtotal new infrastructure:** ~3.4M-5.9M (piece 1's mathlib
share) + ~1.4M-2.7M (pieces 3+4 internal infra) = **~4.8M-8.6M**,
roughly **55-70% of the total cumulative budget**. The new
infrastructure work is the single largest engineering surface and
the largest source of variance.

### §4.3. The Frankl-mathlib-copy-and-tweak pattern (Daniel 2026-05-18 AI-native-dev framing)

Files to copy from mathlib and tweak locally (rather than
contributing upstream + waiting for review). Per Daniel's
2026-05-18 framing: in an AI-native development setting,
"copy-and-tweak" beats "upstream-then-wait" when the upstream
review cycle is long compared to the project's own cadence.

Candidate files (estimated copy targets; verify by reading
mathlib4 at the time of dispatch):

| Mathlib4 source | Used by | Tweak required |
|---|---|---|
| `Mathlib/Combinatorics/SimpleGraph/Density.lean` (Cheeger-adjacent) | piece 1 (S2, S4, S6 Cheeger gap) | Adapt to weighted BK-graph; reversibility + `bkGraph` specifics |
| `Mathlib/Combinatorics/SimpleGraph/Connectivity.lean` (giant component) | piece 2 (S7-D giant-component already grounded but may need extension) | Probably none — extension already in `Step7/GiantComponent.lean` |
| `Mathlib/Order/Antichain.lean` / `Order/Chain.lean` (Dilworth) | piece 1 (S5 decomp-selection), piece 3 (Dilworth A⊔B⊔C input) | Lift to width-3 specifics; mathlib has Dilworth `dilworth_le` but not concrete chain decomposition; tweak in `Mathlib/Poset/Dilworth.lean` (already in tree, partial) |
| `Mathlib/MeasureTheory/Function/Jensen.lean` (Jensen) | piece 1 (S5 second-moment) | Mathlib has Jensen for reals; need `Nat`-restricted variant (already in S7-B grounded form for `Jensen-for-ℕ`); copy as needed |
| `Mathlib/Analysis/MeanInequalities.lean` (AM-GM, etc.) | piece 1 (S5, S6 inequalities) | Mostly usable; tweak for `Nat` cardinalities |
| `Mathlib/Topology/Algebra/Order/Floor.lean` (floor/ceil arithmetic) | piece 1 (constants tracking) | None |
| `Mathlib/Combinatorics/Pigeonhole.lean` | piece 1 (S2 boundary-counting) | None |
| `Mathlib/Probability/ProbabilityMassFunction.lean` (PMF, marginals) | pieces 1, 3 (Pr-marginal-invariance for ordinal sums; already partial in `Mathlib/LinearExtension/Subtype.lean:1152`) | Extension to chain-removal variant (piece 3's mg-S7-F-D) |
| `Mathlib/Topology/Algebra/Module/FiniteDimension.lean` (finite-dim linear algebra for Dirichlet form) | piece 1 (S2 Dirichlet form) | Tweak for finite-state Markov chain restriction |

**Copy-and-tweak pattern is recommended for:** Cheeger inequality
(piece 1 row 1), Dilworth chain decomposition (already partial in
tree at `Mathlib/Poset/Dilworth.lean`), Pr-marginal-invariance
extension (piece 3 mg-S7-F-D).

**Upstream-contribution pattern is recommended for:** weak grid
isoperimetric stability lemma (piece 1 row 2; pure planar
combinatorics, mathlib-natural), order-convex region API (piece 1
row 3; small utility, easy upstream win).

Decision: per polecat-arc and per-prerequisite — defer to the
relevant Phase-A sub-arc to choose. The recommendation here is
*not* to block on upstream review for any piece on the critical
path.

### §4.4. Out-of-scope but tracked (for completeness)

- `case3Witness_hasBalancedPair_outOfScope` axiom drop (mg-ac13
  §5.2 action 2, cap-light enumeration extension). Independent of
  pieces 1-5. **Could be parallel sub-project.**
- `LinearExt.brightwell_sharp_centred` axiom port (mg-b699 retained
  decision). Independent.
- Hypothesis A formalisation (`hyp:arith`). Piece 4 mg-MA-Sig
  decides between in-Lean predicate and project axiom; either way,
  Lean port of `hyp:arith`'s arithmetic content is out of scope
  here (matches `step8.tex` retention as an external arithmetic
  input).

---

## §5. Phase D — forward action recommendation

### §5.1. The action: file execution sub-tickets in dispatch order

Per ticket constraint *"No retreating from FULL refactor — per
Daniel directive, this is the path"*, the forward action is **not**
a choice among A/B/C-style options (that decision was already made
by the 07:13Z directive). The forward action is **dispatch
sequencing**: when to file which sub-tickets.

### §5.2. Recommended dispatch order

**Phase 1: Pre-flight (week 1, 1 ticket).**

- File **mg-MA-Sig** alone. Polecat task: design the refactor
  signature, decide Hypothesis A threading, audit the existing
  `Step8/TheoremE.lean` scaffold (mark substantive or marker).
  Output: a signature contract that downstream sub-tickets
  reference. **Output is paper-and-pencil; no Lean code lands in
  this ticket** (analog of mg-d8c7 itself).

**Phase 2: Cascade port + Piece 6 (weeks 2-14, 23-36 tickets in
waves).**

Wave 1 dispatched immediately after Phase 1 lands (week 2):
- mg-MathlibCheeger (1-2 tickets, parallel sub-arc).
- mg-S1-A, mg-S1-B, mg-S1-C, mg-S1-D (4 tickets, parallel).
- mg-S5-A, mg-S5-B, mg-S5-C, mg-S5-D, mg-S5-E (5 tickets,
  parallel).
- **mg-MA-G4-Full** — **Piece 6** (full Step 8 G4; added mg-faf8).
  1-4 tickets, **fully parallel** — no cascade dependency (§2.6,
  §7.3a). Dispatched here purely for calendar absorption; it only
  needs to land before Phase 4's mg-MA-Body.

Wave 2 (weeks 5-7, after S1 land + mathlib infra):
- mg-MathlibWeakGrid (1 ticket, parallel).
- mg-S2-A, mg-S2-B, mg-S3 (3 tickets, sequential within wave).

Wave 3 (weeks 8-10, after S2 + S3 land):
- mg-S4-A, mg-S4-B, mg-S4-C (3 tickets, sequential within wave).

Wave 4 (weeks 10-12, after S4 lands):
- mg-S6-A, mg-S6-B (2 tickets, sequential).

Checkpoint 1 audit (between waves 3-4): mg-S1234-QA (1 ticket).
Checkpoint 2 audit (after wave 4): mg-S6-QA (1 ticket).

**Phase 3: S7 concretisation + bridge (weeks 13-20, 8-11 tickets).**

After checkpoint 2 passes:
- mg-S7-Conc-A, mg-S7-Conc-B, mg-S7-Conc-C, mg-S7-Conc-D (4
  tickets, sequential within phase but the latter two can be
  parallel).

After piece 2 lands + checkpoint 3 audit:
- mg-S7-F-A, mg-S7-F-B (parallel) → mg-S7-F-C → mg-S7-F-D →
  mg-S7-F-Z (5 tickets total, with one parallelisation step).

**Phase 4: Refactor body + integration (weeks 21-26, 5-7 tickets).**

After checkpoint 4 passes (and after Piece 6 / mg-MA-G4-Full has
landed — it should have, from its Phase 2 parallel dispatch):
- mg-MA-MinCex, mg-MA-ThmE (parallel) → mg-MA-Cascade →
  mg-MA-Body (4 tickets, with one parallelisation step).
  `mg-MA-Body` calls `lem_layered_balanced_full` (Piece 6) — not
  the bounded `lem_layered_balanced` — and drops the
  `hC3 : Case3Witness` threading (MA-Sig §4.3, re-pinned mg-faf8).
- mg-Int-A, mg-Int-B (2 tickets, sequential).

**Total dispatch:** 35-55 tickets across 4 phases / 6-7 months
calendar (post-mg-faf8, including Piece 6).

### §5.3. Strategic checkpoints (re-stated)

See §3.3. Five checkpoints; the highest-risk is **Checkpoint 3**
(before piece 3 starts) — the very audit whose failure produced
mg-5fbd's RED verdict, replayed under the new piece-2 concretisation.

### §5.4. Single most important early signal

**Checkpoint 0** (after piece 4-Sig, week 1). If the
proof-by-contradiction signature can be cleanly typed with
`hyp:arith` threading and minimal-counterexample bundle, the
refactor is structurally feasible end-to-end. If the signature
itself surfaces an unanticipated gap (probability ~15%, the residual
of cumulative-vacuity-discovery), **stop here and re-scope** rather
than proceeding into months of cascade work that would need
re-architecting.

This is the cheapest possible insurance: 250k tokens / 1 session at
the start guards against 7M+ tokens of misdirected downstream work.

---

## §6. Risk watchlist

| # | Risk | Probability | Magnitude | Mitigation |
|---:|---|---:|---|---|
| 1 | ~~Piece 4-Sig surfaces unanticipated architectural gap (8th vacuity-discovery on the Lean signature)~~ **MATERIALISED (mg-0bd1).** The 8th vacuity surfaced on the MA-Sig §4.2 §E *bridge* signature (not piece 4-Sig's headline signature): the five-cap conclusion was unsatisfiable for large α. **Resolved (mg-faf8):** re-pinned to three caps + added Piece 6 (§2.6). | realised | +0.8M-1.6M (Piece 6) — absorbed in the §3.2 table | RESOLVED. Standing mitigation for *future* such gaps: every `∃`-with-caps signature must pass a satisfiability check, not just a type-check (MA-Sig §4.4 check (B); §10). |
| 2 | Cheeger / spectral-gap mathlib gap exceeds 2.5M | 25% | +500k-1M | Sub-arc kickoff in wave 1; copy-and-tweak fallback |
| 3 | `Theorem E` (Step8/TheoremE.lean) is marker, not substantive — grounding needs its own sub-arc | 30% | +500k-800k | Audit at mg-MA-Sig (Checkpoint 0) |
| 4 | Step 7 G4 cocycle O(1) propagation surfaces a missing fineness hypothesis from S6 | 25% | +500k | Checkpoint 3 before piece 3 starts |
| 5 | `lem:layered-from-step7` chain-removal subtype lift surfaces new vacuity | 20% | +500k-1M | Checkpoint 3 before piece 3; F6a/F6b mature |
| 6 | Sub-split overhead exceeds 1.5× on pieces 1 or 3 | 30% | +500k per affected piece | Inter-step QA after S1234 + after S6 |
| 7 | Mathlib upstream review delays on Cheeger / weak-grid | 50% | +2-4 weeks calendar | In-tree fallback; copy-and-tweak |
| 8 | Daniel changes course mid-execution | 30% | Variable | Phase 1 pre-flight is itself a partial-mitigation; checkpoint 3 is the natural pivot point |
| 9 | Hypothesis A threading decision is contentious | 20% | +200k-400k | mg-MA-Sig defaults to in-Lean-predicate; Daniel review at Checkpoint 0 |
| 10 | `Step7.LayeredWidth3` retention (sub-option 5B over 5A) surfaces during integration | 10% | +100k | Decide at piece 5; default 5A (delete) |

**Aggregate risk-adjusted budget:** mid-estimate **10.0M** + risk
weighted expected delta **~2.0M-3.5M** ⇒ **planning ceiling
~13.5M / 7-8 months**. Communicate this ceiling to Daniel; the
realistic delivery target is the **9.0M-10.5M** mid.

---

## §7. Pre-filed execution sub-tickets (RECOMMENDATIONS, not filed)

Per ticket constraint *"No premature execution commitment without
Daniel sign-off post-scoping"*, this section records **proposed
sub-ticket bodies** but **does NOT call `mg new` for any of them**.
After Daniel approves the dispatch sequence, a follow-on ticket (or
pm-pogo) files the relevant subset.

### §7.1. Phase 1 — pre-flight (file first)

#### mg-MA-Sig — refactor signature design

```
Title: OneThird-MA-Sig: design proof-by-contradiction refactor
       signature for width3_one_third_two_thirds_assembled; decide
       hyp:arith threading; audit Step8/TheoremE.lean scaffold
Depends: nothing (pre-flight; output is a paper-and-pencil signature
         contract).
Tags: onethird, lean-port, full-refactor, scoped-by-mg-d8c7, signature-design
Repo: one_third_width_three; default to main
Body: SCOPING ticket — no Lean code. Output:
      docs/state-MA-Sig-Session1.md fixing the refactor signature
      for downstream sub-tickets to reference. Decide:
      (1) hyp:arith — Lean predicate vs project axiom.
      (2) MinimalCounterexample bundle shape (Nat.find on
          Fintype.card vs Finset.min').
      (3) Step8/TheoremE.lean substantive vs marker (per
          PROOF-STRUCTURE-ONBOARDING §2 tag legend). If marker,
          scope its grounding as a separate sub-arc.
      Budget: 200-300k, 1 polecat session. Verdict: GREEN if
      signature types cleanly + Theorem E is substantive (or its
      grounding is scoped); RED if 8th vacuity-discovery on the
      signature itself.
```

### §7.2. Phase 2 — cascade port

(Inherit mg-6ab8 §7.1 + §7.2 verbatim. The bodies of mg-S1-A
through mg-S6-B, mg-S1234-QA, mg-S6-QA, mg-MathlibCheeger,
mg-MathlibWeakGrid are unchanged from mg-6ab8 §7. The dispatch
order is per §5.2 above.)

### §7.2a. Phase 2 (parallel) — Piece 6, full Step 8 G4 (added mg-faf8)

#### mg-MA-G4-Full — full Step 8 G4 port (`lem_layered_balanced_full`)

```
Title: OneThird-MA-G4-Full: Lean port of the FULL Step 8 G4
       (paper lem:layered-balanced, step8.tex:2453-2464 / proof
       3211-3266) — lem_layered_balanced_full: strong induction on
       |β|, consuming ONLY L.w ≤ 4. Piece 6 of the mg-d8c7 scope.
Depends: NOTHING on the cascade. Consumes only an abstract
         LayeredDecomposition with L.w ≤ 4. Inductive machinery
         (lem_cut, windowLocalization, lem_layered_reduction,
         Case3Witness_proof, probLT_restrict_eq) already in tree.
         Signature fixed by MA-Sig §4.2 §G (re-pinned mg-faf8).
         Dispatchable immediately, in parallel with piece 1.
Tags: onethird, lean-port, full-refactor, scoped-by-mg-d8c7,
      piece-6, step8-g4, 8th-vacuity-fix
Repo: one_third_width_three; default to main
Body: 1-4 tickets (mg-G4-A induction skeleton / mg-G4-B Case B
      ordinal reducibility / mg-G4-C Case C1 window recursion /
      mg-G4-D Case C2 bounded base). Target file
      lean/OneThird/Step8/LayeredBalancedFull.lean (new).
      mg-G4-D MUST extend the C2 bounded base beyond the cap-1
      singleton-band sub-slice (Case3Witness_proof covers only
      that) to non-singleton-band |β| ≤ 39 posets — via the
      mg-be48 cap-light enumeration or a direct
      prop:in-situ-balanced port; this is the piece's single
      non-trivial risk (§2.6 risk 1).
      Budget per ticket: 200-550k, 1-2 sessions.
      Aggregate: 0.8M-1.6M, 3-6 sessions.
      Verdict: GREEN if lem_layered_balanced_full closes with no
      new project axiom and no sorry; RED if the C2 base-case
      coverage gap surfaces a 9th vacuity.
```

### §7.3. Phase 3 — S7 concretisation + bridge

#### mg-S7-Conc-A through mg-S7-Conc-D — S7-A-E ground-set concretisation

```
Title: OneThird-S7-Conc-{A,B,C,D}: wire S7-A-E grounded forms to
       ground-set α of headline; concretise Edge/Vertex/Pair/src/
       tgt/signedWeight/path/posMass + constants b_n/b_d/c_n/c_d/M₀
       from Steps 5-6 cascade outputs
Depends: piece 1 (Steps 5 + 6 grounded forms landed).
Body: 4 tickets concrete-instantiating the S7-A-E grounded scaffold
      onto the BK-graph of α. mg-S7-Conc-A: BK-graph data. -B:
      Step 5 constants. -C: Step 6 constants. -D: assembly producing
      L_{S7E} : Step7.LayeredWidth3 with bandwidth ≤ 4.
      Budget per ticket: 150-300k, 1 session.
      Aggregate: 0.5M-1.0M, 3-5 sessions.
```

#### mg-S7-F-A through mg-S7-F-Z — S7-F bridge

```
Title: OneThird-S7-F-{A,B,C,D,Z}: Lean port of step8.tex
       lem:layered-from-step7 (ground-set lift from prop:72 output
       to def:layered on X∖X^exc); chain-removal subtype lift
       extension
Depends: piece 2 (S7-A-E concretised); ChainLiftData α (F7a,
         mg-7b26); exc_perturb (F6b, mg-7496); OneElemPerturb (F6a,
         mg-1f5e).
Body: 5 tickets covering the bridge construction. mg-S7-F-A:
      exceptional-set construction X^{exc} with |X^{exc}| ≤
      C_{exc}(T) bound. -B: synchronization maps f_{AB}/f_{AC}/f_{BC}.
      -C: band assembly producing LayeredDecomposition (X\X^{exc})
      with L.w ≤ 4. -D: chain-removal subtype lift extension to
      Mathlib/LinearExtension/Subtype.lean. -Z: integration + QA.
      RE-PINNED mg-faf8: the bridge conclusion emits EXACTLY THREE
      caps — |X^{exc}| ≤ C_exc T, band-nonempty, L.w ≤ 4 (MA-Sig
      §4.2 §E). It MUST NOT transcribe Case3Witness's five caps
      (band injectivity / L.K ≤ 2 L.w+2 / card bound) — those are
      unsatisfiable for large α (mg-0bd1). The bridge's consumer
      is Piece 6 (lem_layered_balanced_full), not the bounded
      lem_layered_balanced.
      Budget per ticket: 200-500k, 1-2 sessions.
      Aggregate: 1.0M-1.5M, 4-6 sessions.
      MANDATORY hold-the-line audit (analog of mg-5fbd Phase D
      Checkpoint 3) before mg-S7-F-A starts; if piece 2's L_{S7E}
      doesn't deliver bridge inputs concretely, re-scope piece 2
      before piece 3.
```

### §7.4. Phase 4 — refactor body + integration

#### mg-MA-MinCex, mg-MA-ThmE, mg-MA-Cascade, mg-MA-Body — refactor body

```
Title: OneThird-MA-{MinCex,ThmE,Cascade,Body}: implement the
       proof-by-contradiction refactor of
       width3_one_third_two_thirds_assembled per the mg-MA-Sig
       signature contract; thread minimal-counterexample +
       Theorem E + Steps 1-7 cascade output through to
       lem_layered_from_step7 + lem_layered_balanced_full (Piece 6)
       + exc_perturb_lift
Depends: mg-MA-Sig (signature contract); pieces 1, 2, 3, AND 6
         all landed.
Body: 4 tickets covering the refactor body. mg-MA-MinCex: build
      pickMinimalCounterexample (Nat.find on Fintype.card). mg-MA-ThmE:
      wire Step8/TheoremE.lean output to LowConductanceOn predicate
      (grounding scope per mg-MA-Sig). mg-MA-Cascade: build
      stepsOneToSevenCascade : LowConductanceOn → Step5R ∨ Step5C.
      mg-MA-Body: rewrite width3_one_third_two_thirds_assembled per
      the new proof-by-contradiction shape; delete mainAssembly,
      mainTheoremInputsOf, caseC_canonicalLayered. RE-PINNED
      mg-faf8: mg-MA-Body calls lem_layered_balanced_full (Piece 6),
      NOT the bounded lem_layered_balanced; it drops the hInj/hKw/
      hCardw args and the hC3 : Case3Witness threading, and the
      hC3 parameter from width3_one_third_two_thirds[_assembled]
      (MA-Sig §4.3).
      Budget per ticket: 200-500k, 1-2 sessions.
      Aggregate: 0.6M-1.2M, 3-4 sessions.
```

#### mg-Int-A, mg-Int-B — integration

```
Title: OneThird-Int-{A,B}: integration — close MainAssembly.lean:265
       sorry; retire Step7.LayeredWidth3 paper-axiom; #print axioms
       audit; update PROOF-STRUCTURE-ONBOARDING.md + AXIOMS.md
Depends: mg-MA-Body landed.
Body: 2 tickets covering residual cleanup. mg-Int-A: delete residual
      scaffolding from MainAssembly.lean (caseC_canonicalLayered,
      mainTheoremInputsOf, mainAssembly, MainTheoremInputs); decide
      Step7.LayeredWidth3 retain/delete (default delete, sub-option
      5A). mg-Int-B: #print axioms audit on the headline; update
      AXIOMS.md (remove Step7.LayeredWidth3-related entries; add
      HypothesisArithmetic if piece 4 chose the axiom route);
      update PROOF-STRUCTURE-ONBOARDING.md §1/§2/§3.
      Budget per ticket: 100-300k, 0.5-1 session.
      Aggregate: 0.2M-0.5M, 1-2 sessions.
```

### §7.5. Recommended dispatch order summary

```
Phase 1 (week 1):
  mg-MA-Sig

Phase 2 Wave 1 (weeks 2-4, ALL parallel):
  mg-S1-A, mg-S1-B, mg-S1-C, mg-S1-D
  mg-S5-A, mg-S5-B, mg-S5-C, mg-S5-D, mg-S5-E
  mg-MathlibCheeger (sub-arc; possibly 2 sequential tickets)
  mg-MA-G4-Full  (PIECE 6, added mg-faf8; no cascade dependency,
                  fully parallel — just needs to land before
                  Phase 4's mg-MA-Body)

Phase 2 Wave 2 (weeks 5-7):
  mg-MathlibWeakGrid (parallel with the rest of wave 2)
  mg-S2-A → mg-S2-B → mg-S3 (sequential)

Phase 2 Wave 3 (weeks 8-10):
  mg-S4-A → mg-S4-B → mg-S4-C (sequential)
  mg-S1234-QA (after S4-A; checkpoint 1)

Phase 2 Wave 4 (weeks 10-12):
  mg-S6-A → mg-S6-B (sequential)
  mg-S6-QA (after S6-B; checkpoint 2)

Phase 3 (weeks 13-20):
  mg-S7-Conc-A → mg-S7-Conc-B → mg-S7-Conc-C → mg-S7-Conc-D
    (sequential; -C and -D can parallelise)
  [checkpoint 3 audit]
  mg-S7-F-A ∥ mg-S7-F-B → mg-S7-F-C → mg-S7-F-D → mg-S7-F-Z

Phase 4 (weeks 21-26):
  [checkpoint 4 audit — also confirm mg-MA-G4-Full / Piece 6 landed]
  mg-MA-MinCex ∥ mg-MA-ThmE → mg-MA-Cascade → mg-MA-Body
    (mg-MA-Body consumes Piece 6's lem_layered_balanced_full)
  mg-Int-A → mg-Int-B
```

---

## §8. Cross-reference index

### §8.1. Paper

- `paper/main.tex` §1.4 road map, residual paragraph (lines 380-413).
- `paper/step8.tex:36-181` — Theorem E (`thm:thmE`).
- `paper/step8.tex:511-525` — Hypothesis A (`hyp:arith`).
- `paper/step8.tex:531-755` — `thm:main-step8` paper proof
  (the template piece 4 mirrors).
- `paper/step8.tex:1376-1396` — F6b `lem:exc-perturb`.
- `paper/step8.tex:964` — F6a `lem:one-elem-perturb`.
- `paper/step8.tex:1983-2106` — `def:layered` + `lem:layered-from-step7`
  (the piece-3 target).
- `paper/step8.tex:2244-2262` — paper's invocation of
  `lem:layered-from-step7` in the layered-reduction context.
- `paper/step8.tex:2453-2464` — `lem:layered-balanced` statement;
  `paper/step8.tex:3211-3266` — its proof (strong induction on
  `|β|`). **The piece-6 target (added mg-faf8).**
- `paper/step7.tex:1175-1193` — `prop:72`.
- `paper/step7.tex:1018-1056` — `lem:bandwidth ≤ 4` (S7-E target).

### §8.2. Lean (this worktree)

- `lean/OneThird/MainTheorem.lean:56` — headline.
- `lean/OneThird/Step8/MainAssembly.lean:236-267` —
  `caseC_canonicalLayered` (the unfixable in-place site; piece 4
  deletes).
- `lean/OneThird/Step8/MainAssembly.lean:308-372` — current
  `mainAssembly` + `width3_one_third_two_thirds_assembled` (piece 4
  rewrites).
- `lean/OneThird/Step8/LayeredBalanced.lean:626/681` — post-mg-234e
  `lem_layered_balanced` (**Piece 6's bounded base case** —
  re-pinned mg-faf8; *not* directly piece-4's invocation).
- `lem_layered_balanced_full` — **Piece 6 deliverable, NOT yet in
  tree.** Target file `lean/OneThird/Step8/LayeredBalancedFull.lean`
  (new). The full Step 8 G4 (paper `lem:layered-balanced`); piece
  4-body invokes this.
- `lean/OneThird/Step8/LayeredBalanced.lean:461-472` —
  `Case3Witness.{u}` (the five-cap structure; pieces 4 + 5 may
  retain or refactor as needed).
- `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`
  (piece 3 consumes).
- `lean/OneThird/Step8/ExcPerturb.lean:351` — `exc_perturb` (piece
  3 + 4 consume).
- `lean/OneThird/Step8/OneElemPerturb.lean` — F6a single-deletion
  bound (piece 3 consumes).
- `lean/OneThird/Step8/LayeredBridges.lean` — `layeredFromBridges`
  placeholder (piece 3 replaces).
- `lean/OneThird/Step8/TheoremE.lean` — Theorem E scaffold (piece
  4 mg-MA-ThmE audits + grounds).
- `lean/OneThird/Step7/Assembly.lean:302-413` —
  `Step7.LayeredWidth3` structure + `prop_72` + `prop_73`
  (pieces 2 + 5 consume + retire).
- `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean` — S7-E
  grounded `lem_bandwidth_le_four_bundled` (piece 2 invokes
  concretely on α).
- `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152` —
  `OrdinalDecomp.hasBalancedPair_lift` (piece 3 mg-S7-F-D extends
  to chain-removal variant).
- `lean/AXIOMS.md` — current axiom inventory (piece 5 mg-Int-B
  updates).

### §8.3. Predecessor scoping + audit documents

- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical
  proof-tree; §3 pitfall #5 = the obstruction this ticket scopes
  around.
- `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — the RED 7th
  vacuity discovery; the WHY of this refactor; §6.1 Option (A')
  enumerated as the multi-month full-refactor path.
- `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) — Steps
  1-7 multi-month scoping; recommended Option B pilot which led to
  the S7-A-E landing + mg-5fbd RED.
- `docs/coherence-collapse-case-extraction.md` (mg-ac13) —
  technique-known verdict; 3-disjoint-chains counterexample
  refuting mg-2970 R2 (the pitfall #2.3 specialised at piece 4's
  site).
- `docs/width3-residual-statement.md` (mg-2970) — SUPERSEDED but
  retains useful satisfiability + discharge-coverage analysis.
- `docs/onethird-proof-outline-audit.md` (mg-82fc) — per-step
  proof-tree tagging.
- `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2)
  — canonicalLayered bypass diagnosis.
- `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9) —
  cap-5 proposal history.
- `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0) — cap-5 sorry
  landing; relocated by mg-234e.
- `docs/state-S7-A-G1-G2-Session1.md` (mg-4584), `state-S7-B-G3-Session1.md`
  (mg-9331), `state-S7-C-G4-G5-Session1.md` (mg-1069),
  `state-S7-D-G6-G9-Session1.md` (mg-d135),
  `state-S7-E-prop71-prop72-Session1.md` (mg-516f) — S7-A-E pilot
  Session 1 docs (the grounded forms piece 2 concretises).

### §8.4. Predecessor work items

- mg-e2e9 (cap-5 proposal), mg-74d2 (canonicalLayered diagnosis),
  mg-5c32 (residual extraction first try), mg-82fc (proof-tree
  audit), mg-2970 (residual re-extraction), mg-ac13 (coherence
  collapse extraction), mg-6ab8 (Steps 1-7 scoping; selected
  Option B pilot), mg-4584/9331/1069/d135/516f (S7-A-E pilot
  execution), mg-5fbd (S7-F bridge audit; RED 7th vacuity
  discovery), mg-d8c7 (this scoping), mg-a22b (MA-Sig Phase 1
  signature contract), mg-0bd1 (S7-F bridge Session 2; RED 8th
  vacuity discovery), **mg-faf8 (MA-Sig re-pin + Piece 6 recorded
  here — §2.6)**.

---

## §9. Maintenance contract

This file is the **single-source-of-truth scoping document for the
Option A' FULL REFACTOR** (per Daniel directive 2026-05-19T07:13Z,
work item `mg-d8c7`).

Update this file in the **same commit** as any of the following:

- Daniel approves a specific Phase / dispatch wave and pm-pogo
  files the relevant §7 sub-tickets.
- A sub-piece lands and its actual budget / sub-split count
  contradicts §2.x; update the relevant row and the §3.2 aggregate.
- A risk in §6 materialises; update the probability + mitigation.
- A §3.3 / §5.3 checkpoint triggers a re-scope.
- A further vacuity-discovery surfaces; update the relevant §2.x
  with the new finding and §6 with the re-scoped recommendation.

**Update history.** The 8th vacuity-discovery (mg-0bd1) surfaced
on the MA-Sig §4.2 §E bridge signature and was corrected by
mg-faf8: the bridge is re-pinned to three caps, and **Piece 6**
(full Step 8 G4) is recorded as §2.6 — this is now a 6-piece
decomposition.

Daniel's "vacuity-discovery pattern has hit **8 times** as of
mg-0bd1" (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13,
mg-5fbd, mg-0bd1); **default to skeptical paper-first reading**,
not abstract-scaffold optimism — and, per the mg-0bd1 lesson,
**check every pinned `∃`-with-caps signature for satisfiability,
not merely type-compatibility** (`docs/state-MA-Sig-Session1.md`
§4.4 check (B), §10). The Option A' FULL REFACTOR's structural
feasibility rests on the paper-side `thm:main-step8` /
`lem:layered-balanced` / `lem:layered-from-step7` proofs being
clean (they are) and on the architectural shift not surfacing a
further gap.

If this file is wrong, edit it directly. Source-of-truth is the
Lean tree and `step{1..8}.tex`; this scoping is summary-of-plan.

**Forward-action mail draft (for the polecat to send after this
scoping lands).** *[Historical — mg-d8c7's original draft. Scope
figures superseded by the mg-faf8 re-pin: now **6 pieces /
35-57 dispatches / 8.3M-14.6M tokens / 6-7 months** — see §0
table and §3.2.]*

```
Subject: mg-d8c7 Option A' FULL REFACTOR scoping landed
From: mg-d8c7

GREEN scoping per the deliverable doc
(docs/OneThird-Option-A-FULL-REFACTOR-scoping.md).

Per Daniel directive 2026-05-19T07:13Z, Option A' FULL REFACTOR
is the path forward (Options B' / C' from mg-5fbd are
superseded). Scope:

  5 pieces / 34-51 polecat dispatches / 7.5M-13M tokens /
  5-7 months calendar.
  [SUPERSEDED mg-faf8: 6 pieces / 35-57 / 8.3M-14.6M / 6-7 months]

The single load-bearing architectural piece (piece 4 — MainAssembly
proof-by-contradiction refactor) is what makes pieces 1-3 invokable
together. Without it, S7-F bridge has no contradiction hypothesis
to consume — the obstruction mg-5fbd Session 1 surfaced.

Pre-flight recommendation: file mg-MA-Sig FIRST as a 1-session
paper-and-pencil signature design ticket; checkpoint 0 audit
before scaling out the cascade port.

Risk-adjusted planning ceiling: 13.5M / 7-8 months. Mid-target:
9-10M / 5-6 months.

Reply with dispatch authorization (full Phase 1+2 immediately, or
just pre-flight Phase 1 with Phase 2 decision deferred). If
authorized, pm-pogo files the §7 sub-tickets per the recommended
dispatch order in §5.2.
```
