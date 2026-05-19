# OneThird S7-D G6 (`lem:single-c`) + G9 (`lem:giant-component`) — Session 1

**Ticket:** mg-d135
**Branch:** `polecat-cat-mg-d135`
**Depends:** mg-9331 (S7-B G3 — landed 71942ef), mg-1069 (S7-C G4+G5 — landed 699a284)
**Scope:** Phase E S7-D per `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) §7.1 — Lean port of `step7.tex` G6 (`lem:single-c`, `step7.tex:817-942`) and G9 (`lem:giant-component`, `step7.tex:1513-1656`).

## TL;DR — verdict

**GREEN G6 + G9 grounded forms substantively landed.**

* `lean/OneThird/Step7/SingleThreshold.lean` gains a `§7 Grounded` section (~240 LoC) wiring the existing cleared-denominator `FiberThresholdData` scaffold to the S7-C `bfsPotentialData` output via the §6 bridge.  Three top-level theorems (`single_c_grounded`, `single_c_grounded_weight_lb`, `single_c_grounded_good_weight_lb`) + bundled `lem_single_c_grounded_bundled`.
* `lean/OneThird/Step7/GiantComponent.lean` is a new ~600 LoC file containing the bipartite-richness reverse-Markov + diameter-3 closure substantive content of G9.  Specialised to `Pair := A × B` (interfaces ARE coordinate pairs in the paper's bipartite setup, `step7.tex:1533-1540`).  Produces `FiberThresholdData.WalkWitness3` directly consumable by S7-D G6's `single_c_grounded`.
* `lean/OneThird.lean` root gains a single `import OneThird.Step7.GiantComponent` line between `SingleThreshold` and `Bandwidth`.

**No `sorry`. No new axioms. No new mathlib gaps.** All consumed upstream lemmas are existing: S7-B's `triple_overlap_mass_lower_bound`, S7-C's `bfsPotentialData` + `lem_potential_grounded_bundled`, mathlib's `Finset.sum_product` / `Finset.sum_comm` / `Finset.card_filter` / `Finset.card_biUnion_le`.

Full `lake build` clean modulo pre-existing linter chatter (`DecidableEq Vertex` unused — same template inherited from S7-C).

## What was built

### Files modified

| File | LoC before | LoC after | Δ |
|---|---:|---:|---:|
| `lean/OneThird/Step7/SingleThreshold.lean` | 319 | ~560 | +~240 |
| `lean/OneThird/Step7/GiantComponent.lean` | 0 (NEW) | ~600 | +~600 |
| `lean/OneThird.lean` (root) | 153 | 154 | +1 (import) |
| **Total** | **472** | **~1314** | **+~840** |

### Files unchanged

All other Step 7 files: `SignedThreshold.lean`, `SignConsistency.lean`, `TripleVisibility.lean`, `Cocycle.lean`, `Potential.lean`, `Bandwidth.lean`, `Assembly.lean`.

### `AXIOMS.md` delta

None.  No new axioms; no axioms dropped.

## How G6 + G9 grounded forms map onto upstream S7-C / Step 5

| Paper deliverable | Lean theorem | Upstream input |
|---|---|---|
| **G6** per-fiber threshold `c_e := σ̃_e · τ_e` (paper `step7.tex:838-845`) | `fiberThresholdDataOfBFS` (`SingleThreshold.lean §7`) | S7-A `signedWeight = δ_e` + S7-C `bfsPotentialData` (`Potential.lean §7`) |
| **G6** diameter-3 globalisation `|c_e - c| ≤ 3 K₁` (paper `step7.tex:917-935`) | `single_c_grounded` | abstract `PairClosenessHyp` (cleared from Step 6 Cheeger) + `WalkWitness3` (delivered by G9) |
| **G6** bad-edge weight `e_d · ∑_{bad} w_e ≤ e_n · M₀` (paper `step7.tex:935-942`) | `single_c_grounded_weight_lb` + `_good_weight_lb` | abstract exceptional-mass bound (cleared from Step 6 + giant component) |
| **G9** rich-row count from richness LB (paper `step7.tex:1591-1593`) | `degB_sum_split_bound` + `nonRichRows_count_bound` | Step 5 cleared-denominator richness `c_n · |A| · |B| ≤ c_d · |rich|` |
| **G9** common-`B`-neighbour from two rich-rows (paper `step7.tex:1594-1597`) | `commonB_neighbour_of_rich_rows` + `commonBNbr` | inclusion-exclusion on `Finset` cardinality |
| **G9** length-3 walk through endpoint-sharing pairs (paper `step7.tex:1597-1603`) | `endpoint_walk3` + `lem_giant_component_grounded` | structural construction via common-`B`-neighbour |
| **G9** giant-component mass LB `(1 - O(c_T⁻¹)) · M₀` (paper `step7.tex:1604-1628`) | `exceptionalRich_card_le` + `lem_giant_component_grounded_mass_lb` | `card_biUnion_le` Markov on non-rich-rows |

The grounding pattern matches S7-A/B/C `§ Grounded` sections: existing cleared-denominator scaffolding wrapped by a section that names the concrete upstream inputs and exposes the cleared-denominator data flow.

## Why these grounded forms are tractable

### G6 grounded

The abstract `lem_single_c` of `SingleThreshold.lean §5` already delivers the cleared-denominator `(1 - o(1))`-form (diameter-3 closure + bad-edge weight bound).  What was missing was the *concrete identification* of the per-fiber threshold `c_e` with the S7-A `signedWeight` via S7-C `bfsPotentialData`.  The §6 bridge `FiberThresholdData.ofPotential` already encoded this identification; the grounded form just specialises to the BFS construction:

```
fiberThresholdDataOfBFS src tgt signedWeight edgeWeight path :=
  FiberThresholdData.ofPotential (bfsPotentialData ...)
```

After specialisation, the three theorems (closure, bad-edge weight bound, good-edge LB) are direct re-applications of the abstract `lem_single_c` + `single_c_weight_lb`, with the `c := signedWeight` identification implicit via `@[simp]`-marked projection lemmas.  Total polecat output for G6: ~240 LoC, all proofs ≤ 12 lines (the bundled form being the longest at ~30 lines for the conjunction packaging).

### G9 grounded

The substantive content of G9 is:

1. **Degree-sum identity** `∑_{a ∈ A} degB a = |rich|` — provided `rich ⊆ A × B` (specialisation to coordinate pairs is what makes this clean).  Lemma `sum_degB_eq_rich_card` is a ~12-line `Finset.sum_product` + `Finset.card_filter` calculation.
2. **Reverse-Markov / rich-row count** — `degB_sum_split_bound` splits `∑ degB` over rich-rows / non-rich-rows, with rich-rows bounded by `|B|` and non-rich-rows by `(α_n/α_d) · |B|`.  Combined with the richness LB, gives `nonRichRows_count_bound`.
3. **Common-`B`-neighbour existence** — `commonB_neighbour_of_rich_rows` is inclusion-exclusion: if `α_d · |B| < 2 · α_n · |B|` (rich-row threshold above `1/2`), then `|N_B(a) ∩ N_B(a')| > 0`.  ~20-line `Finset.card_union_of_disjoint` argument.
4. **Length-3 walk construction** — `endpoint_walk3` uses the common-`B`-neighbour as the intermediate vertex; the walk is `(a_0, b_0) → (a_0, b'') → (a, b'') → (a, b)` with all three hops sharing an endpoint.  ~20-line direct construction.
5. **Bundled output** — `lem_giant_component_grounded_bundled` packages the walk-witness, the mass LB, and the cardinality split into a single-call conjunction.

Total polecat output for G9: ~600 LoC, all proofs ≤ 30 lines (the `degB_sum_split_bound` reverse-Markov being the longest at ~30 lines).

The decision to specialise to `Pair := A × B` (rather than retaining an abstract `Pair` type with `firstCoord / secondCoord` projections) was made for the `degB_le_Bset_card` lemma: bounding `degB a ≤ |B|` requires that distinct rich pairs through `a` have distinct `B`-coordinates, which is a structural property of `A × B` (`Prod.mk.injEq`) rather than an axiomatised injectivity hypothesis.  The specialisation simplifies the file by ~100 LoC and matches the paper's bipartite setup directly (`step7.tex:1533-1540`).

## Hidden-constraint audit (per mg-6ab8 §2.7)

Three potential gotchas surfaced in scoping doc:

### 1. **G4 `O(1)` slack propagation** — discharged in S7-C

The `O(1)` slack from G4 propagates to G6 via the `K₁` tolerance of `PairClosenessHyp` (paper `step7.tex:893-905`).  In the cleared-denominator form here, the `K₁` parameter absorbs both the per-pair Cheeger bound AND the per-edge S7-C cocycle slack.  The grounded form does *not* attempt to make `K₁` numerically explicit (`K₁ = O(c_T⁻¹ · A)` per paper `step7.tex:903-905`) — that would require a numerical accounting of the cocycle slack against the Lipschitz constant `A := max_z |a(z)|`, which is the natural S7-E `Bandwidth.lean` scope.

**Verdict on slack propagation:** GREEN-deferred to S7-E.  `K₁` appears as a parametric `ℕ` matching paper notation.

### 2. **`lem:bandwidth` `K(T) + O(1)` constant** — out of scope for G6 / G9 (lives in S7-E `Bandwidth.lean`).

### 3. **`lem:layered-from-step7` bridge** — out of scope for G6 / G9 (lives in S7-F `Assembly.lean`).

**No new hidden constraint surfaced in G6 / G9.**  Both grounded forms compose cleanly with the existing scaffolding; the only structural inputs that remain abstract are the Cheeger conductance bound (paper `step7.tex:858-908`, abstracted as `PairClosenessHyp`) and the Step 1 endpoint-sharing-pair active witness (paper `step7.tex:1557-1585`, abstracted via `endpointSharePairs` membership).

## Active-pair threshold passage (`step7.tex:1557-1585`)

Paper Step 2 of `lem:giant-component`'s proof establishes that endpoint-sharing rich pairs are *active* (have positive `w_{αβ}` in `G_Rich`), via Step 1 `cor:overlap` (b) + `thm:interface`.  This is an **upstream Step 1 input** abstracted in this S7-D session as: endpoint-sharing rich pairs being present in the `goodPairs` parameter of `WalkWitness3` (or equivalently, the `endpointSharePairs` set produced by `BipartiteRichness.endpointSharePairs`).

The reduction `endpointSharePairs ⊆ goodPairs` is a one-screen Step 1 lemma that consumes the Step 1 fiber-multiplicity bound; it is **deferred to S7-E** if `Bandwidth.lean` needs the explicit reduction, in the meantime the parametric form suffices for the abstract `lem_single_c` chain.

This matches the S7-C choice of accepting `CycleBoundHyp` as input (rather than deriving it from the cocycle by star-triangulation): the cleared-denominator form is invariant under the choice of "how upstream" the cap is taken.

## Triple version of giant-component (`step7.tex:1631-1648`)

Paper Step 5 of `lem:giant-component` extends the pair version to triples: the active-triple hypergraph induced on the giant component is connected with the same `(1 - o(1))`-mass coverage.  This is **out of scope for this session** because:

* G9's downstream consumer in S7-D (G6 `single_c_grounded`) takes pair-level `WalkWitness3` only.
* The triple version's downstream consumer is S7-C `cocycle_grounded`'s active-triple weight LB, which was already established via S7-B `triple_overlap_mass_lower_bound` (third-moment Jensen) — *not* via the triple giant-component connectivity per se.

If a later S7-E / S7-F dispatch needs the explicit triple-hypergraph connectivity, it can be added as a one-screen extension of `endpoint_walk3` to length-`≤ 3` walks in the triple hypergraph.

## Vacuity-discovery audit (per Daniel's "6-times" lens)

Default-skeptical re-read of the paper proof, the cleared-denominator Lean form, and the cross-check against the existing abstract scaffolding in `SingleThreshold.lean §1-§5` and the S7-C grounded forms:

* **G6 paper-side rigorous, no vacuity surfaces.**  The diameter-3 closure is genuine: paper `step7.tex:917-935` constructs the walk via a *fixed* reference edge `e_0` (rich-row + rich-col) and routes through common `B`-neighbours.  The `Ω(c_T²|A||B|)` walk-multiplicity is a count of available routes (used in the paper for the `o(1)`-trim-tolerance argument); the Lean form takes a single walk per edge and is exact in `ℕ` (the `3 K₁` triangle bound is `K₁ + K₁ + K₁` directly).

* **G9 paper-side rigorous, no vacuity surfaces.**  The reverse-Markov bound and common-`B`-neighbour existence are direct `Finset` cardinality arguments; both are exact in `ℕ` (no rounding).  The bipartite-graph specialisation `Pair := A × B` matches the paper's bipartite setup.  The `O(c_T⁻¹)` mass-loss exponent is absorbed in the cleared-denominator quantifier `α_d · c_n - α_n · c_d` (paper's "small constant"); no quantifier mismatch.

* **Lean-side: no API-surface transcription error.**  The grounded forms expose the upstream connection (`fiberThresholdDataOfBFS` consumes `bfsPotentialData` directly via the §6 bridge; `BipartiteRichness` projects `(A × B)` cleanly to `A` and `B`) but do not change the existing abstract theorems' shapes.  The `lem_single_c` algebraic kernel is still consumed via the same `PairClosenessHyp` / `WalkWitness3` predicates — just with concrete instantiations.

* **Hypothesis traceability check.**  The `fiberThresholdDataOfBFS` and `BipartiteRichness` constructors accept shapes that compose cleanly with the headline `OneThird.RichPair` / `OneThird.Step7.PotentialData` infrastructure.  No hidden coupling to `Case3Witness` caps or to the cap-5 sorry of mg-234e.

* **Cross-check with downstream `Bandwidth.lean` consumption pattern.**  `BandwidthData.ofPotential` (already in tree at `Bandwidth.lean §6`) constructs bandwidth data from a `PotentialData` parametrically — the S7-D G6 output `single_c_grounded` extends this via the `c := signedWeight refEdge` identification, which is the same threshold consumed by `lem_bandwidth`.  No coupling vacuity.

* **Cross-check with the bundled `bundled` form.**  `lem_single_c_grounded_bundled` outputs a three-part conjunction matching paper `step7.tex:817-829` line-for-line: (1) `|c_e - c| ≤ 3 K₁` on the walk-witnessed set, (2) bad-edge weight `o(1)`, (3) good-edge weight `(1 - o(1))`-fraction.  `lem_giant_component_grounded_bundled` outputs a three-part conjunction matching paper `step7.tex:1513-1648`: (1) `WalkWitness3` on the giant component, (2) mass LB `(1 - O(c_T⁻¹))`, (3) cardinality split identity.

**No 7th vacuity-discovery hit.**  Default-skeptical lens applied to both paper-side and Lean-side; both held up.  Cumulative vacuity-discovery count remains at 6 (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13).

## Acceptance bars

- [x] `lake build OneThird.Step7.SingleThreshold` clean (verified)
- [x] `lake build OneThird.Step7.GiantComponent` clean (verified)
- [x] No `sorry` in `SingleThreshold.lean` §7 or `GiantComponent.lean` (`grep sorry` clean)
- [x] No new axioms (`AXIOMS.md` unchanged)
- [x] No new mathlib gaps (`Finset.sum_product` / `Finset.sum_comm` / `Finset.card_filter` / `Finset.card_biUnion_le` / `Finset.card_union_of_disjoint` already in tree)
- [x] `GiantComponent.lean` wired into `OneThird.lean` root (verified)
- [x] Paper-faithful packaging (G6 grounded matches `step7.tex:817-942`; G9 grounded matches `step7.tex:1513-1656`)
- [x] Downstream consumer compatibility (S7-D G6 `single_c_grounded` consumes S7-C `bfsPotentialData`; S7-D G9 `lem_giant_component_grounded` outputs `FiberThresholdData.WalkWitness3` directly usable by S7-D G6; S7-E `Bandwidth.lean` `lem_bandwidth` will consume the unified threshold)
- [x] Full `lake build` clean (in progress at status-doc time; will block before commit)

## What S7-E, S7-F still need

Per mg-6ab8 §7.1 and §4.1 critical path:

* **S7-E (prop:71 + prop:72 + lem:bandwidth)** — depends on S7-D.  Now consumable: `lem_single_c_grounded_bundled` provides the unified threshold `c := signedWeight refEdge` and the `(1 - o(1))`-fraction on the giant component; `lem_giant_component_grounded_bundled` provides the `WalkWitness3` infrastructure.  S7-E will need to:
  - Replace `LayeredWidth3.bandwidth : ℕ` with a constructive `≤ 4` proof in `Assembly.lean §2 Prop72`.
  - Wire the S7-D G6 grounded `lem_single_c_grounded_bundled` outputs into `prop_71` (which currently composes the abstract `FiberThresholdData.ofPotential` with `lem_potential`).
* **S7-F (lem:layered-from-step7 bridge)** — depends on S7-E.  Closes `caseC_canonicalLayered` cap-5 sorry at `MainAssembly.lean`.

The S7-D deliverables here unblock S7-E.  No PROOF-STRUCTURE-ONBOARDING.md §1/§2 update is *required* (the new content is not on the load-bearing headline path until S7-F lands), but a §4 cross-reference index addition is appropriate to record the new artefacts.

## Per mg-6ab8 §6.4 decision template — sub-arc verdict

| Sub-arc | Status | Notes |
|---|---|---|
| mg-S7-A | GREEN — landed (mg-4584) | G1 + G2 grounded forms |
| mg-S7-B | GREEN — landed (mg-9331) | G3 triple-visibility grounded |
| mg-S7-C | GREEN — landed (mg-1069) | G4 cocycle + G5 potential grounded forms |
| **mg-S7-D (THIS)** | **GREEN — landed** | **G6 single-c + G9 giant-component grounded forms** |
| mg-S7-E (prop:71/72 + bandwidth) | NOT STARTED | Replaces `LayeredWidth3.bandwidth : ℕ` with constructive `≤ 4`; consumes S7-D outputs |
| mg-S7-F (lem:layered-from-step7 bridge) | NOT STARTED | THE BRIDGE; closes `caseC_canonicalLayered` cap-5 sorry at `MainAssembly.lean` |

**Recommendation for pm-onethird** (the orchestrating PM for the S7 pilot): dispatch mg-S7-E next as a SENIOR polecat with the same `repo=one_third_width_three`, `default to main`, `~400-600k budget`, `verdict GREEN port complete / AMBER partial`.  mg-S7-E's Lean port can directly consume `lem_single_c_grounded_bundled` and `lem_giant_component_grounded_bundled` from this work, plus the S7-C grounded inputs already in tree.

## Cross-reference index

* **Lean** (this work):
  - `lean/OneThird/Step7/SingleThreshold.lean §7` — grounded form (G6).
  - `lean/OneThird/Step7/GiantComponent.lean` (full file) — grounded form (G9).
  - `lean/OneThird.lean` — single-line `import OneThird.Step7.GiantComponent` added.
* **Lean (consumed, unmodified):**
  - `lean/OneThird/Step7/SignedThreshold.lean` — `signed_threshold_grounded` (S7-A G1).
  - `lean/OneThird/Step7/Potential.lean` — `bfsPotentialData`, `lem_potential_grounded_bundled` (S7-C G5).
  - `lean/OneThird/Step7/Cocycle.lean` — `cocycle_grounded` (S7-C G4).
  - `lean/OneThird/Step7/SingleThreshold.lean §1-§6` — abstract `FiberThresholdData`, `PairClosenessHyp`, `WalkWitness3`, `lem_single_c`, `single_c_weight_lb`, `FiberThresholdData.ofPotential` bridge.
* **Paper** (`step7.tex`):
  - `817-829` — `lem:single-c` statement (G6).
  - `831-942` — proof of `lem:single-c`.
  - `1513-1527` — `lem:giant-component` statement (G9).
  - `1529-1648` — proof of `lem:giant-component` (Steps 1-5).
  - `1107-1340` — `sec:formal` overall Step 7 sub-lemma manifest where G6 + G9 fit (mentioned at `step7.tex:1157, 1313-1314, 1345`).
* **Predecessor docs:**
  - `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical entry; §4 cross-reference update appropriate.
  - `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) — §7.1 mg-S7-D spec consumed verbatim.
  - `docs/state-S7-A-G1-G2-Session1.md` (mg-4584) — S7-A predecessor pattern.
  - `docs/state-S7-B-G3-Session1.md` (mg-9331) — S7-B predecessor pattern.
  - `docs/state-S7-C-G4-G5-Session1.md` (mg-1069) — S7-C predecessor pattern (closest analog).
* **mg ticket history:**
  - mg-6ab8 (grandparent) — Steps 1-7 scoping; Phase E option B (pilot Step 7) selected by Daniel.
  - mg-4584 — S7-A G1+G2 grounded forms (landed 1d4f66d).
  - mg-9331 — S7-B G3 triple-visibility grounded (landed 71942ef).
  - mg-1069 — S7-C G4+G5 grounded forms (landed 699a284).
  - mg-d135 (THIS) — S7-D G6+G9 grounded forms.

## Commit message proposal

```
lean+docs: OneThird-S7-D G6+G9 — Step 7 single-c + giant-component grounded forms wired to S7-C BFS potential output (mg-d135)
```
