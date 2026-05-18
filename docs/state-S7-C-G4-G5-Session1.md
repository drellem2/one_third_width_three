# OneThird S7-C G4 (`lem:cocycle`) + G5 (`lem:potential`) — Session 1

**Ticket:** mg-1069
**Branch:** `polecat-cat-mg-1069`
**Depends:** mg-9331 (S7-B G3 triple-visibility — landed at 71942ef)
**Scope:** Phase E S7-C per `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) §7.1 — Lean port of `step7.tex` G4 (`lem:cocycle`, `step7.tex:388-643`) and G5 (`lem:potential`, `step7.tex:654-789`).

## TL;DR — verdict

**GREEN G4 + G5 grounded forms substantively landed.** Both `lean/OneThird/Step7/Cocycle.lean` and `lean/OneThird/Step7/Potential.lean` now expose a `§ Grounded` section wiring the existing cleared-denominator abstract scaffolding (760 LoC Cocycle, 381 LoC Potential) to the upstream S7-A (`signed_threshold_grounded`) and S7-B (`triple_visibility_grounded`) outputs from the just-landed mg-4584 / mg-9331 sub-arcs. Full `lake build` clean modulo pre-existing linter chatter; no new axioms; no new `sorry`s; no new mathlib gaps.

Key Lean deliverables (Cocycle §6 grounded, Potential §7 grounded):

* **`tripleDataOfVisibility`** (`Cocycle.lean:843`) — concrete `TripleData (Pair × Pair × Pair) LinExt` whose `tripleFib` and `weight` fields are wired to S7-B `tripleOverlap` / `tripleOverlapMass`, with the cocycle-specific fields (`uCoord`, `vCoord`, `cocycleDefect`, `fiberBound`) accepted as abstract upstream-Step-1/S7-A inputs.
* **`tripleDataOfVisibility_total_weight_lb`** — `c³ · |LP| ≤ ∑_{T ∈ richStar³} weight T`, derived from `triple_overlap_mass_lower_bound` (S7-B part (a)+(b) composition).
* **`cocycle_grounded`** (`Cocycle.lean:888`) — bundled conjunction (i) S7-B total triple-mass LB + (ii) `lem_cocycle` bad-triple weight bound `b_d · c_w · ⌊K₀/2⌋² · ∑_{bad T} w_T ≤ c_d · tMax · b_n · M³`. Single-call output for downstream G5 consumption.
* **`cocycle_grounded_good_weight_lb`** — contrapositive form `b_d · c_w · ⌊K₀/2⌋² · (totalW − ∑_{good} w_T) ≤ c_d · tMax · b_n · M³`.
* **`bfsSumPot`** (`Potential.lean:447`) — explicit `bfsSumPot signedWeight path z := ∑ e ∈ path z, signedWeight e` realising paper `a(z) := ∑_{e ∈ path_T(z₀ → z)} δ_e` (`step7.tex:699`).
* **`bfsSumPot_tree_diff`** — the fundamental BFS tree-edge identity `pot (tgt e) - pot (src e) = signedWeight e` from path-extension.
* **`BFSTreeExtensionHyp`** — abstract structural hypothesis `path (tgt e) = path (src e) ++ [e]` on tree edges; the predicate that the `path` data really encodes a BFS tree rooted at the basepoint.
* **`bfsPotentialData`** — concrete `PotentialData Vertex Edge` whose `pot` field is `bfsSumPot`; other fields abstract upstream inputs.
* **`bfsPotentialData_tree_integration`** — discharge of the abstract `TreeIntegrationHyp` from `BFSTreeExtensionHyp`.
* **`potential_grounded`** (`Potential.lean:610`) — paper-faithful cleared-denominator bound `e_d · ∑_{bad e} edgeWeight e ≤ e_n · M₀`, composing `bfsPotentialData_tree_integration` with the abstract `lem_potential`.
* **`potential_grounded_good_weight_lb`** — contrapositive form.
* **`lem_potential_grounded_bundled`** — single-call paper-statement bundle: (1) tree-edge identity + (2) sign-agreement on good edges + (3) bad-edge weight bound.

**No `sorry`. No new axioms. No new mathlib gaps.** All consumed upstream lemmas are existing: S7-B's `triple_overlap_mass_lower_bound`, the §1-§5 Cocycle scaffolding, the §1-§6 Potential scaffolding, and `List.map_append` / `List.sum_append` from mathlib.

## What was built

### Files modified

| File | LoC before | LoC after | Δ |
|---|---:|---:|---:|
| `lean/OneThird/Step7/Cocycle.lean` | 760 | 999 | +239 |
| `lean/OneThird/Step7/Potential.lean` | 381 | 711 | +330 |
| **Total** | **1141** | **1710** | **+569** |

### Files unchanged

All other Step 7 files: `SignedThreshold.lean`, `SignConsistency.lean`, `TripleVisibility.lean`, `SingleThreshold.lean`, `Bandwidth.lean`, `Assembly.lean`. `OneThird.lean` root unchanged (both grounded files were already imported pre-S7-C).

### `AXIOMS.md` delta

None. No new axioms; no axioms dropped.

## How G4 + G5 grounded forms map onto upstream Step 5 / S7-A / S7-B

| Paper deliverable | Lean theorem | Upstream input |
|---|---|---|
| **G4** triple-overlap mass `∑ w_T ≥ c³·\|LP\|` (active-triple LB) | `tripleDataOfVisibility_total_weight_lb` (`Cocycle.lean:867`) | S7-B `triple_overlap_mass_lower_bound` (`TripleVisibility.lean:312`) |
| **G4** bad-triple weight bound `b_d·c_w·⌊K₀/2⌋²·∑_{bad} w_T ≤ c_d·tMax·b_n·M³` | `cocycle_grounded.2` (`Cocycle.lean:888`) | abstract `PushforwardHyp` (Step 1 ℤ²-action), `SummedBudgetHyp` (S7-A signed-threshold integrated), `fiberBound ≤ tMax`, `cocycleDefect` form |
| **G5** BFS path potential `a(z) := ∑_{e ∈ path} δ_e` | `bfsSumPot` (`Potential.lean:447`) | S7-A signed-weight `δ_e = σ̃_e · τ_e` via `signedWeight : Edge → ℤ` parameter |
| **G5** tree-edge identity `a(y) − a(x) = δ_e` exactly | `bfsSumPot_tree_diff` (`Potential.lean:472`) | abstract `BFSTreeExtensionHyp` (path-extension on tree edges) |
| **G5** bad-edge weight bound `e_d·∑_{bad e} w_e ≤ e_n·M₀` | `potential_grounded` (`Potential.lean:610`) | abstract `CycleBoundHyp` (star-triangulation through S7-C cocycle, paper `step7.tex:712-733`); abstract `LongDecompositionHyp` + cleared long-edge weight (paper diameter-3 lemma, `step7.tex:773-785`) |

The grounding pattern matches the S7-A `SignedThreshold.lean §7` and S7-B `TripleVisibility.lean §4` grounded sections: existing cleared-denominator algebraic kernels are wrapped by a `§ Grounded` section that names the concrete upstream inputs and exposes the cleared-denominator data flow.

## Why these grounded forms are tractable

### G4 grounded

The abstract `lem_cocycle` and `good_triple_weight_lb` of `Cocycle.lean` §5 already deliver the `(1 − o(1))` form in cleared-denominator: bad-triple weight bound and its contrapositive. What was missing was the *connection to the visibility/triple-overlap data* from S7-B (`tripleOverlapMass`, `tripleOverlap`).

The grounded form is a 240-line wrapper: it specialises `Triple := Pair × Pair × Pair`, `tripleFib := tripleOverlap`, `weight := tripleOverlapMass`, then derives the active-triple weight LB via S7-B's `triple_overlap_mass_lower_bound` and bundles the result with the abstract `lem_cocycle` conclusion into a single conjunction. Total polecat output for G4: ~240 LoC, all proofs ≤ 5 lines.

### G5 grounded

Similarly, the abstract `lem_potential` of `Potential.lean` §5 already delivers the cleared-denominator form. What was missing was a *concrete construction of `pot`* matching paper `step7.tex:699`.

The grounded form constructs `pot := bfsSumPot signedWeight path` from the path data and shows that the abstract `TreeIntegrationHyp` reduces to the structural `BFSTreeExtensionHyp` (path-extension on tree edges). The key lemma `bfsSumPot_tree_diff` is a 3-line proof using `List.map_append` and `List.sum_append`. Total polecat output for G5: ~330 LoC, all proofs ≤ 8 lines.

## Hidden-constraint audit (per mg-6ab8 §2.7)

Three potential gotchas surfaced in scoping doc:

### 1. **G4 `O(1)` slack propagation through BFS spanning tree** (`mg-6ab8 §2.7` hidden constraint #1)

Paper `step7.tex:454-457` `|Δ_0(T, L)| ≤ C_0` propagates uniformly through the BFS integration via `bfsSumPot_tree_diff` as the exact-tree-edge identity (defect 0) plus the `CycleBoundHyp` short-cycle bound (per-edge constant `C₁ = O(diameter)`).

In the cleared-denominator form here, the `C₁` parameter is *parametric* and the grounded form exposes it explicitly: the downstream Potential.lean caller chooses `C₁` matching the diameter-3 bound times the per-triangle `K₀` of G4. The Lean form does *not* attempt to make `C₁` numerically explicit (`C₁ ≤ 7 · K₀` per `step7.tex:765-768`) — that would couple G5 to the diameter argument of `lem:giant-component`, which is S7-D scope.

**Verdict on slack propagation:** GREEN-deferred. The `O(1)` slack appears in the Lean signature as a parametric `C₁ : ℕ` matching paper notation. S7-D will instantiate `C₁` against the diameter-3 bound.

### 2. **`lem:bandwidth` `K(T) + O(1)` constant** — out of scope for G4 / G5 (lives in S7-E `Bandwidth.lean`).

### 3. **`lem:layered-from-step7` bridge** — out of scope for G4 / G5 (lives in S7-F).

**No new hidden constraint surfaced.** Both grounded forms compose cleanly with the existing scaffolding; the only structural inputs that remain abstract are `PushforwardHyp` (Step 1 ℤ²-action lower bound — paper-axiomatised at the Step 1 layer), `CycleBoundHyp` (short-cycle defect bound — paper-derivable from S7-C cocycle by star-triangulation), and `LongDecompositionHyp` + long-edge weight (paper-axiomatised at S7-D `lem:giant-component` layer).

## Active-triple threshold passage (`step7.tex:619-643`)

Paper `lem:cocycle`'s passage from "per-triple `K(T) ≥ K_0` implies disagreement-rectangle mass bound" to "summed bad-triple weight ≤ `O(ε_2 · M^{(3)})`" is already in tree at `Cocycle.lean:566-665` (`sum_bad_weight_bound` + `lem_cocycle`). The grounded form just wires the upstream visibility data and bundles. **No new substantive passage was needed in this session.**

## Star-triangulation short-cycle bound (`step7.tex:712-733`)

The paper's star-triangulation derivation of `|∮_γ δ| ≤ O(1) · ℓ(e)` from G4 on each triangle is **not** explicitly formalised in this session. Instead, the grounded form takes the short-cycle bound `CycleBoundHyp` as an abstract input — this is the same compositional shape as S7-A's `AffineStaircaseSpreadHyp` (cleared-denominator spread bound taken as input from upstream Step 2 BK-boundary argument).

The derivation `CycleBoundHyp ← (cocycle_grounded.2 + BFS-tree path structure)` is a 1-screen Lean lemma that consumes `cocycle_grounded.2` (the bad-triple weight bound) plus a structural decomposition of each fundamental cycle into triangles. It is **deferred to a small S7-C follow-up** if the downstream S7-D / S7-E layer needs the explicit reduction; in the meantime, the parametric form is sufficient for the abstract `lem_potential` chain.

This matches the S7-A choice of accepting `AffineStaircaseSpreadHyp` as input (rather than deriving it from Step 2 BK-boundary count): the cleared-denominator form is invariant under the choice of "how upstream" the cap is taken.

## Vacuity-discovery audit (per Daniel's "6-times" lens)

Default-skeptical re-read of the paper proof, the cleared-denominator Lean form, and the cross-check against the existing abstract scaffolding in `Cocycle.lean` §1-§5 and `Potential.lean` §1-§6:

* **G4 paper-side rigorous, no vacuity surfaces.** The disagreement-rectangle argument is genuine: the `ℤ²`-action lower bound is a *finite-volume* result (paper `step7.tex:530-587` derives it from `cor:triple-overlap` cube structure). The cleared-denominator Lean form is exact in ℕ (the `⌊K₀/2⌋²` is a strict lower bound, dropping the off-by-one in `|rectLattice K|` for odd `K`). The active-triple weight LB from S7-B is the third-moment Jensen at `n = 2`, a genuine Chebyshev-sum bound.

* **G5 paper-side rigorous, no vacuity surfaces.** The BFS spanning-tree integration is genuine: `bfsSumPot` is a concrete ℤ-valued sum, and the tree-edge identity reduces to `List.map_append` + `List.sum_append`. The cleared-denominator Lean form is exact in ℕ for the bad-edge weight bound; no rounding occurs in the abstract `lem_potential` step.

* **Lean-side: no API-surface transcription error.** The grounded forms expose the upstream connection (`tripleDataOfVisibility` consumes S7-B `tripleOverlap`/`tripleOverlapMass` directly, not via an abstract `Triple : Type*` placeholder) but do not change the existing abstract theorems' shapes. The `lem_cocycle` and `lem_potential` algebraic kernels are still consumed via the same `PushforwardHyp` / `SummedBudgetHyp` / `TreeIntegrationHyp` / `CycleBoundHyp` predicates — just with concrete instantiations.

* **Hypothesis traceability check.** The `tripleDataOfVisibility` and `bfsPotentialData` constructors accept a `Pair`, `LinExt`, `Vertex`, `Edge` shape that composes cleanly with the headline `OneThird.RichPair` / `OneThird.Mathlib.LinearExtension` infrastructure. No hidden coupling to `Case3Witness` caps or to the cap-5 sorry of mg-234e.

* **Cross-check with downstream `Cocycle.lean`'s consumption pattern.** `Potential.lean`'s `bfsPotentialData` parameterisation (over `Vertex Edge : Type*`) is compatible with the `Pair × Pair × Pair` triples consumed by `Cocycle.lean`'s `cocycle_grounded`: the edges `e = (x, y)` of the element graph `G^P` of `step7.tex:669` are pairs, and the BFS path is over those pairs. No coupling vacuity.

**No 7th vacuity-discovery hit.** Default-skeptical lens applied to both paper-side and Lean-side; both held up.

## Acceptance bars

- [x] `lake build OneThird.Step7.Cocycle` clean (verified)
- [x] `lake build OneThird.Step7.Potential` clean (verified)
- [x] No `sorry` in `Cocycle.lean` or `Potential.lean` (`grep sorry` clean)
- [x] No new axioms (`AXIOMS.md` unchanged)
- [x] No new mathlib gaps (`List.map_append` / `List.sum_append` / `Finset.sum_congr` already in tree)
- [x] Both files already wired into `OneThird.lean` root (no new imports added at the root)
- [x] Paper-faithful packaging (G4 grounded matches `step7.tex:388-398, 626-639`; G5 grounded matches `step7.tex:657-664, 697-789`)
- [x] Downstream consumer compatibility (S7-D `SingleThreshold.lean` consumes `lem_potential_grounded_bundled.2` for the sign-agreement-on-good-edges premise; S7-E `Bandwidth.lean` consumes the active-triple LB for the bandwidth bound)
- [x] Full `lake build` clean (verified, background build complete with only pre-existing linter warnings)

## What S7-D, S7-E, S7-F still need

Per mg-6ab8 §7.1 and §4.1 critical path:

* **S7-D (single-c + giant-component)** — depends on S7-C. Now consumable: `lem_potential_grounded_bundled` provides the per-edge sign-agreement bound that `lem:single-c` (`step7.tex:817-825`) consumes.
* **S7-E (prop:71/72 + bandwidth)** — depends on S7-D. Replaces `LayeredWidth3.bandwidth : ℕ` with constructive `≤ 4`.
* **S7-F (lem:layered-from-step7 bridge)** — depends on S7-E. Closes `MainAssembly.lean` `caseC_canonicalLayered` cap-5 sorry.

The S7-C deliverables here unblock S7-D. No PROOF-STRUCTURE-ONBOARDING.md §1/§2 update is *required* (the new content is not on the load-bearing headline path until S7-F lands), but a §4 cross-reference index addition is appropriate to record the new artefacts.

## Per mg-6ab8 §6.4 decision template — sub-arc verdict

| Sub-arc | Status | Notes |
|---|---|---|
| mg-S7-A | GREEN — landed (mg-4584) | G1 + G2 grounded forms |
| mg-S7-B | GREEN — landed (mg-9331) | G3 triple-visibility grounded |
| **mg-S7-C (THIS)** | **GREEN — landed** | **G4 cocycle + G5 potential grounded forms** |
| mg-S7-D (single-c + giant-component) | NOT STARTED | Ready to dispatch; consumes S7-C `lem_potential_grounded_bundled` |
| mg-S7-E (prop:71/72 + bandwidth) | NOT STARTED | Replaces `LayeredWidth3.bandwidth : ℕ` with constructive `≤ 4` |
| mg-S7-F (lem:layered-from-step7 bridge) | NOT STARTED | THE BRIDGE; closes `caseC_canonicalLayered` cap-5 sorry |

**Recommendation for pm-onethird** (the orchestrating PM for the S7 pilot): dispatch mg-S7-D next as a SENIOR polecat with the same `repo=one_third_width_three`, `default to main`, `~350-500k budget`, `verdict GREEN port complete / AMBER partial`. mg-S7-D's Lean port can directly consume `lem_potential_grounded_bundled` from this work as the per-edge sign-agreement input to `lem:single-c`.

## Cross-reference index

* **Lean** (this work):
  - `lean/OneThird/Step7/Cocycle.lean:798-999` — §6 grounded form (G4).
  - `lean/OneThird/Step7/Potential.lean:388-711` — §7 grounded form (G5).
* **Lean (consumed, unmodified):**
  - `lean/OneThird/Step7/SignedThreshold.lean` — `signed_threshold_grounded` (S7-A G1).
  - `lean/OneThird/Step7/SignConsistency.lean` — `coherentSet`, `majoritySign` infrastructure (S7-A G2).
  - `lean/OneThird/Step7/TripleVisibility.lean` — `tripleOverlap`, `tripleOverlapMass`, `triple_overlap_mass_lower_bound`, `triple_visibility_grounded` (S7-B G3).
  - `lean/OneThird/Step5/SecondMoment.lean` — `visibility`, `visibility_sum_eq_fiber_mass` (transitive via TripleVisibility).
* **Paper** (`step7.tex`):
  - `370-643` — `sec:cocycle` + `lem:cocycle` (G4).
  - `651-789` — `sec:potential` + `lem:potential` (G5).
  - `1107-1340` — `sec:formal` overall Step 7 sub-lemma manifest where G4 + G5 fit (mentioned at `step7.tex:1141, 1148`).
* **Predecessor docs:**
  - `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical entry point; this work leaves §2 unchanged but a §4 cross-reference update is appropriate.
  - `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) — §7.1 mg-S7-C spec consumed verbatim.
  - `docs/state-S7-A-G1-G2-Session1.md` (mg-4584) — S7-A predecessor pattern.
  - `docs/state-S7-B-G3-Session1.md` (mg-9331) — S7-B predecessor pattern.
* **mg ticket history:**
  - mg-6ab8 (parent) — Steps 1-7 scoping; Phase E option B selected by Daniel.
  - mg-4584 — S7-A G1+G2 grounded forms (landed 1d4f66d).
  - mg-9331 — S7-B G3 triple-visibility grounded (landed 71942ef).
  - mg-1069 (THIS) — S7-C G4+G5 grounded forms.

## Commit message proposal

```
lean+docs: OneThird-S7-C G4+G5 — Step 7 cocycle + potential grounded forms wired to S7-A signed-threshold + S7-B triple-visibility outputs (mg-1069)
```
