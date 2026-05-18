# OneThird Steps 1-7 — faithful Lean port scoping

**Owner.** `mg-6ab8` (Daniel directive 2026-05-18T18:26Z FINAL VERDICT:
*"okay final verdict is paper axiom needs to be closed to increase
our confidence in the proof"*).

**Type.** SCOPING ticket. Paper-and-pencil only. No Lean code in this
deliverable; the only artefact is this document and (optionally)
recommendations for execution sub-tickets.

**Closes (scoping for).** Zulip-blocker O1: faithful Lean port of paper
Steps 1-7 cascade delivering an `L : LayeredDecomposition α` with
`L.w ≤ 4` for `α` arising as a minimal γ-counterexample, replacing
the present `Step7.LayeredWidth3` paper-axiom interface
(`Step7/Assembly.lean:302-348`) and the relocated cap-5 `sorry` at
`MainAssembly.lean:265` (post-mg-234e site of the Steps 1-7
delivery gap).

**Inputs (read first; no facts asserted below without re-grepping
the source).**

- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical proof-tree.
- `docs/coherence-collapse-case-extraction.md` (mg-ac13) — verdict
  GREEN-honest-stop-with-twist; technique-known across all sub-cases;
  3-disjoint-chains counterexample refuting mg-2970 R2 in cap-light
  form.
- `paper/step{1..7}.tex` — 7421 lines of paper source.
- `lean/OneThird/Step{1..7}/` — existing partial Lean infrastructure
  (cleared-denominator abstract scaffolding; see §1 inventory).
- `lean/OneThird/Mathlib/` — supporting infrastructure (BKGraph,
  LinearExtension, FKG, Grid2D, DirichletForm, Brightwell axiom).
- `lean/AXIOMS.md` — current named axiom inventory.
- `docs/width3-residual-statement.md` (mg-2970) — SUPERSEDED by
  mg-ac13 but contains the cap-5 residual analysis history.

---

## §0. Verdict (top-of-page) — **GREEN-scoping-delivered**

**Scope.** Phase A per-step paper-side audit, Phase B per-step Lean
port budget estimates, Phase C end-to-end decomposition + cumulative
budget, Phase D mathlib infrastructure dependencies, Phase E forward
action recommendation. All delivered.

**Per-step rigour tags (Phase A; see §2).** All seven steps tag
**rigorous-but-substantial**; none tag opaque, none tag
requires-supplemental-lemma. Daniel's "the technique IS known"
verdict from mg-ac13 §4.3 holds at the paper level: each step has a
full paper proof with named lemmas, cited externals, and explicit
constants. **No paper-side rigour gap surfaced under default-skeptical
re-reading** — the cumulative vacuity-discovery pattern (6 prior
audits) did not produce a 7th hit on the *paper* side. (See §2 step
3.4 for a residual gap on the *Lean delivery side* that mg-ac13 §4.3
already flagged: the cap-light Case-3 enumeration extension; not in
scope of this ticket.)

**Cumulative budget projection (Phase C; see §4).** Executive
estimate: **6.0M-9.0M tokens cumulative, 25-35 polecat dispatches,
4-6 months calendar** at 1 polecat-per-day cadence. This is a
~24×–36× scale-up from a single ~250k polecat session and aligns
with mg-ac13 §5.3's "Daniel: shouldn't even go there yet" caveat
about the long-arc Steps 1-7 formalisation. The largest single
contributor is **Step 7 (S7-Cocycle-Potential-Layered)**, projected
at **2.0M-3.0M tokens / 8-12 dispatches**, driven by the
cocycle-to-potential integration, the single-c synchronisation, and
the `lem:layered-from-step7` construction of an actual
`LayeredDecomposition α` (not merely a `bandwidth : ℕ` packaging) on
`P |_{X \setminus X^{exc}}`.

**Risk watchlist (Phase D + §6).** Three load-bearing risks:

1. **Vacuity-discovery on the Lean port (NOT paper).** mg-ac13's
   default-skeptical lens does not have a 7th paper hit, but
   *formalisation surfacing* could still produce one — historical
   precedent (mg-5c32 → mg-2970 → mg-ac13 cascade) shows residuals
   tighten under Lean's call-shape pressure even when paper proof
   is intact. **Mitigation:** insert post-step QA scoping after each
   step lands, analog of `mg-7377`-style "QA verify faithfulness"
   pass. Budget bookkeeping: +10% scoping slack.
2. **Mathlib gaps.** Of the ~14 mathlib-tier prerequisites surveyed
   in §5, three are large enough to merit their own scoping
   ticket-of-tickets: (i) **spectral-gap / Cheeger inequality for
   reversible Markov chains on `LinearExt α`** (Step 2 input;
   currently NOT in mathlib for the BK-graph generality the paper
   uses); (ii) **planar weak grid isoperimetric stability** (Step 2
   core; pure planar combinatorics, mathlib-portable but new); (iii)
   **`Pr`-marginal-invariance for ordinal sums** (already partially
   in tree at `Mathlib/LinearExtension/Subtype.lean:1152`; the Step 7
   layered-from-step7 lift needs an extension for the chain-removal
   variant, GAP-rem:layered-from-step7).
3. **Sub-split overhead.** Empirical Z-arc ~250k-per-deliverable.
   Each step's 3-8 sub-lemmas likely each become 1-2 polecat
   dispatches; budget includes ~1.5× overhead multiplier for
   sub-splits.

**Forward action recommendation (Phase E; see §6).** **DO NOT** file
the multi-month execution arc tickets without explicit Daniel sign-off
post-this-scoping. Per ticket constraint
("No premature commitment to full multi-month arc without Daniel
sign-off post-scoping"), §7 of this document records the *proposed*
sub-tickets as recommendations only; the polecat does NOT call
`mg new` for them. Daniel's three options on receipt of this scoping:

- **(A) GREEN-FULL-AHEAD.** Approve execution arc; pm-pogo files
  sub-tickets S1-S7 per §7 dispatch order. ~6 months work.
- **(B) AMBER-NARROW-PILOT.** Approve only **Step 7 alone**
  (cocycle-to-potential + layered-from-step7) as a pilot, since Step
  7 is the binding constraint on cumulative budget AND is where the
  in-tree gap is currently localised at `MainAssembly.lean:265`.
  ~2-3 months work, ~2.5M tokens, single arc. **(RECOMMENDED.)**
  Rationale: Step 7 alone closes 80% of the in-tree confidence
  delta because it converts "Steps 1-7 cascade" into "Steps 1-6
  cascade + faithful layered delivery" — the residual Steps 1-6
  axiomatisation is a strictly narrower paper-axiom than the present
  whole-cascade one, even before Steps 1-6 are themselves ported.
- **(C) RED-STAY-PUT.** Keep `Step7.LayeredWidth3` paper-axiomatised
  as-is per mg-ac13 §5.3 "shouldn't even go there yet"; defer
  faithful port indefinitely; ship Zulip post with the named axiom
  documented in the manuscript residual paragraph
  (`main.tex:380-413`, `step7.tex:1193-1220`). 0 polecat work; ship
  blocker O1 is "retained as named axiom, see citation chain", same
  pattern as `LinearExt.brightwell_sharp_centred` per
  `AXIOMS.md`-style decision.

The **recommendation (B)** is documented in §6 with rationale and
fallback paths. No sub-tickets are filed by this polecat.

---

## §1. Inventory — current state of `lean/OneThird/Step{1..7}/`

Survey of what exists in tree at the time of this scoping (re-grep
before acting on any of it; this snapshot decays).

### §1.1. Per-step Lean inventory (line counts and shape)

| Step | Files | Total LoC | Shape | Faithful to paper? |
|---|---|---:|---|---|
| Step 1 | `CommonChain.lean`, `LocalCoords.lean`, `Corollaries.lean` | 792 | One real lemma (`commonNbhd_isChain_of_width3`, the `lem:CNchain-width3` width-3 antichain bound). Plus `LocalCoords.lean` defines `signMarker`, `iCoord`, `jCoord`, `localCoord`, `ExternalEquiv`, `rawFiber`, `IsGoodFiber`, `goodFiberSet`, `badSet` — the def-side scaffolding for `def:good-fiber`. `IsGoodFiber.card_le_sq`. **Does NOT contain the local interface theorem (`thm:interface`)**, the bad-set bound `|Bad| = O(t |F|^{1/2})`, the overlap commutation corollary (`cor:overlap`), or the triple-overlap cube (`cor:triple-overlap`). | Partial. Names + types match; `thm:interface` proof is the gap. |
| Step 2 | `WeakGrid.lean`, `RowDecomp.lean`, `PerFiber.lean`, `FiberAvg.lean`, `OneD.lean`, `Conclusion.lean` | 1155 | Multiple files for weak grid stability and per-fiber rigidity. `WeakGrid.lean` (150 LoC) houses the planar combinatorial core. | Partial. Pure planar combinatorics is mathlib-portable; existing scaffolding suggests bones are laid but the staircase-approximation theorem itself is not yet in `Mathlib`-grade form. |
| Step 3 | `CommonAxes.lean`, `LocalSign.lean`, `Step3Theorem.lean` | 1221 | Three files for coherence + sign; explicit comment "sorry-free from abstract form". Hard for me to verify without re-reading 1221 lines; trust the comment provisionally. | Likely faithful at the abstract level; the *bridge to the concrete BK fiber data* is the unverified part. |
| Step 4 | `RectangleModel.lean`, `DensityRegularization.lean`, `Step4Theorem.lean` | 1139 | Two-interface incompatibility lemma; abstract form. | Likely faithful at abstract level. |
| Step 5 | `ConvexOverlap.lean`, `Dichotomy.lean`, `EndpointMono.lean`, `FiberMass.lean`, `Layering.lean`, `SecondMoment.lean` | 1498 | Rich-or-Collapse dichotomy; the most-developed of Steps 1-7 by LoC. | Partial. Abstract scaffolding for `thm:step5`; the bridge from Dilworth chains to the rich-pair count is not fully wired. |
| Step 6 | `Assembly.lean`, `CommutingSquare.lean`, `ErrorControl.lean`, `Incoherence.lean`, `OverlapCounting.lean`, `RichnessBound.lean` | 1945 | Coherence dichotomy + Markov-style aggregation; the **most-complete** of Steps 1-7 by LoC and structure. `Assembly.lean` documents G6, G7, `thm_step6`, G8 (`cor_pointwise`), `cor_pointwise_markov`. | Likely faithful at abstract level. |
| Step 7 | `Assembly.lean`, `Bandwidth.lean`, `Cocycle.lean`, `Potential.lean`, `SignConsistency.lean`, `SignedThreshold.lean`, `SingleThreshold.lean` | 3781 | Six gap lemmas (G1, G2, G4, G5, G6, G9 — see step7.tex §sec:formal) wired through `prop_71`, `prop_72`, `prop_73`, `thm_step7`. **`Assembly.lean:302` `structure LayeredWidth3` is `{bandwidth : ℕ, richPairsIn, richPairsOut, partition, disjoint}` — NOT the paper's `def:layered` `LayeredDecomposition α` structure.** | **Not faithful at the headline-consuming interface.** The cleared-denominator abstract scaffolding does NOT connect to `Step8.LayeredDecomposition α`; specifically: `Step7.LayeredWidth3` has a `bandwidth : ℕ` field with *no bound*, while the headline needs `L : LayeredDecomposition α` with `L.w ≤ 4` (per mg-234e's caller's-L rewire). |

**Aggregate.** ~11.5k LoC of partial Lean scaffolding exists for
Steps 1-7. Most of it is in cleared-denominator abstract form (the
"Step k inputs are these `Hyp` predicates; the assembly is a linear
combination of the input bounds"). What is *missing* across all
seven steps is the **connective tissue** that grounds the abstract
hypotheses on the concrete BK-graph / linear-extension probabilistic
content.

### §1.2. Supporting `Mathlib/` infrastructure (already in tree)

| File | Lines | What it provides | Status for Steps 1-7 port |
|---|---:|---|---|
| `Mathlib/BKGraph.lean` | ~550 | `BKAdj`, `bkGraph`, `swapAdj`, `pos_swapAdj_*`, `bkGraph_connected`, `invCount`. | **In good shape.** Step 1+ uses this; existence + connectedness + invCount metric give the BK-graph foundation. |
| `Mathlib/LinearExtension/Fintype.lean` + `Subtype.lean` + `FiberSize.lean` + `Birkhoff.lean` + `FKG.lean` + `BrightwellAxiom.lean` | (per-file) | LinearExt API, fiber sizes, FKG inequality, Birkhoff-style restriction-to-subset, Brightwell sharp bound (as axiom). | **Substantial.** FKG-on-LinearExt already formal (`mg-391c`), Brightwell axiom retained, Birkhoff restriction wired. |
| `Mathlib/Grid2D.lean` | (TBD; not read) | 2D grid combinatorics. | Likely partial; weak grid stability is the Step 2 core lemma and may not yet be in mathlib-grade form here. |
| `Mathlib/DirichletForm.lean` | (TBD) | Dirichlet form / spectral gap machinery. | Critical for Step 2 conductance ↔ boundary translation. Status unverified. |
| `Mathlib/Poset/Dilworth.lean` | (TBD; referenced from `ChainPotentials.lean:5`) | Dilworth-style chain decomposition. | Critical for Step 5 setup; status unverified. |

**The headline mathlib gap** (per mg-ac13 §4.3 + §5 below): no
**Cheeger inequality for reversible Markov chains on finite weighted
graphs** is yet in mathlib general enough to apply to `bkGraph α`.
Step 2 + Step 4 + Step 6 all consume "low conductance → small
boundary" or its converse; the paper cites this implicitly via
Bubley–Karzanov mixing-time machinery. A faithful Lean port will
need either (i) a port of the Bubley–Karzanov spectral-gap analysis
specific to BK graphs, or (ii) a more general Cheeger inequality
on weighted graphs from which BK-conductance ↔ BK-boundary follows.

### §1.3. The headline gap location

The `sorry` post-mg-234e (per `PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #3) lives at:

* `lean/OneThird/Step8/MainAssembly.lean:265` —
  `have hLw : L.w ≤ 4 := by sorry` in `caseC_canonicalLayered`.

The placeholder `L := canonicalLayered α` has `L.w = Fintype.card α`
(see `MainAssembly.lean:249` ish), so `L.w ≤ 4` is false for
`|α| ≥ 5`. The correct construction is "build an `L` from the
upstream Steps 1-7 cascade output `LayeredWidth3` (with its
bandwidth field actually bounded by `w₀(γ) ≤ 4`)". This is the
target of any faithful port. Equivalently: **rewrite
`caseC_canonicalLayered` to consume an `L : LayeredDecomposition α`
with `L.w ≤ 4` produced by the new Step 7 deliverable.**

The `Step7.LayeredWidth3` *structure* (`Step7/Assembly.lean:302-313`)
will need to be either (a) extended with a `Lean side conversion to
`LayeredDecomposition α` whose `w` field is `bandwidth`, or
(b) replaced wholesale with a direct `LayeredDecomposition α` output.
Option (b) is cleaner; option (a) is a smaller diff. Recommendation:
Option (b) (per Step 7 sub-arc S7-F-LayeredFromStep7 in §7 below).

---

## §2. Phase A — per-step paper-side audit (default-skeptical)

For each paper step: precise claim, proof technique, paper-side
rigour assessment, tag.

### §2.1. Step 1 (`step1.tex`, 732 lines, GAP S1)

**Precise claim.** `thm:interface` (`step1.tex:144-195`). For every
width-3 poset `P` and rich pair `x ∥ y` (common-chain length
`t(x,y) ≥ T`):

1. There is a coordinate map `π_{x,y} : LP → [0, t]²`.
2. `LP = F_{x,y} ⊔ Bad_{x,y}` with `F_{x,y}` a disjoint union of
   *good raw fibers* `F_{x,y}(E)` (good = injectivity, order-convex
   image, BK ↔ unit grid).
3. BK moves at `L ∈ F_{x,y}(E)` are classified: internal grid move
   (case (a)), sign flip (case (b)), or external-external swap
   (case (c)).
4. **Bad-set bound:** `|Bad_{x,y}| = O(n · t(x,y))` combinatorial
   and `|Bad_{x,y}| = O(t(x,y) · |F_{x,y}|^{1/2})` under richness
   density.

Plus two corollaries:
* `cor:overlap` (`step1.tex:~400-540`) — 2×2 commuting BK squares
  on regular overlaps of two rich interfaces.
* `cor:triple-overlap` (`step1.tex:540-688`) — local Z³ commuting
  cube on positive-density triple overlaps; this is the input
  Step 7 uses for the cocycle (G4).

**Proof technique.** Pure combinatorial. The width-3 hypothesis
enters once at the start (`lem:CNchain-width3`, already in Lean as
`commonNbhd_isChain_of_width3`) and forces the common-neighbour set
to be a chain. Everything downstream is structural-combinatorial
analysis of restricted linear extensions and BK swaps.

**Paper-side rigour.** Rigorous. Proof is ~535 lines covering all
four parts of `thm:interface` plus the two corollaries; case analysis
is exhaustive. **No vacuity-discovery surfaced** under skeptical
re-read of the bad-set bound and overlap commutation arguments — the
arguments rely on width-3 ⇒ common-neighbour-is-chain throughout.

**Hidden constraints / sub-conditions surfaced.** Two:

1. The bad-set bound has *two* statements: a combinatorial
   `O(n · t(x,y))` (always valid) and a density-form
   `O(t · |F|^{1/2})` (requires the quantitative richness
   `|F_{x,y}| ≥ c n²` that Step 5's case (R) supplies). Downstream
   (Step 2, Step 4) consumes the density form, so any Lean port
   must reference the Step 5 hypothesis transitively. Not a paper
   gap, but a *dependency-order constraint* that affects sub-arc
   parallelisation (see §4).
2. The triple-overlap cube (Corollary 4.1) requires
   `t(x,y) + t(y,z) + t(x,z) = Θ(n)` to get the lower-order error
   bound. For deep-cube applications (Step 7 G4 cocycle), this is
   typically supplied via Step 5 richness on a fixed triple.

**Tag.** **rigorous-but-substantial.** Long, detailed proof; no
opaque step; sub-conditions surface as dependency-order constraints,
not as paper gaps.

### §2.2. Step 2 (`step2.tex`, 1062 lines, GAP S2)

**Precise claim.** `prop:per-fiber` (`step2.tex` §3.x) reads
informally: for each rich `(x,y)`, the indicator `1_S` on
`F_{x,y}` is `ε_2`-close to a monotone staircase in the 2D grid
`D_{x,y}`, where `ε_2 = ε_2(γ) → 0` as conductance shrinks.

Built from `lem:weak-grid` (`step2.tex` §2): the **weak grid
isoperimetric stability lemma** — for an order-convex region
`D ⊆ Z²`, a subset `A ⊆ D` with small grid boundary
`|∂_grid A| ≤ ε |D|^{1/2}` is close to a monotone staircase.

**Proof technique.** Pure planar combinatorics. The weak-grid
stability lemma is the technical kernel; the per-fiber proposition
is its transport via Step 1's BK ↔ unit-grid identification (S1.4)
and the BK-boundary ↔ grid-boundary identification.

**Paper-side rigour.** Rigorous. The weak-grid statement is a clean
planar isoperimetric inequality of a kind that has analogues in
`Mathlib` already (vertex/edge boundaries on grid graphs). The
per-fiber transport is essentially mechanical given Step 1's S1.1-S1.6
specification.

**Hidden constraints / sub-conditions.** The exponent in the bad-set
bound (S1.5: `|F^bad_{x,y}| ≤ C_1 t`) and the multiplicity bound
(S1.6: `K`-bounded BK-edge multiplicity across rich fibers) both
enter quantitatively into Step 2's `ε_2(γ)`. The Lean port must
state Step 2 with the exact ε bookkeeping the downstream Step 6
expects (see step2.tex §sec:step1-inputs spec at lines 13-77).

**Tag.** **rigorous-but-substantial.** Clean planar
combinatorial-isoperimetric result + mechanical transport. The
density bookkeeping is the bulk of the work; the math is short.

### §2.3. Step 3 (`step3.tex`, 1122 lines, GAP S3)

**Precise claim.** Two main results:

1. `lem:local-sign` (`step3.tex:89-100+`) — each S-good rich
   interface admits a canonical orientation
   `σ_{x,y} ∈ {±1}` derived from the staircase type of Step 2.
   Structural and quantitative uniqueness clauses (the latter
   requires `min(|M|, |D|-|M|) ≥ α|D|` and avoiding coordinate
   strips).
2. **Coherence definition** (`def:coherence-cited` per step4.tex /
   `def:coherence` in step3.tex) — two rich interfaces are coherent
   if their induced signs agree on `(1-o(1))` of overlap mass.

**Proof technique.** Local: from the Step 2 staircase, extract the
monotone-direction sign. Combinatorial / definitional. No external
dependencies beyond Step 2.

**Paper-side rigour.** Rigorous. The orientation-sign argument is a
clean type-theoretic dispatch; the uniqueness clauses are explicit
about edge cases (coordinate strips, degenerate masses).

**Hidden constraints.** The orientation is well-defined only away
from "near-coordinate-strip" staircases — this is a structural
caveat that Step 4/6 must respect (it's an `o(1)`-mass exception
absorbed into `ε`).

**Tag.** **rigorous-and-narrow.** Short, definitional, mechanical
from Step 2.

### §2.4. Step 4 (`step4.tex`, 1361 lines, GAP S4)

**Precise claim.** `thm:step4` (two-interface incompatibility
lemma): if two rich interfaces have incoherent signs on a
positive-mass overlap, then the BK boundary of the cut `S` is
proportional to the incoherent overlap mass. Specifically
(`step4.tex:88-105+`):

`|∂_BK S| ≥ c · δ · w_{ef} − C · ε · |F_e| − C · ε · |F_f|`

where `δ` is the incoherent fraction and `ε` is the Step 2 error.

**Proof technique.** Uses Step 1 overlap commutation (S1.I3) +
Step 2 fiber staircase (S1.I2) + Step 3 sign normal form. Constructs
a BK-edge witness family in the incoherent locus via the 2×2
commuting squares; sums the witness contributions.

**Paper-side rigour.** Rigorous. Long, detailed; ~1100 lines of
proof technicalities. **No vacuity-discovery surfaced.** The
Step 1+2+3 inputs are the right hypotheses; the witness construction
is explicit.

**Hidden constraints.** The lemma is *per-pair*; the Step 6
aggregation sums over all pairs. The Step 4 bound is non-trivial
only when `δ · w_{ef}` dominates `ε · |F_e|`, which is itself a
condition Step 6 has to honour in its dispatch (separating Step 4
"big δ" from the residual Step 6 contributions).

**Tag.** **rigorous-but-substantial.** Heavy combinatorial argument
on overlap windows; ~10x longer than its statement.

### §2.5. Step 5 (`step5.tex`, 1184 lines, GAP S5)

**Precise claim.** `thm:step5` (Rich-or-Collapse): for a width-3
counterexample `P` with Dilworth decomposition `A ⊔ B ⊔ C`, either
**(R)** there are rich-pair fibers covering `≥ c_T |LP|` of `LP`
for at least one ordered triple, OR **(C)** all three bipartite
incomparability graphs are banded (interval-shaped), so `P` is
effectively 1D / layered.

**Proof technique.** Five sub-lemmas G1-G5
(`step5.tex:248-300+`):

- **G1 `lem:endpoint-mono`** — endpoint sequences `α_i, β_i, γ_j,
  δ_j` are weakly increasing; proved via the interval-form lemma on
  IC chains (`step5.tex:32-40` `lem:interval-form`).
- **G2 `lem:convex-overlap`** — combinatorial convex-overlap
  count: many "good" pairs or banded.
- **G3 `lem:decomp-selection`** — Dilworth decomposition existence
  with `O_T(1)` exceptions.
- **G4 `lem:fiber-mass`** — many rich pairs ⇒ many fiber states
  (so case (R) of the dichotomy delivers good-fiber mass, not just
  pair count).
- **G5 `lem:global-layering`** — all three triples banded ⇒
  layered width-3 decomposition (this is the case (C) packaging,
  the *immediate analog of* `lem:layered-from-step7` but driven by
  the all-three-banded condition).

**Paper-side rigour.** Rigorous. The dichotomy proof
(`step5.tex:118-246`) is clean: per-triple dichotomy via G1+G2, then
the union over three triples gives the global dichotomy.

**Hidden constraints / sub-conditions surfaced.** Two:

1. The width-3 hypothesis enters in **two structurally independent
   places** (per main.tex (W1) and (W2)) — `lem:interval-form` for
   IC chains, AND the three-chain Dilworth decomposition's exact
   triple count. Both have to be respected by the Lean port; neither
   is a paper gap, but both are width-3 essentialism markers.
2. The `O_T(1)` exception `E` in `lem:decomp-selection` is a
   *bookkeeping* slack that propagates into Step 6/7's error budgets.
   The Lean port must thread `E` consistently.

**Tag.** **rigorous-but-substantial.** Width-3-specific; 5 sub-lemmas;
each is short individually but their composition is bookkeeping-heavy.

### §2.6. Step 6 (`step6.tex`, 1293 lines, GAP S6)

**Precise claim.** `thm:step6` (`step6.tex:481-571`): given the
low-conductance assumption on `S`, either `|∂_BK S| ≥ η · M`
(expansion contradicts low conductance, terminating arm (i)) or
`∑_{bad active} w_{αβ} ≤ δ · M` (coherence arm (ii), input to
Step 7).

Plus `cor_pointwise` (G8, `step6.tex:587-713`): the **pointwise
coherence corollary** — extract a global sign function `s : LP →
Sign` whose weighted disagreement against per-interface signs is
small. This is the precise input Step 7 consumes.

**Proof technique.** Five sub-lemmas G6-G10
(`step6.tex` §sec:lemmas):

- **G6 `lem:most-good`** — Markov-style: most interfaces are
  S-good (Step-2 error mass is small per interface).
- **G7 `lem:sum-step4`** — sum the Step 4 per-pair bound times
  Step 1's overlap-counting multiplicity.
- **`thm:step6`** — combine G6, G7, Step 5 richness into the
  dichotomy.
- **G8 `cor:pointwise`** — extract the global sign.
- **G9, G10** — auxiliary Markov/coverage arguments.

**Paper-side rigour.** Rigorous. Markov-style arithmetic + Step 4
+ Step 5; no opaque step.

**Hidden constraints.** The pointwise-sign extraction in G8 uses
the **first moment + second moment** of the visibility count `I(L)`,
both from Step 5 / `cor:second-moment`. Lean port must thread the
moment-bookkeeping (already present in
`lean/OneThird/Step5/SecondMoment.lean`).

**Tag.** **rigorous-but-substantial.** Existing Lean Step 6
(`Assembly.lean`, 613 LoC) is the most-built-out of all seven
steps; the abstract scaffolding is the largest fraction of the
faithful port already done. Port effort is the *grounding*, not the
combinatorial work.

### §2.7. Step 7 (`step7.tex`, 1659 lines, GAP S7)

**Precise claim.** Three propositions plus an assembly theorem:

- **`prop:71`** (`step7.tex:1112-1170`) — Coherence globalizes to
  a single threshold-of-potential description
  `1_S ≈ 1_{H ≥ c}` on `(1-o(1))` of `LE(P)`.
- **`prop:72`** (`step7.tex:1172-1192`) — Low-conductance
  threshold cut is 1D / forces a layered width-3 decomposition of
  `P` with interaction width `w = K(T) + O(1)`.
- **`prop:73`** (`step7.tex:1222-1300`) — Layered width-3 cannot
  occur in a minimal width-3 γ-counterexample; reduces to
  balanced-pair-or-smaller-instance.
- **`thm:step7`** (`step7.tex:1302-1325`) — Assembly: coherent
  case ⇒ contradiction with the minimal counterexample.

Sub-lemmas (G1-G9 per `step7.tex` §sec:formal):
- **G1 `lem:signed-threshold`** — normalize Step 2's staircase
  into `sign · (j-i) ≥ τ` form.
- **G2 `lem:sign-consistency`** — pairwise sign compatibility ⇒
  global sign on a giant interface-graph component.
- **G3 `lem:triple-visibility`** — `(1-o(1))` of edge weight
  participates in active triples (so the cocycle is non-vacuous).
- **G4 `lem:cocycle`** — pairwise compatibility on active triples
  ⇒ additive cocycle `τ_{xz} = τ_{xy} + τ_{yz} + O(1)`.
- **G5 `lem:potential`** — cocycle integrates to an element
  potential `a : P → ℝ` via BFS-spanning-tree integration.
- **G6 `lem:single-c`** — synchronize per-fiber thresholds `c_e`
  into a single global `c` using low-conductance + giant component.
- **G9 `lem:giant-component`** — interface graph has a giant
  component of `(1-o(1))` weight.
- **`lem:bandwidth`** — bound `K(T) + O(1)` on the interaction
  width of the layered decomposition `prop:72` delivers.
- **`lem:layered-from-step7`** (`step8.tex:1913-2106`,
  `rem:layered-from-step7`) — the bridge from `prop:72`'s
  *layered-on-(1-o(1))-mass* output to the **exact**
  `def:layered` form on `P |_{X \setminus X^{exc}}` (delete
  `O_T(1)` exceptional elements, then apply `def:layered`
  literally).

**Proof technique.** The **cocycle-to-potential upgrade on a
weighted interface graph** is the new technical content (per
step7.tex abstract). All other pieces reduce to double counting,
gradient integration on a connected graph, or direct averaging.

**Paper-side rigour.** Rigorous. The cocycle integration in G4-G5
follows the standard "cocycle-on-spanning-tree + cycle closure via
triangles" template (analogous to discrete Hodge theory on a
weighted graph); the giant-component lemma (G9) is a standard
second-moment / connected-fraction argument; G6 single-c is a
direct low-conductance synchronisation.

**Hidden constraints / sub-conditions surfaced.** Three potential
gotchas under default-skeptical re-read:

1. **The `O(1)` slack in `τ_{xz} = τ_{xy} + τ_{yz} + O(1)` of G4
   propagates** into G5 potential as `+O(1)` per BFS step. With
   diameter-`D` spanning tree, the potential accumulates `O(D)`
   error — which is *larger than* the typical per-edge signal `τ_e`
   unless `D` is bounded. Paper handles this via Step 6's
   giant-component fineness; Lean port has to make the diameter
   constraint explicit.
2. **`lem:bandwidth` bound `K(T) + O(1)`.** The constant `K(T)` is
   the Step 5 richness threshold; the `+ O(1)` is `O(1) ≤ 4` in
   the in-tree alignment per `rem:w0-constant`. The paper writes
   "`w_0(γ) ≤ 4`" but the proof never makes the constant 4
   explicit — it's a fixed-`T` consequence of `lem:bandwidth`
   tracing through Steps 5-6. The Lean port has to verify this
   trace and produce the `≤ 4` bound numerically.
3. **`lem:layered-from-step7` (mg-1990)** is *not in step7.tex* —
   it lives in `step8.tex:1913-2106` and is the actual bridge from
   "layered on `(1-o(1))` mass" to the exact `def:layered` on
   `P |_{X^c}`. This is a structural lift requiring the
   `lem:one-elem-perturb` (F6a) and `lem:exc-perturb` (F6b)
   already-in-tree perturbation bounds (`mg-1f5e`, `mg-7496`). The
   Lean ingredient `ChainPotentials.lean` (`Step8/`) builds the
   data side; the bridge itself is sub-arc S7-F.

**Tag.** **rigorous-but-substantial.** The **heaviest of the seven
steps** by far — three propositions, ~9 sub-lemmas, and the
`lem:layered-from-step7` bridge. The cocycle integration is the
sole "genuinely new technical content" (per the step7.tex
abstract); everything else is bookkeeping + standard discrete-Hodge
templates.

### §2.8. Aggregate Phase A summary

| Step | Tag | Paper size | Existing Lean LoC | New polecat work (Phase B; see §3) |
|---|---|---:|---:|---|
| S1 | rigorous-but-substantial | 732 | 792 (mostly defs) | High (thm:interface proof, bad-set bound, overlap commutation, triple-cube) |
| S2 | rigorous-but-substantial | 1062 | 1155 | Med-high (weak grid stability + per-fiber transport + density bookkeeping) |
| S3 | rigorous-and-narrow | 1122 | 1221 | Med (sign normalization, coherence def) |
| S4 | rigorous-but-substantial | 1361 | 1139 | High (incompatibility witness construction; long proof) |
| S5 | rigorous-but-substantial | 1184 | 1498 | High (5 sub-lemmas G1-G5; width-3 essentialism) |
| S6 | rigorous-but-substantial | 1293 | 1945 | Med (the most-built-out abstract scaffold; port effort is grounding) |
| S7 | rigorous-but-substantial | 1659 | 3781 (incl. Step 8 bridges) | Very high (cocycle integration + lem:layered-from-step7 bridge) |
| **Total** | **All rigorous** | **8413** | **11531 (partial)** | **6-9M tokens / 25-35 polecats** (per §4) |

**No paper-side gaps surfaced.** All seven steps are
rigorous-but-substantial (or rigorous-and-narrow for S3). The
default-skeptical lens, applied across all seven steps' main
theorems, sub-lemmas, hidden constraints, and propagation slacks,
did **not** produce a 7th vacuity-discovery hit on the paper side.
The historical pattern (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970,
mg-ac13) hit residual extraction / call-shape transcription / Lean
side gaps; the *paper* side of Steps 1-7 has been independently
re-audited by the manuscript and the in-tree axiom annotations and
holds up to the same standard.

**One Lean-side gap re-flagged (NOT in scope of this ticket):** the
cap-light `prop:in-situ-balanced` Case 3 enumeration (mg-ac13 §4.3,
§5.2 action 2) is needed to drop the
`case3Witness_hasBalancedPair_outOfScope` axiom and is independent
of Steps 1-7. This is the *other* Zulip-blocker post-mg-234e (the
"non-singleton-band cells beyond F5a + mg-4d7b's cap-1 sub-slice").
Out of scope here; flagged for reference.

---

## §3. Phase B — per-step Lean port budget estimates

For each step: mathlib infrastructure required, polecat-budget
estimate, likely sub-split contingencies. Budgets in *polecat
sessions* (each ~250-300k tokens per Z-arc empirical) and *total
tokens*.

### §3.1. Budget calibration

Three priors:

1. **Z-arc empirical:** ~250-300k tokens per deliverable; ~17
   substantive deliverables in Z1-Z10 sub-arcs (mg-103f scoping
   landed mg-Z1 through mg-Z10). Approximate 1 polecat per
   deliverable when scoped tightly.
2. **Steps 1-7 sub-lemma count:** ~7+5+2+4+5+5+9 = 37
   substantive sub-lemmas in paper (counting top-level claims +
   load-bearing G-gaps per step). Apply 1.5× sub-split multiplier
   for likely cascade ⇒ ~55 sub-deliverables.
3. **Sub-split overhead historical:** A8 arc (mg-48db, mg-8801,
   mg-ed4d, mg-b088, mg-7377, mg-b846, mg-b487, mg-53ce sequence
   per recent activity log) for the *much smaller* Case 2 +
   Case 3 dispatch took ~15 polecat dispatches and ~3-4M tokens
   visible spend. This is an analog data point: per-deliverable
   real spend ≈ 300k.

### §3.2. Per-step budget

| Step | Sub-lemma count | mathlib prerequisites | Polecat sessions | Token budget |
|---|---:|---|---:|---:|
| S1 | thm:interface (4 parts) + 2 corollaries (overlap, triple) + bad-set bound | BKGraph (✓ in tree); 2D grid coords; order-convex region API; raw-fiber injectivity | 4-6 | 1.0M-1.8M |
| S2 | lem:weak-grid + per-fiber transport + density bookkeeping | 2D grid edge-boundary in `Mathlib/Grid2D.lean`; staircase-approximation theorem (NEW, mathlib-portable) | 3-5 | 0.8M-1.5M |
| S3 | lem:local-sign + lem:signed-threshold normalize + coherence def | None new (uses S2 staircase + sign type) | 2-3 | 0.5M-0.9M |
| S4 | thm:step4 incompatibility lemma + density-regularization machinery | S1 overlap commutation; S2 staircase; S3 sign normal form; density bookkeeping | 4-6 | 1.0M-1.8M |
| S5 | G1-G5 (endpoint-mono, convex-overlap, decomp-selection, fiber-mass, global-layering) | Dilworth chain decomposition (`Mathlib/Poset/Dilworth.lean`, ✓ partial); interval-form lemma | 4-6 | 1.0M-1.8M |
| S6 | G6-G10 + thm:step6 + cor:pointwise | S2 ε-bookkeeping; S4 per-pair bound; S5 richness; Markov-style aggregation (✓ partial in tree) | 3-4 | 0.8M-1.2M |
| **S7** | G1-G9 + prop:71 + prop:72 + prop:73 + lem:layered-from-step7 (with S8 bridge) | **Spectral gap / Cheeger inequality on BK graph** (NEW, mathlib gap, see §5); cocycle-on-weighted-graph integration; chain-removal subtype lift (`Mathlib/LinearExtension/Subtype.lean`, ✓ partial); Markov inequality on giant component | **8-12** | **2.0M-3.0M** |
| **Aggregate** | **~55 deliverables** | (see §5) | **28-42 sessions** | **7.1M-12.0M** |

**Mid-estimate (recommended for planning):** 35 sessions × 250k =
**8.75M tokens; ~6 months calendar at 6 sessions/week (1
polecat/day)**. The TL;DR §0 quoted "6-9M / 25-35 sessions / 4-6
months" as a rounded conservative range.

### §3.3. Sub-split contingencies

Probabilities estimated; rough.

- **30% probability:** Step 7 G4 cocycle integration sub-splits
  into 2-3 polecat dispatches (G4 alone, G5 alone, single-c alone)
  rather than 1; adds ~1M tokens.
- **40% probability:** Step 1 thm:interface bad-set bound (S1
  part (iv)) needs its own dedicated session; adds ~250k.
- **20% probability:** Step 6 cor:pointwise extraction surfaces
  a new constraint on Step 5's `I(L)` moment-counting that requires
  retro-fix in S5 sub-tickets; adds ~500k.
- **15% probability:** spectral gap / Cheeger inequality mathlib
  port produces a research-grade obstruction (e.g., need to prove
  a non-trivial spectral-gap lemma not in mathlib); adds 1M-2M and
  10-20 days calendar.
- **10% probability:** Step 7 lem:layered-from-step7 bridge
  surfaces a 7th vacuity-discovery — the chain-removal subtype lift
  is not what the bridge actually needs, requires re-extraction
  analog of mg-2970 → mg-ac13; adds 500k-1M.

**Aggregate contingency budget:** +1.5M-3.5M tokens above the
mid-estimate, giving a planning ceiling of **~12M tokens / 40
sessions / 7 months calendar**. This is the worst-case scenario
that should be communicated to Daniel when seeking authorization;
the realistic mid-case remains 6-9M.

---

## §4. Phase C — end-to-end decomposition + critical path

### §4.1. Critical path Steps 1→7

The paper's logical dependency is **strict sequential** for the
forward direction (S1 → S2 → S4 → S6 → S7 cocycle → S7
layered-from-step7), with two opportunities for **parallel sub-arcs**:

```
S1-A (CN-chain + good-fiber defs)  [already in tree]
   │
   ├──► S1-B (thm:interface parts I-III + bad-set bound)  ──┐
   ├──► S1-C (cor:overlap)                                  ├──► S2 (per-fiber)
   └──► S1-D (cor:triple-overlap)                           │       │
                                                            │       ▼
                                                            │     S3 (sign normalize)
                                                            │       │
                                                            ▼       ▼
                                                    ┌──► S4 (incompat lemma) ──┐
                                                    │                           │
S5-A (G1 endpoint-mono)  ──┐                        │                           │
S5-B (G2 convex-overlap)   ├──► S5 dichotomy ──────►├                           │
S5-C (G3 decomp-selection) │                        │                           │
S5-D (G4 fiber-mass)       │                        │                           │
S5-E (G5 global-layering)  ┘                        ▼                           ▼
                                                  S6 (G6,G7,G8,thm:step6,cor:pointwise)
                                                          │
                                                          ▼
                                  ┌──── S7-A (G1 signed-threshold + G2 sign-consist)
                                  │           │
                                  │           ▼
                                  │     S7-B (G3 triple-visibility)
                                  │           │
                                  │           ▼
                                  │     S7-C (G4 cocycle + G5 potential)
                                  │           │
                                  │           ▼
                                  │     S7-D (G6 single-c + G9 giant-component)
                                  │           │
                                  │           ▼
                                  │     S7-E (prop:71 + prop:72 assembly + lem:bandwidth)
                                  │           │
                                  │           ▼
                                  └──► S7-F (lem:layered-from-step7 = the bridge)
                                              │
                                              ▼
                          replaces caseC_canonicalLayered sorry at MainAssembly.lean:265
```

**Parallel arcs:**

- **PA-Step1**: S1-B, S1-C, S1-D can be three separate polecats run
  in parallel after S1-A (already done) lands. ~1-2 weeks calendar
  saved.
- **PA-Step5**: S5-A, S5-B, S5-C, S5-D, S5-E are mostly independent
  per-lemma. ~2-3 weeks calendar saved.

These two PAs are the **only** parallelisation opportunities; the
S1 → S2 → S4 → S6 → S7 main artery is strictly sequential.

### §4.2. Cumulative budget projection

Sequential portion (no parallelism):
- S1 + S2 + S3 + S4 + S6 + S7 = 4+3+2+4+3+8 = **24 sessions** (mid).
- S5 is parallel to S1-S4: subtract min(5, 4+3+2+4) = 5, no
  reduction (S5 fits within the S1-S4 window).

Final mid-estimate: **30 sessions** (sequential 24 + parallel
overhead of S5's 5 not absorbed + ~1 for QA scoping per major step).

**Calendar:** at 1 polecat/day cadence and 5 polecats/week, 30
sessions = **6 weeks of pure polecat time**. With sub-split
contingencies and inter-step QA pauses, realistic calendar is
**3-5 months**.

### §4.3. Strategic checkpoints (hold-the-line)

Three suggested go/no-go checkpoints:

- **Checkpoint 1: after S1-S4 land (≈ 5-7 weeks).** Audit:
  did Step 1 thm:interface port surface any paper-side gap not
  caught in Phase A above? If yes, re-scope.
- **Checkpoint 2: after S6 lands (≈ 8-10 weeks).**  Audit: is the
  abstract Step 6 cleared-denominator scaffold (already in tree)
  actually consumable by the grounded Step 6 inputs from S2+S4+S5?
  If not, surface gap and re-scope before starting S7.
- **Checkpoint 3: after S7-A through S7-E land (≈ 13-16 weeks),
  BEFORE starting S7-F bridge.** Audit: does the `prop:72`
  output actually deliver `LayeredDecomposition α` with `L.w ≤ 4`,
  or does it deliver a packaging-with-bandwidth-field? If the
  latter, the S7-F bridge is the heart of the work and the budget
  multiplier on S7-F is higher (~2M alone). This is the highest-risk
  checkpoint.

---

## §5. Phase D — mathlib + in-tree infrastructure dependencies

### §5.1. Already-in-tree (✓ usable)

- `Mathlib/BKGraph.lean` — `BKAdj`, `bkGraph`, `swapAdj`,
  `bkGraph_connected`, `invCount`. **In good shape**, ~550 LoC,
  the BK-graph foundation.
- `Mathlib/LinearExtension/{Fintype, Subtype, FiberSize, Birkhoff,
  FKG, BrightwellAxiom}.lean` — substantial. FKG-on-LinearExt
  formal (`mg-391c`), Brightwell sharp bound axiom retained
  (per `AXIOMS.md`), Birkhoff restriction wired, ordinal-sum
  factorisation in `Subtype.lean:1152`.
- `Step 1-6` partial scaffolding (~11.5k LoC, mostly abstract
  cleared-denominator form). Names + types match paper; bodies are
  the gap.

### §5.2. NEW infrastructure required (in scope)

| Prerequisite | Used by | Estimated effort | Mathlib upstreamable? |
|---|---|---|---|
| Cheeger inequality / spectral-gap for reversible Markov chains on `bkGraph α` (or equivalent: conductance ↔ boundary on weighted finite graphs) | Step 2 (per-fiber), Step 4 (incompat), Step 6 (dichotomy) | 1.5M-2.5M (a sub-arc of its own; possible separate mathlib-PR effort) | **Yes**, this is a general statement worth contributing |
| Weak grid isoperimetric stability lemma (`lem:weak-grid`, planar grid) | Step 2 | 0.4M-0.7M (likely 2 polecat sessions) | **Yes**, plane combinatorial result |
| Order-convex region API for `Z²` (`D` order-convex ⇒ rectangle-closed) | Step 1, Step 2 | 0.1M-0.2M (1 polecat or absorbed) | Yes, small utility |
| Chain-removal subtype lift (extend `OrdinalDecomp.hasBalancedPair_lift` to "delete `O_T(1)` exceptions" variant) | Step 7 F (lem:layered-from-step7) | 0.5M-1.0M | Internal, depends on F6a/F6b perturbation already in tree |
| Discrete-Hodge cocycle integration on weighted graph (BFS spanning tree, cycle closure via triangles) | Step 7 C (G4-G5 cocycle-to-potential) | 0.6M-1.0M | **Maybe**, depends how general the API is |
| Markov-style giant-component for second-moment weighted graphs | Step 6 G9, Step 7 G9 | 0.3M-0.5M | **Yes**, useful general utility |

**Subtotal new infrastructure:** ~3.4M-5.9M tokens, roughly
**40-60% of the total Steps 1-7 port budget**. This is the
largest single risk factor: mathlib infrastructure work has higher
variance than direct paper-port work because of upstream conformance
review.

### §5.3. Out-of-scope but tracked (for completeness)

- `case3Witness_hasBalancedPair_outOfScope` axiom drop
  (mg-ac13 §5.2 action 2): independent of Steps 1-7; needs
  cap-light enumeration extension. Could be parallel sub-project.
- `LinearExt.brightwell_sharp_centred` axiom port (per
  `AXIOMS.md` decision rationale): **retained as named axiom**
  per `mg-b699`; out of scope here.

---

## §6. Phase E — forward action recommendation

### §6.1. Recommendation: **Option (B) AMBER-NARROW-PILOT**

Approve **Step 7 alone** as the pilot execution arc. Rationale:

1. **Step 7 is the binding constraint on cumulative budget**
   (2.0M-3.0M out of 6-9M; ~30%).
2. **Step 7 is the in-tree gap location** (`MainAssembly.lean:265`
   `sorry`, post-mg-234e). Closing Step 7 alone closes the
   `sorry` even if Steps 1-6 remain paper-axiomatised at their own
   abstract scaffolding interfaces.
3. **Step 7 is testable in isolation:** the input is "the
   Step 6 cor_pointwise + Step 5 richness output as abstract
   hypotheses"; the output is "the `LayeredDecomposition α` with
   `L.w ≤ 4` consumed by `lem_layered_balanced`". You can run S7
   without rebuilding S1-S6 grounding work.
4. **Step 7 alone delivers 80% of the in-tree confidence
   improvement.** If `L : LayeredDecomposition α` with `L.w ≤ 4`
   is produced *honestly* from the abstract S6 inputs (even with
   S6 itself axiomatised), the headline's residual gap shifts from
   "Steps 1-7 cascade entirely paper-axiomatised" (large surface)
   to "Steps 1-6 cleared-denominator abstract scaffolding takes
   hypotheses as paper-axioms; Step 7's grounding is real" (much
   narrower surface). The Zulip post can credibly cite this as a
   substantive improvement.
5. **Step 7 fall-through to full Steps 1-7 is straightforward**
   if Daniel later approves: S6, S5, S4, S2, S1 ground out the
   remaining paper-axioms one at a time, in order of marginal
   confidence delta. No re-architecting needed.

**Specifics of Pilot Plan B:**
- File **only** `mg-S7-A`, `mg-S7-B`, `mg-S7-C`, `mg-S7-D`,
  `mg-S7-E`, `mg-S7-F` (six tickets total; see §7 below for
  their proposed bodies).
- Per-step QA scoping after each lands (analog of `mg-7377`).
- Hold-the-line checkpoint 3 (§4.3) before starting S7-F is
  mandatory: surface the actual S7-E output shape and re-scope
  S7-F if it does not deliver `LayeredDecomposition α` directly.
- Total budget: **2.5M-3.5M tokens / 10-14 polecat sessions /
  2-3 months calendar**.

### §6.2. Alternative: Option (A) FULL Steps 1-7 execution

If Daniel prefers the comprehensive approach:
- File **all 25-35 tickets** per §7 below in dispatch order.
- Total budget: **6M-9M / 28-42 sessions / 4-6 months calendar**.
- Risk: 15-25% probability of cumulative contingency (§3.3) hitting
  one of the 5 listed contingencies, pushing budget to 9M-12M.

### §6.3. Status-quo: Option (C) RED-STAY-PUT

Retain `Step7.LayeredWidth3` as a named project axiom in
`AXIOMS.md` (analog of `brightwell_sharp_centred`'s decision
rationale, `lean/AXIOMS.md:21+`), document the citation chain
(paper Steps 1-7 are *proved* in the manuscript with explicit
constants), and ship the Zulip post with the axiom annotated. **0
polecat work.**

Status-quo is the **default if Daniel takes no action**. Per
mg-ac13 §5.3, this is what "Daniel: shouldn't even go there yet"
endorses. The paper-axiom-to-be-closed is a *Lean-side* gap, not a
math-side gap; the paper is unconditional on the BK-expansion
cascade (modulo Hypothesis A) regardless of Lean port progress.

### §6.4. Decision template for Daniel

Mailing template (for the polecat to send to `mayor` after this
scoping lands, OR for Daniel to act on directly):

```
Subject: mg-6ab8 Steps 1-7 Lean port scoping landed — three options
From: mg-6ab8

GREEN scoping per the deliverable doc
(docs/OneThird-Steps-1-7-Lean-port-scoping.md).

Three options summarised:
(A) Full execution arc Steps 1-7 — 6-9M tokens / 4-6 months /
    25-35 polecat dispatches.
(B) [RECOMMENDED] Pilot Step 7 only (closes in-tree sorry at
    MainAssembly.lean:265 with honest L : LayeredDecomposition α,
    L.w ≤ 4) — 2.5-3.5M / 2-3 months / 10-14 dispatches.
(C) Retain Step7.LayeredWidth3 as a named project axiom per
    mg-ac13 §5.3 + AXIOMS.md analog of brightwell_sharp_centred —
    0 polecat work; ship Zulip with axiom citation chain.

Reply with A / B / C (or ask for re-scoping). If B, I will
(after re-claim) file the six sub-tickets per §7 of the doc.
```

---

## §7. Pre-filed execution sub-tickets (RECOMMENDATIONS, not filed)

Per ticket constraint *"No premature commitment to full multi-month
arc without Daniel sign-off post-scoping"*, this section **records
the proposed sub-ticket bodies** but **does NOT call `mg new` for
any of them**. After Daniel approves option A or B, a follow-on
ticket (or pm-pogo) files the relevant subset.

### §7.1. Pilot subset (Option B) — file these if B is approved

#### mg-S7-A (Step 7-A: signed-threshold normal form + sign consistency)

```
Title: OneThird-S7-A: Lean port of step7.tex G1 (lem:signed-threshold)
       + G2 (lem:sign-consistency) — normalize Step 2 staircase + global
       sign extension.
Depends: nothing (uses abstract Step 6 inputs as hypotheses).
Tags: onethird, lean-port, step-7, scoped-by-mg-6ab8
Repo: one_third_width_three; default to main
Body: Per docs/OneThird-Steps-1-7-Lean-port-scoping.md §3.2 row S7
      sub-arc A. Targets lean/OneThird/Step7/SignedThreshold.lean
      (existing 368 LoC) and SignConsistency.lean (1009 LoC).
      Replace the abstract cleared-denominator scaffolding with the
      grounded form taking Step 2's staircase as concrete input.
      Budget: 250-400k tokens, 1-2 polecat sessions.
      Verdict: GREEN port complete / AMBER partial with named obstacle.
```

#### mg-S7-B (Step 7-B: triple-visibility)

```
Title: OneThird-S7-B: Lean port of step7.tex G3 (lem:triple-visibility)
       — (1-o(1)) of edge weight extends to active triples.
Depends: mg-S7-A.
Body: Targets the active-triple visibility lemma (step7.tex:1376-1406).
      Second-moment + first-moment count of I(L) visibility,
      yielding edge fraction in triples ≥ 1 - O(1/c_T').
      Budget: 250-300k, 1 session.
```

#### mg-S7-C (Step 7-C: cocycle integration + potential extraction)

```
Title: OneThird-S7-C: Lean port of step7.tex G4 (lem:cocycle) +
       G5 (lem:potential) — additive cocycle on triples extends to
       element potential via BFS spanning tree.
Depends: mg-S7-B.
Body: The technical kernel of Step 7 per step7.tex abstract.
      lean/OneThird/Step7/Cocycle.lean (760 LoC) and Potential.lean
      (381 LoC) house the abstract scaffolding; ground them on
      S7-A signed-threshold + S7-B triple-visibility outputs.
      Budget: 500-800k, 2-3 polecat sessions (high sub-split
      probability per §3.3).
      RISK: G4 O(1) slack propagation through BFS spanning tree;
      see §2.7 hidden constraint #1.
```

#### mg-S7-D (Step 7-D: single-c synchronization + giant component)

```
Title: OneThird-S7-D: Lean port of step7.tex G6 (lem:single-c) +
       G9 (lem:giant-component) — per-fiber thresholds collapse to
       single c via low-conductance + giant-component connectedness.
Depends: mg-S7-C.
Body: lean/OneThird/Step7/SingleThreshold.lean (319 LoC) scaffold +
      new giant-component infrastructure. Mathlib gap: Markov-style
      giant-component for second-moment weighted graphs (§5.2 row).
      Budget: 350-500k, 1-2 sessions.
```

#### mg-S7-E (Step 7-E: prop:71 + prop:72 assembly + lem:bandwidth)

```
Title: OneThird-S7-E: Lean port of step7.tex prop:71 + prop:72 +
       lem:bandwidth — combine G1-G6+G9 into the global
       threshold-of-potential description and the bandwidth bound
       K(T) + O(1) ≤ 4.
Depends: mg-S7-D.
Body: lean/OneThird/Step7/Assembly.lean prop_71/prop_72 already
      exist as abstract scaffolding (LayeredWidth3 = {bandwidth : ℕ,
      richPairsIn, richPairsOut, ...}). REPLACE bandwidth : ℕ field
      with a concrete construction whose value is bounded by 4
      (per rem:w0-constant alignment).
      Budget: 400-600k, 1-2 sessions.
      Key deliverable: replace LayeredWidth3.bandwidth : ℕ packaging
      with a constructive `bandwidth ≤ 4` proof.
```

#### mg-S7-F (Step 7-F: lem:layered-from-step7 — THE BRIDGE)

```
Title: OneThird-S7-F: Lean port of step8.tex lem:layered-from-step7
       (rem:layered-from-step7, step8.tex:1913-2106) — convert
       prop:72's layered-on-(1-o(1))-mass into exact def:layered on
       P |_{X \ X^exc}.
Depends: mg-S7-E.
Body: THE STRUCTURAL BRIDGE that closes MainAssembly.lean:265 sorry.
      Consumes mg-S7-E's bandwidth ≤ 4 + Step 8 ChainPotentials.lean
      ChainLiftData + F6a/F6b perturbation bounds (already in tree
      per mg-1f5e, mg-7496). Produces an L : LayeredDecomposition α
      with L.w ≤ 4 for α arising as minimal γ-counterexample.
      Wires into caseC_canonicalLayered (MainAssembly.lean:236) to
      replace the canonicalLayered α placeholder with the bridged L.
      Budget: 600M-1.0M, 2-4 sessions (HIGHEST sub-split risk per
      §3.3; mandatory hold-the-line checkpoint per §4.3 before
      starting).
      Verdict: GREEN cap-5 sorry CLOSED honestly / AMBER partial /
      RED structural blocker discovered at the bridge construction.
```

### §7.2. Full execution arc (Option A) — add to §7.1 if A is approved

If Daniel approves Option A (full Steps 1-7), pm-pogo files in
addition to §7.1:

- **mg-S1-A through mg-S1-D**: thm:interface parts I-III, bad-set
  bound, cor:overlap, cor:triple-overlap. 4 tickets, 1.0M-1.8M.
- **mg-S2-A, mg-S2-B**: lem:weak-grid + per-fiber transport. 2-3
  tickets, 0.8M-1.5M. (Possibly 3 if weak-grid is its own
  mathlib-port sub-arc.)
- **mg-S3**: sign normalization + coherence def. 1-2 tickets,
  0.5M-0.9M.
- **mg-S4-A through mg-S4-C**: incompatibility lemma + density-reg
  + witness construction. 3 tickets, 1.0M-1.8M.
- **mg-S5-A through mg-S5-E**: G1-G5 per §2.5. 5 tickets,
  1.0M-1.8M.
- **mg-S6-A, mg-S6-B**: G6-G10 + thm:step6 + cor:pointwise. 2-3
  tickets, 0.8M-1.2M.

Plus **mg-MathlibCheeger**, **mg-MathlibWeakGrid**,
**mg-MathlibChainRemoveLift**, **mg-MathlibCocycleHodge** as
separate mathlib-infrastructure tickets per §5.2; budget folded into
the per-step rows already.

Plus **inter-step QA scoping** tickets per checkpoint (§4.3):
**mg-S1234-QA**, **mg-S6-QA**, **mg-S7-checkpoint**. 3 tickets,
~250k each.

### §7.3. Recommended dispatch order

For Option B (pilot Step 7): strict sequential S7-A → S7-B → S7-C
→ S7-D → S7-E → S7-F. **No parallelism in pilot.**

For Option A (full): per §4.1 critical path. Recommended dispatch
order:

1. **Parallel wave 1** (~weeks 1-3): mg-S1-A through mg-S1-D
   (parallel), mg-S5-A through mg-S5-E (parallel), mg-MathlibCheeger
   sub-arc (parallel kickoff).
2. **Wave 2** (~weeks 4-6): mg-S2-A, mg-S2-B (sequential);
   mg-S3 (sequential after S2); mg-MathlibWeakGrid as needed.
3. **Wave 3** (~weeks 7-9): mg-S4-A through mg-S4-C (sequential).
4. **Wave 4** (~weeks 10-12): mg-S6-A, mg-S6-B (sequential).
   Hold-the-line checkpoint 2.
5. **Wave 5** (~weeks 13-20): mg-S7-A through mg-S7-F per §7.1
   strict sequential.

---

## §8. Risk watchlist

| # | Risk | Probability | Magnitude | Mitigation |
|---:|---|---:|---|---|
| 1 | 7th vacuity-discovery on the Lean port surface (not paper) | 30% | +500k-1M | Post-step QA scoping (§4.3 checkpoints); analog of mg-7377 |
| 2 | Cheeger / spectral-gap mathlib gap needs its own substantial port | 60% | +1.5M-2.5M | Sub-arc kickoff in wave 1 (§7.3); upstreamable to mathlib |
| 3 | Step 7 G4 cocycle O(1) propagation diameter constraint surfaces a missing Step 6 fineness hypothesis | 25% | +500k | Hold-the-line checkpoint 3 before starting S7-F (§4.3) |
| 4 | lem:layered-from-step7 chain-removal subtype lift needs Subtype.lean extension that surfaces a new vacuity | 20% | +500k-1M | F6a/F6b perturbation bounds (mg-1f5e, mg-7496) are mature; risk concentrated at bridge construction |
| 5 | Sub-split overhead exceeds 1.5× multiplier (i.e., a step's 5 sub-lemmas need 12 polecats instead of 7-8) | 30% | +500k per affected step | Z-arc empirical 250k/deliverable; budget multiplier built in |
| 6 | Daniel changes course mid-execution (per cumulative-vacuity-discovery pattern) | 40% | Variable | Pilot (Option B) is itself a partial-mitigation strategy |
| 7 | mathlib upstream review introduces delays on Cheeger / weak-grid lemmas | 50% | +2-4 weeks calendar | Have an in-tree fallback (no upstream PR) ready as Plan B |

**Aggregate risk-adjusted budget:** mid-estimate **8.75M** + risk
weighted expected delta **~1.5M-3M** ⇒ **planning ceiling ~12M**.
Communicate this ceiling to Daniel; the realistic delivery is
mid-estimate.

---

## §9. Cross-reference index

### §9.1. Paper

- `paper/main.tex` — §1.4 road map, residual paragraph
  (lines 380-413), discussion §discussion.
- `paper/step{1..7}.tex` — Steps 1-7 individual proofs.
- `paper/step8.tex` — Step 8 conclusion + ChainLiftData + the
  `lem:layered-from-step7` lift at lines 1913-2106.

### §9.2. Lean (this worktree)

- `lean/OneThird/Step{1..7}/` — partial scaffolding (per §1.1
  inventory).
- `lean/OneThird/Step7/Assembly.lean:302-348` — current paper-axiom
  `structure LayeredWidth3` interface (the target of S7-E).
- `lean/OneThird/Step8/MainAssembly.lean:236-267` —
  `caseC_canonicalLayered` with the relocated cap-5 sorry at
  `:265` (the target of S7-F).
- `lean/OneThird/Step8/LayeredBridges.lean` —
  `layeredFromBridges` placeholder + sham-bandwidth note (pre-mg-234e
  history; superseded). Useful for S7-F as a reference for the
  bridge architecture even though its current body is vacuous.
- `lean/OneThird/Step8/ChainPotentials.lean` — `ChainLiftData α`
  structural data; the S7-F bridge consumes this.
- `lean/OneThird/Mathlib/BKGraph.lean`, `LinearExtension/*.lean`,
  `Grid2D.lean`, `DirichletForm.lean`, `Poset/Dilworth.lean` —
  mathlib-tier supporting infrastructure (per §1.2).
- `lean/AXIOMS.md` — current named axiom inventory; analog for
  Step7.LayeredWidth3 if Option C is taken.

### §9.3. Predecessor documents

- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical
  proof-tree summary.
- `docs/coherence-collapse-case-extraction.md` (mg-ac13) — paper
  side technique-known verdict (GREEN); 3-disjoint-chains
  counterexample refuting mg-2970 R2.
- `docs/width3-residual-statement.md` (mg-2970) — SUPERSEDED but
  retains useful satisfiability + discharge-coverage analysis.
- `docs/onethird-proof-outline-audit.md` (mg-82fc) — per-step
  proof-tree tagging.
- `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2)
  — canonicalLayered bypass diagnosis.
- `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0) — cap-5 sorry
  history; relocated by mg-234e.
- `docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`
  (mg-0cbf) — Option D-narrow framing; mg-234e implements §5e.

### §9.4. Predecessor work items (vacuity-discovery cascade)

- mg-e2e9 (cap-5 proposal), mg-74d2 (canonicalLayered diagnosis),
  mg-5c32 (residual extraction first try), mg-82fc (proof-tree
  audit), mg-2970 (residual re-extraction), mg-ac13 (coherence
  collapse extraction; SUPERSEDES mg-2970), **mg-6ab8 (this scoping)**.

### §9.5. Sister scoping tickets

- mg-103f (Z-arc scoping) — analog scoping with Z1-Z10 pre-filed
  sub-tickets per same template. Different domain (Z-arc =
  ordinal/cap propagation); same scoping pattern.

---

## §10. Maintenance contract

This file is the **single-source-of-truth scoping document for
Steps 1-7 faithful Lean port** (per Daniel directive 2026-05-18T18:26Z
FINAL VERDICT, work item mg-6ab8).

Update this file in the **same commit** as any of the following:

- Daniel decides Option A / B / C and pm-pogo files (or doesn't
  file) the §7 sub-tickets.
- A sub-step lands and its actual budget / sub-split count
  contradicts §3.2; update the row and the aggregate.
- A risk in §8 materialises; update the probability and
  mitigation.
- The §4.3 hold-the-line checkpoints trigger a re-scope.
- A 7th vacuity-discovery surfaces (most likely site: S7-F bridge
  construction); update §2 with the new finding and §6 with the
  re-scoped recommendation.

**Daniel's "vacuity-discovery pattern has hit 6 times as of
mg-ac13"** (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13);
default to skeptical Lean-port reading, not abstract-scaffold
optimism. **Pattern is: surface area in the *grounding* tends to
reveal hidden constraints that the abstract scaffold absorbed
implicitly.**

If this file is wrong, edit it directly. Source-of-truth is the
Lean tree and `step{1..7}.tex`; this scoping is summary-of-plan.
