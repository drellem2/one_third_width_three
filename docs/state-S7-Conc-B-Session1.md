# State — S7-Conc-B — Session 1: extract the Step 5 richness constants `c_n, c_d, M₀`

**Ticket:** mg-8f9c (OneThird-S7-Conc-B: Piece 2 follow-on — extract
the Step 5 richness constants `c_n, c_d, M₀`).
**Branch:** `polecat-8f9c`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.2 Piece 2,
sub-arc mg-S7-Conc-B.
**Depends:** mg-4ce6 (S7-Conc-A — the BK-graph carrier types,
`Step7/GroundSet.lean`); Piece 1 (Steps 1-6 cascade — landed,
Checkpoint 2 passed via mg-496b; the S5 wave mg-d4bb / mg-be3e
delivered the Step 5 grounded forms this extraction consumes).

---

## §0. Verdict — **GREEN-richness-constants-extracted**

The Step 5 richness constants are extracted from the **landed**
Step 5 grounded output and discharged into the Step 7 `RichnessHyp`
parametric signature:

| Constant | Genuine value | Source |
|---|---|---|
| `c_n` | `1` | post-activation density `c'_T = c₅⋆/2` numerator |
| `c_d` | `2` | post-activation density `c'_T = c₅⋆/2` denominator |
| `M₀`  | `|LP|` | the linear-extension universe cardinality (`|LE(P)|` when `LP = univ`) |

The deliverable is `lean/OneThird/Step7/RichnessConstants.lean`
(NEW, ~310 LoC, sorry-free, axiom-free), wired into
`OneThird.lean`. `lake build OneThird` is clean.

**The constants project cleanly into the parametric signature.**
The mg-8f9c non-triviality bar mandates a block-and-report *if* the
Step 5 constants do not project cleanly into the parametric
`lem_bandwidth_le_four_bundled` signature. They do — and the
projection is exhibited end-to-end by
`lem_bandwidth_le_four_bundled_of_step5_richness` (§3 of the file),
which feeds the extracted `RichnessHyp` straight into the S7-E
`lem_bandwidth_le_four_bundled_groundSet` with **no adapter
algebra**. Block-and-report does **not** fire.

**Non-triviality bar met.** The extracted constants are the genuine
concrete values from the landed Step 5 output, not placeholders:
`c_d = 2` is the genuine activation factor of `lem:fiber-mass`
clause (b) (`step5.tex:643-652`), and the fraction `c_n/c_d = 1/2`
is the load-bearing post-activation per-pair density `c'_T = c₅⋆/2`
(`step5.tex:721-738`). The concrete instance (§4 of the file) fires
the bound non-vacuously on genuine numbers (`M₀ = 6`, `posMass = 4`,
`1·6 ≤ 2·4`).

**One routing finding, disclosed (not a gap).** The per-pair
richness must be projected from the **G4 grounded form**
`Step5.fiber_mass_grounded`, not from the top-level dichotomy
packaging `Step5.thm_step5_grounded`. See §3.

---

## §1. Context — what mg-4ce6 left parametric

mg-4ce6 (S7-Conc-A) concretised the S7-A–E carrier types to the
BK-graph ground set (`Step7/GroundSet.lean`: `BKVertex α`,
`BKEdge α`, `Pair := α × α`) and re-exported the S7-E bandwidth
lemma as `lem_bandwidth_le_four_bundled_groundSet`. That lemma
consumes the per-pair richness hypothesis

```
RichnessHyp richPairs c_n c_d M₀
  := ∀ p ∈ richPairs, c_n · M₀ ≤ c_d · posMass p
```

(`Step7/Bandwidth.lean:221`, the cleared form of the paper's
`c_T`-richness, `step7.tex:1033-1036`) with the constants
`c_n, c_d, M₀` and the `RichnessHyp` proof left **parametric**.

mg-4ce6 left them parametric because — at the time —
"a Step 5 grounded form exporting concrete richness constants" was
"Not in tree" (`docs/state-S7-Conc-Session1.md` §5). That is the
mg-S7-Conc-B sub-arc, deferred to "after piece 1 … lands".

Piece 1 has since landed: the S5 wave (mg-d4bb `DichotomyGrounded`,
mg-be3e `G4G5Grounded`) is in tree, and Checkpoint 2 passed
(mg-496b cascade composition). This session executes the deferred
extraction.

**Pitfall #4 check performed.** The mg-4ce6 doc's "Not in tree"
claim was verified to be stale: `grep` confirms `Step5/G4G5Grounded.lean`
exports `fiber_mass_grounded`, the per-pair G4 grounded form, and
`Step5/DichotomyGrounded.lean` exports `thm_step5_grounded`. The
grounded forms the extraction needs **now exist**.

---

## §2. What was built

### §2.1. File

| File | Δ |
|---|---:|
| `lean/OneThird/Step7/RichnessConstants.lean` | +310 (NEW) |
| `lean/OneThird.lean` | +1 (import) |
| `docs/state-S7-Conc-B-Session1.md` | +NEW |
| `docs/state-S7-Conc-Session1.md` | §5 update (mg-S7-Conc-B done) |
| `docs/PROOF-STRUCTURE-ONBOARDING.md` | §4 cross-ref update |

**`AXIOMS.md` delta: none.** No new axioms, none dropped, no
`sorry`.

### §2.2. The four deliverables

`RichnessConstants.lean` has four sections:

1. **`richnessHyp_of_fiber_mass_grounded`** (§1, core). Given the
   landed Step 5 G4 interface-partition data (the hypotheses of
   `Step5.fiber_mass_grounded`: cover (I1), disjointness, thin bad
   sets (I2), activation `2·B₀ ≤ |LP|`) and any `BandwidthData D`
   whose `posMass` is the good-fiber cardinality on the rich set,
   it discharges `D.RichnessHyp richPairs 1 2 LP.card`. The proof
   is one line: the first conjunct of `Step5.fiber_mass_grounded`
   is `∀ p ∈ richPairs, 2·|goodFiber p| ≥ |LP|`, which **is**
   `RichnessHyp` at `c_n = 1, c_d = 2, M₀ = |LP|`.

2. **`richnessHyp_groundSet_of_step5`** (§2). The core specialised
   to the mg-4ce6 carrier types (`Pair := α × α`,
   `LinExt := BKVertex α`) and the `BandwidthData.ofPotential`
   shape `lem_bandwidth_le_four_bundled_groundSet` consumes, with
   the free `posMass` slot wired to `fun p => |goodFiber p|`. This
   is the `hRich` argument the S7-F bridge / sub-arc mg-S7-Conc-D
   will pass.

3. **`lem_bandwidth_le_four_bundled_of_step5_richness`** (§3). The
   clean-projection certificate: composes §2's `RichnessHyp` with
   the S7-E `lem_bandwidth_le_four_bundled_groundSet` to produce
   the `LayeredWidth3` with `bandwidth ≤ 4`. Its very existence
   discharges the mg-8f9c non-triviality bar's "projects cleanly"
   condition. `hBud` (Step 6 budget) is threaded as a hypothesis.

4. **`richnessHyp_concrete` / `richnessHyp_concrete_nonvacuous`**
   (§4). The extraction fired on the genuine Step 5 concrete
   witness (`Step5.cLP/cRich/cGood/cBad` of `G4G5Grounded.lean`):
   `M₀ = 6`, two rich pairs, per-pair mass `posMass = 4`, bound
   `1·6 ≤ 2·4` with genuine slack.

---

## §3. The "which grounded form" finding — disclosed, not a gap

The mg-8f9c ticket says: extract the constants "from the `thm:step5`
R-branch grounded form". There are **two** landed Step 5 (R)-branch
grounded forms, and they expose **different** shapes:

* **`Step5.thm_step5_grounded`** (`Step5/DichotomyGrounded.lean`) —
  the top-level dichotomy packaging. Its (R) branch outputs
  `Step5.Step5Richness LP_card fiberSum c_R := c_R · LP_card ≤
  fiberSum` — an **aggregate** bound on the *total* fiber mass
  `∑_{p rich} |F_p|`. This is the form that feeds Step 6's second
  moment (`cor:second-moment`). An aggregate bound does **not** by
  itself yield a per-pair lower bound, so `Step5Richness` does not
  project into the per-pair `RichnessHyp`.

* **`Step5.fiber_mass_grounded`** (`Step5/G4G5Grounded.lean`) — the
  G4 grounded form, the grounding of `lem:fiber-mass`. Its output
  is a conjunction whose **first conjunct** is the **per-pair**
  bound `∀ p ∈ richPairs, 2·|goodFiber p| ≥ |LP|`. `thm_step5_grounded`
  invokes G4 precisely on its (R) branch (the `hG4_*` closures), so
  `fiber_mass_grounded` *is* the (R)-branch grounded form — it is
  simply one level down from the dichotomy packaging.

The per-pair `RichnessHyp` is the cleared form of `c_T`-richness —
the *defining* property of a rich pair (`step7.tex:1033-1036`). It
is therefore correctly projected from the **per-pair** G4 form
`fiber_mass_grounded`, not from the **aggregate**
`thm_step5_grounded` packaging.

This is a routing fact, **not** a vacuity-discovery: both forms are
landed and sound; the per-pair one is the one `RichnessHyp` needs.
Recorded here so a future polecat does not mis-attribute it to
`Step5Richness` and conclude (falsely) that the constants do not
project.

---

## §4. The extracted constants — genuineness

* **`c_n = 1`, `c_d = 2`.** `Step5.fiber_mass_grounded` is the
  grounding of `lem:fiber-mass` clause (b), the *activated*
  multiplicative form (`step5.tex:643-652`, `step5.tex:704-718`):
  after the activation step `2·B₀ ≤ |LP|`, the genuine per-pair
  bound is `2·|goodFiber p| ≥ |LP|` — the good fiber carries at
  least *half* the linear-extension mass. The factor `2` is the
  genuine activation factor; the fraction `c_n/c_d = 1/2` is the
  paper's post-activation per-pair density `c'_T = c₅⋆/2`
  (`step5.tex:721-738`, Step 3 of the `lem:fiber-mass` proof).
  These are **not** placeholders.

* **`M₀ = |LP|`.** `LP : Finset LinExt` is the linear-extension
  universe of the Step 5 forms. When `LP = Finset.univ`,
  `|LP| = Fintype.card (LinearExt α) = |LE(P)|` — exactly the
  §2.2 spec's `M₀ := |LE(P)|`.

* **`posMass p := |goodFiber p|`.** The free `posMass` slot of
  `BandwidthData.ofPotential` is instantiated with the Step 5
  good-fiber cardinality. The richness is then a *specific Finset
  cardinality bound* on the ground set: `1·|LP| ≤ 2·|goodFiber p|`.

**Consistency constraint passed to mg-S7-Conc-C.** `posMass`
appears in *both* the `RichnessHyp` (extracted here) and the
`VarBudgetHyp` (`hBud`, the Step 6 sub-arc mg-S7-Conc-C). Sub-arc
mg-S7-Conc-C must produce `hBud` for the **same**
`posMass := fun p => |goodFiber p|` and the **same**
`M₀ := |LP|`. This is documented in the §3 docstring of
`RichnessConstants.lean`.

---

## §5. Vacuity-discovery audit (Daniel's "skeptical" lens)

Per `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks:

1. **Satisfiability.** `RichnessHyp richPairs 1 2 |LP|` is
   satisfiable at the headline range: `richnessHyp_concrete` proves
   it on genuine 6/4 numbers (`1·6 ≤ 2·4`, slack `6 ≤ 8`).
   `richnessHyp_concrete_nonvacuous` certifies the rich set is
   non-empty, so the `∀` is not vacuously true. Were the good
   fibers empty (`posMass = 0`), `1·6 ≤ 2·0` would be **false** and
   the file would not compile — the hard satisfiability gate.

2. **Discharge-coverage.** The extraction cites exactly one Step 5
   artefact — `Step5.fiber_mass_grounded` — and its actual scope
   (the per-pair clause `∀ p, 2·|goodFiber p| ≥ |LP|`) matches the
   claimed `RichnessHyp` shape exactly. No over-claim: the aggregate
   `Step5Richness` is explicitly *not* cited (§3).

3. **Universal-quantifier truthfulness.** No false universal is
   introduced. `richnessHyp_of_fiber_mass_grounded` is conditional
   on the genuine Step 5 G4 hypotheses (cover / disjoint / thin /
   activation); it does not assert `∀ α, RichnessHyp …`
   unconditionally.

**Verdict:** no vacuity-discovery. The extraction is a pure
projection of a landed, sound Step 5 grounded form.

---

## §6. Acceptance bars

- [x] `lake build OneThird.Step7.RichnessConstants` clean
  (1335/1335 jobs).
- [x] `lake build OneThird` (full root) clean.
- [x] No `sorry` in `RichnessConstants.lean`.
- [x] No new axioms (`AXIOMS.md` unchanged).
- [x] Genuine concrete constants extracted: `c_n = 1`, `c_d = 2`,
  `M₀ = |LP|` — the post-activation density `c'_T = 1/2` of
  `step5.tex:721-738`, not placeholders.
- [x] Constants project cleanly into the parametric S7-E signature
  — exhibited by `lem_bandwidth_le_four_bundled_of_step5_richness`.
  Block-and-report does not fire.
- [x] Non-vacuous concrete instance on the genuine Step 5 witness
  (`richnessHyp_concrete_nonvacuous`).
- [x] Wired into `OneThird.lean` root.
- [x] Skeptical vacuity audit applied (§5) — no discovery.

---

## §7. What remains (post-mg-8f9c piece-2 follow-on)

* **mg-S7-Conc-C** — extract `b_n, b_d` from the Step 6
  `thm:step6` + `cor:pointwise` grounded forms, producing the
  `VarBudgetHyp` (`hBud`). **Inherits the §4 consistency
  constraint:** must use `posMass := fun p => |goodFiber p|` and
  `M₀ := |LP|`.
* **mg-S7-Conc-D (discharge half)** — combine the mg-S7-Conc-B
  `RichnessHyp` (this session) with the mg-S7-Conc-C `VarBudgetHyp`
  and invoke `lem_bandwidth_le_four_bundled_of_step5_richness` (or
  `lem_bandwidth_le_four_bundled_groundSet` directly) to produce an
  *unconditional* `L_{S7E} : LayeredWidth3 (richPairs α)` with
  `bandwidth ≤ 4` for `α` a minimal γ-counterexample.

`lem_bandwidth_le_four_bundled_of_step5_richness` already wires
mg-S7-Conc-B's output into the S7-E signature, so mg-S7-Conc-D's
remaining work is exactly: supply `hBud` (mg-S7-Conc-C) and the
genuine Step 5 G4 interface-partition data for the headline α.

---

## §8. Cross-reference index

### §8.1. Lean (this work)

* `lean/OneThird/Step7/RichnessConstants.lean` (NEW) —
  `richnessHyp_of_fiber_mass_grounded`,
  `richnessHyp_groundSet_of_step5`,
  `lem_bandwidth_le_four_bundled_of_step5_richness`,
  `cRichBandwidthData`, `richnessHyp_concrete`,
  `richnessHyp_concrete_nonvacuous`.
* `lean/OneThird.lean` — `import OneThird.Step7.RichnessConstants`.

### §8.2. Lean (consumed, unmodified)

* `lean/OneThird/Step5/G4G5Grounded.lean` (mg-be3e) —
  `fiber_mass_grounded` (per-pair G4 grounded form),
  `cLP`, `cRich`, `cGood`, `cBad`, `cRich_nonempty`.
* `lean/OneThird/Step5/DichotomyGrounded.lean` (mg-d4bb) —
  `thm_step5_grounded`, `Step5Richness` (aggregate (R) conclusion).
* `lean/OneThird/Step7/Bandwidth.lean` — `BandwidthData`,
  `RichnessHyp`, `VarBudgetHyp`, `BandwidthData.ofPotential`.
* `lean/OneThird/Step7/GroundSet.lean` (mg-4ce6) — `BKVertex`,
  `BKEdge`, `lem_bandwidth_le_four_bundled_groundSet`.

### §8.3. Paper

* `step5.tex:643-652`, `step5.tex:704-718` — `lem:fiber-mass`
  clause (b), the activated per-pair bulk bound.
* `step5.tex:721-738` — Step 3, the richness conclusion (R) with
  `c'_T = c₅⋆/2`.
* `step7.tex:1033-1036` — `c_T`-richness (the per-pair `RichnessHyp`).

### §8.4. Predecessor docs

* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) §2.2
  — the mg-S7-Conc-B sub-arc spec.
* `docs/state-S7-Conc-Session1.md` (mg-4ce6) — S7-Conc-A; §5 lists
  mg-S7-Conc-B as the deferred follow-on (updated this session).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §3 pitfall #2
  (skeptical lens, §5) and pitfall #4 (verify "not in tree", §1).

### §8.5. Predecessor work items

mg-d8c7 (Option A' scoping), mg-4ce6 (S7-Conc-A), mg-516f (S7-E
bandwidth lemma), mg-d4bb / mg-be3e (Step 5 grounded wave),
mg-496b (Checkpoint 2 cascade composition), **mg-8f9c (this
session)**.

---

## §9. Maintenance contract

This file is the state record for piece-2 sub-arc mg-S7-Conc-B
(Step 5 richness-constant extraction). Update it in the same commit
as any change that:

* Changes the extracted constants (`c_n = 1`, `c_d = 2`) — e.g. if
  a future Step 5 grounding revises the activation factor.
* Changes the `posMass := |goodFiber p|` wiring (the §4 consistency
  constraint mg-S7-Conc-C inherits).
* Lands mg-S7-Conc-C / mg-S7-Conc-D and thereby discharges `hBud`
  or produces the unconditional `L_{S7E}`.

If mg-S7-Conc-C cannot produce `hBud` for the `posMass`/`M₀` this
sub-arc fixed, record the mismatch here and re-scope.
