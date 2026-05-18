# OneThird-S7-A-G1-G2 Session 1 state report — grounded forms landed

**Ticket:** mg-4584 (first execution sub-ticket of S7 pilot per mg-6ab8 Phase E option B).
**Verdict:** **GREEN — substantively landed.** G1 (`lem:signed-threshold`) and G2 (`lem:sign-consistency`) grounded forms added to `lean/OneThird/Step7/SignedThreshold.lean` and `lean/OneThird/Step7/SignConsistency.lean` respectively; full `lake build` clean modulo pre-existing `unusedDecidableInType` linter warnings unrelated to this work.

---

## §0. TL;DR

* **G1 (signed-threshold).** Added `§7 — Grounded form: from a Step 2 staircase to signed-threshold` to `SignedThreshold.lean`. Wraps the existing cleared-denominator algebraic kernel (`signed_threshold_normal_form`, `signed_threshold_exists`) with a concrete `affineStaircase σ̃ φ D` predicate matching paper `eq:affine-staircase`, plus the `AffineStaircaseSpreadHyp` cleared-denominator spread bound consumed by the grounded `signed_threshold_grounded` theorem.
* **G2 (sign-consistency).** Added `§6 — Grounded form: from Step 6 cor:pointwise to sign consistency` to `SignConsistency.lean`. Defines `coherentSet` as the complement of `cor_pointwise`'s "bad" set, proves the bridge `mismatch_sum_majority_eq_minority_sum`, the grounded `doubleCountHyp_grounded` theorem (cleared-denominator `DoubleCountHyp` from `cor_pointwise`), and three grounded conclusion theorems specialising the existing flipped-weight / refined-set / overlap-agreement bounds.
* **No new axioms; no new `sorry`s; no headline shape change.** The grounded forms are wrappers on the existing cleared-denominator infrastructure; they wire Step 7's S7.a / S7.b sub-arcs to their upstream Step 2 / Step 3 / Step 6 outputs.
* **Build clean.** `lake build OneThird.Step7.SignedThreshold` and `lake build OneThird.Step7.SignConsistency` both succeed with no errors; warnings limited to the pre-existing `unusedDecidableInType` linter chatter on `[DecidableEq Pair]` / `[DecidableEq β]` instances in unrelated files.
* **Per `mg-6ab8` §3.3 sub-split contingencies:** no 7th vacuity-discovery surfaced on the paper-side (the §7 G1/G2 paper proofs were independently re-read against `step7.tex:124-369` and held up). The remaining S7-A engineering is *upstream* in S7-C (cocycle integration) and *downstream* in S7-F (bridge to `LayeredDecomposition α`), neither of which is in scope.

## §1. Inventory delta

```
SignedThreshold.lean     368 LoC → 587 LoC  (+219 LoC, +59%; §7 grounded form)
SignConsistency.lean    1009 LoC → 1290 LoC  (+281 LoC, +28%; §6 grounded form)
```

**Net polecat output:** ~500 LoC of Lean, plus this state doc.

## §2. G1 (signed-threshold) — what's grounded

### §2.1. Paper context (`step7.tex:124-230`)

`lem:signed-threshold` takes Step 2's per-fiber staircase `M_e ⊆ fib_e` and normalises it into the explicit signed-threshold form `1_S(L) = 1{σ_e·(j(L)-i(L)) ≥ τ_e} + O(ε_2)`. The paper proceeds in two steps:

1. **Collapse `φ_e ↦ τ̄_e`** (median replacement). The transverse-axis column-threshold function `φ_e` has spread `O(ε₂·t_e)` by a BK-boundary counting argument; replacing it by its median `τ̄_e` costs symmetric difference `O(ε₂·|fib_e|)`.
2. **Rewrite `\hat M_e` as signed half-plane**, possibly via the single-axis reflection `(i, j) ↦ (i, t_e - j)` in the `σ̃ = +1` case.

### §2.2. Existing scaffolding (pre-S7-A)

The pre-S7-A `SignedThreshold.lean` (368 LoC) handled **only step 2** in the cleared-denominator abstract form: given the *already-collapsed* affine half-plane `affineHalfPlane σ̃ τ̄ D`, prove it equals `signedHalfPlane σ τ D'` modulo the single-axis reflection. This is the file's `signed_threshold_normal_form` (line 325) and `signed_threshold_exists` (line 353).

What was missing: the **input shape**. There was no Lean object representing Step 2's staircase `M_e` in the form `eq:affine-staircase`, nor any connection to `affineHalfPlane` through the spread-bounded collapse.

### §2.3. S7-A G1 additions

`§7 — Grounded form: from a Step 2 staircase to signed-threshold` (lines 367–587) adds:

| Symbol | Role |
|---|---|
| `affineStaircase σTil φ D` | Concrete `Finset (ℤ × ℤ)` matching paper `eq:affine-staircase` — the staircase `{(i, j) ∈ D : i + σ̃·j ≤ φ(i - σ̃·j)}`. |
| `mem_affineStaircase` | Membership unfolding. |
| `affineStaircase_subset` | Subset of ambient grid. |
| `affineStaircase_const_eq_affineHalfPlane` | When `φ` is constant `≡ τ̄`, the staircase equals `affineHalfPlane σTil τ̄ D` (the `spread = 0` extreme of the collapse). |
| `isFlippedBy σTil φ τ̄ p` | Pointwise predicate: `p`'s membership flips between `affineStaircase σTil φ D` and `affineHalfPlane σTil τ̄ D`. |
| `affineStaircase_symmDiff_eq_flipped` | The symmetric difference equals `D.filter isFlippedBy`. |
| `affineStaircase_symmDiff_card` | Cardinality form of the above. |
| `affineStaircase_symmDiff_le_D` | Trivial bound: symmetric difference `≤ |D|`. |
| `AffineStaircaseSpreadHyp σTil φ τ̄ D spread_n spread_d` | Cleared-denominator spread hypothesis: `spread_d · #flipped ≤ spread_n · |D|`. Encodes the paper's `spread(φ_e) ≤ O(ε₂·t_e)` bound. |
| `affineStaircase_symmDiff_le_spread` | Symmetric difference bound under the spread hypothesis. |
| `signed_threshold_grounded` | **Main grounded theorem:** combines the above with `signed_threshold_normal_form` / `signed_threshold_exists` to deliver the signed-threshold equality modulo a cleared-denominator symmetric-difference bound. |

### §2.4. What's *not* grounded yet (out of scope per mg-6ab8 §7.1 budget)

* The **BK-boundary argument** that *produces* `AffineStaircaseSpreadHyp` from Step 2's conductance budget (`step7.tex:158-181`). The hypothesis is accepted as input; the upstream derivation is a separate sub-arc (likely S7-B or part of a Step 2 retro-fit per mg-6ab8 §3.3 row "S2.b weak-grid stability").
* The **bridge from Step 3's `IsStaircaseType σ D M`** (column-threshold form `j ≤ f(i)`, the format of Step 2 output via `PerFiber.exists_staircase_per_fiber` + `local_sign_exists`) to the paper's affine `eq:affine-staircase` form `i + σ̃·j ≤ φ(i - σ̃·j)`. The two are equivalent under the change of variables `(u, v) = (i + σ̃·j, i - σ̃·j)`, but the explicit Lean bijection is a separate small lemma; deferred to S7-B follow-up.
* The **median-existence** for `φ_e` on the transverse range `V_e`. We accept `τ̄ : ℤ` as a polymorphic input; a constructive median (e.g., `V_e.image φ |>.toList.sort.get (V_e.card / 2)`) is straightforward to wire later.

## §3. G2 (sign-consistency) — what's grounded

### §3.1. Paper context (`step7.tex:240-369`)

`lem:sign-consistency` takes the coherence case of Step 6 (output of `cor:pointwise`, `step6.tex:587`) and globalises the per-`L` reference sign `s(L)` to a per-interface refined sign `σ̃_e = ε_e · σ_e` on a mass-dominant subset `E⋆ ⊆ Rich⋆`. The paper structure:

1. **Definition of `σ̃`.** Let `ε_α = +1` if `m_α ≥ μ_α / 2`, else `-1`; set `σ̃_α := ε_α · σ_α`.
2. **Flipped weight `≤ 4√δ · M₀`** (condition 1).
3. **Refined set `E⋆`** via Markov on `(1 - δ^{1/4})`-dominance.
4. **Overlap compatibility** on active pairs in `E⋆ × E⋆` via union bound.

### §3.2. Existing scaffolding (pre-S7-A)

The pre-S7-A `SignConsistency.lean` (1009 LoC) handled steps **1–4 in the cleared-denominator abstract form** but with **abstract parameters** for the coherent set `Ω` and reference sign `s`. The downstream consumer was required to construct `Ω` and `s` itself and supply the cleared-denominator `DoubleCountHyp` / `OutsideMassHyp` hypotheses by hand.

What was missing: the **concrete instantiation** linking `Ω`, `s`, and `DoubleCountHyp` to Step 6's `cor_pointwise` output.

### §3.3. S7-A G2 additions

`§6 — Grounded form: from Step 6 cor:pointwise to sign consistency` (lines 1006–1290) adds:

| Symbol | Role |
|---|---|
| `badSet richStar Fstar σ LP t_n t_d` | The "bad" set of `cor_pointwise`: `L ∈ LP` with `t_n · I(L) ≤ t_d · m(L)`. |
| `coherentSet richStar Fstar σ LP t_n t_d` | The complement `LP \ badSet`, cleared-denominator analog of paper's `Ω`. |
| `mem_coherentSet` / `coherentSet_subset` / `coherentSet_minority_bound` | Membership unfolding + subset of `LP` + the pointwise `t_d · m(L) ≤ t_n · I(L)` bound for `L ∈ coherentSet`. |
| `mismatch_sum_majority_eq_minority_sum` | **Bridge lemma:** `∑_α mismatchCount Fstar Ω σ majoritySign α = ∑_{L ∈ Ω} minorityCount L`. Chains `mismatch_sum_eq_incidence` with `majority_disagree_eq_minority` (Step 6). |
| `doubleCountHyp_grounded` | **Main grounded `DoubleCountHyp`:** for `Ω := coherentSet` and `s := majoritySign`, the cleared-denominator `DoubleCountHyp` holds with `η_n = t_n`, `η_d = t_d`, `M₀ = ∑_LP visibility(L)`. |
| `OutsideMassGroundedHyp` | The companion `OutsideMassHyp` packaged for the grounded `Ω = coherentSet`. Accepted as input parameter (paper supplies it from Step 6 second-moment / triple-visibility). |
| `sign_consistency_grounded_flipped_weight` | **Condition (1):** flipped weight `≤ 4 · (t_n/t_d) · M₀` (cleared-denominator). |
| `sign_consistency_grounded_notRefined` | **Condition (2) — refined-set Markov:** non-refined-set mass `≤ 2 · (δ₁_d/δ₁_n) · (t_n/t_d) · M₀`. |
| `sign_consistency_grounded_overlap_agree` | **Condition (2) — overlap compatibility:** union-bound on active-pair disagreement. |

### §3.4. What's *not* grounded yet (out of scope per mg-6ab8 §7.1 budget)

* The **`OutsideMassGroundedHyp` discharge.** The paper cites either (a) Step 6 pointwise control of `Ω`-complement mass, or (b) `lem:triple-visibility` (S7-B). We supply the predicate; the discharge is part of S7-B's `lem:triple-visibility` Lean port.
* The **active-pair quantitative refinement.** `sign_consistency_grounded_overlap_agree` is the union-bound form; the paper's quantitative form using `w_{ef} ≥ δ^{1/4} · min(μ_e, μ_f)` is supplied as a separate input by the downstream consumer (Step 7-d assembly, not in S7-A scope).

## §4. Architectural impact on PROOF-STRUCTURE-ONBOARDING.md (mg-6f04)

This work **does not** change the headline proof tree of §2 in the onboarding doc:

* No new axioms (verify with `grep -n axiom lean/AXIOMS.md` — unchanged).
* No new sorrys (verify with `grep -rn 'sorry' lean/OneThird/Step7/` — unchanged).
* The `Step7.LayeredWidth3` paper-axiom interface at `Step7/Assembly.lean:302` is untouched; the cap-5 sorry at `MainAssembly.lean` `caseC_canonicalLayered` is untouched.

What changes: the **honesty of the S7.a / S7.b sub-arcs**. Pre-S7-A, `SignedThreshold.lean` and `SignConsistency.lean` were cleared-denominator abstract scaffolds with no link to Step 2 / Step 6 outputs (`grep "OneThird.Step5\|OneThird.Step6" lean/OneThird/Step7/SignedThreshold.lean` returned `OneThird.Step3.LocalSign` only; `SignConsistency.lean` did import Step 6 but used only `Sign`, not the concrete `cor_pointwise` / `majoritySign` infrastructure). Post-S7-A, both files have an explicit `§ Grounded` section that names the upstream input and exposes the cleared-denominator data flow.

**Suggested PROOF-STRUCTURE-ONBOARDING.md §2 row update** (deferred to S7-F polecat, who will own the full §7 row rewrite):

> Step 7.a (`SignedThreshold.lean`): S + S-grounded as of S7-A (mg-4584). The cleared-denominator algebraic kernel of §§ 1-6 is wrapped by `§7 — Grounded form` taking the paper's `eq:affine-staircase` shape as concrete input + `AffineStaircaseSpreadHyp` as the cleared-denominator collapse cost.
>
> Step 7.b (`SignConsistency.lean`): S + S-grounded as of S7-A (mg-4584). The cleared-denominator double-counting kernel of §§ 1-4 is wrapped by `§6 — Grounded form` taking Step 6 `cor_pointwise`'s output as concrete input + `OutsideMassGroundedHyp` as the cleared-denominator complement-mass input.

Since this is the *first* S7 sub-arc landed, and we want to avoid maintenance-doc churn from incremental sub-arc landings (per onboarding doc maintenance contract: "owner = whoever ships the next major architectural audit, residual re-extraction, axiom land/drop, or headline restatement"), this state doc is the authoritative record; the onboarding doc will be updated when S7-F lands and the §7 row materially changes (i.e., when `Step7.LayeredWidth3` actually delivers `L.w ≤ 4`).

## §5. Default-skeptical verification (per mg-6ab8 §8 risk watchlist)

Per Daniel's "vacuity-discovery hit 6 times" pattern (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13), the **mg-6ab8 §8 row "30%: 7th-vacuity-discovery on Lean port of Steps 1-7"** is the standing risk for this work.

I re-read the paper sections (`step7.tex:124-230` for G1, `step7.tex:240-369` for G2) and the existing Lean code with default-skeptical eyes. Findings:

1. **G1 paper-side rigorous, no vacuity surfaces.** The collapse `φ ↦ τ̄` is a genuine `O(ε₂·t_e)` symmetric-difference cost backed by the BK-boundary count `|∂_BK M_e ∩ fib_e| ≥ c · spread(φ) · t_e`. The signed-half-plane rewrite is direct algebra. No `∃ L : LayeredDecomposition α`-style universal-existence claim is hidden anywhere — the input/output shapes are honest.

2. **G2 paper-side rigorous, no vacuity surfaces.** The double-counting identity is genuine (`mismatch_sum_eq_incidence` is provable from Fubini). The flipped-weight bound, refined-set Markov, and overlap union bound are direct cleared-denominator versions of the paper's arguments. The `Ω`-complement mass control (`OutsideMassHyp`) is properly separated as an input — the paper cites it from a separate Step 6 / triple-visibility argument.

3. **Lean-side: no API-surface transcription error.** The grounded forms expose the upstream connection (`coherentSet` is built from `OneThird.Step6.minorityCount` and `OneThird.Step5.visibility` directly, not via an abstract `Fstar α ⊆ LP` placeholder) but do not change the existing cleared-denominator kernel theorems' shapes. The `flipped_weight_bound` and `notRefined_mass_bound` are still consumed via the same `DoubleCountHyp` / `OutsideMassHyp` predicates — just with concrete instantiations.

4. **Hypothesis traceability check.** All five caps of the existing `Case3Witness` API surface (mg-d5a0 cap-5 fix) are untouched. Per onboarding doc §3 pitfall #2 ("don't transcribe Case3Witness's caps as the residual"), no residual restatement is implied by this work.

**Verdict on §8 risk watchlist: no 7th vacuity-discovery surfaced.** Default-skeptical lens applied to both paper-side and Lean-side; both held up.

## §6. Per mg-6ab8 §6.4 decision template — sub-arc verdict

| Sub-arc | Status | Notes |
|---|---|---|
| mg-S7-A (THIS) | **GREEN — landed** | G1 + G2 grounded forms, `lake build` clean. |
| mg-S7-B (triple-visibility) | NOT STARTED | Ready to dispatch; consumes S7-A's `coherentSet` + `OutsideMassGroundedHyp` interfaces. |
| mg-S7-C (cocycle + potential) | NOT STARTED | Consumes S7-A's `affineStaircase` + S7-B's triple-visibility. |
| mg-S7-D (single-c + giant-component) | NOT STARTED | Consumes S7-C cocycle output. |
| mg-S7-E (prop:71/72 + bandwidth) | NOT STARTED | Replaces `LayeredWidth3.bandwidth : ℕ` with constructive `≤ 4`. |
| mg-S7-F (lem:layered-from-step7 bridge) | NOT STARTED | THE BRIDGE; closes `MainAssembly.lean` `caseC_canonicalLayered` cap-5 sorry. |

**Recommendation for pm-onethird** (the orchestrating PM for the S7 pilot): dispatch mg-S7-B next as a SENIOR polecat with the same `repo=one_third_width_three`, `default to main`, `~250-300k budget`, `verdict GREEN port complete / AMBER partial`. mg-S7-B's Lean port can directly consume the `coherentSet` / `OutsideMassGroundedHyp` interface from this work.

## §7. Cross-reference index

* **Lean** (this work):
  - `lean/OneThird/Step7/SignedThreshold.lean:367-587` — §7 grounded form (G1).
  - `lean/OneThird/Step7/SignConsistency.lean:1006-1290` — §6 grounded form (G2).
* **Lean (consumed, unmodified):**
  - `lean/OneThird/Step3/LocalSign.lean` — `Sign`, `IsStaircaseType`, `local_sign_exists`.
  - `lean/OneThird/Step5/SecondMoment.lean:134` — `visibility`.
  - `lean/OneThird/Step6/Assembly.lean:317/520/536/545` — `minorityCount`, `cor_pointwise`, `majoritySign`, `majority_disagree_eq_minority`.
* **Paper** (`step7.tex`):
  - `124-230` — `lem:signed-threshold` (G1).
  - `240-369` — `lem:sign-consistency` (G2).
  - `1107-1340` — §`sec:formal` — overall Step 7 sub-lemma manifest where G1 + G2 fit.
* **Predecessor docs:**
  - `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical entry point; this work leaves §2 unchanged but adds §3 below.
  - `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) — §7.1 mg-S7-A spec consumed verbatim.
* **mg ticket history:**
  - mg-6ab8 (parent) — Steps 1-7 scoping; Phase E option B selected by Daniel 2026-05-18T22:13Z.
  - mg-ac13 — coherence-collapse extraction; `Step7.LayeredWidth3` paper-axiom rationale (downstream of this work).
  - mg-234e — caller's L rewire at K ≥ 2; relocated cap-5 sorry to `MainAssembly.lean` (independent of S7-A).
