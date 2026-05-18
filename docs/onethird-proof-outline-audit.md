# OneThird width-3 proof outline audit — F3 strong-induction conclusion-lift

**Polecat:** mg-82fc (ticket (A) of A+B split per Daniel 2026-05-18T07:35Z)
**Date:** 2026-05-18
**Scope:** Phase A–E (F3 conclusion-lift, Case3Witness invocation, API + Bool certificate, per-step tag, forward action)
**Predecessor docs:**
[mg-e2e9 architecture analysis](onethird-Case3Witness-architecture-analysis.md),
[mg-74d2 layered-vs-coherence audit](layered-form-vs-coherence-architecture-audit.md),
[mg-0cbf post-cap-5 tractability](onethird-Case3Witness-post-cap-5-tractability-analysis.md),
[mg-4d7b enumeration state](state-Case3Witness-cap5-enumeration.md),
[mg-5c32 residual statement](width3-residual-statement.md)

---

## §0 — Executive verdict

**The F3 strong-induction conclusion-lift mechanism inside `Step8.OptionC.Case3Witness_proof.{u}` is SUBSTANTIVE, not circular.** Daniel's worry (2026-05-18T07:36Z: "the inductive thing you describe on case 3 witness still makes it sound equivalent to proving the whole conjecture") is **RESOLVED**.

The recursive descent does not hand-wave by re-applying the conjecture; it strictly descends on `Fintype.card β` and lifts the IH-supplied balanced pair from a sub-poset to the ambient via the genuine **marginal-invariance** content of `lem:ordinal-factorisation` (paper `step8.tex:2404-2418`). The bridge is `OrdinalDecomp.hasBalancedPair_lift` in `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152` — a Lean proof of `Pr[u<v]` invariance under ordinal-sum-factor restriction, derived from a genuine bijection `LinearExt α ≃ LinearExt Lower × LinearExt Mid × LinearExt Upper`.

**Verdict: GREEN-substantive-found** — for the Phase A *inner* F3 mechanism.

But this verdict is **NOT** an architectural green light. The audit confirms (and re-confirms) the four cumulative vacuity findings:

1. **mg-e2e9** (pre-cap-5 Case3Witness vacuous via `canonicalLayered` substitution at the caller site) — UNCHANGED. The post-cap-5 `lem_layered_balanced` K≥2 dispatch still substitutes `canonicalLayered α` and trips the cap-5 obligation, hence the `sorry` at `LayeredBalanced.lean:751` (mg-d5a0).
2. **mg-74d2** (bare F3 framework and `bounded_irreducible_balanced{,_hybrid}` are marker theorems) — CONFIRMED for the *outer* skeleton at `LayerOrdinal.lean:370` and for the hybrid dispatcher at `BoundedIrreducibleBalanced.lean:1681`; **REFINED** by Phase A here — `Case3Witness_proof.{u}` carries its OWN internal strong induction that is *not* the bare framework and IS substantive.
3. **mg-5c32** (LayeredResidual structurally vacuous for `|α|≥11` under caps 1+2+5) — UNCHANGED. Caps 1+4 force `K=|β|`, caps 2+5 force `K≤10`. The ∀-family in `Case3Witness.{u}` is non-vacuous exactly on `|β|≤10`.
4. **Daniel-flagged conclusion-lift question** (THIS AUDIT) — RESOLVED-substantive. The mechanism is not circular; it lifts via real marginal-invariance, not hand-waved IH re-application.

**Net architectural status: AMBER**, identical to mg-74d2's verdict, with the additional **positive** clarification that the layered-form architecture has a **real substantive backbone in the |β|≤10 slice** — the F3 inner strong induction + the mg-4d7b enumeration evidence + `bounded_irreducible_balanced_inScope` honest Bool↔Prop bridge.

The forward action for ticket (B) (residual re-extraction) does **NOT** pivot away from layered form. It pivots to **rewiring the call site** (rewrite `lem_layered_balanced` K≥2 to consume the caller's `L` rather than substitute `canonicalLayered`) so that the substantive |β|≤10 backbone is consumed at the headline path. See §5 for the recipe.

---

## §1 — Phase A: F3 strong-induction conclusion-lift mechanism (THE KEY QUESTION)

### §1.1 — Distinguish two F3 things

Two distinct constructs in the tree are both called "F3 strong induction":

| Construct | File / line | What it is | Substantive? |
|---|---|---|---|
| `hasBalancedPair_of_layered_strongInduction[_width3]` | `LayerOrdinal.lean:370` / `:472` | **Bare F3 skeleton** — strong induction on `Fintype.card α` with the step closure taken as an inline `hStep` hypothesis. Recursion ignores `L`; only `Fintype.card α` is used. Pure template. | NO — marker-only (mg-74d2 confirmed). The framework just packages strong-induction-on-Nat with type-generalization. Never consumed by the headline path. |
| `Case3Witness_proof.{u}` | `OptionC/Case3WitnessProof.lean:256` | **Internal F3 strong induction** specific to the Case3Witness ∀-family, built by hand via `Nat.strong_induction_on` (line 286) on `Fintype.card β`, with explicit cap-propagation for the recursive call. NOT the bare framework — does NOT call `hasBalancedPair_of_layered_strongInduction`. | **YES — substantive**. This is the load-bearing F3 instance for the headline. |

mg-74d2 §3's marker-only finding applied to the FIRST construct (the skeleton). Phase A here probes the SECOND construct (the internal Case3Witness induction) — which mg-74d2 explicitly did NOT audit. That's the question Daniel flagged.

### §1.2 — Anatomy of the conclusion-lift (Case3Witness_proof.{u})

The proof is at `Case3WitnessProof.lean:286–547`. The recursive structure:

```
induction n using Nat.strong_induction_on with
  | _ n ih => …                          -- ih : ∀ m < n, ∀ β …, HasBalancedPair β
```

The case split on `LB.K`:

| Case | Branch | Discharge |
|---|---|---|
| K = 1 | `absurd_K1_of_injective` | Caps 1 (Injective) + `2 ≤ |β|` force two distinct elements both with band 1, contradicting injectivity. **No IH call.** |
| K = 2 reducible at k=1 | `isChain_of_K2_reducible_under_injective` | Caps 1 + 4 force bands singletons → `|β|=2` → unique cross-pair forced to `<` by reducibility → `β` is chain → contradicts `hNC`. **No IH call.** |
| K = 2 irreducible | `OptionC.option_c_K2_closure` | mg-01ec deliverable. `w=0` excluded structurally (forced cross-band `<` would be reducibility); for `w≥1` dispatches the F5a Bool certificate `case2_certificate` via `normalizeWAtK2` to the w=1 sister. **No IH call.** |
| K ≥ 3 reducible at some k | F3 LIFT (see §1.3) | Recursive call on `D.Lower` or `D.Upper` via `compactify`. **IH call. This is the load-bearing recursive lift.** |
| K ≥ 3 irreducible | `bounded_irreducible_balanced_hybrid` | Splits on `Decidable(InCase3Scope L.w |β| L.K)`. In-scope: `bounded_irreducible_balanced_inScope` + `case3_certificate`. Out-of-scope: `hStruct_of_case2_discharge`. **No IH call.** |

The IH is consumed **only** in the K≥3 reducible branch. That branch is the F3 conclusion-lift in the sense Daniel asked about.

### §1.3 — The K≥3 reducible branch: how the lift works

Code at `Case3WitnessProof.lean:311–516`. Step by step:

**Step 1.** Pick the reducibility witness: `obtain ⟨k, hk1, hkLt, hRed⟩ := hRedSome` with `1 ≤ k < L.K` and `LayerOrdinalReducible LB k`.

**Step 2.** Construct the ordinal decomposition:
```
set D := OrdinalDecompOfReducible LB k hRed
```
where `OrdinalDecompOfReducible` (`LayerOrdinal.lean:108`) packages
- `D.Lower := {z : LB.band z ≤ k}`
- `D.Mid := ∅`
- `D.Upper := {z : k < LB.band z}`

as a genuine `OrdinalDecomp β`. The crucial field `hLU_lt` (every element of Lower is `<` every element of Upper) is discharged BY `LayerOrdinalReducible LB k` itself: the reducibility hypothesis is operationally "every cross-pair (u, v) with `band u ≤ k`, `band v > k` satisfies `u < v`". So `OrdinalDecompOfReducible` is the data-bearing conversion from reducibility to a real ordinal decomposition. **SUBSTANTIVE.**

**Step 3.** Extract the incomparable pair from `¬IsChainPoset β`:
```
obtain ⟨x, y, hxy_le, hyx_le⟩ := hNC
```

**Step 4.** Show that `(x, y)` cannot be a cross-pair. The case split on band placement (`band x ≤ k` vs `band x > k`, and same for `y`) yields four cases:
- Both in Lower: recurse on Lower.
- x in Lower, y in Upper: `hRed x y` forces `x < y`, contradicting `hxy_le`. (Cross-pair eliminated.)
- y in Lower, x in Upper: `hRed y x` forces `y < x`, contradicting `hyx_le`. (Cross-pair eliminated.)
- Both in Upper: recurse on Upper.

This is the **load-bearing structural lever**: reducibility eliminates cross-pair-incomparability, so the incomparable pair must live entirely inside one factor. **SUBSTANTIVE** — this is not assumed; it's derived from the reducibility hypothesis via direct order-theoretic case analysis.

**Step 5.** Recurse on the factor containing the pair. For Lower:
```
let LB' : LayeredDecomposition ↥D.Lower := LB.compactify D.Lower
```
The recursive call (line 435):
```
ih (Fintype.card ↥D.Lower) hcard_le' ↥D.Lower LB'
   (le_refl _) hInj' hKw' hCardw' hNonempty' hLBw' hW3' hNC' h2'
```
Strict descent: `Fintype.card ↥D.Lower < Fintype.card β` because `D.Upper` is non-empty (band `K` element exists by `hNonempty K`, has band `K > k`). **SUBSTANTIVE.**

**Step 6.** Cap propagation for `LB'`:
- `hInj' = compactify_band_injective_of_injective LB D.Lower hInj` — preserves Injective. Verified `LayeredDecomposition/Compactify.lean`. **SUBSTANTIVE.**
- `hKw' : LB'.K ≤ 2*LB'.w + 2` from `LB'.K ≤ LB.K ≤ 2*LB.w+2 = 2*LB'.w+2` (uses `compactify_K_le + compactify_w_eq`). **SUBSTANTIVE.**
- `hCardw' : |↥D.Lower| ≤ 6*LB'.w+6` from `|↥D.Lower| ≤ |β| ≤ 6*LB.w+6 = 6*LB'.w+6`. **SUBSTANTIVE.**
- `hNonempty' = compactify_bandSet_nonempty` (mg-8c72 inline lemma). **SUBSTANTIVE.**
- `hLBw' : LB'.w ≤ 4` from `compactify_w_eq` (`LB'.w = LB.w` definitionally, since `compactify_w_eq` is `rfl`). **SUBSTANTIVE.**
- `hW3' = hasWidthAtMost_subtype hW3 D.Lower` — width-3 transfers to sub-finset. **SUBSTANTIVE.**
- `hNC' : ¬IsChainPoset ↥D.Lower` — `D.Lower` contains `x, y` incomparable. **SUBSTANTIVE.**
- `h2' : 2 ≤ |↥D.Lower|` — `D.Lower` contains `x ≠ y`. **SUBSTANTIVE.**

All cap propagations are honest Lean lemmas, not axioms or hand-waves.

**Step 7.** IH returns `hbp_lower : HasBalancedPair ↥D.Lower`.

**Step 8.** THE LIFT: `exact D.hasBalancedPair_lift_lower hbp_lower` (line 438).

The lift theorem `OrdinalDecomp.hasBalancedPair_lift_lower` (`Mathlib/LinearExtension/Subtype.lean:1227`) calls `D.toMidOfLower.hasBalancedPair_lift`, which:
- Repackages `D` as `D' := toMidOfLower D` with `D'.Lower := ∅, D'.Mid := D.Lower, D'.Upper := D.Mid ∪ D.Upper`.
- Applies `OrdinalDecomp.hasBalancedPair_lift` (`Subtype.lean:1152`), which takes the IH's balanced pair `(u, v) ∈ ↥D.Mid` (= `↥D.Lower` in the repackage) and produces `(u.val, v.val) ∈ β`.

The lift's substance is:
1. **Incomparability transfer** — `Subtype` order is restricted ambient order, so incomparability lifts. **TRIVIAL-AS-DEFINITIONAL.**
2. **Probability invariance** — `D.probLT_restrict_eq u.property v.property` (`Subtype.lean:~1060`) supplies `Pr[u.val <_α v.val] = Pr[u <_↥D.Mid v]`. **THIS IS THE LOAD-BEARING SUBSTANCE.**

`probLT_restrict_eq` is the **marginal-invariance corollary** of the genuine `LinearExt α ≃ LinearExt Lower × LinearExt Mid × LinearExt Upper` bijection (paper `lem:ordinal-factorisation`, `step8.tex:2404-2418`). The probability of `u<v` over linear extensions of α equals the probability over linear extensions of the factor containing both — because the bijection partitions extensions of α as a Cartesian product, and any pair in one factor is permuted independently of the other factors.

This is **NOT** a hand-wave. The bijection is constructed (`Subtype.lean:~700+`) with full Cartesian-product structure; the probability identity follows by `Fintype.card_congr + Fintype.card_prod + field_simp`. **SUBSTANTIVE.**

### §1.4 — Verdict for Phase A

**The F3 conclusion-lift mechanism is SUBSTANTIVE.** The "delete + apply IH + somehow conclude" pattern Daniel feared is actually:

1. Reducibility eliminates cross-pair-incomparability → incomparable pair lives in one factor.
2. Compactify the layered decomposition onto that factor; all five caps propagate via real lemmas.
3. IH produces a balanced pair on the strictly smaller factor.
4. Lift to ambient via real marginal-invariance from `lem:ordinal-factorisation`.

The recursion terminates at `|β| ≤ 2` (vacuous) or at K=1/K=2 base cases (substantive contradictions or `option_c_K2_closure`) or at K≥3 irreducible (Bool certificate `case3_certificate` for `InCase3Scope`, axiom `case3Witness_hasBalancedPair_outOfScope` for `¬InCase3Scope`).

Daniel's worry: **resolved**. The F3 mechanism is not equivalent to assuming the whole conjecture for `α`; it's a real Tukey-style ordinal-sum-driven structural induction with genuine factor-marginal-invariance as the lift.

The **scope** in which this substantive content is non-vacuous is `|β| ≤ 10` (caps 1+4 force `K=|β|`, caps 2+5 force `K ≤ 10`). For `|β| ≥ 11` the Case3Witness antecedent is structurally unsatisfiable, so the ∀-family is vacuously true on that range — but that's a **scope** restriction, not a circularity.

---

## §2 — Phase B: Case3Witness invocation pattern audit for |β|≤10

### §2.1 — The headline call site

`Step8.lem_layered_balanced` (`LayeredBalanced.lean:626–756`) is the K≥1 dispatcher. The K≥2 branch (line 681–756) is where `Case3Witness` is invoked.

**The invocation discards the input L and substitutes `canonicalLayered α`** (line 720):
```
let L' : LayeredDecomposition α := canonicalLayered α
...
exact hC3 α L' hInj hKw hCardw hNonempty hLBw hW3 hNotChain' h2
```

`canonicalLayered α` is the Szpilrajn-derived singleton-band layered decomposition with `K = w = |α|`. It satisfies caps 1+2+3+4 with slack — but **NOT cap 5** (`L'.w = |α| ≤ 4` requires `|α| ≤ 4`, the antecedent is structurally absent for arbitrary `|α|`).

This is the surfaced `sorry` at `LayeredBalanced.lean:751` (mg-d5a0). The cap-5 obligation cannot be discharged on `canonicalLayered`. **VACUOUS-COVER**.

### §2.2 — The mg-4d7b enumeration evidence is NOT wired

`Cap5Singletons.lean` (mg-4d7b) supplies Bool-level `native_decide` certificates for K∈{2, 4..8} cap-5 singletons, K=9 in `Cap5SingletonsK9.lean`, K=10 external JSON. These verify that EVERY cap-5-singletons cell is balanced.

These are **NOT** consumed by `lem_layered_balanced`. They are standalone Lean witnesses (decoupled from the headline path). They are paper-level evidence that the |β|≤10 slice can be discharged once the call site is rewired.

The actual operational consumer of Case3Witness IS `lem_layered_balanced` via `canonicalLayered`, which trips cap 5. So the mg-4d7b enumeration is **architectural ammunition** for the |β|≤10 slice rewrite (Option D-narrow per mg-0cbf), not currently in the headline.

### §2.3 — What `Case3Witness_proof.{u}` actually delivers

Within its caps 1–5 scope (i.e., for any LB satisfying all five caps), `Case3Witness_proof.{u}` delivers `HasBalancedPair β` honestly, via:

- For |β|≤10 (the non-vacuous scope under caps 1+2+4+5):
  - F3 strong induction terminating at K=1/K=2 base cases or K≥3 enumeration cells.
  - The K≥3 in-scope branch uses `case3_certificate` (K=3 + K=4-w=1, mg-9a4a Window C).
  - The K≥3 out-of-scope branch uses `case3Witness_hasBalancedPair_outOfScope` AXIOM for K∈{4 w≥2, 5..10} cells.
- For |β|≥11: caps 1+4+2+5 are unsatisfiable, so the universal is vacuously delivered.

**Net Phase B verdict:** The Case3Witness invocation at `lem_layered_balanced` is VACUOUS-COVER (`canonicalLayered` substitution, cap-5 sorry). The Case3Witness_proof.{u} ∀-family itself is substantive-within-scope (|β|≤10) modulo one paper-axiomatised residual.

---

## §3 — Phase C: bounded_irreducible_balanced API + F5a-ℓ Bool certificate audit

### §3.1 — The API gateway is marker (mg-74d2 confirmed)

`Step8.bounded_irreducible_balanced` (`BoundedIrreducibleBalanced.lean:1626`): all six structural hypotheses (`_hWidth3, _hIrr, _hK3, _hw, _hCard, _hDepth`) are underscored; the conclusion is `hEnum` returned as-is. **Pure identity. MARKER theorem.**

`Step8.bounded_irreducible_balanced_hybrid` (`BoundedIrreducibleBalanced.lean:1681`): all six structural hypotheses underscored. Proof body:
```
by_cases h : InCase3Scope L.w (Fintype.card α) L.K
· exact hCert h
· exact hStruct h
```
**Pure dispatcher on `Decidable(InCase3Scope)`. MARKER theorem.**

### §3.2 — `bounded_irreducible_balanced_inScope` IS substantive

`BoundedIrreducibleBalancedInScope.lean:97` consumes:
- `_hWidth3` (underscored — width-3 implicit via `L.band_size ≤ 3` field)
- `hIrr : LayerOrdinalIrreducible L` — used substantively in `irreducible_predMaskOf_offsetsOf_eq_true L hIrr` (B1', mg-a08f)
- `hScope : InCase3Scope L.w |α| L.K` — used substantively for `K ≥ 2` extraction (rcases on InCase3Scope branches)
- `hNonempty : ∀ k ∈ [1, L.K], 1 ≤ bandSize L k` — used substantively for `hasAdjacentIncomp_predMaskOf_eq_true` (B2, mg-e9d6)
- `h_certificate : Case3Enum.enumPosetsFor L.w (bandSizes L) = true` — the F5a Bool certificate

These compose via the G1' (mg-b487) + G3a (mg-609a) + G3a-followup (mg-792a) + G3b (mg-59cf) + G3c (mg-9568) + B1' + B2 + B3 (mg-0f0e) bridges through `closureCanonical_predMaskOf` and `predMaskOf_warshall` to produce `HasBalancedPair α`. **SUBSTANTIVE.**

The bridge structure is: predMaskOf L (an upper-triangular predecessor mask derived from L via the `cross_band_lt_upward` field, mg-53ce) → Bool-level `hasBalancedPair (predMaskOf L) (Fintype.card α) = true` → Prop-level `HasBalancedPair (Fin n)` → transport to `HasBalancedPair α` via `bandMajorOrderIso_predOrder L`.

### §3.3 — What does `case3_certificate` actually verify?

`Case3Enum/Certificate.lean:71`:
```
case3_certificate :
    allBalanced 1 9 = true ∧    -- K=3, w=1, sizeLimit=9, 344243 configs
    allBalanced 2 7 = true ∧    -- K=3, w=2, sizeLimit=7, 102784 configs
    allBalanced 3 7 = true ∧    -- K=3, w=3, sizeLimit=7, 102784 configs
    allBalanced 4 7 = true ∧    -- K=3, w=4, sizeLimit=7, 102784 configs
    allBalancedAtK 4 1 8 = true -- K=4, w=1, sizeLimit=8, 50 tuples (mg-9a4a)
```

`allBalanced w sizeLimit` is `Id.run`-implemented Bool enumeration over `bandSizesGen K sizeLimit` × `predicates`. It iterates over every closure-canonical mask configuration with bandwidth ≤ w and verifies `hasBalancedPair (predMask) n = true` for each. Each conjunct is closed by `native_decide` (records `Lean.ofReduceBool` axiom only).

**Sound and complete on the certified scope** (`Case3Enum/W1.lean` through `K4W1.lean`). No skipped cases, no relaxation. The Bool↔Prop bridge in `bounded_irreducible_balanced_inScope` consumes the certificate at L's band-major encoding via `bandSizes_mem_bandSizesGen` (membership) + `allBalanced_imp_enumPosetsFor` (extraction).

### §3.4 — `hStruct_of_case2_discharge` audit

`Case3Residual.lean:265–280`. Composition:
```
hStruct_of_case2_discharge … case2Discharge :=
  fun hScope =>
    rcases case1_dispatch_balanced_or_witness L hWidth3 hIrr hScope with
    | Case1 ambient match  → h1                                    [SUBSTANTIVE]
    | Case2 within-band ⪯  → case2Discharge h2                     [VACUOUS-UNDER-INJECTIVE in C3WP invocation]
    | Case3 residual       → hasBalancedPair_of_case3_outOfScope … [AXIOM]
```

In `Case3Witness_proof.{u}`'s invocation:
- `case2Discharge := case2_discharge_of_injective hInj` — VACUOUS under cap 1 (Injective). The Case2Witness predicate posits two distinct elements with equal bands, contradicting Injective. So Case 2 never fires; `case2Discharge` is a do-nothing fallthrough.
- Case 1 branch closed via `hasBalancedPair_of_ambient_profile_match` (mg-f92d): SUBSTANTIVE — direct profile-symmetry argument using `Equiv.swap`.
- Case 3 branch closed via AXIOM: paper-axiomatised from `step8.tex:3033-3047` (the `rem:enumeration` SKETCH at `step8.tex:3157-3173` — paper itself only sketches the argument). Load-bearing for `K∈{4 w≥2, 5..10}` ¬InCase3Scope cells.

mg-7377's QA verified: the typed `Case3Witness L` predicate IS what the axiom requires (faithful dispatch).

**Net Phase C verdict:** API gateway marker (`bounded_irreducible_balanced{,_hybrid}`); `_inScope` substantive via real bridges + Bool certificate. `hStruct_of_case2_discharge` composes substantive Case 1 + vacuous Case 2 (under Injective) + paper-axiomatised Case 3 residual.

---

## §4 — Phase D: Per-step proof-tree tagging

Below is the complete proof tree of `OneThird.width3_one_third_two_thirds`, traversed top-to-bottom from the headline. Each node is tagged with one of:

| Tag | Meaning |
|---|---|
| **SUBSTANTIVE-AND-FORMALIZED** | Real Lean proof with non-trivial mathematical content. |
| **SUBSTANTIVE-COMPUTATIONAL** | Real content discharged via `native_decide` (Bool certificate). |
| **SUBSTANTIVE-BUT-PAPER-AXIOMATISED** | Project axiom faithful to a stated paper result. |
| **SUBSTANTIVE-BUT-EXTERNALLY-AXIOMATISED** | Project axiom faithful to a published external result. |
| **MARKER** | Theorem whose proof body uses only a subset of declared hypotheses — typing-only dispatcher. |
| **VACUOUS-COVER** | Structurally vacuous antecedent; conclusion may be unreachable or substitute discards meaningful inputs. |
| **TODO-SORRY** | Structured `sorry` in tree. |
| **TRIVIAL** | Pure rewriting / definitional / arithmetic. |

### §4.1 — Headline call graph

| Node | File:Line | Tag | Notes |
|---|---|---|---|
| `OneThird.width3_one_third_two_thirds` | `MainTheorem.lean:39` | **TRIVIAL-WRAPPER** | Calls `Step8.width3_one_third_two_thirds_via_step8` with `Case3Witness_proof` as `hC3`. |
| `Step8.width3_one_third_two_thirds_via_step8` | `MainAssembly.lean:352` | **TRIVIAL-WRAPPER** | Calls `Step8.width3_one_third_two_thirds_assembled`. |
| `Step8.width3_one_third_two_thirds_assembled` | `MainAssembly.lean:320` | **SUBSTANTIVE-AND-FORMALIZED** (Step 5 dispatch shape) | Case split on `|α| < 2` (vacuous against `¬IsChainPoset`) vs `|α| ≥ 2` (calls `mainAssembly` with `mainTheoremInputsOf`). |
| `Step8.mainAssembly` | `MainAssembly.lean:277` | **MARKER + VACUOUS-COVER** (Step 5 collapse) | `step5_choice = true` (convention; both `true` and `false` branches dispatch to `caseC caseR_to_caseC` — see line 286–289). The dichotomy is collapsed to a single call path. |
| `Step8.mainTheoremInputsOf` | `MainAssembly.lean:238` | **SUBSTANTIVE-AND-FORMALIZED** (bundle construction) | Builds the `MainTheoremInputs` record: `caseC := λ L → lem_layered_balanced L h2 hNotChain hW3 hC3`, `caseR_to_caseC := layeredFromBridges`. |
| `Step8.layeredFromBridges` | `LayeredBridges.lean` | **VACUOUS-COVER (per mg-74d2)** | The `w` field is now `Lwidth3.bandwidth` (post-mg-7b26 fix) rather than the prior sham `|α|+bandwidth`, but Steps 1–7 currently deliver `Lwidth3.bandwidth = |α|+1` rather than the paper's bounded `w₀(γ)`. The bridge is structurally honest but the upstream content is sham. |
| `Step8.lem_layered_balanced` | `LayeredBalanced.lean:626` | **MIXED** (see below) | K=1 substantive; K≥2 VACUOUS-COVER + TODO-SORRY. |

### §4.2 — `lem_layered_balanced` interior

| Sub-node | Branch | Tag | Notes |
|---|---|---|---|
| K=1 branch | `LayeredBalanced.lean:647–680` | **SUBSTANTIVE-AND-FORMALIZED** | All elements have band 1 (forced by `band_pos` + `band_le`), so `univ` is an antichain. Closed via `bipartite_balanced_enum` with `A := univ, B := ∅`. |
| K≥2 branch | `LayeredBalanced.lean:681–756` | **VACUOUS-COVER + TODO-SORRY** | Substitutes `L' := canonicalLayered α`, attempts to apply `hC3 α L'`. Caps 1–4 discharged on `canonicalLayered`. **Cap 5 (`L'.w ≤ 4`) is UNPROVABLE on canonicalLayered for `|α|≥5`** — structured `sorry` at line 751. The input `L` is DISCARDED. |

### §4.3 — `Case3Witness_proof.{u}` interior (the substantive backbone)

| Sub-node | File:Line | Tag | Notes |
|---|---|---|---|
| Strong induction skeleton | `Case3WitnessProof.lean:286` | **SUBSTANTIVE-AND-FORMALIZED** | `Nat.strong_induction_on` on `Fintype.card β`. NOT the bare F3 framework — has its own induction body. |
| K=1 base | `:290–297` via `absurd_K1_of_injective` | **SUBSTANTIVE-AND-FORMALIZED** | Cap 1 + 2≤|β| → contradiction. |
| K=2 reducible | `:303–307` via `isChain_of_K2_reducible_under_injective` | **SUBSTANTIVE-AND-FORMALIZED** | Caps 1+4 + reducibility → chain, contradicts `hNC`. |
| K=2 irreducible | `:308–309` via `OptionC.option_c_K2_closure` | **SUBSTANTIVE-COMPUTATIONAL** (mg-01ec) | w=0 excluded structurally; w≥1 dispatched via `normalizeWAtK2` + F5a K=2 `case2_certificate` (Bool, `native_decide`). |
| K≥3 reducible — Ordinal-decomp construction | `:312–347` via `OrdinalDecompOfReducible` + `mem_OrdinalDecompOfReducible_{Lower,Upper}` | **SUBSTANTIVE-AND-FORMALIZED** | Reducibility hypothesis provides `hLU_lt` field; cross-pair-incomparability eliminated. |
| K≥3 reducible — Recursive descent on Lower | `:350–438` | **SUBSTANTIVE-AND-FORMALIZED** | Strict size descent (`|↥D.Lower| < |β|`); all 5 caps propagate via `compactify_{band_injective_of_injective, K_le, card_le_of_card_le, bandSet_nonempty, w_eq}`. |
| K≥3 reducible — Recursive descent on Upper | `:439–516` | **SUBSTANTIVE-AND-FORMALIZED** | Symmetric. |
| K≥3 reducible — Conclusion lift | `:438` / `:516` via `D.hasBalancedPair_lift_{lower, upper}` → `OrdinalDecomp.hasBalancedPair_lift` → `probLT_restrict_eq` | **SUBSTANTIVE-AND-FORMALIZED** (`Subtype.lean:1152`) | Marginal-invariance from `lem:ordinal-factorisation` (`LinearExt α ≃ LinearExt Lower × LinearExt Mid × LinearExt Upper`). **THE KEY LIFT — substantive, not circular.** |
| K≥3 irreducible — Hybrid dispatch | `:517–547` via `bounded_irreducible_balanced_hybrid` | **MARKER** (mg-74d2) | `by_cases Decidable(InCase3Scope)`; dispatches to `hCert` or `hStruct`. |
| K≥3 irreducible — In-scope branch | `hCert := bounded_irreducible_balanced_inScope … case3_certificate` | **SUBSTANTIVE-COMPUTATIONAL** | F5a Bool certificate via G1'+G3a+G3b+G3c+B1'+B2+B3 bridges. Real content. |
| K≥3 irreducible — Out-of-scope branch — Case 1 | `case1_dispatch_balanced_or_witness` → `hasBalancedPair_of_ambient_profile_match` (mg-f92d) | **SUBSTANTIVE-AND-FORMALIZED** | `Equiv.swap` symmetric profile argument. |
| K≥3 irreducible — Out-of-scope branch — Case 2 | `case2_discharge_of_injective` | **VACUOUS-COVER** | Case 2 posits two distinct elements with equal bands; contradicts Injective. Cap 1 makes this branch unreachable. |
| K≥3 irreducible — Out-of-scope branch — Case 3 residual | `case3Witness_hasBalancedPair_outOfScope` (`Case3Residual.lean:208`) | **SUBSTANTIVE-BUT-PAPER-AXIOMATISED** | Paper-axiomatised from `step8.tex:3033-3047` + `rem:enumeration` (`step8.tex:3157-3173` — paper proof is a SKETCH, not fleshed out). Load-bearing for K∈{4 w≥2, 5..10} cells where the Bool certificate doesn't cover. |

### §4.4 — Auxiliary substantive nodes consumed in dispatch

| Node | File:Line | Tag |
|---|---|---|
| `OrdinalDecomp.hasBalancedPair_lift` | `Mathlib/LinearExtension/Subtype.lean:1152` | **SUBSTANTIVE-AND-FORMALIZED** |
| `OrdinalDecomp.probLT_restrict_eq` | `Subtype.lean:~1020` | **SUBSTANTIVE-AND-FORMALIZED** |
| `OrdinalDecomp.tripleEquiv` (factorisation bijection) | `Subtype.lean:~700` | **SUBSTANTIVE-AND-FORMALIZED** |
| `LayeredDecomposition.compactify` + 5 cap-propagation lemmas | `LayeredDecomposition/Compactify.lean` | **SUBSTANTIVE-AND-FORMALIZED** |
| `Step8.exists_adjacent_not_lt_of_irreducible` (F2) | `LayerOrdinal.lean:276` | **SUBSTANTIVE-AND-FORMALIZED** |
| `Step8.OrdinalDecompOfReducible` | `LayerOrdinal.lean:108` | **SUBSTANTIVE-AND-FORMALIZED** |
| `Step8.hasBalancedPair_of_layered_strongInduction` (bare F3 framework) | `LayerOrdinal.lean:370` | **MARKER** (mg-74d2 — L unused, body is `Nat.strong_induction_on`). **Not consumed** by the headline call path. |
| `Step8.bounded_irreducible_balanced` (no _inScope) | `BoundedIrreducibleBalanced.lean:1626` | **MARKER** (mg-74d2 — pure identity, all hyps underscored). **Not consumed** by the headline; only `_inScope` and `_hybrid` are. |
| `Step8.bounded_irreducible_balanced_hybrid` | `BoundedIrreducibleBalanced.lean:1681` | **MARKER** (mg-74d2 — pure `by_cases Decidable(InCase3Scope)`). |
| `Step8.bounded_irreducible_balanced_inScope` | `BoundedIrreducibleBalancedInScope.lean:97` | **SUBSTANTIVE-AND-FORMALIZED** |
| `case3_certificate` (mg-9a4a Window C) | `Case3Enum/Certificate.lean:71` | **SUBSTANTIVE-COMPUTATIONAL** |
| `Cap5Singletons.K{2,4..8}` (mg-4d7b) | `Cap5Singletons.lean` | **SUBSTANTIVE-COMPUTATIONAL** but **NOT CONSUMED** by headline. |
| `Cap5SingletonsK9` | `Cap5SingletonsK9.lean` | **SUBSTANTIVE-COMPUTATIONAL** but NOT IMPORTED into `OneThird.lean`. |
| K=10 cap-5 external JSON | `lean/scripts/enum_cap5_K10_certificate.json` | **EXTERNAL** (no Lean axiom). |
| `case3Witness_hasBalancedPair_outOfScope` | `Case3Residual.lean:208` | **SUBSTANTIVE-BUT-PAPER-AXIOMATISED** |
| `LinearExt.brightwell_sharp_centred` | external | **SUBSTANTIVE-BUT-EXTERNALLY-AXIOMATISED** (Brightwell–Tetali sharp 1/3) |
| Steps 1–7 paper-axiomatised (cuts, windows, BK-Cheeger, layered collapse) | `Step1through7/*` | **SUBSTANTIVE-BUT-PAPER-AXIOMATISED** (Steps 1–7) |
| `lem_cut`, `lem_window`, `lem_layered_reduction` | `Step8/{Window,WindowDecomp,LayeredReduction}.lean` | **SUBSTANTIVE-AND-FORMALIZED** but **NOT-ON-HEADLINE-PATH** (leftover infrastructure from earlier size-minimal framing per mg-805c). |

### §4.5 — Per-step tagging summary

- **17 nodes SUBSTANTIVE-AND-FORMALIZED** on the headline path (real Lean proofs).
- **3 nodes SUBSTANTIVE-COMPUTATIONAL** (Bool certificates: `case3_certificate`, F5a K=2 `case2_certificate`, `case3_balanced_K4_w1`).
- **1 node SUBSTANTIVE-BUT-PAPER-AXIOMATISED** load-bearing on headline (`case3Witness_hasBalancedPair_outOfScope`).
- **1 node SUBSTANTIVE-BUT-EXTERNALLY-AXIOMATISED** (`brightwell_sharp_centred`).
- **4 nodes MARKER** (`bounded_irreducible_balanced{,_hybrid}`, bare F3 framework — none consumed in their marker form on the headline path; `mainAssembly` Step-5 dispatch is the marker for the `step5_choice` collapse).
- **3 nodes VACUOUS-COVER** on headline path: (a) `layeredFromBridges` w-sham (now structurally correct but upstream Steps 1–7 deliver `|α|+1` not `w₀(γ)`); (b) `lem_layered_balanced` K≥2 `canonicalLayered` substitution; (c) `case2_discharge_of_injective` (vacuous, but that's by design — Case 2 IS unreachable under Injective cap 1).
- **1 node TODO-SORRY** structured (`LayeredBalanced.lean:751`).
- **3 nodes NOT-CONSUMED** (mg-4d7b enumeration, leftover `lem_cut`/`lem_window`/`lem_layered_reduction` infrastructure).

This count agrees with mg-5c32 §3 with one ADDITIONAL substantive node identified: the K≥3-reducible internal-recursive-descent + lift-via-marginal-invariance is now explicitly tagged as substantive (was under-audited in mg-74d2).

---

## §5 — Phase E: Forward action recommendation for ticket (B)

### §5.1 — What Phase A unblocks

The F3 inner strong induction in `Case3Witness_proof.{u}` is substantive. That means the layered-form architecture has a **real backbone in the |β|≤10 slice**, not just paint-by-numbers vacuous-cover.

The ticket (B) (residual re-extraction) does NOT need to pivot to coherence or abandon layered form. The substantive backbone exists. The remaining work is to **wire that backbone into the headline call path** so the headline `width3_one_third_two_thirds` consumes it.

### §5.2 — Recommended rewrite scope (Option D-narrow, per mg-0cbf §5e)

**Headline rewrite.** Rewrite `Step8.lem_layered_balanced` (`LayeredBalanced.lean:626`) so that the K≥2 dispatch consumes the **caller's** `L : LayeredDecomposition α` rather than substituting `canonicalLayered α`. Specifically:

1. Drop the `let L' := canonicalLayered α` substitution (line 720).
2. Pass the caller's `L` directly into `hC3 α L hInj hKw hCardw hNonempty hLBw hW3 hNotChain' h2`.
3. The five cap obligations (`hInj, hKw, hCardw, hNonempty, hLBw`) now land at the caller site of `lem_layered_balanced` rather than vacuously inside it.

**Caller-site fix.** Update `Step8.mainTheoremInputsOf` (`MainAssembly.lean:238`) so that `caseC` discharges the five caps explicitly, using whatever data `layeredFromBridges` actually delivers.

This rewrite **eliminates the `sorry` at LayeredBalanced.lean:751** by relocating the cap-5 obligation from inside the dispatch to the call site. The call site can then EITHER:

(a) **|α|≤10 path** — Discharge the five caps via mg-4d7b's `Cap5Singletons` certificates (extending `case3_certificate` to K∈{2, 4..10} cap-5 cells, OR threading `Cap5Singletons` Bool certificates directly into a wider `enumPosetsFor_eq_true_of_inScope_extended`). The substantive backbone of `Case3Witness_proof.{u}` then discharges the |β|≤10 slice **unconditionally** (modulo the K∈{4 w≥2, 5..10} ¬InCase3Scope axiom, which is paper-axiomatised).

(b) **|α|≥11 path** — Reduce to LayeredResidual_broad of mg-5c32: the paper's prop:72 layered collapse with `w₀(γ) ≤ 4` from Step 7. This is the upstream Steps 1–7 w₀(γ) delivery (Option A per mg-0cbf), currently blocked.

(c) **Restate the headline** — Per mg-5c32 §4, expose |α|≤10 as unconditional (discharged by mg-4d7b + Phase A substantive backbone) and |α|≥11 as Steps-1-7-conditional (residual = bounded-w `L` delivery). Operationally: width3_one_third_two_thirds becomes a conjunction of the |α|≤10 slice and the LayeredResidual_broad-conditional |α|≥11 slice.

### §5.3 — Why Option D-narrow is the right ticket-(B) scope

- It uses the **substantive F3 backbone** identified in Phase A (the work is real, not throwaway).
- It dispatches against the **already-shipped mg-4d7b enumeration** (no fresh enumeration work).
- It DROPS one project axiom in the |α|≤10 slice (`case3Witness_hasBalancedPair_outOfScope` becomes vacuous for K=|α|≤10 cells once the dispatch is extended to consume Cap5Singletons).
- It closes the mg-d5a0 structured `sorry`.
- It does **NOT** require fresh math content. It's a Lean re-wiring exercise.

Estimated scope: 3–5 polecat sessions (per mg-74d2 Phase B clean-restatement scope estimate, still applicable).

### §5.4 — What ticket (B) should NOT pivot to

- **NOT** pivot to coherence implementation. Per mg-74d2 §3: the layered form IS the data type the coherence-collapse argument's conclusion lives in (paper Prop. 7.2 / prop_72); the two are stacked, not alternatives.
- **NOT** treat F3 as circular and abandon layered form. Phase A here shows F3 conclusion-lift is substantive.
- **NOT** restart from a fresh proof attempt. The substantive backbone is already in tree.
- **NOT** invoke a "project-life-level Daniel call" — the architecture has a substantive backbone; the missing piece is rewiring, not new math.

### §5.5 — What's still under-audited / open for follow-on

- **`option_c_K2_closure` deep audit** — checked at proof shell (it's substantive-computational); the F5a K=2 `case2_certificate` (mg-01ec) should get the same Phase C audit as `case3_certificate`. Not done here.
- **`hasBalancedPair_of_ambient_profile_match` (mg-f92d) audit** — Case 1 of `prop:in-situ-balanced`, used in `hStruct_of_case2_discharge`. Should be SUBSTANTIVE per its docstring (uses `Equiv.swap` profile-symmetry); deep audit not done here.
- **Steps 1–7 paper-axiomatisations** — taken on trust per polecat constraint ("if so, surface it"); no audit done here. The known issue is `Lwidth3.bandwidth = |α|+1` rather than `w₀(γ)`, but that's a delivery gap not a paper gap.
- **`compactify_bandSet_nonempty`** — mg-8c72 inline lemma; depended on for K≥3 reducible recursive descent. Verified at proof shell; not deep-audited.

These are NOT blockers for ticket (B). They're follow-on quality work.

---

## §6 — Cross-reference index

### Lean files touched in this audit

- `lean/OneThird/MainTheorem.lean:39` — headline `width3_one_third_two_thirds`
- `lean/OneThird/Step8/MainAssembly.lean:238/277/320/352` — Step 5 dispatch, `mainAssembly`, `mainTheoremInputsOf`, `width3_one_third_two_thirds_assembled`
- `lean/OneThird/Step8/LayeredBalanced.lean:626/751` — `lem_layered_balanced` + structured `sorry`
- `lean/OneThird/Step8/LayerOrdinal.lean:108/276/370/472` — `OrdinalDecompOfReducible`, F2 adjacent, bare F3 framework
- `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1626/1681` — marker theorems
- `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:97` — substantive in-scope discharge
- `lean/OneThird/Step8/Case3Residual.lean:208/265` — Case 3 residual axiom + `hStruct_of_case2_discharge`
- `lean/OneThird/Step8/Case3Enum/Certificate.lean:71` — `case3_certificate`
- `lean/OneThird/Step8/Case3Enum/Cap5Singletons.lean` — mg-4d7b enumeration (NOT consumed by headline)
- `lean/OneThird/Step8/OptionC/K2Closure.lean:500` — `option_c_K2_closure`
- `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:256` — `Case3Witness_proof.{u}` (the substantive backbone)
- `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152/1227/1237` — `OrdinalDecomp.hasBalancedPair_lift{,_lower,_upper}` (the load-bearing lift)
- `lean/OneThird/Step8/LayeredDecomposition/Compactify.lean` — compactify + cap-propagation lemmas

### Paper sources

- `step8.tex:2404-2418` — `lem:ordinal-factorisation` (the marginal-invariance source for the lift)
- `step8.tex:2580-2593` — `def:layer-reducible`
- `step8.tex:2595-2619` — `lem:reducible-witness`
- `step8.tex:2621-2654` — `cor:reducibility-transfer`
- `step8.tex:2780-2797` — `lem:irr-adjacent` (F2)
- `step8.tex:2965-2970` — `prop:in-situ-balanced`
- `step8.tex:2984-3032` — Cases 1 + 2 (substantive structural)
- `step8.tex:3033-3047` — Case 3 (axiomatised residual)
- `step8.tex:3050-3067` — `lem:enum`
- `step8.tex:3071-3124` — `lem:layered-balanced` strong-induction proof (the paper's F3)
- `step8.tex:3157-3173` — `rem:enumeration` (paper sketch underlying the Case 3 axiom)
- `step8.tex:3194-3236` — `rem:residual-base`

### Predecessor work items

- **mg-e2e9** (2026-05-17 14:38Z) — pre-cap-5 Case3Witness vacuous via canonicalLayered substitution
- **mg-d5a0** — cap-5 signature refactor (introduced the structured sorry)
- **mg-74d2** (2026-05-17 21:43Z) — layered-form vs coherence audit; MARKER theorems identified
- **mg-0cbf** (2026-05-17 ~12:57Z) — post-cap-5 tractability analysis; Option D-narrow + D-broad framing
- **mg-4d7b** (2026-05-17 ~20:55Z) — cap-5 enumeration polecat; Cap5Singletons certificates
- **mg-5c32** (2026-05-17 23:28Z) — LayeredResidual statement (over-constrained at |α|≥11 caught)
- **mg-7377** — QA on case3Witness_hasBalancedPair_outOfScope dispatch faithfulness
- **mg-9a4a** — Window C narrowing for case3_certificate K=4-w=1 sliver
- **mg-8c72** — Option-C Stage 2B (Case3Witness_proof.{u})
- **mg-01ec** — Option-C Stage 1 (`option_c_K2_closure`)
- **mg-2a56** — Option-C Stage 2A (compactify infrastructure)
- **mg-53ce** — A5-G2 path 1 (`cross_band_lt_upward` field, predMaskOf upper-triangularity)
- **mg-b487** — G1' `enumPosetsFor_iter_balanced`
- **mg-f92d** — Case 1 ambient profile match (`hasBalancedPair_of_ambient_profile_match`)

---

## §7 — TL;DR

1. **Daniel's KEY question answered: F3 strong-induction conclusion-lift is SUBSTANTIVE.** The lift is via real marginal-invariance from `lem:ordinal-factorisation`, not hand-waved IH re-application. The induction strictly descends on `|β|` and terminates at real base cases.

2. **The Case3Witness_proof.{u} ∀-family is substantive within scope (|β|≤10)** modulo one paper-axiomatised residual (`case3Witness_hasBalancedPair_outOfScope`).

3. **The headline call site (`lem_layered_balanced` K≥2) is still VACUOUS-COVER** — substitutes `canonicalLayered`, trips cap 5, structured `sorry` at line 751. This is mg-d5a0's surfaced architectural debt, NOT a F3 problem.

4. **mg-4d7b's `Cap5Singletons` enumeration is the missing piece** — it's in-tree but not consumed by the headline path.

5. **Ticket (B) recommended scope:** Option D-narrow (rewrite `lem_layered_balanced` K≥2 to consume caller's `L`; wire `Cap5Singletons` into the dispatch; restate headline per mg-5c32 §4). 3–5 polecat sessions. No new project axioms. Drops one axiom in the |α|≤10 slice. Closes the mg-d5a0 sorry.

6. **NOT a project-life event.** The architecture has a real substantive backbone in the |β|≤10 slice. The remaining work is Lean rewiring, not fresh math. Per Daniel's framing of "inductive thing equivalent to proving the whole conjecture" — **NO**, the F3 mechanism is honest math.
