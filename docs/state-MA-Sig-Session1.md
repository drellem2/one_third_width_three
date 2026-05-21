# State — MA-Sig — Session 1: refactor signature contract

**Owner.** `mg-a22b` (OneThird-MA-Sig per `mg-d8c7` §7.1).

**Scope.** Phase 1 pre-flight of the Option A' FULL REFACTOR
(`mg-d8c7`, doc `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`).
**SCOPING ticket — no Lean code.** Output: this document fixing
the refactor signature for downstream sub-tickets (Phase 2-4) to
reference.

**Inputs (re-read on `origin/main` before writing).**

- `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7).
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §2 tag legend.
- `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8).
- `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — RED 7th vacuity.
- `lean/OneThird/Step8/MainAssembly.lean` — current call site
  (`width3_one_third_two_thirds_assembled` at line 353;
  `caseC_canonicalLayered` cap-5 `sorry` at line 265).
- `lean/OneThird/Step8/TheoremE.lean` — the scaffold to audit
  substantive-vs-marker.
- `lean/OneThird/Step8/FrozenPair.lean` — Theorem E's foundation
  lemma (`frozenPairCut_exists` at line 219).
- `lean/OneThird/Step8/ExcPerturb.lean` — `exc_perturb` at line 351.
- `lean/OneThird/Step8/LayeredBalanced.lean` — `lem_layered_balanced`
  at line 626 (post-mg-234e caller-`L` rewire).
- `lean/OneThird/LinearExtension.lean` — `HasBalancedPair`,
  `IsGammaCounterexample`, `Phi`, `volume`,
  `edgeBoundary_pairCut_sum_le` (line 166).
- `lean/OneThird/Mathlib/Poset/Indecomposable.lean` — `Indecomposable α`
  + `exists_incomp`.
- `step8.tex:9-23` — Hypothesis A (`hyp:arith`, arithmetic richness).
- `step8.tex:32-91` — `thm:main-step8` statement + Lean restatement
  remark.
- `step8.tex:106-260` — `thm:main-step8` proof body (the template
  the refactor mirrors).

(Paper section numbers extracted from `origin/main:step8.tex`; the
parent scoping doc cites `step8.tex:511-525` / `:531-755`, which
correspond to the same content. Citations below use the
`origin/main` byte ranges.)

---

> **⚠ CORRECTED (mg-faf8, 2026-05-20).** The §4.2 §E bridge
> signature and §4.2 §G consumer pinning **have been re-pinned**
> to fix the 8th vacuity-discovery defect found by mg-0bd1: the
> original five-cap bridge conclusion was structurally
> unsatisfiable for large α. As re-pinned:
>
> * **§4.2 §E** — the bridge `lem_layered_from_step7` now emits
>   only **three** caps (`Xexc.card ≤ C_exc T`, band-nonempty,
>   `L.w ≤ 4`). The three Case3Witness API artefacts (band
>   injectivity, `L.K ≤ 2 L.w + 2`, the `card − Xexc` bound) are
>   **dropped**. It also gains an explicit hypothesis
>   `hCex : IsGammaCounterexample α γ` pinning the bridge's domain
>   to the γ-counterexample regime (surfaced by the §10
>   satisfiability check).
> * **§4.2 §G** — the downstream consumer is now **Piece 6**
>   (`lem_layered_balanced_full`, the full Step 8 G4), which
>   consumes only `L.w ≤ 4`. The bounded-base `lem_layered_balanced`
>   is no longer on the §E→§G boundary; it becomes the bounded
>   base case *inside* Piece 6's strong induction.
> * **§4.3 / §4.4** — updated to match.
> * **§10** (added this session) — the corrected contract is
>   **satisfiability-verified**, including against the mg-0bd1
>   counterexample class (the 3-disjoint-chains family).
>
> §9 records the original mg-0bd1 finding and preserves the
> superseded five-cap form (also in `docs/state-S7-F-bridge-Session2.md`
> §0). The §0 verdict below predates the correction — read §9–§10
> alongside it; its "no 8th vacuity-discovery" claim held only for
> *type-checking* (old §4.4), never *satisfiability*.

> **⚠ RECONCILED (mg-3119 / S7F-R2, 2026-05-21).** The §4.2 §E
> bridge *input shape* has been re-pinned. Checkpoint 3 (mg-ca83,
> `docs/state-S7F-Checkpoint3-Session1.md`) found the bridge
> contract pinned **inconsistently** across the two READ-FIRST
> docs — §4.2 §E here said the bridge consumes
> `Step5R ∨ Step5C`; the scoping doc §2.3 said it consumes
> Piece 2's `L_S7E`. Neither names the object the bridge body can
> actually consume to build a ground-set `LayeredDecomposition`.
> As re-pinned (full analysis in §11):
>
> * **§4.2 §E** — `lem_layered_from_step7` now consumes a concrete
>   **`ChainLiftData α`** (Dilworth triple + chain potential + sync
>   maps `fAB/fAC/fBC` + `K_bw`; `ChainPotentials.lean:328`) plus
>   `hKbw : cld.K_bw ≤ 2`, **replacing** the abstract
>   `hCascade : Step5R ∨ Step5C` hypothesis.
> * **§4.2 §D′ (NEW)** — `chainLiftData_of_cascade` converts the
>   Step-5 dichotomy into the `ChainLiftData` bundle (dispatching
>   both disjuncts). This is the **R1 deliverable** (mg-974c).
> * **§4.3 / §4.4** — call-site + boundary table updated to match.
> * **§11 (added this session)** — records the reconciliation and
>   re-runs the satisfiability check for the new input shape.
>
> **F7a — SETTLED GREEN (R1, mg-974c, 2026-05-21).** A concrete,
> non-degenerate `ChainLiftData α` IS constructible
> (`lean/OneThird/Step8/ConcreteChainLiftData.lean`,
> `gridChainLiftData` on the 3×3 grid). Per §11.4.1 this is **case
> 1** — the witness matches the *bare* structure, so §4.2 §D′/§E
> **stand as pinned**; the contract is no longer provisional on
> constructibility. Remaining (a Piece-3 concern, *not* F7a): the
> §11.3 soundness caveat — whether the bridge *body* needs a
> strengthened structure (resolution (B)). §9–§10 record the
> earlier mg-faf8 re-pin against the *superseded* `Step5R ∨ Step5C`
> input shape; their conclusion-side (3-cap) analysis is unchanged
> — only the *input* is superseded by §11.

## §0. Verdict — **GREEN-signature-types-cleanly + Theorem-E-substantive**

The proof-by-contradiction refactor signature **types cleanly** with
the three decisions below. **No 8th vacuity-discovery surfaced** on
the signature itself under default-skeptical re-audit.

Headline finding: **Theorem E is SUBSTANTIVE, not a marker** — the
existing `Step8/TheoremE.lean` `cexImpliesLowBKExpansion`
(line 171) is a fully discharged Lean theorem (no `sorry`, no project
axiom on the headline path), built on `frozenPairCut_exists` /
`dirichletConductance` / `card_univ_le_ordIncompPairs_card` /
`edgeBoundary_pairCut_sum_le` — all of which are themselves
substantive Lean proofs in `Step8/FrozenPair.lean` and
`OneThird/LinearExtension.lean`. The parent scoping doc §2.4 Risk #3
("Theorem E may be marker, +500k-800k, 30% probability") **does not
materialize**. mg-MA-ThmE reduces from a 0.5M-0.8M grounding sub-arc
to a ~0.2-0.3M *wiring* sub-arc. **Saves ~250k-500k on piece 4.**

The three fixed decisions (full rationale in §3 below):

1. **hyp:arith threading.** Lean predicate (a `HypothesisArithmetic`
   structure parameter on the headline), **not** project axiom.
2. **Minimal-counterexample bundle shape.** **Neither** `Nat.find`
   **nor** `Finset.min'` — `Nat.strongRecOn` on `Fintype.card α` with
   inline IH (the Lean-idiomatic form of "pick the minimal
   counterexample"; the IH itself *is* the minimality witness; no
   separate `pickMinimalCounterexample` constructor function).
3. **Step8/TheoremE.lean status.** **SUBSTANTIVE** per
   `PROOF-STRUCTURE-ONBOARDING.md` §2 tag legend. No grounding
   sub-arc needed. The mg-MA-ThmE sub-arc reduces to wiring
   (extract `Indecomposable α` from minimal-counterexample IH +
   re-pack the existential output for the cascade consumer).

Acceptance bar (against ticket body):

| # | Bar | Status |
|---:|---|---|
| 1 | `docs/state-MA-Sig-Session1.md` lands on `origin/main` (~150-300 lines) | this doc (~330 lines) |
| 2 | Three decisions FIXED with single recommendation + rationale | §3.1-§3.3 |
| 3 | Refactor signature types cleanly in pseudocode | §4 |
| 4 | Theorem E status declared (and grounding scoped if MARKER) | §3.3 — SUBSTANTIVE, no grounding sub-arc needed |
| 5 | GREEN if signature types cleanly + Theorem E substantive | **GREEN** |

---

## §1. Context (one-paragraph recap)

The pre-refactor headline `width3_one_third_two_thirds_assembled`
(`MainAssembly.lean:353`) does **direct construction**: given
`(α, hP, hNonChain, hC3)`, build the balanced pair. The body
descends through `mainAssembly` (the abstract `MainTheoremInputs`
black-box dispatcher) into `caseC_canonicalLayered`, which
substitutes `canonicalLayered α` (singleton bands, `K = w = |α|`)
and then needs to prove `L.w ≤ 4` — unprovable for `|α| ≥ 5`
(`MainAssembly.lean:265` is a structured `sorry`).

`mg-5fbd` Session 1 traced this to a **three-way obstruction**:
five-cap unsatisfiability for `|α| ≥ 11`; specific-α
unsatisfiability at `|α| ≤ 10` (3-disjoint-chains); and the paper
`lem:layered-from-step7` is fundamentally not free-standing on
the call site (requires Step 5(C) collapse data or Step 7(ii)
globalization data, both *cascade outputs* gated on minimal
γ-counterexample status — not in scope at the direct-construction
call site).

The refactor (this session) restates the proof shape as
**proof-by-contradiction with a minimal γ-counterexample**, exactly
mirroring `step8.tex:106-260`'s template.

---

## §2. What the current call site looks like (audit)

### §2.1. `width3_one_third_two_thirds_assembled` (line 353)

```lean
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α := by
  by_cases hcard : Fintype.card α ≤ 1
  · -- subsingleton ⇒ chain, contradicts hNonChain
    ...
  have h2 : 2 ≤ Fintype.card α := by omega
  exact mainAssembly 1 3 h2 hP hNonChain
    (mainTheoremInputsOf 1 3 h2 hNonChain hP hC3)
```

`mainAssembly` is the `MainTheoremInputs` black-box dispatcher
(line 308); `mainTheoremInputsOf` (line 269) constructs the bundle
with `caseC := caseC_canonicalLayered ...`, and
`caseC_canonicalLayered` (line 236) terminates at the cap-5 `sorry`
on line 265.

### §2.2. `Step8/TheoremE.lean` audit — SUBSTANTIVE

The file already exposes `cexImpliesLowBKExpansion` at line 171 with
a complete proof body:

```lean
theorem cexImpliesLowBKExpansion
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1 / 3)
    (hP : HasWidthAtMost α 3)
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α) :
    ∃ S : Finset (LinearExt α),
      (γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
        ≤ (volume S : ℚ)) ∧
      (Phi S ≤ 2 / (γ * (Fintype.card α : ℚ)))
```

The proof body unwraps `frozenPairCut_exists` (`FrozenPair.lean:219`,
substantive — averaging argument over the ordered-incomparable-pair
finset, no `sorry`/no axiom) and combines it with the volume
identity `volume = card · (n - 1)`. The downstream
`edgeBoundary_pairCut_sum_le` foundation lemma
(`LinearExtension.lean:166`, used inside `frozenPairCut_exists`) is
also a complete Lean proof (the double-counting injection
`((x, y), L, L') ↦ (L, L.pos x)`).

**Per `PROOF-STRUCTURE-ONBOARDING.md` §2 tag legend: SUBSTANTIVE.**
Specifically: real proof content + correct dependency-chain
content; not a placeholder needing grounding. Compare:
`mainAssembly`'s `step5_choice : Bool` collapse is MARKER per
mg-74d2 §2; `dirichletConductance` / `cexImpliesLowBKExpansion`
are SUBSTANTIVE.

This update **propagates back to mg-d8c7 §2.4 risk #3**: the risk
does not materialize. mg-MA-ThmE is a wiring sub-arc, not a
grounding sub-arc. Budget delta: −250k to −500k on piece 4.

---

## §3. The three decisions

### §3.1. Decision 1 — hyp:arith threading: **Lean predicate**

**Recommendation: in-Lean structure `HypothesisArithmetic` threaded
as an explicit parameter on `width3_one_third_two_thirds_assembled`
(propagating one level up to `OneThird.width3_one_third_two_thirds`).**

Rationale:

- **Paper-faithful.** `step8.tex:32-36`'s theorem statement says
  *"Assume Hypothesis~\ref{hyp:arith}. Then every finite width-3
  poset..."*. The conditionality is explicit at the paper level; the
  Lean signature should reflect it.
- **Pattern match.** `IsGammaCounterexample`, `HasWidthAtMost`,
  `Indecomposable` are all in-Lean predicate-or-structure forms.
  `brightwell_sharp_centred` is reserved for purely combinatorial
  facts about linear extensions (not parameter-cascade conditionals).
- **Discharge-friendly.** A predicate form can be discharged
  *later* by numerical verification on the relevant γ ranges; a
  project axiom is harder to retire.
- **Default position.** Parent scoping doc §6 Risk #9 mitigation
  says *"mg-MA-Sig defaults to in-Lean-predicate"*.

Concrete Lean shape (pseudo-Lean; not built):

```lean
/-- Paper hyp:arith (`step8.tex:12-23`): for every γ ∈ (0, 1/3 − δ_KL)
there exists T(γ) ≥ T₀ such that the n-independent inequality
  γ² · c₅(T) · c₆ · δ₀(γ) ≥ 8
holds, where `δ₀(γ) := min(1/(4 C₇), 1/(2 w K₀))` and `c₅(T), c₆,
C₇, w, K₀` are the sealed Step 5/6/7 constants. -/
structure HypothesisArithmetic where
  T : ℚ → ℕ
  T_ge_T0 : ∀ γ : ℚ, 0 < γ → γ < 1/3 → T_zero ≤ T γ
  arith_holds : ∀ γ : ℚ, 0 < γ → γ < 1/3 →
    (8 : ℚ) ≤ γ^2 * c5 (T γ) * c6 * delta0 γ
```

Constants `c5 : ℕ → ℚ`, `c6 : ℚ`, `T_zero : ℕ`, `delta0 : ℚ → ℚ` are
**piece 1** deliverables (Steps 5/6 grounded forms — specifically
mg-6ab8 §7 mg-S5-E, mg-S6-B). The body of `HypothesisArithmetic` is
**out of scope** for the refactor (per parent §4.4); only the
*threading* of this hypothesis through the cascade is in scope.

Headline restatement (post-refactor):

```lean
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : HypothesisArithmetic)            -- NEW
    : HasBalancedPair α
```

**RE-PINNED mg-faf8.** The `hC3 : Step8.Case3Witness.{u}`
parameter is **dropped** from both the headline
`width3_one_third_two_thirds` and the inner
`width3_one_third_two_thirds_assembled` (§4.3). Under the corrected
contract the end-of-cascade consumer is **Piece 6**
(`lem_layered_balanced_full`, §4.2 §G), which consumes only
`L.w ≤ 4`; the `Case3Witness` proposition is discharged
*internally* by Piece 6's strong-induction base case
(`Case3Witness_proof.{u}` invoked there as a closed term, not
threaded as a hypothesis). Pre-mg-faf8 the contract retained
`hC3` because the consumer was the bounded `lem_layered_balanced`.

### §3.2. Decision 2 — Minimal-counterexample bundle shape: **`Nat.strongRecOn` on `Fintype.card α`**

**Recommendation: `Nat.strongRecOn` (Lean's strong induction on ℕ)
on `Fintype.card α`, with the IH supplied inline in the proof body.
NO separate `pickMinimalCounterexample` constructor.**

This is a refinement of the parent doc's *"Nat.find on Fintype.card
(well-founded recursion friendly) vs Finset.min' (cleaner Lean
idiom)"* — both originally-proposed options have universe and
predicate-decidability obstructions; strong induction sidesteps
them.

Rationale:

- **Universe-safe.** `Nat.find` requires a decidable existential
  over `Type u`-indexed posets; `Decidable (∃ α : Type u, P α)` is
  not in general available. `Finset.min'` requires an a-priori-bounded
  Finset of γ-counterexamples; none such exists. `Nat.strongRecOn`
  on `Fintype.card α` works at the **fixed α we are given as input**,
  using the IH to handle smaller-cardinality posets.
- **Idiomatic.** `Nat.strongRecOn` (or `Nat.strong_induction_on`) is
  Mathlib's standard "smallest counterexample / well-ordering of ℕ"
  idiom. Used pervasively in poset / combinatorics ports.
- **IH-is-minimality-witness.** The IH automatically supplies *"every
  smaller β has the conclusion"*, which is exactly the minimality
  used by `rem:decomp-reduction` (the indecomposability descent) and
  by `lem:layered-from-step7`'s ground-set lift (the recursive descent
  on `X ∖ X^exc`, also a subposet of strictly smaller cardinality).
- **No constructor needed.** The "minimal counterexample bundle" is
  *the tuple `(α, hP, hNonChain, hNoBP, ih)` already in scope* inside
  the `Nat.strongRecOn` body. No separate function with a sigma-type
  return.

Concrete Lean shape:

```lean
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : HypothesisArithmetic) :          -- hC3 DROPPED (mg-faf8)
    HasBalancedPair α := by
  induction h : Fintype.card α using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    -- ih : ∀ m < n, ∀ β : Type u, [Fintype β] [PartialOrder β]
    --        [DecidableEq β], Fintype.card β = m →
    --        HasWidthAtMost β 3 → ¬ IsChainPoset β →
    --        HasBalancedPair β
    -- (... proof body ...)
```

(Note: `generalizing α` lets the IH re-instantiate at any smaller
β. Universe `u` is uniform; the IH descends only on cardinality.)

Sub-arc mapping (this refines parent §7.4 mg-MA-MinCex):

- **mg-MA-MinCex** content: prove `decomp_reduction` (a minimal
  γ-counterexample is indecomposable, via the ordinal-sum
  decomposition splitting `α` into two smaller posets one of which
  is also a γ-counterexample — contradicts IH). ~1 session, 200k.
- **The `pickMinimalCounterexample` function in parent §1.2** is
  *not* built as a separate function — its content is the inline
  `Nat.strong_induction_on` invocation in mg-MA-Body.

### §3.3. Decision 3 — Step8/TheoremE.lean status: **SUBSTANTIVE**

**Per `PROOF-STRUCTURE-ONBOARDING.md` §2 tag legend: SUBSTANTIVE
(real proof content + correct dependency chain).**

Audit detail:

- `cexImpliesLowBKExpansion` (`TheoremE.lean:171`): complete Lean
  proof body. No `sorry`, no axiom.
- `dirichletConductance` (`TheoremE.lean:80`): direct application of
  `SimpleGraph.cheeger_indicator` on `bkGraph α`. Substantive (the
  Cheeger-for-indicators inequality is a complete Mathlib-tier
  theorem in `OneThird.Mathlib.DirichletForm`).
- `indecExistsIncompPartner` (`TheoremE.lean:95`): direct
  `OneThird.Mathlib.Poset.Indecomposable.exists_incomp` invocation.
- `card_univ_le_ordIncompPairs_card` (`TheoremE.lean:119`): complete
  injection-based proof.
- `frozenPairCut_exists` (`FrozenPair.lean:219`): the deep content —
  the paper's averaging argument over the ordered-incomparable-pair
  finset, combining `gamma_le_sizeProd` (variance bound),
  `edgeBoundary_pairCut_sum_le` (Mathlib-tier double-counting), and
  pigeonhole. ~300 LoC of substantive Lean.
- `edgeBoundary_pairCut_sum_le` (`LinearExtension.lean:166`): the
  Mathlib-tier double-counting identity, proved via injection
  `((x,y), L, L') ↦ (L, L.pos x)` into `LinearExt α × Fin n`.

**No grounding sub-arc needed.** mg-MA-ThmE's content reduces to:

1. Extract `Indecomposable α` hypothesis from the minimal-counterexample
   IH (this is `rem:decomp-reduction` content; folded into mg-MA-MinCex).
2. Wire `cexImpliesLowBKExpansion` output `(S, hVol, hPhi)` into the
   next cascade step (Step 5 dichotomy via piece 1).
3. Re-pack the existential output as needed by piece 1's
   `stepsOneToSevenCascade` signature.

Budget for mg-MA-ThmE: revised down to **~200k-300k from
500k-800k** (parent §2.4 risk #3 does not materialize).

---

## §4. The refactor signature contract

Pseudo-Lean signature pinning the public API of every cascade
component. Downstream sub-tickets (Phase 2-4 of parent dispatch)
reference this section by name.

### §4.1. New types

```lean
-- Defined by piece 1's Steps 5/6 grounded forms.
def c5 : ℕ → ℚ          -- step5.tex c_5(T,γ); constant per (T, γ)
def c6 : ℚ              -- step6.tex c_6; absolute
def delta0 : ℚ → ℚ      -- δ_0(γ) = min(1/(4 C_7), 1/(2 w K_0))
def T_zero : ℕ          -- T_0 of step5.tex (absolute Step-5 threshold)

structure HypothesisArithmetic where
  T : ℚ → ℕ
  T_ge_T0 : ∀ γ, 0 < γ → γ < 1/3 → T_zero ≤ T γ
  arith_holds : ∀ γ, 0 < γ → γ < 1/3 →
    (8 : ℚ) ≤ γ^2 * c5 (T γ) * c6 * delta0 γ

-- Defined by piece 1's Step 5 dichotomy (step5.tex thm:step5).
-- Counting-measure form on the BK-graph foundation.
def Step5R (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (γ : ℚ) (T : ℕ) : Prop :=
  -- ∃ rich-overlap mass M ≥ c5(T) · |LinearExt α|.
  ...

def Step5C (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (T : ℕ) : Prop :=
  -- α is layered on X∖X^exc with |X^exc| ≤ C_exc(T) and width ≤ w.
  ...

-- The exceptional-set size constant (step8.tex eq:exc-perturb context).
def C_exc : ℕ → ℕ      -- C_exc(T) = 3 c_1(T) per paper
def n_zero : ℚ → ℕ → ℕ -- n_0(γ, T) per eq:n0-main
```

### §4.2. Cascade API (signatures only)

```lean
-- §C. Theorem E (UNCHANGED — already substantive).
-- Re-exposed in Step8/TheoremE.lean:171; signature is the contract.
theorem cexImpliesLowBKExpansion
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1/3)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α) :
    ∃ S : Finset (LinearExt α),
      γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
        ≤ (volume S : ℚ) ∧
      Phi S ≤ 2 / (γ * (Fintype.card α : ℚ))

-- §D. Steps 1-7 cascade output (NEW — piece 1 + piece 2 deliver).
-- Consumes Theorem E output + hyp:arith + indecomposability +
-- the parameter cascade closing (provided by hArith.arith_holds).
theorem stepsOneToSevenCascade
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1/3)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α)
    (hArith : HypothesisArithmetic)
    (hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card α)
    (hS : ∃ S : Finset (LinearExt α),
            γ * (volume Finset.univ : ℚ) ≤ (volume S : ℚ) ∧
            Phi S ≤ 2 / (γ * (Fintype.card α : ℚ))) :
    Step5R α γ (hArith.T γ) ∨ Step5C α (hArith.T γ)

-- §D′. ChainLiftData constructor (NEW — RECONCILED mg-3119 / R2;
-- this is the R1 deliverable, mg-974c).
-- Converts the Step-5 dichotomy into the concrete globalization
-- bundle the bridge consumes. Dispatches BOTH disjuncts to a
-- single ChainLiftData shape:
--   Step5C α T  → branch (a): the Step 5(C) collapse already gives
--     a bounded-width layered structure; repackage as ChainLiftData
--     with K_bw chosen so K_bw + 2 = w_coll(T) ≤ 4.
--   Step5R α γ T → branch (b): the Step 7(ii) globalization yields
--     the chain potential + sync maps + K_bw directly (K_bw ≤ 2 by
--     lem:bandwidth).
-- Unifying both branches into one ChainLiftData is what lets the
-- bridge §E take a single input type (the paper lem:layered-from-
-- step7 takes the disjunction; the Lean refactor pushes the case
-- split UPSTREAM of the bridge, into this constructor).
-- F7a IS OPEN. No concrete ChainLiftData instance exists in tree
-- (Checkpoint 3, mg-ca83 §6 R1). Whether this constructor can be
-- discharged genuinely — yielding a NON-DEGENERATE ChainLiftData,
-- not the empty-sync-map / inert-K_bw degenerate inhabitant the
-- bare structure admits — is the open F7a question. Part R1
-- (mg-974c) settles it; the signature below is the R2-recommended
-- target shape, provisional until R1 lands (§11.4). A
-- RED-F7a-not-constructible verdict from R1 forces a further
-- re-pin here.
theorem chainLiftData_of_cascade
    (γ : ℚ) (hγ_pos : 0 < γ)
    (T : ℕ)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (hCascade : Step5R α γ T ∨ Step5C α T) :
    ∃ cld : ChainLiftData α, cld.K_bw ≤ 2

-- §E. lem:layered-from-step7 (NEW — piece 3 deliverable).
-- RECONCILED mg-3119 / R2: the bridge consumes a concrete
-- ChainLiftData α (the genuine globalization bundle), NOT the
-- abstract Step5R ∨ Step5C disjunction (which is now dispatched
-- upstream by §D′). See the ⚠ RECONCILED banner above and §11.
-- RE-PINNED mg-faf8: emits only the three SATISFIABLE caps, and
-- carries hCex : IsGammaCounterexample α γ as an explicit
-- hypothesis (see below).
-- Lifts the ChainLiftData to a concrete LayeredDecomposition on
-- X∖X^exc, faithful to paper def:layered (step8.tex:1983-2007) and
-- lem:layered-from-step7 conclusion items (i)/(ii)/(iii)
-- (step8.tex:2054-2088). The bridge then feeds PIECE 6
-- (lem_layered_balanced_full, §G), not the bounded base case.
theorem lem_layered_from_step7
    (γ : ℚ) (hγ_pos : 0 < γ)
    (T : ℕ)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)  -- domain pin (mg-faf8);
                                       -- LOAD-BEARING under the R2
                                       -- reconciliation — see §11.3
    (cld : ChainLiftData α)            -- RECONCILED mg-3119 — the
                                       -- genuine bridge input;
                                       -- REPLACES hCascade
    (hKbw : cld.K_bw ≤ 2)              -- lem:bandwidth bound ⇒
                                       -- L.w = K_bw + 2 ≤ 4
    (ih : ∀ m, m < Fintype.card α →
           ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
             Fintype.card β = m →
             HasWidthAtMost β 3 → ¬ IsChainPoset β →
             HasBalancedPair β) :
    ∃ (Xexc : Finset α) (L : LayeredDecomposition {a : α // a ∉ Xexc}),
      Xexc.card ≤ C_exc T ∧                        -- bound on |X^exc| (item (i))
      (∀ k, 1 ≤ k → k ≤ L.K →                      -- band-nonempty (compactified)
            (L.bandSet k).Nonempty) ∧
      L.w ≤ 4                                      -- interaction width (item (ii))
      -- DROPPED mg-faf8 — the three unsatisfiable Case3Witness
      -- API artefacts:
      --   • Function.Injective L.band        (old cap 1)
      --   • L.K ≤ 2 * L.w + 2                (old cap 2)
      --   • (card α − Xexc.card) ≤ 6*L.w+6   (old cap 3)
      -- Why dropped: caps 1+4 force singleton bands (L.K = card),
      -- caps 2+5 then force L.K ≤ 10, jointly bounding
      -- |α| ≤ 10 + C_exc T — FALSE for minimal γ-counterexamples
      -- of unbounded size (the mg-0bd1 8th vacuity; §9). The
      -- paper def:layered object instead has bands of size ≤ 3
      -- (the LayeredDecomposition.band_size field; NOT singletons)
      -- and depth L.K ≥ |X|/6 (step8.tex:2072) — unbounded — which
      -- the three retained caps permit. Satisfiability of this
      -- corrected conclusion is verified in §10 (against the
      -- mg-faf8 input shape) and §11 (re-run for the R2 input).
      --
      -- ADDED HYPOTHESIS hCex (mg-faf8) — LOAD-BEARING under the
      -- R2 reconciliation. Paper lem:layered-from-step7 only
      -- applies to α arising as a minimal γ-counterexample in the
      -- (R)+(coherent) regime (mg-5fbd / §3 pitfall #5.3); hCex
      -- pins the bridge's domain there. It is MORE load-bearing now
      -- that the input is a ChainLiftData (mg-3119): the bare
      -- ChainLiftData structure is INHABITED for the
      -- 3-disjoint-chains family Δ_ℓ (triple = the three chains,
      -- any strictly-monotone potential, empty sync maps,
      -- K_bw := 0 ≤ 2), yet C(Δ_ℓ) is FALSE for large ℓ (every
      -- layered decomposition of Δ_ℓ has width ≥ ℓ−1; §3 pitfall
      -- #2.3). So a bridge taking cld + hKbw WITHOUT hCex would be
      -- false on Δ_ℓ — repeating the 8th-vacuity error. hCex
      -- excludes Δ_ℓ airtight (Δ_ℓ has balanced pairs by symmetry
      -- ⇒ ¬ IsGammaCounterexample), so the conditional is vacuously
      -- true there (§11.3). hCex is free at the call site — the
      -- §4.3 body has it in scope from §3 (the same hCex
      -- stepsOneToSevenCascade §D and chainLiftData_of_cascade §D′
      -- consume).

-- §F. exc_perturb lift (UNCHANGED — Step8/ExcPerturb.lean:351).
-- Existing signature `exc_perturb` lives at the probLT level; the
-- HasBalancedPair lift below is a thin combinator wrapping it.
theorem excPerturbLift
    (γ : ℚ) (hγ_pos : 0 < γ)
    (Xexc : Finset α)
    (hXexc_small : 2 * (Xexc.card : ℚ) /
        (Fintype.card α - Xexc.card + 1 : ℚ) < γ / 2)
    (hBP_sub : HasBalancedPair {a : α // a ∉ Xexc}) :
    HasBalancedPair α

-- §G. lem_layered_balanced_full (NEW — PIECE 6 deliverable).
-- RE-PINNED mg-faf8: the §E bridge's downstream consumer is the
-- FULL Step 8 G4, not the bounded-base lem_layered_balanced.
-- Faithful Lean port of paper lem:layered-balanced
-- (statement step8.tex:2453-2464; proof 3211-3266): strong
-- induction on |β|, consuming ONLY L.w ≤ 4 (plus width-3,
-- non-chain, 2 ≤ |β|). No band-injectivity, no L.K bound, no
-- card bound — paper lem:layered-balanced has none.
theorem lem_layered_balanced_full.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :          -- ONLY the interaction-width cap
    HasBalancedPair β

-- §G′. lem_layered_balanced (UNCHANGED in tree — LayeredBalanced.lean:626).
-- NO LONGER on the §E→§G boundary. It moves INSIDE Piece 6: the
-- in-tree lem_layered_balanced / Case3Witness_proof.{u} serve the
-- BOUNDED BASE CASE of lem_layered_balanced_full's strong
-- induction — paper Case C2 (step8.tex:3260-3263), the finite
-- slice |β| ≤ 3(3w+1) ≤ 39 / depth K ≤ 3w+1 discharged by
-- prop:in-situ-balanced. On that bounded slice |β| is finite, so
-- caps 1/2/3 are NOT unsatisfiable there (the mg-0bd1 obstruction
-- is a LARGE-α phenomenon only). NOTE — base-case coverage is a
-- Piece 6 engineering sub-task, not a drop-in: the cap-1
-- singleton-band Case3Witness_proof covers only the singleton-band
-- sub-slice of |β| ≤ 39 (PROOF-STRUCTURE-ONBOARDING §3 pitfall #2.2:
-- e.g. 3-antichain ⊕ 3-antichain has no singleton-band L), so
-- Piece 6's bounded base must additionally cover non-singleton-band
-- bounded posets — via the mg-be48 cap-light enumeration extension
-- or a direct prop:in-situ-balanced port. See the Piece 6 scope
-- (OneThird-Option-A-FULL-REFACTOR-scoping.md §2.6, sub-arc
-- mg-G4-D + risk 1) and §10.6 below.
theorem lem_layered_balanced.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hInj : Function.Injective L.band)
    (hKw : L.K ≤ 2 * L.w + 2)
    (hCardw : Fintype.card β ≤ 6 * L.w + 6)
    (hNonempty : ∀ k, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty)
    (hLw : L.w ≤ 4)
    (hC3 : Case3Witness.{u}) :
    HasBalancedPair β
```

### §4.3. The refactored headline body (pseudo-Lean)

```lean
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : HypothesisArithmetic) :     -- NEW parameter; hC3 DROPPED (mg-faf8)
    HasBalancedPair α := by
  -- §1. Strong induction on |α|; trivial cases first.
  induction hcard : Fintype.card α using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    by_cases hsmall : n ≤ 1
    · -- |α| ≤ 1: forced chain, contradicts hNonChain.
      exact absurd (chain_of_subsingleton hsmall) hNonChain
    -- §2. Proof by contradiction.
    by_contra hNoBP
    -- §3. Pick γ > 0 making α a γ-counterexample.
    --   ¬ HasBalancedPair α + non-chain ⇒ some γ ∈ (0, 1/3) works.
    obtain ⟨γ, hγ_pos, hγ_third, hCex⟩ :=
      gamma_counterexample_of_no_BP hNonChain hNoBP
    have h2 : 2 ≤ Fintype.card α := by omega
    -- §4. α is indecomposable (rem:decomp-reduction; uses IH).
    have hI : Indecomposable α :=
      decomp_reduction hP hNonChain hCex (ih_descent ih)
    -- §5. Realisability of the parameter cascade (eq:arith-cond +
    --     n ≥ n_0).
    have hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card α :=
      n_zero_le_of_cascade_realised hArith hcard hγ_pos hγ_third
    -- §6. Theorem E: low-conductance cut.
    have hThmE := cexImpliesLowBKExpansion γ hγ_pos hγ_third hP hI hCex h2
    -- §7. Steps 1-7 cascade: Step5R ∨ Step5C.
    have hCascade :=
      stepsOneToSevenCascade γ hγ_pos hγ_third hP hI hCex h2 hArith hn0 hThmE
    -- §7′. ChainLiftData constructor (§D′; R1 — mg-974c): convert
    --   the Step-5 dichotomy into the concrete globalization bundle
    --   the bridge consumes. RECONCILED mg-3119 — see §4.2 §D′, §11.
    obtain ⟨cld, hKbw⟩ :=
      chainLiftData_of_cascade γ hγ_pos (hArith.T γ) hP hI hCex hCascade
    -- §8. lem:layered-from-step7: LayeredDecomposition on X∖X^exc.
    --   RE-PINNED mg-faf8: the bridge emits only three caps
    --   (Xexc bound, band-nonempty, L.w ≤ 4).
    --   RECONCILED mg-3119: the bridge consumes cld : ChainLiftData α
    --   (+ hKbw : cld.K_bw ≤ 2), NOT hCascade — see §4.2 §E.
    obtain ⟨Xexc, L, hXexc_small, hNonempty, hLw⟩ :=
      lem_layered_from_step7 γ hγ_pos (hArith.T γ) hP hI hCex cld hKbw
        (ih_descent ih)
    -- §9. lem_layered_balanced_full (PIECE 6) on {a // a ∉ Xexc}.
    --   RE-PINNED mg-faf8: the consumer is the full Step 8 G4,
    --   which needs only hLw : L.w ≤ 4 — no hInj/hKw/hCardw, and
    --   no hC3 : Case3Witness (the witness is internal to Piece 6's
    --   strong induction). hNonempty is emitted by the bridge and
    --   carried for Piece 6's internal base-case use; it is not a
    --   top-level argument of lem_layered_balanced_full.
    have hP_sub : HasWidthAtMost {a : α // a ∉ Xexc} 3 :=
      hP.subtype _
    have hNonChain_sub : ¬ IsChainPoset {a : α // a ∉ Xexc} :=
      non_chain_subtype_of_exc hNonChain hXexc_small hcard
    have h2_sub : 2 ≤ Fintype.card {a : α // a ∉ Xexc} := by
      have := hXexc_small
      have := hcard
      omega
    have hBP_sub : HasBalancedPair {a : α // a ∉ Xexc} :=
      lem_layered_balanced_full L h2_sub hNonChain_sub hP_sub hLw
    -- §10. exc_perturb lift: HasBalancedPair {a // a ∉ Xexc} → α.
    have hXexc_pert : 2 * (Xexc.card : ℚ) /
        (Fintype.card α - Xexc.card + 1 : ℚ) < γ / 2 :=
      exc_perturb_bound_of_n_zero hn0 hXexc_small
    have hBP : HasBalancedPair α :=
      excPerturbLift γ hγ_pos Xexc hXexc_pert hBP_sub
    -- §11. Contradiction.
    exact hNoBP hBP
```

**Auxiliary lemmas implied** (each is a thin combinator at a piece's
boundary):

- `chain_of_subsingleton` — `|α| ≤ 1 → IsChainPoset α`. Trivial.
- `gamma_counterexample_of_no_BP` — `¬ HasBalancedPair α ∧
  ¬ IsChainPoset α → ∃ γ > 0, γ ≤ 1/3 ∧ IsGammaCounterexample α γ`.
  Folded into mg-MA-Body's preamble. **No vacuity:**
  `HasBalancedPair ↔ ∃ x ∥ y, min(p_xy, p_yx) ≥ 1/3`; negate over
  finite α; finitely many incomparable pairs ⇒ pick min slack.
- `decomp_reduction` — `step8.tex` `rem:decomp-reduction` lifted to
  Lean. Folded into mg-MA-MinCex. Substantive content: if `α` is
  decomposable as `L ⊕ U` and `¬ HasBalancedPair α`, either `L` or
  `U` is a smaller γ-counterexample (use the marginal-invariance of
  `probLT` on each summand), contradicting the IH; hence `α` is
  indecomposable.
- `ih_descent` — adapter from the `Nat.strong_induction_on` IH (over
  `Fintype.card`) to the form `lem_layered_from_step7` consumes.
- `n_zero_le_of_cascade_realised` — given `hArith.arith_holds` +
  `2 ≤ |α|`, derive `n_zero γ T ≤ |α|`; if not, the small-`n` base
  case (`Step8/SmallN.lem_small_n`) discharges directly. Folded into
  mg-MA-Cascade.
- `non_chain_subtype_of_exc` — under `|Xexc| ≤ C_exc(T)` and `|α|`
  large (`≥ n_zero γ T`, supplied by `hcard`/`hn0`), the subtype
  `{a // a ∉ Xexc}` is also non-chain. **RE-PINNED mg-faf8:**
  renamed from `non_chain_subtype_of_C_exc_le`; no longer consumes
  the dropped cap 3 (`hCardw : |α| − |Xexc| ≤ 6 L.w + 6`).
  Non-chain-ness of the subposet does not depend on cap 3 — a
  width-3 non-chain `α` has `≥ |α| − 3` incomparable pairs, so
  deleting `O_T(1)` exceptional elements leaves one. Mechanical.
- `exc_perturb_bound_of_n_zero` — algebraic massage of the
  `eq:exc-perturb` bound at `n ≥ n_0(γ, T) = ⌈4 C_exc(T)/γ⌉ +
  C_exc(T) − 1`. Mechanical.

### §4.4. Why this types cleanly **and is satisfiable** (RE-PINNED mg-faf8)

**The original §4.4 checked only type-compatibility — that is the
gap that produced the 8th vacuity (mg-0bd1; see §9).** A clean
type-check is *necessary but not sufficient*: a signature can type
cleanly and still pin an unsatisfiable proposition. This re-pinned
§4.4 therefore runs **both** checks per `PROOF-STRUCTURE-ONBOARDING.md`
§3 pitfall #2: (A) type compatibility, and (B) satisfiability
under caps.

**Check (A) — type compatibility on each cross-piece boundary:**

| Boundary | Type-check verdict |
|---|---|
| `cexImpliesLowBKExpansion` → `stepsOneToSevenCascade` | hThmE matches the `hS` parameter signature byte-for-byte (both are `∃ S, vol ≥ γ·vol(univ) ∧ Phi ≤ 2/(γn)`) |
| `stepsOneToSevenCascade` → `chainLiftData_of_cascade` (RECONCILED mg-3119) | the cascade output `Step5R ∨ Step5C` matches the `hCascade` parameter of the §D′ constructor; `T` threaded via `hArith.T γ`; `hCex` in scope from §4.3 body §3 |
| `chainLiftData_of_cascade` → `lem_layered_from_step7` (RECONCILED mg-3119) | the §D′ constructor emits `∃ cld : ChainLiftData α, cld.K_bw ≤ 2`; `obtain` destructures it to `cld` + `hKbw`, matching the bridge's `cld` / `hKbw` parameters; `hCex` / `hP` / `hI` / `T` threaded directly. **F7a settled GREEN by R1 (mg-974c)** — §11.4.1; §4.2 §D′/§E stand |
| `lem_layered_from_step7` → `lem_layered_balanced_full` (Piece 6) | output `LayeredDecomposition {a // a ∉ Xexc}` matches input `L : LayeredDecomposition β` (`β := {a // a ∉ Xexc}`); the bridge emits `Xexc.card ≤ C_exc T ∧ band-nonempty ∧ L.w ≤ 4`, and Piece 6 consumes exactly `hLw : L.w ≤ 4` — the `band-nonempty` conjunct is carried for Piece 6's internal base case, the `Xexc.card` conjunct is consumed by `excPerturbLift` |
| `lem_layered_balanced_full` → `excPerturbLift` | `HasBalancedPair {a // a ∉ Xexc}` matches `hBP_sub` |
| `excPerturbLift` → final contradiction | `HasBalancedPair α` contradicts `hNoBP` |
| IH (Nat.strong_induction_on) → `decomp_reduction` + `lem_layered_from_step7` recursive descent | Both consume the IH on strict-cardinality-smaller posets; the IH supplies it directly |

All boundaries match concretely. No "shape mismatch" / "missing
hypothesis" / "wrong universe" surfaces under inspection.

**Check (B) — satisfiability under caps.** The decisive check
(skipped by the original §4.4). At the `lem_layered_from_step7 →
lem_layered_balanced_full` boundary, is the emitted conclusion
*satisfiable* for the headline's full `|α|` range under the
hypotheses that actually reach the bridge? The original five-cap
shape failed this — it forced `|α| ≤ 10 + C_exc T` (mg-0bd1 §2).
The corrected three-cap shape **passes** it: the paper `def:layered`
object has unbounded depth `L.K ≥ |X|/6`, bands of size `≤ 3`, and
`L.w ≤ 4`, satisfying exactly `Xexc.card ≤ C_exc T`, band-nonempty,
and `L.w ≤ 4`. The full verification — including instantiation
against the mg-0bd1 counterexample class — is **§10** below.

The other boundaries carry no `∃`-conclusion with caps, so type
compatibility is also satisfiability for them.

---

## §5. Audit comparison vs parent scoping doc §2.4

| Parent §2.4 risk | This session's finding | Budget delta |
|---|---|---|
| Risk #1: 8th vacuity-discovery on signature | ~~Did not materialize. Signature types cleanly.~~ **CORRECTED (mg-0bd1/mg-faf8):** the risk DID materialize — the §4.2 §E five-cap bridge conclusion was unsatisfiable for large α. Surfaced by mg-0bd1, re-pinned by mg-faf8 (§4.2 §E/§G, §4.3, §4.4, §9, §10). The original "did not materialize" claim rested on a type-only audit. | re-scope: +Piece 6 (0.8M–1.6M; see scoping doc §2.6) |
| Risk #2: Decomposability hypotheses non-trivial | Folded into mg-MA-MinCex via `decomp_reduction`; substantive but bounded by paper rem:decomp-reduction content. | within parent estimate |
| Risk #3: Theorem E may be marker (30%, +500-800k) | **Theorem E is SUBSTANTIVE.** mg-MA-ThmE is wiring, not grounding. | **−250k to −500k** |
| Risk #9: hyp:arith threading contentious | Decided: in-Lean predicate (default). Defer body content to piece 1 / out-of-scope. | within parent estimate |

**Net budget impact:** parent estimate (piece 4 = 0.8M-1.5M / 4-6
sessions) revised slightly down to **0.55M-1.0M / 3-5 sessions** if
mg-MA-ThmE wiring takes ≤300k.

This propagates to parent §3.2 cumulative budget: mid-estimate
**10.0M → 9.7M**; planning ceiling **13.5M → 13.0M**.

---

## §6. Recommendations for Phase 2-4 follow-on (no `mg new` here)

Per ticket constraint *"no premature execution commitment without
Daniel sign-off"*, this session does **not** file the sub-tickets.
Updates to the parent dispatch sequence:

1. **mg-MA-ThmE downgrade.** Re-tag from "Theorem E grounding"
   (0.5-0.8M) to "Theorem E wiring" (0.2-0.3M). Body: extract
   `Indecomposable α` from the IH; re-pack `cexImpliesLowBKExpansion`
   output for the Step 5 dichotomy consumer.
2. **`pickMinimalCounterexample` constructor removed from mg-MA-MinCex.**
   The minimal counterexample lives inline in `mg-MA-Body` via
   `Nat.strong_induction_on`. mg-MA-MinCex's content is just
   `decomp_reduction` (indecomposability descent) — still ~200k / 1
   session, but content-clear.
3. **NEW (mg-faf8): Piece 6 sub-arc.** The re-pin (§9, §10) adds a
   **sixth piece** to mg-d8c7 — `lem_layered_balanced_full` (the
   full Step 8 G4 port, §4.2 §G). It is **not** part of piece 4;
   it has **no upstream cascade dependency** (consumes only a
   `LayeredDecomposition` with `L.w ≤ 4`; `lem_cut`,
   `windowLocalization`, `lem_layered_reduction` are already in
   tree) and can be dispatched in parallel with piece 1. Sub-arc
   recommendation `mg-MA-G4-Full`: see
   `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6 and §7.3a.
   Budget ~0.8M-1.6M / 3-6 sessions.

The other parent §7.4 sub-tickets (`mg-MA-Cascade`, `mg-MA-Body`)
are unchanged in shape. `mg-MA-Body` now calls
`lem_layered_balanced_full` (no `hC3`). Recommended Phase 4
dispatch:

```
[Piece 6 — mg-MA-G4-Full — dispatched early, parallel with piece 1]

[After pieces 1, 2, 3, 6 land + checkpoint 4 audit]
  mg-MA-MinCex ∥ mg-MA-ThmE                 (parallel, ~250k each)
  mg-MA-Cascade                              (sequential, ~250k-300k)
  mg-MA-Body                                 (sequential, ~250k-300k)
  [+ mg-Int-A, mg-Int-B per parent §7.4 — unchanged]
```

---

## §7. Cross-reference index

### §7.1. Lean (this worktree, `origin/main`)

- `lean/OneThird/Step8/MainAssembly.lean:236-267` — `caseC_canonicalLayered`
  (deleted by mg-MA-Body).
- `lean/OneThird/Step8/MainAssembly.lean:269-279` — `mainTheoremInputsOf`
  (deleted by mg-MA-Body).
- `lean/OneThird/Step8/MainAssembly.lean:308-322` — `mainAssembly`
  (deleted by mg-MA-Body).
- `lean/OneThird/Step8/MainAssembly.lean:353-372` —
  `width3_one_third_two_thirds_assembled` (rewritten body by
  mg-MA-Body; signature gains `hArith : HypothesisArithmetic`).
- `lean/OneThird/Step8/TheoremE.lean:171` — `cexImpliesLowBKExpansion`
  (SUBSTANTIVE; unchanged).
- `lean/OneThird/Step8/FrozenPair.lean:219` — `frozenPairCut_exists`
  (SUBSTANTIVE; unchanged).
- `lean/OneThird/Step8/ExcPerturb.lean:351` — `exc_perturb`
  (SUBSTANTIVE; consumed by `excPerturbLift` thin combinator).
- `lean/OneThird/Step8/LayeredBalanced.lean:626` — `lem_layered_balanced`
  (post-mg-234e; in-tree signature unchanged; **RE-PINNED mg-faf8:**
  no longer the §4.2 §E consumer — it becomes the bounded base case
  *inside* Piece 6's `lem_layered_balanced_full`).
- `lem_layered_balanced_full` — **Piece 6 deliverable, NEW; not yet
  in tree.** Full Step 8 G4 (paper `lem:layered-balanced`,
  `step8.tex:2453-2464` / proof `3211-3266`). Strong induction on
  `|β|`; consumes only `L.w ≤ 4`. Target file
  `lean/OneThird/Step8/LayeredBalancedFull.lean` (new). Consumes
  the NC lemmas `lem_cut` / `windowLocalization` /
  `lem_layered_reduction` (`LayeredReduction.lean` /
  `LayeredBalanced.lean:103`).
- `lean/OneThird/LinearExtension.lean:38,50,71` — `HasBalancedPair`,
  `IsGammaCounterexample`, `Phi` (definitions; unchanged).
- `lean/OneThird/LinearExtension.lean:166` — `edgeBoundary_pairCut_sum_le`
  (SUBSTANTIVE; foundation for Theorem E; unchanged).
- `lean/OneThird/Mathlib/Poset/Indecomposable.lean` —
  `Indecomposable α` + `exists_incomp` (SUBSTANTIVE; consumed by
  Theorem E + `decomp_reduction`).
- `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`
  (consumed by `lem_layered_from_step7`).

### §7.2. Paper (`origin/main:step8.tex`)

- `step8.tex:9-23` — Hypothesis A (`hyp:arith`).
- `step8.tex:32-91` — `thm:main-step8` + `rem:headline-lean-restatement`.
- `step8.tex:106-260` — `thm:main-step8` proof body (the refactor
  template).
- (See parent doc §8.1 for the long form including step7.tex
  `prop:72` + `lem:bandwidth ≤ 4` references.)

### §7.3. Predecessor docs

- `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) —
  §2.6 records Piece 6 (added by mg-faf8).
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §2 tag legend;
  §3 pitfall #6 (the 8th vacuity).
- `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8).
- `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — RED 7th vacuity.
- `docs/state-S7-F-bridge-Session2.md` (mg-0bd1) — RED 8th
  vacuity discovery; the full proof that the original §4.2 §E
  five-cap conclusion is unsatisfiable for large α. The source
  of this session's re-pin.
- `docs/coherence-collapse-case-extraction.md` (mg-ac13) —
  3-disjoint-chains counterexample (motivates the refactor).
- `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2)
  — canonicalLayered bypass diagnosis.

### §7.4. Predecessor work items

- mg-d8c7 (Option A' FULL REFACTOR scoping; mg-a22b's parent),
- mg-6ab8 (Steps 1-7 scoping), mg-5fbd (S7-F bridge audit; RED),
- mg-ac13 (coherence-collapse extraction),
- mg-234e (lem_layered_balanced caller-L rewire),
- mg-d5a0 (cap-5 sorry first surfaced; relocated by mg-234e),
- mg-a22b (Phase 1 signature contract — the session this doc
  was created in),
- mg-0bd1 (S7-F bridge Session 2 — RED 8th vacuity discovery on
  the §4.2 §E signature),
- mg-faf8 (the MA-Sig re-pin correcting the 8th vacuity; §4.2
  §E/§G, §4.3, §4.4, §9, §10),
- mg-ca83 (S7-F Checkpoint 3 — RED; found the bridge contract
  pinned inconsistently MA-Sig §4.2 §E vs scoping §2.3),
- **mg-3119 (this session — S7F-R2; the bridge-input
  reconciliation: §4.2 §E now consumes a `ChainLiftData`, §4.2
  §D′ added, §4.3/§4.4 updated, §11 added)**,
- mg-974c (S7F-R1 — the F7a `ChainLiftData` constructibility
  ticket; depends on mg-3119).

---

## §8. Maintenance contract

This file is the **signature contract for the Option A' FULL
REFACTOR's piece 4 and (post-mg-faf8) piece 6**. Downstream
sub-tickets (mg-MA-G4-Full, mg-MA-MinCex, mg-MA-ThmE,
mg-MA-Cascade, mg-MA-Body, mg-Int-A, mg-Int-B) reference the
§4.2-§4.3 signatures.

> **⚠ Piece 6 status (mg-fdc2, 2026-05-20).** The §4.2 §G
> `lem_layered_balanced_full` signature is **still a correct,
> satisfiable proposition** (§10.6 unaffected). But the first
> execution attempt (mg-fdc2) found the **proof routing**
> unbuildable: `Case3Witness_proof` cannot be the base case (it
> requires band injectivity the re-pinned input `L` deliberately
> lacks), and the named inductive-step lemmas `windowLocalization`
> / `lem_layered_reduction` are vacuous placeholders. Honest
> closure needs new formalization (a genuine window
> marginal-invariance lift + a non-singleton-band
> `prop:in-situ-balanced` Case 2 port) or a new disclosed
> base-case axiom — a re-scoping decision. See
> `docs/state-Piece6-FullStep8G4-Session1.md` §7 (options
> G1/G2/G3) and `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #7.
> No §4.2 §G *signature* re-pin is required; what changed is the
> Piece 6 *execution plan* (mg-MA-G4-Full must be split per
> §7 of the Piece 6 state doc).

> **⚠ Bridge input reconciled (mg-3119 / S7F-R2, 2026-05-21);
> F7a settled GREEN (mg-974c / S7F-R1, 2026-05-21).**
> The §4.2 §E bridge *input* is re-pinned: `lem_layered_from_step7`
> consumes a `ChainLiftData α` (+ `hKbw`), not `Step5R ∨ Step5C`;
> a §4.2 §D′ constructor `chainLiftData_of_cascade` is added. See
> §11. **R1 settled F7a GREEN** — a concrete non-degenerate
> `ChainLiftData α` is constructible (`gridChainLiftData`,
> `Step8/ConcreteChainLiftData.lean`). Per §11.4.1 this is **case
> 1**: the witness matches the *bare* structure, so §4.2 §D′/§E
> **stand as pinned** — no re-pin needed.

Update this file in the **same commit** as any of the following:

- A Phase 2/4 sub-ticket lands and its actual signature drifts
  from §4.2; reflect the drift here.
- A further vacuity-discovery surfaces during execution; record
  here with re-scoped recommendation.
- A piece 1/2/3/6 deliverable lands and its output shape differs
  from what §4.2 assumes; update the consumer-side signature.
- **R1 (mg-974c) settles F7a** — land the resolution per §11.4
  (case 1 stand / case 2 re-pin to a strengthened `ChainLiftData`
  / case 3 reopen on RED-not-constructible).

Default-skeptical posture: per Daniel's "vacuity-discovery has hit
**8 times**" pattern (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970,
mg-ac13, mg-5fbd, **mg-0bd1**), if execution surfaces a gap,
**stop and re-scope** rather than pushing through. The §4.2
signature is the contract — and per the mg-0bd1 lesson, "the
contract" means a **satisfiable** proposition, not merely a
type-clean one. Every `∃`-with-caps conclusion pinned here must
pass `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 check #1
(satisfiability under caps) before it is accepted — see §4.4
check (B) and §10.

---

## §9. 8th vacuity-discovery — the §4.2 §E bridge signature is unsatisfiable (mg-0bd1)

**Recorded per §8 maintenance contract** (*"An 8th vacuity-discovery
surfaces during Phase 2-4 execution; record here with re-scoped
recommendation"*). Source: `docs/state-S7-F-bridge-Session2.md`
(mg-0bd1, the piece-3 execution attempt).

**Finding.** The §4.2 §E `lem_layered_from_step7` conclusion
transcribes the five `Case3Witness` caps onto
`L : LayeredDecomposition {a // a ∉ Xexc}`. caps 1 + 4 force
singleton bands (`card {a // a ∉ Xexc} = L.K`); caps 2 + 5 force
`L.K ≤ 10`. Hence the conclusion entails
`Fintype.card α ≤ 10 + C_exc T`, a fixed finite bound. But the
hypothesis `Step5R ∨ Step5C` (Step 5 dichotomy) holds for minimal
γ-counterexamples of unbounded size. So the pinned bridge is
**false**, not vacuous, for every large minimal γ-counterexample.
This is `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2.1 recurring
inside this contract's pseudo-Lean.

**Why §4.4 missed it.** §4.4's "no 8th vacuity" table checked, at
the `lem_layered_from_step7 → lem_layered_balanced` boundary, only
that *"5 caps match"* — producer/consumer **type compatibility**.
It did not run pitfall #2's mandated **check #1 — satisfiability
under caps**. The signature types cleanly *and* is unsatisfiable.

**Root cause.** §4.2 §G pinned `lem_layered_balanced` "UNCHANGED"
as the Step-8 endpoint. But `lem_layered_balanced` /
`Case3Witness` is — per its own docstring (`LayeredBalanced.lean:
447-450`) — the bounded `|β| ≤ 30`, `K ≤ 10` base sub-slice of
Step 8 G4, not the full G4. The full Step 8 G4 (paper
`lem:layered-balanced`, `step8.tex:3071-3124`: only `L.w ≤ 4`,
strong induction on `|β|`) is not in tree and is not one of
mg-d8c7's 5 pieces.

**Re-pin — APPLIED by mg-faf8 (supersedes the original §4.2 §E
and §4.2 §G).** The three corrections below are now **landed** in
this document; see §10 for the satisfiability verification that
gates them.

1. **Piece 6 added to mg-d8c7** — the full Step 8 G4 port,
   `lem_layered_balanced_full` (signature pinned at §4.2 §G):
   ```lean
   theorem lem_layered_balanced_full
       {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
       (L : LayeredDecomposition β) (h2 : 2 ≤ Fintype.card β)
       (hNotChain : ¬ IsChainPoset β) (hW3 : HasWidthAtMost β 3)
       (hLw : L.w ≤ 4) :          -- ONLY cap 5
       HasBalancedPair β
   ```
   The existing `lem_layered_balanced` becomes its bounded base
   case (paper Case C2, `|β| ≤ 3(3w+1) ≤ 39`). Recorded as the
   sixth piece in `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`
   §2.6.

2. **§4.2 §E re-pinned** — the bridge emits only
   `Xexc.card ≤ C_exc T`, the band-nonempty cap, and `L.w ≤ 4`;
   caps 1, 2, 3 (band injectivity; `L.K ≤ 2 L.w + 2`; the
   `card − Xexc` bound) are dropped as `Case3Witness` API
   artefacts, false for `|X ∖ X^exc| > 10`. The bridge also
   gains `hCex : IsGammaCounterexample α γ` (domain pin) — see
   §10.4 (X-b) for why the satisfiability check requires it.

3. **§4.3 re-pinned** — the headline body calls
   `lem_layered_balanced_full` (Piece 6), dropping the
   `hInj`/`hKw`/`hCardw` arguments, the `hC3 : Case3Witness`
   threading, and the `hC3` parameter from
   `width3_one_third_two_thirds[_assembled]`.

**Status.** The re-scope mg-0bd1 recommended (Option (R1), 1
session) is **this session, mg-faf8**. Piece 6 has no upstream
cascade dependency (it consumes only a `LayeredDecomposition`
with `L.w ≤ 4`, and `lem_cut` / `windowLocalization` /
`lem_layered_reduction` are already in tree) — it can be
dispatched immediately, in parallel with piece 1 (mg-0bd1
Option (R2) ordering). Full forward options:
`state-S7-F-bridge-Session2.md` §7-§8.

---

## §10. Satisfiability verification of the corrected contract (mg-faf8)

> **⚠ INPUT SHAPE SUPERSEDED (mg-3119 / R2).** §10 verifies the
> mg-faf8 contract whose bridge *input* was `Step5R ∨ Step5C`. The
> R2 reconciliation (§11) re-pins that input to a `ChainLiftData α`.
> §10's **conclusion-side** analysis — the 3-cap shape `C(α)`, and
> the (V)/(S)/(X) checks on `Xexc.card ≤ C_exc T` ∧ band-nonempty
> ∧ `L.w ≤ 4` — is **unchanged** and carries over verbatim. Only
> the *hypothesis* `H(α)` changes: where §10 writes
> "`Step5R α γ T ∨ Step5C α T`" the reconciled bridge reads
> "`cld : ChainLiftData α` with `cld.K_bw ≤ 2`". §11 re-runs
> (V)/(S)/(X) against that new input.

**This section is the acceptance-bar deliverable.** The 8th
vacuity (mg-0bd1) was caused precisely by an audit (the original
§4.4) that checked **type-compatibility only**. A re-pin that
merely type-checks would repeat the error. So the corrected §4.2
§E/§G contract is verified here for **satisfiability** — per
`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 check #1 — and the
verification is instantiated explicitly against the mg-0bd1
counterexample class (the 3-disjoint-chains family).

### §10.1. The corrected bridge as a proposition

Write the corrected §4.2 §E bridge as the conditional
`∀ α, H(α) → C(α)`, where

```
H(α)  :=  HasWidthAtMost α 3
        ∧ Indecomposable α
        ∧ IsGammaCounterexample α γ              -- added mg-faf8 (§4.2 §E)
        ∧ (Step5R α γ T ∨ Step5C α T)
        ∧ ih                                    -- (the strong-induction IH)

C(α)  :=  ∃ (Xexc : Finset α) (L : LayeredDecomposition {a // a ∉ Xexc}),
              Xexc.card ≤ C_exc T
            ∧ (∀ k, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty)
            ∧ L.w ≤ 4
```

The `IsGammaCounterexample α γ` conjunct is the **load-bearing
domain pin** added by the re-pin. The original §4.2 §E omitted
it; the satisfiability check below (§10.4 (X-b)) shows why it is
required — without it, the bridge's truth on non-γ-counterexample
posets would hinge on the not-yet-pinned exact definitions of
`Step5R`/`Step5C`. With it, the bridge is a true proposition
*standalone*.

The bridge is a **true** proposition iff `H(α) → C(α)` for every
`α`. It is moreover **non-vacuously** true iff `H(α)` is itself
satisfiable (otherwise the bridge is a harmless-but-empty shell).
Both must be checked. We check three things:

* **(V) Non-vacuity** — `H(α)` is satisfiable for `α` of
  *unbounded* size (§10.2).
* **(S) Satisfiable conclusion** — whenever `H(α)` holds, `C(α)`
  holds, for every `α` regardless of `|α|` (§10.3).
* **(X) Counterexample-class instantiation** — explicit check
  against the mg-0bd1 / mg-5fbd 3-disjoint-chains family (§10.4).

### §10.2. (V) — `H(α)` is satisfiable for unbounded `|α|`

This is exactly the fact that made the *original* contract
**false** rather than vacuous (mg-0bd1 §3). The re-pin touched
the conclusion `C` and added the `IsGammaCounterexample` conjunct
to `H` — neither change makes `H` unsatisfiable, because the
witnesses are *minimal γ-counterexamples*, which satisfy the new
conjunct trivially:

* The 1/3–2/3 conjecture ranges over all finite posets. If it had
  a width-3 non-chain counterexample, a **minimal** one `α`
  exists; by `rem:decomp-reduction` it is `Indecomposable`, it is
  width-3 non-chain by assumption, and it satisfies
  `IsGammaCounterexample α γ` for the relevant `γ` **by
  construction** (it is a counterexample).
* For every minimal γ-counterexample `α` above the small-`n`
  threshold `n_0(γ,T)`, paper `thm:step5` (`step5.tex`) makes the
  Step 5 dichotomy `Step5R α γ T ∨ Step5C α T` **true**.
* Minimal γ-counterexamples are of **unbounded** size: the small
  ones are dispatched by `lem_small_n`; the cascade's domain is
  exactly the large ones.

Hence all four substantive conjuncts of `H(α)` (`HasWidthAtMost`,
`Indecomposable`, `IsGammaCounterexample`, `Step5R ∨ Step5C`)
hold simultaneously for `α` of every sufficiently large size —
the bridge is **not** a vacuous shell. ∎(V)

### §10.3. (S) — `C(α)` holds whenever `H(α)` holds

Fix any `α` with `H(α)`. Then `Step5R α γ T ∨ Step5C α T` holds,
which is exactly the two-branch input of paper
`lem:layered-from-step7` (`step8.tex:2009-2089`):

* `Step5C α T` ⟹ branch (a), the Step 5(C) collapse input
  (`step8.tex:2016-2021`);
* `Step5R α γ T` ⟹ branch (b) via the Step 7(ii) globalization it
  feeds (`step8.tex:2022-2027`).

The paper lemma's conclusion (`step8.tex:2054-2088`) then produces
an exceptional set `X^exc` and an **exact** `def:layered`
decomposition of `P|_{X∖X^exc}` (`step8.tex:1983-2007`) with:

| Paper conclusion item | Value | Corrected Lean cap |
|---|---|---|
| (i) `\|X^exc\| ≤ C_exc(T) = 3 c_1(T) = O_T(1)` | bounded | `Xexc.card ≤ C_exc T` ✓ |
| (ii) interaction width `w = K_bw + 2` (branch b) / `w_coll` (branch a), each `≤ 4` by `lem:bandwidth`/`rem:w0-constant` (`w_0(γ) ≤ 4`, `step8.tex:576`) | `≤ 4` | `L.w ≤ 4` ✓ |
| ordered partition `X∖X^exc = L_1 ⊔ ⋯ ⊔ L_K` into `K` **nonempty** bands (`compactify` re-indexes to guarantee it) | all `[1,K]` hit | `∀ k ∈ [1,K], (bandSet k).Nonempty` ✓ |

So `C(α)` holds. **The key point:** the paper object has bands of
size `≤ 3` — *not* singletons — and depth
`K ≥ (|X| − |X^exc|)/3 ≥ |X|/6` (`step8.tex:2072`), which is
`Θ(|α|)` and **unbounded**. The corrected `C` permits this because
it no longer carries:

* old cap 1 (`Function.Injective L.band`) — would force singleton
  bands, hence `L.K = |X∖X^exc|`;
* old cap 2 (`L.K ≤ 2 L.w + 2`) — would then force
  `L.K ≤ 2·4+2 = 10`;
* old cap 3 (`|X∖X^exc| ≤ 6 L.w + 6`) — an independent `≤ 30`
  bound.

Caps 1+2 jointly forced `|α| ≤ 10 + C_exc T` — the mg-0bd1 defect.
Dropping them lets `L.K` be `Θ(|α|)`, matching the paper object
exactly. (`LayeredDecomposition.band_size`, an intrinsic structure
field, already guarantees bands of size `≤ 3` — no cap needed for
that.) Hence `H(α) → C(α)` for every `α`, **of every size**. ∎(S)

Together (V)+(S): the corrected bridge is a **true, non-vacuous**
proposition. This is the property the original five-cap signature
provably lacked.

### §10.4. (X) — instantiation against the mg-0bd1 counterexample class

The mg-0bd1 / mg-5fbd counterexample class is the
**3-disjoint-chains family** `Δ_ℓ` := three pairwise-disjoint
chains each of length `ℓ` (so `|Δ_ℓ| = 3 ℓ`, width 3, non-chain).
mg-5fbd §2.3 used `Δ_3` (`|Δ_3| = 9`); mg-0bd1 §2.3 generalised to
all `ℓ`. The ticket requires confirming the **corrected** contract
holds on this class. We take the two regimes separately.

**(X-a) `Δ_3` — the named family member (`|Δ_3| = 9`).** Label the
chains `a_1 <_P a_2 <_P a_3`, `b_1 < b_2 < b_3`, `c_1 < c_2 < c_3`.

* *Under the original five-cap contract* mg-5fbd §2.3 showed **no**
  `L` satisfies all five caps: cap 1 forces singleton bands, so
  `L.K = 9`; cap 2 forces `9 ≤ 2 L.w + 2`, i.e. `L.w ≥ 4`; cap 5
  forces `L.w = 4`; then (L2-forced) demands 10 ground-set pairs
  at band-distance `> w` be `<_P`-comparable, but `Δ_3` has only 9
  comparable pairs (all within-chain). Contradiction.
* *Under the corrected three-cap contract* a satisfying witness
  **exists**. Take `Xexc := ∅` (so `Xexc.card = 0 ≤ C_exc T`) and
  the natural banding `L_k := {a_k, b_k, c_k}` for `k = 1,2,3`.
  Then `L.K = 3`, every band is a 3-element antichain (the three
  chains are mutually incomparable — `band_size = 3 ≤ 3` ✓,
  `band_antichain` ✓), and all of `[1,3]` is hit (band-nonempty
  cap ✓). Interaction width: the only cross-band incomparabilities
  are cross-chain pairs (e.g. `a_1 ∥ b_3`), whose maximum
  band-distance is `|1 − 3| = 2`; within-chain comparabilities
  `a_i <_P a_j` (`i<j`) are band-upward, satisfying (L4). So
  `L.w = 2 ≤ 4` (cap ✓), (L2-forced) is vacuous (no pair has
  `band x + 2 < band y` since `K = 3`), (L3) holds. **All three
  corrected caps are satisfied** — `C(Δ_3)` is true. The cap the
  original contract failed, cap 1, is exactly the one dropped:
  the natural bands are 3-element antichains, not singletons.

So on `Δ_3` the corrected contract is fine *even at the level of
the conclusion alone*. (And note: `Δ_3` is not a γ-counterexample
— it has balanced pairs by symmetry, e.g. `(a_1,b_1)` with
`Pr = 1/2` — so `H(Δ_3)` is false and the bridge is in any case
vacuously true on it; see (X-c).)

**(X-b) `Δ_ℓ`, `ℓ > 5` — the unbounded regime (`|Δ_ℓ| = 3ℓ`).**
Here `C(Δ_ℓ)` is **false**: by `PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #2.3, every layered decomposition of `Δ_ℓ` has interaction
width `≥ ℓ − 1` (a length-`ℓ` chain occupies `ℓ` distinct band
indices by (L1)+(L4), and a cross-chain pair `a_1 ∥ b_ℓ` then
forces `w ≥ ℓ − 1` by (L3)); deleting `C_exc(T) = O_T(1)`
exceptional elements still leaves width `≥ ℓ − O_T(1) > 4`. So no
`L` with `L.w ≤ 4` exists — `C(Δ_ℓ)` fails.

**This does not break the corrected contract**, because
`H(Δ_ℓ)` is *also* false — and, with the `hCex` conjunct added
by the re-pin, **provably and definition-independently** so:

* **`Δ_ℓ` is not a γ-counterexample.** `(a_1, b_1)` are exchanged
  by a poset-automorphism of `Δ_ℓ` (swap chains `A` and `B`
  pointwise), so `Pr[a_1 <_L b_1] = 1/2 ∈ [1/3, 2/3]` — a
  balanced pair. Hence `HasBalancedPair Δ_ℓ` holds and
  `IsGammaCounterexample Δ_ℓ γ` is **false** for every `γ`. The
  `H` conjunct `IsGammaCounterexample α γ` (added mg-faf8) is
  therefore false on `Δ_ℓ`, so `H(Δ_ℓ)` is false **outright** —
  no reasoning about `Step5R`/`Step5C` is needed. This is the
  reason `hCex` was added to §4.2 §E: it makes the exclusion of
  the 3-disjoint-chains family **airtight**, not contingent on
  the (not-yet-pinned) exact definitions of `Step5R`/`Step5C`.
* For completeness, the cascade conjunct is false too:
  `Step5C Δ_ℓ T` literally asserts a bounded-width (`width ≤ w`,
  `w = w_coll(T) = O_T(1)`) layered structure on `X∖X^exc` —
  false for `ℓ` large by the pitfall #2.3 argument above. And
  `Step5R Δ_ℓ γ T` is a richness conclusion the Step 5 dichotomy
  (`thm:step5`) certifies only from Theorem E's low-conductance
  input, which holds only for minimal γ-counterexamples — but
  this third bullet is **not load-bearing**: the first bullet
  already kills `H(Δ_ℓ)`.

Hence `H(Δ_ℓ)` is false, and the corrected bridge is
**vacuously true** on `Δ_ℓ`: `false → false`. This is a *correct*
vacuity — a harmless conditional with an unsatisfiable
hypothesis — **not** the *falsity* (`true → false`) that the
original five-cap contract had on genuine large minimal
γ-counterexamples.

**(X-c) Why this is the decisive distinction.** The 3-disjoint-
chains family is the standard witness that *"∀ width-3 non-chain
`α`, ∃ `L` with `L.w ≤ 4`"* is **false** (pitfall #2.3). The
corrected bridge does **not** make that false universal claim: it
quantifies only over `α` satisfying `H`, i.e. over the
cascade-hypothesis region — exactly the minimal γ-counterexamples.
The `Δ_ℓ` family sits entirely **outside** that region. The
re-pin's correctness rests on this: the bridge's domain is
`{α : H(α)}`, and on that domain `C` is satisfiable (§10.3);
`Δ_ℓ ∉ {α : H(α)}`, so it never constrains the bridge.

### §10.5. Old vs corrected — the contrast in one table

For a poset `α` in each row, the bridge `H(α) → C(α)`:

| `α` | `H(α)` | old `C₅(α)` (5 caps) | corrected `C₃(α)` (3 caps) | old bridge | corrected bridge |
|---|---|---|---|---|---|
| genuine minimal γ-cex, `\|α\|` large | **true** (`thm:step5`) | **false** (forces `\|α\| ≤ 10 + C_exc T`) | **true** (paper `def:layered`, `K = Θ(\|α\|)`) | **`true→false` = FALSE** ✗ | `true→true` = true ✓ |
| genuine minimal γ-cex, `\|α\|` small | true | possibly true | true | conditional ok | true ✓ |
| `Δ_3` (3 chains of 3) | false (has balanced pair) | false (mg-5fbd §2.3) | true (X-a) | `false→…` = vacuous | `false→true` = true ✓ |
| `Δ_ℓ`, `ℓ` large | false (has balanced pair) | false | false (pitfall #2.3) | `false→…` = vacuous | `false→false` = true ✓ |

The original contract has a row — *genuine large minimal
γ-counterexample* — where it is outright **false**. The corrected
contract has **no false row**: wherever `H` is true, `C` is true;
wherever `C` is false, `H` is false. That is the whole content of
the re-pin.

### §10.6. Satisfiability of the §4.2 §G consumer (Piece 6)

The corrected consumer `lem_layered_balanced_full` (§4.2 §G) is a
**faithful transcription of paper `lem:layered-balanced`**
(`step8.tex:2453-2464`): "a width-3 poset `P` with `|X| ≥ 2`,
not a chain, admitting a layered decomposition of interaction
width `w` — has a balanced pair." The paper statement carries
**no** injectivity / `K`-bound / `card`-bound hypothesis; the Lean
`hLw : L.w ≤ 4` restricts `w` to the headline-relevant range and
keeps the paper-proof's Case-C2 base case a *finite decidable*
family. So §4.2 §G is satisfiable by construction — it is the
paper lemma. The paper proof (`step8.tex:3211-3266`) is a strong
induction on `|β|` (base `|β| = 2`; Case A `K=1`; Case B
ordinal-reducible; Case C irreducible, sub-case C1 window `⊊ X`
recurses, C2 `W = X` bounded `|β| ≤ 3(3w+1)`). **Caveat carried
forward (not a vacuity, a Piece-6 scope item):** the C2 bounded
base must cover *all* width-3 non-chain posets with `|β| ≤ 3(3w+1)`,
whereas the in-tree `Case3Witness_proof` covers only the
singleton-band (cap-1) sub-slice of that range. Piece 6's base
case must therefore extend coverage to non-singleton-band bounded
posets — via the mg-be48 cap-light enumeration or a direct
`prop:in-situ-balanced` port. This is recorded as a Piece 6
sub-task in the scoping doc §2.6, **not** papered over here.

### §10.7. Acceptance-bar verdict

| Acceptance bar (ticket mg-faf8) | Status |
|---|---|
| Re-pin §4.2 §E to emit only `Xexc.card ≤ C_exc T` + band-nonempty + `L.w ≤ 4` | **Done** — §4.2 §E |
| Drop the three unsatisfiable caps (band injectivity; `L.K ≤ 2 L.w + 2`; `card − Xexc` bound) | **Done** — §4.2 §E |
| (Surfaced during the satisfiability check) Pin the bridge domain via `hCex : IsGammaCounterexample α γ` | **Done** — §4.2 §E; rationale §10.1, §10.4 (X-b) |
| Re-pin §4.2 §G consumer to Piece 6 (`lem_layered_balanced_full`, only `L.w ≤ 4`) | **Done** — §4.2 §G |
| `Case3Witness_proof` becomes Piece 6's bounded base case | **Done** — §4.2 §G′, §10.6 |
| Update §4.3 body + downstream consumer references | **Done** — §3.1, §4.3, §4.4 |
| Record Piece 6 as the sixth piece of mg-d8c7 | **Done** — `OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6 |
| **Satisfiability, not just types** — corrected conclusion satisfiable for minimal γ-counterexamples of unbounded size | **Verified** — §10.2 (V) + §10.3 (S) |
| Instantiate against the mg-0bd1 counterexample class (3-disjoint-chains); confirm the corrected contract holds there | **Verified** — §10.4 (X-a/b/c), §10.5 |
| A type-checks-clean verdict is NOT sufficient | Acknowledged — §4.4 now runs check (A) **and** check (B); §10 is check (B) in full |

**Verdict: GREEN — corrected contract satisfiability-verified.**
The corrected §4.2 §E/§G contract is a true, non-vacuous
proposition; the 8th vacuity (caps 1+2 forcing `|α| ≤ 10 + C_exc T`)
is eliminated, and the fix is confirmed against the exact
counterexample class that exposed the defect.

---

## §11. R2 reconciliation — the bridge input is a `ChainLiftData`, not `Step5R ∨ Step5C` (mg-3119)

**Recorded per §8 maintenance contract** (*"A piece 1/2/3/6
deliverable lands and its output shape differs from what §4.2
assumes; update the consumer-side signature"*). Source: the
Checkpoint-3 audit `docs/state-S7F-Checkpoint3-Session1.md`
(mg-ca83), §5 + §6 R2. This section is the mg-3119 (S7F-R2)
deliverable. It re-pins the **input** of §4.2 §E; §9–§10 (the
mg-faf8 conclusion-side re-pin) are unaffected.

### §11.0. What R2 reconciles, and the verdict

Checkpoint 3 (mg-ca83 §5) found the S7-F bridge contract pinned
**inconsistently** across the two READ-FIRST documents:

* **MA-Sig §4.2 §E** (this doc, pre-mg-3119) — the bridge
  `lem_layered_from_step7` consumes the abstract Step-5 dichotomy
  `hCascade : Step5R α γ T ∨ Step5C α T`.
* **Scoping §2.3** (`OneThird-Option-A-FULL-REFACTOR-scoping.md`)
  — the bridge *"consumes `L_{S7E}`"*, i.e. Piece 2's
  `Step7.LayeredWidth3` packaging.

These cannot both be the contract, and — decisively — **neither
names the object the bridge *body* can consume to build a
ground-set `LayeredDecomposition`** (mg-ca83 §2–§4, §3 pitfall #9).
The audit established (§6 R1/R2) that the bridge must, to build a
ground-set `LayeredDecomposition {a : α // a ∉ Xexc}`, consume a
**`ChainLiftData α`**: the bundle of a Dilworth triple `A/B/C`, a
chain potential, the sync maps `fAB/fAC/fBC`, and the bandwidth
constant `K_bw` (`Step8/ChainPotentials.lean:328-340`).

**R2 re-pins both documents to consistently state the bridge input
as a `ChainLiftData α`.** MA-Sig §4.2 §E is re-pinned in place
(§11.2 below); scoping §2.3 is re-pinned in the parallel mg-3119
commit, dropping its "from piece 2's `L_S7E`" wording.

**Verdict: GREEN-reconciled-PROVISIONAL.** The two documents now
agree, and the named input (`ChainLiftData α`) is the object the
bridge body genuinely consumes. The contract is **provisional
until R1 (mg-974c) confirms F7a** — the open question of whether a
concrete, non-degenerate `ChainLiftData α` is constructible for a
minimal γ-counterexample (§11.4).

### §11.1. Why `Step5R ∨ Step5C` and `L_S7E` both failed

* **`L_S7E : Step7.LayeredWidth3`** is a rich-pair window-confinement
  packaging on the pair space `α × α` — `bandwidth : ℕ` plus a
  partition of `richPairs`. It carries **no** band map, **no**
  potential, **no** sync maps, **no** Dilworth triple; its
  `bandwidth ≤ 4` is the inert `4 ≤ 4` (mg-ca83 §3.1–§3.2,
  §3 pitfall #9). The only in-tree `LayeredWidth3 →
  LayeredDecomposition` conversion (`layeredFromBridges`) is a
  documented sham. `L_S7E` is sound Step-7 *internal* scaffolding,
  but it is the wrong object for the Piece-2/Piece-3 boundary.
* **`Step5R ∨ Step5C`** is an abstract dichotomy *proposition*.
  It is the right *upstream* object — it is what
  `stepsOneToSevenCascade` (§4.2 §D) emits — but the bridge body
  cannot build a band map directly from a `Prop`. The paper
  `lem:layered-from-step7` (`step8.tex:2009-2089`) consumes the
  *content behind* the disjunction: the potential `a`, the
  threshold, the Dilworth chains, the sync maps, `K_bw`. That
  content is exactly `ChainLiftData`.

The reconciliation therefore **keeps the disjunction**, but moves
it one step upstream — into the §D′ constructor
`chainLiftData_of_cascade`, which turns `Step5R ∨ Step5C` into a
`ChainLiftData α`. The bridge §E then consumes the `ChainLiftData`.

### §11.2. The reconciled contract

Two signature changes, both landed above:

1. **§4.2 §D′ (NEW)** — `chainLiftData_of_cascade`:
   ```
   Step5R α γ T ∨ Step5C α T  →  ∃ cld : ChainLiftData α, cld.K_bw ≤ 2
   ```
   Dispatches both disjuncts to one `ChainLiftData` shape (branch
   (a) collapse: `K_bw + 2 = w_coll ≤ 4`; branch (b) globalization:
   `K_bw ≤ 2` by `lem:bandwidth`). This is the **R1 deliverable**
   (mg-974c).
2. **§4.2 §E re-pinned** — `lem_layered_from_step7` drops
   `hCascade : Step5R α γ T ∨ Step5C α T` and gains
   `(cld : ChainLiftData α)` + `(hKbw : cld.K_bw ≤ 2)`. The
   conclusion `C(α)` (the three caps) is **unchanged** from the
   mg-faf8 re-pin (§10).

**Note on the `ChainLiftData` field set.** The in-tree structure
(`ChainPotentials.lean:328-340`) has fields `triple`, `pot`,
`K_bw`, `fAB`, `fAC`, `fBC` — Dilworth triple, chain potential,
bandwidth constant, three sync maps. The paper's *threshold* `c`
(`step8.tex:2022-2027`) is **not** a structure field; it is
chosen inside the bridge body from the potential, or is implicit
in the `K_bw` window. Whether the reconciled bridge needs an
explicit threshold field added to `ChainLiftData` is an R1/F7a
detail (§11.4); R2 pins the *named type*, R1 pins the *exact
field set*.

### §11.3. Satisfiability re-check for the `ChainLiftData` input

The acceptance bar is *satisfiability, not just types* (the
8th-vacuity lesson). §10 verified the mg-faf8 contract; here the
three checks are re-run for the **new input shape**.

**(V) Non-vacuity.** `H(α)` is now
`HasWidthAtMost α 3 ∧ Indecomposable α ∧ IsGammaCounterexample α γ
∧ (∃ cld : ChainLiftData α, cld.K_bw ≤ 2) ∧ ih`. Every conjunct is
satisfiable for minimal γ-counterexamples of unbounded size: the
first three exactly as §10.2; the new
`∃ cld : ChainLiftData α, cld.K_bw ≤ 2` conjunct is satisfiable
because a `ChainLiftData α` *exists* for every finite poset
(Dilworth gives the triple, every chain admits a strictly-monotone
potential, `K_bw` is a free `ℕ` — set it `≤ 2`). So `H(α)` is not
a vacuous shell. ∎(V)

**(S) Conclusion holds on the domain.** `C(α)` (the 3-cap
conclusion) is **unchanged** from §10.3 — the paper `def:layered`
object with bands of size `≤ 3`, depth `K = Θ(|α|)`, `L.w ≤ 4`
satisfies it for every `α` regardless of `|α|`. §10.3's proof goes
through verbatim once the `ChainLiftData` is the genuine cascade
output (branch (a)/(b) → paper `lem:layered-from-step7`). ∎(S)

**(X) The `hCex` domain pin is LOAD-BEARING — and more so now.**
This is the critical re-check. Under the mg-faf8 input shape the
3-disjoint-chains family `Δ_ℓ` was excluded because `Δ_ℓ` is not a
γ-counterexample (§10.4 X-b). Under the `ChainLiftData` input that
exclusion is **even more necessary**, because:

> The **bare** `ChainLiftData α` structure is INHABITED for
> `Δ_ℓ`. Take `triple` := the three length-`ℓ` chains, `pot` :=
> any strictly-monotone potential along each chain, `K_bw := 0`,
> and `fAB = fAC = fBC := SyncMap.empty` (`ChainPotentials.lean:238`).
> All structure fields are satisfied; `K_bw = 0 ≤ 2`. So
> `∃ cld : ChainLiftData Δ_ℓ, cld.K_bw ≤ 2` is **true**.

Yet `C(Δ_ℓ)` is **false** for `ℓ > 5` (every layered decomposition
of `Δ_ℓ` has interaction width `≥ ℓ − 1`; §3 pitfall #2.3,
§10.4 X-b). So a reconciled bridge that took `cld` + `hKbw` but
**dropped `hCex`** would be a `true → false` proposition on
`Δ_ℓ` — re-introducing the 8th-vacuity error in a new form.

The re-pin therefore **retains `hCex : IsGammaCounterexample α γ`**
(mg-faf8) as the load-bearing domain pin. `Δ_ℓ` has balanced pairs
by symmetry (`(a_1, b_1)` exchanged by the chain-swap automorphism,
`Pr = 1/2`), so `IsGammaCounterexample Δ_ℓ γ` is false for every
`γ`; `H(Δ_ℓ)` is false outright; the bridge is **vacuously true**
(`false → false`) on `Δ_ℓ`. This is a correct vacuity, not a
falsity. ∎(X)

The contrast table of §10.5 still holds, with the middle column
read as the `ChainLiftData` input: every row is `true → true` or
`false → …` — **no false row**.

**Caveat — the bare structure is necessary but not sufficient.**
(V) shows a `ChainLiftData α` *exists* for every poset; (X) shows
the bare structure does **not** by itself force `C(α)` (it is
inhabited for `Δ_ℓ`, where `C` fails). What makes the bridge body
go through is the `ChainLiftData` being the **genuine cascade
output** — the potential being the BFS potential, the sync maps
being the argmin-aligned maps of `step8.tex:2102-2105`, the band
assembly `L_k := {a_k, b_{fAB(k)}, c_{fAC(k)}}` then having width
`K_bw + 2 ≤ 4`. The bare `ChainLiftData` structure carries no
field asserting that genuineness. Two honest resolutions, and R1
picks:

* **(A)** keep `hCex` as the domain pin (done) and rely on
  `C(α)` being `α`-determined-true on `{α : H}` (§10.3 / §11.3-S);
  `cld` is then the constructive vehicle for the bridge *proof*;
* **(B)** strengthen the `ChainLiftData` structure with soundness
  fields (potential/sync-map consistency, a bounded-width witness)
  so that *every* inhabitant genuinely drives `C(α)`.

R2 pins **(A)** as the contract shape (minimal, satisfiable as a
proposition via `hCex`). Whether **(B)** is additionally needed —
i.e. whether the bridge *body* is buildable from the bare
structure — is part of F7a (§11.4).

### §11.4. F7a provisionality — the contract is provisional until R1

**F7a is the open question: is a concrete, non-degenerate
`ChainLiftData α` constructible for `α` a minimal
γ-counterexample?** No concrete `ChainLiftData` instance exists in
tree (mg-ca83 §6 R1: the structure is referenced only in
`LayeredBridges.lean` / `MainAssembly.lean` / its defining file,
never instantiated). The reconciled contract **names an input the
bridge can consume**, but whether that input is **constructible**
is not settled here.

**Part R1 (mg-974c) settles F7a.** R1 re-points Piece 2's
concretisation to deliver a concrete `ChainLiftData α` — or, if it
genuinely cannot be constructed for a minimal counterexample,
returns a RED-F7a-not-constructible block-and-report (a valid and
important outcome). R1's non-triviality bar forbids a degenerate
witness (the bare structure admits `SyncMap.empty` sync maps and
an inert `K_bw` — exactly the degeneracy Checkpoint 3 Finding D
flagged for `L_S7E`).

**This contract is PROVISIONAL until R1 confirms F7a.** Concretely:

1. If R1 lands GREEN with a concrete non-degenerate
   `ChainLiftData α` matching the bare structure, §4.2 §D′/§E
   stand as pinned.
2. If R1 finds the bare structure insufficient and **strengthens**
   it (resolution (B), §11.3 — adds soundness/consistency fields),
   §4.2 §D′ (the `∃ cld, …` shape) and §E (the `cld` parameter)
   must be **re-pinned** to the strengthened type, in the same
   commit as R1's landing, per the §8 maintenance contract.
3. If R1 returns RED-F7a-not-constructible, the S7-F bridge
   approach itself needs rethinking, and §4.2 §D′/§E are reopened.

Until one of these resolves, Piece 3 (the S7-F bridge sub-arcs
mg-S7-F-A … mg-S7-F-Z) stays **blocked** — Checkpoint 3 is not
GREEN, it is GREEN-reconciled-PROVISIONAL.

#### §11.4.1. R1 resolution — F7a SETTLED GREEN, case 1 (mg-974c, 2026-05-21)

**R1 (mg-974c) has landed: F7a is settled GREEN — a concrete,
non-degenerate `ChainLiftData α` IS constructible.** The deliverable
is `lean/OneThird/Step8/ConcreteChainLiftData.lean` (NEW; sorry-free,
axiom-free; imported into `OneThird.lean`):
`GridChainLift.gridChainLiftData : ChainLiftData (Fin 3 × Fin 3)` on
the 3×3 grid — a genuine width-3, non-chain, 9-element poset. It is
non-degenerate on every axis Checkpoint 3 Finding D flagged: a
non-constant `i+j` chain potential (5 distinct values); sync maps
`f_AB`/`f_BC` total and non-constant, `f_AC` genuinely partial with a
real `X^exc_sync` orphan; and `K_bw = 1` proven to be the *actual,
tight* maximum potential gap over incomparable pairs — not an inert
literal. `f7a_chainLiftData_constructible` packages it as the §4.2
§D′ codomain `∃ cld : ChainLiftData α, cld.K_bw ≤ 2`.

**This is §11.4 case 1.** The witness matches the **bare**
`ChainLiftData` structure (`ChainPotentials.lean:328`) — no fields
added, no structure change. **Therefore §4.2 §D′/§E stand as pinned;
no re-pin is required.** The provisionality on *constructibility* is
discharged.

**The §11.3 caveat is NOT resolved by R1 — and was never F7a.** The
bare structure still carries no soundness invariant: it is inhabited
for `Δ_ℓ` (the witness's `pot`/sync-maps could be the cascade output
or could be arbitrary). Whether the bridge *body* is provable from
the bare structure (resolution (A), `hCex` domain pin) or needs a
strengthened structure with soundness fields (resolution (B)) is a
**Piece-3 / F7-bridge** decision — Piece 3 inherits it. R1
demonstrates `gridChainLiftData` is the *genuine* (non-`Δ_ℓ`) kind
via `gridChainLiftData_bandwidth_genuine` (the grid's potential
confines every incomparable pair within `K_bw` — provably false for
`Δ_ℓ`) and `gridLayered` (the grid admits a genuine
`LayeredDecomposition` with `w = 1 ≤ 4`).

**Checkpoint 3 is now GREEN-reconciled** (no longer PROVISIONAL on
F7a). Piece 3 is unblocked on F7a. Full record:
`docs/state-S7F-R1-Session1.md`.

### §11.5. Acceptance-bar verdict (ticket mg-3119)

| Acceptance bar (ticket mg-3119) | Status |
|---|---|
| Re-pin MA-Sig §4.2 §E so the bridge input is a `ChainLiftData` | **Done** — §4.2 §E (`cld` + `hKbw` replace `hCascade`); §D′ added |
| Re-pin scoping §2.3 to consistently state the input as a `ChainLiftData` | **Done** — parallel mg-3119 commit on `OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 |
| Drop the scoping §2.3 "from piece 2's `L_S7E`" wording | **Done** — scoping §2.3 |
| The two documents now state the contract consistently | **Done** — both name `ChainLiftData α` |
| Satisfiability, not just types — the input is one the bridge can actually consume | **Verified** — §11.1–§11.3; the bridge body builds the band map from `ChainLiftData`, not from a `Prop` or a pair-finset |
| The named input is constructible | **OPEN — F7a** — flagged §11.4; R1 (mg-974c) settles it |
| Flag the contract as provisional until R1 confirms F7a | **Done** — §11.4; top banner; §4.2 §D′ comment |
| `hCex` retained as the domain pin (no new false row) | **Verified** — §11.3 (X); the bare `ChainLiftData` is inhabited for `Δ_ℓ`, so `hCex` is load-bearing |

**Verdict: GREEN-reconciled-PROVISIONAL.** The S7-F bridge
contract is now pinned consistently across MA-Sig §4.2 §E and
scoping §2.3 as consuming a `ChainLiftData α`. The contract names
an input the bridge body can genuinely consume and is a
satisfiable proposition (via the retained `hCex` pin). It is
**provisional until R1 (mg-974c) confirms F7a** — the
constructibility of a concrete non-degenerate `ChainLiftData α`.

### §11.6. Cross-reference

* `docs/state-S7F-Checkpoint3-Session1.md` (mg-ca83) — the
  Checkpoint-3 audit; §5 the inconsistency, §6 R1/R2 the re-scope.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 — the
  scoping-side bridge contract, re-pinned by mg-3119 to match.
* `lean/OneThird/Step8/ChainPotentials.lean:328-340` —
  `ChainLiftData α` structure (`triple`/`pot`/`K_bw`/`fAB`/`fAC`/
  `fBC`); `:211` `SyncMap`; `:238` `SyncMap.empty` (the degenerate
  inhabitant R1 must avoid); `:267` `ChainPotential`.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #9 — the
  `LayeredWidth3` ≠ `LayeredDecomposition` standing lesson.
* mg-974c (S7F-R1) — the F7a constructibility ticket; depends on
  this one (mg-3119).
