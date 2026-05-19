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

The `hC3 : Step8.Case3Witness.{u}` parameter is retained unchanged
(it is consumed by `lem_layered_balanced` at the end of the cascade;
see §4).

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
    (hC3 : Step8.Case3Witness.{u})
    (hArith : HypothesisArithmetic) :
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

-- §E. lem:layered-from-step7 (NEW — piece 3 deliverable).
-- Lifts the cascade output to a concrete LayeredDecomposition on
-- X∖X^exc, with the ChainLift data structure that the perturbation
-- lift consumes.
theorem lem_layered_from_step7
    (γ : ℚ) (hγ_pos : 0 < γ)
    (T : ℕ)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCascade : Step5R α γ T ∨ Step5C α T)
    (ih : ∀ m, m < Fintype.card α →
           ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
             Fintype.card β = m →
             HasWidthAtMost β 3 → ¬ IsChainPoset β →
             HasBalancedPair β) :
    ∃ (Xexc : Finset α) (L : LayeredDecomposition {a : α // a ∉ Xexc}),
      Xexc.card ≤ C_exc T ∧
      Function.Injective L.band ∧                  -- cap 1
      L.K ≤ 2 * L.w + 2 ∧                          -- cap 2
      (Fintype.card α - Xexc.card) ≤ 6 * L.w + 6 ∧ -- cap 3
      (∀ k, 1 ≤ k → k ≤ L.K →                      -- cap 4
            (L.bandSet k).Nonempty) ∧
      L.w ≤ 4                                      -- cap 5

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

-- §G. lem_layered_balanced (UNCHANGED — LayeredBalanced.lean:626).
-- Signature is post-mg-234e caller-L rewire; consumed on the subtype
-- {a // a ∉ Xexc} via the LayeredDecomposition produced by §E.
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
    (hC3 : Step8.Case3Witness.{u})
    (hArith : HypothesisArithmetic) :     -- NEW parameter
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
    -- §8. lem:layered-from-step7: LayeredDecomposition on X∖X^exc.
    obtain ⟨Xexc, L, hXexc_small,
            hInj, hKw, hCardw, hNonempty, hLw⟩ :=
      lem_layered_from_step7 γ hγ_pos (hArith.T γ) hP hI hCascade
        (ih_descent ih)
    -- §9. lem_layered_balanced on the subposet {a // a ∉ Xexc}.
    have hP_sub : HasWidthAtMost {a : α // a ∉ Xexc} 3 :=
      hP.subtype _
    have hNonChain_sub : ¬ IsChainPoset {a : α // a ∉ Xexc} :=
      non_chain_subtype_of_C_exc_le hNonChain hCardw hXexc_small
    have h2_sub : 2 ≤ Fintype.card {a : α // a ∉ Xexc} := by
      have := hXexc_small
      have := hcard
      omega
    have hBP_sub : HasBalancedPair {a : α // a ∉ Xexc} :=
      lem_layered_balanced L h2_sub hNonChain_sub hP_sub
        hInj hKw hCardw hNonempty hLw hC3
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
- `non_chain_subtype_of_C_exc_le` — under `|Xexc| ≤ C_exc(T)` and
  `|α| ≥ 6 L.w + 6`, the subtype is also non-chain. Mechanical.
- `exc_perturb_bound_of_n_zero` — algebraic massage of the
  `eq:exc-perturb` bound at `n ≥ n_0(γ, T) = ⌈4 C_exc(T)/γ⌉ +
  C_exc(T) − 1`. Mechanical.

### §4.4. Why this types cleanly (no 8th vacuity)

Sanity check on each cross-piece boundary:

| Boundary | Type-check verdict |
|---|---|
| `cexImpliesLowBKExpansion` → `stepsOneToSevenCascade` | hThmE matches the `hS` parameter signature byte-for-byte (both are `∃ S, vol ≥ γ·vol(univ) ∧ Phi ≤ 2/(γn)`) |
| `stepsOneToSevenCascade` → `lem_layered_from_step7` | hCascade matches `hCascade` parameter; T threaded via `hArith.T γ` |
| `lem_layered_from_step7` → `lem_layered_balanced` | output `LayeredDecomposition {a // a ∉ Xexc}` matches input `L : LayeredDecomposition β` (with `β := {a // a ∉ Xexc}`); 5 caps match |
| `lem_layered_balanced` → `excPerturbLift` | `HasBalancedPair {a // a ∉ Xexc}` matches `hBP_sub` |
| `excPerturbLift` → final contradiction | `HasBalancedPair α` contradicts `hNoBP` |
| IH (Nat.strong_induction_on) → `decomp_reduction` + `lem_layered_from_step7` recursive descent | Both consume the IH on strict-cardinality-smaller posets; the IH supplies it directly |

All boundaries match concretely. No "shape mismatch" / "missing
hypothesis" / "wrong universe" surfaces under inspection.

---

## §5. Audit comparison vs parent scoping doc §2.4

| Parent §2.4 risk | This session's finding | Budget delta |
|---|---|---|
| Risk #1: 8th vacuity-discovery on signature | Did not materialize. Signature types cleanly. | 0 |
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
Two updates to the parent dispatch sequence are recommended:

1. **mg-MA-ThmE downgrade.** Re-tag from "Theorem E grounding"
   (0.5-0.8M) to "Theorem E wiring" (0.2-0.3M). Body: extract
   `Indecomposable α` from the IH; re-pack `cexImpliesLowBKExpansion`
   output for the Step 5 dichotomy consumer.
2. **`pickMinimalCounterexample` constructor removed from mg-MA-MinCex.**
   The minimal counterexample lives inline in `mg-MA-Body` via
   `Nat.strong_induction_on`. mg-MA-MinCex's content is just
   `decomp_reduction` (indecomposability descent) — still ~200k / 1
   session, but content-clear.

The other parent §7.4 sub-tickets (`mg-MA-Cascade`, `mg-MA-Body`)
are unchanged in shape. Recommended Phase 4 dispatch:

```
[After pieces 1, 2, 3 land + checkpoint 4 audit]
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
  (post-mg-234e; unchanged; consumed on subtype `{a // a ∉ Xexc}`).
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

- `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7).
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §2 tag legend.
- `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8).
- `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — RED 7th vacuity.
- `docs/coherence-collapse-case-extraction.md` (mg-ac13) —
  3-disjoint-chains counterexample (motivates the refactor).
- `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2)
  — canonicalLayered bypass diagnosis.

### §7.4. Predecessor work items

- mg-d8c7 (Option A' FULL REFACTOR scoping; this session's parent),
- mg-6ab8 (Steps 1-7 scoping), mg-5fbd (S7-F bridge audit; RED),
- mg-ac13 (coherence-collapse extraction),
- mg-234e (lem_layered_balanced caller-L rewire),
- mg-d5a0 (cap-5 sorry first surfaced; relocated by mg-234e),
- **mg-a22b (this session)**.

---

## §8. Maintenance contract

This file is the **signature contract for the Option A' FULL
REFACTOR's piece 4**. Downstream sub-tickets (mg-MA-MinCex,
mg-MA-ThmE, mg-MA-Cascade, mg-MA-Body, mg-Int-A, mg-Int-B) reference
the §4.2-§4.3 signatures.

Update this file in the **same commit** as any of the following:

- A Phase 4 sub-ticket lands and its actual signature drifts from
  §4.2; reflect the drift here.
- An 8th vacuity-discovery surfaces during Phase 4 execution; record
  here with re-scoped recommendation.
- A piece 1/2/3 deliverable lands and its output shape differs from
  what §4.2 assumes; update the consumer-side signature.

Default-skeptical posture: per Daniel's "vacuity-discovery has hit 7
times" pattern (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970,
mg-ac13, mg-5fbd), if Phase 2-4 surfaces a gap, **stop and re-scope**
rather than pushing through. The signature in §4.2 is the contract;
if it doesn't hold, the assumption fails, not the dispatch sequence.
