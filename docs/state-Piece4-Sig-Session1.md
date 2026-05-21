# State — Piece-4-Sig — Session 1: the pinned Piece-4 signature contract

**Owner.** `mg-92a8` (OneThird-Piece4-Sig per `mg-d8c7` §7.4
`mg-MA-Sig` / the Phase-2 Piece-4 pre-flight).

**Scope.** Pre-flight **signature design only** for Piece 4 of the
Option A' FULL REFACTOR (`mg-d8c7`, doc
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.4) — the
`MainAssembly` proof-by-contradiction refactor. **SCOPING ticket — no
Lean code.** Output: this document. It finalises the signatures the
Piece-4 *body* sub-tickets (`mg-MA-MinCex`, `mg-MA-ThmE`,
`mg-MA-Cascade`, `mg-MA-Body`) build against, so they need no
downstream signature re-scope.

**Relationship to `docs/state-MA-Sig-Session1.md` (mg-a22b).** That
document is the **Phase-1** pre-flight signature contract. It was
written *before* Pieces 3 and 6 landed and pins them in **pseudo-Lean**
(§4.2 §E/§F/§G). This document is the **Phase-2 Piece-4** pre-flight:
it re-pins the §4.2 contract against the **actual finalised Lean
signatures** of the landed pieces, and runs the satisfiability check
the ticket mandates — *not just type-compatibility*. Where this
document and MA-Sig §4.2 disagree, **this document wins** (it audited
the source; MA-Sig §4.2 is archaeology for the §E/§F/§G rows).

**Inputs (re-read on this worktree's branch before writing).**

- `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) §2.4
  — the Piece 4 spec.
- `docs/state-MA-Sig-Session1.md` (mg-a22b/mg-faf8/mg-3119) — the
  Phase-1 contract; §4.2 §E/§G, §10, §11.
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) §0 (mg-02cd /
  mg-65de bullets), §2 tag legend, §3 pitfalls #5/#6/#9/#10.
- `lean/OneThird/Step8/LayeredFromStep7.lean` (mg-02cd) — Piece 3,
  `lem_layered_from_step7` **finalised**.
- `lean/OneThird/Step8/LayeredBalancedFull.lean` (mg-65de) — Piece
  6, `lem_layered_balanced_full` + the disclosed axiom.
- `lean/OneThird/Step8/ExcBalancedLift.lean` (mg-876f) — S7-F-D,
  `not_isGammaCounterexample_of_exc_balanced[_compl]` / `excPerturbLift`.
- `lean/OneThird/Step8/TheoremE.lean` — `cexImpliesLowBKExpansion`.
- `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`.
- `lean/OneThird/Step8/ExceptionalSet.lean` — `ExcBudget`, `C_exc`.
- `lean/OneThird/Step8/BridgeLayered.lean:162` —
  `ChainLiftData.PotPosetMono`.
- `lean/OneThird/Step8/MainAssembly.lean` — the refactor target.
- `lean/OneThird/MainTheorem.lean:56` — the headline wrapper.
- `lean/OneThird/LinearExtension.lean:38/50` — `HasBalancedPair`,
  `IsGammaCounterexample`.
- `lean/OneThird/Mathlib/Poset/Indecomposable.lean:60` —
  `Indecomposable`.
- `lean/AXIOMS.md:560` — `lem_layered_balanced_irreducible_base`.

---

## §0. Verdict — **GREEN-Piece-4-signatures-pinned-and-satisfiability-verified**

The proof-by-contradiction refactor signatures for Piece 4 are
**pinned in §4** and each is **satisfiability-verified against the
actual landed Piece-3/6 + S7-F-D Lean code** in §5 — not merely
type-compatible. **No 11th vacuity-discovery** surfaced under
default-skeptical re-audit.

**Headline finding.** MA-Sig §4.2 §E/§F (the Phase-1 pseudo-Lean
pins) were written before Pieces 3/6 landed and are **stale** — the
*actual* finalised signatures differ. Seven mismatches are flagged
as findings **F1–F7** (§4) and re-pinned here. None is a
satisfiability defect; they are the predictable drift of a Phase-1
pseudo-Lean contract against a Phase-2 finalised implementation.
**The acceptance-bar question — does each pinned signature have a
real witness path from the landed pieces? — is answered YES** (§5),
and the end of the chain (bridge → Piece 6 → S7-F-D) is exhibited
**concretely non-vacuously** on the R1 grid witness.

The seven findings, one line each:

| # | Finding | §4 re-pin |
|---|---|---|
| F1 | `lem_layered_from_step7` (Piece 3) takes `(T, cld, hKbw, hMono, hBudget)` — **not** the MA-Sig §4.2 §E `(γ, hP, hI, hCex, cld, hKbw, ih)`. | §4.6 |
| F2 | `chainLiftData_of_cascade` (§D′) codomain must be **widened** to emit `hMono` + `hBudget`, not just `K_bw ≤ 2` — the actual bridge consumes them. | §4.5 |
| F3 | The perturbation lift concludes `¬ IsGammaCounterexample α γ`, **not** `HasBalancedPair α` (MA-Sig §4.2 §F was ill-posed; mg-876f). Final contradiction is on `hCex`, not `hNoBP`. | §4.7 |
| F4 | The bridge output carrier is `↥(Xexcᶜ)`, not `{a // a ∉ Xexc}`; consume via the S7-F-D `_compl` variant. | §4.6/§4.7 |
| F5 | The `exc_perturb` side condition is `2·\|Xexc\|/(\|α\|−\|Xexc\|+1) ≤ γ` (`≤ γ`, not the MA-Sig §4.3 `< γ/2`). | §4.7 |
| F6 | Piece 6 carries the disclosed axiom `lem_layered_balanced_irreducible_base`; wiring Piece 6 into the headline adds it to `#print axioms` (replacing `case3Witness_hasBalancedPair_outOfScope`). | §4.4/§6 |
| F7 | The landed bridge needs `[DecidableLE α]`; the headline lacks it. Open `width3_one_third_two_thirds[_assembled]` proof body with `classical`. | §4.1 |

The three Phase-1 MA-Sig decisions are **re-confirmed unchanged**:
1. `hyp:arith` threading — Lean predicate (`HypothesisArithmetic`),
   not project axiom (§4.2).
2. minimal-counterexample shape — `Nat.strong_induction_on` on
   `Fintype.card α`, no separate `pickMinimalCounterexample`
   constructor (§4.3).
3. Theorem E status — **SUBSTANTIVE**; `mg-MA-ThmE` is a wiring
   sub-arc, not a grounding sub-arc (§4.4).

Acceptance bar (against the ticket body):

| # | Bar | Status |
|---:|---|---|
| 1 | Pin the proof-by-contradiction setup for `width3_one_third_two_thirds_assembled` | §4.1, §4.8 |
| 2 | `pickMinimalCounterexample` — confirm the `Nat.strongRecOn`-on-`card` form | §4.3 — confirmed |
| 3 | Theorem E wiring signature | §4.4 |
| 4 | `stepsOneToSevenCascade` → Step5R/Step5C, wired into `chainLiftData_of_cascade` | §4.5 |
| 5 | Headline consumes bridge (P3) → `lem_layered_balanced_full` (P6) → `exc_perturb` | §4.6, §4.7 |
| 6 | `hyp:arith` threading — Lean predicate | §4.2 — confirmed |
| 7 | **Satisfiability**, not just type-compatibility; real witness path from landed pieces | §5 |
| 8 | Flag mismatches as findings; do not paper over | §4, findings F1–F7 |

---

## §1. Context — what Piece 4 is, and what landed since MA-Sig

### §1.1. The refactor target

The headline `OneThird.width3_one_third_two_thirds`
(`MainTheorem.lean:56`) descends through
`Step8.width3_one_third_two_thirds_assembled`
(`MainAssembly.lean:353`) which is **direct construction**: given
`(hP, hNonChain, hC3 : Case3Witness)`, it dispatches through
`mainAssembly` / `mainTheoremInputsOf` / `caseC_canonicalLayered`,
terminating at the cap-5 structured `sorry` at
`MainAssembly.lean:265` (`canonicalLayered α` has `w = |α|`, fails
`L.w ≤ 4`). `mg-5fbd` proved this `sorry` is **architecturally
unclosable in-place** (PROOF-STRUCTURE-ONBOARDING §3 pitfall #5).

Piece 4 rewrites `width3_one_third_two_thirds_assembled` from direct
construction to **proof by contradiction**, mirroring paper
`thm:main-step8` (`step8.tex:106-260`): assume `¬ HasBalancedPair`,
take a minimal γ-counterexample, run Theorem E + the Steps 1-7
cascade, lift to a balanced pair, contradict.

### §1.2. What landed since the MA-Sig Phase-1 contract

MA-Sig (`mg-a22b`, then `mg-faf8`/`mg-3119`) pinned the Phase-1
contract in **pseudo-Lean**. Since then the downstream pieces
**landed as real Lean**:

| Piece | Deliverable | File | Work item |
|---|---|---|---|
| 3 | `lem_layered_from_step7` **finalised** | `LayeredFromStep7.lean:152` | mg-02cd (S7-F-Z) |
| 6 | `lem_layered_balanced_full` | `LayeredBalancedFull.lean:169` | mg-65de (Piece-6 redo) |
| S7-F-D | `not_isGammaCounterexample_of_exc_balanced[_compl]`, `excPerturbLift` | `ExcBalancedLift.lean:273/345/310` | mg-876f |
| R1 | `gridChainLiftData` + `grid_PotPosetMono` + `grid_excBudget` (concrete witness) | `ConcreteChainLiftData.lean`, `BridgeLayered.lean:510`, `ExceptionalSet.lean:425` | mg-974c |

These are the **actual finalised** objects Piece 4 must consume. The
MA-Sig §4.2 §E/§F/§G rows predate them and **must be re-pinned** — that
is the bulk of this document (§4, findings F1–F7).

### §1.3. What is NOT in tree (and is expected not to be)

`stepsOneToSevenCascade`, `chainLiftData_of_cascade`, `Step5R`,
`Step5C`, `HypothesisArithmetic`, `n_zero`, `decomp_reduction`,
`gamma_counterexample_of_no_BP` — **none are in tree** (verified by
`grep`). This is **correct and expected**: they are the Piece-4
*body* deliverables (`mg-MA-Cascade`, `mg-MA-MinCex`, `mg-MA-Body`)
that *this* pre-flight scopes. The pre-flight pins their signatures;
the body sub-tickets build them. Their satisfiability is established
in §5 at the signature level + against the landed Pieces 1/2 math
content (Step 5 dichotomy, S7-A–E grounded forms, R1 concrete
witness). The general `chainLiftData_of_cascade` discharge for an
arbitrary minimal γ-counterexample is the cross-Piece-1/2 work that
remains; see §5.4.

---

## §2. The actual landed signatures (audit)

Verbatim from the source on this worktree's branch. **These are the
contract anchors** — every §4 pin is derived from them.

### §2.1. Piece 3 — `lem_layered_from_step7` (`LayeredFromStep7.lean:152`)

```lean
theorem lem_layered_from_step7 (T : ℕ) (cld : ChainLiftData α)
    (hKbw : cld.K_bw ≤ 2)
    (hMono : cld.PotPosetMono)
    (hBudget : ExcBudget cld T) :
    ∃ (Xexc : Finset α) (L : LayeredDecomposition ↥(Xexcᶜ)),
      Xexc.card ≤ C_exc T ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4
```

(File-level `variable {α} [PartialOrder α] [Fintype α]
[DecidableEq α] [DecidableLE α]`.)

### §2.2. Piece 6 — `lem_layered_balanced_full` (`LayeredBalancedFull.lean:169`)

```lean
theorem lem_layered_balanced_full.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ OneThird.IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :
    OneThird.HasBalancedPair β
```

Strong induction on `Fintype.card β`; consumes the disclosed axiom
`lem_layered_balanced_irreducible_base` (`LayeredBalancedFull.lean:127`,
`AXIOMS.md:560`) in the irreducible-twin-free branch.

### §2.3. S7-F-D — the perturbation lift (`ExcBalancedLift.lean`)

```lean
theorem not_isGammaCounterexample_of_exc_balanced_compl (γ : ℚ)
    (T : Finset α)
    (hε : 2 * (T.card : ℚ) / (Fintype.card α - T.card + 1 : ℚ) ≤ γ)
    (h : HasBalancedPair {a : α // a ∈ Tᶜ}) :
    ¬ IsGammaCounterexample α γ                          -- :345

theorem excPerturbLift (γ : ℚ) (Xexc : Finset α)
    (hXexc_small : 2 * (Xexc.card : ℚ)
      / (Fintype.card α - Xexc.card + 1 : ℚ) ≤ γ)
    (hBP_sub : HasBalancedPair {a : α // a ∉ Xexc}) :
    ¬ IsGammaCounterexample α γ                          -- :310
```

The bridge-output-carrier variant `_compl` is the one Piece 4 uses:
`{a // a ∈ Tᶜ}` is definitionally `↥(Tᶜ)` (the bridge output
carrier). The `excPerturbLift_of_bridge_output`
(`LayeredFromStep7.lean:192`) already wires Piece 3 ⟶ S7-F-D and
is the boundary template (see §5.2).

### §2.4. Theorem E — `cexImpliesLowBKExpansion` (`TheoremE.lean:171`)

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

**SUBSTANTIVE** (sorry-free, axiom-free; MA-Sig §3.3 re-confirmed).
Signature **unchanged** from MA-Sig §4.2 §C.

### §2.5. The supporting data types (unchanged, in tree)

- `ChainLiftData α` — `ChainPotentials.lean:328`: fields `triple`,
  `pot`, `K_bw`, `fAB`, `fAC`, `fBC`.
- `ChainLiftData.PotPosetMono` — `BridgeLayered.lean:162`:
  `∀ x y : α, x < y → D.pot.a x < D.pot.a y` (decidable; paper
  `prop:71`).
- `ExcBudget (D : ChainLiftData α) (T : ℕ)` — `ExceptionalSet.lean:343`:
  a `Prop`-structure with fields `band_le`, `orphan_AB`, `orphan_AC`,
  `orphan_BC` (paper `lem:bandwidth` + per-chain orphan bounds).
- `C_exc (T : ℕ) : ℕ := c₁ T + 6` — `ExceptionalSet.lean:336`.
- `HasBalancedPair`, `IsGammaCounterexample` — `LinearExtension.lean:38/50`.
- `Indecomposable α` — `Mathlib/Poset/Indecomposable.lean:60`.

---

## §3. The decision recap (§3.1–§3.3 of MA-Sig — re-confirmed)

The three Phase-1 decisions are re-confirmed; nothing in the landed
Pieces 3/6/S7-F-D disturbs them.

1. **`hyp:arith` — Lean predicate.** A `HypothesisArithmetic`
   structure threaded as an explicit parameter (MA-Sig §3.1). Not a
   project axiom: paper-faithful (`step8.tex` states the theorem
   *"Assume Hypothesis hyp:arith"*), pattern-matches the other
   in-Lean predicate hypotheses, and is discharge-friendly.
2. **Minimal counterexample — `Nat.strong_induction_on`.** On
   `Fintype.card α`, IH inline; **no** separate
   `pickMinimalCounterexample` constructor (MA-Sig §3.2). Universe-safe
   (no `Decidable (∃ α : Type u, …)`), idiomatic, IH-is-minimality.
3. **Theorem E — SUBSTANTIVE.** No grounding sub-arc;
   `cexImpliesLowBKExpansion` is a complete proof (MA-Sig §3.3).

---

## §4. The pinned Piece-4 signature contract

Pseudo-Lean. Downstream Piece-4 body sub-tickets reference this
section by sub-number. **Symbols marked `[LANDED]` exist in tree
verbatim (§2); symbols marked `[Piece-4]` are this pre-flight's
pinned targets for the body sub-tickets.**

### §4.1. The headline signature

```lean
-- [Piece-4 — mg-MA-Body]  width3_one_third_two_thirds_assembled
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : HypothesisArithmetic) :        -- NEW; hC3 DROPPED
    HasBalancedPair α
```

- `hC3 : Case3Witness` is **dropped** (MA-Sig §3.1 re-pin: the
  end-of-cascade consumer is Piece 6, which discharges the witness
  internally).
- `hArith : HypothesisArithmetic` is **added** (decision 1).
- **F7 — `[DecidableLE α]`.** The landed `lem_layered_from_step7`
  (§2.1) carries a file-level `[DecidableLE α]` instance argument;
  the headline does not have it. **Pin:** the proof body opens with
  `classical` (or `letI := Classical.decRel ((· ≤ ·) : α → α →
  Prop)`). Since `width3_one_third_two_thirds[_assembled]` is a
  `theorem` (a `Prop`), this is invisible to callers — **no public
  API change**. Do **not** add `[DecidableLE α]` to the headline
  signature; that would propagate into `MainTheorem.width3_one_third_two_thirds`
  and change the paper-stated public surface.

The outer wrapper `MainTheorem.width3_one_third_two_thirds`
(`MainTheorem.lean:56`) gains the same `hArith` parameter and
forwards it.

### §4.2. `HypothesisArithmetic` (decision 1)

```lean
-- [Piece-4 — mg-MA-Sig/body]  hyp:arith as an in-Lean structure
def c5 : ℕ → ℚ          -- step5.tex c_5(T,γ)        [Piece-1]
def c6 : ℚ              -- step6.tex c_6             [Piece-1]
def delta0 : ℚ → ℚ      -- δ_0(γ)                    [Piece-1]
def T_zero : ℕ          -- T_0                        [Piece-1]

structure HypothesisArithmetic where
  T : ℚ → ℕ
  T_ge_T0 : ∀ γ : ℚ, 0 < γ → γ < 1/3 → T_zero ≤ T γ
  arith_holds : ∀ γ : ℚ, 0 < γ → γ < 1/3 →
    (8 : ℚ) ≤ γ^2 * c5 (T γ) * c6 * delta0 γ
```

The constants `c5/c6/delta0/T_zero` are **Piece-1** deliverables
(Steps 5/6 grounded forms). The *body* of `HypothesisArithmetic` is
out of scope for Piece 4 — only the *threading* is. Unchanged from
MA-Sig §3.1/§4.1.

### §4.3. The minimal counterexample — `Nat.strong_induction_on` (decision 2)

**Confirmed: `Nat.strong_induction_on` on `Fintype.card α`, IH
inline. No `pickMinimalCounterexample` constructor function.** This
is the form MA-Sig §3.2 pinned, and the landed `lem_layered_balanced_full`
(§2.2) itself uses exactly this idiom internally
(`LayeredBalancedFull.lean:189` `induction n using
Nat.strong_induction_on`), confirming it is the in-tree-idiomatic
choice.

The IH shape, as it appears in the `mg-MA-Body` proof:

```lean
induction hcard : Fintype.card α using Nat.strong_induction_on
  generalizing α with
| _ n ih =>
  -- ih : ∀ m, m < n → ∀ {β : Type u} [PartialOrder β] [Fintype β]
  --        [DecidableEq β], Fintype.card β = m →
  --        HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β
  …
```

**Where the IH is consumed.** *Only* by `decomp_reduction` (§4.4),
to prove `Indecomposable α`. It is **not** a parameter of
`lem_layered_from_step7` (the landed bridge does not recurse — see
F1) nor of `lem_layered_balanced_full` (Piece 6 runs its own
internal strong induction). So `mg-MA-MinCex` content = the single
lemma `decomp_reduction` (a minimal γ-cex is indecomposable) + the
`ih_descent` adapter. ~1 session, ~200k.

### §4.4. Theorem E wiring (decision 3 — `[LANDED]` + thin wiring)

`cexImpliesLowBKExpansion` (§2.4) is **consumed verbatim**; no
grounding. The Piece-4 `mg-MA-ThmE` sub-arc is **wiring only**:

1. `decomp_reduction` — produce `Indecomposable α` from the minimal
   counterexample. Lifts paper `rem:decomp-reduction`
   (`step8.tex:274`): if `α = L ⊕ U` decomposable, the non-chain
   summand is a strictly-smaller width-3 non-chain poset with no
   balanced pair (balanced pairs lift between ordinal summands by
   the in-tree marginal-invariance `probLT_restrict_eq`), so the IH
   (§4.3) gives it a balanced pair — contradiction; hence `α` is
   indecomposable. **Consumes the IH.** Folded into `mg-MA-MinCex`.
2. `ih_descent` — adapt the `Nat.strong_induction_on` IH to the form
   `decomp_reduction` consumes.

   ```lean
   -- [Piece-4]  decomp_reduction : a minimal γ-cex is indecomposable
   theorem decomp_reduction
       (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
       (hCex : IsGammaCounterexample α γ)
       (ih : ∀ m, m < Fintype.card α →
              ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
                Fintype.card β = m →
                HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β) :
       Indecomposable α
   ```

`cexImpliesLowBKExpansion` is then called directly with
`(γ, hγ_pos, hγ_third, hP, hI, hCex, h2)` — the §2.4 signature.

**LANDED (mg-3638, `mg-MA-ThmE`).** The wiring is in tree:
`lean/OneThird/Step8/TheoremEWiring.lean` (NEW, sorry-free,
axiom-free — only `propext`/`Classical.choice`/`Quot.sound`).
`theoremE_lowConductanceWitness` is the wired call of
`cexImpliesLowBKExpansion` with the §2.4 tuple, its conclusion
written out as the **exact** cascade-`hS` shape (§4.5) so the
Theorem-E → cascade boundary is fixed at one named point. The
`mg-MA-Body` body step §6 may call either
`theoremE_lowConductanceWitness` or `cexImpliesLowBKExpansion`
directly — they are signature-identical. The output type-checks
against the §4.5 cascade `hS` pin verbatim — **no ill-posed
obligation, no block-report.** The companion
`theoremE_lowConductanceWitness_nonempty` is a genuineness
certificate: the wired witness's cut `S` is provably non-empty
(forced by the bulk-volume bound), so the wiring is not vacuous
routing. The supporting `volume_univ_pos` records
`0 < vol(𝓛(P))` for `|α| ≥ 2`. The four Theorem-E-wiring sub-arc
items in §4.4 list 1–2 (`decomp_reduction`, `ih_descent`) remain
`mg-MA-MinCex`; `mg-MA-ThmE` is complete.

**F6 note (axioms).** Theorem E itself is axiom-free. The headline's
post-refactor `#print axioms` is addressed in §6.

### §4.5. The Steps 1-7 cascade — `stepsOneToSevenCascade` + `chainLiftData_of_cascade`

Two `[Piece-4]` signatures. `stepsOneToSevenCascade` produces the
abstract Step-5 dichotomy; `chainLiftData_of_cascade` turns it into
the concrete bridge input.

```lean
-- [Piece-4 — mg-MA-Cascade]  Step5R / Step5C — α-indexed wrappers
--   around the in-tree Step5.Step5Richness (Dichotomy.lean:148) and
--   Step5.Step5Collapse (Dichotomy.lean:165), which are numeric-arg
--   predicates. The α-side wrapper supplies LP_card / fiberSum / c_R /
--   p / q from the BK-graph of α.
def Step5R (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (γ : ℚ) (T : ℕ) : Prop := …
def Step5C (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (T : ℕ) : Prop := …

-- [Piece-4 — mg-MA-Cascade]  the cascade
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
```

**F2 — `chainLiftData_of_cascade` codomain WIDENED.** MA-Sig §4.2
§D′ pinned the codomain `∃ cld : ChainLiftData α, cld.K_bw ≤ 2`.
**That is insufficient.** The landed bridge `lem_layered_from_step7`
(§2.1) consumes **three** facts about `cld`: `hKbw : cld.K_bw ≤ 2`,
`hMono : cld.PotPosetMono`, **and** `hBudget : ExcBudget cld T`. So
the constructor must emit all three:

```lean
-- [Piece-4 — mg-MA-Cascade]  ChainLiftData constructor — WIDENED (F2)
theorem chainLiftData_of_cascade
    (γ : ℚ) (hγ_pos : 0 < γ)
    (T : ℕ)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)            -- LOAD-BEARING (§5.3)
    (hCascade : Step5R α γ T ∨ Step5C α T) :
    ∃ cld : ChainLiftData α,
      cld.K_bw ≤ 2 ∧ cld.PotPosetMono ∧ ExcBudget cld T
```

The three output conjuncts are exactly the three `cld`-hypotheses
the landed bridge needs. `hCex` is **load-bearing** here — see §5.3
(the bare `ChainLiftData` is inhabited for the 3-disjoint-chains
family `Δ_ℓ`, where `PotPosetMono`/`ExcBudget` provably *fail*; only
`hCex` excludes `Δ_ℓ`). This is the **correct home** for the `hCex`
domain pin: MA-Sig §4.2 §E carried `hCex` *on the bridge*, but
mg-02cd's QA finding established it is inert in the bridge body — the
`Δ_ℓ`-exclusion role is carried by `hMono`/`hBudget`. F2 relocates
`hCex` one level up, to the constructor that *produces*
`hMono`/`hBudget`.

`n_zero : ℚ → ℕ → ℕ` is a `[Piece-4]` helper (`n_zero γ T` ≈
`⌈4·C_exc T/γ⌉ + C_exc T`), pinned so the §4.7 perturbation side
condition is dischargeable.

### §4.6. The S7-F bridge consumption — `lem_layered_from_step7` `[LANDED]`

**F1 — the bridge signature is the §2.1 landed form, not MA-Sig
§4.2 §E.** The Piece-4 body calls the bridge as:

```lean
obtain ⟨Xexc, L, hXexc, hNonempty, hLw⟩ :=
  lem_layered_from_step7 (hArith.T γ) cld hKbw hMono hBudget
```

Differences from MA-Sig §4.2 §E (pseudo-Lean), all flagged:

| MA-Sig §4.2 §E param | Landed `lem_layered_from_step7` | Resolution |
|---|---|---|
| `γ`, `hγ_pos` | absent | dropped — bridge is γ-agnostic |
| `hP`, `hI` | absent | dropped — not used in the bridge body |
| `hCex` | absent | **relocated to `chainLiftData_of_cascade`** (F2; mg-02cd QA finding) |
| `ih` | absent | dropped — the bridge does not recurse |
| `cld`, `hKbw` | `cld`, `hKbw` | unchanged |
| — | `hMono : cld.PotPosetMono` | **NEW** — must be supplied (F2 widening) |
| — | `hBudget : ExcBudget cld T` | **NEW** — must be supplied (F2 widening) |
| `T` | `T` (first positional) | unchanged |

Output (unchanged from §2.1): `∃ Xexc L, Xexc.card ≤ C_exc T ∧
(band-nonempty) ∧ L.w ≤ 4`, with **F4** — `L :
LayeredDecomposition ↥(Xexcᶜ)`, the `Finset.compl`-coercion carrier
(**not** `{a // a ∉ Xexc}`).

### §4.7. Piece 6 + the perturbation lift — `[LANDED]`

```lean
-- §9. Piece 6 on the bridge carrier ↥(Xexcᶜ).            [LANDED §2.2]
have hP_sub  : HasWidthAtMost ↥(Xexcᶜ) 3 :=
  hasWidthAtMost_subtype hP (Xexcᶜ)         -- LayeredBalanced.lean:375
have hNC_sub : ¬ IsChainPoset ↥(Xexcᶜ) :=
  non_chain_subtype_of_exc hNonChain hXexc hn0          -- [Piece-4]
have h2_sub  : 2 ≤ Fintype.card ↥(Xexcᶜ) :=
  card_compl_ge_two hXexc hn0                           -- [Piece-4]
have hBP_sub : HasBalancedPair ↥(Xexcᶜ) :=
  lem_layered_balanced_full L h2_sub hNC_sub hP_sub hLw

-- §10. S7-F-D perturbation lift.                          [LANDED §2.3]
have hε : 2 * (Xexc.card : ℚ)
    / (Fintype.card α - Xexc.card + 1 : ℚ) ≤ γ :=
  exc_perturb_bound_of_n_zero hn0 hXexc                  -- [Piece-4]
have hNotCex : ¬ IsGammaCounterexample α γ :=
  not_isGammaCounterexample_of_exc_balanced_compl γ Xexc hε hBP_sub
```

- **F4** — Piece 6 is polymorphic in `β`; instantiate `β :=
  ↥(Xexcᶜ)`. The bridge emits `L : LayeredDecomposition ↥(Xexcᶜ)`,
  which is exactly the `L` argument. `hasWidthAtMost_subtype` takes
  the finset `Xexcᶜ` and produces `HasWidthAtMost ↥(Xexcᶜ) 3`.
- **F3** — the perturbation lift concludes **`¬ IsGammaCounterexample
  α γ`**, not `HasBalancedPair α`. MA-Sig §4.2 §F pinned
  `excPerturbLift : … → HasBalancedPair α`; mg-876f proved that
  **ill-posed** (the perturbation widens the balance window by
  `ε > 0`, so an exact `HasBalancedPair α` is *false* whenever
  `|Xexc| ≥ 1`). The honest landed form (§2.3) concludes the
  negation of the γ-counterexample property — which is exactly what
  the proof-by-contradiction body needs.
- **F4** — use the `_compl` variant
  `not_isGammaCounterexample_of_exc_balanced_compl` (carrier
  `{a // a ∈ Tᶜ}` = `↥(Tᶜ)`), **not** the `{a // a ∉ Xexc}` form
  `excPerturbLift`. `T := Xexc`.
- **F5** — the side condition is `2·|Xexc|/(|α|−|Xexc|+1) ≤ γ`
  (`≤ γ`). MA-Sig §4.3 wrote `< γ/2`; the landed lemma takes `≤ γ`.
  `exc_perturb_bound_of_n_zero` (a `[Piece-4]` helper) discharges it
  from `hn0` (`n_zero γ T ≤ |α|`) and `hXexc` (`|Xexc| ≤ C_exc T`):
  the LHS is monotone-decreasing in `|α|` and monotone-increasing in
  `|Xexc|`, so `n_zero` is pinned (§4.5) large enough that the worst
  case `|Xexc| = C_exc T` still satisfies `≤ γ`.

### §4.8. The pinned proof-by-contradiction body

The complete `mg-MA-Body` target. Auxiliary `[Piece-4]` lemmas are
listed after.

```lean
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : HypothesisArithmetic) :
    HasBalancedPair α := by
  classical                                    -- F7: DecidableLE α
  -- §1. Strong induction on |α| (decision 2).
  induction hcard : Fintype.card α using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    by_cases hsmall : n ≤ 1
    · exact absurd (chain_of_subsingleton hsmall) hNonChain
    -- §2. Proof by contradiction.
    by_contra hNoBP
    -- §3. Pick γ making α a γ-counterexample.
    obtain ⟨γ, hγ_pos, hγ_third, hCex⟩ :=
      gamma_counterexample_of_no_BP hNonChain hNoBP
    have h2 : 2 ≤ Fintype.card α := by omega
    -- §4. Indecomposability (consumes ih).
    have hI : Indecomposable α :=
      decomp_reduction hP hNonChain hCex (ih_descent ih)
    -- §5. n ≥ n_0 realisability.
    have hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card α :=
      n_zero_le_of_cascade_realised hArith hcard hγ_pos hγ_third
    -- §6. Theorem E (LANDED).
    have hThmE :=
      cexImpliesLowBKExpansion γ hγ_pos hγ_third hP hI hCex h2
    -- §7. Steps 1-7 cascade.
    have hCascade :=
      stepsOneToSevenCascade γ hγ_pos hγ_third hP hI hCex h2
        hArith hn0 hThmE
    -- §7'. ChainLiftData (F2 — widened: emits hKbw + hMono + hBudget).
    obtain ⟨cld, hKbw, hMono, hBudget⟩ :=
      chainLiftData_of_cascade γ hγ_pos (hArith.T γ) hP hI hCex hCascade
    -- §8. S7-F bridge (LANDED — F1: hMono/hBudget, no hCex/ih).
    obtain ⟨Xexc, L, hXexc, hNonempty, hLw⟩ :=
      lem_layered_from_step7 (hArith.T γ) cld hKbw hMono hBudget
    -- §9. Piece 6 (LANDED) on ↥(Xexcᶜ)  (F4).
    have hP_sub  : HasWidthAtMost ↥(Xexcᶜ) 3 :=
      hasWidthAtMost_subtype hP (Xexcᶜ)
    have hNC_sub : ¬ IsChainPoset ↥(Xexcᶜ) :=
      non_chain_subtype_of_exc hNonChain hXexc hn0
    have h2_sub  : 2 ≤ Fintype.card ↥(Xexcᶜ) :=
      card_compl_ge_two hXexc hn0
    have hBP_sub : HasBalancedPair ↥(Xexcᶜ) :=
      lem_layered_balanced_full L h2_sub hNC_sub hP_sub hLw
    -- §10. S7-F-D perturbation lift (LANDED — F3/F4/F5).
    have hε : 2 * (Xexc.card : ℚ)
        / (Fintype.card α - Xexc.card + 1 : ℚ) ≤ γ :=
      exc_perturb_bound_of_n_zero hn0 hXexc
    have hNotCex : ¬ IsGammaCounterexample α γ :=
      not_isGammaCounterexample_of_exc_balanced_compl γ Xexc hε hBP_sub
    -- §11. Contradiction — F3: contradict hCex, not hNoBP.
    exact hNotCex hCex
```

`mainAssembly`, `mainTheoremInputsOf`, `caseC_canonicalLayered`,
`MainTheoremInputs` (`MainAssembly.lean:94/236/269/308`) are
**deleted** by `mg-MA-Body` / Piece 5.

**Auxiliary `[Piece-4]` lemmas** (each a thin combinator at a
boundary; all mechanical):

- `chain_of_subsingleton : n ≤ 1 → IsChainPoset α`. Trivial.
- `gamma_counterexample_of_no_BP : ¬ HasBalancedPair α →
  ¬ IsChainPoset α → ∃ γ, 0 < γ ∧ γ ≤ 1/3 ∧ IsGammaCounterexample
  α γ`. **No vacuity:** `HasBalancedPair` negated over the finite
  set of incomparable pairs (non-empty since non-chain) — pick the
  minimum balance slack as `γ`. Folded into `mg-MA-Body` preamble.
- `decomp_reduction` (§4.4) — folded into `mg-MA-MinCex`.
- `ih_descent` — adapts the `Nat.strong_induction_on` IH.
- `n_zero_le_of_cascade_realised` — derives `n_zero γ T ≤ |α|` from
  `hArith` + `2 ≤ |α|` (and, if `|α| < n_zero`, the small-`n` slice
  `Step8/SmallN.lem_small_n` discharges directly). Folded into
  `mg-MA-Cascade`.
- `non_chain_subtype_of_exc` — `¬ IsChainPoset ↥(Xexcᶜ)` from
  `¬ IsChainPoset α` + `|Xexc| ≤ C_exc T` + `|α|` large. A width-3
  non-chain `α` has `≥ |α| − 3` incomparable pairs; deleting
  `O_T(1)` elements leaves one. Mechanical.
- `card_compl_ge_two` — `2 ≤ |↥(Xexcᶜ)|` from `|Xexc| ≤ C_exc T`
  and `n_zero γ T ≤ |α|`. Mechanical `omega`.
- `exc_perturb_bound_of_n_zero` (§4.7, F5) — mechanical algebra.

---

## §5. Satisfiability verification (the acceptance bar)

The ticket's acceptance bar: **satisfiability, not just
type-compatibility** — confirm each pinned signature has a *real
witness path* from the landed pieces. This is the §10/§11 discipline
of MA-Sig (the 8th-vacuity lesson) applied to the Piece-4 contract.

### §5.1. Type-compatibility on each cross-piece boundary (necessary, not sufficient)

| Boundary | Verdict |
|---|---|
| `cexImpliesLowBKExpansion` → `stepsOneToSevenCascade.hS` | `hThmE` is `∃ S, γ·vol(univ) ≤ vol S ∧ Phi S ≤ 2/(γn)` — matches `hS` byte-for-byte |
| `stepsOneToSevenCascade` → `chainLiftData_of_cascade.hCascade` | output `Step5R α γ T ∨ Step5C α T` matches the `hCascade` param; `T = hArith.T γ` threaded |
| `chainLiftData_of_cascade` → `lem_layered_from_step7` | **F2**: the widened codomain `∃ cld, K_bw≤2 ∧ PotPosetMono ∧ ExcBudget cld T` `obtain`-destructures to `⟨cld,hKbw,hMono,hBudget⟩` — exactly the bridge's four `cld`-arguments |
| `lem_layered_from_step7` → `lem_layered_balanced_full` | **F4**: bridge emits `L : LayeredDecomposition ↥(Xexcᶜ)`; Piece 6 takes `L : LayeredDecomposition β` at `β := ↥(Xexcᶜ)`; `hLw : L.w ≤ 4` is the third bridge conjunct |
| `lem_layered_balanced_full` → `not_isGammaCounterexample_of_exc_balanced_compl` | **F4**: Piece 6 emits `HasBalancedPair ↥(Xexcᶜ)`; the `_compl` lift consumes `HasBalancedPair {a // a ∈ Xexcᶜ}` — definitionally equal |
| lift → final `exact` | **F3**: lift emits `¬ IsGammaCounterexample α γ`; `hCex : IsGammaCounterexample α γ` in scope — `hNotCex hCex : False` |
| IH → `decomp_reduction` | both quantify over strict-card-smaller posets; `ih_descent` adapts |

All boundaries type-match **once F1–F5 are applied**. Under the
*stale* MA-Sig §4.2 §E/§F shapes they would **not** — that is the
content of the findings.

### §5.2. Witness path — the END of the chain is concretely exhibited

The decisive satisfiability check. The chain
**bridge (P3) → Piece 6 → S7-F-D** is **fully landed** and has a
**concrete non-vacuous witness** on the R1 grid object
(`gridChainLiftData`, the 3×3 grid):

- `grid_lem_layered_from_step7` (`LayeredFromStep7.lean:214`): the
  bridge fires on `gridChainLiftData` — both Resolution-A
  obligations hold (`grid_PotPosetMono`, `grid_excBudget`) — and
  emits a genuine `LayeredDecomposition ↥((Xexc gridChainLiftData)ᶜ)`
  on the 8-element ground set `Grid ∖ {(0,0)}`.
- That decomposition `gridLayeredFromStep7` (`:225`) is
  **non-degenerate**: `gridLayeredFromStep7_w = 3` (`:242`, a real
  `K_bw+2`, not the inert cap `4`), band map non-constant (`:251`),
  depth `K ≥ 2` (`:272`).
- **Piece 6 fires on it.** `lem_layered_balanced_full
  gridLayeredFromStep7 …` is applicable: `β := ↥((Xexc
  gridChainLiftData)ᶜ)` is an 8-element (`2 ≤`), width-3,
  non-chain poset, and `gridLayeredFromStep7.w = 3 ≤ 4`. It produces
  `HasBalancedPair ↥((Xexc gridChainLiftData)ᶜ)`.
- `excPerturbLift_of_bridge_output` (`LayeredFromStep7.lean:192`)
  **already wires P3 → S7-F-D** carrier-to-carrier, taking exactly a
  `HasBalancedPair ↥((Xexc cld)ᶜ)` and emitting
  `¬ IsGammaCounterexample`. `grid_excPerturbLift_of_bridge` (`:287`)
  runs it end-to-end: `¬ IsGammaCounterexample (Fin 3 × Fin 3)
  (2/9)`.

So the §4.8 body lines **§8–§11 compose with a real, non-vacuous
witness** — the bridge output is genuine, Piece 6 consumes it, the
lift refutes the γ-counterexample. The Piece-6 link (the one step
`grid_excPerturbLift_of_bridge` shortcuts via the direct
coordinate-swap automorphism) is satisfiable because Piece 6's four
hypotheses are all met on the grid bridge output, as itemised above.
**END-of-chain verdict: GREEN — real witness path, concretely
instantiated.**

### §5.3. Witness path — `chainLiftData_of_cascade` (F2) and the `hCex` pin

The widened §D′ codomain `∃ cld, K_bw≤2 ∧ PotPosetMono ∧ ExcBudget
cld T` is **satisfiable, non-vacuously**: `gridChainLiftData` with
`gridChainLiftData_K_bw_le_two` + `grid_PotPosetMono`
(`BridgeLayered.lean:510`) + `grid_excBudget` (`ExceptionalSet.lean:425`)
is a concrete inhabitant of all three conjuncts. So the F2-widened
constructor signature is **not** an unsatisfiable pin.

**The `hCex` hypothesis of `chainLiftData_of_cascade` is
load-bearing** — and this is the satisfiability subtlety that the
8th-vacuity lesson demands be checked. Per MA-Sig §11.3:

> The **bare** `ChainLiftData α` structure is *inhabited* for the
> 3-disjoint-chains family `Δ_ℓ` (triple = the three chains, any
> strictly-monotone potential, empty sync maps, `K_bw := 0`). Yet
> for `ℓ > 5` *every* layered decomposition of `Δ_ℓ` has width
> `≥ ℓ−1 > 4`.

So a constructor emitting `∃ cld, K_bw≤2 ∧ PotPosetMono ∧ ExcBudget`
**without** an `hCex` domain pin would be a `true → false`
proposition on `Δ_ℓ` — re-introducing the 8th-vacuity error.
**Resolution (already in the §4.5 pin):** `chainLiftData_of_cascade`
carries `hCex : IsGammaCounterexample α γ`. `Δ_ℓ` has balanced pairs
by the chain-swap automorphism (`Pr = 1/2`), so `IsGammaCounterexample
Δ_ℓ γ` is false; `Δ_ℓ` is excluded from the constructor's domain;
the conditional is vacuously true there. **And `PotPosetMono` /
`ExcBudget` themselves provably fail on `Δ_ℓ`** (a width-`ℓ` poset
admits no chain potential that is poset-monotone within `K_bw ≤ 2`),
so even the *output* conjuncts are unsatisfiable on `Δ_ℓ` — exactly
why they cannot be produced without `hCex`. The pin is sound: on the
domain `{α : IsGammaCounterexample α γ ∧ …}`, the cascade output is
the *genuine* BFS potential (`prop:71` ⇒ `PotPosetMono`) and the
genuine `lem:bandwidth` count (⇒ `ExcBudget`).

### §5.4. Witness path — `stepsOneToSevenCascade` (Piece-1/2 dependency)

`stepsOneToSevenCascade` and `chainLiftData_of_cascade` are
`[Piece-4]` body deliverables (`mg-MA-Cascade`), **not yet in
tree**. Their *signatures* are satisfiable (§5.3 exhibits a
non-degenerate witness for the harder one); their *general
discharge* for an arbitrary minimal γ-counterexample draws on:

- **Step 5 dichotomy** — in tree: `Step5.Step5Richness`
  (`Step5/Dichotomy.lean:148`), `Step5.Step5Collapse` (`:165`), and
  the dichotomy assembly in `Bridge.lean:191-200`. The α-indexed
  `Step5R`/`Step5C` wrappers (§4.5) repackage these with the
  BK-graph-of-α numeric arguments — wiring, not new math.
- **Steps 1-6 grounded cascade** — Piece 1: landed as
  `cascade_steps_1_6_grounded[_genuine]` (mg-496b,
  `Step6/CascadeComposed.lean`).
- **S7-A–E grounded forms** — Piece 2 substrate: landed
  (mg-4584/9331/1069/d135/516f).
- **R1 concrete `ChainLiftData`** — landed (`gridChainLiftData`).

**Honest scoping statement.** The two cascade producers are
satisfiable *as propositions* and have a concrete non-degenerate
witness for the `chainLiftData_of_cascade` codomain. The remaining
work — the **general** `chainLiftData_of_cascade` discharge that
turns a *minimal-γ-counterexample* cascade output into `cld + hMono
+ hBudget` for arbitrary `α` — is the cross-Piece-1/2 concretisation
(`mg-MA-Cascade` consuming the Piece-1 grounded cascade + Piece-2
S7-A–E α-side wiring). This pre-flight **pins their signatures so
`mg-MA-Cascade` builds without a downstream re-scope**; it does not
claim the general discharge is already done. No vacuity hazard:
the signatures are checked satisfiable (§5.3), and the `hCex` pin
forecloses the `Δ_ℓ` failure mode.

### §5.5. Satisfiability verdict per pinned signature

| Signature | In tree? | Satisfiable? | Witness / basis |
|---|---|---|---|
| `width3_one_third_two_thirds_assembled` (§4.1/§4.8) | no `[Piece-4]` | YES | the §4.8 body composes (§5.1 boundaries + §5.2 end-chain) |
| `HypothesisArithmetic` (§4.2) | no `[Piece-4]` | YES | a `structure`; inhabited once Piece-1 constants land |
| `Nat.strong_induction_on` shape (§4.3) | idiom | YES | the in-tree idiom; `lem_layered_balanced_full` uses it |
| `decomp_reduction` (§4.4) | no `[Piece-4]` | YES | paper `rem:decomp-reduction`; IH genuinely load-bearing |
| `cexImpliesLowBKExpansion` (§4.4) | **LANDED** | YES | sorry-free, axiom-free proof (`TheoremE.lean:171`) |
| `stepsOneToSevenCascade` (§4.5) | no `[Piece-4]` | YES (sig) | §5.4 — Step-5 dichotomy in tree; general discharge = `mg-MA-Cascade` |
| `chainLiftData_of_cascade` **widened** (§4.5, F2) | no `[Piece-4]` | YES | §5.3 — `gridChainLiftData`+`grid_PotPosetMono`+`grid_excBudget` |
| `lem_layered_from_step7` (§4.6, F1) | **LANDED** | YES | `grid_lem_layered_from_step7` non-vacuous |
| `lem_layered_balanced_full` (§4.7) | **LANDED** | YES | fires on `gridLayeredFromStep7` (§5.2) |
| `not_isGammaCounterexample_of_exc_balanced_compl` (§4.7, F3/F4) | **LANDED** | YES | `grid_excPerturbLift_of_bridge` non-vacuous |

**No row is unsatisfiable. No `true → false` pin.** The contract
passes the 8th-vacuity acceptance bar.

---

## §6. The headline axiom set after the refactor (F6)

Wiring Piece 6 into the headline changes `#print axioms
width3_one_third_two_thirds`:

- **Dropped:** `case3Witness_hasBalancedPair_outOfScope`
  (`Case3Residual.lean`) — only reachable through the *old*
  `Case3Witness_proof` direct-construction path, which Piece 4
  deletes.
- **Added:** `lem_layered_balanced_irreducible_base`
  (`LayeredBalancedFull.lean:127`, `AXIOMS.md:560`) — Piece 6's
  disclosed axiom (irreducible twin-free residual of
  `prop:in-situ-balanced`; mg-44f1 audit verdict
  **TRUE-strong-evidence**, recommends permanent accept).
- **Unchanged:** `LinearExt.brightwell_sharp_centred` (the external
  Brightwell–Tetali axiom).

Post-refactor headline axioms = `{brightwell_sharp_centred,
lem_layered_balanced_irreducible_base}` + Mathlib's
`propext`/`Classical.choice`/`Quot.sound`. This is a **net wash on
axiom count** (one project axiom swapped for another, the new one
better-audited) and is a **Piece-5 integration** item (`mg-Int-B`:
update `AXIOMS.md`). `HypothesisArithmetic` is a Lean predicate
(decision 1) — **not** an axiom; it adds a hypothesis to the
headline, not an axiom.

---

## §7. Recommendations for the Piece-4 body sub-tickets

Per the ticket (*"the body sub-tickets file on this ticket's
merge"*), the recommended sub-arc shapes (no `mg new` called here):

| Sub-ticket | Content | Pin reference | Budget |
|---|---|---|---|
| `mg-MA-MinCex` | `decomp_reduction` + `ih_descent` + `gamma_counterexample_of_no_BP` + `chain_of_subsingleton` | §4.3, §4.4, §4.8 aux | ~1 session, 200k |
| `mg-MA-ThmE` | **LANDED (mg-3638)** — `theoremE_lowConductanceWitness` wires `cexImpliesLowBKExpansion` with the §2.4 tuple; conclusion pinned to the §4.5 cascade-`hS` shape; `theoremE_lowConductanceWitness_nonempty` genuineness certificate; `Step8/TheoremEWiring.lean` (NEW) | §4.4 | ~1 session, 200k-250k |
| `mg-MA-Cascade` | `Step5R`/`Step5C` α-wrappers, `stepsOneToSevenCascade`, **F2-widened** `chainLiftData_of_cascade`, `n_zero`, `n_zero_le_of_cascade_realised` | §4.5 | ~1-2 sessions, 250k-450k |
| `mg-MA-Body` | the §4.8 body; delete `mainAssembly`/`mainTheoremInputsOf`/`caseC_canonicalLayered`/`MainTheoremInputs`; aux combinators `non_chain_subtype_of_exc`, `card_compl_ge_two`, `exc_perturb_bound_of_n_zero` | §4.1, §4.6, §4.7, §4.8 | ~1 session, 250k-300k |

**Dispatch note for `mg-MA-Cascade`.** The widened §D′ codomain (F2)
is the single most important pin in this contract — it is the one
the *landed* bridge forced. `mg-MA-Cascade` must emit `hMono` +
`hBudget`, not just `K_bw ≤ 2`. Building `chainLiftData_of_cascade`
to the MA-Sig §4.2 §D′ (stale) codomain would type-check against
nothing and fail at the `lem_layered_from_step7` call site.

**Dependency note.** `mg-MA-Cascade`'s *general discharge* depends
on Piece-1's grounded cascade + Piece-2's S7-A–E α-side wiring being
consumable (§5.4). If, at `mg-MA-Cascade` kickoff, the Piece-1/2
α-side concretisation is not consumable, that is a **hold-the-line
finding** to surface — not a defect of this contract (the signatures
are correct; the discharge is the cross-piece work).

---

## §8. Cross-reference index

### §8.1. Lean (this worktree's branch)

- `lean/OneThird/Step8/LayeredFromStep7.lean:152` —
  `lem_layered_from_step7` (Piece 3, LANDED; §2.1).
- `:192` — `excPerturbLift_of_bridge_output` (P3⟶S7-F-D boundary).
- `:214/:225/:242/:272/:287` — the grid non-vacuity certificates.
- `lean/OneThird/Step8/LayeredBalancedFull.lean:169` —
  `lem_layered_balanced_full` (Piece 6, LANDED; §2.2).
- `:127` — `lem_layered_balanced_irreducible_base` (disclosed axiom).
- `lean/OneThird/Step8/ExcBalancedLift.lean:273/310/345` —
  `not_isGammaCounterexample_of_exc_balanced[_compl]`,
  `excPerturbLift` (S7-F-D, LANDED; §2.3).
- `lean/OneThird/Step8/TheoremE.lean:171` —
  `cexImpliesLowBKExpansion` (LANDED; §2.4).
- `lean/OneThird/Step8/TheoremEWiring.lean` —
  `theoremE_lowConductanceWitness` + `_nonempty` + `volume_univ_pos`
  (the `mg-MA-ThmE` deliverable, mg-3638; §4.4).
- `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`.
- `lean/OneThird/Step8/BridgeLayered.lean:162` —
  `ChainLiftData.PotPosetMono`; `:510` `grid_PotPosetMono`.
- `lean/OneThird/Step8/ExceptionalSet.lean:336/343/357/425` —
  `C_exc`, `ExcBudget`, `Xexc_card_le`, `grid_excBudget`.
- `lean/OneThird/Step8/LayeredBalanced.lean:375` —
  `hasWidthAtMost_subtype`.
- `lean/OneThird/Step5/Dichotomy.lean:148/165` —
  `Step5Richness`, `Step5Collapse`.
- `lean/OneThird/Step8/MainAssembly.lean:236/265/269/308/353` —
  the refactor target (deleted/rewritten by Piece 4).
- `lean/OneThird/MainTheorem.lean:56` — the headline wrapper.
- `lean/OneThird/LinearExtension.lean:38/50` — `HasBalancedPair`,
  `IsGammaCounterexample`.
- `lean/OneThird/Mathlib/Poset/Indecomposable.lean:60` —
  `Indecomposable`.
- `lean/AXIOMS.md:560` — `lem_layered_balanced_irreducible_base`.

### §8.2. Paper (`step8.tex`)

- `step8.tex:9-23` — Hypothesis A (`hyp:arith`).
- `step8.tex:32-91` — `thm:main-step8` + restatement remark.
- `step8.tex:106-260` — `thm:main-step8` proof (the §4.8 template).
- `step8.tex:274` — `rem:decomp-reduction` (`decomp_reduction`).
- `step8.tex:2009-2089` — `lem:layered-from-step7` (Piece 3).
- `step8.tex:2453-2464` / `:3211-3266` — `lem:layered-balanced`
  (Piece 6).

### §8.3. Predecessor docs / work items

- `docs/state-MA-Sig-Session1.md` (mg-a22b/mg-faf8/mg-3119) — the
  Phase-1 contract; §4.2 §E/§F/§G **superseded** by §4 here for the
  landed-signature rows.
- `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) §2.4 —
  the Piece-4 spec.
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — §0 mg-02cd /
  mg-65de / mg-876f bullets; §3 pitfalls #5/#6/#9/#10.
- `docs/state-S7F-Z-Session1.md` (mg-02cd) — Piece 3 finalisation;
  the QA finding that `hCex` is not a bridge-body input.
- `docs/state-S7F-D-Session1.md` (mg-876f) — the S7-F-D
  block-report (MA-Sig §4.2 §F ill-posed).
- `docs/state-Piece6-Redo-Session1.md` (mg-65de) — Piece 6.
- Work items: mg-d8c7, mg-a22b, mg-faf8, mg-3119, mg-974c,
  mg-02cd, mg-876f, mg-65de, mg-44f1, mg-5fbd, mg-0bd1, mg-ca83.

---

## §9. Maintenance contract

This file is the **Piece-4 signature contract**. The Piece-4 body
sub-tickets (`mg-MA-MinCex`, `mg-MA-ThmE`, `mg-MA-Cascade`,
`mg-MA-Body`) reference §4 by sub-number.

Update this file in the **same commit** as any of the following:

- A Piece-4 body sub-ticket lands and its actual signature drifts
  from §4 — reflect the drift here.
- A landed Piece-3/6/S7-F-D signature changes (e.g. a follow-on
  re-pin of `lem_layered_from_step7`) — re-audit §2 and §4.
- A further vacuity-discovery surfaces during Piece-4 execution —
  record here with a re-scoped recommendation.

**Default-skeptical posture.** Per Daniel's vacuity-discovery
pattern (10 discoveries to date), the acceptance bar is
**satisfiability**, not type-compatibility. Every `∃`-with-caps
signature pinned in §4 was checked against the *actual landed Lean*
(§2) and exhibited a real witness path (§5). The MA-Sig §4.2
pseudo-Lean is **not** the contract for the §E/§F/§G rows — the
landed code is, and §4 here re-pins to it. A Piece-4 body
sub-ticket that finds §4 type-checks but is unsatisfiable should
**stop and re-scope**, not push through.

---

## §10. Body sub-ticket landings

Per §9, each Piece-4 body sub-ticket records its landing and any
signature drift here.

### §10.1. `mg-MA-MinCex` — minimal-counterexample machinery (LANDED)

`mg-7969` (OneThird-MA-MinCex, re-scoped) landed
`lean/OneThird/Step8/MinCounterexample.lean` —
`chain_of_subsingleton`, `gamma_counterexample_of_no_BP`,
`decomp_reduction`, `ih_descent`, and the packaged
`Nat.strong_induction_on` minimal-counterexample induction
`hasBalancedPair_of_strongInduction` (§4.3).  Sorry-free; axioms
`[propext, Classical.choice, Quot.sound]` only.  State doc:
`docs/state-MA-MinCex-Session1.md`.

**`WithEdge` design resolution.** §4.8 aux `gamma_counterexample_of_no_BP`
needs `probLT x y > 0` for incomparable pairs (else `γ > 0` is
unprovable and the lemma is vacuous).  The first session ground in an
edit-build-fail loop trying to give a new `WithEdge x y` type a
`PartialOrder` instance.  The landed file uses the in-tree
order-refinement pattern `OneThird.RelationPoset` + `addRel` instead —
a data-level poset, no instance to synthesize.  No `WithEdge` type
exists.

**Drift from §4.4 — `decomp_reduction` hypothesis (finding F-MinCex-1).**
§4.4 pins `decomp_reduction` with `hCex : IsGammaCounterexample α γ`.
The landed signature instead takes `hNoBP : ¬ HasBalancedPair α`
directly:

```lean
theorem decomp_reduction
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hNoBP : ¬ HasBalancedPair α)
    (ih : ∀ m, m < Fintype.card α → ∀ {β : Type u} [PartialOrder β]
            [Fintype β] [DecidableEq β], Fintype.card β = m →
            HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β) :
    Indecomposable α
```

`decomp_reduction` uses only "α has no balanced pair"; deriving that
from `IsGammaCounterexample α γ` additionally needs `0 ≤ γ` (an
incomparable balanced pair has `min(probLT) ≥ 1/3`, contradicting
`min < 1/3 − γ` only when `γ ≥ 0`).  **Call-site impact: none** — the
§4.8 body opens with `by_contra hNoBP`, so `hNoBP` is in scope; §4.8
line §4 becomes `decomp_reduction hP hNonChain hNoBP (ih_descent hcard ih)`.
This is the predictable Phase-1/Phase-2 drift, not a satisfiability
defect.

### §10.2. `mg-MA-Cascade` — the Steps 1-7 cascade wiring (LANDED)

`mg-52e0` (OneThird-MA-Cascade) landed
`lean/OneThird/Step8/Cascade.lean` — `HypothesisArithmetic`,
`n_zero` (+ correctness lemma `n_zero_ceil_ge`), `Step5R` / `Step5C`,
`not_hasBalancedPair_of_isGammaCounterexample`,
`stepsOneToSevenCascade`, `chainLiftData_of_cascade`, and the
non-vacuity certificates `GridChainLift.grid_Step5C` /
`grid_Step5C_fires_bridge`.  `lake build OneThird` succeeds.
`#print axioms`: `chainLiftData_of_cascade` and the four supporting
lemmas are **axiom-free** (`propext` / `Classical.choice` /
`Quot.sound` only); `stepsOneToSevenCascade` carries the one new
project axiom (see F-Cascade-1).  State doc:
`docs/state-MA-Cascade-Session1.md`.  Findings F-Cascade-1..4:

**F-Cascade-1 — `stepsOneToSevenCascade` landed as a named project
axiom, not a theorem.**  §4.5 wrote `theorem stepsOneToSevenCascade`.
The genuine content — BK-expansion ⇒ Step-5 dichotomy ⇒ Steps 6-7
chain-potential cascade — is a multi-month Lean port that is not in
tree (Step 7 is the rich-pair packaging `Step7.LayeredWidth3`, which
`mg-ca83` Checkpoint 3 found carries no poset-structural content;
there is no consumable α-side `ChainLiftData`-valued cascade).  This
is exactly the hold-the-line situation §7's Dependency note
anticipates.  The honest representation is a named, paper-faithful,
`AXIOMS.md`-certified project axiom (`step8.tex` thm:main-step8
Steps 1-7 + `step7.tex:1173` `prop:72`).  Consistent with the
sanctioned posture (mg-ac13 Option C, mg-6ab8; onboarding §1 step 1).

**F-Cascade-2 — §6's axiom accounting was incomplete.**  §6 stated the
post-refactor headline axiom set is a "net wash"
(`brightwell_sharp_centred` + `lem_layered_balanced_irreducible_base`).
It omitted the Steps-1-7 gap.  The accurate picture: the current
`MainAssembly.lean` cap-5 **`sorry`** *is* the Steps-1-7 `w₀(γ) ≤ 4`
delivery gap (onboarding §0, pitfall #3/#5).  Piece 4 converts that
`sorry` into the named axiom `stepsOneToSevenCascade` — a
`sorry → documented axiom` upgrade.  **Corrected §6:** post-refactor
the headline is sorry-free with axioms
`{brightwell_sharp_centred, lem_layered_balanced_irreducible_base,
stepsOneToSevenCascade}` + Mathlib's.

**F-Cascade-3 — `Step5R` / `Step5C` are not wrappers around the
in-tree numeric predicates.**  §4.5 described them as wrappers around
`Step5.Step5Richness` / `Step5.Step5Collapse`.  Those in-tree
predicates are structurally weak — `Step5Collapse p q` is provably
`True` (`fAC := 0, fBC := 0, K := 0`), `Step5Richness` likewise when
the numerics are free — so a literal wrapper would be **vacuous**,
violating the non-triviality bar.  The landed `Step5C` is the
F2-widened bridge-ready `ChainLiftData` existence (Step-7 collapse
output); `Step5R := HasBalancedPair α` (the richness route's net
conclusion via Step 6 `cor:pointwise`).  The §4.5 signatures (name,
`α`/`γ`/`T` arity, `: Prop`) are honoured; only the elided `…` bodies
differ from the §4.5 prose description.

**F-Cascade-4 — `chainLiftData_of_cascade`'s `hP`/`hI` are inert.**
Given the F2-widened `Step5C` (which carries the full codomain),
`chainLiftData_of_cascade` is a genuine but thin extraction:
`hγ_pos`, `hCex`, `hCascade` are load-bearing (`hCex` *excludes the
`Step5R` branch*, per §5.3); `hP`/`hI` are inert and kept only for
§4.5 signature conformance.  Also: `Step5C` /
`chainLiftData_of_cascade` / `stepsOneToSevenCascade` carry
`[DecidableLE α]` (needed transitively by `ExcBudget`), which §4.5
omitted — the same instance the F7 finding flags; the §4.8 headline
body's opening `classical` supplies it, so no public-API change.

All four are predictable Phase-1/Phase-2 drift, not satisfiability
defects: `chainLiftData_of_cascade`'s codomain is satisfiable against
the landed bridge (`grid_Step5C_fires_bridge`), and `stepsOneToSeven
Cascade`'s `Step5C` disjunct is the same non-vacuous codomain.

### §10.3. `mg-MA-Body` — the proof-by-contradiction body (LANDED)

`mg-9add` (OneThird-MA-Body) rewrote
`lean/OneThird/Step8/MainAssembly.lean`:
`width3_one_third_two_thirds_assembled` is now the §4.8
proof-by-contradiction (sorry-free); `MainTheoremInputs`,
`caseC_canonicalLayered`, `mainTheoremInputsOf`, `mainAssembly` are
**deleted**; `MainTheorem.width3_one_third_two_thirds` gains `hArith`.
The headline instantiates non-vacuously at `Antichain3`
(`antichain3_width3_one_third_two_thirds_assembled`). `lake build
OneThird` succeeds. **Piece 4 is complete.** State doc:
`docs/state-MA-Body-Session1.md`. Findings F-Body-1, F-Body-2:

**F-Body-1 — `n_zero_le_of_cascade_realised` is ill-posed.** §4.8
pins `hn0 := n_zero_le_of_cascade_realised hArith hcard hγ_pos
hγ_third : n_zero γ (hArith.T γ) ≤ |α|`. No such theorem exists — it
is *false* for every minimal counterexample with `|α| < n_zero γ T`
(a non-empty reachable regime: `n_zero ≥ C_exc T ≥ 6`). `mg-52e0`
correctly did not land it. The honest body uses a `by_cases`
dichotomy on `n_zero γ (hArith.T γ) ≤ |β|`; the small-`|β|` leaf is
the paper `lem:small-n` base case. The in-tree `Step8.lem_small_n`
(`SmallN.lean`) is **not** a discharge (it packages Kahn–Linial +
enumeration as hypotheses). The honest discharge is the new disclosed
project axiom `width3_smallN_hasBalancedPair` (Kahn–Linial is
external; the enumeration is unformalised) — `AXIOMS.md`-certified.

**F-Body-2 — `non_chain_subtype_of_exc` is not mechanical.** §4.8
aux lists it as a "mechanical" combinator (`¬ IsChainPoset ↥(Xexcᶜ)`
from `¬ IsChainPoset α` + size bounds), justified by "`≥ |α| − 3`
incomparable pairs survive deletion." That justification is **false**
(a width-3 non-chain poset can concentrate all incomparability on an
`O_T(1)` vertex cover). The fact is true only via `hNoBP` (a floater
incomparable to a long sub-chain forms a balanced pair) — Step-8
combinatorics, not a combinator. It is the new disclosed project
axiom `nonChain_compl_of_no_balancedPair` — `AXIOMS.md`-certified.

**F-Body-3 — §6's axiom accounting is `+2`, not the projected wash.**
§6 (corrected by F-Cascade-2 to `{brightwell_sharp_centred,
lem_layered_balanced_irreducible_base, stepsOneToSevenCascade}`) omits
the two base-case leaves the §4.8 body had assumed mechanical. The
accurate post-refactor headline axiom set is that set **plus**
`width3_smallN_hasBalancedPair` and `nonChain_compl_of_no_balancedPair`
(both sorry-free, paper-faithful, `AXIOMS.md`-certified). The
`case3Witness_hasBalancedPair_outOfScope` axiom and the
`caseC_canonicalLayered` structured `sorry` both drop off the
headline (the deleted `Case3Witness_proof` direct path).

Findings F3/F4/F5/F7 and F-MinCex-1 were honoured exactly — no drift.
