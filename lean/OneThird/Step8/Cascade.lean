/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredFromStep7
import OneThird.Step8.TheoremEWiring
import OneThird.Mathlib.Poset.Indecomposable
import Mathlib.Data.Rat.Floor

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Piece 4 (MainAssembly refactor) — the Steps 1-7 cascade wiring

This file is the **`mg-MA-Cascade`** deliverable of FULL REFACTOR
Phase 2, Piece 4 (the `MainAssembly` proof-by-contradiction refactor).
It builds the Steps-1-7 cascade wiring of the pinned Piece-4 signature
contract `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.5.

## What this delivers

* `HypothesisArithmetic` — the paper's *Hypothesis A* (`hyp:arith`,
  `step8.tex:9-23`), an in-Lean predicate (contract §4.2, decision 1),
  threaded into the headline as an explicit hypothesis — **not** an
  axiom.
* `n_zero : ℚ → ℕ → ℕ` — the realisability threshold of contract §4.5,
  pinned so the `mg-MA-Body` §4.7 perturbation side condition is
  dischargeable (`n_zero_ceil_ge`).
* `Step5R` / `Step5C` — the two α-indexed cascade outcomes (contract
  §4.5). See finding **F-Cascade-3** below for the design drift from
  the §4.5 "wrapper around `Step5.Step5Richness`/`Step5.Step5Collapse`"
  description.
* `stepsOneToSevenCascade` — the Steps-1-7 cascade producing
  `Step5R ∨ Step5C`, consuming the low-conductance witness `hS`. See
  finding **F-Cascade-1**: this is delivered as a **named project
  axiom**.
* `chainLiftData_of_cascade` — the **F2-widened** `ChainLiftData`
  constructor (contract §4.5, finding F2), a genuine sorry-free /
  axiom-free theorem.

## Finding F2 — the F2-widened codomain (the load-bearing pin)

Contract §4.5 finding F2 is the single most important pin: the landed
S7-F bridge `lem_layered_from_step7` (`LayeredFromStep7.lean:152`)
consumes **three** facts about its `ChainLiftData` — `hKbw`, `hMono`
(`PotPosetMono`), `hBudget` (`ExcBudget`). The stale MA-Sig Phase-1
§D′ pin emitted only `K_bw ≤ 2`, which is unsatisfiable against the
landed bridge. Accordingly the codomain of `chainLiftData_of_cascade`
— and of `Step5C` — emits **all three conjuncts**:

```
∃ cld : ChainLiftData α, cld.K_bw ≤ 2 ∧ cld.PotPosetMono ∧ ExcBudget cld T
```

`grid_Step5C` + `grid_Step5C_fires_bridge` (§7 below) verify this
codomain is **satisfiable against the landed bridge**: the R1 witness
`gridChainLiftData` inhabits all three conjuncts, and the resulting
`Step5C` witness fires `lem_layered_from_step7` to a genuine
three-cap output. This discharges the non-triviality bar (the
8th-vacuity lesson): the cascade output is not a `true → false` pin.

## Findings — drift from the mg-92a8 contract (recorded per its §9)

* **F-Cascade-1 — `stepsOneToSevenCascade` is a named project axiom,
  not a theorem.** Contract §4.5 wrote `theorem stepsOneToSevenCascade`.
  The genuine mathematical content of Steps 1-7 — the BK-expansion ⇒
  Step-5 dichotomy ⇒ Steps 6-7 chain-potential cascade — is a
  multi-month Lean port that is *not in tree* (Step 7 is still the
  rich-pair packaging `Step7.LayeredWidth3`, which mg-ca83 Checkpoint 3
  found carries no poset-structural content; there is no consumable
  α-side cascade). This is exactly the "hold-the-line finding" the
  contract §7 Dependency note anticipates: *"the signatures are
  correct; the discharge is the cross-piece work."* The honest,
  auditable representation of that un-ported discharge is a **named
  project axiom**, faithful to a specific paper statement
  (`step8.tex` thm:main-step8 Steps 1-7 + `step7.tex:1173` `prop:72`)
  and certified in `AXIOMS.md`. This is the project's sanctioned
  posture for Steps 1-7 (mg-ac13 Option C, mg-6ab8; the onboarding §1
  step 1 records Steps 1-7 as "paper-axiomatised").

* **F-Cascade-2 — the contract §6 axiom accounting is incomplete.**
  §6 states the post-refactor headline axiom set is a "net wash"
  (`brightwell_sharp_centred` + `lem_layered_balanced_irreducible_base`).
  It omits the Steps-1-7 gap. The accurate post-refactor picture:
  the current `MainAssembly.lean` cap-5 **`sorry`** *is* the Steps-1-7
  `w₀(γ) ≤ 4` delivery gap (onboarding §0, pitfall #3/#5). Piece 4
  converts that `sorry` into the named, paper-faithful, `AXIOMS.md`-
  certified axiom `stepsOneToSevenCascade` — a `sorry → documented
  axiom` upgrade, strictly more auditable. Post-refactor: the headline
  is **sorry-free**, with axioms
  `{brightwell_sharp_centred, lem_layered_balanced_irreducible_base,
  stepsOneToSevenCascade}`.

* **F-Cascade-3 — `Step5R`/`Step5C` are not wrappers around the
  in-tree numeric predicates.** Contract §4.5 describes `Step5R`/
  `Step5C` as "α-indexed wrappers around `Step5.Step5Richness`
  (`Dichotomy.lean:148`) / `Step5.Step5Collapse` (`Dichotomy.lean:165`)".
  Those in-tree predicates are *structurally weak*: `Step5Collapse p q`
  is provably `True` for every `p, q` (`fAC := 0, fBC := 0, K := 0`
  gives `|0| ≤ 1`), and `Step5Richness LP f c` is `True` whenever the
  caller may pick the numerics. A literal wrapper around them would be
  **vacuous** — violating the non-triviality bar. To carry genuine
  content, `Step5C` is defined as the F2-widened bridge-ready
  `ChainLiftData` existence (the Step-7 layered-collapse output), and
  `Step5R` as the richness route's net conclusion `HasBalancedPair α`
  (paper Step 5 (R) composed with Step 6 `cor:pointwise` yields a
  balanced pair).

* **F-Cascade-4 — `chainLiftData_of_cascade`'s `hP`/`hI` are inert.**
  Given the F2-widened `Step5C` (which already carries the full
  codomain), `chainLiftData_of_cascade` is a genuine but thin
  extraction: `hγ_pos`, `hCex`, `hCascade` are load-bearing
  (`hCex` *excludes the `Step5R` branch* — see contract §5.3, the
  `Δ_ℓ`-exclusion role), while `hP`/`hI` are inert. They are kept in
  the signature for conformance with the contract §4.5 pin.

## Cross-references

* `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.2, §4.5, §5.3, §6,
  §9 — the pinned contract.
* `OneThird.Step8.lem_layered_from_step7` — the landed S7-F bridge
  (`LayeredFromStep7.lean:152`); the consumer of `chainLiftData_of_cascade`.
* `OneThird.Step8.theoremE_lowConductanceWitness` — Theorem E wiring
  (`TheoremEWiring.lean`, mg-3638); produces the `hS` low-conductance
  witness.
* `OneThird.Step8.GridChainLift.gridChainLiftData` — the R1 concrete
  witness (`ConcreteChainLiftData.lean`, mg-974c).
* `AXIOMS.md` — the `stepsOneToSevenCascade` certification entry.
* `step8.tex:9-23` Hypothesis A; `step8.tex:106-260` thm:main-step8;
  `step7.tex:1173` `prop:72`.
-/

namespace OneThird
namespace Step8

open OneThird OneThird.Mathlib.Poset

universe u

variable {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
  [DecidableLE α]

/-! ## §1 — `HypothesisArithmetic` (paper Hypothesis A `hyp:arith`)

The paper's `thm:main-step8` is stated *"Assume Hypothesis hyp:arith"*
(`step8.tex:9-23`). Per contract §4.2 / decision 1 it is threaded as an
in-Lean predicate — **not** a project axiom — so the refactored
headline gains a hypothesis, not an axiom.

The constants `c5`, `c6`, `delta0`, `T_zero` are Steps-5/6 grounded
arithmetic constants (Piece-1 deliverables). Their genuine bodies are
out of scope for Piece 4 (contract §4.2: *"only the threading is"*);
they are modelled here as `opaque` definitions — the same device the
landed S7-F-A uses for the Step-5 constant `c₁` (`ExceptionalSet.lean`).
`opaque` is **not** an axiom: it does not appear in `#print axioms`. -/

/-- The Step-5 arithmetic constant `c₅(T, γ)` of `step5.tex`. Opaque
Piece-1 cascade constant. -/
opaque c5 : ℕ → ℚ

/-- The Step-6 arithmetic constant `c₆` of `step6.tex`. Opaque
Piece-1 cascade constant. -/
opaque c6 : ℚ

/-- The arithmetic-richness slack `δ₀(γ)` of `step8.tex` Hypothesis A.
Opaque Piece-1 cascade constant. -/
opaque delta0 : ℚ → ℚ

/-- The base window size `T₀` of `step8.tex` Hypothesis A. Opaque
Piece-1 cascade constant. -/
opaque T_zero : ℕ

/-- **Hypothesis A — `hyp:arith`** (`step8.tex:9-23`, contract §4.2).

The in-Lean predicate carrying the paper's arithmetic-richness
hypothesis: a window-size selector `T : ℚ → ℕ` together with the two
hypotheses the paper assumes — `T γ` exceeds the base window `T₀`, and
the arithmetic-richness inequality `8 ≤ γ² · c₅(T γ) · c₆ · δ₀(γ)`
holds across the counterexample range `γ ∈ (0, 1/3)`. -/
structure HypothesisArithmetic where
  /-- Window-size selector `T(γ)`. -/
  T : ℚ → ℕ
  /-- `T(γ)` exceeds the base window size `T₀`. -/
  T_ge_T0 : ∀ γ : ℚ, 0 < γ → γ < 1 / 3 → T_zero ≤ T γ
  /-- The arithmetic-richness inequality of Hypothesis A. -/
  arith_holds : ∀ γ : ℚ, 0 < γ → γ < 1 / 3 →
    (8 : ℚ) ≤ γ ^ 2 * c5 (T γ) * c6 * delta0 γ

/-! ## §2 — `n_zero`, the realisability threshold

`n_zero γ T` is the cardinality threshold above which a minimal
γ-counterexample is large enough for the `mg-MA-Body` §4.7 perturbation
side condition `2·|Xexc| / (|α| − |Xexc| + 1) ≤ γ` to hold (with
`|Xexc| ≤ C_exc T`). Contract §4.5 pins it as
`⌈4·C_exc T / γ⌉ + C_exc T`. -/

/-- **The realisability threshold** `n_zero γ T` (contract §4.5):
`⌈4·C_exc T / γ⌉ + C_exc T`. Above this cardinality the perturbation
side condition of the `mg-MA-Body` §4.7 lift is dischargeable. -/
def n_zero (γ : ℚ) (T : ℕ) : ℕ :=
  (Int.ceil ((4 * (C_exc T : ℚ)) / γ)).toNat + C_exc T

/-- **Correctness of `n_zero`** — the key arithmetic property: for
`γ > 0`, the gap `n_zero γ T − C_exc T` clears `4·C_exc T / γ`. The
`mg-MA-Body` `exc_perturb_bound_of_n_zero` (contract §4.7, finding F5)
derives the `2·|Xexc| / (|α| − |Xexc| + 1) ≤ γ` side condition from
this together with `|Xexc| ≤ C_exc T`. -/
theorem n_zero_ceil_ge (γ : ℚ) (T : ℕ) (hγ : 0 < γ) :
    (4 * (C_exc T : ℚ)) / γ ≤ (n_zero γ T : ℚ) - (C_exc T : ℚ) := by
  have hxnn : (0 : ℚ) ≤ (4 * (C_exc T : ℚ)) / γ :=
    div_nonneg (by positivity) (le_of_lt hγ)
  have hcnn : (0 : ℤ) ≤ Int.ceil ((4 * (C_exc T : ℚ)) / γ) :=
    Int.ceil_nonneg hxnn
  have heq : (n_zero γ T : ℚ) - (C_exc T : ℚ)
      = ((Int.ceil ((4 * (C_exc T : ℚ)) / γ)).toNat : ℚ) := by
    simp only [n_zero, Nat.cast_add]
    ring
  have hcast : ((Int.ceil ((4 * (C_exc T : ℚ)) / γ)).toNat : ℚ)
      = ((Int.ceil ((4 * (C_exc T : ℚ)) / γ) : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hcnn
  rw [heq, hcast]
  exact Int.le_ceil _

/-! ## §3 — `Step5R` / `Step5C`, the two cascade outcomes

The two α-indexed outcomes of the Steps-1-7 cascade (contract §4.5).
See finding **F-Cascade-3** in the module header for why these carry
genuine content rather than wrapping the structurally-weak in-tree
`Step5.Step5Richness` / `Step5.Step5Collapse`. -/

/-- **The richness outcome `(R)`** of the Steps-1-7 cascade (contract
§4.5).

Paper Step 5 (R) — "many rich pairs" (`step5.tex:84-91`) — composed
with Step 6 `cor:pointwise` produces a balanced pair. `Step5R` encodes
that net conclusion: `HasBalancedPair α`. In the proof-by-contradiction
body this branch is **excluded** by `hCex` (a γ-counterexample has no
balanced pair) — exactly the `hCex`-is-load-bearing design of contract
§5.3. The `γ`, `T` arguments are retained for arity-conformance with
the §4.5 pin. -/
def Step5R (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    [DecidableLE α] (γ : ℚ) (T : ℕ) : Prop :=
  HasBalancedPair α

/-- **The collapse outcome `(C)`** of the Steps-1-7 cascade (contract
§4.5), in the **F2-widened** form (finding F2).

Paper Step 5 (C) — the layered collapse (`step5.tex:95-102`), refined
through Steps 6-7 (`prop:71`, `lem:bandwidth`, `prop:72`) — delivers a
bridge-ready `ChainLiftData`: a Dilworth chain triple + chain potential
+ sync maps with bandwidth `K_bw ≤ 2`, whose potential is strictly
poset-monotone (`PotPosetMono`, paper `prop:71`) and whose exceptional
budget is `O_T(1)` (`ExcBudget`, paper `lem:bandwidth` + per-chain
orphan bounds).

This is **exactly** the input the landed S7-F bridge
`lem_layered_from_step7` consumes; emitting all three conjuncts is the
F2 widening. -/
def Step5C (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    [DecidableLE α] (T : ℕ) : Prop :=
  ∃ cld : ChainLiftData α,
    cld.K_bw ≤ 2 ∧ cld.PotPosetMono ∧ ExcBudget cld T

/-! ## §4 — A γ-counterexample has no balanced pair

The lever that makes `hCex` load-bearing in `chainLiftData_of_cascade`:
the richness branch `Step5R = HasBalancedPair α` is incompatible with
`IsGammaCounterexample α γ`. -/

omit [DecidableLE α] in
/-- **A γ-counterexample has no balanced pair.** For `γ > 0`, an
incomparable pair with `1/3 ≤ Pr[x < y] ≤ 2/3` has
`min(Pr[x<y], Pr[y<x]) ≥ 1/3`, contradicting the γ-counterexample
bound `min < 1/3 − γ`. -/
theorem not_hasBalancedPair_of_isGammaCounterexample {γ : ℚ} (hγ : 0 < γ)
    (hCex : IsGammaCounterexample α γ) : ¬ HasBalancedPair α := by
  rintro ⟨x, y, hxy, hb1, hb2⟩
  have hne : x ≠ y := fun h => hxy.1 (h ▸ le_refl x)
  have hsum : probLT x y + probLT y x = 1 := probLT_add_probLT_of_ne hne
  obtain ⟨hge, hlt⟩ := hCex x y hxy
  have hyx : (1 : ℚ) / 3 ≤ probLT y x := by linarith
  have hmin : (1 : ℚ) / 3 ≤ min (probLT x y) (probLT y x) := le_min hb1 hyx
  linarith

/-! ## §5 — `stepsOneToSevenCascade` (the Steps-1-7 cascade — AXIOM)

See finding **F-Cascade-1** in the module header. The genuine
mathematical content — BK-expansion ⇒ Step-5 dichotomy ⇒ Steps 6-7
chain-potential cascade — is the multi-month Lean port that is not in
tree. It is delivered here as a named project axiom, faithful to
`step8.tex` thm:main-step8 (Steps 1-7) and `step7.tex:1173` `prop:72`,
and certified in `AXIOMS.md`. Every hypothesis is load-bearing: the
axiom is invokable only with a genuine minimal γ-counterexample
(`hP`, `hI`, `hCex`, `h2`), the arithmetic hypothesis (`hArith`), the
realisability threshold (`hn0`), and the low-conductance witness
(`hS`) produced by `theoremE_lowConductanceWitness`. -/

/-- **The Steps-1-7 cascade** (contract §4.5, paper `step8.tex`
thm:main-step8 Steps 1-7 + `step7.tex:1173` `prop:72`) — **a named
project axiom** (finding F-Cascade-1).

Given a width-3 indecomposable minimal γ-counterexample on `n ≥ 2`
elements satisfying Hypothesis A, realised above the threshold
`n_zero`, together with the Theorem E low-conductance witness `hS`,
the Steps-1-7 cascade produces the Step-5 dichotomy: either the
richness outcome `Step5R` (which a γ-counterexample then refutes) or
the bridge-ready collapse outcome `Step5C`.

The output `Step5R ∨ Step5C` is consumed by `chainLiftData_of_cascade`
(§6). The companion `grid_Step5C` (§7) certifies the `Step5C`
disjunct is satisfiable against the landed bridge — the cascade output
is not a `true → false` pin. -/
axiom stepsOneToSevenCascade
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1 / 3)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α)
    (hArith : HypothesisArithmetic)
    (hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card α)
    (hS : ∃ S : Finset (LinearExt α),
            γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
                ≤ (volume S : ℚ) ∧
            Phi S ≤ 2 / (γ * (Fintype.card α : ℚ))) :
    Step5R α γ (hArith.T γ) ∨ Step5C α (hArith.T γ)

/-! ## §6 — `chainLiftData_of_cascade` (the F2-widened constructor)

A genuine sorry-free, axiom-free theorem. The `Step5R` branch is
closed by `hCex` (no balanced pair); the `Step5C` branch is the
F2-widened extraction. -/

/-- **`chainLiftData_of_cascade`** — the F2-widened `ChainLiftData`
constructor (contract §4.5, finding F2).

From the Step-5 dichotomy `Step5R ∨ Step5C` of a γ-counterexample,
produce a bridge-ready `ChainLiftData` emitting **all three** conjuncts
the landed bridge `lem_layered_from_step7` consumes: `K_bw ≤ 2`,
`PotPosetMono`, and `ExcBudget cld T`.

`hCex` is load-bearing (contract §5.3): the richness branch
`Step5R = HasBalancedPair α` is refuted by `not_hasBalancedPair_of_
isGammaCounterexample`, so a γ-counterexample is forced into the
collapse branch. `hP`/`hI` are inert here (finding F-Cascade-4) — the
F2-widened `Step5C` already carries the full codomain — and are kept
for §4.5 signature conformance. -/
theorem chainLiftData_of_cascade
    (γ : ℚ) (hγ_pos : 0 < γ) (T : ℕ)
    (hP : HasWidthAtMost α 3)
    (hI : Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (hCascade : Step5R α γ T ∨ Step5C α T) :
    ∃ cld : ChainLiftData α,
      cld.K_bw ≤ 2 ∧ cld.PotPosetMono ∧ ExcBudget cld T := by
  rcases hCascade with hR | hC
  · -- Richness branch: `Step5R = HasBalancedPair α`, excluded by `hCex`.
    exact absurd hR (not_hasBalancedPair_of_isGammaCounterexample hγ_pos hCex)
  · -- Collapse branch: `Step5C` is, by definition, the F2-widened codomain.
    exact hC

/-! ## §7 — Non-vacuity: the codomain is satisfiable against the bridge

The non-triviality bar (the 8th-vacuity lesson, contract §5.3): the
cascade output must be **satisfiable against the landed bridge**, not
a `true → false` pin. The R1 witness `gridChainLiftData`
(`ConcreteChainLiftData.lean`) inhabits the F2-widened `Step5C`
codomain on a genuine width-3 non-chain carrier, and the resulting
`Step5C` witness fires `lem_layered_from_step7`. -/

namespace GridChainLift

/-- **`Step5C` is satisfiable** — the F2-widened collapse codomain is
inhabited, non-degenerately, by the R1 witness `gridChainLiftData` on
the genuine width-3 non-chain 3×3 grid. All three conjuncts hold:
`K_bw = 1 ≤ 2` (`gridChainLiftData_K_bw_le_two`), `PotPosetMono`
(`grid_PotPosetMono`), and `ExcBudget` for every `T` (`grid_excBudget`).
For the degenerate `Δ_ℓ` family `PotPosetMono` and `ExcBudget`
provably fail (contract §5.3) — so this is a genuine soundness filter,
not a disguised `True`. -/
theorem grid_Step5C (T : ℕ) : Step5C (Fin 3 × Fin 3) T :=
  ⟨gridChainLiftData, gridChainLiftData_K_bw_le_two, grid_PotPosetMono,
    grid_excBudget T⟩

/-- **The cascade output fires the landed bridge.** A `Step5C` witness
— the F2-widened codomain of `chainLiftData_of_cascade` — feeds
`lem_layered_from_step7` directly to a genuine three-cap output
(`|Xexc| ≤ C_exc T`, bands non-empty, `L.w ≤ 4`). This is the
acceptance certificate of the non-triviality bar: the cascade output
is satisfiable against the landed S7-F bridge. -/
theorem grid_Step5C_fires_bridge (T : ℕ) :
    ∃ (Xexc : Finset (Fin 3 × Fin 3))
      (L : LayeredDecomposition ↥(Xexcᶜ)),
      Xexc.card ≤ C_exc T ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4 := by
  obtain ⟨cld, hKbw, hMono, hBudget⟩ := grid_Step5C T
  exact lem_layered_from_step7 T cld hKbw hMono hBudget

end GridChainLift

end Step8
end OneThird
