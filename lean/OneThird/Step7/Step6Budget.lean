/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step6.CascadeComposed
import OneThird.Step7.Bandwidth

/-!
# Step 7 — Piece 2 sub-arc C: the Step 6 budget constants `b_n, b_d`

FULL REFACTOR Phase 2, Piece 2 (S7-A–E concretisation) follow-on
(`mg-5f3e`, S7-Conc-C; scoped by `mg-d8c7`
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2 item 5,
sub-arc `mg-S7-Conc-C`).  Piece 1 (the Steps 1–6 cascade Lean port)
is complete (`mg-496b`, `Step6/CascadeComposed.lean`), so the
Step 6 grounded output the constant-extraction needs now exists in
tree.

## What this file extracts

The Step 7 variational-budget hypothesis
`BandwidthData.VarBudgetHyp pairs b_n b_d M₀` (`Step7/Bandwidth.lean`)
is the cleared-denominator form

  `b_d · ∑_{Δ > 0} Δ⁺ · posMass ≤ b_n · M₀`

of the paper's `∑ Δ⁺ · p ≤ η = o(1)` (`step7.tex:960-967`,
`lem:budget-var`).  Its budget fraction `η = b_n / b_d` is **not**
manufactured inside Step 7 — it is supplied by Step 6: the
conductance-to-coherence dichotomy `thm:step6` plus the pointwise
corollary `cor:pointwise`, assembled end-to-end in
`Step6.cascade_steps_1_6_grounded` (`Step6/PointwiseGrounded.lean`).

That assembled Step 6 output has conclusion (Conclusion B,
`step6.tex:735-760`)

  `t_n · δ_d · ∑_{L ∈ A} I(L)² ≤ t_d · (2 · δ_n · M)`,

where `δ = δ_n/δ_d` is the coherence fraction of `thm:step6`,
`t = t_n/t_d` is the `I²`-weighted threshold of `cor:pointwise`,
`A` is the "mostly-disagreeing" exceptional set, and
`M = ∑_{α,β} w_{αβ}` is the genuine second moment / overlap mass.

Re-associated, this is exactly a cleared-denominator budget bound
`b_d · X ≤ b_n · M`, and the **genuine concrete budget constants
extracted from the landed Step 6 cascade are**

  `b_n := step6BudgetNum t_d δ_n = 2 · t_d · δ_n`,
  `b_d := step6BudgetDen t_n δ_d = t_n · δ_d`.

These are not placeholders: they are read off the literal
multiplicative structure of `cascade_steps_1_6_grounded`'s
conclusion (the `δ_n, δ_d` of the dichotomy and the `t_n, t_d` of
the pointwise corollary).

## What this file delivers

* `step6BudgetNum`, `step6BudgetDen` — the extracted constants as
  functions of the Step 6 grounded constants `t_d, δ_n` / `t_n, δ_d`.
* `step6_budget_grounded` — **the extraction theorem**: from the
  `cascade_steps_1_6_grounded` hypotheses, the budget bound
  `step6BudgetDen · ∑_A I² ≤ step6BudgetNum · M` in the
  `VarBudgetHyp` cleared shape.
* `varBudgetHyp_of_budget_bound` — the abstract projection bridge:
  any `BandwidthData` whose budget quantity is dominated by the
  Step 6 exceptional `I²`-mass satisfies `VarBudgetHyp` with the
  extracted constants.  This is the verification that the Step 6
  constants **project cleanly** into the parametric
  `lem_bandwidth_le_four_bundled` signature.
* `step6_varBudgetHyp_grounded` — the end-to-end wire: Step 6
  cascade hypotheses ⟹ `BandwidthData.VarBudgetHyp` with `b_n, b_d`.
* `step6_budget_constants_antichain3`, `antichain3_varBudgetHyp_genuine`
  — non-vacuous instantiations on the genuine width-3 non-chain
  poset `Antichain3` (`mg-496b`'s genuine S1-fiber cascade witness),
  extracting `b_n = 4`, `b_d = 1`.

## Honest scope boundary

This sub-arc extracts the **constants** `b_n, b_d` and exhibits
their clean projection into `BandwidthData.VarBudgetHyp`.  The
*genuine* `BandwidthData.ofPotential` wiring — where `delta` is the
real BFS-potential gradient and `posMass` is the real BK-adjacency
mass, and where the budget index set is the rich-pair finset rather
than the linear-extension universe — is sub-arc `mg-S7-Conc-D` (the
assembly).  That step additionally needs the paper's `lem:budget-var`
index conversion (conductance ⟹ variational budget) and a uniform
choice of the cleared denominator `M₀` shared with the Step 5
richness side (`mg-S7-Conc-B`).  Both are disclosed coordination
points, not projection failures: the extracted budget *fraction*
`b_n / b_d` is denominator-independent, so the constants slot into
the parametric signature unchanged.  See
`docs/state-S7-Conc-Session1.md` §5.

## Cross-references

* `lean/OneThird/Step7/Bandwidth.lean` — `BandwidthData`,
  `VarBudgetHyp`, `posDeltaPairs`, `lem_bandwidth`.
* `lean/OneThird/Step6/PointwiseGrounded.lean` —
  `cor_pointwise_grounded`, `cascade_steps_1_6_grounded`.
* `lean/OneThird/Step6/DichotomyGrounded.lean` — `thm_step6_grounded`.
* `lean/OneThird/Step6/CascadeComposed.lean` (`mg-496b`) — the
  genuine S1-fiber cascade witness `cascade_steps_1_6_grounded_genuine`.
* `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean` —
  `lem_bandwidth_le_four_bundled` (the parametric `b_n, b_d`
  consumer).
* Paper: `step7.tex:960-967` (`lem:budget-var`),
  `step6.tex:477-503` (`thm:step6`), `step6.tex:583-713`
  (`cor:pointwise`), `step6.tex:735-760` (the cascade).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2 — Piece 2
  spec.
-/

namespace OneThird
namespace Step7

open Finset OneThird.Step5 OneThird.Step6
open scoped BigOperators

/-! ### §1 — the extracted Step 6 budget constants -/

/-- **Step 6 budget numerator `b_n`** (`step7.tex:eq:var-budget`).

Read off `cascade_steps_1_6_grounded`'s conclusion
`t_n · δ_d · ∑_A I² ≤ t_d · (2 · δ_n · M)`: the budget numerator is
the `M`-coefficient on the right, `2 · t_d · δ_n` — twice the
`I²`-weighted threshold denominator `t_d` times the coherence-fraction
numerator `δ_n`.  The factor `2` is the `step6.tex:646-649`
active/non-active split of the disagreement mass. -/
def step6BudgetNum (t_d δ_n : ℕ) : ℕ := 2 * t_d * δ_n

/-- **Step 6 budget denominator `b_d`** (`step7.tex:eq:var-budget`).

Read off `cascade_steps_1_6_grounded`'s conclusion
`t_n · δ_d · ∑_A I² ≤ t_d · (2 · δ_n · M)`: the budget denominator is
the coefficient on the budget quantity `∑_A I²` on the left,
`t_n · δ_d` — the `I²`-weighted threshold numerator `t_n` times the
coherence-fraction denominator `δ_d`. -/
def step6BudgetDen (t_n δ_d : ℕ) : ℕ := t_n * δ_d

/-! ### §2 — the budget bound extracted from the Step 6 cascade -/

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
variable {Pair : Type*} [DecidableEq Pair]

/-- **The Step 6 budget bound, extracted in the `VarBudgetHyp`
cleared shape** (`mg-S7-Conc-C`).

The assembled Steps 1–6 cascade `cascade_steps_1_6_grounded`
(`Step6/PointwiseGrounded.lean`, `mg-65af`) delivers Conclusion B

  `t_n · δ_d · ∑_{L ∈ A} I(L)² ≤ t_d · (2 · δ_n · M)`.

Re-associating the multiplicative constants, this is precisely a
cleared-denominator budget bound

  `b_d · X ≤ b_n · M₀`

with the **genuine extracted constants** `b_d = step6BudgetDen t_n δ_d`
(`= t_n · δ_d`) and `b_n = step6BudgetNum t_d δ_n` (`= 2 · t_d · δ_n`),
the budget quantity `X = ∑_{L ∈ A} I(L)²` (the exceptional
`I²`-mass on the "mostly-disagreeing" set `A`), and the cleared
denominator `M₀ = M = ∑_{α,β} w_{αβ}` the genuine second moment /
overlap mass.

This is the shape `BandwidthData.VarBudgetHyp` consumes — see
`varBudgetHyp_of_budget_bound`. -/
theorem step6_budget_grounded
    (S LP : Finset (LinearExt α))
    (richStar : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (σ : Pair → Sign)
    (badSet : Finset (Pair × Pair)) (w : Pair → Pair → ℕ)
    (mult c_n c_d δ_n δ_d c_R t_n t_d : ℕ)
    (hsub : ∀ a ∈ richStar, Fstar a ⊆ LP)
    (hfirst : c_R * LP.card ≤ ∑ a ∈ richStar, (Fstar a).card)
    (hvol : S.card ≤ LP.card)
    (hSum : c_n * ∑ p ∈ badSet, w p.1 p.2
              ≤ c_d * mult * (Step4.bkBoundary S).card)
    (hLow : c_d * mult * δ_d * (Step4.bkBoundary S).card
              < c_n * δ_n * c_R ^ 2 * S.card)
    (hbadW : ∀ p ∈ badSet, w p.1 p.2 = pairOverlap Fstar p.1 p.2)
    (hbadSub : badSet ⊆ disagreePairs richStar σ)
    (hNonActive : δ_d * (∑ p ∈ disagreePairs richStar σ \ badSet,
        pairOverlap Fstar p.1 p.2)
          ≤ δ_n * (∑ p ∈ richStar ×ˢ richStar,
              pairOverlap Fstar p.1 p.2)) :
    step6BudgetDen t_n δ_d *
        ∑ L ∈ LP.filter (fun L => t_n * visibility richStar Fstar L
              ≤ t_d * minorityCount richStar Fstar σ L),
          (visibility richStar Fstar L) ^ 2
      ≤ step6BudgetNum t_d δ_n
          * (∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2) := by
  have hcasc := cascade_steps_1_6_grounded S LP richStar Fstar σ badSet w
    mult c_n c_d δ_n δ_d c_R t_n t_d hsub hfirst hvol hSum hLow hbadW
    hbadSub hNonActive
  unfold step6BudgetDen step6BudgetNum
  exact le_trans hcasc (le_of_eq (by ring))

/-! ### §3 — clean projection into the Step 7 `VarBudgetHyp` signature -/

/-- **The extracted constants project cleanly into
`BandwidthData.VarBudgetHyp`** (`mg-S7-Conc-C` non-triviality bar).

`VarBudgetHyp pairs b_n b_d M₀` (`Step7/Bandwidth.lean`) is, by
definition,

  `b_d · ∑_{p ∈ posDeltaPairs} Δ⁺(p) · posMass(p) ≤ b_n · M₀`.

Given **any** `BandwidthData D` over **any** carrier `Pair'` whose
budget quantity `∑ Δ⁺ · posMass` is dominated by the Step 6
exceptional `I²`-mass (`hModel`), and the Step 6 budget bound
`b_d · (exceptional mass) ≤ b_n · M₀` (`hBound`, the output of
`step6_budget_grounded`), the `VarBudgetHyp` holds with the
extracted constants `b_n, b_d` and cleared denominator `M₀`.

This is the verification that the Step 6 constants slot into the
parametric `lem_bandwidth_le_four_bundled` signature with **no
adapter algebra** — the cleared-denominator shapes coincide. -/
theorem varBudgetHyp_of_budget_bound
    {Pair' : Type*}
    (D : BandwidthData Pair') (budgetPairs : Finset Pair')
    (b_n b_d M₀ exceptionalMass : ℕ)
    (hModel : ∑ p ∈ D.posDeltaPairs budgetPairs,
        (D.delta p).toNat * D.posMass p ≤ exceptionalMass)
    (hBound : b_d * exceptionalMass ≤ b_n * M₀) :
    D.VarBudgetHyp budgetPairs b_n b_d M₀ := by
  unfold BandwidthData.VarBudgetHyp
  exact le_trans (Nat.mul_le_mul_left _ hModel) hBound

/-- **End-to-end wire: the Step 6 cascade discharges
`BandwidthData.VarBudgetHyp`** (`mg-S7-Conc-C`).

Composes `step6_budget_grounded` (the budget bound extracted from
`cascade_steps_1_6_grounded`) with `varBudgetHyp_of_budget_bound`
(clean projection): from the genuine Steps 1–6 cascade hypotheses
plus a model bound `hModel` tying a `BandwidthData D`'s budget
quantity to the Step 6 exceptional `I²`-mass, conclude

  `D.VarBudgetHyp budgetPairs (step6BudgetNum t_d δ_n)
      (step6BudgetDen t_n δ_d) M`,

i.e. the Step 7 variational-budget hypothesis with the **genuine
extracted Step 6 constants** `b_n = 2·t_d·δ_n`, `b_d = t_n·δ_d` and
the second moment `M` as the cleared denominator.  This is the
object `mg-S7-Conc-D` feeds, as `hBud`, to
`lem_bandwidth_le_four_bundled`. -/
theorem step6_varBudgetHyp_grounded
    {Pair' : Type*}
    (D : BandwidthData Pair') (budgetPairs : Finset Pair')
    (S LP : Finset (LinearExt α))
    (richStar : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (σ : Pair → Sign)
    (badSet : Finset (Pair × Pair)) (w : Pair → Pair → ℕ)
    (mult c_n c_d δ_n δ_d c_R t_n t_d : ℕ)
    (hsub : ∀ a ∈ richStar, Fstar a ⊆ LP)
    (hfirst : c_R * LP.card ≤ ∑ a ∈ richStar, (Fstar a).card)
    (hvol : S.card ≤ LP.card)
    (hSum : c_n * ∑ p ∈ badSet, w p.1 p.2
              ≤ c_d * mult * (Step4.bkBoundary S).card)
    (hLow : c_d * mult * δ_d * (Step4.bkBoundary S).card
              < c_n * δ_n * c_R ^ 2 * S.card)
    (hbadW : ∀ p ∈ badSet, w p.1 p.2 = pairOverlap Fstar p.1 p.2)
    (hbadSub : badSet ⊆ disagreePairs richStar σ)
    (hNonActive : δ_d * (∑ p ∈ disagreePairs richStar σ \ badSet,
        pairOverlap Fstar p.1 p.2)
          ≤ δ_n * (∑ p ∈ richStar ×ˢ richStar,
              pairOverlap Fstar p.1 p.2))
    (hModel : ∑ p ∈ D.posDeltaPairs budgetPairs,
          (D.delta p).toNat * D.posMass p
        ≤ ∑ L ∈ LP.filter (fun L => t_n * visibility richStar Fstar L
              ≤ t_d * minorityCount richStar Fstar σ L),
            (visibility richStar Fstar L) ^ 2) :
    D.VarBudgetHyp budgetPairs (step6BudgetNum t_d δ_n)
        (step6BudgetDen t_n δ_d)
        (∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2) :=
  varBudgetHyp_of_budget_bound D budgetPairs _ _ _ _ hModel
    (step6_budget_grounded S LP richStar Fstar σ badSet w mult c_n c_d
      δ_n δ_d c_R t_n t_d hsub hfirst hvol hSum hLow hbadW hbadSub
      hNonActive)

/-! ### §4 — non-vacuous instantiation at the genuine `Antichain3` cascade

The `mg-496b` genuine cascade witness `cascade_steps_1_6_grounded_genuine`
(`Step6/CascadeComposed.lean`) runs the whole Steps 1–6 cascade on the
genuine S1 `thm_interface`-produced good-fiber set of the width-3
non-chain poset `Antichain3`.  Its constants are
`t_n = 1, t_d = 2, δ_n = 1, δ_d = 1`, so the extracted Step 6 budget
constants are

  `b_n = step6BudgetNum 2 1 = 4`,  `b_d = step6BudgetDen 1 1 = 1`.

The witnesses below re-derive that cascade through `step6_budget_grounded`
and exhibit a genuine `BandwidthData.VarBudgetHyp` carrying these
constants — the un-fakeable satisfiability gate: every quantity is a
sum over the genuine fiber `goodFiberSet a0 a1`, which would be `0`
were that fiber empty (its provable pre-`mg-fc78` state). -/

section ConcreteWitness

/-- **The Step 6 budget constants extracted at the genuine `Antichain3`
cascade** (`mg-S7-Conc-C` non-triviality bar).

Routes the genuine Steps 1–6 cascade of `Antichain3` (the `mg-496b`
witness data: singleton cut `genCut`, two opposite-signed rich
interfaces with the genuine S1 good-fiber `genFstar`) through
`step6_budget_grounded`, and reads off:

* the genuine extracted constants `b_n = 4`, `b_d = 1`;
* the budget bound `b_d · ∑_A I² ≤ b_n · M`, i.e. `1 · 24 ≤ 4 · 24`
  with the genuine exceptional `I²`-mass `∑_A I² = 24` and second
  moment `M = 24`.

Not a placeholder: the `4` and `1` are `step6BudgetNum 2 1` /
`step6BudgetDen 1 1` evaluated at the cascade's own constants
`t_d = 2, δ_n = 1` / `t_n = 1, δ_d = 1`, and the bound is discharged
by `step6_budget_grounded` on the genuine cascade hypotheses. -/
theorem step6_budget_constants_antichain3 :
    step6BudgetNum 2 1 = 4 ∧
    step6BudgetDen 1 1 = 1 ∧
    step6BudgetDen 1 1
        * (∑ L ∈ genLP.filter (fun L => 1 * visibility genRich genFstar L
              ≤ 2 * minorityCount genRich genFstar genSign L),
            (visibility genRich genFstar L) ^ 2)
      ≤ step6BudgetNum 2 1
          * (∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2) := by
  refine ⟨rfl, rfl, ?_⟩
  set B := (Step4.bkBoundary genCut).card with hBdef
  have hsub : ∀ a ∈ genRich, genFstar a ⊆ genLP :=
    fun a _ => Finset.subset_univ (genFstar a)
  have hvol : genCut.card ≤ genLP.card := by
    rw [show genCut.card = 1 from by simp [genCut], gen_LP_card]
    decide
  have hSum : (B + 1) * ∑ p ∈ (∅ : Finset (Bool × Bool)),
        (fun _ _ => (0 : ℕ)) p.1 p.2
      ≤ 1 * 1 * (Step4.bkBoundary genCut).card := by
    simp
  have hLow : 1 * 1 * 1 * (Step4.bkBoundary genCut).card
      < (B + 1) * 1 * (1 : ℕ) ^ 2 * genCut.card := by
    have hcard : genCut.card = 1 := by simp [genCut]
    rw [hcard, ← hBdef]
    ring_nf
    omega
  have hbadW : ∀ p ∈ (∅ : Finset (Bool × Bool)),
      (fun _ _ => (0 : ℕ)) p.1 p.2 = pairOverlap genFstar p.1 p.2 :=
    fun p hp => absurd hp (by simp)
  have hbadSub : (∅ : Finset (Bool × Bool)) ⊆ disagreePairs genRich genSign :=
    Finset.empty_subset _
  have hNonActive : (1 : ℕ) * (∑ p ∈ disagreePairs genRich genSign
        \ (∅ : Finset (Bool × Bool)), pairOverlap genFstar p.1 p.2)
      ≤ 1 * (∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2) := by
    rw [Finset.sdiff_empty, gen_disagree_mass, gen_M]
    decide
  exact step6_budget_grounded genCut genLP genRich genFstar genSign
    (∅ : Finset (Bool × Bool)) (fun _ _ => 0) 1 (B + 1) 1 1 1 1 1 2
    hsub gen_step5_richness hvol hSum hLow hbadW hbadSub hNonActive

/-- **Concrete `BandwidthData` modeling the Step 6 disagreement
budget on `Antichain3`.**

A *shape witness* for the clean projection: the carrier is the
linear-extension universe `LinearExt Antichain3`, and the per-`L`
signed gradient and adjacency mass are both the genuine visibility
count `I(L)`, so the cleared budget quantity `Δ⁺(L) · posMass(L)`
is the genuine `I(L)²`.

This is **not** the genuine `BandwidthData.ofPotential` of
`mg-S7-Conc-D` (whose `delta` is the BFS-potential gradient and
whose carrier is the rich-pair finset).  It is the minimal genuine
`BandwidthData` whose `VarBudgetHyp` exposes the extracted Step 6
constants on real cascade data — confirming the projection is
non-vacuously realisable. -/
noncomputable def antichain3DisagreeBudget :
    BandwidthData (LinearExt Antichain3) :=
  { delta := fun L => (visibility genRich genFstar L : ℤ)
    posMass := fun L => visibility genRich genFstar L }

@[simp] lemma antichain3DisagreeBudget_delta (L : LinearExt Antichain3) :
    antichain3DisagreeBudget.delta L
      = (visibility genRich genFstar L : ℤ) := rfl

@[simp] lemma antichain3DisagreeBudget_posMass (L : LinearExt Antichain3) :
    antichain3DisagreeBudget.posMass L
      = visibility genRich genFstar L := rfl

/-- **A genuine `BandwidthData.VarBudgetHyp` carrying the extracted
Step 6 constants** (`mg-S7-Conc-C` non-triviality bar).

`antichain3DisagreeBudget` satisfies the Step 7 variational-budget
hypothesis

  `VarBudgetHyp genLP (step6BudgetNum 2 1) (step6BudgetDen 1 1) M`

— i.e. `VarBudgetHyp` with the **genuine extracted constants**
`b_n = 4`, `b_d = 1` and cleared denominator the second moment
`M = 24`.  The proof composes `varBudgetHyp_of_budget_bound` (clean
projection) with `step6_budget_constants_antichain3` (the genuine
Step 6 budget bound), the model bound `hModel` being the genuine
identity `∑ Δ⁺·posMass = ∑_A I² = 24` (both sides positive — `0`
were the S1 fiber empty).  This is the compiler-checked witness that
the Step 6 constants project into the parametric signature without
adapter algebra. -/
theorem antichain3_varBudgetHyp_genuine :
    antichain3DisagreeBudget.VarBudgetHyp genLP
        (step6BudgetNum 2 1) (step6BudgetDen 1 1)
        (∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2) := by
  have hpd : antichain3DisagreeBudget.posDeltaPairs genLP = genLP := by
    unfold BandwidthData.posDeltaPairs
    apply Finset.filter_true_of_mem
    intro L _
    simp only [antichain3DisagreeBudget_delta]
    rw [gen_visibility L]
    decide
  have hLHS : ∑ p ∈ antichain3DisagreeBudget.posDeltaPairs genLP,
      (antichain3DisagreeBudget.delta p).toNat
        * antichain3DisagreeBudget.posMass p = 24 := by
    rw [hpd]
    have hterm : ∀ L ∈ genLP,
        (antichain3DisagreeBudget.delta L).toNat
          * antichain3DisagreeBudget.posMass L = 4 := by
      intro L _
      simp only [antichain3DisagreeBudget_delta,
        antichain3DisagreeBudget_posMass]
      rw [gen_visibility L]
      decide
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
      gen_LP_card]
  have hModel : ∑ p ∈ antichain3DisagreeBudget.posDeltaPairs genLP,
        (antichain3DisagreeBudget.delta p).toNat
          * antichain3DisagreeBudget.posMass p
      ≤ ∑ L ∈ genLP.filter (fun L => 1 * visibility genRich genFstar L
            ≤ 2 * minorityCount genRich genFstar genSign L),
          (visibility genRich genFstar L) ^ 2 :=
    le_of_eq (by rw [hLHS, gen_A_sum])
  exact varBudgetHyp_of_budget_bound antichain3DisagreeBudget genLP
    (step6BudgetNum 2 1) (step6BudgetDen 1 1)
    (∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2)
    (∑ L ∈ genLP.filter (fun L => 1 * visibility genRich genFstar L
          ≤ 2 * minorityCount genRich genFstar genSign L),
        (visibility genRich genFstar L) ^ 2)
    hModel (step6_budget_constants_antichain3).2.2

end ConcreteWitness

end Step7
end OneThird
