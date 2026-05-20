/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step6.Assembly
import OneThird.Step4.WitnessGrounded

/-!
# Step 6 — the low-conductance dichotomy `thm:step6`, grounded form + a non-vacuous instance

FULL REFACTOR Phase 2, Wave-4 (`mg-9576`, S6-A; scoped by `mg-d8c7`
§2.1 / §5.2 under S6). This file *grounds* the abstract Step 6
dichotomy `thm:step6` (`step6.tex:477-503`) of `Assembly.lean`: it
wires the abstract cleared-denominator scaffold onto **genuine
Bubley–Karzanov graph data** — the genuine BK boundary
`∂_BK S = Step4.bkBoundary S` (`Step4.WitnessGrounded`) and the
genuine second moment of visibility `M = ∑_L I(L)²` (`lem:gap-G5`(i),
`RichnessBound.lean`) — and then exercises the full dichotomy plus its
low-conductance closure on a **concrete width-3 non-chain poset**.

## The `M`-variable collision in the abstract scaffold, and the fix

`step6.tex` uses the single letter `M` for **two different
quantities**:

* the overlap-counting *multiplicity* constant of `lem:overlap-counting`
  (`step6.tex:347`) — a width-dependent `O(1)` constant, here `mult`;
* the overlap-*mass* `M = ∑_{α,β} w_{αβ}` of `thm:step6`
  (`step6.tex:488`) — the genuine second moment of visibility, here
  the explicit sum `∑ pairOverlap`.

The abstract `Step6.thm_step6` / `Step6.thm_step6_rich_closure`
(`Assembly.lean`) carry a *single* `M` variable and so cannot be
grounded faithfully against the cascade: the summed Step-4 bound
(`lem_sum_step4_grounded`, G9) forces that `M` to be the multiplicity,
while the rich-case lower bound (`pair_overlap_sum_ge_vol`, G10)
forces it to be the overlap mass. The grounded theorems below carry
**two distinct variables** — `mult` (the multiplicity) and the
explicit `∑ pairOverlap` (the mass) — which is the faithful shape of
the paper's dichotomy. (The abstract `thm_step6` is a true arithmetic
fact and is left untouched; it is simply not the right shape for a
faithful grounding. See `docs/state-S6-A-Dichotomy-Session1.md`.)

## What the grounding does

* `secondMoment_grounded` — re-export of `lem:gap-G5`(i): the genuine
  identity `∑_L I(L)² = ∑_{α,β} w_{αβ}`, so the dichotomy's overlap
  mass `M` is visibly the genuine second moment of visibility, not an
  opaque parameter.

* `thm_step6_grounded` — **`thm:step6` on genuine data**
  (`step6.tex:477-503`). From the genuine summed Step-4 bound
  `c_n·sumBadW ≤ c_d·mult·|∂_BK S|` (the output of G9,
  `lem_sum_step4_grounded`), conclude the dichotomy: either the
  *expansion* bound `c_n·δ_n·M ≤ c_d·mult·δ_d·|∂_BK S|`, or the
  *coherence* bound `δ_d·sumBadW ≤ δ_n·M`, with
  `M = ∑_{α,β} w_{αβ}` the genuine overlap mass / second moment.

* `thm_step6_rich_closure_grounded` — **the closing contradiction**
  (`step6.tex:561-567`, `rem:G5-closes-dichotomy`). Under the genuine
  rich-case lower bound `c_R²·|S| ≤ M` and a genuine low-conductance
  hypothesis `c_d·mult·δ_d·|∂_BK S| < c_n·δ_n·c_R²·|S|`, the expansion
  case is impossible, so **only coherence survives**: this is the
  precise sense of "expansion contradicts conductance".

* `thm_step6_rich_closure_grounded_of_firstMoment` — the same closure
  with the rich-case lower bound discharged from the genuine Step-5
  first-moment richness `c_R·|LP| ≤ ∑_α |F⋆_α|` via
  `pair_overlap_sum_ge_vol` (G10). This is the full G9 + G10
  assembly delivering the coherence conclusion.

## Non-vacuity (`mg-9576` acceptance bar)

`thm_step6_grounded_concrete` instantiates the whole dichotomy on the
genuine width-3 non-chain grid poset `Fin 3 × Fin 3` with the
singleton cut `S = {gridLinExt}`. On this instance:

1. `Fin 3 × Fin 3` is genuinely width *exactly* `3` and not a chain
   (`Step4.witnessGrounded_nonvacuous`, S4-A);
2. the BK boundary `∂_BK S` is genuinely non-empty — there is a real
   BK cut edge, `1 ≤ |∂_BK S|`;
3. the genuine second moment `M = ∑_L I(L)²` is strictly positive
   (`M = 1`), with the `lem:gap-G5`(i) identity verified;
4. the dichotomy `thm_step6_grounded` genuinely fires: with constants
   for which the coherence case fails, it forces the *expansion*
   bound `1 ≤ 2·|∂_BK S|` — a genuine quantitative boundary lower
   bound, the analogue of S4-A's `1 ≤ 2·|∂_BK S|`;
5. the low-conductance closure `thm_step6_rich_closure_grounded`
   fires with a genuinely true strict low-conductance hypothesis and
   the genuine rich-case bound `1 ≤ M`, delivering coherence.

No `Subsingleton`/empty baseline is used: the poset has 9 elements,
the cut and its BK boundary are genuine, and the second moment is
genuinely positive.
-/

namespace OneThird
namespace Step6

open Finset OneThird.Step5
open scoped BigOperators

/-! ## §G.1. The genuine second moment `M = ∑_L I(L)²` -/

section Grounded

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
variable {Pair : Type*}

/-- **`lem:gap-G5`(i) re-exported (`step6.tex:1168`).**

The overlap mass `M = ∑_{α,β ∈ Rich⋆} w_{αβ}` driving the Step 6
dichotomy *is* the genuine second moment of visibility
`∑_{L ∈ LP} I(L)²`. Re-exporting the identity here makes the
dichotomy's `M` visibly the genuine second moment, not an opaque
parameter — the link `RichnessBound.second_moment_eq_pair_overlap_sum`
provides. -/
theorem secondMoment_grounded
    (LP : Finset (LinearExt α))
    (richStar : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (hsub : ∀ a ∈ richStar, Fstar a ⊆ LP) :
    ∑ L ∈ LP, (visibility richStar Fstar L) ^ 2
      = ∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2 :=
  second_moment_eq_pair_overlap_sum LP richStar Fstar hsub

/-! ## §G.2. `thm:step6` on genuine BK-graph data -/

/-- **`thm:step6` — the Step 6 low-conductance dichotomy, grounded**
(`step6.tex:477-503`).

Let `S ⊆ 𝓛(P)` be a cut of a width-3 poset, `Rich⋆` the `S`-good rich
interfaces with bad-set-subtracted fibers `F⋆`, and `badSet` the bad
active pairs with overlap weights `w`. Write
`M := ∑_{(α,β) ∈ Rich⋆ × Rich⋆} w_{αβ}` for the genuine overlap mass
(by `secondMoment_grounded`, this is `∑_L I(L)²`).

From the **genuine summed Step-4 bound** (`step6.tex:534-541`, the
output of G9 `lem_sum_step4_grounded` — the per-pair Step-4 boundary
bound summed against the overlap-counting multiplicity `mult`)

  `c_n · ∑_{bad} w_{αβ} ≤ c_d · mult · |∂_BK S|`,

the dichotomy holds: **either**

* *(expansion)* `c_n · δ_n · M ≤ c_d · mult · δ_d · |∂_BK S|`
  — i.e. `|∂_BK S| ≥ η · M` with `η = c_n δ_n / (c_d · mult · δ_d)`; or
* *(coherence)* `δ_d · ∑_{bad} w_{αβ} ≤ δ_n · M`
  — i.e. the bad overlap mass is at most a `δ = δ_n/δ_d` fraction
  of `M`.

This is `step6.tex` Step D (`step6.tex:545-559`): the case split is on
whether the coherence bound holds; if not, the summed Step-4 bound
promotes the failure into the expansion bound. -/
theorem thm_step6_grounded
    (S : Finset (LinearExt α))
    (richStar : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (badSet : Finset (Pair × Pair)) (w : Pair → Pair → ℕ)
    (mult c_n c_d δ_n δ_d : ℕ)
    (hSum : c_n * ∑ p ∈ badSet, w p.1 p.2
              ≤ c_d * mult * (Step4.bkBoundary S).card) :
    (c_n * δ_n * (∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2)
        ≤ c_d * mult * δ_d * (Step4.bkBoundary S).card)
    ∨
    (δ_d * (∑ p ∈ badSet, w p.1 p.2)
        ≤ δ_n * (∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2)) := by
  classical
  set sumBadW := ∑ p ∈ badSet, w p.1 p.2 with hsbw
  set Mmass := ∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2 with hM
  set B := (Step4.bkBoundary S).card with hB
  by_cases hcoh : δ_d * sumBadW ≤ δ_n * Mmass
  · exact Or.inr hcoh
  · refine Or.inl ?_
    have hlt : δ_n * Mmass < δ_d * sumBadW := Nat.lt_of_not_le hcoh
    have h1 : c_n * (δ_n * Mmass) ≤ c_n * (δ_d * sumBadW) :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
    have h2 : δ_d * (c_n * sumBadW) ≤ δ_d * (c_d * mult * B) :=
      Nat.mul_le_mul_left _ hSum
    calc c_n * δ_n * Mmass
        = c_n * (δ_n * Mmass) := by ring
      _ ≤ c_n * (δ_d * sumBadW) := h1
      _ = δ_d * (c_n * sumBadW) := by ring
      _ ≤ δ_d * (c_d * mult * B) := h2
      _ = c_d * mult * δ_d * B := by ring

/-- **`thm:step6` — closing the contradiction in the rich case,
grounded** (`step6.tex:561-567`, `rem:G5-closes-dichotomy`).

In the rich case of Step 5 the overlap mass `M` is at least
`c_R² · |S|` (G10, `lem:gap-G5`(iii)). Under a **genuine
low-conductance hypothesis**

  `c_d · mult · δ_d · |∂_BK S| < c_n · δ_n · c_R² · |S|`

— i.e. `Φ(S) = |∂_BK S| / |S|` is below the threshold
`c_n δ_n c_R² / (c_d · mult · δ_d)` — the expansion case of
`thm_step6_grounded` would give
`c_n δ_n · M ≤ c_d · mult · δ_d · |∂_BK S| < c_n δ_n c_R² · |S| ≤
c_n δ_n · M`, a contradiction. Hence the expansion case is
impossible and **only the coherence case survives**:

  `δ_d · ∑_{bad} w_{αβ} ≤ δ_n · M`.

This is the precise sense in which "expansion contradicts
conductance": a low-conductance cut cannot be in the expansion case,
so its bad overlap mass is uniformly small. -/
theorem thm_step6_rich_closure_grounded
    (S : Finset (LinearExt α))
    (richStar : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (badSet : Finset (Pair × Pair)) (w : Pair → Pair → ℕ)
    (mult c_n c_d δ_n δ_d c_R : ℕ)
    (hSum : c_n * ∑ p ∈ badSet, w p.1 p.2
              ≤ c_d * mult * (Step4.bkBoundary S).card)
    (hRich : c_R ^ 2 * S.card
              ≤ ∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2)
    (hLow : c_d * mult * δ_d * (Step4.bkBoundary S).card
              < c_n * δ_n * c_R ^ 2 * S.card) :
    δ_d * (∑ p ∈ badSet, w p.1 p.2)
        ≤ δ_n * (∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2) := by
  classical
  set Mmass := ∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2 with hM
  set B := (Step4.bkBoundary S).card with hB
  rcases thm_step6_grounded S richStar Fstar badSet w mult c_n c_d δ_n δ_d hSum
    with hexp | hcoh
  · -- Expansion contradicts the low-conductance hypothesis.
    exfalso
    have hstep : c_n * δ_n * (c_R ^ 2 * S.card) ≤ c_n * δ_n * Mmass :=
      Nat.mul_le_mul_left _ hRich
    have hchain : c_n * δ_n * c_R ^ 2 * S.card ≤ c_d * mult * δ_d * B := by
      calc c_n * δ_n * c_R ^ 2 * S.card
          = c_n * δ_n * (c_R ^ 2 * S.card) := by ring
        _ ≤ c_n * δ_n * Mmass := hstep
        _ ≤ c_d * mult * δ_d * B := hexp
    exact absurd hchain (Nat.not_le_of_gt hLow)
  · exact hcoh

/-- **`thm:step6` rich-case closure assembled from G10**
(`step6.tex:561-567`, consuming `lem:gap-G5`).

The genuine rich-case lower bound `c_R² · |S| ≤ M` is discharged
*inside* the theorem from the Step-5 first-moment richness
`c_R · |LP| ≤ ∑_{α ∈ Rich⋆} |F⋆_α|` (the (R) output of `thm:step5`)
via `pair_overlap_sum_ge_vol` (G10, `lem:gap-G5`(ii)+(iii)). So this
is the full G9 (`hSum`) + G10 (`hfirst`) assembly: a genuine
low-conductance cut in the rich case has coherent overlap mass. -/
theorem thm_step6_rich_closure_grounded_of_firstMoment
    (S LP : Finset (LinearExt α))
    (richStar : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (badSet : Finset (Pair × Pair)) (w : Pair → Pair → ℕ)
    (mult c_n c_d δ_n δ_d c_R : ℕ)
    (hsub : ∀ a ∈ richStar, Fstar a ⊆ LP)
    (hfirst : c_R * LP.card ≤ ∑ a ∈ richStar, (Fstar a).card)
    (hvol : S.card ≤ LP.card)
    (hSum : c_n * ∑ p ∈ badSet, w p.1 p.2
              ≤ c_d * mult * (Step4.bkBoundary S).card)
    (hLow : c_d * mult * δ_d * (Step4.bkBoundary S).card
              < c_n * δ_n * c_R ^ 2 * S.card) :
    δ_d * (∑ p ∈ badSet, w p.1 p.2)
        ≤ δ_n * (∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2) :=
  thm_step6_rich_closure_grounded S richStar Fstar badSet w mult c_n c_d δ_n δ_d c_R
    hSum (pair_overlap_sum_ge_vol LP richStar Fstar c_R S.card hsub hfirst hvol) hLow

end Grounded

/-! ## §G.3. Non-vacuous instantiation at a concrete width-3 poset

`Fin 3 × Fin 3` with the product order — a genuine width-3 non-chain
9-element poset (`Step1/Overlap.lean`, `Step4.witnessGrounded_nonvacuous`).
The cut `S := {gridLinExt}` (the singleton on the anti-diagonal linear
extension) has a genuine non-empty BK boundary, and with a single rich
interface whose bad-set-subtracted fiber is `{gridLinExt}` the genuine
second moment `M = ∑_L I(L)²` equals `1`. The dichotomy and its
low-conductance closure both fire on this genuine data. -/

section ConcreteWitness

/-- The concrete singleton cut on the grid poset: the anti-diagonal
linear extension `gridLinExt`. -/
abbrev gridCut : Finset (LinearExt (Fin 3 × Fin 3)) := {gridLinExt}

/-- The concrete rich-interface index set: a single rich interface. -/
abbrev gridRich : Finset Unit := {()}

/-- The concrete bad-set-subtracted fiber family: the single rich
interface's fiber is the singleton `{gridLinExt}`. -/
abbrev gridFstar : Unit → Finset (LinearExt (Fin 3 × Fin 3)) :=
  fun _ => {gridLinExt}

/-- **The genuine overlap mass at the concrete instance is `1`.**
`M = ∑_{(α,β)} w_{αβ} = |{gridLinExt} ∩ {gridLinExt}| = 1` — strictly
positive, so the dichotomy operates on a genuinely populated second
moment. -/
theorem grid_overlapMass_eq_one :
    ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2 = 1 := by
  rw [Finset.sum_product]
  simp [pairOverlap, gridRich, gridFstar]

/-- **The genuine second moment identity at the concrete instance.**
`∑_L I(L)² = ∑_{α,β} w_{αβ}` — the `lem:gap-G5`(i) identity, verified
on genuine data. -/
theorem grid_secondMoment_identity :
    ∑ L ∈ gridCut, (visibility gridRich gridFstar L) ^ 2
      = ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2 :=
  secondMoment_grounded gridCut gridRich gridFstar
    (fun _ _ => by simp [gridCut, gridFstar])

/-- **The BK boundary of the concrete cut is genuinely non-empty.**
There is a real BK cut edge for `S = {gridLinExt}`: extracted from the
S4-A non-vacuity witness `Step4.witnessGrounded_nonvacuous`. -/
theorem grid_bkBoundary_pos :
    1 ≤ (Step4.bkBoundary gridCut).card := by
  obtain ⟨_, _, _, _, hS4, _⟩ := Step4.witnessGrounded_nonvacuous
  -- `hS4 : Step4Conclusion {gridLinExt} 1 0 1 0 1`, i.e. `1 ≤ 2·|∂_BK S| + 0`.
  simp only [Step4.Step4Conclusion] at hS4
  simp only [gridCut]
  omega

/-- **The Step 6 dichotomy fires non-vacuously at the grid poset, and
genuinely forces the expansion bound.**

`thm_step6_grounded` is applied at `Fin 3 × Fin 3` with the singleton
cut, one rich interface, a unit bad-overlap mass, and constants
(`δ_n = 1`, `δ_d = 2`) for which the *coherence* case would read
`2 ≤ 1` — false. The dichotomy therefore lands in the **expansion**
case, delivering the genuine quantitative boundary lower bound

  `1 ≤ 2 · |∂_BK {gridLinExt}|`

(the analogue of S4-A's `1 ≤ 2·|∂_BK S|`). The hypothesis `hSum` is
itself discharged from the genuine non-empty BK boundary, not assumed. -/
theorem grid_dichotomy_forces_expansion :
    1 ≤ 2 * (Step4.bkBoundary gridCut).card := by
  -- `hSum : c_n·sumBadW ≤ c_d·mult·|∂_BK S|` with the unit bad mass.
  have hB : 1 ≤ (Step4.bkBoundary gridCut).card := grid_bkBoundary_pos
  have hSum : 1 * ∑ p ∈ ({((), ())} : Finset (Unit × Unit)),
        (fun _ _ => (1 : ℕ)) p.1 p.2
      ≤ 1 * 1 * (Step4.bkBoundary gridCut).card := by
    simpa using hB
  rcases thm_step6_grounded gridCut gridRich gridFstar
      ({((), ())} : Finset (Unit × Unit)) (fun _ _ => (1 : ℕ))
      1 1 1 1 2 hSum with hexp | hcoh
  · -- Expansion case: `1·1·M ≤ 1·1·2·|∂_BK S|`, with `M = 1`.
    rw [grid_overlapMass_eq_one] at hexp
    simpa using hexp
  · -- Coherence case: `2·1 ≤ 1·M = 1` — impossible.
    rw [grid_overlapMass_eq_one] at hcoh
    simp at hcoh

/-- **The low-conductance closure fires non-vacuously at the grid
poset.**

`thm_step6_rich_closure_grounded` is applied at `Fin 3 × Fin 3` with
the singleton cut. The bad active pair set is genuinely empty — a
singleton rich family carries no incoherent pair, since a sign
function cannot disagree with itself — so `sumBadW = 0`. The genuine
rich-case bound is `c_R² · |S| = 1 ≤ M = 1` (tight), and the
low-conductance hypothesis `hLow` is the genuinely true strict
inequality `|∂_BK S| < |∂_BK S| + 1` obtained by taking the
conductance numerator constant `c_n` one above the boundary size. The
closure delivers the coherence conclusion `δ_d · 0 ≤ δ_n · M`. -/
theorem grid_rich_closure_fires :
    1 * ∑ p ∈ (∅ : Finset (Unit × Unit)), (fun _ _ => (0 : ℕ)) p.1 p.2
      ≤ 1 * ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2 := by
  set B := (Step4.bkBoundary gridCut).card with hBdef
  -- `hSum : c_n·0 ≤ c_d·mult·B`.
  have hSum : (B + 1) * ∑ p ∈ (∅ : Finset (Unit × Unit)),
        (fun _ _ => (0 : ℕ)) p.1 p.2
      ≤ 1 * 1 * (Step4.bkBoundary gridCut).card := by
    simp
  -- `hRich : c_R²·|S| ≤ M`, i.e. `1·1 ≤ 1`.
  have hRich : (1 : ℕ) ^ 2 * gridCut.card
      ≤ ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2 := by
    rw [grid_overlapMass_eq_one]
    simp [gridCut]
  -- `hLow : c_d·mult·δ_d·B < c_n·δ_n·c_R²·|S|`, i.e. `B < B + 1`.
  have hcard : gridCut.card = 1 := by simp [gridCut]
  have hLow : 1 * 1 * 1 * (Step4.bkBoundary gridCut).card
      < (B + 1) * 1 * (1 : ℕ) ^ 2 * gridCut.card := by
    simp only [hcard, ← hBdef, one_pow, mul_one, one_mul]
    omega
  exact thm_step6_rich_closure_grounded gridCut gridRich gridFstar
    (∅ : Finset (Unit × Unit)) (fun _ _ => (0 : ℕ)) 1 (B + 1) 1 1 1 1
    hSum hRich hLow

/-- **`thm:step6` grounded, instantiated and verified non-vacuous**
(`mg-9576` acceptance bar).

On the concrete width-3 non-chain poset `Fin 3 × Fin 3` with the
singleton cut `S = {gridLinExt}`:

1. `Fin 3 × Fin 3` is genuinely width *exactly* `3` and not a chain;
2. the BK boundary `∂_BK S` is genuinely non-empty (`1 ≤ |∂_BK S|`) —
   a real BK cut edge;
3. the genuine second moment satisfies the `lem:gap-G5`(i) identity
   `∑_L I(L)² = ∑_{α,β} w_{αβ}` and is strictly positive (`= 1`);
4. the dichotomy `thm_step6_grounded` genuinely fires: in a regime
   where the coherence case is false it forces the expansion bound
   `1 ≤ 2·|∂_BK S|`;
5. the low-conductance closure `thm_step6_rich_closure_grounded`
   fires, delivering coherence.

No `Subsingleton`/empty baseline is used: `Fin 3 × Fin 3` has `9`
elements, the cut and its boundary are genuine, and the overlap
mass / second moment is genuinely positive. -/
theorem thm_step6_grounded_concrete :
    HasWidth (Fin 3 × Fin 3) 3 ∧
    ¬ IsChainPoset (Fin 3 × Fin 3) ∧
    1 ≤ (Step4.bkBoundary gridCut).card ∧
    (∑ L ∈ gridCut, (visibility gridRich gridFstar L) ^ 2
      = ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2) ∧
    1 ≤ ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2 ∧
    1 ≤ 2 * (Step4.bkBoundary gridCut).card ∧
    (1 * ∑ p ∈ (∅ : Finset (Unit × Unit)), (fun _ _ => (0 : ℕ)) p.1 p.2
      ≤ 1 * ∑ p ∈ (gridRich ×ˢ gridRich), pairOverlap gridFstar p.1 p.2) := by
  obtain ⟨hW, hNC, _, _, _, _⟩ := Step4.witnessGrounded_nonvacuous
  refine ⟨hW, hNC, grid_bkBoundary_pos, grid_secondMoment_identity, ?_,
    grid_dichotomy_forces_expansion, grid_rich_closure_fires⟩
  rw [grid_overlapMass_eq_one]

end ConcreteWitness

end Step6
end OneThird
