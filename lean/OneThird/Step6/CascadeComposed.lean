/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step6.PointwiseGrounded
import OneThird.Step1.Interface
import OneThird.Step5.Dichotomy

/-!
# Step 6 — the Steps 1-6 cascade composed end-to-end on a genuine S1 fiber

FULL REFACTOR Phase 2 — Checkpoint-2 follow-on, item 3 of 3 (`mg-496b`,
scoped by the S6-QA Checkpoint-2 audit `docs/state-S6-QA-Checkpoint2-Session1.md`
§6.1 item 3). This file is what **genuinely completes Piece 1**.

## What the S6-QA Checkpoint-2 audit rejected

The audit (`mg-e996`) found `cascade_steps_1_6_grounded`
(`Step6/PointwiseGrounded.lean`) consumable **only parametrically**: its
concrete witness `cascade_steps_1_6_grounded_concrete` uses
`pwFstar := fun _ => {gridLinExt}` — a **hand-built singleton** fiber,
not a fiber produced by Step 1's `thm_interface`. As the audit §5 put
it: *"It tests only that the arithmetic fires given a non-degenerate
`Fstar`."* A hand-built singleton would compile even if the genuine S1
good-fiber set were **empty** — which it provably was, before the
`mg-fc78` S1-G2 re-port (`interface_part_iv_faithfulness_defect`).

## What this file delivers — the un-fakeable satisfiability gate

`cascade_steps_1_6_grounded_genuine` re-does the concrete witness with
the **genuine S1 `thm_interface`-produced fiber**: the fiber family is

  `genFstar := fun _ : Bool => goodFiberSet a0 a1`

— `goodFiberSet`, the Step 1 good-fiber set of the rich pair `(a0, a1)`
on the concrete width-3 non-chain poset `Antichain3`. It is **not**
hand-built: `goodFiberSet a0 a1` is the genuine output of the
`def:good-fiber` re-port (`mg-fc78`), and the witness:

* genuinely invokes the assembled S1 interface theorem `thm_interface`,
  producing `InterfaceConclusion a0 a1`;
* genuinely consumes `interface_part_iv_goodFiber_nonempty` (the
  `mg-fc78` hard-gate theorem: `goodFiberSet a0 a1` is non-empty);
* feeds the genuine fiber through `cascade_steps_1_6_grounded` (which
  internally composes the S6 grounded producers
  `thm_step6_rich_closure_grounded_of_firstMoment` and
  `cor_pointwise_grounded`), and discharges `hfirst` through a genuine
  `Step5.Step5Richness` value (the S5 (R) first-moment-richness
  conclusion type) computed **from** the genuine fiber.

**This is un-fakeable.** Every positive quantity the witness asserts —
the overlap mass `M = 24`, the disagreement mass `12`, the `I²`-mass
`24` on the "mostly-disagreeing" set `A` — is a sum of
`pairOverlap genFstar`, hence a sum over `goodFiberSet a0 a1`. If
`goodFiberSet a0 a1` were empty (as it provably was pre-`mg-fc78`),
every one of those sums would be `0`, the asserted equalities
(`= 24`, `= 12`) would be false, and **this file would not compile**.
That is exactly the hard satisfiability gate the Checkpoint-2 audit
demanded: a compiler-checked genuine witness, not the parametric
fiction.

## The arithmetic on the genuine fiber

`Antichain3` has `6` linear extensions; the re-ported `def:good-fiber`
makes `goodFiberSet a0 a1 = 𝓛(Antichain3)` (all `6` — the good fiber's
coordinate image is the honest `2×2` square `{0,1}²`,
`interface_part_iv_goodFiber_nonempty`). Two rich interfaces (`Bool`,
`false`/`true`) carrying **opposite** Step-3 orientations both have
this genuine `6`-element fiber. Hence:

* every overlap weight `w_{αβ} = pairOverlap genFstar α β = 6`;
* the genuine overlap mass / second moment `M = ∑_{α,β} w = 4·6 = 24`;
* the genuine disagreement mass `∑_{Rich_disagree} w = 2·6 = 12`;
* the visibility at every `L` is `2`, the minority count `1`, so the
  "mostly-disagreeing" set `A` (threshold `t = 1/2`) is all of
  `𝓛(Antichain3)` and carries `I²`-mass `6·2² = 24`;
* `cascade_steps_1_6_grounded` fires, delivering Conclusion B
  `1·1·∑_A I² ≤ 2·(2·1·M)`, i.e. `24 ≤ 96`.
-/

namespace OneThird
namespace Step6

open Finset OneThird.Step5
open scoped BigOperators

/-! ## §C.1. The genuine S1 fiber and the cascade carrier data

`Antichain3` is the concrete width-3 non-chain poset of the S1 ports;
`(a0, a1)` its rich pair (`t = 1`). The carrier data below mirrors the
parametric `cascade_steps_1_6_grounded_concrete` of
`PointwiseGrounded.lean` exactly, with **one** change: the fiber family
`genFstar` is the genuine `goodFiberSet a0 a1`, not a hand-built
singleton. -/

section GenuineWitness

/-- Two rich interfaces, encoded by `Bool`. -/
abbrev genRich : Finset Bool := Finset.univ

/-- **The genuine S1 fiber family.** Both rich interfaces carry the
Step 1 good-fiber set `goodFiberSet a0 a1` of `Antichain3` — the
genuine `thm_interface` output, **not** a hand-built singleton. -/
noncomputable abbrev genFstar :
    Bool → Finset (LinearExt Antichain3) :=
  fun _ => goodFiberSet Antichain3.a0 Antichain3.a1

/-- The two interfaces carry **opposite** Step-3 orientations
(`σ false = +1`, `σ true = -1`) — a genuine incoherent pair. -/
abbrev genSign : Bool → Sign := fun b => b

/-- The universe of linear extensions of `Antichain3` — all `6`. -/
noncomputable abbrev genLP : Finset (LinearExt Antichain3) := Finset.univ

/-- A genuine singleton cut of `Antichain3` (the identity extension). -/
noncomputable abbrev genCut : Finset (LinearExt Antichain3) :=
  {Antichain3.extId}

/-- **The genuine fiber is all of `𝓛(Antichain3)`.** This is the
`mg-fc78` S1-G2 re-port payoff `goodFiberSet_a0_a1_eq_univ` — the exact
flip of the S1-E `goodFiberSet a0 a1 = ∅` refutation. Every numeric
fact below routes through this equation; were it `= ∅` instead (the
pre-`mg-fc78` state), this file would not compile. -/
theorem gen_fiber_eq (a : Bool) :
    genFstar a = (Finset.univ : Finset (LinearExt Antichain3)) :=
  Antichain3.goodFiberSet_a0_a1_eq_univ

/-- The genuine fiber has `6` elements (`= |𝓛(Antichain3)|`). -/
theorem gen_fiber_card (a : Bool) : (genFstar a).card = 6 := by
  rw [gen_fiber_eq a, Finset.card_univ]
  exact Antichain3.card_linExt

/-- Every linear extension lies in the genuine fiber (it is all of
`𝓛(Antichain3)`). -/
theorem gen_mem (L : LinearExt Antichain3) (a : Bool) : L ∈ genFstar a := by
  rw [gen_fiber_eq a]
  exact Finset.mem_univ L

/-! ## §C.2. The genuine overlap, disagreement and visibility data -/

/-- Every overlap weight on the genuine fiber is `w_{αβ} = 6`:
`|goodFiberSet a0 a1 ∩ goodFiberSet a0 a1| = |goodFiberSet a0 a1| = 6`. -/
theorem gen_pairOverlap (a b : Bool) : pairOverlap genFstar a b = 6 := by
  unfold pairOverlap
  rw [gen_fiber_eq a, Finset.inter_self, Finset.card_univ]
  exact Antichain3.card_linExt

/-- **The genuine second moment / overlap mass is `M = 24`.** All four
ordered pairs of the two interfaces overlap with weight `6`. Strictly
positive — and `0` if the fiber were empty. -/
theorem gen_M :
    ∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2 = 24 := by
  have h : ∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2
      = ∑ _p ∈ genRich ×ˢ genRich, (6 : ℕ) :=
    Finset.sum_congr rfl (fun p _ => gen_pairOverlap p.1 p.2)
  rw [h, Finset.sum_const, smul_eq_mul]
  decide

/-- **The genuine disagreement mass is `12`.** The two disagreeing
pairs `(false, true)` and `(true, false)`, each of overlap `6` — a real
incoherent pair on a real overlap. Strictly positive — and `0` if the
fiber were empty. -/
theorem gen_disagree_mass :
    ∑ p ∈ disagreePairs genRich genSign, pairOverlap genFstar p.1 p.2
      = 12 := by
  have h : ∑ p ∈ disagreePairs genRich genSign, pairOverlap genFstar p.1 p.2
      = ∑ _p ∈ disagreePairs genRich genSign, (6 : ℕ) :=
    Finset.sum_congr rfl (fun p _ => gen_pairOverlap p.1 p.2)
  rw [h, Finset.sum_const, smul_eq_mul]
  decide

/-- The genuine visibility at every `L` is `2`: both interfaces are
visible there (the genuine fiber contains every linear extension). -/
theorem gen_visibility (L : LinearExt Antichain3) :
    visibility genRich genFstar L = 2 := by
  unfold visibility
  have h : genRich.filter (fun a => L ∈ genFstar a) = genRich := by
    apply Finset.filter_true_of_mem
    intro a _
    exact gen_mem L a
  rw [h]
  decide

/-- The genuine positive count at every `L` is `1`: exactly one
interface (`false`) carries the `+1` orientation, and it is visible. -/
theorem gen_posCount (L : LinearExt Antichain3) :
    posCount genRich genFstar genSign L = 1 := by
  classical
  unfold posCount
  have h : genRich.filter (fun a => genSign a = false ∧ L ∈ genFstar a)
      = genRich.filter (fun a => a = false) := by
    apply Finset.filter_congr
    intro a _
    constructor
    · rintro ⟨h1, _⟩; exact h1
    · intro h1; exact ⟨h1, gen_mem L a⟩
  rw [h]
  decide

/-- The genuine negative count at every `L` is `1`: exactly one
interface (`true`) carries the `-1` orientation, and it is visible. -/
theorem gen_negCount (L : LinearExt Antichain3) :
    negCount genRich genFstar genSign L = 1 := by
  classical
  unfold negCount
  have h : genRich.filter (fun a => genSign a = true ∧ L ∈ genFstar a)
      = genRich.filter (fun a => a = true) := by
    apply Finset.filter_congr
    intro a _
    constructor
    · rintro ⟨h1, _⟩; exact h1
    · intro h1; exact ⟨h1, gen_mem L a⟩
  rw [h]
  decide

/-- The genuine minority count at every `L` is `1`: the two
opposite-signed interfaces are perfectly split. -/
theorem gen_minorityCount (L : LinearExt Antichain3) :
    minorityCount genRich genFstar genSign L = 1 := by
  unfold minorityCount
  rw [gen_posCount L, gen_negCount L]
  decide

/-- The "mostly-disagreeing" set `A` (threshold `t = 1/2`) is all of
`𝓛(Antichain3)`: the minority count `1` is exactly `1/2` of the
visibility `2` at every `L`. -/
theorem gen_A_eq :
    genLP.filter (fun L => 1 * visibility genRich genFstar L
        ≤ 2 * minorityCount genRich genFstar genSign L) = genLP := by
  apply Finset.filter_true_of_mem
  intro L _
  have hv := gen_visibility L
  have hm := gen_minorityCount L
  omega

/-- **The genuine `I²`-mass on the "mostly-disagreeing" set `A` is
`24`.** `A` is all `6` extensions, each of visibility `2`. Strictly
positive — and `0` if the fiber were empty. -/
theorem gen_A_sum :
    ∑ L ∈ genLP.filter (fun L => 1 * visibility genRich genFstar L
        ≤ 2 * minorityCount genRich genFstar genSign L),
      (visibility genRich genFstar L) ^ 2 = 24 := by
  rw [gen_A_eq]
  have h : ∑ L ∈ genLP, (visibility genRich genFstar L) ^ 2
      = ∑ _L ∈ genLP, (4 : ℕ) :=
    Finset.sum_congr rfl (fun L _ => by rw [gen_visibility L]; decide)
  rw [h, Finset.sum_const, smul_eq_mul,
      show genLP.card = 6 from by
        rw [Finset.card_univ]; exact Antichain3.card_linExt]

/-- The genuine first-moment fiber sum is `∑_α |F⋆_α| = 12`. -/
theorem gen_fiberSum : ∑ a ∈ genRich, (genFstar a).card = 12 := by
  have h : ∑ a ∈ genRich, (genFstar a).card = ∑ _a ∈ genRich, (6 : ℕ) :=
    Finset.sum_congr rfl (fun a _ => gen_fiber_card a)
  rw [h, Finset.sum_const, smul_eq_mul]
  decide

/-- The universe `genLP` has `6` linear extensions. -/
theorem gen_LP_card : genLP.card = 6 := by
  rw [Finset.card_univ]
  exact Antichain3.card_linExt

/-! ## §C.3. The genuine Step 5 (R) first-moment richness

`hfirst` of `cascade_steps_1_6_grounded` is, definitionally, a
`Step5.Step5Richness` — the cleared-denominator (R) conclusion of
`thm:step5` (`Step5/Dichotomy.lean`: `Step5Richness LP fiberSum c_R`
is `c_R * LP ≤ fiberSum`). `gen_step5_richness` constructs that S5
conclusion value **from the genuine fiber**: `c_R = 1`, `|LP| = 6`,
`fiberSum = ∑_α |F⋆_α| = 12`, so `1·6 ≤ 12`. It is then fed directly
as the cascade's `hfirst` — the genuine S5 → S6 wire on the genuine
fiber, replacing the free hypothesis. -/
theorem gen_step5_richness :
    Step5.Step5Richness genLP.card
      (∑ a ∈ genRich, (genFstar a).card) 1 := by
  change 1 * genLP.card ≤ ∑ a ∈ genRich, (genFstar a).card
  rw [gen_LP_card, gen_fiberSum]
  decide

/-! ## §C.4. The end-to-end genuine cascade witness -/

/-- **The Steps 1-6 cascade composed end-to-end on the genuine S1
fiber — the compiler-checked satisfiability gate** (`mg-496b`,
Checkpoint-2 follow-on item 3; the genuine completion of Piece 1).

On the concrete width-3 non-chain poset `Antichain3` with the rich pair
`(a0, a1)` and two opposite-signed rich interfaces whose fibers are the
**genuine S1 `thm_interface`-produced good-fiber set** `goodFiberSet a0
a1` (re-ported by `mg-fc78`):

1. `Antichain3` is genuinely width *exactly* `3` and not a chain;
2. the assembled S1 interface theorem `thm_interface` **fires**,
   producing the four-part `InterfaceConclusion a0 a1`;
3. the genuine good-fiber set is **non-empty**
   (`interface_part_iv_goodFiber_nonempty`, the `mg-fc78` hard gate);
4. the genuine overlap mass / second moment is `M = 24`, strictly
   positive — a sum of `pairOverlap genFstar`, hence over
   `goodFiberSet a0 a1`;
5. the genuine disagreement mass is `12`, strictly positive — a real
   incoherent pair on a real overlap;
6. the genuine `I²`-mass on the "mostly-disagreeing" set `A` is `24`;
7. `cascade_steps_1_6_grounded` **fires on the genuine fiber**,
   assembling the whole Steps 1-6 cascade (genuine S1 fiber → S5 (R)
   first-moment richness `gen_step5_richness` → the S6 grounded
   producers internal to the cascade → Conclusion B):
   `1·1·∑_A I² ≤ 2·(2·1·M)`, i.e. `24 ≤ 96`.

**Un-fakeable.** Conjuncts 4, 5, 6 each claim a *strictly positive*
value (`24`, `12`, `24`) for a sum of `pairOverlap genFstar` — a sum
over the genuine fiber `goodFiberSet a0 a1`. Were `goodFiberSet a0 a1`
empty (its provable state before the `mg-fc78` S1-G2 re-port,
`interface_part_iv_faithfulness_defect`), each sum would be `0`, the
equalities would be false, and this theorem would **not compile**. A
hand-built singleton fiber (the parametric fiction the Checkpoint-2
audit rejected) would compile regardless of the genuine fiber's
emptiness; this witness does not. -/
theorem cascade_steps_1_6_grounded_genuine :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    InterfaceConclusion Antichain3.a0 Antichain3.a1 ∧
    (goodFiberSet Antichain3.a0 Antichain3.a1).Nonempty ∧
    (∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2 = 24) ∧
    (∑ p ∈ disagreePairs genRich genSign,
        pairOverlap genFstar p.1 p.2 = 12) ∧
    (∑ L ∈ genLP.filter (fun L => 1 * visibility genRich genFstar L
          ≤ 2 * minorityCount genRich genFstar genSign L),
        (visibility genRich genFstar L) ^ 2 = 24) ∧
    (1 * 1 * ∑ L ∈ genLP.filter (fun L => 1 * visibility genRich genFstar L
          ≤ 2 * minorityCount genRich genFstar genSign L),
        (visibility genRich genFstar L) ^ 2
      ≤ 2 * (2 * 1 * (∑ p ∈ genRich ×ˢ genRich,
          pairOverlap genFstar p.1 p.2))) := by
  refine ⟨Antichain3.hasWidth, Antichain3.not_isChainPoset, ?_, ?_,
    gen_M, gen_disagree_mass, gen_A_sum, ?_⟩
  · -- Genuine S1: the assembled `thm_interface` fires at `(a0, a1)`.
    exact thm_interface Antichain3.hasWidthAtMost 1
      Antichain3.a0 Antichain3.a1 Antichain3.isRich_a0_a1
  · -- The genuine fiber is non-empty: the `mg-fc78` hard gate.
    exact (Antichain3.interface_part_iv_goodFiber_nonempty).2.2.2.1
  · -- Conclusion B, end-to-end on the genuine fiber.
    set B := (Step4.bkBoundary genCut).card with hBdef
    -- `hsub`: the genuine fiber lies inside the universe.
    have hsub : ∀ a ∈ genRich, genFstar a ⊆ genLP :=
      fun a _ => Finset.subset_univ (genFstar a)
    -- `hvol`: the cut is no larger than the universe.
    have hvol : genCut.card ≤ genLP.card := by
      rw [show genCut.card = 1 from by simp [genCut], gen_LP_card]
      decide
    -- G9: the summed Step-4 bound holds trivially (no bad active pairs;
    -- all disagreement mass is non-active — the active/non-active split
    -- of `step6.tex:646-649`).
    have hSum : (B + 1) * ∑ p ∈ (∅ : Finset (Bool × Bool)),
          (fun _ _ => (0 : ℕ)) p.1 p.2
        ≤ 1 * 1 * (Step4.bkBoundary genCut).card := by
      simp
    -- Low conductance: `B < B + 1`.
    have hLow : 1 * 1 * 1 * (Step4.bkBoundary genCut).card
        < (B + 1) * 1 * (1 : ℕ) ^ 2 * genCut.card := by
      have hcard : genCut.card = 1 := by simp [genCut]
      rw [hcard, ← hBdef]
      ring_nf
      omega
    have hbadW : ∀ p ∈ (∅ : Finset (Bool × Bool)),
        (fun _ _ => (0 : ℕ)) p.1 p.2 = pairOverlap genFstar p.1 p.2 :=
      fun p hp => absurd hp (by simp)
    have hbadSub : (∅ : Finset (Bool × Bool))
        ⊆ disagreePairs genRich genSign :=
      Finset.empty_subset _
    -- The genuine non-active disagreement mass `12` is a `δ`-fraction
    -- of `M = 24`.
    have hNonActive : (1 : ℕ) * (∑ p ∈ disagreePairs genRich genSign
          \ (∅ : Finset (Bool × Bool)), pairOverlap genFstar p.1 p.2)
        ≤ 1 * (∑ p ∈ genRich ×ˢ genRich, pairOverlap genFstar p.1 p.2) := by
      rw [Finset.sdiff_empty, gen_disagree_mass, gen_M]
      decide
    -- The genuine cascade fires: S1 fiber → S5 (R) richness → S6 → B.
    exact cascade_steps_1_6_grounded genCut genLP genRich genFstar genSign
      (∅ : Finset (Bool × Bool)) (fun _ _ => 0) 1 (B + 1) 1 1 1 1 1 2
      hsub gen_step5_richness hvol hSum hLow hbadW hbadSub hNonActive

end GenuineWitness

end Step6
end OneThird
