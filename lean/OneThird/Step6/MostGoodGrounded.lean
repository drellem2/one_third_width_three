/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step6.DichotomyGrounded
import OneThird.Step2.PerFiberGrounded2

/-!
# Step 6 — G6 `lem:most-good` grounded, and the S2 `ε₂` bookkeeping wired in

FULL REFACTOR Phase 2 — Checkpoint-2 follow-on (`mg-aa02`, item 2 of 3;
gated by `mg-fc78` item 1).  The S6-QA Checkpoint-2 audit
(`docs/state-S6-QA-Checkpoint2-Session1.md` §3.1) found **two**
unfinished pieces of Step 6 grounding:

* **G6 (`lem:most-good`) was abstract-only.**  The cleared-denominator
  `lem_most_good` (`Step6/Assembly.lean`) was never grounded onto
  genuine Bubble–Karzanov-graph data — the grounded dichotomy chain
  (`DichotomyGrounded.lean`) starts at G9, skipping G6 entirely.
* **The S2 `ε₂` bookkeeping wired into zero Step 6 files.**  S2-B
  (`docs/state-S2-B-Session1.md` §2/§4) *explicitly deferred* the
  `ε₂ ↔ C₂'` reconciliation to Checkpoint 2: `ε₂` (the
  `fiberStaircaseRate` of `Step2/PerFiberGrounded2.lean`) appeared in
  no Step 6 file, and the Step 6 `badSet`/`richStar` split was an
  opaque parameter disconnected from the staircase error it must be
  produced by.

This file closes both.

## §M.1 — the `S`-good classification

`step6.tex` `def:S-good` (`step6.tex:148-152`): an interface `α` is
`S`-good iff Step 2 applies to `F_α` with error at most `ε₂`, i.e.
`|B_α| ≤ ε₂·|F_α|` where `B_α` is the per-fiber exceptional set.
`sGoodInterfaces ε₂ richSet Fstar excSize` is exactly this split,
computed as a `Finset.filter` on the explicit `ε₂` threshold — so the
Markov antecedent `hBadMass` of the abstract `lem_most_good` is
**derived** here, not assumed.

## §M.2 — G6 `lem:most-good` grounded on the BK boundary

`lem_most_good_grounded` is the `step6.tex:154` Markov argument run on
the **genuine BK boundary** `globalBKBdy S` (`Step2/PerFiberGrounded2`,
the directed `∂_BK S` of `bkGraph α`).  From the summed Step-2 error
`∑_α |B_α| ≤ C₂'·|∂_BK S|` (`step6.tex` `eq:step2-summed`) and the
low-conductance hypothesis `|∂_BK S| ≤ Φ₀·vol(S)`, it concludes the
bad-interface mass bound `ε₂·∑_{Rich∖Rich⋆}|F_α| ≤ C₂'·Φ₀·vol(S)`.
`lem_most_good_grounded_good_mass` is the equivalent `(1-o(1))`
good-mass form.

## §M.3 — the S2 `ε₂` wire (the `ε₂ ↔ C₂'` reconciliation)

`lem_most_good_grounded_step2` performs the reconciliation S2-B §2
deferred.  Every **boundary-good** fiber of `step2.tex`
(`goodFibers Fam S η`, the fibers with `|∂_BK(S∩fib)| ≤ η·|fib|`) is
an **`S`-good** interface (`|B_α| ≤ ε₂·|F_α|`): this is the genuine
reconciliation — boundary-good ⇒ error-good.  Hence the `ε₂`-error-bad
interfaces `Rich ∖ Rich⋆` are contained in the `η`-boundary-bad fibers
`badFibers Fam S η`, and the G6 bad-mass bound follows from S2's own
`prop_per_fiber_bad_mass`, with the constant `K·κ/η` — exactly the
constant S2-B §2 named opposite `step6.tex`'s `C₂'`.

`lem_most_good_grounded_of_thm_step2` makes the wire end-to-end: it
consumes `step2.tex` `thm:step2` directly — clause (ii) supplies, for
every boundary-good fiber, a monotone staircase whose
symmetric-difference exceptional set `B_r` satisfies
`|B_r| ≤ ε₂·|D_r|` with `ε₂` the uniform `fiberStaircaseRate` bound —
and the grid bijection `fiberGrid_card` converts `|D_r|` to `|F_r|`.
So `fiberStaircaseRate` / `ε₂` now genuinely thread into the Step 6
per-fiber aggregation.

## Non-vacuity

* `lem_most_good_grounded_nonvacuous` — G6 fires at the genuine
  width-3 non-chain grid poset `Fin 3 × Fin 3` with a genuine
  non-empty BK boundary and a genuinely **error-bad** interface
  (`Rich ∖ Rich⋆` non-empty).
* `lem_most_good_step2_nonvacuous` — the full S2 wire fires at the
  genuine width-3 non-chain poset `Antichain3`: `thm:step2` is
  genuinely consumed, the uniform error rate `ε₂` is the genuine
  `fiberStaircaseRate 1 1 1 1`, and the genuine rich-fiber family
  `antichain3Family` is classified.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace OneThird
namespace Step6

open Finset
open scoped BigOperators
open OneThird.Step2.PerFiberGrounded

/-! ## §M.1. The `S`-good interface classification (`step6.tex` `def:S-good`) -/

section SGood

variable {Pair : Type*} [DecidableEq Pair]
variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **`step6.tex` `def:S-good` (`step6.tex:148-152`).**

An interface `a` is `S`-good iff Step 2's per-fiber exceptional set
`B_a` is small relative to the good fiber `F_a`: `|B_a| ≤ ε₂·|F_a|`.
`excSize a` is the cardinality `|B_a|` of the exceptional set (a
`Finset` of grid cells in the concrete Step-2 staircase; only its
mass enters `lem:most-good`); `Fstar a` is the good fiber `F_a`. -/
def IsSGood (ε₂ : ℚ) (Fstar : Pair → Finset (LinearExt α))
    (excSize : Pair → ℕ) (a : Pair) : Prop :=
  ((excSize a : ℚ)) ≤ ε₂ * ((Fstar a).card : ℚ)

instance instDecidableIsSGood (ε₂ : ℚ) (Fstar : Pair → Finset (LinearExt α))
    (excSize : Pair → ℕ) (a : Pair) : Decidable (IsSGood ε₂ Fstar excSize a) :=
  inferInstanceAs (Decidable ((excSize a : ℚ) ≤ ε₂ * ((Fstar a).card : ℚ)))

/-- **The `S`-good rich interfaces `Rich⋆` (`step6.tex:151`).**

The subset of `richSet` whose interfaces are `S`-good.  This is the
explicit `ε₂`-threshold split — the Step-6 per-fiber aggregation that
*produces* `Rich⋆` from the Step-2 error data, computed rather than
assumed. -/
def sGoodInterfaces (ε₂ : ℚ) (richSet : Finset Pair)
    (Fstar : Pair → Finset (LinearExt α)) (excSize : Pair → ℕ) :
    Finset Pair :=
  richSet.filter (fun a => IsSGood ε₂ Fstar excSize a)

theorem mem_sGoodInterfaces {ε₂ : ℚ} {richSet : Finset Pair}
    {Fstar : Pair → Finset (LinearExt α)} {excSize : Pair → ℕ} {a : Pair} :
    a ∈ sGoodInterfaces ε₂ richSet Fstar excSize ↔
      a ∈ richSet ∧ ((excSize a : ℚ) ≤ ε₂ * ((Fstar a).card : ℚ)) := by
  unfold sGoodInterfaces IsSGood
  rw [Finset.mem_filter]

theorem sGoodInterfaces_subset (ε₂ : ℚ) (richSet : Finset Pair)
    (Fstar : Pair → Finset (LinearExt α)) (excSize : Pair → ℕ) :
    sGoodInterfaces ε₂ richSet Fstar excSize ⊆ richSet :=
  Finset.filter_subset _ _

/-- **The Markov antecedent, derived.**  An interface in
`Rich ∖ Rich⋆` genuinely fails the `S`-good test: `ε₂·|F_a| < |B_a|`.
This is the `hBadMass` hypothesis the abstract `Step6.lem_most_good`
takes as a free parameter — here it is a *consequence* of the explicit
`ε₂` split. -/
theorem lt_excSize_of_mem_sdiff {ε₂ : ℚ} {richSet : Finset Pair}
    {Fstar : Pair → Finset (LinearExt α)} {excSize : Pair → ℕ} {a : Pair}
    (ha : a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize) :
    ε₂ * ((Fstar a).card : ℚ) < (excSize a : ℚ) := by
  rw [Finset.mem_sdiff, mem_sGoodInterfaces] at ha
  obtain ⟨hrich, hnot⟩ := ha
  exact not_le.mp (fun h => hnot ⟨hrich, h⟩)

end SGood

/-! ## §M.2. G6 `lem:most-good` grounded on the BK boundary -/

section MostGood

variable {Pair : Type*} [DecidableEq Pair]
variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **G6 — `lem:most-good`, grounded on the BK boundary**
(`step6.tex:154-167`).

Let `S ⊆ 𝓛(P)` be a cut, `richSet` the rich interfaces with good
fibers `Fstar` and per-fiber exceptional masses `excSize` (`|B_α|`).
Write `Rich⋆ = sGoodInterfaces ε₂ …` for the `S`-good split.  Given

* the **summed Step-2 error** (`step6.tex` `eq:step2-summed`)
  `∑_{α ∈ Rich} |B_α| ≤ C₂'·|∂_BK S|`, on the genuine directed BK
  boundary `globalBKBdy S` of `bkGraph α`, and
* the **low-conductance hypothesis** `|∂_BK S| ≤ Φ₀·vol(S)`
  (with `vol(S) = |S|`),

the bad-interface mass is `o(1)` of the volume:

  `ε₂ · ∑_{α ∈ Rich ∖ Rich⋆} |F_α| ≤ C₂' · Φ₀ · vol(S)`.

This is the cleared-denominator form of `step6.tex:194-227`'s
`∑_{Rich^bad}|F_α| < ε₂⁻¹ C₂' Φ₀ vol(S)` — the Markov inequality
applied fiberwise.  Unlike the abstract `Step6.lem_most_good`, the
`hBadMass` antecedent is *derived* from the explicit `ε₂` split
(`lt_excSize_of_mem_sdiff`), not assumed. -/
theorem lem_most_good_grounded
    (S : Finset (LinearExt α))
    (richSet : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (excSize : Pair → ℕ) (C₂' Φ₀ ε₂ : ℚ)
    (hC₂' : 0 ≤ C₂')
    (hStep2 : (∑ a ∈ richSet, (excSize a : ℚ))
                ≤ C₂' * ((globalBKBdy S).card : ℚ))
    (hΦ : ((globalBKBdy S).card : ℚ) ≤ Φ₀ * (S.card : ℚ)) :
    ε₂ * (∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
            ((Fstar a).card : ℚ))
      ≤ C₂' * Φ₀ * (S.card : ℚ) := by
  classical
  -- Markov, fiberwise: on `Rich ∖ Rich⋆`, `ε₂·|F_a| ≤ |B_a|`.
  have hmarkov :
      ε₂ * (∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
              ((Fstar a).card : ℚ))
        ≤ ∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
              (excSize a : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact le_of_lt (lt_excSize_of_mem_sdiff ha)
  -- The bad-set error mass is at most the total error mass.
  have hsub :
      (∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
          (excSize a : ℚ))
        ≤ ∑ a ∈ richSet, (excSize a : ℚ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro a _ _
    positivity
  -- Chain: ε₂·∑_bad|F| ≤ ∑_bad|B| ≤ ∑_Rich|B| ≤ C₂'·|∂S| ≤ C₂'·Φ₀·vol(S).
  calc ε₂ * (∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
              ((Fstar a).card : ℚ))
      ≤ ∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
            (excSize a : ℚ) := hmarkov
    _ ≤ ∑ a ∈ richSet, (excSize a : ℚ) := hsub
    _ ≤ C₂' * ((globalBKBdy S).card : ℚ) := hStep2
    _ ≤ C₂' * (Φ₀ * (S.card : ℚ)) := mul_le_mul_of_nonneg_left hΦ hC₂'
    _ = C₂' * Φ₀ * (S.card : ℚ) := by ring

/-- **G6 — `lem:most-good`, the `(1-o(1))` good-mass form**
(`step6.tex:163-167`, `step6.tex:228-230`).

The dual of `lem_most_good_grounded`: the `S`-good interfaces carry
*almost all* of the rich-interface mass,

  `ε₂ · ∑_{α ∈ Rich} |F_α| − C₂' · Φ₀ · vol(S)
      ≤ ε₂ · ∑_{α ∈ Rich⋆} |F_α|`.

As `Φ₀ → 0` the deficit `C₂'·Φ₀·vol(S)` vanishes, recovering the
paper's `∑_{Rich⋆}|F_α| ≥ (1-o(1))∑_{Rich}|F_α|`. -/
theorem lem_most_good_grounded_good_mass
    (S : Finset (LinearExt α))
    (richSet : Finset Pair) (Fstar : Pair → Finset (LinearExt α))
    (excSize : Pair → ℕ) (C₂' Φ₀ ε₂ : ℚ)
    (hC₂' : 0 ≤ C₂')
    (hStep2 : (∑ a ∈ richSet, (excSize a : ℚ))
                ≤ C₂' * ((globalBKBdy S).card : ℚ))
    (hΦ : ((globalBKBdy S).card : ℚ) ≤ Φ₀ * (S.card : ℚ)) :
    ε₂ * (∑ a ∈ richSet, ((Fstar a).card : ℚ)) - C₂' * Φ₀ * (S.card : ℚ)
      ≤ ε₂ * (∑ a ∈ sGoodInterfaces ε₂ richSet Fstar excSize,
                ((Fstar a).card : ℚ)) := by
  have hbad := lem_most_good_grounded S richSet Fstar excSize C₂' Φ₀ ε₂
    hC₂' hStep2 hΦ
  have hsplit :
      (∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
          ((Fstar a).card : ℚ))
        + (∑ a ∈ sGoodInterfaces ε₂ richSet Fstar excSize,
            ((Fstar a).card : ℚ))
        = ∑ a ∈ richSet, ((Fstar a).card : ℚ) :=
    Finset.sum_sdiff (sGoodInterfaces_subset ε₂ richSet Fstar excSize)
  have hdistrib :
      ε₂ * (∑ a ∈ richSet, ((Fstar a).card : ℚ))
        = ε₂ * (∑ a ∈ richSet \ sGoodInterfaces ε₂ richSet Fstar excSize,
                  ((Fstar a).card : ℚ))
          + ε₂ * (∑ a ∈ sGoodInterfaces ε₂ richSet Fstar excSize,
                  ((Fstar a).card : ℚ)) := by
    rw [← mul_add, hsplit]
  linarith [hbad, hdistrib]

end MostGood

/-! ## §M.3. The S2 `ε₂` wire — the `ε₂ ↔ C₂'` reconciliation -/

section Step2Wire

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **G6 wired to the S2 `ε₂` bookkeeping** (`step6.tex:154` ∘
`step2.tex` `prop:per-fiber`; the `ε₂ ↔ C₂'` reconciliation S2-B §2
deferred to Checkpoint 2).

The genuine reconciliation: every **boundary-good** fiber of
`step2.tex` (`goodFibers Fam S η`, the fibers with
`|∂_BK(S∩fib)| ≤ η·|fib|`) is an **`S`-good** interface of
`step6.tex` (`|B_α| ≤ ε₂·|F_α|`).  This is the hypothesis `hexc` — it
is exactly what `thm:step2` clause (ii) delivers (see
`lem_most_good_grounded_of_thm_step2`).  Consequently the
`ε₂`-error-bad interfaces `Rich ∖ Rich⋆` are contained in the
`η`-boundary-bad fibers `badFibers Fam S η`, and the G6 bad-mass
bound is S2's own `prop_per_fiber_bad_mass`:

  `∑_{r ∈ Rich ∖ Rich⋆} |F_r| ≤ K · κ · |S| / η`.

So the Step-6 `C₂'`-style bad-mass bound is, in the grounded port,
the S2 constant `K·κ/η` — the reconciliation S2-B §2 named. -/
theorem lem_most_good_grounded_step2
    (Fam : RichFamily α) (S : Finset (LinearExt α))
    {K : ℕ} {κ η ε₂ : ℚ} (hη : 0 < η)
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ))
    (excSize : α × α → ℕ)
    (hexc : ∀ r ∈ goodFibers Fam S η,
      ((excSize r : ℚ)) ≤ ε₂ * ((Fam.fib r).card : ℚ)) :
    (∑ r ∈ Fam.carrier \ sGoodInterfaces ε₂ Fam.carrier Fam.fib excSize,
        ((Fam.fib r).card : ℚ))
      ≤ (K : ℚ) * κ * (S.card : ℚ) / η := by
  classical
  -- The reconciliation: error-bad ⊆ boundary-bad.
  have hcontain :
      Fam.carrier \ sGoodInterfaces ε₂ Fam.carrier Fam.fib excSize
        ⊆ badFibers Fam S η := by
    intro r hr
    rw [Finset.mem_sdiff, mem_sGoodInterfaces] at hr
    obtain ⟨hrc, hnot⟩ := hr
    by_contra hbad
    -- `r ∉ badFibers` and `r ∈ carrier` ⇒ `r` is boundary-good.
    have hgood : r ∈ goodFibers Fam S η := by
      rw [goodFibers_eq_sdiff, Finset.mem_sdiff]
      exact ⟨hrc, hbad⟩
    -- boundary-good ⇒ error-good, contradicting `r ∉ Rich⋆`.
    exact hnot ⟨hrc, hexc r hgood⟩
  calc (∑ r ∈ Fam.carrier \ sGoodInterfaces ε₂ Fam.carrier Fam.fib excSize,
          ((Fam.fib r).card : ℚ))
      ≤ ∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hcontain
        intro r _ _
        positivity
    _ ≤ (K : ℚ) * κ * (S.card : ℚ) / η :=
        prop_per_fiber_bad_mass Fam S hη hmult hcond

/-- **G6 wired end-to-end to `thm:step2` — the explicit
`fiberStaircaseRate` / `ε₂` consumption** (`step6.tex:154` ∘
`step2.tex` `thm:step2`).

This consumes `step2.tex` `thm:step2` directly.  Clause (ii) of
`thm:step2` supplies, for every boundary-good fiber `r`, a monotone
staircase `M_r` whose symmetric-difference exceptional set
`B_r = A_r △ M_r` satisfies `|B_r| ≤ ε₂·|D_r|`, where `ε₂` is the
uniform `fiberStaircaseRate` upper bound (`huniform`).  The grid
bijection `fiberGrid_card` (valid on a constant-sign good fiber)
converts `|D_r|` to `|F_r|`, so every boundary-good fiber is `S`-good,
discharging the `hexc` hypothesis of `lem_most_good_grounded_step2`.

This is the wire the S6-QA Checkpoint-2 audit (§3.1) found missing:
`ε₂` / `fiberStaircaseRate` now threads from `thm:step2` into the
Step 6 per-fiber aggregation. -/
theorem lem_most_good_grounded_of_thm_step2
    (Fam : RichFamily α) (S : Finset (LinearExt α))
    {c : ℚ} {K : ℕ} {κ η ε₂ : ℚ} (hc : 0 < c) (hη : 0 < η)
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ))
    (ht : ∀ r ∈ goodFibers Fam S η, 1 ≤ commonNbhdLength r.1 r.2)
    (hmass : ∀ r ∈ goodFibers Fam S η,
      c * (commonNbhdLength r.1 r.2 : ℚ) ^ 2
        ≤ ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ))
    (huniform : ∀ r ∈ goodFibers Fam S η,
      fiberStaircaseRate c η (Fam.fib r).card
          (commonNbhdLength r.1 r.2) ≤ ε₂) :
    ∃ excSize : α × α → ℕ,
      (∀ r ∈ goodFibers Fam S η,
        ((excSize r : ℚ)) ≤ ε₂ * ((Fam.fib r).card : ℚ)) ∧
      (∑ r ∈ Fam.carrier \ sGoodInterfaces ε₂ Fam.carrier Fam.fib excSize,
          ((Fam.fib r).card : ℚ))
        ≤ (K : ℚ) * κ * (S.card : ℚ) / η := by
  classical
  -- `thm:step2` clause (ii): a staircase, per boundary-good fiber.
  have hstair := (thm_step2 Fam S hc hη hmult hcond ht hmass huniform).2
  -- Make the per-fiber existential unconditional, then choose.
  have hstair' : ∀ r : α × α, ∃ M : Finset (ℤ × ℤ),
      r ∈ goodFibers Fam S η →
        ((symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) M).card : ℚ)
          ≤ ε₂ * ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ) := by
    intro r
    by_cases hr : r ∈ goodFibers Fam S η
    · obtain ⟨M, _, hM⟩ := hstair r hr
      exact ⟨M, fun _ => hM⟩
    · exact ⟨∅, fun h => absurd h hr⟩
  choose Mfun hMfun using hstair'
  -- The genuine per-fiber exceptional mass `|B_r| = |A_r △ M_r|`.
  refine ⟨fun r => (symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) (Mfun r)).card,
    ?_, ?_⟩
  · -- Every boundary-good fiber is `S`-good (the grid bijection).
    intro r hr
    have hrc : r ∈ Fam.carrier := goodFibers_subset Fam S η hr
    have hgrid : (fiberGrid r.1 r.2 (Fam.fib r)).card = (Fam.fib r).card :=
      fiberGrid_card (Fam.good r hrc) (Fam.signConst r hrc)
    calc (((symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) (Mfun r)).card : ℚ))
        ≤ ε₂ * ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ) := hMfun r hr
      _ = ε₂ * ((Fam.fib r).card : ℚ) := by rw [hgrid]
  · -- The G6 bad-mass bound, via the reconciliation.
    refine lem_most_good_grounded_step2 Fam S hη hmult hcond
      (fun r => (symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) (Mfun r)).card)
      ?_
    intro r hr
    have hrc : r ∈ Fam.carrier := goodFibers_subset Fam S η hr
    have hgrid : (fiberGrid r.1 r.2 (Fam.fib r)).card = (Fam.fib r).card :=
      fiberGrid_card (Fam.good r hrc) (Fam.signConst r hrc)
    calc (((symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) (Mfun r)).card : ℚ))
        ≤ ε₂ * ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ) := hMfun r hr
      _ = ε₂ * ((Fam.fib r).card : ℚ) := by rw [hgrid]

end Step2Wire

/-! ## §M.4. Non-vacuity — G6 grounded fires at concrete width-3 posets -/

section ConcreteWitness

/-- The genuine directed BK boundary of the concrete grid cut
`S = {gridLinExt}` is non-empty: a real directed BK cut edge,
extracted from the S6-A non-vacuity witness `grid_bkBoundary_pos`. -/
theorem globalBKBdy_gridCut_nonempty :
    (globalBKBdy gridCut).Nonempty := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp grid_bkBoundary_pos
  obtain ⟨L, L', rfl, hadj⟩ := Step4.bkAdj_of_mem_bkBoundary he
  rw [Step4.mem_bkBoundary] at he
  rcases he.2 with ⟨hLS, hL'S⟩ | ⟨hLS, hL'S⟩
  · exact ⟨(L, L'), mem_globalBKBdy.mpr ⟨⟨hLS, hL'S⟩, hadj⟩⟩
  · exact ⟨(L', L), mem_globalBKBdy.mpr ⟨⟨hL'S, hLS⟩, hadj.symm⟩⟩

/-- **G6 `lem:most-good` grounded, instantiated and verified
non-vacuous** (`mg-aa02` acceptance bar, Route A).

On the genuine width-3 non-chain grid poset `Fin 3 × Fin 3` with the
singleton cut `S = {gridLinExt}`:

1. `Fin 3 × Fin 3` is genuinely width *exactly* `3` and not a chain;
2. the directed BK boundary `∂_BK S` is genuinely non-empty — a real
   directed BK cut edge;
3. with one rich interface carrying a genuine non-empty good fiber
   `{gridLinExt}` and one genuine unit of exceptional mass, the
   `S`-good split at threshold `ε₂ = 1/2` classifies the interface as
   **bad** — `Rich ∖ Rich⋆` is genuinely **non-empty**;
4. `lem_most_good_grounded` genuinely fires, delivering the bad-mass
   bound `(1/2)·∑_{Rich∖Rich⋆}|F_α| ≤ C₂'·Φ₀·vol(S)`.

No `Subsingleton`/empty baseline: the poset has 9 elements, the BK
boundary is a genuine non-empty edge set, the fiber and exceptional
set are genuine non-empty finsets, and the bad-interface set is
genuinely non-empty — this exercises the Markov core of G6, not a
`0 ≤ 0` degeneracy. -/
theorem lem_most_good_grounded_nonvacuous :
    HasWidth (Fin 3 × Fin 3) 3 ∧
    ¬ IsChainPoset (Fin 3 × Fin 3) ∧
    1 ≤ (globalBKBdy gridCut).card ∧
    ((Finset.univ : Finset Unit)
      \ sGoodInterfaces (1/2 : ℚ) (Finset.univ : Finset Unit)
          (fun _ => ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3))))
          (fun _ => 1)).Nonempty ∧
    ((1/2 : ℚ)
        * (∑ a ∈ (Finset.univ : Finset Unit)
            \ sGoodInterfaces (1/2 : ℚ) (Finset.univ : Finset Unit)
                (fun _ => ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3))))
                (fun _ => 1),
            (((fun _ => ({gridLinExt} :
                  Finset (LinearExt (Fin 3 × Fin 3)))) a).card : ℚ))
      ≤ ((globalBKBdy gridCut).card : ℚ)
          * ((globalBKBdy gridCut).card : ℚ) * (gridCut.card : ℚ)) := by
  classical
  obtain ⟨hW, hNC, _, _, _, _⟩ := Step4.witnessGrounded_nonvacuous
  have hBpos : 1 ≤ (globalBKBdy gridCut).card :=
    Finset.card_pos.mpr globalBKBdy_gridCut_nonempty
  have hBℚ : (1 : ℚ) ≤ ((globalBKBdy gridCut).card : ℚ) := by exact_mod_cast hBpos
  set Fstar : Unit → Finset (LinearExt (Fin 3 × Fin 3)) :=
    fun _ => {gridLinExt} with hFstar
  set excSize : Unit → ℕ := fun _ => 1 with hexcSize
  -- The single interface is genuinely bad: `Rich ∖ Rich⋆` is non-empty.
  have hbadne :
      ((Finset.univ : Finset Unit)
        \ sGoodInterfaces (1/2 : ℚ) (Finset.univ : Finset Unit)
            Fstar excSize).Nonempty := by
    refine ⟨(), ?_⟩
    rw [Finset.mem_sdiff, mem_sGoodInterfaces]
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro ⟨-, hle⟩
    simp only [hFstar, hexcSize, Finset.card_singleton] at hle
    norm_num at hle
  refine ⟨hW, hNC, hBpos, hbadne, ?_⟩
  -- `lem_most_good_grounded` fires; discharge its two cascade inputs.
  have hsum : (∑ a ∈ (Finset.univ : Finset Unit), (excSize a : ℚ)) = 1 := by
    simp [hexcSize]
  have hStep2 :
      (∑ a ∈ (Finset.univ : Finset Unit), (excSize a : ℚ))
        ≤ (((globalBKBdy gridCut).card : ℚ))
            * ((globalBKBdy gridCut).card : ℚ) := by
    rw [hsum]
    nlinarith [hBℚ]
  have hΦ :
      ((globalBKBdy gridCut).card : ℚ)
        ≤ ((globalBKBdy gridCut).card : ℚ) * (gridCut.card : ℚ) := by
    have : (gridCut.card : ℚ) = 1 := by
      simp [gridCut]
    rw [this, mul_one]
  exact lem_most_good_grounded gridCut (Finset.univ : Finset Unit)
    Fstar excSize ((globalBKBdy gridCut).card : ℚ)
    ((globalBKBdy gridCut).card : ℚ) (1/2 : ℚ)
    (by positivity) hStep2 hΦ

/-- **The S2 `ε₂` wire fires non-vacuously at `Antichain3`**
(`mg-aa02` acceptance bar, Route B — the genuine `thm:step2`
consumption).

On the genuine width-3 non-chain poset `Antichain3`, with the genuine
rich-fiber family `antichain3Family` (carrier `{(a0, a1)}`, a
singleton good fiber of constant sign), the empty cut, and the
**genuine uniform staircase rate** `ε₂ = fiberStaircaseRate 1 1 1 1`:

1. `Antichain3` is genuinely width-3 and non-chain;
2. `lem_most_good_grounded_of_thm_step2` genuinely fires — it consumes
   `step2.tex` `thm:step2` and the `fiberStaircaseRate` bookkeeping,
   producing a genuine per-fiber exceptional-mass assignment and the
   G6 bad-mass bound `∑_{Rich∖Rich⋆}|F_r| ≤ K·κ·|S|/η`;
3. the genuine rich-fiber family is non-empty (`{(a0, a1)}`), and its
   one boundary-good fiber is classified `S`-good by the genuine `ε₂`.

This is the wire the S6-QA Checkpoint-2 audit flagged absent: `ε₂` /
`fiberStaircaseRate` now genuinely thread from `thm:step2` into the
Step 6 per-fiber aggregation. -/
theorem lem_most_good_step2_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    ∃ L : LinearExt Antichain3,
      (antichain3Family L).carrier.Nonempty ∧
      ∃ excSize : Antichain3 × Antichain3 → ℕ,
        (∀ r ∈ goodFibers (antichain3Family L)
            (∅ : Finset (LinearExt Antichain3)) 1,
          ((excSize r : ℚ))
            ≤ fiberStaircaseRate 1 1 1 1 * (((antichain3Family L).fib r).card : ℚ)) ∧
        (∑ r ∈ (antichain3Family L).carrier
            \ sGoodInterfaces (fiberStaircaseRate 1 1 1 1)
                (antichain3Family L).carrier (antichain3Family L).fib excSize,
            (((antichain3Family L).fib r).card : ℚ))
          ≤ (1 : ℚ) * 1
              * ((∅ : Finset (LinearExt Antichain3)).card : ℚ) / 1 := by
  classical
  refine ⟨Antichain3.hasWidth, Antichain3.not_isChainPoset, ?_⟩
  obtain ⟨L⟩ : Nonempty (LinearExt Antichain3) := by
    have h := Antichain3.two_le_numLinExt
    unfold numLinExt at h
    exact Fintype.card_pos_iff.mp (by omega)
  refine ⟨L, ⟨_, Finset.mem_singleton_self _⟩, ?_⟩
  -- Every member of `goodFibers` is the genuine rich pair `(a0, a1)`.
  have hgoodmem : ∀ r ∈ goodFibers (antichain3Family L)
      (∅ : Finset (LinearExt Antichain3)) 1,
      r = (Antichain3.a0, Antichain3.a1) := by
    intro r hr
    have := goodFibers_subset (antichain3Family L)
      (∅ : Finset (LinearExt Antichain3)) 1 hr
    rwa [antichain3Family_carrier, Finset.mem_singleton] at this
  -- `thm:step2`'s hypotheses, discharged at the genuine family.
  have hmult : ∀ e ∈ globalBKBdy (∅ : Finset (LinearExt Antichain3)),
      ((antichain3Family L).carrier.filter
        (fun r => edgeInternal (antichain3Family L) r e)).card ≤ 1 := by
    intro e he
    rw [globalBKBdy_empty] at he
    simp at he
  have hcond : ((globalBKBdy (∅ : Finset (LinearExt Antichain3))).card : ℚ)
      ≤ 1 * ((∅ : Finset (LinearExt Antichain3)).card : ℚ) := by
    rw [globalBKBdy_empty]
    simp
  have ht : ∀ r ∈ goodFibers (antichain3Family L)
      (∅ : Finset (LinearExt Antichain3)) 1,
      1 ≤ commonNbhdLength r.1 r.2 := by
    intro r hr
    rw [hgoodmem r hr]
    change 1 ≤ commonNbhdLength Antichain3.a0 Antichain3.a1
    rw [Antichain3.commonNbhdLength_a0_a1]
  have hmass : ∀ r ∈ goodFibers (antichain3Family L)
      (∅ : Finset (LinearExt Antichain3)) 1,
      (1 : ℚ) * (commonNbhdLength r.1 r.2 : ℚ) ^ 2
        ≤ ((fiberGrid r.1 r.2 ((antichain3Family L).fib r)).card : ℚ) := by
    intro r hr
    have hr' := hgoodmem r hr
    subst hr'
    have hsign : ∀ L' ∈ ((antichain3Family L).fib
        (Antichain3.a0, Antichain3.a1)),
        signMarker Antichain3.a0 Antichain3.a1 L'
          = signMarker Antichain3.a0 Antichain3.a1 L := by
      intro L' hL'
      rw [antichain3Family_fib, Finset.mem_singleton] at hL'
      rw [hL']
    have hcardF : (fiberGrid Antichain3.a0 Antichain3.a1
        ((antichain3Family L).fib (Antichain3.a0, Antichain3.a1))).card = 1 := by
      rw [antichain3Family_fib]
      rw [fiberGrid_card (isGoodFiber_singleton _ _ L)
        (by intro L' hL'; rw [Finset.mem_singleton] at hL'; rw [hL'])]
      exact Finset.card_singleton L
    change (1 : ℚ) * (commonNbhdLength Antichain3.a0 Antichain3.a1 : ℚ) ^ 2
      ≤ ((fiberGrid Antichain3.a0 Antichain3.a1
          ((antichain3Family L).fib (Antichain3.a0, Antichain3.a1))).card : ℚ)
    rw [Antichain3.commonNbhdLength_a0_a1, hcardF]
    norm_num
  have huniform : ∀ r ∈ goodFibers (antichain3Family L)
      (∅ : Finset (LinearExt Antichain3)) 1,
      fiberStaircaseRate 1 1 ((antichain3Family L).fib r).card
          (commonNbhdLength r.1 r.2)
        ≤ fiberStaircaseRate 1 1 1 1 := by
    intro r hr
    have hr' := hgoodmem r hr
    subst hr'
    rw [antichain3Family_fib, Finset.card_singleton]
    change fiberStaircaseRate 1 1 1
        (commonNbhdLength Antichain3.a0 Antichain3.a1)
      ≤ fiberStaircaseRate 1 1 1 1
    rw [Antichain3.commonNbhdLength_a0_a1]
  exact lem_most_good_grounded_of_thm_step2 (antichain3Family L)
    (∅ : Finset (LinearExt Antichain3)) (by norm_num) (by norm_num)
    hmult hcond ht hmass huniform

end ConcreteWitness

end Step6
end OneThird
