/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step4.Step4Theorem
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 6 — Overlap counting lemma (G4, `lem:overlap-counting`)

Formalises the overlap counting lemma of `step6.tex`
(`step6.tex:345-475`).

The lemma states that the witness-edge families
`{E_{αβ}}_{(α,β) ∈ Rich⋆×Rich⋆}` supplied by Step 4 can be chosen so
that every BK edge `e ∈ E(G_BK)` is contained in at most `M` families
`E_{αβ}`, for a width-dependent constant `M` (concretely `M = 2·M₁`
with `M₁` the width-3 local-fiber bound).

The core content is already proved in `OneThird.Step4.Step4Theorem`:

* `OneThird.Step4.lem_G6` — per-edge multiplicity bound
  `witnessCount e ≤ 2·M₁`, assuming Step 1 pinning
  (`hpin : ∀ α β e, e ∈ witness α β → swapPair e = α ∨ swapPair e = β`)
  and the width-3 local-fiber bound (`LocalFiberBound`).
* `OneThird.Step4.cor_step6_input` — summed form
  `∑_{(α,β)} (∂S ∩ E_{αβ}).card ≤ M · |∂S|`.

Here we re-export these under Step 6 names (`lem_overlap_counting`,
`lem_overlap_counting_summed`) and provide the specialisation to
bad-active pair Finsets consumed by `lem:sum-step4` and `thm:step6`.

## Content

* `lem_overlap_counting` — per-edge multiplicity bound (alias for
  `Step4.lem_G6`).
* `lem_overlap_counting_summed` — summed form
  `∑ |∂S ∩ E_{αβ}| ≤ M · |∂S|` (alias for `Step4.cor_step6_input`).
* `overlap_counting_restrict` — restriction of the summed form to a
  subfinset `T ⊆ Rich⋆ ×ˢ Rich⋆` (in particular `T = badActivePairs`):
  `∑_{(α,β) ∈ T} |∂S ∩ E_{αβ}| ≤ M · |∂S|`.
-/

namespace OneThird
namespace Step6

open Finset

/-! ### `lem:overlap-counting` — per-edge multiplicity (`step6.tex:351`) -/

section PerEdge

variable {Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- **`lem:overlap-counting` — per-edge multiplicity bound**
(`step6.tex:351`, alias of `OneThird.Step4.lem_G6`, `step4.tex:1177`).

Each BK edge `e` is contained in at most `2·M₁` ordered rich-interface
witness families, under the Step 1 pinning hypothesis and the width-3
local-fiber bound. The constant `M = 2·M₁` depends only on the
width. -/
theorem lem_overlap_counting
    (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge)
    (swapPair : Edge → Pair) (M₁ : ℕ)
    (hpin : ∀ α β e, e ∈ witness α β → swapPair e = α ∨ swapPair e = β)
    (hbnd : OneThird.Step4.LocalFiberBound richPairs witness M₁)
    (e : Edge) :
    OneThird.Step4.witnessCount richPairs witness e ≤ 2 * M₁ :=
  OneThird.Step4.lem_G6 richPairs witness swapPair M₁ hpin hbnd e

end PerEdge

/-! ### Summed form of the overlap counting lemma (`step6.tex:325-340`) -/

section Summed

variable {Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- **`lem:overlap-counting` — summed form** (`step6.tex:325-340`,
alias of `OneThird.Step4.cor_step6_input`).

`∑_{(α,β) ∈ Rich⋆×Rich⋆} |∂S ∩ E_{αβ}| ≤ M · |∂S|`. -/
theorem lem_overlap_counting_summed
    (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge)
    (boundary : Finset Edge) (M : ℕ)
    (hmult : ∀ e ∈ boundary,
      OneThird.Step4.witnessCount richPairs witness e ≤ M) :
    ∑ p ∈ richPairs ×ˢ richPairs,
        OneThird.Step4.pairWeight boundary witness p.1 p.2
      ≤ M * boundary.card :=
  OneThird.Step4.cor_step6_input richPairs witness boundary M hmult

end Summed

/-! ### Restriction to bad-active pairs -/

section Restriction

variable {Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- **Overlap counting restricted to a subset `T`**.

If every BK edge in `∂S` appears in at most `M` witness families from
`richPairs × richPairs`, then for any `T ⊆ richPairs ×ˢ richPairs`
the same bound holds for the restricted sum:

  `∑_{(α,β) ∈ T} |∂S ∩ E_{αβ}| ≤ M · |∂S|`.

This is the form consumed by `Step6.Assembly.lem_sum_step4`: taking
`T = badActivePairs`, the summed Step 4 bound is obtained by chaining
a per-bad-active-pair lower bound on `|∂S ∩ E_{αβ}|` with the
multiplicity bound. -/
theorem overlap_counting_restrict
    (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge)
    (boundary : Finset Edge) (M : ℕ)
    (T : Finset (Pair × Pair))
    (hT : T ⊆ richPairs ×ˢ richPairs)
    (hmult : ∀ e ∈ boundary,
      OneThird.Step4.witnessCount richPairs witness e ≤ M) :
    ∑ p ∈ T, OneThird.Step4.pairWeight boundary witness p.1 p.2
      ≤ M * boundary.card := by
  classical
  have hfull :
      ∑ p ∈ richPairs ×ˢ richPairs,
          OneThird.Step4.pairWeight boundary witness p.1 p.2
        ≤ M * boundary.card :=
    lem_overlap_counting_summed richPairs witness boundary M hmult
  have hmono :
      ∑ p ∈ T, OneThird.Step4.pairWeight boundary witness p.1 p.2
        ≤ ∑ p ∈ richPairs ×ˢ richPairs,
            OneThird.Step4.pairWeight boundary witness p.1 p.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (by intros; exact Nat.zero_le _)
  exact hmono.trans hfull

end Restriction

end Step6
end OneThird
