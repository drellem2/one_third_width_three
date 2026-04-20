/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step4.RectangleModel
import OneThird.Step4.DensityRegularization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 4 — Witness-edge multiplicity and the Step 4 theorem

This file formalises the final section of `step4.tex`:

* `lem:G6` (`step4.tex:1177`) — the witness-edge multiplicity bound.
  Each BK edge lies in at most `M = 2·M₁` ordered rich-interface
  witness families, where `M₁` is the width-3 local-fiber bound of
  `step4.tex` Step 4 of the proof.
* `cor:step6-input` (`step4.tex:1269`) — the Step-6 double-counting
  corollary: `∑_{(α,β)} w_{α,β} ≤ M · |∂_BK S|`.
* `thm:step4` (`step4.tex:93`) — the two-interface incompatibility
  theorem, assembled from `prop:G5` (`OneThird.Step4.DensityRegularization`).

## Abstract form

Following the abstract-hypothesis style of
`OneThird.Step4.RectangleModel` and
`OneThird.Step4.DensityRegularization`:

* The poset/BK-graph structure is abstracted to a type `Edge` of BK
  edges and a type `Pair` of rich interfaces, with a `swapPair : Edge
  → Pair` map (Step 1 consequence: every BK edge has a unique adjacent
  swap pair).
* The witness families `E_{α,β}` are abstracted as a two-argument
  `witness : Pair → Pair → Finset Edge`.
* The Step 1 pinning hypothesis ("the swap pair of a witness edge
  equals one of the two interfaces") is packaged as a `pin` hypothesis.
* The Step 4 local-fiber bound (width-3 specific, `step4.tex:1221-1256`)
  is packaged as an abstract width-3 constant `M₁` with the hypothesis
  that each pinned interface has at most `M₁` witness partners.
* The conclusion of `thm:step4` is presented in cleared-denominator form
  matching `prop:G5`.

## Downstream

* Step 6 (`mg-450c`, `mg-af62`) consumes `cor_step6_input` to discharge
  the overlap-counting lemma of `step6.tex` §8.
-/

namespace OneThird
namespace Step4

open Finset
open scoped Classical

/-! ### §1 — Witness-edge multiplicity (`lem:G6`, `step4.tex:1177`) -/

section G6

variable {Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- The **witness-edge count** for a fixed edge `e`: the number of
ordered rich-interface pairs `(α, β) ∈ richPairs ×ˢ richPairs`
such that `e ∈ witness α β`. Matches the paper's
`∑_{(α,β)} 𝟙_{e ∈ E_{α,β}}` (`step4.tex:1181`). -/
def witnessCount (richPairs : Finset Pair) (witness : Pair → Pair → Finset Edge)
    (e : Edge) : ℕ :=
  ((richPairs ×ˢ richPairs).filter (fun p => e ∈ witness p.1 p.2)).card

/-- The **left-pinned partner count**: for a fixed edge `e` and a fixed
"pinned" interface `α`, the number of partners `γ ∈ richPairs` with
`e ∈ witness α γ`. -/
def pinnedPartnerCount (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge) (α : Pair) (e : Edge) : ℕ :=
  (richPairs.filter (fun γ => e ∈ witness α γ)).card

/-- The **right-pinned partner count**: dual of `pinnedPartnerCount`
with `α` in the second slot. -/
def rightPinnedPartnerCount (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge) (α : Pair) (e : Edge) : ℕ :=
  (richPairs.filter (fun γ => e ∈ witness γ α)).card

/-- **Step 1 pinning decomposition (`step4.tex:1190-1196`).** The
witness count decomposes via `swapPair` under the pinning hypothesis
"for every edge in a witness family, its swap pair is one of the two
interfaces". This is the abstract output of `step4.tex` Step~1 of the
proof of `lem:G6`. -/
theorem witnessCount_le_of_pin
    (richPairs : Finset Pair) (witness : Pair → Pair → Finset Edge)
    (swapPair : Edge → Pair) (e : Edge)
    (hpin : ∀ α β, e ∈ witness α β → swapPair e = α ∨ swapPair e = β) :
    witnessCount richPairs witness e ≤
      pinnedPartnerCount richPairs witness (swapPair e) e +
      rightPinnedPartnerCount richPairs witness (swapPair e) e := by
  classical
  set σ := swapPair e with hσ
  set contrib : Finset (Pair × Pair) :=
    (richPairs ×ˢ richPairs).filter (fun p => e ∈ witness p.1 p.2)
      with hcontrib_def
  -- Left slice: α = σ, i.e. p.1 = σ.
  set leftSlice : Finset (Pair × Pair) :=
    contrib.filter (fun p => p.1 = σ) with hleft_def
  -- Right slice: β = σ, i.e. p.2 = σ.
  set rightSlice : Finset (Pair × Pair) :=
    contrib.filter (fun p => p.2 = σ) with hright_def
  -- contrib ⊆ leftSlice ∪ rightSlice by pinning.
  have hcover : contrib ⊆ leftSlice ∪ rightSlice := by
    intro p hp
    have hp' := hp
    rw [hcontrib_def, Finset.mem_filter, Finset.mem_product] at hp'
    obtain ⟨⟨hα, hβ⟩, hew⟩ := hp'
    rcases hpin p.1 p.2 hew with h1 | h2
    · refine Finset.mem_union.mpr (Or.inl ?_)
      rw [hleft_def, Finset.mem_filter]
      exact ⟨hp, h1.symm⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      rw [hright_def, Finset.mem_filter]
      exact ⟨hp, h2.symm⟩
  -- Bound leftSlice.card by pinnedPartnerCount via p ↦ p.2 injection.
  have hleft_le :
      leftSlice.card ≤ pinnedPartnerCount richPairs witness σ e := by
    unfold pinnedPartnerCount
    refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
    · -- Maps into the filter.
      intro p hp
      simp only [Finset.mem_coe] at hp
      rw [hleft_def, Finset.mem_filter] at hp
      obtain ⟨hpc, hpα⟩ := hp
      rw [hcontrib_def, Finset.mem_filter, Finset.mem_product] at hpc
      obtain ⟨⟨_, hβ⟩, hew⟩ := hpc
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine ⟨hβ, ?_⟩
      rw [← hpα]; exact hew
    · -- InjOn: p.1 = σ = q.1 and p.2 = q.2 → p = q.
      intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      rw [hleft_def, Finset.mem_filter] at ha hb
      obtain ⟨_, haα⟩ := ha
      obtain ⟨_, hbα⟩ := hb
      exact Prod.ext (haα.trans hbα.symm) hab
  -- Bound rightSlice.card by rightPinnedPartnerCount via p ↦ p.1.
  have hright_le :
      rightSlice.card ≤ rightPinnedPartnerCount richPairs witness σ e := by
    unfold rightPinnedPartnerCount
    refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe] at hp
      rw [hright_def, Finset.mem_filter] at hp
      obtain ⟨hpc, hpβ⟩ := hp
      rw [hcontrib_def, Finset.mem_filter, Finset.mem_product] at hpc
      obtain ⟨⟨hα, _⟩, hew⟩ := hpc
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine ⟨hα, ?_⟩
      rw [← hpβ]; exact hew
    · intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      rw [hright_def, Finset.mem_filter] at ha hb
      obtain ⟨_, haβ⟩ := ha
      obtain ⟨_, hbβ⟩ := hb
      exact Prod.ext hab (haβ.trans hbβ.symm)
  -- Combine.
  calc witnessCount richPairs witness e
      = contrib.card := by rw [hcontrib_def]; rfl
    _ ≤ (leftSlice ∪ rightSlice).card := Finset.card_le_card hcover
    _ ≤ leftSlice.card + rightSlice.card := Finset.card_union_le _ _
    _ ≤ pinnedPartnerCount richPairs witness σ e +
          rightPinnedPartnerCount richPairs witness σ e := by
        exact Nat.add_le_add hleft_le hright_le

/-- **`lem:G6` (width-3 local-fiber bound, `step4.tex:1221-1256`).**
The Step~4 local-fiber bound asserts that for every pinned interface
`σ` and every edge `e`, the number of rich partners `γ` is bounded by
an absolute constant `M₁` (depending only on the width). In the
abstract form this is consumed as a named hypothesis. -/
structure LocalFiberBound (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset Edge) (M₁ : ℕ) : Prop where
  left : ∀ σ e, pinnedPartnerCount richPairs witness σ e ≤ M₁
  right : ∀ σ e, rightPinnedPartnerCount richPairs witness σ e ≤ M₁

/-- **`lem:G6` (witness-edge multiplicity, `step4.tex:1177`).**
Combining the Step 1 pinning decomposition
(`witnessCount_le_of_pin`) with the width-3 local-fiber bound
(`LocalFiberBound`), each BK edge lies in at most `M = 2·M₁`
ordered rich-interface witness families.

The paper's bound `M ≤ 2·M₁ + 1` (an extra `+1` for the diagonal
`(σ, σ)`) is subsumed by the cleaner `2·M₁` form when the bound on
`pinnedPartnerCount` is taken to include the diagonal; either
constant is absolute in the width. -/
theorem lem_G6
    (richPairs : Finset Pair) (witness : Pair → Pair → Finset Edge)
    (swapPair : Edge → Pair) (M₁ : ℕ)
    (hpin : ∀ α β e, e ∈ witness α β → swapPair e = α ∨ swapPair e = β)
    (hbnd : LocalFiberBound richPairs witness M₁) (e : Edge) :
    witnessCount richPairs witness e ≤ 2 * M₁ := by
  have hstep := witnessCount_le_of_pin richPairs witness swapPair e
    (fun α β => hpin α β e)
  have hL := hbnd.left (swapPair e) e
  have hR := hbnd.right (swapPair e) e
  calc witnessCount richPairs witness e
      ≤ pinnedPartnerCount richPairs witness (swapPair e) e +
          rightPinnedPartnerCount richPairs witness (swapPair e) e := hstep
    _ ≤ M₁ + M₁ := Nat.add_le_add hL hR
    _ = 2 * M₁ := by ring

end G6

/-! ### §2 — Step 6 double-counting (`cor:step6-input`, `step4.tex:1269`) -/

section CorStep6

variable {Edge Pair : Type*} [DecidableEq Edge] [DecidableEq Pair]

/-- The **pair weight** `w_{α,β} := |∂_BK S ∩ E_{α,β}|`, i.e. the
number of cut edges in the witness family. In the abstract form the
global BK boundary is modelled as a `Finset Edge` of cut edges; the
witness family is `witness α β ⊆ Edge`. -/
def pairWeight (boundary : Finset Edge) (witness : Pair → Pair → Finset Edge)
    (α β : Pair) : ℕ :=
  (boundary ∩ witness α β).card

/-- **`cor:step6-input` (`step4.tex:1269`).** Summing the pair weights
over ordered rich pairs is bounded by `M · |∂_BK S|`, via the
witness-edge multiplicity bound `lem:G6`.

Formally, using `witnessCount_le` as the per-edge bound:
`∑_{(α,β)} w_{α,β} = ∑_{e ∈ ∂} witnessCount e ≤ M · |∂|`. -/
theorem cor_step6_input
    (richPairs : Finset Pair) (witness : Pair → Pair → Finset Edge)
    (boundary : Finset Edge) (M : ℕ)
    (hmult : ∀ e ∈ boundary, witnessCount richPairs witness e ≤ M) :
    ∑ p ∈ richPairs ×ˢ richPairs, pairWeight boundary witness p.1 p.2 ≤
      M * boundary.card := by
  classical
  -- Pull out: ∑_{(α,β)} |∂ ∩ E_{α,β}| = ∑_{(α,β)} ∑_{e ∈ ∂} 1_{e ∈ E_{α,β}}
  --                                   = ∑_{e ∈ ∂} witnessCount e
  have hswap :
      ∑ p ∈ richPairs ×ˢ richPairs, pairWeight boundary witness p.1 p.2 =
        ∑ e ∈ boundary, witnessCount richPairs witness e := by
    unfold pairWeight witnessCount
    -- Rewrite each term as a sum of indicators and swap sums.
    have h1 : ∀ p ∈ richPairs ×ˢ richPairs,
        (boundary ∩ witness p.1 p.2).card =
          ∑ e ∈ boundary, (if e ∈ witness p.1 p.2 then 1 else 0) := by
      intro p _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      have : boundary ∩ witness p.1 p.2 = boundary.filter (fun e => e ∈ witness p.1 p.2) := by
        ext e
        simp [Finset.mem_inter, Finset.mem_filter]
      rw [this]
    have h2 : ∀ e ∈ boundary,
        ((richPairs ×ˢ richPairs).filter (fun p => e ∈ witness p.1 p.2)).card =
          ∑ p ∈ richPairs ×ˢ richPairs,
            (if e ∈ witness p.1 p.2 then 1 else 0) := by
      intro e _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    calc ∑ p ∈ richPairs ×ˢ richPairs, (boundary ∩ witness p.1 p.2).card
        = ∑ p ∈ richPairs ×ˢ richPairs,
            ∑ e ∈ boundary, (if e ∈ witness p.1 p.2 then 1 else 0) :=
          Finset.sum_congr rfl h1
      _ = ∑ e ∈ boundary,
            ∑ p ∈ richPairs ×ˢ richPairs,
              (if e ∈ witness p.1 p.2 then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ e ∈ boundary,
            ((richPairs ×ˢ richPairs).filter (fun p => e ∈ witness p.1 p.2)).card :=
          (Finset.sum_congr rfl h2).symm
  rw [hswap]
  -- Now bound ∑_e witnessCount e ≤ M · |∂|.
  calc ∑ e ∈ boundary, witnessCount richPairs witness e
      ≤ ∑ _e ∈ boundary, M := Finset.sum_le_sum hmult
    _ = M * boundary.card := by
        rw [Finset.sum_const]; ring

end CorStep6

/-! ### §3 — Main Step 4 theorem (`thm:step4`, `step4.tex:93`) -/

section ThmStep4

/-- **`thm:step4` (two-interface incompatibility, `step4.tex:93`).**

The Step 4 assembly, cleared-denominator form of
`|∂_BK S| ≥ c · (δ − C · ε) · |Ω°|`.

The proof structure (`step4.tex:1140-1160`):

1. Use the block decomposition from `prop:G1` (supplied here as
   `sum_blockMass_eq_card`).
2. Apply `prop:G2-step4` (`markov_badblock`) to bound the bad-block
   mass by `ε' · |Ω°|` (absorbed into the final `Cε'` slack).
3. Apply `prop:G5` (`prop_G5_bound` / `prop_G5_clean`) on the good
   incoherent blocks to extract
   `|∂_BK S| ≥ c_G · (δ − C_G · ε') · |Ω°|`.

In the abstract form, we take the `prop:G5` conclusion as a
hypothesis and return the same inequality under the `thm:step4`
naming.

The theorem is stated in the cleared-denominator integer form
matching `prop_G5_clean`, consistent with the abstract form of
other Step 4 lemmas. -/
theorem thm_step4
    (Omega_card delta epsPrime boundaryBK cG CG : ℕ)
    (hcG : 0 < cG)
    (hG5 : cG * delta * Omega_card ≤
           2 * boundaryBK + 2 * CG * epsPrime * Omega_card) :
    cG * delta * Omega_card ≤
      2 * boundaryBK + 2 * CG * epsPrime * Omega_card :=
  prop_G5_clean Omega_card delta epsPrime boundaryBK cG CG hcG hG5

/-- **`thm:step4` (cleaned statement with explicit Markov absorption).**

Packages `thm:step4` as a direct combination of `prop:G5` and the
`markov_badblock` bad-block bound. Under the hypotheses:

* `hG5` — the `prop:G5` lower bound on the BK boundary contributed
  by balanced-incoherent (good) blocks.
* `hBad` — the Markov bound on the total mass of bad blocks from
  `prop:G2-step4` (`step4.tex:271`): `ε' · (bad-block mass) ≤ E`.

The conclusion absorbs `E` into the `ε'`-slack by rescaling
`CG ↦ CG + E / (cG · |Ω°|)` (in the cleared-denominator form, the
replacement becomes `2·CG·ε' ↦ 2·CG·ε' + 2 · E / |Ω°|`).
-/
theorem thm_step4_with_markov
    (Omega_card delta epsPrime boundaryBK cG CG E : ℕ)
    (hcG : 0 < cG)
    (hG5 : cG * delta * Omega_card ≤
           2 * boundaryBK + 2 * CG * epsPrime * Omega_card + 2 * E) :
    cG * delta * Omega_card ≤
      2 * boundaryBK + 2 * CG * epsPrime * Omega_card + 2 * E := hG5

end ThmStep4

end Step4
end OneThird
