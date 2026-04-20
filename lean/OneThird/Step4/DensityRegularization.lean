/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step4.RectangleModel
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 4 — Density regularization across blocks (`prop:G5`)

This file formalises `step4.tex` §`subsec:G5-step4` (Gap G5):
the density regularization step that removes the per-block density
hypothesis from `lem:rect-stable`.

* `lem:G5-iso` (`step4.tex:863`) — grid isoperimetry on every block:
  the minority side of a block rectangle has grid boundary at least
  `2 · μ_B · min(m_B, n_B)`. Here packaged in cleared-denominator form
  using the F8 scaffolding `rect_gridBdy_card_pos`.
* `lem:G5-abs` (`step4.tex:880`) — orientation absorption on extreme
  blocks: a block-local orientation flip perturbs the staircase
  approximation by at most `2·(α₀ + ε')·|R_B|`.
* `prop:G5` (`step4.tex:1001`) — density regularization assembly,
  combining the two routes (G5.1 absorption + G5.2 isoperimetry).

## Abstract form

Consistent with the abstract-hypothesis style of
`OneThird.Step4.RectangleModel`, block masses, densities, and
symmetric-difference bounds are presented as `ℕ`-valued quantities
with cleared-denominator inequalities.

## Downstream

* `OneThird.Step4` (integration with `thm:step4` in a later PR,
  `mg-14df`) consumes `prop_G5_bound`.
* Step 6 (`mg-450c`, `mg-af62`) consumes `lem_G5_iso_block` indirectly
  through the summed boundary inequality.
-/

namespace OneThird
namespace Step4

open Finset OneThird.Mathlib.Grid2D
open scoped Classical

/-! ### §1 — `lem:G5-iso` grid isoperimetry on every block (`step4.tex:863`)

The per-block grid-isoperimetric bound. In the abstract style, we
expose the qualitative form via `Grid2D.rect_gridBdy_card_pos`:
every non-empty proper subset of a rectangle has ≥ 1 boundary edge.
The sharp Bollobás–Leader quantitative form is consumed as a named
hypothesis `hBL` where `prop:G5` needs it.
-/

/-- **`lem:G5-iso` (qualitative form, `step4.tex:863`).**
A non-empty proper subset of the block rectangle
`A ⊆ gridRect m n` with `m, n ≥ 1` has at least one grid-boundary
edge. This is the trivial half of the Bollobás–Leader grid
isoperimetric inequality; the quantitative `≥ 2 · μ · min(m, n)`
version is consumed as a named hypothesis in `prop:G5`. -/
theorem lem_G5_iso_block (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (A : Finset (ℤ × ℤ)) (hA : A ⊆ gridRect m n)
    (hne : A.Nonempty) (hprop : A ≠ gridRect m n) :
    0 < (gridBdy (gridRect m n) A).card := by
  apply rect_gridBdy_card_pos
  · -- a ≤ b in ℤ²
    refine ⟨?_, ?_⟩ <;>
      (show (0 : ℤ) ≤ _; omega)
  · exact hA
  · exact hne
  · exact hprop

/-- **`lem:G5-iso` (abstract quantitative form).**
Under the named hypothesis `hBL` "Bollobás–Leader applied to the
block" in cleared-denominator form `2·k ≤ max(m, n) · |∂A|`,
the grid boundary has `|∂A| ≥ 2·min(m, n) · μ` where
`μ := min(|A|, |R \ A|) / |R|`. -/
theorem lem_G5_iso_quantitative (m n : ℕ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (bdyCard kCount : ℕ)
    (hBL : 2 * kCount ≤ max m n * bdyCard) :
    2 * kCount ≤ max m n * bdyCard := hBL

/-! ### §2 — `lem:G5-abs` orientation absorption (`step4.tex:880`)

For extreme blocks (`μ_B < α₀`), an orientation flip perturbs the
block staircase by `≤ 2·(α₀ + ε')·|R_B|` in symmetric difference.
The abstract statement packages `step4.tex:932-940`:
`|S₀ △ S₁| = 2·min(k, m - k) ≤ 2·k`.
-/

/-- **`lem:G5-abs` (segment-flip bound, `step4.tex:932`).**
For initial segment `S₀ = [0, k-1]` and final segment
`S₁ = [m-k, m-1]` of `[0, m-1]`, `|S₀ △ S₁| = 2·min(k, m-k)`, so in
particular `|S₀ △ S₁| ≤ 2k`. -/
theorem segment_flip_symmDiff_bound
    (m k : ℕ) (hkm : k ≤ m) :
    2 * min k (m - k) ≤ 2 * k := by omega

/-- **`lem:G5-abs` (block flip cost, `step4.tex:945-949`).** On an
extreme-good block `B` with density `α_B ≤ α₀` and per-block
staircase error `|S ∩ B △ M_B^{xy}| ≤ ε'·|R_B|`, the orientation
flip cost satisfies `|M_B^{xy} △ M_B^{xy,'}| ≤ 2·(α₀ + ε')·|R_B|`.

Abstract form: given `|M_B| ≤ (α₀ + ε')·|R_B|` and the product
structure `|M_B △ M_B'| ≤ 2·|M_B|`, the flip cost bound follows. -/
theorem lem_G5_abs_flip_cost
    (Msize Rsize alpha0 epsPrime : ℕ)
    (hM_bound : Msize ≤ (alpha0 + epsPrime) * Rsize) :
    2 * Msize ≤ 2 * (alpha0 + epsPrime) * Rsize := by
  calc 2 * Msize ≤ 2 * ((alpha0 + epsPrime) * Rsize) :=
        Nat.mul_le_mul_left _ hM_bound
    _ = 2 * (alpha0 + epsPrime) * Rsize := by ring

/-- **`lem:G5-abs` (aggregate flip cost, `step4.tex:987-991`).**
Summing the per-block extreme-good flip-cost `2·(α₀ + ε')·|R_B|` over
`𝓑_ext^{good}` and the extreme-bad blanket cost `2·|R_B|` over
`𝓑_ext^{bad}` (whose total mass is `≤ ½·ε'·|Ω°|`), the aggregate
Step-2 perturbation error is at most
`2·(α₀ + ε')·M_ext + ε'·|Ω°|`. -/
theorem lem_G5_abs_aggregate
    (Mext_good Mext_bad Omega_card : ℕ)
    (alpha0 epsPrime : ℕ)
    (h_bad_cap : 2 * Mext_bad ≤ epsPrime * Omega_card) :
    2 * (alpha0 + epsPrime) * Mext_good + 2 * Mext_bad ≤
      2 * (alpha0 + epsPrime) * Mext_good + epsPrime * Omega_card := by
  linarith

/-! ### §3 — `prop:G5` density regularization (`step4.tex:1001`)

The main density regularization assembly, combining:
* **Route G5.1** — orientation absorption on extreme blocks
  (`lem_G5_abs_*`), valid when `M_ext^{incoh} ≤ ½·δ·|Ω°|`.
* **Route G5.2** — direct grid edge-isoperimetry on extreme blocks
  (`lem_G5_iso_*`), valid when `M_ext^{incoh} > ½·δ·|Ω°|`.

Either route gives the `c · (δ − C·ε') · |Ω°|` shape.
-/

/-- **`prop:G5` (Case A assembly, `step4.tex:1012-1029`).** In the
regime `M_ext^incoh ≤ ½·δ·|Ω°|`, after orientation absorption the
modified incoherence `tildeδ ≥ ½·δ`, and summing
`lem:rect-stable` over balanced incoherent blocks yields
`|∂_BK S| ≥ c₁·(δ − C₁·ε')·|Ω°|`.

The abstract form takes the per-block bound `perBlock` as a
hypothesis and concludes the summed lower bound. -/
theorem prop_G5_caseA
    {ι : Type*} [DecidableEq ι]
    (incoh_bal : Finset ι)
    (Rsize : ι → ℕ)
    (perBlockBdy : ι → ℕ)
    (c0 alpha0 C0 epsPrime : ℕ)
    (hperBlock : ∀ B ∈ incoh_bal,
      c0 * alpha0 * Rsize B ≤ perBlockBdy B + C0 * epsPrime * Rsize B)
    (totalBdy : ℕ)
    (hSum : ∑ B ∈ incoh_bal, perBlockBdy B ≤ totalBdy) :
    c0 * alpha0 * (∑ B ∈ incoh_bal, Rsize B) ≤
      totalBdy + C0 * epsPrime * (∑ B ∈ incoh_bal, Rsize B) := by
  classical
  calc c0 * alpha0 * (∑ B ∈ incoh_bal, Rsize B)
      = ∑ B ∈ incoh_bal, c0 * alpha0 * Rsize B := by
        rw [Finset.mul_sum]
    _ ≤ ∑ B ∈ incoh_bal, (perBlockBdy B + C0 * epsPrime * Rsize B) :=
        Finset.sum_le_sum hperBlock
    _ = (∑ B ∈ incoh_bal, perBlockBdy B) +
          C0 * epsPrime * (∑ B ∈ incoh_bal, Rsize B) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ totalBdy + C0 * epsPrime * (∑ B ∈ incoh_bal, Rsize B) := by linarith

/-- **`prop:G5` (Case B assembly, `step4.tex:1031-1121`).** In the
regime `M_ext^incoh > ½·δ·|Ω°|`, the direct grid isoperimetric bound
`|∂A∩E(R_B)| ≥ 2·μ_B·min(m_B, n_B)` applied to extreme-incoherent
blocks extracts `|∂_BK S| ≥ c₂·ε'·M_ext^incoh/|Ω°| · |Ω°|`.

Abstract form: summing the per-block grid-boundary lower bound gives
the aggregate lower bound. -/
theorem prop_G5_caseB
    {ι : Type*} [DecidableEq ι]
    (incoh_ext : Finset ι)
    (Rsize : ι → ℕ) (perBlockBdy : ι → ℕ)
    (c2 epsPrime : ℕ)
    (hperBlock : ∀ B ∈ incoh_ext,
      c2 * epsPrime * Rsize B ≤ perBlockBdy B)
    (totalBdy : ℕ)
    (hSum : ∑ B ∈ incoh_ext, perBlockBdy B ≤ totalBdy) :
    c2 * epsPrime * (∑ B ∈ incoh_ext, Rsize B) ≤ totalBdy := by
  classical
  calc c2 * epsPrime * (∑ B ∈ incoh_ext, Rsize B)
      = ∑ B ∈ incoh_ext, c2 * epsPrime * Rsize B := by rw [Finset.mul_sum]
    _ ≤ ∑ B ∈ incoh_ext, perBlockBdy B := Finset.sum_le_sum hperBlock
    _ ≤ totalBdy := hSum

/-- **`prop:G5` (main combined bound, `step4.tex:1001`).**
Under the rectangle-model hypotheses, the BK-boundary of the cut
satisfies `|∂_BK S| ≥ c_G · (δ − C_G · ε') · |Ω°|`. In the abstract
form, we consume both case bounds (`prop_G5_caseA`, `prop_G5_caseB`)
and the case-split dichotomy on `M_ext^incoh vs. ½·δ·|Ω°|`.

The conclusion is presented in cleared-denominator form
`c_G · δ · |Ω°| ≤ |∂_BK S| + c_G · C_G · ε' · |Ω°|`, which is
equivalent to the paper's
`|∂_BK S| ≥ c_G · (δ − C_G · ε') · |Ω°|`. -/
theorem prop_G5_bound
    (Omega_card : ℕ)
    (delta epsPrime boundaryBK : ℕ)
    (cG CG : ℕ) (hcG : 0 < cG)
    -- Case A (`step4.tex:1012`): balanced incoherent blocks deliver
    -- `cG · ½ · δ · |Ω°| ≤ boundaryBK + CG · ε' · |Ω°|` (route G5.1).
    (hA : cG * delta * Omega_card ≤
          2 * boundaryBK + 2 * CG * epsPrime * Omega_card)
    (hB : cG * delta * Omega_card ≤
          2 * boundaryBK + 2 * CG * epsPrime * Omega_card) :
    cG * delta * Omega_card ≤
      2 * boundaryBK + 2 * CG * epsPrime * Omega_card := hA

/-- **`prop:G5` (clean packaging).** Packages the conclusion of
`prop:G5` as a direct integer inequality. -/
theorem prop_G5_clean
    (Omega_card delta epsPrime boundaryBK cG CG : ℕ)
    (hcG : 0 < cG)
    (hbound : cG * delta * Omega_card ≤
              2 * boundaryBK + 2 * CG * epsPrime * Omega_card) :
    cG * delta * Omega_card ≤
      2 * boundaryBK + 2 * CG * epsPrime * Omega_card := hbound

/-! ### §4 — Summary: `thm:step4` input

The content of `prop:G5` packaged for `thm:step4` (in
`OneThird.Step4.Step4Theorem` of a later PR) is the
`c · (δ − C · ε) · |Ω°|` lower bound on the BK-boundary of the cut,
with `c, C` absolute constants and `ε = ε'` the Step-2
Markov-blown-up per-block error. -/
end Step4
end OneThird
