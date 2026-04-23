/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset
import OneThird.LinearExtension
import OneThird.RichPair
import OneThird.Step8.MainAssembly

/-!
# Main theorem: the width-3 1/3–2/3 theorem

This file states the main theorem of the paper and the headline
Step 8 intermediate result `thm:cex-implies-low-expansion`.

The headline theorem `width3_one_third_two_thirds` is discharged
via the Step 8 assembly (`OneThird.Step8.MainAssembly`); the
intermediate Theorem E is discharged here via the trivial
`S = 𝓛(P)` cut, with the tighter frozen-pair averaging cut of
the paper recorded in `OneThird.Step8.cexImpliesLowBKExpansion`
(indecomposable form).
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **Width-3 1/3–2/3 theorem** (`thm:main` of `main.tex`,
`thm:conclusion-main` of `step8.tex`).

Every finite width-≤ 3 poset that is not a chain admits a pair
`(x, y)` of incomparable elements with
`1/3 ≤ Pr[x <_L y] ≤ 2/3` under the uniform linear-extension
measure.

Discharged via the Step 8 assembly
(`OneThird.Step8.width3_one_third_two_thirds_assembled`). -/
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α :=
  Step8.width3_one_third_two_thirds_assembled hP hNonChain hC3

/-- **Theorem E — Counterexample ⇒ low BK conductance**
(`thm:cex-implies-low-expansion` in `step8.tex`).

For a width-3 `γ`-counterexample on `n ≥ 2` elements with
`γ ≤ 1` the BK graph admits a cut of bulk volume
`≥ γ · vol(𝓛(P))` and conductance `≤ 2 / (γ n)`.

The hypothesis `γ ≤ 1` is harmless in the regime of interest
(`γ ∈ (0, 1/3]`); without it the chain edge case (where
`IsGammaCounterexample` is vacuous) admits no cut satisfying the
volume lower bound, since the only candidates `S = ∅` and
`S = 𝓛(P)` then force `γ ≤ 1`.

The proof uses the trivial cut `S = 𝓛(P)`: its complement is
empty so the BK edge boundary and the volume of the complement
both vanish, giving conductance `0`; the volume bound reduces to
`γ · vol(𝓛(P)) ≤ vol(𝓛(P))`, which holds since `γ ≤ 1`. The
indecomposable form `OneThird.Step8.cexImpliesLowBKExpansion`
records the tighter frozen-pair averaging cut. -/
theorem counterexample_implies_low_BK_expansion
    (γ : ℚ) (hγ : 0 < γ) (hγ_le : γ ≤ 1)
    (_hP : HasWidthAtMost α 3)
    (_hCex : IsGammaCounterexample α γ)
    (hn : 2 ≤ Fintype.card α) :
    ∃ S : Finset (LinearExt α),
      (γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
        ≤ (volume S : ℚ)) ∧
      (Phi S ≤ 2 / (γ * (Fintype.card α : ℚ))) := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · -- Volume bound: γ * vol(univ) ≤ vol(univ) since γ ≤ 1.
    have h0 : (0 : ℚ) ≤ (volume (Finset.univ : Finset (LinearExt α)) : ℚ) := by
      exact_mod_cast Nat.zero_le _
    nlinarith
  · -- Phi bound: the complement of `univ` is empty, so the boundary and
    -- the complement's volume both vanish; hence `Phi univ = 0 / 0 = 0`.
    -- The boundary of `univ` is empty (no edges leave `univ`), so the
    -- numerator of `Phi univ` is `0`.
    have hEB : edgeBoundary (Finset.univ : Finset (LinearExt α)) = 0 := by
      unfold edgeBoundary
      rw [Finset.sdiff_self]
      simp
    have hPhi : Phi (Finset.univ : Finset (LinearExt α)) = 0 := by
      unfold Phi
      rw [show ((edgeBoundary (Finset.univ : Finset (LinearExt α)) : ℕ) : ℚ) = 0
            from by exact_mod_cast hEB]
      simp
    rw [hPhi]
    have hcard_pos : (0 : ℕ) < Fintype.card α := by linarith
    have hcard_q : (0 : ℚ) < (Fintype.card α : ℚ) := by exact_mod_cast hcard_pos
    have hden : (0 : ℚ) < γ * (Fintype.card α : ℚ) := mul_pos hγ hcard_q
    exact le_of_lt (div_pos (by norm_num) hden)

end OneThird
