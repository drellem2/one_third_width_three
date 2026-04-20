/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step5.SecondMoment
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 6 — Rich-case lower bound on `M` (`lem:gap-G5`)

Formalises the rich-case lower bound subsection of `step6.tex`
(`step6.tex:1160-1273`).

Define, for each `α ∈ Rich⋆`, the good-fiber with bad-set removed
`F⋆_α := F_α ∖ B_α`, and the pairwise weighted overlap
`w_{α,β} := |F⋆_α ∩ F⋆_β| = |(F_α ∩ F_β) ∖ (B_α ∪ B_β)|`. Set

  `M := ∑_{α,β ∈ Rich⋆} w_{α,β}`,
  `I(L) := |{α ∈ Rich⋆ : L ∈ F⋆_α}|`.

The paper's Lemma `lem:gap-G5` has three clauses:

* **(i) Exact identity.** `M = ∑_{L ∈ LE(P)} I(L)²`.
  Proof: double-count triples `(L, α, β)` with `L ∈ F⋆_α ∩ F⋆_β`.
* **(ii) Rich-case lower bound.** Under the rich case of Step 5, the
  first-moment bound `c_T · |LE(P)| ≤ ∑_α |F⋆_α|` combined with
  Cauchy–Schwarz yields `c_T² · |LE(P)| ≤ ∑_L I(L)² = M`.
* **(iii) Volume comparison.** For any conductance normalization
  with `vol(S) ≤ |LE(P)|`, the same bound gives `c_T² · vol(S) ≤ M`.

## Main results

* `second_moment_eq_pair_overlap_sum` — identity (i):
  `∑_L I(L)² = ∑_{α,β ∈ Rich⋆} w_{α,β}`.
* `pair_overlap_sum_ge_firstMoment_sq` — rich-case lower bound (ii) in
  cleared-denominator form: `c² · |LP| ≤ ∑_{α,β} w_{α,β}`.
* `pair_overlap_sum_ge_vol` — volume comparison (iii):
  `c² · vol_S ≤ ∑_{α,β} w_{α,β}` when `vol_S ≤ |LP|`.
-/

namespace OneThird
namespace Step6

open Finset OneThird.Step5
open scoped BigOperators

/-! ### Pairwise overlap weight and its decomposition -/

section Weights

variable {Pair LinExt : Type*} [DecidableEq LinExt]

/-- **Pairwise overlap weight** `w_{α,β}` (`step6.tex:247-253`,
`step6.tex:1162`). With `F⋆_α := F_α ∖ B_α`, the weight is
`|F⋆_α ∩ F⋆_β|`. We use the `Fstar : Pair → Finset LinExt` family
(fibers already bad-set-subtracted) as the abstract primitive. -/
def pairOverlap (Fstar : Pair → Finset LinExt) (α β : Pair) : ℕ :=
  (Fstar α ∩ Fstar β).card

/-- Pointwise decomposition of `I(L)²` as a sum over ordered pairs:

  `I(L)² = ∑_{α,β} 𝟙[L ∈ F⋆_α ∩ F⋆_β]`.

This is the key algebraic step behind `lem:gap-G5`(i). -/
lemma visibility_sq_eq_sum_pairs
    (richStar : Finset Pair) (Fstar : Pair → Finset LinExt)
    (L : LinExt) :
    (visibility richStar Fstar L) ^ 2
      = ∑ p ∈ richStar ×ˢ richStar,
          (if L ∈ Fstar p.1 ∩ Fstar p.2 then (1 : ℕ) else 0) := by
  classical
  unfold visibility
  -- |richStar.filter (L ∈ Fstar α)|² = (∑_α 𝟙[L ∈ Fstar α])²
  --  = ∑_{α,β} 𝟙[L ∈ Fstar α] · 𝟙[L ∈ Fstar β]
  --  = ∑_{α,β} 𝟙[L ∈ Fstar α ∩ Fstar β]
  have key :
      (richStar.filter (fun α => L ∈ Fstar α)).card
        = ∑ α ∈ richStar, (if L ∈ Fstar α then (1 : ℕ) else 0) := by
    rw [Finset.card_filter]
  rw [key]
  -- (∑_α 𝟙α)² = ∑_{α,β} 𝟙α · 𝟙β, i.e. Finset.sum_mul_sum applied to the indicator.
  have hsq :
      (∑ α ∈ richStar, (if L ∈ Fstar α then (1 : ℕ) else 0)) ^ 2
        = (∑ α ∈ richStar, (if L ∈ Fstar α then (1 : ℕ) else 0))
            * (∑ β ∈ richStar, (if L ∈ Fstar β then (1 : ℕ) else 0)) := by
    ring
  rw [hsq]
  rw [Finset.sum_mul_sum]
  -- Now show ∑_{α,β} 𝟙α · 𝟙β = ∑_{α,β} 𝟙[α∩β].
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  -- Need: (if L ∈ Fstar α) * (if L ∈ Fstar β) = if L ∈ Fstar α ∩ Fstar β then 1 else 0.
  simp only [Finset.mem_inter]
  by_cases hα : L ∈ Fstar α
  · by_cases hβ : L ∈ Fstar β
    · simp [hα, hβ]
    · simp [hα, hβ]
  · simp [hα]

/-- **Sum-swap lemma.** For a finite "universe" `LP` and ordered pairs
`(α, β) ∈ RS × RS`, swapping sums gives

  `∑_{L ∈ LP} ∑_{(α,β)} 𝟙[L ∈ F⋆_α ∩ F⋆_β]
     = ∑_{(α,β)} |F⋆_α ∩ F⋆_β ∩ LP|`.

When each `F⋆_α ⊆ LP`, the right-hand side simplifies to
`∑_{(α,β)} |F⋆_α ∩ F⋆_β| = ∑_{(α,β)} w_{α,β}`. -/
lemma sum_indicator_pairs_swap
    (LP : Finset LinExt) (richStar : Finset Pair)
    (Fstar : Pair → Finset LinExt)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP) :
    ∑ L ∈ LP, ∑ p ∈ richStar ×ˢ richStar,
        (if L ∈ Fstar p.1 ∩ Fstar p.2 then (1 : ℕ) else 0)
      = ∑ p ∈ richStar ×ˢ richStar,
          pairOverlap Fstar p.1 p.2 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  rintro ⟨α, β⟩ hp
  rw [Finset.mem_product] at hp
  obtain ⟨hα, _hβ⟩ := hp
  unfold pairOverlap
  -- ∑_{L ∈ LP} 𝟙[L ∈ Fstar α ∩ Fstar β] = |Fstar α ∩ Fstar β|
  -- because Fstar α ⊆ LP ⇒ Fstar α ∩ Fstar β ⊆ LP.
  have h : Fstar α ∩ Fstar β ⊆ LP := by
    intro L hL
    rw [Finset.mem_inter] at hL
    exact hsub α hα hL.1
  calc ∑ L ∈ LP, (if L ∈ Fstar α ∩ Fstar β then (1 : ℕ) else 0)
      = (LP.filter (fun L => L ∈ Fstar α ∩ Fstar β)).card := by
        rw [Finset.card_filter]
    _ = (Fstar α ∩ Fstar β).card := by
        congr 1
        apply Finset.Subset.antisymm
        · intro L hL
          rw [Finset.mem_filter] at hL
          exact hL.2
        · intro L hL
          rw [Finset.mem_filter]
          exact ⟨h hL, hL⟩

end Weights

/-! ### `lem:gap-G5`(i) — exact identity `M = ∑ I(L)²` -/

section Identity

variable {Pair LinExt : Type*} [DecidableEq LinExt]

/-- **`lem:gap-G5`(i)** (`step6.tex:1168`): the second moment of the
visibility count equals the pairwise overlap sum `M`.

  `∑_{L ∈ LP} I(L)² = ∑_{(α,β) ∈ Rich⋆ × Rich⋆} w_{α,β}`.

The identity is exact (no `O`-term): the bad-set exclusions
`B_α ∪ B_β` are baked into the definition of `w_{α,β}` via
`F⋆_α := F_α ∖ B_α`, and `I(L)` is taken over `Rich⋆`. -/
theorem second_moment_eq_pair_overlap_sum
    (LP : Finset LinExt) (richStar : Finset Pair)
    (Fstar : Pair → Finset LinExt)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP) :
    ∑ L ∈ LP, (visibility richStar Fstar L) ^ 2
      = ∑ p ∈ richStar ×ˢ richStar,
          pairOverlap Fstar p.1 p.2 := by
  classical
  -- Rewrite each I(L)² using visibility_sq_eq_sum_pairs, then swap sums.
  have hrw : ∀ L ∈ LP,
      (visibility richStar Fstar L) ^ 2
        = ∑ p ∈ richStar ×ˢ richStar,
            (if L ∈ Fstar p.1 ∩ Fstar p.2 then (1 : ℕ) else 0) := by
    intro L _; exact visibility_sq_eq_sum_pairs richStar Fstar L
  calc ∑ L ∈ LP, (visibility richStar Fstar L) ^ 2
      = ∑ L ∈ LP, ∑ p ∈ richStar ×ˢ richStar,
          (if L ∈ Fstar p.1 ∩ Fstar p.2 then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl hrw
    _ = ∑ p ∈ richStar ×ˢ richStar,
          pairOverlap Fstar p.1 p.2 :=
        sum_indicator_pairs_swap LP richStar Fstar hsub

end Identity

/-! ### `lem:gap-G5`(ii) — rich-case lower bound on `M` -/

section RichLowerBound

variable {Pair LinExt : Type*} [DecidableEq LinExt]

/-- **`lem:gap-G5`(ii)** (`step6.tex:1213-1237`): rich-case lower bound
on `M`.

From the Step-5 first-moment hypothesis `c · |LP| ≤ ∑_α |F⋆_α|`,
together with the containment `F⋆_α ⊆ LP` for each α, Cauchy–Schwarz
yields `c² · |LP| ≤ ∑_L I(L)²`, and by `lem:gap-G5`(i) this equals
`∑_{α,β} w_{α,β} = M`. -/
theorem pair_overlap_sum_ge_firstMoment_sq
    (LP : Finset LinExt) (richStar : Finset Pair)
    (Fstar : Pair → Finset LinExt) (c : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card) :
    c ^ 2 * LP.card
      ≤ ∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2 := by
  classical
  have h1 :=
    second_moment_visibility richStar Fstar LP c hsub hfirst
  have h2 :=
    second_moment_eq_pair_overlap_sum LP richStar Fstar hsub
  linarith

end RichLowerBound

/-! ### `lem:gap-G5`(iii) — volume comparison -/

section VolumeComparison

variable {Pair LinExt : Type*} [DecidableEq LinExt]

/-- **`lem:gap-G5`(iii)** (`step6.tex:1241-1250`): the same rich-case
bound against any admissible volume normalization with `vol(S) ≤ |LP|`.

Under the counting normalization `vol(S) = |S| ≤ |LP|`, the lower bound
transfers: `c² · vol(S) ≤ M`. -/
theorem pair_overlap_sum_ge_vol
    (LP : Finset LinExt) (richStar : Finset Pair)
    (Fstar : Pair → Finset LinExt) (c volS : ℕ)
    (hsub : ∀ α ∈ richStar, Fstar α ⊆ LP)
    (hfirst : c * LP.card ≤ ∑ α ∈ richStar, (Fstar α).card)
    (hvol : volS ≤ LP.card) :
    c ^ 2 * volS
      ≤ ∑ p ∈ richStar ×ˢ richStar, pairOverlap Fstar p.1 p.2 := by
  classical
  have h := pair_overlap_sum_ge_firstMoment_sq LP richStar Fstar c hsub hfirst
  have h' : c ^ 2 * volS ≤ c ^ 2 * LP.card := Nat.mul_le_mul_left _ hvol
  exact h'.trans h

end VolumeComparison

/-! ### Closing remark — absorbed constants (`rem:G5-closes-dichotomy`) -/

section Closure

variable {Pair LinExt : Type*} [DecidableEq LinExt]

/-- **`rem:G5-closes-dichotomy`** (`step6.tex:1264-1273`): combining
`pair_overlap_sum_ge_vol` with Step 6's expansion case gives
`|∂S| ≥ η · M ≥ η · c² · vol(S)`, i.e. conductance `≥ η c²`.

Abstract form: from `η · M ≤ |∂S|` and `c² · vol(S) ≤ M`, conclude
`η · c² · vol(S) ≤ |∂S|`. -/
theorem conductance_closure
    (η c volS M boundary : ℕ)
    (hexp : η * M ≤ boundary)
    (hrich : c ^ 2 * volS ≤ M) :
    η * c ^ 2 * volS ≤ boundary := by
  have h1 : η * (c ^ 2 * volS) ≤ η * M := Nat.mul_le_mul_left _ hrich
  calc η * c ^ 2 * volS
      = η * (c ^ 2 * volS) := by ring
    _ ≤ η * M := h1
    _ ≤ boundary := hexp

end Closure

end Step6
end OneThird
