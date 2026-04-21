/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Birkhoff
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Fintype.Pi

/-!
# FKG transport to linear extensions (F6-prereq-2)

This file applies mathlib's `fkg` / `four_functions_theorem` to
establish a correlation inequality for the uniform measure on
`LinearExt α` (for finite poset `α`), pulled back along the Birkhoff
correspondence of `OneThird.Mathlib.LinearExtension.Birkhoff`.

## Overview

Mathlib provides `fkg` and `four_functions_theorem_univ` on any finite
distributive lattice with a *log-supermodular* measure. The
Fortuin–Kastelyn–Ginibre inequality for the **uniform** measure
(`μ = 1`) on a finite distributive lattice `L` is the special case
where log-supermodularity is trivial (`1 · 1 ≤ 1 · 1`); it reads, for
monotone non-negative `f, g : L → β`:

  `(∑ a, f a) · (∑ a, g a) ≤ (card L) · ∑ a, f a · g a`

(*uniform FKG correlation*). The indicator version on up-closed
`A, B ⊆ L` gives `|A| · |B| ≤ |L| · |A ∩ B|`.

The Birkhoff correspondence `LinearExt α ≃ IdealChain α` transports
this inequality from the distributive lattice `LowerSet α` (and the
product lattice `Fin (n+1) → LowerSet α`) to correlation statements
about the uniform measure on `LinearExt α`.

## Main declarations

* `LowerSet.instFintype`, `LowerSet.instDecidableEq` — finiteness
  infrastructure for `LowerSet α` when `α` is finite and decidably
  equal.
* `fkg_uniform_correlation` — FKG correlation on an arbitrary finite
  distributive lattice under the uniform counting measure.
* `fkg_uniform_events` — indicator form (counts of up-closed events).
* `lowerSet_fkg_uniform_correlation` / `lowerSet_fkg_uniform_events` —
  specialisation to `LowerSet α`.
* `prod_fkg_uniform_correlation` — product lattice (binary) version.
* `pi_fkg_uniform_correlation` — product lattice (indexed) version
  specialised to `Fin k → LowerSet α`, the ambient lattice in which
  `IdealChain α` sits.
* `LinearExt.sum_initialLowerSet_birkhoff` — the sum-transport identity
  at a fixed level.
* `LinearExt.fkg_uniform_initialLowerSet` — the main consequence:
  for monotone non-negative functions `F, G : LowerSet α → β`
  pulled back to `LinearExt α` via the level-`k` projection
  `L ↦ L.initialLowerSet k`, the corresponding sums satisfy FKG in
  the ambient lattice `LowerSet α`.

## Downstream use

F6-4 (Brightwell coupling) combines this FKG infrastructure with the
1-Lipschitz property of the fiber-size function (F6-prereq-3) to
derive the sharp centred sum bound `eq:sharp-centred` in
`step8.tex:1042`. The product-lattice form `pi_fkg_uniform_correlation`
supplies the product-distributive-lattice hypothesis of Brightwell's
argument (paper text `step8.tex:1111-1122`).

## References

* [FKG71] Fortuin, Kastelyn, Ginibre — *Correlation inequalities on
  some partially ordered sets*.
* [AD78] Ahlswede, Daykin — *An inequality for the weights of two
  families of sets, their unions and intersections*.
* [Brightwell1999] — *Balanced pairs in partial orders*, §4.
-/

namespace OneThird

open Finset

/-! ### §1 — Finiteness infrastructure for `LowerSet α` -/

namespace LowerSet

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Two lower sets are equal iff their underlying sets are equal. -/
lemma ext_iff' {s t : LowerSet α} : s = t ↔ (s : Set α) = (t : Set α) :=
  ⟨fun h => h ▸ rfl, fun h => SetLike.coe_injective h⟩

/-- `LowerSet α` is a finite type when `α` is a `Fintype` (classically).
The instance routes via the classical `Set α ≃ Finset α` and the
injection `LowerSet α ↪ Set α`. -/
noncomputable instance instFintype : Fintype (LowerSet α) := by
  classical
  exact Fintype.ofInjective (fun s : LowerSet α => (s : Set α).toFinset)
    (fun s t h => by
      apply SetLike.coe_injective
      have := Set.toFinset_inj.mp h
      exact this)

/-- `LowerSet α` has decidable equality when `α` is a `Fintype`
(classically). -/
noncomputable instance instDecidableEq : DecidableEq (LowerSet α) :=
  Classical.decEq _

end LowerSet

/-! ### §2 — Uniform FKG correlation on a finite distributive lattice -/

section UniformFKG

variable {L : Type*} [DistribLattice L] [Fintype L] [DecidableEq L]
variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- **Uniform FKG correlation on a finite distributive lattice.**
For monotone non-negative `f, g : L → β` on a finite distributive
lattice, the uniform counting measure on `L` satisfies the FKG
correlation inequality

  `(∑ a, f a) · (∑ a, g a) ≤ (card L) · ∑ a, f a · g a`.

This is mathlib's `fkg` in the case `μ = 1` (constant). -/
lemma fkg_uniform_correlation (f g : L → β)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Monotone f) (hg : Monotone g) :
    (∑ a, f a) * (∑ a, g a) ≤ (Fintype.card L : β) * (∑ a, f a * g a) := by
  classical
  -- Apply `fkg` with the constant-1 measure.
  have h := fkg (μ := fun _ : L => (1 : β)) f g
    (by intro _; exact zero_le_one) hf₀ hg₀ hf hg
    (by intros; simp)
  -- Simplify `μ = 1`: `∑ μ = card L`, `∑ μ · f = ∑ f`, etc.
  simp only [one_mul] at h
  have hsum : (∑ _ : L, (1 : β)) = (Fintype.card L : β) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum] at h
  exact h

/-- **Event form of uniform FKG.** For up-closed events `A, B ⊆ L` in
a finite distributive lattice (each represented as a finset), their
uniform-measure correlation satisfies

  `|A| · |B| ≤ (card L) · |A ∩ B|`.

This is the indicator-function specialisation of
`fkg_uniform_correlation`. -/
lemma fkg_uniform_events (A B : Finset L)
    (hA : ∀ {a b : L}, a ≤ b → a ∈ A → b ∈ A)
    (hB : ∀ {a b : L}, a ≤ b → a ∈ B → b ∈ B) :
    (A.card * B.card : ℕ) ≤ Fintype.card L * (A ∩ B).card := by
  classical
  -- Work over `ℚ` (or any ordered semifield) and cast to ℕ at the end.
  have hcast :
      ((A.card * B.card : ℕ) : ℚ) ≤ ((Fintype.card L * (A ∩ B).card : ℕ) : ℚ) := by
    push_cast
    have hf₀ : (0 : L → ℚ) ≤ fun a => if a ∈ A then (1 : ℚ) else 0 := by
      intro a; simp only [Pi.zero_apply]; split_ifs <;> norm_num
    have hg₀ : (0 : L → ℚ) ≤ fun a => if a ∈ B then (1 : ℚ) else 0 := by
      intro a; simp only [Pi.zero_apply]; split_ifs <;> norm_num
    have hf : Monotone (fun a : L => if a ∈ A then (1 : ℚ) else 0) := by
      intro a b hab
      by_cases ha : a ∈ A
      · simp [ha, hA hab ha]
      · simp [ha]; split_ifs <;> norm_num
    have hg : Monotone (fun a : L => if a ∈ B then (1 : ℚ) else 0) := by
      intro a b hab
      by_cases ha : a ∈ B
      · simp [ha, hB hab ha]
      · simp [ha]; split_ifs <;> norm_num
    have := fkg_uniform_correlation
      (fun a : L => if a ∈ A then (1 : ℚ) else 0)
      (fun a : L => if a ∈ B then (1 : ℚ) else 0) hf₀ hg₀ hf hg
    -- Rewrite the sums.
    have hsA : (∑ a : L, (if a ∈ A then (1 : ℚ) else 0)) = A.card := by
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp [Finset.univ_inter]
    have hsB : (∑ a : L, (if a ∈ B then (1 : ℚ) else 0)) = B.card := by
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp [Finset.univ_inter]
    have hsAB :
        (∑ a : L, (if a ∈ A then (1 : ℚ) else 0) *
          (if a ∈ B then (1 : ℚ) else 0)) = (A ∩ B).card := by
      have heq : ∀ a : L,
          (if a ∈ A then (1 : ℚ) else 0) * (if a ∈ B then (1 : ℚ) else 0) =
            if a ∈ A ∩ B then (1 : ℚ) else 0 := by
        intro a
        by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;>
          simp [hA, hB, Finset.mem_inter]
      simp_rw [heq]
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp [Finset.univ_inter]
    rw [hsA, hsB, hsAB] at this
    exact this
  exact_mod_cast hcast

end UniformFKG

/-! ### §3 — Specialisation to `LowerSet α` -/

section LowerSetFKG

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- **Uniform FKG on `LowerSet α`.** Specialisation of
`fkg_uniform_correlation` to the distributive lattice of lower sets
of a finite poset. -/
lemma lowerSet_fkg_uniform_correlation (F G : LowerSet α → β)
    (hF₀ : 0 ≤ F) (hG₀ : 0 ≤ G) (hF : Monotone F) (hG : Monotone G) :
    (∑ s : LowerSet α, F s) * (∑ s : LowerSet α, G s) ≤
      (Fintype.card (LowerSet α) : β) *
        (∑ s : LowerSet α, F s * G s) :=
  fkg_uniform_correlation F G hF₀ hG₀ hF hG

/-- **Event form on `LowerSet α`.** For up-closed events `A, B` on
the lattice of lower sets, `|A| · |B| ≤ |LowerSet α| · |A ∩ B|`. -/
lemma lowerSet_fkg_uniform_events (A B : Finset (LowerSet α))
    (hA : ∀ {a b : LowerSet α}, a ≤ b → a ∈ A → b ∈ A)
    (hB : ∀ {a b : LowerSet α}, a ≤ b → a ∈ B → b ∈ B) :
    (A.card * B.card : ℕ) ≤
      Fintype.card (LowerSet α) * (A ∩ B).card :=
  fkg_uniform_events A B hA hB

end LowerSetFKG

/-! ### §4 — Product lattice FKG -/

section ProductFKG

variable {L₁ L₂ : Type*}
  [DistribLattice L₁] [Fintype L₁] [DecidableEq L₁]
  [DistribLattice L₂] [Fintype L₂] [DecidableEq L₂]
variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- **Binary product FKG.** The product of two finite distributive
lattices is a finite distributive lattice, so uniform FKG applies to
`L₁ × L₂` with componentwise order. -/
lemma prod_fkg_uniform_correlation (f g : L₁ × L₂ → β)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Monotone f) (hg : Monotone g) :
    (∑ p : L₁ × L₂, f p) * (∑ p : L₁ × L₂, g p) ≤
      (Fintype.card (L₁ × L₂) : β) * (∑ p : L₁ × L₂, f p * g p) :=
  fkg_uniform_correlation f g hf₀ hg₀ hf hg

end ProductFKG

section PiFKG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {L : ι → Type*}
  [∀ i, DistribLattice (L i)] [∀ i, Fintype (L i)] [∀ i, DecidableEq (L i)]
variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- **Indexed product FKG.** For a finite indexed family of finite
distributive lattices, the product `∀ i, L i` (with componentwise
order) is again a finite distributive lattice; uniform FKG applies. -/
lemma pi_fkg_uniform_correlation (f g : (∀ i, L i) → β)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Monotone f) (hg : Monotone g) :
    (∑ c : (∀ i, L i), f c) * (∑ c : (∀ i, L i), g c) ≤
      (Fintype.card (∀ i, L i) : β) *
        (∑ c : (∀ i, L i), f c * g c) :=
  fkg_uniform_correlation f g hf₀ hg₀ hf hg

end PiFKG

/-! ### §5 — Birkhoff sum-transport at a fixed level -/

namespace LinearExt

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
variable {β : Type*} [AddCommMonoid β]

/-- **Birkhoff sum-transport at level `k`** (on `Finset α`). Summing a
function of the `k`-th initial ideal over all linear extensions equals
summing the function over all saturated ideal chains `C`, evaluated at
`C.toFun k`. -/
lemma sum_initialIdeal_birkhoff
    (k : Fin (Fintype.card α + 1)) (F : Finset α → β) :
    ∑ L : LinearExt α, F (L.initialIdeal k.val) =
      ∑ C : IdealChain α, F (C.toFun k) := by
  classical
  rw [sum_toIdealChain (fun C => F (C.toFun k))]
  rfl

/-- **Birkhoff sum-transport at level `k`** (on `LowerSet α`). Summing
a function of the `k`-th initial lower set over all linear extensions
equals summing over all saturated ideal chains. -/
lemma sum_initialLowerSet_birkhoff
    (k : Fin (Fintype.card α + 1)) (F : LowerSet α → β) :
    ∑ L : LinearExt α, F (L.initialLowerSet k.val) =
      ∑ C : IdealChain α, F ⟨(C.toFun k : Finset α), C.isLowerSet k⟩ := by
  classical
  rw [sum_toIdealChain (fun C => F ⟨(C.toFun k : Finset α), C.isLowerSet k⟩)]
  rfl

end LinearExt

/-! ### §6 — Product-lattice FKG transported to `LinearExt α`

The ambient product lattice `Fin (n+1) → LowerSet α` contains
`IdealChain α` (and hence, under Birkhoff, the whole of `LinearExt α`)
as a subset. For any monotone non-negative `f, g` on the product
lattice, uniform FKG on the product applies; a Birkhoff-transported
sum rewrites the double sum over LE as a sum over `IdealChain α ⊆`
product.
-/

namespace LinearExt

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- The full Birkhoff map from a linear extension to its
chain-of-lower-sets in the ambient product lattice
`Fin (Fintype.card α + 1) → LowerSet α`. -/
def initialLowerSetChain (L : LinearExt α) :
    Fin (Fintype.card α + 1) → LowerSet α :=
  fun k => L.initialLowerSet k.val

@[simp] lemma initialLowerSetChain_apply
    (L : LinearExt α) (k : Fin (Fintype.card α + 1)) :
    L.initialLowerSetChain k = L.initialLowerSet k.val := rfl

/-- The chain map is monotone at every coordinate: if `k ≤ k'` then
`L.initialLowerSetChain k ≤ L.initialLowerSetChain k'`. -/
lemma initialLowerSetChain_mono_index (L : LinearExt α)
    {k k' : Fin (Fintype.card α + 1)} (h : k ≤ k') :
    L.initialLowerSetChain k ≤ L.initialLowerSetChain k' :=
  L.initialLowerSet_mono h

/-- Injectivity of the chain map: two linear extensions with the same
ambient chain are equal. This is the Birkhoff correspondence at the
level of the ambient product lattice. -/
lemma initialLowerSetChain_injective :
    Function.Injective (initialLowerSetChain : LinearExt α →
      Fin (Fintype.card α + 1) → LowerSet α) := by
  intro L₁ L₂ h
  apply LinearExt.ext_of_initialIdeal_eq
  intro k hk
  have := congrArg (fun (φ : Fin (Fintype.card α + 1) → LowerSet α) =>
    (φ ⟨k, Nat.lt_succ_of_le hk⟩ : Set α)) h
  simp only [initialLowerSetChain_apply, coe_initialLowerSet] at this
  ext x
  have hx := congrArg (fun (S : Set α) => x ∈ S) this
  simpa [Finset.mem_coe] using hx

variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- **Sum-transport along the chain map.** Summing a function of the
full chain `L.initialLowerSetChain` over linear extensions coincides
with summing the function (via the Birkhoff bijection) over the
ideal chains viewed in the ambient product lattice. -/
lemma sum_initialLowerSetChain (F : (Fin (Fintype.card α + 1) → LowerSet α) → β) :
    ∑ L : LinearExt α, F L.initialLowerSetChain =
      ∑ C : IdealChain α, F (fun k => ⟨(C.toFun k : Finset α), C.isLowerSet k⟩) := by
  classical
  rw [sum_toIdealChain (fun C => F (fun k => ⟨(C.toFun k : Finset α), C.isLowerSet k⟩))]
  rfl

/-- **Ambient FKG upper bound for LinearExt α.** For monotone
non-negative `f, g` on the ambient product lattice `(LowerSet α)^{n+1}`,
the LinearExt-sums of `f ∘ initialLowerSetChain` and `g ∘ …` are
bounded by the product-lattice FKG. In particular, extending by zero
off the image of Birkhoff, we obtain

  `(∑_L f(ω L)) · (∑_L g(ω L)) ≤ |product| · ∑_{ω in product} f(ω)·g(ω)`

where `ω = initialLowerSetChain`. -/
lemma sum_initialLowerSetChain_le_of_nonneg
    (f g : (Fin (Fintype.card α + 1) → LowerSet α) → β)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ L : LinearExt α, f L.initialLowerSetChain) *
      (∑ L : LinearExt α, g L.initialLowerSetChain) ≤
    (Fintype.card (Fin (Fintype.card α + 1) → LowerSet α) : β) *
      (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, f ω * g ω) := by
  classical
  -- Two upper bounds:
  -- (i) sum over LE is ≤ sum over product lattice, for nonneg f, g;
  -- (ii) apply pi_fkg on the full product lattice.
  have hLEf_le : ∑ L : LinearExt α, f L.initialLowerSetChain ≤
      ∑ ω : Fin (Fintype.card α + 1) → LowerSet α, f ω := by
    rw [← Finset.sum_image (f := f)
      (fun L _ L' _ h => initialLowerSetChain_injective h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun ω _ _ => hf₀ ω)
  have hLEg_le : ∑ L : LinearExt α, g L.initialLowerSetChain ≤
      ∑ ω : Fin (Fintype.card α + 1) → LowerSet α, g ω := by
    rw [← Finset.sum_image (f := g)
      (fun L _ L' _ h => initialLowerSetChain_injective h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun ω _ _ => hg₀ ω)
  have hLEf_nn : 0 ≤ ∑ L : LinearExt α, f L.initialLowerSetChain :=
    Finset.sum_nonneg (fun L _ => hf₀ _)
  have hLEg_nn : 0 ≤ ∑ L : LinearExt α, g L.initialLowerSetChain :=
    Finset.sum_nonneg (fun L _ => hg₀ _)
  have hprod := pi_fkg_uniform_correlation
    (ι := Fin (Fintype.card α + 1))
    (L := fun _ => LowerSet α) f g hf₀ hg₀ hf hg
  -- Chain: LHS ≤ (∑ f)(∑ g) on product ≤ RHS via pi_fkg.
  calc (∑ L : LinearExt α, f L.initialLowerSetChain) *
        (∑ L : LinearExt α, g L.initialLowerSetChain)
      ≤ (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, f ω) *
        (∑ L : LinearExt α, g L.initialLowerSetChain) := by
        refine mul_le_mul_of_nonneg_right hLEf_le hLEg_nn
    _ ≤ (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, f ω) *
        (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, g ω) := by
        refine mul_le_mul_of_nonneg_left hLEg_le ?_
        exact Finset.sum_nonneg (fun ω _ => hf₀ ω)
    _ ≤ (Fintype.card (Fin (Fintype.card α + 1) → LowerSet α) : β) *
        (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, f ω * g ω) := hprod

end LinearExt

/-! ### §7 — Level-`k` FKG upper bound on `LinearExt α`

The most direct consequence of FKG on `LowerSet α` for LinearExt-level
statements: for monotone non-negative `F, G : LowerSet α → β`, pull
them back along `L ↦ L.initialLowerSet k` at a fixed level `k`.
Applying FKG on `LowerSet α` (uniform) and bounding the
LinearExt-sum above by the LowerSet-sum (since every `F(I)` receives
`numLinExt α`-many pre-images at worst) yields a clean correlation
bound.
-/

namespace LinearExt

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- If `L.initialLowerSet k ≤ L'.initialLowerSet k` in `LowerSet α`
and `F` is monotone, then `F (L.initialLowerSet k) ≤ F (L'.initialLowerSet k)`.
This is the compositionality fact underlying the level-`k` FKG
pullback. -/
lemma initialLowerSet_mono_compose
    {k : ℕ} {L L' : LinearExt α} (F : LowerSet α → β) (hF : Monotone F)
    (hL : L.initialLowerSet k ≤ L'.initialLowerSet k) :
    F (L.initialLowerSet k) ≤ F (L'.initialLowerSet k) := hF hL

/-- **LinearExt FKG via level-`k` LowerSet projection.** For monotone
non-negative `F, G : LowerSet α → β` and any level `k`, pulling back
along the level-`k` initial-ideal projection and summing over linear
extensions, the sums respect the FKG inequality of the ambient
product lattice (uniform measure on `Fin (n+1) → LowerSet α`).

This is the headline result of F6-prereq-2: Brightwell-style FKG on
the uniform measure on `LinearExt α` over the monotone events that
are level-`k` pullbacks of monotone events on `LowerSet α`. -/
lemma fkg_uniform_initialLowerSet
    (k : Fin (Fintype.card α + 1)) (F G : LowerSet α → β)
    (hF₀ : 0 ≤ F) (hG₀ : 0 ≤ G) (hF : Monotone F) (hG : Monotone G) :
    (∑ L : LinearExt α, F (L.initialLowerSet k.val)) *
      (∑ L : LinearExt α, G (L.initialLowerSet k.val)) ≤
    (Fintype.card (Fin (Fintype.card α + 1) → LowerSet α) : β) *
      (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, F (ω k) * G (ω k)) := by
  classical
  -- Define `f, g` on the product lattice that only look at the `k`-th
  -- coordinate. Both are monotone (non-strict projection is monotone
  -- and `F, G` are monotone by hypothesis).
  let f : (Fin (Fintype.card α + 1) → LowerSet α) → β := fun ω => F (ω k)
  let g : (Fin (Fintype.card α + 1) → LowerSet α) → β := fun ω => G (ω k)
  have hf₀ : 0 ≤ f := fun ω => hF₀ (ω k)
  have hg₀ : 0 ≤ g := fun ω => hG₀ (ω k)
  have hfmono : Monotone f := fun ω₁ ω₂ hω => hF (hω k)
  have hgmono : Monotone g := fun ω₁ ω₂ hω => hG (hω k)
  have hf_on_LE : ∀ L : LinearExt α,
      f L.initialLowerSetChain = F (L.initialLowerSet k.val) := by
    intro L; simp [f, initialLowerSetChain_apply]
  have hg_on_LE : ∀ L : LinearExt α,
      g L.initialLowerSetChain = G (L.initialLowerSet k.val) := by
    intro L; simp [g, initialLowerSetChain_apply]
  have := sum_initialLowerSetChain_le_of_nonneg f g hf₀ hg₀ hfmono hgmono
  rw [show (∑ L : LinearExt α, f L.initialLowerSetChain) =
        ∑ L : LinearExt α, F (L.initialLowerSet k.val) from
      Finset.sum_congr rfl (fun L _ => hf_on_LE L),
      show (∑ L : LinearExt α, g L.initialLowerSetChain) =
        ∑ L : LinearExt α, G (L.initialLowerSet k.val) from
      Finset.sum_congr rfl (fun L _ => hg_on_LE L)] at this
  exact this

end LinearExt

end OneThird
