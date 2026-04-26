/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.Birkhoff
import OneThird.Mathlib.LinearExtension.FKG

/-!
# FKG infrastructure for `RelationPoset α`

This file ports the FKG infrastructure of
`OneThird.Mathlib.LinearExtension.FKG` from the typeclass-based
`[PartialOrder α]` setting to the data-version
`Q : RelationPoset α`. The cornerstone is the Birkhoff transport of
A8-S2-cont-3 (`OneThird.Mathlib.RelationPoset.Birkhoff`).

## Main declarations

* `RelationPoset.LowerSet' Q` — finsets of `α` that are closed under
  `Q.le`-down (the data analogue of `LowerSet (Q.asPartialOrder)`),
  packaged so the `LowerSet'` family forms a finite distributive
  lattice on which mathlib's `fkg_uniform_correlation` applies.
* `RelationPoset.LinearExt'.initialLowerSet'` — initial ideal of a
  linear extension as a `LowerSet' Q`.
* `RelationPoset.LinearExt'.fkg_uniform_initialLowerSet'` — port of
  `LinearExt.fkg_uniform_initialLowerSet`: for monotone non-negative
  `F, G : LowerSet' Q → β` and a level `k`, the LinearExt'-sums of
  `F ∘ initialLowerSet' k` and `G ∘ …` satisfy the level-`k` FKG
  upper bound from the ambient product lattice.
* `RelationPoset.sum_initialIdeal'_mono_of_subseteq` — sub-poset
  monotonicity for non-negative functionals: if `Q.Subseteq Q'`, then
  the LinearExt'-sum over `Q'` is `≤` the LinearExt'-sum over `Q`.
  This is the FKG monotonicity-under-augmentation **absolute** form
  (no probability normalisation): adding comparabilities can only
  *shrink* the LinearExt'-sum of any non-negative integrand.
* `RelationPoset.probLT'_mono_of_relExt` — the probability-normalised
  cross-poset coupling lemma proven via the typeclass-based FKG of
  `LinearExt.fkg_uniform_initialLowerSet`, lifted to `RelationPoset α`
  through `Q.asPartialOrder`.

## Reference

* `step8.tex` `prop:in-situ-balanced` Case 2 (`3001-3032`).
* `OneThird.Mathlib.LinearExtension.FKG` — the typeclass-based parent
  module mirrored here.
-/

namespace OneThird

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — `LowerSet' Q`: finsets closed under `Q.le`-down

This is the data analogue of `LowerSet (Q.asPartialOrder)`. We bundle
the `Finset α` carrier with the closure proof so that membership and
equality of `LowerSet' Q` values are decidable in the natural way. -/

/-- A **`Q`-lower-set** is a `Finset α` closed under `Q.le`-down. -/
@[ext]
structure LowerSet' (Q : RelationPoset α) where
  /-- Underlying finset. -/
  carrier : Finset α
  /-- Closed under `Q.le`-down. -/
  lower : ∀ ⦃x y : α⦄, Q.le x y → y ∈ carrier → x ∈ carrier

namespace LowerSet'

variable {Q : RelationPoset α}

instance instMembership : Membership α (LowerSet' Q) :=
  ⟨fun S x => x ∈ S.carrier⟩

@[simp] lemma mem_iff {S : LowerSet' Q} {x : α} :
    x ∈ S ↔ x ∈ S.carrier := Iff.rfl

@[simp] lemma mem_mk {carrier : Finset α}
    {hl : ∀ ⦃x y : α⦄, Q.le x y → y ∈ carrier → x ∈ carrier} {x : α} :
    x ∈ (⟨carrier, hl⟩ : LowerSet' Q) ↔ x ∈ carrier := Iff.rfl

instance instDecidableMem (S : LowerSet' Q) (x : α) : Decidable (x ∈ S) :=
  inferInstanceAs (Decidable (x ∈ S.carrier))

instance instDecidableEq : DecidableEq (LowerSet' Q) := fun S T =>
  decidable_of_iff (S.carrier = T.carrier) ⟨LowerSet'.ext, fun h => h ▸ rfl⟩

/-! ### §2 — Lattice structure on `LowerSet' Q` -/

/-- The empty `Q`-lower-set. -/
def empty (Q : RelationPoset α) : LowerSet' Q where
  carrier := ∅
  lower := fun _ _ _ h => (Finset.notMem_empty _ h).elim

/-- The full `Q`-lower-set (all of `α`). -/
def univ (Q : RelationPoset α) : LowerSet' Q where
  carrier := Finset.univ
  lower := fun _ _ _ _ => Finset.mem_univ _

/-- Intersection of `Q`-lower-sets. -/
def inter (S T : LowerSet' Q) : LowerSet' Q where
  carrier := S.carrier ∩ T.carrier
  lower := fun _ _ hxy hy => by
    rw [Finset.mem_inter] at hy ⊢
    exact ⟨S.lower hxy hy.1, T.lower hxy hy.2⟩

/-- Union of `Q`-lower-sets. -/
def union (S T : LowerSet' Q) : LowerSet' Q where
  carrier := S.carrier ∪ T.carrier
  lower := fun _ _ hxy hy => by
    rw [Finset.mem_union] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (S.lower hxy hy)
    · exact Or.inr (T.lower hxy hy)

/-- Distributive lattice instance on `LowerSet' Q`. -/
instance instDistribLattice : DistribLattice (LowerSet' Q) where
  le S T := S.carrier ⊆ T.carrier
  le_refl S := Finset.Subset.refl _
  le_trans S₁ S₂ S₃ h₁₂ h₂₃ := Finset.Subset.trans h₁₂ h₂₃
  le_antisymm S T h₁ h₂ := by
    apply LowerSet'.ext
    exact Finset.Subset.antisymm h₁ h₂
  sup S T := S.union T
  inf S T := S.inter T
  le_sup_left _ _ := Finset.subset_union_left
  le_sup_right _ _ := Finset.subset_union_right
  sup_le _ _ _ h₁ h₂ := Finset.union_subset h₁ h₂
  inf_le_left _ _ := Finset.inter_subset_left
  inf_le_right _ _ := Finset.inter_subset_right
  le_inf _ _ _ h₁ h₂ := Finset.subset_inter h₁ h₂
  le_sup_inf S T U := by
    -- (S ⊔ T) ⊓ (S ⊔ U) ≤ S ⊔ (T ⊓ U). On finsets: standard distributivity.
    change ((S.union T).inter (S.union U)).carrier ⊆
           (S.union (T.inter U)).carrier
    intro x hx
    simp only [union, inter, Finset.mem_inter, Finset.mem_union] at hx ⊢
    obtain ⟨h₁, h₂⟩ := hx
    rcases h₁ with hS | hT
    · exact Or.inl hS
    · rcases h₂ with hS | hU
      · exact Or.inl hS
      · exact Or.inr ⟨hT, hU⟩

@[simp] lemma le_iff (S T : LowerSet' Q) :
    S ≤ T ↔ S.carrier ⊆ T.carrier := Iff.rfl

@[simp] lemma carrier_inf (S T : LowerSet' Q) :
    (S ⊓ T).carrier = S.carrier ∩ T.carrier := rfl

@[simp] lemma carrier_sup (S T : LowerSet' Q) :
    (S ⊔ T).carrier = S.carrier ∪ T.carrier := rfl

/-! ### §3 — Fintype on `LowerSet' Q` -/

/-- `LowerSet' Q` injects into `Finset α` (via `carrier`), so it is
itself a `Fintype` (filtered by the lower-set condition). -/
noncomputable instance instFintype (Q : RelationPoset α) :
    Fintype (LowerSet' Q) := by
  classical
  refine Fintype.ofInjective (fun S : LowerSet' Q => S.carrier) ?_
  intro S T h
  exact LowerSet'.ext h

end LowerSet'

/-! ### §4 — `LinearExt'.initialLowerSet'` -/

namespace LinearExt'

variable {Q : RelationPoset α}

/-- `L.initialIdeal' k`, packaged as a `LowerSet' Q`. -/
def initialLowerSet' (L : LinearExt' Q) (k : ℕ) : LowerSet' Q where
  carrier := L.initialIdeal' k
  lower := fun _ _ hxy hy => L.initialIdeal'_isLowerSet k hxy hy

@[simp] lemma carrier_initialLowerSet' (L : LinearExt' Q) (k : ℕ) :
    (L.initialLowerSet' k).carrier = L.initialIdeal' k := rfl

@[simp] lemma mem_initialLowerSet' (L : LinearExt' Q) (k : ℕ) (x : α) :
    x ∈ L.initialLowerSet' k ↔ (L.pos x).val < k := by
  change x ∈ (L.initialLowerSet' k).carrier ↔ _
  rw [carrier_initialLowerSet', mem_initialIdeal']

lemma initialLowerSet'_mono (L : LinearExt' Q) :
    Monotone (L.initialLowerSet') := by
  intro k k' hk
  change (L.initialLowerSet' k).carrier ⊆ (L.initialLowerSet' k').carrier
  exact L.initialIdeal'_mono hk

/-! ### §5 — Sum-transport at level `k` -/

lemma sum_initialLowerSet'_birkhoff {β : Type*} [AddCommMonoid β]
    (k : Fin (Fintype.card α + 1)) (F : LowerSet' Q → β) :
    ∑ L : LinearExt' Q, F (L.initialLowerSet' k.val) =
      ∑ C : IdealChain' Q, F ⟨C.toFun k, fun _ _ hxy hy => C.isLowerSet k hxy hy⟩ := by
  classical
  rw [sum_toIdealChain'
    (fun C => F ⟨C.toFun k, fun _ _ hxy hy => C.isLowerSet k hxy hy⟩)]
  rfl

/-! ### §6 — `initialLowerSetChain'`: full chain in product lattice -/

/-- The full Birkhoff map from a linear extension to its
chain-of-`Q`-lower-sets. -/
def initialLowerSetChain' (L : LinearExt' Q) :
    Fin (Fintype.card α + 1) → LowerSet' Q :=
  fun k => L.initialLowerSet' k.val

@[simp] lemma initialLowerSetChain'_apply
    (L : LinearExt' Q) (k : Fin (Fintype.card α + 1)) :
    L.initialLowerSetChain' k = L.initialLowerSet' k.val := rfl

lemma initialLowerSetChain'_mono_index (L : LinearExt' Q)
    {k k' : Fin (Fintype.card α + 1)} (h : k ≤ k') :
    L.initialLowerSetChain' k ≤ L.initialLowerSetChain' k' :=
  L.initialLowerSet'_mono h

/-- Injectivity of the chain map. -/
lemma initialLowerSetChain'_injective :
    Function.Injective
      (initialLowerSetChain' :
        LinearExt' Q → Fin (Fintype.card α + 1) → LowerSet' Q) := by
  intro L₁ L₂ h
  apply LinearExt'.ext_of_initialIdeal'_eq
  intro k hk
  have := congrArg
    (fun (φ : Fin (Fintype.card α + 1) → LowerSet' Q) =>
      (φ ⟨k, Nat.lt_succ_of_le hk⟩).carrier) h
  simpa [initialLowerSetChain'_apply] using this

end LinearExt'

/-! ### §7 — FKG on `LowerSet' Q` (uniform measure) -/

section FKGOnLowerSet'

variable {Q : RelationPoset α}
variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- **Uniform FKG correlation on `LowerSet' Q`.** Direct application
of mathlib's `fkg_uniform_correlation` to the distributive lattice
`LowerSet' Q`. -/
lemma lowerSet'_fkg_uniform_correlation (F G : LowerSet' Q → β)
    (hF₀ : 0 ≤ F) (hG₀ : 0 ≤ G) (hF : Monotone F) (hG : Monotone G) :
    (∑ s : LowerSet' Q, F s) * (∑ s : LowerSet' Q, G s) ≤
      (Fintype.card (LowerSet' Q) : β) *
        (∑ s : LowerSet' Q, F s * G s) := by
  classical
  exact fkg_uniform_correlation F G hF₀ hG₀ hF hG

end FKGOnLowerSet'

/-! ### §8 — Sum-transport along the chain map (product lattice) -/

namespace LinearExt'

variable {Q : RelationPoset α}

variable {β : Type*} [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

omit [LinearOrder β] [IsStrictOrderedRing β] [ExistsAddOfLE β] in
lemma sum_initialLowerSetChain' (F : (Fin (Fintype.card α + 1) → LowerSet' Q) → β) :
    ∑ L : LinearExt' Q, F L.initialLowerSetChain' =
      ∑ C : IdealChain' Q, F (fun k =>
        ⟨C.toFun k, fun _ _ hxy hy => C.isLowerSet k hxy hy⟩) := by
  classical
  rw [sum_toIdealChain'
    (fun C => F (fun k => ⟨C.toFun k, fun _ _ hxy hy => C.isLowerSet k hxy hy⟩))]
  rfl

/-- **Ambient FKG upper bound for `LinearExt' Q`.** For monotone
non-negative `f, g` on `(LowerSet' Q)^{n+1}`, the LinearExt'-sums of
`f ∘ initialLowerSetChain'` and `g ∘ …` are bounded by the
product-lattice FKG. -/
lemma sum_initialLowerSetChain'_le_of_nonneg
    (f g : (Fin (Fintype.card α + 1) → LowerSet' Q) → β)
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ L : LinearExt' Q, f L.initialLowerSetChain') *
      (∑ L : LinearExt' Q, g L.initialLowerSetChain') ≤
    (Fintype.card (Fin (Fintype.card α + 1) → LowerSet' Q) : β) *
      (∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, f ω * g ω) := by
  classical
  have hLEf_le : ∑ L : LinearExt' Q, f L.initialLowerSetChain' ≤
      ∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, f ω := by
    rw [← Finset.sum_image (f := f)
      (fun L _ L' _ h => initialLowerSetChain'_injective h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun ω _ _ => hf₀ ω)
  have hLEg_le : ∑ L : LinearExt' Q, g L.initialLowerSetChain' ≤
      ∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, g ω := by
    rw [← Finset.sum_image (f := g)
      (fun L _ L' _ h => initialLowerSetChain'_injective h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun ω _ _ => hg₀ ω)
  have hLEf_nn : 0 ≤ ∑ L : LinearExt' Q, f L.initialLowerSetChain' :=
    Finset.sum_nonneg (fun L _ => hf₀ _)
  have hLEg_nn : 0 ≤ ∑ L : LinearExt' Q, g L.initialLowerSetChain' :=
    Finset.sum_nonneg (fun L _ => hg₀ _)
  have hprod := pi_fkg_uniform_correlation
    (ι := Fin (Fintype.card α + 1))
    (L := fun _ => LowerSet' Q) f g hf₀ hg₀ hf hg
  calc (∑ L : LinearExt' Q, f L.initialLowerSetChain') *
        (∑ L : LinearExt' Q, g L.initialLowerSetChain')
      ≤ (∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, f ω) *
        (∑ L : LinearExt' Q, g L.initialLowerSetChain') := by
        refine mul_le_mul_of_nonneg_right hLEf_le hLEg_nn
    _ ≤ (∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, f ω) *
        (∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, g ω) := by
        refine mul_le_mul_of_nonneg_left hLEg_le ?_
        exact Finset.sum_nonneg (fun ω _ => hf₀ ω)
    _ ≤ (Fintype.card (Fin (Fintype.card α + 1) → LowerSet' Q) : β) *
        (∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, f ω * g ω) := hprod

/-! ### §9 — Level-`k` FKG upper bound on `LinearExt' Q` -/

/-- **LinearExt' FKG via level-`k` LowerSet' projection.** Port of
`LinearExt.fkg_uniform_initialLowerSet` to the data version. -/
lemma fkg_uniform_initialLowerSet'
    (k : Fin (Fintype.card α + 1)) (F G : LowerSet' Q → β)
    (hF₀ : 0 ≤ F) (hG₀ : 0 ≤ G) (hF : Monotone F) (hG : Monotone G) :
    (∑ L : LinearExt' Q, F (L.initialLowerSet' k.val)) *
      (∑ L : LinearExt' Q, G (L.initialLowerSet' k.val)) ≤
    (Fintype.card (Fin (Fintype.card α + 1) → LowerSet' Q) : β) *
      (∑ ω : Fin (Fintype.card α + 1) → LowerSet' Q, F (ω k) * G (ω k)) := by
  classical
  let f : (Fin (Fintype.card α + 1) → LowerSet' Q) → β := fun ω => F (ω k)
  let g : (Fin (Fintype.card α + 1) → LowerSet' Q) → β := fun ω => G (ω k)
  have hf₀ : 0 ≤ f := fun ω => hF₀ (ω k)
  have hg₀ : 0 ≤ g := fun ω => hG₀ (ω k)
  have hfmono : Monotone f := fun ω₁ ω₂ hω => hF (hω k)
  have hgmono : Monotone g := fun ω₁ ω₂ hω => hG (hω k)
  have hf_on_LE : ∀ L : LinearExt' Q,
      f L.initialLowerSetChain' = F (L.initialLowerSet' k.val) := by
    intro L; simp [f, initialLowerSetChain'_apply]
  have hg_on_LE : ∀ L : LinearExt' Q,
      g L.initialLowerSetChain' = G (L.initialLowerSet' k.val) := by
    intro L; simp [g, initialLowerSetChain'_apply]
  have := sum_initialLowerSetChain'_le_of_nonneg f g hf₀ hg₀ hfmono hgmono
  rw [show (∑ L : LinearExt' Q, f L.initialLowerSetChain') =
        ∑ L : LinearExt' Q, F (L.initialLowerSet' k.val) from
      Finset.sum_congr rfl (fun L _ => hf_on_LE L),
      show (∑ L : LinearExt' Q, g L.initialLowerSetChain') =
        ∑ L : LinearExt' Q, G (L.initialLowerSet' k.val) from
      Finset.sum_congr rfl (fun L _ => hg_on_LE L)] at this
  exact this

end LinearExt'

/-! ### §10 — Sub-poset monotonicity (cross-poset coupling)

For `Q.Subseteq Q'`, `LinearExt' Q'` injects into `LinearExt' Q` via
`LinearExt'.restrict`. This gives the **absolute** form of FKG
monotonicity-under-augmentation: the `LinearExt'`-sum of any
non-negative integrand can only *shrink* under poset augmentation.

For the *probability-normalised* form (the headline lemma needed by
the rotation argument of `prop:in-situ-balanced` Case 2), we need to
divide both sums by the respective `numLinExt'` counts; the
normalisation factor is *also* monotone (`numLinExt' Q' ≤ numLinExt' Q`),
so the two bounds compose to give the correct FKG-monotonicity sign
when the integrand is *down-closed* in the `Finset α` lattice. The
detailed argument uses level-`k` FKG positive correlation on
`LinearExt' Q` between the integrand-event and the
"`L` respects the new `Q'`-comparabilities" event; we factor this
through the typeclass-based `LinearExt.fkg_uniform_initialLowerSet`
applied to `Q.asPartialOrder`. -/

/-- **Sub-poset bound (absolute form).** For non-negative `F`, summing
the value of `F` at the level-`k` initial ideal across `LinearExt' Q'`
is bounded above by the same sum over `LinearExt' Q`, when
`Q.Subseteq Q'`. This is the FKG monotonicity-under-augmentation
inequality in its un-normalised "trivial" form, derived from the
embedding `LinearExt'.restrict : LinearExt' Q' ↪ LinearExt' Q`. -/
lemma sum_initialIdeal'_le_of_subseteq
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    {β : Type*} [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    (k : Fin (Fintype.card α + 1))
    (F : Finset α → β) (hF₀ : ∀ S, 0 ≤ F S) :
    ∑ L' : LinearExt' Q', F (L'.initialIdeal' k.val) ≤
    ∑ L : LinearExt' Q, F (L.initialIdeal' k.val) := by
  classical
  -- Reindex the LHS via the injection `restrict : LE Q' ↪ LE Q`.
  have hinj : Function.Injective
      (LinearExt'.restrict hQQ' : LinearExt' Q' → LinearExt' Q) :=
    LinearExt'.restrict_injective hQQ'
  rw [show (∑ L' : LinearExt' Q', F (L'.initialIdeal' k.val)) =
        ∑ L ∈ (Finset.univ : Finset (LinearExt' Q')).image
          (LinearExt'.restrict hQQ'), F (L.initialIdeal' k.val) from ?_]
  · refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun L _ _ => hF₀ _)
  · -- Reindexing equality.
    rw [Finset.sum_image (fun L _ L' _ h => hinj h)]
    refine Finset.sum_congr rfl ?_
    intro L' _
    -- (restrict L').initialIdeal' k = L'.initialIdeal' k since both rely only on .pos.
    rfl

/-! ### §11 — Counting-form headline: FKG monotonicity-under-augmentation

The probability-normalised statement targeted by the rotation argument
of `prop:in-situ-balanced` Case 2 has signature

  `(probEvent' Q').onEvent E ≤ (probEvent' Q).onEvent E`

for `E` a level-`k` "down-closed" `Finset α`-event and
`Q.Subseteq Q'` (Q' adds at least one comparability). In its
**counting form** (un-normalised by `numLinExt'`), the headline
follows directly from the embedding
`LinearExt'.restrict : LinearExt' Q' ↪ LinearExt' Q`: the count of
`Q'`-extensions satisfying any decidable level-`k` event is bounded
above by the count of `Q`-extensions satisfying it.

The probability-normalised form requires positive-correlation
(FKG / Ahlswede–Daykin) between the level-`k` event and the
"`L` respects every new `Q'`-comparability" event in the
LinearExt' Q lattice; this is recorded as future work in
`docs/a8-s2-status.md`. The counting form below is the form actually
used by the rotation argument's chain of inequalities (which only
divides by `numLinExt'` at the final probability-extraction step). -/

/-- Uniform-measure probability of a decidable event on linear
extensions of a `RelationPoset α`. -/
noncomputable def probEvent' (Q : RelationPoset α)
    (E : LinearExt' Q → Prop) [DecidablePred E] : ℚ :=
  ((Finset.univ.filter E).card : ℚ) / (numLinExt' Q : ℚ)

lemma probEvent'_nonneg (Q : RelationPoset α)
    (E : LinearExt' Q → Prop) [DecidablePred E] :
    0 ≤ probEvent' Q E := by
  unfold probEvent'
  positivity

lemma probEvent'_le_one (Q : RelationPoset α)
    (E : LinearExt' Q → Prop) [DecidablePred E] :
    probEvent' Q E ≤ 1 := by
  unfold probEvent'
  rw [div_le_one (by exact_mod_cast numLinExt'_pos Q)]
  exact_mod_cast (Finset.card_filter_le _ _).trans Finset.card_univ.le

/-- **Headline lemma — FKG monotonicity-under-augmentation
(counting form).** For `Q.Subseteq Q'` and any decidable level-`k`
event `S` on `Finset α`, the count of `Q'`-linear-extensions whose
level-`k` initial ideal satisfies `S` is bounded above by the
analogous count over `Q`-linear-extensions:

  `|{L' ∈ LE Q' : S(L'.iI k)}|  ≤  |{L ∈ LE Q : S(L.iI k)}|`.

In other words, augmenting the comparability relation can only
*shrink* (or fix) the count of extensions exhibiting any given
level-`k` finset-event. This is the un-normalised version of the
statement targeted by `prop:in-situ-balanced` Case 2.

The proof is by the embedding
`LinearExt'.restrict : LinearExt' Q' ↪ LinearExt' Q`: every
`Q'`-extension `L'` injects to a `Q`-extension `L` with the *same*
position function and hence the *same* level-`k` initial ideal. -/
theorem probLT'_mono_of_relExt
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    (Finset.univ.filter
        (fun L' : LinearExt' Q' => S (L'.initialIdeal' k.val))).card ≤
      (Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card := by
  classical
  -- Strategy: identify the LHS filter with the image, under restrict, of
  -- those Q-LEs that come from Q'-LEs and satisfy S; bound by all Q-LEs
  -- satisfying S.
  have hinj : Function.Injective
      (LinearExt'.restrict hQQ' : LinearExt' Q' → LinearExt' Q) :=
    LinearExt'.restrict_injective hQQ'
  -- Map each Q'-LE satisfying S to its restriction (a Q-LE with the
  -- same iI k, hence still satisfying S).
  have hsub :
      (Finset.univ.filter
          (fun L' : LinearExt' Q' => S (L'.initialIdeal' k.val))).image
          (LinearExt'.restrict hQQ') ⊆
        Finset.univ.filter
          (fun L : LinearExt' Q => S (L.initialIdeal' k.val)) := by
    intro L hL
    rw [Finset.mem_image] at hL
    obtain ⟨L', hL', hrestrict⟩ := hL
    rw [Finset.mem_filter] at hL'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- `L = restrict L'`, so `L.iI k = L'.iI k`.
    rw [← hrestrict]
    exact hL'.2
  calc (Finset.univ.filter
          (fun L' : LinearExt' Q' => S (L'.initialIdeal' k.val))).card
      = ((Finset.univ.filter
          (fun L' : LinearExt' Q' => S (L'.initialIdeal' k.val))).image
            (LinearExt'.restrict hQQ')).card := by
            rw [Finset.card_image_of_injOn (fun _ _ _ _ h => hinj h)]
    _ ≤ (Finset.univ.filter
            (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card :=
        Finset.card_le_card hsub

/-- **Probability form of the headline**, derived directly from the
counting form `probLT'_mono_of_relExt`.

Strictly speaking, the displayed inequality compares the
*restricted-numerator* probability — i.e. dividing the smaller count
by the *larger* (`Q`-side) denominator `numLinExt' Q` — and is
therefore weaker than the standard Daykin–Saks "drops" inequality
between the two genuine averages. The standard form requires FKG
positive correlation between the `S`-event and the
"`L` respects new `Q'`-comparabilities" event in the LinearExt' Q
lattice, recorded as a follow-up in `docs/a8-s2-status.md`.

The form below is what the rotation-argument's pipeline actually
threads (the final probability-extraction step happens after the
sum-level monotonicity is collapsed). -/
lemma probLT'_count_div_le_of_relExt
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    ((Finset.univ.filter
        (fun L' : LinearExt' Q' => S (L'.initialIdeal' k.val))).card : ℚ)
        / (numLinExt' Q : ℚ) ≤
      ((Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card : ℚ)
        / (numLinExt' Q : ℚ) := by
  classical
  have hpos : (0 : ℚ) < numLinExt' Q := by exact_mod_cast numLinExt'_pos Q
  rw [div_le_div_iff_of_pos_right hpos]
  exact_mod_cast probLT'_mono_of_relExt hQQ' k S

end RelationPoset

end OneThird


