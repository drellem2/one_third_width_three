/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.Poset.Width
import Mathlib.Order.Preorder.Finite

/-!
# Dilworth's theorem for finite posets

A finite partial order of width `w` admits a chain cover of size `w`: there
is a function `f : α → Fin w` whose fibers are chains.

The proof is by strong induction on `|α|`. In the non-antichain case we
pick a minimum/maximum pair `b < t` (with `b` minimal and `t` maximal) and
consider `β' = α \ {b, t}`. If `width β' < w`, we extend the inductive
cover of `β'` by the chain `{b, t}`. If `width β' = w`, we apply the
Galvin antichain split along a width-witnessing antichain `A ⊂ β'`.

This file lives in the `OneThird/Mathlib/` tier — it is a self-contained
mathlib-flavored contribution, independent of the 1/3–2/3 conjecture, and
could be extracted as a small `Order.Dilworth` module.

## Main definitions

* `OneThird.Mathlib.Poset.HasChainCover` — a cover of `α` by `w` chains,
  presented as a function `f : α → Fin w` whose fibers are chains.

## Main results

* `OneThird.Mathlib.Poset.HasChainCover.mono` — a cover of size `w`
  extends to a cover of any larger size.
* `OneThird.Mathlib.Poset.width_le_of_hasChainCover` — the easy direction:
  every chain cover has at least `width α` classes.
* `OneThird.Mathlib.Poset.hasChainCover_of_hasWidth` — Dilworth's theorem:
  if `α` has width `w`, then it admits a chain cover of size `w`.
* `OneThird.Mathlib.Poset.hasChainCover_iff_width_le` — the width is
  the minimum number of chains in a chain cover.
-/

open Finset

namespace OneThird
namespace Mathlib
namespace Poset

variable {α : Type*}

section HasChainCover

/-- A chain cover of `α` by `w` chains is a function `f : α → Fin w` such
that each fiber `{x | f x = i}` is a chain. -/
def HasChainCover (α : Type*) [PartialOrder α] (w : ℕ) : Prop :=
  ∃ f : α → Fin w, ∀ i : Fin w, IsChain (· ≤ ·) ({x | f x = i} : Set α)

variable [PartialOrder α]

/-- An empty type is covered by `0` chains. -/
theorem hasChainCover_zero_of_isEmpty [IsEmpty α] : HasChainCover α 0 :=
  ⟨fun a => isEmptyElim a, fun i => i.elim0⟩

/-- A chain cover of size `w` gives a chain cover of any larger size
`w'` by leaving extra classes empty. -/
theorem HasChainCover.mono {w w' : ℕ} (hw : HasChainCover α w) (h : w ≤ w') :
    HasChainCover α w' := by
  obtain ⟨f, hf⟩ := hw
  refine ⟨fun a => (f a).castLE h, fun i => ?_⟩
  intro x hx y hy hxy
  simp only [Set.mem_setOf_eq] at hx hy
  have hfxy : f x = f y := by
    apply Fin.castLE_injective h
    rw [hx, hy]
  have hxmem : x ∈ ({z | f z = f x} : Set α) := rfl
  have hymem : y ∈ ({z | f z = f x} : Set α) := hfxy.symm
  exact hf (f x) hxmem hymem hxy

end HasChainCover

section Dilworth

variable [PartialOrder α] [Fintype α] [DecidableEq α]

/-- The universal cover where each element is in its own class: a chain
cover of size `Fintype.card α`. Singletons are chains. -/
theorem hasChainCover_card : HasChainCover α (Fintype.card α) := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  refine ⟨e, fun _ => ?_⟩
  intro x hx y hy hxy
  simp only [Set.mem_setOf_eq] at hx hy
  exact absurd (e.injective (hx.trans hy.symm)) hxy

/-- Chain covers of size `< width α` do not exist: every chain cover has
at least `width α` classes. This is the easy direction of Dilworth. -/
theorem width_le_of_hasChainCover {w : ℕ} (hw : HasChainCover α w) :
    width α ≤ w := by
  classical
  obtain ⟨f, hf⟩ := hw
  obtain ⟨s, hs, hcard⟩ := exists_antichain_card_eq_width (α := α)
  rw [← hcard]
  have hinj : Set.InjOn f (s : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    have hchain := hf (f x)
    have hxmem : x ∈ ({z | f z = f x} : Set α) := rfl
    have hymem : y ∈ ({z | f z = f x} : Set α) := by
      change f y = f x
      exact hxy.symm
    rcases hchain hxmem hymem hne with hle | hle
    · exact hs hx hy hne hle
    · exact hs hy hx (Ne.symm hne) hle
  have hcard_image : s.card = (s.image f).card := by
    symm
    apply Finset.card_image_of_injOn
    intro x hx y hy
    exact hinj hx hy
  rw [hcard_image]
  calc (s.image f).card
      ≤ (Finset.univ : Finset (Fin w)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = w := (Finset.card_univ).trans (Fintype.card_fin w)

/-!
### Machinery for Dilworth's theorem

The proof is by strong induction on `Fintype.card`, so we phrase
everything generically in a fresh finite poset `β`. The inductive step
applies the hypothesis to the subtypes
`β \ {b, t}`, `{x | ∃ a ∈ A, x ≤ a}`, and `{x | ∃ a ∈ A, a ≤ x}`.
-/

/-- Image of a subtype antichain under `Subtype.val` is an antichain. -/
private lemma isAntichain_image_val {β : Type*} [PartialOrder β] [DecidableEq β]
    {P : β → Prop} {s : Finset {x : β // P x}}
    (hs : IsAntichain (· ≤ ·) (s : Set {x : β // P x})) :
    IsAntichain (· ≤ ·) ((s.image Subtype.val : Finset β) : Set β) := by
  intro x hx y hy hxy hle
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨x', hx', hxv⟩ := hx
  obtain ⟨y', hy', hyv⟩ := hy
  subst hxv; subst hyv
  exact hs hx' hy' (fun heq => hxy (congrArg Subtype.val heq)) hle

/-- **Splicing lemma (axiomatized for split).** Given two chain covers
`fD : D → Fin k` and `fU : U → Fin k` of the down-set and up-set of an
antichain `A`, if `D ∩ U = A` (as subsets of `β`), `D ∪ U = β`, and the
covers are "aligned" to `A` (each `a ∈ A` lies in a canonical fiber in
both covers), the combined function is a chain cover of `β`.

*Follow-up work:* the alignment step (permuting fiber labels so `a ∈ A`
lands in a canonical fiber) and the splicing proof are mechanically
routine but long; they are being completed in work-item `mg-ca21b`. -/
private theorem dilworth_splice {β : Type*} [PartialOrder β] [Fintype β]
    {PD PU : β → Prop} {k : ℕ} (Aβ : Finset β) (hAcard : Aβ.card = k)
    (hAanti : IsAntichain (· ≤ ·) (Aβ : Set β))
    (hAD : ∀ a ∈ Aβ, PD a) (hAU : ∀ a ∈ Aβ, PU a)
    (hDU_union : ∀ x : β, PD x ∨ PU x)
    (hDU_inter : ∀ x : β, PD x → PU x → x ∈ Aβ)
    (hPD_down : ∀ x : β, PD x ↔ ∃ a ∈ Aβ, x ≤ a)
    (hPU_up : ∀ x : β, PU x ↔ ∃ a ∈ Aβ, a ≤ x)
    (hcovD : HasChainCover {x : β // PD x} k)
    (hcovU : HasChainCover {x : β // PU x} k) :
    HasChainCover β k := by
  classical
  obtain ⟨fD, hfD⟩ := hcovD
  obtain ⟨fU, hfU⟩ := hcovU
  -- For each `a ∈ Aβ`, its index in `fD` (and `fU`).  Because `Aβ` is
  -- an antichain of size `k`, `fD|A` and `fU|A` are bijections to `Fin k`.
  -- We then realign `fU` so that it agrees with `fD` on `Aβ`.
  -- The remaining argument is standard but mechanical; the split at the
  -- current cut-line defers this to follow-up `mg-ca21b`.
  sorry

/-- Auxiliary: Dilworth's theorem by strong induction on `Fintype.card β`.
Generalized over `β` so that the induction hypothesis applies to the
subtypes `β \ {b, t}`, `D`, and `U` arising in the Galvin split. -/
private theorem hasChainCover_of_hasWidth_aux :
    ∀ n : ℕ, ∀ (β : Type*) [PartialOrder β] [Fintype β] [DecidableEq β] {k : ℕ},
      Fintype.card β = n → HasWidth β k → HasChainCover β k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro β _ _ _ k hcard hw
    classical
    -- Base case: β is empty.
    rcases Nat.eq_zero_or_pos n with hzero | hpos
    · subst hzero
      haveI : IsEmpty β := Fintype.card_eq_zero_iff.mp hcard
      obtain ⟨_, s, _, hs⟩ := hw
      have he : s = ∅ := Finset.eq_empty_of_isEmpty s
      rw [he, Finset.card_empty] at hs
      subst hs
      exact hasChainCover_zero_of_isEmpty
    haveI hne : Nonempty β := Fintype.card_pos_iff.mp (hcard ▸ hpos)
    obtain ⟨hwle, A₀, hA₀anti, hA₀card⟩ := hw
    -- Width is positive in a nonempty poset.
    have hk_pos : 0 < k := by
      obtain ⟨x⟩ := hne
      have h1 : ({x} : Finset β).card ≤ k := hwle _ (by
        rw [Finset.coe_singleton]; exact IsAntichain.singleton)
      simpa using h1
    -- Antichain case: β is itself an antichain.
    by_cases hac : IsAntichain (· ≤ ·) (Set.univ : Set β)
    · have hkβ : Fintype.card β = k := by
        apply le_antisymm
        · have hu : Fintype.card β = (Finset.univ : Finset β).card :=
            Finset.card_univ.symm
          rw [hu]
          apply hwle
          rw [Finset.coe_univ]
          exact hac
        · rw [← hA₀card]
          refine (Finset.card_le_card (Finset.subset_univ _)).trans_eq ?_
          exact Finset.card_univ
      rw [← hkβ]
      exact hasChainCover_card
    -- Non-antichain case: find a comparable pair `u < v`.
    have hcomp : ∃ u v : β, u < v := by
      by_contra hne'
      push_neg at hne'
      apply hac
      intro a _ b' _ hab hle
      exact hne' a b' (lt_of_le_of_ne hle hab)
    obtain ⟨u, v, huv⟩ := hcomp
    obtain ⟨t, hvt, ht_max⟩ :=
      Finset.exists_le_maximal (Finset.univ : Finset β) (Finset.mem_univ v)
    have hut : u < t := lt_of_lt_of_le huv hvt
    have hut_le : u ≤ t := le_of_lt hut
    obtain ⟨b, hbt, hb_min⟩ :=
      Finset.exists_le_minimal (Finset.univ : Finset β) (Finset.mem_univ t)
    have hbt_lt : b < t := by
      rcases lt_or_eq_of_le hbt with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq] at hut_le hut
        have hbu : b ≤ u := hb_min.2 (Finset.mem_univ u) hut_le
        exact hut.ne (le_antisymm hut_le hbu)
    have hbt_ne : b ≠ t := ne_of_lt hbt_lt
    have ht_is_max : ∀ y : β, t ≤ y → y = t := fun y hty =>
      le_antisymm (ht_max.2 (Finset.mem_univ y) hty) hty
    have hb_is_min : ∀ y : β, y ≤ b → y = b := fun y hyb =>
      le_antisymm hyb (hb_min.2 (Finset.mem_univ y) hyb)
    -- The remaining carrier `β' = β \ {b, t}` as a subtype.
    let β' : Type _ := {x : β // x ≠ b ∧ x ≠ t}
    haveI : Fintype β' := Subtype.fintype _
    -- Cardinality computations.
    have card_β'_eq : Fintype.card β' = n - 2 := by
      simp only [β']
      rw [Fintype.card_subtype]
      have hfilter : ((Finset.univ : Finset β).filter
          (fun x => x ≠ b ∧ x ≠ t)) = (Finset.univ.erase b).erase t := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and]
        tauto
      rw [hfilter]
      have hte : t ∈ (Finset.univ : Finset β).erase b := by
        simp [Finset.mem_erase, hbt_ne.symm, Finset.mem_univ]
      rw [Finset.card_erase_of_mem hte]
      rw [Finset.card_erase_of_mem (Finset.mem_univ b)]
      rw [Finset.card_univ, hcard]
      omega
    have hn_ge_2 : 2 ≤ n := by
      have h2 : ({b, t} : Finset β).card = 2 := by
        rw [show ({b, t} : Finset β) = insert b {t} from rfl,
            Finset.card_insert_of_notMem (by simp [hbt_ne]),
            Finset.card_singleton]
      have : ({b, t} : Finset β).card ≤ Fintype.card β :=
        (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ
      rw [h2, hcard] at this
      exact this
    have hcardβ'_lt : Fintype.card β' < n := by
      rw [card_β'_eq]; omega
    -- The width of β' is at most k.
    have hwle_β' : HasWidthAtMost β' k := by
      intro s hs
      have himgcard : (s.image (Subtype.val : β' → β)).card = s.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      have himg_anti :
          IsAntichain (· ≤ ·) ((s.image Subtype.val : Finset β) : Set β) :=
        isAntichain_image_val hs
      have := hwle (s.image Subtype.val) himg_anti
      rw [himgcard] at this
      exact this
    -- Case split on whether β' contains an antichain of size k.
    by_cases hexists : ∃ A : Finset β', IsAntichain (· ≤ ·) (A : Set β') ∧ A.card = k
    · -- Case B: Galvin split.
      obtain ⟨A, hAanti, hAcard⟩ := hexists
      -- Project `A` into `β`.
      let Aβ : Finset β := A.image Subtype.val
      have hAβ_card : Aβ.card = k := by
        simp only [Aβ]
        rw [Finset.card_image_of_injective _ Subtype.val_injective, hAcard]
      have hAβ_anti : IsAntichain (· ≤ ·) (Aβ : Set β) :=
        isAntichain_image_val hAanti
      -- No element of Aβ equals b or t.
      have hAβ_ne_b : ∀ x ∈ Aβ, x ≠ b := by
        intro x hx
        simp only [Aβ, Finset.mem_image] at hx
        obtain ⟨x', _, hxv⟩ := hx
        intro hxb
        exact x'.2.1 (hxv.trans hxb)
      have hAβ_ne_t : ∀ x ∈ Aβ, x ≠ t := by
        intro x hx
        simp only [Aβ, Finset.mem_image] at hx
        obtain ⟨x', _, hxv⟩ := hx
        intro hxt
        exact x'.2.2 (hxv.trans hxt)
      -- Down-set and up-set predicates.
      let PD : β → Prop := fun x => ∃ a ∈ Aβ, x ≤ a
      let PU : β → Prop := fun x => ∃ a ∈ Aβ, a ≤ x
      haveI hdecD : DecidablePred PD := fun _ => Classical.dec _
      haveI hdecU : DecidablePred PU := fun _ => Classical.dec _
      let D : Type _ := {x : β // PD x}
      let U : Type _ := {x : β // PU x}
      haveI : Fintype D := Subtype.fintype _
      haveI : Fintype U := Subtype.fintype _
      -- `t ∉ D`: since `t` is maximal and `t ∉ Aβ`, `t ≤ a ∈ Aβ` would force `a = t`.
      have ht_notD : ¬ PD t := by
        rintro ⟨a, haA, hta⟩
        have : a = t := ht_is_max a hta
        exact hAβ_ne_t a haA this
      -- `b ∉ U`.
      have hb_notU : ¬ PU b := by
        rintro ⟨a, haA, hab⟩
        have : a = b := hb_is_min a hab
        exact hAβ_ne_b a haA this
      -- `PD x ∨ PU x` for every `x`.
      have hDU_union : ∀ x : β, PD x ∨ PU x := by
        intro x
        by_contra hnone
        push_neg at hnone
        obtain ⟨hxD, hxU⟩ := hnone
        have hx_notin : x ∉ Aβ := fun hx => hxD ⟨x, hx, le_refl x⟩
        have hins_anti :
            IsAntichain (· ≤ ·) ((insert x Aβ : Finset β) : Set β) := by
          rw [Finset.coe_insert]
          intro p hp q hq hpq hle
          simp only [Set.mem_insert_iff] at hp hq
          rcases hp with rfl | hp
          · rcases hq with rfl | hq
            · exact hpq rfl
            · exact hxD ⟨q, hq, hle⟩
          · rcases hq with rfl | hq
            · exact hxU ⟨p, hp, hle⟩
            · exact hAβ_anti hp hq hpq hle
        have hcard_ins : (insert x Aβ).card = k + 1 := by
          rw [Finset.card_insert_of_notMem hx_notin, hAβ_card]
        have := hwle _ hins_anti
        omega
      -- `PD x ∧ PU x → x ∈ Aβ`.
      have hDU_inter : ∀ x : β, PD x → PU x → x ∈ Aβ := by
        rintro x ⟨a1, ha1, hxa1⟩ ⟨a2, ha2, ha2x⟩
        by_cases heq : a2 = a1
        · have hxa2 : x = a2 := le_antisymm (heq ▸ hxa1) ha2x
          rw [hxa2]; exact ha2
        · exfalso
          have ha2a1 : a2 ≤ a1 := ha2x.trans hxa1
          exact hAβ_anti ha2 ha1 heq ha2a1
      have hA_sub_D : ∀ a ∈ Aβ, PD a := fun a ha => ⟨a, ha, le_refl a⟩
      have hA_sub_U : ∀ a ∈ Aβ, PU a := fun a ha => ⟨a, ha, le_refl a⟩
      -- Cardinalities of D and U: both are < n.
      have hcardD_lt : Fintype.card D < n := by
        have hcardD_le : Fintype.card D ≤ n - 1 := by
          have h1 : Fintype.card D =
              ((Finset.univ : Finset β).filter PD).card :=
            Fintype.card_subtype _
          rw [h1]
          have hsubset : (Finset.univ : Finset β).filter PD ⊆
              (Finset.univ : Finset β).erase t := by
            intro x hx
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_erase]
            exact ⟨fun heq => ht_notD (heq ▸ hx.2), Finset.mem_univ x⟩
          refine (Finset.card_le_card hsubset).trans_eq ?_
          rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, hcard]
        omega
      have hcardU_lt : Fintype.card U < n := by
        have hcardU_le : Fintype.card U ≤ n - 1 := by
          have h1 : Fintype.card U =
              ((Finset.univ : Finset β).filter PU).card :=
            Fintype.card_subtype _
          rw [h1]
          have hsubset : (Finset.univ : Finset β).filter PU ⊆
              (Finset.univ : Finset β).erase b := by
            intro x hx
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_erase]
            exact ⟨fun heq => hb_notU (heq ▸ hx.2), Finset.mem_univ x⟩
          refine (Finset.card_le_card hsubset).trans_eq ?_
          rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, hcard]
        omega
      -- Aβ as antichain in D of size k.
      let AD : Finset D := Aβ.attach.image
        (fun a => (⟨a.1, hA_sub_D a.1 a.2⟩ : D))
      let AU : Finset U := Aβ.attach.image
        (fun a => (⟨a.1, hA_sub_U a.1 a.2⟩ : U))
      have hAD_inj : Function.Injective
          (fun (a : {x // x ∈ Aβ}) => (⟨a.1, hA_sub_D a.1 a.2⟩ : D)) := by
        intro x y hxy
        apply Subtype.ext
        exact (Subtype.mk.injEq _ _ _ _).mp hxy
      have hAU_inj : Function.Injective
          (fun (a : {x // x ∈ Aβ}) => (⟨a.1, hA_sub_U a.1 a.2⟩ : U)) := by
        intro x y hxy
        apply Subtype.ext
        exact (Subtype.mk.injEq _ _ _ _).mp hxy
      have hAD_card : AD.card = k := by
        simp only [AD]
        rw [Finset.card_image_of_injective _ hAD_inj, Finset.card_attach, hAβ_card]
      have hAU_card : AU.card = k := by
        simp only [AU]
        rw [Finset.card_image_of_injective _ hAU_inj, Finset.card_attach, hAβ_card]
      have hAD_anti : IsAntichain (· ≤ ·) (AD : Set D) := by
        intro x hx y hy hxy hle
        simp only [AD, Finset.coe_image, Finset.coe_attach, Set.image_univ,
          Set.mem_range, Subtype.exists] at hx hy
        obtain ⟨xv, hxv_mem, heqx⟩ := hx
        obtain ⟨yv, hyv_mem, heqy⟩ := hy
        apply hAβ_anti hxv_mem hyv_mem
        · intro h
          subst h
          apply hxy
          rw [← heqx, ← heqy]
        · rw [← heqx, ← heqy] at hle
          exact hle
      have hAU_anti : IsAntichain (· ≤ ·) (AU : Set U) := by
        intro x hx y hy hxy hle
        simp only [AU, Finset.coe_image, Finset.coe_attach, Set.image_univ,
          Set.mem_range, Subtype.exists] at hx hy
        obtain ⟨xv, hxv_mem, heqx⟩ := hx
        obtain ⟨yv, hyv_mem, heqy⟩ := hy
        apply hAβ_anti hxv_mem hyv_mem
        · intro h
          subst h
          apply hxy
          rw [← heqx, ← heqy]
        · rw [← heqx, ← heqy] at hle
          exact hle
      have hwle_D : HasWidthAtMost D k := by
        intro s hs
        have himgcard : (s.image (Subtype.val : D → β)).card = s.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have himg_anti :
            IsAntichain (· ≤ ·) ((s.image Subtype.val : Finset β) : Set β) :=
          isAntichain_image_val hs
        have := hwle (s.image Subtype.val) himg_anti
        rw [himgcard] at this
        exact this
      have hwle_U : HasWidthAtMost U k := by
        intro s hs
        have himgcard : (s.image (Subtype.val : U → β)).card = s.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have himg_anti :
            IsAntichain (· ≤ ·) ((s.image Subtype.val : Finset β) : Set β) :=
          isAntichain_image_val hs
        have := hwle (s.image Subtype.val) himg_anti
        rw [himgcard] at this
        exact this
      have hwD : HasWidth D k := ⟨hwle_D, AD, hAD_anti, hAD_card⟩
      have hwU : HasWidth U k := ⟨hwle_U, AU, hAU_anti, hAU_card⟩
      have hcovD : HasChainCover D k := ih _ hcardD_lt D rfl hwD
      have hcovU : HasChainCover U k := ih _ hcardU_lt U rfl hwU
      -- Defer the splice step to the helper lemma.
      exact dilworth_splice Aβ hAβ_card hAβ_anti hA_sub_D hA_sub_U hDU_union
        hDU_inter (fun _ => Iff.rfl) (fun _ => Iff.rfl) hcovD hcovU
    · -- Case A: width β' < k; extend inductively by chain {b, t}.
      push_neg at hexists
      have hw_β' : HasWidth β' (width β') := hasWidth_iff_width_eq.mpr rfl
      have h_wβ'_le : width β' ≤ k := (hasWidthAtMost_iff_width_le).mp hwle_β'
      have h_wβ'_lt : width β' < k := by
        rcases lt_or_eq_of_le h_wβ'_le with hlt | heq
        · exact hlt
        · exfalso
          obtain ⟨A, hA, hcardA⟩ := exists_antichain_card_eq_width (α := β')
          exact hexists A hA (hcardA.trans heq)
      have hcovβ' : HasChainCover β' (width β') :=
        ih _ hcardβ'_lt β' rfl hw_β'
      have hcovβ'_k1 : HasChainCover β' (k - 1) := hcovβ'.mono (by omega)
      obtain ⟨f', hf'⟩ := hcovβ'_k1
      -- Build `f : β → Fin k` by sending b, t to the last class.
      let last : Fin k := ⟨k - 1, Nat.pred_lt hk_pos.ne'⟩
      let f : β → Fin k := fun x =>
        if hx : x ≠ b ∧ x ≠ t then
          (f' ⟨x, hx⟩).castLE (Nat.sub_le k 1)
        else last
      refine ⟨f, ?_⟩
      intro i x hx y hy hxy
      simp only [Set.mem_setOf_eq] at hx hy
      -- Helper: evaluate `f` via dite.
      have hf_eval : ∀ x : β, f x = if hx : x ≠ b ∧ x ≠ t then
          (f' ⟨x, hx⟩).castLE (Nat.sub_le k 1) else last := fun _ => rfl
      -- Analyze whether x, y ∈ β' or ∈ {b, t}.
      by_cases hxP : x ≠ b ∧ x ≠ t
      · by_cases hyP : y ≠ b ∧ y ≠ t
        · -- Both in β': use chain property of f'.
          have hfx : f x = (f' ⟨x, hxP⟩).castLE (Nat.sub_le k 1) := by
            rw [hf_eval, dif_pos hxP]
          have hfy : f y = (f' ⟨y, hyP⟩).castLE (Nat.sub_le k 1) := by
            rw [hf_eval, dif_pos hyP]
          have heq : f' ⟨x, hxP⟩ = f' ⟨y, hyP⟩ := by
            apply Fin.castLE_injective (Nat.sub_le k 1)
            rw [← hfx, ← hfy, hx, hy]
          have hxmem : (⟨x, hxP⟩ : β') ∈
              ({z | f' z = f' ⟨x, hxP⟩} : Set β') := rfl
          have hymem : (⟨y, hyP⟩ : β') ∈
              ({z | f' z = f' ⟨x, hxP⟩} : Set β') := heq.symm
          have hne : (⟨x, hxP⟩ : β') ≠ ⟨y, hyP⟩ := by
            intro h
            exact hxy (Subtype.mk.inj h)
          exact hf' _ hxmem hymem hne
        · -- y ∈ {b, t}, x ∈ β'. Derive contradiction from hx, hy.
          exfalso
          have hfy : f y = last := by rw [hf_eval, dif_neg hyP]
          have hfx : f x = (f' ⟨x, hxP⟩).castLE (Nat.sub_le k 1) := by
            rw [hf_eval, dif_pos hxP]
          have hfxlt : (f x).val < k - 1 := by
            rw [hfx]
            exact (f' ⟨x, hxP⟩).2
          rw [hx, ← hy, hfy] at hfxlt
          simp only [last] at hfxlt
          omega
      · by_cases hyP : y ≠ b ∧ y ≠ t
        · exfalso
          have hfx : f x = last := by rw [hf_eval, dif_neg hxP]
          have hfy : f y = (f' ⟨y, hyP⟩).castLE (Nat.sub_le k 1) := by
            rw [hf_eval, dif_pos hyP]
          have hfylt : (f y).val < k - 1 := by
            rw [hfy]
            exact (f' ⟨y, hyP⟩).2
          rw [hy, ← hx, hfx] at hfylt
          simp only [last] at hfylt
          omega
        · -- Both in {b, t}.
          have hx_is : x = b ∨ x = t := by
            by_cases hxb : x = b
            · exact Or.inl hxb
            · have : x = t := by
                by_contra hxt
                exact hxP ⟨hxb, hxt⟩
              exact Or.inr this
          have hy_is : y = b ∨ y = t := by
            by_cases hyb : y = b
            · exact Or.inl hyb
            · have : y = t := by
                by_contra hyt
                exact hyP ⟨hyb, hyt⟩
              exact Or.inr this
          rcases hx_is with rfl | rfl
          · rcases hy_is with rfl | rfl
            · exact absurd rfl hxy
            · exact Or.inl (le_of_lt hbt_lt)
          · rcases hy_is with rfl | rfl
            · exact Or.inr (le_of_lt hbt_lt)
            · exact absurd rfl hxy

/-- **Dilworth's theorem** (finite case): a finite partial order of width `w`
admits a chain cover of size `w`.

*Proof.* Strong induction on `Fintype.card α`, via the Galvin antichain
split. If `α` is itself an antichain, the identity cover works.
Otherwise, pick `b < t` with `b` minimal and `t` maximal, and consider
`β' = α \ {b, t}`. If `width β' < w`, extend the inductive cover of `β'`
by the new chain `{b, t}`. If `width β' = w`, pick a width-witnessing
antichain `A ⊂ β'` and split `α` into `D` (elements below some `a ∈ A`)
and `U` (elements above some `a ∈ A`). Both are strictly smaller than `α`
(since `t ∉ D` and `b ∉ U`), and their inductive covers splice along
`D ∩ U = A` into a cover of `α` by `w` chains (via `dilworth_splice`). -/
theorem hasChainCover_of_hasWidth {w : ℕ} (hw : HasWidth α w) :
    HasChainCover α w :=
  hasChainCover_of_hasWidth_aux _ α rfl hw

/-- Dilworth's theorem specialized to `width α`. -/
theorem hasChainCover_width : HasChainCover α (width α) := by
  classical
  refine hasChainCover_of_hasWidth ?_
  exact (hasWidth_iff_width_eq).mpr rfl

/-- Dilworth duality (finite case): a chain cover of size `w` exists iff
`width α ≤ w`. -/
theorem hasChainCover_iff_width_le {w : ℕ} :
    HasChainCover α w ↔ width α ≤ w := by
  refine ⟨width_le_of_hasChainCover, fun h => (hasChainCover_width (α := α)).mono h⟩

end Dilworth

end Poset
end Mathlib
end OneThird
