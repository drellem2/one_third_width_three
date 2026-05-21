/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredBalanced
import OneThird.Mathlib.Poset.Indecomposable
import OneThird.Mathlib.RelationPoset.LinearExt

/-!
# Minimal-counterexample machinery (Piece 4 — `mg-MA-MinCex`)

This file builds the minimal-counterexample machinery for the
proof-by-contradiction refactor of `width3_one_third_two_thirds`
(`docs/state-Piece4-Sig-Session1.md` §4.3/§4.4, paper
`thm:main-step8` `step8.tex:106-260` and `rem:decomp-reduction`
`step8.tex:274`).

## Deliverables

* `chain_of_subsingleton` — a poset with `≤ 1` element is a chain.
* `gamma_counterexample_of_no_BP` — a non-chain poset with no balanced
  pair *is* a `γ`-counterexample for a positive `γ ≤ 1/3`.
* `decomp_reduction` — a minimal `γ`-counterexample is indecomposable
  (paper `rem:decomp-reduction`).
* `ih_descent` — adapt the `Nat.strong_induction_on` induction
  hypothesis to the `< Fintype.card α` form `decomp_reduction` consumes.
* `hasBalancedPair_of_strongInduction` — the `Nat.strong_induction_on`
  minimal-counterexample induction principle, packaged so the
  `mg-MA-Body` cascade supplies only the inductive `step`.

## The `WithEdge` design resolution

`gamma_counterexample_of_no_BP` needs `probLT x y > 0` for every
incomparable pair `(x, y)` — otherwise the produced `γ` could not be
positive and the statement would be vacuous. Establishing this needs a
Szpilrajn-style witness: a linear extension of `α` with `x` placed
before `y`.

The first session of this ticket tried to build this via a fresh type
`WithEdge x y` (the poset `α` with the edge `x ≤ y` adjoined) and to
hand it a `private` `PartialOrder` instance.  Lean's type-class
resolution cannot find such an ad-hoc instance, and the session ground
in an edit-build-fail loop.

The resolution is **not** a new type at all.  The codebase already
provides the *order-refinement pattern*: `OneThird.RelationPoset α`
(`Mathlib/RelationPoset.lean`) is a poset whose order is a **value**
(a `Finset (α × α)`), not a typeclass — so there is nothing to
synthesize.  `RelationPoset.addRel` augments a poset by one
comparability, `RelationPoset.LinearExt'` / `probLT'` mirror the
typeclass linear-extension API, and `probLT'_ofPartialOrder` bridges
the data poset back to the typeclass `probLT`.  `probLT_pos_of_not_le`
below uses exactly this: it adjoins the edge `x ≤ y` with `addRel`,
takes a linear extension of the augmented data poset, restricts it
back, and concludes the filter of `x`-before-`y` extensions is
nonempty.

`decomp_reduction` needs no edge adjunction at all: it works entirely
with the existing `OrdinalDecomp` partition data and the
`hasBalancedPair_lift_lower` / `_upper` lifts.
-/

namespace OneThird

open OneThird.Mathlib.Poset

universe u

variable {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## §1 — Small posets are chains -/

omit [DecidableEq α] in
/-- A finite poset with at most one element is a chain: any two elements
are equal, hence comparable. -/
theorem chain_of_subsingleton (h : Fintype.card α ≤ 1) : IsChainPoset α := by
  have hss : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp h
  intro x y
  exact Or.inl (le_of_eq (Subsingleton.elim x y))

/-! ## §2 — Positivity of `probLT` for incomparable pairs

The order-refinement step.  `probLT x y` is the fraction of linear
extensions in which `x` precedes `y`.  Whenever `¬ y ≤ x` (in
particular for every incomparable pair) at least one linear extension
places `x` before `y`, so `probLT x y > 0`.  The witness is produced
by adjoining the edge `x ≤ y` to the data poset `ofPartialOrder α` via
`RelationPoset.addRel` and restricting a linear extension of the
augmentation back to the original. -/

/-- If `¬ y ≤ x` and `x ≠ y`, then `probLT x y > 0`: some linear
extension places `x` before `y`. -/
theorem probLT_pos_of_not_le {x y : α} (hne : x ≠ y) (hyx : ¬ y ≤ x) :
    0 < probLT x y := by
  classical
  -- The data poset of the ambient order, and its augmentation by `x ≤ y`.
  have hQyx : ¬ (RelationPoset.ofPartialOrder α).le y x := by
    rw [RelationPoset.ofPartialOrder_le_iff]
    exact hyx
  set Q := RelationPoset.ofPartialOrder α with hQ
  set Q' := RelationPoset.addRel Q x y hQyx with hQ'
  have hQ'lt : Q'.lt x y :=
    RelationPoset.lt_of_le_of_ne Q' (RelationPoset.addRel_le Q x y hQyx) hne
  have hsub : Q.Subseteq Q' := RelationPoset.subseteq_addRel Q x y hQyx
  -- A linear extension of `Q'` restricts to one of `Q` placing `x` before `y`.
  set L' := RelationPoset.LinearExt'.szpilrajn Q' with hL'
  set L := L'.restrict hsub with hL
  have hLlt : L.lt x y := by
    rw [hL, RelationPoset.LinearExt'.restrict_lt]
    exact L'.lt_of_lt hQ'lt
  have hmem : L ∈
      Finset.univ.filter (fun M : RelationPoset.LinearExt' Q => M.lt x y) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLlt⟩
  have hcard_pos : 0 <
      (Finset.univ.filter
        (fun M : RelationPoset.LinearExt' Q => M.lt x y)).card :=
    Finset.card_pos.mpr ⟨L, hmem⟩
  have hpos : 0 < RelationPoset.probLT' Q x y := by
    unfold RelationPoset.probLT'
    apply div_pos
    · exact_mod_cast hcard_pos
    · exact_mod_cast RelationPoset.numLinExt'_pos Q
  have heq : RelationPoset.probLT' Q x y = probLT x y := by
    rw [hQ]; exact RelationPoset.probLT'_ofPartialOrder x y
  rwa [heq] at hpos

/-! ## §3 — A non-chain poset with no balanced pair is a `γ`-counterexample -/

/-- **`gamma_counterexample_of_no_BP`.** If a finite poset is not a chain
and has no balanced pair, then it is a `γ`-counterexample for some
`γ` with `0 < γ ≤ 1/3`.

This is the entry point of the proof-by-contradiction body: it converts
`¬ HasBalancedPair α` (the negated goal) into the `IsGammaCounterexample`
hypothesis Theorem E and the Steps-1-7 cascade consume.

Non-vacuity: each incomparable pair `(x, y)` has
`0 < min (probLT x y) (probLT y x) < 1/3` — the lower bound from
`probLT_pos_of_not_le` (both one-sided probabilities are positive), the
upper bound from `¬ IsBalanced x y` together with
`probLT x y + probLT y x = 1`.  `γ` is taken as half the finite
infimum, over the (nonempty) set of incomparable pairs, of
`min (m p) (1/3 - m p)` where `m p` is the balance slack of `p`. -/
theorem gamma_counterexample_of_no_BP
    (hNonChain : ¬ IsChainPoset α) (hNoBP : ¬ HasBalancedPair α) :
    ∃ γ : ℚ, 0 < γ ∧ γ ≤ 1 / 3 ∧ IsGammaCounterexample α γ := by
  classical
  -- Per-pair bounds: `0 < min (probLT x y) (probLT y x) < 1/3`.
  have hpair : ∀ x y : α, x ∥ y →
      0 < min (probLT x y) (probLT y x) ∧
        min (probLT x y) (probLT y x) < 1 / 3 := by
    intro x y hxy
    have hne : x ≠ y := fun h => hxy.1 (h ▸ le_refl x)
    have hpos1 : 0 < probLT x y := probLT_pos_of_not_le hne hxy.2
    have hpos2 : 0 < probLT y x := probLT_pos_of_not_le hne.symm hxy.1
    have hsum : probLT x y + probLT y x = 1 := probLT_add_probLT_of_ne hne
    have hnb : ¬ IsBalanced x y := fun hb => hNoBP ⟨x, y, hxy, hb⟩
    simp only [IsBalanced, not_and, not_le] at hnb
    refine ⟨lt_min hpos1 hpos2, ?_⟩
    rcases lt_or_ge (probLT x y) (1 / 3) with hlt | hge
    · exact lt_of_le_of_lt (min_le_left _ _) hlt
    · have h23 : 2 / 3 < probLT x y := hnb hge
      have hyx : probLT y x < 1 / 3 := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hyx
  -- `S` = the set of incomparable ordered pairs; nonempty since non-chain.
  set S : Finset (α × α) :=
    Finset.univ.filter (fun p => p.1 ∥ p.2) with hSdef
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hNonChain
    intro x y
    by_contra hc
    push_neg at hc
    have hmem : (x, y) ∈ S := by
      rw [hSdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hc.1, hc.2⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  -- `F p` = `min (slack p) (1/3 − slack p)`, all positive on `S`.
  set F : α × α → ℚ := fun p =>
    min (min (probLT p.1 p.2) (probLT p.2 p.1))
        (1 / 3 - min (probLT p.1 p.2) (probLT p.2 p.1)) with hFdef
  set γ₀ : ℚ := S.inf' hSne F with hγ₀def
  have hF_pos : ∀ p ∈ S, 0 < F p := by
    intro p hp
    rw [hSdef, Finset.mem_filter] at hp
    obtain ⟨hb_pos, hb_lt⟩ := hpair p.1 p.2 hp.2
    simp only [hFdef]
    exact lt_min hb_pos (by linarith)
  have hγ₀_pos : 0 < γ₀ := by
    rw [hγ₀def, Finset.lt_inf'_iff]
    exact hF_pos
  refine ⟨γ₀ / 2, by linarith, ?_, ?_⟩
  · -- `γ₀ / 2 ≤ 1/3`.
    obtain ⟨p₀, hp₀⟩ := hSne
    have hle : γ₀ ≤ F p₀ := Finset.inf'_le F hp₀
    rw [hSdef, Finset.mem_filter] at hp₀
    obtain ⟨_, hslack_lt⟩ := hpair p₀.1 p₀.2 hp₀.2
    have hFle : F p₀ ≤ min (probLT p₀.1 p₀.2) (probLT p₀.2 p₀.1) := by
      simp only [hFdef]; exact min_le_left _ _
    linarith
  · -- `IsGammaCounterexample α (γ₀ / 2)`.
    intro x y hxy
    have hmem : (x, y) ∈ S := by
      rw [hSdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxy⟩
    have hle : γ₀ ≤ F (x, y) := Finset.inf'_le F hmem
    have hFle1 : F (x, y) ≤ min (probLT x y) (probLT y x) := by
      simp only [hFdef]; exact min_le_left _ _
    have hFle2 :
        F (x, y) ≤ 1 / 3 - min (probLT x y) (probLT y x) := by
      simp only [hFdef]; exact min_le_right _ _
    exact ⟨by linarith, by linarith⟩

/-! ## §4 — A minimal `γ`-counterexample is indecomposable

Paper `rem:decomp-reduction` (`step8.tex:274`).  If `α` is order-iso to
an ordinal sum `ordSum P₁ P₂` of two nonempty posets, then `α`
partitions into two nonempty `Finset`s `A < B` (the preimages of the
two summands).  At least one of the induced sub-posets `↥A`, `↥B` is
non-chain (otherwise `α` would be a chain), is strictly smaller than
`α`, and has width `≤ 3`; the induction hypothesis hands it a balanced
pair, which `hasBalancedPair_lift_lower` / `_upper` lifts to a balanced
pair of `α` — contradicting `¬ HasBalancedPair α`.

The hypothesis taken here is `¬ HasBalancedPair α` directly, rather than
`IsGammaCounterexample α γ` as written in the Piece-4 signature contract
§4.4: `decomp_reduction` uses only "no balanced pair", and deriving that
from `IsGammaCounterexample α γ` additionally needs `0 ≤ γ`.  Both
`¬ HasBalancedPair α` and `0 < γ` are in scope at the §4.8 call site
(`by_contra hNoBP`), so the call site is unaffected. -/

/-- If a poset splits as `A < B` with both `↥A` and `↥B` chains, the
whole poset is a chain. -/
private theorem isChainPoset_of_split {A B : Finset α}
    (hcover : A ∪ B = Finset.univ)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x < y)
    (hAchain : IsChainPoset (↥A)) (hBchain : IsChainPoset (↥B)) :
    IsChainPoset α := by
  intro x y
  have hx : x ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ x
  have hy : y ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ y
  rcases Finset.mem_union.mp hx with hxA | hxB
  · rcases Finset.mem_union.mp hy with hyA | hyB
    · rcases hAchain ⟨x, hxA⟩ ⟨y, hyA⟩ with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inl (hAB x hxA y hyB).le
  · rcases Finset.mem_union.mp hy with hyA | hyB
    · exact Or.inr (hAB y hyA x hxB).le
    · rcases hBchain ⟨x, hxB⟩ ⟨y, hyB⟩ with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- **`decomp_reduction`** (paper `rem:decomp-reduction`).  A finite
width-`3` non-chain poset with no balanced pair, all of whose strictly
smaller width-`3` non-chain induced sub-posets do have a balanced pair
(the induction hypothesis), is indecomposable. -/
theorem decomp_reduction
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hNoBP : ¬ HasBalancedPair α)
    (ih : ∀ m, m < Fintype.card α →
            ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
              Fintype.card β = m →
              HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β) :
    Indecomposable α := by
  classical
  rintro ⟨P₁, P₂, inst₁, inst₂, ⟨p₁⟩, ⟨p₂⟩, ⟨f⟩⟩
  letI := inst₁
  letI := inst₂
  -- `A`, `B` : preimages under `f` of the left / right summand.
  set A : Finset α :=
    Finset.univ.filter (fun a => (ofLex (f a)).isLeft = true) with hAdef
  set B : Finset α :=
    Finset.univ.filter (fun a => (ofLex (f a)).isLeft = false) with hBdef
  have hmemA : ∀ a, a ∈ A ↔ (ofLex (f a)).isLeft = true := by
    intro a; rw [hAdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hmemB : ∀ a, a ∈ B ↔ (ofLex (f a)).isLeft = false := by
    intro a; rw [hBdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- `A` carries the `inl` elements, `B` the `inr` elements.
  have hAinl : ∀ a ∈ A, ∃ p : P₁, ofLex (f a) = Sum.inl p := by
    intro a ha
    rw [hmemA] at ha
    rcases hs : ofLex (f a) with p | q
    · exact ⟨p, rfl⟩
    · rw [hs] at ha; simp at ha
  have hBinr : ∀ a ∈ B, ∃ q : P₂, ofLex (f a) = Sum.inr q := by
    intro a ha
    rw [hmemB] at ha
    rcases hs : ofLex (f a) with p | q
    · rw [hs] at ha; simp at ha
    · exact ⟨q, rfl⟩
  -- `A` and `B` partition `Finset.univ`.
  have hcover : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    rw [Finset.mem_union, hmemA, hmemB]
    cases h : (ofLex (f a)).isLeft with
    | true => exact Or.inl rfl
    | false => exact Or.inr rfl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    rw [hmemA] at haA
    rw [hmemB] at haB
    rw [haA] at haB
    exact Bool.noConfusion haB
  -- Every `A`-element is strictly below every `B`-element.
  have hAB : ∀ x ∈ A, ∀ y ∈ B, x < y := by
    intro x hx y hy
    obtain ⟨p, hp⟩ := hAinl x hx
    obtain ⟨q, hq⟩ := hBinr y hy
    have hfx : f x = toLex (Sum.inl p) := congrArg toLex hp
    have hfy : f y = toLex (Sum.inr q) := congrArg toLex hq
    have hlt : f x < f y := by
      rw [hfx, hfy]
      refine lt_of_le_of_ne (Sum.Lex.inl_le_inr p q) ?_
      intro h
      exact Sum.inl_ne_inr (congrArg ofLex h)
    exact (f.lt_iff_lt).mp hlt
  -- `A` and `B` are nonempty.
  have hAne : A.Nonempty := by
    refine ⟨f.symm (ordSum.inL p₁), ?_⟩
    rw [hmemA, f.apply_symm_apply]
    rfl
  have hBne : B.Nonempty := by
    refine ⟨f.symm (ordSum.inR p₂), ?_⟩
    rw [hmemB, f.apply_symm_apply]
    rfl
  -- Cardinality bookkeeping.
  have hpart : A.card + B.card = Fintype.card α := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]
  have hAcard : 0 < A.card := Finset.card_pos.mpr hAne
  have hBcard : 0 < B.card := Finset.card_pos.mpr hBne
  -- The ordinal-decomposition data `(A, ∅, B)`.
  let D : OrdinalDecomp α :=
    { Lower := A
      Mid := ∅
      Upper := B
      hCover := by rw [Finset.union_empty]; exact hcover
      hDisjLM := Finset.disjoint_empty_right A
      hDisjLU := hdisj
      hDisjMU := Finset.disjoint_empty_left B
      hLM_lt := fun _ _ y hy => absurd hy (Finset.notMem_empty y)
      hLU_lt := hAB
      hMU_lt := fun x hx => absurd hx (Finset.notMem_empty x) }
  -- One of `↥A`, `↥B` is non-chain; the IH hands it a balanced pair.
  by_cases hAchain : IsChainPoset (↥A)
  · -- `↥A` is a chain, so `↥B` is not.
    have hBnc : ¬ IsChainPoset (↥B) := fun hBchain =>
      hNonChain (isChainPoset_of_split hcover hAB hAchain hBchain)
    have hcardB : Fintype.card (↥B) < Fintype.card α := by
      rw [Fintype.card_coe]; omega
    have hbpB : HasBalancedPair (↥B) :=
      ih (Fintype.card (↥B)) hcardB (β := ↥B) rfl
        (Step8.hasWidthAtMost_subtype hP B) hBnc
    exact hNoBP (D.hasBalancedPair_lift_upper hbpB)
  · -- `↥A` is non-chain.
    have hcardA : Fintype.card (↥A) < Fintype.card α := by
      rw [Fintype.card_coe]; omega
    have hbpA : HasBalancedPair (↥A) :=
      ih (Fintype.card (↥A)) hcardA (β := ↥A) rfl
        (Step8.hasWidthAtMost_subtype hP A) hAchain
    exact hNoBP (D.hasBalancedPair_lift_lower hbpA)

/-! ## §5 — The minimal-counterexample strong induction -/

omit [PartialOrder α] [DecidableEq α] in
/-- **`ih_descent`.**  Re-index the `Nat.strong_induction_on` induction
hypothesis from "smaller than the running numeral `n`" to "smaller than
`Fintype.card α`", which is the form `decomp_reduction` consumes.  In
the induction body `hcard : Fintype.card α = n` is the equation
introduced by `induction hcard : Fintype.card α`. -/
theorem ih_descent {n : ℕ} (hcard : Fintype.card α = n)
    (ih : ∀ m, m < n →
            ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
              Fintype.card β = m →
              HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β) :
    ∀ m, m < Fintype.card α →
      ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
        Fintype.card β = m →
        HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β := by
  intro m hm
  exact ih m (hcard ▸ hm)

/-- **The minimal-counterexample induction.**  `Nat.strong_induction_on`
on `Fintype.card α`, packaged as an induction principle: to prove every
finite width-`3` non-chain poset has a balanced pair it suffices to give
the inductive `step` — produce a balanced pair from the width-`3`
non-chain hypotheses together with the induction hypothesis "every
strictly smaller width-`3` non-chain poset has a balanced pair".

This is the `Nat.strong_induction_on generalizing` minimal-counterexample
induction of the Piece-4 contract §4.3.  The `mg-MA-Body` proof of
`width3_one_third_two_thirds_assembled` discharges `step` with the
Theorem-E + Steps-1-7 + bridge + Piece-6 cascade.  The induction
hypothesis delivered to `step` is exactly the form `decomp_reduction`
consumes. -/
theorem hasBalancedPair_of_strongInduction
    (step : ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
              HasWidthAtMost β 3 → ¬ IsChainPoset β →
              (∀ m, m < Fintype.card β →
                ∀ {δ : Type u} [PartialOrder δ] [Fintype δ] [DecidableEq δ],
                  Fintype.card δ = m →
                  HasWidthAtMost δ 3 → ¬ IsChainPoset δ → HasBalancedPair δ) →
              HasBalancedPair β)
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α := by
  suffices h : ∀ n : ℕ,
      ∀ {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β],
        Fintype.card β = n →
        HasWidthAtMost β 3 → ¬ IsChainPoset β → HasBalancedPair β by
    exact h (Fintype.card α) rfl hP hNonChain
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro β _ _ _ hcard hPβ hNCβ
    exact step hPβ hNCβ (ih_descent hcard (fun m hm => ih m hm))

end OneThird
