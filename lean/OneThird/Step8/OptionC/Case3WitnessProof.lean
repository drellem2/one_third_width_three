/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredBalanced
import OneThird.Step8.LayeredDecomposition.Compactify
import OneThird.Step8.OptionC.K2Closure
import OneThird.Step8.BoundedIrreducibleBalanced
import OneThird.Step8.BoundedIrreducibleBalancedInScope
import OneThird.Step8.Case3Residual
import OneThird.Step8.Case3Enum.Certificate
import OneThird.Step8.Case3Enum.AllBalancedBridge

/-!
# Step 8 — Option-C Stage 2B (`mg-8c72`): `Case3Witness_proof`

Discharges the (Candidate A''-tightened) `Step8.Case3Witness.{u}`
universal of `OneThird/Step8/LayeredBalanced.lean` as a Lean theorem,
making `OneThird.width3_one_third_two_thirds` hypothesis-free
(modulo `hP` and `hNonChain`, matching the paper's
`thm:main`).

## Architecture

The proof is a strong induction on `Fintype.card β`, with the F3-style
K-dispatch enabled by the four cap-antecedents of Candidate A''
(`Function.Injective LB.band`, `LB.K ≤ 2 * LB.w + 2`,
`Fintype.card β ≤ 6 * LB.w + 6`, and `(LB.bandSet k).Nonempty` on
`[1, LB.K]`):

* **K = 1**: vacuous under cap 1 + `2 ≤ |β|`. Two distinct elements
  share band 1, contradicting injectivity.
* **K = 2**:
  * If `LayerOrdinalReducible LB 1`: under cap 1 each band has at
    most one element; combined with cap 4 each band has exactly one
    element, forcing `|β| = 2` with the unique cross-pair
    `(M_1, M_2)` reduced to `<`. Then `β` is a chain, contradicting
    `¬IsChainPoset β`.
  * If `LayerOrdinalIrreducible LB`: apply `option_c_K2_closure`
    (`mg-01ec` Stage 1).
* **K ≥ 3**: dispatch on layered-ordinal reducibility.
  * If reducible at some `k`: descend on the piece carrying the
    incomparable pair via `LB.compactify` (caps 1-3 propagate via
    the Stage 2A `compactify_*_le_of_*_le` /
    `compactify_band_injective_of_injective` lemmas; cap 4 holds
    by construction of `compactify`).
  * If irreducible: apply `bounded_irreducible_balanced_hybrid`.
    The `hCert` slot consumes `bounded_irreducible_balanced_inScope`
    fed by `case3_certificate` via `allBalanced_imp_enumPosetsFor`.
    The `hStruct` slot consumes `hStruct_of_case2_discharge` with
    `case2Discharge` provided by the Injective cap (the Case 2
    predicate posits two distinct elements with equal bands — vacuous
    under `Function.Injective`).

## Reference

* `mg-8c72` — this work item (Option-C Stage 2B).
* `mg-2a56` — Stage 2A (compactify infrastructure).
* `mg-01ec` — Stage 1 (K=2 substantive closure).
* `mg-979e-block-and-report.md` §1.b — Candidate A'' shape origin
  and the empty-band obstruction this file routes around via
  `compactify`.
-/

namespace OneThird
namespace Step8
namespace OptionC

open Step8 LayeredDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ### §1 — Helper lemmas -/

/-- Under cap 1 (Injective band), `K = 1` is inconsistent with
`2 ≤ Fintype.card β`. Every element has band 1 (forced by
`band_pos`/`band_le` at K = 1), so two distinct elements share
band 1, contradicting injectivity. -/
private lemma absurd_K1_of_injective
    {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : LayeredDecomposition β) (hK1 : LB.K = 1)
    (hInj : Function.Injective LB.band)
    (h2 : 2 ≤ Fintype.card β) : False := by
  -- Two distinct elements exist (Finset.one_lt_card on univ).
  rw [show 2 = 1 + 1 from rfl] at h2
  rw [← Finset.card_univ] at h2
  obtain ⟨x, _, y, _, hne⟩ := Finset.one_lt_card.mp h2
  -- Both have band ≤ K = 1 and band ≥ 1, so band x = band y = 1.
  have hxle : LB.band x ≤ 1 := by rw [← hK1]; exact LB.band_le x
  have hxge : 1 ≤ LB.band x := LB.band_pos x
  have hyle : LB.band y ≤ 1 := by rw [← hK1]; exact LB.band_le y
  have hyge : 1 ≤ LB.band y := LB.band_pos y
  have hxy : LB.band x = LB.band y := by omega
  exact hne (hInj hxy)

/-- Under caps 1 (Injective) + 4 (non-empty bands) + `K = 2` +
`LayerOrdinalReducible LB 1`, `β` is forced to be a chain.

**Proof sketch.** Each band has size ≤ 1 (Injective) and ≥ 1
(non-empty), so size exactly 1. The unique elements `x ∈ M_1`,
`y ∈ M_2` are forced into `x < y` by reducibility at `k = 1`. Any
other element coincides with one of `x, y` (since `|β| = 2` by the
band-size argument). So `β = {x, y}` is a chain. -/
private lemma isChain_of_K2_reducible_under_injective
    {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : LayeredDecomposition β) (hK2 : LB.K = 2)
    (hInj : Function.Injective LB.band)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ LB.K → (LB.bandSet k).Nonempty)
    (hRed : LayerOrdinalReducible LB 1) : IsChainPoset β := by
  classical
  intro a b
  -- Band trichotomy: each of `a`, `b` has band 1 or band 2.
  have ha_pos : 1 ≤ LB.band a := LB.band_pos a
  have ha_le : LB.band a ≤ 2 := by rw [← hK2]; exact LB.band_le a
  have hb_pos : 1 ≤ LB.band b := LB.band_pos b
  have hb_le : LB.band b ≤ 2 := by rw [← hK2]; exact LB.band_le b
  -- Case split on band a vs band b.
  rcases lt_or_eq_of_le ha_le with ha2_lt | ha2_eq
  · -- band a = 1.
    have ha1 : LB.band a = 1 := by omega
    rcases lt_or_eq_of_le hb_le with hb2_lt | hb2_eq
    · -- band b = 1: by Injective, a = b.
      have hb1 : LB.band b = 1 := by omega
      have : LB.band a = LB.band b := by omega
      exact Or.inl ((hInj this) ▸ le_refl a)
    · -- band b = 2: reducibility at k = 1 forces a < b.
      have hb2 : LB.band b = 2 := hb2_eq
      have hred_b : 1 < LB.band b := by omega
      exact Or.inl (le_of_lt (hRed a b (le_of_eq ha1) hred_b))
  · -- band a = 2.
    have ha2 : LB.band a = 2 := ha2_eq
    rcases lt_or_eq_of_le hb_le with hb2_lt | hb2_eq
    · -- band b = 1: reducibility forces b < a.
      have hb1 : LB.band b = 1 := by omega
      have hred_a : 1 < LB.band a := by omega
      exact Or.inr (le_of_lt (hRed b a (le_of_eq hb1) hred_a))
    · -- band b = 2: by Injective, a = b.
      have hb2 : LB.band b = 2 := hb2_eq
      have : LB.band a = LB.band b := by omega
      exact Or.inl ((hInj this) ▸ le_refl a)

/-- The Case 2 witness predicate of `Step8.InSitu.Case2Witness` is
vacuous under the Injective band cap: it posits two distinct elements
`a ≠ a'` with `LB.band a = LB.band a'`, contradicting `Injective`. -/
private lemma case2_discharge_of_injective
    {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]
    {LB : LayeredDecomposition β} (hInj : Function.Injective LB.band) :
    Step8.InSitu.Case2Witness LB → HasBalancedPair β := by
  intro hCase2
  obtain ⟨a, a', hne, hb_eq, _, _⟩ := hCase2
  exact absurd (hInj hb_eq) hne

/-- Specialisation of `case3_certificate` together with
`allBalanced_imp_enumPosetsFor` / `allBalancedAtK_imp_enumPosetsFor`
and `bandSizes_mem_bandSizesGen` to produce the
`enumPosetsFor LB.w (bandSizes LB) = true` Bool fact required by
`bounded_irreducible_balanced_inScope` whenever `InCase3Scope` holds
and bands are non-empty.

Post-`mg-9a4a` Window C (small size-limit variant), `InCase3Scope`
is the two-way disjunction

  * `K = 3 ∧ w ∈ {1,…,4} ∧ size caps` (original K=3 cert via
    `case3_balanced_w{1,…,4}`).
  * `K = 4 ∧ w = 1 ∧ card ≤ 8`        (the `mg-9a4a` K=4 small-size
                                      extension `case3_balanced_K4_w1`).

So the dispatch first splits K=3 vs K=4, then on `w` inside K=3. -/
private lemma enumPosetsFor_eq_true_of_inScope
    {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : LayeredDecomposition β)
    (hScope : InCase3Scope LB.w (Fintype.card β) LB.K)
    (hNonemptyB : ∀ k : ℕ, 1 ≤ k → k ≤ LB.K → 1 ≤ Step8.bandSize LB k) :
    Step8.Case3Enum.enumPosetsFor LB.w (Step8.bandSizes LB) = true := by
  classical
  -- Pick the right entry of `case3_certificate`.
  rcases Step8.Case3Enum.case3_certificate with
    ⟨hw1cert, hw2cert, hw3cert, hw4cert, hK4w1cert⟩
  -- Two-way split on `InCase3Scope`.
  rcases hScope with ⟨hK3, _hw_pos, _hw_le, hcap1, hcap2⟩
                   | ⟨hK4, hw1, hcard8⟩
  · -- K=3 branch: four-way split on `w`.
    have hw_split : LB.w = 1 ∨ LB.w = 2 ∨ LB.w = 3 ∨ LB.w = 4 := by
      rcases Nat.lt_or_ge LB.w 2 with hlt | hge
      · exact Or.inl (by omega)
      rcases Nat.lt_or_ge LB.w 3 with hlt | hge
      · exact Or.inr (Or.inl (by omega))
      rcases Nat.lt_or_ge LB.w 4 with hlt | hge
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (by omega)))
    rcases hw_split with hw | hw | hw | hw
    · -- w = 1: sizeLimit = 9 (case3_balanced_w1).
      have hCard : Fintype.card β ≤ 9 := hcap1 hw
      have hMem : Step8.bandSizes LB ∈ Step8.Case3Enum.bandSizesGen LB.K 9 :=
        Step8.bandSizes_mem_bandSizesGen LB 9 hCard hNonemptyB
      rw [hK3] at hMem
      rw [hw]
      exact Step8.Case3Enum.allBalanced_imp_enumPosetsFor 1 9 hw1cert _ hMem
    · -- w = 2: sizeLimit = 7 (case3_balanced_w2).
      have hCard : Fintype.card β ≤ 7 := hcap2 (by omega)
      have hMem : Step8.bandSizes LB ∈ Step8.Case3Enum.bandSizesGen LB.K 7 :=
        Step8.bandSizes_mem_bandSizesGen LB 7 hCard hNonemptyB
      rw [hK3] at hMem
      rw [hw]
      exact Step8.Case3Enum.allBalanced_imp_enumPosetsFor 2 7 hw2cert _ hMem
    · -- w = 3: sizeLimit = 7 (case3_balanced_w3).
      have hCard : Fintype.card β ≤ 7 := hcap2 (by omega)
      have hMem : Step8.bandSizes LB ∈ Step8.Case3Enum.bandSizesGen LB.K 7 :=
        Step8.bandSizes_mem_bandSizesGen LB 7 hCard hNonemptyB
      rw [hK3] at hMem
      rw [hw]
      exact Step8.Case3Enum.allBalanced_imp_enumPosetsFor 3 7 hw3cert _ hMem
    · -- w = 4: sizeLimit = 7 (case3_balanced_w4).
      have hCard : Fintype.card β ≤ 7 := hcap2 (by omega)
      have hMem : Step8.bandSizes LB ∈ Step8.Case3Enum.bandSizesGen LB.K 7 :=
        Step8.bandSizes_mem_bandSizesGen LB 7 hCard hNonemptyB
      rw [hK3] at hMem
      rw [hw]
      exact Step8.Case3Enum.allBalanced_imp_enumPosetsFor 4 7 hw4cert _ hMem
  · -- K=4 branch: w = 1, sizeLimit = 8 (case3_balanced_K4_w1).
    have hMem : Step8.bandSizes LB ∈ Step8.Case3Enum.bandSizesGen LB.K 8 :=
      Step8.bandSizes_mem_bandSizesGen LB 8 hcard8 hNonemptyB
    rw [hK4] at hMem
    rw [hw1]
    exact Step8.Case3Enum.allBalancedAtK_imp_enumPosetsFor 4 1 8 hK4w1cert _
      hMem

/-! ### §2 — Main proof: `Case3Witness_proof`

The four Candidate A'' caps survive sub-poset descent:

* **Injective** — `compactify_band_injective_of_injective` (Stage 2A,
  `mg-2a56`).
* **K-cap** — `compactify_K_le_of_K_le` plus `compactify_w_eq`.
* **Cardinality cap** — `compactify_card_le_of_card_le` plus
  `compactify_w_eq`.
* **Non-empty bands** — `compactify_bandSet_nonempty` (`mg-8c72`,
  added inline to `Compactify.lean` since the proof rests on the
  rank/orderIsoOfFin identity rather than `bandSize` infrastructure).

These together with the operational headline path's caps (`mg-8c72`)
discharge the threading. -/

/-- **`Case3Witness_proof`** (Option-C Stage 2B, `mg-8c72`).

The Candidate A''-tightened universal `Step8.Case3Witness` is a
theorem: every layered width-3 non-chain `β` with `2 ≤ |β|` whose
layered decomposition `LB` carries the four cap-antecedents
(Injective band, K-cap, cardinality cap, non-empty bands) admits a
balanced pair.

The proof is a strong induction on `Fintype.card β`, with the F3
K-dispatch documented in the file header. -/
theorem Case3Witness_proof.{u} : Step8.Case3Witness.{u} := by
  classical
  -- Strong induction on `Fintype.card β`, generalising over `β`.
  -- **Cap 5 (`mg-d5a0`, `LB.w ≤ 4`).** Threaded through the strong
  -- induction; preserved on `compactify` descent by
  -- `LayeredDecomposition.compactify_w_eq`, so the recursion call
  -- supplies `LB'.w ≤ 4` from `LB.w ≤ 4` directly. The hypothesis
  -- is *not* consumed by the K = 1 contradiction, the K = 2
  -- `option_c_K2_closure` dispatch, or the K ≥ 3
  -- `bounded_irreducible_balanced_hybrid` dispatch — it is purely a
  -- threading obligation on this end. The architectural debt lives
  -- in the *consumer-side* `lem_layered_balanced` K ≥ 2 dispatch
  -- (`LayeredBalanced.lean:668`), where `canonicalLayered α` cannot
  -- satisfy cap 5.
  suffices h : ∀ n : ℕ, ∀ (β : Type u) [PartialOrder β] [Fintype β]
      [DecidableEq β] (LB : Step8.LayeredDecomposition β),
      Fintype.card β ≤ n →
      Function.Injective LB.band →
      LB.K ≤ 2 * LB.w + 2 →
      Fintype.card β ≤ 6 * LB.w + 6 →
      (∀ k : ℕ, 1 ≤ k → k ≤ LB.K → (LB.bandSet k).Nonempty) →
      LB.w ≤ 4 →
      HasWidthAtMost β 3 →
      ¬ IsChainPoset β →
      2 ≤ Fintype.card β →
      HasBalancedPair β by
    intro β _ _ _ LB hInj hKw hCardw hNonempty hLBw hW3 hNC h2
    exact h (Fintype.card β) β LB (le_refl _) hInj hKw hCardw hNonempty
      hLBw hW3 hNC h2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intros β _ _ _ LB hcard_le hInj hKw hCardw hNonempty hLBw hW3 hNC h2
    -- Case split on `LB.K`.
    rcases Nat.lt_or_ge LB.K 2 with hK1 | hK2
    · -- K ≤ 1: actually K = 1 since `1 ≤ LB.K` (any element provides this
      -- via `band_pos` + `band_le`; we have `2 ≤ |β|` so an element exists).
      have hcard_pos : 1 ≤ Fintype.card β := by omega
      obtain ⟨x⟩ := Fintype.card_pos_iff.mp hcard_pos
      have hK_pos : 1 ≤ LB.K := (LB.band_pos x).trans (LB.band_le x)
      have hK_eq1 : LB.K = 1 := by omega
      exact absurd (absurd_K1_of_injective LB hK_eq1 hInj h2) id
    · -- K ≥ 2.
      rcases Nat.lt_or_ge LB.K 3 with hK_eq2 | hK3
      · -- **K = 2 case.**
        have hK2_eq : LB.K = 2 := by omega
        -- Reducible at k=1 vs irreducible.
        by_cases hRed : LayerOrdinalReducible LB 1
        · -- Reducible: forces β to be a chain.
          exfalso
          exact hNC (isChain_of_K2_reducible_under_injective LB hK2_eq hInj
            hNonempty hRed)
        · -- Irreducible: apply `option_c_K2_closure`.
          exact OptionC.option_c_K2_closure LB hW3 hNC hK2_eq h2 hRed
      · -- **K ≥ 3 case.**
        -- Try reducible at some k ∈ [1, K-1].
        by_cases hRedSome : ∃ k : ℕ, 1 ≤ k ∧ k < LB.K ∧
            LayerOrdinalReducible LB k
        · -- Reducible: descend on the piece carrying the incomparable pair.
          obtain ⟨k, hk1, hkLt, hRed⟩ := hRedSome
          set D := OrdinalDecompOfReducible LB k hRed with hD_def
          -- Get incomparable pair (x, y) from ¬IsChainPoset.
          unfold IsChainPoset at hNC
          push_neg at hNC
          obtain ⟨x, y, hxy_le, hyx_le⟩ := hNC
          have hxy_inc : x ∥ y := ⟨hxy_le, hyx_le⟩
          -- The pair (x, y) cannot be cross-pair (reducibility forces <).
          -- So both x, y are in D.Lower or both in D.Upper.
          have hxbnd : LB.band x ≤ k ∨ k < LB.band x := by omega
          have hybnd : LB.band y ≤ k ∨ k < LB.band y := by omega
          -- Case on band x and band y.
          have hpair_in : (x ∈ D.Lower ∧ y ∈ D.Lower) ∨
              (x ∈ D.Upper ∧ y ∈ D.Upper) := by
            rcases hxbnd with hxlo | hxhi
            · rcases hybnd with hylo | hyhi
              · -- Both in Lower.
                left
                refine ⟨?_, ?_⟩
                · rw [mem_OrdinalDecompOfReducible_Lower]; exact hxlo
                · rw [mem_OrdinalDecompOfReducible_Lower]; exact hylo
              · -- x in Lower, y in Upper: cross-pair, x < y forced.
                exfalso
                exact hxy_le (le_of_lt (hRed x y hxlo hyhi))
            · rcases hybnd with hylo | hyhi
              · -- y in Lower, x in Upper: y < x forced.
                exfalso
                exact hyx_le (le_of_lt (hRed y x hylo hxhi))
              · -- Both in Upper.
                right
                refine ⟨?_, ?_⟩
                · rw [mem_OrdinalDecompOfReducible_Upper]; exact hxhi
                · rw [mem_OrdinalDecompOfReducible_Upper]; exact hyhi
          -- Recurse on the side carrying the pair.
          rcases hpair_in with ⟨hxL, hyL⟩ | ⟨hxU, hyU⟩
          · -- Recurse on D.Lower.
            -- Build LB' := LB.compactify D.Lower.
            let LB' : LayeredDecomposition ↥D.Lower :=
              LB.compactify D.Lower
            -- Cardinality: |↥D.Lower| < |β|, since D.Upper non-empty.
            have hUpper_nonempty : D.Upper.Nonempty := by
              -- band K element exists (by hNonempty K) with band K > k.
              obtain ⟨z, hz⟩ := hNonempty LB.K (by omega) (le_refl _)
              rw [LayeredDecomposition.mem_bandSet] at hz
              exact ⟨z, by
                rw [mem_OrdinalDecompOfReducible_Upper]
                rw [hz]; omega⟩
            have hcard_strict : Fintype.card ↥D.Lower < Fintype.card β := by
              -- |Lower| + |Upper| = |β| (D.Mid = ∅).
              have hcover := D.hCover
              have hdisj := D.hDisjLU
              have hmid : D.Mid = ∅ := rfl
              -- |Lower ∪ Upper| = |β| (univ).
              have hsum :
                  D.Lower.card + D.Upper.card = Fintype.card β := by
                have h1 : D.Lower ∪ D.Upper = (Finset.univ : Finset β) := by
                  rw [← hcover, hmid, Finset.union_empty]
                have h2 : (D.Lower ∪ D.Upper).card =
                    D.Lower.card + D.Upper.card := by
                  rw [Finset.card_union_of_disjoint hdisj]
                rw [← h2, h1, Finset.card_univ]
              -- |↥D.Lower| = D.Lower.card via Fintype.card_coe.
              have hLcard : Fintype.card ↥D.Lower = D.Lower.card :=
                Fintype.card_coe _
              have hUpos : 0 < D.Upper.card :=
                Finset.card_pos.mpr hUpper_nonempty
              omega
            -- Caps for LB'.
            have hInj' : Function.Injective LB'.band :=
              LayeredDecomposition.compactify_band_injective_of_injective
                LB D.Lower hInj
            have hKw' : LB'.K ≤ 2 * LB'.w + 2 := by
              have hKle := LayeredDecomposition.compactify_K_le LB D.Lower
              have hweq := LayeredDecomposition.compactify_w_eq LB D.Lower
              show LB'.K ≤ 2 * LB'.w + 2
              calc LB'.K
                  ≤ LB.K := hKle
                _ ≤ 2 * LB.w + 2 := hKw
                _ = 2 * LB'.w + 2 := by rw [hweq]
            have hCardw' : Fintype.card ↥D.Lower ≤ 6 * LB'.w + 6 := by
              have hweq := LayeredDecomposition.compactify_w_eq LB D.Lower
              calc Fintype.card ↥D.Lower
                  ≤ Fintype.card β := Fintype.card_subtype_le _
                _ ≤ 6 * LB.w + 6 := hCardw
                _ = 6 * LB'.w + 6 := by rw [hweq]
            have hNonempty' : ∀ k : ℕ, 1 ≤ k → k ≤ LB'.K →
                (LB'.bandSet k).Nonempty := by
              intro k' hk1' hkK'
              exact compactify_bandSet_nonempty LB D.Lower hk1' hkK'
            -- Width-3 transfers to subtype.
            have hW3' : HasWidthAtMost ↥D.Lower 3 :=
              hasWidthAtMost_subtype hW3 D.Lower
            -- Non-chain on ↥D.Lower (contains x, y incomparable).
            have hNC' : ¬ IsChainPoset ↥D.Lower := by
              intro hchain
              rcases hchain ⟨x, hxL⟩ ⟨y, hyL⟩ with hle | hle
              · exact hxy_le hle
              · exact hyx_le hle
            -- 2 ≤ |↥D.Lower| (contains x, y).
            have hxne : (⟨x, hxL⟩ : ↥D.Lower) ≠ ⟨y, hyL⟩ := by
              intro h
              have : x = y := by
                have := (Subtype.mk.injEq x hxL y hyL).mp h
                exact this
              exact hxy_le (this ▸ le_refl x)
            have h2' : 2 ≤ Fintype.card ↥D.Lower := by
              have := Finset.one_lt_card.mpr
                ⟨(⟨x, hxL⟩ : ↥D.Lower), Finset.mem_univ _,
                 (⟨y, hyL⟩ : ↥D.Lower), Finset.mem_univ _, hxne⟩
              rw [Finset.card_univ] at this
              exact this
            -- Cap 5 propagates via `compactify_w_eq`.
            have hLBw' : LB'.w ≤ 4 := by
              have hweq := LayeredDecomposition.compactify_w_eq LB D.Lower
              show LB'.w ≤ 4
              calc LB'.w = LB.w := hweq
                _ ≤ 4 := hLBw
            -- Apply IH.
            have hcard_le' : Fintype.card ↥D.Lower < n := by omega
            have hbp_lower : HasBalancedPair ↥D.Lower :=
              ih (Fintype.card ↥D.Lower) hcard_le' ↥D.Lower LB'
                (le_refl _) hInj' hKw' hCardw' hNonempty' hLBw' hW3' hNC' h2'
            -- Lift to β.
            exact D.hasBalancedPair_lift_lower hbp_lower
          · -- Recurse on D.Upper. (Symmetric to D.Lower.)
            let LB' : LayeredDecomposition ↥D.Upper :=
              LB.compactify D.Upper
            -- |↥D.Upper| < |β|, since D.Lower non-empty (band 1 element).
            have hLower_nonempty : D.Lower.Nonempty := by
              obtain ⟨z, hz⟩ := hNonempty 1 (le_refl _) (by omega)
              rw [LayeredDecomposition.mem_bandSet] at hz
              exact ⟨z, by
                rw [mem_OrdinalDecompOfReducible_Lower]
                rw [hz]; omega⟩
            have hcard_strict : Fintype.card ↥D.Upper < Fintype.card β := by
              have hcover := D.hCover
              have hdisj := D.hDisjLU
              have hmid : D.Mid = ∅ := rfl
              have hsum :
                  D.Lower.card + D.Upper.card = Fintype.card β := by
                have h1 : D.Lower ∪ D.Upper = (Finset.univ : Finset β) := by
                  rw [← hcover, hmid, Finset.union_empty]
                have h2 : (D.Lower ∪ D.Upper).card =
                    D.Lower.card + D.Upper.card := by
                  rw [Finset.card_union_of_disjoint hdisj]
                rw [← h2, h1, Finset.card_univ]
              have hUcard : Fintype.card ↥D.Upper = D.Upper.card :=
                Fintype.card_coe _
              have hLpos : 0 < D.Lower.card :=
                Finset.card_pos.mpr hLower_nonempty
              omega
            -- Caps for LB'.
            have hInj' : Function.Injective LB'.band :=
              LayeredDecomposition.compactify_band_injective_of_injective
                LB D.Upper hInj
            have hKw' : LB'.K ≤ 2 * LB'.w + 2 := by
              have hKle := LayeredDecomposition.compactify_K_le LB D.Upper
              have hweq := LayeredDecomposition.compactify_w_eq LB D.Upper
              calc LB'.K
                  ≤ LB.K := hKle
                _ ≤ 2 * LB.w + 2 := hKw
                _ = 2 * LB'.w + 2 := by rw [hweq]
            have hCardw' : Fintype.card ↥D.Upper ≤ 6 * LB'.w + 6 := by
              have hweq := LayeredDecomposition.compactify_w_eq LB D.Upper
              calc Fintype.card ↥D.Upper
                  ≤ Fintype.card β := Fintype.card_subtype_le _
                _ ≤ 6 * LB.w + 6 := hCardw
                _ = 6 * LB'.w + 6 := by rw [hweq]
            have hNonempty' : ∀ k : ℕ, 1 ≤ k → k ≤ LB'.K →
                (LB'.bandSet k).Nonempty := by
              intro k' hk1' hkK'
              exact compactify_bandSet_nonempty LB D.Upper hk1' hkK'
            have hW3' : HasWidthAtMost ↥D.Upper 3 :=
              hasWidthAtMost_subtype hW3 D.Upper
            have hNC' : ¬ IsChainPoset ↥D.Upper := by
              intro hchain
              rcases hchain ⟨x, hxU⟩ ⟨y, hyU⟩ with hle | hle
              · exact hxy_le hle
              · exact hyx_le hle
            have hxne : (⟨x, hxU⟩ : ↥D.Upper) ≠ ⟨y, hyU⟩ := by
              intro h
              have : x = y := by
                have := (Subtype.mk.injEq x hxU y hyU).mp h
                exact this
              exact hxy_le (this ▸ le_refl x)
            have h2' : 2 ≤ Fintype.card ↥D.Upper := by
              have := Finset.one_lt_card.mpr
                ⟨(⟨x, hxU⟩ : ↥D.Upper), Finset.mem_univ _,
                 (⟨y, hyU⟩ : ↥D.Upper), Finset.mem_univ _, hxne⟩
              rw [Finset.card_univ] at this
              exact this
            -- Cap 5 propagates via `compactify_w_eq`.
            have hLBw' : LB'.w ≤ 4 := by
              have hweq := LayeredDecomposition.compactify_w_eq LB D.Upper
              show LB'.w ≤ 4
              calc LB'.w = LB.w := hweq
                _ ≤ 4 := hLBw
            have hcard_le' : Fintype.card ↥D.Upper < n := by omega
            have hbp_upper : HasBalancedPair ↥D.Upper :=
              ih (Fintype.card ↥D.Upper) hcard_le' ↥D.Upper LB'
                (le_refl _) hInj' hKw' hCardw' hNonempty' hLBw' hW3' hNC' h2'
            exact D.hasBalancedPair_lift_upper hbp_upper
        · -- Irreducible: apply `bounded_irreducible_balanced_hybrid`.
          push_neg at hRedSome
          have hIrr : LayerOrdinalIrreducible LB := by
            intro k' hk1' hkLt'
            exact hRedSome k' hk1' hkLt'
          -- Auxiliary: `1 ≤ LB.w`. From `K ≥ 3` and `K ≤ 2w + 2`.
          have hw_pos : 1 ≤ LB.w := by omega
          -- `hCert`: in-scope branch via `bounded_irreducible_balanced_inScope`.
          have hCert : InCase3Scope LB.w (Fintype.card β) LB.K →
              HasBalancedPair β := by
            intro hScope
            -- Convert `(bandSet k).Nonempty` to `1 ≤ bandSize`.
            have hNonemptyB :
                ∀ k : ℕ, 1 ≤ k → k ≤ LB.K → 1 ≤ Step8.bandSize LB k := by
              intro k hk1 hkK
              have := hNonempty k hk1 hkK
              show 0 < (LB.bandSet k).card
              exact Finset.card_pos.mpr this
            have h_cert :=
              enumPosetsFor_eq_true_of_inScope LB hScope hNonemptyB
            exact Step8.bounded_irreducible_balanced_inScope LB hW3 hIrr
              hScope hNonemptyB h_cert
          -- `hStruct`: out-of-scope branch via `hStruct_of_case2_discharge`
          -- + Case 2 discharge from Injective.
          have hStruct : ¬ InCase3Scope LB.w (Fintype.card β) LB.K →
              HasBalancedPair β :=
            Step8.InSitu.hStruct_of_case2_discharge LB hW3 hIrr
              hK3 hw_pos hCardw hKw (case2_discharge_of_injective hInj)
          -- Apply hybrid dispatch.
          exact bounded_irreducible_balanced_hybrid LB hW3 hIrr hK3 hw_pos
            hCardw hKw hCert hStruct

end OptionC
end Step8
end OneThird
