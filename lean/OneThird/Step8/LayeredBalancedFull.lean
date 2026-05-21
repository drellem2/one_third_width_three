/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredBalanced
import OneThird.Step8.Case3Struct

/-!
# Step 8 — G4 (full): `lem_layered_balanced_full`

Formalises the **full** Step 8 G4 lemma `lem:layered-balanced`
(`step8.tex:2453-2464`, proof `step8.tex:3211-3266`): *every width-3
poset `P = (β, ≤)` with `|β| ≥ 2` that is not a chain and admits a
layered decomposition of interaction width `w ≤ 4` contains a balanced
pair.*

This is **Piece 6** of the Option A' FULL REFACTOR (mg-faf8 / mg-d8c7).
Unlike the bounded `lem_layered_balanced` (`LayeredBalanced.lean`),
which routes through `Case3Witness_proof` and so is restricted to the
*singleton-band* (`Function.Injective L.band`) sub-slice, the full form
below carries **only** the interaction-width cap `L.w ≤ 4` — exactly
the paper hypothesis — and so applies to **non-singleton-band** layered
decompositions (paper `def:layered` bands have size `≤ 3`).

## Proof architecture

Strong induction on `Fintype.card β` (the paper's outer induction on
`|X|`). The step dispatches on the **ordinal-sum structure** of `β`:

* **Case B — `β` is layer-ordinal reducible** at a band index `k` with
  *both* sides non-empty.  Then `β = β₁ ⊕ β₂` is a genuine two-part
  ordinal sum.  The incomparable pair lands wholly inside one
  (strictly smaller) side (a cross-pair would be `<`-forced by
  reducibility), so the induction hypothesis produces a balanced pair
  there, and `lem_layered_reduction` lifts it back to `β` via the
  ordinal-sum marginal-invariance identity.

* **Case C — `β` is (layer-ordinal) irreducible.**  The base case.
  * **C-twin** — if `β` has two distinct elements with identical
    ambient `<`-profile, `hasBalancedPair_of_ambient_profile_match`
    closes it (the transposition is a poset-automorphism, so the pair
    has `Pr = 1/2`).  This subsumes the `K = 1` single-antichain case
    of the paper.
  * **C-residual** — irreducible, width-3, non-chain, no profile
    collision: this is the genuine residual — paper
    `prop:in-situ-balanced` Cases 2 + 3 (the FKG profile-ordering
    argument and the finite profile-antichain enumeration).  It is
    discharged here by the **named, disclosed project axiom**
    `lem_layered_balanced_irreducible_base` — see its docstring and
    `lean/AXIOMS.md` for the full disclosure and the
    block-and-report to pm-onethird.

## Why the residual is genuinely an axiom (mg-65de finding)

The mg-fdc2 RED diagnostic (`docs/state-Piece6-FullStep8G4-Session1.md`)
already established that `Case3Witness_proof` cannot serve as the base
case (it needs band injectivity Piece 6's `L` does not carry).  This
session additionally found a **genuine gap in the paper proof**: the
paper's window-localization Case C1 (recurse on a proper window
`W ⊊ X`) is **impossible for an irreducible layered poset**.  An
ordinal middle piece needs its two boundary cuts to be clean (no
straddling incomparable pair); an irreducible poset has *no* clean cut
at all, so the only window is `W = X` itself.  And the paper's
`W = X ⟹ |X| ≤ 3(3w+1)` size bound is **false**: the poset
`{1,…,K}` with `i <_P j ⇔ j − i > 2` is irreducible, width 3, of
interaction width `w = 2`, with `K` *unbounded*.  So the irreducible
residual is genuinely unbounded and genuinely open — see the state
doc `docs/state-Piece6-Redo-Session1.md` §3.

The de-vacuified `windowLocalization` (`LayeredBalanced.lean`) and
`lem_layered_reduction` (`LayeredReduction.lean`) carry genuine
ordinal-sum marginal-invariance content; `lem_layered_reduction` is
wired into Case B here.

## Reference

`step8.tex` `lem:layered-balanced` (`:2453-2464`), proof
(`:3211-3266`); `prop:in-situ-balanced` (`:3096-3186`).
-/

namespace OneThird
namespace Step8

/-! ### §1 — The irreducible-base-case axiom -/

/-- **Irreducible-base-case axiom for `lem_layered_balanced_full`**
(`prop:in-situ-balanced` Cases 2 + 3, `step8.tex:3096-3186`).

For a width-3, non-chain poset `β` admitting a layered decomposition
`L` of interaction width `L.w ≤ 4` that is **layer-ordinal
irreducible** (`hIrr`: no band cut `k` is reducible with both sides
non-empty) and has **no profile collision** (`hNoTwin`: no two
distinct elements share an ambient `<`-profile), `β` contains a
balanced pair.

**Status: DISCLOSED PROJECT AXIOM (mg-65de).**  This is a genuine
sub-lemma *strictly weaker* than the headline `lem_layered_balanced_full`:
the reducible case (`¬hIrr`) is genuinely discharged by Case B of
`lem_layered_balanced_full` (ordinal-sum recursion + the de-vacuified
`lem_layered_reduction`), and the profile-collision case (`¬hNoTwin`)
is genuinely discharged by `hasBalancedPair_of_ambient_profile_match`.
What remains — irreducible *and* twin-free — is exactly the paper's
`prop:in-situ-balanced` Cases 2 (the Ahlswede–Daykin / FKG
profile-ordering inequality for linear extensions) and 3 (the finite
enumeration of width-3 profile antichains).

**Why an axiom and not a proof.**  Per the mg-65de genuine attempt
(`docs/state-Piece6-Redo-Session1.md`):

* the FKG / Ahlswede–Daykin inequality for linear extensions is not
  in the Lean tree and is listed as future work
  (`Mathlib/RelationPoset/FKG.lean §11`); the in-tree
  `Case2FKGSubClaim` is *provably false* (`OptionC/K2Closure.lean:21`);
* the irreducible residual is **genuinely unbounded** — the paper's
  `prop:in-situ-balanced` size bound `|Q| ≤ 3(3w+1)` does not hold
  for irreducible posets (counterexample: `{1,…,K}`, `i < j ⇔
  j − i > 2`, irreducible, width 3, `w = 2`, `K` unbounded), so the
  existing bounded enumeration certificates (`case3_certificate`,
  mg-4d7b) do not cover it;
* the paper's own window-localization Case C1 recursion is invalid
  for irreducible posets (no clean sub-window exists).

This axiom is therefore the **minimal precise residual** of Piece 6,
filed for pm-onethird review (ticket mg-65de).  It is faithfully
transcribed from `prop:in-situ-balanced`, which mg-faf8
satisfiability-verified as a sound proposition. -/
axiom lem_layered_balanced_irreducible_base.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ OneThird.IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4)
    (hIrr : ¬ ∃ k : ℕ, 1 ≤ k ∧ k < L.K ∧ LayerOrdinalReducible L k ∧
        ((Finset.univ : Finset β).filter (fun z => k < L.band z)).Nonempty ∧
        ((Finset.univ : Finset β).filter (fun z => L.band z ≤ k)).Nonempty)
    (hNoTwin : ¬ ∃ a a' : β, a ≠ a' ∧
        (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')) :
    OneThird.HasBalancedPair β

/-! ### §2 — `lem_layered_balanced_full` -/

set_option linter.unusedVariables false in
/-- **`lem:layered-balanced` — full Step 8 G4** (`step8.tex:2453-2464`,
proof `:3211-3266`).  **Piece 6 of the FULL REFACTOR.**

Every width-3 poset `β` with `|β| ≥ 2` that is not a chain and admits
a layered decomposition `L` of interaction width `L.w ≤ 4` contains a
balanced pair.

The hypothesis is **only** `L.w ≤ 4` — the paper hypothesis — with no
band-injectivity / depth / cardinality cap.  In particular it applies
to genuine `def:layered` decompositions with **non-singleton bands**
(bands of size `≤ 3`), which the bounded `lem_layered_balanced` (routed
through the singleton-band `Case3Witness_proof`) does not.

**Proof.**  Strong induction on `Fintype.card β`.  The step:

* extract an incomparable pair `(x, y)` from `¬ IsChainPoset β`;
* **Case B** — if `L` is layer-ordinal reducible at some band index
  `k` with both sides non-empty: the pair lies wholly in one side
  (`hRed` `<`-forces every cross-pair), recurse there via the
  induction hypothesis on `L.restrict`, and lift with
  `lem_layered_reduction` (the de-vacuified G3 reduction);
* **Case C-twin** — else, if `β` has a profile collision: close with
  `hasBalancedPair_of_ambient_profile_match`;
* **Case C-residual** — else (`β` irreducible, twin-free): close with
  the disclosed axiom `lem_layered_balanced_irreducible_base`. -/
theorem lem_layered_balanced_full.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ OneThird.IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :
    OneThird.HasBalancedPair β := by
  classical
  -- Strong induction on the numeric `Fintype.card β`, generalising β.
  suffices h : ∀ n : ℕ, ∀ (β : Type u) [PartialOrder β] [Fintype β]
      [DecidableEq β] (L : LayeredDecomposition β),
      Fintype.card β = n →
      2 ≤ Fintype.card β →
      ¬ OneThird.IsChainPoset β →
      HasWidthAtMost β 3 →
      L.w ≤ 4 →
      OneThird.HasBalancedPair β by
    exact h (Fintype.card β) β L rfl h2 hNotChain hW3 hLw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro β _ _ _ L hcard h2 hNotChain hW3 hLw
    -- Extract an incomparable pair from the non-chain hypothesis.
    have hpair : ∃ x y : β, ¬ x ≤ y ∧ ¬ y ≤ x := by
      unfold OneThird.IsChainPoset at hNotChain
      push_neg at hNotChain
      exact hNotChain
    obtain ⟨x, y, hxle, hyle⟩ := hpair
    have hxyInc : x ∥ y := ⟨hxle, hyle⟩
    -- Local recursion helper: a strictly-smaller non-chain side `S`
    -- containing `(x, y)` has a balanced pair (by the IH on `L.restrict S`).
    have recSide : ∀ (S : Finset β), x ∈ S → y ∈ S → (∃ z, z ∉ S) →
        OneThird.HasBalancedPair ↥S := by
      intro S hxS hyS hProper
      have hcardLt : Fintype.card ↥S < n := by
        rw [Fintype.card_coe]
        have hss : S ⊂ (Finset.univ : Finset β) := by
          obtain ⟨z, hz⟩ := hProper
          exact ⟨Finset.subset_univ _,
            fun hc => hz (hc (Finset.mem_univ z))⟩
        have hlt := Finset.card_lt_card hss
        rw [Finset.card_univ, hcard] at hlt
        exact hlt
      have hxneβ : x ≠ y := fun hxyeq => hxle (hxyeq ▸ le_refl x)
      have h2S : 2 ≤ Fintype.card ↥S := by
        rw [Fintype.card_coe]
        have h1 : 1 < S.card :=
          Finset.one_lt_card.mpr ⟨x, hxS, y, hyS, hxneβ⟩
        omega
      have hNCS : ¬ OneThird.IsChainPoset ↥S := by
        intro hch
        rcases hch ⟨x, hxS⟩ ⟨y, hyS⟩ with hcmp | hcmp
        · exact hxle hcmp
        · exact hyle hcmp
      have hW3S : HasWidthAtMost ↥S 3 := hasWidthAtMost_subtype hW3 S
      have hLwS : (L.restrict S).w ≤ 4 := by
        rw [LayeredDecomposition.w_restrict]; exact hLw
      exact ih (Fintype.card ↥S) hcardLt ↥S (L.restrict S) rfl h2S hNCS
        hW3S hLwS
    -- **Case split** on layer-ordinal reducibility with both sides
    -- non-empty (a genuine two-part ordinal cut).
    by_cases hNice : ∃ k : ℕ, 1 ≤ k ∧ k < L.K ∧ LayerOrdinalReducible L k ∧
        ((Finset.univ : Finset β).filter (fun z => k < L.band z)).Nonempty ∧
        ((Finset.univ : Finset β).filter (fun z => L.band z ≤ k)).Nonempty
    · -- **Case B — reducible.**
      obtain ⟨k, hk1, hkK, hRed, hUpNE, hLoNE⟩ := hNice
      have hLowerNE :
          (OrdinalDecompOfReducible L k hRed).Lower.Nonempty := hLoNE
      have hUpperNE :
          (OrdinalDecompOfReducible L k hRed).Upper.Nonempty := hUpNE
      -- The pair lies wholly in one side: a cross-pair is `<`-forced.
      rcases le_or_gt (L.band x) k with hxk | hxk <;>
        rcases le_or_gt (L.band y) k with hyk | hyk
      · -- both in the lower side `{band ≤ k}`.
        refine lem_layered_reduction
          ⟨OrdinalDecompOfReducible L k hRed,
            OrdinalDecompOfReducible_Mid L k hRed, hLowerNE, hUpperNE,
            Or.inl (recSide _ ?_ ?_ ?_)⟩
        · rw [mem_OrdinalDecompOfReducible_Lower]; exact hxk
        · rw [mem_OrdinalDecompOfReducible_Lower]; exact hyk
        · obtain ⟨z, hz⟩ := hUpNE
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact ⟨z, by
            rw [mem_OrdinalDecompOfReducible_Lower]; omega⟩
      · -- `band x ≤ k < band y`: reducibility forces `x < y`.
        exact absurd (hRed x y hxk hyk).le hxle
      · -- `band y ≤ k < band x`: reducibility forces `y < x`.
        exact absurd (hRed y x hyk hxk).le hyle
      · -- both in the upper side `{band > k}`.
        refine lem_layered_reduction
          ⟨OrdinalDecompOfReducible L k hRed,
            OrdinalDecompOfReducible_Mid L k hRed, hLowerNE, hUpperNE,
            Or.inr (recSide _ ?_ ?_ ?_)⟩
        · rw [mem_OrdinalDecompOfReducible_Upper]; exact hxk
        · rw [mem_OrdinalDecompOfReducible_Upper]; exact hyk
        · obtain ⟨z, hz⟩ := hLoNE
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact ⟨z, by
            rw [mem_OrdinalDecompOfReducible_Upper]; omega⟩
    · -- **Case C — irreducible.**
      by_cases hTwin : ∃ a a' : β, a ≠ a' ∧
          (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')
      · -- **C-twin** — a profile collision gives `Pr = 1/2`.
        obtain ⟨a, a', hne, hup, hdown⟩ := hTwin
        exact hasBalancedPair_of_ambient_profile_match a a' hne hup hdown
      · -- **C-residual** — irreducible, twin-free: the disclosed axiom.
        exact lem_layered_balanced_irreducible_base L h2 hNotChain hW3 hLw
          hNice hTwin

/-! ### §3 — Combined G3 + G4 conclusion (full form) -/

/-- **Combined G3 + G4 conclusion, full form** (`step8.tex:3187-3204`).

Restatement of `lem_layered_balanced_full` matching the assembly
interface: a width-3 non-chain poset admitting a layered decomposition
of interaction width `≤ 4` has a balanced pair.  This is the form the
S7-F bridge (`lem_layered_from_step7`, MA-Sig §4.2 §E) feeds into —
its conclusion is exactly the three-cap `LayeredDecomposition` with
`L.w ≤ 4` (mg-faf8), and Piece 6 is its consumer (MA-Sig §4.2 §G). -/
theorem layered_implies_balanced_full.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ OneThird.IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :
    OneThird.HasBalancedPair β :=
  lem_layered_balanced_full L h2 hNotChain hW3 hLw

end Step8
end OneThird
