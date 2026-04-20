/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Mathlib.DirichletForm
import OneThird.Mathlib.Poset.Indecomposable
import OneThird.Step8.FrozenPair

/-!
# Step 8 Theorem E: counterexample ⇒ low BK conductance

This file formalises the statements and the downstream assembly of
Step 8 / Theorem E (`step8.tex` §`sec:G1`). The file combines three
ingredients to close Theorem E:

* `OneThird.Step8.dirichletConductance` — `lem:dirichlet-conductance`
  (`step8.tex:115`). For a cut `S ⊆ 𝓛(P)`, the BK conductance is
  bounded by the Dirichlet/variance ratio of its indicator. Supplied
  at the project level by the Cheeger-for-indicators inequality
  `SimpleGraph.cheeger_indicator` proved in
  `OneThird.Mathlib.DirichletForm` (F7 foundation).

* `OneThird.Step8.indecExistsIncompPartner` — `lem:indec-incompairs`
  (`step8.tex:165`), project-level wrapper of
  `OneThird.Mathlib.Poset.Indecomposable.exists_incomp`. In a finite
  indecomposable poset of size `≥ 2`, every element has an
  incomparable partner.

* `OneThird.Step8.card_univ_le_ordIncompPairs_card` — quantitative form
  of `lem:indec-incompairs`: `|α| ≤ |{(x,y) : x ∥ y}|`. Proved in full
  from `indecExistsIncompPartner` via the injection `x ↦ (x, f x)`,
  where `f x` is any chosen incomparable partner of `x`. Corresponds
  to the `2 I(P) ≥ n` count in `step8.tex:191`.

* `OneThird.Step8.cexImpliesLowBKExpansion` — **Theorem E**
  (`thm:cex-implies-low-expansion`, `step8.tex:58`). For a width-3
  indecomposable `γ`-counterexample on `n ≥ 2` elements there is a
  cut `S ⊆ 𝓛(P)` of bulk volume `≥ γ · vol(𝓛(P))` and conductance
  `Φ(S) ≤ 2/(γ n)`. Proved by taking `S := pairCut x y` for a frozen
  pair `(x, y)` produced by
  `OneThird.Step8.frozenPairCut_exists` (`Step8/FrozenPair.lean`) and
  translating the `γ ≤ probLT x y` balance bound into the required
  `γ · vol(𝓛(P)) ≤ vol(S)` inequality.

The pair-order cut and indicator definitions (`pairCut`,
`pairIndicator`) together with the frozen-pair foundation lemma
(`frozenPairCut_exists`) live in `OneThird.Step8.FrozenPair` to avoid
an import cycle.

## References

`step8.tex` §`sec:G1` (Theorem E), Lemmas `lem:dirichlet-conductance`,
`lem:indec-incompairs`, `lem:frozen-pair-existence`.
-/

namespace OneThird.Step8

open Finset OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### `lem:dirichlet-conductance` -/

open Classical in
/-- **Dirichlet-vs-conductance inequality for indicators**
(`step8.tex:115`, `lem:dirichlet-conductance`, cleared form).

The project-level statement records the same cleared-denominator form
as the Mathlib-level `SimpleGraph.cheeger_indicator`:

`|∂S| · |S| · |Sᶜ| ≤ 𝓔(𝟙_S) · |𝓛(P)| · min(|S|, |Sᶜ|)`

where `𝓔` is the reversible-chain Dirichlet form of
`OneThird.Mathlib.DirichletForm`. Dividing through (for non-trivial
cuts) gives the `Φ(S) ≤ 𝓔(𝟙_S)/Var(𝟙_S)` statement of the paper.

This is a direct consequence of `SimpleGraph.cheeger_indicator` applied
to the Bubley–Karzanov graph `bkGraph α`. -/
theorem dirichletConductance (S : Finset (LinearExt α)) :
    (((bkGraph α).edgeBoundary S).card : ℚ) *
        ((S.card : ℚ) * ((Finset.univ \ S).card : ℚ)) ≤
      SimpleGraph.dirichletForm (bkGraph α)
          (fun L => if L ∈ S then (1 : ℚ) else 0) *
        ((Fintype.card (LinearExt α) : ℚ) *
          ((min S.card (Finset.univ \ S).card : ℕ) : ℚ)) :=
  (bkGraph α).cheeger_indicator S

/-! ### `lem:indec-incompairs` -/

omit [DecidableEq α] in
/-- **Indecomposable posets have incomparable partners**
(`step8.tex:165`, `lem:indec-incompairs`), project-level wrapper of
`OneThird.Mathlib.Poset.Indecomposable.exists_incomp`. -/
theorem indecExistsIncompPartner
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (h2 : 2 ≤ Fintype.card α) (x : α) :
    ∃ y : α, y ∥ x :=
  hI.exists_incomp h2 x

open Classical in
/-- The finset of ordered incomparable pairs `{(x, y) : x ∥ y}` in a
finite poset. Every unordered pair `{x, y}` contributes two elements
`(x, y)` and `(y, x)`, so `|ordIncompPairs| = 2 I(P)` in the
`step8.tex` notation. -/
noncomputable def ordIncompPairs (α : Type*)
    [PartialOrder α] [Fintype α] [DecidableEq α] : Finset (α × α) :=
  (Finset.univ : Finset (α × α)).filter (fun p => p.1 ∥ p.2)

/-- **Quantitative form of `lem:indec-incompairs`** (`step8.tex:191`).
In a finite indecomposable poset on `n ≥ 2` elements,
`n ≤ |{(x, y) : x ∥ y}|`. Equivalently `I(P) ≥ n/2` where `I(P)`
is the number of unordered incomparable pairs, since the LHS is
`2 · I(P)`.

The proof picks, for each `x`, an incomparable partner `f x` (by the
qualitative lemma) and observes that `x ↦ (x, f x)` injects `α` into
the ordered-incomparable-pair finset. -/
theorem card_univ_le_ordIncompPairs_card
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (h2 : 2 ≤ Fintype.card α) :
    Fintype.card α ≤ (ordIncompPairs α).card := by
  classical
  choose f hf using indecExistsIncompPartner hI h2
  have hmem : ∀ x : α, (x, f x) ∈ ordIncompPairs α := by
    intro x
    have hx : (x ∥ f x) := (hf x).symm
    simpa [ordIncompPairs] using hx
  have hinj : Function.Injective (fun x : α => (x, f x)) := by
    intro a b hab
    exact (Prod.mk.inj hab).1
  have himg_subset :
      (Finset.univ : Finset α).image (fun x => (x, f x)) ⊆ ordIncompPairs α := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x, _, rfl⟩
    exact hmem x
  calc Fintype.card α
      = (Finset.univ : Finset α).card := (Finset.card_univ).symm
    _ = ((Finset.univ : Finset α).image (fun x => (x, f x))).card :=
          (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (ordIncompPairs α).card := Finset.card_le_card himg_subset

/-! ### Theorem E -/

/-- **Theorem E** (`thm:cex-implies-low-expansion`, `step8.tex:58`).
For a width-3 indecomposable `γ`-counterexample `P` on `n ≥ 2`
elements with `γ ∈ (0, 1/3]`, there is a cut `S ⊆ 𝓛(P)` with

* `vol(S) ≥ γ · vol(𝓛(P))` (bulk volume);
* `Φ(S) ≤ 2/(γ n)` (low conductance).

The cut is the pair-order cut `S_xy = pairCut x y` of a frozen
incomparable pair `(x, y)` produced by
`OneThird.Step8.frozenPairCut_exists` (`Step8/FrozenPair.lean`;
`lem:frozen-pair-existence`, `step8.tex:195`). The frozen pair comes
with three data: `x ∥ y`, `γ ≤ probLT x y` (bulk), and
`Phi (pairCut x y) ≤ 2/(γn)` (low conductance). The `Phi`-bound is
the second conjunct verbatim; the `vol`-bound is the cardinality-to-
volume translation proved below (`γ · |𝓛(P)| ≤ |pairCut x y|` follows
from `γ ≤ |pairCut x y|/|𝓛(P)|`; multiply by `(n-1)` to upgrade to
`vol`).

This is the same statement as
`OneThird.counterexample_implies_low_BK_expansion` in
`OneThird/MainTheorem.lean`; the variant here additionally records
the indecomposability hypothesis from `step8.tex:59` (needed by the
averaging proof via `card_univ_le_ordIncompPairs_card`). The two
theorems are interchangeable along
`rem:decomp-reduction` (`step8.tex:274`): a minimal
`γ`-counterexample is always indecomposable. -/
theorem cexImpliesLowBKExpansion
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1 / 3)
    (hP : HasWidthAtMost α 3)
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α) :
    ∃ S : Finset (LinearExt α),
      (γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
        ≤ (volume S : ℚ)) ∧
      (Phi S ≤ 2 / (γ * (Fintype.card α : ℚ))) := by
  -- Frozen-pair foundation: pulls out an incomparable pair `(x, y)` for
  -- which `pairCut x y` is both bulk (`γ ≤ probLT x y`) and
  -- low-conductance (`Phi ≤ 2/(γn)`).
  obtain ⟨x, y, _hxy, hγxy, _hγyx, hΦ⟩ :=
    frozenPairCut_exists γ hγ_pos hγ_third hP hI hCex h2
  refine ⟨pairCut x y, ?_, hΦ⟩
  -- Remains to translate `γ ≤ probLT x y` into
  -- `γ · vol(𝓛(P)) ≤ vol(pairCut x y)`.
  have hN_pos : (0 : ℚ) < (numLinExt α : ℚ) := by
    exact_mod_cast numLinExt_pos
  have hCount : γ * (numLinExt α : ℚ) ≤ ((pairCut x y).card : ℚ) := by
    rw [probLT_eq_card_pairCut_div] at hγxy
    exact (le_div_iff₀ hN_pos).mp hγxy
  have hn1_nonneg : (0 : ℚ) ≤ ((Fintype.card α - 1 : ℕ) : ℚ) := by positivity
  have hVol :
      γ * ((numLinExt α : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ))
        ≤ ((pairCut x y).card : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ) := by
    calc γ * ((numLinExt α : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ))
        = γ * (numLinExt α : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ) := by ring
      _ ≤ ((pairCut x y).card : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ) :=
          mul_le_mul_of_nonneg_right hCount hn1_nonneg
  -- Translate `numLinExt α = |univ|` and unfold `volume`.
  have hvolUniv :
      ((volume (Finset.univ : Finset (LinearExt α)) : ℕ) : ℚ)
        = (numLinExt α : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ) := by
    change (((Finset.univ : Finset (LinearExt α)).card * (Fintype.card α - 1) : ℕ) : ℚ)
        = (numLinExt α : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ)
    rw [Finset.card_univ]
    push_cast
    rfl
  have hvolS :
      ((volume (pairCut x y) : ℕ) : ℚ)
        = ((pairCut x y).card : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ) := by
    change (((pairCut x y).card * (Fintype.card α - 1) : ℕ) : ℚ)
        = ((pairCut x y).card : ℚ) * ((Fintype.card α - 1 : ℕ) : ℚ)
    push_cast
    rfl
  rw [hvolUniv, hvolS]
  exact hVol

end OneThird.Step8
