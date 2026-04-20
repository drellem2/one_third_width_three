/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Mathlib.Poset.Indecomposable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Step 8 frozen-pair foundation: pair-order cut and conductance bound

Pair-ordering cut definitions and the BK-Dirichlet / frozen-pair foundation
lemma driving Theorem E (`step8.tex` §`sec:G1`). Kept in a separate file
from `Step8/TheoremE.lean` so the downstream assembly there (the
`cexImpliesLowBKExpansion` proof) can import this file without a cycle.

## Contents

* `OneThird.Step8.pairCut x y` — the cut
  `S_xy = {L ∈ 𝓛(P) : x <_L y}` of linear extensions that place `x`
  before `y` (`step8.tex:98`).
* `OneThird.Step8.pairIndicator x y` — the `ℚ`-valued indicator
  `f_xy = 𝟙_{S_xy}` (`step8.tex:100`) driving the Dirichlet form in the
  frozen-pair averaging.
* `OneThird.Step8.frozenPairCut_exists` — **frozen-pair foundation
  lemma** bundling `lem:dirichlet-conductance` (`step8.tex:114-152`) and
  `lem:frozen-pair-existence` (`step8.tex:195-273`).

## The foundation lemma

`frozenPairCut_exists` packages the deep content of Theorem E: for a
width-3 indecomposable `γ`-counterexample on `n ≥ 2` elements there is
an incomparable pair `(x, y)` whose pair-order cut `pairCut x y` is both

* bulk (`γ ≤ probLT x y` and `γ ≤ probLT y x`, directly from the
  strengthened `IsGammaCounterexample`); and
* low-conductance (`Phi ≤ 2 / (γ · n)`, from the averaging argument).

The proof is the paper's averaging argument. It combines:

1. The **BK-Dirichlet foundation** `edgeBoundary_pairCut_sum_le`
   (`OneThird/LinearExtension.lean`): the total pair-cut edge boundary
   summed over ordered incomparable pairs is at most `(n - 1) · |𝓛(P)|`.
   This is the only Mathlib-tier deferral.

2. The **counterexample γ-bound**: the strengthened
   `OneThird.IsGammaCounterexample` (`OneThird/LinearExtension.lean`,
   matching `step8.tex:30-33`) gives `γ ≤ min(p_{xy}, p_{yx})` for
   every incomparable pair.

3. The **incomparable-pair count**: in a finite indecomposable poset
   of size `n ≥ 2`, the number of ordered incomparable pairs is at
   least `n` (elementary consequence of
   `OneThird.Mathlib.Poset.Indecomposable.exists_incomp`).

Averaging the ratio `|∂S_{xy}| · |𝓛(P)| / (|S_{xy}| · |S_{xy}^c|)`
produces an incomparable pair `(x, y)` with
`Phi(pairCut x y) ≤ 2/(γ · n)`. -/

namespace OneThird.Step8

open Finset OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### Pair-ordering cut and indicator -/

/-- The cut `S_xy = {L ∈ 𝓛(P) : x <_L y}` of linear extensions that
place `x` before `y` in `step8.tex:98`. When `(x, y)` is an
incomparable pair, this gives a non-trivial subset of `𝓛(P)` whose
indicator is the pair test function driving Theorem E. -/
noncomputable def pairCut (x y : α) : Finset (LinearExt α) :=
  (Finset.univ : Finset (LinearExt α)).filter (fun L => L.lt x y)

/-- The pair test function `f_xy = 𝟙_{S_xy}` of `step8.tex:100`, as a
map `LinearExt α → ℚ`. Its `ℚ`-valued indicator is the input to the
Dirichlet form through `SimpleGraph.cheeger_indicator`. -/
noncomputable def pairIndicator (x y : α) : LinearExt α → ℚ :=
  fun L => if L ∈ pairCut x y then (1 : ℚ) else 0

lemma pairIndicator_eq (x y : α) :
    pairIndicator x y =
      (fun L : LinearExt α => if L ∈ pairCut x y then (1 : ℚ) else 0) :=
  rfl

lemma mem_pairCut {x y : α} {L : LinearExt α} :
    L ∈ pairCut x y ↔ L.lt x y := by
  simp [pairCut]

/-- The cardinality of `pairCut x y` equals the numerator of
`probLT x y = |pairCut x y| / |𝓛(P)|`. -/
lemma probLT_eq_card_pairCut_div (x y : α) :
    probLT x y = ((pairCut x y).card : ℚ) / (numLinExt α : ℚ) :=
  rfl

/-- On an incomparable pair, `pairCut y x` is the complement of
`pairCut x y` in `𝓛(P)`. -/
lemma pairCut_compl {x y : α} (hxy : x ∥ y) :
    ((Finset.univ : Finset (LinearExt α)) \ pairCut x y) = pairCut y x := by
  have hne : x ≠ y := fun h => hxy.1 (le_of_eq h)
  ext L
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_pairCut]
  constructor
  · intro hL
    rcases lt_trichotomy (L.pos x) (L.pos y) with h | h | h
    · exact (hL h).elim
    · exact absurd (L.pos_injective h) hne
    · exact h
  · intro hL hL'
    exact absurd (hL.trans hL') (lt_irrefl _)

/-- Cardinality form: `|univ \ pairCut x y| = |pairCut y x|`. -/
lemma card_sdiff_pairCut {x y : α} (hxy : x ∥ y) :
    ((Finset.univ : Finset (LinearExt α)) \ pairCut x y).card =
      (pairCut y x).card := by
  rw [pairCut_compl hxy]

/-! ### Ordered incomparable pairs -/

/-- The finset of ordered incomparable pairs `{(x, y) : x ∥ y}`. -/
noncomputable def orderedIncompPairs (α : Type*)
    [PartialOrder α] [Fintype α] [DecidableEq α] : Finset (α × α) := by
  classical
  exact (Finset.univ : Finset (α × α)).filter (fun p : α × α => p.1 ∥ p.2)

lemma mem_orderedIncompPairs {p : α × α} :
    p ∈ orderedIncompPairs α ↔ p.1 ∥ p.2 := by
  classical
  simp [orderedIncompPairs]

/-- **Quantitative form of `lem:indec-incompairs`** (`step8.tex:191`):
the number of ordered incomparable pairs is at least `n`. -/
theorem card_le_orderedIncompPairs_card
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (h2 : 2 ≤ Fintype.card α) :
    Fintype.card α ≤ (orderedIncompPairs α).card := by
  classical
  choose f hf using hI.exists_incomp (α := α) h2
  have hmem : ∀ x : α, (x, f x) ∈ orderedIncompPairs α := by
    intro x
    exact (mem_orderedIncompPairs).mpr (hf x).symm
  have hinj : Function.Injective (fun x : α => (x, f x)) := by
    intro a b hab; exact (Prod.mk.inj hab).1
  have himg_subset :
      (Finset.univ : Finset α).image (fun x => (x, f x)) ⊆
        orderedIncompPairs α := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x, _, rfl⟩
    exact hmem x
  calc Fintype.card α
      = (Finset.univ : Finset α).card := (Finset.card_univ).symm
    _ = ((Finset.univ : Finset α).image (fun x => (x, f x))).card :=
          (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (orderedIncompPairs α).card := Finset.card_le_card himg_subset

/-! ### Per-pair variance bound -/

/-- Per-pair variance translation: for an incomparable pair `(x, y)` with
`γ ≤ min(p_{xy}, p_{yx})` (and `γ ≤ 1/2`), the cut-size product is at
least `γ(1-γ) · N²`. This is the project-level form of
`Var(f_xy) ≥ γ(1-γ)` from `step8.tex:238`. -/
private lemma gamma_le_sizeProd
    {γ : ℚ} (hγ_pos : 0 < γ)
    {x y : α} (hxy : x ∥ y)
    (hγmin : γ ≤ min (probLT x y) (probLT y x)) :
    γ * (1 - γ) * (numLinExt α : ℚ) ^ 2 ≤
      ((pairCut x y).card : ℚ) * ((pairCut y x).card : ℚ) := by
  have hxy_ne : x ≠ y := fun h => hxy.1 (le_of_eq h)
  set N : ℕ := numLinExt α
  have hN_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast numLinExt_pos
  have hγ_le_pxy : γ ≤ probLT x y := le_trans hγmin (min_le_left _ _)
  have hγ_le_pyx : γ ≤ probLT y x := le_trans hγmin (min_le_right _ _)
  have hsum : probLT x y + probLT y x = 1 :=
    probLT_add_probLT_of_ne hxy_ne
  have hpxy_le : probLT x y ≤ 1 - γ := by
    have : probLT x y = 1 - probLT y x := by linarith
    linarith
  -- (p - γ)(1-γ - p) ≥ 0 ⇒ p(1-p) ≥ γ(1-γ)
  have hkey : γ * (1 - γ) ≤ probLT x y * probLT y x := by
    have hyx_eq : probLT y x = 1 - probLT x y := by linarith
    rw [hyx_eq]
    nlinarith [hγ_le_pxy, hpxy_le, hγ_pos, sq_nonneg (probLT x y - γ),
      sq_nonneg (1 - γ - probLT x y)]
  -- Translate to cardinalities
  have hpxy_eq : probLT x y = ((pairCut x y).card : ℚ) / (N : ℚ) :=
    probLT_eq_card_pairCut_div x y
  have hpyx_eq : probLT y x = ((pairCut y x).card : ℚ) / (N : ℚ) :=
    probLT_eq_card_pairCut_div y x
  rw [hpxy_eq, hpyx_eq] at hkey
  have hN2_pos : (0 : ℚ) < (N : ℚ) ^ 2 := by positivity
  have : γ * (1 - γ) * (N : ℚ) ^ 2 ≤
      (((pairCut x y).card : ℚ) / (N : ℚ)) *
        (((pairCut y x).card : ℚ) / (N : ℚ)) * (N : ℚ) ^ 2 :=
    mul_le_mul_of_nonneg_right hkey (le_of_lt hN2_pos)
  have hNne : (N : ℚ) ≠ 0 := ne_of_gt hN_pos
  calc γ * (1 - γ) * (N : ℚ) ^ 2
      ≤ (((pairCut x y).card : ℚ) / (N : ℚ)) *
          (((pairCut y x).card : ℚ) / (N : ℚ)) * (N : ℚ) ^ 2 := this
    _ = ((pairCut x y).card : ℚ) * ((pairCut y x).card : ℚ) := by
        field_simp

/-! ### Frozen-pair foundation lemma -/

/-- **Frozen-pair cut (foundation form; `lem:frozen-pair-existence` +
`lem:dirichlet-conductance`).**

For a width-3 indecomposable `γ`-counterexample on `n ≥ 2` elements with
`γ ∈ (0, 1/3]`, there exists an incomparable pair `(x, y)` whose
pair-order cut `S_xy = pairCut x y` is simultaneously

* bulk: `γ ≤ probLT x y` and `γ ≤ probLT y x` (directly from the
  strengthened `IsGammaCounterexample`);
* low-conductance: `Phi (pairCut x y) ≤ 2 / (γ n)` (via averaging). -/
theorem frozenPairCut_exists
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1 / 3)
    (_hP : HasWidthAtMost α 3)
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α) :
    ∃ x y : α, (x ∥ y) ∧
      γ ≤ probLT x y ∧ γ ≤ probLT y x ∧
      Phi (pairCut x y) ≤ 2 / (γ * (Fintype.card α : ℚ)) := by
  classical
  set n : ℕ := Fintype.card α with hn_def
  set N : ℕ := numLinExt α with hN_def
  have hN_pos : 0 < N := numLinExt_pos
  have hN_posQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN_pos
  have hn_ge_two : 2 ≤ n := h2
  have hn_pos : 0 < n := by omega
  have hn_posQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
  have hγ_half : γ ≤ 1 / 2 := by linarith
  have h1mγ_pos : (0 : ℚ) < 1 - γ := by linarith
  have h1mγ_ge_half : (1 : ℚ) / 2 ≤ 1 - γ := by linarith
  have hγ1mγ_pos : 0 < γ * (1 - γ) := mul_pos hγ_pos h1mγ_pos
  have hn_minus_one_pos : 0 < n - 1 := by omega
  have hn_minus_one_posQ : (0 : ℚ) < ((n - 1 : ℕ) : ℚ) := by
    exact_mod_cast hn_minus_one_pos
  -- pairs = ordered incomparable pairs
  set pairs : Finset (α × α) := orderedIncompPairs α with hpairs_def
  have hpairs_card : n ≤ pairs.card := card_le_orderedIncompPairs_card hI h2
  have hpairs_nonempty : pairs.Nonempty := by
    have : 0 < pairs.card := by linarith
    exact Finset.card_pos.mp this
  -- Per-pair functions
  let e : α × α → ℕ := fun p => edgeBoundary (pairCut p.1 p.2)
  let b : α × α → ℕ := fun p => (pairCut p.1 p.2).card * (pairCut p.2 p.1).card
  -- Variance bound per pair
  have hb_lower : ∀ p ∈ pairs, γ * (1 - γ) * (N : ℚ) ^ 2 ≤ (b p : ℚ) := by
    intro p hp
    have hxy : p.1 ∥ p.2 := (mem_orderedIncompPairs).mp hp
    have hγmin : γ ≤ min (probLT p.1 p.2) (probLT p.2 p.1) := (hCex p.1 p.2 hxy).1
    have hbound := gamma_le_sizeProd (α := α) hγ_pos hxy hγmin
    show γ * (1 - γ) * (↑N) ^ 2 ≤
      ↑((pairCut p.1 p.2).card * (pairCut p.2 p.1).card)
    push_cast
    exact hbound
  -- Edge-sum upper bound
  have he_sum_le : (∑ p ∈ pairs, e p) ≤ (n - 1) * N := by
    exact @edgeBoundary_pairCut_sum_le α _ _ _
  have he_sum_leQ : (∑ p ∈ pairs, (e p : ℚ)) ≤ ((n - 1 : ℕ) * N : ℚ) := by
    have hcast : (∑ p ∈ pairs, (e p : ℚ)) = ((∑ p ∈ pairs, e p : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast]; exact_mod_cast he_sum_le
  -- Total b bound
  have hb_sum_lower :
      γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ) ≤ (∑ p ∈ pairs, (b p : ℚ)) := by
    have hγ1mγN2_nonneg : 0 ≤ γ * (1 - γ) * (N : ℚ) ^ 2 := by positivity
    calc γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)
        ≤ γ * (1 - γ) * (N : ℚ) ^ 2 * (pairs.card : ℚ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hpairs_card)
            hγ1mγN2_nonneg
      _ = ∑ _p ∈ pairs, γ * (1 - γ) * (N : ℚ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (∑ p ∈ pairs, (b p : ℚ)) := Finset.sum_le_sum hb_lower
  -- Pigeonhole: ∃ p ∈ pairs, e(p) · γ(1-γ)N²n ≤ (n-1)N · b(p)
  have hExistsPair :
      ∃ p ∈ pairs,
        (e p : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) ≤
          ((n - 1 : ℕ) * N : ℚ) * (b p : ℚ) := by
    by_contra hAll
    push_neg at hAll
    have hstrict : ∀ p ∈ pairs,
        ((n - 1 : ℕ) * N : ℚ) * (b p : ℚ) <
          (e p : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) := hAll
    have hSum_strict :
        (∑ p ∈ pairs, ((n - 1 : ℕ) * N : ℚ) * (b p : ℚ)) <
          (∑ p ∈ pairs,
             (e p : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ))) :=
      Finset.sum_lt_sum_of_nonempty hpairs_nonempty hstrict
    rw [← Finset.mul_sum] at hSum_strict
    have hRHS :
        (∑ p ∈ pairs,
           (e p : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ))) =
          (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) *
            (∑ p ∈ pairs, (e p : ℚ)) := by
      rw [← Finset.sum_mul]; ring
    rw [hRHS] at hSum_strict
    have h_n1N_pos : (0 : ℚ) < ((n - 1 : ℕ) * N : ℚ) :=
      mul_pos hn_minus_one_posQ hN_posQ
    have hγ1mγN2n_nonneg : 0 ≤ γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ) := by
      positivity
    -- From hSum_strict: (n-1)N · Σb < γ(1-γ)N²n · Σe ≤ γ(1-γ)N²n · (n-1)N
    have h_rhs_bound :
        (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) * (∑ p ∈ pairs, (e p : ℚ)) ≤
          (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) * ((n - 1 : ℕ) * N : ℚ) :=
      mul_le_mul_of_nonneg_left he_sum_leQ hγ1mγN2n_nonneg
    have h_combined :
        ((n - 1 : ℕ) * N : ℚ) * (∑ p ∈ pairs, (b p : ℚ)) <
          (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) *
            ((n - 1 : ℕ) * N : ℚ) :=
      lt_of_lt_of_le hSum_strict h_rhs_bound
    have h_div : (∑ p ∈ pairs, (b p : ℚ)) <
        γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ) := by
      have hcomm : (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) *
            ((n - 1 : ℕ) * N : ℚ) =
          ((n - 1 : ℕ) * N : ℚ) *
            (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) := by ring
      have := h_combined
      rw [hcomm] at this
      exact lt_of_mul_lt_mul_left this (le_of_lt h_n1N_pos)
    linarith
  -- Extract the pair
  obtain ⟨⟨x, y⟩, hmem, hineq⟩ := hExistsPair
  have hxy : x ∥ y := (mem_orderedIncompPairs).mp hmem
  have hCex_xy := hCex x y hxy
  have hγmin : γ ≤ min (probLT x y) (probLT y x) := hCex_xy.1
  have hγxy : γ ≤ probLT x y := le_trans hγmin (min_le_left _ _)
  have hγyx : γ ≤ probLT y x := le_trans hγmin (min_le_right _ _)
  refine ⟨x, y, hxy, hγxy, hγyx, ?_⟩
  -- Now prove Phi (pairCut x y) ≤ 2/(γn)
  set S := pairCut x y with hS_def
  set sC := (Finset.univ : Finset (LinearExt α)) \ S with hsC_def
  -- sC = pairCut y x
  have hsC_eq : sC = pairCut y x := pairCut_compl hxy
  set ssize : ℕ := S.card with hssize_def
  set scsize : ℕ := sC.card with hscsize_def
  have hscsize_eq : scsize = (pairCut y x).card := by
    change sC.card = (pairCut y x).card
    rw [hsC_eq]
  -- hineq in terms of ssize, scsize
  have h_b_eq : (b (x, y) : ℚ) = (ssize : ℚ) * (scsize : ℚ) := by
    change (((pairCut x y).card * (pairCut y x).card : ℕ) : ℚ) =
      (ssize : ℚ) * (scsize : ℚ)
    rw [hscsize_eq]
    push_cast
    rfl
  have hineq' :
      (edgeBoundary S : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) ≤
        ((n - 1 : ℕ) * N : ℚ) * ((ssize : ℚ) * (scsize : ℚ)) := by
    have h_e_eq : (e (x, y) : ℚ) = (edgeBoundary S : ℚ) := rfl
    have := hineq
    rw [← h_e_eq, ← h_b_eq]
    exact this
  -- |S| + |Sᶜ| = N
  have h_card_sum_nat : ssize + scsize = N := by
    change S.card + sC.card = numLinExt α
    have hsub : S ⊆ (Finset.univ : Finset (LinearExt α)) :=
      Finset.subset_univ _
    have hsdiff : ((Finset.univ : Finset (LinearExt α)) \ S).card =
        Fintype.card (LinearExt α) - S.card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ]
    change S.card + ((Finset.univ : Finset (LinearExt α)) \ S).card = numLinExt α
    rw [hsdiff]
    have hle : S.card ≤ Fintype.card (LinearExt α) := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_univ] at this
    unfold numLinExt
    omega
  -- Size-product ≤ N · min
  have h_size_prod_le_Q :
      ((ssize : ℚ) * (scsize : ℚ)) ≤
        (N : ℚ) * ((min ssize scsize : ℕ) : ℚ) := by
    have hfundamental : ssize * scsize ≤ N * min ssize scsize := by
      rcases le_total ssize scsize with h | h
      · rw [min_eq_left h]
        calc ssize * scsize = scsize * ssize := Nat.mul_comm _ _
          _ ≤ (ssize + scsize) * ssize :=
              Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
          _ = N * ssize := by rw [h_card_sum_nat]
      · rw [min_eq_right h]
        calc ssize * scsize ≤ (ssize + scsize) * scsize :=
              Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
          _ = N * scsize := by rw [h_card_sum_nat]
    calc (ssize : ℚ) * (scsize : ℚ) = ((ssize * scsize : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((N * min ssize scsize : ℕ) : ℚ) := by exact_mod_cast hfundamental
      _ = (N : ℚ) * ((min ssize scsize : ℕ) : ℚ) := by push_cast; ring
  -- Chain: edgeBoundary * γ(1-γ)N²n ≤ (n-1)N · ssize·scsize ≤ (n-1)N · N·min
  have hStep1 :
      (edgeBoundary S : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) ≤
        ((n - 1 : ℕ) * N : ℚ) * ((N : ℚ) * (min ssize scsize : ℕ)) := by
    have h_n1N_nonneg : (0 : ℚ) ≤ ((n - 1 : ℕ) * N : ℚ) := by
      have : (0 : ℕ) ≤ (n - 1) * N := Nat.zero_le _
      exact_mod_cast this
    exact le_trans hineq' (mul_le_mul_of_nonneg_left h_size_prod_le_Q h_n1N_nonneg)
  -- Divide by N²: e · γ(1-γ)n ≤ (n-1) · min
  have hN2_pos : (0 : ℚ) < (N : ℚ) ^ 2 := by positivity
  have hStep2 :
      (edgeBoundary S : ℚ) * (γ * (1 - γ) * (n : ℚ)) ≤
        ((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ) := by
    have h_lhs_eq :
        (edgeBoundary S : ℚ) * (γ * (1 - γ) * (N : ℚ) ^ 2 * (n : ℚ)) =
          ((edgeBoundary S : ℚ) * (γ * (1 - γ) * (n : ℚ))) * (N : ℚ) ^ 2 := by
      ring
    have h_rhs_eq :
        ((n - 1 : ℕ) * N : ℚ) * ((N : ℚ) * (min ssize scsize : ℕ)) =
          (((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ)) * (N : ℚ) ^ 2 := by
      push_cast; ring
    rw [h_lhs_eq, h_rhs_eq] at hStep1
    exact le_of_mul_le_mul_right hStep1 hN2_pos
  -- Use γ(1-γ) ≥ γ/2
  have h_edge_nonneg : (0 : ℚ) ≤ (edgeBoundary S : ℚ) := by exact_mod_cast Nat.zero_le _
  have hStep3 :
      (edgeBoundary S : ℚ) * (γ * (n : ℚ)) / 2 ≤
        ((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ) := by
    have h_edge_γn_nonneg : 0 ≤ (edgeBoundary S : ℚ) * γ * (n : ℚ) := by
      have := h_edge_nonneg
      have : 0 ≤ (edgeBoundary S : ℚ) * γ :=
        mul_nonneg h_edge_nonneg (le_of_lt hγ_pos)
      exact mul_nonneg this (le_of_lt hn_posQ)
    have h_mul :
        (edgeBoundary S : ℚ) * (γ * ((1 : ℚ) / 2) * (n : ℚ)) ≤
          (edgeBoundary S : ℚ) * (γ * (1 - γ) * (n : ℚ)) := by
      have h_rearr1 : (edgeBoundary S : ℚ) * (γ * ((1 : ℚ) / 2) * (n : ℚ)) =
          (edgeBoundary S : ℚ) * γ * (n : ℚ) * ((1 : ℚ) / 2) := by ring
      have h_rearr2 : (edgeBoundary S : ℚ) * (γ * (1 - γ) * (n : ℚ)) =
          (edgeBoundary S : ℚ) * γ * (n : ℚ) * (1 - γ) := by ring
      rw [h_rearr1, h_rearr2]
      exact mul_le_mul_of_nonneg_left h1mγ_ge_half h_edge_γn_nonneg
    calc (edgeBoundary S : ℚ) * (γ * (n : ℚ)) / 2
        = (edgeBoundary S : ℚ) * (γ * ((1 : ℚ) / 2) * (n : ℚ)) := by ring
      _ ≤ (edgeBoundary S : ℚ) * (γ * (1 - γ) * (n : ℚ)) := h_mul
      _ ≤ ((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ) := hStep2
  -- Rearrange to: edgeBoundary * γn ≤ 2(n-1) min
  have hStep4 :
      (edgeBoundary S : ℚ) * γ * (n : ℚ) ≤
        2 * (((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ)) := by
    have := hStep3
    have : (edgeBoundary S : ℚ) * (γ * (n : ℚ)) ≤
        2 * (((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ)) := by
      have h2_pos : (0 : ℚ) < 2 := by norm_num
      linarith
    linarith
  -- Now translate min(ssize, scsize) to min(volume S, volume sC) / (n-1)
  have h_min_vol_eq_nat :
      min (volume S) (volume sC) = (n - 1) * min ssize scsize := by
    have hvS : volume S = ssize * (n - 1) := rfl
    have hvSc : volume sC = scsize * (n - 1) := rfl
    rw [hvS, hvSc]
    rcases le_total ssize scsize with hle | hle
    · have h1 : ssize * (n - 1) ≤ scsize * (n - 1) :=
        Nat.mul_le_mul_right _ hle
      rw [min_eq_left h1, min_eq_left hle, Nat.mul_comm]
    · have h1 : scsize * (n - 1) ≤ ssize * (n - 1) :=
        Nat.mul_le_mul_right _ hle
      rw [min_eq_right h1, min_eq_right hle, Nat.mul_comm]
  -- In ℚ, min commutes with the ℕ → ℚ cast
  have h_min_vol_eq :
      min ((volume S : ℕ) : ℚ) ((volume sC : ℕ) : ℚ) =
        ((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ) := by
    have hcast_min :
        (((min (volume S) (volume sC)) : ℕ) : ℚ) =
          min ((volume S : ℕ) : ℚ) ((volume sC : ℕ) : ℚ) := by
      push_cast; rfl
    rw [← hcast_min, h_min_vol_eq_nat]
    push_cast; ring
  -- Conclude Phi ≤ 2/(γn)
  -- Need min(vol S, vol Sᶜ) > 0 for division.
  -- ssize ≥ γ N > 0, scsize ≥ γ N > 0, so min(ssize, scsize) > 0.
  have hssize_pos : 0 < ssize := by
    have hγN_lt : γ * (N : ℚ) ≤ (ssize : ℚ) := by
      have := hγxy
      rw [probLT_eq_card_pairCut_div] at this
      have := (le_div_iff₀ hN_posQ).mp this
      show γ * (N : ℚ) ≤ ((pairCut x y).card : ℚ); exact this
    have hγN_pos : 0 < γ * (N : ℚ) := mul_pos hγ_pos hN_posQ
    have : (0 : ℚ) < (ssize : ℚ) := lt_of_lt_of_le hγN_pos hγN_lt
    exact_mod_cast this
  have hscsize_pos : 0 < scsize := by
    have hγN_lt : γ * (N : ℚ) ≤ (scsize : ℚ) := by
      have := hγyx
      rw [probLT_eq_card_pairCut_div] at this
      have hdiv := (le_div_iff₀ hN_posQ).mp this
      rw [hscsize_eq]
      show γ * (N : ℚ) ≤ ((pairCut y x).card : ℚ); exact hdiv
    have hγN_pos : 0 < γ * (N : ℚ) := mul_pos hγ_pos hN_posQ
    have : (0 : ℚ) < (scsize : ℚ) := lt_of_lt_of_le hγN_pos hγN_lt
    exact_mod_cast this
  have hmin_pos : 0 < min ssize scsize := by
    rcases le_total ssize scsize with h | h
    · rw [min_eq_left h]; exact hssize_pos
    · rw [min_eq_right h]; exact hscsize_pos
  have hmin_posQ : (0 : ℚ) < ((min ssize scsize : ℕ) : ℚ) := by
    exact_mod_cast hmin_pos
  have hminvol_posℚ : (0 : ℚ) <
      min ((volume S : ℕ) : ℚ) ((volume sC : ℕ) : ℚ) := by
    rw [h_min_vol_eq]
    exact mul_pos hn_minus_one_posQ hmin_posQ
  -- Goal: Phi (pairCut x y) ≤ 2 / (γ * n)
  unfold Phi
  -- pairCut x y = S, volume (univ \ S) = volume sC by definition
  change (edgeBoundary S : ℚ) /
      min ((volume S : ℕ) : ℚ) ((volume sC : ℕ) : ℚ) ≤ 2 / (γ * (n : ℚ))
  have hγn_pos : (0 : ℚ) < γ * (n : ℚ) := mul_pos hγ_pos hn_posQ
  rw [div_le_div_iff₀ hminvol_posℚ hγn_pos]
  rw [h_min_vol_eq]
  -- We have hStep4: edgeBoundary S * γ * n ≤ 2 · (n-1) · min
  have : (edgeBoundary S : ℚ) * (γ * (n : ℚ)) ≤
      2 * (((n - 1 : ℕ) : ℚ) * ((min ssize scsize : ℕ) : ℚ)) := by
    have := hStep4; linarith
  linarith

end OneThird.Step8
