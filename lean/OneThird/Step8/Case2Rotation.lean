/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.Case2FKG
import OneThird.Step8.Case3Dispatch
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Case 2 FKG `m = 3` rotation argument
(`mg-A8` sub-split A8-S2-rotation, `mg-5a62`)

This file lifts the **rotation argument** of
`prop:bipartite-balanced` Case 2 (`step8.tex:2877-2914`) — the `m = 3`
sub-case combining three pairwise FKG monotonicity inequalities to
extract a triple in `[1/3, 2/3]` — to a self-contained probability
lemma on three within-band incomparable elements.

## Summary

The paper's `m = 3` rotation argument has two distinct ingredients:

1. **The rotation inequality** (`step8.tex:2904-2914`,
   parenthetical "the three rotations cover every total order"):
   for any three distinct elements `a₁, a₂, a₃` of a finite poset and
   any uniform-LE distribution, the three rotation events
   `{a₂ <_L a₁}`, `{a₃ <_L a₂}`, `{a₁ <_L a₃}` cover every linear
   extension — at least one holds in every LE because their negations
   would form the cycle `a₁ <_L a₂ <_L a₃ <_L a₁` (impossible in a
   total order). Hence
   `Pr[a₂<a₁] + Pr[a₃<a₂] + Pr[a₁<a₃] ≥ 1`.

   This is a pure rational-arithmetic fact about three distinct
   elements; it requires no FKG input. Recorded here as
   `rotation_sum_ge_one` and its symmetric variant
   `rotation_sum_ge_one'`.

2. **The case analysis on the three pair-probabilities**
   (`step8.tex:2878-2900`): given three FKG sub-claim hypotheses
   `Pr[a_i <_L a_{i+1}] ≥ 1/2` for the three `⪯`-comparable
   within-`A` pairs (where `i` ranges over `{(1,2), (2,3), (1,3)}`),
   the dispatch is:

   * If `Pr[a_i <_L a_{i+1}] ≤ 2/3` for any of the three pairs, the
     corresponding pair is **balanced** in `[1/2, 2/3] ⊆ [1/3, 2/3]`,
     yielding `HasBalancedPair α` directly.
   * Otherwise all three pairs satisfy `Pr > 2/3`. The paper claims
     this case yields a contradiction by combining the rotation
     inequality with an inclusion-exclusion bound; see §4 below for
     the **honest gap analysis** of why the paper's contradiction
     does not literally close, and what additional structural input
     is needed to discharge this residual.

   Recorded here as `m3_rotation_balanced_or_residual`: the case
   analysis returns either `HasBalancedPair α` (the easy three
   sub-cases) or the residual `Pr > 2/3` triple-inequality (the hard
   case for follow-up work).

## Strengthened witness predicate

The existing `Step8.InSitu.StrictCase2Witness L`
(`Case2FKG.lean:217`) carries a **single** within-band `⪯`-comparable
pair, the input shape of the paper's `m = 2` argument
(`step8.tex:2858-2875`). The `m = 3` rotation argument needs three
within-band elements forming a `⪯`-chain. This file introduces:

* **`Step8.InSitu.StrictCase2WitnessChain L`** — the strengthened
  witness: three pairwise distinct within-band elements `a₁, a₂, a₃`
  forming a `⪯`-chain, i.e., the one-sided ambient profile inclusions
  `(∀ z, a_i < z → a_{i+1} < z) ∧ (∀ z, z < a_{i+1} → z < a_i)` hold
  for `i = 1, 2`. The `(1, 3)` direction follows by transitivity and
  is recorded as `StrictCase2WitnessChain.chain_one_three`.

The chain witness is the input shape of the rotation argument's
`m = 3` discharge; extraction from the layered hypothesis profile
(width 3, irreducibility, `¬ InCase3Scope`) at the call site of
`case1_dispatch_balanced_or_witness` is **not** in scope for this
sub-split (recorded as a follow-up in §5).

## What is **not** in this file

The full `StrictCase2WitnessChain L → HasBalancedPair α` discharge is
**not** completed here, for two distinct reasons:

* **The three FKG sub-claims `Pr[a_i <_L a_{i+1}] ≥ 1/2`** —
  derived in the paper from the Ahlswede-Daykin / FKG cross-poset
  coupling argument (`step8.tex:2858-2875`). This relies on the
  *probability-normalised* form of the FKG monotonicity-under-
  augmentation inequality, which is acknowledged as **future work**
  in `OneThird.Mathlib.RelationPoset.FKG` (`§11`, lines 405-426):
  the current cross-poset infrastructure
  (`probLT'_mono_of_relExt`) is the **count-normalised** form,
  which does not directly entail the probability-normalised form
  without an additional positive-correlation step.

* **The `Pr > 2/3` residual case** — the paper's argument
  (`step8.tex:2900-2914`) attempts to derive a contradiction from
  "summing the three complements `< 1` but the rotation sum `≥ 1`".
  As written, this argument has a transcription error: the three
  *complements* are the events `{a₂<a₁, a₃<a₂, a₃<a₁}`, whose
  negations form the *consistent* total order `a₁<a₂<a₃` (not a
  cycle), so they are **not** a rotation cover and need not sum to
  `≥ 1`. The genuine rotations are
  `{a₂<a₁, a₃<a₂, a₁<a₃}` (third event is the **forward** `a₁<a₃`,
  not the complement) — these do cover every LE (their negations
  form the cycle `a₁<a₂<a₃<a₁`), but their sum under the
  "all > 2/3" hypothesis is `< 1/3 + 1/3 + 1 = 5/3`, consistent with
  `≥ 1`, so no contradiction follows. Closing this case requires
  additional structural input from the layered hypothesis profile
  (width 3, irreducibility); see §4 for the gap analysis.

`#print axioms` on the new theorems reports only the mathlib trio
`[propext, Classical.choice, Quot.sound]` — no new axioms, no
sorries.

## References

* `step8.tex` `prop:bipartite-balanced` Case 2, `m = 3` rotation
  argument (`2877-2914`).
* `step8.tex` `prop:in-situ-balanced` Case 2 (`3001-3032`); the
  `prop:in-situ-balanced` Case 2 is the `K ≥ 2` lift of
  `prop:bipartite-balanced` Case 2 to which the rotation applies.
* `lean/OneThird/Step8/Case2FKG.lean` — A8-S2 partial deliverable
  with `StrictCase2Witness` (the `m = 2` shape, mg-8801).
* `lean/OneThird/Step8/Case2BipartiteBound.lean` — A8-S2-bipartite-bound,
  the `Pr ≤ 2/3` upper bound for K=2, w=0 (mg-ed4d).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean` — A8-S2-cont-3, the
  cross-poset FKG monotonicity headline (mg-0b81); §11 doc-comment
  records the probability-normalised follow-up.
* `docs/a8-s2-status.md` — A8-S2 status report.
-/

namespace OneThird
namespace Step8
namespace InSitu

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### §1 — `StrictCase2WitnessChain L`: three within-band `⪯`-chain elements

Strengthening of `StrictCase2Witness L` (`Case2FKG.lean:217`) from a
single `⪯`-comparable pair to a three-element `⪯`-chain. The
chain hypothesis is the input shape of the paper's `m = 3` rotation
argument (`step8.tex:2877-2914`). -/

/-- **Strict Case 2 witness with `m = 3` chain.** Three pairwise
distinct within-band elements `a₁, a₂, a₃` forming a `⪯`-chain in
the two-sided profile order `Π`:

* `a₁ ⪯ a₂` — `(∀ z, a₁ < z → a₂ < z) ∧ (∀ z, z < a₂ → z < a₁)`;
* `a₂ ⪯ a₃` — `(∀ z, a₂ < z → a₃ < z) ∧ (∀ z, z < a₃ → z < a₂)`.

The `a₁ ⪯ a₃` direction follows by transitivity (see
`StrictCase2WitnessChain.chain_one_three`); the within-band
incomparabilities follow from `band_antichain` (see
`StrictCase2WitnessChain.incomp_pairs`).

This is the shape of the paper's `m = 3` rotation argument
(`step8.tex:2877-2914`). The single-pair `StrictCase2Witness` of
`Case2FKG.lean` corresponds to the `m = 2` case
(`step8.tex:2858-2875`). -/
def StrictCase2WitnessChain (L : LayeredDecomposition α) : Prop :=
  ∃ a₁ a₂ a₃ : α,
    a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₁ ≠ a₃ ∧
    L.band a₁ = L.band a₂ ∧ L.band a₁ = L.band a₃ ∧
    (∀ z, a₁ < z → a₂ < z) ∧ (∀ z, z < a₂ → z < a₁) ∧
    (∀ z, a₂ < z → a₃ < z) ∧ (∀ z, z < a₃ → z < a₂)

namespace StrictCase2WitnessChain

/-- Transitivity of the chain: `a₁ ⪯ a₂` and `a₂ ⪯ a₃` give
`a₁ ⪯ a₃`. Pure logical chaining of the four implications. -/
lemma chain_one_three
    {a₁ a₂ a₃ : α}
    (h12_up : ∀ z, a₁ < z → a₂ < z) (h12_down : ∀ z, z < a₂ → z < a₁)
    (h23_up : ∀ z, a₂ < z → a₃ < z) (h23_down : ∀ z, z < a₃ → z < a₂) :
    (∀ z, a₁ < z → a₃ < z) ∧ (∀ z, z < a₃ → z < a₁) := by
  refine ⟨fun z hz => h23_up z (h12_up z hz), fun z hz => h12_down z (h23_down z hz)⟩

/-- The three within-band elements of a `StrictCase2WitnessChain`
are pairwise incomparable, by `band_antichain`. -/
lemma incomp_pairs (L : LayeredDecomposition α)
    (h : StrictCase2WitnessChain L) :
    ∃ a₁ a₂ a₃ : α,
      a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₁ ≠ a₃ ∧
      L.band a₁ = L.band a₂ ∧ L.band a₁ = L.band a₃ ∧
      a₁ ∥ a₂ ∧ a₂ ∥ a₃ ∧ a₁ ∥ a₃ ∧
      (∀ z, a₁ < z → a₂ < z) ∧ (∀ z, z < a₂ → z < a₁) ∧
      (∀ z, a₂ < z → a₃ < z) ∧ (∀ z, z < a₃ → z < a₂) ∧
      (∀ z, a₁ < z → a₃ < z) ∧ (∀ z, z < a₃ → z < a₁) := by
  obtain ⟨a₁, a₂, a₃, h12, h23, h13, hb12, hb13, hu12, hd12, hu23, hd23⟩ := h
  have hb23 : L.band a₂ = L.band a₃ := hb12.symm.trans hb13
  have hi12 : a₁ ∥ a₂ := incomp_of_within_band L h12 hb12
  have hi23 : a₂ ∥ a₃ := incomp_of_within_band L h23 hb23
  have hi13 : a₁ ∥ a₃ := incomp_of_within_band L h13 hb13
  obtain ⟨hu13, hd13⟩ := chain_one_three hu12 hd12 hu23 hd23
  exact ⟨a₁, a₂, a₃, h12, h23, h13, hb12, hb13, hi12, hi23, hi13,
    hu12, hd12, hu23, hd23, hu13, hd13⟩

end StrictCase2WitnessChain

/-! ### §2 — Rotation inequality on `LinearExt α`

For any three distinct elements `a₁, a₂, a₃ : α`, the three
rotation events `{L : a₂ <_L a₁}`, `{L : a₃ <_L a₂}`,
`{L : a₁ <_L a₃}` cover every linear extension `L : LinearExt α`:
their simultaneous negations would force the cycle `a₁ <_L a₂ <_L
a₃ <_L a₁`, impossible in a total order.

Hence `Pr[a₂<a₁] + Pr[a₃<a₂] + Pr[a₁<a₃] ≥ 1`. -/

set_option linter.unusedVariables false in
/-- **Rotation cover** (`step8.tex:2909-2914`). For any three
pairwise distinct elements `a₁, a₂, a₃ : α` and any linear extension
`L : LinearExt α`, at least one of the three rotation events
`a₂ <_L a₁`, `a₃ <_L a₂`, `a₁ <_L a₃` holds.

The negation (all three fail) forces `a₁ <_L a₂ <_L a₃ <_L a₁`,
impossible since `<_L` is a strict total order on `LinearExt α`.
(Distinctness of `a₂, a₃` and `a₁, a₃` is propagated through the
signature for downstream callers; the proof itself only needs
`a₁ ≠ a₂` to extract the contradiction `pos a₁ = pos a₂`.) -/
lemma rotation_cover {a₁ a₂ a₃ : α}
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃)
    (L : LinearExt α) :
    L.lt a₂ a₁ ∨ L.lt a₃ a₂ ∨ L.lt a₁ a₃ := by
  classical
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨h_a₂a₁, h_a₃a₂, h_a₁a₃⟩ := hcontra
  -- ¬ (a₂ <_L a₁), ¬ (a₃ <_L a₂), ¬ (a₁ <_L a₃)
  -- Strict total order on positions: ¬ (q < p) ↔ p ≤ q.
  -- So pos a₁ ≤ pos a₂, pos a₂ ≤ pos a₃, pos a₃ ≤ pos a₁.
  -- This forces pos a₁ = pos a₂ = pos a₃, contradicting injectivity.
  have h1 : L.pos a₁ ≤ L.pos a₂ := not_lt.mp h_a₂a₁
  have h2 : L.pos a₂ ≤ L.pos a₃ := not_lt.mp h_a₃a₂
  have h3 : L.pos a₃ ≤ L.pos a₁ := not_lt.mp h_a₁a₃
  have h_eq12 : L.pos a₁ = L.pos a₂ := le_antisymm h1 (h2.trans h3)
  exact h12 (L.pos_injective h_eq12)

/-- **Rotation sum lower bound** (`step8.tex:2904-2914`). For any
three pairwise distinct elements `a₁, a₂, a₃ : α`,
`probLT a₂ a₁ + probLT a₃ a₂ + probLT a₁ a₃ ≥ 1`.

This is the inclusion-exclusion bound on the union
`{a₂<_L a₁} ∪ {a₃<_L a₂} ∪ {a₁<_L a₃}`, which by `rotation_cover`
is the entire `Finset.univ : Finset (LinearExt α)`. -/
theorem rotation_sum_ge_one {a₁ a₂ a₃ : α}
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃) :
    probLT a₂ a₁ + probLT a₃ a₂ + probLT a₁ a₃ ≥ 1 := by
  classical
  -- Strategy: for each L, the indicator sum
  -- 1[a₂<a₁] + 1[a₃<a₂] + 1[a₁<a₃] ≥ 1 by `rotation_cover`. Summing:
  --   |F₁| + |F₂| + |F₃| ≥ |Finset.univ| = numLinExt α.
  -- Then dividing by numLinExt α gives the probability bound.
  set F₁ : Finset (LinearExt α) :=
    Finset.univ.filter (fun L : LinearExt α => L.lt a₂ a₁) with hF₁
  set F₂ : Finset (LinearExt α) :=
    Finset.univ.filter (fun L : LinearExt α => L.lt a₃ a₂) with hF₂
  set F₃ : Finset (LinearExt α) :=
    Finset.univ.filter (fun L : LinearExt α => L.lt a₁ a₃) with hF₃
  have hcover : (F₁ ∪ F₂ ∪ F₃) = (Finset.univ : Finset (LinearExt α)) := by
    apply Finset.eq_univ_of_forall
    intro L
    rcases rotation_cover h12 h23 h13 L with h | h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  -- |F₁| + |F₂| + |F₃| ≥ |F₁ ∪ F₂ ∪ F₃| = |Finset.univ| = numLinExt α.
  have hle_union : (F₁ ∪ F₂ ∪ F₃).card ≤ F₁.card + F₂.card + F₃.card := by
    calc (F₁ ∪ F₂ ∪ F₃).card
        ≤ (F₁ ∪ F₂).card + F₃.card := Finset.card_union_le _ _
      _ ≤ (F₁.card + F₂.card) + F₃.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = F₁.card + F₂.card + F₃.card := by ring
  have hcard_univ_le :
      (numLinExt α : ℕ) ≤ F₁.card + F₂.card + F₃.card := by
    rw [show (numLinExt α : ℕ) = (Finset.univ : Finset (LinearExt α)).card from
        Finset.card_univ.symm]
    rw [← hcover]; exact hle_union
  -- Convert to ℚ inequality.
  have hpos : (0 : ℚ) < numLinExt α := by exact_mod_cast numLinExt_pos
  have hcast : ((numLinExt α : ℕ) : ℚ) ≤ ((F₁.card + F₂.card + F₃.card : ℕ) : ℚ) := by
    exact_mod_cast hcard_univ_le
  push_cast at hcast
  have hsum_eq :
      probLT a₂ a₁ + probLT a₃ a₂ + probLT a₁ a₃ =
        ((F₁.card : ℚ) + (F₂.card : ℚ) + (F₃.card : ℚ)) / (numLinExt α : ℚ) := by
    unfold probLT
    rw [hF₁, hF₂, hF₃]
    field_simp
  rw [hsum_eq, ge_iff_le, le_div_iff₀ hpos, one_mul]
  linarith

/-- **Symmetric rotation sum** — the other rotation cover
`{a₁<a₂, a₂<a₃, a₃<a₁}` (negations form the cycle
`a₂<a₁, a₃<a₂, a₁<a₃`) gives the analogous lower bound on the
forward chain. -/
theorem rotation_sum_ge_one' {a₁ a₂ a₃ : α}
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃) :
    probLT a₁ a₂ + probLT a₂ a₃ + probLT a₃ a₁ ≥ 1 := by
  -- Apply `rotation_sum_ge_one` with the relabelling (b₁,b₂,b₃) :=
  -- (a₁, a₃, a₂): then `probLT b₂ b₁ = probLT a₃ a₁`,
  -- `probLT b₃ b₂ = probLT a₂ a₃`, `probLT b₁ b₃ = probLT a₁ a₂`,
  -- exactly the symmetric rotation.
  have h := rotation_sum_ge_one (a₁ := a₁) (a₂ := a₃) (a₃ := a₂)
    h13 (Ne.symm h23) h12
  linarith

/-! ### §3 — Main rotation theorem: case analysis with residual

Given three FKG sub-claim hypotheses
`Pr[a_i <_L a_{i+1}] ≥ 1/2` (for `i = 1, 2, 3` in the natural pairing,
where `(1, 3)` is the long pair across the chain), the rotation
argument either yields `HasBalancedPair α` directly (when one of the
three pair probabilities is `≤ 2/3`, so it lies in `[1/2, 2/3] ⊆
[1/3, 2/3]`) or returns the residual `Pr > 2/3` triple-inequality
for downstream discharge.

The residual case is where the paper's `step8.tex:2900-2914` argument
attempts to derive a contradiction; see the file-level §4 doc for the
gap analysis. -/

set_option linter.unusedVariables false in
/-- **Main rotation argument: dispatch on the three pair-probabilities.**

Given three pairwise distinct, pairwise incomparable elements
`a₁, a₂, a₃ : α` and three FKG sub-claim hypotheses
`1/2 ≤ probLT a_i a_{i+1}` (for the pairs `(a₁,a₂)`, `(a₂,a₃)`,
`(a₁,a₃)`), one of the following two outcomes holds:

* `HasBalancedPair α` — extracted from one of the three pairs whose
  forward probability lies in `[1/2, 2/3] ⊆ [1/3, 2/3]`; this is
  the easy three sub-cases of `step8.tex:2877-2900`.
* **Residual:** all three pair probabilities exceed `2/3`. This is
  the hard case where the paper's `step8.tex:2900-2914` argument
  applies; see §4 for the gap analysis.

This dispatch is **pure rational arithmetic** — it does not use the
chain hypothesis or the within-band structure beyond the
incomparability inputs. The chain / within-band data is needed only
for the (deferred) discharge of the residual case.

Distinctness hypotheses `h12, h23, h13` are derivable from the
incomparability hypotheses (`a ∥ b → a ≠ b` via `Incomp.irrefl`)
but are taken explicitly here to match the natural call-site
signature where both are available from `StrictCase2WitnessChain`. -/
theorem m3_rotation_balanced_or_residual
    (a₁ a₂ a₃ : α)
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃)
    (hi12 : a₁ ∥ a₂) (hi23 : a₂ ∥ a₃) (hi13 : a₁ ∥ a₃)
    (hp12 : (1 : ℚ) / 2 ≤ probLT a₁ a₂)
    (hp23 : (1 : ℚ) / 2 ≤ probLT a₂ a₃)
    (hp13 : (1 : ℚ) / 2 ≤ probLT a₁ a₃) :
    HasBalancedPair α ∨
      ((2 : ℚ) / 3 < probLT a₁ a₂ ∧
        (2 : ℚ) / 3 < probLT a₂ a₃ ∧
        (2 : ℚ) / 3 < probLT a₁ a₃) := by
  classical
  by_cases hp13_le : probLT a₁ a₃ ≤ 2 / 3
  · -- (a₁, a₃) is balanced.
    refine Or.inl ⟨a₁, a₃, hi13, ?_, hp13_le⟩
    linarith
  push_neg at hp13_le
  by_cases hp12_le : probLT a₁ a₂ ≤ 2 / 3
  · -- (a₁, a₂) is balanced.
    refine Or.inl ⟨a₁, a₂, hi12, ?_, hp12_le⟩
    linarith
  push_neg at hp12_le
  by_cases hp23_le : probLT a₂ a₃ ≤ 2 / 3
  · -- (a₂, a₃) is balanced.
    refine Or.inl ⟨a₂, a₃, hi23, ?_, hp23_le⟩
    linarith
  push_neg at hp23_le
  -- Residual: all three exceed 2/3.
  exact Or.inr ⟨hp12_le, hp23_le, hp13_le⟩

/-! ### §4 — Honest gap analysis: the `Pr > 2/3` residual case

The paper's argument (`step8.tex:2900-2914`) attempts to derive a
contradiction from the residual "all three forward probabilities
> 2/3" case via the "rotation inequality" + complement bound. As
written, the argument has a transcription error that prevents a
contradiction from following. We document the issue here for
downstream work.

**Paper's claim.** Under hypothesis `p := Pr[a₁<a₂] > 2/3`,
`q := Pr[a₂<a₃] > 2/3`, `r := Pr[a₁<a₃] > 2/3`:

> "summing the three complements `Pr[a₂<a₁] + Pr[a₃<a₂] + Pr[a₃<a₁] < 1`,
> while any three random variables taking values in `{<, >}` satisfy
> `Pr[π₁] + Pr[π₂] + Pr[π₃] ≥ 1` for the three 'rotations' (since
> the events cover at least one of the six orderings of the triple)"

**Issue.** The "three complements" are `{a₂<a₁, a₃<a₂, a₃<a₁}`,
whose simultaneous negations `{a₁<a₂, a₂<a₃, a₁<a₃}` form the
**consistent** total order `a₁<a₂<a₃`. So all three complements
**can** simultaneously fail (in the LE `a₁<a₂<a₃`), and they need
not sum to `≥ 1`. The genuine "rotation" cover with `≥ 1` lower
bound is `{a₂<a₁, a₃<a₂, a₁<a₃}` (third event is the **forward**
`a₁<a₃`, not the complement `a₃<a₁`) — these do cover every LE
because their negations form the cycle `a₁<a₂<a₃<a₁`. But under
the "all > 2/3" hypothesis,
`Pr[a₂<a₁] + Pr[a₃<a₂] + Pr[a₁<a₃] = (1-p) + (1-q) + r
< 1/3 + 1/3 + 1 = 5/3`, consistent with `≥ 1`.

**Lower bound proven.** `rotation_sum_ge_one` and
`rotation_sum_ge_one'` give the two genuine rotation inequalities
on `LinearExt α`. The corollary
`rotation_residual_lower_bound` below records the bound the
residual hypothesis must satisfy.

**What is needed to close the residual case.** The paper's argument
implicitly assumes additional structural input beyond the FKG
sub-claims — namely, that the within-band antichain `A := {a₁, a₂,
a₃}` of width 3 in an irreducible layered poset cannot
simultaneously achieve `Pr > 2/3` on all three of its `⪯`-adjacent
pairs. Two routes have been suggested for this:

* **Route A: structural impossibility.** Use the layered hypothesis
  profile (width 3, irreducibility, `¬ InCase3Scope`) to show
  directly that "all three > 2/3" forces a comparability in `Q`
  among `{a₁, a₂, a₃}`, contradicting the within-band antichain
  hypothesis.

* **Route B: tighter probability bounds from FKG monotonicity.**
  The cross-poset coupling
  (`OneThird.Mathlib.RelationPoset.FKG.probLT'_mono_of_relExt`) in
  its **probability-normalised** form (currently future work, see
  `Mathlib/RelationPoset/FKG.lean:407-426`) would give upper
  bounds on `Pr[a_i<a_{i+1}]` from the chain structure, making
  "all > 2/3" infeasible.

Either route would close the residual case and complete the m=3
discharge `StrictCase2WitnessChain L → HasBalancedPair α`. -/

set_option linter.unusedVariables false in
/-- **Residual lower bound from the rotation inequality.** Under the
"all forward `Pr > 2/3`" residual hypothesis, the rotation sum
`Pr[a₂<a₁] + Pr[a₃<a₂] + Pr[a₁<a₃]` is strictly bounded **below by
`2/3`** (from the forward hypothesis on the third term alone) and
**below by 1** (from the rotation inequality). The two bounds
together are consistent (`5/3 > 1`), explaining why the rotation
inequality alone does not contradict the residual hypothesis.

The forward hypotheses `hp12`, `hp23` are propagated through the
signature to make the residual shape explicit at the call site,
even though only `hp13` is needed for the strict bound `> 2/3`. -/
lemma rotation_residual_lower_bound
    {a₁ a₂ a₃ : α}
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃)
    (hp12 : (2 : ℚ) / 3 < probLT a₁ a₂)
    (hp23 : (2 : ℚ) / 3 < probLT a₂ a₃)
    (hp13 : (2 : ℚ) / 3 < probLT a₁ a₃) :
    (2 : ℚ) / 3 < probLT a₂ a₁ + probLT a₃ a₂ + probLT a₁ a₃ ∧
    probLT a₂ a₁ + probLT a₃ a₂ + probLT a₁ a₃ ≥ 1 := by
  refine ⟨?_, rotation_sum_ge_one h12 h23 h13⟩
  have h_nonneg₁ : (0 : ℚ) ≤ probLT a₂ a₁ := probLT_nonneg _ _
  have h_nonneg₂ : (0 : ℚ) ≤ probLT a₃ a₂ := probLT_nonneg _ _
  linarith

/-! ### §5 — Composition with `StrictCase2WitnessChain`

Composes `m3_rotation_balanced_or_residual` with the chain witness
`StrictCase2WitnessChain L`: the chain provides the three pairwise
distinct, within-band incomparable elements; the FKG sub-claim
hypotheses on the three pair-probabilities are taken as separate
inputs (deferred to the cross-poset coupling infrastructure). -/

/-- **Chain witness composed with the rotation argument.** Given a
`StrictCase2WitnessChain L` (three within-band `⪯`-chain elements)
and the three FKG sub-claim hypotheses on the corresponding
pair-probabilities, the rotation argument either yields
`HasBalancedPair α` or returns the residual "all three pair
probabilities > 2/3" — packaged with the chain structure preserved
for downstream structural discharge. -/
theorem strictCase2WitnessChain_balanced_or_residual
    (L : LayeredDecomposition α) (hC2chain : StrictCase2WitnessChain L)
    (hFKG : ∀ a₁ a₂ a₃ : α,
      a₁ ≠ a₂ → a₂ ≠ a₃ → a₁ ≠ a₃ →
      L.band a₁ = L.band a₂ → L.band a₁ = L.band a₃ →
      a₁ ∥ a₂ → a₂ ∥ a₃ → a₁ ∥ a₃ →
      (∀ z, a₁ < z → a₂ < z) → (∀ z, z < a₂ → z < a₁) →
      (∀ z, a₂ < z → a₃ < z) → (∀ z, z < a₃ → z < a₂) →
      (1 : ℚ) / 2 ≤ probLT a₁ a₂ ∧
      (1 : ℚ) / 2 ≤ probLT a₂ a₃ ∧
      (1 : ℚ) / 2 ≤ probLT a₁ a₃) :
    HasBalancedPair α ∨
      ∃ a₁ a₂ a₃ : α,
        a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₁ ≠ a₃ ∧
        L.band a₁ = L.band a₂ ∧ L.band a₁ = L.band a₃ ∧
        a₁ ∥ a₂ ∧ a₂ ∥ a₃ ∧ a₁ ∥ a₃ ∧
        (∀ z, a₁ < z → a₂ < z) ∧ (∀ z, z < a₂ → z < a₁) ∧
        (∀ z, a₂ < z → a₃ < z) ∧ (∀ z, z < a₃ → z < a₂) ∧
        (2 : ℚ) / 3 < probLT a₁ a₂ ∧
        (2 : ℚ) / 3 < probLT a₂ a₃ ∧
        (2 : ℚ) / 3 < probLT a₁ a₃ := by
  obtain ⟨a₁, a₂, a₃, h12, h23, h13, hb12, hb13, hi12, hi23, hi13,
    hu12, hd12, hu23, hd23, _hu13, _hd13⟩ :=
    StrictCase2WitnessChain.incomp_pairs L hC2chain
  obtain ⟨hp12, hp23, hp13⟩ :=
    hFKG a₁ a₂ a₃ h12 h23 h13 hb12 hb13 hi12 hi23 hi13 hu12 hd12 hu23 hd23
  rcases m3_rotation_balanced_or_residual a₁ a₂ a₃ h12 h23 h13
      hi12 hi23 hi13 hp12 hp23 hp13 with hbal | ⟨hr12, hr23, hr13⟩
  · exact Or.inl hbal
  · refine Or.inr ⟨a₁, a₂, a₃, h12, h23, h13, hb12, hb13,
      hi12, hi23, hi13, hu12, hd12, hu23, hd23, hr12, hr23, hr13⟩

end InSitu
end Step8
end OneThird
