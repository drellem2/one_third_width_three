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

/-! ### §6 — Chain swap: forward chain probability bound

This section provides a direct combinatorial closure of the **forward
direction** of the residual case from `m3_rotation_balanced_or_residual`:
under the chain hypothesis, every forward chain probability satisfies
`probLT a a' ≤ 1/2`, which strictly contradicts the `> 2/3` residual.

The construction.  Given a one-sided ⪯-chain `(a, a')` —
`upper(a) ⊆ upper(a')` and `lower(a') ⊆ lower(a)` — and a linear
extension `L` with `L.lt a a'`, exchange the positions of `a` and
`a'` in `L` to obtain a new linear extension with `a' <_L a`.
Monotonicity of the swapped extension follows from the chain
inclusions and the `L.lt a a'` hypothesis (case-by-case on whether
`x, y ∈ {a, a'}`); see `chainSwap_LE` below.

Compared to the Case 1 ambient form
(`Step8.hasBalancedPair_of_ambient_profile_match` in `Case3Struct.lean`,
mg-f92d), the chain swap requires only a *one-sided* profile inclusion,
not bi-implication.  The cost of the weaker hypothesis is that the
swap is no longer a poset automorphism of `α` (so cannot be packaged
via `LinearExt.pullback`), and is only valid as a swap on positions
for LEs in which `a` precedes `a'`.

The bound `Pr ≤ 1/2` is in the **same direction** as the chain
inclusions.  The OPPOSITE direction (`Pr[a' <_L a] ≤ 2/3`) is **not**
provided by chain swap; see `docs/a8-s2-rotation-residual-status.md`
for the full gap analysis. -/

set_option linter.unusedVariables false in
/-- **Chain swap construction.**  Given a one-sided ⪯-chain `(a, a')`
with `a ≠ a'`, `a ∥ a'`, `upper(a) ⊆ upper(a')`,
`lower(a') ⊆ lower(a)`, and a linear extension `L` with `L.lt a a'`,
construct a new linear extension by exchanging the positions of `a`
and `a'` in `L`. The `hne` field is propagated through the signature
for downstream callers (chain witnesses carry `a ≠ a'` separately
from `a ∥ a'`); the proof itself only uses `hi`. -/
def chainSwap_LE
    {a a' : α} (hne : a ≠ a') (hi : a ∥ a')
    (h_up : ∀ z, a < z → a' < z) (h_down : ∀ z, z < a' → z < a)
    (L : LinearExt α) (h_lt : L.lt a a') : LinearExt α where
  toFun := (Equiv.swap a a').trans L.toFun
  monotone {x y} hxy := by
    classical
    have hpos : L.toFun a < L.toFun a' := h_lt
    change L.toFun ((Equiv.swap a a') x) ≤ L.toFun ((Equiv.swap a a') y)
    by_cases hxa : x = a
    · rw [hxa] at hxy ⊢
      rw [Equiv.swap_apply_left]
      by_cases hya : y = a
      · rw [hya, Equiv.swap_apply_left]
      by_cases hya' : y = a'
      · rw [hya'] at hxy
        exact absurd hxy hi.1
      · rw [Equiv.swap_apply_of_ne_of_ne hya hya']
        have hay : a < y := lt_of_le_of_ne hxy (Ne.symm hya)
        exact (L.lt_of_lt (h_up y hay)).le
    by_cases hxa' : x = a'
    · rw [hxa'] at hxy ⊢
      rw [Equiv.swap_apply_right]
      by_cases hya : y = a
      · rw [hya] at hxy
        exact absurd hxy hi.2
      by_cases hya' : y = a'
      · rw [hya', Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hya hya']
        have ha'y : a' < y := lt_of_le_of_ne hxy (Ne.symm hya')
        exact (hpos.trans (L.lt_of_lt ha'y)).le
    -- x ∉ {a, a'}.
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxa']
    by_cases hya : y = a
    · rw [hya] at hxy ⊢
      rw [Equiv.swap_apply_left]
      have hxa_lt : x < a := lt_of_le_of_ne hxy hxa
      exact ((L.lt_of_lt hxa_lt).trans hpos).le
    by_cases hya' : y = a'
    · rw [hya'] at hxy ⊢
      rw [Equiv.swap_apply_right]
      have hxa'_lt : x < a' := lt_of_le_of_ne hxy hxa'
      have hxa_lt : x < a := h_down x hxa'_lt
      exact (L.lt_of_lt hxa_lt).le
    · rw [Equiv.swap_apply_of_ne_of_ne hya hya']
      exact L.monotone hxy

/-- Position of any element under the chain swap is the position of its
`Equiv.swap a a'`-image under `L`. -/
@[simp] lemma chainSwap_LE_pos
    {a a' : α} (hne : a ≠ a') (hi : a ∥ a')
    (h_up : ∀ z, a < z → a' < z) (h_down : ∀ z, z < a' → z < a)
    (L : LinearExt α) (h_lt : L.lt a a') (z : α) :
    (chainSwap_LE hne hi h_up h_down L h_lt).pos z =
      L.pos (Equiv.swap a a' z) := rfl

/-- The chain swap of an LE with `a <_L a'` has `a' <_L' a`. -/
lemma chainSwap_LE_lt
    {a a' : α} (hne : a ≠ a') (hi : a ∥ a')
    (h_up : ∀ z, a < z → a' < z) (h_down : ∀ z, z < a' → z < a)
    (L : LinearExt α) (h_lt : L.lt a a') :
    (chainSwap_LE hne hi h_up h_down L h_lt).lt a' a := by
  change (chainSwap_LE hne hi h_up h_down L h_lt).pos a' <
        (chainSwap_LE hne hi h_up h_down L h_lt).pos a
  rw [chainSwap_LE_pos, chainSwap_LE_pos,
      Equiv.swap_apply_right, Equiv.swap_apply_left]
  exact h_lt

/-- **Forward chain probability bound.**  Under a one-sided ⪯-chain
`(a, a')`, the forward probability `probLT a a'` is at most `1/2`.

Proof: chain swap is an injection from `{L : L.lt a a'}` into
`{L : L.lt a' a}` (its "inverse" applied to a chain swap recovers
the original LE because `Equiv.swap a a'` is an involution).  Hence
`|{L : L.lt a a'}| ≤ |{L : L.lt a' a}|`, which combined with
`Pr[a < a'] + Pr[a' < a] = 1` yields `Pr[a < a'] ≤ 1/2`. -/
theorem probLT_le_half_of_chain
    {a a' : α} (hne : a ≠ a') (hi : a ∥ a')
    (h_up : ∀ z, a < z → a' < z) (h_down : ∀ z, z < a' → z < a) :
    probLT a a' ≤ (1 : ℚ) / 2 := by
  classical
  set Sf : Finset (LinearExt α) :=
    Finset.univ.filter (fun L => L.lt a a') with hSf_def
  set Sb : Finset (LinearExt α) :=
    Finset.univ.filter (fun L => L.lt a' a) with hSb_def
  -- Chain swap is an injection Sf → Sb.
  let f : LinearExt α → LinearExt α := fun L =>
    if h : L.lt a a' then chainSwap_LE hne hi h_up h_down L h else L
  have h_f_lands : ∀ L ∈ Sf, f L ∈ Sb := by
    intro L hL
    simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    simp only [Sb, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [f, dif_pos hL]
    exact chainSwap_LE_lt hne hi h_up h_down L hL
  have h_f_inj : Set.InjOn f (Sf : Set (LinearExt α)) := by
    intro L₁ hL₁ L₂ hL₂ heq
    simp only [Sf, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hL₁ hL₂
    simp only [f, dif_pos hL₁, dif_pos hL₂] at heq
    apply LinearExt.ext
    apply Equiv.ext
    intro z
    have htoFun_eq :
        (chainSwap_LE hne hi h_up h_down L₁ hL₁).toFun =
        (chainSwap_LE hne hi h_up h_down L₂ hL₂).toFun := by
      rw [heq]
    have h_at_swap :
        ((Equiv.swap a a').trans L₁.toFun) (Equiv.swap a a' z) =
        ((Equiv.swap a a').trans L₂.toFun) (Equiv.swap a a' z) := by
      have hcoe :
          ((chainSwap_LE hne hi h_up h_down L₁ hL₁).toFun :
              α → Fin (Fintype.card α)) =
          ((chainSwap_LE hne hi h_up h_down L₂ hL₂).toFun :
              α → Fin (Fintype.card α)) := by
        rw [htoFun_eq]
      exact congrFun hcoe (Equiv.swap a a' z)
    simp only [Equiv.trans_apply, Equiv.swap_apply_self] at h_at_swap
    exact h_at_swap
  have hcard_le : Sf.card ≤ Sb.card :=
    Finset.card_le_card_of_injOn f h_f_lands h_f_inj
  -- Bridge via probLT_add_probLT_of_ne.
  have hcard_pos : (0 : ℚ) < (numLinExt α : ℚ) := by exact_mod_cast numLinExt_pos
  have hSf_le_Sb : (Sf.card : ℚ) ≤ (Sb.card : ℚ) := by exact_mod_cast hcard_le
  have h_p_le : probLT a a' ≤ probLT a' a := by
    unfold probLT
    exact (div_le_div_iff_of_pos_right hcard_pos).mpr hSf_le_Sb
  have hsum : probLT a a' + probLT a' a = 1 := probLT_add_probLT_of_ne hne
  linarith

set_option linter.unusedVariables false in
/-- **Residual impossibility under the chain hypothesis.**  The
forward `Pr > 2/3` triple-residual output of
`m3_rotation_balanced_or_residual` is structurally impossible under
the chain hypothesis: chain swap forces each forward chain
probability `probLT a_i a_{i+1} ≤ 1/2 < 2/3`, contradicting the
strict `> 2/3` lower bound. -/
theorem chain_residual_impossible
    {a₁ a₂ a₃ : α} (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃)
    (hi12 : a₁ ∥ a₂) (hi23 : a₂ ∥ a₃) (hi13 : a₁ ∥ a₃)
    (hu12 : ∀ z, a₁ < z → a₂ < z) (hd12 : ∀ z, z < a₂ → z < a₁)
    (hu23 : ∀ z, a₂ < z → a₃ < z) (hd23 : ∀ z, z < a₃ → z < a₂)
    (hu13 : ∀ z, a₁ < z → a₃ < z) (hd13 : ∀ z, z < a₃ → z < a₁)
    (hr12 : (2 : ℚ) / 3 < probLT a₁ a₂)
    (hr23 : (2 : ℚ) / 3 < probLT a₂ a₃)
    (hr13 : (2 : ℚ) / 3 < probLT a₁ a₃) :
    False := by
  -- Any one of the three chain pairs suffices: chain swap on (a₁, a₂)
  -- gives `probLT a₁ a₂ ≤ 1/2`, contradicting `2/3 < probLT a₁ a₂`.
  -- The other two chain pairs are propagated through the signature
  -- to make the residual triple-shape explicit at the call site.
  have h12_le : probLT a₁ a₂ ≤ 1/2 :=
    probLT_le_half_of_chain h12 hi12 hu12 hd12
  linarith

/-- **Composed corollary**: under the chain hypothesis (no FKG
sub-claim required), `strictCase2WitnessChain_balanced_or_residual`
collapses to `HasBalancedPair α` whenever the FKG sub-claim
hypothesis is supplied — the residual disjunct is structurally
ruled out by chain swap.

The gap to closing `strictCase2WitnessChain L → HasBalancedPair α`
unconditionally is the FKG sub-claim hypothesis itself (the input
to `strictCase2WitnessChain_balanced_or_residual`); see
`docs/a8-s2-rotation-residual-status.md` for the full status. -/
theorem strictCase2WitnessChain_balanced_under_FKG
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
    HasBalancedPair α := by
  rcases strictCase2WitnessChain_balanced_or_residual L hC2chain hFKG with
    h | ⟨a₁, a₂, a₃, h12, h23, h13, _hb12, _hb13, hi12, hi23, hi13,
         hu12, hd12, hu23, hd23, hr12, hr23, hr13⟩
  · exact h
  · -- Residual: contradicted by chain swap.
    obtain ⟨hu13, hd13⟩ :=
      StrictCase2WitnessChain.chain_one_three hu12 hd12 hu23 hd23
    exact (chain_residual_impossible h12 h23 h13 hi12 hi23 hi13
        hu12 hd12 hu23 hd23 hu13 hd13 hr12 hr23 hr13).elim

/-! ### §7 — Bundled FKG sub-claim hypothesis (`m = 2` pair + `m = 3` chain)
(`mg-27c2`)

The paper's FKG sub-claim of `prop:bipartite-balanced` Case 2
(`step8.tex:2855-2856`) is stated uniformly for `m ∈ {2, 3}`: under a
within-band `⪯`-comparable pair (`m = 2`) or chain (`m = 3`), the
forward probabilities `probLT a_i a_{i+1}` are bounded below by `1/2`.

`Step8.InSitu.Case2FKGSubClaim L` bundles both shapes as a single named
hypothesis. Bundling reflects the paper's "single sub-claim" framing
and lets the `StrictCase2Witness L → HasBalancedPair α` closure
dispatch on chain-extension availability without changing the headline
hypothesis count.

The `chain` field has the same shape as the existing `hFKG` argument of
`strictCase2WitnessChain_balanced_under_FKG` (`§5`); the `pair` field is
its `m = 2` specialisation, the natural single-pair shape consumed by
the `m = 2` closure (chain swap + pair FKG ⇒ `probLT a a' = 1/2`). -/

/-- **FKG sub-claim hypothesis** (`step8.tex:2855-2856`, `m ∈ {2, 3}`).

A single Prop bundling the two FKG sub-claim instances the paper's
Case 2 in-situ argument relies on:

* `pair` — `m = 2` instance: `probLT a a' ≥ 1/2` for any within-band
  `⪯`-comparable pair `(a, a')`.
* `chain` — `m = 3` instance: `probLT a_i a_j ≥ 1/2` for the three
  pair-probabilities of any within-band `⪯`-chain `(a₁, a₂, a₃)`.

This is a hypothesis (an input to the closure theorem), not a theorem.
The probability-normalised cross-poset FKG infrastructure that would
prove it is documented as future work in
`Mathlib/RelationPoset/FKG.lean §11` (lines 407-426). -/
structure Case2FKGSubClaim (L : LayeredDecomposition α) : Prop where
  /-- **`m = 2` sub-claim** — single within-band `⪯`-comparable pair
  (`step8.tex:2855-2856`, `m = 2` instance). The paper derives this
  from the bipartite Case 2 coupling argument
  (`step8.tex:2858-2875`). -/
  pair : ∀ a a' : α, a ≠ a' → L.band a = L.band a' → a ∥ a' →
    (∀ z, a < z → a' < z) → (∀ z, z < a' → z < a) →
    (1 : ℚ) / 2 ≤ probLT a a'
  /-- **`m = 3` sub-claim** — three within-band `⪯`-chain elements
  (`step8.tex:2855-2856`, `m = 3` instance). Same shape as the `hFKG`
  argument of `strictCase2WitnessChain_balanced_under_FKG`. -/
  chain : ∀ a₁ a₂ a₃ : α,
    a₁ ≠ a₂ → a₂ ≠ a₃ → a₁ ≠ a₃ →
    L.band a₁ = L.band a₂ → L.band a₁ = L.band a₃ →
    a₁ ∥ a₂ → a₂ ∥ a₃ → a₁ ∥ a₃ →
    (∀ z, a₁ < z → a₂ < z) → (∀ z, z < a₂ → z < a₁) →
    (∀ z, a₂ < z → a₃ < z) → (∀ z, z < a₃ → z < a₂) →
    (1 : ℚ) / 2 ≤ probLT a₁ a₂ ∧
    (1 : ℚ) / 2 ≤ probLT a₂ a₃ ∧
    (1 : ℚ) / 2 ≤ probLT a₁ a₃

/-! ### §8 — `m = 2` single-pair closure
(`mg-27c2`, `docs/a8-s2-strict-witness-status.md` §2)

The `m = 2` instance of the StrictCase2 closure: under a strict
`⪯`-comparable within-band pair `(a, a')` and the pair part of
`Case2FKGSubClaim`, chain swap (`probLT_le_half_of_chain`) gives
`probLT a a' ≤ 1/2`, the FKG sub-claim gives `probLT a a' ≥ 1/2`,
hence `probLT a a' = 1/2 ∈ [1/3, 2/3]`. -/

/-- **`m = 2` single-pair closure**
(`step8.tex:2858-2875`, `m = 2` instance, `mg-27c2`).

Combines chain swap (`probLT_le_half_of_chain`, mg-ba0c) with the
`m = 2` part of the FKG sub-claim hypothesis to close the strict
single-pair case directly: `probLT a a' = 1/2 ∈ [1/3, 2/3]`, so the
within-band incomparable pair `(a, a')` is balanced.

Used by `strictCase2Witness_balanced_under_FKG` in the branch where no
`StrictCase2WitnessChain` extension is available (typically the band of
`a` has only the strict pair). -/
theorem strictCase2Witness_m2_balanced
    {a a' : α} (hne : a ≠ a') (hi : a ∥ a')
    (h_up : ∀ z, a < z → a' < z) (h_down : ∀ z, z < a' → z < a)
    (hp : (1 : ℚ) / 2 ≤ probLT a a') :
    HasBalancedPair α := by
  have h_le : probLT a a' ≤ (1 : ℚ) / 2 :=
    probLT_le_half_of_chain hne hi h_up h_down
  refine ⟨a, a', hi, ?_, ?_⟩
  · -- `1/3 ≤ probLT a a'` from `1/2 ≤ probLT a a'`.
    linarith
  · -- `probLT a a' ≤ 2/3` from `probLT a a' ≤ 1/2`.
    linarith

/-! ### §9 — `m = 2 → m = 3` chain extension dispatch
(`mg-27c2`, paper-level argument in `step8.tex:3001-3032`)

Under classical excluded middle on whether
`StrictCase2WitnessChain L` holds, the `StrictCase2Witness L → HasBalancedPair α`
closure dispatches:

* **Chain extension succeeds** (`StrictCase2WitnessChain L` holds): the
  band admits three within-band `⪯`-chain elements
  `a₁ ⪯ a₂ ⪯ a₃`. Apply
  `strictCase2WitnessChain_balanced_under_FKG` (§5) with the `chain`
  part of `Case2FKGSubClaim`.

* **Chain extension fails** (`¬ StrictCase2WitnessChain L`): no third
  within-band `⪯`-chain element extends the strict pair `(a, a')`
  carried by `StrictCase2Witness L` (e.g., the band has size 2, or the
  third within-band element is `⪯`-incomparable to the pair). The
  `m = 2` single-pair closure (`strictCase2Witness_m2_balanced`)
  closes via chain swap + the `pair` part of `Case2FKGSubClaim`.

The classical case split is the Lean image of the paper's Case 2 chain
extension dispatch (`step8.tex:3001-3032`): "If there exist `a, a' ∈ A`
with `Π(a) ⪯ Π(a')` (strictly, by the failure of Case 1), … if `|A| = 3`
and the three profiles form a chain in `⪯`, the rotation argument
applies; otherwise the `m = 2` direct closure handles the pair." -/

/-- **`StrictCase2Witness L → HasBalancedPair α`**
(`mg-27c2`, `docs/a8-s2-strict-witness-status.md` §3).

The chain-form FKG closure of the strict Case 2 witness, dispatching by
classical case-split on `StrictCase2WitnessChain L` (the chain
extension):

* **`m = 3` branch** — `StrictCase2WitnessChain L` holds: apply
  `strictCase2WitnessChain_balanced_under_FKG` with `hFKG.chain`.
* **`m = 2` branch** — `StrictCase2WitnessChain L` fails: apply
  `strictCase2Witness_m2_balanced` (chain swap + `hFKG.pair`).

Both branches are closed by the **same** bundled hypothesis
`hFKG : Case2FKGSubClaim L`; the dispatch is internal to the proof.

This is the discharge theorem consumed by mg-072c (the headline
`width3_one_third_two_thirds` wiring after the Path C drop-`hC3` /
add-`hFKG` swap). -/
theorem strictCase2Witness_balanced_under_FKG
    (L : LayeredDecomposition α) (hC2strict : StrictCase2Witness L)
    (hFKG : Case2FKGSubClaim L) :
    HasBalancedPair α := by
  classical
  by_cases h_chain : StrictCase2WitnessChain L
  · -- `m = 3` branch: dispatch to the existing chain closure (§5/§6).
    exact strictCase2WitnessChain_balanced_under_FKG L h_chain hFKG.chain
  · -- `m = 2` branch: chain swap + pair FKG ⇒ `probLT a a' = 1/2`.
    obtain ⟨a, a', hne, hband, hi, hu, hd, _hStrict⟩ := hC2strict
    exact strictCase2Witness_m2_balanced hne hi hu hd
      (hFKG.pair a a' hne hband hi hu hd)

/-- **`Case2Witness L → HasBalancedPair α`** (composed form).

Routes through `case2Witness_balanced_or_strict` (mg-8801): every
`Case2Witness L` is either a Case 1 ambient match (closed inline by the
symmetric collapse to `hasBalancedPair_of_ambient_profile_match`,
mg-f92d) or a `StrictCase2Witness L` (closed by
`strictCase2Witness_balanced_under_FKG`).

This is the form the headline-wiring (mg-072c) consumes when filling
the `case2Discharge : Case2Witness L → HasBalancedPair α` slot of
`hStruct_of_case2_discharge` (`Case3Residual.lean:265`). -/
theorem case2Witness_balanced_under_FKG
    (L : LayeredDecomposition α) (hC2 : Case2Witness L)
    (hFKG : Case2FKGSubClaim L) :
    HasBalancedPair α := by
  rcases case2Witness_balanced_or_strict L hC2 with h | h
  · exact h
  · exact strictCase2Witness_balanced_under_FKG L h hFKG

end InSitu
end Step8
end OneThird
