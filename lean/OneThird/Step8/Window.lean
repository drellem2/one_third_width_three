/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredReduction
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Window / bipartite construction (`sec:g4-balanced-pair`)

Formalises the *window* and *bipartite-block* data of
`step8.tex` §`sec:g4-balanced-pair` (`step8.tex:1571-1765`). These
are the geometric inputs to GAP G4 (`lem:layered-balanced`) — the
`LayeredBalanced.lean` companion file packages the conclusions; this
file provides the concrete combinatorial constructions used to
discharge the size bounds.

## Setup

For a `LayeredDecomposition L` of width `w` and any pair of band
indices `i, j` with `|i − j| ≤ w` (the only case allowed by `(L2)`),
the **window** at `(i, j)` is the band slice

  `W(i, j) := L_{a} ∪ L_{a+1} ∪ ⋯ ∪ L_{b}`

with `a := max(1, min(i, j) − w)`, `b := min(K, max(i, j) + w)`. By
`(L1)`, `|L_k| ≤ 3` for every `k`, and the window spans at most
`3w + 1` bands (with `|i − j| ≤ w`), so

  `|W(i, j)| ≤ 3 · (3w + 1)`     (`step8.tex:1606-1607`).

For the **bipartite-block** reduct of a height-2 window, we package
two consecutive bands `A = L_i, B = L_{i+1}` of size `≤ 3` each, with
the cross-band-comparability axiom `A < B` reading off (L1)/(L2) at
band-distance 1.

## Main results

* `Window` — the window structure: indices, slice finset, size bound.
* `Window.ofBandPair` — the concrete construction.
* `Window.card_le` — `|W(i, j)| ≤ 3 · (3w + 1)`.
* `BipartiteBlock` — the height-2 bipartite reduct.
* `BipartiteBlock.ofConsecutiveBands` — the concrete construction.

## References

`step8.tex` §`sec:g4-balanced-pair` (`step8.tex:1571-1765`),
Lemma `lem:window-localization`, Proposition
`prop:bipartite-balanced`.
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Window data -/

/-- **Window data** (`step8.tex:1573-1607`).

A *window* `W(i, j)` of a layered decomposition is the band slice
between `min(i, j) − w` and `max(i, j) + w` (clamped to `[1, K]`).
The structural conclusion is

* `slice = L_a ∪ ⋯ ∪ L_b`, equivalently
  `slice = {z : a ≤ band z ≤ b}`,
* `i, j ∈ [a, b]`, hence `bandSet i ∪ bandSet j ⊆ slice`,
* `|slice| ≤ 3 · (3 w + 1)` (size bound). -/
structure Window (L : LayeredDecomposition α) where
  /-- Lower band index of the window. -/
  loBand : ℕ
  /-- Upper band index of the window. -/
  hiBand : ℕ
  /-- Window finset. -/
  slice : Finset α
  /-- The window is the union of bands `[loBand, hiBand]`. -/
  slice_eq :
    slice =
      (Finset.univ : Finset α).filter
        (fun x => loBand ≤ L.band x ∧ L.band x ≤ hiBand)
  /-- The window spans at most `3w + 1` bands. -/
  span_le : hiBand + 1 ≤ loBand + (3 * L.w + 1)

namespace Window

variable (L : LayeredDecomposition α)

/-- **Concrete window construction** at a band-pair `(i, j)` with
`|i − j| ≤ w` (`step8.tex:1576-1582`).

The window is `[max(1, min i j − w), max i j + w]`, which spans at
most `2w + 1 + (j − i) ≤ 3w + 1` bands. -/
noncomputable def ofBandPair (i j : ℕ) (hij : max i j ≤ min i j + L.w) :
    Window L := by
  classical
  refine
    { loBand := if min i j ≤ L.w then 1 else min i j - L.w
      hiBand := max i j + L.w
      slice :=
        (Finset.univ : Finset α).filter
          (fun x =>
            (if min i j ≤ L.w then 1 else min i j - L.w) ≤ L.band x ∧
              L.band x ≤ max i j + L.w)
      slice_eq := rfl
      span_le := ?_ }
  -- Span bound: `(max + w) + 1 ≤ (lo) + 3w + 1`.
  -- Case A: `min ≤ w`, so `lo = 1` and span is `max + w`. We need
  -- `max + w ≤ 3w`, i.e. `max ≤ 2w`. Use `max ≤ min + w ≤ w + w = 2w`.
  -- Case B: `min > w`, so `lo = min − w` and span is `2w + (max − min) + 1`,
  -- which needs `max − min ≤ w`, given by `hij` directly.
  by_cases hmin : min i j ≤ L.w
  · simp only [if_pos hmin]
    have : max i j ≤ L.w + L.w := by omega
    omega
  · simp only [if_neg hmin]
    have hmin' : L.w < min i j := Nat.not_le.mp hmin
    have hgap : max i j - min i j ≤ L.w := by omega
    omega

/-- The window contains the band of every element with band index in
`[loBand, hiBand]`. -/
@[simp] lemma mem_iff (W : Window L) (x : α) :
    x ∈ W.slice ↔ W.loBand ≤ L.band x ∧ L.band x ≤ W.hiBand := by
  classical
  rw [W.slice_eq]
  simp

/-- **Window size bound** (`step8.tex:1606-1607`).

`|W(i, j)| ≤ 3 · (3w + 1)`, by `(L1)` (each band has size `≤ 3`)
summed over the at-most-`3w + 1` bands of the window. -/
theorem card_le (W : Window L) :
    W.slice.card ≤ 3 * (3 * L.w + 1) := by
  classical
  -- Express the slice as a disjoint union of bands `bandSet k` for
  -- `k ∈ [loBand, hiBand]`. Then bound each band by 3 and the number
  -- of bands by `3w + 1`.
  -- Concretely: `slice = ⋃_{k ∈ [lo, hi]} bandSet k` (disjoint).
  set bandRange : Finset ℕ :=
    (Finset.range (W.hiBand + 1)).filter (fun k => W.loBand ≤ k) with hRange
  have hSliceEq :
      W.slice = bandRange.biUnion (fun k => L.bandSet k) := by
    ext x
    simp only [Window.mem_iff, Finset.mem_biUnion, hRange, Finset.mem_filter,
      Finset.mem_range, LayeredDecomposition.mem_bandSet]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨L.band x, ⟨Nat.lt_succ_of_le h2, h1⟩, rfl⟩
    · rintro ⟨k, ⟨hk_lt, hk_lo⟩, rfl⟩
      exact ⟨hk_lo, Nat.le_of_lt_succ hk_lt⟩
  -- The biUnion is over disjoint band sets (different `k`s give
  -- disjoint band sets), so we can bound the cardinality by the sum.
  have hCardBound :
      W.slice.card ≤ ∑ k ∈ bandRange, (L.bandSet k).card := by
    rw [hSliceEq]
    exact Finset.card_biUnion_le
  -- Each band has size ≤ 3 (axiom L1).
  have hBandLe : ∀ k ∈ bandRange, (L.bandSet k).card ≤ 3 := by
    intro k _
    exact L.band_size k
  -- Sum bound: `∑_k (L.bandSet k).card ≤ 3 · |bandRange|`.
  have hSumBound :
      ∑ k ∈ bandRange, (L.bandSet k).card ≤ 3 * bandRange.card := by
    have h1 : ∑ k ∈ bandRange, (L.bandSet k).card ≤
        ∑ _k ∈ bandRange, 3 := Finset.sum_le_sum hBandLe
    have h2 : ∑ _k ∈ bandRange, (3 : ℕ) = 3 * bandRange.card := by
      simp [Finset.sum_const, mul_comm]
    omega
  -- `|bandRange| ≤ 3w + 1` from the span bound. The bandRange is the
  -- set `{k : loBand ≤ k ≤ hiBand}` viewed as a subset of `ℕ`; its
  -- cardinality is `hiBand + 1 − loBand` (or 0 if loBand > hiBand).
  have hRangeCard : bandRange.card ≤ 3 * L.w + 1 := by
    -- Inject `bandRange` into `Finset.range (3 * L.w + 1)` via
    -- `k ↦ k − loBand`, then use cardinality monotonicity.
    have hinj :
        Set.InjOn (fun k : ℕ => k - W.loBand) (bandRange : Set ℕ) := by
      intro a ha b hb hab
      simp only [hRange, Finset.coe_filter, Finset.mem_coe,
        Finset.mem_range, Set.mem_setOf_eq] at ha hb
      simp only at hab
      -- `a - loBand = b - loBand` with `loBand ≤ a, b`, hence `a = b`.
      have ha2 : W.loBand ≤ a := ha.2
      have hb2 : W.loBand ≤ b := hb.2
      omega
    have himg :
        bandRange.image (fun k => k - W.loBand) ⊆
          Finset.range (3 * L.w + 1) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
      simp only [hRange, Finset.mem_filter, Finset.mem_range] at hk
      have := W.span_le
      simp only [Finset.mem_range]
      omega
    calc bandRange.card
        = (bandRange.image (fun k => k - W.loBand)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (3 * L.w + 1)).card :=
          Finset.card_le_card himg
      _ = 3 * L.w + 1 := Finset.card_range _
  calc W.slice.card
      ≤ ∑ k ∈ bandRange, (L.bandSet k).card := hCardBound
    _ ≤ 3 * bandRange.card := hSumBound
    _ ≤ 3 * (3 * L.w + 1) := Nat.mul_le_mul_left 3 hRangeCard

end Window

/-! ### §2 — Bipartite-block reduct -/

/-- **Bipartite block** (`step8.tex:1610-1632`).

A *bipartite block* is the height-2 reduct extracted from two
consecutive bands `A = L_i, B = L_{i+1}` of a layered decomposition:

* `A, B : Finset α` are antichains of size `≤ 3`;
* every cross-pair satisfies `a ≤ b` (forced by (L2) for adjacent
  bands? no — adjacent bands are *not* forced comparable; the
  cross-comparability comes from height-2 internal ordinal
  decomposition). The structural axiom `aLeB` records the directed
  cross-pair comparability that holds in the reduct, supplied by
  the caller. -/
structure BipartiteBlock (L : LayeredDecomposition α) where
  /-- Lower band finset (`A = L_i`). -/
  A : Finset α
  /-- Upper band finset (`B = L_{i+1}`). -/
  B : Finset α
  /-- Lower band is an antichain. -/
  hA_anti : IsAntichain (· ≤ ·) (A : Set α)
  /-- Upper band is an antichain. -/
  hB_anti : IsAntichain (· ≤ ·) (B : Set α)
  /-- `|A| ≤ 3`, by (L1). -/
  hA_size : A.card ≤ 3
  /-- `|B| ≤ 3`, by (L1). -/
  hB_size : B.card ≤ 3
  /-- Cross-pair direction (caller supplies; in the layered setting
  this is forced by (L2) at far bands or supplied as part of the
  reduct construction). -/
  aLeB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b
  /-- At least one incomparable cross-pair witnesses non-triviality
  of the reduct. -/
  hIncomp : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧ a ∥ a'

namespace BipartiteBlock

variable (L : LayeredDecomposition α)

/-- **Concrete bipartite-block construction** from two band finsets.

The user supplies two finsets `A, B : Finset α`, the antichain
witnesses, the size bounds (by L1), the cross-direction
witness (an external structural input), and the within-band
incomparable-pair witness.

We use `ofConsecutiveBands` rather than `mk` to avoid clashing with
the auto-generated structure constructor. -/
noncomputable def ofConsecutiveBands
    (A B : Finset α)
    (hA_anti : IsAntichain (· ≤ ·) (A : Set α))
    (hB_anti : IsAntichain (· ≤ ·) (B : Set α))
    (hA_size : A.card ≤ 3) (hB_size : B.card ≤ 3)
    (aLeB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (hIncomp : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧ a ∥ a') :
    BipartiteBlock L :=
  { A := A, B := B,
    hA_anti := hA_anti, hB_anti := hB_anti,
    hA_size := hA_size, hB_size := hB_size,
    aLeB := aLeB, hIncomp := hIncomp }

/-- **Total size bound** for a bipartite block: `|A ∪ B| ≤ 6`. -/
theorem total_size_le (Q : BipartiteBlock L) :
    (Q.A ∪ Q.B).card ≤ 6 := by
  calc (Q.A ∪ Q.B).card
      ≤ Q.A.card + Q.B.card := Finset.card_union_le _ _
    _ ≤ 3 + 3 := Nat.add_le_add Q.hA_size Q.hB_size

end BipartiteBlock

end Step8
end OneThird
