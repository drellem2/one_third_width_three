/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.Mathlib.BKGraph
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Fiber-size function on the BK graph

For a finite poset `α` and two finsets `Pred Succ : Finset α` satisfying

* `Disjoint Pred Succ`, and
* `∀ x ∈ Pred, ∀ y ∈ Succ, x ≤ y`,

define the **fiber-size function**
`fiberSize Pred Succ : LinearExt α → ℕ` via
`f L = minSuccPos Succ L - maxPredPos Pred L`, where

* `maxPredPos Pred L` is the maximum 1-indexed position of a `Pred`
  element, or `0` if `Pred = ∅`;
* `minSuccPos Succ L` is the minimum 1-indexed position of a `Succ`
  element, or `Fintype.card α + 1` if `Succ = ∅`.

Combinatorially, `fiberSize L` counts the number of positions at
which a new element `z` (with predecessor set `Pred` and successor
set `Succ` in some ambient poset extending `α`) can be inserted into
`L` to produce a linear extension of the enlarged poset. This matches
`step8.tex`'s paper-side convention:
`S(L') := m` if `succ(z) = ∅`, where `m = |Q| = |α| + 1`, so that
`f(L') = S(L') − P(L') ∈ {1, …, m}` is the actual insertion-count
(`step8.tex:932–937`).

## Main result

`fiberSize_lipschitz_on_bkAdj`: for any BK-adjacent pair `L, L'`,
`fiberSize L ≤ fiberSize L' + 1 ∧ fiberSize L' ≤ fiberSize L + 1`
(the natural-number form of 1-Lipschitz). The variant
`fiberSize_lipschitz_on_bkGraph` states the same for
`(bkGraph α).Adj`, and `fiberSize_abs_int_sub_le_one_on_bkAdj`
repackages in the `|·|` form over `ℤ`.

## Proof outline

Two key observations:

1. On a BK swap `L ~ L'` at participants `(x₀, y₀)`, the map
   `posAux L : α → ℕ` — defined as `posAux L x = (L.pos x).val + 1` —
   differs from `posAux L'` only at `x₀, y₀`, and then by exactly
   `1`. So `|Pred.sup (posAux L) - Pred.sup (posAux L')| ≤ 1` and
   similarly for `Succ.inf'` (general |Δ| ≤ 1 bound).
2. Under the disjointness and comparability hypotheses, the two
   swap participants cannot split as "one in `Pred`, one in `Succ`":
   the comparability `x₀ ≤ y₀` would contradict the BK
   incomparability `x₀ ∥ y₀`, and disjointness rules out
   simultaneous membership. So at most one of `maxPredPos`,
   `minSuccPos` actually moves across the swap — the other is
   preserved. Combining, `|ΔfiberSize| ≤ 1`.

## Reference

Self-contained combinatorics. Required as input to the Brightwell
coupling in Step 8's F6-4.
-/

namespace OneThird

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

namespace LinearExt

/-! ### §1 — Fiber-size definitions -/

/-- The 1-indexed position of `x` under the linear extension `L`. The
`+1` shift keeps every real position in `{1, …, n}`, strictly above
the default `0` used for `maxPredPos` on an empty `Pred`. -/
def posAux (L : LinearExt α) (x : α) : ℕ := (L.pos x).val + 1

lemma posAux_pos (L : LinearExt α) (x : α) : 0 < L.posAux x :=
  Nat.succ_pos _

lemma posAux_le_card (L : LinearExt α) (x : α) :
    L.posAux x ≤ Fintype.card α := by
  unfold posAux
  have := (L.pos x).isLt
  omega

/-- Maximum 1-indexed position of a `Pred` element; `0` if `Pred = ∅`. -/
noncomputable def maxPredPos (Pred : Finset α) (L : LinearExt α) : ℕ :=
  Pred.sup L.posAux

/-- Minimum 1-indexed position of a `Succ` element; `Fintype.card α + 1`
if `Succ = ∅`.

The `Succ = ∅` default is `|α| + 1 = |Q|` (matching `step8.tex`'s
`S(L') := m` when `succ(z) = ∅`) so that `fiberSize = S − P` counts
the actual number of valid insertion positions `{P+1, …, S}` for `z`
in an ambient `Q = α ⊔ {z}`; in particular, when both `Pred = ∅` and
`Succ = ∅`, `fiberSize L = Fintype.card α + 1 = m`, as there are `m`
valid insertion ranks. -/
noncomputable def minSuccPos (Succ : Finset α) (L : LinearExt α) : ℕ :=
  if h : Succ.Nonempty then Succ.inf' h L.posAux else Fintype.card α + 1

/-- The fiber-size function `f L = S(L) − P(L)`. -/
noncomputable def fiberSize (Pred Succ : Finset α) (L : LinearExt α) : ℕ :=
  minSuccPos Succ L - maxPredPos Pred L

/-! ### §2 — Basic bounds -/

lemma maxPredPos_empty (L : LinearExt α) :
    maxPredPos (∅ : Finset α) L = 0 := by
  unfold maxPredPos; simp

lemma minSuccPos_empty (L : LinearExt α) :
    minSuccPos (∅ : Finset α) L = Fintype.card α + 1 := by
  unfold minSuccPos
  rw [dif_neg Finset.not_nonempty_empty]

lemma maxPredPos_le_card (Pred : Finset α) (L : LinearExt α) :
    maxPredPos Pred L ≤ Fintype.card α := by
  unfold maxPredPos
  refine Finset.sup_le ?_
  intro x _
  exact L.posAux_le_card x

lemma minSuccPos_le_card_succ (Succ : Finset α) (L : LinearExt α) :
    minSuccPos Succ L ≤ Fintype.card α + 1 := by
  unfold minSuccPos
  split_ifs with hSne
  · obtain ⟨x, hx⟩ := hSne
    calc Succ.inf' _ L.posAux ≤ L.posAux x := Finset.inf'_le _ hx
      _ ≤ Fintype.card α := L.posAux_le_card x
      _ ≤ Fintype.card α + 1 := Nat.le_succ _
  · exact le_refl _

/-- `minSuccPos` is bounded by `Fintype.card α` when `Succ` is
nonempty (its position values are genuine ranks `∈ {1, …, |α|}`). -/
lemma minSuccPos_le_card_of_nonempty (Succ : Finset α) (L : LinearExt α)
    (hSne : Succ.Nonempty) :
    minSuccPos Succ L ≤ Fintype.card α := by
  unfold minSuccPos
  rw [dif_pos hSne]
  obtain ⟨x, hx⟩ := hSne
  calc Succ.inf' _ L.posAux ≤ L.posAux x := Finset.inf'_le _ hx
    _ ≤ Fintype.card α := L.posAux_le_card x

/-! ### §3 — Consistency: `maxPredPos L ≤ minSuccPos L` -/

/-- Under the pred/succ comparability hypothesis, the max
predecessor position is at most the min successor position in every
linear extension, so `fiberSize = minSuccPos − maxPredPos` is a
"real" (untruncated) natural-number subtraction. -/
lemma maxPredPos_le_minSuccPos
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ x ∈ Pred, ∀ y ∈ Succ, x ≤ y)
    (L : LinearExt α) :
    maxPredPos Pred L ≤ minSuccPos Succ L := by
  rcases Pred.eq_empty_or_nonempty with hPE | hPne
  · subst hPE
    rw [maxPredPos_empty]
    exact Nat.zero_le _
  rcases Succ.eq_empty_or_nonempty with hSE | hSne
  · subst hSE
    rw [minSuccPos_empty]
    exact Nat.le_succ_of_le (maxPredPos_le_card Pred L)
  -- Both nonempty: pointwise bound on each (x, y) ∈ Pred × Succ.
  unfold minSuccPos
  rw [dif_pos hSne]
  unfold maxPredPos
  refine Finset.sup_le ?_
  intro x hx
  refine Finset.le_inf' hSne _ ?_
  intro y hy
  have hxy_le : x ≤ y := hComp x hx y hy
  have hxy_ne : x ≠ y := fun heq =>
    (Finset.disjoint_left.mp hDisj) hx (heq ▸ hy)
  have hpos_lt : L.pos x < L.pos y := L.pos_lt_pos_of_lt hxy_le hxy_ne
  have : (L.pos x).val + 1 ≤ (L.pos y).val := hpos_lt
  unfold posAux
  omega

/-- `fiberSize` never exceeds `Fintype.card α + 1 = |Q|`.

Equality holds only when `Pred = ∅` and `Succ = ∅` simultaneously, in
which case `fiberSize = Fintype.card α + 1` corresponds to the `m`
valid insertion ranks of an unconstrained element. -/
lemma fiberSize_le_card_succ (Pred Succ : Finset α) (L : LinearExt α) :
    fiberSize Pred Succ L ≤ Fintype.card α + 1 := by
  unfold fiberSize
  calc minSuccPos Succ L - maxPredPos Pred L
      ≤ minSuccPos Succ L := Nat.sub_le _ _
    _ ≤ Fintype.card α + 1 := minSuccPos_le_card_succ Succ L

/-! ### §4 — `posAux` pointwise bound and invariance under BK swaps -/

/-- On a BK swap `L ~ L'` at participants `(x₀, y₀)`, `posAux` agrees
between `L` and `L'` on every element other than `x₀, y₀`. -/
private lemma posAux_eq_of_not_swapped
    {L L' : LinearExt α}
    {x₀ y₀ : α}
    (hrest : ∀ z : α, z ≠ x₀ → z ≠ y₀ → L.pos z = L'.pos z)
    {z : α} (hzx : z ≠ x₀) (hzy : z ≠ y₀) :
    L.posAux z = L'.posAux z := by
  unfold posAux
  rw [hrest z hzx hzy]

/-- On a BK swap, `posAux L x ≤ posAux L' x + 1` for every `x ∈ α`
(and symmetrically). -/
private lemma posAux_le_add_one
    {L L' : LinearExt α} (h : BKAdj L L') (z : α) :
    L.posAux z ≤ L'.posAux z + 1 := by
  obtain ⟨x₀, y₀, k, _, _, hLx, hLy, hL'x, hL'y, hrest⟩ := h
  by_cases hzx : z = x₀
  · subst hzx
    have h1 : L.posAux z = k.val + 1 := by unfold posAux; rw [hLx]
    have h2 : L'.posAux z = k.val + 2 := by unfold posAux; rw [hL'x]
    omega
  by_cases hzy : z = y₀
  · subst hzy
    have h1 : L.posAux z = k.val + 2 := by unfold posAux; rw [hLy]
    have h2 : L'.posAux z = k.val + 1 := by unfold posAux; rw [hL'y]
    omega
  · have heq := posAux_eq_of_not_swapped hrest hzx hzy
    omega

/-! ### §5 — One-sided `|Δ| ≤ 1` bounds for `maxPredPos` and `minSuccPos` -/

lemma maxPredPos_le_succ_add_one (Pred : Finset α) {L L' : LinearExt α}
    (h : BKAdj L L') :
    maxPredPos Pred L ≤ maxPredPos Pred L' + 1 := by
  unfold maxPredPos
  refine Finset.sup_le ?_
  intro x hx
  have h1 : L.posAux x ≤ L'.posAux x + 1 := posAux_le_add_one h x
  have h2 : L'.posAux x ≤ Pred.sup L'.posAux := Finset.le_sup hx
  omega

lemma minSuccPos_le_succ_add_one (Succ : Finset α) {L L' : LinearExt α}
    (h : BKAdj L L') :
    minSuccPos Succ L ≤ minSuccPos Succ L' + 1 := by
  unfold minSuccPos
  split_ifs with hSne
  · -- Need: Succ.inf' hSne L.posAux ≤ Succ.inf' hSne L'.posAux + 1.
    -- Strategy: use `Finset.inf'_le_iff.mpr ⟨x, hx, h⟩` where x ∈ Succ
    -- and `L.posAux x ≤ Succ.inf' hSne L'.posAux + 1`. Pick x = argmin of
    -- `L'.posAux` on Succ.
    obtain ⟨x, hx, hx_eq⟩ := Finset.exists_mem_eq_inf' (H := hSne) L'.posAux
    rw [hx_eq]
    have h1 : L.posAux x ≤ L'.posAux x + 1 := posAux_le_add_one h x
    have h2 : Succ.inf' hSne L.posAux ≤ L.posAux x :=
      Finset.inf'_le _ hx
    omega
  · exact Nat.le_succ _

/-! ### §6 — Side-preservation: `maxPredPos` or `minSuccPos` unchanged -/

/-- When both swap participants `x₀, y₀` lie in `Pred`, the max pred
position is unchanged. The `posAux` values `{k+1, k+2}` merely swap
between `x₀` and `y₀`, leaving the multiset `Pred.image posAux`
fixed. -/
private lemma maxPredPos_eq_of_both_in_pred
    (Pred : Finset α)
    {L L' : LinearExt α}
    {x₀ y₀ : α} {k : Fin (Fintype.card α)}
    {hk : k.val + 1 < Fintype.card α}
    (hLx : L.pos x₀ = k) (hLy : L.pos y₀ = ⟨k.val + 1, hk⟩)
    (hL'x : L'.pos x₀ = ⟨k.val + 1, hk⟩) (hL'y : L'.pos y₀ = k)
    (hrest : ∀ z : α, z ≠ x₀ → z ≠ y₀ → L.pos z = L'.pos z)
    (hxP : x₀ ∈ Pred) (hyP : y₀ ∈ Pred) :
    maxPredPos Pred L = maxPredPos Pred L' := by
  have hLx_eq : L.posAux x₀ = k.val + 1 := by unfold posAux; rw [hLx]
  have hLy_eq : L.posAux y₀ = k.val + 2 := by unfold posAux; rw [hLy]
  have hL'x_eq : L'.posAux x₀ = k.val + 2 := by unfold posAux; rw [hL'x]
  have hL'y_eq : L'.posAux y₀ = k.val + 1 := by unfold posAux; rw [hL'y]
  unfold maxPredPos
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro z hz
    by_cases hzx : z = x₀
    · subst hzx
      rw [hLx_eq, ← hL'y_eq]
      exact Finset.le_sup hyP
    · by_cases hzy : z = y₀
      · subst hzy
        rw [hLy_eq, ← hL'x_eq]
        exact Finset.le_sup hxP
      · rw [posAux_eq_of_not_swapped hrest hzx hzy]
        exact Finset.le_sup hz
  · refine Finset.sup_le ?_
    intro z hz
    by_cases hzx : z = x₀
    · subst hzx
      rw [hL'x_eq, ← hLy_eq]
      exact Finset.le_sup hyP
    · by_cases hzy : z = y₀
      · subst hzy
        rw [hL'y_eq, ← hLx_eq]
        exact Finset.le_sup hxP
      · rw [← posAux_eq_of_not_swapped hrest hzx hzy]
        exact Finset.le_sup hz

/-- When neither swap participant lies in `Pred`, `maxPredPos` is
unchanged. -/
private lemma maxPredPos_eq_of_both_out_pred
    (Pred : Finset α)
    {L L' : LinearExt α}
    {x₀ y₀ : α}
    (hrest : ∀ z : α, z ≠ x₀ → z ≠ y₀ → L.pos z = L'.pos z)
    (hxP : x₀ ∉ Pred) (hyP : y₀ ∉ Pred) :
    maxPredPos Pred L = maxPredPos Pred L' := by
  unfold maxPredPos
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro z hz
    have hzx : z ≠ x₀ := fun h => hxP (h ▸ hz)
    have hzy : z ≠ y₀ := fun h => hyP (h ▸ hz)
    rw [posAux_eq_of_not_swapped hrest hzx hzy]
    exact Finset.le_sup hz
  · refine Finset.sup_le ?_
    intro z hz
    have hzx : z ≠ x₀ := fun h => hxP (h ▸ hz)
    have hzy : z ≠ y₀ := fun h => hyP (h ▸ hz)
    rw [← posAux_eq_of_not_swapped hrest hzx hzy]
    exact Finset.le_sup hz

/-- When neither swap participant lies in `Succ`, `minSuccPos` is
unchanged. -/
private lemma minSuccPos_eq_of_both_out_succ
    (Succ : Finset α)
    {L L' : LinearExt α}
    {x₀ y₀ : α}
    (hrest : ∀ z : α, z ≠ x₀ → z ≠ y₀ → L.pos z = L'.pos z)
    (hxS : x₀ ∉ Succ) (hyS : y₀ ∉ Succ) :
    minSuccPos Succ L = minSuccPos Succ L' := by
  unfold minSuccPos
  split_ifs with hSne
  · apply le_antisymm
    · refine Finset.le_inf' hSne _ ?_
      intro z hz
      have hzx : z ≠ x₀ := fun h => hxS (h ▸ hz)
      have hzy : z ≠ y₀ := fun h => hyS (h ▸ hz)
      rw [← posAux_eq_of_not_swapped hrest hzx hzy]
      exact Finset.inf'_le _ hz
    · refine Finset.le_inf' hSne _ ?_
      intro z hz
      have hzx : z ≠ x₀ := fun h => hxS (h ▸ hz)
      have hzy : z ≠ y₀ := fun h => hyS (h ▸ hz)
      rw [posAux_eq_of_not_swapped hrest hzx hzy]
      exact Finset.inf'_le _ hz
  · rfl

/-! ### §7 — Main theorem: fiber size is 1-Lipschitz on BK -/

/-- On a BK swap under the hypotheses of `fiberSize_lipschitz_on_bkAdj`,
exactly one of `maxPredPos`, `minSuccPos` is preserved, depending on
whether the two swap participants share Pred-status or not. -/
private lemma pred_preserved_or_succ_preserved
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ x ∈ Pred, ∀ y ∈ Succ, x ≤ y)
    {L L' : LinearExt α} (h : BKAdj L L') :
    maxPredPos Pred L = maxPredPos Pred L' ∨
      minSuccPos Succ L = minSuccPos Succ L' := by
  obtain ⟨x₀, y₀, k, hk, hxy, hLx, hLy, hL'x, hL'y, hrest⟩ := h
  -- Exclusion from comparability + incomparability + disjointness:
  have exclPred_of_x : x₀ ∈ Pred → x₀ ∉ Succ ∧ y₀ ∉ Succ := by
    intro hxP
    refine ⟨fun hxS => ?_, fun hyS => ?_⟩
    · exact (Finset.disjoint_left.mp hDisj) hxP hxS
    · exact hxy.1 (hComp x₀ hxP y₀ hyS)
  have exclPred_of_y : y₀ ∈ Pred → x₀ ∉ Succ ∧ y₀ ∉ Succ := by
    intro hyP
    refine ⟨fun hxS => ?_, fun hyS => ?_⟩
    · exact hxy.2 (hComp y₀ hyP x₀ hxS)
    · exact (Finset.disjoint_left.mp hDisj) hyP hyS
  by_cases hxP : x₀ ∈ Pred
  · by_cases hyP : y₀ ∈ Pred
    · left
      exact maxPredPos_eq_of_both_in_pred Pred (hk := hk)
        hLx hLy hL'x hL'y hrest hxP hyP
    · obtain ⟨hxS, hyS⟩ := exclPred_of_x hxP
      right
      exact minSuccPos_eq_of_both_out_succ Succ hrest hxS hyS
  · by_cases hyP : y₀ ∈ Pred
    · obtain ⟨hxS, hyS⟩ := exclPred_of_y hyP
      right
      exact minSuccPos_eq_of_both_out_succ Succ hrest hxS hyS
    · left
      exact maxPredPos_eq_of_both_out_pred Pred hrest hxP hyP

/-- The **fiber-size function is 1-Lipschitz** on the
Bubley–Karzanov / adjacent-transposition graph `bkGraph α`. -/
theorem fiberSize_lipschitz_on_bkAdj
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ x ∈ Pred, ∀ y ∈ Succ, x ≤ y)
    {L L' : LinearExt α} (h : BKAdj L L') :
    fiberSize Pred Succ L ≤ fiberSize Pred Succ L' + 1 ∧
      fiberSize Pred Succ L' ≤ fiberSize Pred Succ L + 1 := by
  have hP : maxPredPos Pred L ≤ minSuccPos Succ L :=
    maxPredPos_le_minSuccPos Pred Succ hDisj hComp L
  have hP' : maxPredPos Pred L' ≤ minSuccPos Succ L' :=
    maxPredPos_le_minSuccPos Pred Succ hDisj hComp L'
  rcases pred_preserved_or_succ_preserved Pred Succ hDisj hComp h with hEq | hEq
  · -- maxPredPos is preserved: fiberSize difference is controlled by
    -- |ΔminSuccPos| ≤ 1.
    have h1 : minSuccPos Succ L ≤ minSuccPos Succ L' + 1 :=
      minSuccPos_le_succ_add_one Succ h
    have h2 : minSuccPos Succ L' ≤ minSuccPos Succ L + 1 :=
      minSuccPos_le_succ_add_one Succ h.symm
    unfold fiberSize
    rw [hEq]
    -- Goal: minSuccPos L - maxPredPos L' ≤ minSuccPos L' - maxPredPos L' + 1 ∧ ...
    have hP'' : maxPredPos Pred L' ≤ minSuccPos Succ L := hEq ▸ hP
    refine ⟨?_, ?_⟩ <;> omega
  · -- minSuccPos is preserved: difference controlled by |ΔmaxPredPos| ≤ 1.
    have h1 : maxPredPos Pred L ≤ maxPredPos Pred L' + 1 :=
      maxPredPos_le_succ_add_one Pred h
    have h2 : maxPredPos Pred L' ≤ maxPredPos Pred L + 1 :=
      maxPredPos_le_succ_add_one Pred h.symm
    unfold fiberSize
    rw [hEq]
    have hP'' : maxPredPos Pred L ≤ minSuccPos Succ L' := hEq ▸ hP
    refine ⟨?_, ?_⟩ <;> omega

/-- `fiberSize` is 1-Lipschitz on the BK graph. -/
theorem fiberSize_lipschitz_on_bkGraph
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ x ∈ Pred, ∀ y ∈ Succ, x ≤ y)
    {L L' : LinearExt α} (h : (bkGraph α).Adj L L') :
    fiberSize Pred Succ L ≤ fiberSize Pred Succ L' + 1 ∧
      fiberSize Pred Succ L' ≤ fiberSize Pred Succ L + 1 :=
  fiberSize_lipschitz_on_bkAdj Pred Succ hDisj hComp h

/-- Integer-`|·|` form of the Lipschitz bound. -/
theorem fiberSize_abs_int_sub_le_one_on_bkAdj
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ x ∈ Pred, ∀ y ∈ Succ, x ≤ y)
    {L L' : LinearExt α} (h : BKAdj L L') :
    |(fiberSize Pred Succ L : ℤ) - fiberSize Pred Succ L'| ≤ 1 := by
  obtain ⟨h₁, h₂⟩ :=
    fiberSize_lipschitz_on_bkAdj Pred Succ hDisj hComp h
  have h₁' : (fiberSize Pred Succ L : ℤ) ≤ fiberSize Pred Succ L' + 1 := by
    exact_mod_cast h₁
  have h₂' : (fiberSize Pred Succ L' : ℤ) ≤ fiberSize Pred Succ L + 1 := by
    exact_mod_cast h₂
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end LinearExt

end OneThird
