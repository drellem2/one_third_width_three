/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.BKGraph
import OneThird.Poset
import Mathlib.Data.Fin.VecNotation

/-!
# Step 1 — Commuting BK squares and cubes

The combinatorial core of the Step 1 overlap and triple-overlap
corollaries (`cor:overlap`, `cor:triple-overlap` in `step1.tex`).

The paper's `cor:overlap` part (a) and `cor:triple-overlap` part (b)
both reduce to one fact: **adjacent transpositions with disjoint
supports commute**, so two (resp. three) BK moves whose moved elements
sit at disjoint position intervals generate an embedded `2×2` BK square
(resp. `2×2×2` BK cube). This file proves that fact in full, on the
abstract `bkGraph`, depending only on `OneThird/Mathlib/BKGraph.lean`.

The connection from the paper's *interaction-locus exclusion*
(membership in the regular overlap `Ω°` / `Ω°°°`) to the
*disjoint-support* hypothesis used here is the BK-move classification
of `thm:interface` part (iii) (the S1-B deliverable); it is wired in at
Step 1 assembly. The verifications in this file are unconditional and
non-vacuous — see `bkCommCube_grid_example` for a concrete width-3
non-chain instantiation.

## Main definitions

* `BKCommSquare L₀ L₁ L₂ L₃` — the four extensions form a commuting
  `2×2` BK square: `L₀–L₁`, `L₀–L₂`, `L₁–L₃`, `L₂–L₃` are BK edges.
* `BKCommCube` — the eight extensions form a commuting `2×2×2` BK cube,
  bundled as its six commuting faces.

## Main results

* `swap_trans_swap_comm` — disjoint-support transpositions commute.
* `swapAdj_comm` — `swapAdj` at disjoint positions commutes.
* `bkCommSquare_of_disjoint` — `cor:overlap` part (a): two BK moves at
  disjoint positions span a commuting `2×2` square.
* `bkAdj_commuting_square` — the same, phrased with `BKAdj` inputs and a
  disjoint-element-support hypothesis.
* `bkCommCube_of_disjoint` — `cor:triple-overlap` parts (b),(c): three
  BK moves at pairwise-disjoint positions span a commuting `2×2×2`
  cube.
* `bkCommCube_grid_example` — non-vacuity: the cube instantiates on the
  concrete width-3 non-chain poset `Fin 3 × Fin 3`.
-/

namespace OneThird

open Equiv

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## §1. Disjoint-support transpositions commute -/

/-- Two transpositions whose four points are pairwise distinct across
the pairs commute: this is the algebraic heart of every commuting BK
square. -/
lemma swap_trans_swap_comm {β : Type*} [DecidableEq β] {a b c d : β}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d)
      = (Equiv.swap c d).trans (Equiv.swap a b) := by
  ext i
  simp only [Equiv.trans_apply]
  rcases eq_or_ne i a with rfl | hia
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbc hbd,
        Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left]
  rcases eq_or_ne i b with rfl | hib
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac had,
        Equiv.swap_apply_of_ne_of_ne hbc hbd, Equiv.swap_apply_right]
  rcases eq_or_ne i c with rfl | hic
  · rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  rcases eq_or_ne i d with rfl | hid
  · rw [Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · rw [Equiv.swap_apply_of_ne_of_ne hia hib,
        Equiv.swap_apply_of_ne_of_ne hic hid,
        Equiv.swap_apply_of_ne_of_ne hia hib]

/-! ## §2. Disjoint positions

A BK move at position `k` transposes the elements at positions `k` and
`k+1`. Two moves at positions `k`, `m` have **disjoint support** when
the intervals `{k, k+1}` and `{m, m+1}` are disjoint, i.e.
`k + 1 < m ∨ m + 1 < k`. -/

/-- Disjoint position intervals. -/
def DisjointPos {n : ℕ} (k m : Fin n) : Prop :=
  k.val + 1 < m.val ∨ m.val + 1 < k.val

lemma DisjointPos.symm {n : ℕ} {k m : Fin n} (h : DisjointPos k m) :
    DisjointPos m k := Or.symm h

instance {n : ℕ} (k m : Fin n) : Decidable (DisjointPos k m) := by
  unfold DisjointPos; infer_instance

/-- From disjoint positions, the four `Fin`-points of the two moves are
pairwise distinct. -/
lemma DisjointPos.ne_left {n : ℕ} {k m : Fin n} (h : DisjointPos k m) :
    m ≠ k := by
  rcases h with h | h <;> exact Fin.ne_of_val_ne (by omega)

lemma DisjointPos.ne_succ_left {n : ℕ} {k m : Fin n}
    (h : DisjointPos k m) (hk : k.val + 1 < n) :
    m ≠ ⟨k.val + 1, hk⟩ := by
  rcases h with h | h <;> exact Fin.ne_of_val_ne (by simp; omega)

lemma DisjointPos.succ_ne_left {n : ℕ} {k m : Fin n}
    (h : DisjointPos k m) (hm : m.val + 1 < n) :
    (⟨m.val + 1, hm⟩ : Fin n) ≠ k := by
  rcases h with h | h <;> exact Fin.ne_of_val_ne (by simp; omega)

lemma DisjointPos.succ_ne_succ_left {n : ℕ} {k m : Fin n}
    (h : DisjointPos k m) (hk : k.val + 1 < n) (hm : m.val + 1 < n) :
    (⟨m.val + 1, hm⟩ : Fin n) ≠ ⟨k.val + 1, hk⟩ := by
  rcases h with h | h <;> exact Fin.ne_of_val_ne (by simp; omega)

/-! ## §3. `swapAdj` at disjoint positions -/

/-- A `swapAdj` at position `k` fixes the element sitting at any
position outside `{k, k+1}`. -/
lemma swapAdj_toFun_symm_eq (L : LinearExt α) {k : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α)
    (hinc : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    {i : Fin (Fintype.card α)} (hik : i ≠ k)
    (hik' : i ≠ ⟨k.val + 1, hk⟩) :
    (L.swapAdj k hk hinc).toFun.symm i = L.toFun.symm i := by
  rw [Equiv.symm_apply_eq]
  have hz : L.pos (L.toFun.symm i) = i := L.toFun.apply_symm_apply i
  have hzk : L.pos (L.toFun.symm i) ≠ k := by rw [hz]; exact hik
  have hzk' : L.pos (L.toFun.symm i) ≠ ⟨k.val + 1, hk⟩ := by rw [hz]; exact hik'
  have hpos := L.pos_swapAdj_of_other k hk hinc hzk hzk'
  rw [hz] at hpos
  exact hpos.symm

/-- A BK move at position `m` remains enabled after a `swapAdj` at a
disjoint position `k`: the incomparability of the elements at `m`,
`m+1` is preserved. -/
lemma swapAdj_incomp_of_disjoint (L : LinearExt α)
    {k m : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) (hm : m.val + 1 < Fintype.card α)
    (hkinc : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    (hminc : L.toFun.symm m ∥ L.toFun.symm ⟨m.val + 1, hm⟩)
    (hdisj : DisjointPos k m) :
    (L.swapAdj k hk hkinc).toFun.symm m ∥
      (L.swapAdj k hk hkinc).toFun.symm ⟨m.val + 1, hm⟩ := by
  rw [swapAdj_toFun_symm_eq L hk hkinc hdisj.ne_left
        (hdisj.ne_succ_left hk),
      swapAdj_toFun_symm_eq L hk hkinc (hdisj.succ_ne_left hm)
        (hdisj.succ_ne_succ_left hk hm)]
  exact hminc

/-- `swapAdj` at two disjoint positions commute. (The result is
independent of the incomparability proof terms, which live in `Prop`.) -/
lemma swapAdj_comm (L : LinearExt α) {k m : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) (hm : m.val + 1 < Fintype.card α)
    (hkinc : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    (hminc : L.toFun.symm m ∥ L.toFun.symm ⟨m.val + 1, hm⟩)
    (hdisj : DisjointPos k m) :
    (L.swapAdj k hk hkinc).swapAdj m hm
        (swapAdj_incomp_of_disjoint L hk hm hkinc hminc hdisj)
      = (L.swapAdj m hm hminc).swapAdj k hk
        (swapAdj_incomp_of_disjoint L hm hk hminc hkinc hdisj.symm) := by
  apply LinearExt.ext
  change (L.toFun.trans (Equiv.swap k ⟨k.val + 1, hk⟩)).trans
        (Equiv.swap m ⟨m.val + 1, hm⟩)
      = (L.toFun.trans (Equiv.swap m ⟨m.val + 1, hm⟩)).trans
        (Equiv.swap k ⟨k.val + 1, hk⟩)
  rw [Equiv.trans_assoc, Equiv.trans_assoc,
      swap_trans_swap_comm (hdisj.ne_left).symm
        ((hdisj.succ_ne_left hm)).symm
        ((hdisj.ne_succ_left hk)).symm
        ((hdisj.succ_ne_succ_left hk hm)).symm]

/-! ## §4. The commuting `2×2` BK square (`cor:overlap` part (a)) -/

/-- A **commuting `2×2` BK square**: the four extensions are connected
by BK edges `L₀–L₁`, `L₀–L₂`, `L₁–L₃`, `L₂–L₃`. -/
structure BKCommSquare (L₀ L₁ L₂ L₃ : LinearExt α) : Prop where
  bkAdj01 : BKAdj L₀ L₁
  bkAdj02 : BKAdj L₀ L₂
  bkAdj13 : BKAdj L₁ L₃
  bkAdj23 : BKAdj L₂ L₃

/-- **`cor:overlap` part (a), commuting-square verification.** Two BK
moves at disjoint positions `k`, `m` of `L₀` span an embedded
commuting `2×2` BK square, whose fourth corner is reachable by either
order of the two moves. -/
theorem bkCommSquare_of_disjoint (L₀ : LinearExt α)
    {k m : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) (hm : m.val + 1 < Fintype.card α)
    (hkinc : L₀.toFun.symm k ∥ L₀.toFun.symm ⟨k.val + 1, hk⟩)
    (hminc : L₀.toFun.symm m ∥ L₀.toFun.symm ⟨m.val + 1, hm⟩)
    (hdisj : DisjointPos k m) :
    BKCommSquare L₀ (L₀.swapAdj k hk hkinc) (L₀.swapAdj m hm hminc)
      ((L₀.swapAdj k hk hkinc).swapAdj m hm
        (swapAdj_incomp_of_disjoint L₀ hk hm hkinc hminc hdisj)) := by
  have hminc' := swapAdj_incomp_of_disjoint L₀ hk hm hkinc hminc hdisj
  have hkinc' :=
    swapAdj_incomp_of_disjoint L₀ hm hk hminc hkinc hdisj.symm
  have hcomm := swapAdj_comm L₀ hk hm hkinc hminc hdisj
  refine ⟨bkAdj_swapAdj L₀ k hk hkinc, bkAdj_swapAdj L₀ m hm hminc,
    bkAdj_swapAdj (L₀.swapAdj k hk hkinc) m hm hminc', ?_⟩
  rw [hcomm]
  exact bkAdj_swapAdj (L₀.swapAdj m hm hminc) k hk hkinc'

/-- A BK move identifies the moved elements: from `BKAdj L L'` we
recover the position `k` and the underlying `swapAdj`. -/
lemma exists_swapAdj_of_bkAdj {L L' : LinearExt α} (h : BKAdj L L') :
    ∃ (k : Fin (Fintype.card α)) (hk : k.val + 1 < Fintype.card α)
      (hinc : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩),
      L' = L.swapAdj k hk hinc := by
  obtain ⟨x, y, k, hk, hxy, hLx, hLy, hL'x, hL'y, hrest⟩ := h
  have hsx : L.toFun.symm k = x := by
    rw [Equiv.symm_apply_eq]; exact hLx.symm
  have hsy : L.toFun.symm ⟨k.val + 1, hk⟩ = y := by
    rw [Equiv.symm_apply_eq]; exact hLy.symm
  have hinc : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩ := by
    rw [hsx, hsy]; exact hxy
  refine ⟨k, hk, hinc, ?_⟩
  apply LinearExt.ext
  apply Equiv.ext
  intro a
  rcases eq_or_ne a x with rfl | hax
  · change L'.toFun a = (L.swapAdj k hk hinc).toFun a
    have h1 : L'.toFun a = ⟨k.val + 1, hk⟩ := hL'x
    have h2 : (L.swapAdj k hk hinc).pos a = ⟨k.val + 1, hk⟩ :=
      L.pos_swapAdj_of_pos_eq k hk hinc a hLx
    rw [h1]; exact h2.symm
  rcases eq_or_ne a y with rfl | hay
  · change L'.toFun a = (L.swapAdj k hk hinc).toFun a
    have h1 : L'.toFun a = k := hL'y
    have h2 : (L.swapAdj k hk hinc).pos a = k :=
      L.pos_swapAdj_of_pos_eq_succ k hk hinc a hLy
    rw [h1]; exact h2.symm
  · change L'.toFun a = (L.swapAdj k hk hinc).toFun a
    have h1 : L'.toFun a = L.toFun a := (hrest a hax hay).symm
    have hak : L.pos a ≠ k := by
      rw [← hLx]; exact fun h => hax (L.toFun.injective h)
    have hak' : L.pos a ≠ ⟨k.val + 1, hk⟩ := by
      rw [← hLy]; exact fun h => hay (L.toFun.injective h)
    have h2 : (L.swapAdj k hk hinc).pos a = L.pos a :=
      L.pos_swapAdj_of_other k hk hinc hak hak'
    rw [h1]; exact h2.symm

/-! ## §5. The commuting `2×2×2` BK cube (`cor:triple-overlap` parts (b),(c)) -/

/-- `swapAdj` depends on its base extension only: equal bases give
equal `swapAdj` (the incomparability arguments are proof-irrelevant). -/
lemma swapAdj_congr {L L' : LinearExt α} (k : Fin (Fintype.card α))
    (hk : k.val + 1 < Fintype.card α)
    {h : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩}
    (hLL : L = L') :
    L.swapAdj k hk h = L'.swapAdj k hk (hLL ▸ h) := by
  subst hLL; rfl

/-- A **commuting `2×2×2` BK cube**: the eight extensions form a cube
whose six faces are all commuting `2×2` BK squares. Vertices are named
by the subset of the three move-directions applied to the base `v₀`. -/
structure BKCommCube (v₀ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ : LinearExt α) :
    Prop where
  /-- The `{1,2}` face through the base. -/
  face₁₂ : BKCommSquare v₀ v₁ v₂ v₁₂
  /-- The `{1,3}` face through the base. -/
  face₁₃ : BKCommSquare v₀ v₁ v₃ v₁₃
  /-- The `{2,3}` face through the base. -/
  face₂₃ : BKCommSquare v₀ v₂ v₃ v₂₃
  /-- The `{1,2}` face through the apex. -/
  face₁₂' : BKCommSquare v₃ v₁₃ v₂₃ v₁₂₃
  /-- The `{1,3}` face through the apex. -/
  face₁₃' : BKCommSquare v₂ v₁₂ v₂₃ v₁₂₃
  /-- The `{2,3}` face through the apex. -/
  face₂₃' : BKCommSquare v₁ v₁₂ v₁₃ v₁₂₃

/-- **`cor:triple-overlap` parts (b),(c), commuting-cube verification.**
Three BK moves at pairwise-disjoint positions `p₁, p₂, p₃` of `L₀` span
an embedded commuting `2×2×2` BK cube: the three move-directions
pairwise commute, so all eight subset-vertices are reachable and all
six faces commute. This is the local `ℤ³` cube model `cor:triple-overlap`
supplies to Step 7 (gap G4). -/
theorem bkCommCube_of_disjoint (L₀ : LinearExt α)
    {p₁ p₂ p₃ : Fin (Fintype.card α)}
    (hp₁ : p₁.val + 1 < Fintype.card α)
    (hp₂ : p₂.val + 1 < Fintype.card α)
    (hp₃ : p₃.val + 1 < Fintype.card α)
    (hi₁ : L₀.toFun.symm p₁ ∥ L₀.toFun.symm ⟨p₁.val + 1, hp₁⟩)
    (hi₂ : L₀.toFun.symm p₂ ∥ L₀.toFun.symm ⟨p₂.val + 1, hp₂⟩)
    (hi₃ : L₀.toFun.symm p₃ ∥ L₀.toFun.symm ⟨p₃.val + 1, hp₃⟩)
    (h₁₂ : DisjointPos p₁ p₂) (h₁₃ : DisjointPos p₁ p₃)
    (h₂₃ : DisjointPos p₂ p₃) :
    ∃ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ : LinearExt α,
      BKCommCube L₀ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ := by
  -- Incomparabilities of the second move relative to a single prior move.
  have j₁₂ := swapAdj_incomp_of_disjoint L₀ hp₁ hp₂ hi₁ hi₂ h₁₂
  have j₁₃ := swapAdj_incomp_of_disjoint L₀ hp₁ hp₃ hi₁ hi₃ h₁₃
  have j₂₃ := swapAdj_incomp_of_disjoint L₀ hp₂ hp₃ hi₂ hi₃ h₂₃
  have j₂₁ := swapAdj_incomp_of_disjoint L₀ hp₂ hp₁ hi₂ hi₁ h₁₂.symm
  -- The three faces through the base `L₀`.
  have face₁₂ := bkCommSquare_of_disjoint L₀ hp₁ hp₂ hi₁ hi₂ h₁₂
  have face₁₃ := bkCommSquare_of_disjoint L₀ hp₁ hp₃ hi₁ hi₃ h₁₃
  have face₂₃ := bkCommSquare_of_disjoint L₀ hp₂ hp₃ hi₂ hi₃ h₂₃
  -- The face `{2,3}` through `v₁`; its apex is the triple vertex.
  have face123 := bkCommSquare_of_disjoint (L₀.swapAdj p₁ hp₁ hi₁)
    hp₂ hp₃ j₁₂ j₁₃ h₂₃
  -- The twelfth edge `v₂₃–v₁₂₃`, obtained by commuting the moves.
  have inc1 := swapAdj_incomp_of_disjoint (L₀.swapAdj p₂ hp₂ hi₂)
    hp₃ hp₁ j₂₃ j₂₁ h₁₃.symm
  have e1 := swapAdj_comm (L₀.swapAdj p₂ hp₂ hi₂) hp₃ hp₁ j₂₃ j₂₁ h₁₃.symm
  have e2 := swapAdj_comm L₀ hp₂ hp₁ hi₂ hi₁ h₁₂.symm
  have heq := e1.trans (swapAdj_congr p₃ hp₃ e2)
  have edge₂₃ :=
    heq ▸ bkAdj_swapAdj ((L₀.swapAdj p₂ hp₂ hi₂).swapAdj p₃ hp₃ j₂₃)
      p₁ hp₁ inc1
  refine ⟨_, _, _, _, _, _, _,
    face₁₂, face₁₃, face₂₃, ?_, ?_, face123⟩
  · -- face `{1,2}` through the apex: `BKCommSquare v₃ v₁₃ v₂₃ v₁₂₃`.
    exact ⟨face₁₃.bkAdj23, face₂₃.bkAdj23, face123.bkAdj23, edge₂₃⟩
  · -- face `{1,3}` through the apex: `BKCommSquare v₂ v₁₂ v₂₃ v₁₂₃`.
    exact ⟨face₁₂.bkAdj23, face₂₃.bkAdj13, face123.bkAdj13, edge₂₃⟩

/-! ## §6. Non-vacuity: a concrete width-3 non-chain instantiation

The verifications above are not vacuous. We exhibit the commuting cube
on the grid poset `Fin 3 × Fin 3` — a genuine width-3 non-chain finite
poset — instantiated at its anti-diagonal linear extension, where the
three BK moves at positions `1`, `3`, `6` have pairwise-disjoint
support. -/

section Example

/-- The **anti-diagonal linear extension** of the grid poset
`Fin 3 × Fin 3`: list the elements anti-diagonal by anti-diagonal,
`(0,0)`, `(0,1),(1,0)`, `(0,2),(1,1),(2,0)`, `(1,2),(2,1)`, `(2,2)`.
A valid linear extension because `a ≤ b` implies `a` precedes `b`. -/
def gridLinExt : LinearExt (Fin 3 × Fin 3) where
  toFun :=
    { toFun := fun p => ![![0, 1, 3], ![2, 4, 6], ![5, 7, 8]] p.1 p.2
      invFun := ![(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0),
        (1, 2), (2, 1), (2, 2)]
      left_inv := by decide
      right_inv := by decide }
  monotone := by decide

/-- The grid poset `Fin 3 × Fin 3` has width at most `3`: an antichain
meets each first-coordinate fibre (a chain) at most once. -/
theorem grid_hasWidthAtMost_three : HasWidthAtMost (Fin 3 × Fin 3) 3 := by
  intro s hs
  have hinj : Set.InjOn Prod.fst (↑s : Set (Fin 3 × Fin 3)) := by
    intro a ha b hb hfst
    by_contra hne
    rcases le_total a.2 b.2 with hle | hle
    · exact hs ha hb hne (Prod.le_def.mpr ⟨le_of_eq hfst, hle⟩)
    · exact hs hb ha (Ne.symm hne) (Prod.le_def.mpr ⟨le_of_eq hfst.symm, hle⟩)
  calc s.card = (s.image Prod.fst).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 3 := by decide

/-- The grid poset `Fin 3 × Fin 3` is not a chain: `(0,1)` and `(1,0)`
are incomparable. -/
theorem grid_not_chain : ¬ IsChainPoset (Fin 3 × Fin 3) := by
  intro h
  have := h (0, 1) (1, 0)
  revert this
  decide

/-- **Non-vacuity of the commuting-cube verification.** On the genuine
width-3 non-chain poset `Fin 3 × Fin 3`, the anti-diagonal linear
extension carries three BK moves at the pairwise-disjoint positions
`1`, `3`, `6`, and they span a commuting `2×2×2` BK cube. -/
theorem bkCommCube_grid_example :
    ∃ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ : LinearExt (Fin 3 × Fin 3),
      BKCommCube gridLinExt v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ :=
  bkCommCube_of_disjoint gridLinExt
    (p₁ := 1) (p₂ := 3) (p₃ := 6)
    (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide) (by decide) (by decide)

end Example

end OneThird
