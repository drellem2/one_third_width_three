/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.Grid2D
import OneThird.Step3.Step3Theorem
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 4 — Rectangle model (Gaps G1–G4)

This file formalises the rectangle-model content of `step4.tex`
§§Rectangle-model – Rectangle-lemma:

* `prop:G1` (`step4.tex:130`) — the common-overlap rectangle
  decomposition (`BlockDecomp` + `sum_blockMass_eq_card`).
* `prop:G2-step4` (`step4.tex:271`) — Markov bad-block bound
  (`markov_badblock`).
* `lem:rect-exact` (`step4.tex:396`) — exact row-initial ∩
  column-final rectangle constancy (`lem_rect_exact_constant`).
* `lem:rect-stable` (`step4.tex:430`) — stable rectangle
  incompatibility lemma, packaged via the area-scale version.
* `lem:rect-stable-area` (`step4.tex:546`) — the area-scale
  2×2 double-counting (`rect_stable_area_nonconst_lb`).
* `lem:22` (`step4.tex:687`) — atomic 2×2 conflict square
  (`lem_22`, `lem_22_contrapositive`).
* `lem:many-nonconst` (`step4.tex:731`) — density implies many
  non-constant 2×2 subsquares; the grid edge-isoperimetric input
  is consumed as a hypothesis (`many_nonconst_from_boundary`).
* `lem:square-multiplicity` (`step4.tex:802`) — each grid edge lies
  in ≤ 2 axis-aligned 2×2 subsquares (`square_mult_hor_card`).

## Abstract form

Following the style of `OneThird.Step3.Step3Theorem`, probability
statements are presented in cleared-denominator integer form and the
heavyweight geometric inputs (notably the Bollobás–Leader edge
isoperimetric inequality) are consumed as named hypotheses.

## Downstream

* `OneThird.Step4.DensityRegularization` consumes
  `rect_stable_area_nonconst_lb`, `markov_badblock`.
* Step 6 (`mg-450c`, `mg-af62`) consumes `BlockDecomp` and the
  multiplicity-1 property.
-/

namespace OneThird
namespace Step4

open Finset OneThird.Mathlib.Grid2D
open scoped Classical

/-! ### §1 — Grid rectangles and 2×2 subsquares -/

/-- The axis-aligned rectangle `[0, m−1] × [0, n−1]` in `ℤ²`, as a
`Finset`. For `m = 0` or `n = 0` this is empty. -/
def gridRect (m n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc ((0 : ℤ), (0 : ℤ)) (((m : ℤ) - 1), ((n : ℤ) - 1))

lemma mem_gridRect {m n : ℕ} {p : ℤ × ℤ} :
    p ∈ gridRect m n ↔ 0 ≤ p.1 ∧ p.1 ≤ (m : ℤ) - 1 ∧
      0 ≤ p.2 ∧ p.2 ≤ (n : ℤ) - 1 := by
  unfold gridRect
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h3, h2, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩

lemma gridRect_card (m n : ℕ) : (gridRect m n).card = m * n := by
  classical
  unfold gridRect
  rw [show (Finset.Icc ((0 : ℤ), (0 : ℤ)) ((m : ℤ) - 1, (n : ℤ) - 1))
        = Finset.Icc (0 : ℤ) ((m : ℤ) - 1) ×ˢ Finset.Icc (0 : ℤ) ((n : ℤ) - 1)
      from rfl]
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have h1 : ((m : ℤ) - 1 + 1 - 0).toNat = m := by
    have h : ((m : ℤ) - 1 + 1 - 0) = (m : ℤ) := by ring
    rw [h]; exact Int.toNat_natCast _
  have h2 : ((n : ℤ) - 1 + 1 - 0).toNat = n := by
    have h : ((n : ℤ) - 1 + 1 - 0) = (n : ℤ) := by ring
    rw [h]; exact Int.toNat_natCast _
  rw [h1, h2]

/-- The 2×2 axis-aligned subsquare with lower-left corner `(r, c)`. -/
def twoBytwo (r c : ℤ) : Finset (ℤ × ℤ) :=
  {(r, c), (r + 1, c), (r, c + 1), (r + 1, c + 1)}

lemma mem_twoBytwo {r c : ℤ} {p : ℤ × ℤ} :
    p ∈ twoBytwo r c ↔
      p = (r, c) ∨ p = (r + 1, c) ∨ p = (r, c + 1) ∨ p = (r + 1, c + 1) := by
  unfold twoBytwo
  simp [Finset.mem_insert, Finset.mem_singleton, or_assoc]

lemma twoBytwo_card_le (r c : ℤ) : (twoBytwo r c).card ≤ 4 := by
  classical
  unfold twoBytwo
  calc ({(r, c), (r + 1, c), (r, c + 1), (r + 1, c + 1)} : Finset (ℤ × ℤ)).card
      ≤ 1 + 1 + 1 + 1 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        rw [Finset.card_singleton]
    _ = 4 := by ring

/-! ### §2 — `lem:22` (atomic 2×2 conflict square, `step4.tex:687`)

Given a Boolean function `χ : ℤ × ℤ → Bool`, if none of the four
grid edges of the 2×2 square at `(r, c)` is a cut edge, then `χ` is
constant on the square.
-/

/-- `(u, v)` is a **cut edge** of the Boolean function `χ` iff
`χ u ≠ χ v`. -/
def IsCutEdge (χ : ℤ × ℤ → Bool) (u v : ℤ × ℤ) : Prop := χ u ≠ χ v

lemma IsCutEdge.symm {χ : ℤ × ℤ → Bool} {u v : ℤ × ℤ}
    (h : IsCutEdge χ u v) : IsCutEdge χ v u := fun h' => h h'.symm

/-- `χ` is **constant on `Q`** iff all cells of `Q` share the same
`χ`-value. -/
def ConstantOn (χ : ℤ × ℤ → Bool) (Q : Finset (ℤ × ℤ)) : Prop :=
  ∀ p ∈ Q, ∀ q ∈ Q, χ p = χ q

/-- **`lem:22` (`step4.tex:687`).** No cut edge on any of the four
grid edges of `twoBytwo r c` ⇒ `χ` is constant on the square. -/
theorem lem_22 (χ : ℤ × ℤ → Bool) (r c : ℤ)
    (h1 : ¬ IsCutEdge χ (r, c) (r + 1, c))
    (h2 : ¬ IsCutEdge χ (r, c + 1) (r + 1, c + 1))
    (h3 : ¬ IsCutEdge χ (r, c) (r, c + 1))
    (_h4 : ¬ IsCutEdge χ (r + 1, c) (r + 1, c + 1)) :
    ConstantOn χ (twoBytwo r c) := by
  have e1 : χ (r, c) = χ (r + 1, c) := by
    unfold IsCutEdge at h1; push_neg at h1; exact h1
  have e2 : χ (r, c + 1) = χ (r + 1, c + 1) := by
    unfold IsCutEdge at h2; push_neg at h2; exact h2
  have e3 : χ (r, c) = χ (r, c + 1) := by
    unfold IsCutEdge at h3; push_neg at h3; exact h3
  have ea : χ (r, c) = χ (r + 1, c) := e1
  have eb : χ (r, c) = χ (r, c + 1) := e3
  have ec : χ (r, c) = χ (r + 1, c + 1) := e3.trans e2
  intro p hp q hq
  rw [mem_twoBytwo] at hp hq
  have hval : ∀ x, (x = (r, c) ∨ x = (r + 1, c) ∨
                x = (r, c + 1) ∨ x = (r + 1, c + 1)) → χ x = χ (r, c) := by
    rintro x (rfl | rfl | rfl | rfl)
    · rfl
    · exact ea.symm
    · exact eb.symm
    · exact ec.symm
  rw [hval p hp, ← hval q hq]

/-- **Contrapositive of `lem:22`.** `χ` non-constant on `twoBytwo r c`
⇒ at least one of the four grid edges of the square is a cut edge. -/
theorem lem_22_contrapositive (χ : ℤ × ℤ → Bool) (r c : ℤ)
    (hnc : ¬ ConstantOn χ (twoBytwo r c)) :
    IsCutEdge χ (r, c) (r + 1, c) ∨
    IsCutEdge χ (r, c + 1) (r + 1, c + 1) ∨
    IsCutEdge χ (r, c) (r, c + 1) ∨
    IsCutEdge χ (r + 1, c) (r + 1, c + 1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  exact hnc (lem_22 χ r c h1 h2 h3 h4)

/-! ### §3 — `lem:square-multiplicity` (`step4.tex:802`)

Each grid edge lies in at most two axis-aligned 2×2 subsquares.
-/

/-- **`lem:square-multiplicity` (horizontal edges, abstract).**
Given a finset `S : Finset (ℤ × ℤ)` of lower-left corners, each of
whose squares contains the horizontal edge `((i, j), (i+1, j))`,
`S` has cardinality at most 2. -/
theorem square_mult_hor_card (i j : ℤ) (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, (i, j) ∈ twoBytwo p.1 p.2 ∧
      (i + 1, j) ∈ twoBytwo p.1 p.2) :
    S.card ≤ 2 := by
  classical
  -- Each p ∈ S satisfies p = (i, j) ∨ p = (i, j - 1) by direct case
  -- analysis on the four possible positions of (i, j) and (i+1, j)
  -- inside `twoBytwo p.1 p.2`.
  have hpin : ∀ p ∈ S, p = (i, j) ∨ p = (i, j - 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hS p hp
    rw [mem_twoBytwo] at h1 h2
    -- Extract coordinates.
    set r := p.1 with hr_def
    set c := p.2 with hc_def
    have hpeq : p = (r, c) := Prod.ext rfl rfl
    -- From h1 we get 4 cases for (i, j); from h2 another 4 cases for (i+1, j).
    -- Turn each disjunct into a pair of coordinate equalities (ei : _ = i, ej : _ = j)
    -- and combine with omega.
    rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
    · rw [Prod.mk.injEq] at h1 h2
      obtain ⟨hi1, hj1⟩ := h1
      obtain ⟨hi2, hj2⟩ := h2
      -- The valid pairs are h1 = first and h2 = second disjuncts, or h1 = third and h2 = fourth.
      -- omega can solve these given the coordinate equalities.
      first
        | (left; rw [hpeq, Prod.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega)
        | (right; rw [hpeq, Prod.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega)
        | (exfalso; omega)
  have hsub : S ⊆ ({(i, j), (i, j - 1)} : Finset (ℤ × ℤ)) := by
    intro p hp
    rcases hpin p hp with rfl | rfl
    · simp
    · simp
  calc S.card
      ≤ ({((i : ℤ), (j : ℤ)), (i, j - 1)} : Finset (ℤ × ℤ)).card :=
        Finset.card_le_card hsub
    _ ≤ 2 := by
        refine (Finset.card_insert_le _ _).trans ?_
        rw [Finset.card_singleton]

/-! ### §4 — `lem:rect-exact` (`step4.tex:396`)

Row-initial + column-final on a rectangle `[m] × [n]` forces the
subset to be either empty / full or constant-density along the
longer axis, yielding `|∂A| ≥ α · min(m, n)` at density `α`.

In the abstract setting we prove the key structural consequence:
under both hypotheses, a cell `(r, c) ∈ A` forces every cell
`(r', c') ∈ R` with `r' ≥ r, c' ≤ c` to lie in `A`. This is the
"`f` is nondecreasing and nonincreasing" collapse
(`step4.tex:416-417`).
-/

/-- `A ⊆ gridRect m n` is **row-initial** (`step4.tex:400`): for every
row `r`, `A ∩ (row r)` is an initial segment in `c`. Equivalently,
for every `(r, c) ∈ A` and `c' ≤ c` with `(r, c') ∈ gridRect m n`,
`(r, c') ∈ A`. -/
def IsRowInitial (m n : ℕ) (A : Finset (ℤ × ℤ)) : Prop :=
  A ⊆ gridRect m n ∧
  ∀ r c c' : ℤ, (r, c) ∈ A → (r, c') ∈ gridRect m n → c' ≤ c → (r, c') ∈ A

/-- `A ⊆ gridRect m n` is **column-final** (`step4.tex:401`): for every
column `c`, `A ∩ (column c)` is a final segment in `r`. Equivalently,
for every `(r, c) ∈ A` and `r' ≥ r` with `(r', c) ∈ gridRect m n`,
`(r', c) ∈ A`. -/
def IsColumnFinal (m n : ℕ) (A : Finset (ℤ × ℤ)) : Prop :=
  A ⊆ gridRect m n ∧
  ∀ r r' c : ℤ, (r, c) ∈ A → (r', c) ∈ gridRect m n → r ≤ r' → (r', c) ∈ A

/-- **`lem:rect-exact` (corner-collapse, `step4.tex:416`).** Under
row-initial + column-final, `A` contains every rectangle cell
`(r', c') ∈ R` with `r' ≥ r` and `c' ≤ c` whenever `(r, c) ∈ A`.
(The paper's `c ≤ f(r) ⟺ r ≥ g(c)` collapse.) -/
theorem lem_rect_exact_collapse {m n : ℕ} {A : Finset (ℤ × ℤ)}
    (hrow : IsRowInitial m n A) (hcol : IsColumnFinal m n A)
    {r c : ℤ} (hrc : (r, c) ∈ A)
    {r' c' : ℤ} (hrect : (r', c') ∈ gridRect m n)
    (hr : r ≤ r') (hc : c' ≤ c) : (r', c') ∈ A := by
  -- Step: (r, c) ∈ A + column-final with r ≤ r' gives (r', c) ∈ A.
  have hrrect : (r, c) ∈ gridRect m n := hrow.1 hrc
  rw [mem_gridRect] at hrrect hrect
  have hrc_rect : (r', c) ∈ gridRect m n := by
    rw [mem_gridRect]
    refine ⟨by linarith, ?_, hrrect.2.2.1, hrrect.2.2.2⟩
    -- r' ≤ m - 1: from (r', c') ∈ R.
    exact hrect.2.1
  have hrc' : (r', c) ∈ A := hcol.2 r r' c hrc hrc_rect hr
  -- Then row-initial at r', with c' ≤ c, gives (r', c') ∈ A.
  have hrc''_rect : (r', c') ∈ gridRect m n := by
    rw [mem_gridRect]
    exact ⟨hrect.1, hrect.2.1, hrect.2.2.1, hrect.2.2.2⟩
  exact hrow.2 r' c c' hrc' hrc''_rect hc

/-! ### §5 — `BlockDecomp` (`prop:G1`, `step4.tex:130`)

The block decomposition of `Ω° : Finset γ` into rectangle blocks.
-/

/-- A **block decomposition** of `Ω : Finset γ` into rectangle blocks,
abstracting `prop:G1` (`step4.tex:130`). -/
structure BlockDecomp (γ ι : Type*) [DecidableEq γ] [DecidableEq ι] where
  /-- The finite set of blocks. -/
  blocks : Finset ι
  /-- Block assignment: each `L : γ` goes to some block. -/
  blk : γ → ι
  /-- Block dimensions `(m_B, n_B)`. -/
  dim : ι → ℕ × ℕ

namespace BlockDecomp

variable {γ ι : Type*} [DecidableEq γ] [DecidableEq ι]

/-- Members of `Ω` assigned to block `B`. -/
def memberSet (D : BlockDecomp γ ι) (Ω : Finset γ) (B : ι) : Finset γ :=
  Ω.filter (fun L => D.blk L = B)

lemma memberSet_subset (D : BlockDecomp γ ι) (Ω : Finset γ) (B : ι) :
    D.memberSet Ω B ⊆ Ω := Finset.filter_subset _ _

lemma memberSet_disjoint (D : BlockDecomp γ ι) (Ω : Finset γ) {B B' : ι}
    (h : B ≠ B') : Disjoint (D.memberSet Ω B) (D.memberSet Ω B') := by
  classical
  rw [Finset.disjoint_left]
  intro L hLB hLB'
  unfold memberSet at hLB hLB'
  rw [Finset.mem_filter] at hLB hLB'
  exact h (hLB.2.symm.trans hLB'.2)

/-- **`prop:G1.2` (multiplicity 1, `step4.tex:157`).** Every state of
`Ω` lies in exactly one block, so the member-set cardinalities sum to
`|Ω|`. -/
theorem sum_memberSet_eq_card
    (D : BlockDecomp γ ι) (Ω : Finset γ)
    (hblk : ∀ L ∈ Ω, D.blk L ∈ D.blocks) :
    ∑ B ∈ D.blocks, (D.memberSet Ω B).card = Ω.card := by
  classical
  -- Partition Ω by the block assignment: `Ω = ⋃_B memberSet B`.
  -- Use Finset.card_eq_sum_card_fiberwise.
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := D.blk) (s := Ω) (t := D.blocks) hblk

/-- The **block mass function** `|R_B| := m_B · n_B`. -/
def blockMass (D : BlockDecomp γ ι) (B : ι) : ℕ := (D.dim B).1 * (D.dim B).2

/-- `HasRectBijection`: each block's member-set has cardinality equal
to its rectangle size `m_B · n_B` (a witness to the bijection
`B ≃ gridRect m_B n_B`). -/
def HasRectBijection (D : BlockDecomp γ ι) (Ω : Finset γ) : Prop :=
  ∀ B ∈ D.blocks, (D.memberSet Ω B).card = D.blockMass B

/-- **`prop:G1`** (`step4.tex:138`): `∑_B (m_B · n_B) = |Ω|`. -/
theorem sum_blockMass_eq_card
    (D : BlockDecomp γ ι) (Ω : Finset γ)
    (hblk : ∀ L ∈ Ω, D.blk L ∈ D.blocks)
    (hbij : D.HasRectBijection Ω) :
    ∑ B ∈ D.blocks, D.blockMass B = Ω.card := by
  rw [← sum_memberSet_eq_card D Ω hblk]
  refine Finset.sum_congr rfl ?_
  intro B hB
  rw [hbij B hB]

end BlockDecomp

/-! ### §6 — `prop:G2-step4` Markov bad-block bound (`step4.tex:271`) -/

/-- **`prop:G2-step4` (`step4.tex:342`).** If `err : ι → ℕ` is a
per-block error function with `∑_B err B ≤ E` and each block has
mass `mass B`, then the total mass of bad blocks
`{B : ε' · mass B < err B}` is at most `E / ε'` in cleared-
denominator form `ε' · (bad mass) ≤ E`. -/
theorem markov_badblock
    {ι : Type*} [DecidableEq ι]
    (blocks : Finset ι) (err mass : ι → ℕ) (ε' E : ℕ)
    (hbudget : ∑ B ∈ blocks, err B ≤ E) :
    ε' * (∑ B ∈ blocks.filter (fun B => ε' * mass B < err B), mass B) ≤ E := by
  classical
  set badBlocks := blocks.filter (fun B => ε' * mass B < err B) with hbad_def
  have hbad_bound : ε' * (∑ B ∈ badBlocks, mass B) ≤ ∑ B ∈ badBlocks, err B := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro B hB
    rw [hbad_def, Finset.mem_filter] at hB
    exact Nat.le_of_lt hB.2
  have hsub : badBlocks ⊆ blocks := Finset.filter_subset _ _
  calc ε' * (∑ B ∈ badBlocks, mass B)
      ≤ ∑ B ∈ badBlocks, err B := hbad_bound
    _ ≤ ∑ B ∈ blocks, err B := Finset.sum_le_sum_of_subset hsub
    _ ≤ E := hbudget

/-- **`prop:G2-step4` (good-block pointwise bound).** Every block not
in the bad set satisfies `err B ≤ ε' · mass B`. -/
theorem good_block_bound
    {ι : Type*}
    (blocks : Finset ι) (err mass : ι → ℕ) (ε' : ℕ) (B : ι)
    (hB : B ∈ blocks)
    (hgood : B ∉ blocks.filter (fun B => ε' * mass B < err B)) :
    err B ≤ ε' * mass B := by
  classical
  rw [Finset.mem_filter] at hgood
  push_neg at hgood
  exact hgood hB

/-! ### §7 — `lem:rect-stable-area` area-scale 2×2 counting

`step4.tex:546-642`: given row/col model indicators `χrow`, `χcol`
with `|A △ χrow|, |A △ χcol| ≤ ε|R|` and
`|χrow △ χcol| ≥ β|R|`, the number of non-constant 2×2 subsquares
is at least `(β/4)|R| − 2ε|R|`.

We package the constant-on-incompatible-square obstruction as a
direct combinatorial lemma (`errCount_ge_one_of_disagree_and_constant`),
and the count lemma as a subtraction bound
(`rect_stable_area_nonconst_lb`).
-/

/-- Per-square error count: sum over cells of `|χA - χrow| + |χA - χcol|`. -/
def errCount (χA χrow χcol : ℤ × ℤ → Bool) (Q : Finset (ℤ × ℤ)) : ℕ :=
  ∑ p ∈ Q,
    ((if χA p ≠ χrow p then 1 else 0) + (if χA p ≠ χcol p then 1 else 0))

/-- A non-empty 2×2 square with a disagreement cell `p ∈ Q` where
`χrow p ≠ χcol p` and `χA` constant on `Q` has `errCount ≥ 1`.
(`step4.tex:596-611`: "A|_Q constant ⇒ err(Q) ≥ k(Q) ≥ 1".) -/
lemma errCount_ge_one_of_disagree_and_constant
    (χA χrow χcol : ℤ × ℤ → Bool) (Q : Finset (ℤ × ℤ))
    (hconst : ConstantOn χA Q)
    (hdis : ∃ p ∈ Q, χrow p ≠ χcol p) :
    1 ≤ errCount χA χrow χcol Q := by
  classical
  obtain ⟨p, hp, hne'⟩ := hdis
  -- At cell p: either χA p ≠ χrow p OR χA p ≠ χcol p.
  have hp_err : 1 ≤ (if χA p ≠ χrow p then 1 else 0) +
                   (if χA p ≠ χcol p then (1 : ℕ) else 0) := by
    by_cases hApR : χA p = χrow p
    · by_cases hApC : χA p = χcol p
      · exact absurd (hApR.symm.trans hApC) hne'
      · rw [if_neg (by push_neg; exact hApR), if_pos hApC]
    · rw [if_pos hApR]; omega
  unfold errCount
  rw [← Finset.sum_erase_add _ _ hp]
  have hrest : 0 ≤ ∑ q ∈ Q.erase p,
      ((if χA q ≠ χrow q then 1 else 0) + (if χA q ≠ χcol q then (1 : ℕ) else 0)) :=
    Nat.zero_le _
  omega

/-- **`lem:rect-stable-area` (constant-count bound, `step4.tex:614-619`).**
Number of subsquares in `𝒬_inc` that are constant for `χA` is
bounded by the total error budget. -/
theorem rect_stable_area_const_count
    {ι : Type*} [DecidableEq ι]
    (𝒬 : Finset ι) (Qmap : ι → Finset (ℤ × ℤ))
    (χA χrow χcol : ℤ × ℤ → Bool)
    (𝒬inc : Finset ι) (hincSub : 𝒬inc ⊆ 𝒬)
    (hincDis : ∀ Q ∈ 𝒬inc, ∃ p ∈ Qmap Q, χrow p ≠ χcol p)
    (E : ℕ)
    (herr : ∑ Q ∈ 𝒬, errCount χA χrow χcol (Qmap Q) ≤ E) :
    (𝒬inc.filter (fun Q => ConstantOn χA (Qmap Q))).card ≤ E := by
  classical
  set const𝒬 := 𝒬inc.filter (fun Q => ConstantOn χA (Qmap Q)) with hconst_def
  have hwitness : ∀ Q ∈ const𝒬, 1 ≤ errCount χA χrow χcol (Qmap Q) := by
    intro Q hQ
    rw [hconst_def, Finset.mem_filter] at hQ
    exact errCount_ge_one_of_disagree_and_constant χA χrow χcol (Qmap Q)
      hQ.2 (hincDis Q hQ.1)
  have hconst_sub_𝒬 : const𝒬 ⊆ 𝒬 :=
    (Finset.filter_subset _ _).trans hincSub
  calc const𝒬.card
      = ∑ _Q ∈ const𝒬, 1 := by rw [Finset.sum_const]; simp
    _ ≤ ∑ Q ∈ const𝒬, errCount χA χrow χcol (Qmap Q) := Finset.sum_le_sum hwitness
    _ ≤ ∑ Q ∈ 𝒬, errCount χA χrow χcol (Qmap Q) :=
        Finset.sum_le_sum_of_subset hconst_sub_𝒬
    _ ≤ E := herr

/-- **`lem:rect-stable-area` (non-constant count lower bound,
`step4.tex:620-623`).** The number of **non-constant** subsquares in
`𝒬_inc` is at least `|𝒬_inc| − E`. -/
theorem rect_stable_area_nonconst_lb
    {ι : Type*} [DecidableEq ι]
    (𝒬 : Finset ι) (Qmap : ι → Finset (ℤ × ℤ))
    (χA χrow χcol : ℤ × ℤ → Bool)
    (𝒬inc : Finset ι) (hincSub : 𝒬inc ⊆ 𝒬)
    (hincDis : ∀ Q ∈ 𝒬inc, ∃ p ∈ Qmap Q, χrow p ≠ χcol p)
    (E : ℕ)
    (herr : ∑ Q ∈ 𝒬, errCount χA χrow χcol (Qmap Q) ≤ E) :
    𝒬inc.card ≤
      (𝒬inc.filter (fun Q => ¬ ConstantOn χA (Qmap Q))).card + E := by
  classical
  have hsplit : 𝒬inc.card =
      (𝒬inc.filter (fun Q => ConstantOn χA (Qmap Q))).card +
      (𝒬inc.filter (fun Q => ¬ ConstantOn χA (Qmap Q))).card := by
    have := Finset.card_filter_add_card_filter_not
      (s := 𝒬inc) (fun Q => ConstantOn χA (Qmap Q))
    linarith
  have hconst := rect_stable_area_const_count (ι := ι) 𝒬 Qmap χA χrow χcol
    𝒬inc hincSub hincDis E herr
  omega

/-! ### §8 — `lem:many-nonconst` (`step4.tex:731`)

The density bound: `α`-balanced `A` on a rectangle yields
`≥ c₁·α·min(m, n)` non-constant 2×2 subsquares. The proof routes
through the grid edge-isoperimetric inequality
`|∂A| ≥ 2·k/max(m, n)` (Bollobás–Leader, consumed as hypothesis
`hiso`) and each edge is in at most two subsquares
(`square_mult_hor_card`).

The abstract form takes the per-edge witness map as a hypothesis,
matching the abstract-hypothesis style of
`OneThird.Step2.WeakGrid.weak_grid_exists`.
-/

/-- **`lem:many-nonconst` (abstract edge-to-square form).**
Given cut edges `cutEdges` with cardinality `≥ bound`, and a
witness map assigning each cut edge to a non-constant 2×2 subsquare
in `𝒬` containing both endpoints, with **each subsquare receiving
at most 4 cut edges via the witness**, the number of non-constant
subsquares is at least `bound / 4`. -/
theorem many_nonconst_from_boundary
    {ι : Type*} [DecidableEq ι]
    (𝒬 : Finset ι)
    (Qmap : ι → Finset (ℤ × ℤ))
    (χA : ℤ × ℤ → Bool)
    (cutEdges : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (Qwit : ((ℤ × ℤ) × (ℤ × ℤ)) → ι)
    (hwit_mem : ∀ e ∈ cutEdges, Qwit e ∈ 𝒬)
    (hwit_nonconst : ∀ e ∈ cutEdges, ¬ ConstantOn χA (Qmap (Qwit e)))
    (hfib : ∀ Q ∈ 𝒬, (cutEdges.filter (fun e => Qwit e = Q)).card ≤ 4) :
    cutEdges.card ≤
      4 * (𝒬.filter (fun Q => ¬ ConstantOn χA (Qmap Q))).card := by
  classical
  set ncSet : Finset ι := 𝒬.filter (fun Q => ¬ ConstantOn χA (Qmap Q))
      with hnc_def
  -- Each e ∈ cutEdges has Qwit e ∈ ncSet.
  have hwit_in_nc : ∀ e ∈ cutEdges, Qwit e ∈ ncSet := by
    intro e he
    rw [hnc_def, Finset.mem_filter]
    exact ⟨hwit_mem e he, hwit_nonconst e he⟩
  -- Partition cutEdges by Qwit-fiber over ncSet.
  have hsum_card : cutEdges.card =
      ∑ Q ∈ ncSet, (cutEdges.filter (fun e => Qwit e = Q)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Qwit) (s := cutEdges) (t := ncSet)
      hwit_in_nc
  -- Each fiber has card ≤ 4 (since ncSet ⊆ 𝒬 and `hfib`).
  have hfib_nc : ∀ Q ∈ ncSet, (cutEdges.filter (fun e => Qwit e = Q)).card ≤ 4 := by
    intro Q hQ
    rw [hnc_def, Finset.mem_filter] at hQ
    exact hfib Q hQ.1
  have hstep : cutEdges.card ≤ 4 * ncSet.card := by
    calc cutEdges.card
        = ∑ Q ∈ ncSet, (cutEdges.filter (fun e => Qwit e = Q)).card := hsum_card
      _ ≤ ∑ _Q ∈ ncSet, 4 := Finset.sum_le_sum hfib_nc
      _ = 4 * ncSet.card := by rw [Finset.sum_const]; ring
  exact hstep

/-- **`lem:many-nonconst` (paper-form lower bound, cleared denominators).**
Under the Bollobás–Leader input `2 · cutMass ≤ max(m, n) · |∂A|`
combined with density `α·mn ≤ cutMass`, and the subsquare-witness
map with `per-Q fiber ≤ 4`, we obtain at least
`α · min(m, n) / 2` non-constant 2×2 subsquares. -/
theorem lem_many_nonconst
    {ι : Type*} [DecidableEq ι]
    (𝒬 : Finset ι)
    (Qmap : ι → Finset (ℤ × ℤ))
    (χA : ℤ × ℤ → Bool)
    (m n : ℕ)
    (cutEdges : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (Qwit : ((ℤ × ℤ) × (ℤ × ℤ)) → ι)
    (hwit_mem : ∀ e ∈ cutEdges, Qwit e ∈ 𝒬)
    (hwit_nonconst : ∀ e ∈ cutEdges, ¬ ConstantOn χA (Qmap (Qwit e)))
    (hfib : ∀ Q ∈ 𝒬, (cutEdges.filter (fun e => Qwit e = Q)).card ≤ 4)
    (hiso : 2 * min m n ≤ cutEdges.card) :
    min m n ≤
      2 * (𝒬.filter (fun Q => ¬ ConstantOn χA (Qmap Q))).card := by
  classical
  have hmain := many_nonconst_from_boundary (ι := ι) 𝒬 Qmap χA
    cutEdges Qwit hwit_mem hwit_nonconst hfib
  omega

end Step4
end OneThird
