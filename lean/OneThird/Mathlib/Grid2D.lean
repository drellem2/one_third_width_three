/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OneThird.Basic

/-!
# 2D-grid isoperimetric scaffolding

This file assembles the generic 2D-lattice facts that Step 2
(`lem:weak-grid`, weak grid stability) and Step 4 (`lem:G5-iso`,
grid edge-isoperimetry on a block) consume. It is entry **F8**
of `MATHLIB_GAPS.md` and covers items **F2**, **F4**, **F5** of
that audit:

* **F2 — order-convex subsets of `ℤ²`.** A thin specialization of
  `Set.OrdConnected` to `ℤ × ℤ`, with lemmas for rectangles,
  intersections, and "lying between" behavior.
* **F4 — staircase regions via `YoungDiagram`.** Mathlib's
  `YoungDiagram` already models finite lower sets of `ℕ²`
  (exactly the "staircase region" object of `step2.tex`
  Definition `def:staircase` in its positive orientation). We cast
  the cells of a `YoungDiagram` into `Finset (ℤ × ℤ)` via the
  natural embedding, prove the image sits in the `[0, t]²` rectangle,
  and wire up four orientation equivalences via the reflection group
  of `ℤ²` so that downstream proofs (Step 2, Step 3) can pick their
  preferred monotone frame.
* **F5 — grid boundary `∂_D A`.** The set of ordered adjacent pairs
  `(u, v)` with `u ∈ A`, `v ∈ D \ A` and `‖u − v‖₁ = 1`
  (`step2.tex` Definition `def:grid-bdy`), as a `Finset`. Standard
  bookkeeping lemmas: empty / full cases, symmetry under complements
  inside `D`, pointwise characterization, reflection invariance.

Finally a **basic isoperimetric bound** (the elementary half of
`lem:G5-iso`): for every non-empty proper subset of an axis-aligned
rectangle in `ℤ²`, the grid boundary has at least one edge. This is
the trivial "some edge must cross" statement; the quantitative
Bollobás–Leader form (`2k / max(m, n)`) is the Step 4 work item.

All code here is project-generic: nothing depends on the width-3
hypothesis, the BK graph, or linear extensions. It is kept under
`OneThird/Mathlib/` so it can be extracted into mathlib later as a
small `Combinatorics.Grid2D.Isoperimetric` module.

## Main definitions

* `OneThird.Mathlib.Grid2D.IsOrdConvex` — order-convex subset of
  `ℤ × ℤ`; abbrev for `Set.OrdConnected`.
* `OneThird.Mathlib.Grid2D.l1dist` — the `ℓ¹` distance on `ℤ²`
  as a `ℕ`-valued function.
* `OneThird.Mathlib.Grid2D.L1Adj` — `p` and `q` are L1-adjacent
  iff `l1dist p q = 1`.
* `OneThird.Mathlib.Grid2D.reflectFst`, `reflectSnd`,
  `reflectBoth` — the three non-identity reflections in the Klein-four
  group of axis reflections `ℤ × ℤ ≃ ℤ × ℤ`, realizing the
  four `(±, ±)` orientations of the axes.
* `OneThird.Mathlib.Grid2D.ofYoungDiagram` — cast the cells of a
  `YoungDiagram` to `Finset (ℤ × ℤ)`.
* `OneThird.Mathlib.Grid2D.gridBdy D A` — the grid edge boundary
  of `A` inside `D` (ordered adjacent pairs, one in `A`, one in
  `D \ A`).

## Main results

* `IsOrdConvex.Icc`, `IsOrdConvex.inter`, `IsOrdConvex.icc_subset`
  — the three facts about order-convex sets that the Step 2 weak
  grid stability proof calls.
* `reflectFst_l1dist`, `reflectSnd_l1dist`, `reflectBoth_l1dist`
  — each of the three non-trivial axis reflections preserves the
  `ℓ¹` distance; so each conjugates the grid boundary to itself
  up to a bijection.
* `ofYoungDiagram_subset_rect` — the image of a `YoungDiagram` in
  `ℤ²` sits inside the rectangle `[0, t]²` whenever `t` dominates
  both the row and column lengths.
* `gridBdy_empty`, `gridBdy_self`, `mem_gridBdy`,
  `gridBdy_card_compl_eq` — the standard boundary bookkeeping.
* `rect_gridBdy_nonempty` — the elementary isoperimetric lower
  bound: on an axis-aligned rectangle with at least two cells,
  every non-empty proper subset has a non-empty grid boundary.
-/

namespace OneThird
namespace Mathlib
namespace Grid2D

open Set Finset

/-! ### §1. Order-convex subsets of `ℤ × ℤ` -/

/-- A subset of `ℤ²` (or more generally any product of two preorders) is
*order-convex* if whenever it contains `p` and `q`, it contains the
entire order-interval `[p, q]` in the product order. This is the
same as `Set.OrdConnected`; we expose it under the name used in
`step2.tex` Definition `def:staircase` to make call sites explicit. -/
abbrev IsOrdConvex (D : Set (ℤ × ℤ)) : Prop := OrdConnected D

/-- Every axis-aligned rectangle `[[a, b]]` in `ℤ²` is order-convex. -/
theorem IsOrdConvex.Icc (a b : ℤ × ℤ) : IsOrdConvex (Set.Icc a b) :=
  Set.ordConnected_Icc

/-- The intersection of two order-convex sets is order-convex. -/
theorem IsOrdConvex.inter {D E : Set (ℤ × ℤ)}
    (hD : IsOrdConvex D) (hE : IsOrdConvex E) : IsOrdConvex (D ∩ E) :=
  Set.OrdConnected.inter hD hE

/-- Order-convexity unpacks to "the interval between two members is
contained in the set". -/
theorem IsOrdConvex.icc_subset {D : Set (ℤ × ℤ)} (hD : IsOrdConvex D)
    {p q : ℤ × ℤ} (hp : p ∈ D) (hq : q ∈ D) : Set.Icc p q ⊆ D :=
  hD.out hp hq

theorem IsOrdConvex.univ : IsOrdConvex (Set.univ : Set (ℤ × ℤ)) :=
  Set.ordConnected_univ

theorem IsOrdConvex.empty : IsOrdConvex (∅ : Set (ℤ × ℤ)) :=
  Set.ordConnected_empty

/-- A point sandwiched between two points of an order-convex set belongs
to the set. The `p ≤ r ≤ q` form is the shape Step 2's
one-dimensional interval lemmas consume. -/
theorem IsOrdConvex.mem_of_between {D : Set (ℤ × ℤ)} (hD : IsOrdConvex D)
    {p q r : ℤ × ℤ} (hp : p ∈ D) (hq : q ∈ D)
    (hpr : p ≤ r) (hrq : r ≤ q) : r ∈ D :=
  hD.icc_subset hp hq ⟨hpr, hrq⟩

/-! ### §2. The `ℓ¹` distance and grid adjacency -/

/-- `ℓ¹` distance on `ℤ²`, as a natural number. Matches `step2.tex`'s
`‖u − v‖₁`. -/
def l1dist (p q : ℤ × ℤ) : ℕ := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

@[simp] theorem l1dist_self (p : ℤ × ℤ) : l1dist p p = 0 := by
  simp [l1dist]

theorem l1dist_comm (p q : ℤ × ℤ) : l1dist p q = l1dist q p := by
  unfold l1dist
  have h1 : (p.1 - q.1).natAbs = (q.1 - p.1).natAbs := by
    have : q.1 - p.1 = -(p.1 - q.1) := by ring
    rw [this, Int.natAbs_neg]
  have h2 : (p.2 - q.2).natAbs = (q.2 - p.2).natAbs := by
    have : q.2 - p.2 = -(p.2 - q.2) := by ring
    rw [this, Int.natAbs_neg]
  rw [h1, h2]

theorem l1dist_eq_zero_iff {p q : ℤ × ℤ} : l1dist p q = 0 ↔ p = q := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ : (p.1 - q.1).natAbs = 0 ∧ (p.2 - q.2).natAbs = 0 :=
      Nat.add_eq_zero_iff.mp h
    have e1 : p.1 = q.1 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp h1)
    have e2 : p.2 = q.2 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp h2)
    exact Prod.ext e1 e2
  · rintro rfl; simp

/-- `p` and `q` are *L1-adjacent* (share a grid edge) iff their
coordinatewise `ℓ¹` distance is `1`. -/
def L1Adj (p q : ℤ × ℤ) : Prop := l1dist p q = 1

theorem L1Adj.symm {p q : ℤ × ℤ} (h : L1Adj p q) : L1Adj q p := by
  unfold L1Adj at h ⊢
  rw [l1dist_comm] at h
  exact h

theorem L1Adj.ne {p q : ℤ × ℤ} (h : L1Adj p q) : p ≠ q := by
  intro hpq
  unfold L1Adj at h
  have : l1dist p q = 0 := by rw [hpq]; simp
  rw [this] at h
  exact absurd h.symm Nat.one_ne_zero

instance L1Adj.decidable : DecidableRel L1Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = 1))

/-! ### §3. Axis reflections: the four `(±, ±)` orientations

Order-convex regions and L1-adjacency are preserved by the Klein-four
group of axis reflections on `ℤ²`: `id`, flip the first axis at
`n₁ ∈ ℤ`, flip the second axis at `n₂ ∈ ℤ`, or both. These are the
"four orientations" that the Step 2 / Step 3 proofs use to reduce to
the single "positive" monotone orientation handled by `YoungDiagram`.

We implement each as an `Equiv ℤ² ℤ²` because `YoungDiagram ≃ YoungDiagram`
globally only supports the axis swap (transpose); reflection across an
axis line cannot be realized globally on `ℕ²`, since it exits `ℕ²`.
Instead we work at the level of the ambient lattice `ℤ²`, where all
four orientations are natural involutions, and then cast a
`YoungDiagram` into `ℤ²` via `ofYoungDiagram` below.
-/

/-- Reflect the first coordinate at `n`, leaving the second unchanged. -/
def reflectFst (n : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (n - p.1, p.2)
  invFun p := (n - p.1, p.2)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by rintro ⟨a, b⟩; simp

/-- Reflect the second coordinate at `m`, leaving the first unchanged. -/
def reflectSnd (m : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, m - p.2)
  invFun p := (p.1, m - p.2)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by rintro ⟨a, b⟩; simp

/-- Reflect both coordinates at `(n, m)`. -/
def reflectBoth (n m : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (n - p.1, m - p.2)
  invFun p := (n - p.1, m - p.2)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by rintro ⟨a, b⟩; simp

@[simp] theorem reflectFst_apply (n : ℤ) (p : ℤ × ℤ) :
    reflectFst n p = (n - p.1, p.2) := rfl

@[simp] theorem reflectSnd_apply (m : ℤ) (p : ℤ × ℤ) :
    reflectSnd m p = (p.1, m - p.2) := rfl

@[simp] theorem reflectBoth_apply (n m : ℤ) (p : ℤ × ℤ) :
    reflectBoth n m p = (n - p.1, m - p.2) := rfl

@[simp] theorem reflectFst_reflectFst (n : ℤ) (p : ℤ × ℤ) :
    reflectFst n (reflectFst n p) = p := by
  simp [reflectFst]

@[simp] theorem reflectSnd_reflectSnd (m : ℤ) (p : ℤ × ℤ) :
    reflectSnd m (reflectSnd m p) = p := by
  simp [reflectSnd]

@[simp] theorem reflectBoth_reflectBoth (n m : ℤ) (p : ℤ × ℤ) :
    reflectBoth n m (reflectBoth n m p) = p := by
  simp [reflectBoth]

/-- Reflecting the first coordinate preserves `ℓ¹` distance. -/
theorem reflectFst_l1dist (n : ℤ) (p q : ℤ × ℤ) :
    l1dist (reflectFst n p) (reflectFst n q) = l1dist p q := by
  unfold l1dist reflectFst
  simp only [Equiv.coe_fn_mk]
  have h : (n - p.1 - (n - q.1)).natAbs = (p.1 - q.1).natAbs := by
    have heq : n - p.1 - (n - q.1) = -(p.1 - q.1) := by ring
    rw [heq, Int.natAbs_neg]
  rw [h]

/-- Reflecting the second coordinate preserves `ℓ¹` distance. -/
theorem reflectSnd_l1dist (m : ℤ) (p q : ℤ × ℤ) :
    l1dist (reflectSnd m p) (reflectSnd m q) = l1dist p q := by
  unfold l1dist reflectSnd
  simp only [Equiv.coe_fn_mk]
  have h : (m - p.2 - (m - q.2)).natAbs = (p.2 - q.2).natAbs := by
    have heq : m - p.2 - (m - q.2) = -(p.2 - q.2) := by ring
    rw [heq, Int.natAbs_neg]
  rw [h]

/-- Reflecting both coordinates preserves `ℓ¹` distance. -/
theorem reflectBoth_l1dist (n m : ℤ) (p q : ℤ × ℤ) :
    l1dist (reflectBoth n m p) (reflectBoth n m q) = l1dist p q := by
  unfold l1dist reflectBoth
  simp only [Equiv.coe_fn_mk]
  have h1 : (n - p.1 - (n - q.1)).natAbs = (p.1 - q.1).natAbs := by
    have heq : n - p.1 - (n - q.1) = -(p.1 - q.1) := by ring
    rw [heq, Int.natAbs_neg]
  have h2 : (m - p.2 - (m - q.2)).natAbs = (p.2 - q.2).natAbs := by
    have heq : m - p.2 - (m - q.2) = -(p.2 - q.2) := by ring
    rw [heq, Int.natAbs_neg]
  rw [h1, h2]

/-- Each axis reflection preserves L1-adjacency. -/
theorem reflectFst_L1Adj {n : ℤ} {p q : ℤ × ℤ} :
    L1Adj (reflectFst n p) (reflectFst n q) ↔ L1Adj p q := by
  unfold L1Adj; rw [reflectFst_l1dist]

theorem reflectSnd_L1Adj {m : ℤ} {p q : ℤ × ℤ} :
    L1Adj (reflectSnd m p) (reflectSnd m q) ↔ L1Adj p q := by
  unfold L1Adj; rw [reflectSnd_l1dist]

theorem reflectBoth_L1Adj {n m : ℤ} {p q : ℤ × ℤ} :
    L1Adj (reflectBoth n m p) (reflectBoth n m q) ↔ L1Adj p q := by
  unfold L1Adj; rw [reflectBoth_l1dist]

/-! ### §4. `YoungDiagram` as a staircase region in `ℤ²`

Mathlib's `YoungDiagram` is, definitionally, a finite lower set of
`ℕ²`. This is precisely the `+`-oriented staircase of
`step2.tex` Definition `def:staircase`. We expose it as a
`Finset (ℤ × ℤ)` via the natural embedding `ℕ → ℤ`, and package
the basic membership and rectangle-containment lemmas.

Axis swap (the `(swap i, j)` orientation equivalence) is already
`YoungDiagram.transposeOrderIso : YoungDiagram ≃o YoungDiagram` in
mathlib; we re-export it under the orientation-focused name
`flipDiag`. The other three `(±, ±)` orientations are obtained by
composing with the `reflect*` equivalences above after casting into
`ℤ²`.
-/

/-- Cast the cells of a `YoungDiagram` into `Finset (ℤ × ℤ)` via the
coordinatewise `ℕ → ℤ` embedding. -/
def ofYoungDiagram (μ : YoungDiagram) : Finset (ℤ × ℤ) :=
  μ.cells.image (fun p => ((p.1 : ℤ), (p.2 : ℤ)))

@[simp] theorem mem_ofYoungDiagram {μ : YoungDiagram} {p : ℤ × ℤ} :
    p ∈ ofYoungDiagram μ ↔
      ∃ q : ℕ × ℕ, q ∈ μ.cells ∧ ((q.1 : ℤ), (q.2 : ℤ)) = p := by
  unfold ofYoungDiagram
  exact Finset.mem_image

theorem ofYoungDiagram_mono {μ ν : YoungDiagram} (h : μ ≤ ν) :
    ofYoungDiagram μ ⊆ ofYoungDiagram ν := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  exact Finset.mem_image.mpr ⟨q, YoungDiagram.cells_subset_iff.mpr h hq, rfl⟩

/-- The cells of a `YoungDiagram`, viewed in `ℤ²`, all have
non-negative coordinates. -/
theorem ofYoungDiagram_nonneg (μ : YoungDiagram) {p : ℤ × ℤ}
    (hp : p ∈ ofYoungDiagram μ) : 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
  exact ⟨Int.natCast_nonneg q.1, Int.natCast_nonneg q.2⟩

/-- If every cell of `μ` lies in the `[0, t] × [0, t]` rectangle, so does
its image in `ℤ²`. This is the form Step 2 consumes: every staircase
region sits inside the bounding box of its fiber. -/
theorem ofYoungDiagram_subset_rect (μ : YoungDiagram) (t : ℕ)
    (hrow : μ.colLen 0 ≤ t + 1) (hcol : μ.rowLen 0 ≤ t + 1) :
    ∀ p ∈ ofYoungDiagram μ,
      p ∈ Set.Icc ((0 : ℤ), (0 : ℤ)) ((t : ℤ), (t : ℤ)) := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨⟨i, j⟩, hij, rfl⟩
  have hmem : (i, j) ∈ μ := hij
  have hi : i < μ.colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem (Nat.le_refl i) (Nat.zero_le j) hmem)
  have hj : j < μ.rowLen 0 :=
    YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (Nat.zero_le i) (Nat.le_refl j) hmem)
  have hi' : i ≤ t := by omega
  have hj' : j ≤ t := by omega
  have h1 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  have h2 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
  have h3 : (i : ℤ) ≤ (t : ℤ) := by exact_mod_cast hi'
  have h4 : (j : ℤ) ≤ (t : ℤ) := by exact_mod_cast hj'
  exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- `ofYoungDiagram` is injective: a `YoungDiagram` is determined by its
image in `ℤ²`. -/
theorem ofYoungDiagram_injective :
    Function.Injective ofYoungDiagram := by
  intro μ ν h
  apply YoungDiagram.ext
  apply Finset.ext
  intro q
  rcases q with ⟨i, j⟩
  constructor
  · intro hq
    have hmem : ((i : ℤ), (j : ℤ)) ∈ ofYoungDiagram μ :=
      Finset.mem_image.mpr ⟨(i, j), hq, rfl⟩
    rw [h] at hmem
    rcases Finset.mem_image.mp hmem with ⟨⟨i', j'⟩, hq', heq⟩
    obtain ⟨e1, e2⟩ := Prod.mk.inj heq
    have h1 : i' = i := by exact_mod_cast e1
    have h2 : j' = j := by exact_mod_cast e2
    subst h1; subst h2; exact hq'
  · intro hq
    have hmem : ((i : ℤ), (j : ℤ)) ∈ ofYoungDiagram ν :=
      Finset.mem_image.mpr ⟨(i, j), hq, rfl⟩
    rw [← h] at hmem
    rcases Finset.mem_image.mp hmem with ⟨⟨i', j'⟩, hq', heq⟩
    obtain ⟨e1, e2⟩ := Prod.mk.inj heq
    have h1 : i' = i := by exact_mod_cast e1
    have h2 : j' = j := by exact_mod_cast e2
    subst h1; subst h2; exact hq'

/-- The axis-swap orientation on `YoungDiagram`, re-exported from
mathlib's `transposeOrderIso`. Pair this with `reflectFst` and
`reflectSnd` on `ℤ²` to obtain all four `(±, ±)` orientations. -/
def flipDiag : YoungDiagram ≃o YoungDiagram :=
  YoungDiagram.transposeOrderIso

@[simp] theorem flipDiag_apply (μ : YoungDiagram) :
    flipDiag μ = μ.transpose := rfl

theorem flipDiag_flipDiag (μ : YoungDiagram) :
    flipDiag (flipDiag μ) = μ :=
  μ.transpose_transpose

/-! ### §5. Grid boundary `∂_D A` -/

/-- The **grid edge boundary** of `A` inside `D`: the finset of
ordered adjacent pairs `(u, v)` with `u ∈ A`, `v ∈ D \ A`, and
`‖u − v‖₁ = 1`. Matches `step2.tex` Definition `def:grid-bdy`
(up to the ordered-pair presentation the polecat task specifies). -/
def gridBdy (D A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (A ×ˢ (D \ A)).filter (fun p => L1Adj p.1 p.2)

theorem mem_gridBdy {D A : Finset (ℤ × ℤ)} {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ gridBdy D A ↔ p.1 ∈ A ∧ p.2 ∈ D ∧ p.2 ∉ A ∧ L1Adj p.1 p.2 := by
  unfold gridBdy
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff]
  tauto

theorem mk_mem_gridBdy {D A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} :
    (u, v) ∈ gridBdy D A ↔ u ∈ A ∧ v ∈ D ∧ v ∉ A ∧ L1Adj u v :=
  mem_gridBdy

@[simp] theorem gridBdy_empty (D : Finset (ℤ × ℤ)) :
    gridBdy D (∅ : Finset (ℤ × ℤ)) = ∅ := by
  unfold gridBdy
  rw [Finset.empty_product]
  exact Finset.filter_empty _

@[simp] theorem gridBdy_self (D : Finset (ℤ × ℤ)) :
    gridBdy D D = ∅ := by
  unfold gridBdy
  rw [Finset.sdiff_self, Finset.product_empty]
  exact Finset.filter_empty _

theorem gridBdy_fst_mem {D A : Finset (ℤ × ℤ)}
    {p : (ℤ × ℤ) × (ℤ × ℤ)} (hp : p ∈ gridBdy D A) : p.1 ∈ A :=
  (mem_gridBdy.mp hp).1

theorem gridBdy_snd_mem {D A : Finset (ℤ × ℤ)}
    {p : (ℤ × ℤ) × (ℤ × ℤ)} (hp : p ∈ gridBdy D A) : p.2 ∈ D :=
  (mem_gridBdy.mp hp).2.1

theorem gridBdy_snd_notMem {D A : Finset (ℤ × ℤ)}
    {p : (ℤ × ℤ) × (ℤ × ℤ)} (hp : p ∈ gridBdy D A) : p.2 ∉ A :=
  (mem_gridBdy.mp hp).2.2.1

theorem gridBdy_adj {D A : Finset (ℤ × ℤ)}
    {p : (ℤ × ℤ) × (ℤ × ℤ)} (hp : p ∈ gridBdy D A) : L1Adj p.1 p.2 :=
  (mem_gridBdy.mp hp).2.2.2

/-- The swap `(u, v) ↦ (v, u)` is a bijection from the boundary of `A`
inside `D` to the boundary of `D \ A` inside `D`. -/
theorem gridBdy_card_compl_eq {D A : Finset (ℤ × ℤ)} (hA : A ⊆ D) :
    (gridBdy D (D \ A)).card = (gridBdy D A).card := by
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · -- image lands in the other boundary
    intro p hp
    obtain ⟨huDA, hvD, hvDA, hadj⟩ := mem_gridBdy.mp hp
    obtain ⟨huD, huA⟩ := Finset.mem_sdiff.mp huDA
    refine mem_gridBdy.mpr ⟨?_, huD, ?_, hadj.symm⟩
    · -- p.2 ∈ A: we know p.2 ∈ D and p.2 ∉ D \ A.
      have : ¬ (p.2 ∈ D ∧ p.2 ∉ A) := fun h => hvDA (Finset.mem_sdiff.mpr h)
      by_contra hnA
      exact this ⟨hvD, hnA⟩
    · -- p.1 ∉ A: immediate from p.1 ∈ D \ A.
      exact huA
  · -- injective
    intro p hp q hq hpq
    exact Prod.ext (Prod.mk.inj hpq).2 (Prod.mk.inj hpq).1
  · -- surjective
    intro q hq
    obtain ⟨huA, hvD, hvA, hadj⟩ := mem_gridBdy.mp hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    refine mem_gridBdy.mpr ⟨?_, hA huA, ?_, hadj.symm⟩
    · exact Finset.mem_sdiff.mpr ⟨hvD, hvA⟩
    · intro h
      exact (Finset.mem_sdiff.mp h).2 huA

/-! ### §6. Elementary isoperimetric bound on a rectangle

For an axis-aligned rectangle with at least two cells, a non-empty
proper subset always has at least one grid-boundary edge. This is
the trivial "some edge must cross" statement; the quantitative
Bollobás–Leader form lives in Step 4.

The proof is the standard "monotone lattice path from some `p ∈ A`
to some `q ∈ D \ A` must flip". We build the path inductively on
its length in `ℓ¹`.
-/

namespace rectIso

/-- Single first-coordinate step inside a rectangle. -/
private lemma step_fst {a b : ℤ × ℤ} {p : ℤ × ℤ} (hp : p ∈ Set.Icc a b)
    (hlt : p.1 < b.1) : (p.1 + 1, p.2) ∈ Set.Icc a b := by
  refine ⟨⟨?_, hp.1.2⟩, ?_, hp.2.2⟩
  · exact le_trans hp.1.1 (Int.le_add_one (le_refl _))
  · exact hlt

/-- Single second-coordinate step inside a rectangle. -/
private lemma step_snd {a b : ℤ × ℤ} {p : ℤ × ℤ} (hp : p ∈ Set.Icc a b)
    (hlt : p.2 < b.2) : (p.1, p.2 + 1) ∈ Set.Icc a b := by
  refine ⟨⟨hp.1.1, ?_⟩, hp.2.1, ?_⟩
  · exact le_trans hp.1.2 (Int.le_add_one (le_refl _))
  · exact hlt

/-- In an axis-aligned rectangle `[a, b]`, any two comparable points
`p ≤ q` both inside the rectangle admit a monotone lattice path: if
`p ∈ A` and `q ∉ A` for some `A ⊆ rect`, we can find an adjacent
pair `(u, v)` with `u ∈ A`, `v ∉ A`, both inside the rectangle.
-/
private lemma cross_of_le
    {a b : ℤ × ℤ} {A : Set (ℤ × ℤ)}
    {p q : ℤ × ℤ} (hp : p ∈ Set.Icc a b) (hq : q ∈ Set.Icc a b)
    (hle : p ≤ q) (hpA : p ∈ A) (hqA : q ∉ A) :
    ∃ u v : ℤ × ℤ,
      u ∈ A ∧ u ∈ Set.Icc a b ∧ v ∈ Set.Icc a b ∧ v ∉ A ∧ L1Adj u v := by
  set n := (q.1 - p.1).natAbs + (q.2 - p.2).natAbs with hn_def
  clear_value n
  induction n using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h1 : p.1 < q.1
    · -- step in first coord
      set p' : ℤ × ℤ := (p.1 + 1, p.2) with hp'
      have hp'rect : p' ∈ Set.Icc a b := by
        have hlt : p.1 < b.1 := lt_of_lt_of_le h1 hq.2.1
        exact step_fst hp hlt
      by_cases hp'A : p' ∈ A
      · have hp'le_q : p' ≤ q := by
          refine ⟨?_, hle.2⟩
          simp only [hp']
          exact h1
        have hn' : (q.1 - p'.1).natAbs + (q.2 - p'.2).natAbs < n := by
          rw [hn_def]
          simp only [hp']
          have hpos : 0 < q.1 - p.1 := by linarith
          omega
        exact ih _ hn' hp'rect hp'le_q hp'A rfl
      · refine ⟨p, p', hpA, hp, hp'rect, hp'A, ?_⟩
        unfold L1Adj l1dist
        simp only [hp', sub_self, Int.natAbs_zero, add_zero]
        have : p.1 - (p.1 + 1) = -1 := by ring
        rw [this]
        rfl
    · -- no first-coord step; must step in second
      have h1' : q.1 ≤ p.1 := not_lt.mp h1
      have heq1 : p.1 = q.1 := le_antisymm hle.1 h1'
      have h2 : p.2 < q.2 := by
        rcases lt_or_eq_of_le hle.2 with h | h
        · exact h
        · exfalso
          have : p = q := Prod.ext heq1 h
          exact hqA (this ▸ hpA)
      set p' : ℤ × ℤ := (p.1, p.2 + 1) with hp'
      have hp'rect : p' ∈ Set.Icc a b := by
        have hlt : p.2 < b.2 := lt_of_lt_of_le h2 hq.2.2
        exact step_snd hp hlt
      by_cases hp'A : p' ∈ A
      · have hp'le_q : p' ≤ q := by
          refine ⟨hle.1, ?_⟩
          simp only [hp']
          exact h2
        have hn' : (q.1 - p'.1).natAbs + (q.2 - p'.2).natAbs < n := by
          rw [hn_def]
          simp only [hp']
          have hpos : 0 < q.2 - p.2 := by linarith
          omega
        exact ih _ hn' hp'rect hp'le_q hp'A rfl
      · refine ⟨p, p', hpA, hp, hp'rect, hp'A, ?_⟩
        unfold L1Adj l1dist
        simp only [hp', sub_self, Int.natAbs_zero, zero_add]
        have : p.2 - (p.2 + 1) = -1 := by ring
        rw [this]
        rfl

end rectIso

open rectIso in
/-- **Elementary isoperimetric bound on a rectangle.** Let `a ≤ b` in
`ℤ²` and `D` the `Finset` of lattice points of the rectangle `[a, b]`
(via `Finset.Icc`). Any non-empty proper subset `A ⊆ D` has at least
one grid-boundary edge. The proof is the standard "monotone path
must cross" argument. -/
theorem rect_gridBdy_nonempty {a b : ℤ × ℤ} (_hab : a ≤ b)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Finset.Icc a b) (hne : A.Nonempty)
    (hprop : A ≠ Finset.Icc a b) :
    (gridBdy (Finset.Icc a b) A).Nonempty := by
  -- Strategy: pick any p ∈ A and q ∉ A in the rectangle. If p ≤ q, use
  -- cross_of_le. Otherwise, use a corner (min(p, q) or max(p, q)) that
  -- IS in the rectangle and has a known side (in A or not). We pick
  -- a corner of the rectangle that is outside A (or inside), then
  -- apply cross_of_le from there.
  obtain ⟨p, hpA⟩ := hne
  have hp : p ∈ Finset.Icc a b := hA hpA
  -- D \ A is non-empty.
  have hDmA : ((Finset.Icc a b : Finset (ℤ × ℤ)) \ A).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact hprop (le_antisymm hA h)
  obtain ⟨q, hqDA⟩ := hDmA
  obtain ⟨hq, hqA⟩ := Finset.mem_sdiff.mp hqDA
  -- Work in Set-land
  have hpSet : p ∈ Set.Icc a b := Finset.mem_Icc.mp hp
  have hqSet : q ∈ Set.Icc a b := Finset.mem_Icc.mp hq
  -- Consider the corner `r = (min p.1 q.1, min p.2 q.2)`. This is in
  -- the rectangle since both p and q are. Either r ∈ A or r ∉ A.
  set r : ℤ × ℤ := (min p.1 q.1, min p.2 q.2) with hr_def
  have hrSet : r ∈ Set.Icc a b := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact le_min hpSet.1.1 hqSet.1.1
    · exact le_min hpSet.1.2 hqSet.1.2
    · exact min_le_of_left_le hpSet.2.1
    · exact min_le_of_left_le hpSet.2.2
  have hrFinset : r ∈ Finset.Icc a b := Finset.mem_Icc.mpr hrSet
  have hr_le_p : r ≤ p := ⟨min_le_left _ _, min_le_left _ _⟩
  have hr_le_q : r ≤ q := ⟨min_le_right _ _, min_le_right _ _⟩
  -- If r ∈ A, walk r → q (r ≤ q, r ∈ A, q ∉ A): find a crossing.
  -- Else r ∉ A, walk r → p (r ≤ p, r ∉ A, p ∈ A): flip orientation.
  by_cases hrA : r ∈ (A : Set (ℤ × ℤ))
  · obtain ⟨u, v, huA, _, hvRect, hvA, hadj⟩ :=
      cross_of_le (A := (A : Set (ℤ × ℤ))) hrSet hqSet hr_le_q hrA (by exact_mod_cast hqA)
    refine ⟨(u, v), mem_gridBdy.mpr ⟨?_, ?_, ?_, hadj⟩⟩
    · exact_mod_cast huA
    · exact Finset.mem_Icc.mpr hvRect
    · exact_mod_cast hvA
  · -- r ∉ A; walk r → p.
    obtain ⟨u, v, huA, huRect, _, hvA, hadj⟩ :=
      cross_of_le (A := ((A : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))ᶜ)
        hrSet hpSet hr_le_p hrA (by
          show p ∉ ((A : Set (ℤ × ℤ)))ᶜ
          simp only [Set.mem_compl_iff, not_not]
          exact_mod_cast hpA)
    -- Now u ∉ A, v ∉ Aᶜ (i.e., v ∈ A), and they are adjacent. Swap to
    -- get an (A, D\A) boundary pair.
    refine ⟨(v, u), mem_gridBdy.mpr ⟨?_, ?_, ?_, hadj.symm⟩⟩
    · -- v ∈ A
      have : v ∈ (A : Set (ℤ × ℤ)) := by
        have := hvA
        simp only [Set.mem_compl_iff, not_not] at this
        exact this
      exact_mod_cast this
    · exact Finset.mem_Icc.mpr huRect
    · -- u ∉ A
      exact_mod_cast huA

/-- Corollary: in an axis-aligned rectangle with `≥ 2` cells, every
non-empty proper subset has boundary size `≥ 1`. Packaged as a
cardinality statement for direct use in Step 4's `lem:G5-iso`. -/
theorem rect_gridBdy_card_pos {a b : ℤ × ℤ} (hab : a ≤ b)
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ Finset.Icc a b) (hne : A.Nonempty)
    (hprop : A ≠ Finset.Icc a b) :
    0 < (gridBdy (Finset.Icc a b) A).card :=
  Finset.card_pos.mpr (rect_gridBdy_nonempty (a := a) (b := b) hab hA hne hprop)

end Grid2D
end Mathlib
end OneThird
