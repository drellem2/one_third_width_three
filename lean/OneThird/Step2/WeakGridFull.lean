/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step2.WeakGrid
import Mathlib.Tactic.Push

/-!
# Step 2 — Weak grid stability, completed (`lem:weak-grid`, F6b)

This file completes the Step 2 weak grid stability lemma `lem:weak-grid`
(`step2.tex`:121, proof Steps 1–6). It builds on the single-orientation
quantitative core `weak_grid_quantitative` of `WeakGrid.lean` §2 (F6a,
work item `mg-28fe`) and delivers the three remaining pieces (F6b, work
item `mg-6b23`):

1. **Column transpose.** The column-direction machinery `vertColBdy`
   (the transpose of `RowDecomp.horizRowBdy`) together with the
   per-line edge-counting lemmas. This bounds `|M \ A|` in the same
   way `RowDecomp` bounds the row side.
2. **HV-convex layer.** The cleanup obligations `hrow` / `hcol` of
   `weak_grid_quantitative` are discharged here, and the discharge uses
   only `IsHVConvex` (every row and column an interval) — the
   reflection-stable hypothesis. `IsHVConvex` and its
   reflection-stability live in `Grid2D.lean` §3b; `step2.tex` states
   the reflection step in terms of order-convexity, which is the
   imprecision of work item `mg-6db2`.
3. **Four-orientation reduction.** `weak_grid_covariant` transports the
   per-orientation core along an `ℓ¹`-preserving equivalence, giving
   the bound in each of the four Klein-group orientations.

## Main results

* `exRows_card_le_gridBdy_card`, `exCols_card_le_gridBdy_card` —
  discharge the two cleanup hypotheses of `weak_grid_quantitative`.
  Each exceptional row (resp. column) carries a boundary edge, and
  edges in distinct rows (columns) are distinct.
* `weak_grid` — the **completed** `lem:weak-grid`: for order-convex
  `D ⊆ [0,t]²` with `|D| ≥ c t²` and `A ⊆ D` with `∂_D A ≤ ε t`, there
  is a genuine `+`-staircase `M` with `|A △ M| ≤ (4ε/c)|D|`. No
  auxiliary hypotheses, no `sorry`. This supersedes both the trivial
  `δ ≤ 1` placeholder `weak_grid_bound` and the hypothesis-laden
  `weak_grid_quantitative`.
* `weak_grid_covariant` — the four-orientation reduction engine.
* `weak_grid_reflectBoth`, `weak_grid_reflectFst`, `weak_grid_reflectSnd`
  — the lemma in the other three orientations.

## Finding (recorded for `mg-6b23`)

The four-orientation WLOG of `step2.tex` Step 2 picks the row/column
anchor by a `min` argument so that each anchor mismatch is bounded by
`B^h/2` resp. `B^v/2`. After formalisation this `min` step turns out
**not to be load-bearing**: every exceptional row carries at least one
horizontal boundary edge regardless of orientation (a non-interval row
even carries two), and edges in distinct rows are distinct, so
`|exRows D A| ≤ |∂_D A|` holds *unconditionally* for the `+`
orientation — see `exRows_card_le_gridBdy_card`. The same holds for
columns. Hence the `+` orientation always satisfies the cleanup
bounds; `weak_grid` needs no orientation choice. The four-orientation
machinery (`weak_grid_covariant` and the three reflected forms) is
nonetheless delivered as genuine, reusable infrastructure: it is what a
downstream consumer needs to obtain a staircase in a *prescribed*
reflected frame.
-/

namespace OneThird
namespace Step2
namespace WeakGrid

open Finset OneThird.Mathlib.Grid2D

/-! ## §1. A one-dimensional sign-change helper -/

/-- **1D sign change.** If `p ∉ A`, `q ∈ A`, and `p ≤ q`, then somewhere
strictly between `p` and `q` the indicator of `A` flips from `0` to `1`:
there is a `k` with `p ≤ k < q`, `k ∉ A` and `k + 1 ∈ A`.

This is the elementary engine behind "an exceptional line carries a
boundary edge": it finds the last `0` before reaching the `1` at `q`. -/
theorem exists_flip_up {A : Finset ℤ} {p q : ℤ}
    (hpq : p ≤ q) (hp : p ∉ A) (hq : q ∈ A) :
    ∃ k : ℤ, p ≤ k ∧ k < q ∧ k ∉ A ∧ k + 1 ∈ A := by
  have hpltq : p < q := lt_of_le_of_ne hpq (by rintro rfl; exact hp hq)
  let T : Finset ℤ := (Finset.Icc p (q - 1)).filter (fun j => j ∉ A)
  have hpT : p ∈ T := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl p, by omega⟩, hp⟩
  have hTne : T.Nonempty := ⟨p, hpT⟩
  let k := T.max' hTne
  have hkT : k ∈ T := T.max'_mem hTne
  have hkprop : k ∈ Finset.Icc p (q - 1) ∧ k ∉ A := by
    rw [Finset.mem_filter] at hkT; exact hkT
  rw [Finset.mem_Icc] at hkprop
  obtain ⟨⟨hkp, hkq⟩, hkA⟩ := hkprop
  refine ⟨k, hkp, by omega, hkA, ?_⟩
  by_cases h : k + 1 = q
  · rw [h]; exact hq
  · by_contra hk1A
    have hk1T : k + 1 ∈ T := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hk1A⟩
    have := T.le_max' _ hk1T
    omega

/-! ## §2. Column-direction machinery (transpose of `RowDecomp`)

`RowDecomp.horizRowBdy D A i` collects the boundary edges lying in
row `i`. The transpose `vertColBdy D A j` collects those lying in
column `j`. The column slice `colSlice` is already defined in
`WeakGrid.lean` §2. -/

/-- A **vertical** boundary edge in column `j`: an element `(u, v)` of
`gridBdy D A` with `u.2 = v.2 = j`. The column transpose of
`RowDecomp.horizRowBdy`. -/
def vertColBdy (D A : Finset (ℤ × ℤ)) (j : ℤ) :
    Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (gridBdy D A).filter (fun p => p.1.2 = j ∧ p.2.2 = j)

lemma mem_vertColBdy {D A : Finset (ℤ × ℤ)} {j : ℤ}
    {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ vertColBdy D A j ↔ p ∈ gridBdy D A ∧ p.1.2 = j ∧ p.2.2 = j := by
  unfold vertColBdy
  rw [Finset.mem_filter]

/-- Vertical boundaries in distinct columns are disjoint. -/
lemma vertColBdy_disjoint {D A : Finset (ℤ × ℤ)} {j j' : ℤ} (h : j ≠ j') :
    Disjoint (vertColBdy D A j) (vertColBdy D A j') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_vertColBdy] at hp hp'
  exact h (hp.2.1.symm.trans hp'.2.1)

/-- Every vertical boundary is part of the full grid boundary. -/
lemma vertColBdy_subset_gridBdy (D A : Finset (ℤ × ℤ)) (j : ℤ) :
    vertColBdy D A j ⊆ gridBdy D A := by
  intro p hp
  rw [mem_vertColBdy] at hp
  exact hp.1

/-! ### HV-convex variants of the row/column slice interval lemmas

`RowDecomp.rowSlice_eq_Icc_of_ordConvex` needs only that rows are
intervals, i.e. `IsHVConvex`. We record the HV-convex variants, which
are what the reflection-stable form of the argument consumes. -/

/-- HV-convex variant of `RowDecomp.rowSlice_eq_Icc_of_ordConvex`:
under `IsHVConvex` a non-empty row slice of `D` is a closed interval. -/
theorem rowSlice_eq_Icc_of_hvConvex {D : Finset (ℤ × ℤ)}
    (hD : IsHVConvex D) (i : ℤ) (hne : (RowDecomp.rowSlice D i).Nonempty) :
    ∃ a b : ℤ, a ≤ b ∧ RowDecomp.rowSlice D i = Finset.Icc a b := by
  classical
  let a := (RowDecomp.rowSlice D i).min' hne
  let b := (RowDecomp.rowSlice D i).max' hne
  have ha : a ∈ RowDecomp.rowSlice D i := (RowDecomp.rowSlice D i).min'_mem hne
  have hb : b ∈ RowDecomp.rowSlice D i := (RowDecomp.rowSlice D i).max'_mem hne
  have hab : a ≤ b := (RowDecomp.rowSlice D i).min'_le b hb
  refine ⟨a, b, hab, Finset.Subset.antisymm ?_ ?_⟩
  · intro j hj
    rw [Finset.mem_Icc]
    exact ⟨(RowDecomp.rowSlice D i).min'_le j hj, (RowDecomp.rowSlice D i).le_max' j hj⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [RowDecomp.mem_rowSlice]
    rw [RowDecomp.mem_rowSlice] at ha hb
    exact hD.row ha hb hj.1 hj.2

/-- HV-convex variant for columns: under `IsHVConvex` a non-empty
column slice of `D` is a closed interval. -/
theorem colSlice_eq_Icc_of_hvConvex {D : Finset (ℤ × ℤ)}
    (hD : IsHVConvex D) (j : ℤ) (hne : (colSlice D j).Nonempty) :
    ∃ a b : ℤ, a ≤ b ∧ colSlice D j = Finset.Icc a b := by
  classical
  let a := (colSlice D j).min' hne
  let b := (colSlice D j).max' hne
  have ha : a ∈ colSlice D j := (colSlice D j).min'_mem hne
  have hb : b ∈ colSlice D j := (colSlice D j).max'_mem hne
  have hab : a ≤ b := (colSlice D j).min'_le b hb
  refine ⟨a, b, hab, Finset.Subset.antisymm ?_ ?_⟩
  · intro i hi
    rw [Finset.mem_Icc]
    exact ⟨(colSlice D j).min'_le i hi, (colSlice D j).le_max' i hi⟩
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [mem_colSlice]
    rw [mem_colSlice] at ha hb
    exact hD.col ha hb hi.1 hi.2

/-! ## §3. Discharging the cleanup hypotheses

The two cleanup hypotheses of `weak_grid_quantitative` are
`hrow : |exRows D A| ≤ |∂_D A|` and `hcol : |exCols D A| ≤ |∂_D A|`.
We prove both unconditionally (for `IsHVConvex D`) by showing every
exceptional row/column carries a boundary edge in its own line. -/

/-- **Every exceptional row carries a horizontal boundary edge.** If
row `i` is `A`-non-empty but carries no corner (it is not a
left-anchored interval), then `RowDecomp.horizRowBdy D A i` is
non-empty. Order-convexity is not needed — only that `D`'s rows are
intervals (`IsHVConvex`). -/
theorem one_le_horizRowBdy_of_mem_exRows {D A : Finset (ℤ × ℤ)}
    (hD : IsHVConvex D) (hAD : A ⊆ D) {i : ℤ} (hi : i ∈ exRows D A) :
    1 ≤ (RowDecomp.horizRowBdy D A i).card := by
  classical
  rw [mem_exRows] at hi
  obtain ⟨_, hne, hnocorner⟩ := hi
  set M := (RowDecomp.rowSlice A i).max' hne with hM_def
  have hM_mem : M ∈ RowDecomp.rowSlice A i := (RowDecomp.rowSlice A i).max'_mem hne
  have hM_A : ((i, M) : ℤ × ℤ) ∈ A := RowDecomp.mem_rowSlice.mp hM_mem
  have hM_D : ((i, M) : ℤ × ℤ) ∈ D := hAD hM_A
  -- No corner ⟹ some `D`-cell weakly below `(i, M)` is missing from `A`.
  have hclaim : ∃ j ∈ RowDecomp.rowSlice D i, j ≤ M ∧ ((i, j) : ℤ × ℤ) ∉ A := by
    by_contra hcon
    push Not at hcon
    apply hnocorner
    refine ⟨(i, M), ?_, rfl⟩
    rw [mem_cornerSet]
    refine ⟨hM_A, ?_, ?_⟩
    · intro j' hj'
      exact (RowDecomp.rowSlice A i).le_max' j' hj'
    · intro j hj hjM
      exact hcon j hj hjM
  obtain ⟨j, hjD, hjM, hjA⟩ := hclaim
  have hjD' : ((i, j) : ℤ × ℤ) ∈ D := RowDecomp.mem_rowSlice.mp hjD
  obtain ⟨k, hjk, hkM, hkA, hk1A⟩ :=
    exists_flip_up hjM (fun h => hjA (RowDecomp.mem_rowSlice.mp h)) hM_mem
  have hkA' : ((i, k) : ℤ × ℤ) ∉ A := fun h => hkA (RowDecomp.mem_rowSlice.mpr h)
  have hk1A' : ((i, k + 1) : ℤ × ℤ) ∈ A := RowDecomp.mem_rowSlice.mp hk1A
  have hkD : ((i, k) : ℤ × ℤ) ∈ D := hD.row hjD' hM_D hjk (le_of_lt hkM)
  have hedge : (((i, k + 1), (i, k)) : (ℤ × ℤ) × (ℤ × ℤ))
      ∈ RowDecomp.horizRowBdy D A i := by
    rw [RowDecomp.mem_horizRowBdy]
    refine ⟨?_, rfl, rfl⟩
    rw [mem_gridBdy]
    refine ⟨hk1A', hkD, hkA', ?_⟩
    have : l1dist ((i, k + 1) : ℤ × ℤ) (i, k) = 1 := by simp [l1dist]
    exact this
  exact Finset.card_pos.mpr ⟨_, hedge⟩

/-- **Every exceptional column carries a vertical boundary edge.** If
column `j` is `A`-non-empty but not bottom-anchored (some `D`-cell
weakly below an `A`-cell of the column is itself outside `A`), then
`vertColBdy D A j` is non-empty. Only `IsHVConvex` is needed. -/
theorem one_le_vertColBdy_of_mem_exCols {D A : Finset (ℤ × ℤ)}
    (hD : IsHVConvex D) (hAD : A ⊆ D) {j : ℤ} (hj : j ∈ exCols D A) :
    1 ≤ (vertColBdy D A j).card := by
  classical
  rw [mem_exCols] at hj
  obtain ⟨_, _, hnotdc⟩ := hj
  push Not at hnotdc
  obtain ⟨i, hiD, i', hiA, hle, hinotA⟩ := hnotdc
  have hiD' : ((i, j) : ℤ × ℤ) ∈ D := mem_colSlice.mp hiD
  have hiA' : ((i', j) : ℤ × ℤ) ∈ A := mem_colSlice.mp hiA
  have hiD'' : ((i', j) : ℤ × ℤ) ∈ D := hAD hiA'
  obtain ⟨k, hik, hki', hkA, hk1A⟩ :=
    exists_flip_up hle (fun h => hinotA (mem_colSlice.mp h)) hiA
  have hkA' : ((k, j) : ℤ × ℤ) ∉ A := fun h => hkA (mem_colSlice.mpr h)
  have hk1A' : ((k + 1, j) : ℤ × ℤ) ∈ A := mem_colSlice.mp hk1A
  have hkD : ((k, j) : ℤ × ℤ) ∈ D := hD.col hiD' hiD'' hik (le_of_lt hki')
  have hedge : (((k + 1, j), (k, j)) : (ℤ × ℤ) × (ℤ × ℤ))
      ∈ vertColBdy D A j := by
    rw [mem_vertColBdy]
    refine ⟨?_, rfl, rfl⟩
    rw [mem_gridBdy]
    refine ⟨hk1A', hkD, hkA', ?_⟩
    have : l1dist ((k + 1, j) : ℤ × ℤ) (k, j) = 1 := by simp [l1dist]
    exact this
  exact Finset.card_pos.mpr ⟨_, hedge⟩

/-- **Row cleanup (paper Step 1, row side), discharged.** The number of
exceptional rows is at most the grid boundary: `|exRows D A| ≤ |∂_D A|`.
Each exceptional row carries a horizontal boundary edge, and horizontal
edges in distinct rows are distinct. -/
theorem exRows_card_le_gridBdy_card {D A : Finset (ℤ × ℤ)}
    (hD : IsHVConvex D) (hAD : A ⊆ D) :
    (exRows D A).card ≤ (gridBdy D A).card := by
  classical
  have h_sum : ∑ i ∈ exRows D A, (RowDecomp.horizRowBdy D A i).card
      ≤ (gridBdy D A).card := by
    rw [← Finset.card_biUnion
      (fun i _ i' _ hii' => RowDecomp.horizRowBdy_disjoint hii')]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨i, _, hpi⟩ := hp
    exact RowDecomp.horizRowBdy_subset_gridBdy D A i hpi
  calc (exRows D A).card
      = ∑ _i ∈ exRows D A, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ i ∈ exRows D A, (RowDecomp.horizRowBdy D A i).card :=
        Finset.sum_le_sum (fun i hi => one_le_horizRowBdy_of_mem_exRows hD hAD hi)
    _ ≤ (gridBdy D A).card := h_sum

/-- **Column cleanup (paper Step 1, column side), discharged.** The
number of exceptional columns is at most the grid boundary:
`|exCols D A| ≤ |∂_D A|`. This is the column transpose of
`exRows_card_le_gridBdy_card`, and it is the column-direction bound
behind `|M \ A|`. -/
theorem exCols_card_le_gridBdy_card {D A : Finset (ℤ × ℤ)}
    (hD : IsHVConvex D) (hAD : A ⊆ D) :
    (exCols D A).card ≤ (gridBdy D A).card := by
  classical
  have h_sum : ∑ j ∈ exCols D A, (vertColBdy D A j).card
      ≤ (gridBdy D A).card := by
    rw [← Finset.card_biUnion
      (fun j _ j' _ hjj' => vertColBdy_disjoint hjj')]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨j, _, hpj⟩ := hp
    exact vertColBdy_subset_gridBdy D A j hpj
  calc (exCols D A).card
      = ∑ _j ∈ exCols D A, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ j ∈ exCols D A, (vertColBdy D A j).card :=
        Finset.sum_le_sum (fun j hj => one_le_vertColBdy_of_mem_exCols hD hAD hj)
    _ ≤ (gridBdy D A).card := h_sum

/-! ## §4. The completed `lem:weak-grid` -/

/-- **`lem:weak-grid`, completed (`+` orientation).** For an
order-convex `D ⊆ [0,t]²` with `|D| ≥ c t²` and `A ⊆ D` with
`∂_D A ≤ ε t`, there is a genuine `+`-staircase `M` with
`|A △ M| ≤ (4ε/c)|D|`.

This is the full `step2.tex` Lemma `lem:weak-grid` (proof Steps 1–6):
the cleanup hypotheses `hrow`/`hcol` of `weak_grid_quantitative` are
now discharged by `exRows_card_le_gridBdy_card` and
`exCols_card_le_gridBdy_card`, so this lemma has **no auxiliary
hypotheses and no `sorry`**. It supersedes the trivial `δ ≤ 1`
placeholder `weak_grid_bound`. -/
theorem weak_grid {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ}
    (hc : 0 < c)
    (hD : IsOrdConvex (D : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ D, 0 ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (t : ℤ))
    (ht : 1 ≤ t)
    (hmass : c * (t : ℚ) ^ 2 ≤ (D.card : ℚ))
    (hAD : A ⊆ D)
    (hbdy : ((gridBdy D A).card : ℚ) ≤ ε * (t : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircasePlus D M ∧
      ((symmDiff A M).card : ℚ) ≤ (4 * ε / c) * (D.card : ℚ) :=
  weak_grid_quantitative hc hD hbox ht hmass hAD hbdy
    (exRows_card_le_gridBdy_card hD.isHVConvex hAD)
    (exCols_card_le_gridBdy_card hD.isHVConvex hAD)

/-! ## §5. The four-orientation reduction

`weak_grid` delivers the `+` (SW-anchored) orientation. The other
three orientations of `step2.tex` Remark `rem:four-orient` are obtained
by transporting the lemma along the Klein-four group of axis
reflections. -/

/-- `M` is a **`g`-oriented staircase** of `D` (for `g` an axis
reflection) iff its `g`-image is a `+`-staircase of the `g`-image of
`D`. With `g = Equiv.refl` this is `IsStaircasePlus`. -/
def IsStaircaseOriented (g : ℤ × ℤ ≃ ℤ × ℤ) (D M : Finset (ℤ × ℤ)) : Prop :=
  IsStaircasePlus (D.image g) (M.image g)

/-- Applying an equivalence and then its inverse to a finset is the
identity. -/
lemma image_symm_image (g : ℤ × ℤ ≃ ℤ × ℤ) (s : Finset (ℤ × ℤ)) :
    (s.image g.symm).image g = s := by
  rw [Finset.image_image, g.self_comp_symm, Finset.image_id]

/-- An `ℓ¹`-preserving equivalence conjugates the grid boundary to a
boundary of the same cardinality. -/
lemma gridBdy_card_image {g : ℤ × ℤ ≃ ℤ × ℤ}
    (hg : ∀ p q : ℤ × ℤ, l1dist (g p) (g q) = l1dist p q)
    (D A : Finset (ℤ × ℤ)) :
    (gridBdy (D.image g) (A.image g)).card = (gridBdy D A).card := by
  symm
  refine Finset.card_bij (fun p _ => (g p.1, g p.2)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_gridBdy.mp hp
    refine mem_gridBdy.mpr ⟨Finset.mem_image_of_mem g h1,
      Finset.mem_image_of_mem g h2, ?_, ?_⟩
    · intro hc
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hc
      exact h3 (by rwa [g.injective hxeq] at hx)
    · change l1dist (g p.1) (g p.2) = 1
      rw [hg]; exact h4
  · intro p _ q _ hpq
    obtain ⟨e1, e2⟩ := Prod.mk.inj hpq
    exact Prod.ext (g.injective e1) (g.injective e2)
  · intro b hb
    obtain ⟨h1, h2, h3, h4⟩ := mem_gridBdy.mp hb
    obtain ⟨u, hu, hueq⟩ := Finset.mem_image.mp h1
    obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp h2
    refine ⟨(u, v), mem_gridBdy.mpr ⟨hu, hv, ?_, ?_⟩, ?_⟩
    · intro hvA
      exact h3 (hveq ▸ Finset.mem_image_of_mem g hvA)
    · change l1dist u v = 1
      have h : l1dist (g u) (g v) = 1 := by rw [hueq, hveq]; exact h4
      rwa [hg] at h
    · change (g (u, v).1, g (u, v).2) = b
      rw [hueq, hveq]

/-- **Four-orientation reduction engine.** Transport `weak_grid` along
an `ℓ¹`-preserving equivalence `g`. Given that the `g`-image of `D` is
order-convex and box-bounded, the lemma holds in the `g`-orientation.

For `g = reflectBoth` this applies to every order-convex `D` (see
`weak_grid_reflectBoth`), since `reflectBoth` preserves order-convexity.
For `g = reflectFst` / `reflectSnd` the hypothesis `hgD` is genuine
extra input — order-convexity of `D` does **not** imply order-convexity
of its single-axis reflection. -/
theorem weak_grid_covariant
    {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ} (g : ℤ × ℤ ≃ ℤ × ℤ)
    (hg : ∀ p q : ℤ × ℤ, l1dist (g p) (g q) = l1dist p q)
    (hc : 0 < c)
    (hgD : IsOrdConvex ((D.image g : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    (hgbox : ∀ p ∈ D.image g,
      0 ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (t : ℤ))
    (ht : 1 ≤ t)
    (hmass : c * (t : ℚ) ^ 2 ≤ (D.card : ℚ))
    (hAD : A ⊆ D)
    (hbdy : ((gridBdy D A).card : ℚ) ≤ ε * (t : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircaseOriented g D M ∧
      ((symmDiff A M).card : ℚ) ≤ (4 * ε / c) * (D.card : ℚ) := by
  have hcard : (D.image g).card = D.card :=
    Finset.card_image_of_injective D g.injective
  have hmass' : c * (t : ℚ) ^ 2 ≤ ((D.image g).card : ℚ) := by
    rw [hcard]; exact hmass
  have hAD' : A.image g ⊆ D.image g := Finset.image_subset_image hAD
  have hbdy' : ((gridBdy (D.image g) (A.image g)).card : ℚ) ≤ ε * (t : ℚ) := by
    rw [gridBdy_card_image hg]; exact hbdy
  obtain ⟨M', hM'stair, hM'card⟩ :=
    weak_grid hc hgD hgbox ht hmass' hAD' hbdy'
  refine ⟨M'.image g.symm, ?_, ?_⟩
  · change IsStaircasePlus (D.image g) ((M'.image g.symm).image g)
    rw [image_symm_image]
    exact hM'stair
  · have hsdimg : (symmDiff A (M'.image g.symm)).image g
        = symmDiff (A.image g) M' := by
      rw [Finset.image_symmDiff _ _ g.injective, image_symm_image]
    have hsdcard : (symmDiff A (M'.image g.symm)).card
        = (symmDiff (A.image g) M').card := by
      rw [← hsdimg, Finset.card_image_of_injective _ g.injective]
    rw [hsdcard, hcard] at *
    exact hM'card

/-- `reflectBoth` preserves order-convexity: it reverses the whole
product order, and order-convexity is order-reversal invariant. -/
theorem ordConvex_image_reflectBoth {D : Finset (ℤ × ℤ)} {n m : ℤ}
    (hD : IsOrdConvex (D : Set (ℤ × ℤ))) :
    IsOrdConvex ((D.image (reflectBoth n m) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  constructor
  rintro ⟨i, j⟩ hp ⟨i', j'⟩ hq ⟨a, b⟩ ⟨⟨hia, hjb⟩, hai', hbj'⟩
  rw [Finset.mem_coe, mem_image_reflectBoth] at hp hq
  rw [Finset.mem_coe, mem_image_reflectBoth]
  have key : ((n - a, m - b) : ℤ × ℤ) ∈ (D : Set (ℤ × ℤ)) :=
    hD.mem_of_between (by exact_mod_cast hq) (by exact_mod_cast hp)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact_mod_cast key

/-- **`lem:weak-grid`, `reflectBoth` (NE) orientation.** A second free
orientation: `reflectBoth` preserves order-convexity, so every
order-convex `D` admits an NE-oriented staircase approximation too. -/
theorem weak_grid_reflectBoth {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ}
    (hc : 0 < c)
    (hD : IsOrdConvex (D : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ D, 0 ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (t : ℤ))
    (ht : 1 ≤ t)
    (hmass : c * (t : ℚ) ^ 2 ≤ (D.card : ℚ))
    (hAD : A ⊆ D)
    (hbdy : ((gridBdy D A).card : ℚ) ≤ ε * (t : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircaseOriented (reflectBoth (t : ℤ) (t : ℤ)) D M ∧
      ((symmDiff A M).card : ℚ) ≤ (4 * ε / c) * (D.card : ℚ) := by
  refine weak_grid_covariant (reflectBoth (t : ℤ) (t : ℤ))
    (reflectBoth_l1dist (t : ℤ) (t : ℤ)) hc (ordConvex_image_reflectBoth hD)
    ?_ ht hmass hAD hbdy
  intro p hp
  obtain ⟨i, j⟩ := p
  rw [mem_image_reflectBoth] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hbox _ hp
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **`lem:weak-grid`, `reflectFst` orientation.** Order-convexity of
`D` does **not** imply order-convexity of `reflectFst D` (the
imprecision of `mg-6db2`), so this orientation takes `hgD` — order-
convexity of the reflected region — as a genuine hypothesis. It holds
for every region that is order-convex in the first-axis-reversed frame
(equivalently, a `reflectFst`-image of an order-convex region). -/
theorem weak_grid_reflectFst {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ}
    (hc : 0 < c)
    (hgD : IsOrdConvex
      ((D.image (reflectFst (t : ℤ)) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ D, 0 ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (t : ℤ))
    (ht : 1 ≤ t)
    (hmass : c * (t : ℚ) ^ 2 ≤ (D.card : ℚ))
    (hAD : A ⊆ D)
    (hbdy : ((gridBdy D A).card : ℚ) ≤ ε * (t : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircaseOriented (reflectFst (t : ℤ)) D M ∧
      ((symmDiff A M).card : ℚ) ≤ (4 * ε / c) * (D.card : ℚ) := by
  refine weak_grid_covariant (reflectFst (t : ℤ))
    (reflectFst_l1dist (t : ℤ)) hc hgD ?_ ht hmass hAD hbdy
  intro p hp
  obtain ⟨i, j⟩ := p
  rw [mem_image_reflectFst] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hbox _ hp
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **`lem:weak-grid`, `reflectSnd` orientation.** As with `reflectFst`,
order-convexity of the reflected region is taken as a hypothesis. -/
theorem weak_grid_reflectSnd {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ}
    (hc : 0 < c)
    (hgD : IsOrdConvex
      ((D.image (reflectSnd (t : ℤ)) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ D, 0 ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (t : ℤ))
    (ht : 1 ≤ t)
    (hmass : c * (t : ℚ) ^ 2 ≤ (D.card : ℚ))
    (hAD : A ⊆ D)
    (hbdy : ((gridBdy D A).card : ℚ) ≤ ε * (t : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircaseOriented (reflectSnd (t : ℤ)) D M ∧
      ((symmDiff A M).card : ℚ) ≤ (4 * ε / c) * (D.card : ℚ) := by
  refine weak_grid_covariant (reflectSnd (t : ℤ))
    (reflectSnd_l1dist (t : ℤ)) hc hgD ?_ ht hmass hAD hbdy
  intro p hp
  obtain ⟨i, j⟩ := p
  rw [mem_image_reflectSnd] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hbox _ hp
  exact ⟨by omega, by omega, by omega, by omega⟩

end WeakGrid
end Step2
end OneThird
