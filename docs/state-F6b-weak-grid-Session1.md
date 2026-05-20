# OneThird-F6b — quantitative weak-grid stability, completed

**Work item:** mg-6b23 (FULL REFACTOR Phase 2, F6 deliverable part b;
depends on F6a / mg-28fe).
**Status:** GREEN — `lem:weak-grid` completed: the cleanup hypotheses
of the F6a core are discharged, the lemma is `0`-`sorry` and
hypothesis-free, all four orientations delivered, `lake build OneThird`
green.

---

## 1. What was delivered

Two files changed, one added.

### `lean/OneThird/Mathlib/Grid2D.lean` §3b (new, ~110 lines)

The **HV-convex layer**:

* `IsHVConvex` — a finset `D ⊆ ℤ²` is HV-convex if every row and every
  column is an integer interval. The reflection-stable weakening of
  `IsOrdConvex`.
* `IsOrdConvex.isHVConvex` — order-convex ⟹ HV-convex.
* `mem_image_reflectFst` / `_reflectSnd` / `_reflectBoth` — membership
  in the reflected images.
* `isHVConvex_image_reflectFst` / `_reflectSnd` / `_reflectBoth` —
  **HV-convexity is invariant under the whole Klein-four group of axis
  reflections.** This is the concrete Lean form of the paper-side fix
  tracked by `mg-6db2`: `step2.tex` Step 2 states the reflection step
  in terms of order-convexity, which is *not* reflection-stable
  (counterexample `{(0,0),(1,0),(0,1)}`); HV-convexity is.

### `lean/OneThird/Step2/WeakGridFull.lean` (new, ~500 lines)

The completed F6 lemma. Sections:

* **§1.** `exists_flip_up` — 1D sign-change helper: `p ∉ A`, `q ∈ A`,
  `p ≤ q` ⟹ the indicator of `A` flips up somewhere in `[p, q)`.
* **§2.** `vertColBdy` — vertical boundary edges in a column (the
  transpose of `RowDecomp.horizRowBdy`), with `mem_`, disjointness and
  subset lemmas. HV-convex variants of the slice-interval lemmas
  (`rowSlice_eq_Icc_of_hvConvex`, `colSlice_eq_Icc_of_hvConvex`).
* **§3.** `one_le_horizRowBdy_of_mem_exRows`,
  `one_le_vertColBdy_of_mem_exCols` — every exceptional row/column
  carries a boundary edge in its own line. Then
  `exRows_card_le_gridBdy_card`, `exCols_card_le_gridBdy_card` — the
  two cleanup hypotheses of `weak_grid_quantitative`, discharged.
* **§4.** `weak_grid` — the **completed `lem:weak-grid`**: order-convex
  `D ⊆ [0,t]²`, `|D| ≥ c t²`, `A ⊆ D`, `∂_D A ≤ ε t` ⟹ a genuine
  `+`-staircase `M` with `|A △ M| ≤ (4ε/c)|D|`. No auxiliary
  hypotheses, no `sorry`.
* **§5.** `IsStaircaseOriented`, `weak_grid_covariant` (the
  four-orientation engine), `weak_grid_reflectBoth` /
  `weak_grid_reflectFst` / `weak_grid_reflectSnd`.

`lean/OneThird.lean` gains the `WeakGridFull` import.

## 2. Proof architecture (maps to `step2.tex` proof Steps 1–6)

F6a (`weak_grid_quantitative`) delivered Steps 3–6 with the Step 1–2
cleanup as *hypotheses* `hrow : |exRows D A| ≤ |∂_D A|` and
`hcol : |exCols D A| ≤ |∂_D A|`. F6b discharges them:

* **Cleanup, both directions.** An exceptional row (`A`-non-empty, not
  a left-anchored interval) always has a `D`-cell weakly below its
  topmost `A`-cell that is missing from `A`; `exists_flip_up` turns
  that into an adjacent `0→1` flip, i.e. a horizontal boundary edge in
  that row. Edges in distinct rows are distinct, so
  `|exRows D A| ≤ |∂_D A|`. The column side is the exact transpose
  via `vertColBdy`.
* **Combine.** `weak_grid = weak_grid_quantitative` with `hrow`/`hcol`
  supplied by the two discharge lemmas.

## 3. Finding — the four-orientation WLOG is not load-bearing

`step2.tex` Step 2 (`majority orientation; WLOG reduction`) chooses the
row anchor `L`/`R` and column anchor `B`/`T` by a `min` argument so
each anchor mismatch is `≤ B^h/2` resp. `≤ B^v/2`. **After
formalisation this `min` step is unnecessary.**

`|exRows D A| = |I_b| + |I_ne ∖ I_L|` (bad rows + non-left-anchored
interval rows). Each bad row carries `≥ 2` horizontal edges
(`RowDecomp`), each non-left-anchored interval row carries `≥ 1`, and
all these edges are in distinct rows. So
`B^h ≥ 2|I_b| + |I_ne ∖ I_L| ≥ |I_b| + |I_ne ∖ I_L| = |exRows D A|`
*for the `+` orientation directly* — no orientation choice needed. The
formalised discharge `exRows_card_le_gridBdy_card` proves exactly this
(uniformly, via "≥ 1 edge per exceptional line", which subsumes both
the bad-row and non-anchored-row cases). The column side is identical.

Consequently `weak_grid` (the `+` / SW orientation) holds for every
order-convex `D` with no orientation choice. This is consistent with
`lem:weak-grid` only ever asserting *one* staircase exists
(`M ∈ Stair(D)`, with `Stair` the union of the four orientations): the
`+` orientation always lands in that union.

The four-orientation machinery is nonetheless delivered as genuine,
non-placeholder infrastructure:

* `weak_grid_covariant` transports the core along any `ℓ¹`-preserving
  equivalence;
* `weak_grid_reflectBoth` is a second *free* orientation —
  `reflectBoth` preserves order-convexity (it reverses the whole
  product order), so `ordConvex_image_reflectBoth` discharges its
  convexity obligation;
* `weak_grid_reflectFst` / `weak_grid_reflectSnd` take order-convexity
  *of the reflected region* as a hypothesis. This is correct and not a
  weakness: a single-axis reflection does **not** preserve
  order-convexity (the `mg-6db2` counterexample), and order-convex `D`
  genuinely need not admit a good `reflectFst`-staircase — e.g. a
  filled triangle `{i+j ≤ n}` is `0`-far from a `+`-staircase but
  `Ω(n²)`-far from every `reflectFst`-staircase. The reflected-frame
  orientations are meaningful exactly for regions order-convex in the
  reflected frame, and the hypothesis records that faithfully.

This is a *finding*, not a block-and-report: every obligation is
well-posed and fully discharged. The deliverable is simpler than the
ticket anticipated (no orientation WLOG required to discharge the
cleanup hypotheses), and the column transpose plus HV-convex layer are
delivered in full.

## 4. HV-convexity threading

The discharge lemmas (`exRows_card_le_gridBdy_card`,
`exCols_card_le_gridBdy_card` and their `one_le_*` helpers) require
only `IsHVConvex D` — they use that `D`'s rows and columns are
intervals, never the full 2D order-interval (box) property. `weak_grid`
takes `IsOrdConvex D` (the box property is still needed inside F6a's
`weak_grid_quantitative`, for the Step 5 column bound) and feeds
`hD.isHVConvex` to the cleanup. So the row/column cleanup is genuinely
an HV-convex-level statement, and `Grid2D` §3b proves HV-convexity is
the reflection-stable notion — the two halves of the `mg-6db2` fix made
concrete in Lean.

## 5. Non-triviality / non-vacuity

* `weak_grid` is the genuine `δ = 4ε/c` bound, linear in `ε`, with
  **no auxiliary hypotheses** — it supersedes both the trivial
  `δ ≤ 1` placeholder `weak_grid_bound` and the hypothesis-laden
  `weak_grid_quantitative`.
* The discharge is real content: `exists_flip_up` plus the per-line
  edge construction is the formal core of `cor:most-rows-intervals`
  and its column transpose, in the unified "≥ 1 edge per exceptional
  line" form.
* All four orientations are delivered as `0`-`sorry` theorems.

## 6. Deferred (correctly out of F6b scope)

* The literal `≥ 2`-edges-per-bad-line corollary
  `cor:most-rows-intervals` for columns (`twice_badCols`): the
  discharge route uses the stronger-coverage "≥ 1 edge per *every*
  exceptional line", which subsumes it; the bare `≥ 2` column
  corollary is not on the F6 critical path. `RowDecomp` already
  carries the row form `twice_badRows_le_gridBdy_card`.
* `cor:sign` (orientation assignment), `lem:fiber-avg`,
  `prop:per-fiber` — separate Step 2 deliverables.
* The paper-side correction of the order-convex/HV-convex imprecision
  is `mg-6db2`.

## 7. Build

`lake build OneThird.Step2.WeakGridFull` — green, `0`-`sorry`, no
warnings. Full `lake build OneThird` — green (no consumer broke).
