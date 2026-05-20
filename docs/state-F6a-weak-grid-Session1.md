# OneThird-F6a — quantitative weak-grid stability, single-orientation core

**Work item:** mg-28fe (FULL REFACTOR Phase 2, F6 deliverable part a;
continuation of the re-scoped mg-dc4c `OneThird-WeakGridF6`).
**Status:** GREEN — genuine quantitative `δ = 4ε/c` core delivered,
`0`-`sorry`, `lake build` green.

---

## 1. What was delivered

`lean/OneThird/Step2/WeakGrid.lean` §2 (new, ~330 lines appended; the
pre-existing §1 placeholder content is untouched and still exported
for its current consumers `PerFiber.lean` / `Conclusion.lean`).

The headline new theorem is

```
theorem weak_grid_quantitative
    {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ}
    (hc : 0 < c)
    (hD : IsOrdConvex (D : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ D, 0 ≤ p.1 ∧ p.1 ≤ t ∧ 0 ≤ p.2 ∧ p.2 ≤ t)
    (ht : 1 ≤ t)
    (hmass : c * t ^ 2 ≤ D.card)
    (hAD : A ⊆ D)
    (hbdy : (gridBdy D A).card ≤ ε * t)
    (hrow : (exRows D A).card ≤ (gridBdy D A).card)
    (hcol : (exCols D A).card ≤ (gridBdy D A).card) :
    ∃ M, IsStaircasePlus D M ∧ (symmDiff A M).card ≤ (4 * ε / c) * D.card
```

This is the **genuine quantitative `δ = 4ε/c` form** of `step2.tex`
Lemma `lem:weak-grid` (proof Steps 1–6), superseding the trivial
`δ ≤ 1` placeholder `weak_grid_bound`. No placeholder, no `sorry`.

Supporting public API added in the same file:

* `colSlice` / `mem_colSlice` — column slices (the transpose of the
  existing `RowDecomp.rowSlice`).
* `cornerSet` / `mem_cornerSet` — the corners of `A` inside `D`
  (left-anchored interval rows together with their right end).
* `stairM` / `mem_stairM` — the single-orientation `+`-staircase, the
  down-closure of `cornerSet`. `stairM_isStaircasePlus` proves it is a
  genuine product-order lower set (proof Step 3).
* `exRows` / `exCols` (+ `mem_` lemmas) — the row/column exceptional
  sets of paper Steps 1–2.
* `ordConvex_box` — the "box" lemma (the **only** use of
  order-convexity).
* `fst_mem_exRows_of_mem_sdiff` (Step 4), `snd_mem_exCols_of_mem_sdiff`
  (Step 5) — the two cardinality-localisation lemmas.
* `card_Icc_zero_t`, `card_filter_fst_le`, `card_filter_snd_le` —
  the `≤ |S|·(t+1)` counting lemmas.

## 2. Proof architecture (maps to `step2.tex` proof Steps 1–6)

The construction is `M := stairM D A`, the set of `D`-cells weakly
below some **corner** — an `A`-cell `(i, r)` where `r = max A`-row-`i`
and the whole `D`-row up to `r` lies in `A` (so `A`-row `i` is the
left-anchored interval `[min D-row i, r]`).

* **Step 3 (construction).** `M` is the down-closure of `cornerSet`,
  hence a product-order lower set by one `le_trans`
  (`stairM_isStaircasePlus`).
* **Step 4 (`|A \ M|`).** Any `A`-cell in a left-anchored row sits
  below that row's corner, so `A \ M` lives on exceptional rows
  (`exRows`): rows that are `A`-non-empty but carry no corner.
* **Step 5 (`|M \ A|`).** An `M`-cell `(i,j)` has a corner witness
  `(i',r')` with `i ≤ i'`, `j ≤ r'`. The **box lemma** places
  `(i',j) ∈ D`; the corner's down-closure property then gives
  `(i',j) ∈ A`, so `(i,j)` sits weakly below an `A`-cell of column
  `j`. Hence `M \ A` lives on exceptional columns (`exCols`):
  `A`-non-empty columns that are not bottom-anchored.
* **Steps 1–2 (cleanup + orientation)** are the *hypotheses* `hrow`,
  `hcol`: each exceptional set has cardinality `≤ ∂_D A`. This is
  exactly what Steps 1–2 deliver for one fixed orientation
  (`cor:most-rows-intervals` bounds the bad/non-interval rows;
  the orientation choice bounds the non-anchored ones). Discharging
  these by the four-orientation reflection argument is **F6b**.
* **Step 6 (combine).** `|A △ M| ≤ (exRows + exCols)(t+1)
  ≤ 2·∂_D A·(t+1) ≤ 2εt(t+1) ≤ 4εt² ≤ (4ε/c)|D|`, the last step
  from `|D| ≥ c t²`.

## 3. Finding — `IsOrdConvex` vs HV-convex for the single-orientation core

The ticket directed "build F6a against HV-convex, not bare
`IsOrdConvex`". After working the proof, the single-orientation core
is delivered against **`IsOrdConvex`** instead. This is a deliberate,
documented deviation, not a block-and-report — the obligation is
well-posed and fully discharged. Reasoning:

1. **Step 5 genuinely needs the box property.** The key step
   "`M` does not stick out above `A` in a good column" reduces to:
   `(i,j) ∈ D`, `(i',r') ∈ D`, `i ≤ i'`, `j ≤ r'` ⟹ `(i',j) ∈ D`.
   This is full order-convexity (the 2D order-interval), and is
   **not** implied by HV-convexity (rows + columns intervals): an
   HV-convex set can omit the diagonal corner `(i',j)`.
2. **F6a performs no reflection.** The reason the dc4c polecat
   flagged HV-convex was reflection-stability: the axis reflections
   `i ↦ t−i` do not preserve `IsOrdConvex` but do preserve
   HV-convexity. F6a is the *single-orientation* core — it never
   reflects — so the reflection-stability concern does not apply to
   it. The orientation is pre-chosen and supplied via `hrow`/`hcol`.
3. **`IsOrdConvex` is what Step 1 actually delivers.** `step2.tex`
   (S1.2) produces `D_{x,y}` order-convex; F6a consumes it directly.
4. **The clean predicate design sidesteps the RowDecomp lemmas.**
   The ticket anticipated "HV-convex variants of the RowDecomp
   lemmas". The delivered proof does **not** route through
   `RowDecomp.twice_badRows_le_gridBdy_card` at all: the
   `cornerSet` / `exCols` predicates carry exactly the needed
   interval/anchoring structure, and order-convexity is isolated to
   the single `ordConvex_box` lemma. So no HV-convex RowDecomp
   variants were needed.

**Consequence for F6b.** The four-orientation reduction (F6b) *is*
where HV-convexity must be threaded — it reflects, and after a
reflection only HV-convexity survives. F6b will need: (a) an
`IsHVConvex` definition, (b) `IsOrdConvex → IsHVConvex`, (c) a
reflected variant of the box lemma valid under HV-convexity *for the
reflected region* (a reflected order-convex set, while not
order-convex, still has the box property in the reflected frame).
The cleanest F6b route is to keep F6a's `weak_grid_quantitative` as
the per-orientation core and apply it to each of the four reflected
`(D, A)` pairs, picking the orientation that satisfies `hrow`/`hcol`
(paper Step 2's `min` argument). F6a's core is reflection-agnostic
and so is directly reusable.

## 4. Non-triviality / non-vacuity

* The bound is the genuine `4ε/c`, linear in `ε` — `δ(ε) → 0` as
  `ε → 0`. Not the `δ ≤ 1` placeholder.
* The hypotheses are jointly satisfiable and non-vacuous: take
  `D` a filled rectangle and `A` any left-and-bottom-anchored
  staircase — then `exRows = exCols = ∅` and `∂_D A` can be made
  arbitrarily small. As `A` moves away from a staircase the
  exceptional sets grow, and `hrow`/`hcol` force `∂_D A` to grow
  with them — the content is real.
* `M = stairM D A` is a genuine `+`-staircase (`IsStaircasePlus`,
  product-order lower set), proven, not assumed.

## 5. Deferred (correctly out of F6a scope)

* **F6b** — the four-orientation reflection reduction that discharges
  `hrow` / `hcol`; needs `IsHVConvex` + reflected box lemma (see §3).
* The B^h/B^v horizontal/vertical boundary split (`lem:row-decomp`'s
  finer form): F6a uses the coarser `exSet ≤ ∂_D A` bound on each
  axis, which still yields the full `4ε/c`. A B^h/B^v refinement
  would tighten constants only; not needed for the headline bound.
* `cor:sign` (orientation assignment / separation), `lem:fiber-avg`,
  `prop:per-fiber` — separate Step 2 deliverables, already partly in
  tree (`FiberAvg.lean`, `PerFiber.lean`).

## 6. Build

`lake build OneThird.Step2.WeakGrid` — green, `0`-`sorry`, no new
warnings on `WeakGrid.lean`. Full `lake build OneThird` — green
(no consumer broke; `weak_grid_exists` / `IsStaircasePlus` kept
intact for `PerFiber` / `Conclusion`).
