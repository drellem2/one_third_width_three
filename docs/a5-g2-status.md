# A5-G2 status — RESOLVED via path 1 (`mg-53ce` continuation)

**Work item:** `mg-53ce` (A5-G2 path 1: add `cross_band_lt_upward`
field to `LayeredDecomposition`).

**Status:** **resolved (path 1 implemented)**.

**Author:** path-1 polecat continuation, 2026-04-26.

---

## Resolution summary

The (L2) gap diagnosed below — the paper assumes
"cross-band comparabilities are upward" but Lean's
`LayeredDecomposition` did not — has been closed by adding the
explicit field

```lean
cross_band_lt_upward : ∀ x y, x < y → band x ≤ band y
```

to `LayeredDecomposition` (in
`lean/OneThird/Step8/LayeredReduction.lean`).

The three real instance-construction sites have been updated to
discharge the new field:

* `LayeredDecomposition.restrict` — inherits trivially via subtype
  injection (Subtype order = ambient order).
* `Step8.trivialLayered` (in `MainAssembly.lean`) — band map now
  uses `LinearExt.szpilrajn α` (a Szpilrajn linear extension of `α`)
  rather than the arbitrary `Fintype.equivFin`. Monotonicity of `e`
  discharges the field.
* `Step8.layeredFromBridges` (in `LayeredBridges.lean`) — same
  Szpilrajn-based band-map change as `trivialLayered`.

The "~17 files" enumeration in the original report counted *files
mentioning* `LayeredDecomposition`, not files that *construct* an
instance. Most are consumers of the structure (parameters, lemmas,
projections); those don't require any change after adding a field.

The in-tree (L2) gap note at `LayerOrdinal.lean:253-260` has been
rewritten to reflect that the field now exists; the historical
note remains as a short paragraph.

The counterexample below (`α = {a, b, c}` with `c < a` only,
band-mapped to make `band a < band c`) is no longer a valid
`LayeredDecomposition` after the refactor — it violates
`cross_band_lt_upward` (`c < a` would force `band c ≤ band a`,
contradicting `band c > band a`). So the F5a Bool certificate's
upper-triangular `enumPredAtMaskOf` enumeration is structurally
correct on every input that survives the layered axioms.

The F5a discharge of `bounded_irreducible_balanced_inScope`
(`BoundedIrreducibleBalanced.lean:1543-1550`) now has its
load-bearing structural prerequisite in place. Wiring the
construction-equivalence + B1'-B2-B3 + G1' + symmetric extraction
+ bandMajorOrderIso transport into a real proof body remains a
follow-on (originally the second half of the `mg-53ce` task spec)
— it does not require any new axiom or sorry, just the glue work.
This file no longer documents that wiring as blocked.

**Axiom audit:** unchanged (mathlib trio +
`brightwell_sharp_centred` +
`case3Witness_hasBalancedPair_outOfScope`).

---

## Historical diagnosis (preserved for context)

The remainder of this file, below, is the original `pc-53ce` polecat
report from 2026-04-26 documenting why the gap existed and the
four resolution paths considered. Path 1 was selected by the
mini-CEO call and is now implemented; paths 2/3/4 are obsolete.

---

## Original TL;DR

The spec for `bounded_irreducible_balanced_inScope` cannot be
discharged as written without either (a) a new axiom, (b) a new
field on `LayeredDecomposition`, or (c) a substantially more
involved relabeling argument.

The "construction-equivalence" step

```
warshall (enumPredPreWarshallOf L.w (bandSizes L) (maskOf L))
         (Fintype.card α)
  = predMaskOf L
```

is **mathematically false** for layered decompositions with
order-band inversions (a partial-order pair `x < y` in `α` whose
Fin labelings satisfy `(bandMajorEquiv L) x > (bandMajorEquiv L)
y`). Such inversions are permitted by `LayeredDecomposition` and
CAN occur within `InCase3Scope` (K=3, w ≤ 4) when combined with
`LayerOrdinalIrreducible`.

(Path 1 closes this by adding `cross_band_lt_upward` as a field —
order-band inversions become structurally impossible.)

## Original concrete counterexample (now invalid under path 1)

* `α = {a, b, c}` with `c < a` only (`a, b` incomparable, `b, c`
  incomparable).
* Layered decomposition `L`: `M_1 = {a}`, `M_2 = {b}`, `M_3 = {c}`,
  `L.w = 2`. `forced_lt` is satisfied vacuously (with `w = 2`, no
  band-gap exceeds `w`).
* **Under path 1**, `cross_band_lt_upward c a (h : c < a)` would
  require `band c ≤ band a`, i.e. `3 ≤ 1` — impossible. So this
  `L` is *no longer a valid `LayeredDecomposition`*.

## Original root cause (now closed)

The paper's stronger (L2): cross-band comparabilities are upward
(no inversions). Pre-`mg-53ce` the Lean structure only encoded the
weaker `forced_lt`. The Python certificate's enumeration relied
on the stronger paper-(L2) — it only enumerates upper-triangle
predmasks. Path 1 promotes the upward property to a structural
field, so Lean and the certificate now agree.

---

## Original four paths considered

(Selected: path 1.)

### (1) Strengthen `LayeredDecomposition` ✅ **chosen and implemented**

Add a field
`cross_band_lt_upward : ∀ x y, x < y → L.band x ≤ L.band y`.
Updating sites that build instances; once the field exists,
`predMaskOf L` is upper-triangular and the spec's
construction-equivalence becomes provable.

### (2) Add an extra hypothesis to `bounded_irreducible_balanced_inScope`

Take `(hMono : ∀ x y, x < y → L.band x ≤ L.band y)` as an
explicit hypothesis. Push the obligation onto callers. Avoids
touching existing `LayeredDecomposition` instances but propagates
the hypothesis up the call chain to F5's strong-induction driver.
**Rejected** — relocates the obligation rather than discharging
it.

### (3) Relabel-then-certify

For any `L`, construct `L' : LayeredDecomposition α` that respects
α's order. Significant new work (~600+ LOC). **Rejected.**

### (4) Axiom

**Forbidden** by polecat instructions.

---

## References

* Polecat instructions: `mg-53ce` task body.
* `lean/OneThird/Step8/LayeredReduction.lean` — `LayeredDecomposition`
  structure, post-refactor includes `cross_band_lt_upward`.
* `lean/OneThird/Step8/LayerOrdinal.lean` — gap note at the old
  `:253-260` rewritten to reflect the resolution.
* `lean/OneThird/Step8/MainAssembly.lean` — `trivialLayered`
  Szpilrajn refactor.
* `lean/OneThird/Step8/LayeredBridges.lean` — `layeredFromBridges`
  Szpilrajn refactor.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1543-1550`
  — `bounded_irreducible_balanced_inScope` placeholder body
  (still `hEnum => hEnum`; the structural prerequisite is now in
  place for a real discharge in a follow-up).
* `step8.tex` `prop:in-situ-balanced` `2965-3048`; (L2) at the
  §sec:g4 setup discussion.
* `docs/a5-glue-status.md` — parent A5 status.
* `lean/AXIOMS.md` — axiom audit (unchanged).
