# A5-G2 status — `pc-53ce` polecat report

**Work item:** `mg-53ce` (A5-G2: replace `fun hEnum => hEnum`
placeholder in `bounded_irreducible_balanced_inScope` with a real
proof composing B1'-B2-B3 + G1' + construction-equivalence +
Symmetric extraction + bandMajorOrderIso transport).
**Status:** **blocked** — paper-vs-formalization gap (the (L2)
gap, already documented in tree at `LayerOrdinal.lean:253-260`).
No code changes; polecat preserved this status doc and exited.
**Author:** `pc-53ce` polecat, 2026-04-26.

---

## TL;DR

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

Polecat instructions explicitly forbid sorry's / axioms / hacky
shortcuts, so this work item is **blocked** awaiting a
human-decided resolution.

---

## Concrete counterexample

* `α = {a, b, c}` with `c < a` only (`a, b` incomparable, `b, c`
  incomparable).
* Layered decomposition `L`: `M_1 = {a}`, `M_2 = {b}`, `M_3 = {c}`,
  `L.w = 2`. `forced_lt` is satisfied vacuously (with `w = 2`, no
  band-gap exceeds `w`).
* `LayerOrdinalIrreducible L`: at `k = 1`, witness pair `(a, c)`
  fails `a < c` (we have `c < a`); at `k = 2`, same witness fails.
  So `L` is irreducible.
* `InCase3Scope L.w (Fintype.card α) L.K`: `K = 3 ✓`, `w ∈ [1,4] ✓`,
  `w = 2 → |α| = 3 ≤ 7 ✓`. **In scope.**
* `HasWidthAtMost α 3`: max antichain size ≤ 2 ✓.

So this is a valid input to `bounded_irreducible_balanced_inScope`.

`bandMajorEquiv L` gives `e a = 0`, `e b = 1`, `e c = 2` (canonical
Fintype labeling within each singleton band).

`predMaskOf L` (bit `u` of `pred[v]` set iff `e.symm u < e.symm v`):
* `pred[0]`: bits with `e.symm u < a`. `e.symm 2 = c < a ✓`. So
  `pred[0] = bit 2 = 4`. **A lower-triangle bit (`u=2 > v=0`).**
* `pred[1]`: nothing strictly below `b`. `pred[1] = 0`.
* `pred[2]`: nothing strictly below `c`. `pred[2] = 0`.
* `predMaskOf L = [4, 0, 0]`.

`enumPredPreWarshallOf L.w (bandSizes L) (maskOf L)` only sets
**upper-triangle** bits (the `enumPartition` loop has `j > i`, so
the free/forced UVs are all `(a, b)` with `a` in lower band and
`b` in higher band, hence `a < b` in Fin). Trace:
* `bs = [1,1,1]`, `forcedUV = []`, `freeUV = [(0,1), (1,2), (0,2)]`.
* `maskOf L`: bit `k` = bit `freeUV[k].1` of
  `predMaskOf L[freeUV[k].2]`: bit 0 of `pred[1] = 0`; bit 1 of
  `pred[2] = 0`; bit 0 of `pred[2] = 0`. So `maskOf L = 0`.
* No forced edges, no masked free edges → pre-warshall pred is
  `[0, 0, 0]`. Warshall is a no-op on the empty pred.
* `enumPredAtMaskOf L.w (bandSizes L) (maskOf L) = [0, 0, 0]`.

So `enumPredAtMaskOf … ≠ predMaskOf L` (the lower-triangle bit
`pred[0] = 4` is missing). The "construction-equivalence" of the
spec is false.

---

## Why no recovery via the certificate

* The certificate proves `hasBalancedPair (enumPredAtMaskOf …) n
  = true` for the enumerated pred, on `Fin n` with the
  **enumerated pred's** order — which on this input is the empty
  order.
* `hasBalancedPair_of_orderIso` requires an `α ≃o (Fin n)` whose
  Fin-side `LE` matches the enumerated pred's order. But `α` has
  `c < a` and the enumerated pred has no relations, so no such
  order iso exists.
* Even ignoring the orderiso direction, transporting a balanced
  pair from the empty Fin-3 poset (6 LEs, every pair has probLT
  = 1/2) to α (3 LEs, different probabilities) is mathematically
  wrong: the probabilities differ.

Note: the example's actual α DOES have a balanced pair `(a, b)`
with probLT = 1/3 (computed: 3 LEs total, 1 has `a < b`). So the
theorem is *true* — just not provable via the spec's strategy.

---

## Root cause: the (L2) gap

This is a known paper-vs-formalization gap, already documented
inside the codebase at `LayerOrdinal.lean:253-260`:

> The paper's conclusion asks for `(u, v)` *incomparable* in `Q`.
> The Lean form `¬ (u < v)` is what irreducibility directly
> provides: the reverse-direction ruling-out `¬ (v < u)` is argued
> in the paper via "(L2)", which is a property of the cross-band
> direction in the §sec:g4 setup but **not an axiom of
> `LayeredDecomposition` in Lean**.

The paper assumes a stronger (L2): cross-band comparabilities are
upward (no inversions). The Lean structure only encodes the
weaker `forced_lt`. The Python certificate's enumeration relies
on the stronger paper-(L2) — it only enumerates upper-triangle
predmasks.

---

## Proposed paths forward

Four options. **Polecat recommends (1) or (2).**

### (1) Strengthen `LayeredDecomposition`

Add a field
`cross_band_lt_upward : ∀ x y, x < y → L.band x ≤ L.band y`
(or equivalently:
`∀ x y, L.band y < L.band x → ¬ (x < y)`). Matches the paper's
(L2). Costs:

* Updating ~17 files that build `LayeredDecomposition` instances.
  Many trivially satisfy this (e.g., `LayeredBridges`'
  `bandwidth = |α| + 1` chain layering) or already implicitly
  assume it.
* Once the field exists, `predMaskOf L` is upper-triangular and
  the spec's construction-equivalence becomes provable along the
  lines the spec describes.

### (2) Add an extra hypothesis to `bounded_irreducible_balanced_inScope`

Take `(hMono : ∀ x y, x < y → L.band x ≤ L.band y)` as an
explicit hypothesis. Push the obligation onto callers. Avoids
touching existing `LayeredDecomposition` instances but propagates
the hypothesis up the call chain to F5's strong-induction driver.

### (3) Relabel-then-certify

For any `L`, construct `L' : LayeredDecomposition α` that respects
α's order (topological-sort within bands, monotone band ordering),
prove `L'` is in scope and irreducible whenever `L` is, apply the
certificate to `L'`. Significant new work (~600+ LOC), and still
needs a clear theorem about when `L'` exists matching `L`'s
parameters.

### (4) Axiom (mirroring `case3Witness_hasBalancedPair_outOfScope`)

Cleanest if "no new axioms" is relaxed. Mirrors the existing
out-of-scope axiom in `Case3Residual.lean`. Disclosure entry in
`AXIOMS.md`. Polecat instructions for this work item explicitly
forbade this.

---

## What this status doc preserves

* The full diagnosis (counterexample, root cause, options) is in
  this file so future polecats / human reviewers don't have to
  re-derive it.
* The placeholder body in `bounded_irreducible_balanced_inScope`
  remains in tree (`fun hEnum => hEnum`). No code changes.
* `Case3Witness L` remains a hypothesis on
  `width3_one_third_two_thirds`; eliminating it remains the goal
  of A5-G3 (depends on G2 = this status's resolution).
* Current `#print axioms` output is unchanged (mathlib trio +
  `brightwell_sharp_centred` + `case3Witness_hasBalancedPair_outOfScope`).

---

## References

* Polecat instructions: `mg-53ce` task body.
* `lean/OneThird/Step8/LayerOrdinal.lean:253-260` — the original
  in-tree (L2) gap note.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1531-1538`
  — the placeholder body in `bounded_irreducible_balanced_inScope`.
* `step8.tex` `prop:in-situ-balanced` `2965-3048`; (L2) at the
  §sec:g4 setup discussion.
* `docs/a5-glue-status.md` — the parent A5 status doc.
* `docs/a5-profile-resolution.md` — B4 hybrid resolution +
  InCase3Scope definition.
* `lean/AXIOMS.md` — current project axiom audit.
