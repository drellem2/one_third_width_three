# Deliverable A — F1-inactive ⇒ N-poset-core (uniform proof)

**EXPLORATORY ONLY — NOT a live program.**

Sub-deliverable A of `mg-fefe` (Option-C validation arc 1).
Latex-rigor markdown, doc-only. No Lean source changes; no
signature changes; no new axioms. The proof is paper-level
(~1 page) per the ticket's bounded-math budget.

---

## §0 — Statement

Let `α` be a finite poset equipped with a layered decomposition
`L : LayeredDecomposition α` (`lean/OneThird/Step8/LayeredReduction.lean:115`)
satisfying

* **(L.K)**       `L.K = 2` (depth two — bipartite layered),
* **(L.w)**       `L.w ≥ 1`,
* **(L.width)**   `HasWidthAtMost α 3`,
* **(L.irred)**   `LayerOrdinalIrreducible L`
                  (`lean/OneThird/Step8/LayerOrdinal.lean:240`),
* **(L.size)**    `Fintype.card α ∈ {3, 4, 5, 6}`.

Let `L_1 := { x : L.band x = 1 }`, `L_2 := { x : L.band x = 2 }`,
`m := |L_1|`, `n := |L_2|`. By (L.K) and `band_pos`, `L_1 ⊔ L_2 = α`
and `m + n = |α|`. By **(L1b)** `band_antichain`, both `L_1` and
`L_2` are antichains. By **(L2-upward)** `cross_band_lt_upward`
(field `cross_band_lt_upward`, `LayeredReduction.lean:149`,
`mg-53ce`), `x < y ⇒ band x ≤ band y`; combined with **(L2-forced)**
`forced_lt` being vacuous at K=2, w≥1 (since `1 + w < 2` requires
`w = 0`), the comparability relation reduces to a bipartite
incidence

```
E := { (a, b) ∈ L_1 × L_2 :  a < b }.
```

Define for `a ∈ L_1` its **upper-set image** `N(a) := { b ∈ L_2 :
(a, b) ∈ E }` (the row neighborhood) and for `b ∈ L_2` its
**lower-set image** `M(b) := { a ∈ L_1 : (a, b) ∈ E }` (the column
neighborhood).

**F1-inactive** (`docs/why-hC3-is-structural.md` §F1, `mg-b666`)
means **no within-band ⪯-strict pair exists**:

* For all `(a, a') ∈ L_1 × L_1` with `a ≠ a'`: `N(a) ⊊ N(a')` is
  false, AND
* for all `(b, b') ∈ L_2 × L_2` with `b ≠ b'`: `M(b) ⊊ M(b')` is
  false.

Equivalently, every two row neighborhoods are **equal or
incomparable** under containment, and likewise for columns.

### N-poset (canonical form)

The **4-element N-poset** is the poset on `{a_1, a_2, b_1, b_2}`
with comparability relation `{(a_1, b_1), (a_2, b_2)}` (cf.
`feedback_n_poset_is_not_ordinal_sum`; `K2-N4-22-N` in mg-e112 §A).
It is layered-irreducible at K=2, width 3, and F1-inactive.

### Theorem (Deliverable A's main claim)

> **Theorem (F1-inactive ⇒ N-poset-core).**
> Under hypotheses (L.K), (L.w), (L.width), (L.irred), (L.size)
> with `Fintype.card α ∈ {4, 5, 6}`, if `α` is F1-inactive then
> `α` contains the 4-element N-poset as an induced sub-poset:
> there exist `a_1, a_2 ∈ L_1` and `b_1, b_2 ∈ L_2`, all distinct,
> with `a_1 < b_1`, `a_2 < b_2`, and `a_1 ⊥ b_2`, `a_2 ⊥ b_1`,
> `a_1 ⊥ a_2`, `b_1 ⊥ b_2`.

> **Remark (degenerate |α| = 3 case).**
> For `Fintype.card α = 3`, F1-inactive forces `α` to be a
> 3-element antichain (cf. §3 below). The theorem's conclusion is
> vacuously unattainable (no 4-element induced sub-poset), but
> the antichain is trivially balanced (`Pr_α[x < y] = 1/2` for
> every incomparable pair) and does **not** require the N-core
> route — it is dispatched by `bipartite_balanced_enum` directly
> (cf. `lean/OneThird/Step8/LayeredBalanced.lean:498-518`,
> the K=1 branch's structural twin within the K=2 antichain
> sub-case). See §3 for the dispatch reading.

The proof is uniform: it proceeds by a single structural
case-split on the row-neighborhood pattern, with no per-class
enumeration. The 6-class verification table in §4 records that
the proof's case-split lands on the explicit witness in each
class catalogued in mg-e112 §4 (modulo the |α|=3 antichain
remark above).

---

## §1 — Proof of the theorem

We assume `Fintype.card α ∈ {4, 5, 6}` and F1-inactive. The
argument splits on the existence of two rows with **incomparable**
neighborhoods.

### Lemma 1 (key structural lemma)

> **Lemma 1.**  Under (L.K), (L.w), (L.width), (L.irred),
> (L.size) with `|α| ≥ 4`, if `α` is F1-inactive then there
> exist `a_1, a_2 ∈ L_1` distinct with `N(a_1)` and `N(a_2)`
> **incomparable** under containment (i.e., neither `N(a_1) ⊆
> N(a_2)` nor `N(a_2) ⊆ N(a_1)`).

**Proof of Lemma 1.**  Suppose for contradiction that no two rows
have incomparable neighborhoods. By F1-inactive (no strict
containment), every pair of distinct rows then satisfies
`N(a) = N(a')` (equal). Hence **all rows have the same
neighborhood** `S ⊆ L_2` (a single common value).

We rule out each of the three sub-cases for `S`:

1. **`S = L_2`.** Then every cross-pair `(a, b) ∈ L_1 × L_2`
   satisfies `a < b`, so `LayerOrdinalReducible L 1` holds (cut at
   `k = 1`). Contradicts (L.irred).

2. **`S = ∅`.** Then `E = ∅` and there are **no comparabilities**
   at all (within-band incomparability holds by (L1b); cross-band
   has no edges). So `α` is a `(m + n)`-element antichain. By
   (L.size), `m + n = |α| ≥ 4`. But (L.width) requires every
   antichain to have size ≤ 3 (`HasWidthAtMost α 3`). Contradiction.

3. **`∅ ⊊ S ⊊ L_2`.** Pick `b_∈ ∈ S` and `b_∉ ∈ L_2 \ S`. The
   column neighborhoods are `M(b_∈) = L_1` (every row contains
   `b_∈` in its nbhd `S`) and `M(b_∉) = ∅` (no row contains
   `b_∉` in `S`). Since `m = |L_1| ≥ 1`, we have
   `M(b_∉) = ∅ ⊊ L_1 = M(b_∈)`, a strict containment in `L_2`.
   This contradicts F1-inactive on `L_2`.

(In sub-case 3 we used `m ≥ 1`. For the partition `(m, n) = (0, k)`
to occur we'd need an empty band L_1, which is forbidden by the
ticket's regime since `|β| ≥ 3` and `K = 2` with `band_pos` and
`band_le` forces both bands non-empty when `|α| ≥ 2` — a
band-collapse to one side would degenerate to K=1. We use only
`m, n ≥ 1` below.)

All three sub-cases fail; hence the contradiction hypothesis
fails, and there exist `a_1 ≠ a_2 ∈ L_1` with `N(a_1)` and
`N(a_2)` incomparable. ∎

### Lemma 2 (N-poset extraction from incomparable rows)

> **Lemma 2.**  If there exist `a_1 ≠ a_2 ∈ L_1` with `N(a_1)`
> and `N(a_2)` mutually non-contained, then `α` contains a
> 4-element induced N-poset.

**Proof of Lemma 2.**  By non-containment, there exist
`b_1 ∈ N(a_1) \ N(a_2)` and `b_2 ∈ N(a_2) \ N(a_1)`. Note
`b_1 ≠ b_2` (since `b_1 ∈ N(a_1)` but `b_2 ∉ N(a_1)`).
Restrict the comparability relation to the 4-element subset
`{a_1, a_2, b_1, b_2}`:

* `a_1 < b_1` (by `b_1 ∈ N(a_1)`).
* `a_2 < b_2` (by `b_2 ∈ N(a_2)`).
* `a_1 ⊥ b_2` (since `b_2 ∉ N(a_1)` ⇒ `(a_1, b_2) ∉ E` ⇒ not
  `a_1 < b_2`; the reverse `b_2 < a_1` is forbidden by (L2-upward)
  `cross_band_lt_upward` since `band b_2 = 2 > 1 = band a_1`).
* `a_2 ⊥ b_1` (symmetric to the previous bullet).
* `a_1 ⊥ a_2` (within-band, by (L1b) `band_antichain`).
* `b_1 ⊥ b_2` (within-band, by (L1b)).

So the induced sub-poset on `{a_1, a_2, b_1, b_2}` has comparability
relation exactly `{(a_1, b_1), (a_2, b_2)}` — the 4-element
N-poset. ∎

### Theorem proof (composition)

By Lemma 1, two rows with incomparable neighborhoods exist. By
Lemma 2, the resulting 4-element subset is the N-poset.
∎

---

## §2 — Where each (L.) hypothesis is consumed

A short audit of which structural hypothesis each step requires —
useful for the robustness discussion in §6.

| Hypothesis | Consumed at | Role |
|---|---|---|
| (L.K) `L.K = 2` | Throughout | Reduces to bipartite incidence `E ⊆ L_1 × L_2`. |
| (L.w) `L.w ≥ 1` | Setup | Makes `forced_lt` vacuous, so `E ≠ L_1 × L_2` is the only obstruction to reducibility at `k = 1`. Without this, `forced_lt` could force comparabilities and shift the picture. |
| (L.width) | Lemma 1, sub-case 2 | Rules out the `m + n` antichain when `S = ∅`. |
| (L.irred) | Lemma 1, sub-case 1 | Rules out the `S = L_2` complete-bipartite (reducible) case. |
| (L.size) | Lemma 1, sub-case 2 | Forces `|α| ≥ 4`, which conflicts with `|α| ≤ 3` (width-3 antichain). For `|α| ∈ {4, 5, 6}` the contradiction fires. |
| F1-inactive | Lemma 1, sub-case 3, and the lemma's setup | Rules out the row-equal `∅ ⊊ S ⊊ L_2` case via the column-strict pair, and reduces the `not incomparable` hypothesis to "all rows equal". |
| (L1b) `band_antichain` | Lemma 2 | Provides `a_1 ⊥ a_2` and `b_1 ⊥ b_2` within bands. |
| (L2-upward) `cross_band_lt_upward` | Lemma 2 | Forbids `b_2 < a_1` in the upper band, completing `a_1 ⊥ b_2`. |

The proof depends on (L1b) and (L2-upward) only at Lemma 2. It
depends on (L.irred), (L.width), (L.size) only at Lemma 1's
sub-cases. **F1-inactive on L_2** (the column condition) is used
exactly once — to rule out the `S` middle-rank sub-case. The
**F1-inactive on L_1** (the row condition) is used to convert
"no incomp pair" into "all rows equal" before sub-cases fire.

---

## §3 — Degenerate |α| = 3 case (antichain remark)

For `|α| = 3` with `K = 2` and `w ≥ 1`, the partitions are `(m, n) ∈
{(1, 2), (2, 1)}`. By F1-inactive on `L_2` (in the (1, 2) case)
and `L_1` (in the (2, 1) case), and because the singletons of `L_1`
have at most 2 distinct values for `N(a) ⊆ L_2 = {b_1, b_2}`, the
column non-strict-pair condition collapses:

* In partition `(1, 2)` with `L_1 = {a}`: `M(b_1), M(b_2) ⊆ \{a\}`
  are subsets of a 1-element set, so each is `∅` or `\{a\}`. F1-
  inactive on `L_2` requires no strict containment, hence
  `M(b_1) = M(b_2)`. Both `∅`: no edges, antichain on 3 (OK,
  width ≤ 3). Both `\{a\}`: complete bipartite `\{a\} \times \{b_1,
  b_2\}` ⊆ `E`, layered-reducible at `k = 1`, contradicting
  (L.irred). So the F1-inactive |α|=3 case in partition `(1, 2)`
  is **exactly** the 3-element antichain (`K2-N3-AC` in mg-e112
  §A).
* Partition `(2, 1)` is symmetric and yields `K2-N3-AC'`.

In both classes, every pair `(x, y)` is incomparable, so
`Pr_α[x < y] = 1/2 ∈ [1/3, 2/3]`: every incomparable pair is
balanced trivially. The N-core route is unnecessary; the dispatch
is structural (`bipartite_balanced_enum` consumes `α` as a
3-element antichain at the outer K=1 branch's structural twin
or, equivalently, via the case-1 ambient route in
`bipartite_balanced_enum_general` with `B = ∅`).

This is consistent with the catalog tagging both `K2-N3-AC` and
`K2-N3-AC'` as **B** (balanced-pair branch) rather than **N**
(N-core branch) in mg-e112 §A §2.1, despite both being F1-inactive.

---

## §4 — 6-class verification table

The classes for which the theorem applies are the F1-inactive
classes in mg-e112 §A with `|α| ∈ {4, 5, 6}`. For each class the
proof's Lemma 1 incomparable-row pair and Lemma 2 N-core witness
are explicit. (We tabulate the 6 such classes; the antichain
classes `K2-N3-AC` and `K2-N3-AC'` from §3 fall outside the
theorem's applicable range and are handled there.)

For each class we list:
* **mg-e112 §A ID** and biadjacency matrix `M`.
* **`(a_1, a_2)`** — the row pair Lemma 1 produces (with the
  catalog's row-labelling `a_1, ..., a_m`).
* **`b_1 ∈ N(a_1) \ N(a_2)`** and **`b_2 ∈ N(a_2) \ N(a_1)`**.
* **N-core sub-poset** — the comparability of the 4 elements.

Note on mg-e112 §A's F1 count: mg-e112 §A §4 records "Updated
count: 32 of 40 F1-active, 8 F1-inactive" but its enumerated
list omits two `(2,3)/(3,2)` classes. The full F1-inactive
enumeration (re-derived below from the matrices in mg-e112 §2):
**`K2-N3-AC`, `K2-N3-AC'`** (|α|=3, antichains, dispatched per §3),
**`K2-N4-22-N`** (|α|=4), **`K2-N5-23-1⊄2`, `K2-N5-32-1⊄2`**
(|α|=5, the (2,3)/(3,2) "(1,2) cross" entries), **`K2-N6-M`,
`K2-N6-{122}-(1,2,2)a`, `K2-N6-{222}-(2,2,2)`** (|α|=6).
Total 8, matching the corrected count.

### Class 1 — `K2-N4-22-N`  (|α| = 4)

* `M = [1 0; 0 1]`, so `N(a_1) = {b_1}`, `N(a_2) = {b_2}`.
* `N(a_1) \ N(a_2) = {b_1}`, `N(a_2) \ N(a_1) = {b_2}` —
  incomparable.
* N-core on `{a_1, a_2, b_1, b_2} = α`: `a_1 < b_1`, `a_2 < b_2`,
  all other pairs incomparable. **The class IS the N-poset.**

### Class 2 — `K2-N5-23-1⊄2`  (|α| = 5, partition (2, 3))

* `M = [1 0 0; 0 1 1]`. `N(a_1) = {b_1}`, `N(a_2) = {b_2, b_3}`.
* `N(a_1) \ N(a_2) = {b_1}`, `N(a_2) \ N(a_1) = {b_2, b_3}`.
* Lemma 2's witness picks `b_1` and either of `{b_2, b_3}` — say
  `b_2`. N-core on `{a_1, a_2, b_1, b_2}`: `a_1 < b_1`,
  `a_2 < b_2`, all other pairs incomp.
* (Alternatively, picking `b_3` instead of `b_2` produces the
  isomorphic N-core on `{a_1, a_2, b_1, b_3}`.)

### Class 3 — `K2-N5-32-1⊄2`  (|α| = 5, partition (3, 2))

* By duality with Class 2 (transpose `M` and swap band order):
  `M = [1 0; 0 1; 0 1]` (3 rows, 2 cols). `N(a_1) = {b_1}`,
  `N(a_2) = {b_2}`, `N(a_3) = {b_2}`.
* Lemma 1 produces the incomparable pair `(a_1, a_3)` (or
  `(a_1, a_2)`): `N(a_1) = {b_1}` vs `N(a_3) = {b_2}`,
  incomparable singletons.
* Lemma 2's witnesses: `b_1 ∈ {b_1} \ {b_2}`, `b_2 ∈ {b_2} \
  {b_1}`. N-core on `{a_1, a_3, b_1, b_2}`.

### Class 4 — `K2-N6-M`  (|α| = 6, partition (3, 3) — matching)

* `M = [1 0 0; 0 1 0; 0 0 1]`. `N(a_i) = {b_i}` for each
  `i ∈ {1, 2, 3}`.
* Lemma 1 produces three choices of incomparable row pair
  `(a_i, a_j)`: every pair of singleton rows is incomparable.
* Lemma 2's witness for the choice `(a_1, a_2)`:
  `b_1 ∈ {b_1} \ {b_2}`, `b_2 ∈ {b_2} \ {b_1}`. N-core on
  `{a_1, a_2, b_1, b_2}`.
* (Three N-cores total, one for each pair of matching legs.)

### Class 5 — `K2-N6-{122}-(1,2,2)a`  (|α| = 6, partition (3, 3))

* `M = [1 0 0; 0 1 1; 0 1 1]`. `N(a_1) = {b_1}`, `N(a_2) =
  N(a_3) = {b_2, b_3}`.
* Lemma 1 produces the row pair `(a_1, a_2)` (or `(a_1, a_3)`):
  `{b_1}` vs `{b_2, b_3}`, mutually non-contained.
* Lemma 2's witness: `b_1 ∈ {b_1} \ {b_2, b_3}`, `b_2 ∈ {b_2, b_3}
  \ {b_1}`. N-core on `{a_1, a_2, b_1, b_2}`.
* (Picking `b_3` instead of `b_2` produces an isomorphic N-core;
  picking `(a_1, a_3)` instead of `(a_1, a_2)` likewise.)

### Class 6 — `K2-N6-{222}-(2,2,2)`  (|α| = 6, 6-cycle complement)

* `M = [0 1 1; 1 0 1; 1 1 0]`. `N(a_1) = {b_2, b_3}`,
  `N(a_2) = {b_1, b_3}`, `N(a_3) = {b_1, b_2}` — pairwise
  incomparable (each missing a different element).
* Lemma 1 produces the row pair `(a_1, a_2)` (or any pair):
  `{b_2, b_3}` vs `{b_1, b_3}`, mutually non-contained.
* Lemma 2's witness: `b_2 ∈ {b_2, b_3} \ {b_1, b_3}`,
  `b_1 ∈ {b_1, b_3} \ {b_2, b_3}`. N-core on `{a_1, a_2, b_1,
  b_2}` — comparability `a_1 < b_2`, `a_2 < b_1`, all other pairs
  incomp. This is the N-poset along the **anti-diagonal** of the
  4-element bipartite restriction (equivalent to the canonical
  N-poset by re-labelling).

### Verification summary

In each of the 6 classes (|α| ≥ 4), Lemma 1's incomparable-row
pair exists and Lemma 2's N-core extraction produces a 4-element
induced N-poset. The proof's structural case-split is uniform
and matches the per-class witness.

---

## §5 — K=2 N-poset is the canonical first check (arc 4.0 §8.2)

Per the ticket's constraint `K=2 N-poset is the canonical first
check per arc 4.0 §8.2`, we verify the theorem on `K2-N4-22-N`
(Class 1 above) explicitly.

`K2-N4-22-N` has `α = {a_1, a_2, b_1, b_2}` with `a_1 < b_1` and
`a_2 < b_2` only. F1-inactive: row neighborhoods `{b_1}, {b_2}`
incomparable; column neighborhoods `{a_1}, {a_2}` incomparable.
(L.K) `K = 2`, (L.w) `w = 1` (the `(1, 1)` "different singletons"
profile), (L.irred) holds (no `k=1` reducibility witness — `(a_1,
b_2)` and `(a_2, b_1)` are incomparable cross-pairs), (L.width)
holds, (L.size) `|α| = 4`.

Lemma 1: take `a_1, a_2 ∈ L_1`. `N(a_1) = {b_1}` and
`N(a_2) = {b_2}` — incomparable (neither contains the other,
both being distinct singletons).

Lemma 2: `b_1 ∈ N(a_1) \ N(a_2) = {b_1}`,
`b_2 ∈ N(a_2) \ N(a_1) = {b_2}`. The 4-element induced sub-poset
on `{a_1, a_2, b_1, b_2}` has comparabilities `a_1 < b_1` and
`a_2 < b_2` only — the N-poset.

Theorem's conclusion holds; the canonical first check passes.

---

## §6 — Robustness to family extension

The proof's hypotheses are tight, but its **uniform** character
admits a clean extrapolation to broader families. We discuss:

### 6a. |α| ≥ 7 within K=2

For K=2, `|α| ≤ 6` is **forced** by (L1) `band_size ≤ 3` and
`L.K = 2`: `|α| = m + n ≤ 3 + 3 = 6`. So the case `|α| ≥ 7` does
not arise within the ticket's K=2 width-3 layered scope.

If one were to drop (L1) and consider larger bands at K=2 (e.g.,
band sizes ≤ k for some k ≥ 4), the proof's Lemma 2 step is
**fully uniform** (it consumes only (L1b) `band_antichain`,
which does not depend on band size, and (L2-upward), which is
band-size-independent). Lemma 1's sub-case 2 (the `S = ∅`
antichain contradiction) consumes (L.width) `HasWidthAtMost α 3`;
without width 3 the antichain case would not be ruled out, but
that case is the *trivial* balanced case (Pr=1/2 everywhere) and
would dispatch via the antichain path of §3. Lemma 1's sub-case 3
is band-size-independent. So for K=2 layered (without the band-3
size cap and width-3 ambient), the theorem extends to: `α`
F1-inactive ⇒ N-poset-core OR `α` is a `(m+n)`-element antichain.

### 6b. K ≥ 3 (deferred to Deliverable C)

For K ≥ 3, the bipartite framing breaks: `E ⊂ L_i × L_j` has more
band index pairs `(i, j)` to consider, and the F1-inactive
condition becomes a multi-band condition. The proof here does
**not** transfer directly to K ≥ 3. See Deliverable C
(`k-ge-3-lift-plan.md`) for the K ≥ 3 strategy, which uses F3
strong-induction descent on `|α|` rather than direct bipartite
analysis.

### 6c. Width relaxation

(L.width) `HasWidthAtMost α 3` is consumed only at Lemma 1's
sub-case 2 (the antichain contradiction). For width ≤ w₀
(general w₀), the antichain ruling becomes `m + n ≤ w₀`, so the
F1-inactive antichain case is real for `|α| ≤ w₀`. For
`|α| ∈ {w₀ + 1, ..., 6}` the proof closes uniformly. Below
`|α| ≤ w₀` the antichain dispatch is needed.

### 6d. Dropping (L.w) `w ≥ 1`

If `w = 0`, then (L2-forced) becomes operative: `1 + 0 < 2`, so
`band x = 1, band y = 2 ⇒ x < y`. Hence `E = L_1 × L_2`
unconditionally, contradicting (L.irred). So the w=0 K=2
irreducible case is **empty**, and the theorem holds vacuously.
(This is the structural reason for the (L.w) hypothesis in the
ticket: w=0 K=2 is disposed of by `hasBalancedPair_of_K2_w0_incomp`
in `lean/OneThird/Step8/Case2BipartiteBound.lean:197`.)

### 6e. Catalog extension to `|α| ∈ {7, ..., n}` (hypothetical)

The theorem's uniform proof does not naturally extend past `|α|
= 6` *within K=2 width-3 layered* because no such posets exist
in the regime. An extension to a different regime (K ≥ 3, or
relaxed band-size cap) requires a separate analysis. **Flag**:
mg-e112 §A's catalog covers exactly the K=2 width-3 layered
regime; broader catalogs would be a separate scoping deliverable.

---

## §7 — Trip-wire checks (per `feedback_complexity_blowup_means_wrong_path`)

### 7a. F4-b trap (relabelling-as-progress)

The proof's hypotheses are **F1, (L1), (L2-upward)** — all
arc-2-or-earlier structural facts. It does **not** invoke F2
(Brightwell), F3 (strong-induction recursion), or any global
fiber/coherence argument (Steps 5-7 machinery). The proof is
purely structural at the K=2 bipartite level. **No F4-b trap
fires.**

### 7b. F6 / F7 (new structural obstructions)

The proof's case-split (incomparable rows vs all rows equal vs
strict middle) is exhaustive over the F1-inactive classes within
the regime. No new structural obstruction surfaces. **No F6/F7
escalation.**

### 7c. Bounded paper-math budget

The proof is ~1 page of structural argument, two lemmas plus
composition, plus an audit (§2) and a class-by-class verification
table (§4). Within the ticket's "paper-level not arc-level" ceiling.

### 7d. N-poset is not ordinal sum (`feedback_n_poset_is_not_ordinal_sum`)

The N-poset extracted in Lemma 2 has comparability relation
`{(a_1, b_1), (a_2, b_2)}` — exactly two cross-band edges out of
4 possible. `a_1 ⊥ b_2` and `a_2 ⊥ b_1` are explicitly verified
in Lemma 2. The 4-element sub-poset is **not** an ordinal sum
`{a_1, a_2} < {b_1, b_2}` (which would require all four
cross-pairs comparable). The N-poset is the structural opposite
of the ordinal-sum reducible case; **the warning is honored.**

### 7e. No new axioms; no signature regression

The proof is paper-only and introduces no Lean axioms or
signature changes. **`feedback_audit_bar_for_axioms` honored.**

---

## §8 — Cross-references

* `docs/why-hC3-is-structural.md` §F1 — F1 cardinality obstruction
  definition.
* `docs/proof-approaches-catalog-1/obstruction-enumeration.md`
  (`mg-e112` §A) — 40-class catalog. The 6 F1-inactive classes
  with `|α| ∈ {4, 5, 6}` are verified in §4 above.
* `docs/proof-approaches-catalog-1/in-tree-primitive-inventory.md`
  (`mg-e112` §C) — Lean primitives:
  - `LayeredDecomposition` (§2),
  - `LayerOrdinalIrreducible` (§2),
  - `cross_band_lt_upward` (§2),
  - `band_antichain` (§2 via L1b in the structure).
  The proof uses these primitives only as *interpretive
  scaffolding* — no Lean code is produced.
* `docs/alternating-cancellation-arc-1/lemma-statement.md`
  (`mg-acc8` A) — ACL lemma; an N-poset core is a separate
  structural witness, not a consequence of ACL alone.
* `docs/path-c-track-1-status-1.md` (`mg-b666`) — F1 strict-pair
  obstruction; F1-inactive is the **complement** of this regime.
* `lean/OneThird/Step8/CompoundMatching.lean:663` —
  `matching_exists_of_K2_irreducible_noWithinBand`: the existing
  in-tree consumer that **uses** F1-inactive ⇒ N-core
  *implicitly* via `NConfig` in `mg-c0c7`. This deliverable's
  theorem is the **explicit, uniform** statement that justifies
  that consumer's structural soundness across the catalog.

---

## §9 — Provenance

Sub-deliverable A of `mg-fefe` (Option-C validation arc 1).
Filed 2026-05-05. Origin: Daniel directive 2026-05-05T~15:24Z
("keep making forward progress"). Branch
`option-c-validation-arc-1`.

The proof's mathematical content is structural at the K=2
bipartite level and does **not** introduce paper-level new
combinatorics beyond the 1-page proof.
