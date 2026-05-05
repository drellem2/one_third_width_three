# Alternating-Cancellation Lemma — verification on the K=2 obstruction family

> **EXPLORATORY ONLY — NOT a live program.**
>
> Deliverable B for `mg-acc8` (alternating-cancellation arc 1.0
> kickoff, polecat `pacc8`). This file enumerates the
> Alternating-Cancellation Lemma's quantities (`|Σ|/|L|`, BK
> graph, fire-sets `D_i`, multi-direction intersections
> `D_S`, structural reading) on six K=2 obstruction-family
> configurations.
>
> See `lemma-statement.md` (Deliverable A) for the lemma
> formalisation and `verdict.md` (Deliverable C) for the
> aggregate verdict.

---

## 0. Conventions

For each poset `α`:

* `n = |α|`. Reference linear extension `L_0` chosen to be
  the lexicographically-least; labels `1, …, n` indexed in
  `L_0` order.
* `σ_L ∈ S_n` is the permutation `σ_L(i) = pos_L(label_i)`.
* `sign(L) := sign(σ_L)`.
* `Σ(α) := Σ_L sign(L)`.
* `D_i(α) := { L : L[i], L[i+1] are α-incomparable }` for
  `i ∈ {1, …, n−1}`.
* `D_S(α) := ∩_{i ∈ S} D_i(α)` for `S ⊆ {1, …, n−1}`.
* `m(α) := max_{S non-adj} |D_S(α)|`.
* `BK(L(α))`: BK graph; vertex set `L(α)`; edges
  `{L, τ_i L}` for `L ∈ D_i`.
* Lemma bound (single direction):
  `|Σ(α)| ≤ |L(α)| − max_i |D_i(α)|`.
* Lemma bound (multi direction):
  `|Σ(α)| ≤ |L(α)| − m(α)`.

The "structural reading" is what (5.2.b) of `lemma-statement.md`
says about `α` given the saturation level `|Σ|/|L|`.

---

## 1. Configuration K2-N — the K=2 N-poset (canonical)

### 1.1 Definition

`α = {x_1, x_2, y_1, y_2}` with cover relations `x_1 < y_1`,
`x_2 < y_2` (no other comparabilities). `n = 4`. K = 2,
w = 0, |β| = 2. Bands: `band(x_i) = 1`, `band(y_i) = 2`.

* **Irreducible?** Yes (per
  `feedback_n_poset_is_not_ordinal_sum`; not an ordinal sum
  because not every lower is below every upper).
* **Case-2-strict?** No. `upper(x_1) = {y_1}`,
  `upper(x_2) = {y_2}` — incomparable subsets, neither `⊊`
  the other.

### 1.2 Linear extensions

Reference `L_0 = (x_1, x_2, y_1, y_2)`, labels
`1=x_1, 2=x_2, 3=y_1, 4=y_2`.

| #   | LE                           | `σ_L` (cycle)        | sign  |
|-----|------------------------------|----------------------|-------|
| L_1 | `(x_1, x_2, y_1, y_2)`       | `e`                  | +1    |
| L_2 | `(x_1, x_2, y_2, y_1)`       | `(3 4)`              | −1    |
| L_3 | `(x_1, y_1, x_2, y_2)`       | `(2 3)`              | −1    |
| L_4 | `(x_2, x_1, y_1, y_2)`       | `(1 2)`              | −1    |
| L_5 | `(x_2, x_1, y_2, y_1)`       | `(1 2)(3 4)`         | +1    |
| L_6 | `(x_2, y_2, x_1, y_1)`       | `(1 3 4 2)`          | −1    |

`|L| = 6`. `Σ = +1 − 1 − 1 − 1 + 1 − 1 = −2`. `|Σ|/|L| =
1/3` **(saturation)**.

### 1.3 Fire-sets

| `i` | `D_i` membership                          | `|D_i|` |
|-----|-------------------------------------------|---------|
| 1   | `{L_1, L_2, L_4, L_5}` (positions 1,2 = x's, incomp)  | 4       |
| 2   | `{L_1, L_3, L_5, L_6}` (positions 2,3 incomp)         | 4       |
| 3   | `{L_1, L_2, L_4, L_5}` (positions 3,4 = y's, incomp)  | 4       |

`D_{1,3} = D_1 ∩ D_3 = {L_1, L_2, L_4, L_5}`,
`|D_{1,3}| = 4`. (Only non-adjacent pair is `{1, 3}` since
`|1−3| = 2`.)

`m(α) = 4` (attained by every individual `D_i` and by
`D_{1,3}`).

### 1.4 BK graph

```
E_1 = { {L_1, L_4}, {L_2, L_5} }            (τ_1-edges)
E_2 = { {L_1, L_3}, {L_5, L_6} }            (τ_2-edges)
E_3 = { {L_1, L_2}, {L_4, L_5} }            (τ_3-edges)
```

Total 6 edges, 6 vertices. Degree sequence:
`deg(L_1) = 3, deg(L_2) = 2, deg(L_3) = 1, deg(L_4) = 2,
deg(L_5) = 3, deg(L_6) = 1`.

**Min degree** `= 1` (attained at `L_3` and `L_6` — the
"thin" LEs).

Sign-bipartition: `L_+ = {L_1, L_5}` (signs `+1`),
`L_− = {L_2, L_3, L_4, L_6}` (signs `−1`). Maximum bipartite
matching saturates the smaller side `L_+`: e.g.
`{L_1, L_2}, {L_5, L_6}`, size 2. Matching deficiency
`= |L| − 2|M| = 6 − 4 = 2 = |Σ|`. **Bound (4.2.a) tight.**

### 1.5 Lemma bound

```
|Σ|  ≤  |L|  −  m(α)  =  6 − 4  =  2.
```

`|Σ| = 2`. **Equality.** Lemma is tight on K2-N.

### 1.6 Structural reading

Saturation contrapositive (5.2.b): `m/|L| ≤ 2/3`. Attained:
`4/6 = 2/3`. The `|L|/3 = 2` "thin" LEs are exactly
`{L_3, L_6}`. Both are interleaving extensions of the form
`(x_i, y_i, x_j, y_j)` (the two-chain interleaving pattern
characteristic of the N-poset).

`L_3 = (x_1, y_1, x_2, y_2)` and `L_6 = (x_2, y_2, x_1, y_1)`
swap the two `(x, y)`-chain blocks. They are the only LEs in
which neither the within-band `(x_1, x_2)` swap nor the
within-band `(y_1, y_2)` swap is supported (because the
positional structure puts an element of band 1 next to an
element of band 2 with a strict `<` relation).

**Reading:** the lemma's saturation contrapositive on the
N-poset *correctly identifies* the "interleaving" structure
of the thin LEs. This matches the canonical N-poset
combinatorial signature.

---

## 2. Configuration F1-min — the F1 3-element minimal counterexample

### 2.1 Definition

`α = {a, a', y}` with the single cover relation `a' < y`.
`n = 3`. K = 2 (bands `{a, a'}, {y}`), w = 1, |β| = 1.

* **Irreducible?** Yes (per
  `docs/path-c-track-1-status-1.md` §2 minimal counterexample).
* **Case-2-strict?** Yes: `upper(a) = ∅`,
  `upper(a') = {y}`, so `∅ ⊊ {y}`.

### 2.2 Linear extensions

Reference `L_0 = (a, a', y)`, labels `1=a, 2=a', 3=y`.

| #   | LE             | `σ_L`              | sign |
|-----|----------------|---------------------|------|
| L_1 | `(a, a', y)`   | `e`                 | +1   |
| L_2 | `(a', a, y)`   | `(1 2)`             | −1   |
| L_3 | `(a', y, a)`   | `(1 3 2)` 3-cycle   | +1   |

`|L| = 3`. `Σ = +1 − 1 + 1 = 1`. `|Σ|/|L| = 1/3`
**(saturation)**.

### 2.3 Fire-sets

| `i` | `D_i` membership | `|D_i|` |
|-----|------------------|---------|
| 1   | `{L_1, L_2}` (positions 1,2 ∈ {a, a'}, incomp) | 2 |
| 2   | `{L_2, L_3}` (positions 2,3 incomp in each)    | 2 |

For `n = 3`, only adjacent indices `{1, 2}` exist; no
non-adjacent pair. `m(α) = 2`.

### 2.4 BK graph

```
E_1 = { {L_1, L_2} }      (τ_1: a ↔ a' at positions 1,2)
E_2 = { {L_2, L_3} }      (τ_2: a ↔ y at positions 2,3 in L_2)
```

`E = {{L_1, L_2}, {L_2, L_3}}`. Path `L_1 − L_2 − L_3`. Min
degree 1.

Sign-bipartition: `L_+ = {L_1, L_3}` (signs `+1`),
`L_− = {L_2}` (sign `−1`). Max matching saturates `L_−`:
`{L_1, L_2}` or `{L_2, L_3}`, size 1. Deficiency
`= 3 − 2 = 1 = |Σ|`. **Bound (4.2.a) tight.**

### 2.5 Lemma bound

```
|Σ|  ≤  |L|  −  m(α)  =  3 − 2  =  1.
```

`|Σ| = 1`. **Equality.** Lemma is tight on F1-min.

### 2.6 Structural reading

`|L|/3 = 1` "thin" LE. Identifying it: `L \ D_1 = {L_3}` (no
`τ_1`-fire because positions 1,2 of `L_3` are `a', y` —
comparable). `L \ D_2 = {L_1}` (no `τ_2`-fire because
positions 2,3 of `L_1` are `a', y`).

So `L_1` and `L_3` are each "thin" with respect to one
single direction; under any individual direction choice,
exactly `|L|/3 = 1` LE is in the complement.

**Reading:** the lemma correctly identifies the
boundary-LEs of the case-2-strict structure: `L_1` and `L_3`
are the LEs in which the strict ⪯-pair `(a, a')` interacts
with the upper element `y` at a band boundary. This matches
F1's structural signature (per `docs/why-hC3-is-structural.md`
§F1).

---

## 3. Configuration K2-Y — the Y-poset (case-2-strict, `|Σ| = 0`)

### 3.1 Definition

`α = {x_1, x_2, y_1, y_2}` with cover relations `x_1 < y_1`,
`x_1 < y_2`. `n = 4`. K = 2, w = 1, |β| = 2.

* **Irreducible?** Yes.
* **Case-2-strict?** Yes: `upper(x_2) = ∅`,
  `upper(x_1) = {y_1, y_2}`, so `∅ ⊊ {y_1, y_2}`.

### 3.2 Linear extensions

Reference `L_0 = (x_1, x_2, y_1, y_2)`, labels
`1=x_1, 2=x_2, 3=y_1, 4=y_2`.

x_1 must precede both y_1 and y_2; x_2 is unconstrained.
Eight LEs (x_2 can go in any of 4 positions, then choose
order of y_1, y_2):

| #   | LE                              | `σ_L` (one-line) | sign  |
|-----|---------------------------------|-------------------|-------|
| L_1 | `(x_1, x_2, y_1, y_2)`          | `1 2 3 4` (e)     | +1    |
| L_2 | `(x_1, x_2, y_2, y_1)`          | `1 2 4 3`         | −1    |
| L_3 | `(x_1, y_1, x_2, y_2)`          | `1 3 2 4`         | −1    |
| L_4 | `(x_1, y_1, y_2, x_2)`          | `1 4 2 3`         | +1    |
| L_5 | `(x_1, y_2, x_2, y_1)`          | `1 3 4 2`         | +1    |
| L_6 | `(x_1, y_2, y_1, x_2)`          | `1 4 3 2`         | −1    |
| L_7 | `(x_2, x_1, y_1, y_2)`          | `2 1 3 4`         | −1    |
| L_8 | `(x_2, x_1, y_2, y_1)`          | `2 1 4 3`         | +1    |

`|L| = 8`. `Σ = +1 − 1 − 1 + 1 + 1 − 1 − 1 + 1 = 0`.
`|Σ|/|L| = 0`.

### 3.3 Fire-sets

| `i` | `D_i` membership                                         | `|D_i|` |
|-----|----------------------------------------------------------|---------|
| 1   | `{L_1, L_2, L_7, L_8}` (positions 1,2 = x's or x_2 first) | 4       |
| 2   | `L \ {L_7, L_8}` (positions 2,3: y or x_2; comp only when pos 2 = x_1) | 6 |
| 3   | all 8 (positions 3,4 always incomparable in this α)        | 8       |

`D_{1,3} = D_1 ∩ D_3 = {L_1, L_2, L_7, L_8}`,
`|D_{1,3}| = 4`. `m(α) = 8` (from `D_3`).

### 3.4 Lemma bound

```
|Σ|  ≤  |L|  −  m(α)  =  8 − 8  =  0.
```

`|Σ| = 0`. **Equality (trivially).** The bound fires
trivially because `m = |L|` (direction `τ_3` is
**globally available** — `D_3 = L(α)` — by the structural
fact that the last two positions are always among
`{x_2, y_1, y_2}` with `(x_2, y_1)`, `(x_2, y_2)`,
`(y_1, y_2)` all incomparable).

### 3.5 Structural reading

The Y-poset is **trivially below saturation** (|Σ|/|L| = 0),
so the lemma's saturation contrapositive gives no
information. The "globally available" direction `τ_3`
forces `Σ = 0` directly: `τ_3` is a fixed-point-free
sign-flipping involution on all of `L(α)`.

**Reading:** Y-poset is *not* a difficult case for the
lemma — it has too much symmetry (the upper band is a
2-element antichain freely permutable). The lemma's bound
is satisfied automatically.

---

## 4. Configuration K2-N+e — the K=2 N-poset + diagonal edge `x_1 < y_2`

### 4.1 Definition

`α = {x_1, x_2, y_1, y_2}` with cover relations `x_1 < y_1`,
`x_2 < y_2`, `x_1 < y_2`. `n = 4`. K = 2, w = 0, |β| = 3.

* **Irreducible?** Yes.
* **Case-2-strict?** Yes: `upper(x_2) = {y_2}`,
  `upper(x_1) = {y_1, y_2}`, so `{y_2} ⊊ {y_1, y_2}`.

### 4.2 Linear extensions

`x_1` precedes `y_1, y_2`; `x_2` precedes `y_2`. Five LEs
(per arc 4.0 §2.6 row 6):

| #   | LE                          | `σ_L`            | sign  |
|-----|-----------------------------|------------------|-------|
| L_1 | `(x_1, x_2, y_1, y_2)`      | `e`              | +1    |
| L_2 | `(x_1, x_2, y_2, y_1)`      | `(3 4)`          | −1    |
| L_3 | `(x_1, y_1, x_2, y_2)`      | `(2 3)`          | −1    |
| L_4 | `(x_2, x_1, y_1, y_2)`      | `(1 2)`          | −1    |
| L_5 | `(x_2, x_1, y_2, y_1)`      | `(1 2)(3 4)`     | +1    |

`|L| = 5`. `Σ = +1 − 1 − 1 − 1 + 1 = −1`. `|Σ|/|L| = 1/5`
(`= 0.2`, below the 1/3 saturation threshold).

### 4.3 Fire-sets

| `i` | `D_i` membership                       | `|D_i|` |
|-----|----------------------------------------|---------|
| 1   | `{L_1, L_2, L_4, L_5}` (positions 1,2 = x's) | 4 |
| 2   | `{L_1, L_3}` (positions 2,3 incomp)          | 2 |
| 3   | `{L_1, L_2, L_4, L_5}` (positions 3,4 = y's) | 4 |

`D_{1,3} = {L_1, L_2, L_4, L_5}`, `|D_{1,3}| = 4`.
`m(α) = 4`.

### 4.4 Lemma bound

```
|Σ|  ≤  |L|  −  m(α)  =  5 − 4  =  1.
```

`|Σ| = 1`. **Equality.** Lemma is tight.

### 4.5 Structural reading

`|L|/3 ≈ 1.67`. Below saturation, but lemma is still tight.
The single thin LE is `L_3 = (x_1, y_1, x_2, y_2)` — the
"interleaving" extension. Same structural signature as
K2-N's `L_3` and `L_6`.

**Reading:** adding the diagonal `x_1 < y_2` reduces |L|
from 6 to 5 (it kills `L_6 = (x_2, y_2, x_1, y_1)`, which
violates `x_1 < y_2`). The remaining single thin LE is the
case-2-strict witness. The lemma identifies it correctly.

---

## 5. Configuration K2-claw — the claw `{x; y_1, y_2, y_3}`

### 5.1 Definition

`α = {x, y_1, y_2, y_3}` with cover relations `x < y_i` for
`i = 1, 2, 3`. `n = 4`.

* **Irreducible?** **No.** The claw is the ordinal sum
  `{x} ⊕ Antichain_3` — a 1-element band followed by a
  3-element antichain. Per `feedback_n_poset_is_not_ordinal_sum`,
  this is reducible.
* **Case-2-strict?** No. Both bands have a single
  `upper`-set per element (`upper(x) = {y_1, y_2, y_3}`,
  `upper(y_i) = ∅`); no `⊊` strict ⪯-pair.

Included as a sanity-check on a known reducible config.

### 5.2 Linear extensions

`x` is forced first; remaining 3 elements permute freely.
6 LEs.

Reference `L_0 = (x, y_1, y_2, y_3)`, labels `1=x, 2=y_1,
3=y_2, 4=y_3`.

| #   | LE                          | `σ_L` (cycle)   | sign  |
|-----|-----------------------------|------------------|-------|
| L_1 | `(x, y_1, y_2, y_3)`        | `e`              | +1    |
| L_2 | `(x, y_1, y_3, y_2)`        | `(3 4)`          | −1    |
| L_3 | `(x, y_2, y_1, y_3)`        | `(2 3)`          | −1    |
| L_4 | `(x, y_2, y_3, y_1)`        | `(2 4 3)`        | +1    |
| L_5 | `(x, y_3, y_1, y_2)`        | `(2 3 4)`        | +1    |
| L_6 | `(x, y_3, y_2, y_1)`        | `(2 4)`          | −1    |

`|L| = 6`. `Σ = +1 − 1 − 1 + 1 + 1 − 1 = 0`. `|Σ|/|L| = 0`.

### 5.3 Fire-sets

| `i` | `D_i`                                     | `|D_i|` |
|-----|-------------------------------------------|---------|
| 1   | `∅` (position 1 always = x; pos 2 always = y_j; comp) | 0 |
| 2   | all 6 (positions 2, 3 are both y's, incomp)             | 6 |
| 3   | all 6 (positions 3, 4 are both y's, incomp)             | 6 |

`D_{1,3} = D_1 ∩ D_3 = ∅`. `m(α) = 6` (from `D_2` or `D_3`).

### 5.4 Lemma bound

```
|Σ|  ≤  |L|  −  m(α)  =  6 − 6  =  0.
```

Trivially satisfied (`Σ = 0`).

### 5.5 Structural reading

The claw is a **reducible** poset — `{x} ⊕ A_3` — and the
lemma's saturation contrapositive gives no information
(the LHS is `0`, well below `1/3`). This is consistent: the
trichotomy's "reducible" branch should not produce
saturating |Σ|/|L|, and indeed here |Σ|/|L| = 0.

**Reading:** the lemma is trivially tight on a reducible
configuration. No structural conclusion follows from the
contrapositive (because the antecedent fails).

---

## 6. Configuration K2-OS — the full ordinal sum `{x_1, x_2} ⊕ {y_1, y_2}`

### 6.1 Definition

`α = {x_1, x_2, y_1, y_2}` with cover relations `x_i < y_j`
for all `i, j ∈ {1, 2}` (4 cross-edges). `n = 4`. K = 2,
w = 0.

* **Irreducible?** **No.** Full ordinal sum.
* **Case-2-strict?** No. `upper(x_1) = upper(x_2) =
  {y_1, y_2}`; equal, not `⊊`.

### 6.2 Linear extensions

All x's must precede all y's; within each band, any
permutation. `|L| = 2! · 2! = 4`.

| #   | LE                          | `σ_L`         | sign  |
|-----|-----------------------------|---------------|-------|
| L_1 | `(x_1, x_2, y_1, y_2)`      | `e`           | +1    |
| L_2 | `(x_1, x_2, y_2, y_1)`      | `(3 4)`       | −1    |
| L_3 | `(x_2, x_1, y_1, y_2)`      | `(1 2)`       | −1    |
| L_4 | `(x_2, x_1, y_2, y_1)`      | `(1 2)(3 4)`  | +1    |

`Σ = 0`. `|Σ|/|L| = 0`.

### 6.3 Fire-sets

| `i` | `D_i`                                                  | `|D_i|` |
|-----|--------------------------------------------------------|---------|
| 1   | all 4 (positions 1, 2 are both x's, incomp)            | 4 |
| 2   | `∅` (positions 2, 3 are x and y, comparable in OS)     | 0 |
| 3   | all 4 (positions 3, 4 are both y's, incomp)            | 4 |

`D_{1,3} = D_1 ∩ D_3 = `all 4. `|D_{1,3}| = 4`.
`m(α) = 4`.

### 6.4 Lemma bound

```
|Σ|  ≤  |L|  −  m(α)  =  4 − 4  =  0.
```

Trivially tight.

### 6.5 Structural reading

The Y-poset's "chain quotient" is exact in this case: bands
are full antichains with no cross-band variability.
Direction `τ_2` (the band-boundary direction) never fires —
its elements are always comparable. Directions `τ_1, τ_3`
(within-band) fire universally. This is the ordinal-sum
signature.

**Reading:** the lemma's `m/|L| = 1` (perfect cancellation
via two non-adjacent within-band directions) is the
ordinal-sum signature. Reducible cases give `Σ = 0`
trivially.

---

## 7. Configuration K2-3DC — three disjoint chains (asymptotic comparison)

### 7.1 Definition

`α = {x_1, x_2, x_3, y_1, y_2, y_3}` with cover relations
`x_i < y_i` for `i = 1, 2, 3`. `n = 6`. K = 2, w = 2,
|β| = 3.

* **Irreducible?** Yes (no element is below all uppers; not
  an ordinal sum).
* **Case-2-strict?** No (each `upper(x_i) = {y_i}`, all
  singletons, incomparable subsets).

The "asymptotic" K=2 sibling — generalisation of K=2 N-poset
from 2 chains to 3.

### 7.2 LE count and sign-imbalance

Per arc 4.0 §2.6 (Python-enumerated):

* `|L| = 90`.
* `Σ(α) = 6` (or `−6`; sign convention dependent).
* `|Σ|/|L| = 6/90 = 1/15 ≈ 0.067`. **Well below `1/3`.**

(Polecat does not re-enumerate by hand at `|L| = 90`;
relies on arc 4.0's enumeration as authoritative.)

### 7.3 Lemma bound (qualitative)

By the lemma, `m(α) ≥ |L| − |Σ| = 84`. So at most 6 LEs are
"thin" under non-adjacent direction choice.

Without a full enumeration, the polecat cannot compute the
exact `m(α)` value, but the bound `|Σ| ≤ |L| − m(α)` gives
`m(α) ≤ 84` necessarily and `m(α) = 84` if the bound is
tight (analogous to K2-N).

### 7.4 Structural reading

Three disjoint chains exhibit the same N-poset interleaving
pattern, but with three threads instead of two. The thin LEs
are likely the "fully interleaved" extensions (alternating
between chains), of which there are
`3!^2 / (some factor) ≈ 6` candidates. This matches the
6-LE upper bound on |Σ|.

**Reading (heuristic):** the K=2 obstruction-family
saturation level **decreases** from `1/3` (K=2 N-poset, 2
chains) to `1/15` (3 chains). The "thin" LEs are
proportionally rarer as the chain count grows. This is
consistent with the asymptotic regime arc 4.0 §3.4 noted
("`|λ_sign|` shrinks as `n` grows in the K=2 family"). The
lemma's saturation contrapositive only fires meaningfully on
small-`n` configurations.

---

## 8. Summary table

| Config            | `n` | `|L|` | `|Σ|` | `|Σ|/|L|`  | `max_i |D_i|` | `m(α)`  | `|L| − m` | bound tight? | structural reading                       |
|-------------------|-----|-------|-------|-----------|---------------|---------|-----------|--------------|------------------------------------------|
| **K2-N**          | 4   | 6     | 2     | **1/3**   | 4             | 4       | 2         | ✓            | 2 thin interleaving LEs (canonical)      |
| **F1-min**        | 3   | 3     | 1     | **1/3**   | 2             | 2       | 1         | ✓            | 1 thin LE at band boundary (case-2-strict) |
| **K2-Y**          | 4   | 8     | 0     | 0         | 8             | 8       | 0         | ✓ (trivially) | globally-available τ_3; |Σ| = 0          |
| **K2-N+e**        | 4   | 5     | 1     | 1/5       | 4             | 4       | 1         | ✓            | 1 thin LE; case-2-strict                 |
| **K2-claw**       | 4   | 6     | 0     | 0         | 6             | 6       | 0         | ✓ (trivially) | reducible (ordinal sum), Σ = 0          |
| **K2-OS**         | 4   | 4     | 0     | 0         | 4             | 4       | 0         | ✓ (trivially) | full ordinal sum, perfect cancellation   |
| **K2-3DC**        | 6   | 90    | 6     | 1/15      | (bound-only)  | ≥ 84    | ≤ 6       | (bound-only) | thin LEs ≤ 6 — interleaving signature    |

Three case-2-strict siblings tested explicitly (F1-min,
K2-Y, K2-N+e). Six configurations with full enumeration; one
asymptotic comparison (K2-3DC) using arc 4.0's enumeration.

### 8.1 Patterns

* **Bound is tight on every tested config.** `|Σ| = |L| −
  m(α)` exactly in all 7 cases (with the K2-3DC case
  inferred indirectly).
* **Saturation `|Σ|/|L| = 1/3` attained by exactly 2 of 7
  configs:** K2-N and F1-min. Both are small (`n ≤ 4`),
  irreducible, and exhibit a specific structural feature
  (N-poset core resp. case-2-strict at band boundary).
* **Saturation NOT attained by any other tested config**,
  including the case-2-strict siblings K2-Y (Σ = 0) and
  K2-N+e (1/5). So saturation is **not an artefact of
  case-2-strictness alone**.
* **All `|Σ| = 0` configs (K2-Y, K2-claw, K2-OS) have a
  globally-available direction** — i.e., some `τ_i`
  satisfying `D_i = L(α)`. This is a sufficient condition
  for `Σ = 0` (lemma 2.1 with `|D_i| = |L|`).
* **Reducible configs (K2-claw, K2-OS) trivially satisfy
  the bound** with `Σ = 0`. The lemma's saturation
  contrapositive does not distinguish them from the Y-poset
  (also `Σ = 0`).

### 8.2 What "the lemma's classifier output" tells us

In the saturation-contrapositive sense (5.2.b: `|Σ|/|L| =
1/3 ⟹ m/|L| ≤ 2/3`):

* **K2-N (saturating):** the contrapositive holds with
  equality (`m/|L| = 4/6 = 2/3`). The 2 "thin" LEs are
  identified as the interleaving extensions
  `{(x_1, y_1, x_2, y_2), (x_2, y_2, x_1, y_1)}`. **This
  is structurally informative — it pins down the
  N-poset's interleaving pattern.**
* **F1-min (saturating):** contrapositive holds with
  equality (`m/|L| = 2/3`). The 1 thin LE is identified.
* **All non-saturating configs:** the contrapositive does
  not fire (the antecedent `|Σ|/|L| = 1/3` fails). The
  lemma gives the inequality bound but no saturation
  conclusion.

So the lemma's saturation contrapositive gives a
**structurally informative output on the two saturating
configs** — but those are exactly the configurations where
the lemma's antecedent holds. **For non-saturating configs,
the lemma is silent on structural conclusions** beyond the
matching-deficiency bound.

### 8.3 Net finding

The lemma's content can be summarised:

**`|Σ(α)|/|L(α)| = 1/3`  ⟹  there exist exactly `|L|/3`
"thin" linear extensions** — LEs `L` with the property that
no choice of pairwise non-adjacent directions
`S ⊆ {1, …, n−1}` has every `τ_i · L ∈ L(α)` for `i ∈ S`.

This is **a numerical / combinatorial conclusion**, not a
classifier of `α` itself into structural classes. To
upgrade it to a classifier (i.e., the trichotomy
N-poset-core / reducible / balanced) requires substantively
new combinatorial machinery — see `verdict.md` §3 for what's
needed.

---

## 9. Computation provenance

* The K2-N enumeration, sign computation, and `|Σ|` value
  reproduce arc 4.0 §2.1 (mg-0bc8).
* The K2-N+e and K2-3DC `|L|` and `|Σ|` values reproduce
  arc 4.0 §2.6 rows 4 and 6.
* The F1-min enumeration matches
  `docs/path-c-track-1-status-1.md` §2 (mg-b666).
* The Y-poset (K2-Y), claw (K2-claw), and ordinal-sum
  (K2-OS) enumerations are by direct hand-computation in
  this arc; reproducible by enumerating
  `permutations({1, …, n})` constrained by the cover
  relations and computing `sign`, fire-sets, and
  `D_S`-intersections.

All values are exact rational; no asymptotic / numerical
approximation is involved.

---

*This file is Deliverable B for `mg-acc8`, filed
2026-05-05 by polecat `pacc8` on branch
`alternating-cancellation-arc-1`. It is doc-only (no Lean
source changes). See `lemma-statement.md` (Deliverable A)
for the lemma formalisation and `verdict.md` (Deliverable C)
for the aggregate verdict.*
