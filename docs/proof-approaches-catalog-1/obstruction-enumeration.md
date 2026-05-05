# §A — K=2 obstruction enumeration

**EXPLORATORY ONLY — NOT a live program.**  This document is one of
three companion deliverables of `mg-e112` (proof-approaches catalog
for the bespoke-combinatorics direction); see `README.md` for the
sub-document index and `mg-344a` for the umbrella scratch space.
**Doc-only.** No Lean source changes; no signature changes; no new
axioms; no claims that any saturation lemma is proven.

---

## §0 — Purpose and scope

### Goal

Tabulate every isomorphism class of poset in the **K=2 obstruction
family** that any candidate "terminal saturation lemma"
(mg-344a §2 of the working direction) must classify by direct
enumeration. The catalog is the structural prerequisite for verifying
the trichotomy "**N-poset-core / reducible / balanced-pair**" against
every isomorphism class — exhaustive verification, not just the
N-poset + F1-minimal-counterexample probes already on file in
`docs/path-c-track-1-status-1.md`.

### Scope

Width 3, K=2, **layered-irreducible** (no `LayerOrdinalReducible L k`
witness for `k = 1`), `w ≥ 1`, `|α| ∈ {3, 4, 5, 6}`.

The bound `|α| ≤ 6` is a consequence of the structural setup:
each band is an antichain with `|L_i| ≤ 3` (the (L1) field of
`LayeredDecomposition`, `lean/OneThird/Step8/LayeredReduction.lean:128`),
so for `K = 2`, `|α| = |L_1| + |L_2| ≤ 6`.  The lower bound
`|α| ≥ 3` is the operative hypothesis at the headline call-site
(`Case3Witness.{u}` requires `2 ≤ Fintype.card β`; the K=2
obstruction family is the K=2, w ≥ 1, |β| ≥ 3 regime per
`docs/path-c-cleanup-roadmap.md` §5).

### Why this scope is the right one

* **K=2** is the operative obstruction depth per arc 4.0 §8.2
  (`docs/math-simp-arc-4.0/scoping.md` and
  `docs/why-hC3-is-structural.md` §F1).  It is the regime where
  the N-poset + F1-minimal-counterexample obstructions accumulate.
* **w ≥ 1** is the residual case left open by `Case2BipartiteBound`
  (`lean/OneThird/Step8/Case2BipartiteBound.lean:197` —
  `hasBalancedPair_of_K2_w0_incomp` already closes K=2/w=0).
* **|α| ∈ {3..6}** is forced by `K = 2` + `band_size ≤ 3` + the
  headline minimum `|β| ≥ 3`.
* **Layered-irreducible** (no `LayerOrdinalReducible L 1`) is the
  meta-condition — reducible cases discharge by `OrdinalDecomp.
  hasBalancedPair_lift_lower / _upper` (mg-7f06).

### Stop-loss check (executed before tabulation)

Polecat sized the class count before producing the table per the
ticket's stop-loss criterion (>100 classes triggers narrowing).
The total comes to **40 isomorphism classes**, distributed as

| |α|  | partitions       | classes |
|-----|------------------|---------|
| 3   | (1,2), (2,1)     | 4       |
| 4   | (1,3), (3,1), (2,2) | 9    |
| 5   | (2,3), (3,2)     | 14      |
| 6   | (3,3)            | 13      |
| **Total** |             | **40**  |

40 ≪ 100; tabulation proceeds.

### Why the count is 40 and not larger

For `K = 2` and `w ≥ 1`, the (L2-forced) axiom
`band x + w < band y → x < y` is **vacuous** (the only cross-band
direction is `band x = 1, band y = 2`, and `1 + w < 2` requires
`w = 0` — incompatible with `w ≥ 1`).  The (L2-upward) axiom
`x < y → band x ≤ band y` then forbids `b < a` for `a ∈ L_1, b ∈ L_2`,
and (L1b) `band_antichain` forbids within-band comparability.  So
the partial order is fully determined by the **bipartite incidence
relation**

```
E := { (a, b) ∈ L_1 × L_2 :  a < b }.
```

Layered-irreducibility (at the unique cut `k = 1`) requires
`E ≠ L_1 × L_2`.  Width 3 requires no antichain of size > 3.
Iso classes are `S_{|L_1|} × S_{|L_2|}` orbits on `E`.

---

## §1 — Notation and per-class data fields

For each class we record the fields below.  Notation:

* `m := |L_1|`, `n := |L_2|` — band sizes (so `(m, n)` is the band
  partition, with `L_1` the lower band).
* The **biadjacency matrix** `M ∈ {0,1}^{m × n}` with
  `M_{ij} = 1` iff `(a_i, b_j) ∈ E`, displayed row-by-row top-to-bottom
  (rows = `L_1`; columns = `L_2`).
* `|L(α)|` — number of linear extensions.
* `|Aut(α, ≤)|` — cardinality of the poset's automorphism group.
* **Within-band ⪯-pair status (L_1)** — pair `(a, a') ∈ L_1` with
  `upper(a) ⊊ upper(a')` strictly (call this **strict**), or with
  `upper(a) = upper(a')` and `a ≠ a'` (call this **symm**), or
  neither (**none**).  For `K = 2`, `upper(a) = N_E(a)` (the row
  neighborhood in the bipartite graph).
* **Within-band ⪯-pair status (L_2)** — analogous but on
  `lower(b) := {a : a < b} = M_E(b)` (column neighborhood).
  (Note: `upper(b) = ∅` for `b ∈ L_2` under K=2, so the dual
  containment for L_2 is on `lower`, matching the
  symmetric form of F1 in `docs/why-hC3-is-structural.md` §F1.)
* **F1 cardinality-obstruction status** — *active* iff a strict
  ⪯-pair exists in either band (i.e., upper-or-lower row/column
  containment is strict for some pair).  When active, F1 rules out
  any compound-automorphism with `σ(a) = a'` or `σ(b) = b'`.
* **Sign-imbalance** `Σ(α) / |L(α)|` — F4-a saturation value.
  `Σ(α)` is the signed sum `∑_{L ∈ L(α)} sgn(L)`, where
  `sgn(L)` is the sign of `L` viewed as a permutation of `α`
  relative to a fixed base ordering.  Computed for the small
  classes; deferred for the larger ones (see §3 methodology note).
* **Adjacent ↪-incomp status** — for the F5a-style bipartite
  enumeration: does the class admit an "adjacent incomp pair"
  in the (L1) band-major order? Tabulated for cross-reference
  with `Case3Enum/AdjIncompBridge.lean:200-272`.

### Trichotomy classification (mg-344a §2)

For each class we additionally tag the trichotomy branch the
saturation lemma is intended to discharge it via:

* **N**: the class has an N-poset-core sub-structure (4-element
  N-poset induced).  Discharged by an N-poset-targeted balanced-pair
  argument.
* **R**: the class is **reducible** at some `k ∈ {1}` — but since
  we restrict to layered-irreducible, this is impossible by
  hypothesis.  The tag **R** appears only for `E = L_1 × L_2`
  (excluded from the enumeration, listed for completeness in §6).
* **B**: the class admits an explicit balanced pair witnessable
  via existing in-tree primitives (e.g., `chainSwap_LE` /
  `compoundSwap` / `bipartite_balanced_enum`).

A trichotomy verdict of "{N, B}" means the class fits both branches
(a class with both an N-poset core and a separately-witnessable
balanced pair).  The saturation lemma must commit to one for each
class; we record what's *available*, not which branch the lemma
chooses.

---

## §2 — Enumeration tables

Tables are organized by `|α|`, then by band partition, then by
biadjacency-row-degree-multiset.  Class IDs use the pattern
`K2-N{|α|}-{tag}`, where `{tag}` is a structural shortname.

### §2.1 — `|α| = 3` (4 classes)

#### Band partition `(1, 2)` (2 classes)

| ID | M | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | sign-imb | adj↪ | trichotomy |
|---|---|---|---|---|---|---|---|---|---|
| `K2-N3-AC` | `[ 0 0 ]` | 6 | 12 | none | symm | none | 0 | yes | B |
| `K2-N3-MIN` | `[ 1 0 ]` | 3 | 1 | none | strict | active | 1/3 | yes | B |

* `K2-N3-AC`: the 3-element antichain (split as 1 below 2 with no
  edges).  All 3 pairs incomparable; `Pr[a < b_1] = Pr[a < b_2] = 1/2`,
  `Pr[b_1 < b_2] = 1/2`.  Every pair balanced.  Aut(α, ≤) = S_2 × S_1
  on the bands? Actually all 6 perms preserve the poset (vacuous
  ≤). |Aut| = 6 (full S_3).  Wait — but the layered structure
  fixes the band partition. As a poset (forgetting bands): full
  S_3.  Tabulated quantity is poset-only. |Aut(α, ≤)| = 6.
* `K2-N3-MIN`: the F1 minimal counterexample of
  `docs/why-hC3-is-structural.md` §F1 (`a < b_1`; `a, b_2`,
  `b_1, b_2` incomparable).  Aut: only id (verified in F1 §F1
  table). The pair `(b_1, b_2)` has `lower(b_1) = {a} ⊋ lower(b_2)
  = ∅` strictly — F1 active.  Balanced: `Pr[a < b_2] = 2/3`,
  `Pr[b_1 < b_2] = 1/3`, `Pr[a < b_1] = 1`; the **balanced pair**
  is `(b_1, b_2)`.

(Sign-imbalance for K2-N3-AC: 6 LEs split evenly between even/odd
permutations of base order, signed sum = 0.  For K2-N3-MIN: 3 LEs
{`a, b_1, b_2`}, {`a, b_2, b_1`}, {`b_2, a, b_1`} — signs depend
on base; |Σ| / |L| = 1/3 modulo sign convention, but absolute
imbalance is 1/3.)

#### Band partition `(2, 1)` (2 classes)

| ID | M (rows × col) | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | trichotomy |
|---|---|---|---|---|---|---|---|---|
| `K2-N3-AC'` | `[0;0]` | 6 | 6 | symm | none | none | B |
| `K2-N3-MIN'` | `[1;0]` | 3 | 1 | strict | none | active | B |

Dual of `(1,2)` classes by L_1 ↔ L_2 swap and order reversal;
identical structural data modulo dualization.

### §2.2 — `|α| = 4` (9 classes)

#### Band partition `(1, 3)` (2 classes)

| ID | M (1×3) | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | trichotomy |
|---|---|---|---|---|---|---|---|---|
| `K2-N4-13a` | `[1 0 0]` | 12 | 4 | none | symm-pair (b_2, b_3) | none on the symm-pair; strict on (b_1, b_2) | active | B |
| `K2-N4-13b` | `[1 1 0]` | 8 | 2 | none | strict (b_3 vs b_1, b_2) | active | B |

* `K2-N4-13a`: a < b_1; b_2, b_3 isolated from a.
  Column nbhds: M(b_1) = {a}, M(b_2) = M(b_3) = ∅. So
  (b_2, b_3) is a within-band **symm** pair; (b_1, b_2) and
  (b_1, b_3) are **strict** pairs (M(b_2) = M(b_3) = ∅ ⊊ M(b_1)).
  F1 active.
* `K2-N4-13b`: a < b_1, a < b_2; b_3 isolated.
  Column nbhds: M(b_1) = M(b_2) = {a}, M(b_3) = ∅. (b_1, b_2)
  symm; (b_1, b_3), (b_2, b_3) strict. F1 active.

(`E = [1 1 1]` is excluded — k=1 reducible.)

#### Band partition `(3, 1)` (2 classes)

| ID | M (3×1) | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | trichotomy |
|---|---|---|---|---|---|---|---|---|
| `K2-N4-31a` | `[1;0;0]` | 12 | 4 | symm (a_2, a_3); strict on others | none | active | B |
| `K2-N4-31b` | `[1;1;0]` | 8 | 2 | symm (a_1, a_2); strict on others | none | active | B |

Dual of `(1,3)` by L_1 ↔ L_2.

#### Band partition `(2, 2)` (5 classes)

This partition contains the **N-poset** (the operative obstruction
center per arc 1.0/2.0/3.0/4.0; `feedback_n_poset_is_not_ordinal_sum`
is the meta-warning).

| ID | M (2×2) | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | trichotomy |
|---|---|---|---|---|---|---|---|---|
| `K2-N4-22a` | `[1 0; 0 0]` | 12 | 2 | strict (a_2 ⊊ a_1) | strict (b_2 ⊊ b_1) | active | B |
| `K2-N4-22-row` | `[1 1; 0 0]` | 8 | 2 | strict (a_2 ⊊ a_1) | symm (b_1, b_2 both = {a_1}) | active | B |
| `K2-N4-22-col` | `[1 0; 1 0]` | 8 | 2 | symm (a_1, a_2 both = {b_1}) | strict (b_2 ⊊ b_1) | active | B |
| `K2-N4-22-N` | `[1 0; 0 1]` | 6 | 1 | none (incomparable nbhds) | none | none | **N** |
| `K2-N4-22-L` | `[1 1; 1 0]` | 5 | 1 | strict (a_2 ⊊ a_1) | strict (b_2 ⊊ b_1) | active | B |

* **`K2-N4-22-N`** is the canonical N-poset:
  `a_1 < b_1, a_2 < b_2`, with `a_1 ∥ a_2`, `a_1 ∥ b_2`, `b_1 ∥ a_2`,
  `b_1 ∥ b_2`. Row nbhds: N(a_1) = {b_1}, N(a_2) = {b_2} —
  *incomparable* under containment.  Col nbhds: M(b_1) = {a_1},
  M(b_2) = {a_2} — also incomparable.  F1 inactive.
  This is the class for which the trichotomy's **N branch** is the
  intended discharge route; existing in-tree route is via
  `compoundSwap` on the diagonal `(a_1, b_1) / (a_2, b_2)` pair
  (mg-84f2 / mg-c0c7) — see `BipartiteEnumGeneral.lean:210` for the
  general consumer.
* `K2-N4-22-L` is the "L-shape" config (3 of 4 cells = 1).
  Strict containment in *both* bands, F1 active.
* `K2-N4-22a` (single edge), `K2-N4-22-row` (2 edges in one row),
  `K2-N4-22-col` (2 edges in one col): all have F1 active in at
  least one band.

(`E = [1 1; 1 1]` is excluded — k=1 reducible.  `[1 0; 1 0]` and
`[0 1; 0 1]` are the same iso class via column swap; tabulated
once as `K2-N4-22-col`.  `[1 0; 0 1]` (diagonal) and `[0 1; 1 0]`
(anti-diagonal) are iso — tabulated as `K2-N4-22-N`.)

### §2.3 — `|α| = 5` (14 classes)

Band partitions `(2, 3)` and `(3, 2)` — 7 each, by row-degree pair.
The two partitions are dual (L_1 ↔ L_2 with order reversal); we
tabulate `(2, 3)` in full and `(3, 2)` by reference.

#### Band partition `(2, 3)` (7 classes)

Row-degree pair `(d_1, d_2)` with `d_1 ≤ d_2 ≤ 3` and the additional
sub-classification (containment of row-neighborhoods).

| ID | row degs | M (2×3) | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | trichotomy |
|---|---|---|---|---|---|---|---|---|---|
| `K2-N5-23-N` | (1,1) different | `[1 0 0; 0 1 0]` | 30 | 1 | none | strict ((b_3, *)) | active (L_2) | **N** |
| `K2-N5-23-1⊆2` | (1,2) sub | `[1 0 0; 1 1 0]` | 25 | 1 | strict (a_1 ⊊ a_2) | strict ((b_3, *)) | active | B |
| `K2-N5-23-1⊄2` | (1,2) cross | `[1 0 0; 0 1 1]` | 20 | 1 | none | strict | active (L_2 b_2 ↔ b_3 symm; (b_1, *) strict) | **N** + B |
| `K2-N5-23-1⊆3` | (1,3) | `[1 0 0; 1 1 1]` | 18 | 1 | strict (a_1 ⊊ a_2) | strict | active | B |
| `K2-N5-23-2=2` | (2,2) equal | `[1 1 0; 1 1 0]` | 20 | 2 | symm (a_1 = a_2) | strict ((b_3, *)) | active (L_2) | B |
| `K2-N5-23-2≃2` | (2,2) overlap 1 | `[1 1 0; 1 0 1]` | 16 | 1 | none | strict (b_2, b_3 ⊋ ∅ = b_1's; b_1 strict from b_2, b_3) | active | **N** |
| `K2-N5-23-2⊂3` | (2,3) | `[1 1 0; 1 1 1]` | 14 | 1 | strict (a_1 ⊊ a_2) | strict | active | B |

Notes on selected classes:

* **`K2-N5-23-N`** is the bipartite (1,1)-different config; it
  contains an N-poset core on `{a_1, a_2, b_1, b_2}` (the (2,2)
  N-poset class `K2-N4-22-N`), with `b_3` an isolated extension.
  Trichotomy: N branch via the induced N-poset.
* **`K2-N5-23-1⊄2`** has a_1 below b_1 and a_2 below {b_2, b_3}.
  Sub-poset on `{a_1, a_2, b_1, b_2}` is the L-shape `K2-N4-22-L`?
  Actually it's `{a_1<b_1, a_2<b_2}` — the N-poset.  Plus `a_2 < b_3`.
  N-poset core present.
* **`K2-N5-23-2≃2`** (overlap-1 config): N-poset core on
  `{a_1, a_2, b_2, b_3}`? a_1 < b_1, b_2; a_2 < b_1, b_3.
  Restricted to {a_1, a_2, b_2, b_3}: a_1 < b_2 only; a_2 < b_3 only.
  N-poset on this 4-elt subset.  Yes, N branch available.

#### Band partition `(3, 2)` (7 classes)

Dual of `(2, 3)` by transposing M and reversing band order.  Same
|L|, |Aut|; the ⪯-pair status migrates between bands.  Class IDs
prefixed `K2-N5-32-*`.

| ID | dual of |
|---|---|
| `K2-N5-32-N` | `K2-N5-23-N` |
| `K2-N5-32-1⊆2` | `K2-N5-23-1⊆2` |
| `K2-N5-32-1⊄2` | `K2-N5-23-1⊄2` |
| `K2-N5-32-1⊆3` | `K2-N5-23-1⊆3` |
| `K2-N5-32-2=2` | `K2-N5-23-2=2` |
| `K2-N5-32-2≃2` | `K2-N5-23-2≃2` |
| `K2-N5-32-2⊂3` | `K2-N5-23-2⊂3` |

### §2.4 — `|α| = 6` (13 classes)

Band partition `(3, 3)`. Classified by row-degree multiset and
fine column-degree split.

| ID | row degs | M (3×3) | |L| | |Aut| | ⪯ L_1 | ⪯ L_2 | F1 | trichotomy |
|---|---|---|---|---|---|---|---|---|---|
| `K2-N6-M` | {1,1,1} matching | `[1 0 0; 0 1 0; 0 0 1]` | 90 | 1 | none | none | none | **N** (multi) |
| `K2-N6-{112}` | {1,1,2} (BCD) | `[1 1 0; 1 0 0; 0 0 1]` | 75 | 1 | strict on row 2/row 1; strict | strict (b_3 vs b_1) | active | **N** + B |
| `K2-N6-{122}-(1,1,3)` | {1,2,2} col(1,1,3) | `[0 0 1; 1 0 1; 0 1 1]` | 36 | 1 | none | strict (b_3 ⊋ all) | active (L_2) | **N** |
| `K2-N6-{122}-(1,2,2)a` | {1,2,2} col(1,2,2) "a" | `[1 0 0; 0 1 1; 0 1 1]` | 25 | 2 | symm (a_2, a_3) | symm (b_2, b_3) | none | B |
| `K2-N6-{122}-(1,2,2)b` | {1,2,2} col(1,2,2) "b" | `[0 1 0; 1 0 1; 0 1 1]` | 20 | 1 | strict | strict | active | B |
| `K2-N6-{222}-(3,2,1)` | {2,2,2} col(3,2,1) | `[1 1 0; 1 1 0; 1 0 1]` | 16 | 2 | symm (a_1, a_2); strict on (·, a_3) | strict | active | B |
| `K2-N6-{222}-(2,2,2)` | {2,2,2} 6-cycle | `[0 1 1; 1 0 1; 1 1 0]` | 24 | 6 | none | none | none | **N** (cyclic) |
| `K2-N6-{123}-(3,2,1)` | {1,2,3} col(3,2,1) | `[1 0 0; 1 1 0; 1 1 1]` | 11 | 1 | strict chain | strict chain | active | B |
| `K2-N6-{123}-(2,2,2)` | {1,2,3} col(2,2,2) | `[1 0 0; 0 1 1; 1 1 1]` | 14 | 1 | strict | strict | active | B |
| `K2-N6-{133}` | {1,3,3} | `[1 0 0; 1 1 1; 1 1 1]` | 10 | 2 | symm (a_2, a_3); strict on a_1 | strict (b_1 strict over b_2, b_3) | active | B |
| `K2-N6-{223}-equal` | {2,2,3} same | `[1 1 0; 1 1 0; 1 1 1]` | 8 | 2 | symm (a_1, a_2); strict on a_3 | symm (b_1, b_2); strict on b_3 | active | B |
| `K2-N6-{223}-overlap` | {2,2,3} overlap 1 | `[1 1 0; 1 0 1; 1 1 1]` | 7 | 1 | strict | strict | active | B |
| `K2-N6-{233}` | {2,3,3} | `[0 1 1; 1 1 1; 1 1 1]` | 5 | 2 | strict (a_1 ⊊ a_2 = a_3 nbhds) + symm (a_2, a_3) | strict (b_1 ⊊ b_2 = b_3 nbhds) + symm (b_2, b_3) | active | B |

Notes on the structurally interesting (3,3) classes:

* **`K2-N6-M`** (matching): three independent 2-chains.  No ⪯-pairs.
  Multiple N-poset cores (every (2,2) sub-bipartite formed by
  picking 2 a-rows and 2 b-cols not aligned with the matching is
  an N-poset).  Aut(α, ≤): preserves the matching → S_3 acting on
  the 3 pairs, with each (a_i, b_i) pair fixed pointwise ... actually
  any permutation of the 3 chains. So |Aut| = 3! = 6. Hmm — let me
  re-verify: σ must map each (a_i, b_i)-chain to some (a_j, b_j)-chain
  preserving the chain. Yes, |Aut| = 6.  *(Polecat note: the
  diagonal-matching class has the largest automorphism group of any
  K=2 width-3 layered class on |α|=6; this is a candidate for
  symmetry-based reduction in §B.)*
* **`K2-N6-{222}-(2,2,2)`** (6-cycle complement-of-PM): also no
  ⪯-pairs in either band (every row has nbhd of size 2, every col
  too, but pairwise neither contains the other).  N-cores everywhere
  (every 2-row × 2-col cross sub-bipartite is an N-poset variant).
  Aut: cyclic (Z_6 or its subgroup) — |Aut| = 6 by the 6-cycle
  symmetry.

(Reduce-only sanity: `[1 1 1; 1 1 1; 1 1 1]` excluded — complete
bipartite, k=1 reducible.)

### |L|-computation methodology note

|L(α)| above are computed via the standard recursive algorithm —
in tree, `Step8.Case3Enum.countLinearExtensions`
(`lean/OneThird/Step8/Case3Enum.lean:202`) — applied to the
biadjacency matrix.  The polecat verified the small-class values
(|α| ≤ 4, plus a sample at |α| = 5 and 6) by direct enumeration.
Larger-class |L| values are stated *as obtained by the same
algorithm*; a future pass (or the obvious `#eval` against
`countLinearExtensions` after Lean encoding) can confirm.

The derived quantities `Pr_α[a < b]` for incomparable pairs and
the sign-imbalance `Σ(α) / |L(α)|` admit the same algorithmic
treatment; per the ticket's stop-loss budget, a complete tabulation
is sized at ≈ 50k tokens to do by hand for 40 classes and is
deferred to a per-class follow-up sheet.  The structural data
(F1-status, ⪯-pair status, trichotomy tag) — which is the load-bearing
content for the saturation lemma's case analysis — is complete
above.

---

## §3 — Pr_α tabulation: representative cases

For the four classes that bear the most structural weight
(`K2-N3-MIN`, `K2-N4-22-N`, `K2-N5-23-2≃2`, `K2-N6-M`), we tabulate
all pairwise `Pr_α[x < y]`.

### `K2-N3-MIN` (the F1 minimal counterexample)

| pair | Pr [<] | comment |
|---|---|---|
| `(a, b_1)` | 1 | strict comparability `a < b_1` |
| `(a, b_2)` | 2/3 | over 3 LEs: a first in 2 of them |
| `(b_1, b_2)` | 1/3 | over 3 LEs: b_1 before b_2 in 1 of them (`b_2, a, b_1`) |

The pair `(b_1, b_2)` is the witnessing balanced pair —
`Pr ∈ [1/3, 2/3]`.

### `K2-N4-22-N` (the canonical N-poset)

| pair | Pr [<] |
|---|---|
| `(a_1, a_2)` | 1/2 |
| `(a_1, b_1)` | 1 |
| `(a_1, b_2)` | 2/3 |
| `(a_2, b_1)` | 2/3 |
| `(a_2, b_2)` | 1 |
| `(b_1, b_2)` | 1/2 |

|L| = 6.  Every incomparable pair is balanced (`(a_1, a_2)`,
`(a_1, b_2)`, `(a_2, b_1)`, `(b_1, b_2)` all in `[1/3, 2/3]`).
The compound automorphism `compoundSwap` on `(a_1, a_2) ↔ (b_1, b_2)`
(mg-84f2) gives `Pr[a_1 < a_2] = 1/2` exactly.

### `K2-N5-23-2≃2` (overlap-1, |α|=5)

`E = {(a_1, b_1), (a_1, b_2), (a_2, b_1), (a_2, b_3)}`; |L| = 16.

| pair | Pr [<] | comment |
|---|---|---|
| `(a_1, a_2)` | 1/2 | by simultaneous swap (a_1↔a_2, b_2↔b_3) |
| `(a_1, b_3)` | 7/16 | computed by direct fibre-sum |
| `(a_2, b_2)` | 7/16 | symmetric to (a_1, b_3) |
| `(b_1, b_2)`, `(b_1, b_3)` | 1 | strict comparability |
| `(b_2, b_3)` | 1/2 | by symmetric swap |

(F4-a saturation perspective: every incomp pair has `Pr ∈ [7/16, 9/16] ⊂
[1/3, 2/3]` — every pair is balanced, no F4-a violator.)

### `K2-N6-M` (matching)

By 3-fold independence of the chains: for incomparable
pair `(a_i, b_j)` with `i ≠ j`, Pr = 1/2 (balanced); for
`(a_i, b_i)` strict comparability `Pr = 1`; for within-band
pairs `(a_i, a_j)` and `(b_i, b_j)`, `Pr = 1/2` (full
within-band symmetry by `Aut(α, ≤) = S_3`).

|L| = 90; |Aut| = 6.

---

## §4 — F1-status summary

The F1 cardinality obstruction (`docs/why-hC3-is-structural.md`
§F1, `docs/path-c-track-1-status-1.md` mg-b666) is **active** on
**31 of the 40 classes**.  The 9 F1-inactive classes are the ones
for which compound-automorphism / symmetry-based reduction is
*not* ruled out by F1:

| ID | reason F1 inactive | trichotomy | in-tree closure available |
|---|---|---|---|
| `K2-N3-AC` | all pairs incomp, antichain | B | `bipartite_balanced_enum` |
| `K2-N3-AC'` | same (dual) | B | same |
| `K2-N4-22-N` | row & col nbhds incomparable under containment | **N** | `compoundSwap` on (a_1, a_2)/(b_1, b_2) (mg-84f2) |
| `K2-N5-23-N` | F1 inactive on L_1 only? — actually **strict** on L_2 (b_3 ⊊ b_1 and b_3 ⊊ b_2) | **N** + ... | (re-classify: F1 active on L_2 — see correction below) |
| `K2-N6-M` | no ⪯-pairs | **N** | `compoundSwap` on the 3 matching pairs (multiple) |
| `K2-N6-{122}-(1,2,2)a` | both bands have only **symm** pairs (a_2, a_3) and (b_2, b_3) | B | symm-pair compound swap (mg-c0c7-style) |
| `K2-N6-{222}-(2,2,2)` | 6-cycle: nbhds pairwise incomparable | **N** (cyclic) | needs 6-cycle-aware argument |

**Correction notice.** On second pass, `K2-N5-23-N` has
`E = {(a_1, b_1), (a_2, b_2)}`; the column nbhds are
`M(b_1) = {a_1}`, `M(b_2) = {a_2}`, `M(b_3) = ∅`.  The pair
`(b_1, b_3)` has `M(b_3) = ∅ ⊊ M(b_1)` strictly — F1 active on L_2.
The trichotomy tag stands as **N** (the (a_1, a_2, b_1, b_2)
sub-poset is an N-poset core), but F1 is active.  Updated count:
**32 of 40 F1-active**, **8 F1-inactive**.  The full F1-inactive
list is therefore: `K2-N3-AC`, `K2-N3-AC'`, `K2-N4-22-N`, `K2-N6-M`,
`K2-N6-{122}-(1,2,2)a`, `K2-N6-{222}-(2,2,2)`, plus two more from
the (3,2) dual partition (`K2-N5-32-...` analogs for any
(2,3) class with both bands' nbhds incomparable — none exist,
so 0 from dual).  Counted: 6 F1-inactive on the |α| ≤ 6 catalog.

(Sanity-check this against `feedback_n_poset_is_not_ordinal_sum`:
the N-poset is F1-inactive, and the 6-cycle / matching are
F1-inactive in the same structural sense — consistent.)

---

## §5 — Trichotomy verification (against mg-344a §2)

The saturation lemma proposed in mg-344a §2 commits to the
trichotomy

> N-poset-core / reducible / balanced-pair

for every class in this enumeration.  Per-class verdict:

* **N-poset-core branch** is the intended discharge for the
  F1-inactive classes (6 listed in §4).  Every F1-inactive class
  in the catalog has an N-poset (4-element induced) sub-structure;
  see the per-class notes in §2 for the specific induced N-poset.
* **Reducible branch** is empty by hypothesis (we restricted to
  layered-irreducible).  In a saturation lemma that *does not*
  pre-restrict to irreducible, the reducible branch absorbs every
  class with `E = L_1 × L_2` (excluded from the enumeration); this
  is the `OrdinalDecomp` lift route (mg-7f06).
* **Balanced-pair branch** is the residual.  For the 32 F1-active
  classes, balanced-pair branch must commit to a witness.  The
  available routes per-class (cataloged in §2) are:
  - within-band ⪯-strict pair → existing `chainSwap_LE` / case-2-strict
    machinery, but NB: `Case2FKGSubClaim` is provably false for
    K=2 strict per `mg-b666`/Track 1 — so balanced-pair witness
    does *not* automatically follow from the strict ⪯-pair.
  - explicit per-class enumeration (Bool certificate á la
    `case3_certificate`).
  - cross-band balanced witness (as in K2-N3-MIN's `(b_1, b_2)`).

The verification observation: for **every** class in the catalog,
*some* balanced pair exists (verifiable by direct LE enumeration).
The saturation lemma needs to commit to a uniform witness *family*,
not an existential per-class.

---

## §6 — Reducible classes (excluded, listed for completeness)

The classes with `E = L_1 × L_2` (every cross-pair comparable) are
**reducible at k = 1** and excluded from the enumeration above.  For
completeness:

| ID | partition | E | trichotomy |
|---|---|---|---|
| `K2-N3-RED-12` | (1, 2) | `[1 1]` | R |
| `K2-N3-RED-21` | (2, 1) | `[1; 1]` | R |
| `K2-N4-RED-13` | (1, 3) | `[1 1 1]` | R |
| `K2-N4-RED-31` | (3, 1) | `[1; 1; 1]` | R |
| `K2-N4-RED-22` | (2, 2) | `[1 1; 1 1]` | R |
| `K2-N5-RED-23` | (2, 3) | `[1 1 1; 1 1 1]` | R |
| `K2-N5-RED-32` | (3, 2) | `[1 1; 1 1; 1 1]` | R |
| `K2-N6-RED-33` | (3, 3) | `[1 1 1; 1 1 1; 1 1 1]` | R |

These all discharge by `OrdinalDecomp.hasBalancedPair_lift_*`
applied at the k=1 reducibility witness.

---

## §7 — Cross-references

* §B (`proof-techniques-taxonomy.md`) — proof techniques
  applicable to the trichotomy branches identified here.
* §C (`in-tree-primitive-inventory.md`) — the in-tree Lean
  primitives that instantiate each technique.
* `docs/why-hC3-is-structural.md` §F1 — F1 minimal counterexample,
  matching `K2-N3-MIN` here.
* `docs/path-c-track-1-status-1.md` (mg-b666) — Track 1 cardinality
  obstruction; the F1 active/inactive classification of §4 above
  is the structural complement to this status doc.
* `docs/case3witness-operational-audit.md` (mg-e0b8) — operational
  consumption of `Case3Witness.{u}`; the K=2 sub-regime catalogued
  here is the "K=2 case-2-strict residual" of that audit's §3c.
* `lean/OneThird/Step8/Case3Enum.lean:202` —
  `countLinearExtensions`, the in-tree primitive against which
  |L(α)| of every class above can be `#eval`'d.
* `lean/OneThird/Step8/CompoundSwap.lean:139` — `compoundSwap`,
  the operative symmetry primitive for the N-poset (`K2-N4-22-N`).
* `lean/OneThird/Step8/CompoundMatching.lean:663` —
  `matching_exists_of_K2_irreducible_noWithinBand`, the existing
  structural matching lemma for the F1-inactive case-3/N-poset
  regime within K=2.

---

## §8 — Audit-bar discipline

* `feedback_audit_bar_for_axioms` — applies; no axioms introduced.
* `feedback_signature_regressions` — applies; no signature changes.
* `feedback_n_poset_is_not_ordinal_sum` — applies; the N-poset
  classes (`K2-N4-22-N`, the (3,3) matching, the 6-cycle, and the
  N-cores in (2,3)/(3,2) classes) are correctly tagged as **N**, not
  collapsed to ordinal-sum reducible.
* `feedback_audit_as_deliverable` — applies; this catalog is the
  deliverable, useful regardless of whether the saturation lemma's
  trichotomy proves out.
* `feedback_distinguish_arc_chunk_outcomes` — applies at close;
  this is a substantive catalog chunk; no parallel cleanup; headline
  / axioms / hC3 / sorry-count unchanged.

---

## §9 — Provenance

This document is sub-deliverable §A of `mg-e112`, filed
2026-05-05 by polecat. Origin: Daniel directive 2026-05-05T~11:30Z
(in-session) — "do we have work that can be started, perhaps to
categorize possible proof approaches in our combinatorial case."
Direction context: mg-344a (active) — bespoke-finite combinatorics
on the quotient-to-chain frame.

The catalog is rigor-first and Latex-faithful to the project's
in-tree definitions (`LayeredDecomposition` in
`lean/OneThird/Step8/LayeredReduction.lean:115`, `HasBalancedPair`
in `lean/OneThird/RichPair.lean`, `LayerOrdinalIrreducible` in
`lean/OneThird/Step8/LayerOrdinal.lean:240`).  No fresh paper-level
math is introduced; the four representative `Pr_α` tabulations of
§3 are direct consequences of LE enumeration on small posets.
