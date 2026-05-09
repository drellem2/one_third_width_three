# EX-5 Session A — chamber simplex `σ_L` + chamber decomposition (latex-first scoping)

**Polecat.** mg-79a9 (cat-mg-79a9).
**Date.** 2026-05-09.
**Branch.** `polecat-mg-79a9` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-2442 (`89786cf`) — EX-4 Session B executed: Stanley vertex
  theorem ported to Lean (`OrderPolytope.extremePoints_eq`).
- mg-4831 (`ac56bc4`) — EX-4 Session A latex writeup + mathlib
  mapping (LowerSet → UpperSet correction).
- mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α` defined
  with basic structural properties (convex / closed / bounded /
  compact / measurable + discrete-3-antichain witness).
- mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolved: GREEN-A;
  PM commits Path A.
- mg-91be (`bb450a4`) — sub-α-C high-level scoping; EX-5 spec in §5.5.
- mg-d0fc (`00cbc2d`) — EX-1 Option A: `stanley_log_supermod`
  axiom landed (consumed by EX-7, not by EX-5).

**Verdict.** **GREEN-2** (split Session B + Session C).

The chamber decomposition admits a clean, finite-poset-only
formalisation against the in-tree `OrderPolytope α` (mg-8c66) +
`LinearExt α` (`Fintype.lean:45`), with **no measure-theoretic gap
beyond what mathlib already provides**:

1. **Volume = `1/n!`.** Push σ_L forward to the standard ordered
   cube `Δ_n ⊂ Fin n → ℝ` via the measure-preserving relabelling
   `MeasurableEquiv.piCongrLeft (fun _ => ℝ) L.toFun.symm`
   (Mathlib `measurePreserving_piCongrLeft`, verified at
   `MeasureTheory/Constructions/Pi.lean:744`); compute
   `Vol(Δ_n) = 1/n!` via the symmetric S_n-tiling of `[0,1]^n`.
2. **Cover.** Given `f ∈ O(α)`, sort α by `f`-value, breaking ties
   inside each level set `f^{-1}(c)` by Szpilrajn applied to the
   restricted poset. The resulting linear extension `L_f`
   satisfies `f ∈ σ_{L_f}`.
3. **Measure-zero overlap.** For `L ≠ L'`, pick `(x, y)` with
   `L.pos x < L.pos y` and `L'.pos y < L'.pos x` (always exists
   when the bijections differ). Then `σ_L ∩ σ_{L'} ⊆ { f | f x =
   f y }`, a **strict linear subspace** of `α → ℝ`, hence Lebesgue-
   null by `MeasureTheory.Measure.addHaar_submodule`
   (`MeasureTheory/Measure/Lebesgue/EqHaar.lean:175`).

The single piece of in-tree machinery that **mathlib does not
provide directly** is the **standard ordered cube volume**
`Vol{ y ∈ ℝ^n | 0 ≤ y_0 ≤ … ≤ y_{n-1} ≤ 1 } = 1/n!`. This is **not
a fundamental gap** — it follows from existing mathlib infrastructure
(`measurePreserving_piCongrLeft` over permutations, `volume_Icc_pi`,
and the same `addHaar_submodule` argument for diagonals) — but it
is **~150–200 LoC of derivation** that does not yet sit in mathlib
under any obvious name. **DH-5 candidate** (combined EX-3 + EX-4 +
EX-5 polytope file `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`)
gains a third lemma `volume_orderedCube` from this Session A.

The cover proof requires a Szpilrajn-on-level-set construction that
is **constructive but combinatorially fiddly** (~150–250 LoC):
build a linear extension by concatenating level-set extensions in
increasing f-value order. mg-91be §5.5 originally estimated EX-5 at
"2 polecat sessions, ~800–1500 LoC, ~400–800k tokens combined."
This Session A **revises upward to GREEN-2** — split B + C —
because:

- Volume + relabel + ordered-cube derivation: ~400–550 LoC, one
  Session B.
- Cover (Szpilrajn-on-level-set) + measure-zero overlap + master
  theorem: ~450–600 LoC, one Session C.

Total **~850–1150 LoC** spread across **2 polecat sessions**, well
inside the mg-91be §5.5 envelope. Volume Session B is the
mathlib-PR-class contribution (DH-5 candidate); Cover + overlap
Session C is project-internal.

This document is the latex-first deliverable per polecat brief §3
and `feedback_latex_first_for_math_simp`. **No Lean source
touched.**

---

## §1 Statement, conventions, and Stanley 1986 cite

### §1.1 Conventions

Throughout: `α` is a finite poset (`PartialOrder α`, `Fintype α`,
`DecidableEq α` for the algorithmic level-set construction in §3).
Write `n := Fintype.card α`. Following Szpilrajn (`LinearExt.szpilrajn`,
`Fintype.lean:91`), `n ≥ 1` is forced when α is the discrete
3-antichain or any other instance of interest in this project; we
state the math for `n ≥ 0` when natural and flag the `n = 0` edge
case where it matters.

The order polytope (mg-8c66, `OrderPolytope.lean`) is

```
O(α) := { f : α → ℝ | (∀ x, 0 ≤ f x ≤ 1) ∧ (∀ x y, x ≤ y → f x ≤ f y) }
       ⊆ α → ℝ.
```

A linear extension (mg-`Fintype.lean:45`) is an order-preserving
bijection

```
L : α ≃ Fin n,        L.pos x := L.toFun x : Fin n,
∀ x y, x ≤ y → L.pos x ≤ L.pos y.
```

The Lebesgue measure on `α → ℝ` is `Measure.pi (fun _ : α => volume)`,
auto-resolved via the `MeasureSpace.pi` instance
(`MeasureTheory/Measure/Lebesgue/Basic.lean:216`). When we write
`volume X` for `X ⊆ α → ℝ`, this is the measure intended.

### §1.2 The chamber and the chamber decomposition

For `L : LinearExt α`, the **chamber simplex** indexed by `L` is

```
σ_L := { f : α → ℝ
       | (∀ x, 0 ≤ f x ≤ 1) ∧
         (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) }.                (1.1)
```

This is the **position-based** form. It is equivalent to the
**chain form** advertised in mg-91be §5.5 / mg-163f §5.4:

```
σ_L = { f ∈ O(α)
      | ∀ i : Fin (n - 1), f(L⁻¹(i.castSucc)) ≤ f(L⁻¹(i.succ)) }      (1.2)
```

modulo the `n = 0` edge (where (1.2) requires `Fin.{0} - 1 = 0`
and the chain is vacuous). We adopt (1.1) as the **canonical Lean
signature** because:
- It avoids `Fin (n - 1)` natural-number subtraction (ill-defined
  for `n = 0`).
- It does not require `f ∈ OrderPolytope α` as a conjunct, since
  any `L`-respecting `f` is automatically α-monotone (L is a
  linear extension of α, so `x ≤_α y → L.pos x ≤ L.pos y`, so
  `L`-respect implies α-monotone).
- The chain form is a derived equivalence (`chamber_iff_chain`,
  §5.1 below), not a primitive.

**The chamber decomposition** (Stanley 1986, §1, p. 12; statement (3)):

> *Theorem.* For a finite poset `α` with `n` elements,
>
> 1. `Vol(σ_L) = 1/n!` for every `L : LinearExt α`,
> 2. `O(α) = ⋃_{L : LinearExt α} σ_L`,
> 3. `Vol(σ_L ∩ σ_{L'}) = 0` for `L ≠ L'`.
>
> *Corollary.* `Vol(O(α)) = numLinExt α / n!`.

This document targets parts (1)–(3) (the corollary is consumed by
EX-7 / EX-9 downstream and is a one-line consequence; we record
the signature in §5.4 but do not re-prove it as a separate
theorem here).

### §1.3 Why three theorems, not one

Stanley packages all four claims as a single theorem; we split for
two engineering reasons:

- **Independent consumers.** EX-7 (`probEvent'_mono_of_subseteq_upClosed`)
  consumes the cover (1.2) and the measure-zero overlap (1.3) but
  **not the volume formula** — it works with any chamber decomposition
  with measure-zero overlap. The volume formula (1.1) is consumed
  only by EX-9 (Brightwell-port-A drops → centred-sum). Splitting
  reduces downstream coupling.

- **Mathlib upstream.** The volume formula is the DH-5 candidate;
  the cover + overlap pieces are project-internal even under DH-5.
  Keeping the three claims separate makes the upstream-PR-class
  surface clean.

### §1.4 Stanley 1986 citation map

Stanley 1986, *Two poset polytopes*, Discrete Comput. Geom. 1 (1986),
9–23:

- §1 p. 9–10. Order polytope definition. Consumed by EX-3 (mg-8c66).
- §1 p. 10–11. Vertex theorem (Theorem 1.2). Consumed by EX-4
  (mg-4831 + mg-2442).
- §1 p. 11–13. **Chamber decomposition (this Session A target).**
  Specifically:
  * Stanley (1.4) (p. 12): the chamber simplex `K_σ` parameterised
    by a permutation `σ` of `α`'s vertices that is a linear
    extension. *Notational note: Stanley writes `K_σ` for
    `σ : LinearExt α`; we write `σ_L` for `L : LinearExt α`.
    Equivalent.*
  * Stanley (1.5) (p. 12): `K_σ` is a **unimodular** simplex of
    volume `1/n!`. *Stanley proves unimodularity by noting that
    `K_σ` is the image of the standard ordered simplex under a
    linear map with permutation matrix; this is exactly our §2
    relabel argument.*
  * Stanley Lemma 1.3 (p. 12, line 4): `O(α) = ⋃ K_σ` and
    `K_σ ∩ K_τ` is a face of both for `σ ≠ τ`. *The "face" claim
    is stronger than measure-zero, but for our application
    measure-zero is sufficient and easier to formalise.*
  * Stanley Corollary 1.4 (p. 13): `Vol(O(α)) = e(α)/n!`. *Consumed
    downstream by EX-7 and EX-9.*

Hibi 1985 (*Distributive lattices, affine semigroup rings, and
algebras with straightening laws*) is a parallel geometric source
for the same chamber decomposition, but Stanley's combinatorial
formulation maps more directly to our `LinearExt α`-based Lean
infrastructure; we adopt Stanley as the canonical cite.

### §1.5 Hand-verification: discrete 3-antichain

Setting `α = Three` (the canonical mg-163f / mg-8c66 hand-verification
case, `Three := {a, b, c}` with discrete partial order: `x ≤ y` iff
`x = y`):
- `O(α) = [0, 1]^3` (mg-8c66 `eq_cube_of_discrete` + the `example`
  on `Three`).
- `LinearExt α` has `numLinExt = 3! = 6` elements (one per linear
  order on `{a, b, c}`).
- The 6 chambers are the standard permutohedral chambers of
  `[0, 1]^3`:
  `σ_L = { (x_a, x_b, x_c) | L^{-1}(0) \mapsto \text{smallest},
  L^{-1}(1) \mapsto \text{middle}, L^{-1}(2) \mapsto \text{largest} }`.
- `Vol(σ_L) = 1/6 = 1/3!` for each. ✓
- `[0,1]^3 = ⋃_L σ_L`. ✓
- `σ_L ∩ σ_{L'} ⊆ { f | f x = f y }` for some `x ≠ y` ∈ Three,
  hence has Lebesgue measure 0 in ℝ^3. ✓
- `Vol(O(α)) = 6 · 1/6 = 1 = e(α) / 3!`, where `e(α) = 6` for the
  3-antichain. ✓

The 3-antichain hand-verification is the small concrete witness
the polecat-brief §6 verdict targets ask for; we record it in the
Lean signature §5.5 as an `example` mirroring `mg-8c66`'s
discrete-3-antichain `example`.

---

## §2 Volume — `Vol(σ_L) = 1/n!`

### §2.1 Strategy

**Two-step reduction.**

- **Step A (relabel).** The relabelling `Φ_L : (α → ℝ) ≃ (Fin n → ℝ)`
  defined by `Φ_L f := f ∘ L.toFun.symm` is a **measure-preserving
  bijection** of `α → ℝ` and `Fin n → ℝ` under the product Lebesgue
  measures. Under `Φ_L`, the chamber σ_L corresponds to the
  **standard ordered cube**

  ```
  Δ_n := { y : Fin n → ℝ | (∀ i, 0 ≤ y i ≤ 1) ∧ (∀ i j, i ≤ j → y i ≤ y j) }
       ⊆ Fin n → ℝ.                                                       (2.1)
  ```

  Therefore `Vol(σ_L) = Vol(Δ_n)`.

- **Step B (ordered cube volume).** The standard ordered cube has
  volume `1/n!`:

  ```
  Vol(Δ_n) = 1 / Nat.factorial n.                                          (2.2)
  ```

  Proof by symmetric S_n-tiling: `[0,1]^n = ⋃_{σ ∈ S_n} Δ_n^σ`
  where `Δ_n^σ := { y | y_{σ(0)} ≤ … ≤ y_{σ(n-1)} } ∩ [0,1]^n`,
  pairwise overlaps `Δ_n^σ ∩ Δ_n^τ` for `σ ≠ τ` lie in some
  diagonal hyperplane `{ y_i = y_j }` (Lebesgue-null), and the
  permutation S_n-action on `Fin n → ℝ` is volume-preserving so
  all `Δ_n^σ` have equal volume. Hence `n! · Vol(Δ_n) = Vol([0,1]^n)
  = 1`, giving (2.2).

### §2.2 Step A — `Φ_L` is measure-preserving

**Setup.** For a fintype `ι`, the product Lebesgue measure on `ι →
ℝ` is `Measure.pi (fun _ : ι => volume) : Measure (ι → ℝ)`.

**Mathlib API.** `MeasurableEquiv.piCongrLeft` lifts an equivalence
`f : ι ≃ ι'` to a measurable equivalence
`(ι → α (f ·)) ≃ᵐ (ι' → α ·)`, and
`MeasureTheory.measurePreserving_piCongrLeft` shows it preserves
the product measure (`MeasureTheory/Constructions/Pi.lean:744`):

```lean
theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
      (Measure.pi fun i' => μ (f i')) (Measure.pi μ)
```

Specialising `ι' := Fin n`, `ι := α`, `α (·) := ℝ` (constant), and
`f := L.toFun.symm : Fin n ≃ α`, we get a measure-preserving
bijection `Φ_L⁻¹ : (Fin n → ℝ) ≃ᵐ (α → ℝ)`. Its inverse `Φ_L =
Φ_L⁻¹⁻¹ : (α → ℝ) ≃ᵐ (Fin n → ℝ)` is also measure-preserving
(`MeasurePreserving.symm`).

**Concretely:** `Φ_L(f)(i) = f(L.toFun.symm i)` for `f : α → ℝ`,
`i : Fin n`.

**Effect on the chamber.** The image `Φ_L(σ_L)` consists of
`y : Fin n → ℝ` with:
- `0 ≤ y i ≤ 1` for all `i` (from `0 ≤ f x ≤ 1` for all `x ∈ α`,
  since `L.toFun.symm` is bijective),
- `y i ≤ y j` for `i ≤ j` (from `L.pos x ≤ L.pos y → f x ≤ f y`,
  applied with `x = L.toFun.symm i`, `y = L.toFun.symm j`, giving
  `i = L.pos x ≤ L.pos y = j → f x ≤ f y`, i.e. `y i ≤ y j`).

So `Φ_L(σ_L) = Δ_n` (definitionally — both directions are proved
by point-wise unfolding via `L.toFun.left_inv` /
`L.toFun.right_inv`).

**Volume conservation.** Since `Φ_L` is measure-preserving and
σ_L is the preimage of Δ_n under `Φ_L`:

```
Vol(σ_L) = Vol(Φ_L⁻¹(Δ_n)) = (Φ_L⁻¹).map volume Δ_n = Vol(Δ_n).
```

In mathlib idiom, this is one of:
- `MeasurePreserving.measure_preimage` (preimage form),
- `MeasurePreserving.measure_image` (image form).

Both available at `MeasureTheory/Measure/MeasurePreserving.lean`.

### §2.3 Step B — `Vol(Δ_n) = 1/n!`

**Key lemma (S_n-action on `Fin n → ℝ`).** For any permutation
`σ : Equiv.Perm (Fin n)`, the relabelling
`τ_σ : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ)` defined by `τ_σ y := y ∘ σ` is
measure-preserving. This is `measurePreserving_piCongrLeft` with
`f := σ.symm` (or the equivalent specialisation). Mathlib
provides this directly via `MeasurableEquiv.piCongrLeft`.

**Permutation chambers.** For each `σ : Equiv.Perm (Fin n)`, define

```
Δ_n^σ := { y : Fin n → ℝ | (∀ i, 0 ≤ y i ≤ 1) ∧
                            (∀ i j, i ≤ j → y (σ i) ≤ y (σ j)) }.       (2.3)
```

Then `Δ_n^id = Δ_n`, and `τ_σ⁻¹(Δ_n) = Δ_n^σ` (the relabelling
permutes the chain order). Since `τ_σ` is measure-preserving:

```
Vol(Δ_n^σ) = Vol(τ_σ⁻¹(Δ_n)) = Vol(Δ_n)              for all σ.        (2.4)
```

**Tiling claim.** `[0,1]^n = ⋃_{σ ∈ S_n} Δ_n^σ`.

*Proof.* `(⊇)` Each `Δ_n^σ ⊆ [0,1]^n` by the `0 ≤ y i ≤ 1`
condition. `(⊆)` Given `y ∈ [0,1]^n`, sort the coordinates: let
`σ` be a permutation realising the sort
`y(σ⁻¹ 0) ≤ y(σ⁻¹ 1) ≤ … ≤ y(σ⁻¹ (n-1))` (any tie-break works).
Then `y ∈ Δ_n^σ⁻¹`. ∎

In Lean: `Tuple.sort` (`Mathlib.Data.Fintype.Sort:43`) provides the
sort permutation; combined with a small lemma that the sorted
sequence is monotone, the cover follows. Some care is needed with
ties (the sort permutation is non-unique); the existence of *some*
covering σ is what's required, and `Tuple.sort` provides it
canonically.

**Pairwise null overlaps.** For `σ ≠ τ` in `Equiv.Perm (Fin n)`:
pick `i, j : Fin n` with `i < j` and `σ⁻¹ i > σ⁻¹ j` while
`τ⁻¹ i ≤ τ⁻¹ j` (or vice versa); such `(i, j)` exists since
`σ ≠ τ` implies their induced linear orders differ.

Then on `Δ_n^σ ∩ Δ_n^τ`: by the σ-chain we get `y(σ(σ⁻¹ j)) ≤
y(σ(σ⁻¹ i))`, i.e. `y j ≤ y i`. By the τ-chain we get `y i ≤ y j`.
So `y i = y j`, i.e.

```
Δ_n^σ ∩ Δ_n^τ ⊆ { y : Fin n → ℝ | y i = y j }.
```

The set `H_{i,j} := { y | y i = y j }` is the kernel of the linear
map `y ↦ y i - y j : (Fin n → ℝ) → ℝ`; this kernel is a
**strict linear subspace** of `Fin n → ℝ` (strict because
`y ↦ y i - y j` is non-zero: take `y = Pi.single i 1`, giving
`1 - 0 = 1 ≠ 0`, since `i ≠ j`). By
`MeasureTheory.Measure.addHaar_submodule`
(`MeasureTheory/Measure/Lebesgue/EqHaar.lean:175`):

```lean
theorem addHaar_submodule (μ : Measure E) [IsAddHaarMeasure μ]
    (s : Submodule ℝ E) (hs : s ≠ ⊤) : μ s = 0
```

with `μ := volume`, `E := Fin n → ℝ`, and the
`isAddHaarMeasure_volume_pi` instance
(`MeasureTheory/Measure/Lebesgue/EqHaar.lean:126`), we conclude
`volume H_{i,j} = 0`, hence `volume(Δ_n^σ ∩ Δ_n^τ) = 0`. ∎

**Combining the tiling + overlap + permutation invariance.**

```
1 = Vol([0,1]^n)                                                        (volume_Icc_pi)
  = Vol(⋃_σ Δ_n^σ)                                                      (tiling)
  ≤ ∑_σ Vol(Δ_n^σ)                                                      (countable subadditivity)
  = n! · Vol(Δ_n)                                                       ((2.4) + |S_n| = n!)
```

and

```
n! · Vol(Δ_n) = ∑_σ Vol(Δ_n^σ)
              ≤ Vol([0,1]^n) + ∑_{σ ≠ τ} Vol(Δ_n^σ ∩ Δ_n^τ)             (inclusion–exclusion bound)
              = 1 + 0
              = 1.
```

So `n! · Vol(Δ_n) = 1`, giving `Vol(Δ_n) = 1/n!`. ∎

*Remark.* The inclusion–exclusion direction is most cleanly done
in mathlib via `MeasureTheory.measure_iUnion_le` (subadditivity)
plus the equality
`∑_σ Vol(Δ_n^σ) = Vol(⋃_σ Δ_n^σ) + (correction null term)`. The
"correction null term" is null because pairwise overlaps are null;
formally, one uses
`MeasureTheory.measure_iUnion_eq_sum_of_pairwiseAEDisjoint` (or
the equivalent), which mathlib provides for AE-disjoint families.

### §2.4 Combining

```
Vol(σ_L) = Vol(Δ_n) = 1 / Nat.factorial n.
```

This is the master volume claim. ∎

### §2.5 Note on `Real.map_linearMap_volume_pi_eq_smul_volume_pi` (alternative route)

There is an alternative volume-derivation route via the determinant-
formula `Real.map_linearMap_volume_pi_eq_smul_volume_pi`
(`MeasureTheory/Measure/Lebesgue/Basic.lean:433`):

```lean
theorem map_linearMap_volume_pi_eq_smul_volume_pi
    {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ} (hf : f.det ≠ 0) :
    Measure.map f volume = ENNReal.ofReal |f.det⁻¹| • volume
```

Stanley's "unimodular simplex" cite (1986 (1.5)) hinges on the
relabelling `(α → ℝ) → (Fin n → ℝ)` being represented by a
**permutation matrix**, hence having `|det| = 1`. The
`Real.map_linearMap_volume_pi` route would let one say "σ_L is the
linear image of Δ_n under a unimodular map, hence volume preserved."

We **do not adopt this route** because:
- It requires identifying the bijection `Φ_L : (α → ℝ) → (Fin n → ℝ)`
  as a Lean `LinearMap` and computing its determinant; this is
  more painful than `MeasureTheory.measurePreserving_piCongrLeft`,
  which packages the same fact for arbitrary fintype relabellings.
- It does not generalise to arbitrary `α` (only `α = Fin n`),
  whereas `piCongrLeft` works directly on `LinearExt α`'s
  underlying `α ≃ Fin n`.

We record the alternative for cross-reference (§7.4) but build the
proof on `piCongrLeft`.

---

## §3 Cover — `O(α) = ⋃_{L : LinearExt α} σ_L`

### §3.1 Strategy

The harder direction is `O(α) ⊆ ⋃_L σ_L`: given `f ∈ O(α)`,
construct `L_f : LinearExt α` such that `f ∈ σ_{L_f}`. The reverse
inclusion `σ_L ⊆ O(α)` is automatic from §1.2's "`L`-respect
implies α-monotone" remark.

The construction: **sort α by f-value, with ties broken inside
each level set by Szpilrajn**.

### §3.2 The level-set decomposition

For `f ∈ O(α)`, define the level sets
```
α_c := { x : α | f x = c }    for c ∈ ℝ.                                (3.1)
```
The non-empty `α_c`'s partition α: there are finitely many
(bounded by `|α|`), and each is a sub-poset of α via the
`Subtype.partialOrder` instance (the same wrapping used by
`StanleyLogSupermodAxiom.lean`'s `subPoset`).

Since `α_c` is finite, by Szpilrajn (`LinearExt.szpilrajn`) it
admits a linear extension `M_c : LinearExt α_c`.

### §3.3 The `L_f` construction

Let `α_c` and `M_c` be as above. Concretely, list the distinct
f-values as `c_0 < c_1 < … < c_{k-1}` (with `k ≤ n`), and let
`s_j := |{ x : α | f x < c_j }|` be the cumulative cardinality of
strictly lower level sets.

Define `L_f : LinearExt α` by:

```
L_f.pos x := s_{j(x)} + M_{c_{j(x)}}.pos x_{α_{c_{j(x)}}}                (3.2)
```

where `j(x)` is the unique index with `f x = c_{j(x)}`, and
`x_{α_{c_{j(x)}}}` denotes the embedding of `x` into the level-set
sub-poset.

(The Lean implementation will use `Finset.image` and
`Finset.orderEmbOfFin` rather than literal cumulative indexing, but
the math is the same.)

**Range claim.** `L_f.pos : α → Fin n` is a bijection — it lists
α's elements in non-decreasing f-value order, with each level set
internally permuted by `M_{c_j}`. Cardinality: `∑_j |α_{c_j}| = n`
(level sets partition α).

**Order-preservation claim.** `L_f` is a linear extension of α,
i.e. `x ≤_α y → L_f.pos x ≤ L_f.pos y`.
*Proof.* Suppose `x ≤_α y`. Then `f x ≤ f y` (since `f ∈ O(α)`).
- Case `f x < f y`: `j(x) < j(y)`, so
  `L_f.pos x ≤ s_{j(x)+1} - 1 < s_{j(x)+1} ≤ s_{j(y)} ≤ L_f.pos y`.
- Case `f x = f y`: `j(x) = j(y) =: j`. Then both `x, y ∈ α_{c_j}`,
  and `M_{c_j}` is a linear extension of `α_{c_j}`, so
  `M_{c_j}.pos x ≤ M_{c_j}.pos y`. Hence
  `L_f.pos x = s_j + M_{c_j}.pos x ≤ s_j + M_{c_j}.pos y = L_f.pos y`.
∎

**Chamber-membership claim.** `f ∈ σ_{L_f}`.
*Proof.* The `0 ≤ f x ≤ 1` condition holds since `f ∈ O(α)`. For
the L-respect condition: suppose `L_f.pos x ≤ L_f.pos y`. We show
`f x ≤ f y`.
- Case `j(x) < j(y)`: `f x = c_{j(x)} < c_{j(y)} = f y`. ✓
- Case `j(x) = j(y)`: `f x = c_{j(x)} = c_{j(y)} = f y`. ✓
- Case `j(x) > j(y)`: by definition of `s_·`,
  `L_f.pos x ≥ s_{j(x)} > s_{j(x)} - 1 ≥ s_{j(y)+1} - 1 ≥ L_f.pos y`,
  contradiction with the hypothesis. ✗ (vacuous case).

So either `f x = f y` or `f x < f y`; either way `f x ≤ f y`. ∎

### §3.4 The cover inclusion

Combining: `f ∈ σ_{L_f} ⊆ ⋃_L σ_L`. Since this holds for arbitrary
`f ∈ O(α)`, we have `O(α) ⊆ ⋃_L σ_L`. The reverse inclusion is the
"`L`-respect implies α-monotone" remark (§1.2), giving
`⋃_L σ_L ⊆ O(α)`. ∎

### §3.5 Engineering note — Szpilrajn-on-level-set

The `M_c` family in §3.2 is constructed pointwise for each
`c ∈ Set.range f` — a **finite** set since `α` is finite. The Lean
implementation has two routes:

- **Route A (direct).** Use `Classical.choice` to pick
  `M_c : LinearExt α_c` for each `c ∈ ℝ` (or just for
  `c ∈ Set.range f`), then assemble `L_f` via `Finset.range_succ`-
  style index arithmetic. Clean but requires several auxiliary
  lemmas about cumulative cardinalities.

- **Route B (induction on `n`).** Strong induction on `n := |α|`:
  base case `n = 0` is vacuous; inductive step takes the
  minimum-f-value level set, peels it off using
  `OneThird.LinearExt.OrdinalDecomp` infrastructure
  (`Subtype.lean:140`, already in tree from mg-b088), and
  recursively constructs L_f on the complement.

Route B reuses **substantial** existing infrastructure:
`OrdinalDecomp.restrictMid`, `restrictLower`, `restrictUpper`, the
`assemble` operations (`Subtype.lean:576` etc.) — all the band-
splicing primitives already in tree for the sub-α-A bipartite-bound
arc. The Session C polecat should evaluate which route minimises
LoC; mg-91be §5.5's 800–1500 LoC envelope accommodates either.

**Recommendation:** Route B, conditional on the Session C polecat
verifying that `OrdinalDecomp` adapts to the level-set partitioning
(it was designed for the discrete band-decomposition for case3, but
the level-set partitioning is the same shape). If not, fall back
to Route A.

---

## §4 Measure-zero overlap — `Vol(σ_L ∩ σ_{L'}) = 0` for `L ≠ L'`

### §4.1 Strategy

For `L ≠ L'`, the chambers `σ_L` and `σ_{L'}` enforce **opposing
inequalities** on at least one pair `(x, y)` (we make this precise
below). The intersection therefore lies in `{ f : α → ℝ | f x = f y }`,
which is the kernel of the linear functional `f ↦ f x - f y`. Since
`x ≠ y`, this is a **proper linear subspace** of `α → ℝ` — hence
Lebesgue-null by `addHaar_submodule`.

### §4.2 Existence of an "inversion pair"

**Claim.** If `L, L' : LinearExt α` and `L ≠ L'`, then there exist
`x, y : α` with `L.pos x < L.pos y` and `L'.pos y < L'.pos x`.

*Proof.* `L ≠ L'` means `L.toFun ≠ L'.toFun` as functions
`α ≃ Fin n` (`LinearExt.ext`,
`Fintype.lean:55`).

Suppose for contradiction that no such `(x, y)` exists. Then for
all `x, y`: `L.pos x < L.pos y → L'.pos x < L'.pos y` (since
`Fin n` is linearly ordered, the negation of "`L'.pos y < L'.pos x`"
is "`L'.pos x ≤ L'.pos y`"; combined with injectivity of `L'.pos`
when `x ≠ y`, this gives `L'.pos x < L'.pos y`).

By symmetry (swap roles of `L` and `L'`), we also get
`L'.pos x < L'.pos y → L.pos x < L.pos y`. So `L.pos x < L.pos y ↔
L'.pos x < L'.pos y` for all `x, y`, i.e. the strict orders on α
induced by `L` and `L'` agree.

Two bijections `α ≃ Fin n` inducing the same strict order on `α`
must agree (the strict order determines the position of each
element: `L.pos x = |{ y : α | L.pos y < L.pos x }| = |{ y : α |
L'.pos y < L'.pos x }| = L'.pos x`). Hence `L.toFun = L'.toFun`,
contradicting `L ≠ L'`. ∎

In Lean: this is one of the `LinearExt`-extensionality results;
it does not currently exist in tree but is a ~15-line lemma using
`Finset.card_filter` to count strict predecessors. (mg-b088's
`RelationPoset` infrastructure may have a similar lemma already; the
Session C polecat should check.)

**Concrete witness construction.** Given `L ≠ L'`, find the **first
inversion**: the smallest `i : Fin n` with `L'.pos (L.toFun.symm i) ≠ i`,
equivalently the smallest `i` with `L.toFun.symm i ≠ L'.toFun.symm i`
(the first place where the listings disagree). Set `x := L.toFun.symm i`
and `y := L.toFun.symm (i + 1)` (or rather: the first index `j > i`
with `L'.pos (L.toFun.symm j) < L'.pos x`). The combinatorial details
are in §5 of the Session C Lean spec; the math is the standard
"adjacent-transposition decomposition of `Equiv.Perm`" fact.

### §4.3 The intersection

Pick `(x, y)` from §4.2. Since `L.pos x < L.pos y` and σ_L
imposes `L.pos x ≤ L.pos y → f x ≤ f y` (which is L-respect):

```
σ_L ⊆ { f : α → ℝ | f x ≤ f y }.
```

Symmetrically, since `L'.pos y < L'.pos x`:

```
σ_{L'} ⊆ { f : α → ℝ | f y ≤ f x }.
```

Therefore:

```
σ_L ∩ σ_{L'} ⊆ { f : α → ℝ | f x = f y } =: H_{x,y}.                    (4.1)
```

### §4.4 `H_{x,y}` is a strict linear subspace

The functional
```
ev_{x,y} : (α → ℝ) →ₗ[ℝ] ℝ,    f ↦ f x - f y                            (4.2)
```
is ℝ-linear (both `f ↦ f x` and `f ↦ f y` are evaluation maps,
which are linear). Its kernel is `H_{x,y}`, hence `H_{x,y} =
LinearMap.ker ev_{x,y}` is a `Submodule ℝ (α → ℝ)`.

**Strictness:** `H_{x,y} ≠ ⊤`. Take `f₀ := Pi.single x 1` (the
function which is 1 at x and 0 elsewhere). Then
`ev_{x,y} f₀ = 1 - 0 = 1 ≠ 0` (since `x ≠ y`, which holds because
`L.pos x ≠ L.pos y`). So `f₀ ∉ H_{x,y}`, hence `H_{x,y} ≠ ⊤`. ∎

### §4.5 Lebesgue-null via `addHaar_submodule`

Mathlib (`MeasureTheory/Measure/Lebesgue/EqHaar.lean:175`):

```lean
theorem addHaar_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (s : Submodule ℝ E) (hs : s ≠ ⊤) : μ s = 0
```

With `E := α → ℝ`, `μ := volume`:
- `NormedAddCommGroup (α → ℝ)`: from `Pi.normedAddCommGroup` (since α is
  Fintype, ℝ is normed).
- `NormedSpace ℝ (α → ℝ)`: from `Pi.normedSpace`.
- `MeasurableSpace (α → ℝ)`: from `MeasurableSpace.pi`.
- `BorelSpace (α → ℝ)`: from `Pi.borelSpace`
  (`MeasureTheory.Constructions.BorelSpace.Pi`).
- `FiniteDimensional ℝ (α → ℝ)`: from `Module.Finite.pi` since α is
  Fintype and ℝ is one-dim.
- `IsAddHaarMeasure (volume : Measure (α → ℝ))`: from
  `isAddHaarMeasure_volume_pi`
  (`MeasureTheory/Measure/Lebesgue/EqHaar.lean:126`).

All instances are off-the-shelf. Applying:

```
volume H_{x,y} = volume (LinearMap.ker ev_{x,y} : Submodule ℝ (α → ℝ)) = 0.
```

Combined with (4.1) and monotonicity of measure:

```
volume (σ_L ∩ σ_{L'}) ≤ volume H_{x,y} = 0,
```

hence `volume (σ_L ∩ σ_{L'}) = 0`. ∎

### §4.6 Edge case `n ≤ 1`

For `n = 0`: `LinearExt α` has at most one element (the unique
`α ≃ Fin 0` is the empty equivalence), so `L = L'` always and the
hypothesis `L ≠ L'` is vacuous. Statement holds vacuously.

For `n = 1`: same — `LinearExt α` has exactly one element, so
`L ≠ L'` is vacuous. Statement holds vacuously.

For `n ≥ 2`: the §4.2 construction goes through.

---

## §5 Lean signatures (target for Sessions B / C)

### §5.1 The chamber

```lean
-- lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean (extend)

namespace OneThird.LinearExt.OrderPolytope

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- The chamber simplex indexed by a linear extension `L : LinearExt α`:
the set of `α → ℝ` functions with values in `[0, 1]` that are
non-decreasing along `L`'s linear order. -/
def chamber (L : LinearExt α) : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) }

/-- The chain-form characterisation of `chamber L`. -/
lemma chamber_iff_chain (L : LinearExt α) {f : α → ℝ} :
    f ∈ chamber L ↔
      f ∈ OrderPolytope α ∧
      ∀ i : Fin (Fintype.card α - 1),
        f (L.toFun.symm i.castSucc) ≤ f (L.toFun.symm i.succ)

/-- Every chamber lies inside the order polytope. -/
lemma chamber_subset_orderPolytope (L : LinearExt α) :
    chamber L ⊆ OrderPolytope α
```

### §5.2 Volume

```lean
/-- The chamber `σ_L` has Lebesgue volume `1 / n!`. -/
theorem chamber_volume (L : LinearExt α) :
    MeasureTheory.volume (chamber L) =
      ENNReal.ofReal (1 / (Nat.factorial (Fintype.card α) : ℝ))

/-- Auxiliary: the standard ordered cube `Δ_n ⊆ Fin n → ℝ`. -/
def orderedCube (n : ℕ) : Set (Fin n → ℝ) :=
  { y : Fin n → ℝ |
      (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i j : Fin n, i ≤ j → y i ≤ y j) }

/-- Auxiliary (DH-5 candidate): the standard ordered cube has
volume `1 / n!`. -/
theorem volume_orderedCube (n : ℕ) :
    MeasureTheory.volume (orderedCube n) =
      ENNReal.ofReal (1 / (Nat.factorial n : ℝ))
```

`volume_orderedCube` is the **DH-5 mathlib upstream candidate** —
it carries the symmetric S_n-tiling argument and depends only on
`Fin n` (no project-specific `α`).

### §5.3 Cover

```lean
/-- The chambers cover the order polytope. -/
theorem orderPolytope_eq_iUnion_chamber :
    (OrderPolytope α : Set (α → ℝ)) = ⋃ L : LinearExt α, chamber L

/-- Auxiliary: given `f ∈ O(α)`, construct a linear extension `L_f`
such that `f ∈ σ_{L_f}`. -/
noncomputable def linearExtFromOrderPreserving
    {f : α → ℝ} (hf : f ∈ OrderPolytope α) : LinearExt α

lemma mem_chamber_linearExtFromOrderPreserving
    {f : α → ℝ} (hf : f ∈ OrderPolytope α) :
    f ∈ chamber (linearExtFromOrderPreserving hf)
```

### §5.4 Measure-zero overlap

```lean
/-- For `L ≠ L'`, the chambers `σ_L` and `σ_{L'}` intersect in a
Lebesgue-null set. -/
theorem chamber_inter_meas_zero {L L' : LinearExt α} (h : L ≠ L') :
    MeasureTheory.volume (chamber L ∩ chamber L') = 0

/-- Auxiliary: existence of an inversion pair when two LEs differ. -/
lemma exists_inversion_pair {L L' : LinearExt α} (h : L ≠ L') :
    ∃ x y : α, L.pos x < L.pos y ∧ L'.pos y < L'.pos x
```

### §5.5 Master theorem (corollary, deferred to EX-7 / EX-9)

```lean
/-- **Stanley 1986 Corollary 1.4.** Volume of the order polytope is
`numLinExt α / n!`. -/
theorem orderPolytope_volume :
    MeasureTheory.volume (OrderPolytope α : Set (α → ℝ)) =
      ENNReal.ofReal ((numLinExt α : ℝ) / (Nat.factorial (Fintype.card α) : ℝ))
```

This corollary is **not** part of EX-5's GREEN target (it is one
line modulo `volume_iUnion_eq_sum_of_pairwiseAEDisjoint`-style
combinatorics, but neither EX-7 nor EX-9 actually consumes it
directly — they consume `chamber_volume` + `chamber_inter_meas_zero`
+ `orderPolytope_eq_iUnion_chamber` separately). We list it for
completeness; the Session C polecat may include it as a one-line
add if cheap.

### §5.6 Discrete 3-antichain hand-verification (`example`)

```lean
/-- **Hand-verification: discrete 3-antichain.** For `Three`
discrete poset (mg-8c66), each chamber has volume `1/6 = 1/3!`. -/
example (L : LinearExt Three) :
    MeasureTheory.volume (chamber L) = ENNReal.ofReal (1 / 6) := by
  rw [chamber_volume]; norm_num [Nat.factorial]
```

### §5.7 Decidability + classical hooks

`linearExtFromOrderPreserving` is `noncomputable` (the
level-set sort + Szpilrajn pick uses `Classical.choice`); this is
acceptable since the chamber-decomposition arc downstream
(EX-7 / EX-9) is itself `noncomputable`.

`chamber L` membership is **decidable** in principle (finite
universal quantifications + decidable arithmetic on ℝ), but we do
**not** require a `Decidable` instance — the statements are
existence / measure-zero claims, not algorithmic.

### §5.8 Out of scope (deferred to EX-6 / EX-7)

- **Continuous FKG / Ahlswede–Daykin on `[0,1]^n`** (EX-6, mg-91be
  §5.6). Independent mathlib-PR-class chunk. EX-5 does not consume
  EX-6 and vice versa.

- **Drops headline derivation `probEvent'_mono_of_subseteq_upClosed`**
  (EX-7, mg-91be §5.7). Consumes EX-5 (chamber decomp + volume) +
  EX-6 (continuous FKG). EX-5 does not consume EX-7.

- **Brightwell-port-A drops → centred-sum** (EX-9, mg-91be §5.9).
  Consumes the corollary `Vol(O(α)) = e(α)/n!` and the
  level-`k`-projection of the chamber decomposition. EX-9 may
  need `orderPolytope_volume` (§5.5 above) explicitly; the
  Session C polecat should land this as a one-line corollary.

---

## §6 Mathlib API check + gaps

### §6.1 Verified mathlib APIs (lake-manifest at this commit)

The following mathlib symbols are verified at the project's pinned
mathlib (`v4.29.1`-class, per mg-2442 audit):

| Symbol | Location (mathlib) | Used in EX-5 |
|--------|-------------------|--------------|
| `MeasureTheory.Measure.pi` | `Constructions/Pi.lean` | Volume measure on `α → ℝ` |
| `MeasureTheory.MeasureSpace.pi` (instance) | `Measure/Lebesgue/Basic.lean:216` | Auto-resolution of `volume` on Pi types |
| `MeasureTheory.measurePreserving_piCongrLeft` | `Constructions/Pi.lean:744` | §2.2 relabel |
| `MeasureTheory.volume_measurePreserving_piCongrLeft` | `Constructions/Pi.lean:753` | §2.2 (volume specialisation) |
| `MeasureTheory.MeasurableEquiv.piCongrLeft` | (mathlib `MeasurableEquiv` file) | §2.2 |
| `MeasureTheory.volume_Icc_pi` | `Measure/Lebesgue/Basic.lean:241` | §2.3 (`Vol([0,1]^n) = 1`) |
| `MeasureTheory.Measure.addHaar_submodule` | `Measure/Lebesgue/EqHaar.lean:175` | §4.5 measure-zero overlap |
| `MeasureTheory.Measure.addHaar_affineSubspace` | `Measure/Lebesgue/EqHaar.lean:202` | (alt route, §4.5) |
| `MeasureTheory.isAddHaarMeasure_volume_pi` | `Measure/Lebesgue/EqHaar.lean:126` | §4.5 instance |
| `MeasurableSpace.pi` | `Constructions/Pi.lean` | Pi measurable structure |
| `MeasureTheory.Pi.borelSpace` (instance) | `Constructions/BorelSpace/Pi.lean` | §4.5 BorelSpace dependency |
| `MeasureTheory.MeasurePreserving.measure_preimage` | `Measure/MeasurePreserving.lean` | §2.2 volume conservation |
| `MeasureTheory.MeasurePreserving.symm` | `Measure/MeasurePreserving.lean` | §2.2 invertibility |
| `MeasureTheory.measure_iUnion_le` | `Measure/MeasureSpace.lean` | §2.3 subadditivity |
| `MeasureTheory.measure_iUnion_eq_sum_of_pairwiseAEDisjoint` | `Measure/MeasureSpace.lean` | §2.3 finite-disjoint sum |
| `Real.map_linearMap_volume_pi_eq_smul_volume_pi` | `Measure/Lebesgue/Basic.lean:433` | (alt route, §2.5) |
| `Tuple.sort` | `Mathlib.Data.Fintype.Sort:43` | §2.3 tiling permutation |
| `Equiv.Perm` + `Fintype (Equiv.Perm (Fin n))` | `Logic.Equiv.Defs` + Fintype.Perm | §2.3 S_n iteration |
| `Module.Finite.pi` (instance) | `Mathlib.LinearAlgebra.FreeModule.Finite.Basic` | §4.5 FiniteDimensional |
| `Pi.normedAddCommGroup` (instance) | `Analysis.NormedSpace.Pi` | §4.5 NormedAddCommGroup |
| `Pi.normedSpace` (instance) | `Analysis.NormedSpace.Pi` | §4.5 NormedSpace |
| `LinearMap.ker` | `Algebra.Module.Defs` | §4.4 hyperplane representation |
| `Pi.single` | `Algebra.BigOperators.Basic` | §4.4 strictness witness |

**No critical mathlib API missing.**

### §6.2 In-tree dependencies

| Symbol | Location | Used in EX-5 |
|--------|----------|--------------|
| `OneThird.LinearExt` | `Fintype.lean:45` | Domain of `chamber` |
| `OneThird.LinearExt.toFun` | `Fintype.lean:47` | Relabel and chain |
| `OneThird.LinearExt.pos` | `Fintype.lean:64` | Position-based chamber form |
| `OneThird.LinearExt.lt` | `Fintype.lean:67` | Inversion pair §4.2 |
| `OneThird.LinearExt.szpilrajn` | `Fintype.lean:91` | §3.2 level-set extension |
| `OneThird.LinearExt.ext` | `Fintype.lean:55` | §4.2 `L.toFun = L'.toFun → L = L'` |
| `OneThird.numLinExt` | `Fintype.lean:105` | Master corollary §5.5 |
| `OneThird.LinearExt.OrderPolytope` | `OrderPolytope.lean:94` | Chamber baseline |
| `OneThird.LinearExt.OrderPolytope.{convex, isClosed, isCompact, measurableSet}` | `OrderPolytope.lean:123` etc. | Inherited properties |
| `OneThird.LinearExt.OrdinalDecomp` | `Subtype.lean:140` | (Cover, Route B, optional) |

**No critical in-tree gap.**

### §6.3 Mathlib gap surfaced (DH-5 candidate)

The **standard ordered cube volume** `volume_orderedCube` (§5.2) is
**not directly in mathlib**. It is derivable from existing
infrastructure (~150–200 LoC: tiling + symmetry + diagonal-null),
but does not sit under any obvious mathlib name.

Search performed (verified at this commit's mathlib v4.29.1):
- `grep "ordered.*[Ss]implex"` in `Mathlib/MeasureTheory/`: zero
  results.
- `grep "stdSimplex"` in `Mathlib/Analysis/Convex/`:
  `Analysis/Convex/StdSimplex.lean` defines
  `stdSimplex 𝕜 ι := { f | (∀ i, 0 ≤ f i) ∧ ∑ f i = 1 }` — the
  **probability simplex**, not the ordered cube. Different object.
- `grep "factorial" + "volume"` in `Mathlib/MeasureTheory/`: zero
  results binding the two.

**Recommendation.** Land `volume_orderedCube` as part of EX-5
Session B in `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
(or sibling file `Mathlib/LinearExtension/OrderedCube.lean`); it is
mathlib-PR-class on its own (no project-specific α-dependence).
**Combined with EX-3 + EX-4, this strengthens the DH-5 mathlib
upstream-PR-class candidate** (§3.10 of state.md): the package
`Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean` would
include order polytope basics + Stanley vertex theorem +
`volume_orderedCube` + (post-Session-C) chamber decomposition,
totalling ~700–1100 LoC of mathlib value.

DH-5 priority remains lower than DH-1 (Stanley log-supermod) and
DH-4 (continuous FKG), but the case for upstreaming the
combined polytope file gets stronger with each mg-2442 / mg-79a9
landing.

### §6.4 Mathlib gap not surfaced (good news)

We **expected** to need (and did **not** need, on inspection):

- A direct `Vol(orderedSimplex) = 1/n!` lemma — derivable from
  symmetry, see §6.3.
- A "unimodular linear map preserves volume" lemma — exists as
  `Real.map_linearMap_volume_pi_eq_smul_volume_pi`
  (`Measure/Lebesgue/Basic.lean:433`), but we use the more
  natural `measurePreserving_piCongrLeft` form instead.
- A direct "hyperplane in `α → ℝ` is null" lemma — subsumed by
  `addHaar_submodule` (`EqHaar.lean:175`).

### §6.5 Trip-wires per mg-79a9 polecat brief §5

- **Token blow-up trip-wire (320k of 400k cap):** not fired. This
  Session A is closing under ~270k tokens, well within the cap.
- **Mathlib measure-theory gap:** AMBER-fired then resolved.
  `volume_orderedCube` is a derivable gap, not a fundamental one;
  scoped as Session B sub-deliverable + DH-5 strengthening.
  No fallback to discretised path needed.
- **Volume proof harder than expected:** not fired. The relabel +
  S_n-tiling argument cleanly avoids any mixed-volume / convex
  body / Jordan-decomposition machinery. Stanley's "unimodular
  simplex" line in §1 (1.5) corresponds exactly to our
  measure-preserving relabel — **no convex-geometry detour
  needed**.

---

## §7 Session B and Session C ETA refinement (from mg-91be §5.5)

mg-91be §5.5 estimated EX-5 at **"2 polecat sessions, ~800–1500
LoC, ~400–800k tokens combined."** This Session A refines as
follows.

### §7.1 Session B — volume + relabel + ordered-cube infrastructure

**Scope.** §1.2 chamber definition + §2 volume proof + DH-5
candidate `volume_orderedCube`. Lands in
`lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` (extend
the existing file).

| Component | LoC est. | Tokens (k) |
|-----------|---------:|-----------:|
| `chamber` definition + `chamber_iff_chain` + `chamber_subset_orderPolytope` (§5.1) | 30–45 | 15–25 |
| Aux: `Φ_L : (α → ℝ) ≃ᵐ (Fin n → ℝ)` measure-preserving (§2.2) | 25–40 | 15–25 |
| Aux: `chamber L = Φ_L⁻¹ '' Δ_n` (§2.2 image) | 30–45 | 20–30 |
| Aux: `orderedCube` definition + `Δ_n^σ` (§5.2 + §2.3) | 25–35 | 15–20 |
| Aux: S_n-tiling `[0,1]^n = ⋃_σ Δ_n^σ` via `Tuple.sort` (§2.3) | 80–110 | 50–70 |
| Aux: pairwise null overlaps `Δ_n^σ ∩ Δ_n^τ ⊆ {y_i = y_j}` (§2.3) | 60–80 | 35–50 |
| Aux: σ-orbit volume invariance via `measurePreserving_piCongrLeft` (§2.3) | 35–50 | 20–30 |
| `volume_orderedCube` master (§5.2 / §2.3 combine) | 60–85 | 40–60 |
| `chamber_volume` (§5.2 / §2.4) | 30–40 | 15–25 |
| Discrete 3-antichain `example` (§5.6) | 20–30 | 10–15 |
| **Total (Session B)** | **~395–560** | **~235–350** |

**Session B verdict targets.**
- **GREEN.** All claims formalised; no new project axioms;
  `volume_orderedCube` lands as DH-5 candidate; ~400–550 LoC.
- **AMBER.** S_n-tiling argument needs an unexpected mathlib lemma
  (e.g., `Tuple.sort` + monotonicity bridge isn't off-the-shelf);
  scope as in-tree adapter, not a blocker.
- **RED.** `addHaar_submodule` instance resolution fails for
  `α → ℝ` (e.g., `BorelSpace (α → ℝ)` instance missing for
  `α : Type*` Fintype); fallback to direct measure-of-hyperplane
  proof or restrict to `α := Fin n` and lift via `piCongrLeft`.

**Calendar.** 1 polecat session ≈ 3–5 days. No dependencies on
in-flight tickets beyond mg-2442 (already merged); Session B can
dispatch immediately on this Session A landing.

### §7.2 Session C — cover + measure-zero overlap + master theorem

**Scope.** §3 cover + §4 measure-zero overlap + master
`orderPolytope_eq_iUnion_chamber` + `chamber_inter_meas_zero`
theorems. Lands in same file (extend further) **OR** in a sibling
file `OrderPolytope/ChamberDecomp.lean` if the file approaches
`~1000 LoC` total (mg-8c66 + mg-2442 brought it to ~620 LoC; with
Session B another ~400–550, splitting may improve readability).

| Component | LoC est. | Tokens (k) |
|-----------|---------:|-----------:|
| Aux: `linearExtFromOrderPreserving` construction (§3.3) | 100–150 | 60–90 |
| Aux: order-preservation `L_f` is a linear extension (§3.3) | 50–70 | 30–45 |
| `mem_chamber_linearExtFromOrderPreserving` (§3.3) | 35–50 | 20–30 |
| `orderPolytope_eq_iUnion_chamber` (§3.4) | 25–40 | 15–25 |
| Aux: `exists_inversion_pair` (§4.2) | 60–85 | 40–55 |
| Aux: `H_{x,y}` is a strict `Submodule ℝ (α → ℝ)` (§4.4) | 30–45 | 20–30 |
| Aux: `volume H_{x,y} = 0` via `addHaar_submodule` (§4.5) | 25–40 | 15–25 |
| `chamber_inter_meas_zero` (§5.4 / §4.3) | 30–45 | 20–30 |
| `orderPolytope_volume` corollary (§5.5, optional) | 40–60 | 25–40 |
| Discrete 3-antichain hand-verification of cover (§1.5) | 25–40 | 15–25 |
| **Total (Session C)** | **~420–625** | **~260–395** |

**Session C verdict targets.**
- **GREEN.** All claims formalised; cover via Route A or Route B
  (§3.5); ~420–625 LoC. PM dispatches EX-6 (continuous FKG) next.
- **AMBER.** Route A vs Route B: if `OrdinalDecomp` adapts cleanly
  to level-set partitioning, Route B saves ~150 LoC; otherwise
  Route A. Session C polecat decides; either way GREEN possible.
- **RED.** `linearExtFromOrderPreserving` runs into a structural
  obstruction in `Subtype.lean`'s level-set sub-poset
  (e.g., `LinearExt α_c` requires `Fintype α_c` which requires
  `DecidablePred (f · = c)` for `c : ℝ` — a real-equality decidability
  obstruction). Workaround: use `Finset.image (fun x => f x)` to
  enumerate level values (a finite Finset), then case-split via
  `Finset.decidableMem` rather than `f x = c` directly. The Session C
  polecat should drop into this workaround on first encounter.

**Calendar.** 1 polecat session ≈ 3–5 days. Dispatched on Session B
landing.

### §7.3 Aggregate

| Session | LoC | Tokens (k) | Calendar (days) |
|---------|----:|-----------:|----------------:|
| Session A (this; latex) | 0 (latex only) | ~270 | 1 |
| Session B (volume + DH-5) | ~395–560 | ~235–350 | 3–5 |
| Session C (cover + overlap + master) | ~420–625 | ~260–395 | 3–5 |
| **Total (EX-5)** | **~815–1185** | **~765–1015** | **~7–11** |

This lands at the **upper edge of mg-91be §5.5's "800–1500 LoC,
400–800k tokens" envelope** — a slight upward revision on tokens
(Session A's 270k pushes the total above 400k base). The LoC
estimate is mid-range. No fallback to discretised path
(mg-163f §4.4) needed.

**Recommendation: file Session B next** (`volume_orderedCube` +
`chamber_volume`), Session C dispatches on Session B landing.
Both Sessions B and C dispatched within mg-79a9-class budget
(400k each is ample).

### §7.4 Trip-wires (per polecat brief §6) — final status

| Trip-wire | Fire? | Why |
|-----------|-------|-----|
| Token blow-up (320k cap) | Not fired | Session A finishing under 270k |
| Mathlib measure-theory gap | AMBER, resolved | `volume_orderedCube` is a derivable in-file gap, not a fundamental obstruction; folded into Session B as DH-5 candidate |
| Volume proof harder than expected | Not fired | Stanley's "unimodular simplex" line (1.5) maps directly to `measurePreserving_piCongrLeft`; no AF / mixed-volume detour needed |
| Cover-construction blow-up | Not fired | §3 construction is constructive, ~150–250 LoC; Route A always available |
| Overlap-construction blow-up | Not fired | `addHaar_submodule` is off-the-shelf; ~30 LoC core argument |

**No discretised-fallback fire** (mg-163f §4.4 fallback). All three
chamber-decomposition claims sit cleanly inside mathlib's existing
measure-theory infrastructure.

---

## §8 References

### §8.1 Predecessor polecat documents

* mg-2442 (`89786cf`) — EX-4 Session B executed: Stanley vertex
  theorem ported to Lean.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (extension; `OrderPolytope.extremePoints_eq` master theorem).
* mg-4831 (`ac56bc4`) — EX-4 Session A latex writeup + mathlib
  mapping.
  `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`.
* mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α` defined.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (initial; `convex` / `isClosed` / `isBounded` / `isCompact` /
  `measurableSet`).
* mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolved: GREEN-A.
  `docs/path-alpha-execution-arc/path-A-vs-path-B-fork-resolution.md`.
  EX-5 spec in §2.4 / §5.5.
* mg-91be (`bb450a4`) — sub-α-C high-level scoping.
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`. EX-5
  spec in §5.5: "2 polecat sessions, ~800–1500 LoC, ~400–800k
  tokens combined."
* mg-d0fc (`00cbc2d`) — EX-1 Option A: `stanley_log_supermod`
  axiom landed.
  `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`.
  EX-5 does **not** consume this axiom.
* mg-e22f (`f1c4a66`) — Stanley log-supermod independent
  verification: GREEN.
  `docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`.

### §8.2 Literature

* **Stanley 1986.** R. P. Stanley, *Two poset polytopes*, Discrete
  Comput. Geom. **1** (1986), 9–23. **§1, pp. 11–13** — chamber
  decomposition `O(α) = ⋃_σ K_σ`, unimodular simplex
  `Vol(K_σ) = 1/n!`, corollary `Vol(O(α)) = e(α)/n!`. **The
  canonical EX-5 source.**
* **Hibi 1985.** T. Hibi, *Distributive lattices, affine semigroup
  rings, and algebras with straightening laws*. Parallel
  geometric source for the same chamber decomposition; we adopt
  Stanley as canonical. Cited for cross-reference.
* **Brightwell 1999.** G. Brightwell, *Balanced pairs in partial
  orders*, Discrete Math. — §4 Daykin–Saks via chamber decomp +
  continuous FKG (EX-7 / EX-9 source; cites Stanley 1986 for the
  chamber decomp).

### §8.3 In-tree code (verified at this commit)

* `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (mg-8c66 + mg-2442) — `OrderPolytope α` + Stanley vertex
  theorem. EX-5 extends this file (or splits into a sibling
  `OrderPolytope/ChamberDecomp.lean` if Session C tips the file
  above ~1000 LoC).
* `lean/OneThird/Mathlib/LinearExtension/Fintype.lean:45,64,91,105`
  — `LinearExt α`, `LinearExt.pos`, `LinearExt.szpilrajn`,
  `numLinExt`. EX-5 consumes all four.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:140`
  — `OrdinalDecomp α` and band-splicing primitives. **Optional
  consumption** (cover Route B); Session C polecat decides.
* `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`
  (mg-d0fc) — `stanley_log_supermod` temp axiom. **Not consumed
  by EX-5.**
* `lean/AXIOMS.md` — three named project axioms. EX-5 introduces
  no new axioms.

### §8.4 Mathlib code (verified at this commit's `lake-manifest`)

* `Mathlib.MeasureTheory.Constructions.Pi`:
  - `Pi.measureSpace` (auto-resolution),
  - `measurePreserving_piCongrLeft:744`,
  - `volume_measurePreserving_piCongrLeft:753`,
  - `MeasurableEquiv.piCongrLeft`.
* `Mathlib.MeasureTheory.Constructions.BorelSpace.Pi`:
  - `Pi.borelSpace` (auto-resolution).
* `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`:
  - `MeasureTheory.MeasureSpace.pi:216` (auto-resolution),
  - `volume_Icc_pi:241`,
  - `Real.map_linearMap_volume_pi_eq_smul_volume_pi:433` (alt
    route, §2.5; not used).
* `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`:
  - `isAddHaarMeasure_volume_pi:126`,
  - `addHaar_submodule:175`,
  - `addHaar_affineSubspace:202` (alt route, §4.5; not used).
* `Mathlib.MeasureTheory.Measure.MeasurePreserving`:
  - `MeasurePreserving.measure_preimage`,
  - `MeasurePreserving.symm`.
* `Mathlib.MeasureTheory.Measure.MeasureSpace`:
  - `measure_iUnion_le`,
  - `measure_iUnion_eq_sum_of_pairwiseAEDisjoint`.
* `Mathlib.Data.Fintype.Sort:43` — `Tuple.sort`.
* `Mathlib.Logic.Equiv.Defs` + `Mathlib.Data.Fintype.Perm` —
  `Equiv.Perm`, `Fintype (Equiv.Perm (Fin n))`.
* `Mathlib.LinearAlgebra.FreeModule.Finite.Basic` —
  `Module.Finite.pi` instance.
* `Mathlib.Analysis.NormedSpace.Pi` — `Pi.normedAddCommGroup`,
  `Pi.normedSpace`.
* `Mathlib.Algebra.Module.Defs` — `LinearMap.ker`.

### §8.5 Mathlib gap candidates (DH-5)

Per §6.3:

* `volume_orderedCube` (`Vol{ y ∈ ℝ^n | 0 ≤ y_0 ≤ … ≤ y_{n-1} ≤ 1 }
  = 1/n!`) — **not directly in mathlib**; derivable, lands as part
  of EX-5 Session B. **Strengthens DH-5** (combined EX-3 + EX-4 +
  EX-5 mathlib upstream PR).

### §8.6 Feedback / policy applied

* `feedback_polecat_cumulative_state_doc` — applied (state.md
  updates per §4 of polecat brief; commit diff).
* `feedback_latex_first_for_math_simp` — applied (this document is
  the latex deliverable; **no Lean source touched**).
* `feedback_complexity_blowup_means_wrong_path` — applied
  (trip-wires §6.5 + §7.4).
* `feedback_polecat_stop_runaway` — applied (no auto-extension;
  Sessions B and C are filed separately by PM).
* `feedback_pre_execution_dependency_verification` — applied
  (§6.1, §6.2, §8.4 mathlib API verified against pinned
  lake-manifest).
* `feedback_pm_is_mini_ceo_default` — applied (Session B vs C
  split is a Lean-ticket-shape decision; PM decides + informs
  Daniel via digest).
* `feedback_block_and_report` — applied (no blocking on Daniel
  acknowledgment; PM dispatches Session B on this Session A
  landing, Daniel's default-acceptance window applies).

---

*End of EX-5 Session A — chamber simplex `σ_L` + chamber
decomposition latex-first scoping. Lean source unchanged.
Verdict: **GREEN-2** (Session B + Session C); volume + relabel +
ordered-cube infrastructure → Session B (~395–560 LoC, DH-5
candidate); cover + measure-zero overlap + master theorem →
Session C (~420–625 LoC). PM files Session B per §7.1.*
