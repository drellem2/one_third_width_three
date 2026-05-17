# Case3Witness post-cap-5 — tractability analysis (Option D)

**Work item:** `mg-0cbf` (paper-and-pencil tractability analysis,
single-session, no Lean code changes).

**Trigger:** Daniel question 2026-05-17T20:34Z (verbatim):

> "do we already have an analysis of case 3 witness lemma in its new
> form, any assessment of how tractable it seems?"

**Predecessors.** `mg-e2e9` (architecture analysis,
`docs/onethird-Case3Witness-architecture-analysis.md`,
AMBER-fix-proposed) proposed the cap-5 fix. `mg-d5a0` (cap-5 Lean
landing, `docs/state-Case3Witness-cap5-fix.md`) added cap 5 `LB.w ≤ 4`
to `Step8.Case3Witness.{u}` and surfaced the operational gap at
`LayeredBalanced.lean:626` as a structured `sorry`. This analysis
asks: with cap 5 in place, is the post-cap-5 `Case3Witness` Prop
**directly tractable as a finite check** (Option D), and if so what
exactly does that close?

**Parallel ticket.** `mg-4d7b` (computation polecat, TOP PRIORITY per
Daniel 2026-05-17T20:55Z) is concurrently executing the actual
enumeration. The recommendations of this analysis explicitly
coordinate with mg-4d7b — see §4 and §5 below.

---

## Verdict (top-of-page): **GREEN-D2 with one boundary caveat**

**Option D-narrow** (close `case3Witness_hasBalancedPair_outOfScope`
inside `Case3Witness_proof`): **D2-tractable** — closable by
extending `case3_certificate` with 15 additional `(K, w)` tuples
specialised to cap-1 singleton bands, of which 14 fit the existing
`enumPosetsFor` Bool enumerator's `nfree ≤ 27` cap and 1 requires
either an extended enumerator (`nfree = 30`, ≈ 10⁹ masks) or a
small structural carve-out at `(K, w) = (10, 4)`. Under cap 1, Case 1
of `prop:in-situ-balanced` is vacuous (singleton bands ⇒ no within-
band pair), Case 2 is vacuous (already discharged via
`case2_discharge_of_injective`), so only Case 3 remains and the
"finitely-decidable over a bounded family" claim is operative. This
closes the **only project axiom** in `Case3WitnessProof.lean`'s
discharge chain and makes `Case3Witness_proof` axiom-free.

**Option D-broad** (close the `LayeredBalanced.lean:626` cap-5
discharge `sorry` for arbitrary `|α|`): **NOT closable by Option D
alone**. The call site substitutes `canonicalLayered α` whose
`w = |α|` fails cap 5 for `|α| ≥ 5`, and under cap 1 + cap 2 + cap 5
the universal quantifier of `Case3Witness β` is **vacuous for
`|β| ≥ 11`** (no LB satisfies all 5 caps at `|β| = K ≥ 11 ≤ 2·4+2`).
So even an axiom-free `Case3Witness` cannot, on its own, discharge
the dispatch at `|α| ≥ 11`; an alternative LB constructor at the
call site is required and that constructor's existence is the
Steps 1-7 / `w₀(γ)` content (Option A) or the F3 strong-induction
descent (Option B blocked on `mg-b666`).

**Recommendation (consolidating mg-0cbf and mg-4d7b
coordination):**

* mg-4d7b should **proceed**. Its Phases A-B (enumerate +
  HasBalancedPair-verify ~ 1 M width-3 non-chain posets at
  `|β| ≤ 10`) are the math-paper deliverable that (a) underwrites
  Option D-narrow, and (b) is a prerequisite to any future Option-B
  or Option-A refactor that would discharge `LayeredBalanced.lean:626`
  for arbitrary `|α|` (the small-`|β|` leaves of any such descent
  must in any case be verified by enumeration). The TOP PRIORITY
  framing is correct.
* mg-4d7b's Phase D (construct cap-5-satisfying LB for each `β` with
  `|β| ≤ 10`) is the **partial-D-broad** payload: it discharges the
  K ≥ 2 sorry for `|α| ≤ 10` but **not** for `|α| ≥ 11`. The
  honest framing for downstream is *post-mg-4d7b, the headline holds
  unconditionally for `|α| ≤ 10` and reduces to the previously-known
  `|α| ≥ 11` problem* — which is Option A (Steps 1-7 deliver
  `w₀(γ)`) or Option B (F3 strong-induction descent).
* Option D-narrow can be filed as a **follow-on Lean ticket** once
  mg-4d7b lands, refactoring `Case3Witness_proof` to replace the
  residual axiom with the extended certificate. This is a clean
  win — axiom count drops by one with no fresh blockers.
* Option B (`mg-b666` K=2 case-2-strict unblock) is **NOT
  superseded** by Option D. Daniel's "without needing mg-b666"
  framing in mg-0cbf is correct only for **Option D-narrow**.
  Option D-broad still depends on B (or A) for `|α| ≥ 11`.

---

## 1. The post-cap-5 `Case3Witness.{u}` statement

From `LayeredBalanced.lean:461-472` (post-mg-d5a0):

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    Function.Injective LB.band →                            -- cap 1
    LB.K ≤ 2 * LB.w + 2 →                                   -- cap 2
    Fintype.card β ≤ 6 * LB.w + 6 →                         -- cap 3
    (∀ k : ℕ, 1 ≤ k → k ≤ LB.K → (LB.bandSet k).Nonempty) → -- cap 4
    LB.w ≤ 4 →                                              -- cap 5 (mg-d5a0)
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β
```

### 1a. Universal-quantifier domain under the five caps

The caps interact tightly. We track the **effective domain** of
`(β, LB)` pairs satisfying all five caps + `HasWidthAtMost β 3` +
`¬ IsChainPoset β` + `2 ≤ |β|`:

* **Cap 1 + cap 4** ⇒ each band has *exactly one* element (cap 4
  forces `≥ 1`, cap 1 forces `≤ 1`, with `(L1a)`'s `band_size ≤ 3`
  the upper bound is loose). Hence `|β| = LB.K`.
* **Cap 5** ⇒ `LB.w ∈ {0, 1, 2, 3, 4}`. (`LB.w = 0` is the
  bipartite/Case-2 regime, structurally excluded under K ≥ 2
  irreducibility per `option_c_K2_closure`'s `w = 0` branch.)
* **Cap 2 + cap 5** ⇒ `LB.K ≤ 2 · 4 + 2 = 10`.
* **Cap 3 + cap 5** ⇒ `|β| ≤ 6 · 4 + 6 = 30`. Subsumed by
  cap 1's `|β| = LB.K ≤ 10` once cap 1 is applied.
* **`2 ≤ |β|`** ⇒ `LB.K ≥ 2`.

So the **effective hypothesis domain** is:

```
|β| = LB.K ∈ {2, 3, …, 10},  LB.w ∈ {0, 1, 2, 3, 4},
LB.K ≤ 2 · LB.w + 2.
```

The reachable `(K, w)` pairs (writing K for `LB.K`, w for `LB.w`,
ignoring the `w = 0` case which goes through `option_c_K2_closure`'s
direct discharge):

| w \ K | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|-------|---|---|---|---|---|---|---|---|----|
| 1     | ✓ | ✓ | ✓ |   |   |   |   |   |    |
| 2     | ✓ | ✓ | ✓ | ✓ | ✓ |   |   |   |    |
| 3     | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |   |    |
| 4     | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓  |

Total reachable `(K, w)` cells: **27**. Excluding the `K = 2`
column (3 cells; handled by `option_c_K2_closure`): **24** cells.

### 1b. The proof architecture of `Case3Witness_proof`

`OneThird.Step8.OptionC.Case3WitnessProof.Case3Witness_proof`
(`OptionC/Case3WitnessProof.lean:256-547`) discharges this universal
claim by strong induction on `Fintype.card β`. The K-dispatch:

* **K = 1**: ruled out by `absurd_K1_of_injective` — cap 1 +
  `2 ≤ |β|` forces a contradiction.
* **K = 2**: discharged by `OneThird.Step8.OptionC.option_c_K2_closure`
  (`OptionC/K2Closure.lean:500`, fully proved via the
  `case2_certificate` Bool fact). **No project axiom; no sorry.**
* **K ≥ 3, reducible** at some `k ∈ [1, K-1]`: descend on the
  `D.Lower` or `D.Upper` half-poset via `LB.compactify`. Cap 5 is
  preserved by `compactify_w_eq`. Recursive call decreases
  `Fintype.card`.
* **K ≥ 3, irreducible**: dispatch via
  `Step8.bounded_irreducible_balanced_hybrid`, which splits on
  `InCase3Scope`:
  * **In-scope branch** (`hCert`): closes via `case3_certificate`
    + the band-major Fin-n encoding bridge. The certificate covers
    `(K, w) ∈ {(3,1), (3,2), (3,3), (3,4), (4,1)}` with size caps
    `≤ 9` (K=3 w=1), `≤ 7` (K=3 w∈{2,3,4}), `≤ 8` (K=4 w=1).
    Under cap 1, `|β| = K ∈ {3, 4}` satisfies the size caps.
    **No project axiom; no sorry.**
  * **Out-of-scope branch** (`hStruct`): currently routes through
    `InSitu.hStruct_of_case2_discharge` →
    `case3Witness_hasBalancedPair_outOfScope` axiom
    (`Case3Residual.lean:208`). **This is the ONLY project axiom
    in `Case3Witness_proof`'s dispatch chain post-cap-5.**

### 1c. The Case 1 / Case 2 / Case 3 sub-dispatch (out-of-scope)

`hStruct_of_case2_discharge` (`Case3Residual.lean:265`) takes a
`case2Discharge : Case2Witness L → HasBalancedPair α` hypothesis (in
`Case3WitnessProof.lean`, supplied as
`case2_discharge_of_injective hInj` which uses cap 1's injectivity
to make `Case2Witness L` vacuous), then routes via
`case1_dispatch_balanced_or_witness L hWidth3 hIrr hScope`:

* **Case 1 — ambient profile match**: `∃ a a' : α, a ≠ a' ∧
  (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')`. Discharged
  uniformly via `hasBalancedPair_of_ambient_profile_match` (mg-f92d,
  `Case3Struct.lean`). Note: this does **not** require `a, a'` in
  the same band; under cap 1 we can have `band a ≠ band a'`. So
  Case 1 is **not** automatically vacuous under cap 1.
* **Case 2 — within-band ⪯-pair**: `∃ a a' : α, a ≠ a' ∧
  L.band a = L.band a' ∧ (...)`. Vacuous under cap 1 (singleton
  bands ⇒ `L.band a = L.band a'` forces `a = a'`); discharged via
  `case2_discharge_of_injective`.
* **Case 3 — residual** (`InSitu.Case3Witness L`, the *inner*
  predicate, distinct from the outer `Step8.Case3Witness`): the
  negation `¬ Case 1 ∧ ¬ Case 2`. Discharged via
  `case3Witness_hasBalancedPair_outOfScope` axiom.

So **the only operational axiom hit by `Case3Witness_proof`'s
discharge of `Case3Witness.{u}` is `case3Witness_hasBalancedPair_outOfScope`**,
and the hit only happens on the *Case 3* sub-branch of the
*K ≥ 3, irreducible, ¬InCase3Scope* leaf. Under cap 1 + cap 5,
that leaf's parameter domain is the subset of the 24 K ≥ 3 cells
above that fall outside `InCase3Scope`.

---

## 2. Phase 1 — counting the residual-axiom domain

`InCase3Scope w card K` (`BoundedIrreducibleBalanced.lean:1498`):

```
InCase3Scope w card K  ⇔
  (K = 3 ∧ 1 ≤ w ∧ w ≤ 4 ∧ (w = 1 → card ≤ 9) ∧ (2 ≤ w → card ≤ 7))
  ∨ (K = 4 ∧ w = 1 ∧ card ≤ 8)
```

Under cap 1 (`|β| = K`) the size-cap checks are automatic:

* `K = 3, w = 1, |β| = 3 ≤ 9`: ✓ in-scope.
* `K = 3, w ∈ {2,3,4}, |β| = 3 ≤ 7`: ✓ in-scope.
* `K = 4, w = 1, |β| = 4 ≤ 8`: ✓ in-scope.

So under cap 1, the `(K, w)` cells **inside** `InCase3Scope` are
`{(3,1), (3,2), (3,3), (3,4), (4,1)}` — exactly the 5 cells already
covered by `case3_certificate`.

The `(K, w)` cells **outside** `InCase3Scope` (within the cap-5 +
cap-1 + cap-2 + `K ≥ 3` domain), i.e., the **residual-axiom
operative domain under cap 1**:

| K  | w-values | count |
|----|----------|-------|
| 4  | 2, 3, 4  |   3   |
| 5  | 2, 3, 4  |   3   |
| 6  | 2, 3, 4  |   3   |
| 7  | 3, 4     |   2   |
| 8  | 3, 4     |   2   |
| 9  | 4        |   1   |
| 10 | 4        |   1   |
| **Total** |  | **15** |

For each `(K, w)` cell, **cap 1 forces `bandSizes = [1, 1, …, 1]`
of length K** — a single `bandSizes` list per cell. (Without cap 1,
the F5a `enumPosetsFor` would range over `bandSizesGen K (6w+6)`
which has many entries per `(K, w)`; with cap 1 we get a singleton.)

### 2a. Enumerator cost (`enumPosetsFor LB.w [1; K]`)

`enumPosetsFor w bs` (`Case3Enum.lean:324`) iterates `2^nfree`
masks, where

```
nfree = enumNfreeOf w bs = |{(i, j) : i < j ≤ i + w}| under bandSizes bs.
```

Under `bs = [1; K]`, `nfree = Σ_{d=1}^{w} (K - d) = w·K - w(w+1)/2`.
The enumerator hard-stops at `nfree > 27` (returns `false`).

| K  | w | nfree | 2^nfree | within enumerator cap? |
|----|---|-------|---------|------------------------|
| 4  | 2 | 5     | 32      | yes                    |
| 4  | 3 | 6     | 64      | yes                    |
| 4  | 4 | 6     | 64      | yes                    |
| 5  | 2 | 7     | 128     | yes                    |
| 5  | 3 | 9     | 512     | yes                    |
| 5  | 4 | 10    | 1 024   | yes                    |
| 6  | 2 | 9     | 512     | yes                    |
| 6  | 3 | 12    | 4 096   | yes                    |
| 6  | 4 | 14    | 16 384  | yes                    |
| 7  | 3 | 15    | 32 768  | yes                    |
| 7  | 4 | 18    | 262 144 | yes (matches K=3 c-sliver upper end) |
| 8  | 3 | 18    | 262 144 | yes                    |
| 8  | 4 | 22    | 4 194 304 | yes                  |
| 9  | 4 | 26    | 67 108 864 | yes (at threshold)  |
| 10 | 4 | 30    | 1 073 741 824 | **no** (`nfree > 27`) |

Sum of mask iterations (14 in-cap cells): roughly `7.6 · 10⁷` total
masks, dominated by the `(K, w) = (9, 4)` cell at `67 · 10⁶`. With
the `closureCanonical` + `findSymmetricPair` + `irreducible` +
`hasAdjacentIncomp` prune chain (typical pruning ratio ≈ `K!`,
i.e., ≈ `3.6 · 10⁶` at `K = 10`), the *surviving-config* count per
cell falls to the order of `2^nfree / K!`. For (9, 4) that's
≈ `185` survivors after canonical-form pruning.

Native-decide wall-clock projection (extrapolating from the
existing `case3_balanced_w1` at `nfree ≤ 18` build time): order
**single-digit minutes per cell** for the 14 in-cap cells,
**not** including the per-cell `hasBalancedPairSlow` DP cost on
the surviving configs (which is `O(2^K · K)` per config — at
K = 10 that's ~10 ⁴ DP rows per config, modest).

**The `(K, w) = (10, 4)` cell** requires raising the `nfree > 27`
hard-cap in `enumPosetsFor` to `≥ 30`, which lifts the per-cell
iteration count to `≈ 10⁹` masks. This is **at the upper boundary
of single-call `native_decide` feasibility** (cf. the
`compatibility-geometry-pathP3-scoping.md` notes about `nfree > 27`
being out of reach for the current local build window).

### 2b. Tightening under irreducibility

The F5a enumerator's `irreducible` gate filters out configurations
that admit a layered-ordinal-sum cut. For cap-1 singleton bands at
small K, irreducibility is restrictive: e.g., at `K = 4` an
irreducible configuration must have some cross-pair at every
adjacent band-pair `(k, k+1)` for `k ∈ {1, 2, 3}` (else `k` is a
cut). Combined with width-3, the effective configuration count per
cell falls further — likely by an order of magnitude — but the
`for mask in [0:1<<<nfree]` outer loop still iterates the full
`2^nfree` (the gates filter post-construction).

So the binding tractability constraint is **the outer loop length**,
not the per-mask check work. The `nfree > 27` cap is binding only
at `(K, w) = (10, 4)`.

### 2c. The Case 1 sub-branch (under cap 1)

The Case 3 *residual axiom* requires `InSitu.Case3Witness L`, i.e.,
both `¬ Case 1` *and* `¬ Case 2`. Under cap 1, `¬ Case 2` is
automatic. `¬ Case 1` requires that **no two distinct elements of
β have identical ambient strict-`<` profiles in both directions**.

Under cap 1 (singleton bands, Szpilrajn-derived band map), can two
distinct elements `a ≠ a'` of β have identical ambient profiles?
Recall `a < z ↔ a' < z` for *all* `z ∈ β` (strict `<`). For
`z = a`, we'd need `a < a ↔ a' < a`, i.e., `a' < a` is `False`
(since `a < a` is false). Similarly `z = a'` requires `a < a'`
false. So Case 1 requires `a` and `a'` are mutually incomparable
in β.

Under cap 1, `band a ≠ band a'` (singleton bands). The Szpilrajn
extension gives a linear order on `{a, a'}`; WLOG `band a < band a'`.
Then `(L2-forced)`: if `band a + w < band a'`, then `a < a'` —
contradicting incomparability. So Case 1 forces
`band a' - band a ≤ w`. Within a window of size `w + 1`, two
elements with the same `<` and `>` profile to the rest of β.

**Case 1 is NOT vacuous under cap 1.** It captures
configurations where two consecutive-band elements are
"interchangeable" up to the rest of β.

The Case-1 dispatch closes such configurations via the
`Equiv.swap a a'` automorphism argument (gives `probLT a a' = 1/2`,
balanced). The Case-3 residual axiom is invoked only when this
swap-argument fails — i.e., on configurations with no
profile-match pair.

**For the F5a enumerator extension**, we'd need an additional
*Case 1 gate* (Bool predicate "no two elements have identical
ambient profile") to ensure the enumeration's `HasBalancedPair`
discharge is operative only on Case 3 residual configurations.
Alternative: just prove `HasBalancedPair` for *all* configs (Case 1
+ Case 3 union), which is a stronger claim than the residual axiom
but obviously implies it. The Bool enumerator's `findSymmetricPair`
fast-path **already** discharges Case-1-like configurations (the
swap-automorphism witness is a `Symmetric` witness in the Bool
encoding), so this is the path of less resistance.

So **practical Option D-narrow**: extend `case3_certificate` with
the 15 `(K, w)`-cell + bandSizes = `[1; K]` tuples; prove the
result via `native_decide`; replace `case3Witness_hasBalancedPair_outOfScope`
inside `Case3Witness_proof` with the extended certificate
(restricted to cap 1 input). The extended certificate proves a
*stronger* claim than the axiom (covers Case 1 + Case 2 + Case 3
configs uniformly), but the stronger claim is exactly what
`bounded_irreducible_balanced_inScope`'s discharge already proves
on the existing 5 in-scope cells. So the bridge infrastructure
applies uniformly.

---

## 3. Phase 2 — structural argument feasibility (D1 vs D2)

### 3a. The paper's structural argument

`prop:in-situ-balanced` (`step8.tex:2965-3048`) splits into:

* **Case 1** (`step8.tex:2984-2999`): `Equiv.swap` automorphism on
  an ambient-profile-match pair → `probLT = 1/2`. **Uniform.**
* **Case 2** (`step8.tex:3001-3032`): Ahlswede–Daykin / FKG
  monotonicity on a within-band ⪯-pair. **Uniform** (under
  pre-cap-5 axiomatic support).
* **Case 3** (`step8.tex:3033-3047`): residual width-3 within-band
  antichain enumeration (`rem:enumeration`, `step8.tex:3157-3173`).
  **Two-of-three-share-coordinate** argument is uniform in spirit
  but the explicit case analysis is enumerative. The paper's
  language: *"two of the three elements must share *some* coordinate
  of the two-sided profile whenever `|Q| ≤ 3(3w+1)`"*.

Under cap 1, the "within-band antichain" of Case 3 is **vacuous**
(singleton bands). So the paper's Case-3 argument doesn't directly
apply under cap 1 — the structural content shifts to "*cross-band*
profile-coordinate sharing", which is the **inner** content of the
F5a enumeration (`case3_certificate` itself).

### 3b. Could a uniform argument (D1) avoid enumeration?

Under cap 1 + cap 5 + cap 2 + cap 3 + `K ≥ 3` + irreducible
+ width-3 + non-chain + `¬ InCase3Scope`, we're looking at
labelled partial orders on `K ≤ 10` elements satisfying:

* Szpilrajn-compatible band map `band x = e(x)`, `e` a Szpilrajn
  extension.
* `(L2-forced)`: `e(x) + w < e(y) ⇒ x < y`. I.e., distant pairs in
  the Szpilrajn extension are forced comparable.
* `(L2-upward)`: `x < y ⇒ e(x) ≤ e(y)` (Szpilrajn property).
* Width ≤ 3, non-chain, irreducible (no `k ∈ [1, K-1]` such that
  every `(x, y)` with `e(x) ≤ k < e(y)` has `x < y` — i.e., the
  partial order doesn't ordinal-decompose at `k`).
* Outside the F5a enumerator's certified scope (i.e., one of the
  15 `(K, w)` cells in §2).

**Candidate uniform arguments:**

| Argument | Sketch | Verdict |
|----------|--------|---------|
| (U1) Endpoint pair `(e^{-1}(1), e^{-1}(K))` | Forced comparable when `K - 1 > w`; balanced iff some symmetry. | **Fails**: forced comparable means *not* incomparable, so cannot be a balanced *pair* candidate. |
| (U2) Adjacent pair `(e^{-1}(k), e^{-1}(k+1))` for some k | Existence of an incomparable adjacent pair = "adjacent-incomp" gate. | Only existence is guaranteed by irreducibility (`exists_adjacent_not_lt_of_irreducible`); balanced-ness is *not* uniform. |
| (U3) Profile-coordinate share | Paper's `rem:enumeration` argument | Requires `|Q| ≤ 3(3w+1)` (paper); under cap 1 + cap 5, `K ≤ 10 = 3(3·1+1)+1`, tight match for `w = 1` only. Doesn't uniformly cover `w ∈ {2,3,4}`. |
| (U4) Compactify reduction to InCase3Scope | Reduce out-of-scope cells to InCase3Scope cells by deleting/merging elements | Compactify preserves cap 5 but does **not** reduce K below `LB.K - 1`; cannot collapse `K = 10` to `K = 3, 4`. **Fails**. |
| (U5) F3 strong-induction on `|α|` | Descend on `α` to smaller leaves | Already done **inside** `Case3Witness_proof`; the residual is the *irreducible leaves* of that descent. Recursive uniform argument circular. |
| (U6) Direct Brightwell single-element perturbation | Apply `brightwell_sharp_centred` | Fails at `|Q| ≤ 6` (F2 obstruction, `why-hC3-is-structural.md` §F2). The same F2 applies for our `K ≤ 10` cap 1 domain at the smaller `(K, w)` cells. |

**No uniform argument candidate survives.** The paper's
`rem:enumeration` is the closest, and it explicitly degenerates
into a finite case analysis. The 30-year unsolved general
`δ* ≥ 0.276 → 1/3` gap (F3 in `why-hC3-is-structural.md`) is the
literature-level evidence that no uniform argument exists at
arbitrary `|β|`.

### 3c. The "case-1 + symmetric pair" sub-uniform fact

The Bool enumerator's `findSymmetricPair` fast-path discharges
the *vast majority* of masks (per the `enumPosetsFor` docstring:
*"This discharges the vast majority of masks; the remaining
asymmetric ones fall through to the full validity-then-DP
path."*). A symmetric pair in the Bool encoding corresponds
exactly to a Case-1 ambient-profile-match pair under cap 1.

So there **is** a partial uniform fact: *"every config with at
least one symmetric pair has a balanced pair"*. This is genuinely
uniform (the `Equiv.swap`-based proof in `Case3Struct.lean` /
mg-f92d). The **residual after this fast-path** is the asymmetric
configs — which the enumerator handles via the slow-path linear-
extension DP (`hasBalancedPairSlow`).

**Hybrid verdict (refinement of D2):** Option D's tractability
*decomposes* into

* (D-uniform) Case-1 discharge for symmetric configs (proved
  uniformly via `Equiv.swap` automorphism, `mg-f92d`'s
  `hasBalancedPair_of_ambient_profile_match`). **Already in tree.**
* (D-enum) Slow-path DP for asymmetric configs (per-config
  linear-extension count). **This is what enumeration computes.**

The slow-path DP per-config is `O(2^K · K)`; total enumeration
work scales as `(asymmetric-config count) · 2^K · K`. For `K = 10`,
the per-config DP is `≈ 10⁴` operations, and the asymmetric-config
count after canonical-form + Case-1 pruning is much smaller than
`2^nfree`.

### 3d. Why D1 fails specifically

D1 would require a uniform argument for the **asymmetric**
out-of-scope configs (those without a Case-1 profile-match pair).
The paper's `rem:enumeration` is the only candidate, and it
admits the dispatch is enumerative. The 30-year-unsolved literature
status (F3) confirms no shorter uniform argument is known.

So we land at **D2**: enumeration is the path, and the path is
already partially uniformised (Case-1 fast-path uniformly closes
the symmetric majority).

---

## 4. Phase 3 — tractability classification

### 4a. **D2-tractable** (the operative verdict)

* The 15 `(K, w)` cells under cap 1 + cap 5 + `¬ InCase3Scope` have
  a single bandSizes per cell (`[1; K]`).
* 14 of 15 fit `enumPosetsFor`'s `nfree ≤ 27` cap.
* 1 cell (`(K, w) = (10, 4)`) requires raising the cap to
  `nfree ≤ 30`, putting it at `≈ 10⁹` masks per cell.
* The Bool enumerator's existing fast-path (`findSymmetricPair`)
  closes the symmetric majority uniformly.
* The slow-path linear-extension DP handles the asymmetric residual.
* No new project axioms required.

### 4b. The (K, w) = (10, 4) boundary — three viable mitigations

1. **Raise the enumerator's `nfree > 27` hard-cap to `≤ 30`** and
   accept the `~10⁹` mask iteration as a one-time `native_decide`
   cost. Build window: extrapolating from `case3_balanced_w1`'s
   `nfree ≤ 18` build time of seconds-to-minutes, `nfree = 30` is
   likely a wall-clock cost in the *minutes-to-hours* range,
   possibly requiring a build-server (not laptop) for the final
   `native_decide` evaluation. Acceptable in principle; needs
   build-window plan.

2. **Decompose `(10, 4)` into structural sub-cases** that each fit
   `nfree ≤ 27`. E.g., split on whether band-pair `(1, 6)` is
   incomparable (then the `(1, 6)` free edge is fixed to "off",
   reducing nfree by 1). Cascading splits: 4 splits of nfree-1
   reductions → 16 sub-cases each at `nfree = 26 = 67M masks`,
   total `~10⁹` masks but split across 16 separate
   `native_decide` calls (each laptop-feasible).

3. **Structural carve-out**: observe that under cap 1 at
   `K = 10, w = 4`, the partial order has at most `nfree = 30`
   free edges *but* width-3 + irreducibility cut this down sharply.
   Concretely, width-3 on 10 elements has Brightwell-Felsner-Trotter
   enumeration count (OEIS A006455 — see mg-4d7b's reference list)
   that is far smaller than `2^30`. Could enumerate width-3 posets
   directly (rather than per-mask edge enumeration) and check each
   for the layered-bandwidth ≤ 4 + Szpilrajn-compatibility +
   irreducibility predicates. **This is what mg-4d7b is actually
   doing** in Phase A — see §5 for the coordination.

### 4c. Why D3 (intractable) is **NOT** the verdict

D3 would mean: even with the bounded-finite-domain reduction, the
enumeration cannot be completed in any realistic Lean build
window, AND no structural argument is available.

Counter-evidence:

* `case3_certificate`'s existing scope `(K = 3, w ∈ {1,2,3,4})`
  already enumerates `~344K` configs at `w = 1, sizeLimit = 9` and
  `~103K` configs at `w ∈ {2,3,4}, sizeLimit = 7`. These build
  successfully via `native_decide`. The Option D extension to the
  15 cap-1 cells is *quantitatively comparable* or *smaller* in
  aggregate (the cap-1 restriction is a strong pruning).
* `option_c_K2_closure`'s `case2_certificate` enumerates 9 K=2
  band-tuples (`bandSizesGen 2 6`) via `native_decide` with no
  build-window issues.
* mg-4d7b's Phase A target (~1M width-3 non-chain posets at
  `|β| ≤ 10`) is well within the OEIS / poset-enumeration
  literature's ability (Brightwell, Felsner, Trotter et al. have
  computed these counts directly).

So D3 is ruled out. The boundary `(10, 4)` cell is a build-window
matter, not a tractability matter.

### 4d. **D1 (uniform argument) — NOT operative**

Per §3b, no uniform argument candidate survives the F1/F2/F3
obstructions or the paper's own admission of enumeration in
`rem:enumeration`. D1's failure is **structural, not effort-bound**
(consistent with the option (δ) park rationale in
`why-hC3-is-structural.md`).

### 4e. Summary classification

| Sub-classification | Verdict | Notes |
|---|---|---|
| D1 (uniform structural) | **NO** | Paper admits enumeration; F3 30-year gap; no candidate survives. |
| D2 (enumeration tractable) | **YES (with caveat)** | 14/15 cells fit existing enumerator; 1 cell needs raised cap or structural decomposition. |
| D3 (intractable) | **NO** | Per existing certificate precedent; mg-4d7b's parallel computation underwrites feasibility. |

**Overall verdict: D2 with a single boundary caveat at
`(K, w) = (10, 4)`, mitigable three different ways.**

---

## 5. Phase 4 — recommendation and mg-4d7b coordination

### 5a. mg-4d7b: PROCEED

mg-4d7b is the natural execution polecat for the Phase D2 path.
Its scope:

* **Phase A** (enumerate ~1M width-3 non-chain posets at
  `|β| ≤ 10`): the math-paper-level deliverable. Covers both the
  Case3Witness Option-D-narrow scope **and** any future
  Option-A/B/C refactor that needs to handle small-`|β|` leaves
  (any such refactor will hit these leaves regardless of dispatch
  shape).
* **Phase B** (HasBalancedPair-verify each poset): the
  mathematical-truth check; catches a hypothetical counterexample
  to the 1/3-2/3 property on small cases (a major event if
  surfaced, but extremely unlikely per the existing partial
  enumerations in the literature).
* **Phase C** (Lean-ready packaging): the bridge artefact for
  Option-D-narrow Lean execution.
* **Phase D** (construct cap-5-satisfying LB for each poset):
  the partial-D-broad payload. **Closes
  `LayeredBalanced.lean:626` for `|α| ≤ 10` only** — see §5c.

mg-4d7b should **not be shelved**. The enumeration is genuinely
needed for D2 (and for any future small-case discharge).

### 5b. What mg-4d7b's GREEN gets us

Post-mg-4d7b-GREEN:

* **Option D-narrow** (Lean execution): a follow-on ticket
  refactors `Case3Witness_proof`'s out-of-scope branch to consume
  the extended certificate, replacing the
  `case3Witness_hasBalancedPair_outOfScope` axiom. The
  `Case3Witness_proof` then becomes **axiom-free** (modulo the
  standard `Lean.ofReduceBool` from `native_decide`).
* **Partial D-broad**: the `LayeredBalanced.lean:626` `sorry` is
  closable for `|α| ≤ 10` via mg-4d7b's Phase D LB construction.
  Headline holds unconditionally on `|α| ≤ 10`.
* **Headline-level status**: width-3 1/3-2/3 conjecture is
  **proved in Lean for `|α| ≤ 10`** (a non-trivial mathematical
  statement on its own — likely covered by Brightwell et al.'s
  small-case enumerations, but the in-tree Lean-mechanised
  proof is the new artefact).

### 5c. What mg-4d7b's GREEN does NOT get us

* **`LayeredBalanced.lean:626` for `|α| ≥ 11`**: the K ≥ 2
  dispatch needs a cap-5-satisfying LB at the call site, which
  under cap 1 + cap 2 + cap 5 forces `|α| = K ≤ 10`. For
  `|α| ≥ 11`, **no LB satisfies all 5 caps** — the universal
  `Case3Witness β` becomes vacuously true (hypothesis
  conjunction false), but the substitution at
  `LayeredBalanced.lean:626` still fails because `canonicalLayered`
  has `w = |α|`.
* The `|α| ≥ 11` dispatch needs either:
  * **Option A**: Steps 1-7 deliver `w₀(γ) ≤ 4` upstream so
    `layeredFromBridges`-supplied L satisfies cap 5; thread L
    through to the call site rather than substituting
    `canonicalLayered`. **Blocked on faithful in-Lean Steps 1-7
    delivery.**
  * **Option B**: F3 strong-induction descent at the call site on
    `|α|`, with mg-4d7b-supplied small-`|α|` leaves. **Blocked on
    mg-b666 K=2 case-2-strict residual** for the inductive step's
    irreducible-leaf cardinality bound.
  * **Option C**: drop `Case3Witness` hypothesis entirely from
    the headline; same blockers as Option A.

So Daniel's framing in mg-4d7b's body — *"if i understand correctly
width 3 math is COMPLETE and that makes our job much easier, esp if
the only sorry is basically this enumeration"* — is partially correct:
the math becomes complete *on `|α| ≤ 10`*, and the residual sorry
becomes "find a cap-5-satisfying LB at `|α| ≥ 11`" which is the
familiar Steps 1-7 / mg-b666 problem. Not as dramatic a closure as
hoped, but a meaningful step.

### 5d. The Daniel framing of "K ≥ 2 dispatch closure"

The mg-0cbf ticket body states Option D "MIGHT be directly tractable
... closing K ≥ 2 dispatch WITHOUT needing Steps 1-7 w₀(γ)
(Option A) or mg-b666 K=2 case-2-strict unblock (Option B)". This
is **correct for Option D-narrow** (closing the residual axiom
inside `Case3Witness_proof`'s K ≥ 3 irreducible branch), which is
genuinely independent of Options A and B.

It is **not correct for Option D-broad** (closing
`LayeredBalanced.lean:626`'s cap-5 discharge for arbitrary `|α|`),
which still depends on Option A or B for `|α| ≥ 11`.

The honest reading: Option D-narrow is a **clean axiom-reduction
win** (drops project axiom count by 1), genuinely independent of
A/B; Option D-broad is a **partial close** (`|α| ≤ 10` slice)
still parallel to A/B for the full headline.

### 5e. Concrete next-step recommendations

1. **mg-4d7b**: PROCEED on its existing scope. The
   ~1M-poset enumeration is the right shape regardless of which
   downstream Option (D-narrow, D-broad, A, B) consumes it. Phase
   E should note the `|α| ≤ 10` boundary explicitly when
   scope-estimating the FINAL Lean closure ticket.

2. **Option D-narrow Lean execution** (filed *after* mg-4d7b
   lands): extend `case3_certificate` with the 15 cap-1 + cap-5
   cells. Strategy:
   * Add `case3_balanced_cap1_w2_K456`, `_w3_K4678`, `_w4_K45678910`
     (or similar slicing) as new theorems in
     `lean/OneThird/Step8/Case3Enum/Cap1.lean` (new file).
   * Each theorem: `enumPosetsFor w [1; K] = true := by native_decide`.
   * For `(K, w) = (10, 4)`: either raise `enumPosetsFor`'s
     `nfree > 27` cap to `≤ 30` (one-line change, slower build) OR
     structural decomposition into 16 cap-26 sub-cases.
   * In `Case3WitnessProof.lean`, route the `hStruct` branch via
     the extended certificate **under cap 1** (cap 1 is in scope
     at the dispatch site, so this is a typed restriction).
   * The `case3Witness_hasBalancedPair_outOfScope` axiom becomes
     **unused** by `Case3Witness_proof`'s discharge chain — file
     a follow-on cleanup ticket to remove the axiom.
   * Estimated effort: ~200-400 LoC + native_decide build-time
     extension; single-polecat scope.

3. **Partial D-broad Lean execution** (filed *after* mg-4d7b's
   Phase D lands): wire mg-4d7b's per-`|β| ≤ 10` cap-5-satisfying
   LB constructor into `LayeredBalanced.lean:626`'s K ≥ 2
   dispatch under an `|α| ≤ 10` case split. The
   `|α| ≥ 11` branch remains a `sorry` (now narrowed in scope —
   the "no cap-5-satisfying LB exists at this size" is the precise
   mathematical content of the unmitigated gap, surfacing the
   Steps-1-7 / mg-b666 dependency more cleanly than the current
   `canonicalLayered` substitution does).

4. **Option A / Option B**: **NOT superseded by Option D**. Daniel's
   mg-b666 ticket and the Steps 1-7 `w₀(γ)` delivery remain on the
   roadmap for the `|α| ≥ 11` slice. The Option D path is
   complementary, not substitutive.

### 5f. Mathematical correctness assessment

The plan is **mathematically sound**: it does not assume the
conclusion. It does, however, depend on:

* The truth of the 1/3-2/3 property on `|β| ≤ 10` width-3 non-chain
  posets. **This is widely conjectured and partially verified in the
  literature** (Brightwell, Felsner, Trotter; cf. mg-4d7b's
  reference list). mg-4d7b's Phase B is the in-tree verification.
* The `case3_certificate`'s existing extension pattern continues
  to work at `nfree ≤ 27`. **Demonstrated in tree.**
* `native_decide`'s build window can absorb the additional 14
  certificate entries (plus `(K, w) = (10, 4)` via one of the
  three mitigations). **Conservative extrapolation from existing
  build times.**

---

## 6. Cross-references and load-bearing claims

* `lean/OneThird/Step8/LayeredBalanced.lean:461-472` —
  post-cap-5 `Case3Witness.{u}` (the lemma under analysis).
* `lean/OneThird/Step8/LayeredBalanced.lean:626-756` —
  `lem_layered_balanced` with K ≥ 2 dispatch and the structured
  cap-5 `sorry` (mg-d5a0).
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:256-547` —
  `Case3Witness_proof` strong-induction discharge.
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:147-153` —
  `case2_discharge_of_injective` (cap-1 → Case 2 vacuous).
* `lean/OneThird/Step8/OptionC/K2Closure.lean:500-547` —
  `option_c_K2_closure` (K = 2 discharge, fully proved).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1498-1525` —
  `InCase3Scope` and `InCase3Scope.w_mem`.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1681-1694` —
  `bounded_irreducible_balanced_hybrid` (hCert + hStruct dispatch).
* `lean/OneThird/Step8/Case3Residual.lean:208-217` —
  `case3Witness_hasBalancedPair_outOfScope` axiom (the operational
  target of Option D-narrow).
* `lean/OneThird/Step8/Case3Residual.lean:265-280` —
  `hStruct_of_case2_discharge`.
* `lean/OneThird/Step8/Case3Dispatch.lean:156-179` —
  `InSitu.Case2Witness` / `InSitu.Case3Witness` (inner predicates).
* `lean/OneThird/Step8/Case3Enum.lean:324-342` —
  `enumPosetsFor` (the Bool enumerator with `nfree > 27` cap).
* `lean/OneThird/Step8/Case3Enum/Certificate.lean:71-78` —
  `case3_certificate` (existing 5-cell scope).
* `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9) —
  pre-cap-5 architecture analysis; cap-5 proposal.
* `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0) — cap-5 Lean
  landing session log; the operational `sorry` placement.
* `docs/why-hC3-is-structural.md` — F1/F2/F3 obstructions
  (Cardinality / Brightwell-vacuity / 30-year gap); F1 and F2
  rule out specific uniform-argument candidates (U1, U6 in §3b
  here); F3 is the literature-level evidence against D1.
* `docs/path-c-track-1-status-1.md` (mg-b666) — K = 2 case-2-strict
  residual; **named blocker for Option B**, NOT for Option D-narrow.
* `docs/compatibility-geometry-pathP3-scoping.md` — `nfree > 27`
  build-window discussion (referenced in cell `(10, 4)` mitigation
  analysis).
* OEIS A006455 — width-3 poset counts (referenced in mg-4d7b's
  Phase A scope).

---

## 7. Summary

Post-cap-5, `Case3Witness.{u}`'s universal quantifier has effective
domain `(K, w) ∈ {2, …, 10} × {0, …, 4}` with `K ≤ 2w + 2`. Under
cap 1, `|β| = K`. The discharge proof `Case3Witness_proof`
recurses by F3 strong induction, with leaves dispatched via the
F5a `case3_certificate` (in-scope, 5 cells covered) or the
`case3Witness_hasBalancedPair_outOfScope` axiom (out-of-scope,
15 cells under cap 1).

**Option D-narrow** — replace the residual axiom by extending
`case3_certificate` to the 15 cap-1 cells — is
**D2-tractable**. 14 of 15 cells fit the existing
`enumPosetsFor` `nfree ≤ 27` cap; the 15th, `(K, w) = (10, 4)`,
requires raising the cap to `nfree ≤ 30` (build-window cost) or
structural decomposition into smaller sub-cells (16 cap-26
sub-cases). No new project axioms; the
`case3Witness_hasBalancedPair_outOfScope` axiom becomes operationally
unused. **No uniform argument (D1) is available** — the paper
itself admits enumeration in `rem:enumeration`, and the F1/F2/F3
obstructions rule out all elementary alternatives.

**Option D-broad** — close `LayeredBalanced.lean:626` for arbitrary
`|α|` — is **NOT closable by Option D alone**. The dispatch
substitutes `canonicalLayered α` (cap 5 fails at `|α| ≥ 5`); under
cap 1 + cap 2 + cap 5 the universal hypothesis is vacuous at
`|α| ≥ 11`, so no LB substitution discharges that range.
Closes Option B (mg-b666 unblock) or Option A (Steps 1-7 deliver
`w₀(γ) ≤ 4`) remain the routes for `|α| ≥ 11`.

**mg-4d7b coordination**: PROCEED on mg-4d7b. Its Phases A-B-C
underwrite Option D-narrow; its Phase D delivers the partial
D-broad closure (`|α| ≤ 10` slice). Post-mg-4d7b-GREEN, the
follow-on Lean ticket implements Option D-narrow (axiom-free
`Case3Witness_proof`) and the partial D-broad (`|α| ≤ 10`
unconditional headline; `|α| ≥ 11` retains an honest
Steps-1-7-or-mg-b666 sorry).

**Verdict: GREEN-D2-with-`(10,4)`-boundary-caveat, Option D-narrow
clean axiom-reduction, Option D-broad partial close on `|α| ≤ 10`,
Options A/B remain operative for `|α| ≥ 11`.**
