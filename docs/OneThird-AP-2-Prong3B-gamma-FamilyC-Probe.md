# OneThird — AP-2 Prong 3B-gamma: Family C (order-polytope / Ehrhart) probe

*Work item **mg-3b16**. Follow-up to mg-2715 (AP-2 Prong 3B-beta, BROADER-FLOOR-CANDIDATE + proven Wall Lemma §3.2 on Family D), whose boundary probe surfaced the **4/11 seed** — a generic graded width-3 poset with `Q = 4/11 ≈ 0.3636 ∈ (1/3, 8/21)`, below the Prong-3A SP floor. This prong tests whether **Family C (order polytope / Ehrhart)** — one of Daniel's cited algebraic-program inspirations — parametrises that seed or opens a fresh path below it. Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md`](OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md) (the 4/11 seed flag + the Wall-Lemma precedent); [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the `8/21` analytic theorem, the template for a Prong-3C analytic follow-up); [`OneThird-AP-2-Prong2-FamilyB-SP-Probe.md`](OneThird-AP-2-Prong2-FamilyB-SP-Probe.md) (SKEW-ARTIFACT + V1+V2 GENUINE template); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§3C,4C,6,8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3b_gamma_familyC_probe.py`](../scripts/onethird_ap2_prong3b_gamma_familyC_probe.py) — order-polytope / Ehrhart engine (MC) + the 4/11 seed extraction + a **five-engine** cross-validation harness (M1 primary DP, M2 AP-0 kernel, M3 Prong-2 independent check, M4 brute force, MC Ehrhart order-polynomial) + the exhaustive graded-3-level sweep + a broader general-width-3 probe + the §8.2 STRICT guard. Default run ≈ 75 s (the exhaustive graded scan is ≈ 60 s of it); `--wide` pushes the broader probe to `n ≤ 8` (a few minutes). A clean exit is the five-engine agreement + guard clearing.*

---

## 0. Headline

**VERDICT: NEW-TERRITORY-BELOW-4/11, with a proven NEW-WALL sub-finding (Ehrhart-dilation `Q`-invariance).**

Family C (the order polytope `O(P)` and its Ehrhart / order-polynomial volume engine) **parametrises the 4/11 seed exactly** — the seed *is* the order polytope of the `(n1,n2,n3)=(1,3,1)` shape, and `Q = 4/11` is literally a ratio of order-polytope volumes, computed in closed form (`vol O(P) = e(P)/n!`). Used as the volume engine across width-3 posets, Family C then **breaks strictly below the seed**:

```
1/3 ≈ 0.33333  <  14/39 ≈ 0.358974  <  4/11 ≈ 0.363636  <  8/21 ≈ 0.380952,
```

a width-3 poset at `n = 7` with `Q = 14/39 < 4/11` (still `> 1/3` by `0.0256`). The minimum **drops once and then plateaus**: `4/11` at `n = 5,6`, then `14/39` holding at both `n = 7` **and** `n = 8`. This is a *fresh* width-3 region strictly below the 4/11 seed — `NEW-TERRITORY-BELOW-4/11` per the V4 screening — and the drop-then-plateau shape localises precisely where a Prong-3C analytic "does it drop again toward `1/3`, or plateau above it" target lives (whether `14/39` is the next floor or just the `n=7,8` minimum is the open question).

The **NEW-WALL sub-finding (proven, §3):** Family C is *not an independent source of posets* — `O(·)` is a functor `poset → polytope` (Stanley) and a faithful re-encoding of the linear-extension combinatorics. Its two natural algebraic parameters both fail to open new width-3 territory: **(a) the Ehrhart dilation parameter `t` is `Q`-invariant** (Wall Lemma §3.2 — `Q` is a ratio of volumes, scale-invariant), and **(b) the combinatorial type at fixed `n`** simply *is* the width-3 poset sweep. So the roadmap-§4C "closed-form-`Q`-in-a-parameter" ambition for C cannot be a *dilation* sweep; the closed form lives in the **combinatorial type** `(n1,n2,n3,covering structure)` — which Family C *does* deliver, as a closed-form-rational volume ratio. This matches the roadmap's own §3C/§4C framing of C as an **engine / smoothing lens**, here upgraded from caveat to proven fact and turned into the productive instrument that finds `14/39`.

| family region | min `Q` (width exactly 3) | vs `4/11` | vs `8/21` | computability |
|---|---|---|---|---|
| **4/11 seed** — order polytope of `(1,3,1)` | **4/11 ≈ 0.36364** | `=` | `<` | exact, closed-form `vol = 11/120`; five engines |
| **graded-3-level width-3** (the seed's own family; finite, ≤ 9 elts) | **4/11** | `=` | `<` | exhaustive (92,134 configs), exact |
| **general width-3 posets** (order-polytope engine, `n ≤ 7`) | **14/39 ≈ 0.35897** | `<` (by `0.0047`) | `<` | exhaustive to `n=7`, exact, five engines |
| general width-3 posets (`n ≤ 8`, `--wide`) | **14/39** (plateau) | `<` | `<` | exhaustive to `n=8` (643,236 scanned) |

**§8.2 anti-Cheeger guard (INHERITED STRICT) does NOT fire.** The lowest `Q` anywhere in the entire sweep is `14/39 > 1/3`; no `Q ≤ 1/3` candidate exists. The width-2 textbook gadget `point ‖ (y<z)` touches `Q = 1/3` exactly (the conjecture's *satisfied* boundary, a theorem — logged as a boundary touch and independently reconfirmed). No fresh-fourth-codebase halt is triggered.

---

## (i) Vision alignment (V1+V2+V3+V4) — verbatim from the ticket

- **V1 (algebraic objects):** *order polytopes O(P) of finite posets are a clean algebraic family — defined by linear inequalities indexed by the cover-relations of P. Stanley's theorem (Order Polytopes and Linear Extensions, 1986) gives vol(O(P)) = e(P) / n!. Parameterised families: (a) the dilation parameter t in the Ehrhart polynomial L_O(P)(t) = number of 1/t-lattice points; (b) the poset's combinatorial type for fixed n. DISTINCT from skew (Family A), SP (Family B), finite-geometry (Family D).*
- **V2 (computable Q):** *Q on a poset P via the order polytope reduces to ratios of facet integrals over O(P). For graded width-3 posets specifically, these ratios are closed-form RATIONAL FUNCTIONS of the level-population vector (n1, n2, n3) and the bipartite covering structure between levels — closed-form, NOT Monte-Carlo, NOT generic DP. The polecat from mg-2715 already computed Q exactly on 92,134 such posets via the graded3_min_Q engine using exact rational arithmetic — V2 is empirically realisable.*
- **V3 (parameter space):** *for graded 3-level posets, the parameters are (n1, n2, n3) = level populations summing to n, plus the bipartite covering structure between L1-L2 and L2-L3. Width-3 condition pins min(n1, n2, n3) ≤ 3 and width = max level size. Sweep over (n1, n2, n3, bipartite structure).*
- **V4 (sharpness-or-pivot signal):** *screening question per mg-2715 dispatch guidance — does Family C reach Q < 4/11 anywhere (NEW-TERRITORY-BELOW-4/11), Q < 1/3 anywhere (COUNTEREXAMPLE-CANDIDATE; §8.2 STRICT third-codebase HALT), Q in [4/11, 8/21) anywhere (BROADER-TERRITORY-BELOW-8/21 confirmation that the seed extends), or Q ≥ 8/21 across the family (suggests the seed is non-Family-C-parameterisable, file Prong 3C separately)? Pre-flagged NEW-WALL: if Family C's algebraic parameter (dilation, lattice type, etc.) does NOT survive width-3 filter, PROVE the wall as a Wall Lemma §3.x and report cleanly (mg-2715 set the precedent).*

**Which V4 branch fired:** the **first** — `Q < 4/11` is reached (`14/39` at `n = 7`), so **NEW-TERRITORY-BELOW-4/11**. The pre-flagged NEW-WALL *also* fired, but in a subtler form than Family D's: the order-polytope **dilation** parameter does not survive as a `Q`-mover (it is `Q`-invariant — Wall Lemma §3.2, proven below), and the order polytope adds no posets beyond the generic width-3 family. So Family C does not give a *new dilation/lattice sweep*; it gives the **closed-form volume engine** on the existing width-3 combinatorial parameter, and that engine reveals the below-4/11 descent. On V2 the closed-form-rational-`Q` claim is *confirmed* (the seed's `Q = 4/11` is the exact volume ratio `e(P+x<y)/e(P)`, and the graded-3-level family is computed exactly via `vol = e/n!`); on V3 the graded-3-level family is swept exhaustively (it is finite — each rank is an antichain, so each rank has `≤ 3` elements, total `≤ 9`).

---

## 1. Setup and the `Q` metric

The **order polytope** of a finite poset `P` (Stanley, *Two poset polytopes*, 1986) is

```
O(P) = { f : P → [0,1]  |  f(a) ≤ f(b) whenever a ≤ b in P }  ⊂ [0,1]^P.
```

It triangulates into `e(P)` unit simplices, one per linear extension `σ` (the simplex `0 ≤ f(σ_1) ≤ … ≤ f(σ_n) ≤ 1`, each of volume `1/n!`), so

```
vol O(P) = e(P) / n!         (n = |P|).
```

For an **incomparable** pair `x, y`, the sub-polytope `O(P) ∩ {f(x) ≤ f(y)}` is *exactly* the order polytope of the refined poset `P + (x<y)` (imposing one extra cover relation slices off precisely that half-space). Hence, under the uniform distribution on linear extensions,

```
Pr[x < y]  =  vol( O(P) ∩ {f(x) ≤ f(y)} ) / vol O(P)  =  e(P + x<y) / e(P),
Q(P)       =  max over incomparable {x,y} of min( Pr[x<y], Pr[y<x] )
           =  1/2 − min over incomparable pairs of |Pr[x<y] − 1/2|.
```

So `Q(P)` is a **ratio of order-polytope volumes** — the roadmap-§3C/§4C computability claim, realised exactly. The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3` for every non-chain finite poset; *small* `Q` is the dangerous (counterexample) regime. Reference bars: `1/3 ≈ 0.3333` (global textbook tight); `8/21 ≈ 0.3810` (Prong-3A width-3 SP theorem, sharp at `T*`); `4/11 ≈ 0.3636` (the seed); `2/5 = 0.4` (Family D floor); `27/70 ≈ 0.3857` (skew artifact).

**The Family-C engine (MC) — genuinely Ehrhart, distinct from the DP.** The Ehrhart polynomial of `O(P)` is the **order polynomial**

```
Ω_P(t) = #{ order-preserving maps P → {1,…,t} }
       = #{ multichains ∅ = I_0 ⊆ I_1 ⊆ … ⊆ I_t = P in the ideal lattice J(P) },
```

a degree-`n` polynomial in `t` whose **leading coefficient is `vol O(P) = e(P)/n!`**. Sampling at the consecutive integers `t = 1,…,n+1`, the `n`-th finite difference collapses to the leading term times `n!`:

```
e(P) = Δ^n Ω_P  =  Σ_{k=0}^{n} (−1)^{n−k} C(n,k) Ω_P(1+k).
```

We compute `Ω_P(t) = (Z^t)[∅][P̂]` by powers of the zeta matrix `Z` of the ideal lattice (`Z[I][K] = 1` iff `I ⊆ K`), in exact integer arithmetic — counting **lattice points of dilations of the order polytope** and reading the volume off the Ehrhart leading coefficient. This is structurally different from the order-ideal DP (M1), the AP-0 kernel (M2), the minimal-element-removal recursion (M3) and brute force (M4); it is the **fifth** engine, run at every instance of the primary sweeps. Monte-Carlo is never used.

---

## (ii) The extracted 4/11 seed witness + five-engine verification

**The seed (carry-forward from mg-2715 `graded3_min_Q`, reused exactly):** the graded 3-level width-3 poset

```
level populations (n1, n2, n3) = (1, 3, 1):
  L1 = {a0},   L2 = {b0, b1, b2},   L3 = {c0};
covers:  L1→L2:  a0 < b0,  a0 < b1        (a0 is NOT below b2)
         L2→L3:  b0 < c0,  b2 < c0        (b1 is NOT below c0)
induced: a0 < c0.
```

The two incomparable elements realising `Q = 4/11` are the antichain pair `{b0, b1}` in `L2`: `Pr[b0 < b1] = 7/11`, so `Q = min(7/11, 4/11) = 4/11`.

**Order polytope of the seed.** `O(P) ⊂ [0,1]^5` in coordinates `(a0, b0, b1, b2, c0)` is cut out by the four facet inequalities `a0 ≤ b0`, `a0 ≤ b1`, `b0 ≤ c0`, `b2 ≤ c0`. Then

```
e(P)            = 11
vol O(P)        = e(P)/5! = 11/120 ≈ 0.091667
Pr[b0 < b1]     = vol(O(P) ∩ {f(b0) ≤ f(b1)}) / vol O(P) = e(P + b0<b1)/e(P) = 7/11
Q(seed)         = min(7/11, 4/11) = 4/11 ≈ 0.363636.
```

**The explicit volume (closed form).** Integrating `O(P)` over `(a0, b0, b1, b2, c0) ∈ [0,1]^5` with `a0 ≤ b0`, `a0 ≤ b1`, `b0 ≤ c0`, `b2 ≤ c0`: `b1` is free above `a0` (factor contributing `∫_{a0}^1`), `b2` is free below `c0`, and `a0 ≤ b0 ≤ c0` is a 3-chain. Carrying out the nested integral gives `vol O(P) = 11/120` exactly, i.e. `e(P) = 11` — matching the Ehrhart leading-coefficient route and all four combinatorial engines.

**Five-engine cross-check (the acceptance gate, roadmap §4).** Every instance is validated by

| engine | mechanism | `e` | `Q` |
|---|---|---|---|
| **M1** primary | order-ideal DP (Prong-3B-beta harness) | 11 | 4/11 |
| **M2** AP-0 | generic width-3 kernel `Q_via_dp` | 11 | 4/11 |
| **M3** independent | minimal-element-removal recursion (8.2 2nd codebase) | 11 | 4/11 |
| **M4** brute | full linear-extension permutation enumeration | 11 | 4/11 |
| **MC** Family C | Ehrhart order-polynomial leading coefficient | 11 | 4/11 |

All five agree exactly. The seed is reproduced both by the generic graded enumerator and, independently, as the `n = 5` argmin of the general-width-3 probe (relabelled `a0=0, c0=4, {b0,b1,b2}={1,2,3}`).

---

## (iii) V2 gate analysis — does Family C parametrise width-3 with closed-form `Q`?

**Answer: YES for the combinatorial-type parameter (closed-form-rational volume ratio); NO for the dilation parameter (proven `Q`-invariant — Wall Lemma §3.2).**

### 3.1 What clears the gate (the closed-form-rational handle)

For a graded 3-level width-3 poset with level populations `(n1, n2, n3)` (each `≤ 3`) and a fixed bipartite covering structure, the order polytope is a low-dimensional `0/1`-facet polytope and `vol O(P) = e(P)/n!` is an exact rational, computable in closed form by iterated integration (or, as here, by the Ehrhart order-polynomial leading coefficient). Each `Pr[x<y] = e(P+x<y)/e(P)` is then a ratio of two such rationals, and `Q` is `1/2 − min |Pr − 1/2|` over the (few) incomparable pairs — a **closed-form rational function of `(n1,n2,n3, covering structure)`**, exactly the V2 claim. The seed's `Q = 4/11 = min(7/11, 4/11)` with `e = 11`, `e(P+b0<b1) = 7` is the worked instance. Because the family is finite (`≤ 9` elements), the sweep is *exhaustive*, and `Q` is exact at every one of the 92,134 enumerated configurations (computability fraction 100%, Monte-Carlo never used).

### 3.2 Wall Lemma §3.2 — the Ehrhart dilation parameter is `Q`-invariant

> **Wall Lemma §3.2.** Let `P` be a finite poset and `t ≥ 1` the Ehrhart dilation parameter of `O(P)`. Then `Q(P)` is independent of `t`: the dilation parameter does **not** parametrise a family of width-3 posets with varying `Q`.

**Proof.** `Pr[x<y] = vol(O(P) ∩ {f(x) ≤ f(y)}) / vol O(P)` is a ratio of volumes, and volume scales homogeneously under dilation: `vol(t·K) = t^n vol(K)` for any region `K ⊆ R^n`. Dilating both numerator and denominator by `t` multiplies each by `t^n`, leaving the ratio — and hence every `Pr[x<y]` and `Q(P)` — unchanged. Equivalently, in the lattice-point picture the per-`t` ratios `Ω_{P+x<y}(t)/Ω_P(t)` are *not* equal to `Pr[x<y]` for finite `t` (they carry lower-order Ehrhart terms), but they converge to it as `t → ∞`, and the exact value is the leading (volume) ratio `e(P+x<y)/e(P)`, which is a property of `P` alone. The dilation parameter is therefore orthogonal to `Q`. ∎

*(Demonstrated in the script §3 on the seed: the finite-`t` ratios `Ω_{P+b0<b1}(t)/Ω_P(t)` run `1, 5/6, 47/61, 76/103, 28/39, …` — visibly NOT constant in `t` — while the exact volume ratio is the `t`-independent `7/11`. The `t`-sweep moves the lattice-point ratios but never the balance constant.)*

### 3.3 The structural consequence (order polytope is a faithful functor)

`O(·)` is a functor from posets to polytopes; by Stanley's triangulation it is a *faithful re-encoding* of the linear-extension combinatorics, **not an independent source of posets**. Combined with §3.2, the only `Q`-moving Family-C parameter is the **combinatorial type of `P`** — which is just "sweep width-3 posets". So Family C cannot reach any `Q` that the generic width-3 family does not already reach; conversely it computes that `Q` exactly and in closed form. This is precisely the roadmap-§3C/§4C role of C as an **engine / smoothing lens on A/B (and D)**, here proven, and it is the productive lens: applied across general width-3 posets (not just the seed's finite graded family) it surfaces the below-4/11 descent (§5). The NEW-WALL is therefore *clean and disclosed* (per the §8 "name the wall" discipline and the Prong-3B-beta precedent), and it does **not** block the verdict — it sharpens it.

---

## (iv) Sweep table

All `Q` values are exact `Fraction`s. The primary sweeps are cross-validated by all five engines at the seed and at every reported extremum (M1+M2+M3+M4+MC); the broader probe fires the §8.2 STRICT guard on **every** instance (it HALTS at the first `Q ≤ 1/3`) and re-verifies extrema through all five engines.

### 4.1 Sanity controls (ticket ROUTINE CHECKS)

| instance | `n` | width | `e` | `Q` | note |
|---|---:|---:|---:|---|---|
| textbook gadget `point ‖ (y<z)` | 3 | 2 | 3 | **1/3** | width-≤2, tight boundary (theorem) |
| width-2 graded `a,b < c,d` | 4 | 2 | 4 | **1/2** | width-≤2 recovers `Q ≥ 1/3` ✓ |
| width-3 antichain | 3 | 3 | 6 | **1/2** | — |
| `M_3` diamond `0 < {x,y,z} < 1` | 5 | 3 | 6 | **1/2** | order polytope of the `F_2^2` lattice (Family-D bridge) |

### 4.2 Primary sweep — graded-3-level width-3 (the seed's own family, exhaustive)

| quantity | value |
|---|---|
| width-3 graded-3-level configs scanned (exhaustive, finite family) | **92,134** |
| computability fraction (exact, all engines agree at extrema) | **100%** (Monte-Carlo never used) |
| **min `Q`** | **`4/11` = 0.363636** |
| argmin | `(n1,n2,n3)=(1,3,1)` — the seed (a0<b0,b1; b0,b2<c0) |
| `# with Q < 1/3` | **0** |

The graded-3-level width-3 family is *finite* (each rank is an antichain ⟹ `≤ 3` per rank ⟹ `≤ 9` elements), so its minimum is genuinely `4/11`, attained by the seed — Family C parametrises the seed exactly and confirms it is the graded-3-level extremum.

### 4.3 Broader probe — general width-3 posets (order-polytope engine)

| `n` | naturally-labelled width-3 posets scanned | running min `Q` |
|---:|---:|---|
| 3 | 1 | 1/2 |
| 4 | 16 | 1/2 |
| 5 | 212 | **4/11** ≈ 0.36364 (the seed) |
| 6 | 2,842 | 4/11 |
| 7 | 40,916 | **14/39** ≈ 0.35897 `(< 4/11)` |
| 8 (`--wide`) | 643,236 | **14/39** (plateau — same value) |

*(Counts are naturally-labelled — each unlabelled poset appears once per natural labelling; this over-counts but is exhaustive over width-3 posets up to `n`, correct for a min-`Q` search. `Q` is relabel-invariant.)*

The `n = 7` argmin (`Q = 14/39`, `e = 39`, `Pr[b<b'] = 25/39`) is a width-3 poset strictly below the seed, re-verified through all five engines. The minimum **drops once** (`4/11 → 14/39` at `n = 7`) and then **plateaus** (`14/39` again at `n = 8`; the `n=8` argmin is the `n=7` extremal with one element adjoined on top). Whether `min Q(n)` drops again past `n = 8` or plateaus at `14/39 > 1/3` is the open Prong-3C question.

### 4.4 §8.2 guard

Lowest `Q` anywhere in the entire Family C sweep is `14/39 > 1/3` (`n ≤ 8`). No `Q ≤ 1/3` candidate ⟹ the **INHERITED STRICT** guard does not fire and no fresh-fourth-codebase halt is triggered. The single `Q = 1/3` boundary touch is the width-2 textbook gadget (the conjecture's *satisfied* equality, a theorem), independently reconfirmed.

---

## (v) Verdict

**NEW-TERRITORY-BELOW-4/11**, with a proven **NEW-WALL** sub-finding (Ehrhart-dilation `Q`-invariance, Wall Lemma §3.2).

- **Family C parametrises the seed exactly.** The 4/11 seed *is* the order polytope of the `(1,3,1)` shape; `Q = 4/11` is the exact volume ratio `e(P+b0<b1)/e(P) = 7/11`, `Q = min(7/11,4/11)`, with `vol O(P) = 11/120`. Five engines (including the genuinely-Ehrhart MC) agree.
- **It breaks below the seed.** Used as the volume engine across general width-3 posets, Family C reaches `Q = 14/39 ≈ 0.3590 < 4/11` at `n = 7` (still `> 1/3`); `min Q(n)` **drops once** (`4/11 → 14/39`) and then **plateaus** (`14/39` again at `n = 8`). So Family C does reach `Q < 4/11` (the V4 NEW-TERRITORY-BELOW-4/11 branch), opening a fresh width-3 region strictly below the seed — the live counterexample-hunt corridor `(1/3, 4/11)`.
- **NEW-WALL (proven).** The order-polytope **dilation** parameter `t` is `Q`-invariant (Wall Lemma §3.2: `Q` is a scale-invariant volume ratio), and `O(·)` is a faithful functor producing no new posets. So Family C is an **engine/smoothing lens**, not an independent poset family — its closed-form-rational `Q` lives in the *combinatorial type* `(n1,n2,n3,covers)` / general width-3 structure, never in a dilation/lattice sweep. The V2 closed-form-in-`t` ambition is structurally blocked; the V2 closed-form-in-combinatorial-type is delivered. (Clean diagnosis per the §8 / Prong-1 / Prong-3B-beta "name the wall" discipline.)
- **§8.2 guard cleared.** Lowest `Q` is `14/39 > 1/3`; no `Q ≤ 1/3` candidate; STRICT guard does not fire. The `Q = 1/3` touch is the satisfied width-2 boundary, reconfirmed.

This is **not** COUNTEREXAMPLE-CANDIDATE (no `Q < 1/3`), not BROADER-TERRITORY-BELOW-8/21-only (it goes below 4/11, not merely into `[4/11,8/21)`), and not BROADER-FLOOR-CANDIDATE (`8/21` is undercut). The seed is confirmed to live in genuine algebraic (order-polytope) territory, and the territory **extends strictly below it**.

---

## (vi) Suggested Prong 3C brief (gated on this verdict)

The NEW-TERRITORY-BELOW-4/11 result + the descent of `min Q(n)` localise the live question precisely. Prong 3C should be **analytic**, on the general width-3 poset family with the order-polytope engine, mirroring the Prong-3A SP template:

**Prong 3C (recommended) — analytic `inf Q` over width-3 posets via order-polytope volumes (the drop-vs-plateau question).** The empirical shape `4/11 (n≤6) → 14/39 (n=7,8 plateau)` is exactly the "does it drop again toward `1/3` or plateau above it" question Prong 3A answered for SP (`8/21`, sharp at `T*`). The `n=8` plateau at `14/39` is suggestive but not conclusive (the next drop may need `n ≥ 9`). Brief shape: (a) characterise the `14/39` family — the `n=7` argmin and whether any `n=9,10` deformation drops below it (the script's broader-probe argmin witnesses are the seeds); identify the *combinatorial deformation* that lowers `Q` (which cover to add as `n` grows). (b) Using the order polytope's **smoothness** (roadmap §6.3 — volumes vary continuously in a relaxed shape), set up a continuous relaxation / Lawrence–Varchenko volume formula for the descent ray and compute `lim inf Q` analytically. (c) Decide: a limit `> 1/3` is a (width-3-restricted) sharpness result strictly below `8/21` (a genuinely new floor `< 4/11`); a limit `= 1/3` would say width-3 `Q` is dense down to the global bound; a dip `< 1/3` is a **candidate counterexample → §8.2 STRICT, fresh fourth codebase + brute-force re-verification before any claim**. The §8.2 guard rides along on every instance.

*(Parked / out of scope here per NON-GOALS: no analytic lower bound in this ticket — empirical sweep + verdict only; the analytic follow-up gates on this verdict shape. No Family A/B/D re-sweep. No Cheeger/cut-and-window. The seed-family-specific analytic follow-up that BROADER-TERRITORY would have triggered is **superseded** by this stronger NEW-TERRITORY finding — Prong 3C should target the general width-3 descent, not merely the seed's finite graded family.)*

---

## Carry-forwards (for the next polecat)

- **Verdict:** Family C (order polytope / Ehrhart) is the **closed-form volume engine** for width-3 `Q`, not an independent poset family. It parametrises the 4/11 seed exactly (`vol O(P)=11/120`, `Q=4/11`) and, applied across general width-3 posets, reaches **`14/39 ≈ 0.3590 < 4/11`** at `n = 7` (still `> 1/3`); `min Q(n)` **drops once then plateaus** (`4/11` at `n≤6`, `14/39` at `n=7,8`) — `NEW-TERRITORY-BELOW-4/11`.
- **The wall (reusable fact):** the Ehrhart **dilation parameter `t` is `Q`-invariant** (Wall Lemma §3.2 — `Q` is a scale-invariant volume ratio); `O(·)` is a faithful functor (no new posets). Family-C closed-form `Q` lives in the **combinatorial type**, never a dilation/lattice sweep. The V2-C gate clears as engine, not as independent family.
- **The live corridor (Prong 3C seed):** general width-3 posets, `min Q(n)` below `4/11` (drop to `14/39` at `n=7`, plateau at `n=8`) toward an unknown limit in `(1/3, 14/39]`. The `n=7` argmin `14/39` (witness in the script's §5 output) is the descent seed; whether it drops again past `n=8` is open.
- **Reusable instrument:** [`scripts/onethird_ap2_prong3b_gamma_familyC_probe.py`](../scripts/onethird_ap2_prong3b_gamma_familyC_probe.py) — the order-polytope/Ehrhart engine (`order_ideals`, `order_polynomial_values`, `ehrhart_count_extensions`, `ehrhart_Q`, `order_polytope_volume`), the seed extractor (`seed_4_11`), the general-width-3 enumerator (`gen_width3_posets`, `broader_width3_probe`), and the **five-engine** `verify_C` harness (the inherited M1+M2+M3+M4 + MC) with the §8.2 STRICT guard. Default ≈ 75 s; `--wide` (`n≤8`) a few minutes.
- **Reference bars:** `1/3` (global tight), `8/21` (width-3 SP theorem), `27/70` (skew artifact), `2/5` (finite-geometry floor), `4/11` (graded-3-level / seed), and now **`14/39 ≈ 0.3590`** (the lowest width-3 `Q` reached via the order-polytope engine to `n = 7`).
- **Guard discipline (INHERITED STRICT):** lowest `Q` swept is `14/39 > 1/3`; the guard distinguishes `Q < 1/3` (HALT, fresh fourth codebase — AP-0/Prong-2/3B-beta DP all used) from `Q = 1/3` (satisfied boundary, log + reconfirm).
