# OneThird — AP-2 Prong 3B-beta: Family D (finite-geometry incidence) width-3 viability + sweep

*Work item **mg-2715**. Follow-up to mg-7009 (AP-2 Prong 3A, GREEN — `Q ≥ 8/21` on width-exactly-3 SP posets, sharp at `T*`), which settled Family B (width-≤3 SP) as a bounded-null counterexample host. This prong pivots the counterexample hunt to Family D, directly honoring Daniel's unit-distance / point-line-incidence inspiration. Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the `8/21` SP theorem + gadget `G`, witness `T*`); [`OneThird-AP-2-Prong2-FamilyB-SP-Probe.md`](OneThird-AP-2-Prong2-FamilyB-SP-Probe.md) (SKEW-ARTIFACT verdict + `27/70`); [`OneThird-AP-2-Prong1-SelfDual-LowerBound.md`](OneThird-AP-2-Prong1-SelfDual-LowerBound.md) (Outcome-4 wall-and-name pattern); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§3D,4,6,8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3b_beta_familyD_probe.py`](../scripts/onethird_ap2_prong3b_beta_familyD_probe.py) — finite-geometry incidence enumerator + closed-form `M_{q+1}` + exhaustive width-3 sweep + four-engine cross-validation (primary DP, AP-0 kernel, Prong-2 independent codebase, brute force) + the §8.2 guard. Clean run ≈ 0.9 s (`--full-graded` for the exhaustive 92,134-poset boundary probe ≈ 60 s). A clean exit is the cross-check suite + guard passing.*

---

## 0. Headline

**VERDICT: BROADER-FLOOR-CANDIDATE (with a clean structural NEW-WALL sub-finding).**

Every genuine width-exactly-3 finite-geometry incidence poset in the swept range satisfies

```
Q ≥ 2/5 = 0.400000  >  8/21 ≈ 0.380952  >  1/3 ≈ 0.333333,
```

so Family D **hosts no counterexample** and does **not** even reach the Prong-3A SP floor `8/21` — it floors *higher*, at `2/5`. Family D is therefore a **second family** (after width-≤3 SP) whose width-3 balance constant is bounded well above `1/3`, strengthening the case that `8/21` (indeed a larger constant) is a robust width-3 lower envelope across multiple algebraic families.

The structural NEW-WALL sub-finding (proven, not merely observed): **the genuine finite-geometry incidence family has no `q`-parameterised width-3 thread**, so the roadmap-§3D/§4 "closed-form-Q-in-`q`" ambition is *structurally blocked*. Width 3 forces a 2-level point-line incidence poset to have `≤ 3` points and `≤ 3` lines (`≤ 6` elements), and forces a subspace-lattice piece to be a rank-2 interval `≅ M_{q+1}` (width `q+1`, hence width 3 only at `q = 2`). The sweep is consequently *finite and exhaustive*, not asymptotic — and it is complete.

| family region | min `Q` (width exactly 3) | vs `8/21` | computability |
|---|---|---|---|
| **genuine point-line incidence** (≤3 pts, ≤3 lines; complete) | **2/5** | `>` (clears by `0.019`) | exhaustive, exact (100%) |
| **genuine linear spaces** (every line ≥2 pts) | **1/2** | `>` | exhaustive, exact |
| subspace lattice `L_n(q)` width-3 instance (`= M_3`) | **1/2** | `>` | closed-form `e=(q+1)!`, `Q=1/2` |
| *boundary probe:* generic graded 3-level (NOT faithful geometry) | 4/11 ≈ 0.3636 | `<` (but `> 1/3`) | exhaustive (92,134), exact |

The `8/21` floor is undercut **only** outside genuine finite geometry, in the generic graded relaxation (`4/11`, still `> 1/3`) — which pinpoints where a Prong-3C analytic target would live (generic graded width-3 posets, not finite geometry).

**§8.2 anti-Cheeger guard does NOT fire.** The lowest `Q` anywhere in the entire sweep (including the generic-graded boundary probe) is `4/11 > 1/3`; no `Q ≤ 1/3` candidate exists. The width-2 textbook gadget `point ‖ (y<z)` touches `Q = 1/3` exactly (the conjecture's satisfied boundary, a theorem, not a violation) — logged as a boundary touch and independently confirmed, per the Prong-2 / Prong-3A handling.

---

## (i) Vision alignment (V1+V2+V3+V4) — verbatim from the ticket

- **V1 (algebraic objects):** *finite-geometry incidence posets are a clean algebraic family parameterised by field-size q (or analogous geometric parameter). Candidates: subspace lattices of F_q^n, incidence posets of PG(2, q) and PG(3, q), Bruhat-order intervals in small finite reflection groups, generalised quadrangle incidence posets, truncated / quotiented subspace lattices restricted to width-3, point-line incidence posets in finite projective planes / affine planes. DISTINCT from skew (Family A) and SP (Family B).*
- **V2 (computable Q):** *Q computable closed-form as a function of q (or the chosen geometric parameter) — Gaussian q-binomial coefficient ratios for subspace-lattice families; explicit incidence counts for projective-plane families. NOT Monte-Carlo, NOT generic DP-only. The methodological-hope distinguisher.*
- **V3 (parameter space):** *parameter is the field-size q and the geometry-type / dimension; sweep across small (q, dim) values; record min Q.*
- **V4 (sharpness-or-pivot signal):** *screening question per mayor + polecat verdict on mg-7009 — does Family D beat 8/21 toward 1/3 at width-exactly-3, and can it produce posets outside the settled SP / width-≤2 classes? If yes (Q < 8/21 anywhere in Family D), 'New territory beyond SP'; if Q < 1/3 anywhere, COUNTEREXAMPLE CANDIDATE (§8.2 mandatory). If Q ≥ 8/21 across the sweep, Family D adds evidence the 8/21 bound holds more broadly than SP — flagging the bound as a CANDIDATE width-3 algebraic floor across multiple families.*

**Which V4 branch fired:** the last one — **`Q ≥ 8/21` across the genuine sweep** (in fact `Q ≥ 2/5`), so Family D *adds evidence the `8/21` bound holds more broadly than SP*, flagging it (and the larger `2/5`) as a candidate width-3 algebraic floor across multiple families. Family D *does* produce posets outside SP and width-≤2 (the triangle incidence poset is `N`-containing, hence non-SP, at `Q = 1/2`; the asymmetric `2`-point/`3`-line argmin at `Q = 2/5` is likewise non-SP), so the "outside the settled classes" half of the screening question is answered **yes** — but those non-SP posets still clear `8/21`. On V2, the closed-form `Q`-in-`q` ambition is partially met (closed-form `M_{q+1}`: `e = (q+1)!`, `Q = 1/2`, a Gaussian-`q`-binomial-flavoured count) but structurally cannot be pushed to a width-3 *sweep* — see §3, the NEW-WALL.

---

## 1. Setup and the `Q` metric

A finite-geometry incidence poset is built from the points / lines / (planes) of a finite geometry, ordered by incidence/containment. Under the uniform distribution on linear extensions,

```
Q(P) = max over incomparable pairs {x,y} of min( Pr[x<y], Pr[y<x] )
     = 1/2 - min over incomparable pairs of |Pr[x<y] - 1/2|.
```

The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3` for every non-chain finite poset; *small* `Q` is the dangerous (counterexample) regime. Reference bars carried forward: `1/3 ≈ 0.3333` (global textbook tight, attained at the gadget `G = point ‖ 2-chain`); `8/21 ≈ 0.3810` (Prong-3A width-3 SP theorem, sharp at `T* = [G⊕G] ‖ point`); `27/70 ≈ 0.3857` (Family-A skew empirical floor, SKEW-ARTIFACT). `2/5 = 0.4`.

**Computability.** Computing the number of linear extensions is `#P`-complete in general (Brightwell–Winkler), but for width-`≤3` posets the order-ideal DP is `O(n^4)` per instance and yields every pairwise `Pr[x<y]`. So `Q` is exact and polynomial-time *per instance* with no algebraic structure required — the algebra's job (roadmap §1) is to make the *parameter sweep* closed-form/asymptotic. The deliverable computes `Q` four independent exact ways and never uses Monte-Carlo.

---

## 2. Candidate-family scoping (the 3 constructions)

Three finite-geometry incidence-poset constructions were scoped; each is assessed for (a) construction, (b) the parameter range producing width-3, (c) closed-form `Q`, (d) sweep suitability.

### D1. Subspace lattice `L_n(q)` (the Gaussian-`q`-binomial family)

- **(a)** Elements = all subspaces of `F_q^n`; order = inclusion. The genuine "algebraic object parameterised by `q`" of the vision.
- **(b)** Width = the largest Gaussian binomial coefficient `[n choose k]_q`. For rank 2 (`n = 2`) this is `[2 choose 1]_q = q+1` (the number of `1`-dimensional subspaces). The script confirms `width(L_2(q)) = q+1` for `q = 2,3,5` and `width(L_3(q)) = q^2+q+1 ≥ 7`. **Width 3 occurs only at `q = 2, n = 2`** — the `5`-element diamond `M_3` (`0 < {x,y,z} < 1`).
- **(c)** The width-3 instance is `M_3 = M_{q+1}|_{q=2}`. Closed-form for the whole rank-2 family `M_{q+1}` (`0 < (q+1)` atoms `< 1`): `e = (q+1)!` (bottom first, top last, atoms freely permuted); every incomparable pair is a pair of atoms, exchanged by an order-automorphism, so `Pr = 1/2` and **`Q(M_{q+1}) = 1/2` for all `q`** — a clean closed form in `q`.
- **(d)** Width 3 at a single point (`q=2`), `Q = 1/2`. Closed-form but *not sweepable at width 3*. Honors V2's Gaussian-`q`-binomial nod; blocked for V3.

### D2. Point-line incidence posets of finite planes (the unit-distance-faithful family)

- **(a)** Points below incident lines in a finite projective/affine plane or a sub-configuration thereof (triangle, near-pencil, polygon). This is the most direct parallel to the unit-distance / Szemerédi–Trotter incidence inspiration.
- **(b)** A 2-level incidence poset has its points forming an antichain and its lines forming an antichain, so `width ≥ max(#points, #lines)`. **Width 3 forces `#points ≤ 3` and `#lines ≤ 3`** — at most `6` elements. (PG(2,q) itself has `q^2+q+1 ≥ 7` points, width `≥ 7`, never width 3.) The complete width-3 family is therefore the finite set of incidence patterns on `≤3` points and `≤3` lines.
- **(c)** Per-instance exact via the width-3 DP; no `q`-closed-form (there is no `q` once the configuration is fixed-size). The triangle, the single-line config, and `M_3`-with-points are all computable.
- **(d)** Genuinely sweepable but the sweep is a *complete finite enumeration* (42 distinct width-3 posets), not an asymptotic family. **Chosen** as the primary sweep (below).

### D3. Higher-incidence / graded truncations (PG(3,q), generalised quadrangles)

- **(a)** Points < lines < planes (PG(3,q)) or restricted incidence of a GQ, truncated to width 3.
- **(b)** Same antichain obstruction per rank: width 3 forces `≤3` per rank, and faithful PG(3,q)/GQ incidence forces every line onto `q+1 ≥ 3` points and vice-versa, so no faithful truncation is width-3 beyond degenerate sub-configurations.
- **(c)/(d)** Per-instance DP only. The *generic graded relaxation* (arbitrary covers, dropping the geometry axioms) is sweepable and is run as a clearly-labeled **boundary probe** — it is not a faithful finite geometry, but it maps where below-`8/21` territory begins.

### Choice rationale

**D2 (point-line incidence) is chosen for the primary sweep**, with D1's closed-form `M_{q+1}` delivered alongside and D3 run as a labeled boundary probe. Rationale against the four selection criteria:

1. **Computability-gate cleanliness (roadmap §4).** D2 is exact width-3 DP at every instance, never Monte-Carlo; D1's chosen-family closed form `M_{q+1}` (`e=(q+1)!`, `Q=1/2`) is delivered for the `q`-parameterised record. The genuine closed-form-in-`q` *sweep* the gate prizes is unattainable at width 3 — this is the NEW-WALL, disclosed, not hidden.
2. **Genuine width-3 instances at multiple parameter values.** D2 supplies 42 distinct width-3 posets (a real, if finite, sweep); D1 supplies one (`M_3`). D2 wins.
3. **Distinctness from SP and skew.** D2 produces *non-SP* posets (the triangle is `N`-containing; the `2`-pt/`3`-line argmin likewise) — genuinely outside Family A (skew) and Family B (SP).
4. **Unit-distance inspiration fidelity.** D2 *is* point-line incidence — the most direct algebraic-program parallel to the cited unit-distance / incidence breakthroughs.

---

## 3. Chosen family's algebraic structure + closed-form `Q` + the structural wall

### 3.1 The closed-form piece (D1, `M_{q+1}`)

The rank-2 subspace lattice of `F_q^2` is `M_{q+1}`: a bottom `0̂`, a top `1̂`, and the `q+1` one-dimensional subspaces (atoms) between, mutually incomparable. A linear extension places `0̂` first and `1̂` last and permutes the `q+1` atoms arbitrarily, so

```
e(M_{q+1}) = (q+1)!  ,   width(M_{q+1}) = q+1.
```

The only incomparable pairs are atom pairs `{aᵢ, aⱼ}`; the transposition `aᵢ ↔ aⱼ` is an order-automorphism, so `Pr[aᵢ < aⱼ] = 1/2` and

```
Q(M_{q+1}) = 1/2   for every prime power q.
```

This is the genuine closed-form-`Q`-in-`q` the vision asks for — but it is pinned at `1/2` (the symmetric, counterexample-irrelevant ceiling) and is width-3 only at `q = 2`. *(Verified in the script for `q ∈ {2,3,4,5,7,8,9}` by the formula and, at `q=2`, against the explicitly enumerated `F_2^2` lattice through all four engines.)*

### 3.2 The structural wall (the NEW-WALL sub-finding, proven)

> **Wall Lemma (no `q`-parameterised width-3 thread).** No infinite family of width-exactly-3 finite-geometry incidence posets exists with a non-trivial parameter `q`.

**Proof.**
*(2-level case.)* In a points-below-lines incidence poset, any two points are incomparable and any two lines are incomparable. Hence the points form an antichain and the lines form an antichain, so `width ≥ max(#points, #lines)`. Width `= 3` therefore forces `#points ≤ 3` and `#lines ≤ 3`: the family is finite (`≤ 6` elements, ≤ 42 distinct width-3 patterns). In particular the full point-line poset of any projective plane `PG(2,q)` has `q^2+q+1 ≥ 7` points and width `≥ 7`.

*(Lattice case.)* In the subspace lattice `L_n(q)`, an interval `[U,W]` with `dim W − dim U = d` is isomorphic to `L_d(q)`. Its width is the largest Gaussian binomial `[d choose ⌊d/2⌋]_q`. For `d = 2` this is `q+1`; for `d ≥ 3` it is `≥ [3 choose 1]_q = q^2+q+1 ≥ 7`. So the only width-`≤3` intervals are rank-`≤2`, and the rank-2 interval is exactly `M_{q+1}`, width `q+1`, width 3 only at `q = 2`. No truncation/quotient of a subspace lattice produces a width-3 piece carrying a free `q`.

Thus the genuine finite-geometry incidence family is, at width 3, a *finite* object — exhaustively enumerable, but with no asymptotic `inf Q` to chase. ∎

This is precisely the roadmap §3D/§4 forecast ("the restriction needed to force width 3 breaks the clean `q`-formula") upgraded from a caveat to a proven structural fact. It is the honest reason the V3 closed-form `q`-sweep cannot be delivered for Family D, and why the sweep below is exhaustive-finite.

---

## 4. Sweep table

All `Q` values are exact `Fraction`s, cross-validated at **every** instance by four independent engines: (M1) primary order-ideal DP; (M2) the AP-0 generic width-3 kernel `Q_via_dp` (n ≤ 12); (M3) the Prong-2 independent-check codebase (minimal-element-removal recursion — the roadmap-§8.2 second codebase, run at *every* instance); (M4) brute-force permutation enumeration (n ≤ 8). A discrepancy at any instance aborts the run; the clean exit certifies agreement.

### 4.1 Subspace-lattice width sweep (the wall, with data)

| `(q,n)` | #subspaces | width | width-3? |
|---|---:|---:|---|
| `F_2^2` | 5 | **3** | **yes — the only instance (`= M_3`)** |
| `F_3^2` | 6 | 4 | no |
| `F_5^2` | 8 | 6 | no |
| `F_2^3` | 16 | 7 | no |
| `F_3^3` | 28 | 13 | no |

Closed-form `M_{q+1}`: `q ∈ {2,…,9}` all give `Q = 1/2`, width `q+1`; width 3 only at `q=2`.

### 4.2 Primary genuine sweep — all width-3 point-line incidence posets

| quantity | value |
|---|---|
| distinct width-3 incidence posets (up to point/line relabelling) | **42** |
| computability fraction (exact, all engines agree) | **42/42 = 100%** (Monte-Carlo never used) |
| **min `Q`** | **`2/5` = 0.400000** |
| argmin count | 2 (e.g. `2` pts / `3` lines: `l0={p0,p1}, l1={p0}`; and its dual `3` pts / `2` lines) |
| # with `Q < 8/21` | **0** |
| # with `Q < 1/3` | **0** |
| # with `Q = 1/2` | 37 |
| genuine linear-space subfamily (every line ≥2 pts): count / min `Q` | 6 / **`1/2`** |

The argmin `2`-pt/`3`-line poset (`p0` on two lines, `p1` on one) has `Pr[p0 < p1] = 3/5`, `Q = 2/5`; it is non-SP and non-skew, exactly the "outside the settled classes" instance the V4 screening question asks for — and it clears `8/21`.

### 4.3 Boundary probe — generic graded 3-level (NOT faithful geometry)

| quantity | value |
|---|---|
| width-3 graded 3-level posets scanned (`--full-graded`) | **92,134** |
| **min `Q`** | **`4/11` ≈ 0.363636** (`< 8/21`, but `> 1/3` by `0.030`) |
| witness | `1` pt `a0`, `3` lines `b0,b1,b2`, `1` plane `c0`; `a0<b0,b1`; `b0,b2<c0` |
| # with `Q < 1/3` | **0** |

The `4/11` witness is *not* a faithful PG(3,q)/GQ incidence (it has a `1`-point "line" and an empty-of-points "line", impossible in a genuine geometry). It is logged to mark the boundary: below-`8/21` `Q` exists in generic graded width-3 posets, **not** in genuine finite geometry — the Prong-3C target.

---

## 5. Verdict

**BROADER-FLOOR-CANDIDATE**, with a proven **NEW-WALL** structural sub-finding.

- **Bounded-null on Family D.** Every genuine width-exactly-3 finite-geometry incidence poset has `Q ≥ 2/5 > 8/21 > 1/3`. Family D hosts no counterexample and clears the Prong-3A SP floor with margin — a *second* family (after width-≤3 SP) confirming a width-3 lower envelope well above `1/3`. This flags `8/21` (and the larger `2/5`) as a candidate width-3 algebraic floor across multiple families, per the V4 last branch.
- **Outside the settled classes, still safe.** Family D produces genuinely non-SP, non-skew width-3 posets (triangle incidence at `Q=1/2`; the `2`-pt/`3`-line argmin at `Q=2/5`), answering the screening question's "can it produce posets outside SP / width-≤2?" with **yes** — and they remain `≥ 2/5`.
- **NEW-WALL (proven).** The genuine family has no `q`-parameterised width-3 thread (Wall Lemma §3.2): width-3 forces `≤3` points/`≤3` lines (2-level) or a rank-2 interval `≅ M_{q+1}` (lattice, width 3 only at `q=2`). The roadmap-§3D closed-form-`Q`-in-`q` *sweep* is structurally impossible at width 3; the sweep is necessarily finite-exhaustive (and is complete). This is the clean diagnosis the §8/Prong-1 "name the wall" discipline asks for.
- **§8.2 guard cleared.** Lowest `Q` anywhere (incl. the 92,134-poset boundary probe) is `4/11 > 1/3`; no `Q ≤ 1/3` candidate; the guard does not fire and no third-codebase halt is triggered. The width-2 textbook gadget touches `Q = 1/3` exactly (satisfied boundary, independently reconfirmed).

This is not COUNTEREXAMPLE-CANDIDATE (no `Q < 1/3`), and not NEW-TERRITORY-BELOW-8/21 *for genuine Family D* (genuine min is `2/5 > 8/21`). The only below-`8/21` value (`4/11`) lives strictly outside faithful finite geometry, in the generic graded relaxation — recorded as the seed for Prong 3C rather than claimed as a Family-D result.

---

## 6. Suggested Prong 3C brief (gated on this verdict)

The genuine finite-geometry incidence family is *settled* at width 3 (bounded-null, `Q ≥ 2/5`, complete enumeration) and *walled* for `q`-sweeps. So Prong 3C should **not** retry finite geometry. The boundary probe localizes the live question precisely:

**Prong 3C (recommended) — generic graded width-3 posets, the `4/11` region.** The below-`8/21` territory found here lives in generic graded 3-level posets (`min Q = 4/11 ≈ 0.3636`, `> 1/3`). This is a *third* width-3 family beating `8/21` toward `1/3` (after the skew `27/70` artifact and now this), and unlike finite geometry it has an *unbounded* parameter (the number of ranks / elements per rank). Brief shape: (a) build the generic-graded enumerator + exact `Q` (reuse this script's `graded3_min_Q` and the four-engine harness); (b) sweep graded width-3 posets to larger size, track `min Q(n)` and its argmin; (c) ask whether the `4/11`-type witnesses descend toward `1/3` or plateau above it — the same descent-vs-plateau question Prong 3A answered for SP. If they descend below, say, `5/14` it becomes a sharper NEW-TERRITORY signal; if they plateau, it is a second bounded-null family above `8/21`. The §8.2 guard rides along: any `Q ≤ 1/3` halts for a fresh third codebase.

*(Parked, lower priority: Bruhat-interval and generalised-quadrangle incidence families were scoped but share the same antichain obstruction to width-3 `q`-sweeps; they would only re-derive the NEW-WALL. Family C (Ehrhart) remains a separately-fileable Prong 3B-gamma per the ticket NON-GOALS, gated on this verdict — now unblocked.)*

---

## Carry-forwards (for the next polecat)

- **Verdict:** Family D (genuine finite-geometry incidence) is a **settled bounded-null** at width 3: `Q ≥ 2/5 > 8/21 > 1/3`, complete 42-poset enumeration + the `M_{q+1}` closed form. No counterexample; clears the SP floor with margin.
- **The wall (reusable fact):** width-3 ⟹ `≤3` points/`≤3` lines (2-level incidence) or rank-2 interval `≅ M_{q+1}` (subspace lattice, width `q+1`). No finite-geometry incidence poset admits a `q`-parameterised width-3 sweep. PG(2,q)/PG(3,q)/GQ incidence posets all have width `≥ q+1 ≥ 7` for `q ≥ 2`, never width 3.
- **Closed form:** `M_{q+1}` (rank-2 subspace lattice of `F_q^2`): `e=(q+1)!`, `width=q+1`, `Q=1/2` for all `q`.
- **The live region (Prong 3C seed):** generic graded width-3 posets reach `Q = 4/11 ≈ 0.3636 ∈ (1/3, 8/21)`; the below-`8/21` territory is here, *not* in faithful finite geometry. Witness: `1` pt `< 3` lines `< 1` plane with covers `a0<b0,b1`, `b0,b2<c0`.
- **Reusable instrument:** [`scripts/onethird_ap2_prong3b_beta_familyD_probe.py`](../scripts/onethird_ap2_prong3b_beta_familyD_probe.py) — finite-geometry enumerators (`subspace_lattice`, `Mk_lattice`, `point_line_poset`, `enumerate_width3_point_line`), the generic-graded probe (`graded3_min_Q`), and the four-engine `verify_instance` harness (primary DP + AP-0 kernel + Prong-2 independent codebase + brute force) with the §8.2 guard wired in. Default ≈ 0.9 s; `--full-graded` ≈ 60 s.
- **Guard discipline:** lowest `Q` swept is `4/11 > 1/3`; the guard distinguishes `Q < 1/3` (HALT, third codebase) from `Q = 1/3` (satisfied boundary, log + independent reconfirm), matching Prong-2/3A.
- **Reference bars:** `1/3` (global tight), `8/21` (width-3 SP theorem), `27/70` (skew artifact), and now `2/5` (genuine finite-geometry incidence floor) and `4/11` (generic-graded width-3 minimum).
