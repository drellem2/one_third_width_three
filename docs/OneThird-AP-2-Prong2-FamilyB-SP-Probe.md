# OneThird AP-2 Prong 2 — Family B (width-3 series-parallel) viability + sweep

*Work item mg-63df. Follow-up to mg-9597 (AP-2 Prong 1, ANALYTIC-PARTIAL Outcome 4) and the algebraic-program roadmap. Date 2026-05-29.*

*Deliverable scripts:*
*`scripts/onethird_ap2_prong2_familyB_sp_probe.py` (enumerator + closed-form Q + three-engine cross-check + sweep + doc-grade output)*
*`scripts/onethird_ap2_prong2_independent_check.py` (separate-codebase reimplementation for the roadmap §8.2 guard).*

---

## 0. Headline

**VERDICT: SKEW-ARTIFACT.** The Family-A floor 27/70 ≈ 0.385714 does **not** extend to Family B (width-≤3 series-parallel posets). Both the full-family minimum and the width-exactly-3 minimum fall strictly below 27/70:

| family restriction | min Q over Family B | float | vs 27/70 |
|---|---|---|---|
| width ≤ 3 (full Family B) | **1/3** | 0.333333 | **<** (= the global 1/3–2/3 tight bound, attained at the width-2 poset `1 ‖ (y<z)`) |
| width **exactly** 3 | **8/21** | 0.380952 | **<** (attained at a stacked-tight-gadget SP poset, stable for all n ≥ 7) |

27/70 is therefore a structural artifact of 3-row **skew shapes**, not a width-3 algebraic-poset floor. (Family A's 14,267-shape sweep never dropped below 27/70; Family B drops below it already at n = 7 for width 3, and at n = 3 for width ≤ 3.)

The roadmap §8.2 anti-Cheeger guard fired (Q ≤ 1/3 surfaced) and was **cleared**: every trigger is Q = 1/3 *exactly* (175 shapes up to n = 12), never Q < 1/3. Q = 1/3 is the textbook tight boundary of the 1/3–2/3 conjecture (the conjecture is *satisfied*, with equality), independently confirmed by exact brute-force and a separate codebase. **No counterexample is claimed and none exists in the swept range.**

---

## (i) Vision alignment (V1–V4)

Verbatim from the ticket's VISION ALIGNMENT block (`docs/OneThird-Algebraic-Program-Vision.md`, the four load-bearing parts):

- **V1 (algebraic objects):** width-3 SP posets are a clean algebraic family — defined by parallel + series composition operations on width-bounded SP-trees. Distinct from the skew-shape Family A.
- **V2 (computable Q):** Q is computable from the SP-tree via either closed-form linear-extension count (multinomial under parallel composition, factor across series composition) or generic DP. The AP-0 kernel `Q_via_dp` is generic to width-3 posets and reusable verbatim.
- **V3 (parameter space):** the SP-tree itself is the parameter — sweep over width-3 SP-trees up to size n. Enumerate, score Q, find argmins.
- **V4 (sharpness-or-pivot signal):** if min Q over Family B is < 27/70 anywhere, then 27/70 is a skew-shape artifact and Family A's floor does NOT extend; the program continues exploring small-Q regions across families. If min Q over Family B is ≥ 27/70 across the swept range, that's a second piece of evidence for 27/70 as a candidate width-3 algebraic-poset floor.

**Which V4 branch fired:** the first one. min Q over Family B is < 27/70 (both at width ≤ 3 and at width exactly 3) ⇒ 27/70 is a skew-shape artifact.

---

## (ii) Algorithm

### The Q metric

For a finite poset `P` that is not a chain, under the uniform distribution on linear extensions,
```
Q(P) = max over incomparable pairs {x,y} of  min( Pr[x<y], Pr[y<x] )
     = 1/2 - min over incomparable pairs of |Pr[x<y] - 1/2|.
```
The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3` for every non-chain `P`. *Small* Q is the dangerous regime (every incomparable pair unbalanced); `Q < 1/3` would be a counterexample. We sweep Family B for the minimum Q and its argmin.

### Enumerator (with canonical-form dedup spec)

A **labeled SP node** is one of: `('leaf', id)` (a single element); `('S', children)` (ordinal sum / **series**, `children[0]` lowest — every pair across the join is comparable); `('P', children)` (disjoint union / **parallel** — every cross-pair incomparable). Widths: `leaf = 1`, `series = max child width`, `parallel = sum of child widths`. Family B = SP posets of **width ≤ 3** (so parallel composition is gated by `width(P)+width(Q) ≤ 3`; series preserves width).

**Canonical form (dedup spec).** The series-parallel decomposition tree of an SP poset is unique up to (a) associativity of each operation and (b) reordering of parallel children (parallel = commutative; series order is fixed by the poset). So `canon(node)`:
1. flatten same-type nesting (`S(S(a,b),c) → S(a,b,c)`, `P(P(a,b),c) → P(a,b,c)`);
2. **sort** the children of every parallel node (canonical multiset key);
3. **preserve** the order of series children (ordinal-sum order is a genuine poset feature; `P+Q` and `Q+P` are distinct posets — order duals — and are counted separately, which is correct since they are different unlabeled posets).

This yields exactly one representative per SP poset. Enumeration is by binary series/parallel composition of smaller canonical trees followed by `canon` + set dedup; binary composition + flattening reaches every width-≤3 SP poset, and the width gate (`≤ 3` at every step) keeps the family bounded.

A 3-element antichain is `P(leaf,leaf,leaf)`; the canonical tight poset `1‖(y<z)` is `P(leaf, S(leaf,leaf))`.

### Closed-form Q on SP-trees

The incomparable pairs of an SP poset are exactly the pairs whose lowest common ancestor in the SP-tree is a **parallel** node (pairs under a series LCA are comparable, Pr ∈ {0,1}, excluded). For a pair `(x ∈ child Ci, y ∈ child Cj)` of a parallel node, the relative order of `x` and `y` depends **only** on `Ci` and `Cj` (inserting elements from any other component, or from anywhere above/outside this parallel node, never changes whether `x` precedes `y`). Hence
```
Pr[x<y] = Σ_{a,b} R_Ci(x)[a] · R_Cj(y)[b] · F(a,b,|Ci|,|Cj|),
```
where:

- **`R_T(e)`** = the rank distribution of element `e` within a uniform linear extension of subtree `T`, computed by structural recursion:
  - *leaf:* `{1: 1}`.
  - *series:* deterministic shift — `e` in the s-th series block lands at `offset_s + (local rank)`.
  - *parallel:* `e` at local rank `a` in its size-`m` component lands at global rank `a+k`, where `k` (number of other-component elements placed before `e`) is **negative-hypergeometric**: `Pr[k] = C(a-1+k, k)·C(m-a+o-k, o-k) / C(m+o, o)` with `o` = the other-element count.
- **`F(a,b,m,n)`** = `Pr[ a-th element of a size-m group precedes the b-th element of a size-n group ]` in a uniform merge. The a-th of group 1 precedes the b-th of group 2 iff fewer than `b` group-2 elements precede it, so
  `F(a,b,m,n) = ( Σ_{j=0}^{b-1} C(a-1+j, j)·C(m-a+n-j, n-j) ) / C(m+n, n)`.

Linear-extension counts are themselves closed-form (`LE(P+Q)=LE(P)·LE(Q)`; `LE(P‖Q)=LE(P)·LE(Q)·C(|P|+|Q|,|P|)`); the construction above is the corresponding closed-form for the *pairwise* probabilities. All arithmetic is exact (`fractions.Fraction`). **Closed-form-applicability fraction on SP-trees: 100% by construction** (every incomparable pair is resolved by the recursion — no fall-through to the generic DP), in explicit contrast with Family A, where the Naruse closed form only applies when an augmented poset stays a skew shape.

### Three independent engines (cross-check + guard)

1. `Q_closed_sp` — the SP-tree structural recursion above.
2. `Q_via_dp` — generic order-ideal DP over linear-extension counts (family-agnostic; mirrors the AP-0 kernel `scripts/onethird_ap0_familyA_skew_probe.py` `Q_via_dp` — reused algorithm, applied to the SP relation).
3. `Q_via_brute` — brute force over all permutations (gold-standard).

**Cross-check result:** closed-form == DP on **all 32,413** width-≤3 SP shapes up to n = 11, and closed-form == brute on all shapes up to n = 8 — **0 mismatches**. Sanity anchors (three-engine agreement):

| poset | Q | note |
|---|---|---|
| `a‖b‖c` (n=3 antichain) | 1/2 | ✓ ticket sanity |
| `a + (b‖c‖d)` (n=4) | 1/2 | ✓ within-antichain pairs Pr 1/2 |
| `(a‖b) + (c‖d‖e)` (n=5) | 1/2 | ✓ = max of within-component Q |
| `1‖(y<z)` (n=3, width 2) | 1/3 | ✓ textbook tight bound |

---

## (iii) Sweep table

Sweep of every width-≤3 SP poset, n ∈ [3, 12], canonical-form deduplicated. `#SP(w≤3)` = count of distinct SP posets; `#w==3` = those of width exactly 3; `minQ` columns are exact rationals (floats shown); argmin is for the width-exactly-3 column. Every shape with n ≤ 8 is additionally brute-force confirmed inside the sweep.

| n | #SP (w≤3) | #w==3 | min Q (w≤3) | min Q (w==3) | argmin (w==3) |
|---:|---:|---:|---|---|---|
| 3 | 5 | 1 | 1/3 (0.333333) | 1/2 (0.500000) | `(* ‖ * ‖ *)` |
| 4 | 14 | 5 | 1/3 | 1/2 (0.500000) | `(((*+*)‖*)‖*)` |
| 5 | 40 | 21 | 1/3 | 7/15 (0.466667) | `((((*+*)‖*)+*)‖*)` |
| 6 | 116 | 75 | 1/3 | 19/45 (0.422222) | `((((*+*)‖*)+*)‖(*+*))` |
| 7 | 331 | 244 | 1/3 | **8/21 (0.380952)** | `((((*+*)‖*)+((*+*)‖*))‖*)` |
| 8 | 938 | 752 | 1/3 | 8/21 | `(((((*+*)‖*)+((*+*)‖*))‖*)+*)` |
| 9 | 2,644 | 2,248 | 1/3 | 8/21 | `…+*+*` |
| 10 | 7,435 | 6,590 | 1/3 | 8/21 | `…+((*+*)‖*)` |
| 11 | 20,890 | 19,089 | 1/3 | 8/21 | `…+((*+*)‖*)+*` |
| 12 | 58,693 | 54,852 | 1/3 | 8/21 | `…+((*+*)‖*)+*+*` |

**Global minima:** min Q over width ≤ 3 = **1/3** (argmin `((*+*)‖*)` = `1‖(y<z)`, width 2); min Q over width exactly 3 = **8/21** (argmin at n=7 below).

**Closed-form-applicability fraction: 100% at every n** (SP-trees by construction — noted explicitly per the ticket).

### The width-3 argmin, decoded

The stable width-3 minimiser (n = 7, Q = 8/21) is
```
T* = [ (a<b ‖ c)  ⊕  (d<e ‖ f) ]  ‖  g
```
i.e. **two copies of the canonical tight gadget `(2-chain ‖ point)` stacked in series, then put in parallel with a single point `g`** to lift the width from 2 to 3. Each copy of `(2-chain ‖ point)` is the Q = 1/3 width-2 extremal poset; stacking two in series and adding the parallel point is what the search settles on. The value 8/21 ≈ 0.38095 is stable across **six consecutive sizes (n = 7…12)**; larger n simply append series points/gadgets to `T*` without lowering Q. The SP-poset count grows exponentially (58,693 at n = 12), so n = 12 was the budget-feasible exact-rational cap on a laptop; the stability of 8/21 over n = 7…12 is strong evidence it is the width-3 SP floor.

---

## §8.2 guard (anti-Cheeger) — fired and cleared

Q ≤ 1/3 surfaced at **175 shapes** up to n = 12 — **all exactly Q = 1/3, none below**. Per roadmap §8.2 this was handled with full rigor before any claim:

1. **Smallest witness** `1‖(y<z)` (n=3): Pr ranges are exactly `{1/3, 2/3}` over its 3 linear extensions — the textbook tight configuration of the 1/3–2/3 conjecture.
2. **Exact brute-force** (engine 3, permutation enumeration) confirms Q = 1/3 *exactly* on the witness.
3. **Independent reimplementation** in a *separate codebase* with **no shared code** — `scripts/onethird_ap2_prong2_independent_check.py`, which counts linear extensions by a minimal-element-removal recursion (structurally unrelated to the bitmask DP, the SP recursion, and the itertools brute force) — independently reproduces Q = 1/3 for `1‖(y<z)` and finds no Q < 1/3 in its own small exhaustive width-≤3 SP scan.

`Q = 1/3` is the conjecture's *satisfied* boundary, not a violation; only `Q < 1/3` is a counterexample, and none is found. The sweep's complete absence of `Q < 1/3` across 32,413 cross-checked shapes is consistent with the 1/3–2/3 conjecture holding on Family B. **No counterexample is claimed.**

---

## (iv) Verdict

**SKEW-ARTIFACT.** min Q over Family B is strictly below the Family-A floor 27/70:

- width ≤ 3: min Q = **1/3** < 27/70 — and this 1/3 is the global 1/3–2/3 tight bound, reachable inside SP already at the width-2 poset `1‖(y<z)`.
- width exactly 3 (the apples-to-apples comparison with Family A's 3-row shapes): min Q = **8/21 ≈ 0.38095** < 27/70 ≈ 0.38571.

Either way, the inequality is strict: 27/70 is **specific to the 3-row skew-shape structure** and does **not** generalise to width-3 algebraic posets. Family A's triply-confirmed 27/70 floor (AP-0/1a/1b′, at the n=8 shape (4,4,2)/(2,0,0)) reflects the dominance-order geometry of skew cells, which cannot realise either the width-2 tight gadget (→ 1/3) or the stacked-gadget width-3 minimiser (→ 8/21).

This is the V4 "SKEW-ARTIFACT" branch: the program should **continue exploring small-Q regions across families**, and should *not* treat 27/70 as a candidate universal floor.

---

## (v) Suggested Prong 3 brief (gated on the SKEW-ARTIFACT verdict)

Because the verdict is SKEW-ARTIFACT, Prong 3 is *not* "second analytic confirmation of 27/70" (that branch is closed). Two complementary, polecat-sized directions:

**Prong 3A — analytic width-3 SP floor (close out Family B).** Prove the empirical width-exactly-3 SP floor `min Q = 8/21` analytically. The minimiser is fully explicit (`[(2-chain‖pt) ⊕ (2-chain‖pt)] ‖ pt`) and the SP closed form is a clean series-convolution / negative-hypergeometric recursion, so a lower-bound argument `Q(SP, width 3) ≥ 8/21` looks tractable via induction on the SP-tree: (a) series composition takes `max` of child Q-values; (b) parallel composition's cross-pairs are governed by the `F(a,b,m,n)` merge formula, whose most-balanced cross-pair is bounded below. This would upgrade "8/21 empirically stable over n=7…12" to a theorem, and would also re-derive the width-2 SP floor = 1/3 as a corollary. *Non-goal carried forward: still empirical-first; no Cheeger.*

**Prong 3B — redirect the counterexample hunt to OPEN families.** Family B cannot host a counterexample (no Q < 1/3 anywhere; the 1/3–2/3 conjecture is not open on series-parallel posets). The program's actual counterexample target must be a width-3 family where the conjecture is **open** — i.e. *not* SP, *not* width-≤2. Candidate next family from the roadmap shortlist: **Family C (order-polytope / Ehrhart volume)** or **Family D (finite-geometry incidence)**, scored against the new, lower reference bars established here (1/3 global, 8/21 at width 3) rather than 27/70. The key screening question for any new family: *does it beat 8/21 toward 1/3 at width exactly 3, and can it produce posets outside the SP / width-2 classes where the conjecture is settled?*

Recommended ordering: **3A first** (cheap, closes Family B with a theorem and a reusable SP lower-bound lemma), then **3B** (re-points the search). Both inherit the three-engine + §8.2-guard discipline used here.

---

## Carry-forwards (for the next polecat)

- **Family A floor 27/70** at n=8 (4,4,2)/(2,0,0) — *now demoted from "candidate floor" to "skew-shape artifact."*
- **Family B floors (new):** 1/3 at width ≤ 3 (`1‖(y<z)`, n=3); **8/21** at width exactly 3 (`[(2-chain‖pt)⊕(2-chain‖pt)]‖pt`, n=7), stable n=7…12.
- **Reusable instrument:** `scripts/onethird_ap2_prong2_familyB_sp_probe.py` — SP enumerator (canonical dedup), exact closed-form SP Q (100% applicable), and a three-engine cross-check validated on 32,413 shapes.
- **Guard discipline:** §8.2 fired on Q=1/3 and was cleared by exact brute + separate-codebase reimplementation; the canonical Q=1/3 witness is the 1/3–2/3 tight bound, not a counterexample.
- **The §5 Missing Lemma (Family A) stays parked** per mg-9597; no Family A re-attempt here.
