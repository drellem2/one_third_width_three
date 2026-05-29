# OneThird — AP-2 Prong 3G-α: exhaustive ORDER-iso width-3 minimum `Q` on the NON-self-dual arena at `n = 10…13` — does self-duality trap the floor at `6/17`?

*Work item **mg-5406**. Follow-up to mg-7237 (Prong 3F-β), which returned **VERDICT-A** on the **self-dual** width-3 arena: `6/17` holds exhaustively across `71 512` σ-iso classes through `n = 13` (matched at even `n = 10, 12`; never beaten; new off-ladder odd-`n` minimum `134/375 ≈ 0.357333` at `n = 11, 13`). 3F-β's σ-iso reduction was made tractable by the σ-orbit machinery of mg-7ee8. This Prong 3G-α **drops self-duality** and asks the load-bearing question: is self-duality **trapping** the floor at `6/17`, or is `6/17` a genuine structural extremal across the **full** width-3 arena? Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3F-beta-SelfDual-n11-13-Empirical.md`](OneThird-AP-2-Prong3F-beta-SelfDual-n11-13-Empirical.md) (VERDICT-A + `134/375` odd-`n` family + σ-iso reduction protocol + the five-engine harness reused here verbatim); [`OneThird-AP-2-Prong3E-alpha-SelfDualWidth3-FloorBound.md`](OneThird-AP-2-Prong3E-alpha-SelfDualWidth3-FloorBound.md) (σ-orbit machinery + Lemma W + the missing analytic input named); [`OneThird-AP-2-Prong3D-alpha-DescentRay.md`](OneThird-AP-2-Prong3D-alpha-DescentRay.md) (closed-form obstruction + self-dual subspace finding); [`OneThird-AP-2-Prong3C-Width3-FloorBound.md`](OneThird-AP-2-Prong3C-Width3-FloorBound.md) (REFUTATION + descent ladder + `6/17` witness); [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the analytic `8/21` theorem; Lemma-B "series = max" template); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§4,6,8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust.py`](../scripts/onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust.py) — the **full width-3 enumerator** (canonical-augmentation by maximal element, iso-reduced by **order**-isomorphism only), the exact order-canonical form, the self-dual classifier `order-canon(P) = order-canon(Pᵒᵖ)`, the fast all-pairs balance engine (M1), and the five-engine `verify_C` cross-check harness (M1 placed-set DP / M2 AP-0 `Q_via_dp` / M3 Prong-2 `IndPoset` removal recursion / M4 brute permutations / MC Ehrhart order-polynomial), all imported **verbatim** from the Prong-3F-β module. Pure stdlib.*

---

## 0. Headline

**OUTCOME-C with PARTIAL OUTCOME-A — `6/17` is a genuine width-3 floor; self-duality is NOT trapping it.** Over the **exhaustive** order-iso-reduced **full** width-3 arena, the minimum `Q` stays `≥ 6/17` at every `n` reached, and the `6/17` value itself is reached by **non-self-dual** posets from `n = 11` onward — it is *not* an artifact of the self-dual restriction. Compute exhaustion at the `n = 11 → 12` boundary (full width-3 class count grows ≈ `7.5×` per level: `3 168 869` at `n = 11`, `≈ 2·10⁷` at `n = 12`) caps the exhaustive sweep; `n = 12, 13` remain as a named compute wall, **not** a refutation.

| `n` | width-3 classes (total) | self-dual | **non-self-dual** | min `Q` (ALL) | argmin self-dual? | **min `Q` (non-self-dual)** | vs `6/17` |
|----:|------------------------:|----------:|------------------:|:--------------|:------------------|:----------------------------|:----------|
|  5 |        29 |    7 |        22 | `4/11`   | yes | `7/15` (`k=5/2`)  | `>` |
|  6 |       170 |   18 |       152 | `4/11`   | **no** | `4/11` (`k=11`) | `>` |
|  7 |     1 060 |   60 |     1 000 | `14/39`  | yes | `4/11` (`k=11`)   | `>` |
|  8 |     7 079 |  177 |     6 902 | `14/39`  | **no** | `14/39` (`k=13`) | `>` |
|  9 |    50 797 |  525 |    50 272 | `14/39`  | **no** | `14/39` (`k=13`) | `>` |
| **10** |  **389 497** | **1 685** | **387 812** | **`6/17`** | **yes** | **`14/39`** (`k=13`) | **`>`** |
| **11** | **3 168 869** | **4 811** | **3 164 058** | **`6/17`** | **no** | **`6/17`** (`k=17`) | **`=`** |

`6/17 ≈ 0.352941` is the whole-sweep minimum and is **never beaten** by any width-3 poset, self-dual or not, at any `n ≤ 11`. At `n = 11` it is **matched** by non-self-dual posets (the overall `n = 11` argmin is itself **non-self-dual**), not beaten. The §8.2 anti-Cheeger guard fires on **every** one of the `≈ 3.6·10⁶` width-3 iso-classes through `n = 11`; the lowest `Q` anywhere is `6/17 > 1/3`, so the guard never trips and **no sixth codebase is triggered**.

Three structural facts answer the load-bearing question:

1. **At `n = 10` the `6/17` floor is reached ONLY self-dually.** Exhaustively over all `387 812` non-self-dual width-3 classes at `n = 10`, the minimum is `14/39 ≈ 0.358974` — strictly above `6/17`. The `6/17` value is attained at `n = 10` by exactly the self-dual Prong-3C witness (`e = 187`, recovered as a VALIDATION check). So *at its minimal `n`*, the `6/17` extremal is forced self-dual.

2. **But self-duality is NOT trapping the floor — `6/17` is reachable non-self-dually from `n = 11`.** Adjoining a single **global top** (or a single global bottom) to the `n = 10` self-dual `6/17` witness yields a width-3 poset on `11` elements that is **non-self-dual** (one extreme element with no dual mirror) yet has `Q = 6/17` **exactly**: a global maximum is forced last in every linear extension, so `e` is unchanged and every pairwise balance among the original `10` elements is preserved (the order-polytope analogue of Prong-3A's Lemma-B "series = max"; cf. the Q-preserving global-top/bottom σ-pair adjunction that carries `6/17` from `n = 10` to `n = 12` on the self-dual side). Hence `min Q(non-self-dual)` *drops to `6/17`* at `n = 11` but **never below**. The `n = 10`-only self-duality of the `6/17` argmin is a **parity/room artifact** (`n = 10` has no spare element for a free extreme), not a structural trap.

3. **The same "+1 `n` breaks self-duality at constant `Q`" pattern holds for every rung.** Each descent-ladder value first appears self-dually at its minimal `n`, then non-self-dually one step later: `4/11` self-dual at `n = 5` → non-self-dual at `n = 6`; `14/39` self-dual at `n = 7` → non-self-dual at `n = 8`; `6/17` self-dual at `n = 10` → non-self-dual at `n = 11`. The non-self-dual arena therefore **reproduces** the self-dual minima with a one-step `n`-lag and **never undercuts** them.

**Net:** the corridor stays **`(1/3, 6/17]`** across the *full* width-3 arena (self-dual **and** non-self-dual) through every `n` exhaustively reached. Self-duality is a **convenience** (it pins the extremal at the smallest `n`), not the **cause** of the `6/17` floor. This strengthens the empirical case that the open research-grade question is "can we **prove** `Q ≥ 6/17` for all width-3" (the Prong-1 / Prong-3E-α missing-lemma direction).

---

## 1. Vision alignment (verbatim)

> **V1 (algebraic objects):** width-3 posets at `n = 10..13`, iso-reduced by ORDER-isomorphism only (no σ structure available — that is the methodological distinction from Prong 3F-beta). The arena is exactly the complement of mg-7237's σ-iso self-dual arena (modulo iso class boundaries).
>
> **V2 (computable Q):** five-engine harness from Prong 3F-beta (M1 placed-set DP, M2 AP-0 Q_via_dp, M3 IndPoset minimal-element-removal, M4 brute permutation, MC Ehrhart leading coefficient) reusable verbatim. Closed-form rational throughout.
>
> **V3 (parameter space):** combinatorial type of width-3 poset, iso-reduced order-iso. Polynomial-in-n enumeration via orderly-generation or canonical-augmentation.
>
> **V4 (sharpness-or-pivot signal):**
> - **OUTCOME-A:** min Q over non-self-dual width-3 at n=10..13 stays >= 6/17 — STRENGTHENS the 6/17 floor empirically across the FULL width-3 arena; self-duality NOT trapping the floor; 6/17 is a genuine structural extremal across width-3 through n=13.
> - **OUTCOME-B:** min Q < 6/17 at some non-self-dual width-3 P, n in {10..13} — REFUTES 6/17 as width-3 floor; self-duality WAS trapping; narrows corridor further; possibly opens a new descent ladder family.
> - **OUTCOME-C:** compute exhaustion before reaching n=13 — report partial (n=10 or n=11 or n=12), name compute breakpoint.
> - **WALL:** orderly-generation / iso-reduction blockage at some n — name fifth proven wall and report.

**Realised:** V1 — the **entire** width-3 arena (self-dual and non-self-dual together) is enumerated, iso-reduced by **order**-isomorphism only; the self-dual sub-arena is re-identified inside it via `order-canon(P) = order-canon(Pᵒᵖ)`, so the non-self-dual arena is exactly the complement (and the two halves' counts are reported separately at every `n`). V2 — every reported `Q` is an exact `Fraction`; both argmins at every `n` (overall and non-self-dual) are cross-validated through **all five** engines `M1 = M2 = M3 = M4 = MC`, and the fast primary engine M1 is validated against the full harness on **all classes through `n = 8`** and on the argmins + an ≈ 80-class deterministic sample at `n ≥ 9`. V3 — canonical-augmentation by maximal element (below), iso-reduced by an exact order-canonical form. V4 — **OUTCOME-C with partial OUTCOME-A** (floor `≥ 6/17` confirmed exhaustively through the largest `n` reached; `6/17` reached non-self-dually from `n = 11`; compute wall at `n = 11 → 12`).

---

## 2. The enumerator (V3) — canonical-augmentation by maximal element, order-iso reduced

### 2.1 Why generate-all-then-filter is the *only* route here (σ-direct generation is unavailable)

3F-β could generate self-dual posets **directly** (peeling extreme σ-orbits) because self-duality supplies the σ-orbit move. On the non-self-dual arena there is **no σ structure** to exploit — that is the methodological distinction the ticket names. So we must enumerate the **full** width-3 arena and split it. Labelled width-3 posets are hopeless (`> 6·10⁵` at `n = 8`), so the enumeration is **iso-reduced as it is generated**.

### 2.2 The augmentation move (move M)

Every finite poset on `n` elements is obtained from a poset on `n − 1` elements by **removing a maximal element**; removing an element never increases width, so every width-`≤ 3` poset is reachable through a chain of width-`≤ 3` posets under the inverse move:

- **(move M)** adjoin one new **global-maximal** element `x`, whose strict down-set is **any order ideal `D`** (down-closed subset) of the current poset.

Because `D` is down-closed and `x` is maximal, the augmented relation is **already transitively closed** — no closure pass is needed. We prune `width(P) > 3` immediately (Dilworth = `n − (max bipartite matching on the strict-order graph)`, Hopcroft-Karp-style augmenting-path matcher). This reaches **every** width-`≤ 3` poset, exactly once per order-iso class after the dedup below.

### 2.3 Order-isomorphism canonical form + the self-dual classifier

Iso-reduction is by **order**-isomorphism (not σ-isomorphism — there is no σ). We reuse 3F-β's `canonical_form` with a **trivial σ = identity**: with `σ = id` the σ-colour `col[σ(v)] = col[v]` is redundant and the encoded σ-component is constant, so `canonical_form` reduces **exactly** to the order-isomorphism canonical form. (Verified on small cases: `V` (`0<1, 0<2`) vs `Λ` (`0<2, 1<2`) are distinguished; antichains and chains are self-dual; `V ≅ dual(Λ)`.) The canonical key is the lex-min adjacency encoding under colour-refinement + individualization (target-cell branching). Classes are de-duplicated by **set membership** on this exact key as they are generated — no pairwise iso tests.

A poset `P` is **self-dual** iff `P` is order-isomorphic to its order dual `Pᵒᵖ` (relation transposed). We test this **exactly** by

```
is_self_dual(P)  ⇔  order_canon(P) == order_canon(Pᵒᵖ).
```

The self-dual width-3 classes recovered this way are a strict sub-arena; the **non-self-dual** classes are the complement, and `min Q` over them is the deliverable. (Cross-program check: the overall minima recovered here — `6/17` at `n = 10`, and the `134/375` odd-`n` value once `n = 11` is reached — must match mg-7237's self-dual minima, since those argmins *are* self-dual and so appear in this arena.)

### 2.4 The five-engine harness (V2 / roadmap §4 gate), imported verbatim

`Q` is reported only on exact-rational agreement of **M1** order-ideal placed-set DP (primary, the fast all-pairs `fast_Q` with internal `e`- and before-sum self-checks, run on **every** class) / **M2** AP-0 kernel `Q_via_dp` / **M3** Prong-2 `IndPoset` minimal-element-removal recursion / **M4** brute-force linear extensions (own path, `e ≤ cap`) / **MC** Family-C Ehrhart order-polynomial. Monte-Carlo is **never** a source of truth (non-goal §8.5). Cross-engine disagreement **HALTS** as P0. Both argmins at every `n` get the full `M1 = M2 = M3 = M4 = MC` cross-check.

### 2.5 §8.2 anti-Cheeger guard (INHERITED STRICT)

`guard_check` fires on **every** iso-class. A `Q ≤ 1/3` candidate **HALTS immediately** with the mandated message ("`Q ≤ 1/3 candidate at width-3 poset T … halting per §8.2 STRICT — fresh sixth codebase required`") and is **not** written up as a counterexample; M1+M2+M3+M4+MC are all used, and a fresh **sixth** codebase (Stanley-Reisner / AG-dimension / matrix-permanent / SAT-model-count / analytic Euler-product) is reserved for any such candidate. Across the whole sweep the lowest `Q` is `6/17 > 1/3`, so the guard never trips.

---

## 3. Per-`n` results

Validation: the enumerator recovers the descent-ladder minima exactly — `n = 5 → 4/11`, `n = 7 → 14/39`, `n = 10 → 6/17` (all asserted as VALIDATION PASS). The width-3 hard filter rejects the `1/3` textbook gadget (point ∥ 2-chain, width 2). Class counts (width-3, total): `1, 5, 29, 170, 1 060, 7 079, 50 797, 389 497` at `n = 3…10` (ratio ≈ `6.5–7.7×`).

**Overall minimum vs non-self-dual minimum, `n = 3…10` (EXHAUSTIVE):**

| `n` | width-3 classes | self-dual / non-self-dual | min `Q` (ALL) | argmin self-dual? | min `Q` (non-self-dual) | engines |
|----:|----------------:|:--------------------------|:--------------|:------------------|:------------------------|:--------|
|  4 |        5 |  1 / 4    | `1/2`   | yes | `1/2`   | `M1=M2=M3=M4=MC` (all) |
|  5 |       29 |  7 / 22   | `4/11`  | yes | `7/15`  | `M1=M2=M3=M4=MC` (all) |
|  6 |      170 | 18 / 152  | `4/11`  | **no** | `4/11`  | `M1=M2=M3=M4=MC` (all) |
|  7 |    1 060 | 60 / 1 000| `14/39` | yes | `4/11`  | `M1=M2=M3=M4=MC` (all) |
|  8 |    7 079 | 177 / 6 902| `14/39`| **no** | `14/39` | `M1=M2=M3=M4=MC` (all) |
|  9 |   50 797 | 525 / 50 272| `14/39`| **no** | `14/39` | M1+guard all; full-5 on argmins+sample |
| 10 |  389 497 | 1 685 / 387 812| `6/17`| yes | `14/39` | M1+guard all; full-5 on argmins+sample |
| 11 | 3 168 869 | 4 811 / 3 164 058| `6/17`| **no** | `6/17` | M1+guard all `3 168 869`; full-5 on argmins+sample |

(Generation `n = 0…11`: `828 s`; per-`n` analysis `n = 11`: `1 192 s` — M1 fast all-pairs + guard + `is_self_dual` on all `3 168 869` classes, five-engine cross-check on both argmins + an 83-class deterministic sample. Laptop, pure stdlib.)

**Argmin fingerprints (load-bearing witnesses):**

- `n = 10` overall argmin: `Q = 6/17`, `e = 187`, **self-dual** = `True` — this is exactly the Prong-3C `6/17` witness (VALIDATION PASS).
- `n = 10` non-self-dual argmin: `Q = 14/39`, `e = 117`, binding pair Pr `= 25/39`, levels `[2,2,2,1,2,1]` — strictly above `6/17`.
- `n = 11` overall **and** non-self-dual argmin (they coincide): `Q = 6/17`, `e = 187`, **self-dual = `False`**, binding pair `(2,5)` Pr `= 11/17`, levels `[2,2,2,1,2,1,1]` — this is precisely the `n = 10` `6/17` witness with one Q-preserving extreme element adjoined (`e` unchanged at `187`, binding Pr unchanged at `11/17`), exhaustively confirmed to be the global non-self-dual minimum over all `3 164 058` non-self-dual classes.
- `n = 8, 9` overall argmins are **non-self-dual** at `Q = 14/39` (so the `14/39` rung is *not* self-dual-exclusive — it appears non-self-dually one step after its `n = 7` self-dual debut).

**The `n = 11 → 12` compute boundary (the OUTCOME-C wall).** `n = 11` was completed **exhaustively** (`3 168 869` classes; min non-self-dual `Q = 6/17`, matched not beaten). The full width-3 class count is `≈ 2·10⁷` at `n = 12` and `≈ 1.6·10⁸` at `n = 13` (ratio ≈ `7.5×`/level); generation + order-canon dedup + per-class `is_self_dual` (two canonical forms each) at `n = 12, 13` exceed the laptop polecat budget — this is the named compute breakpoint. The decisive structural fact behind the `n = 11` minimum is independently five-engine-verified by direct construction: adjoining a single global top (or bottom) to the `n = 10` self-dual `6/17` witness gives a **non-self-dual** width-3 poset on `11` elements with `Q = 6/17` **exactly** (`§0` fact 2) — and the exhaustive sweep confirms nothing in the `3.16·10⁶` non-self-dual classes beats it.

---

## 4. Verdict

**OUTCOME-C (compute exhaustion at the `n = 11 → 12` boundary) carrying a PARTIAL OUTCOME-A.**

- **Partial OUTCOME-A (the substantive content).** Over the **exhaustive** order-iso-reduced full width-3 arena, `min Q` (over **all** width-3 posets, and in particular over the **non-self-dual** ones) stays `≥ 6/17` at **every `n` reached** — `n ≤ 11` **exhaustively** (`n = 10`: min non-self-dual `= 14/39 > 6/17`; `n = 11`: min non-self-dual `= 6/17`, confirmed both by the exhaustive `3 168 869`-class sweep and by the direct top/bottom-adjunction witness). **Self-duality is NOT trapping the floor:** `6/17` is reached by non-self-dual width-3 posets from `n = 11` onward (the `n = 11` overall argmin is itself non-self-dual), so it is a genuine structural extremal of the full width-3 class, not an artifact of the self-dual restriction. The `n = 10`-only self-duality of the `6/17` argmin is a parity/room phenomenon (the minimal `n` for `6/17` has no spare element for a Q-preserving free extreme), shared by every ladder rung (`4/11`, `14/39`, `6/17` each go non-self-dual exactly one `n`-step after their self-dual debut).

- **Why not full OUTCOME-A.** Full OUTCOME-A requires exhaustive confirmation through `n = 13`. The full width-3 arena (no σ-iso reduction available) grows ≈ `7.5×` per level — `3 168 869` classes at `n = 11` (reached, `≈ 33 min` end-to-end), `≈ 2·10⁷` at `n = 12`, `≈ 1.6·10⁸` at `n = 13` — so `n = 12, 13` exceed the laptop polecat compute budget. This is a **compute wall**, **not** an OUTCOME-B refutation: nothing below `6/17` was found anywhere through `n = 11`, and the guard never tripped.

- **Not OUTCOME-B.** No `Q < 6/17` width-3 poset (self-dual or not) exists at any `n ≤ 11` — verified exhaustively over the entire width-3 arena through `n = 11` (`3 168 869` classes at `n = 11` alone). The §8.2 guard cleared on every class.

- **Not a WALL (in the enumerator sense).** The canonical-augmentation enumerator + order-canonical iso-reduction is correct and complete (validated against the three known minima and against 3F-β's self-dual recovery); the only blockage is raw compute volume at `n ≥ 12`, which is the OUTCOME-C breakpoint, not a structural/methodological wall.

**Corridor:** `(1/3, 6/17]` holds across the **full** width-3 arena (self-dual and non-self-dual) through every `n` exhaustively reached.

---

## 5. Suggested Prong 3H (gated on this verdict)

This verdict is OUTCOME-A-flavoured (floor `≥ 6/17` strengthened across the full width-3 arena; self-duality not trapping) but truncated to OUTCOME-C by compute, so **3H-α** is the indicated next prong:

- **3H-α (structural-review consolidation — RECOMMENDED).** With the corridor `(1/3, 6/17]` now empirically established across the **full** width-3 arena (self-dual **and** non-self-dual) exhaustively through `n = 10`–`11`, and `6/17` shown to be a genuine structural extremal (reached non-self-dually, not a self-dual artifact), the program's natural next phase is **write-up + an analytic-floor-theorem attempt**. The single clean structural lemma the empirics now isolate is the **"+1 `n` Q-preserving extreme adjunction"** (global top/bottom preserves `e` and all balances; the order-polytope analogue of Prong-3A Lemma-B "series = max"), which explains the one-step `n`-lag and reduces the floor question to its self-dual core. The two named research-grade missing inputs remain the analytic targets: the **forced-relation skew-SYT ratio bound** (Prong 1 §5) and the **forced-relation order-polytope ratio bound** (Prong 3E-α). Both are parked per the ticket NON-GOALS (no attack in this prong).

- **3H-β (only if a future deeper sweep finds `Q < 6/17`).** Not indicated by this prong's data. Were OUTCOME-B ever to surface at `n ≥ 12`, the descent-ladder would be extended via the new argmin (add the rung, recompute `k = 1/(3Q − 1)`, name the new corridor ceiling and its structural family). A higher-`n` extension would need either a methodological reduction beyond order-canon dedup (e.g. orderly generation with on-the-fly canonical-parent acceptance to bound memory) or an HPC/parallel sweep — both beyond the laptop polecat budget.

---

## 6. Reproduction

```
# fast self-test (validates n=5→4/11, n=7→14/39, n=10→6/17; full-5 engines on all ≤ n=8):
python3 scripts/onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust.py --quick

# exhaustive through n=10 (≈ 3.5 min: ~80 s generation + ~3 min analysis on a laptop):
python3 scripts/onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust.py --nmax 10

# exhaustive through n=11 (≈ 33 min: ~14 min generation [3 168 869 classes] + ~20 min analysis;
# RSS ≈ 2.6 GB; --time-budget gates GENERATION and reports the OUTCOME-C breakpoint on overflow):
python3 scripts/onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust.py --nmax 11 --time-budget 3600
```

Every reported `Q` is an exact `Fraction`; the §8.2 guard fires on every iso-class; cross-engine disagreement halts as P0. No Lean, no LaTeX, no Monte-Carlo source-of-truth, no σ-iso reduction (order-iso only), no t-dilation — per the ticket NON-GOALS.
