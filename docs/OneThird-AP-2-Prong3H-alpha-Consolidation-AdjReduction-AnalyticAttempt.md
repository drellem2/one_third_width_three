# OneThird — AP-2 Prong 3H-α: structural consolidation + the Q-preserving extreme-adjunction lemma + the extreme-reduction theorem + the analytic `Q ≥ 6/17` attempt on the self-dual core

*Work item **mg-6728**. Consolidation + analytic follow-up to mg-5406 (Prong 3G-α, OUTCOME-C + PARTIAL OUTCOME-A: `6/17` holds across the **full** width-3 arena exhaustively through `n = 11`, reached **non-self-dually** from `n = 11` by global-top adjunction of the `n = 10` self-dual witness) and mg-7ee8 (Prong 3E-α, the self-dual-core Outcome-4 WALL). Date 2026-05-29.*

*Read-first (the whole arc, in sequence): [`OneThird-AP-2-Prong1-SelfDual-LowerBound.md`](OneThird-AP-2-Prong1-SelfDual-LowerBound.md) · [`OneThird-AP-2-Prong2-FamilyB-SP-Probe.md`](OneThird-AP-2-Prong2-FamilyB-SP-Probe.md) · [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) · [`OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md`](OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md) · [`OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md`](OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md) · [`OneThird-AP-2-Prong3C-Width3-FloorBound.md`](OneThird-AP-2-Prong3C-Width3-FloorBound.md) · [`OneThird-AP-2-Prong3D-alpha-DescentRay.md`](OneThird-AP-2-Prong3D-alpha-DescentRay.md) · [`OneThird-AP-2-Prong3E-alpha-SelfDualWidth3-FloorBound.md`](OneThird-AP-2-Prong3E-alpha-SelfDualWidth3-FloorBound.md) · [`OneThird-AP-2-Prong3F-beta-SelfDual-n11-13-Empirical.md`](OneThird-AP-2-Prong3F-beta-SelfDual-n11-13-Empirical.md) · [`OneThird-AP-2-Prong3G-alpha-NonSelfDual-n10-13-Empirical.md`](OneThird-AP-2-Prong3G-alpha-NonSelfDual-n10-13-Empirical.md) · [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§3,4,6,8 · [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3h_alpha_consolidation_verify.py`](../scripts/onethird_ap2_prong3h_alpha_consolidation_verify.py) — reuses the five-engine `verify_C` harness (M1 order-ideal DP / M2 AP-0 kernel / M3 `IndPoset` removal recursion / M4 brute permutations / MC Ehrhart order-polynomial), `find_involution`, and the Prong-3E σ-orbit checker `R1-ORBIT` **verbatim**, and adds: the **adjunction-lemma checker** (`e`, every pairwise balance, width, and `Q` preserved by both `+top` and `+bottom`, exhaustively over every width-3 poset at `n = 4..6` and on every rung witness), the **extreme-reduction core** `core(P)` and its Q-preservation, the **reduction-theorem argmin-table sanity** (every overall per-`n` argmin reduces to a self-dual core), and the **self-dual-core analytic-bound sanity** (R1 + the ladder closed form vs five-engine truth at `k = 11, 13, 17` and the `134/375` family). Pure stdlib; clean run a few seconds. A clean exit *is* the lemma + theorem + sanity suite passing.*

---

## 0. Headline

**VERDICT: OUTCOME-4 (WALL) on the STRONG self-dual-core reduction + analytic `Q ≥ 6/17`, carrying TWO NEW RIGOROUS ANALYTIC DELIVERABLES + the arc's first consolidated structural overview.**

The STRONG goal (prove `Q ≥ 6/17` for *all* width-3 posets, sharp at the rung witnesses) is **not** reached: it terminates at the same forced-relation order-polytope ratio bound that walled Prong 3E-α. But Prong 3H-α converts the previously-empirical "+1-`n` Q-preserving extreme adjunction" pattern into **two proved theorems** and assembles the **consolidation document** the arc was missing. Five exact results:

1. **(ADJ) The Q-preserving extreme-adjunction lemma — PROVED (§3).** For any finite poset `P` and a global maximum `⊤` adjoined (`P + ⊤`), and dually a global minimum `⊥` (`⊥ + P`):
   ```
   e(P + ⊤) = e(P),   Pr_{P+⊤}[x<y] = Pr_P[x<y] for every incomparable {x,y} in P,   Q(P + ⊤) = Q(P),
   ```
   and likewise for `⊥`. This is the `R = singleton` case of the general **ordinal-sum identity** `Q(P ⊕ R) = max(Q(P), Q(R))` — the order-polytope analogue of Prong-3A's Lemma B "series = max", now for **arbitrary** `P` (not only series-parallel). Previously (mg-5ff1, mg-7ee8, mg-5406) this was named and empirically observed; here it is a closed-form theorem with a one-line linear-extension proof.

2. **(RED) The extreme-reduction theorem — PROVED (§4).** Iteratively deleting global maxima and global minima from a width-3 poset `P` (with an incomparable pair) terminates at an **extreme-reduced core** `core(P)` with
   ```
   Q(P) = Q(core(P)),   width(core(P)) = width(P) = 3,   core(P) has no global max and no global min.
   ```
   Hence `inf{Q(P) : P width-3} = inf{Q(C) : C width-3, extreme-reduced}`. The full-arena floor question **reduces rigorously** to the extreme-reduced core.

3. **(GAP) The reduction to the *self-dual* core is CONDITIONAL (§4.3).** Adjunction + extreme-reduction do **not** prove `core(P)` self-dual (no Q-preserving self-dualization operation exists). The STRONG statement "self-dual core `Q ≥ 6/17` ⟹ full-arena `Q ≥ 6/17`" requires the additional **self-dualization hypothesis**: every Q-minimizing extreme-reduced width-3 poset is self-dual. This is **empirically verified exhaustively through `n = 11`** (mg-5406; every overall per-`n` argmin is either (a) a global-extreme adjunction of a self-dual core, or (b) an extreme-reduced self-dual minimum) but **not proved**. This is the named gap; it is *why* STRONG is walled at the polecat scale.

4. **(WALL) The self-dual-core analytic floor stays the mg-7ee8 missing input (§5).** On the self-dual core the bound `Q ≥ 6/17` reduces — via the σ-orbit reduction (Prong-3E-α Thm R1) + the gadget identity (Prong-3D-α) — to the forced-relation order-polytope ratio
   ```
   6/17 · e(P)  ≤  e(P + x<y)  ≤  11/17 · e(P)
   ```
   on the near-twin σ-orbit class: the **same** named missing input. The new content is that **extreme-reduction sharpens the target** — the trivial Q-preserving adjunction families are now excluded from the core, so the bound is needed only on **extreme-reduced** self-dual width-3 posets.

5. **(CONSOLIDATION) §2 is the arc's first cleanly-organised structural overview** — bars, rungs, walls, theorems, the one refutation, the two missing inputs, and the vision-aligned narrative, assembled into a stand-alone reader.

**Corridor UNCHANGED at `(1/3, 6/17]`.** `6/17` is the corridor ceiling, now an explicit theorem-shaped reduction target on the **extreme-reduced self-dual core**.

**§8.2 anti-Cheeger guard (INHERITED STRICT) does NOT fire.** Every `Q` encountered is `> 1/3` (lowest `6/17`); no `Q ≤ 1/3` candidate arises, so M1–M4 + MC suffice and **no sixth codebase is triggered**.

---

## 1. Vision alignment (V2 + V4) — verbatim from the ticket

> **V2 (computable Q):** leverages the closed-form identities consolidated across the arc — Ehrhart volume ratio Pr[x<y] = e(P + x<y) / e(P) (Stanley 1986); the gadget identity Pr[x<y_i] = i/(t+1) (Prong 3D-alpha); the sigma-orbit reduction Q(P) = max over sigma-orbit reps (Prong 3E-alpha Thm R1); the expected-rank antisymmetry r̄(x) + r̄(sigma·x) = n+1 (Prong 3E-alpha Thm R2); and the new Q-preserving extreme adjunction lemma (Prong 3G-alpha). All five together give the analytic toolkit.
>
> **V4 (sharpness-or-pivot signal):**
> - STRONG (analytic-strong like Prong 3A's 8/21 SP theorem): prove Q >= 6/17 for ALL width-3 posets, ALL n, SHARP at the n=10 (and n=11 non-self-dual) 6/17 witnesses. The strongest possible outcome. Requires (a) closing the missing input from Prong 3E-alpha (forced-relation order-polytope ratio bound on the near-twin sigma-orbit class) OR (b) finding an alternative analytic route that bypasses the missing-input wall.
> - PARTIAL: prove Q >= c for some 1/3 < c <= 6/17 on the full width-3 arena. Names the gap. Useful if STRONG hits the same missing-input wall as Prong 3E-alpha did.
> - WALL (Outcome 4 — like Prong 1, Prong 3B-beta, Prong 3B-gamma, Prong 3E-alpha): clean negative diagnosis. The most likely outcome given that Prong 3E-alpha already named the forced-relation order-polytope ratio bound as the missing input on the self-dual core, and adjunction reduces full arena to self-dual core. STRONG implies attacking that missing input. WALL means re-naming the same missing input and consolidating.
> - REFUTATION not applicable: mg-5406 + mg-7237 ruled out Q < 6/17 through n=11; a refutation would require a width-3 P at n >= 12 with Q < 6/17, beyond polecat compute.

**Which V4 branch fired:** the **WALL** branch (Outcome 4), *carrying* the two new analytic theorems and the consolidation doc that the ticket flagged as the prong's primary value. On **V2**, all five closed-form identities are present and used: the order-polytope ratio is the engine of the adjunction proof (§3); the σ-orbit reduction (R1) and expected-rank antisymmetry (R2) localise the self-dual-core target (§5); the gadget identity explains the descent-ladder geometry (§2.3); and the Q-preserving extreme-adjunction lemma is now **proved**, not empirical (§3). On **V4**, STRONG is shown unreachable at polecat scale for two compounding reasons — the conditional self-dualization gap (§4.3) and the unchanged forced-relation ratio wall (§5); PARTIAL with explicit `c > 1/3` on the full arena is open-problem-hard (§5.3, inherited from Prong 3E-α); no REFUTATION is possible at polecat compute. The deliverable is the clean Outcome-4 diagnosis with **two proved theorems**, the precisely-named gap, the re-named (and sharpened) missing input, and the consolidation overview.

---

## 2. The consolidated structural taxonomy of the AP-2 arc

This section is the arc's first stand-alone structural reader. The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3` for every non-chain finite poset; for width 3 it is a **theorem** (the repo's paper, `thm:main`). AP-2 is the *algebraic-program* counterexample search: enumerate / construct width-3 posets whose balance constant `Q(P)` is exactly computable, sweep the parameter space, and either find `Q < 1/3` (a counterexample) or pin the genuine width-3 infimum. Under the uniform distribution on linear extensions,
```
Q(P) = max over incomparable {x,y} of min( Pr[x<y], Pr[y<x] ) = 1/2 − min over incomparable pairs of |Pr[x<y] − 1/2|,
Pr[x<y] = e(P + x<y) / e(P)   (Stanley 1986 order-polytope ratio; e = # linear extensions).
```

### 2.1 Reference bars (the value landmarks)

Sorted from the trivial ceiling down to the conjecture floor (all exact rationals; verified in `§8` of the script):

| bar | value | role | source |
|---|---|---|---|
| `1/2` | 0.500000 | trivial upper ceiling (antichain pair) | — |
| `2/5` | 0.400000 | the `{1,1,1}` three-parallel-chain SP bound; a Family-D bar | Prong 3A §4 / 3B-β |
| `27/70` | 0.385714 | **SKEW-ARTIFACT** — a skew-shape value, *not* a genuine width-3 poset `Q` | Prong 2 (Family A) |
| `8/21` | 0.380952 | **width-3 SP analytic floor — SHARP** at `T* = [G⊕G]‖pt` | Prong 3A (theorem) |
| `4/11` | 0.363636 | descent-ladder **seed** (`k=11`, `n=5`) | Prong 3B-γ / 3C |
| `14/39` | 0.358974 | ladder rung (`k=13`, `n=7`); the **debunked** "odd-`n` floor" | Prong 3C (refuted) |
| `134/375` | 0.357333 | odd-`n` **off-ladder** self-dual minimum (`k=125/9 ∉ ℤ`) | Prong 3F-β |
| `6/17` | 0.352941 | width-3 **corridor ceiling / floor candidate** (`k=17`, `n=10`) | Prong 3C (refutation witness) |
| `1/3` | 0.333333 | global tight bound — **the conjecture** | classical |

The genuine width-3 sharpness ordering is `8/21 (SP) > 4/11 > 14/39 > 134/375 > 6/17 > 1/3`. The crucial structural fact: **`6/17` is the deepest non-SP width-3 value found, and SP posets cannot reach it** (Prong 3A floors all width-3 SP at `8/21`). The descent therefore lives **off** the series-parallel class — exactly why the Prong-3A Lemma-A SP-tree recursion is unavailable on the self-dual core (§5).

### 2.2 The descent ladder (the rungs)

The three minimum-`Q` width-3 witnesses lie on one Diophantine ladder (Prong 3C):
```
Q = (k+1)/(3k) = 1/3 + 1/(3k),   binding pair Pr = (2k−1)/(3k) → 2/3,   k ∈ {11, 13, 17}.
```
| rung | `n` | `Q` | `k` | `e` | binding Pr | self-dual? | source |
|---|---:|---|---:|---:|---|:--|---|
| seed | 5 | `4/11` | 11 | 11 | `7/11` | yes | 3B-γ / 3C |
| `14/39` | 7 | `14/39` | 13 | 39 | `25/39` | yes | 3C |
| `6/17` | 10 | `6/17` | 17 | 187 = 11·17 | `11/17` | yes | 3C |

The ladder **points** toward `inf Q = 1/3` (asymptotically sharp at width 3) but does **not** extend past `k = 17` under construction, one-parameter stretch, or exhaustive local self-dual search (Prong 3D-α). The rungs are **sporadic self-dual minima** — `e ∈ {11, 39, 187}` is not a clean `3k` — not a single parametric family. The `134/375` value (Prong 3F-β, `n = 11, 13`, `e = 750`) is a genuinely new **off-ladder** odd-`n` self-dual extremal sitting strictly inside `(6/17, 14/39)`, not a fourth rung.

### 2.3 The analytic theorems (the proved positive content)

| # | theorem | statement | source |
|---|---|---|---|
| T1 | self-dual symmetry + signed gap | order-reversing involution mirrors balances; signed-gap invariance | Prong 1 |
| T2 | **8/21 SP floor, SHARP** | every width-exactly-3 SP poset has `Q ≥ 8/21`, sharp at `T*` | Prong 3A |
| T3 | gadget identity | point `‖` `t`-chain: `Pr[x<y_i] = i/(t+1)`; `t=2` is the unique `Q=1/3` length | Prong 3D-α |
| T4 | σ-orbit reduction (R1) | self-dual `P`: `Q(P) = max over σ-orbit reps of the orbit balance` | Prong 3E-α |
| T5 | expected-rank antisymmetry (R2) | self-dual `P`: `r̄(x) + r̄(σx) = n+1`; σ-fixed ⟹ central | Prong 3E-α |
| **T6** | **Q-preserving extreme adjunction** | `e, Q,` all balances preserved by global `+top` / `+bottom`; `R=singleton` of `Q(P⊕R)=max(Q(P),Q(R))` | **Prong 3H-α §3** |
| **T7** | **extreme-reduction** | `Q(P)=Q(core(P))`, width-preserving; `inf` over width-3 = `inf` over extreme-reduced width-3 | **Prong 3H-α §4** |

T6 and T7 are this prong's new analytic deliverables; T1–T5 are the inherited toolkit (the five closed-form identities the V2 paragraph names).

### 2.4 The proved structural walls (the named negatives)

| wall | mechanism | source |
|---|---|---|
| W1 | box-rotation signed-gap: an anti-automorphism mirrors bias, does not cancel it | Prong 1 §4 |
| W2 | Family-D algebraic-construction probe: no width-3 sub-`8/21` host | Prong 3B-β |
| W3 | Ehrhart-dilation Q-invariance: `t`-dilation of the order polytope preserves `Q` (no descent via dilation) | Prong 3B-γ §3.2 |
| W4 | signed-gap Φ-invariance on the near-twin σ-orbit: self-duality pins no balance | Prong 3E-α §3 |

### 2.5 The one refutation, the two missing inputs, the empirical exhaustion

- **REFUTATION (Prong 3C):** `14/39` is **not** the width-3 floor — a width-3 poset at `n=10` attains `6/17 < 14/39` (still `> 1/3`), narrowing the corridor `(1/3, 14/39] → (1/3, 6/17]`. The "`n=8` plateau" was a trivial global-top extension artifact (the adjunction lemma, then unnamed).
- **Missing input A (Prong 1 §5):** a forced-relation **skew-SYT** ratio bound — the skew-shape twin of the order-polytope ratio. Research-grade, parked.
- **Missing input B (Prong 3E-α §5):** a forced-relation **order-polytope** ratio bound `6/17·e(P) ≤ e(P+x<y) ≤ 11/17·e(P)` on the near-twin σ-orbit class. Research-grade, parked. **This is the wall Prong 3H-α re-confirms and sharpens.**
- **Empirical exhaustion:** `Q ≥ 6/17` holds over the **full** width-3 arena exhaustively through `n = 11` (mg-5406: 3 168 869 iso-classes at `n = 11`; cumulative ≈ 3.6·10⁶ through `n = 11`), and over the **self-dual** arena through `n = 13` (mg-7237: 71 512 σ-iso classes). `n = 12 (≈ 2·10⁷ classes)` and `n = 13 (≈ 1.6·10⁸)` of the full arena are the compute wall (HPC required; beyond polecat).

### 2.6 Vision-aligned narrative

The program's purpose (Vision V4) is to find a width-3 `Q < 1/3` counterexample **or** pin the genuine width-3 infimum sharply. AP-2 has, across eleven prongs, (i) **settled** the series-parallel sub-family with a sharp theorem (`8/21`, T2), (ii) **discovered and refuted** a false floor (`14/39`) and a false plateau (`n=8`), surfacing the descent ladder and its `6/17` corridor ceiling, (iii) **exhaustively cleared** the full width-3 arena of any `Q < 6/17` through `n = 11` and the self-dual arena through `n = 13`, and (iv) **localised the analytic obstruction** to a single self-contained counting inequality (missing input B) on the extreme-reduced self-dual core. The §8.2 anti-Cheeger guard fired on every one of the millions of swept iso-classes and never tripped: the lowest `Q` anywhere is `6/17 > 1/3`. The honest state is a **bounded null with a sharp corridor `(1/3, 6/17]`** and a named research-grade gateway to either a sharpness theorem or (at `n ≥ 12`, HPC) a possible counterexample.

---

## 3. The Q-preserving extreme-adjunction lemma (T6, PRIMARY analytic deliverable)

> **Lemma B′ (ordinal sum = max — for arbitrary posets).** For any finite posets `P, R`,
> ```
> e(P ⊕ R) = e(P) · e(R),    Q(P ⊕ R) = max( Q(P), Q(R) ),
> ```
> and for every incomparable pair `{x,y}` of `P ⊕ R` (which lies wholly in `P` or wholly in `R`), `Pr_{P⊕R}[x<y]` equals its sub-poset balance. (`Q` of a chain — no incomparable pair — is taken as `−∞`, so a singleton operand drops out of the `max`.)

**Proof.** In the ordinal sum `P ⊕ R` every element of `P` is below every element of `R`. A linear extension of `P ⊕ R` must therefore place all of `P` in the first `|P|` ranks and all of `R` in the last `|R|` ranks; conversely any pair (extension of `P`, extension of `R`) glued this way is a linear extension. Hence `e(P ⊕ R) = e(P)·e(R)`, and the bijection `λ ↦ (λ|_P, λ|_R)` is rank-order-preserving on each side.

Cross pairs `(p ∈ P, r ∈ R)` are all comparable (`p < r`), so the incomparable pairs of `P ⊕ R` are exactly the incomparable pairs **within** `P` together with those **within** `R`. For an incomparable pair `{x,y} ⊆ P`, the `R`-block sits entirely above both `x` and `y` and shifts them equally, so `x < y` in `λ` iff `x < y` in `λ|_P`; therefore `Pr_{P⊕R}[x<y] = Pr_P[x<y]` (and symmetrically for pairs in `R`). Taking the max over all incomparable pairs gives `Q(P ⊕ R) = max(Q(P), Q(R))`. ∎

> **Corollary T6 (Q-preserving extreme adjunction).** Let `⊤` be a global maximum adjoined to `P` (i.e. `P + ⊤ := P ⊕ {⊤}`) and `⊥` a global minimum (`⊥ + P := {⊥} ⊕ P`). Then
> ```
> e(P + ⊤) = e(P),   Q(P + ⊤) = Q(P),   Pr_{P+⊤}[x<y] = Pr_P[x<y]  for every incomparable {x,y} in P,
> ```
> and identically for `⊥ + P`. Moreover `width(P + ⊤) = width(P)` whenever `P` has an incomparable pair.

**Proof.** Apply Lemma B′ with `R = {⊤}` a singleton: `e({⊤}) = 1` so `e(P+⊤) = e(P)·1 = e(P)`; the singleton has no incomparable pair, so `Q({⊤}) = −∞` and `Q(P+⊤) = max(Q(P), −∞) = Q(P)`; every incomparable pair of `P+⊤` lies in `P` with its `P`-balance. (Directly: `⊤ > x` for all `x` forces `λ(⊤) = n+1` in every linear extension, so extensions of `P+⊤` biject with extensions of `P` by restriction, and `⊤` is comparable to everything, leaving the incomparable pairs and their conditional orders untouched.) The dual `⊥ + P` is Lemma B′ with `R = P`, `P → {⊥}`: `λ(⊥) = 1`, all other ranks shift up by `1` uniformly, preserving relative order. Finally, a global extremum is comparable to every element, so it never belongs to an antichain of size `≥ 2`; the maximum antichain (size = width `= 3 > 1`) is unchanged, so `width(P+⊤) = width(P) = width(⊥+P)`. ∎

**Provenance.** This is the order-polytope analogue of Prong-3A's Lemma B "series = max" (which was stated for SP posets via the SP-tree); Lemma B′ proves it for **arbitrary** `P`. It is exactly the structural source of the previously-empirical observations: the Prong-3C "`n=8` plateau" (`14/39` witness `+` global top), the Prong-3D-α / 3E-α "`+2` self-dual floor held only by the e-preserving adjunction", and the Prong-3F-β / 3G-α "`6/17` reached non-self-dually from `n=11` by global-top adjunction of the `n=10` witness". All four are now one theorem.

**Verification.** `§2`–`§3` of the script check T6 (i) on all three rung witnesses (`e`, every pairwise balance, width, and `Q` preserved by both `+top` and `+bottom`, five-engine on the companions), (ii) on the **headline**: the `n=10` self-dual `6/17` witness `+` global top is a **non-self-dual** width-3 poset at `n=11` with `Q = 6/17` exactly (`e = 187` fixed, `find_involution` returns `None`), matching the mg-5406 exhaustive `n=11` non-self-dual argmin, and the `+bottom` dual likewise; and (iii) **exhaustively** on every width-3 poset (with an incomparable pair) at `n = 4, 5, 6` (16 + 212 + 2 842 cases) — `e`, all balances, width, and `Q` preserved by both adjunctions in every case.

---

## 4. The extreme-reduction theorem (T7) and the reduction to the self-dual core

### 4.1 The core and its Q-preservation

> **Definition (extreme-reduced core).** For a finite poset `P`, repeatedly delete a global maximum or a global minimum (whenever one exists) until none remains. Call the result `core(P)`; `P` is **extreme-reduced** if `core(P) = P`, i.e. it has neither a global maximum nor a global minimum.

> **Theorem T7 (extreme-reduction).** For a width-3 poset `P` with at least one incomparable pair,
> ```
> Q(P) = Q(core(P)),   width(core(P)) = 3,   core(P) is extreme-reduced.
> ```
> Consequently `inf{ Q(P) : P width-3 } = inf{ Q(C) : C width-3, extreme-reduced }`.

**Proof.** Each single deletion of a global maximum or minimum is a backward application of Corollary T6 (the deleted element is `⊤` or `⊥` of the current poset), so it preserves `Q` and keeps width `= 3` (a width-3 poset retains its incomparable pair, so T6's width clause applies at every step). Deletion strictly decreases `|P|`, so the process terminates; at termination there is no global max or min, i.e. the result is extreme-reduced. By induction `Q(P) = Q(core(P))` and `width(core(P)) = 3`. The infimum identity follows because every width-3 poset has the same `Q` as its extreme-reduced core, and every extreme-reduced width-3 poset is its own core. ∎

**Well-definedness note.** `core(P)` is the unique extreme-reduced poset reached; although the *order* of stripping max-vs-min can differ, every order yields the same `Q` (all steps are Q-preserving), which is all T7 needs. (The combinatorial core itself is also order-independent: a global max and a global min of the same poset are distinct and removing one cannot create or destroy the other's global-extremum status until it too is isolated, so the strip set is determined.)

### 4.2 The full arena reduces to the extreme-reduced core (RIGOROUS)

T7 is the rigorous half of the ticket's "reduction theorem". It says the full-arena floor question is **identical** to the extreme-reduced-core floor question — no information is lost by discarding posets with global extremes, because their `Q` is inherited unchanged from a strictly smaller core. In particular the descent ladder's "+1-`n` self-duality breakage" (mg-5406: `k=11` `n=5→6`, `k=13` `n=7→8`, `k=17` `n=10→11`) is **uniformly explained**: each rung's value first appears at an extreme-reduced self-dual minimum (`n = 5, 7, 10`), then re-appears one step later as that minimum `+` a single global extreme (`n = 6, 8, 11`), which T6 makes Q-identical and T7 reduces straight back to the self-dual core.

**Verification (the reduction-theorem argmin-table sanity).** `§4` of the script confirms, on the per-`n` overall argmin table of mg-5406:
- **fact (b):** the `n = 5, 7, 10` rung witnesses are **already extreme-reduced** (0 elements stripped) **and self-dual** — extreme-reduced self-dual minima at their own `n`;
- **fact (a):** the `n = 8` companion (`14/39` `+` top) strips `1` top to the `n=7` self-dual core; the `n = 11` companions (`6/17` `+` top, and `+` bottom) strip `1` extreme to the `n=10` self-dual core — `Q` preserved, core self-dual, in every case.

### 4.3 The reduction to the *self-dual* core is CONDITIONAL — the named gap

The ticket's STRONG statement is "if every width-3 **self-dual** poset has `Q ≥ 6/17`, then every width-3 poset has `Q ≥ 6/17`." T7 reduces the full arena to the **extreme-reduced** core, **not** the self-dual core. Closing the remaining distance requires:

> **Self-dualization hypothesis (the gap).** Every Q-minimizing extreme-reduced width-3 poset is self-dual. Equivalently: the extreme-reduced width-3 minimum at each `n` is attained by a self-dual poset.

**Why this is a genuine gap, not a theorem.** Adjunction (T6) and extreme-reduction (T7) are the only structural levers in hand, and **neither produces self-duality**: there is no `Q`-preserving operation that turns an arbitrary extreme-reduced width-3 poset into a self-dual one (symmetrizing moves like `P ⊕ P^op` or products change `Q`). So a width-3 poset with no global extreme, `Q < 6/17`, and **no** order-reversing involution would defeat the reduction while leaving the self-dual-core hypothesis untouched. The self-dualization hypothesis asserts no such Q-minimizer exists.

**Status of the gap.** Verified **exhaustively through `n = 11`** (mg-5406, 3 168 869 iso-classes): every overall per-`n` argmin is (a) a global-extreme adjunction of a self-dual core, or (b) an extreme-reduced self-dual minimum — so the *observed* minimizers all satisfy it. But this is empirical exhaustion to a compute wall, **not** a proof for all `n`. Therefore:

> **Conditional reduction theorem.** Assuming the self-dualization hypothesis, T7 + T6 give: `[every width-3 self-dual poset has Q ≥ 6/17] ⟹ [every width-3 poset has Q ≥ 6/17]`.

This is the honest formalisation of mg-5406 §0 fact 3. The full-arena floor theorem reduces to the self-dual-core floor theorem **up to the self-dualization hypothesis**; the hypothesis is the first of the two gaps that keep STRONG out of polecat reach (the second is §5's missing input).

---

## 5. The analytic `Q ≥ 6/17` attempt on the self-dual core

### 5.1 Goal and route

STRONG goal: `Q ≥ 6/17` for all width-3 posets, sharp at the rung witnesses. By §4, it suffices (given the self-dualization hypothesis) to prove `Q ≥ 6/17` on the **extreme-reduced self-dual** core. The route is the V2 toolkit: localise `Q` to a σ-orbit representative (R1), then bound that representative's balance below by `6/17` via the order-polytope ratio and the gadget identity.

### 5.2 The σ-orbit reduction localises the target; the wall is unchanged

By Prong-3E-α **Theorem R1** (re-verified at all three rungs in `§6` of the script: `Q = max over σ-orbit reps`, every orbit carries one balance), on a self-dual `P` it suffices to bound the **binding σ-orbit** below by `6/17`. At every rung that binding orbit is a **near-twin orbit-2 pair** with `Pr = (2k−1)/(3k)`. Prong-3E-α §3 proved (Lemma W, signed-gap Φ-invariance) that an **order-reversing involution pins no balance**: for orbit-2 pairs σ only mirrors the pair to an equal-balance partner (no pinning equation), and for σ-swapped pairs the signed gap is Φ-invariant. So the symmetry localises the target but cannot bound it. The bound `Q ≥ 6/17` therefore reduces, exactly as in mg-7ee8 §5, to the forced-relation order-polytope ratio
```
6/17 · e(P)  ≤  e(P + x<y)  ≤  11/17 · e(P)   on the near-twin σ-orbit binding pair {x,y}
```
— **missing input B**, a self-contained width-3 extension-count inequality, the Ehrhart twin of Prong-1's skew-SYT missing input, and a special case of the open width-3 sharpness question. The gadget identity `Pr[x<y_i] = i/(t+1)` (T3) is **single-strand**; the binding balance is the **three-strand** ratio governed by the sporadic `e ∈ {11, 39, 187}`, so it cannot supply the bound either. **The wall is identical to Prong 3E-α's.**

### 5.3 What Prong 3H-α adds at the wall: the target is sharpened

The new content is that **extreme-reduction (T7) excludes the trivial Q-preserving adjunction families from the core**. In mg-7ee8 the local-floor evidence had to carry the caveat that the `6/17` minimum is "held *only* by the global-extremum adjunction (`e=187` fixed)"; under T7 those adjunction posets are *not* in the extreme-reduced core at all (they strip back to the `n=10` witness). So missing input B is needed only on **extreme-reduced** self-dual width-3 posets — a strictly smaller class than "all self-dual width-3 posets", excluding precisely the Q-preserving inflations. This sharpens the named gateway; it does not open it.

### 5.4 Why no PARTIAL with explicit `c > 1/3` (inherited, honest)

Any `Q ≥ c` with `c > 1/3` on the full width-3 arena (or its self-dual core) is a strict strengthening of the 1/3–2/3 conjecture restricted to width 3, and the only family-specific lever — self-duality — pins no balance (§5.2). We can prove `Q ≥ 1/3` on the class (the width-3 theorem restricted, with the balanced pair realisable on a σ-orbit by R1), but that is `c = 1/3`, not a strengthening. Claiming any explicit `c > 1/3` would be unsupported; this matches Prong 3E-α §5. (For scale: the strongest *unconditional* non-chain bound, Brightwell–Felsner–Trotter `δ ≥ (5−√5)/10 ≈ 0.2764`, sits *below* `1/3` and cannot even deliver the conjecture.)

### 5.5 Sharpness verification at the rung witnesses

`§7` of the script confirms the closed-form ladder identity agrees with five-engine truth: at `k = 11, 13, 17` the binding-pair balance equals `(k+1)/(3k) = Q`, and `6/17` is the sharp value at the deepest rung `k = 17`. The `134/375` odd-`n` family (mg-7237, five-engine-verified there) is re-confirmed symbolically: `6/17 < 134/375 < 14/39`, `k = 125/9 ∉ ℤ` (off-ladder), binding `Pr = 241/375 = 1 − 134/375` (near-twin orbit-2) — consistent with the `6/17` floor candidate, which it respects. Any analytic bound proved on the self-dual core must therefore be `≤ 6/17` (sharp at `k=17`) and `≤ 134/375` at odd `n=11,13` — both confirmed.

---

## 6. Verdict and the missing input that would close STRONG

**OUTCOME-4 (WALL)** on the STRONG self-dual-core reduction + analytic `Q ≥ 6/17`, carrying **two proved theorems** (T6 adjunction, T7 extreme-reduction), the **named self-dualization gap** (§4.3), the **re-named + sharpened missing input** (§5), and the **consolidation overview** (§2).

**What would close STRONG (explicitly named, per the ticket NON-GOALS):** *two* inputs, both research-grade and parked:
1. **The self-dualization hypothesis (§4.3)** — proving every Q-minimizing extreme-reduced width-3 poset is self-dual, to upgrade T7's extreme-reduced-core reduction to a self-dual-core reduction. (Empirically true through `n=11`.)
2. **Missing input B (§5.2)** — the forced-relation order-polytope ratio `6/17·e(P) ≤ e(P+x<y) ≤ 11/17·e(P)` on the near-twin σ-orbit class of extreme-reduced self-dual width-3 posets. (The Ehrhart twin of Prong-1's missing input A.)

Either alone is insufficient; STRONG needs both. This is the clean Outcome-4 the ticket anticipated: Prong 3H-α replicates Prong 3E-α's wall **with two new features** — the adjunction-reduction is now an explicit theorem (T6 + T7), and §2 is the arc's first cleanly-organised structural overview.

**Corridor UNCHANGED at `(1/3, 6/17]`.** **§8.2 guard cleared** (lowest `Q = 6/17 > 1/3`; no sixth codebase triggered).

---

## 7. Suggested Prong 3I brief (gated on this verdict)

Per the V4 gating, the WALL verdict gates to consolidation-completion + the two named gateways (no `mg new` is called here; recommendations only):

- **3I-α (recommended) — attack the self-dualization hypothesis (§4.3) analytically.** This is the *cheaper* of the two STRONG-closing gateways and is **not** a special case of the open conjecture (contrast missing input B): it is a pure structural-extremal claim about width-3 Q-minimizers. A tractable sub-question: prove that an extreme-reduced width-3 Q-minimizer with a unique binding incomparable pair must admit an order-reversing involution fixing that pair's σ-orbit (the rungs all do). Even a *conditional* proof (self-dual under an extra regularity hypothesis on the minimizer) would tighten §4.3's empirical fact toward a theorem and is polecat-sized.
- **3I-β (research-grade, parked) — missing input B.** The forced-relation order-polytope ratio bound on the near-twin σ-orbit class. Larger than a polecat; a special case of the open width-3 sharpness problem (Prong 3E-α §6 already flagged this as 3F-γ). Per NON-GOALS, **not** attacked at polecat scale.
- **3I-γ (HPC, parked) — full-arena `n = 12, 13` exhaustion.** The `≈ 2·10⁷` / `≈ 1.6·10⁸`-class sweeps that would extend mg-5406's empirical floor (and the self-dualization exhaustion) past `n = 11`. HPC required; separate ticket, beyond polecat.

*(Parked / out of scope per NON-GOALS: no Cheeger/cut-and-window; no HPC `n ≥ 12` here; no `Q ≤ 1/3` claim without a sixth codebase per §8.2 STRICT — not reached, lowest `Q = 6/17`; no Lean/LaTeX/main.tex; Monte-Carlo never source of truth; no t-dilation argument (Wall W3); no new family probe (A/B/C/D exhausted); no attack on the two named missing inputs at polecat scale; no formal closure of Prong-3A's non-binding φ4/Lemma-T lemmas.)*

---

## Carry-forwards (for the next polecat)

- **Verdict:** OUTCOME-4 (WALL) on STRONG, carrying **two proved theorems** + the consolidation doc. Corridor UNCHANGED at `(1/3, 6/17]`; `6/17` the corridor ceiling, now a theorem-shaped reduction target on the **extreme-reduced self-dual core**.
- **T6 — Q-preserving extreme adjunction (PROVED, reusable):** `e, Q,` all balances preserved by global `+top` / `+bottom`; the `R=singleton` case of `Q(P⊕R) = max(Q(P), Q(R))` for **arbitrary** `P` (Lemma B′). Unifies the `n=8` plateau, the `+2` self-dual floor, and the non-self-dual `n=11` `6/17`.
- **T7 — extreme-reduction (PROVED, reusable):** `Q(P) = Q(core(P))`, width-preserving; `inf` over width-3 = `inf` over extreme-reduced width-3. Reduces the full arena to the extreme-reduced core **rigorously**.
- **The named gap (§4.3):** the **self-dualization hypothesis** — every Q-minimizing extreme-reduced width-3 poset is self-dual (empirical through `n=11`, not proved). Needed to upgrade T7 to a *self-dual*-core reduction. This is the cheaper STRONG-closing gateway (3I-α) — *not* a special case of the open conjecture.
- **The re-named + sharpened missing input (§5):** the forced-relation order-polytope ratio `6/17·e(P) ≤ e(P+x<y) ≤ 11/17·e(P)` on the near-twin σ-orbit class of **extreme-reduced** self-dual width-3 posets (T7 excludes the trivial adjunction families). Same wall as mg-7ee8, smaller class.
- **Consolidation (§2):** bars (`1/2, 27/70*, 2/5, 8/21, 4/11, 14/39, 134/375, 6/17, 1/3`), the descent ladder (`k=11,13,17`), 7 theorems (T1–T7), 4 walls (W1–W4), 1 refutation (3C), 2 missing inputs (A skew-SYT, B order-polytope). Stand-alone arc reader.
- **Reusable instrument:** `scripts/onethird_ap2_prong3h_alpha_consolidation_verify.py` — five-engine `verify_C` + `find_involution` + the Prong-3E `R1-ORBIT` checker, plus the adjunction-lemma checker (exhaustive `n=4..6`), the `extreme_core` reduction, the argmin-table sanity, and the analytic-bound sanity. Clean run a few seconds.
- **Guard discipline (INHERITED STRICT):** lowest `Q = 6/17 > 1/3`; M1–M4 + MC suffice. A `Q ≤ 1/3` claim would require a fresh SIXTH codebase + brute force.
- **Prong 3I target:** 3I-α (self-dualization hypothesis — the cheaper gateway, polecat-sized), with 3I-β (missing input B) and 3I-γ (`n=12,13` HPC) parked research-grade.
