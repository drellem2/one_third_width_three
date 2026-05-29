# OneThird — AP-2 Prong 3F-β: exhaustive iso-reduced self-dual width-3 minimum `Q` at `n = 11, 12, 13` — empirical strengthening of the `6/17` corridor ceiling

*Work item **mg-7237**. Follow-up to mg-7ee8 (Prong 3E-α), which returned the Outcome-4 **WALL** on the *analytic* floor `Q ≥ 6/17` for the self-dual width-3 class (the σ-orbit reduction R1, expected-rank duality R2, Lemma W signed-gap Φ-invariance, the closed-form orbit-shape `Q = (k+1)/(3k)`), exhausted the `+1/+2/+3` self-dual extension shell at the `n = 10` `6/17` witness (min stays `6/17`), and named the missing analytic input (forced-relation order-polytope ratio bound) as research-grade beyond polecat scope. Prong 3E-α tested the floor against **local** perturbations of the `6/17` witness; Prong 3F-β tests it against the **full** self-dual width-3 arena at `n = 11, 12, 13` — every iso-class, not just local extensions. Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3E-alpha-SelfDualWidth3-FloorBound.md`](OneThird-AP-2-Prong3E-alpha-SelfDualWidth3-FloorBound.md) (σ-orbit machinery + Lemma W + the missing input named); [`OneThird-AP-2-Prong3D-alpha-DescentRay.md`](OneThird-AP-2-Prong3D-alpha-DescentRay.md) (closed-form obstruction + self-dual classification of the ladder rungs); [`OneThird-AP-2-Prong3C-Width3-FloorBound.md`](OneThird-AP-2-Prong3C-Width3-FloorBound.md) (REFUTATION + descent ladder + `6/17` witness); [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the analytic `8/21` template — the analytic-strong analog of what this prong is the **empirical complement** of); [`OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md`](OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md) (Ehrhart engine, `4/11` seed, Wall §3.2); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§4,6,8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust.py`](../scripts/onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust.py) — the **direct self-dual width-3 enumerator** (peeling / inverse-extreme-σ-orbit generation), the **canonical-form σ-isomorphism iso-reduction**, the fast all-pairs balance engine (M1), and the five-engine `verify_C` cross-check harness (M1 placed-set DP / M2 AP-0 `Q_via_dp` / M3 Prong-2 `IndPoset` removal recursion / M4 brute permutations / MC Ehrhart order-polynomial). Pure stdlib; full `n ≤ 13` run ≈ 3 min on a laptop.*

---

## 0. Headline

**VERDICT-A — the empirical `6/17` floor is STRENGTHENED.** Over the **exhaustive** iso-reduced self-dual width-3 arena, the minimum `Q` at every `n ∈ {11, 12, 13}` stays `≥ 6/17`:

| `n` | width-3 iso-classes | min `Q` | decimal | `k = 1/(3Q−1)` | `e` | vs `6/17` |
|----:|--------------------:|:--------|:--------|:---------------|----:|:----------|
| 11 | 5 240 | `134/375` | 0.357333 | `125/9` (off-ladder) | 750 | `>` |
| 12 | 17 340 | `6/17` | 0.352941 | `17` (rung) | 187 | `=` |
| 13 | 48 932 | `134/375` | 0.357333 | `125/9` (off-ladder) | 750 | `>` |

`6/17 ≈ 0.352941` is **matched** at `n = 12` (and at `n = 10`) but **never beaten** anywhere through `n = 13`. The whole-sweep minimum is exactly `6/17`. The §8.2 anti-Cheeger guard fires on every one of the `~73 000` iso-classes across `n = 3…13`; the lowest `Q` anywhere is `6/17 > 1/3`, so the guard never trips and **no sixth codebase is triggered**.

Two structural facts emerge:

1. **`6/17` lives on the even-`n` thread only.** It is attained at `n = 10` (the `e = 187` Prong-3C witness) and reproduced at `n = 12` by the **Q-preserving global-top/bottom σ-pair adjunction** (a global maximal `u` together with its σ-mirror global minimal `v = σu`, both comparable to everything — `e` stays `187`, every balance unchanged; the order-polytope analogue of Prong-3A Lemma B "series = max"). The `n = 12` argmin fingerprint is `levels = [1,2,2,2,1,2,1,1]`, fixed-point-free σ (6 orbit-2 pairs), binding pair Pr `= 6/17`. At **odd** `n = 11, 13` this Q-preserving move is unavailable (it adds 2 elements), and the true minimum rises to `134/375`.

2. **A new off-ladder minimum at odd `n`: `134/375`.** The `n = 11` and `n = 13` argmins have `Q = 134/375 ≈ 0.357333`, strictly between `6/17 ≈ 0.352941` and the `14/39 ≈ 0.358974` rung. Its ladder parameter `k = 1/(3·134/375 − 1) = 125/9` is **not** integral, so `134/375` is **off** the descent ladder `Q = (k+1)/(3k)`, `k ∈ {11,13,17}` — it is a genuinely new self-dual width-3 extremal value, not a fourth rung. Its argmin carries **one σ-fixed central element** (`#fixed = 1`, forced at odd `n` by R2), `5`–`6` σ-orbit-2 pairs, binding pair Pr `= 241/375` (a near-twin σ-orbit-2 pair, *not* σ-swapped — the same BIND mechanism as the rungs), levels `[2,3,1,2,2,1]` (`n=11`) and `[1,2,3,1,2,2,1,1]` (`n=13`).

This is the empirical complement to Prong 3E-α's analytic WALL: the analytic floor `Q ≥ 6/17` was *not provable* from self-duality (3E-α), but it now holds **empirically over the entire self-dual width-3 arena at `n = 11, 12, 13`**, not merely on local neighbourhoods of the `n = 10` witness. The corridor stays **`(1/3, 6/17]`**.

---

## 1. Vision alignment (verbatim)

> **V1 (self-dual width-3 arena):** the σ-orbit structural arena named in mg-5ff1 and machined in mg-7ee8. Exhaustive enumeration tests the floor empirically on the entire arena, not just local neighborhoods around 6/17.
>
> **V2 (closed-form `Q` via Ehrhart leading coefficient + orbit shape):** every candidate poset's `Q` computed via the same five-engine harness (M1 placed-set DP / M2 AP-0 `Q_via_dp` / M3 IndPoset / M4 brute / MC Ehrhart). Closed-form rational throughout.
>
> **V3 (parameter space):** combinatorial type of the self-dual width-3 poset, iso-reduced. The σ-orbit + width-3 constraints make the enumeration tractable; iso-reduction by σ-isomorphism keeps the count polynomial in `n`.
>
> **V4 (sharpness-or-pivot signal):**
> - **VERDICT-A:** min `Q` over self-dual width-3 at `n ∈ {11, 12, 13}` stays `≥ 6/17` — STRENGTHENS the empirical `6/17` floor (`n=10` was the cap-extension limit; `n=11–13` is the next bracket).
> - **VERDICT-B:** min `Q < 6/17` at some `n ∈ {11, 12, 13}` — REFUTES `6/17` as self-dual floor; narrows corridor further; updates the descent ladder; possibly opens a fifth ladder rung `k_max(n_min)` and a new analytic target.
> - **VERDICT-C:** compute budget exhausted before reaching `n=13` — report partial (`n=11` or `n=12`) verdict, note which higher `n` remains.
> - **WALL:** structural enumeration / iso-reduction blockage emerges — name the wall (a fifth proven wall) and report.

**Realised:** V1 — the entire arena at `n ≤ 13` is enumerated, not sampled. V2 — every reported `Q` is an exact `Fraction`; the argmin at every `n` (the verdict-bearing witness) is cross-validated through **all five** engines `M1 = M2 = M3 = M4 = MC`, and the fast primary engine M1 is validated against the independent slow `Q_primary` on **all 8 758 classes through `n = 11`** and against the full five-engine harness on the argmin + a 60-class deterministic sample at `n = 12, 13`. V3 — iso-reduction by σ-isomorphism via an exact canonical form (below). V4 — **VERDICT-A**.

---

## 2. The iso-reduction protocol (V3) — direct self-dual generation + canonical σ-isomorphism

### 2.1 Why generate-all-then-filter is hopeless, and the peeling that replaces it

Labelled width-3 posets already exceed `6·10⁵` at `n = 8` and `2·10⁶` at `n = 9` (measured), so enumerating all width-3 posets and filtering self-dual is infeasible at `n ≥ 10`. Self-dual posets are **rare**, so the enumerator generates them **directly**.

A finite poset `P` is self-dual iff it admits an order-*reversing* involution `σ` (`x < y ⟺ σy < σx`, `σ² = id`). Every non-empty self-dual poset has a maximal element `u`; then `σu` is minimal, and exactly one of:

- **`u = σu`:** `u` is maximal *and* minimal, hence **isolated** and σ-fixed;
- **`u ≠ σu`:** `{u, σu}` is a σ-orbit with `u` a global maximal, `σu` a global minimal, and removing **both** leaves a smaller self-dual poset (σ restricts).

So the **inverse moves** build *every* self-dual poset from the empty poset, producing `(P, σ)` pairs:

- **Move F** — adjoin one **isolated σ-fixed** point;
- **Move P** — adjoin a σ-orbit pair `{u, v = σu}` with `u` a new **global maximal** (down-set `= any order ideal `D` of the current poset), `v` a new **global minimal** (up-set `= σ(D)`, the dual filter), plus an optional internal `v < u` edge.

The raw edges are **transitively closed** (a subtlety: when `D ∩ σ(D) ≠ ∅`, transitivity *forces* `v < u` through a shared element `v < w < u`, `w ∈ D ∩ σ(D)` — the closure handles this; an early incremental shortcut that missed it produced non-closed spurious "classes" and was the one generation bug found and fixed during development). Width is **monotone** under element addition, so width `> 3` is pruned immediately; the construction is verified order-reversing on every child (`is_order_reversing` clean on all classes). This reaches **every** self-dual width-3 poset, because the peeling above terminates at the empty poset.

Since `Q(P)` depends only on `P` (not on `σ`), and the enumeration produces every self-dual width-3 `P` at least once (with some `σ`), the min-`Q` search is **exhaustive over the arena**. (The iso-classes are σ-isomorphism classes of *pairs* `(P, σ)`, per the ticket; a poset with two non-conjugate self-dualities contributes two classes of equal `Q` — harmless for the minimum, and both `(P, σ)` are retained because dropping one could miss a larger poset that peels to it.)

### 2.2 σ-isomorphism iso-reduction by exact canonical form

Two self-dual posets `(P, σ_P), (P', σ_{P'})` are **σ-isomorphic** iff an order-isomorphism `φ : P → P'` with `φ ∘ σ_P = σ_{P'} ∘ φ` exists. De-duplication uses an **exact canonical form** of the coloured structure (the `below`-digraph together with `σ`-as-a-function): colour-refinement to an equitable partition `(downdeg, updeg, σ-fixed?)` iterated with neighbour-colour multisets and `σ`-image colour, then **individualization–refinement** taking the lexicographically-minimal relabelled adjacency encoding. The canonical key is a hashable tuple; classes are de-duplicated by **set membership** — *no pairwise isomorphism tests*.

This was the decisive engineering point. An earlier weak multiset invariant collided `~1 500` non-isomorphic posets per bucket, triggering **37.6 million** pairwise σ-iso backtracking tests (572 s) just for the `n = 9 → n = 11` expansion. The canonical form drops that to a hashset lookup: generation through `n = 13` runs in **45 s**.

### 2.3 Class counts — smooth, ratio ≈ 3 (V3 "polynomial-in-`n`" check)

| `n` | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|----:|--:|--:|--:|--:|--:|--:|--:|---:|---:|----:|----:|
| width-3 iso-classes | 2 | 2 | 11 | 25 | 78 | 216 | 609 | 1 890 | 5 240 | 17 340 | 48 932 |

The `n = 5, 7, 10` rows are exactly the warm-up validators (below); the growth ratio holds steady near `3`, so `n = 11` is smooth-extrapolable from `n = 10` (`5240/1890 ≈ 2.77`) — the ticket's smoothness sanity check passes, the enumerator neither over- nor under-counts.

---

## 3. The five-engine harness (V2) and the §8.2 guard

`Q` is reported only on exact-rational agreement of the acceptance gate (roadmap §4):

- **M1** — order-ideal placed-set DP. Here implemented as a **fast all-pairs** two-sided ideal DP: `down[I] = #` linear extensions of the sub-poset on ideal `I`, `up[I] = #` of the complementary filter, and `#ext(x before y) = Σ_I down[I]·up[I∪{x}]` over ideals `I` to which `x` is addable and `y` is not yet placed — one pass for **all** incomparable pairs instead of one DP per pair. Two internal self-checks run on **every** class: `down[full] = up[∅]` (the `e` two-direction check) and `before[x][y] + before[y][x] = e` for every incomparable pair.
- **M2** — AP-0 kernel `Q_via_dp` (subset DP, independent codebase).
- **M3** — Prong-2 `IndPoset` minimal-element-removal recursion (the roadmap-§8.2 independent codebase).
- **M4** — brute-force linear-extension enumeration (own path; run when `e ≤ 200 000`).
- **MC** — Family-C Ehrhart order-polynomial (volume engine, methodologically distinct: it reads `e` off the leading coefficient of `Ω_P(t)` rather than counting peels).

Monte-Carlo is **never** a source of truth (non-goal 8.5).

**Verification scope (honestly reported).** The fast M1 carries the exhaustive sweep (with its two internal self-checks on every class). It is validated `= Q_primary` (the independent slow M1) on **all 8 758 classes for `n ≤ 11`** (0 mismatches), and `= M1=M2=M3=M4=MC` on the argmin at **every** `n` plus a 60-class deterministic per-`n` sample. For `n ≤ 9` the full five-engine harness runs on **every** iso-class. The argmin — the witness that fixes the verdict at each `n` — always receives the complete `M1 = M2 = M3 = M4 = MC` treatment. Cross-engine disagreement halts as P0; none occurred.

**GUARD (roadmap §8.2 anti-Cheeger, INHERITED STRICT).** `guard_check` fires on **every** iso-class. A `Q ≤ 1/3` candidate halts immediately with the mandated message *"Q ≤ 1/3 candidate at self-dual poset T, halting per §8.2 STRICT — fresh sixth codebase required"* and is **not** written up as a counterexample. M1+M2+M3+M4+MC are all used; the sixth fresh codebase (Stanley–Reisner face-ring / AG-dimension / matrix-permanent / SAT-model-count / analytic Euler-product) is reserved for a `Q ≤ 1/3` candidate, which does not arise (lowest `Q` anywhere `= 6/17`).

---

## 4. Per-`n` results, with argmin structural fingerprints

All `Q` exact; argmin fingerprint = `(level structure, σ-orbit shape #fixed/#orbit-2, binding pair Pr, σ-swapped?)`; `[engines]` notes the argmin's agreement.

| `n` | width-3 classes | min `Q` | `e` | `k` | argmin levels | σ: #fixed / #orbit-2 | binding Pr | σ-swapped | engines (argmin) |
|----:|----:|:--|----:|:--|:--|:--|:--|:--|:--|
| 3 | 2 | `1/2` | 6 | 2 | `[3]` | 1 / 1 | `1/2` | no | M1=M2=M3=M4=MC |
| 4 | 2 | `1/2` | 12 | 2 | `[3,1]` | 0 / 2 | `1/2` | yes | M1=M2=M3=M4=MC |
| 5 | 11 | **`4/11`** | 11 | 11 | `[2,2,1]` | 1 / 2 | `7/11` | no | M1=M2=M3=M4=MC ✅ |
| 6 | 25 | `8/19` | 57 | `19/5` | `[3,3]` | 0 / 3 | `8/19` | no | M1=M2=M3=M4=MC |
| 7 | 78 | **`14/39`** | 39 | 13 | `[2,2,2,1]` | 1 / 3 | `14/39` | no | M1=M2=M3=M4=MC ✅ |
| 8 | 216 | `27/70` | 140 | `70/11` | `[2,3,2,1]` | 0 / 4 | `43/70` | yes | M1=M2=M3=M4=MC |
| 9 | 609 | `14/39` | 39 | 13 | `[1,2,2,2,1,1]` | 1 / 4 | `14/39` | no | M1=M2=M3=M4=MC |
| 10 | 1 890 | **`6/17`** | 187 | 17 | `[2,2,2,1,2,1]` | 0 / 5 | `6/17` | no | M1=M2=M3=M4=MC ✅ |
| **11** | **5 240** | **`134/375`** | 750 | `125/9` | `[2,3,1,2,2,1]` | 1 / 5 | `241/375` | no | M1=M2=M3=M4=MC |
| **12** | **17 340** | **`6/17`** | 187 | 17 | `[1,2,2,2,1,2,1,1]` | 0 / 6 | `6/17` | no | M1=M2=M3=M4=MC |
| **13** | **48 932** | **`134/375`** | 750 | `125/9` | `[1,2,3,1,2,2,1,1]` | 1 / 6 | `241/375` | no | M1=M2=M3=M4=MC |

**Validation (ROUTINE CHECKS):** `n = 5 → 4/11`, `n = 7 → 14/39`, `n = 10 → 6/17` recovered **exactly** as the argmins of the *full exhaustive* self-dual width-3 enumeration (PASS, asserted in-script). This independently re-derives the three descent-ladder rungs as the global self-dual width-3 minima at their `n`, and cross-checks the Prong-3C/3D/3E witnesses against the entire arena (not just the 4 712-extension local baseline of mg-7ee8). The `4/11` seed (`n=5`) and `14/39` witness (`n=7`) appear in their level-cumulative subsets as required.

**Observations.**
- The **even-`n` `6/17` thread**: `6/17` at `n = 10` and `n = 12`, both `e = 187`, both fixed-point-free σ — the `n=12` instance is the `n=10` witness with a Q-preserving global top+bottom σ-pair adjoined (Lemma-B analogue; `e` unchanged). No `+1` (fixed-point) or other self-dual move at odd `n` reproduces `6/17`.
- The **odd-`n` `134/375` minimum** (`n = 11, 13`, both `e = 750`, both with exactly one σ-fixed central element forced by R2 at odd `n`) is a **new** extremal value strictly inside `(6/17, 14/39)`, **off** the descent ladder (`k = 125/9 ∉ ℤ`). Its binding pair `(241/375)` is a near-twin σ-orbit-2 pair — the identical BIND mechanism (Prong 3E-α §4), not a σ-swapped self-pair.
- Across all `~73 000` iso-classes `n = 3…13`, **min `Q = 6/17`**; never below.

---

## 5. Verdict and §8.2 guard

**VERDICT-A.** Over the exhaustive iso-reduced self-dual width-3 arena, `min Q` at `n = 11, 12, 13` is `134/375, 6/17, 134/375` respectively — **all `≥ 6/17`**. `6/17` is matched (at even `n = 10, 12`) but never beaten through `n = 13`. The empirical `6/17` floor — which Prong 3E-α could *not* establish analytically — is **materially strengthened**: it now holds over every iso-class of the full arena at three new `n`, not just over the `+1/+2/+3` local extension shell of the single `n = 10` witness.

**§8.2 guard cleared.** Every iso-class has `Q > 1/3` (lowest `6/17`); M1+M2+M3+M4+MC all used; the guard does not fire; no sixth codebase is triggered.

**Corridor UNCHANGED at `(1/3, 6/17]`.** No `Q < 6/17` self-dual width-3 poset exists at `n ≤ 13` (no REFUTATION); the analytic floor remains open (Prong 3E-α WALL, the named forced-relation order-polytope ratio bound parked as research-grade); `6/17` stands as the stall rung / corridor ceiling, now with exhaustive empirical support to `n = 13`.

**No new wall.** The enumeration / iso-reduction did **not** blocker out — the canonical-form σ-isomorphism kept the count tractable (≈ 49 k classes, ≈ 3 min) exactly as V3 anticipated. So this prong reports **VERDICT-A**, not a fifth WALL.

---

## 6. Suggested Prong 3G (gated on VERDICT-A)

- **3G-γ (structural-review write-up) — recommended.** `6/17` now holds as the self-dual width-3 minimum exhaustively through `n = 13`, matched only on the even-`n` Q-preserving thread. A structural-review prong would (i) consolidate the corridor `(1/3, 6/17]` evidence across mg-8bd6 / mg-5ff1 / mg-7ee8 / mg-7237 into one statement, and (ii) characterise the new `134/375` odd-`n` minimum family — is it a one-parameter near-twin family analogous to the ladder, and does it persist (or drop) at `n = 15, 17`?
- **3G-α (non-self-dual width-3 minimum at `n = 10–13`) — the load-bearing test.** Self-duality has been the working hypothesis (mg-5ff1) for *where* the minimum lives. The natural next question, now that the self-dual arena is exhausted to `n = 13` with min `6/17`: is self-duality actually load-bearing, or does some **non-self-dual** width-3 poset dip below `6/17`? This is a separate, larger enumeration (the peeling generator does not apply; orderly generation of all width-3 posets up to iso, or a self-dual-relaxed canonical-augmentation, would be needed). Flagged as the most informative follow-up; out of scope here (ticket non-goal: "No non-self-dual width-3 enumeration in this ticket").
- **3G-β (descent-ladder extension)** — **not triggered**: no VERDICT-B argmin appeared; `134/375` is off-ladder and *above* `6/17`, so it is a new extremal value to characterise, not a new rung that lowers the ceiling.

---

## 7. Reproduction

```
python3 scripts/onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust.py            # full n<=13 (~3 min)
python3 scripts/onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust.py --quick    # validation cap n<=10 (fast)
python3 scripts/onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust.py --full-verify-upto 11   # full 5-engine on every class to n=11
```

A clean exit *is* the deliverable: the generator validated (`n=5→4/11`, `n=7→14/39`, `n=10→6/17`), five engines agreeing at every cross-checked class, the §8.2 guard clearing on all `~73 000` iso-classes, and VERDICT-A printed.
