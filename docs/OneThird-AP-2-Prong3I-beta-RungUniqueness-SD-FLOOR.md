# OneThird AP-2 Prong 3I-β: Rung-Uniqueness for SD-FLOOR — closing T7's correct conditional at the ladder n ∈ {5, 7, 10}

**Work item:** mg-f111
**Date:** 2026-05-30
**Status:** **STRONG. Rung-uniqueness PROVED at all three descent-ladder rungs n ∈ {5, 7, 10} by exhaustive extreme-reduced width-3 enumeration: |M₅| = |M₇| = |M₁₀| = 1, each minimizer self-dual. SD-FLOOR is therefore UNCONDITIONALLY proved at the ladder n's via Theorem SD-UNIQ, and T7's correct conditional closes to an arc-wrap statement at every floor-attaining n.**

Headline in one paragraph. Prong 3I-α (mg-f6d3) refuted the over-strong per-n self-dualization hypothesis (off-floor at n=6, a benign non-self-dual dual pair at Q=15/37) but isolated the **correct** floor-relevant residual **SD-FLOOR** (at every n where the global floor q\* is attained, M_n contains a self-dual class) and proved the **Q dual-invariance gateway** SD0 → SD1 → SD-UNIQ → SD-PARITY. This prong closes the SD-FLOOR residual at the three known descent-ladder rungs. By **exhaustive** enumeration of the extreme-reduced **width-exactly-3** sub-arena at n = 5, 7, 10 (arenas of 20, 749, 294 982 isomorphism classes), the per-level Q floor is attained by a **unique** iso-class at each rung — `|M₅| = |M₇| = |M₁₀| = 1` — and that unique minimizer is self-dual (e = 11, 39, 187 respectively; the descent-ladder rungs 4/11, 14/39, 6/17). By Theorem **SD-UNIQ** (|M_n| = 1 ⟹ the minimizer is self-dual), rung-uniqueness holds at all three rungs, so **SD-FLOOR is unconditionally proved at the ladder n's**. In particular at n = 10, where q\*(10) = 6/17 equals the global width-3 floor, the extreme-reduced minimizer set is the single self-dual e=187 class — the carry-forward mg-5406 witness, now confirmed **unique within the extreme-reduced sub-arena** by an independent from-scratch canonical-augmentation enumeration. T7's correct conditional becomes a closed arc-wrap statement at every floor-attaining n: full-arena floor → (T7) → extreme-reduced floor → (rung-uniqueness, SD-UNIQ) → self-dual floor.

---

## Vision Alignment (V2 + V3 + V4) — verbatim from the ticket

> **V2 (computable Q):** leverages the gadget identity Pr[x<y_i] = i/(t+1) (Prong 3D-alpha) + Stanley closed-form Pr[x<y] = e(P+x<y)/e(P) + the new SD0 Q dual-invariance + the new SD-UNIQ + SD-PARITY rigidity. All five together give the analytic toolkit for rung-uniqueness.

> **V3 (parameter space):** extreme-reduced width-3 sub-arena at floor-attaining n in {5, 7, 10}. The M_n cardinality / parity question is finite and combinatorially explicit.

> **V4 (sharpness-or-pivot signal):**
> - STRONG: prove rung-uniqueness for all three rungs n in {5, 7, 10}. SD-FLOOR unconditionally proved at ladder n's. T7's correct conditional closes. The arc reaches genuine arc-close on the analytic floor question.
> - PARTIAL: prove rung-uniqueness for 1 or 2 rungs; named residual for the others.
> - REFUTATION: at some n in {5, 7, 10}, |M_n| is even AND no self-dual class — would force re-opening the SD-FLOOR question. Mayor's empirical baseline says |M_5|=|M_7|=1 confirmed; |M_10| not yet checked but mg-5406 found the 6/17 witness self-dual.
> - WALL (Outcome 4): rung-uniqueness stalls structurally — name the missing combinatorial input.

**Which V4 branch fired: STRONG.** Rung-uniqueness is proved for **all three** rungs n ∈ {5, 7, 10}: `|M_n| = 1` at each (exhaustive enumeration, §3), so by SD-UNIQ each minimizer is self-dual, so **SD-FLOOR holds unconditionally at the ladder n's** and **T7's correct conditional closes** at every floor-attaining n. On **V2**, the verdict is delivered by the full toolkit: the Stanley ratio Pr[x<y] = e(P+x<y)/e(P) computes every balance exactly (no Monte Carlo); SD0 dual-invariance Q(P)=Q(P\*) is re-confirmed (including on the n=6 refutation witness, Q=15/37); SD-UNIQ converts the counting fact |M_n|=1 into self-duality; the gadget identity Pr[x<y_i]=i/(t+1) explains the rung geometry (the binding near-twin pairs). On **V3**, the extreme-reduced width-exactly-3 sub-arena is enumerated **exhaustively** up to iso at each rung n (arenas 20 / 749 / 294 982); the |M_n| question is settled as a finite, explicit count. The §8.2 anti-Cheeger STRICT guard does **not** fire: every Q encountered is ≥ 6/17 > 1/3, so no sixth codebase is triggered.

---

## 1. Setup and definitions (carry-forward, Prong 3I-α §1)

- **Poset** P on {0,…,n−1}; `<` strict order. **Width** w(P) = longest antichain. Arena: **width exactly 3**.
- **e(P)** = number of linear extensions. For incomparable (x,y): **Pr[x<y] = e(P+(x<y))/e(P)** (Stanley 1986 order-polytope ratio).
- **balance(x,y) = min(Pr[x<y], Pr[y<x]) ∈ [0,1/2]**. **Q(P) = max over incomparable (x,y) of balance(x,y)** — the *best* balance.
- **Order dual** P\*: x <\_{P\*} y ⟺ y <\_P x (Stanley reversal). **Self-dual**: P ≅ P\*.
- **Extreme-reduced**: P has neither a global maximum nor a global minimum (equivalently ≥ 2 maximal **and** ≥ 2 minimal elements).
- **𝓔₃(n)** = extreme-reduced width-**exactly-3** posets on n elements; **q\*(n) = min over 𝓔₃(n) of Q**; **M_n = { P ∈ 𝓔₃(n) : Q(P)=q\*(n) }** as a set of iso-classes — the **per-n extreme-reduced minimizers**.
- **Global floor** q\* = inf over n of q\*(n) = the descent-ladder minimum = the width-3 floor (= 6/17, attained at n = 10).

**The descent ladder (Prong 3C/3D).** The three minimum-Q width-3 witnesses lie on one Diophantine ladder `Q = (k+1)/(3k) = 1/3 + 1/(3k)`, binding-pair `Pr = (2k−1)/(3k) → 2/3`, with integral rungs:

| rung | n | k | q\*(n) | e | binding Pr |
|---|---:|---:|---|---:|---|
| seed | 5 | 11 | **4/11** ≈ 0.36364 | 11 | 7/11 |
| — | 7 | 13 | **14/39** ≈ 0.35897 | 39 | 25/39 |
| floor | 10 | 17 | **6/17** ≈ 0.35294 | 187 = 11·17 | 11/17 |

q\*(10) = 6/17 is the **global** floor; n = 5, 7 are floor-attaining only relative to their own n (their q\*(n) lies above 6/17 but each is the deepest value first appearing at that n, i.e. the per-level minimum on the descent ladder).

---

## 2. The rung-uniqueness statement and the gateway it feeds (carry-forward gateway, Prong 3I-α §3)

**Definition (rung-uniqueness at n).** The per-n extreme-reduced minimizer set M_n satisfies `|M_n| = 1` **or** `|M_n|` is odd.

The gateway theorems (all proved unconditionally in Prong 3I-α, re-used here):

- **Lemma SD0 (Q dual-invariance).** Q(P) = Q(P\*) for every finite poset. *(Stanley reversal λ ↦ λ^rev is an involutive bijection of linear extensions; e(P)=e(P\*); balance preserved pairwise.)*
- **Corollary SD1 (dual-closure of M_n).** Dualization maps M_n to M_n. Writing M_n = S_n ⊔ N_n (self-dual ⊔ non-self-dual classes), dualization is a fixed-point-free involution on N_n, so **|N_n| is even**.
- **Theorem SD-UNIQ.** If |M_n| = 1, the unique minimizer is self-dual. *(M_n = {[P]}; SD1 ⟹ [P\*] ∈ M_n = {[P]} ⟹ P\* ≅ P.)*
- **Theorem SD-PARITY.** If |M_n| is odd, then |S_n| ≥ 1 (a self-dual minimizer exists). *(|N_n| even ⟹ |S_n| = |M_n| − |N_n| odd ≥ 1.)*

**Consequence.** Rung-uniqueness at n (|M_n| = 1, or |M_n| odd) ⟹ M_n contains a self-dual class ⟹ SD-FLOOR holds at n. So proving rung-uniqueness at every floor-attaining ladder n closes the SD-FLOOR residual at those n.

---

## 3. Exhaustive enumeration result (script: onethird_ap2_prong3i_beta_rung_uniqueness_verify.py)

**Method.** Width-≤3 posets on n elements are generated **up to order-isomorphism** by **canonical augmentation**: build level by level, adding one element at a time as a new **maximal** element whose strict-lower set is an order ideal of the current poset; dedup each level by a canonical form (color-refinement + color-respecting backtracking, which keeps the search tiny since width-3 color classes are small). Width-≤3 is kept *during* augmentation (so a width-2 parent that grows into a width-3 child is not pruned); the **arena** is then filtered to **width exactly 3** (width-2 posets — e.g. the textbook point ∥ 2-chain Q=1/3 gadget — are a different regime and are excluded) **and** extreme-reduced. For each arena poset, Q is computed via the Stanley ratio with **early rejection**: scanning the incomparable pairs, the moment one has balance exceeding the running floor the poset is discarded (it cannot be a minimizer), so the vast majority cost only one or two linear-extension counts. The collected minimizers are reduced to iso-classes and tested for self-duality.

**Generator completeness — independently cross-validated.** Canonical augmentation by "add a new maximal element over an order ideal" is complete (every poset on k+1 elements has a maximal element whose removal leaves a poset on k elements). To rule out a canonical-form bug (under- or over-counting), the generator's arena count was cross-checked against a **completely independent** brute enumeration (all transitively-closed upper-triangle relation subsets, filtered to width-exactly-3 + extreme-reduced, deduped by an n! canonical form): the two agree exactly at **n=5 (20)** and **n=6 (117)**, confirming the generator neither conflates nor duplicates iso-classes.

**Engines / rigour.** e(P) and every e(P+x<y) are cross-checked on each minimizer by **two independent linear-extension engines** — E1 (downset/order-ideal DP) and E3′ (maximal-element-deletion recursion) — and, for n ≤ 8, additionally the E2 full n! permutation count. Monte Carlo is never a source of truth. (These correspond to the M1 / M3 / M4 members of the standard five-engine verify_C harness; M2 Q_via_dp and MC Ehrhart corroborate the same rung witnesses in mg-5ff1 / mg-7ee8 / mg-6728.)

### Result table

| n | arena \|𝓔₃(n)\| | q\*(n) | \|M_n\| | self-dual | e(P) | rung-uniqueness |
|---:|---:|---|---:|:--|---:|---|
| 5 | 20 | **4/11** | **1** | **yes** | 11 | **closes** (SD-UNIQ, \|M\|=1) |
| 7 | 749 | **14/39** | **1** | **yes** | 39 | **closes** (SD-UNIQ, \|M\|=1) |
| 10 | 294 982 | **6/17** | **1** | **yes** | 187 | **closes** (SD-UNIQ, \|M\|=1) |

(Generation passes through the width-≤3 iso-class levels 2/5/15/55/245/1 285/7 790/53 108/397 222 at n=2..10; the n=10 arena of 294 982 is the width-exactly-3 + extreme-reduced restriction of the 397 222 width-≤3 classes.) Every minimizer passed the SD0 check Q(P) = Q(P\*) and the E1/E3′(/E2) engine cross-check. The unique minimizer Hasse diagrams (cover relations on {0,…,n−1}, as produced by the from-scratch enumeration; labels are arbitrary up to iso):

```
n=5  (4/11,  e=11):   0<4; 1<2; 1<3; 3<4
n=7  (14/39, e=39):   0<4; 0<5; 1<2; 1<3; 2<6; 3<4; 3<5; 5<6
n=10 (6/17,  e=187):  0<4; 0<5; 1<2; 1<3; 2<4; 2<8; 3<5; 4<9; 5<6; 6<7; 6<8; 7<9
```

These are order-isomorphic to the carry-forward rung witnesses of Prong 3C/3D (same e ∈ {11, 39, 187}, same Q on the descent ladder, all self-dual). The n=10 class is the mg-5406 6/17 witness — here confirmed to be the **unique** Q-minimizer of the **extreme-reduced** width-3 sub-arena (mg-5406 classified the full arena; this prong settles the extreme-reduced sub-arena directly).

### Sanity re-confirmations (Prong 3I-α facts)
- **n=6 REFUTATION witness** C (covers 0<2, 0<4, 0<5, 1<3, 1<4, 2<3): e(C)=37 by both E1 and E3; Q(C)=Q(C\*)=15/37 (SD0 holds); C not self-dual and C ≇ C\* — the benign off-floor dual pair predicted by SD1. ✓
- **n=5** floor minimizer is the (4/11) self-dual seed; **n=7** floor minimizer is the (14/39) self-dual witness — both unique, re-confirming mg-f6d3's empirical |M₅|=|M₇|=1. ✓

---

## 4. SD-FLOOR closure status at the ladder n's

**SD-FLOOR is UNCONDITIONALLY proved at every known descent-ladder rung n ∈ {5, 7, 10}.** At each rung the extreme-reduced width-3 minimizer set is a singleton (|M_n| = 1), so by Theorem SD-UNIQ the unique minimizer is self-dual; hence M_n contains a self-dual class, which is exactly SD-FLOOR at n. In particular:

- **n = 10 (the global floor, q\* = 6/17):** |M₁₀| = 1, the self-dual e=187 class. SD-FLOOR holds at the value-attaining n of the **global** width-3 floor. This is the load-bearing rung — it is where the corridor ceiling 6/17 is attained — and it is now closed by an independent exhaustive enumeration (arena of 294 982 extreme-reduced width-3 iso-classes), not carried forward as a single reported argmin.
- **n = 5, 7 (per-level floors above the global floor):** |M_n| = 1, self-dual; SD-FLOOR holds at these rungs too.

**T7's correct conditional closes to an arc-wrap statement at the ladder n's.** T7 (Prong 3H-α) gives unconditionally `inf over width-3 = inf over extreme-reduced width-3`. The further reduction to the self-dual core needs SD-FLOOR. At every floor-attaining ladder n the chain now reads, with **no** conditional link:

```
full-arena floor  →(T7, unconditional)→  extreme-reduced floor  →(rung-uniqueness |M_n|=1, SD-UNIQ)→  self-dual floor.
```

So at n ∈ {5, 7, 10} the reduction "self-dual-core floor ⟹ full-arena floor" holds **outright**. The remaining open content is not at these rungs: it is (a) whether the ladder has any **further** rungs at n ≥ 12 (parked, HPC; out of scope per NON-GOALS), in which case rung-uniqueness would have to be re-established there, and (b) the still-open analytic floor inequality itself (Missing Input B). What this prong delivers is the **complete** closure of the SD-FLOOR residual across **all currently known** floor-attaining n.

**Scope honesty.** "SD-FLOOR unconditionally proved at the ladder n's" means: at each of the three n where the descent ladder is known to touch its per-level minimum, the extreme-reduced minimizer is unique and self-dual. It does **not** claim SD-FLOOR for hypothetical higher rungs (none are known; the ladder stalls at k=17 under all searches to date, Prong 3D/3E), and it does **not** prove the floor inequality Q ≥ 6/17 itself (that is Missing Input B, research-grade, untouched here per NON-GOALS).

---

## 5. Guard, non-goals, achieved result

**§8.2 anti-Cheeger STRICT guard — cleared.** Every Q encountered across all three exhaustive arenas is ≥ 6/17 > 1/3 (the per-level floors are 4/11, 14/39, 6/17). No Q ≤ 1/3 candidate arises, so the M1–M4 + MC engine family suffices and **no sixth fresh codebase is triggered**. (The extreme-reduced restriction excludes the adjunction-extension Q=1/3 textbook gadgets, which require a global extreme; consistent with the low-risk note in the ticket guard.)

**NON-GOALS respected.** No Cheeger / cut-and-window; no Q ≤ 1/3 claim; no Lean / LaTeX / main.tex; Monte Carlo never source of truth; no Family A/B/C/D re-sweep; no t-dilation argument; no HPC n ≥ 12 sweep; no Q ≥ 6/17 floor attack (Missing Input B untouched); no re-attack on the refuted literal SD-perN.

**Achieved result.** **STRONG.** Rung-uniqueness `|M_n| = 1` proved by exhaustive extreme-reduced width-exactly-3 enumeration at all three descent-ladder rungs n ∈ {5, 7, 10}; each unique minimizer self-dual (SD-UNIQ). **SD-FLOOR unconditionally proved at the ladder n's; T7's correct conditional closes** at every floor-attaining n. The independent from-scratch canonical-augmentation enumeration (cross-validated against brute force at n=5, 6) confirms the mg-5406 6/17 witness is the unique extreme-reduced minimizer at n=10 (arena of 294 982 iso-classes). Corridor unchanged at (1/3, 6/17].

---

## 6. Suggested Prong 3I-γ brief (gated on this STRONG verdict)

With SD-FLOOR closed at all known ladder n's, the self-dual-core reduction is now in force wherever the floor is currently known to be attained. The honest next steps, in priority order (recommendations only; no `mg new` called here):

1. **3I-γ (recommended) — attack Missing Input B on the now-justified self-dual core.** SD-FLOOR (this prong) + T7 + SD0-orbit reduction (R1) now legitimately reduce the full-arena floor question, *at the ladder n's*, to the self-dual core. The remaining mathematical content is the forced-relation order-polytope ratio bound `6/17·e(P) ≤ e(P+x<y) ≤ 11/17·e(P)` on the near-twin σ-orbit class of extreme-reduced self-dual width-3 posets (Prong 3E-α §5 / 3H-α §5). This is research-grade and a special case of the open width-3 sharpness problem; a polecat-sized sub-step is to prove it on the **σ-fixed central / orbit-2 near-twin** structure that all three rungs exhibit (the gadget identity calibrates the single-strand balances; the three-strand ratio is the gap).
2. **3I-γ′ (cheap rigour) — map the non-self-dual interior band.** Extend the exhaustive extreme-reduced enumeration to n = 8, 9 (the width-≤3 generation already reaches 7 790 / 53 108 iso-classes there in ≈ 15 s; the extreme-reduced width-3 filter + min-finding is feasible offline in minutes) to chart which interior n carry non-self-dual dual-pair minima (like n=6's 15/37) and confirm none dips to or below 6/17. This strengthens SD-FLOOR empirically across the interior and verifies the "off-floor non-self-dual band stays above the corridor ceiling" picture.
3. **3I-γ″ (HPC, parked) — full-arena n = 12, 13 exhaustion.** Would test whether any further descent-ladder rung exists below n's already swept; if one appears, rung-uniqueness must be re-established there. HPC required; out of polecat scope per NON-GOALS.

---

## Reuse / Artifacts
- Verifier + enumerator: `scripts/onethird_ap2_prong3i_beta_rung_uniqueness_verify.py` — SD0/SD1/SD-UNIQ/SD-PARITY kernel, n=6 refutation sanity, canonical-augmentation extreme-reduced width-exactly-3 enumeration (color-refinement canonical form, cross-validated against brute force at n=5, 6), early-rejection minimizer finder, two-engine (E1/E3′, +E2 for n≤8) cross-check on every minimizer. Run `--rungs 5,7` for the fast pair (~0.2 s); add `10` for the full run (~2 min: ~95 s generation + ~70 s minimizer scan).
- Carry-forward: SD0/SD1/SD-UNIQ/SD-PARITY + n=6 refutation (mg-f6d3); T6/T7 extreme adjunction + reduction (mg-6728); R1/R2/Lemma W σ-orbit machinery (mg-7ee8); gadget identity + ladder self-duality (mg-5ff1); 6/17 witness + descent ladder (mg-8bd6); full-arena argmin classification (mg-5406); self-dual exhaustive (mg-7237).
```
