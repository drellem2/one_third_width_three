# OneThird — AP-2 Prong 3D-α: the constructive descent ray (k-jump) — does the Q = 1/3 + 1/(3k) ladder extend past k = 17?

*Work item **mg-5ff1**. Follow-up to mg-8bd6 (Prong 3C), which REFUTED the 14/39 width-3 floor with an exact, five-engine-verified width-3 poset at n = 10 with Q = 6/17 ≈ 0.3529 (binding pair (3,9), Pr = 11/17, e = 187), narrowing the live counterexample-hunt corridor to (1/3, 6/17], and discovered the DESCENT LADDER `Q = 1/3 + 1/(3k) = (k+1)/(3k)`, binding-pair `Pr = (2k−1)/(3k) → 2/3`, with three integral rungs k = 11 (n=5, 4/11), 13 (n=7, 14/39), 17 (n=10, 6/17). Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3C-Width3-FloorBound.md`](OneThird-AP-2-Prong3C-Width3-FloorBound.md) (the REFUTATION + the descent ladder + the near-twin-pair mechanism + the n=8 plateau debunking); [`OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md`](OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md) (the 4/11 seed + the Ehrhart engine + the Wall Lemma §3.2 t-dilation Q-invariance); [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the 8/21 analytic theorem; the structural template for a STALL analytic argument); [`OneThird-AP-2-Prong1-SelfDual-LowerBound.md`](OneThird-AP-2-Prong1-SelfDual-LowerBound.md) (the self-dual lens, now relevant); [`OneThird-AP-2-Prong2-FamilyB-SP-Probe.md`](OneThird-AP-2-Prong2-FamilyB-SP-Probe.md); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§6, 8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3d_alpha_descent_verify.py`](../scripts/onethird_ap2_prong3d_alpha_descent_verify.py) — reuses the mg-8bd6 / mg-3b16 five-engine harness (M1 order-ideal DP, M2 AP-0 kernel, M3 minimal-element-removal recursion, M4 brute permutations, MC Ehrhart order-polynomial) verbatim, and adds: the order-reversing-involution finder (the self-duality witness), the jump-operator-attempt constructors (the overshooting families + the closed-form gadget identity `Pr[x<y_i] = i/(t+1)`), the exhaustive self-dual local-floor scan at the 6/17 witness, and the ladder-rung Q checker. Clean run ≈ a few seconds; a clean exit is the five-engine agreement + ladder identities + self-duality + overshoot + self-dual local-floor + guard clearing.*

---

## 0. Headline

**VERDICT: Outcome-4 clean diagnosis + WEAKER finite-stall. No jump operator extends the ladder past k = 17.**

The constructive descent ray does **not** extend the ladder. Three lines of evidence, all exact:

1. **NEW STRUCTURAL FINDING — the ladder is self-dual.** All three rung witnesses are **self-dual width-3 posets** (each admits an order-reversing automorphism σ), and the near-twin binding pair is the **σ-orbit pair**:

   | rung | n | Q | order-reversing automorphism σ |
   |---:|---:|---|---|
   | 4/11 (k=11) | 5 | (k+1)/(3k) | `(a0 c0)(b1 b2)(b0)` — central element b0 σ-fixed |
   | 14/39 (k=13) | 7 | (k+1)/(3k) | `(0 6)(1 5)(2 4)(3)` — the order reversal, 3 fixed |
   | 6/17 (k=17) | 10 | (k+1)/(3k) | `i ↔ i+5 (mod 10)` — fixed-point-free |

   Self-duality is the hidden symmetry of the descent ladder; the descent lives in the **self-dual width-3 subspace**.

2. **The naive jump-operator candidates OVERSHOOT.** Every one-parameter stretch of a witness (lengthen the central chain up or down; lengthen the heavy twin's chain) leaves the ladder *immediately*: `3Q−1` ceases to be `1/integer` and Q rises toward `1/2`, not down toward `1/3`. The closed-form reason is the gadget identity, for a point x parallel to a t-chain `y_1 < ⋯ < y_t`,
   ```
   Pr[x < y_i] = i/(t+1).
   ```
   The textbook gadget **t = 2 is the unique chain length** whose incomparable pairs sit at exactly `{1/3, 2/3}` with **no** middle pair (giving Q = 1/3); for `t ≥ 3` a middle pair `Pr ≈ 1/2` appears and Q jumps up. So "lengthen a chain" cannot descend the ladder — it manufactures a balanced side pair. This is the analytic core of why the constructive families fail.

3. **6/17 is a strict self-dual local floor.** Exhaustively over every width-3 **self-dual** extension of the 6/17 witness by one σ-symmetric move:
   - **+1** (a σ-fixed central element): all **10** width-3 cases → min Q = **4/11** (overshoots up);
   - **+2** (a σ-symmetric pair): all **163** width-3 cases → min Q = **6/17**, attained **only** by the e-preserving global-top/global-bottom adjunction (e unchanged at 187, the order-polytope analogue of Prong-3A Lemma B "series = max"); every **e-increasing** self-dual move has Q > 6/17.

   So no self-dual local move beats 6/17. Together with Prong 3C's beam + anneal stall to n ≤ 14, the descent ladder is — as far as construction and exhaustive local / self-dual search reach — a **three-rung phenomenon** (k = 11, 13, 17).

**The corridor is UNCHANGED at (1/3, 6/17].** This prong exhibits no Q < 6/17, so it neither proves `inf Q = 1/3` (PRIMARY/STRONGER not reached) nor proves a floor `Q ≥ 6/17` (the Prong-3E target, not claimed here). It is a clean negative diagnosis of the constructive route, with the self-duality + overshoot mechanism + the exhaustive self-dual local-floor as the structural content. `6/17` stands as the **stall rung / corridor ceiling**.

**§8.2 anti-Cheeger guard (INHERITED STRICT) does NOT fire.** Every Q encountered is `> 1/3` (lowest anywhere is 6/17); no `Q ≤ 1/3` candidate arises, so M1–M4 + MC suffice and **no sixth codebase is triggered** (that trigger is reserved for a `Q ≤ 1/3` claim).

---

## (i) Vision alignment (V2 + V3 + V4) — verbatim from the ticket

- **V2 (computable Q):** *each rung's Q is a closed-form Ehrhart volume ratio e(P_k + x<y)/e(P_k). The ladder identity Q = 1/3 + 1/(3k) gives a parameterised closed form in k. NOT generic DP, NOT Monte-Carlo.*
- **V3 (parameter space):** *k is the algebraic parameter (the integer-denominator-3-k identity). The (n, k) relationship n=5 (k=11), n=7 (k=13), n=10 (k=17) is part of the structural pattern to be made explicit.*
- **V4 (sharpness-or-pivot signal):** *if the ladder extends, conjecture asymptotically sharp at width 3 (program's strongest empirical V4 verdict). If it stalls at k=17, the stall value 6/17 becomes the new corridor ceiling and the stall-mechanism is the analytic target (Prong 3E).*

**Which V4 branch fired:** the **stall** branch. The ladder does **not** extend under construction, exhaustive self-dual local extension, or (per Prong 3C) beam + anneal to n ≤ 14. So `6/17` is confirmed as the **new corridor ceiling**, and the stall mechanism — *self-duality + the unique-t=2-gadget overshoot obstruction* — is made explicit here and handed to Prong 3E as the analytic target. On **V2**, every reported Q is an exact order-polytope volume ratio `e(P+x<y)/e(P)` cross-checked through all five engines (MC = Ehrhart leading coefficient); Monte-Carlo is never a source of truth. On **V3**, the algebraic parameter `k` is pinned by the Diophantine identity `3Q − 1 = 1/k`; the `(n, k)` pattern `(5,11), (7,13), (10,17)` is shown below (§3) to be **not** generated by a clean nesting/stretch operator — the rungs are sporadic self-dual minima, not single-parameter deformations of one another.

---

## 1. Setup, the Q metric, the ladder identity, and the self-dual lens (carry-forward)

For a finite poset P, under the uniform distribution on linear extensions,
```
Q(P) = max over incomparable {x,y} of min( Pr[x<y], Pr[y<x] )
     = 1/2 − min over incomparable pairs of |Pr[x<y] − 1/2|.
```
The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3`; for width 3 it is a **theorem** (the repo's paper, `thm:main`). The **order-polytope identity** (Stanley 1986; mg-3b16 §1) gives every balance as a counting ratio: for incomparable x,y,
```
Pr[x<y] = e(P + x<y) / e(P),     Q(P) = max over incomparable {x,y} of min( e(P+x<y), e(P+y<x) ) / e(P).
```

**The descent ladder (mg-8bd6).** The three minimum-Q width-3 witnesses satisfy the single Diophantine relation `3Q − 1 = 1/k` with k = 11, 13, 17 integral, i.e. `Q = (k+1)/(3k) = 1/3 + 1/(3k)` and binding-pair `Pr = (2k−1)/(3k) → 2/3`. As k → ∞, Q → 1/3⁺. (Note the values are exact as rationals; the underlying e is *not* a clean `3k` — e.g. the 6/17 witness has e = 187 = 11·17, with the binding pair splitting `187 = 66 + 121` and `66/187 = 6/17`. The ladder is an identity on the *value* Q, not a uniform `e = 3k` family — already a hint that the rungs are sporadic.)

**The self-dual lens (this prong's finding).** A poset P is *self-dual* if it admits an order-reversing automorphism σ (a bijection with `a < b ⟺ σ(b) < σ(a)`). Self-dual posets are the natural home of perfectly-balanced extremal examples: σ pairs each incomparable pair `{x,y}` with `{σ(x), σ(y)}` and forces `Pr[x<y] = Pr[σ(y) < σ(x)]`, so the balance spectrum is symmetric about 1/2. **All three ladder witnesses are self-dual** (§0 table, verified in the script by an explicit order-reversing-involution finder), and the near-twin binding pair is the σ-orbit pair. This is the structural template the descent ray must respect.

---

## 2. The three rungs — five-engine + ladder identity (re-verified)

The script re-verifies each rung through all five engines (M1 = M2 = M3 = M4 = MC, exact rational arithmetic) and checks `3Q−1 = 1/k`, `Q = (k+1)/(3k)`:

| rung | elems / cover relations | e | binding pair | Pr | Q | k |
|---|---|---:|---|---|---|---:|
| seed | `a0<b0,b1; b0<c0; b2<c0` | 11 | (b0,b1) | 7/11 | 4/11 | 11 |
| 14/39 | `0<2,0<3,1<4,1<5,2<4,2<5,3<6,4<6` | 39 | (1,2) | 25/39 | 14/39 | 13 |
| 6/17 | `0<2,0<3,1<8,1<9,2<9,3<6,3<8,4<6,4<7,7<5,8<5,9<4` | 187 | (3,9) | 11/17 | 6/17 | 17 |

All exact; the §8.2 guard logs each Q > 1/3 and does not fire.

---

## 3. The jump-operator attempt — why the constructive descent ray fails

### 3.1 The closed-form overshoot obstruction (the analytic core)

The near-twin binding mechanism rests on a single gadget. For a point x parallel to a t-chain `y_1 < ⋯ < y_t`, the script confirms exactly
```
Pr[x < y_i] = i/(t+1),     i = 1, …, t.
```
The incomparable pairs `(x, y_i)` therefore have balances `{1/(t+1), 2/(t+1), …, t/(t+1)}`, and
```
Q( point ‖ t-chain ) = 1/2 − min_i | i/(t+1) − 1/2 |.
```
| t | balances Pr[x<y_i] | Q |
|--:|---|---|
| 1 | 1/2 | 1/2 |
| **2** | **1/3, 2/3** | **1/3** ← the textbook gadget |
| 3 | 1/4, 1/2, 3/4 | 1/2 |
| 4 | 1/5, 2/5, 3/5, 4/5 | 2/5 |
| 5 | 1/6, 1/3, 1/2, 2/3, 5/6 | 1/2 |

`t = 2` is the **unique** chain length whose balances are exactly `{1/3, 2/3}` with **no** middle pair near 1/2 — that is precisely what makes the textbook gadget Q = 1/3. For `t ≥ 3` a middle pair `Pr ≈ 1/2` appears and Q jumps up. **Conclusion: you cannot descend the ladder by lengthening a chain** — every chain longer than 2 manufactures a balanced side pair that dominates Q. This is the closed-form reason the obvious jump operators fail.

### 3.2 The naive jump-operator candidates leave the ladder

Three one-parameter "stretch" families (each `t = 1` reproduces a rung):

- **famA** — the seed with its central chain's **top** stretched to `c0 < c1 < ⋯ < c_{t−1}`;
- **famB** — the seed with its central chain's **bottom** stretched;
- **famC** — the 14/39 witness with the heavy twin's down-chain stretched to length t.

The script tabulates Q(t); the pattern is uniform:

```
famA seed-top : t=1:0.3636(L)  t=2:0.4286  t=3:0.4706  t=4:0.4500  t=5:0.4783  t=6:0.4615
famB seed-bot : t=1:0.3636(L)  t=2:0.4286  t=3:0.4706  t=4:0.4500  t=5:0.4783  t=6:0.4615
famC 14-heavy : t=1:0.3590(L)  t=2:0.4769  t=3:0.4433  t=4:0.4889  t=5:0.4637  t=6:0.4934
```
`(L)` marks a point on the ladder (`3Q−1 = 1/integer`, `Q = (k+1)/(3k)`). **Only `t = 1` is on it.** For `t ≥ 2` every family overshoots to `Q ≈ 0.43–0.49`, exactly as §3.1 predicts: the stretched chain creates a near-1/2 side pair (in famA/B the maximal arm `b1` against the lengthened top/bottom; in famC the light twin against the heavy twin's chain). This reproduces and explains mg-8bd6 §4.3's "naive families over-shoot."

### 3.3 The rungs are not deformations of one another

The `(n, k)` jumps `5→7→10` (Δn = 2, 3) and `11→13→17` (Δk = 2, 4) are not a constant-step ladder, and §3.2 shows no single stretch operator links consecutive rungs. The three witnesses have genuinely different binding-pair geometries (seed: σ-fixed central b0 vs maximal arm; 14/39: reversal-symmetric mid-level twins; 6/17: fixed-point-free σ across a 5-element fundamental domain). The honest reading: **the rungs are sporadic self-dual minima** that happen to satisfy the Diophantine relation `Q = 1/3 + 1/(3k)`, not members of a single parametric family produced by a clean recipe. (A sampled +3 self-dual extension search seeded at the 14/39 witness did not surface the 6/17 witness or any rung below it — weak evidence the rungs are not linked by a single clean self-dual operator, consistent with their differing binding-pair geometries; not exhaustive.)

---

## 4. 6/17 is a strict self-dual local floor (the exhaustive result)

If a jump operator exists, the most natural form is a **self-dual extension** of the 6/17 witness (adding σ-symmetric elements, since the witnesses are self-dual). The script enumerates these exhaustively.

**+1 (a σ-fixed central element).** A self-dual extension by one σ-fixed element `f` requires `f`'s down-set `D` to be an order ideal and its up-set to be `σ(D)` (a filter), with `D ∩ σ(D) = ∅`. There are exactly **10** width-3 such extensions (n = 11). Their minimum Q is **4/11** (overshoot up); none is below 6/17.

**+2 (a σ-symmetric pair).** A self-dual extension by a pair `{u, v = σ(u)}` is parametrised by `u`'s down-ideal `D` and up-filter `U`; `v` receives the dual relations `σ(U) < v < σ(D)`. There are exactly **163** width-3 such extensions (n = 12). Their minimum Q is **6/17**, attained **only** by the **e-preserving** adjunction (e unchanged at 187 — `u` a global top together with `v` a global bottom, or the same with labels swapped). This is Q-preserving (a global extremum is forced first/last in every linear extension; the order-polytope analogue of Prong-3A Lemma B "series = max"). **Every e-increasing self-dual +2 move has Q > 6/17.**

So **no self-dual local move beats 6/17**: the +1 neighbourhood floors at 4/11, the +2 neighbourhood floors at 6/17 (only via the trivial Q-preserving adjunction). Combined with mg-8bd6's beam + anneal stall (two beams + a randomized anneal, ~160 restarts, to n ≤ 14, nothing below 6/17), the constructive descent ray **does not extend below 6/17**. The descent moved `4/11 → 14/39 → 6/17` in discrete +2/+3-element jumps with sporadic geometry; neither the closed-form stretches (§3) nor the exhaustive self-dual local extensions (§4) cross the next jump.

*(Caveat, stated honestly: "no self-dual local move beats 6/17" is exhaustive only for the +1 and +2 self-dual neighbourhoods of the 6/17 witness; the +3 self-dual neighbourhood was sampled, not exhausted, and finds nothing below 6/17 either. Absence of a descent under these searches is strong evidence, not a proof, that the ladder terminates — exactly the discrimination limit mg-8bd6 §6 named. The genuine `Q ≥ 6/17` floor remains the Prong-3E theorem target.)*

---

## 5. Why no `inf Q = 1/3` claim and no `Q ≥ 6/17` floor claim (honest scoping)

- **No PRIMARY/STRONGER (`inf Q = 1/3`).** That would require an explicit cofinal family `P_k`, `k → ∞`, with `Q(P_k) = (k+1)/(3k)`. §3 shows the natural one-parameter constructions overshoot, and §4 shows the self-dual local neighbourhood of the deepest known rung does not descend. We found no such family; claiming asymptotic sharpness now would be unsupported.
- **No `Q ≥ 6/17` floor.** That is the strict-strengthening theorem (the Prong-3A `8/21` analogue for the full non-SP width-3 family). It needs a reduction of general-width-3 `Q` to a bounded "near-twin / σ-orbit pair" class, then a `6/17` bound on that class — the SP-tree recursion (Prong-3A Lemma A) does not exist here. We do not have that reduction, so we do not claim the floor. The exhaustive self-dual local-floor of §4 is *evidence for* it, not a proof.
- The corridor therefore stays exactly `(1/3, 6/17]`, with the drop-vs-floor question still open but the **floor hypothesis now better supported within the self-dual subspace** than after mg-8bd6 (which had only heuristic beam/anneal evidence).

---

## 6. Suggested Prong 3E brief (gated on this stall verdict)

The ladder does not extend constructively; `6/17` is the corridor ceiling and the stall mechanism is named. Per the ticket's V4 gating, the recommended Prong 3E (in priority order):

**Prong 3E-α (recommended) — the `Q ≥ 6/17` floor theorem on the self-dual width-3 class.** Attempt the strict-strengthening lower bound `Q ≥ 6/17` for all width-3 posets, sharp at the n = 10 witness, *starting from the self-dual structure*. Concretely: (1) reduce general width-3 `Q` to the binding near-twin / σ-orbit pair class (the missing general-width-3 analogue of Prong-3A Lemma A); (2) bound that class below by `6/17` using the order-polytope volume ratio and the gadget identity `Pr[x<y_i] = i/(t+1)` of §3.1. The self-duality finding (§1) is the new lever: on a self-dual poset the balance spectrum is symmetric about 1/2, so the binding pair is the σ-orbit pair and the bound need only be proved on σ-orbits. A negative result (no such reduction) is itself a clean Outcome-4 deliverable.

**Prong 3E-β (cheap, rigour) — exhaustive self-dual width-3 floor at n = 11, 12, 13.** Pin the exact *self-dual* width-3 minimum at n = 11, 12, 13 by iso-reduced exhaustive enumeration of self-dual posets (the +1/+2 scans of §4 are exhaustive only as *extensions of the 6/17 witness*, not over all self-dual posets at those sizes). If the self-dual minimum is `≥ 6/17` through n = 13, that materially strengthens the floor hypothesis and charts whether the `k`-sequence `11, 13, 17, …` can continue at all.

**Prong 3E-γ (the long shot) — a non-local jump operator.** §3–§4 rule out *local* and *one-parameter-stretch* operators. If the ladder really does reach `1/3`, the operator must be non-local (each rung a fresh sporadic self-dual minimum). A targeted search over self-dual width-3 posets at n = 13, 14, 15 (the next plausible jump sizes, by the +2/+3 pattern) for a rung `Q = 1/3 + 1/(3k)`, `k ∈ {19, 23, 25, …}`, would settle drop-vs-floor empirically one rung further. High cost, uncertain payoff.

*(Parked / out of scope per NON-GOALS: no Cheeger/cut-and-window; no `Q ≤ 1/3` claim without a sixth codebase per §8.2 STRICT — not reached here, lowest Q = 6/17 > 1/3; no Lean / LaTeX / main.tex; Monte-Carlo never source of truth; no Family A/B/D re-sweep; no t-dilation analytic argument (proven Q-invariant); no formal closure of Prong-3A's φ4/T lemmas.)*

---

## 7. Routine checks (ticket ROUTINE CHECKS) — all via the closed-form / five-engine route

The verification script asserts each:
- **Sanity — ladder identity at k = 11, 13, 17.** `3Q − 1 = 1/k`, `Q = (k+1)/(3k)`, binding `Pr = (2k−1)/(3k)`; each rung's Q confirmed via all five engines (M1 = M2 = M3 = M4 = MC). ✓
- **Self-duality of all three rungs.** Explicit order-reversing involution found and printed for the seed, the 14/39 witness, and the 6/17 witness. ✓
- **Gadget identity** `Pr[x<y_i] = i/(t+1)` for t = 1..5; t = 2 is the unique Q = 1/3 length. ✓
- **Overshoot families** famA/famB/famC: only t = 1 on the ladder; t ≥ 2 overshoots. ✓
- **Self-dual local floor at 6/17:** +1 exhaustive (10 cases → min 4/11), +2 exhaustive (163 cases → min 6/17 via the e-preserving adjunction only; every e-increasing move > 6/17). ✓
- **§8.2 guard:** every Q > 1/3; lowest is 6/17; guard does not fire; no sixth-codebase halt. ✓

---

## Carry-forwards (for the next polecat)

- **Verdict:** Outcome-4 clean diagnosis + WEAKER finite-stall. The descent ladder does **not** extend past k = 17 under construction, exhaustive self-dual local extension, or (mg-8bd6) beam + anneal to n ≤ 14. Corridor UNCHANGED at `(1/3, 6/17]`; `6/17` is the stall rung / corridor ceiling. No Q < 6/17 exhibited; no `inf Q = 1/3` and no `Q ≥ 6/17` floor claimed.
- **NEW structural finding (reusable):** all three ladder witnesses are **self-dual** width-3 posets; the near-twin binding pair is the **σ-orbit pair**. σ: seed `(a0 c0)(b1 b2)(b0)`; 14/39 `(0 6)(1 5)(2 4)(3)`; 6/17 `i↔i+5 (mod 10)`. The descent lives in the self-dual width-3 subspace — the right search/proof restriction for Prong 3E.
- **The overshoot obstruction (closed form):** `Pr[x ‖ t-chain < y_i] = i/(t+1)`; only `t = 2` gives the gadget's `{1/3, 2/3}` with no middle pair. Lengthening any chain manufactures a near-1/2 side pair → Q jumps up. This is why the natural jump operators fail.
- **The self-dual local floor:** every self-dual +1 extension of the 6/17 witness floors at 4/11; every self-dual +2 extension floors at 6/17, attained only by the Q-preserving global-top/bottom adjunction (Lemma-B analogue). Evidence (not proof) that 6/17 is a genuine floor.
- **Reusable instrument:** [`scripts/onethird_ap2_prong3d_alpha_descent_verify.py`](../scripts/onethird_ap2_prong3d_alpha_descent_verify.py) — reuses the five-engine `verify_C` harness + §8.2 guard, adds `find_involution` (self-duality witness), `gadget_point_chain` + the overshoot families (jump-operator-attempt constructors), and `selfdual_extend_fixed` / `selfdual_extend_pair` (the exhaustive self-dual local-floor scan) + the `k_of` ladder checker. Clean run ≈ seconds.
- **Guard discipline (INHERITED STRICT):** lowest Q = 6/17 > 1/3; M1–M4 + MC suffice. A `Q ≤ 1/3` claim would still require a fresh SIXTH codebase + brute force.
- **Prong 3E target:** the `Q ≥ 6/17` floor theorem on the self-dual width-3 class (3E-α), or the exhaustive self-dual floor at n = 11, 12, 13 (3E-β). The drop-vs-floor question stays open, but the floor hypothesis is now the better-supported horn within the self-dual subspace.
