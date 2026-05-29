# OneThird — AP-2 Prong 3E-α: the analytic floor theorem `Q ≥ 6/17` on the self-dual width-3 class — sharp at the `k = 17` ladder rung

*Work item **mg-7ee8**. Follow-up to mg-5ff1 (Prong 3D-α), which returned LADDER-STALLED-WEAKER + Outcome-4: the descent ladder `Q = 1/3 + 1/(3k)` does **not** extend past `k = 17` under construction / exhaustive self-dual local extension / beam+anneal, and — the new structural finding — all three rung witnesses (`4/11` at `k=11`, `14/39` at `k=13`, `6/17` at `k=17`) are **self-dual width-3 posets** whose near-twin binding pair is the σ-orbit pair. This prong attempts the **analytic floor theorem** `Q ≥ 6/17` on that self-dual width-3 arena. Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3D-alpha-DescentRay.md`](OneThird-AP-2-Prong3D-alpha-DescentRay.md) (the stall verdict + gadget identity + self-dual classification + closed-form overshoot obstruction); [`OneThird-AP-2-Prong3C-Width3-FloorBound.md`](OneThird-AP-2-Prong3C-Width3-FloorBound.md) (the REFUTATION + ladder discovery + near-twin-pair mechanism + the `6/17` witness); [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the analytic `8/21` theorem — the structural template: Lemma A cross-pair reduction, Lemma B series=max, Lemma G binding case hand-proved); [`OneThird-AP-2-Prong1-SelfDual-LowerBound.md`](OneThird-AP-2-Prong1-SelfDual-LowerBound.md) (the **Outcome-4 precedent** on a *different* self-dual family — the box-rotation pair identity + the signed-gap wall); [`OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md`](OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md) (Ehrhart engine + `4/11` seed); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§4,6,8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3e_alpha_selfdual_floor_verify.py`](../scripts/onethird_ap2_prong3e_alpha_selfdual_floor_verify.py) — reuses the mg-5ff1 / mg-8bd6 five-engine `verify_C` harness (M1 order-ideal DP, M2 AP-0 kernel, M3 minimal-element-removal recursion, M4 brute permutations, MC Ehrhart order-polynomial) and `find_involution` verbatim, and adds the analytic-bound checkers: the σ-orbit-reduction verifier, the expected-rank duality verifier, the extension-involution Φ signed-gap-invariance witness (the wall), the binding-σ-orbit-type classifier, and the exhaustive `+1 / +2 / +3` self-dual local-floor scan (the `+3` neighbourhood now **exhausted**, closing the mg-5ff1 caveat). Pure stdlib; clean run ≈ 15 s. A clean exit *is* the lemma suite + five-engine agreement + the local-floor scan + the guard clearing.*

---

## 0. Headline

**VERDICT: Outcome-4 — clean negative diagnosis (WALL), strengthening the Prong-1 precedent.** The primary `Q ≥ 6/17`-for-all goal is **not** reached; it is not reachable from the self-dual symmetry, for a now-precise reason. The deliverable is the *exact location of the wall* plus the rigorous positive structure the symmetry does buy.

Three results, all exact:

1. **POSITIVE (rigorous) — the σ-orbit reduction + expected-rank duality.** For a self-dual width-3 poset `P` with order-reversing involution `σ`, the incomparable pairs split into σ-orbits carrying a single balance value, so
   ```
   Q(P) = max over σ-orbit representatives {x,y} of  min( Pr[x<y], Pr[y<x] ),
   ```
   and the **expected ranks are σ-antisymmetric about the centre**: `E[rank x] + E[rank σx] = n+1`, so every σ-fixed element is exactly central (`E[rank] = (n+1)/2`). This is the complete probabilistic content of self-duality — the general-poset analogue of Prong-1's Theorem 1 (which was skew-shape-specific), plus the new rank identity.

2. **THE WALL — an order-*reversing* involution pins no balance.** At all three ladder rungs the binding pair is a **σ-orbit-2 near-twin pair** (mirrored by σ to a *distinct* partner pair of equal balance) — never a σ-swapped self-pair, never a both-fixed pair. For such pairs σ supplies only the equation `Pr[x<y] = Pr[σ(y)<σ(x)]` relating the pair to its mirror; it never pins the common value. And for the one σ-*swapped* incomparable pair that does occur (the seed's near-twins `(b1,b2)`), the extension-involution `Φ` is **signed-gap-invariant**, so it permutes the linear extensions *within* each gap-level-set and cannot force balance — concretely `Pr[b1<b2] = 3/11`, wildly off `1/2`, while fully Φ-symmetric. This is exactly the Prong-1 wall (an anti-automorphism is anti-symmetry: it mirrors bias, it does not cancel it), here transferred to the general width-3 setting.

3. **THE TWO EXTRA LEVERS ALSO FAIL — and why.** This prong has two tools Prong 1 lacked: the closed-form gadget identity `Pr[x<y_i] = i/(t+1)` and width-exactly-3 chain structure (Dilworth: a 3-chain cover). Neither closes the bound. The gadget identity is a **single-strand** law (one point against one chain); the near-twin binding pair lives in the **interaction of the third strand with the near-twin σ-orbit**, where the controlling quantity is the global linear-extension count `e(P)` — which on the rungs is the *sporadic* `11, 39, 187 = 11·17`, **not** a clean `3k`. The bound `Q ≥ 6/17` reduces to a forced-relation order-polytope ratio `e(P + x<y)/e(P) ∈ [6/17, 11/17]` on the near-twin σ-orbit class, exactly the order-polytope twin of Prong-1's forced-relation skew-SYT ratio — and self-duality provably does not bound it (this §). The missing input is named in §5.

**Floor hypothesis — better supported, not proved.** The `6/17` local floor is now **exhaustive through the +3 self-dual neighbourhood** of the witness (mg-5ff1 left +3 sampled-only): all `4{,}712` width-3 self-dual `+1/+2/+3` extensions (the `+3` shell alone is `4{,}539`) have `Q ≥ 6/17`, attained only by the Q-preserving global-top/bottom adjunction (`e` fixed at 187); the deepest strictly-larger move sits at `Q = 634/1763 ≈ 0.3596 > 6/17`. So `6/17` survives one full extension shell further than before — strong evidence, still not a proof.

**Corridor UNCHANGED at `(1/3, 6/17]`.** No self-dual width-3 poset with `Q < 6/17` is exhibited (no REFUTATION); no `Q ≥ c` with `1/3 < c ≤ 6/17` is provable on the *full* self-dual class (no PARTIAL — any explicit `c > 1/3` is open-problem-hard, see §5); the PRIMARY/STRONG `Q ≥ 6/17`-for-all is walled (this §). `6/17` stands as the stall rung / corridor ceiling.

**§8.2 anti-Cheeger guard (INHERITED STRICT) does NOT fire.** Every `Q` encountered is `> 1/3` (lowest anywhere is `6/17`); no `Q ≤ 1/3` candidate arises, so M1–M4 + MC suffice and **no sixth codebase is triggered** (that trigger is reserved for a `Q ≤ 1/3` claim, which does not arise).

---

## (i) Vision alignment (V2 + V3 + V4) — verbatim from the ticket

- **V2 (computable Q):** *leverages the GENUINE closed-form Q identity e(P + x<y) / e(P) (Ehrhart volume ratio) PLUS the new gadget identity Pr[x < y_i] = i/(t+1) proved in mg-5ff1. Both closed-form. Both available as analytic levers.*
- **V3 (parameter space):** *the algebraic parameter is the self-dual width-3 combinatorial type (level structure + sigma-orbit pairing). Distinct from Family-B SP-tree, Family-C dilation t (Wall §3.2), Family-D field-q.*
- **V4 (sharpness-or-pivot signal):**
  - *STRONG (analytic-strong, mirror of Prong 3A 8/21 on SP): prove Q >= 6/17 for ALL width-exactly-3 self-dual posets, ALL n, SHARP at the k=17 rung witness. Converts the empirical stall into a family-restricted sharpness theorem. Second-strongest possible outcome.*
  - *PARTIAL: prove Q >= c for some 1/3 < c <= 6/17 on the self-dual class; name the gap structurally.*
  - *REFUTATION: exhibit a self-dual width-3 poset with Q < 6/17 (further narrowing the corridor; would supersede the 6/17 stall as the new ceiling and re-open Prong 3D operator-search).*
  - *WALL (Outcome 4): clean negative diagnosis — name precisely which sigma-orbit class or pair-mechanism blocks the bound, what additional analytic input would close it. Prong 1 set the Outcome 4 precedent shape.*

**Which V4 branch fired:** the **WALL** branch (Outcome 4). On **V2**, the analytic structure is built entirely from the closed-form `Pr[x<y] = e(P+x<y)/e(P)` order-polytope ratio and the `i/(t+1)` gadget identity; both are used as levers and both are shown (§3–§5) to be insufficient — the reduction lands on a *forced-relation* order-polytope ratio with no closed form on the self-dual family, mirroring Prong-1 §5. Every reported `Q` is an exact rational cross-checked through all five engines (M1=M2=M3=M4=MC); Monte-Carlo is never a source of truth. On **V3**, the algebraic parameter is the self-dual width-3 combinatorial type (σ-orbit pairing + level structure); the three rungs are shown (mg-5ff1 §3, re-confirmed here) to be *sporadic* self-dual minima in this parameter space, not a clean single-parameter family, which is itself the obstruction to a uniform analytic bound. On **V4**, the STRONG branch is shown unreachable from the symmetry (the wall), the PARTIAL branch is shown out of reach for any explicit `c > 1/3` (§5), no REFUTATION is found (the floor survives the exhaustive `+3` shell), so the deliverable is the clean Outcome-4 diagnosis with the precisely-named missing input.

---

## 1. Setup — the Q metric, the self-dual arena, and the σ-orbit reduction

For a finite poset `P` on `n` elements, under the uniform distribution on linear extensions (= bijections `λ: P → {1,…,n}` with `x < y ⟹ λ(x) < λ(y)`),
```
Q(P) = max over incomparable {x,y} of min( Pr[x<y], Pr[y<x] )
     = 1/2 − min over incomparable pairs of |Pr[x<y] − 1/2|.
```
The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3`; for width 3 it is a **theorem** (the repo's paper, `thm:main`). The **order-polytope identity** (Stanley 1986) gives every balance as an exact counting ratio:
```
Pr[x<y] = e(P + x<y) / e(P),   Q(P) = max over incomparable {x,y} of min( e(P+x<y), e(P+y<x) ) / e(P),
```
where `e(·)` counts linear extensions (= the leading Ehrhart coefficient of the order polytope, up to `n!`). This is the V2 closed-form lever.

**The self-dual arena.** A finite poset `P` is **self-dual** if it admits an *order-reversing involution* `σ`: a bijection `P → P` with `σ² = id` and
```
x < y  ⟺  σ(y) < σ(x).
```
mg-5ff1 found that all three descent-ladder rungs are self-dual width-3 posets (re-verified here via `find_involution`):

| rung | n | Q | k | order-reversing involution σ | σ-fixed pts |
|---:|---:|---|---:|---|---|
| `4/11` seed | 5 | `(k+1)/(3k)` | 11 | `(a0 c0)(b1 b2)(b0)` | `b0` central |
| `14/39` | 7 | `(k+1)/(3k)` | 13 | `(0 6)(1 5)(2 4)(3)` | `3` central |
| `6/17` | 10 | `(k+1)/(3k)` | 17 | `(0 5)(1 6)(2 7)(3 8)(4 9)` | none (fixed-point-free) |

> **Theorem R1 (the σ-orbit reduction — the rigorous probabilistic content of self-duality).**
> Let `P` be a self-dual poset with order-reversing involution `σ`. Then:
> (a) for every incomparable pair `{x,y}`, the image `{σ(x),σ(y)}` is also incomparable, and `Pr[x<y] = Pr[σ(y)<σ(x)] = 1 − Pr[σ(x)<σ(y)]`;
> (b) consequently the incomparable pairs partition into **σ-orbits** `{ {x,y}, {σx,σy} }` of size 1 or 2, each orbit carrying a single balance value `min(Pr[x<y], Pr[y<x])`; and
> (c) `Q(P) = max over σ-orbit representatives of the orbit balance.`

**Proof.** Define the **extension involution** `Φ` on the set `E` of linear extensions by
```
(Φλ)(c) = n + 1 − λ(σc).
```
If `x < y` then `σy < σx`, so `λ(σy) < λ(σx)`, so `n+1−λ(σy) > n+1−λ(σx)`, i.e. `(Φλ)(y) > (Φλ)(x)`; hence `Φλ ∈ E`. And `Φ²λ(c) = n+1−(Φλ)(σc) = n+1−(n+1−λ(σ²c)) = λ(c)`, using `σ²=id`; so `Φ` is an involution, hence a bijection of `E`.

(a) `σ` is an anti-automorphism, so `{σx,σy}` is incomparable whenever `{x,y}` is. For the probability: for incomparable `x,y`,
```
(Φλ)(x) < (Φλ)(y)  ⟺  n+1−λ(σx) < n+1−λ(σy)  ⟺  λ(σy) < λ(σx),
```
so `|{λ : (Φλ)(x)<(Φλ)(y)}| = |{λ : λ(σy)<λ(σx)}| = e·Pr[σy<σx]`. Since `Φ` is a bijection of `E`, the left side equals `|{τ : τ(x)<τ(y)}| = e·Pr[x<y]`. Divide by `e`: `Pr[x<y] = Pr[σy<σx]`. The second equality is the complement (`σy<σx` and `σx<σy` are the two orders of the incomparable pair `{σx,σy}`).
(b) Applying (a) to `{σx,σy}` and using `σ²=id` gives `Pr[σx<σy] = Pr[y<x] = 1−Pr[x<y]`, so the mirror pair `{σx,σy}` carries balance `min(Pr[σx<σy],Pr[σy<σx]) = min(1−Pr[x<y],Pr[x<y]) = min(Pr[x<y],Pr[y<x])`, equal to the balance of `{x,y}`. Orbits have size ≤ 2 since `σ²=id`.
(c) `Q` is the max balance over all incomparable pairs; by (b) it equals the max over one representative per orbit. ∎

> **Theorem R2 (expected-rank σ-antisymmetry).** For a self-dual poset with order-reversing involution `σ`, the expected rank `r̄(x) := E[λ(x)]` (uniform over `E`) satisfies
> ```
> r̄(x) + r̄(σx) = n + 1   for every x;     in particular   σx = x ⟹ r̄(x) = (n+1)/2.
> ```

**Proof.** With `Φ` as above, `(Φλ)(x) = n+1−λ(σx)`. Since `Φ` is a bijection of the uniform `E`, `λ` and `Φλ` have the same distribution, so `r̄(x) = E[(Φλ)(x)] = n+1 − E[λ(σx)] = n+1 − r̄(σx)`. Setting `σx=x` gives `r̄(x) = (n+1)/2`. ∎

Both theorems are machine-verified inline (script checkers `R1-ORBIT`, `R2-RANK`) at all three rungs: `Q` equals the σ-orbit-rep max; every orbit carries one balance; `r̄(x)+r̄(σx)=n+1` exactly; the σ-fixed `b0` (seed) and `3` (`14/39`) have `r̄ = 3 = (5+1)/2` and `r̄ = 4 = (7+1)/2`.

---

## 2. The binding σ-orbit is a near-twin orbit-2 pair (the characterisation)

> **Characterisation (binding σ-orbit).** At each of the three rungs the Q-realising (binding) incomparable pair is a **σ-orbit of size 2** — `σ` maps it to a *distinct* incomparable pair of equal balance — and the two pairs are the **near-twin pair and its mirror**. None is a σ-swapped self-pair; none is a both-σ-fixed pair.

| rung | binding pair | `Pr` | balance `Q` | σ-image of binding pair | orbit type |
|---:|---|---|---|---|---|
| `4/11` (k=11) | `(b0, b1)` | `7/11` | `4/11` | `(b0, b2)` (≠) | orbit-2; `b0` σ-fixed central, `b1↔b2` near-twins |
| `14/39` (k=13) | `(1, 2)` | `25/39` | `14/39` | `(5, 4)` (≠) | orbit-2; `1↔5`, `2↔4` |
| `6/17` (k=17) | `(3, 9)` | `11/17` | `6/17` | `(8, 4)` (≠) | orbit-2; `3↔8`, `9↔4` |

The binding `Pr` is always `(2k−1)/(3k)` (`7/11, 25/39, 11/17`), the ladder identity; its balance is `min(Pr,1−Pr) = (k+1)/(3k) = Q`. The σ-image gives the *other* near-twin pair, the equal-balance partner — exactly the "near-twin binding pair" of mg-8bd6, now seen as a σ-orbit (verified by checker `BIND-ORBIT`).

**Why `k ∈ {11,13,17}` is not derivable from the gadget identity alone.** mg-5ff1's gadget identity `Pr[x<y_i] = i/(t+1)` governs a *single* point against a *single* `t`-chain; it is what makes a width-≤2 gadget hit `1/3` at `t=2`. But the binding ratio here is `(2k−1)/(3k)`, controlled by the global `e(P)` of the *width-3* self-dual poset, which is the sporadic `e = 11, 39, 187 = 11·17` — not a clean `3k` (e.g. `6/17` splits `187 = 66+121` with `66/187 = 6/17`). The single-strand gadget law cannot produce these because the binding pair's balance is a *three-strand* order-polytope ratio, not a one-strand insertion probability. This is the first appearance of the wall: the closed-form lever the prong inherited is single-strand, the obstruction is three-strand.

---

## 3. The wall — an order-reversing involution pins no balance

This is the heart of the negative diagnosis, and it is the same wall Prong 1 hit, now stated for general self-dual width-3 posets. There are exactly two routes by which a symmetry can *force* (not merely mirror) a balance, and self-duality closes both.

### 3.1 σ-orbit-2 pairs: σ relates, never pins

For the binding pairs (all orbit-2, §2), Theorem R1(a) gives the single equation
```
Pr[x<y] = Pr[σy<σx] = 1 − Pr[σx<σy],
```
i.e. the pair `{x,y}` and its mirror `{σx,σy}` carry probabilities `p` and `1−p`. This is one equation in two pair-balances that are *already equal by construction*; it produces **no constraint on the common value** `min(p,1−p)`. The symmetry organises the pairs into equal-balance orbits (Theorem R1) but never writes down an equation or inequality pinning `p` toward `1/2`. (Contrast an order-*preserving* automorphism swapping an incomparable pair, which forces `Pr = 1/2` immediately — no such automorphism exists here; the only symmetry is the anti-automorphism `σ`.)

### 3.2 σ-swapped pairs: signed-gap invariance (the Lemma-2 wall)

A pair `{x,y}` is **σ-swapped** (an orbit of size 1) iff `σx = y`. The seed has exactly one such incomparable pair: the near-twins `{b1,b2}` (`σ` swaps them). The natural hope is that `σ` balances a pair it swaps. It does **not**:

> **Lemma W (signed-gap invariance).** For a σ-swapped incomparable pair `{x, σx}`, the signed gap `g(λ) = λ(σx) − λ(x)` is invariant under the extension involution: `g(Φλ) = g(λ)` for all `λ ∈ E`.

**Proof.** `(Φλ)(x) = n+1−λ(σx)` and `(Φλ)(σx) = n+1−λ(σ²x) = n+1−λ(x)`, so `g(Φλ) = (Φλ)(σx) − (Φλ)(x) = (n+1−λ(x)) − (n+1−λ(σx)) = λ(σx) − λ(x) = g(λ)`. ∎

So `Φ` permutes the linear extensions *within* each level set of `g`; the whole distribution of `g` — hence `Pr[x<σx] = Pr[g>0]` — is `Φ`-invariant, and `Φ` is the *only* lever self-duality supplies for this pair. It therefore neither forces `Pr = 1/2` nor bounds it away from the extremes. Concretely (checker `WALL`): the seed's swapped near-twins `{b1,b2}` have signed-gap distribution `{−4:1, −3:2, −2:3, −1:2, 1:2, 2:1}` (asymmetric about 0), all of it Φ-symmetric, giving `Pr[b1<b2] = 3/11 ≈ 0.273` — *below* `1/3`, the most-biased pair in the whole poset. **An order-reversing involution is anti-symmetry: it mirrors the bias of a swapped pair onto itself, it does not cancel it.**

This is verbatim the Prong-1 §4 wall (Lemma 2 + Claim 3), confirmed to transfer intact from the skew-shape box-rotation `ρ` to a general order-reversing `σ`. The one structural fact worth re-stating: self-duality acting on incomparable pairs splits them into orbits of equal balance, and that is *all* it does — it pins no balance value, on either orbit type.

### 3.3 The extra width-3 / gadget levers do not bridge the wall

Prong 1 stopped here. This prong has two more tools; both fail, for a reason now precisely visible:

- **Width-exactly-3 (Dilworth 3-chain cover).** Width 3 forces a chain-cover into three chains and an antichain of size 3, but it does not produce an order-*preserving* swap of any incomparable pair (the §3.2 route stays empty), and it gives no closed form for the global `e(P)`.
- **The gadget identity `Pr[x<y_i] = i/(t+1)` (§2).** Single-strand only. The binding pair's balance is the three-strand ratio `e(P + x<y)/e(P)`, where the forced poset `P + (x<y)` is no longer a clean point-over-chain gadget — it is a width-3 order polytope whose extension count is the sporadic `e = 66, 121, …`. The gadget law evaluates one strand; it cannot evaluate the interaction with the third.

So the reduction lands exactly where Prong 1's did, one combinatorial layer down: a **forced-relation extension-count ratio** with no closed form on the self-dual family.

---

## 4. The local floor — exhaustive through the `+3` self-dual shell (evidence)

If a self-dual width-3 poset with `Q < 6/17` exists (a REFUTATION), the most natural place is a small self-dual extension of the `6/17` witness. mg-5ff1 exhausted the `+1` and `+2` self-dual neighbourhoods and *sampled* `+3`. This prong **exhausts `+3`** (checker `LOCAL-FLOOR`):

| shell | construction | # width-3 self-dual extensions | min `Q` | attained by |
|---|---|---:|---|---|
| `+1` | one σ-fixed central element `f` (down-ideal `D`, up = `σ(D)`) | 10 | `4/11` | e-increasing (overshoot up) |
| `+2` | a σ-symmetric pair `{u, σu}` | 163 | **`6/17`** | **only** the e-preserving global-top/bottom adjunction (`e = 187` unchanged) |
| `+3` (fixed+fixed) | two σ-fixed central elements | 83 | `1/2` | — |
| `+3` (fixed+pair) | a σ-fixed element + a σ-pair | 2547 | `634/1763 ≈ 0.3596` | e-increasing |
| `+3` (pair+fixed) | a σ-pair + a σ-fixed element | 1909 | `634/1763 ≈ 0.3596` | e-increasing |

**Result:** across all `4{,}712 = 10 + 163 + (83+2547+1909)` width-3 self-dual `+1/+2/+3` extensions of the `6/17` witness (the `+3` shell alone is `4{,}539`), the minimum `Q` is exactly `6/17`, attained **only** by the trivial Q-preserving global-extremum adjunction (`e` fixed at 187 — a global max/min is forced last/first in every linear extension; the order-polytope analogue of Prong-3A Lemma B "series = max"). Every `e`-increasing self-dual local move has `Q > 6/17`; the deepest is `634/1763 ≈ 0.3596` (off-ladder: `3Q−1 = 139/1763`, `k ≈ 12.68 ∉ ℤ`). So the `6/17` floor now survives **one full self-dual extension shell further** than after mg-5ff1, closing that prong's flagged "`+3` sampled-not-exhausted" caveat.

This is evidence *for* the floor, not a proof: it is exhaustive only as a local search around the *known* witness (it does not enumerate all self-dual width-3 posets at `n = 11, 12, 13` — that is the separately-gated Prong 3E-β, §6), and a genuine fourth rung, if one exists, would by mg-8bd6's ladder geometry be a *non-local* sporadic minimum the `+1/+2/+3` shells cannot reach.

---

## 5. Why no PRIMARY, no PARTIAL-with-`c>1/3`, no REFUTATION (honest scoping) — and the missing input

- **No PRIMARY/STRONG (`Q ≥ 6/17` for all).** This needs (i) a reduction of general self-dual width-3 `Q` to the binding near-twin σ-orbit class — the analogue of Prong-3A's Lemma A cross-pair reduction — and (ii) a `6/17` bound on that class. Step (i) has no SP-tree recursion to lean on (the self-dual posets here are *not* series-parallel), and §3 shows self-duality supplies no such reduction. Step (ii) is exactly the forced-relation ratio bound below. So PRIMARY is walled.
- **No PARTIAL with explicit `1/3 < c ≤ 6/17`.** Any bound `Q ≥ c` with `c > 1/3` on the *full* self-dual width-3 class is open-problem-hard: it is a strict strengthening of the 1/3–2/3 conjecture restricted to this class, and the symmetry (the only family-specific tool) pins no balance (§3). We can prove `Q ≥ 1/3` on the class (it is the width-3 theorem restricted, with the balanced pair realisable on a σ-orbit by Theorem R1) but that is `c = 1/3`, not a strengthening. We therefore claim **no** explicit `c > 1/3`; doing so would be unsupported. (For context, the strongest *unconditional* bound for any non-chain poset is Brightwell–Felsner–Trotter `δ ≥ (5−√5)/10 ≈ 0.2764`, which sits *below* `1/3` and so cannot even deliver the conjecture, let alone `6/17`; cited as scale, not load-bearing.)
- **No REFUTATION.** No self-dual width-3 poset with `Q < 6/17` was found: the floor survives the exhaustive `+3` shell (§4) and mg-8bd6's beam+anneal to `n ≤ 14`. We do not claim one exists or does not.

> **Missing input (what would close the self-dual floor).** A forced-relation order-polytope ratio inequality: for the near-twin σ-orbit binding pair `{x,y}` of a self-dual width-3 poset,
> ```
> 6/17 · e(P)  ≤  e(P + x<y)  ≤  11/17 · e(P)
> ```
> (the sharp `6/17`-window; the `1/3`-window `⅓·e(P) ≤ e(P+x<y) ≤ ⅔·e(P)` is the weaker conjecture form). Equivalently, an Ehrhart/excited-diagram/order-polynomial estimate that bounds `e(P+x<y)/e(P)` into the balanced band for at least one σ-orbit per self-dual width-3 poset. This is the order-polytope twin of Prong-1's Missing Lemma (forced-relation skew-SYT ratios); it is a self-contained width-3 extension-count problem, **not** derivable from self-duality (§3), and a special case of the open width-3 sharpness question.

This is the clean, sanctioned Outcome 4: the self-dual route to the `6/17` floor terminates at a named, self-contained, out-of-scope counting inequality, and the symmetry — the one family-specific lever — is proved (§3) unable to supply it.

---

## 6. Suggested Prong 3F brief (gated on this WALL verdict)

Per the ticket's V4 gating, the WALL/Outcome-4 verdict gates to the **WEAKER-fires** branch (3F-β) as the recommended next step, with the other two recorded for completeness. (No `mg new` is called here; these are recommendations only.)

- **Prong 3F-β (recommended) — exhaustive self-dual width-3 floor at `n = 11, 12, 13`.** §4's `+1/+2/+3` scan is exhaustive only as *extensions of the `6/17` witness*. Pin the exact *self-dual* width-3 minimum at `n = 11, 12, 13` by iso-reduced exhaustive enumeration of self-dual width-3 posets (generate by σ-orbit structure on a fundamental domain, not by all-poset enumeration). If the self-dual minimum is `≥ 6/17` through `n = 13`, the floor hypothesis is materially strengthened and the question of whether the `k`-sequence `11,13,17,…` continues at all is charted directly. This is the cheap-rigour deliverable the WALL verdict points to: the analytic route is exhausted, so the next gain is empirical-exhaustive, not symbolic.
- **Prong 3F-α (gated on a future PRIMARY, not on this verdict) — off-self-dual extension.** Only sensible if some later prong *does* prove `Q ≥ 6/17` on the self-dual class: then extend it off the self-dual subspace to general width-3 (the working hypothesis of mg-5ff1 that Q-minimisers admit small-Q paths to the self-dual subspace would be the bridge). Not actionable now — the self-dual floor itself is unproved.
- **Prong 3F-γ (the long shot) — attack the §5 Missing Lemma directly.** A forced-relation order-polytope ratio bound (Ehrhart log-concavity / excited-diagram estimate) on width-3 posets. This is the genuine mathematical content; it is larger than a polecat and a special case of the open width-3 sharpness problem, so it is a research-grade ticket, not a sweep.

*(Parked / out of scope per NON-GOALS: no Cheeger/cut-and-window; no `Q ≤ 1/3` claim without a sixth codebase per §8.2 STRICT — not reached, lowest `Q = 6/17 > 1/3`; no Lean/LaTeX/main.tex; Monte-Carlo never source of truth; no Family A/B/D re-sweep; no t-dilation argument (Wall §3.2, proven Q-invariant); no formal closure of Prong-3A's non-binding φ4/Lemma-T lemmas; no Prong 3D-γ / 3E-β / 3E-γ executed here — separately gated.)*

---

## 7. Routine checks — sharpness at the rungs and the five-engine cross-check

The verification script asserts each (clean exit *is* the suite passing):

- **Sanity — the three rungs five-engine + ladder identity.** `M1=M2=M3=M4=MC` agree on `e` and `Q`; `3Q−1 = 1/k`, `Q = (k+1)/(3k)`, binding `Pr = (2k−1)/(3k)` at `k = 11, 13, 17`. ✓
- **Sanity — all three rungs self-dual; binding pair is a σ-orbit.** `find_involution` returns σ for each; the binding pair maps to a *distinct* equal-balance partner (orbit-2). ✓
- **Sanity — gadget identity.** `Pr[x<y_i] = i/(t+1)` for `t = 1..5`; `t=2` the unique `Q=1/3` length (re-used from mg-5ff1). At the seed, the gadget calibration `Pr` matches `(2k−1)/(3k) = 7/11` on the binding strand. ✓
- **Theorem R1 (σ-orbit reduction).** `Q` = max over σ-orbit reps; every orbit carries one balance. ✓ (checker `R1-ORBIT`).
- **Theorem R2 (expected-rank duality).** `r̄(x)+r̄(σx) = n+1`; σ-fixed elements central. ✓ (checker `R2-RANK`).
- **Lemma W (the wall).** `Φ` is a closed involution on `E`; for the seed's σ-swapped pair `{b1,b2}` the signed gap is Φ-invariant and `Pr[b1<b2] = 3/11`. ✓ (checker `WALL`).
- **Local floor.** `+1` (10) min `4/11`; `+2` (163) min `6/17` via the e-preserving adjunction only; `+3` (4539 across three families: 83 fixed+fixed, 2547 fixed+pair, 1909 pair+fixed) min `634/1763 > 6/17`. Overall self-dual local min = `6/17` over 4712 extensions. ✓ (checker `LOCAL-FLOOR`).
- **Sharpness ordering.** `4/11 ≈ 0.3636 > 14/39 ≈ 0.3590 > 6/17 ≈ 0.3529`: a `6/17` floor (if proved) would be *loose* (strict) at `k=11, 13` and *sharp* at `k=17`, the deepest rung. ✓
- **§8.2 guard.** Every `Q > 1/3`; lowest is `6/17`; guard does not fire; no sixth codebase triggered. ✓

---

## Carry-forwards (for the next polecat)

- **Verdict:** Outcome-4 — clean WALL diagnosis, strengthening Prong-1. The PRIMARY `Q ≥ 6/17`-for-all is **not** reachable from the self-dual symmetry; no PARTIAL `c > 1/3` is provable on the full class; no REFUTATION found. Corridor UNCHANGED at `(1/3, 6/17]`; `6/17` is the stall rung / corridor ceiling.
- **Positive content (rigorous, reusable):** *Theorem R1* (σ-orbit reduction: `Q` = max over σ-orbit reps, via the extension involution `Φλ(c)=n+1−λ(σc)`) and *Theorem R2* (expected-rank σ-antisymmetry `r̄(x)+r̄(σx)=n+1`, σ-fixed ⟹ central). These are the complete probabilistic content of self-duality, for *any* finite self-dual poset.
- **The wall (reusable):** an order-*reversing* involution pins no balance — σ-orbit-2 pairs are only mirrored to equal-balance partners (no pinning equation), and σ-swapped pairs are *signed-gap-invariant* under `Φ` (Lemma W), so the symmetry permutes within gap-level-sets and cannot force `1/2` (seed's `{b1,b2}` at `Pr=3/11` demonstrates). Anti-symmetry mirrors bias, it does not cancel it. Identical to Prong-1 §4, transferred to general width-3.
- **The two extra levers fail precisely:** the gadget identity is single-strand; the binding pair's balance is the three-strand ratio `e(P+x<y)/e(P)` controlled by the *sporadic* `e = 11,39,187=11·17` (not `3k`); width-3 produces no order-preserving swap. The bound reduces to the §5 Missing Input.
- **Missing input (names what would close it):** a forced-relation order-polytope ratio bound `6/17·e(P) ≤ e(P+x<y) ≤ 11/17·e(P)` for the near-twin σ-orbit pair — the Ehrhart twin of Prong-1's skew-SYT Missing Lemma; self-duality provably does not supply it.
- **Local floor strengthened:** `6/17` survives the **exhaustive `+1/+2/+3` self-dual shell** (4712 extensions total; the `+3` shell alone is 4539, min `634/1763 ≈ 0.3596 > 6/17`); the overall min `6/17` is held only by the Q-preserving global-extremum adjunction. Closes mg-5ff1's "+3 sampled-not-exhausted" caveat. Evidence, not proof.
- **Reusable instrument:** `scripts/onethird_ap2_prong3e_alpha_selfdual_floor_verify.py` — reuses the five-engine `verify_C` + `find_involution` + the `selfdual_extend_*` scans, and adds checkers `R1-ORBIT`, `R2-RANK`, `WALL`, `BIND-ORBIT`, `LOCAL-FLOOR` + the `+3` exhaustion. Clean run ≈ 15 s.
- **Prong 3F target:** 3F-β (exhaustive self-dual width-3 floor at `n = 11, 12, 13`) is the WALL-gated recommended next step; 3F-γ (the §5 forced-relation ratio bound) is the genuine but research-grade mathematical content; 3F-α (off-self-dual extension) is gated on a future PRIMARY that does not yet exist.
- **Guard discipline (INHERITED STRICT):** lowest `Q = 6/17 > 1/3`; M1–M4 + MC suffice. A `Q ≤ 1/3` claim would require a fresh SIXTH codebase + brute force.
