# OneThird AP-2 Prong 3I-alpha: The Self-Dualization Hypothesis — Q Dual-Invariance Gateway + an off-floor REFUTATION of the literal per-n form

**Work item:** mg-f6d3
**Date:** 2026-05-30
**Status:** **REFUTATION of the literal per-n hypothesis (n=6 counterexample) + corrected floor-sufficient hypothesis that SURVIVES + a proved dual-invariance toolkit.**

Headline in one paragraph. The self-dualization hypothesis *as literally named in Prong 3H-alpha §4.3* — "the extreme-reduced width-3 minimum at **each** n is attained by a self-dual poset" — is **FALSE**. At **n=6** the minimum Q over extreme-reduced width-3 posets is **15/37 ≈ 0.4054**, attained by **exactly two** isomorphism classes, and **neither is self-dual**: they are an exact **dual pair** (e=37 each), the structure predicted by the new dual-closure corollary. So even the weaker existence form ("some self-dual minimizer at each n") fails at n=6. **However**, this refutation is **off-floor**: 15/37 ≫ the global width-3 floor 6/17 ≈ 0.3529, so it does **not** break the floor reduction. The floor reduction needs only the *corrected* hypothesis **SD-FLOOR** (the *global* extreme-reduced minimum — the descent-ladder value — is attained self-dually), which is **not** refuted and is **proved on the unique-minimizer sub-class** via the prong's new analytic gateway (Q dual-invariance). T7's conditional is therefore **replaced, not closed**: the correct residual is SD-FLOOR, not the over-strong per-n statement that mg-5406 never actually verified.

---

## Vision Alignment (V2 + V3 + V4)

> **V2 (computable Q):** leverages the closed-form analytic toolkit consolidated in Prong 3H-alpha — Stanley order-polytope ratio Pr[x<y] = e(P+x<y)/e(P), gadget identity Pr[x<y_i] = i/(t+1), sigma-orbit reduction R1, expected-rank antisymmetry R2, Q-preserving extreme adjunction T6, extreme-reduction T7. All five give the analytic distinguishers. NOT generic DP.

> **V3 (parameter space):** extreme-reduced width-3 arena (combinatorial type of poset minus its global extremes). Polynomial-in-n enumeration reuses Prong 3F-beta + Prong 3G-alpha kernel.

> **V4 (sharpness-or-pivot signal):**
> - STRONG: prove the self-dualization hypothesis — every Q-minimizing extreme-reduced width-3 poset is self-dual, for ALL n. Closes T7 conditional, reduces full-arena floor analytically to self-dual core.
> - PARTIAL: prove the hypothesis for a restricted sub-class of extreme-reduced width-3 posets; identify the structural class where the hypothesis is proved and where it remains conditional.
> - REFUTATION: exhibit an extreme-reduced width-3 poset whose Q value matches or beats the self-dual minimum and is NOT self-dual. Would surprise — empirical verification through n=11 (3.16M iso-classes) showed argmin at each n is either self-dual or a T6 adjunction of a self-dual at smaller n. If REFUTATION fires, the full-arena floor question does NOT reduce to self-dual core; the analytic strategy fundamentally changes.
> - WALL (Outcome 4): clean negative diagnosis — name precisely which extreme-reduced sub-class blocks the proof and what additional combinatorial input would close it.

**Which V4 branch fired:** a **REFUTATION of the literal per-n hypothesis** (the n=6 dual pair), but a **benign / off-floor** one — and therefore *explicitly NOT* the floor-breaking REFUTATION the V4 paragraph describes. The V4 REFUTATION clause requires "Q value [that] matches or beats the **self-dual minimum**" (the global floor); the n=6 witnesses sit at 15/37, far *above* 6/17, so the full-arena floor question **does still reduce** to the self-dual core. The analytic strategy does **not** fundamentally change. The deliverable is therefore the clean **Outcome-4-flavoured** diagnosis: the named hypothesis was over-strong (it asserted a *per-n* fact that mg-5406's *full-arena* evidence never tested), it is false off-floor at n=6, and the correct floor-relevant residual (SD-FLOOR) is isolated and proved on the unique-minimizer sub-class. On **V2** the order-polytope ratio is the engine of the dual-invariance lemma; on **V3** the extreme-reduced arena is enumerated exhaustively at n=5,6,7 via the closed-upper-triangle kernel.

---

## 1. Definitions

- **Poset** P on {0,…,n−1}; `<` strict order. **Width** w(P) = longest antichain. Arena: **width-3** (w=3).
- **e(P)** = number of linear extensions. For incomparable (x,y): **Pr[x<y] = e(P+(x<y))/e(P)** (Stanley ratio).
- **balance(x,y) = min(Pr[x<y], Pr[y<x])** ∈ [0,1/2]. **Q(P) = max over incomparable (x,y) of balance(x,y)** — the *best* balance. 1/3–2/3 conjecture: Q ≥ 1/3 for non-chains; width-3 floor empirically 6/17 ≈ 0.35294.
- **Order dual** P\*: x <\_{P\*} y ⟺ y <\_P x. **Self-dual**: P ≅ P\* (∃ order-reversing involution σ).
- **Global extreme**: a global max (above all) or global min (below all). P **extreme-reduced** = neither.
- For each n: **𝓔₃(n)** = extreme-reduced width-3 posets on n elements; **q\*(n) = min over 𝓔₃(n) of Q**; **M_n = { P ∈ 𝓔₃(n) : Q(P)=q\*(n) }** as a set of iso-classes (the **per-n extreme-reduced minimizers**).
- **Global floor** q\* := inf over all n of q\*(n) (= the descent-ladder minimum, = the width-3 floor).

---

## 2. The two hypotheses (precise statements)

**SD-perN (the literal Prong 3H-alpha §4.3 statement).** For *every* n, every P ∈ M_n is self-dual.
Equivalently: for every n, M_n contains no non-self-dual iso-class.

**SD-FLOOR (the floor-sufficient corrected statement).** The global floor is attained on the self-dual
core: inf over 𝓔₃ of Q = inf over self-dual 𝓔₃ of Q. Equivalently (since the floor is attained at the
seed/ladder n's): at the n where q\*(n) = q\*, M_n contains a self-dual class.

**Why the distinction is load-bearing.** T7 (extreme-reduction) gives `inf over width-3 = inf over 𝓔₃`.
To push the floor onto the self-dual core one needs only **SD-FLOOR** — that the *global* extreme-reduced
minimum is self-dual. **SD-perN is strictly stronger**: it demands self-duality of the minimizer at
*every* n, including n where q\*(n) is far above the global floor. Prong 3H-alpha conflated the two: it
named SD-perN but cited mg-5406's *full-arena argmin* evidence, which (via T6/T7) only ever supported the
floor-relevant reduction, never the per-n extreme-reduced statement. §5 shows SD-perN is **false**.

---

## 3. The Q Dual-Invariance Gateway (proved, unconditional)

### Lemma SD0 (Q dual-invariance). For every finite poset P, **Q(P) = Q(P\*)**.

*Proof.* Reversal λ ↦ λ^rev is a bijection between linear extensions of P and of P\*: for u <\_{P\*} v ⟺
v <\_P u ⟺ v before u in λ ⟺ u before v in λ^rev, so λ^rev extends P\*; it is an involution, hence a
bijection, so e(P) = e(P\*). The incomparable pairs of P and P\* coincide (comparability is
dual-symmetric). Restricting the bijection to extensions placing x before y (resp. after y) gives
Pr\_{P\*}[x<y] = Pr\_P[y<x], so balance\_{P\*}(x,y) = balance\_P(x,y) for every incomparable pair; the max
over the (identical) pair sets gives Q(P\*) = Q(P). ∎ *(Verified computationally: Q(P)=Q(P\*) on all
spot-checked posets, three independent linear-extension engines agreeing.)*

### Corollary SD1 (dual-closure of M_n). Dualization maps M_n to M_n; M_n is closed under dualization.

*Proof.* Dualization preserves width (antichains ↦ antichains), sends extreme-reduced to extreme-reduced
(global max ↔ global min), and preserves Q (SD0), hence preserves 𝓔₃(n) and q\*(n). ∎

Write **M_n = S_n ⊔ N_n** (self-dual ⊔ non-self-dual classes). Dualization is a fixed-point-free
involution on N_n, so **|N_n| is even**, and **SD-perN holds at n ⟺ N_n = ∅.**

### Theorem SD-UNIQ. If |M_n| = 1, the unique minimizer is self-dual (so SD-perN holds at n).
*Proof.* M_n = {[P]}; SD1 gives [P\*] ∈ M_n = {[P]}, so P\* ≅ P. ∎

### Theorem SD-PARITY. If |M_n| is odd, then |S_n| ≥ 1 (a self-dual minimizer exists).
*Proof.* |N_n| even, so |M_n| odd ⟹ |S_n| = |M_n|−|N_n| odd ≥ 1. ∎

**These are the gateway.** They reduce *self-duality of a minimizer* to a *counting* question on M_n:
uniqueness (|M_n|=1) forces self-duality; odd cardinality forces a self-dual minimizer to exist; and an
**even, fully non-self-dual** M_n (a union of dual pairs) is exactly how SD-perN can fail. §5 exhibits
that failure at n=6.

---

## 4. The V2 analytic toolkit does not rescue SD-perN

The carry-forward distinguishers cannot exclude a non-self-dual dual pair from M_n:
- **R2 (expected-rank antisymmetry)** presumes a σ; it cannot force a minimizer to *have* one.
- **Lemma W (signed-gap Φ-invariance)**: σ preserves Φ(x,y) = Pr[x<y]−1/2's sign, so symmetry pins no
  balance; it can neither create nor exclude a competing non-self-dual minimizer.
- **Gadget identity / descent ladder** locate self-dual extremal *structures* (the rungs); they certify a
  self-dual minimizer *exists at the ladder values* but say nothing about off-ladder competitors.

So the toolkit is consistent with SD-FLOOR (a self-dual minimizer is *available* at the floor) but powerless
against SD-perN. §5 shows the latter genuinely breaks.

---

## 5. Computational results (script: onethird_ap2_prong3i_alpha_selfdualization_verify.py)

All Q values cross-checked by **three independent linear-extension engines** — E1 pred-mask
antichain-front subset DP (= M1 placed-set DP), E2 brute n! permutation count (= M4 brute, n≤8), E3
recursive deletion-of-maximal (independent recursion). Prior prongs' M2 (Q_via_dp), M3 (IndPoset), MC
(Ehrhart) corroborate the same witnesses. **Monte Carlo is never a source of truth.** Every Q below
exceeds 1/3, so the roadmap §8.2 anti-Cheeger STRICT sixth-codebase guard does not fire.

**Method.** Enumerate all transitively-closed subsets of the upper triangle {(i,j):i<j} (every poset
appears ≥ once under the "labels respect a linear extension" convention; n=5→2¹⁰, n=6→2¹⁵, n=7→2²¹ masks),
filter to width-3 + extreme-reduced, compute Q, collect ALL minimizers, reduce to iso-classes (brute n!
canonical form, applied only to the small minimizer set), and test each for self-duality (find_involution).

### Exhaustive extreme-reduced width-3 minimizer enumeration

| n | q\*(n) = min Q over 𝓔₃(n) | \|M_n\| | self-dual? | witnesses |
|---|---|---|---|---|
| 5 | **4/11** (0.36364) | **1** | **yes** | e=11, binding (1,2). SD-UNIQ ⟹ SD-perN holds at n=5. |
| 6 | **15/37** (0.40541) | **2** | **NO (both)** | **dual pair**, e=37 each. **SD-perN REFUTED at n=6.** |
| 7 | **14/39** (0.35897) | **1** | **yes** | e=39, binding (1,2). SD-UNIQ ⟹ SD-perN holds at n=7. |

**The n=6 refutation (verified, exhibited).** Over all extreme-reduced width-3 posets at n=6, the minimum
Q is 15/37, attained by exactly two iso-classes, **C** and **C\*** = dual(C) (confirmed:
`canonical(dual(C)) = canonical(C*)`, and neither is self-dual). Concrete cover relations:

```
C  :  0<2, 0<4, 0<5, 1<3, 1<4, 2<3      (e=37, Q=15/37, binding (4,5), extreme-reduced)
C* :  0<2, 0<5, 1<4, 1<5, 2<4, 3<4      (e=37, Q=15/37, binding (1,3), extreme-reduced)
```
(cover relations; C\* ≅ dual(C) verified via `canonical(dual(C)) = canonical(C*)`.)

Both are extreme-reduced (no global max/min), both width-3, both Q=15/37 (three-engine + e=37), and
C\* ≅ dual(C). Since M_6 = {C, C\*} and neither is self-dual, **SD-perN is false at n=6** — and so is even
its existence form (no self-dual class achieves q\*(6)). This is exactly the SD1-predicted failure mode:
M_6 is a single dual pair (|M_6| = 2, even, N_6 = M_6).

**Why this does NOT break the floor reduction.** q\*(6) = 15/37 ≈ 0.4054 is far *above* the global width-3
floor 6/17 ≈ 0.3529 (attained at n=10). n=6 is an off-floor "interior" n; its minimizer's non-self-duality
is irrelevant to inf over 𝓔₃. SD-FLOOR (the floor-relevant statement) is untouched.

### Floor-relevant evidence (SD-FLOOR), carry-forward + this prong
- **n=5** (seed/ladder, q\*=4/11): |M_5|=1, self-dual — SD-UNIQ proves it (this prong).
- **n=7** (seed/ladder, q\*=14/39): |M_7|=1, self-dual (e=39, binding (1,2)) — SD-UNIQ proves it (this
  prong, exhaustive). The interior n=6 lies *between* these two seeds and is exactly where SD-perN breaks.
- **n=10** (global floor, q\*=6/17): the extreme-reduced argmin is the self-dual e=187, binding (3,9)
  witness (carry-forward mg-5406; reported as the single argmin class). SD-FLOOR holds at the floor.
- **Structural pattern (this prong):** at the *seed/ladder* n's (5, 7, 10) the extreme-reduced minimum is
  the *unique* self-dual rung (SD-UNIQ); at the *interior* n=6 the minimum is off-floor (15/37) and a
  *non-self-dual dual pair*. So self-duality tracks the *floor-attaining* n's, not all n — precisely
  SD-FLOOR, not SD-perN.

### Sanity checks
- Q dual-invariance Q(P)=Q(P\*) confirmed on all spot checks (Lemma SD0).
- The n=5 (4/11) seed is extreme-reduced, self-dual, achieves its Q (three engines + find_involution).
- The n=6 dual pair is exhibited above with explicit relations.

---

## 6. Achieved Result

**REFUTATION of the literal per-n self-dualization hypothesis (SD-perN), off-floor at n=6 — with the
floor-relevant hypothesis SD-FLOOR surviving and proved on the unique-minimizer sub-class.**

Unconditionally proved (the gateway):
1. **Lemma SD0** — Q dual-invariance. 2. **Corollary SD1** — M_n dual-closed (so |N_n| even).
3. **Theorem SD-UNIQ** — |M_n|=1 ⟹ minimizer self-dual. 4. **Theorem SD-PARITY** — |M_n| odd ⟹ a
self-dual minimizer exists.

Refuted: **SD-perN** — exhibited a dual pair of non-self-dual extreme-reduced Q-minimizers at n=6
(Q=15/37, e=37). Both the universal and the existence per-n forms fail at n=6.

Surviving + partially proved: **SD-FLOOR** — not refuted (the n=6 failure is off-floor); holds at the seed
n=5 (SD-UNIQ, since |M_5|=1) and at the global-floor n=10 (carry-forward). On the **unique-minimizer
sub-class** (n with |M_n|=1) SD-perN — hence SD-FLOOR — is *proved* by SD-UNIQ; on the **odd-cardinality
sub-class** SD-FLOOR's existence form is proved by SD-PARITY.

This is **not STRONG** (SD-perN is false, so it cannot be proved). It is **not the floor-breaking V4
REFUTATION** (the n=6 witnesses do not match-or-beat the self-dual *global* minimum). It is the honest
**Outcome-4 correction**: the named hypothesis was over-strong; the correct residual is SD-FLOOR.

---

## 7. Closure-of-T7-Conditional Status

T7 reduces the full width-3 floor question to the extreme-reduced core unconditionally. The further
reduction to the self-dual core:

- **T7's conditional is REPLACED, not closed.** The correct residual is **SD-FLOOR** (the global
  extreme-reduced minimum is self-dual), *not* the false per-n SD-perN. Given SD-FLOOR, T7 reduces the
  floor to the self-dual core.
- **At the global-floor n (n=10) SD-FLOOR holds** (carry-forward self-dual e=187 witness); at the seed
  n=5 it holds by SD-UNIQ. So *with present evidence* the floor reduction is in force at the relevant n.
- The general SD-FLOOR (for all future ladder n, e.g. higher rungs) reduces to a **uniqueness/parity
  question at the floor-attaining n's**: |M_n|=1 ⟹ self-dual (SD-UNIQ); |M_n| odd ⟹ self-dual exists
  (SD-PARITY). This is the residual.

Honest headline: *full-arena floor* → (T7) → *extreme-reduced floor* → (SD-FLOOR, given uniqueness/parity
at the floor n) → *self-dual floor*. The last arrow holds at every n where the floor-attaining minimizer
is unique/odd (verified n=5; carry-forward n=10). The over-strong per-n SD-perN is *false* (n=6) and is
**discarded**.

---

## 8. Suggested Prong 3I-beta Brief (gated on this verdict)

The verdict is a **refutation-with-correction**, so 3I-beta should **secure SD-FLOOR**, not chase the dead
SD-perN, and not yet attack Q ≥ 6/17:

1. **Primary — prove SD-FLOOR at the floor-attaining n's.** It suffices to prove |M_n|=1 (SD-UNIQ) or
   |M_n| odd (SD-PARITY) *at the n where q\*(n) equals the global floor* (the ladder n's). (a) For the
   descent-ladder rungs, prove the rung is the **unique** extreme-reduced minimizer via gadget-identity
   rigidity. (b) Confirm |M_10| = 1 within the extreme-reduced sub-arena (the carry-forward enumeration
   reported a single argmin class; re-confirm with the closed-upper-triangle kernel — feasible offline).
2. **Map the non-self-dual interior.** Extend the exhaustive extreme-reduced enumeration to n=8,9 to chart
   *which* interior n's (like n=6) have non-self-dual dual-pair minima. This characterises the
   "off-floor non-self-dual band" and confirms it never dips to the global floor — strengthening SD-FLOOR
   empirically.
3. **Only after SD-FLOOR is secured (≥ existence form):** attempt Q ≥ 6/17 on the now-reduced self-dual
   core (Missing Input B, Prong 3E-alpha). Do not attempt it before the self-dual reduction holds in at
   least the SD-FLOOR/odd-cardinality form.

---

## 9. Appendix: what mg-5406 actually verified vs. what 3H-alpha named

3H-alpha §4.3 named SD-perN ("the extreme-reduced minimum at **each** n is attained by a self-dual poset")
and cited mg-5406's "exhaustive through n=11" as support. But mg-5406 classified the **full-arena** per-n
argmin and its self-duality, then used T6/T7 to relate it to a self-dual core — it never computed the
**extreme-reduced-only** minimum at each n. The two differ exactly at interior n's: at n=6 the full-arena
min is 4/11 (a *non-extreme-reduced* T6 adjunction of the n=5 seed), while the **extreme-reduced** min is
15/37, attained by a non-self-dual dual pair. So mg-5406's evidence was always evidence for the
*full-arena → self-dual-core* reduction (i.e. SD-FLOOR), never for the stronger per-n SD-perN. This prong is
the first to enumerate the extreme-reduced-only minimum per n, and it falsifies SD-perN at the first
interior n it reaches. Lemma SD0/SD1 then *explain* the n=6 structure (a dual pair) and isolate SD-FLOOR as
the correct, surviving residual.

---

## Reuse / Artifacts
- Verifier + enumerator: `scripts/onethird_ap2_prong3i_alpha_selfdualization_verify.py`
  (three-engine cross-check, Q dual-invariance check, find_involution, exhaustive extreme-reduced
  enumeration n=5,6,7 with per-n |M_n| + self-duality + dual-pair classification).
- Carry-forward: T6/T7 (mg-6728), R1/R2/Lemma W (mg-7ee8), gadget/ladder (mg-5ff1), full-arena argmin
  classification (mg-5406), self-dual exhaustive (mg-7237).
