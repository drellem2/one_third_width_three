# OneThird — closing L1b: proof of (A) SPREAD + named wall on (B) LOCALITY

**Work item:** mg-dbd1 (high, repo `one_third_width_three`). Spectral / near-ordinal-sum
program **only** (Čech / F-series program ignored per Daniel directive). Builds directly on
the mg-8201 expected-rank certificate (`docs/OneThird-L1b-ExpectedRank-Certificate.md`,
commit `6a4abec`); the certificate machinery is **reused, not re-derived**. LaTeX-first,
prove-or-wall each sublemma independently, block-and-report. Lean deferred.

**Verdict: (A) SPREAD — PROVEN. (B) LOCALITY — WALL, precisely named.**

- **(A) `‖r‖² = Ω(n³)` is a theorem** for any frozen counterexample (δ < 1/3, every
  incomparable pair > 2/3-biased toward a common linear extension `e`). Clean two-line band
  bound: `‖r‖² ≥ (n−1)³/1152`. It uses **only** δ < 1/3 — **not width 3, and not exact
  expected-rank monotonicity** (which is *false*, mg-b0a6). This resolves the program's L2 in
  the weaker "spread" form the certificate actually needs.
- **(B) `E[Σ disp²] = O(E[inv_e])` is walled.** It is the **L2 (second-moment) strengthening
  of the *unconditional* Diaconis–Graham L1 bound** `E[Σ|disp|] ≤ 2 E[inv_e]`. An exact
  identity (verified numerically) localises the entire gap to a **same-element
  inversion-correlation term** — precisely the class of poset correlation inequalities that
  mg-f9f4 found "genuinely hard / new; known poset correlation inequalities provably
  insufficient." The falsifier mechanism is named (a *bimodal chain-cross* of the `e`-minimal
  element) but its realizability under a single frozen `e` in width 3 is open and **doubly out
  of empirical reach** (brute LE is `O(n!)` → `n ≤ 9`, and strictly-frozen width-3 posets are
  so rare that 20 000 random dense trials at `n ≤ 9` produced **zero**).

**Net:** L1b is **one honest lemma from closed**, and that lemma (B) is now pinned to a single
concrete correlation inequality, not a vague "prove near-ordinal-sum." Empirical flatness of
the locality ratio (mg-8201: median 3.0, max 4.3) remains **evidence, not proof** — the regime
that could break it is unreachable.

---

## 0. Setup (recalled from the certificate; notation fixed once)

`P` a finite poset on `[n]`, uniform linear extensions `L(P)`, `σ ∈ L(P)` a bijection
positions → elements. For an element `x`, `pos_σ(x) ∈ {0, …, n−1}` is its 0-indexed position
in `σ`. The **element-position transport** is `(T_P)_{x,a} = Pr[pos_σ(x) = a]`, and the
symmetrized standard block `S_P = (T_P + T_Pᵀ)/2 |_H`, `H = 𝟙^⊥`, has top eigenvalue
`λ_std(P)`. The transport-energy identity (program §4) gives, for **every** fixed `f ∈ H`, a
rigorous per-poset lower bound
```
λ_std(P) ≥ R(f) = 1 − energy(f)/‖f‖²,   energy(f) = (1/2|L|) Σ_σ Σ_a (f_a − f_{σ(a)})².
```
The certificate's lead vector is the **centred expected rank**
```
u_a = a − (n−1)/2,   r = T_P u,   r_x = E[pos_σ(x)] − (n−1)/2.
```
Write `d_x := E[pos_σ(x)] = Σ_{y≠x} Pr[pos_σ(y) < pos_σ(x)]` (so `r_x = d_x − (n−1)/2`,
`Σ_x d_x = C(n,2)`, mean `(n−1)/2`).

**Frozen-counterexample hypothesis (H).** There is a linear extension `e` of `P` such that
every **incomparable** pair `{x,y}` with `x <_e y` has `Pr[pos_σ(x) < pos_σ(y)] > 2/3`
(equivalently δ(P) < 1/3, with the > 2/3-orientation acyclic and realized by `e`). Existence
of `e` is exactly mg-b0a6's killshot-1 (acyclicity of the strong-majority orientation); the
program assumes it and we condition (A)/(B) on it. **Relabel elements by `e`-rank**, so
`e`-rank(`x`) = `x` and, 0-indexed, `#{z : z <_e x} = x`.

Two derived quantities, both `e`-referenced:
- **`e`-inversion mass** `E[inv_e] = Σ_{x <_e y, incomparable} Pr[pos_σ(y) < pos_σ(x)]`
  (comparable pairs never invert since `e` is a linear extension). Each summand `< 1/3` under (H).
- **displacement** `disp_σ(x) = pos_σ(x) − erank(x)` (footrule displacement against `e`).
  `E[Σ_x disp_σ(x)²]` is the quantity in lemma (B).

The certificate's exact scaling law is `1 − R(r) = energy(r)/‖r‖²`, and closing L1b via `r`
needs the two factors bounded:

> **(A) SPREAD** `‖r‖² = Ω(n³)`  and  **(B) LOCALITY** `E[Σ disp²] = O(E[inv_e])`
> (plus a Lipschitz constant `Λ = O(1)`; see §3.4), which together give
> `1 − λ_std ≤ energy(r)/‖r‖² = O(E[inv_e]/n³) = O(1/n)` even when `E[inv_e] = Θ(n²)`.

---

## 1. Lemma (A) SPREAD — PROVEN: `‖r‖² ≥ (n−1)³/1152 = Ω(n³)`

### 1.1 The band bound (the whole proof)

Fix an element of `e`-rank `k ∈ {0, …, n−1}`; call it `x`. Split
`d_x = Σ_{z <_e x} Pr[z\text{ before }x] + Σ_{z >_e x} Pr[z\text{ before }x]`.

- There are `k` elements `z <_e x`. For each, `Pr[z\text{ before }x] ≥ 2/3`: if `z <_P x`
  (comparable) it is `1`; if incomparable, (H) gives `> 2/3` (`z` is the `e`-smaller, biased
  first). Also each `≤ 1`.
- There are `n−1−k` elements `z >_e x`. For each, `Pr[z\text{ before }x] ≤ 1/3`: if `x <_P z`
  it is `0`; if incomparable, (H) gives `< 1/3`. Also each `≥ 0`.

Hence, with **no** monotonicity assumption,
```
(2/3) k  ≤  d_k  ≤  k·1 + (n−1−k)/3  =  (2/3) k + (n−1)/3.          (band)
```
So `d_k` lies in a band of width `(n−1)/3` around the line of slope `2/3`. (Verified: `bnd=True`
on **every** frozen poset in reach, incl. the whole tight3 tower — §4.)

### 1.2 From the band to the spread

Write `r_k = d_k − (n−1)/2`. Using the **upper** band bound,
```
r_k ≤ (2/3) k + (n−1)/3 − (n−1)/2 = (2/3) k − (n−1)/6.
```
For every `k ≤ (n−1)/8` the RHS is `≤ (2/3)(n−1)/8 − (n−1)/6 = (n−1)/12 − (n−1)/6 = −(n−1)/12 < 0`,
so `r_k` is negative and
```
|r_k| = −r_k ≥ (n−1)/6 − (2/3) k ≥ (n−1)/6 − (2/3)·(n−1)/8 = (n−1)/12.
```
There are at least `(n−1)/8` such indices `k`, so
```
‖r‖² = Σ_k r_k²  ≥  Σ_{k=0}^{⌊(n−1)/8⌋} r_k²  ≥  (n−1)/8 · ((n−1)/12)²  =  (n−1)³ / 1152.
```
∎ **`‖r‖² = Ω(n³)`.** The symmetric argument on the *top* `e`-ranks (lower band bound
`r_k ≥ (2/3)k − (n−1)/6 > 0` for `k ≥ 3(n−1)/4`) contributes another `Ω(n³)`; and on the
frozen tight3 tower `‖r‖²/n³ → 1/12` exactly (§4), so the true constant is far larger than
`1/1152`. Only `Ω(n³)` is needed.

### 1.3 Why this is the right (non-circular, monotonicity-free) statement

- **No exact monotonicity.** mg-b0a6 falsified exact expected-rank monotonicity (L2 in its
  strong form). The band *permits* `d_k` to wobble by up to `(n−1)/3` — i.e. it permits the
  monotonicity failures b0a6 found — and still forces `Ω(n³)` spread. The certificate never
  needed monotonicity, only spread; (A) delivers exactly that.
- **No width hypothesis.** The proof uses only (H) (δ < 1/3 toward a common `e`). Width 3 is a
  special case. So (A) is robust and slightly more general than the ticket asks.
- **Non-circular.** `d_k` is a first-order observable (a single expected position); the bound
  reads it off pairwise biases via (H) with no appeal to `λ_std`, no prefix, no thin interface.

---

## 2. Lemma (B) LOCALITY — the reduction

`disp` is the footrule displacement of `σ` against the fixed reference order `e`, and
`E[inv_e]` is the Kendall (inversion) count against the same `e`. Three exact facts frame (B).

### 2.1 Diaconis–Graham: the L1 version of (B) is *unconditionally* true

For any permutation `σ` and the fixed reference `e`, the Diaconis–Graham inequality states
`I(σ) ≤ D(σ) ≤ 2 I(σ)`, where `I(σ) = ` #`e`-inversions of `σ` and
`D(σ) = Σ_x |disp_σ(x)|` is the Spearman footrule. Averaging over `L(P)`:
```
E[Σ_x |disp_σ(x)|]  ≤  2 E[inv_e].                                   (DG, unconditional)
```
So the **L1** locality bound needs *no hypothesis at all*. Lemma (B) asks for the **L2** version
`E[Σ_x disp²] = O(E[inv_e])`, which is strictly stronger: the gap is governed by the largest
displacements,
```
E[Σ disp²]  ≤  E[ max_x |disp_σ(x)| · Σ_x |disp_σ(x)| ]  ≤  2 · E[inv_e] · (typical max |disp|).
```
Thus **(B) ⟺ displacements have no heavy tail** — a second-moment / concentration statement,
not a counting one. This is the precise sense in which (B) is "weaker than LIB but still
substantive": LIB demanded `E[inv_e] = O(n)` (the conclusion); (B) demands only that squared
displacement be linearly controlled by inversions, which DG already delivers in L1.

### 2.2 Exact identity localising (B) to an inversion correlation (verified)

Write `I_{xy}(σ) = 1` iff `{x,y}` is `e`-inverted in `σ`, and `ε_{xy} = sign(erank(y) − erank(x))`.
Then `disp_σ(x) = Σ_{y≠x} ε_{xy} I_{xy}(σ)` (an `e`-above element before `x` pushes `x` right by
`+1`; an `e`-below element after `x` pushes it left by `−1`), so
```
E[Σ_x disp²]  =  2 E[inv_e]  +  Σ_x Σ_{y≠z} ε_{xy} ε_{xz} · E[I_{xy} I_{xz}].     (★)
```
The diagonal `Σ_x Σ_y E[I_{xy}] = 2 E[inv_e]` is *exactly* `O(E[inv_e])`. **Verified numerically**
(script §1: `n = 3,4,5`, `lhs = rhs` to `1e−9`). Therefore
```
(B) holds  ⟺  Cross := Σ_x Σ_{y≠z} ε_{xy} ε_{xz} E[I_{xy} I_{xz}]  =  O(E[inv_e]).
```
`Cross` is a sum, over each element `x` and each **pair of distinct incomparable partners**
`y,z`, of the signed **joint probability that both `{x,y}` and `{x,z}` invert**. It is a genuine
same-element three-point correlation of inversion events. This is exactly the object mg-f9f4
concluded is "genuinely hard / new," with known poset correlation inequalities (FKG, XYZ,
Shepp, Fishburn) provably insufficient to sign or bound it.

### 2.3 Equivalent second-moment view (why `Cross` can blow up)

`E[Σ disp²] = Σ_x (Var disp_σ(x) + E[disp_σ(x)]²)`. The deterministic part is
```
Σ_x E[disp_σ(x)]²  =  Σ_x (d_x − erank(x))²  =  Σ_x (E[A_x] − E[B_x])²,
```
where `A_x` = #(`e`-above elements before `x`), `B_x` = #(`e`-below elements after `x`),
`E[A_x] + E[B_x] = m_x` = expected inversion degree of `x`, and `Σ_x m_x = 2 E[inv_e]`. Since
`E[disp(x)]² ≤ m_x²`,
```
Σ_x E[disp(x)]²  ≤  Σ_x m_x²  ≤  (max_x m_x) · Σ_x m_x  =  2 (max_x m_x) E[inv_e].
```
So **`max_x m_x = O(1)` ⟹ the deterministic part of (B) holds**.

> ~~and by Jensen `E[disp(x)²] ≥ E[disp(x)]²`, so if any single `m_x = Θ(n)` while
> `E[inv_e] = Θ(n)`, then `E[Σ disp²] ≥ m_x² = Θ(n²)` and **(B) fails by a factor `n`**. Lemma (B)
> therefore hinges on whether the frozen structure caps the per-element inversion degree `m_x` (and
> the analogous variance tails).~~
>
> **STRUCK 2026-07-31 (mg-fccb) — inequality-direction error.** Retained struck rather than deleted
> so the corpus keeps the record of what was asserted. Diagnosis in the annotation below; the
> correct replacement is stated immediately.

**What §2.3 actually supplies (corrected, mg-fccb).** Only the **sufficiency** direction, and only
for the deterministic part:

```
max_x m_x = O(1)   ⟹   Σ_x E[disp(x)]² = O(E[inv_e])          [valid, via b_x ≤ m_x]
max_x m_x = Θ(n)   ⇏   (B) fails                              [INVALID — needs b_x ≥ m_x]
```

Jensen gives `E[Σ disp²] ≥ Σ_x E[disp(x)]² = Σ_x b_x²` correctly; what fails is the *next*
substitution `b_x² → m_x²`, which needs `b_x ≥ m_x` when only `b_x ≤ m_x` is available. So a large
per-element inversion **degree** `m_x` does not by itself force a large **bias** `b_x`, and lemma (B)
does **not** hinge on capping `max_x m_x`. The quantity a falsifier must make large is the bias
`b_x`, not the degree `m_x` — which is exactly mg-a58f's **(EQ)**, `max_x b_x = O(1)`.

> ### ⚠️ ANNOTATION (2026-07-29, mg-1fdb): the sentence beginning *"and by Jensen"* above is **WRONG — an inequality-direction error.**
>
> **What is wrong.** The display `Σ_x E[disp(x)]² ≤ Σ_x m_x²` at line 179 is **correct** — it is an
> **upper** bound, and it uses `|E[disp(x)]| ≤ m_x` in the direction the triangle inequality supplies.
> The very next sentence reverses it: to conclude `E[Σ disp²] ≥ m_x² = Θ(n²)` from a single
> `m_x = Θ(n)` you need `|E[disp(x)]| ≥ m_x`, i.e. `b_x ≥ m_x`, where
> `b_x := |E[pos_σ(x)] − rank_e(x)| = |E[A_x] − E[B_x]|`. **The only available relation is
> `b_x ≤ m_x`** (Identity 4.1 of `OneThird-Bbias-Locality-Lemma.md`, mg-a58f: `b_x` is the *difference*
> of the `e`-above and `e`-below inversion masses, `m_x` their *sum*; equality holds iff the mass is
> one-sided). This is the same `b`-versus-`m` conflation mg-a58f diagnoses as "the lossy step" —
> **used here in the opposite direction, where it is not lossy but invalid.**
>
> **Refuted by an explicit witness.** On `W_m = C_m ⊔ C_1` (mg-a58f §6.1, all values hand-computed and
> independently recomputed by the mg-d112 audit §2.3): `m_z = Θ(n)` and `E[inv_e] = Θ(n)` — exactly the
> hypothesis of the quoted sentence — yet `Σ_x E[disp_σ(x)]² = Σ_x b_x² ≤ n = Θ(n)`, **not** `Θ(n²)`.
> The inference fails on the very configuration it describes. *(Lemma (B) does fail on `W_m` — but
> through the **variance** term, which is not what the quoted argument claims. `W_m` also has
> `δ = 1/2`, so it is a separation of **quantities**, not of frozen-conditional statements.)*
>
> **Consequence for this document.** §2.3's *upper*-bound half stands unchanged, and with it the
> sufficiency direction "`max_x m_x = O(1)` ⟹ the deterministic part of (B)". What does **not** stand
> is the converse reading: **`max_x m_x = Θ(n)` does not falsify (B)**, so §2.3 does not establish that
> lemma (B) "hinges on" capping `max_x m_x`. See the further annotation at §3.2.
>
> **Provenance, and why the record is worth keeping.** Caught by the independent audit mg-d112 (§6.2)
> of the mg-a58f deliverable. mg-a58f itself **read this passage, quoted the display immediately above
> the error (line 179), and concluded "Both are correct"** — true of what it quoted, and one line short
> of the error. It had every tool needed to catch it (Identity 4.1, Observation 5.2, and `W_m` itself).
> Recorded plainly because *how the miss happened* is the durable value here: this is the second
> instance of the same defect family — an unflagged inequality-direction error in merged work, the
> first being mg-0ed7 §7.5, caught by mg-8f56. Both survived a prior review. The corresponding process
> repair is `STATE.md` Appendix A step **4b** (strength check + falsifier-quantifier check).

> ### ✅ INDEPENDENT RE-DERIVATION (2026-07-31, mg-fccb) — the direction above is CONFIRMED, and sharpened
>
> The annotation above was written from the mg-d112 audit report. mg-fccb re-derived the inequality
> **from scratch, from the definitions, without consulting that report's argument**, and reached the
> same verdict. Recorded because a direction error confirmed only against the report that found it is
> not independently confirmed.
>
> **The derivation.** With `disp_σ(x) = A_x − B_x` (§2.3's own decomposition: `A_x` = #`e`-above
> elements before `x`, `B_x` = #`e`-below elements after `x`, both `≥ 0`),
> ```
> m_x = E[A_x] + E[B_x]        a SUM of two non-negative terms
> b_x = |E[A_x] − E[B_x]|      a DIFFERENCE of the same two terms
> ```
> so `b_x ≤ m_x` by the triangle inequality, with **equality iff one of the two masses vanishes**.
> The struck sentence needs `b_x ≥ m_x`. That is available only in the equality case, i.e. only where
> the inversion mass is entirely one-sided. **Direction confirmed: `b_x ≤ m_x`, never the reverse.**
>
> **Exact refutation on `W_m`, recomputed from the definitions.** `W_m = C_m ⊔ C_1`, `n = m+1`,
> `|L(W_m)| = m+1` (`z` into one of `m+1` slots, uniform); `Pr[z <_σ c_i] = i/(m+1)`;
> `m_{zc_i} = min(i, m+1−i)/(m+1)`. For `m = 2s`:
> ```
> m_z = s(s+1)/(2s+1) = Θ(n)          E[inv_e] = m_z = Θ(n)          b_z = 0
> Σ_x b_x² = s(s+1)/(3(2s+1))         so   Σ_x b_x² / E[inv_e] = 1/3   EXACTLY, every even m
> ```
> The hypothesis of the struck sentence (`m_x = Θ(n)` and `E[inv_e] = Θ(n)`) holds on `W_m`, and its
> conclusion (`Θ(n²)`) is false there by a factor `n`: the deterministic part of (B) is satisfied on
> the nose, with constant `1/3`. The **exact ratio `1/3`** is new here — mg-d112 §2.3 established only
> the bound `Σ_x b_x² ≤ n`.
>
> **Where (B) does fail on `W_m`, quantified.** `Var(pos_σ z) = m(m+2)/12 = Θ(n²)` while
> `E[inv_e] = Θ(n)`, so `E[Σ disp²]/E[inv_e]` grows linearly in `m` (asymptotically `~ m/3`). The
> failure is **entirely** in the variance term; the deterministic term the struck sentence names is
> the one part of the sum that is healthy. *(`W_m` has `δ = 1/2`, so this separates the **quantities**,
> not the frozen-conditional **statements**.)*
>
> **Machine-checked.** `scripts/onethird_mgfccb_direction_check.py`, exact rational arithmetic, no
> sampling: `b_x ≤ m_x` holds in **31 625/31 625** (element, reference-order) cases over all posets on
> `n = 3,4,5` and every reference order, with **0** cases of `b_x > m_x` and `13 545` strictly lossy;
> `b_x = m_x` at the `e`-minimum in **6 385/6 385** cases (which is why §3.1 stands — see there); and
> the `1/3` ratio and the closed form `s(s+1)/(3(2s+1))` are confirmed exactly at every even
> `m ≤ 8`.

---

## 3. Lemma (B) — the wall, named

### 3.1 The falsifier mechanism: a bimodal chain-cross

Take `x` = the `e`-minimal element. Then `B_x = 0`, `disp_σ(x) = A_x`, and
`d_1 := d_x = E[A_x] = Σ_{y} Pr[y\text{ before }x]` (its whole displacement is `e`-above mass in
front of it). By (★)/§2.3, the `e`-min term alone needs `E[A_x²] = O(E[inv_e])`, and
`E[A_x²] ≥ d_1²`. So:

> **If `d_1 = Θ(n)` while `E[inv_e] = Θ(n)`, lemma (B) is false.**

`d_1 = Θ(n)` means `x` is, on average, `Θ(n)` positions deep despite (H) freezing it before each
incomparable partner. Decompose `x`'s incomparable set (which has width ≤ 2 under width 3, since
`x` + any antichain in it is an antichain) into chains `Y, Z`. For a chain `Y = y_1 <_P … <_P y_p`,
`{x\text{ before }y_1} ⊆ {x\text{ before }y_i}`, so `Pr[y_i\text{ before }x]` is decreasing in `i`
and `d_1`'s `Y`-contribution is `E[slot_Y] = Σ_a Pr[slot_Y ≥ a]`. `d_1 = Θ(n)` with all pairs
frozen forces `slot_Y` **bimodal** — `x` leads all of `Y` (`slot = 0`) w.p. `> 2/3`, but *trails
all of `Y`* (`slot = p`) w.p. `≈ 1/3` — i.e. `x` **crosses the entire frozen chain `Y` as one
block** a constant fraction of the time. This is the ticket's named risk verbatim ("an element
could cross a whole frozen chain and contribute `Θ(n)` to a displacement").

### 3.2 The open question (the wall)

> **Is a bimodal chain-cross realizable under a single frozen `e` in width 3?**
> Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with `E[inv_e] = O(n)`, δ < 1/3, width 3?

> ### ⚠️ ANNOTATION (2026-07-29, mg-1fdb): **"Equivalently" is not an equivalence** — same `b`-vs-`m` conflation as §2.3.
>
> The falsifier of §3.1 is derived **only at the `e`-minimal element**, where `B_x = 0`, so
> `disp_σ(x) = A_x`, `b_x = m_x`, and `E[A_x²] ≥ d_1²` genuinely does bound the (B) sum from below.
> That derivation is sound *at that element*. **Generalising it from the `e`-min to `max_x` is the
> invalid step**: away from the `e`-min the two masses cancel, and the only available relation is
> `b_x ≤ m_x` (Identity 4.1, mg-a58f), which points the wrong way. `W_m = C_m ⊔ C_1` realises
> `max_x m_x = Θ(n)` with `E[inv_e] = Θ(n)` and `max_x b_x ≤ 1` — the second display's hypothesis
> holds and (B)'s deterministic part does not fail.
>
> **So `max_x m_x = Θ(n)` with `E[inv_e] = O(n)` does *not* falsify (B-bias)**, and the second
> display is a *strictly stronger* question than the first, not an equivalent one. Since this section
> is this document's *"single pin"* and the origin of §5's recommendation 1, the effect on the record
> is sharper than bookkeeping: **the recommended target was not merely mis-priced (too strong — see
> mg-a58f Thm 3.2, `Σ_x m_x = 2E[inv_e]`, so a uniform `max_x m_x ≤ C` bound simply *is* LIB); it was
> also mis-derived as a falsifier.** The negation of §3.1's falsifier *at every element* is mg-a58f's
> (EQ), `max_x |E[pos_σ x] − rank_e x| = O(1)`, which is the object that actually does this section's
> job. Caught by the independent audit mg-d112 §6.2; not caught by mg-a58f. See §2.3's annotation.

Two opposing pressures make this genuinely undecided by elementary means:
- **Against.** Freezing `x` *before* a long incomparable chain requires `x` to be *pinned early*
  by order relations, but those relations are comparabilities (inversion-free), which *reduce*
  `m_x`. A bare incomparable chain gives uniform insertion — `Pr[x\text{ before }y_1] = 1/(p+1)`,
  *not* frozen. So the naive constructions of a large-`m_x` frozen element **fail to be frozen**
  (confirmed: §4, the genuine multi-element `x`-crosses-chain cases never reach δ < 1/3, staying
  at δ ≥ 0.357).
- **For.** Nothing elementary forbids a *coupling* element that makes `x`'s insertion bimodal
  while keeping every marginal pair `> 2/3`. Whether width 3 admits such a coupling at scale is
  exactly the unresolved correlation question of §2.2.

### 3.3 Why it cannot be settled empirically here

- **`n ≤ 9` ceiling.** Exact linear-extension enumeration is `O(n!)` (the b0a6 engine brute-filters
  permutations), so exact `disp²`/`inv` are computable only to `n ≤ 9`. This is the *same* ceiling
  at which mg-8201 already "could not exhibit a high-λ + quadratic-`E[inv_e]` poset."
- **Rarity ceiling.** Strictly-frozen (δ < 1/3) width-3 both-connected posets are vanishingly rare
  at small `n`: **20 000** random dense width-3 trials over `n ∈ {6,7,8,9}` produced **zero**
  (§4). The only frozen family in reach is the tight3 ordinal-sum tower (δ = 1/3 boundary), which
  is **thin** (`E[inv_e] = 2n/9`, ratio ≡ 2.0). The quadratic-`E[inv_e]` regime where `Cross`
  could blow up is thus doubly unreachable — by `n` and by rarity.

So the empirical locality-ratio flatness reported by mg-8201 (median 3.0, max 4.3, `~n^{0.12}`)
is measured **entirely inside the thin regime**; it is consistent with (B) but says nothing about
the regime that would refute it. **Empirical flatness is not a proof** (pm-onethird
`feedback_empirical_green_is_not_proven`).

### 3.4 Secondary gap: the Lipschitz constant `Λ = O(1)`

Even granting (A)+(B), the certificate chain needs
`energy(r) ≤ ½ Λ² E[Σ disp²]` with `Λ = max_k (w_{k+1} − w_k)` the largest gap of the **sorted**
expected-rank values `w_1 ≤ … ≤ w_n`. The band (§1.1) bounds the *range* of `d_k` but **not** the
consecutive sorted gap: it permits an `O(n)` gap in the expected-rank spectrum. Empirically
`d_k ≈ (2/3)k` with `Λ = O(1)` (tight3 tower), but `Λ = O(1)` is an additional
equidistribution/no-gap fact that is **not established** here. It is a smaller, separable gap
than (B), and rides on the same "expected ranks are smooth" theme.

---

## 4. Numerical checks (script `scripts/onethird_mgdbd1_L1b_spread_locality_probe.py`)

Reuses the mg-b0a6 `Poset`/LE engine; exact rationals via LE enumeration; deterministic.

- **Identity (★):** `n = 3,4,5` — `lhs = rhs` to `1e−9`, `E[inv]` printed. (★) confirmed.
- **tight3 tower** (δ = 1/3, ordinal sum, only reachable frozen family). Brute LE is `O(n!)`,
  so this script computes it to `n ≤ 9`; `band_ok = True`, locality ratio ≡ **2.000**,
  `max_x m_x = 0.67`, `d_1 = 0.33`, `max|disp| = 1` (bounded) — thin, (B) holds trivially. The
  **large-`n`** tower (via mg-8201's block-diagonal `analyze_osum`, no `n!` blowup, to `n = 36`)
  gives `‖r‖²/n³ → 1/12`, `1 − R(r) = (64/27)/n²`, `E[inv_e] = 2n/9`, ratio → 2 — cited from
  `data/onethird-mg8201-L1b-expected-rank.json`, not recomputed here.
- **`x`-crosses-chain constructions** (`p = 2…6`, two modes): the genuine multi-element cases
  keep δ **≥ 0.357** (never strictly frozen), ratio ≤ 3.33, `d_1 ≤ 0.25`, `max|disp| ≤ 3`,
  `band_ok = True`. The naive falsifier is **not frozen**.
- **Strictly-frozen random search** (`n ≤ 9`, 20 000 dense width-3 trials): **0** posets with
  δ < 1/3. The in-regime empirical test set is *empty* at reachable `n`.

Reproduce:
```
python3.11 scripts/onethird_mgdbd1_L1b_spread_locality_probe.py
```

---

## 5. Status and what remains

| sublemma | statement | status |
|---|---|---|
| **(A) SPREAD** | `‖r‖² = Ω(n³)` for frozen δ<1/3 | **PROVEN** (§1, band bound; `≥ (n−1)³/1152`) |
| **(B) LOCALITY** | `E[Σ disp²] = O(E[inv_e])` | **WALL** (§3): L2-vs-L1 gap `=` inversion-correlation `Cross` (★); bimodal chain-cross realizability open; doubly out of empirical reach |
| (aux) `Λ = O(1)` | no `O(n)` gap in sorted expected ranks | open, smaller (§3.4) |

**If (B) [and Λ] were also proven,** the certificate would yield, for every width-3 frozen
counterexample,
```
1 − λ_std(P) ≤ energy(r)/‖r‖² ≤ ½ Λ² E[Σ disp²] / Ω(n³) = O(E[inv_e]/n³) = O(1/n)  →  0,
```
i.e. `λ_std ≥ 1 − O(1/n)` **with no thin prefix and tolerating quadratic `E[inv_e]`** — this is
**L1b proven non-circularly** (bad mixing ⟹ `λ_std → 1`), the exact deliverable the certificate
was built to enable. (A) removes one of the two obstructions outright.

**Recommended next actions (recommendations only, no tickets filed):**
1. **Attack (B) as a correlation inequality**, not as "prove near-ordinal-sum": show
   `max_x m_x = O(1)` under frozen width-3, or bound `Cross` directly. This is the single pin.
2. **Or hunt the bimodal chain-cross** as a *large-`n`* construction (an `e`-min element trailing
   an incomparable frozen chain a constant fraction of the time with `E[inv_e] = O(n)`) — the
   explicit refuter of (B). If it does not exist, that non-existence *is* (B).
3. **Settle `Λ = O(1)`** (no `O(n)` gap in the expected-rank spectrum) — a separable, likely
   easier smoothness lemma than (B).

> ### ⚠️ ANNOTATION (2026-07-31, mg-fccb): **recommendations 1 and 2 both consumed §2.3's struck inference** — this is the propagation, and it was not previously flagged
>
> §2.3's annotation notes that the struck sentence is "the origin of §5's recommendation 1" but
> §5 itself was never marked. A direction error propagates silently — every consumer of it
> type-checks — so the consumers are annotated here explicitly. **Neither correction changes any
> proven statement in this document; both change what it recommends doing next.**
>
> **Recommendation 1 — "show `max_x m_x = O(1)` … This is the single pin." Two defects.**
> 1. **Mis-derived as a pin.** "Single pin" inherits §2.3's struck "lemma (B) therefore hinges on
>    … `m_x`". Since `max_x m_x = Θ(n)` does *not* falsify (B), `max_x m_x` is not the quantity (B)
>    hinges on, and rec 1 is not a pin. The quantity that does this job is the **bias** `b_x`.
> 2. **Mis-priced (this is mg-a58f's finding, recorded here at the consuming site).** By (F1)
>    `Σ_x m_x = 2E[inv_e]`, a uniform `max_x m_x ≤ C` gives `E[inv_e] ≤ Cn/2` — which *is* LIB,
>    `γ`-free — and with mg-210d's master bound that already yields `1 − λ_std = O(1/n)`, the whole
>    of L1b's conclusion. So rec 1 is **not a cheap step toward (B); it is at least as strong as the
>    wall it was proposed as an approach to.** (Nothing about it is false — it remains a valid
>    sufficient condition — it is simply not the small, separable target the wording offers.)
>
> **The replacement.** mg-a58f's **(EQ)** — `max_x b_x = O(1)`, `b_x := |E[pos_σ x] − rank_e x|` —
> is the negation of §3.1's falsifier *at every element* rather than only at the `e`-min. It is
> proven there to imply the deterministic part (B-bias) unconditionally and to imply §3.4's
> auxiliary `Λ = O(1)`, and it is strictly weaker than `max_x m_x = O(1)`. It leaves **(B-cov)** —
> the covariance/variance half — as the residual. **(EQ) does not close (B); it closes the half
> §2.3 is about.**
>
> **Recommendation 2 — "If it does not exist, that non-existence *is* (B)" is a converse over-read.**
> §3.1 proves one direction: a bimodal chain-cross at the `e`-min ⟹ (B) false. Its contrapositive is
> (B) ⟹ no such cross. Rec 2 asserts the **converse** — no cross ⟹ (B) — which does not follow.
> (B) governs the whole of `E[Σ_x disp²]`, and the deterministic term rec 2 rules out is only one of
> the two. On `W_m` the deterministic term is healthy (ratio exactly `1/3`) and **(B) fails anyway,
> entirely through the variance term** — the exact configuration rec 2's non-existence argument
> cannot see. Corrected reading: **the non-existence of a bimodal chain-cross is necessary for (B),
> not sufficient for it.**
>
> **Status-table row for (B).** "bimodal chain-cross realizability open" names one of the two ways
> (B) can fail. The variance/covariance route — `Cross` in §2.2, `(B-cov)` in mg-dcae's split — is
> the other, and is the one that actually breaks (B) on the document's own witness family. The row
> is narrow, not wrong; read `Cross` (already named in the same cell) as carrying that half.
>
> *(Cross-doc references in this annotation were checked at the far end: mg-a58f Thm 3.2/5.1/5.3 and
> the (EQ) definition in `OneThird-Bbias-Locality-Lemma.md`; the master bound in
> `probe-lambda-constant-bound.md` **Theorem 2.4** (§2, `[proven]`), which mg-a58f cites as (F2);
> (B-cov) in `OneThird-k1-Stanley-Stability-Scoping.md` §5 (mg-dcae). Verification ledger:
> `OneThird-mgd112-DroppedVerdict-Closeout.md` §4.)*

*(A) is done; (B) is reduced from a program-scale conjecture to a single named correlation
inequality with an explicit candidate refuter — the honest remaining content of L1b.*
