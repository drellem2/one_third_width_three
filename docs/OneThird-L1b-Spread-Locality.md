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
So **`max_x m_x = O(1)` ⟹ the deterministic part of (B) holds**; and by Jensen
`E[disp(x)²] ≥ E[disp(x)]²`, so if any single `m_x = Θ(n)` while `E[inv_e] = Θ(n)`, then
`E[Σ disp²] ≥ m_x² = Θ(n²)` and **(B) fails by a factor `n`**. Lemma (B) therefore hinges on
whether the frozen structure caps the per-element inversion degree `m_x` (and the analogous
variance tails).

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

*(A) is done; (B) is reduced from a program-scale conjecture to a single named correlation
inequality with an explicit candidate refuter — the honest remaining content of L1b.*
