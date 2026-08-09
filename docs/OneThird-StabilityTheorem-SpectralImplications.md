# OneThird — Immediate spectral-bound implications of the first Stanley-stability theorem attempt (mg-0ed7)

**Work item:** mg-8f56. **Input:** `docs/OneThird-MaShenfeld-NearSandwich-Stability.md` (mg-0ed7),
Theorems 4.1 and 7.2, Findings 5.2 / 6.5 / 7.3 / 7.4 / 7.5.
**Question (Daniel, verbatim):** *"I want to see the immediate spectral bound implications of the first
stability theorem attempt."*
**Constraint honored:** pure derivation. No enumerations, no datasets, no scripts, no Lean. The only
arithmetic is two hand tables on `n = 4` posets (§2.4, §5.2), each carried out in-line.

---

## 0. Verdict

> **The stability results reach exactly one of the three terms in the spectral budget, and at their
> proven strength they reach it vacuously. But the reason is NOT the §6.5 object mismatch — and
> locating that correctly is the main finding of this ticket.**

Four results, in decreasing order of consequence.

**1. §6.5 is not the binding obstruction on the `λ_std` path, because `λ_std` lives in the
absolute-position coordinate too. [proven]**
`λ_std` is the top eigenvalue on `𝟙⊥` of `S_P = (T_P + T_Pᵀ)/2` with `(T_P)_{x,a} = Pr[σ(a) = x]`. That
matrix **is** the array of absolute-position laws: `(T_P)_{x,i} = N_i(x)/e(P)`. And the program's
route to it — `(B) LOCALITY`, `E[Σ_x disp²] = Σ_x(Var(pos_σ x) + bias_x²)` — is *also* built entirely
from the absolute-position marginals. So `Φ` and `λ_std` are in the **same** coordinate. §6.5's proven
negative (`Φ` transfers to the gap/slot law iff `P∖{x}` is a chain) blocks `Φ → ρ_s → (decay)`, but
**`ρ_s` is an optional intermediate device, not a required destination.** The live path
`Φ → Var(pos) → (B) → λ_std` never enters the `ρ_s` coordinate and is therefore **not blocked by §6.5**.
It is blocked by three other things (findings 2–4).

**2. The one stated bridge from `Φ` to a spectral object is invalid as written. [proven — refuted]**
mg-0ed7 Finding 7.3 argues `Φ ≥ c ⟹ E[|I_x|²] = O(c^{-2}) ⟹ Σ_x Var = O(n/c²)`. The last step does not
follow. By conditional uniformity, the law of total variance gives an **exact two-term split**
$$\operatorname{Var}(\operatorname{pos}_σ x)\;=\;\underbrace{\mathbb E_ν\big[(|I_x|^2-1)/12\big]}_{\textbf{within-window}}\;+\;\underbrace{\operatorname{Var}_ν(\text{midpoint of } I_x)}_{\textbf{between-window}},\qquad ν(τ)\propto|I_x(τ)|,$$
and `Φ` sees **only the first term**. The second is genuinely unbounded by the first: for two parallel
`p`-chains with `x` inserted mid-chain (§4.2), `E_ν[|I_x|²] = O(1)` while
`Var(pos_σ x) = Θ(p) = Θ(n)`. Both terms are verified exactly on two `n = 4` posets (§2.4, §5.2). So
even granting `(LOC)`, mg-0ed7 §7.5's claimed harvest ("the variance half of (B)") does **not** follow.

**3. Theorem 4.1's spectral reach is zero unconditionally, and `Θ(1/n)` in its best corner. [blocked]**
Thm 4.1's RHS is `credit − debit` and is **not sign-definite** (mg-0ed7 §4.3: `C_3⊔C_3` has debit 3).
Ratio propagation — the only mechanism by which a deficit inequality ever reaches `Var(pos)` — needs
`N_i²/(N_{i−1}N_{i+1}) ≥ 1+c`. Thm 4.1 supplies no such bound without an independent handle on the
debits `P, R`, and §6.4 identifies paying the debits as *precisely what AF contributes*. In the corner
`P = R = 0` it does give a clean AF-free ratio bound (§3.2), but Finding 5.2 caps the achievable `c` at
`Θ(1/n)`, which yields `Var = O(n²)`, `Σ_x Var = O(n³)`, and `1 − λ_std ≤ O(Λ²)` — **no information**.

**4. Theorem 7.2's spectral output is exactly `1 − λ_std ≤ O(Λ² W²/n²)` for the within-window term
alone, which is (a) never better than the free bound `|I_x| ≤ W`, and (b) self-contradictory in the
regime where it would matter. [proven, vacuous]**
The proven output `Φ ≳ 1/(3W)` gives `E[|I_x|²] = O(W²)` — which is what `|I_x| ≤ W` gives for nothing.
Worse, Thm 7.2 is non-vacuous only when `ΦW ≪ 1` while its own conclusion is `Φ ≥ 1/(3W)`, i.e.
`ΦW ≥ 1/3`. **The hypothesis and the conclusion are incompatible.** That is Finding 7.4 restated in
spectral currency, and it is the sharpest possible statement of the block.

**Neither theorem says anything whatsoever about the BK gap `λ₂^BK`.** Both are functionals of the
stationary measure; `λ₂^BK` is the gap of a generator. Per mg-4a86 the two are not related by any
inequality in general (`λ_std ≤ λ₂^BK` fails on *every* ordinal sum, ∀`n`; mg-4a86's stronger
"and *exactly* there" reading was **refuted** by mg-d1be's exhaustive scan — true up to
isomorphism at `n ≤ 6`, false from `n = 7`, broken wholesale at `n = 8` over width `≤ 3`), and
Wilson (2004) already pins `gap_BK ≥ (1−cos(π/n))/(n−1)` universally — a bound no `Φ`-statement can
interact with. **[blocked, structural]**

**Net.** The honest immediate implication is: *the `Φ` currency buys one of the three terms of the
`(B)` budget — with room to spare if `Φ ≥ c = Ω(1)` were ever proven — and buys nothing at the strength
actually proven. The other two terms (window location, `(B-bias)`) are outside its reach, and the §6.5
mismatch, though real, is aimed at a coordinate the `λ_std` path does not need to visit.*

### Claim ledger

| # | Claim | Tag |
|---|---|---|
| S1 | `λ_std`, `Var(pos_σ x)`, `bias_x`, hence all of `(B)`, are functionals of the absolute-position marginals `N_·(x)` alone | **[proven]** (§1.2) |
| S2 | Therefore §6.5's mismatch does **not** block `Φ → (B) → λ_std`; it blocks only `Φ → ρ_s → (decay)`, an optional device | **[proven]** (§5.1) |
| S3 | Exact two-term variance split: within-window + between-window; `Φ` controls only the first | **[proven]** (§2.2), verified exactly on two `n=4` posets (§2.4, §5.2) |
| S4 | `E_ν[|I_x|²] = O(1)` does **not** imply `Var(pos_σ x) = O(1)`; two parallel `p`-chains give `O(1)` vs `Θ(n)` | **[proven]** (§4.2), classical negative-hypergeometric variance |
| S5 | mg-0ed7 Finding 7.3's inference `Φ ≥ c ⟹ Σ_x Var = O(n/c²)` is invalid as stated | **[proven — refuted]** (§4) |
| S6 | Whether the between-window term is controlled **under (H)+(LOC)** | **[open]** (§4.3) |
| S7 | Thm 4.1 gives no ratio bound, hence no variance bound, hence nothing for `λ_std`, unconditionally | **[proven]** (§3.1) |
| S8 | Thm 4.1 at `P=R=0` gives ratio `≥ 1 + [(B−C)² + S(2N_i−S)]/(N_{i−1}N_{i+1})`, AF-free | **[proven]** (§3.2) |
| S9 | That corner is capped at `c = Θ(1/n)` by Finding 5.2 ⟹ `1−λ_std ≤ O(Λ²)`, vacuous | **[proven, given Finding 5.2]** (§3.3) |
| S10 | Thm 7.2's within-window spectral output is `O(Λ²W²/n²)`; `(B)`-strength iff `W = O(√n)` | **[proven]** (§5.3) |
| S11 | Thm 7.2's non-vacuity condition `ΦW ≪ 1` contradicts its own conclusion `Φ ≥ 1/(3W)` | **[proven]** (§5.4) |
| S12 | Neither theorem reaches `λ₂^BK`; blocked by the static/dynamical category mismatch (mg-4a86) | **[proven, structural]** (§6) |
| S13 | §6.5's transfer works exactly on width `≤ 2`, where the conjecture is already Linial's theorem | **[proven]**, reach = zero (§5.5) |
| S14 | `(B-bias)` has no `Φ` content at all (mg-dcae Finding 5.3, re-confirmed here) | **[cited + re-confirmed]** (§2.3) |

---

## 1. The spectral objects, and which coordinate each one lives in

This section is bookkeeping, but it is where finding 1 comes from, so it is done explicitly.

### 1.1 The chain the program uses

From `docs/OneThird-L1b-CoreLemma-forDaniel.md` §3, the spectral certificate is

$$1-\lambda_{\mathrm{std}}(P)\;\le\;\frac{\mathrm{energy}(r)}{\|r\|^2}\;\le\;\tfrac12\Lambda^2\,\frac{\mathbb E\big[\sum_x \operatorname{disp}_σ(x)^2\big]}{\|r\|^2},\qquad r_x=\mathbb E[\operatorname{pos}_σ x]-\tfrac{n-1}{2},$$

with **(A) SPREAD** `‖r‖² = Ω(n³)` proven under (H), and **(B) LOCALITY**
`E[Σ_x disp²] = O(E[inv_e])` the open input. Granting both, `1 − λ_std = O(1/n) → 0`, which is the
porting lemma **L1** (`bad mixing ⟹ λ_std ≈ 1`) the near-ordinal-sum program consumes.

Downstream of `λ_std → 1`: prefix capture (empirically GREEN, mg-b0a6 kill-shot 4), thin interface,
near-ordinal-sum, balanced pair. **Nothing in this ticket touches anything downstream of `λ_std`.**

### 1.2 `λ_std`, `(B)`, and `Φ` are all in the absolute-position coordinate — [proven]

The transport operator is, by its definition in `onethird_mgb0a6_spectral_killshot_probe.py:263-296`
and mg-4a86 §1,
$$(T_P)_{x,a}=\Pr_{σ}[σ(a)=x]=\frac{N_a(x)}{e(P)},$$
i.e. **row `x` of `T_P` is exactly the absolute-position law `N_·(x)` of `x`, normalized**. Hence:

> **Observation 1.1 [proven].** `λ_std(P)` is a functional of the family of absolute-position
> marginals `{N_·(x)}_{x∈P}` and of nothing else. In particular it uses no joint information about `σ`
> beyond what those `n` one-element marginals carry.

The same is true one level down. Writing `pos_σ(x)`'s law as `N_·(x)/e(P)`,

$$\mathbb E\Big[\sum_x\operatorname{disp}_σ(x)^2\Big]\;\overset{\text{Identity 5.1 (mg-dcae)}}{=}\;\sum_x\operatorname{Var}\big(\operatorname{pos}_σ x\big)\;+\;\sum_x\big(\mathbb E[\operatorname{pos}_σ x]-\operatorname{rank}_e x\big)^2,$$

and both summands are computed from the marginals alone. So:

> **Observation 1.2 [proven].** The **left-hand side of (B) is a functional of the absolute-position
> marginals.** (Its right-hand side `E[inv_e]` is a *pairwise* object, and that asymmetry — marginal
> LHS, pairwise RHS — is where the real difficulty of (B) sits; it is not a coordinate mismatch.)

And `Φ_i(x) = Pr[i` is an endpoint of `I_x(τ) | i ∈ I_x(τ)]` is a functional of the **insertion-interval
family** of `x`, which is a *refinement* of the marginal `N_·(x)` (`N_i(x) = #{τ : i ∈ I_x(τ)}`, while
`Φ` additionally reads the joint law of the two endpoints `(ℓ_τ, r_τ)`).

**Conclusion of §1.** `Φ ⟶ Var(pos) ⟶ (B) ⟶ λ_std` is a chain **within one coordinate system**. This
is the fact §5 uses to overturn the presumption that §6.5 blocks everything.

### 1.3 What is *not* in that coordinate

- **`ρ_s = q_{s+1}/q_s`** with `q_s = Pr[c_s ≺_σ x]` — the gap/slot coordinate. §6.5's target.
- **`M_{k,l}` / (decay)** — a *joint two-cut* object counting elements whose displacement interval
  spans a whole block. Not a one-element marginal at all.
- **`λ₂^BK`** — a dynamical functional, of a generator, not of the measure. §6.

---

## 2. The variance split: what `Φ` can and cannot see

### 2.1 Setup

For `τ ∈ L(P∖x)` the admissible insertion slots form the interval `I_x(τ) = [ℓ_τ, r_τ]`, and
`pos_σ(x) | τ ~ Uniform(I_x(τ))` (conditional uniformity, mg-a1ec Prop. 4.1). The `σ`-uniform law
weights `τ` by interval length: `ν(τ) = |I_x(τ)|/e(P)`.

### 2.2 The split — [proven]

> **Proposition 2.1 (exact; PROVEN, new to this arc's write-ups).** *For every finite poset `P` and
> every `x ∈ P`,*
> $$\operatorname{Var}\big(\operatorname{pos}_σ x\big)\;=\;\underbrace{\mathbb E_ν\!\left[\frac{|I_x|^2-1}{12}\right]}_{\textbf{(V-in)} \text{ within-window}}\;+\;\underbrace{\operatorname{Var}_ν\!\big(m_τ\big)}_{\textbf{(V-out)} \text{ between-window}},\qquad m_τ:=\tfrac{ℓ_τ+r_τ}{2}.$$
>
> **Proof.** Law of total variance conditioning on `τ`, plus `Var(Unif[ℓ,r]) = (|I|²−1)/12` and
> `E[Unif[ℓ,r]] = m_τ`. ∎

**This is the exact form of mg-0ed7 §7.3's inequality `Var ≥ E[(|I|²−1)/12]`, with the missing term
named.** mg-0ed7 states the inequality correctly and then uses it in the wrong direction (§4).

> **Corollary 2.2 [proven].** *A hazard/endpoint lower bound `Φ ≥ c` over the support controls
> **(V-in)** only:* `E_ν[|I_x|²] = O(c^{-2})` *(geometric tail at rate `1−c`), hence*
> `(V-in) = O(c^{-2})`. *It says nothing about **(V-out)**.*

### 2.3 The three-term spectral budget

Assembling §1.1, Identity 5.1 and Prop. 2.1:

$$1-\lambda_{\mathrm{std}}\;\le\;\frac{\Lambda^2}{2\,\|r\|^2}\Big[\underbrace{\textstyle\sum_x (\text{V-in})_x}_{\textbf{T1}}\;+\;\underbrace{\textstyle\sum_x (\text{V-out})_x}_{\textbf{T2}}\;+\;\underbrace{\textstyle\sum_x \big(\mathbb E[\operatorname{pos}_σ x]-\operatorname{rank}_e x\big)^2}_{\textbf{T3 = (B-bias)}}\Big],\qquad \|r\|^2=\Omega(n^3).$$

> **This display is the answer to the ticket.** Every spectral implication of mg-0ed7 below is a
> statement about **T1 and T1 only**.
> - **T1** — the only term `Φ` sees. Needs `Σ_x (V-in)_x = O(n²)` to be harmless, i.e.
>   `max_x E_ν[|I_x|²] = O(n)`, i.e. `c = Ω(n^{-1/2})`.
> - **T2** — the window-*location* variance. Untouched by `Φ` (§4). Not previously named in this arc.
> - **T3** — `(B-bias)`. mg-dcae Finding 5.3: *"has NO Stanley content whatsoever."* Re-confirmed
>   here: it is a first-moment (bias) object, while `Φ` is an interval-shape object; no `k=1` Stanley
>   or Ma–Shenfeld statement constrains `E[pos_σ x]` at all. **[cited + re-confirmed]**

### 2.4 Exact hand check of Prop. 2.1, `n = 4` — `C_2 ⊔ C_2`

The ticket's suggested check. `P = C_2 ⊔ C_2 = \{u_1<u_2\} ⊔ \{v_1<v_2\}`, `x := u_1`. Then `D(x) = ∅`
so `ℓ_τ ≡ 1` (a staircase), and `N = (3,2,1)`, `e(P) = 6`, `e(P∖x) = 3` (mg-0ed7 §4.2 table). The three
`τ ∈ L(P∖x)` are `(u_2,v_1,v_2)`, `(v_1,u_2,v_2)`, `(v_1,v_2,u_2)`, giving `r_τ = 1,2,3` and widths
`1,2,3`, so `ν = (1/6, 2/6, 3/6)` and midpoints `m_τ = 1, 3/2, 2`.

| quantity | value |
|---|---|
| law of `pos_σ(x)` | `(1/2, 1/3, 1/6)` on `{1,2,3}` |
| `E[pos]`, `E[pos²]` | `5/3`, `10/3` |
| `Var(pos_σ x)` | **`5/9`** |
| **(V-in)** `= E_ν[(|I|²−1)/12]` | `0 + (1/3)(3/12) + (1/2)(8/12) = ` **`5/12`** |
| **(V-out)** `= Var_ν(m_τ)` | `35/12 − 25/9 = ` **`5/36`** |
| sum | `15/36 + 5/36 = 20/36 = ` **`5/9`** ✔ |

Prop. 2.1 checks exactly. Note `Φ_2 = h_2 = 1/2` here (mg-0ed7 Lemma 5.1) — a **large** near-sandwich
distance — and yet `(V-out)` is a full 25 % of the variance. **On the very family mg-0ed7 Finding 7.3
offers as a *confirming* instance for `Φ`-stability, the term `Φ` cannot see is already `Θ(1)` of the
answer.**

---

## 3. Theorem 4.1 → spectra

**Thm 4.1.** `|N^=|² − |N^−||N^+| ≥ (B−C)² + S(2|N^=|−S) − [P(A+2C) + R(A+2B) + PR]`, on the
absolute-position sequence `N_i`, AF-free, with equality iff MS Lemma 3.1(iv),(v) are bijections.

### 3.1 Unconditional reach: **zero**. [blocked at the debit]

The **only** mechanism by which a deficit inequality has ever been proposed to reach a spectral object
in this arc is *ratio propagation* (mg-dcae §2.1): a uniform ratio bound
`N_i²/(N_{i−1}N_{i+1}) ≥ 1 + c` over the support forces geometric decay of `N` away from its mode,
hence `Var(pos_σ x) = O(c^{-2})`, hence a bound on **T1** (and, note, only on T1 — the marginal `N_·(x)`
carries `(V-in)+(V-out)` jointly, so a genuine ratio bound would actually bound `T1 + T2` for that
element; see §4.4 for why this does not rescue anything).

Thm 4.1 delivers a ratio bound iff `credit − debit ≥ c·N_{i−1}N_{i+1}`. Its RHS is **not sign-definite**:
mg-0ed7's own `C_3⊔C_3` row has `credit = 9`, `debit = 3`, and §4.3 states plainly that the RHS "is
genuinely negative in general."

> **Finding 3.1 [proven].** *Theorem 4.1, taken unconditionally, implies **no** lower bound on
> `N_i²/(N_{i−1}N_{i+1})`, hence **no** upper bound on `Var(pos_σ x)`, hence **no** bound on `T1`,
> hence **nothing about `λ_std`**. It is strictly weaker than Stanley's inequality (`deficit ≥ 0`),
> which it does not recover.*

The block is exactly located: it is the debit pair `(P, R)` — Cor. 3.3's *outer-index double-wall*
counts. And mg-0ed7 §6.4 identifies paying those debits as **precisely the content AF supplies at
`k=1`**. So Thm 4.1's spectral vacuity is the same wall as Shenfeld–van Handel's no-compact-resolvent
remark (mg-dcae §4.1, wall 2), reached from the combinatorial side. **This is a useful localization:
"Thm 4.1 is AF-free" and "Thm 4.1 has no spectral consequences" are the same statement.**

### 3.2 The one non-vacuous corner: `P = R = 0`. [proven, conditional]

> **Corollary 3.2 (immediate; PROVEN).** *At an index `i` where the outer double-walls vanish
> (`P = R = 0`, i.e. no `τ` has two consecutive `U(x)`-elements starting at `r_τ = i−1` and none has
> two consecutive `D(x)`-elements ending at `ℓ_τ = i+1`),*
> $$\frac{N_i^2}{N_{i-1}N_{i+1}}\;\ge\;1+\frac{(B-C)^2+S\,(2N_i-S)}{N_{i-1}N_{i+1}}\;\ge\;1+\frac{S_i\,N_i}{N_{i-1}N_{i+1}},$$
> *using `S ≤ N_i`. Writing `s_i := S_i/N_i = Pr[I_x(τ) = \{i\} \mid i ∈ I_x(τ)] ≤ Φ_i`, and using
> `N_{i±1} ≤ N_i·(1+o(1))` on a near-flat window, this reads* `ratio − 1 ≳ s_i`.

This is **AF-free, elementary, and genuinely a `deficit ≥ c·(part of Φ)` bound** — of exactly the shape
Finding 5.2 declares impossible. There is no contradiction: Finding 5.2's obstruction family is the
staircase, where `C = S = 0` identically and the credit degenerates to `B²` while the debit `P` grows
to cancel it. **Corollary 3.2 is precisely the statement that the obstruction is carried by the
debits, not by the credit ledger.** That is a small positive and it is the honest maximum of Thm 4.1's
reach.

### 3.3 …and even that corner is capped at `Θ(1/n)`. [proven, given Finding 5.2]

Corollary 3.2 needs to hold at `Θ(n)` consecutive indices to propagate. But mg-dcae Finding 3.1 and
mg-0ed7 Finding 5.2 together cap the achievable per-index ratio gain at `c = Θ(1/n)` in the regime that
matters (the deficit is a hazard *increment*, and posets accumulate on the geometric ray at rate
`Θ(1/n)`). Feeding `c = Θ(1/n)` through §3.1:

$$\operatorname{Var}(\operatorname{pos}_σ x)=O(c^{-2})=O(n^2)\;\Longrightarrow\;\mathbf{T1+T2}=O(n^3)\;\Longrightarrow\;1-\lambda_{\mathrm{std}}\;\le\;O\!\left(\frac{\Lambda^2 n^3}{n^3}\right)=O(\Lambda^2).$$

> **Finding 3.3 [proven].** *`1 − λ_std ≤ O(Λ²)` is **no information** — `1 − λ_std ≤ 1` holds for
> free. Even in its most favourable corner, and even granting the corner at every index, Theorem 4.1
> yields a **vacuous** bound on `λ_std`. The `n³`-vs-`n` gap mg-dcae §5.3 named between "achievable"
> and "usable" is exactly the gap between `Θ(Λ²)` and `Θ(1/n)` here.*

### 3.4 Thm 4.1 → `ρ_s`, `(decay)`, `λ₂^BK`

- **`ρ_s`:** blocked twice. §6.5 (no coordinate transfer except width `≤ 2`), and mg-dcae §5.5 (the
  `ρ_s` route has no propagation step at all, gap-law log-concavity being numerically false per
  mg-2acf). **[blocked]**
- **`(decay)` / `M_{k,l}`:** `M_{k,l}` is a *joint two-cut* count; Thm 4.1 constrains a *single
  element's one-index* marginal. There is no implication, and the reason is the arc's recorded
  marginals-vs-joint wall (`L1b-CoreLemma` §5: *"Decay must come from the joint LE structure, not the
  marginals"*). **[blocked, structural]**
- **`λ₂^BK`:** see §6. **[blocked, structural]**

---

## 4. The missing term — mg-0ed7 Finding 7.3's inference is invalid

This section is the one place where this ticket **overturns** a claim of its input document, so it is
argued in full.

### 4.1 The claim at issue

mg-0ed7 §7.3 (and §7.5, which the whole forward recommendation rests on):

> *"by conditional uniformity, `Var(pos_σ(x)) ≥ E[(|I_x(τ)|² − 1)/12]`, and a lower bound `Φ ≥ c` on
> the hazard directly bounds `E[|I|²] = O(c^{-2})` — hence `Σ_x Var = O(n/c²)`, exactly (B)'s
> requirement at `c = Θ(1)`."*

The inequality is correct and the middle step is correct. **The conclusion inverts the inequality**:
from `Var ≥ A` and `A = O(c^{-2})` one cannot infer `Var = O(c^{-2})`. By Prop. 2.1 the exact statement
is `Var = A + (V-out)`, and the argument bounds `A` only.

### 4.2 The gap is real: `E_ν[|I_x|²] = O(1)` with `Var(pos_σ x) = Θ(n)`. [proven]

> **Construction 4.2 (PROVEN).** *For `p ≥ 2` let `P_p` be: two incomparable chains
> `A: a_1<\cdots<a_p` and `B: b_1<\cdots<b_p`, plus one element `x` with `a_k <_P x <_P a_{k+1}`,
> `k := \lceil p/2\rceil`. Then `n = 2p+1`, and*
> $$\mathbb E_ν\big[|I_x|^2\big]=O(1)\qquad\text{while}\qquad \operatorname{Var}\big(\operatorname{pos}_σ x\big)=\Theta(p)=\Theta(n).$$

**Proof.** `L(P∖x)` is the set of uniform interleavings of `A` and `B` — `\binom{2p}{p}` words.
`I_x(τ)` is the set of slots strictly between `a_k` and `a_{k+1}`, so
`|I_x(τ)| = 1 + G`, `G := \#\{b\text{'s strictly between } a_k \text{ and } a_{k+1}\}`.

*Width is `O(1)`.* `Pr[G ≥ g]` is the probability that the `g` symbols following `a_k` are all `b`'s.
Conditioned on any prefix ending at `a_k`, the remaining multiset contains at most `p` `b`'s and at
least `p − k ≥ p/2 − 1` `a`'s, so each successive symbol is a `b` with probability at most
`p/(p + p/2 − 1) → 2/3`. Hence `Pr[G ≥ g] ≤ (2/3 + o(1))^g`, giving `E[G²] = O(1)` and
`E_ν[|I_x|²] = O(1)` (the `ν`-reweighting by `|I_x| = 1+G` costs one more factor of the same geometric
tail). ∎(part 1)

*Location has variance `Θ(p)`.* `m_τ = pos_τ(a_k) + (1+G)/2` and `pos_τ(a_k) = k + Y` where
`Y := \#\{b\text{'s before } a_k\}`. `Y` is negative-hypergeometric with
`Pr[Y=y] = \binom{k-1+y}{y}\binom{2p-k-y}{p-y}/\binom{2p}{p}`; at `k = \lceil p/2\rceil` its variance is
`Θ(p)` (classical). Since `G` has bounded variance, `Var_ν(m_τ) = Θ(p)`, and Prop. 2.1 gives
`Var(pos_σ x) ≥ Var_ν(m_τ) = Θ(p)`. ∎

> **Finding 4.2 [proven — refutes the inference].** *The step "`E[|I_x|²] = O(c^{-2})` ⟹
> `Var(pos_σ x) = O(c^{-2})`" is **false as an implication**. `Φ` can be as strong as it is ever
> possible for it to be (windows of bounded length, so the `σ`-average of `Φ` is `Θ(1)`) while the
> variance it is supposed to bound is `Θ(n)`. The missing quantity is the **location** of the insertion
> window, which is a property of the joint placement of `D(x) ∪ U(x)` and is invisible to any
> functional of the interval-length/endpoint statistics.*

### 4.3 What this does and does not kill — [open]

**Does not kill.** `P_p` is **not frozen** (`δ(P_p) = 1/2`; e.g. `Pr[b_k ≺_σ x] ≈ 1/2`). Finding 7.3's
inference is *stated unconditionally*, so a non-frozen witness refutes it as an implication — but it
leaves open whether the inference can be **repaired under (H)**, or under (H)+(LOC).

Note that `P_p` also violates `(LOC)`: for `x` the incomparable set is all of `B`, and
`Σ_{b∈B}\Pr[\{x,b\}\text{ inverts}] = Θ(\sqrt p)` (the width of the `Θ(\sqrt p)` fluctuation window of
`Y`), not `O(1)`. **So `P_p` does not refute the (LOC)-conditional form.**

> **Finding 4.3 [open — the repair target this ticket surfaces].** *Does `(H)` (or `(H)+(LOC)`) bound
> `\sum_x \operatorname{Var}_ν(m_x)` — the **T2** term? Nothing in mg-0ed7, mg-48ab, mg-dcae or the
> `L1b` docs addresses it, because the term had not been named. It is a **joint** object (the spread of
> the down-set/up-set boundary), which places it on the far side of the arc's marginals-vs-joint wall;
> the prior is therefore that `(LOC)`, a first-moment marginal hypothesis, does **not** control it.
> But that is a prediction, not a proof.*

**Consequence for mg-0ed7's forward recommendation.** §7.5's reduction — *"(LOC) ⟹ `Φ ≥ cε` ⟹
`Var = O(ε^{-2})` ⟹ the variance half of (B)"* — must be restated as:

> `(LOC)` `⟹` `Φ ≥ cε` `⟹` **T1** `= O(n/ε²)`. **T2 and T3 remain open.**

`(LOC)` does independently close **T3** via mg-dcae Prop. 5.4 (modulo the unproven equivalence of the
two `(LOC)` formulations, flagged [heuristic] in mg-0ed7 §8). So the honest tally is: **`(LOC)` would
close two of the three terms, and the third — T2 — is newly exposed and unaddressed.** That is a
weaker, but much better-specified, forward statement than the one in the input document.

### 4.4 Why a genuine *ratio* bound would have been different

Worth recording, because it explains why the deficit route was ever attractive. A ratio bound
`N_i²/(N_{i−1}N_{i+1}) ≥ 1+c` is a statement about the **marginal** `N_·(x)`, and `Var(pos_σ x)` is a
functional of that same marginal — so a ratio bound bounds `T1 + T2` **together**, with no missing
term. A `Φ` bound is a statement about the **interval family**, which is finer in one direction
(endpoints) and blind in another (location). **This is the precise sense in which mg-0ed7's
re-denomination from the deficit currency to the `Φ` currency (Finding 7.3) trades one deficiency for
another**: the deficit reaches the whole variance but cannot be lower-bounded (Finding 5.2); `Φ` can be
lower-bounded (conditionally, Thm 7.2) but reaches only part of the variance (Finding 4.2). Neither
half of the trade was visible from inside mg-0ed7.

---

## 5. Theorem 7.2 → spectra, and the §6.5 confrontation

**Thm 7.2.** `1/3 + 2ε ≤ (1 − π(1−WΦ)) + (Λ_Φ+1)/W`, with `Λ_Φ := Σ_{z ∥ x} Pr[y⁻ <_σ z <_σ y⁺]`.
Proven output (Finding 7.4): `Φ ≳ 1/(3W)`.
*(Note: mg-0ed7's `Λ` is unrelated to the certificate's Lipschitz constant `Λ`; written `Λ_Φ` here.)*

### 5.1 Confronting §6.5 — the mismatch is real but is aimed at the wrong coordinate. [proven]

The ticket asks whether §6.5 blocks the transfer. The answer has two halves.

**(i) For `ρ_s` / `(decay)`: yes, blocked, exactly as §6.5 proves.** `Φ` lives on endpoints of
`I_x(τ)` in the absolute-position coordinate; the gap law `a_m = e(P_m)` marginalizes over everything
off the chain `C`, so a single gap index pulls back to a union of slot ranges across many `τ`.
Finding 6.5: transfer holds **iff `P∖{x}` is the chain `C`**. **[blocked]** — and doubly so, since
mg-dcae §5.5 shows the `ρ_s` route has no propagation mechanism even if a drop were supplied.

**(ii) For `λ_std` / `(B)`: no, not blocked — and this is the correction.** By Observations 1.1–1.2,
`λ_std` and both sides of the `Σ_x disp²` decomposition are functionals of the absolute-position
marginals. The `ρ_s` coordinate appears in this program **only** as an intermediate device inside the
`(decay)` formulation of `(B)` (via `(GID)` and `M_{k,l}`), and `(GID)`+`(DG)` are an *equivalent
repackaging* of the same `Σ_x disp²`, not a different destination:

$$\textbf{(B)}\iff \mathbb E\Big[\sum_x\operatorname{disp}^2\Big]=O(\mathbb E[\operatorname{inv}_e])\iff \sum_{k<l}\mathbb E[M_{k,l}]=O(\mathbb E[\operatorname{inv}_e])\iff \textbf{(decay)}\text{'s target}.$$

So `Φ` may attack `(B)` **directly through `Σ_x Var + Σ_x bias²`**, never entering the `ρ_s`/`M_{k,l}`
coordinate at all.

> **Finding 5.1 [proven].** *The §6.5 object mismatch does **not** block the stability results from
> reaching `λ_std`. It blocks only the `ρ_s`/`(decay)` packaging, which is one of two equivalent
> formulations of the same obligation. **The blocks that do bind on the `λ_std` path are different
> ones**: (a) the debit term for Thm 4.1 (§3.1); (b) the rate cap `Θ(1/n)` (§3.3); (c) the missing
> **T2** term (§4); (d) **T3 = (B-bias)**, which has no `Φ` content (§2.3); and (e) for Thm 7.2, an
> internal incompatibility between its hypothesis and its conclusion (§5.4).*

**Why this matters practically.** If one believed §6.5 blocked everything, the correct action would be
to abandon the `Φ` currency. It does not, so the correct action is narrower: `Φ` is a live currency for
**T1**, and the arc should stop describing the mismatch as the obstruction on the `λ_std` route.

### 5.2 Exact hand check that (V-out) is not an artifact of staircases, `n = 4`

`§2.4`'s example is a staircase (`ℓ_τ ≡ 1`), where one might suspect `(V-out)` is an artifact of the
left endpoint being pinned. Second hand check with a two-sided window:
`P = \{d <_P x <_P u\} ⊔ \{c\}`, `n = 4`, `e(P) = 4`, `e(P∖x) = 3`.

| `τ` | `pos(d), pos(u)` | `I_x(τ)` | `|I|` | `m_τ` |
|---|---|---|---|---|
| `d,u,c` | 1, 2 | `[2,2]` | 1 | 2 |
| `d,c,u` | 1, 3 | `[2,3]` | 2 | 5/2 |
| `c,d,u` | 2, 3 | `[3,3]` | 1 | 3 |

`ν = (1/4, 1/2, 1/4)`. Law of `pos_σ(x)`: `(1/2, 1/2)` on `{2,3}`, so `Var = 1/4`.
**(V-in)** `= (1/2)(3/12) = 1/8`. **(V-out)** `= 51/8 − 25/4 = 1/8`. Sum `= 1/4` ✔.

Here **(V-out) is exactly half the variance**, with a two-sided, genuinely mobile window. Prop. 2.1
checks exactly a second time, and the term is not a staircase artifact.

### 5.3 The spectral output of Thm 7.2 at its proven strength. [proven, vacuous]

Feed `Φ ≳ 1/(3W)` (Finding 7.4) through Corollary 2.2 and §2.3:

$$\mathbb E_ν[|I_x|^2]=O(W^2)\;\Longrightarrow\;\mathbf{T1}=O(nW^2)\;\Longrightarrow\;\text{(T1's contribution to)}\;\;1-\lambda_{\mathrm{std}}\;\le\;O\!\left(\frac{\Lambda^2 W^2}{n^2}\right).$$

> **Finding 5.3 [proven].** *Theorem 7.2's immediate spectral implication is exactly*
> `1 − λ_std ≤ O(Λ²W²/n²)` *for the **T1** term alone. It reaches `(B)`-strength (`O(1/n)`) iff
> `W = O(\sqrt n)`, is non-trivial only for `W = o(n)`, and at `W = Θ(n)` degenerates to
> `1 − λ_std ≤ O(Λ²)` — **no information**. **T2 and T3 are untouched at every `W`.***

**And it is never better than free.** `Φ ≥ 1/(3W)` produces `E[|I_x|²] = O(W²)`, but `|I_x| ≤ W` on a
window of width `W` gives `E[|I_x|²] ≤ W²` **with no theorem at all**. Theorem 7.2's spectral content
is therefore not merely weak — at this strength it is **exactly the trivial bound**, which is Finding
7.4 ("recovers the trivial averaging bound and no more") expressed in the spectral currency.

### 5.4 The internal incompatibility — the sharpest form of the block. [proven]

> **Finding 5.4 [proven].** *Theorem 7.2 is non-vacuous only in the near-flat regime `Φ·W ≪ 1`
> (mg-0ed7 §0, §7.4). Its conclusion is `Φ ≥ 1/(3W)`, i.e. `Φ·W ≥ 1/3`. **The regime in which the
> theorem carries information and the regime its own conclusion asserts are disjoint.** There is no
> `W` at which Theorem 7.2 both applies non-vacuously and yields a `Φ` bound stronger than the
> averaging identity `\overline{Φ} = Θ(1/\mathbb E[|I_x|])`.*

This is not a criticism of Theorem 7.2 as a theorem — mg-0ed7 proves it correctly and verifies it
recovers mg-48ab Thm 5.2 exactly at `Φ = 0`. It is a statement that **its spectral harvest is empty**,
and that the emptiness is structural rather than a matter of constants.

### 5.5 The conditional statement, and the width `≤ 2` corner

**Conditional (the honest positive).** Under `(LOC)`: `Λ_Φ = O(1)`, take `W = Θ(Λ_Φ) = Θ(1)`, and
Theorem 7.2 gives `Φ ≥ cε` on the mass-carrying window. Then

$$\mathbf{T1}=O(n/ε^2)\;\Longrightarrow\;\text{(T1's contribution to)}\;\;1-\lambda_{\mathrm{std}}\;=\;O\!\left(\frac{\Lambda^2}{ε^2 n^2}\right)=o(1/n).$$

> **Finding 5.5 [proven as a reduction].** *Under `(LOC)`, Theorem 7.2 gives the **T1** term with room
> to spare — `o(1/n)` against a `(B)`-budget of `O(1/n)`. This is the **entire** positive spectral
> content of mg-0ed7, and it is one of three terms. `(LOC)` additionally closes **T3** via mg-dcae
> Prop. 5.4 (modulo the unproven equivalence of the two `(LOC)` forms). **T2 remains open (§4.3).***

**Width `≤ 2` (the §6.5 transfer corner) — reach is zero. [proven]** §6.5's transfer holds iff `P∖{x}`
is the chain `C`, i.e. `P` = a chain plus one element, so `width(P) ≤ 2`. There, `|L(P∖x)| = 1`, there
is a single interval `I_x`, `pos_σ(x)` is exactly uniform on it, and everything is explicit:
`Var(pos_σ x) = (|I_x|²−1)/12` with `(V-out) = 0`, `Φ_i = 0` on the interior and `1` at the two
endpoints, and the gap law and absolute law coincide. So the stability bound transfers, exactly,
and gives the exact answer.

> **Finding 5.6 [proven].** *The single class on which §6.5's transfer succeeds is `width(P) ≤ 2`,
> where the 1/3–2/3 conjecture is **already a theorem** (Linial 1984, with `δ ≥ 1/3`), so no frozen
> poset exists there and every frozen-conditional statement is vacuously true. **The transfer works
> exactly where there is nothing to transfer.** This is the sharpest available statement of §6.5's
> reach, and it is the reason the width-`≤ 2` escape hatch should not be developed further.*

---

## 6. Neither theorem reaches the BK gap `λ₂^BK` — [blocked, structural]

Per the ticket's explicit instruction to keep the static and dynamical objects apart (the mg-4a86
lesson), stated separately:

- `Φ_i(x)`, `N_i(x)`, the deficit, `Var(pos_σ x)`, `(B)`, and `λ_std` are **all functionals of the
  stationary measure `Unif L(P)`** (§1.2). Nothing above involves a generator.
- `λ₂^BK` is the second eigenvalue of the **BK adjacent-transposition chain** on `L(P)` — a dynamical
  functional. mg-4a86 §0: *"Every technique in the toolkit — decomposition, tempering,
  Diaconis–Saloff-Coste, censoring — produces inequalities between Dirichlet forms. None can have
  `λ_std` as an endpoint, because `λ_std` is not the gap of any chain in the family."*
- There is no inequality to borrow: **SD-BK (`λ₂^BK = λ_std`) is FALSE**, 0/195 at `n=4` and 0/4111 at
  `n=5` (mg-4a86 C2), and even the weak form `λ_std ≤ λ₂^BK` **fails on every ordinal sum**
  (C3, `⟸` proven ∀`n`). **Do not reach for C3's "and *exactly* there" clause as an escape
  hatch — mg-d1be refuted it**: the set equality holds exhaustively at `n ≤ 6`, takes its first
  hit at `n = 7` (an *indecomposable* violator), and breaks **wholesale at `n = 8`** — 19
  indecomposable violators, 16 of **width exactly 3**, each certified by an exact separating
  rational. It is a small-`n` coincidence, not a characterization with exceptions, so neither
  indecomposability nor width-3 restores it
  ([`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md`](OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md) §(e)).
  Standard dominance is available only in the `SD-quant` overlap form and only
  **conditional on the all-pairs-frozen regime**; it is not a universal fact and must not be invoked
  as one.
- And the direction the program actually uses runs the other way (`bad BK mixing ⟹ λ_std ≈ 1`, L1), so
  a `Φ` bound sits on the *conclusion* side of that porting lemma, not the hypothesis side.
- Finally, `λ₂^BK` is already pinned from below universally: **Wilson (2004)**,
  `gap_BK(P) ≥ (1−\cos(π/n))/(n−1) = Θ(n^{-3})` for every `n`-element poset, verified 0/4306 violations
  at `n ≤ 5` (mg-4a86 C7). No statement about `Φ` can improve, contradict, or interact with it.

> **Finding 6.1 [proven, structural].** *Theorems 4.1 and 7.2 imply **nothing whatsoever** about
> `λ₂^BK`, and the obstruction is a category mismatch, not a missing lemma. Any future write-up
> claiming "the stability theorem bounds the spectral gap" must say **which** gap; for these two
> theorems the answer is `λ_std` (partially, term **T1**) and never `λ₂^BK`.*

---

## 7. Verdict — the immediate bounds, with exact reach

| # | Input | Spectral object | Immediate implication | Reach |
|---|---|---|---|---|
| 1 | **Thm 4.1**, unconditional | `λ_std` | **none** — RHS not sign-definite ⟹ no ratio bound ⟹ no variance bound | **[blocked]** at the debit `(P,R)`; = what AF pays for (§6.4) |
| 2 | **Thm 4.1**, at `P=R=0` | `λ_std` via **T1+T2** | `N_i²/(N_{i−1}N_{i+1}) ≥ 1 + [(B−C)²+S(2N_i−S)]/(N_{i−1}N_{i+1})`, AF-free | **[proven]**, but hypothesis `P=R=0` is unverifiable in the frozen regime |
| 3 | #2 + Finding 5.2's cap `c = Θ(1/n)` | `λ_std` | `1 − λ_std ≤ O(Λ²)` | **[proven, vacuous]** — `1−λ_std ≤ 1` is free |
| 4 | **Thm 7.2**, proven strength `Φ ≳ 1/(3W)` | `λ_std` via **T1** | `1 − λ_std ≤ O(Λ²W²/n²)` for T1 alone | **[proven, vacuous]** — equals what `\|I_x\| ≤ W` gives free; and `ΦW≥1/3` contradicts non-vacuity `ΦW≪1` |
| 5 | **Thm 7.2 + (LOC)** | `λ_std` via **T1** | `Φ ≥ cε` ⟹ `T1 = O(n/ε²)` ⟹ T1-contribution `= O(Λ²/(ε²n²)) = o(1/n)` | **[proven as a reduction]** — the entire positive content; 1 of 3 terms |
| 6 | either theorem | **T2** = `Σ_x Var_ν(midpoint)` | **none**; mg-0ed7 §7.3's inference to it is invalid | **[refuted]** (§4.2); repair under (H)+(LOC) **[open]** |
| 7 | either theorem | **T3** = `(B-bias)` | **none** — no `k=1` Stanley/MS statement constrains `E[pos_σ x]` | **[blocked]**, as mg-dcae Finding 5.3 already recorded |
| 8 | either theorem | `ρ_s`, `(decay)`, `M_{k,l}` | **none** | **[blocked]** by §6.5 (coordinates) *and* mg-dcae §5.5 (no propagation) |
| 9 | either theorem | `λ₂^BK` | **none** | **[blocked, structural]** static-vs-dynamical (mg-4a86); Wilson 2004 already pins it |
| 10 | §6.5 transfer corner | all, on `width ≤ 2` | exact and complete | **[proven]**, reach **zero** — Linial 1984 already settles that class |

### The one-sentence answer

> **The immediate spectral implication of mg-0ed7 is `1 − λ_std ≤ O(Λ²W²/n²)`, restricted to the
> within-window term `T1` of a three-term budget, which at the theorems' proven strength is exactly
> the trivial bound and which under the conditional `(LOC)` becomes `o(1/n)` — comfortably enough for
> its own term and irrelevant to the other two. Neither theorem reaches `ρ_s`, `(decay)`, or
> `λ₂^BK` at all.**

### Corrections this ticket makes to the record

1. **§6.5 is not the obstruction on the `λ_std` route.** `λ_std` and `(B)` are absolute-position-marginal
   functionals; `Φ` is in the same coordinate; `ρ_s` is an optional device. The arc should stop citing
   the object mismatch as the block on this path — it blocks a route the path need not take. **[proven]**
2. **mg-0ed7 Finding 7.3 / §7.5's variance inference is invalid**, and the missing quantity — the
   between-window term `T2 = Σ_x Var_ν(midpoint of I_x)` — is newly named here. `(LOC)` would close two
   of three terms, not "the variance half of (B)". **[proven]**
3. **Theorem 7.2's hypothesis and conclusion are mutually exclusive** (`ΦW ≪ 1` vs `Φ ≥ 1/(3W)`). This
   is a sharper statement of the block than "recovers the trivial averaging bound". **[proven]**
4. **Theorem 4.1's AF-freeness and its spectral vacuity are the same fact** — the debits are what AF
   pays for, and the debits are what destroys the ratio bound. **[proven]**
5. **The width `≤ 2` transfer corner should not be developed** — it is exactly the class where the
   conjecture is already Linial's theorem. **[proven]**

### Recommended forward action (scoping only, nothing commissioned)

- **Do not** commission further work aimed at getting `ρ_s`/`(decay)` from a `k=1` stability theorem.
  Blocked twice over, and unnecessary — `(B)` is reachable in the marginal coordinate.
- **Do** decide the `T2` question (§4.3) before any further `Φ`-currency work: *under (H), is
  `Σ_x Var_ν(m_x) = O(E[inv_e])`?* It is cheap to state, it is currently unaddressed, and a negative
  answer would retire the `Φ` currency the way Finding 5.2 retired the deficit currency. The arc's
  marginals-vs-joint wall predicts it is hard; that prediction should be tested, not assumed.
- **`(LOC)` remains the right primary target** (mg-0ed7 §7.5, mg-dcae §7.2 — two routes converging).
  Its value is now better specified: it closes **T1** and **T3**, and leaves **T2**.

---

*mg-8f56. Pure derivation. No datasets, enumerations, scripts, or Lean produced. All arithmetic is the
two `n = 4` hand tables in §2.4 and §5.2, each carried out in-line and checked against the exact
variance of `pos_σ(x)`. Ma–Shenfeld was not re-accessed; Theorems 4.1 and 7.2 are consumed exactly as
stated in mg-0ed7. Every claim is tagged `[proven]` / `[blocked]` / `[open]` / `[cited]` in §0's ledger
and in §7's table.*
