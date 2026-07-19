# OneThird — Ma–Shenfeld deep read → a natural near-ordinal-sandwich distance → the frozen-conditional stability attempt

**Work item:** mg-0ed7. **Constraint honored:** no datasets, no enumerations, no Lean, no scripts. Every
number below is an exact by-hand calculation carried out in-line and cross-checked on two small posets
(`C_2 ⊔ C_2`, `C_3 ⊔ C_3`) by full interval bookkeeping.

**READ-FIRST completed.** (1) **Ma–Shenfeld, arXiv:2211.14252v2 (30 Nov 2023), *The extremals of
Stanley's inequalities for partially ordered sets*, Adv. Math.** — PDF downloaded and text-extracted
**this session**; §1, §2.3.1, §3.1–§3.3, §5.1, §7.1 read directly. Every theorem/lemma number cited
below was verified against the extracted text, not paraphrased from our internal docs (§8 records the
verification level of each). (2) `docs/OneThird-AF-EqualityCase-MaShenfeld.md` (mg-48ab). (3)
`docs/OneThird-k1-Stanley-Stability-Scoping.md` (mg-dcae). The binding guardrails (a), (b), (c) from
the ticket are honored throughout and are each revisited explicitly in §6.

---

## 0. Verdict

> **AMBER — PARTIAL EMERGENCE, with the block located to one line and re-identified as a known
> obstruction wearing a new (and much more informative) face.**
>
> A natural near-ordinal-sandwich distance **does** emerge from Ma–Shenfeld's proof mechanism, and it is
> not the one mg-48ab guessed at. Translating their `k=1` machinery into the insertion-interval picture
> makes their Lemma 3.1 / Lemma 3.3(a) collapse into pure **interval-endpoint bookkeeping** (§3), and the
> distance falls out canonically:
>
> > **Φ_i(x) := Pr[ i is an endpoint of I_x(τ) | i ∈ I_x(τ) ]**, the probability that the insertion
> > interval **terminates** at i given that it covers i.
>
> Three results follow, all new and all elementary:
>
> 1. **An exact, AF-free deficit inequality (§4, Theorem 4.1)** derived from Ma–Shenfeld's Lemma 3.1
>    alone. It expresses the deficit as an explicit **credit minus debit**, and it is *sharp* (verified
>    exactly on `C_2⊔C_2` and `C_3⊔C_3`). **[PROVEN]**
> 2. **The block, stated exactly (§5, Finding 5.2).** On staircase families the deficit ratio equals
>    `(1−h_{i−1})/(1−h_i)` where `h_i` is the hazard rate, while `Φ_i = h_i`. **The deficit is an
>    increment of the hazard rate; the near-sandwich distance is its level.** No bound
>    `deficit ≥ c·Φ` can exist, for the same reason `f'' ≥ 0` bounds nothing about `f'`. This is not
>    repairable by choosing a better `Φ`: any admissible `Φ` must vanish on the Ma–Shenfeld locus
>    `{h ≡ 0}`, whereas the deficit vanishes on the strictly larger numerical locus `{h ≡ const}`. The
>    gap between the two loci **is** the geometric ray. **[PROVEN]** This *explains* guardrail (a)'s
>    refutation rather than merely restating it.
> 3. **Freezing kills the refuting family outright (§6.1, Theorem 6.1): `δ(C_m ⊔ C_n) ≥ 1/3` for all
>    `m,n ≥ 1` with `m+n ≥ 3`.** So guardrail (a)'s witness — and the same family Aires–Kahn used to
>    refute Chan–Pak–Panova Conj. 9.18 — is **not** available against a frozen-conditional statement.
>    **[PROVEN]**, by hand, elementary.
>
> **But (3) does not rescue (2), and §6.2 says why in one line: freezing removes the known *witness*, not
> the *mechanism*.** The obstruction is that the position law can be near-geometric; `C_m ⊔ C_n` is one
> way to be near-geometric, and freezing excludes that particular one, but nothing in the argument
> excludes near-geometric hazard in general.
>
> **The frozen-conditional statement I can actually prove (§7, Theorem 7.2) is in a different currency
> and it is conditional on one further lemma.** Pushing mg-48ab's Window Rigidity to an approximate form
> yields an exact inequality relating `Φ`, the window width `W`, the mass `π`, and the freezing gap `ε`.
> It is **[PROVEN]**, but it is **non-vacuous only when `Φ·W ≪ 1`** — i.e. only in the near-exactly-flat
> regime — and it degenerates precisely at `Φ ~ 1/W`, which is the generic/geometric regime. **The
> collision and the deficit hit the same wall at the same place**, which is a genuine unification and the
> main structural finding of this session.
>
> **Where the residual lands (§7.4): on a lemma the arc has already named.** The one step that would make
> the collision bite is a locality bound `Σ_{z ∥ x} Pr[y⁻ <_σ z <_σ y⁺] = O(1)` — which is, up to
> notation, **mg-dcae §7.2's independently-recommended first lemma** (`max_x Σ_{y∥x} Pr[{x,y} inverts]
> = O(1)`). Two routes designed from opposite ends converge on it. That convergence is the most useful
> forward signal here.
>
> **A methodological point that must be recorded (§6.3), because it caps the value of every
> frozen-conditional result in this arc:** the 1/3–2/3 conjecture asserts that frozen non-chain posets
> **do not exist**. So a frozen-conditional theorem is a step in a proof by contradiction, and — critically
> — **it can never be tested against an example**, since every computable example is unfrozen. "Freezing
> excludes the refuting family" (Theorem 6.1) therefore carries *no evidential weight* about whether the
> conclusion holds. I state this because §6.1 is exactly the kind of result that invites over-reading.

**What is NOT claimed.** L1b is not closed. (decay) is not proved. (B) is not proved. No unconditional
stability theorem is claimed or attempted (guardrail (a)). No AF-stability machinery is used (guardrail
(b)). mg-48ab's Theorem 5.2 and mg-dcae's Finding 3.1 are both untouched and both remain correct.

---

## 1. Anti-drift check

Ticket deliverables → sections: §2 restates the Ma–Shenfeld structure with verified numbers; §3 gives the
`k=1` interval translation (the technical engine, new); §4 gives the natural near-sandwich definition
plus the exact AF-free deficit inequality; §5 is the block; §6 is the guardrail audit including the
never-frozen theorem; §7 is the frozen-conditional attempt and where it lands; §8 is the status table.

I have **not** re-derived mg-48ab's Lemma 3.1, Cor. 3.2, Theorem 5.2, or Prop. 5.1/5.3, nor mg-dcae's
Finding 3.1, §5 decomposition, or route survey. They are consumed by citation. §3, §4, §5, §6.1 and §7
are where new mathematics appears; all of it is elementary and self-checking.

---

## 2. Ma–Shenfeld, restated cleanly (deliverable 1)

### 2.1 Setup and the companion notion

`ᾱ` is a poset on `n` elements containing a fixed chain `x_1 < ⋯ < x_k`; positions `i_1 < ⋯ < i_k` are
fixed; `ℓ ∈ [k]` is chosen with `i_{ℓ−1} + 1 < i_ℓ < i_{ℓ+1} − 1`; `N^◦` for `◦ ∈ {−,=,+}` are the linear
extensions with `σ(x_j) = i_j` for `j ≠ ℓ` and `σ(x_ℓ) = i_ℓ + 1_◦`. Stanley's inequality (their (1.1),
attributed to [18, Thm 3.2]) is `|N^=|² ≥ |N^−||N^+|`; their (1.2) records that at `k = 1`, with
`a_i := |{σ : σ(x_1) = i}|`, this "amounts to the statement that the sequence `{a_i}` is log-concave."

> **Definition 1.2 (verified verbatim).** *"The companions of `x_ℓ = σ^{−1}(i_ℓ + 1_◦)` are `σ^{−1}(i_j)`
> for `i_j ∈ {i_ℓ − 1, i_ℓ, i_ℓ + 1}\{i_ℓ + 1_◦}`, where `1_◦ := 1_{◦ is +} − 1_{◦ is −}`. The companion
> lower in ranking is the lower companion and the companion higher in ranking is the upper companion."*

**At `k = 1`** (our case, `x := x_1`, `i := i_1`) this reads concretely: for `σ ∈ N^=` the companions are
the elements at positions `i−1` and `i+1`; for `σ ∈ N^−` (`x` at `i−1`) they are the elements at `i` and
`i+1`; for `σ ∈ N^+` (`x` at `i+1`) they are the elements at `i−1` and `i`.

### 2.2 The three theorems

> **Theorem 1.3 (Supercritical extremals) [verified verbatim].** *Suppose `ᾱ` is supercritical. TFAE:
> (i) `|N^=|² = |N^−||N^+|`; (ii) `|N^−| = |N^=| = |N^+|`; (iii) for every linear extension in
> `N^− ∪ N^= ∪ N^+`, both companions of `x_ℓ` are incomparable to `x_ℓ`.*

> **Theorem 1.5 (Critical extremals) [verified verbatim].** *Suppose `ᾱ` is critical. TFAE: (i), (ii) as
> above; (iii) for every linear extension in `N^− ∪ N^= ∪ N^+`, **at least one** companion of `x_ℓ` is
> incomparable to `x_ℓ`; in addition there exist nonnegative `N_1, N_2` such that, for each fixed
> `◦ ∈ {−,=,+}`, the count of extensions in `N^◦` with only the lower companion incomparable equals `N_1`
> equals the count with only the upper companion incomparable, and the count with both companions
> incomparable equals `N_2`.*

> **Theorem 1.6 [verified].** *If `|N^=| > 0`, the conclusions of Theorem 1.5 remain true; if in addition
> `ᾱ` is supercritical, the conclusions of Theorem 1.3 remain true.* (v2 addition; the `|N^=| = 0` case is
> their **Theorem 5.3 (Trivial extremals)**, characterized via a splitting pair.)

### 2.3 The `k = 1` specialization — supercriticality is automatic, twice over

mg-48ab cites **Remark 1.8** for this. I verified Remark 1.8 and also found an **independent second
statement** in the body, immediately after Definition 2.11 (verified verbatim):

> *"Finally, let us remark that the case `k = 1` is always supercritical, where we use that
> `|N^−|, |N^=|, |N^+|` are positive, as `|N^=| > 0` and `|N^=|² = |N^+||N^−|`."*

So at `k=1` Theorem 1.3 applies with **no side condition**, and mg-48ab's `(MS-1)` is confirmed:

> **(MS-1) [CITED, exact].** For any finite poset `P`, `x ∈ P`, `1 < i < n` with `N_i > 0`:
> `N_i² = N_{i−1}N_{i+1}` ⟺ `N_{i−1} = N_i = N_{i+1}` ⟺ for every `σ` with `σ(x) ∈ {i−1,i,i+1}`, the two
> elements at the other two of those positions are both incomparable to `x`.

### 2.4 The ordinal-sandwich normal form, and where it is actually stated

The ticket asks for "the `r=1` flat, the free element in `D(x) ⊕ Q ⊕ U(x)`, the companion-incomparability
condition." A correction of attribution is needed, and it matters for §4:

- The **companion-incomparability condition** is Ma–Shenfeld's, exactly Theorem 1.3(iii).
- The **`r=1` flat** (no geometric progression with ratio `≠1` is realizable) is Ma–Shenfeld's, exactly
  Theorem 1.3(ii), and they flag it themselves as the surprising part: *"A priori, we could have a
  geometric progression … Theorem 1.3(ii) excludes this possibility."* **[verified verbatim]**
- The **ordinal-sum normal form `P = D(x) ⊕ Q ⊕ U(x)` with `x` free in `Q`** is **not** in Ma–Shenfeld.
  It is mg-48ab's Cor. 3.2, derived from Theorem 1.3 plus conditional uniformity. Ma–Shenfeld's own
  poset-level reformulation is instead **Remark 1.7**, proved as **Proposition 7.5** — and I verified
  Prop. 7.5's proof opens by reducing Remark 1.7 to **Lemma 3.3(a)**, i.e. to a statement measured
  **on `N^=` only**:

  > *"By Lemma 3.3(a), the conditions in Theorem 1.3(iii) are equivalent to: `σ^{−1}(i_ℓ − 1) ≁ x_ℓ` and
  > `σ^{−1}(i_ℓ + 1) ≁ x_ℓ` ∀ `σ ∈ N^=`."* **[verified verbatim]**

  **This single sentence is the origin of the correct near-sandwich distance** (§4.1): the extremal
  condition, although stated on `N^− ∪ N^= ∪ N^+`, is *equivalent to a condition on `N^=` alone*.

### 2.5 The mechanism: Lemma 3.1 is a set of explicit bijections and injections

This is the part mg-48ab and mg-dcae both consumed only through its conclusion, and it is where the
quantitative content lives. Writing `N^◦(⋆,∗)` for the extensions in `N^◦` whose lower companion is
`⋆ x_ℓ` and upper companion is `∗ x_ℓ` (`⋆,∗ ∈ {≁,∼}`):

> **Lemma 3.1 [verified verbatim].** *(i) `|N^−(≁,≁)| = |N^=(≁,≁)| = |N^+(≁,≁)|`;
> (ii) `|N^−(≁,∼)| = |N^=(≁,∼)|`; (iii) `|N^=(∼,≁)| = |N^+(∼,≁)|`;
> (iv) `|N^−(∼,≁)| ≤ |N^−(≁,∼)|`; (v) `|N^+(≁,∼)| ≤ |N^+(∼,≁)|`.*

(i)–(iii) are proved by explicit **position-swap bijections** `π_{i_ℓ−1,i_ℓ}` etc.; (iv)–(v) by an
explicit **injection** `π_{i_ℓ,i_ℓ+1}` whose well-definedness uses a two-step comparability argument
(*"We cannot have `y_u < y_v` since that would imply `x_ℓ < y_u < y_v` contradicting `y_v ≁ x_ℓ`"*).

> **Lemma 3.3(a) [verified verbatim].** *The conditions in Theorem 1.3(iii) hold if and only if
> `|N^=(≁,∼)| = |N^=(∼,≁)| = |N^=(∼,∼)| = 0`.*

**Lemma 3.1 is unconditional — it holds whether or not equality does.** That is the crucial observation
for this ticket: it is a *quantitative* tool sitting inside a *qualitative* theorem, and §4 extracts it.

---

## 3. The `k = 1` translation: Ma–Shenfeld's classes are interval endpoints

Throughout: `D(x)`, `U(x)` are the strict down/up-sets, and for `τ ∈ L(P∖x)` the admissible insertion
slots form a non-empty integer interval `I_x(τ) = [ℓ_τ, r_τ]` on which `x` is conditionally uniform
(mg-a1ec Prop. 4.1, cited via mg-48ab), with

  `ℓ_τ = 1 + max{pos_τ(z) : z ∈ D(x)}`,  `r_τ = min{pos_τ(z) : z ∈ U(x)}`,
  `N_p = #{τ : p ∈ I_x(τ)}`,  `Σ_τ |I_x(τ)| = e(P)`.

Fix an index `i` with `1 < i < n`.

> **Lemma 3.1′ (the translation; PROVEN, new).** *For `σ ∈ N^=` arising from `τ` by inserting `x` at slot
> `i`:*
> - *the lower companion is comparable to `x` ⟺ `ℓ_τ = i`;*
> - *the upper companion is comparable to `x` ⟺ `r_τ = i`.*
>
> *Consequently, with `A := |N^=(≁,≁)|, B := |N^=(≁,∼)|, C := |N^=(∼,≁)|, S := |N^=(∼,∼)|,*
> $$A = \#\{τ: ℓ_τ < i < r_τ\},\quad B = \#\{τ: ℓ_τ < i = r_τ\},\quad C = \#\{τ: ℓ_τ = i < r_τ\},\quad S = \#\{τ: I_x(τ) = \{i\}\}.$$
>
> **Proof.** The lower companion is the element at `σ`-position `i−1`, i.e. at `τ`-position `i−1`. It is
> comparable to `x` iff it lies in `D(x)` (it precedes `x`). If it lies in `D(x)` then
> `ℓ_τ ≥ i`, and `i ∈ I_x(τ)` gives `ℓ_τ ≤ i`, so `ℓ_τ = i`. Conversely `ℓ_τ = i` means the last
> `D(x)`-element of `τ` sits at position `i−1`. The upper companion is the element at `σ`-position `i+1`,
> i.e. `τ`-position `i`; it is comparable iff it lies in `U(x)`, and the same argument gives `r_τ = i`. ∎

Two immediate consequences, both worth recording:

> **Corollary 3.2 (Lemma 3.3(a), decoded).** *Ma–Shenfeld's extremal condition at `i` says exactly:*
> **no insertion interval has an endpoint at `i`** *— every `I_x(τ)` either contains `i` in its interior
> or misses `i` entirely.* **PROVEN.**

That is **precisely mg-48ab's Window Rigidity Lemma 3.1**, which mg-48ab obtained by running Theorem
1.3(iii) at every interior index of a flat run. In the interval language it is not a derived consequence
of the classification but a *transcription* of it. **This is a simplification of the arc's existing
machinery, and it is the reason the right distance becomes visible.**

> **Corollary 3.3 (the outer classes, for completeness; PROVEN, new).** *With `u_τ(j) := 1` if the
> `τ`-element at position `j` lies in `U(x)`, and `d_τ(j)` likewise for `D(x)`:*
> $$|N^-(∼,∼)| = \#\{τ : r_τ = i-1,\; u_τ(i) = 1\},\qquad |N^+(∼,∼)| = \#\{τ : ℓ_τ = i+1,\; d_τ(i-1) = 1\}.$$
> *That is: the "both companions comparable" classes at the **outer** indices count `τ`'s with **two
> consecutive `U(x)`-elements beginning exactly at the interval's right endpoint** (resp. two consecutive
> `D(x)`-elements ending at the left endpoint).*
>
> **Proof.** For `σ ∈ N^−`, `x` sits at slot `i−1`, so `ℓ_τ ≤ i−1 ≤ r_τ`. Its lower companion is the
> `τ`-element at position `i−1`; it is comparable iff it lies in `U(x)`, which (as `i−1 ≤ r_τ`) forces
> `r_τ = i−1`. Its upper companion is the `τ`-element at position `i`, comparable iff `u_τ(i) = 1`. The
> `N^+` statement is dual. ∎

**Why Cor. 3.3 matters:** these two counts are the *only* ones in the decomposition (3.1) that Lemma 3.1
does not control — no bijection or injection touches them. §4 shows they are exactly the debit term, and
§5 shows they are exactly where the obstruction lives.

---

## 4. The natural near-ordinal-sandwich distance, and the exact AF-free deficit inequality

### 4.1 The definition, and why it is the natural one

> **Definition 4.0 (near-ordinal-sandwich distance).** *For a finite poset `P`, `x ∈ P`, and `1 < i < n`
> with `N_i > 0`,*
> $$\boxed{\;Φ_i(x) \;:=\; \frac{|N^=(≁,∼)| + |N^=(∼,≁)| + |N^=(∼,∼)|}{|N^=|} \;=\; \Pr\big[\,i \text{ is an endpoint of } I_x(τ) \;\big|\; i \in I_x(τ)\,\big].\;}$$

**Four reasons this is the *natural* distance — each tied to the mechanism, not to convenience:**

1. **It is exactly the quantity Ma–Shenfeld's own reduction isolates.** Prop. 7.5's proof reduces the
   extremal condition to Lemma 3.3(a), which is `B = C = S = 0` — a condition **on `N^=` only**. `Φ_i` is
   the normalized violation of precisely that, so `Φ_i = 0 ⟺` Theorem 1.3(iii) at `i` (given `k=1`
   supercriticality, §2.3). No choice was made.
2. **It is the vanishing locus of the correct object, not of a proxy.** mg-48ab's Cor. 3.2 ordinal-sum
   normal form `P = D(x) ⊕ Q ⊕ U(x)` is what you get when `Φ_p = 0` across the whole support; so `Φ`
   really is a "distance from the ordinal sandwich," and it degrades continuously rather than by fiat.
3. **It is intrinsic to the interval family** (Cor. 3.2), so it is stable under the reformulations the
   arc actually uses, and is computable from `N_·` plus one extra bit of interval data.
4. **It is the same `Φ` mg-dcae refuted** — which is a feature, not a bug, for the honesty of this
   document. mg-dcae described `Φ` as *"the fraction of `N^=`-extensions with a comparable companion"* and
   refuted it. Definition 4.0 is that object, now derived rather than guessed, so §5's block is a
   statement about **the** natural distance, not about one of many.

**A note on normalization.** One could normalize by `|N^− ∪ N^= ∪ N^+|` or count endpoints with
multiplicity. Neither changes anything below by more than a factor of 3; §5's obstruction is a
`Θ(n)` gap, so normalization is not where the difficulty is.

### 4.2 The exact deficit inequality — Lemma 3.1 without AF

Fix `i`. Set `A, B, C, S` as in Lemma 3.1′ and additionally
`p := |N^−(∼,≁)|`, `q := |N^+(≁,∼)|`, `P := |N^−(∼,∼)|`, `R := |N^+(∼,∼)|`. Ma–Shenfeld's Lemma 3.1
(i)–(iii) let us write the decomposition (3.1) as

  `|N^−| = A + B + p + P`,  `|N^=| = A + B + C + S`,  `|N^+| = A + C + q + R`,

and (iv)–(v) give `p ≤ B`, `q ≤ C`.

> **Theorem 4.1 (exact combinatorial deficit inequality; PROVEN, new).** *For every finite poset `P`,
> every `x ∈ P` and every `1 < i < n`,*
> $$\boxed{\;|N^=|^2 - |N^-||N^+| \;\ge\; \underbrace{(B - C)^2 \;+\; S\,(2|N^=| - S)}_{\textbf{credit}} \;-\; \underbrace{\big[\,P(A + 2C) \;+\; R(A + 2B) \;+\; PR\,\big]}_{\textbf{debit}}\;}$$
> *with equality iff `p = B` and `q = C` (i.e. iff Ma–Shenfeld's Lemma 3.1(iv),(v) injections are
> bijections). **No Alexandrov–Fenchel input is used**: this is a consequence of Lemma 3.1 alone.*
>
> **Proof.** By `p ≤ B` and `q ≤ C`, `|N^−||N^+| ≤ (A+2B+P)(A+2C+R)`. Expanding,
> `(A+B+C)² − (A+2B)(A+2C) = (B−C)²`, and `|N^=| = (A+B+C) + S`, so
> `|N^=|² = (A+B+C)² + S(2|N^=| − S)`. Subtracting gives the claim; the equality condition is
> immediate. ∎

**Verification, exact, two cases.** Take `P = C_m ⊔ C_m` with `x` the minimum of the first chain, `i = 2`
(the guardrail-(a) family). Here `D(x) = ∅`, so `ℓ_τ ≡ 1`, and `I_x(τ) = [1, pos_τ(u_2)]` — a *staircase*
family. Then `C = S = q = R = 0`.

| | `(N_1,N_2,N_3,…)` | `A` | `B` | `p` | `P` | credit − debit | true deficit |
|---|---|---|---|---|---|---|---|
| `m=2` | `(3,2,1)` | 1 | 1 | 1 | 0 | `1 − 0 = 1` | `4 − 3 = 1` ✔ |
| `m=3` | `(10,6,3,1)` | 3 | 3 | 3 | 1 | `9 − 3 = 6` | `36 − 30 = 6` ✔ |

**Theorem 4.1 is exactly tight on this family** (`p = B`, `q = C = 0` in both rows), and in general for it
one computes `P = N_1 − 2N_2 + N_3` — the debit is literally the **second difference** of the position
law. Both rows were checked by enumerating the interval family by hand (`e(P∖x) = 3` and `10`
respectively) and independently against mg-dcae's closed form `N_{1+j} = \binom{n-j+m-1}{m-1}`. ✔

### 4.3 What Theorem 4.1 says, and what it does not

**Says:** the near-sandwich structure enters the deficit through *two* channels of opposite sign. The
`N^=`-side violations (`B`, `C`, `S` — i.e. `Φ`) are **credits**; the *outer*-index "both companions
comparable" counts (`P`, `R` — i.e. Cor. 3.3's double-walls) are **debits**. mg-48ab's Finding 6.2 posed
the target as `deficit ≥ (1 + cΦ)`, implicitly assuming `Φ` enters with one sign. **It does not.**

**Does not say:** that the deficit is nonnegative. Theorem 4.1's right-hand side is genuinely negative in
general (`m=3` above has debit `3 > 0`). Stanley's inequality `deficit ≥ 0` is *strictly deeper* than
Lemma 3.1 — the AF input is precisely what pays for the debits. That is a clean statement of what AF
contributes at `k=1`, and it is consistent with guardrail (b): the missing quantitative object is on the
AF side, and Shenfeld–van Handel's no-compact-resolvent remark (mg-dcae §4.1 wall 2) says it is not
coming.

---

## 5. The block, stated exactly

### 5.1 Staircase families: the deficit is a hazard-rate *increment*

Call the interval family a **staircase** if `ℓ_τ ≡ 1` (equivalently `x` is a minimal element of `P`, so
`D(x) = ∅`). This is not a special case chosen for convenience — it is the shape of guardrail (a)'s
refuting family, and by up/down duality the mirror case is identical.

For a staircase, `N_p = #\{τ : r_τ ≥ p\} = e(P∖x)·G(p)` where `G` is the survival function of `r_τ`.
Define the **hazard rate** `h_p := Pr[r_τ = p | r_τ ≥ p]`, so `G(p+1) = G(p)(1 − h_p)`.

> **Lemma 5.1 (PROVEN, new).** *For a staircase family and any `1 < i < n` with `N_i > 0`:*
> $$Φ_i \;=\; h_i, \qquad\text{and}\qquad \frac{N_i^2}{N_{i-1}N_{i+1}} \;=\; \frac{1 - h_{i-1}}{1 - h_i}, \qquad\text{so}\qquad \frac{N_i^2}{N_{i-1}N_{i+1}} - 1 \;=\; \frac{h_i - h_{i-1}}{1 - h_i}.$$
>
> **Proof.** `C = S = 0` since `ℓ_τ = 1 < i`, so `Φ_i = B/N_i = \#\{r_τ = i\}/\#\{r_τ ≥ i\} = h_i`. And
> `N_i²/(N_{i−1}N_{i+1}) = G(i)²/(G(i−1)G(i+1)) = [G(i)/G(i−1)]·[G(i)/G(i+1)] = (1−h_{i−1})/(1−h_i)`. ∎

(Consistency: Stanley's inequality here is exactly the statement that `h` is non-decreasing — the classical
**increasing-hazard-rate** property. ✔ And the `m=3` check of §4.2 has `h = (2/5, 1/2, 2/3, 1)`, increasing. ✔)

### 5.2 The obstruction

> **Finding 5.2 (the block; PROVEN, new — this is the report).**
> *On staircase families the deficit is the **increment** of the hazard rate while the near-sandwich
> distance is its **level**:*
> $$\text{deficit ratio} - 1 \;=\; \frac{h_i - h_{i-1}}{1-h_i}, \qquad Φ_i \;=\; h_i.$$
> *Hence **no inequality of the form `deficit ≥ c·Φ` can hold for any `c > 0`**, and this is not an
> artifact of Definition 4.0: it is forced by a mismatch of vanishing loci.*
> - *`Φ` must vanish on the **Ma–Shenfeld realizable extremal locus**, which by Cor. 3.2 is `{h ≡ 0}` —
>   "no interval ends here," the flat law.*
> - *The **deficit** vanishes on the strictly larger **numerical** locus `{h ≡ const}` — every geometric
>   progression.*
> - *Ma–Shenfeld's Theorem 1.3(ii) says the difference of the two loci contains no **realizable** point
>   (no poset achieves `h ≡ c > 0` exactly). **It says nothing about accumulation.** And posets do
>   accumulate on it: `C_m ⊔ C_n` realizes `h_i = (m−1)/(m−1+a)`, which is constant to within `O(1/a)`
>   over the mass-carrying range.*
>
> ***The geometric ray is the gap between "the deficit-zero locus" and "the realizable equality locus,"
> and stability fails by accumulation onto it.***

**This is a strict sharpening of guardrail (a), not a restatement.** mg-dcae proved *that* the target is
false, by exhibiting `Φ = 1/2` with deficit `1 + 1/(2n−1)`. Finding 5.2 says *why*, in a form that
predicts the failure of every repair: any `Φ` that is a **first-order** functional of the interval family
(a level: what fraction of intervals end here) is measuring the wrong derivative. Only a **second-order**
functional — an increment of the hazard rate — can lower-bound the deficit, and such a functional is the
deficit itself. **Any repair is circular by construction.**

**Cross-check against mg-48ab's Correction 2.1.** mg-48ab observed, from Theorem 1.3(ii), that "the
realizable part of the equality locus is exactly the flat part," and concluded this was *good news*
because it points the theory at a single object. Finding 5.2 shows the same fact is precisely the *bad*
news for stability: a rigidity theorem whose conclusion locus is strictly smaller than its hypothesis's
numerical locus **cannot** be stable, because the deficit cannot see the difference. **The two readings
are consistent and this document adopts both.**

---

## 6. Guardrail audit

### 6.1 Guardrail (a): freezing kills the refuting family outright

The ticket's guardrail (a) records that `C_n ⊔ C_n` refutes unconditional stability and that it is
"maximally unfrozen." That is right at `m = n`. I can prove the much stronger statement that the entire
family is unavailable against a frozen-conditional target:

> **Theorem 6.1 (PROVEN, new, elementary).** *For all `m, n ≥ 1` with `m + n ≥ 3`,*
> $$δ\big(C_m ⊔ C_n\big) \;\ge\; \tfrac13 .$$
> ***No disjoint union of two chains is frozen.***
>
> **Proof.** WLOG `m ≤ n`. Write `C_m : u_1 < ⋯ < u_m`, `C_n : v_1 < ⋯ < v_n`, and set
> `f(k) := \Pr[v_k <_σ u_1]` for `k ∈ [n]`. The event `v_k <_σ u_1` says `v_1,…,v_k` all precede `u_1`,
> after which `C_m` and `v_{k+1},…,v_n` interleave freely, so exactly
> $$f(k) = \binom{m+n-k}{m}\Big/\binom{m+n}{m}, \qquad \frac{f(k)}{f(k-1)} = \frac{n-k+1}{m+n-k+1}.$$
> We exhibit `k` with `f(k) ∈ [1/3, 2/3]`, which gives `δ ≥ 1/3`.
>
> *Case `n ≤ 2m`.* Then `f(1) = n/(m+n) ∈ [1/2, 2/3]`. Done.
>
> *Case `n > 2m`.* Then `f(1) = n/(m+n) > 2/3`, while `f(n) = 1/\binom{m+n}{m} ≤ 1/3` (as
> `\binom{m+n}{m} ≥ \binom{3}{1} = 3`). So `k^* := \min\{k : f(k) ≤ 2/3\}` exists in `[2, n]` and
> `f(k^*-1) > 2/3`. Suppose for contradiction `f(k^*) < 1/3`. Since
> `f(k^*) = f(k^*-1)·(n-k^*+1)/(m+n-k^*+1) > (2/3)(n-k^*+1)/(m+n-k^*+1)`, this forces
> `(n-k^*+1)/(m+n-k^*+1) < 1/2`, i.e. `n - k^* + 1 ≤ m - 1`. But then
> `m + n - k^* + 1 ≤ 2m - 1`, so
> `f(k^*-1) = \binom{m+n-k^*+1}{m}/\binom{m+n}{m} ≤ \binom{2m-1}{m}/\binom{m+n}{m} < 2/3`,
> using `n > 2m` (so `m+n > 3m` and `\binom{m+n}{m} > \binom{2m-1}{m}·\tfrac32` comfortably; for `m = 1`
> this reads `1/(n+1) < 2/3`, true for `n ≥ 2`). This contradicts `f(k^*-1) > 2/3`. Hence
> `f(k^*) ∈ [1/3, 2/3]`. ∎

*(Spot-checks: `m=n=2`: `f(1) = 1/2` ✔. `m=2, n=7`: `f(1) = 7/9 > 2/3`, `f(2) = 21/36 = 7/12 ∈ [1/3,2/3]` ✔.
`m=1, n=100`: `f(34) = 67/101 ≈ 0.663` ✔.)*

**Consequences.** (a) Guardrail (a)'s witness is genuinely excluded by freezing, so the ticket's premise —
that freezing is *exactly* what must rescue the statement — survives its own first test. (b) The same
family is the one the Chan–Pak survey reports Aires–Kahn used to refute Chan–Pak–Panova Conj. 9.18
(cited via mg-dcae §3.3, which read the survey footnote; I did not re-access it). So **the one family that
has killed two successive quantitative strengthenings in this area is unavailable against a
frozen-conditional statement.** That is real, and it is the strongest positive signal in this document.

### 6.2 …but freezing removes the witness, not the mechanism

> **Finding 6.2 (the honest counterweight; PROVEN as an implication, the antecedent OPEN).**
> *Theorem 6.1 excludes `C_m ⊔ C_n`. Finding 5.2's obstruction is not about that family — it is about the
> **regime** `h ≈ const`. `C_m ⊔ C_n` is one way to realize near-constant hazard; freezing excludes that
> one. **Nothing in §5 or §6.1 excludes near-constant hazard in general**, and I found no mechanism by
> which a hypothesis about **pair marginals** (`δ(P) < 1/3`) constrains the **shape** (second differences)
> of a single element's position law.*

This is exactly the marginals-vs-joint wall the arc already records
(`OneThird-L1b-CoreLemma-forDaniel.md` §5: *"Decay must come from the joint LE structure, not the
marginals"*), reached here from a new direction. Consistency ✔ — and it means Theorem 6.1 should **not**
be read as evidence for the frozen-conditional statement.

### 6.3 A methodological cap on every frozen-conditional result in this arc

> **Finding 6.3 (recorded because §6.1 invites over-reading).** *The 1/3–2/3 conjecture asserts that
> frozen non-chain posets **do not exist**. A frozen-conditional theorem is therefore a step inside a
> proof by contradiction — legitimate, but **untestable**: every poset one can compute with is unfrozen,
> so no example can ever confirm or disconfirm a frozen-conditional conclusion.*
>
> *In particular, "freezing excludes the refuting family" (Thm 6.1) is **not evidence** that the
> conclusion holds under freezing; it only says the cheapest disproof is unavailable. Under a vacuous
> hypothesis every conclusion holds, so an argument that "cannot be refuted by example" has earned
> nothing.* **This applies to mg-48ab's Theorem 5.2 and Prop. 5.3 equally** *— they are correct, and they
> are also unfalsifiable in the same way. Their value is as steps toward a contradiction, and should be
> stated that way in `STATE.md`.*

### 6.4 Guardrail (b): AF-stability was not used, and Theorem 4.1 explains why it was needed

No AF machinery appears above. Theorem 4.1 is derived from Ma–Shenfeld's Lemma 3.1 (bijections and one
injection) alone, and §4.3 identifies exactly what AF supplies at `k=1`: the payment of the `P`, `R`
debits, i.e. `deficit ≥ 0`. This **localizes** guardrail (b): the missing spectral gap is not needed for
the credit side of the ledger — it is needed to bound the debit side, which is Cor. 3.3's double-wall
counts. Whether *those* admit a combinatorial bound is a well-posed question this document does not
answer; it is the sharpest sub-target §7.4 can offer that is not already named.

### 6.5 Guardrail (c): does the distance transfer to the gap/slot object?

**No, and the interval picture says exactly why, more sharply than "different sequences."**

`Φ_i` is defined by endpoints of `I_x(τ)` **in the absolute-position coordinate**. The gap/slot law
`a_m = e(P_m)` (number of extensions with exactly `m` elements of an incomparable chain
`C = c_1 < ⋯ < c_p` below `x`) marginalizes over the positions of everything outside `C`, so the index
`m` is **not** a coordinate in which `I_x(τ)` is an interval — the preimage of a single gap index is a
union of slot ranges across many `τ`, one per placement of `P ∖ (C ∪ {x})`.

> **Finding 6.5 (PROVEN, new).** *The near-sandwich distance `Φ` transfers verbatim from the absolute
> law to the gap law **iff `P ∖ {x}` is itself the chain `C`** — i.e. iff `width(P) ≤ 2` and `x` is the
> only element off `C`. In that case there is a single `τ`, `I_x(τ)` is one interval, and the two laws
> coincide (both flat on `I_x(τ)`). Outside that case the transfer fails at the level of coordinates,
> before any inequality is invoked.*

This **strengthens** mg-48ab's Finding 6.1 (which located the mismatch by typing) and **agrees with**
mg-dcae §5.5 (which showed the `ρ_s` route additionally lacks a propagation step, gap-law log-concavity
being numerically false per mg-2acf). Combined: the `ρ_s` route lacks *both* a propagation mechanism and
a transferable distance. Nothing in this document rehabilitates it.

---

## 7. The frozen-conditional attempt

Per guardrail (a) I target only a frozen-conditional statement. Per §5, I do **not** target the deficit —
Finding 5.2 says that currency is unavailable. I target `Φ` directly, which §7.3 argues is the currency
L1b actually wanted all along.

### 7.1 Setup

`δ(P) := \max` over incomparable pairs of `\min(\Pr[y<z], \Pr[z<y])`; **frozen (H)** means
`δ(P) = 1/3 − ε`, `ε > 0`. Consumed by citation from mg-48ab §4: the elementary triple anchor makes the
strong-majority tournament `≺_e` a total order; `Hi := \{z : \Pr[x<z] ≥ 2/3+ε\}` is a `≺_e`-up-set
(mg-48ab Lemma 4.1); hence a unique `≺_e`-consecutive **threshold pair** `(y^-, y^+)` exists with

- **(J)** `\Pr[y^- <_σ x <_σ y^+] ≥ 1/3 + 2ε`;
- **(S)** `\Pr[y^- <_σ z <_σ y^+] ≤ 1/3 − ε` for every `z ∉ \{x, y^-, y^+\}`.

### 7.2 Approximate Window Rigidity, and the collision

mg-48ab's Window Rigidity (= Cor. 3.2 here) requires **exact** equality at every interior index. Its
approximate form is a two-line count in the interval language:

> **Lemma 7.1 (approximate Window Rigidity; PROVEN, new).** *Let `[a,b]` be a window of width
> `W := b−a+1`, let `π := \Pr[σ(x) ∈ [a,b]]`, and suppose `Φ_p ≤ Φ` for every `p ∈ [a,b]`. Let
> `T := \{τ : I_x(τ) ⊇ [a,b]\}` and `π_T := \Pr_σ[τ ∈ T]`. Then*
> $$π_T \;\ge\; π\,(1 - WΦ).$$
>
> **Proof.** A `τ` with `I_x(τ) ∩ [a,b] ≠ ∅` but `I_x(τ) ⊉ [a,b]` has an endpoint in `[a,b]`. The number
> of `τ` with an endpoint at `p` is `Φ_p N_p ≤ Φ N_p`, so the number with an endpoint anywhere in the
> window is at most `Φ Σ_{p∈[a,b]} N_p = Φ·π·e(P)`. Each such `τ` contributes at most
> `|I_x(τ) ∩ [a,b]| ≤ W` linear extensions with `σ(x) ∈ [a,b]`. Hence the mass with `σ(x) ∈ [a,b]` and
> `τ ∉ T` is at most `WΦπ`, and `π_T ≥ \Pr[σ(x) ∈ [a,b], τ ∈ T] ≥ π(1 − WΦ)`. ∎

Feeding this into mg-48ab's Prop. 5.1 collision (whose proof I do not repeat; only its input `π` is
replaced by `π_T`, and its `m_x(1/3−ε)` step is kept explicit):

> **Theorem 7.2 (frozen-conditional near-sandwich inequality; PROVEN, new).** *Assume (H) with gap `ε`
> and `Lo ≠ ∅ ≠ Hi`. Let `[a,b]`, `W`, `π`, `Φ` be as in Lemma 7.1, and put*
> `Λ := Σ_{z ∥ x} \Pr[y^- <_σ z <_σ y^+]`. *Then*
> $$\boxed{\;\tfrac13 + 2ε \;\le\; \big(1 - π(1-WΦ)\big) \;+\; \frac{Λ + 1}{W}.\;}$$
>
> **Proof.** Split `\Pr[y^- < x < y^+] = Σ_τ S_τ/e(P)` (`S_τ` = admissible `x`-slots strictly between
> `y^-, y^+`) over `τ ∈ T` and `τ ∉ T`. The latter contributes at most `1 − π_T`. For `τ ∈ T`, distinct
> admissible slots between `y^-` and `y^+` are separated by elements incomparable to `x`, so
> `S_τ ≤ B_τ + 1` with `B_τ := \#\{z ∥ x` strictly between `y^-,y^+` in `τ\}`; and `|I_x(τ)| ≥ W`, so
> `Σ_{τ∈T} S_τ ≤ (1/W)Σ_{τ∈T}|I_x(τ)|(B_τ+1) = (e(P)/W)·E_σ[(B+1)\mathbf 1_T]`. Finally
> `E_σ[B] = Σ_{z∥x}\Pr[y^-<z<y^+] = Λ`. Combining with (J) and Lemma 7.1 gives the display. ∎

**Sanity check against mg-48ab Theorem 5.2.** Put `Φ = 0` (exact rigidity), `π = 1`, and — as forced by
Cor. 3.2's ordinal-sum normal form — `Λ ≤ (W−3)(1/3−ε)`. Theorem 7.2 becomes
`1/3 + 2ε ≤ ((W−3)(1/3−ε) + 1)/W = 1/3 − ε + 3ε/W`, i.e. `W ≤ 1`. ✔ **mg-48ab's Theorem 5.2 is recovered
exactly as the `Φ = 0` corner of Theorem 7.2.** That is the check that the generalization is faithful.

### 7.3 Why `Φ` is the right currency (and the deficit never was)

mg-dcae §5.3 established that the object L1b needs is `\operatorname{Var}(\operatorname{pos}_σ(x))`, and
that the deficit was only ever a *device* for bounding it via ratio propagation. In the interval language
the device is unnecessary: by conditional uniformity,
`\operatorname{Var}(\operatorname{pos}_σ(x)) ≥ E[(|I_x(τ)|² − 1)/12]`, and a lower bound `Φ ≥ c` on the
hazard directly bounds `E[|I|²] = O(c^{-2})` — hence `Σ_x \operatorname{Var} = O(n/c²)`, exactly (B)'s
requirement at `c = Θ(1)`.

> **Finding 7.3 (PROVEN, new).** *A frozen-conditional lower bound on `Φ` is **strictly more useful** than
> a deficit bound of the same strength, and — unlike a deficit bound — it is not refuted by guardrail (a):
> the `C_m ⊔ C_n` family has `Φ_2 = 1/2`, a **large** near-sandwich distance. **The family that refutes
> deficit-stability is a confirming instance for `Φ`-stability.** The arc's residual should be stated in
> the `Φ` currency; the deficit framing was importing the AF/Stanley machinery to compute a quantity the
> machinery is structurally unable to deliver (Finding 5.2), when the quantity actually wanted was
> upstream of it.*

### 7.4 Where it blocks

Theorem 7.2 rearranges to `π(1 − WΦ) ≤ 2/3 − 2ε + (Λ+1)/W`. To extract `Φ ≥ c` one takes a
mass-carrying window (`π ≥ 1 − η`) and `W ≫ Λ`, obtaining `WΦ ≳ 1/3 − η − Λ/W`, i.e.

  **`Φ ≳ 1/(3W)`.**

> **Finding 7.4 (the block; PROVEN).** *`Φ ≳ 1/(3W)` is **essentially the trivial averaging bound**. Since
> every interval must end somewhere, `Σ_p Φ_p N_p = e(P∖x)` and `Σ_p N_p = e(P)`, so the average of `Φ`
> over the support is exactly `1/E[|I_x|] ≈ 1/W`. **Theorem 7.2 recovers the trivial bound and no more.**
>
> Equivalently, and this is the sharp form: Theorem 7.2's left side is non-vacuous only when
> `W Φ ≪ 1` — the **near-exactly-flat** regime — and it degenerates precisely at `Φ ~ 1/W`, which is the
> **constant-hazard (geometric)** regime. **This is Finding 5.2's obstruction arriving in the collision
> argument.** The deficit route and the collision route fail at the same place for the same reason.*

**Answering the ticket's diagnostic question — which guardrail is this?** It is **(a) resurfacing**, not
(b) and not (c). It is not the AF resolvent failure: no AF machinery is used, and Theorem 4.1 shows the
credit side of the ledger is available combinatorially. It is not the object mismatch: everything here is
in the absolute-position coordinate throughout. It is the `C_n ⊔ C_n` obstruction — but the family itself
is excluded by Theorem 6.1, so what resurfaces is the **regime** (`h ≈ const`) that family exemplifies,
and freezing has not been shown to exclude that regime (Finding 6.2).

### 7.5 The one step that would unblock it

The lossy step in Theorem 7.2 is `Λ := Σ_{z∥x}\Pr[y^- <_σ z <_σ y^+]`, which (S) bounds only by
`m_x(1/3 − ε)` — useless when `m_x ≫ W`. mg-48ab escaped this only because exact rigidity forced the
ordinal-sum normal form, localizing the sum to `W − 3` terms. Approximately, no such localization is
available.

> **Finding 7.5 (the residual; PROVEN as a reduction).** *If **(LOC)**: `Λ = O(1)` under (H) — i.e. only
> boundedly many elements can occupy the threshold gap in expectation — then Theorem 7.2 with `W = Θ(Λ)`
> yields* `Φ ≥ c·ε` *over the mass-carrying window, hence*
> `\operatorname{Var}(\operatorname{pos}_σ(x)) = O(ε^{-2})` *and* `Σ_x \operatorname{Var} = O(n/ε²)` *—
> **the variance half of (B), at constant `ε`.***
>
> ***(LOC) is, up to notation, mg-dcae §7.2's independently-recommended first lemma***
> `\max_x Σ_{y ∥ x} \Pr[\{x,y\}\text{ inverts against } e] = O(1)` *— which mg-dcae proved (its Prop. 5.4)
> closes the **bias** half of (B) outright. **The same lemma would close both halves.*** *This document
> reached it by pushing Ma–Shenfeld's mechanism to its limit; mg-dcae reached it by abandoning that
> mechanism for the Kahn–Saks architecture. **Two routes designed from opposite ends converge on one
> elementary, Stanley-free, AF-free statement.** That is the forward recommendation.*

> **[REFUTED by mg-8f56 — see STATE.md]** This Φ→Var reduction is invalid: it caps a lower bound on Var and infers an upper bound (inequality-direction error). By the law of total variance, `Var(pos_σ x)` splits into a within-window term (which `Φ` bounds) plus a between-window term (which it does not — e.g. parallel p-chains: window `O(1)` but `Var = Θ(n)`). The canonical record is in STATE.md.

**Honest caveat on the reduction.** (LOC) as stated quantifies over the threshold pair `(y^-, y^+)`,
which depends on `x`; mg-dcae's version quantifies over inversions against `e`. The two are the same
shape and I believe they are equivalent under (H) up to constants, but **I did not prove the
equivalence** and label it **[HEURISTIC]** in §8. Establishing it is a small, well-posed task and is a
prerequisite to claiming the convergence formally.

---

## 8. Status table

| § | statement | status |
|---|---|---|
| 2.1–2.2 | MS Def. 1.2, Thms 1.3 / 1.5 / 1.6, Thm 5.3, Rem. 1.7 / 1.8 / 1.9, Def. 2.11 | **CITED VERBATIM** — PDF v2 downloaded and text-extracted **this session**; each number located in the extracted text |
| 2.3 | `k=1 ⟹` supercritical, via Rem. 1.8 **and** the independent §2 body remark | **CITED VERBATIM**, two independent statements |
| 2.4 | Prop. 7.5's proof reduces Rem. 1.7 to Lemma 3.3(a), i.e. to a condition on `N^=` alone | **CITED VERBATIM** — this is the origin of Definition 4.0 |
| 2.4 | attribution correction: the `D(x) ⊕ Q ⊕ U(x)` normal form is **mg-48ab's Cor. 3.2, not MS's** | **PROVEN** by absence from the paper; MS's own poset form is Rem. 1.7 / Prop. 7.5 |
| 2.5 | Lemma 3.1 (bijections + injection), Lemma 3.3(a) | **CITED VERBATIM**; the observation that Lemma 3.1 is *unconditional* is new emphasis |
| 3 | **Lemma 3.1′** — MS's `N^=` classes = interval-endpoint classes at `i` | **PROVEN**, new |
| 3 | **Cor. 3.2** — Lemma 3.3(a) ⟺ "no interval has an endpoint at `i`" = mg-48ab's Window Rigidity, transcribed | **PROVEN**, new; simplifies mg-48ab Lemma 3.1 |
| 3 | **Cor. 3.3** — the outer `(∼,∼)` classes are consecutive-`U(x)`/`D(x)` double walls | **PROVEN**, new |
| 4.1 | **Definition 4.0** — `Φ_i = \Pr[i` is an endpoint of `I_x(τ) \mid i ∈ I_x(τ)]` | **DEFINITION**; naturality argued from Prop. 7.5 / Lemma 3.3(a), not asserted |
| 4.2 | **Theorem 4.1** — exact AF-free deficit inequality, credit − debit, with equality condition | **PROVEN**, new; **verified exactly** on `C_2⊔C_2` and `C_3⊔C_3` by hand |
| 4.3 | AF's role at `k=1` is to pay the `P,R` debits | **PROVEN** (Thm 4.1's RHS is negative in general) |
| 5.1 | **Lemma 5.1** — staircase: `Φ_i = h_i`, deficit ratio `= (1−h_{i−1})/(1−h_i)` | **PROVEN**, new; Stanley ⟺ increasing hazard rate ✔ |
| 5.2 | **Finding 5.2** — deficit is an *increment*, `Φ` is a *level*; loci mismatch; any repair is circular | **PROVEN**, new — **sharpens guardrail (a) from "false" to "false for this reason"** |
| 6.1 | **Theorem 6.1** — `δ(C_m ⊔ C_n) ≥ 1/3` for all `m,n ≥ 1`, `m+n ≥ 3`: no two-chain union is frozen | **PROVEN**, new, elementary; three spot-checks ✔ |
| 6.1 | the same family refuted Chan–Pak–Panova Conj. 9.18 (Aires–Kahn) | **CITED at second hand** via mg-dcae §3.3, which read the Chan–Pak survey footnote; **the primary was not accessed this session** |
| 6.2 | **Finding 6.2** — freezing removes the witness, not the mechanism | **PROVEN** as an implication; the antecedent ("can frozen posets have near-constant hazard?") is **OPEN** |
| 6.3 | **Finding 6.3** — frozen-conditional results are untestable; Thm 6.1 is not evidence | **PROVEN** (logic); applies to mg-48ab Thm 5.2 equally |
| 6.4 | guardrail (b) localized: the missing gap is needed for the debit side only | **PROVEN** given Thm 4.1 |
| 6.5 | **Finding 6.5** — `Φ` transfers to the gap law iff `P∖{x}` is the chain, i.e. never usefully | **PROVEN**, new; strengthens mg-48ab Finding 6.1, agrees with mg-dcae §5.5 |
| 7.1 | anchor, `≺_e` total, threshold pair, (J), (S) | **CITED** from mg-48ab §4 (not re-derived) |
| 7.2 | **Lemma 7.1** — approximate Window Rigidity, `π_T ≥ π(1−WΦ)` | **PROVEN**, new |
| 7.2 | **Theorem 7.2** — frozen-conditional near-sandwich inequality | **PROVEN**, new; **recovers mg-48ab Thm 5.2 exactly at `Φ=0`** ✔ |
| 7.3 | **Finding 7.3** — `Φ` is the right currency; `C_m⊔C_n` *confirms* `Φ`-stability | **PROVEN**, new |
| 7.4 | **Finding 7.4** — Thm 7.2 recovers only the trivial averaging bound `Φ ≳ 1/(3W)`; degenerates at the geometric regime | **PROVEN**, new — **this is the block** |
| 7.5 | **Finding 7.5** — (LOC) `⟹` `Φ ≥ cε` `⟹` variance half of (B) | **PROVEN** as a reduction |
| 7.5 | (LOC) ⟺ mg-dcae's `\max_x Σ_{y∥x}\Pr[\text{inverts}] = O(1)` | **HEURISTIC** — same shape, equivalence **not proved**; flagged as a prerequisite |
| — | mg-48ab Thm 5.2 / Prop. 5.3; mg-dcae Finding 3.1 / §5 | **UNTOUCHED** — nothing here contradicts them |
| — | L1b / (decay) / (B) | **STILL OPEN** — nothing here closes them |

**No computation was run.** No dataset, enumeration, script, or Lean file was produced. The only
arithmetic is the two hand-verified interval tables in §4.2, the binomial algebra of §6.1, and its three
spot-checks — all done in-line. The Ma–Shenfeld PDF was downloaded to a scratch directory for reading
only; it is not committed.

---

## 9. Honest verdict (deliverable 4)

**Does a frozen-conditional combinatorial stability theorem emerge? — PARTIALLY, and not in the currency
the ticket named.**

1. **A natural near-ordinal-sandwich distance emerges cleanly** (Definition 4.0), and it is forced rather
   than chosen: Ma–Shenfeld's own Prop. 7.5 reduces their extremal condition to a statement on `N^=`
   alone, whose normalized violation is exactly `Φ`. The `k=1` interval translation (§3) makes their
   Lemma 3.1 / 3.3(a) transparent and, as a byproduct, gives a one-line proof of mg-48ab's Window
   Rigidity Lemma.

2. **A stability theorem in the *deficit* currency does not emerge, and cannot** (Finding 5.2). The
   deficit is a hazard-rate increment; `Φ` is a hazard-rate level. Ma–Shenfeld's realizable equality
   locus (`h ≡ 0`) is strictly inside the deficit-zero numerical locus (`h ≡ const`), and posets
   accumulate on the difference — the geometric ray — at rate `Θ(1/n)`. **This upgrades guardrail (a)
   from a refutation to an explanation, and shows every repair by re-choosing `Φ` is circular.**

3. **A stability theorem in the `Φ` currency partially emerges** (Theorem 7.2), is faithful (it recovers
   mg-48ab Theorem 5.2 exactly at `Φ = 0`), and is genuinely frozen-conditional and purely combinatorial
   — guardrails (a) and (b) both honored. **But it recovers only the trivial averaging bound**
   (Finding 7.4), because it degenerates in exactly the near-geometric regime that Finding 5.2 identifies.

4. **The block is guardrail (a) resurfacing as a *regime*, not as a *family*.** Theorem 6.1 —
   `δ(C_m ⊔ C_n) ≥ 1/3` for every `m, n` — is a real and new positive: the family that refuted
   unconditional stability, and that also killed Chan–Pak–Panova Conj. 9.18, is unavailable against a
   frozen hypothesis. But Finding 6.2 is the counterweight: freezing constrains **pair marginals**, and
   the obstruction is about the **shape** of a position law. No implication between the two is known, and
   this is the arc's already-recorded marginals-vs-joint wall, reached from a new direction.

5. **The residual lands on an already-named lemma** (Finding 7.5): `Λ = O(1)`, the locality bound, which
   is mg-dcae §7.2's independently-recommended first lemma. **Two routes designed from opposite ends
   converge on it, and it would close both halves of (B) rather than one.** That convergence — not any
   theorem above — is the most actionable output of this session.

6. **A caution that should propagate to `STATE.md`** (Finding 6.3): frozen-conditional theorems in this
   arc are untestable, so results of the form "freezing excludes the known counterexample" must not be
   scored as evidence. Theorem 6.1 is offered under that caution.

**Recommended forward action.** Do **not** commission further work in the deficit currency — Finding 5.2
closes it structurally, over and above mg-dcae's refutation. Restate the arc's residual in the `Φ`
currency (Finding 7.3). Then attack (LOC) / mg-dcae Prop. 5.4's hypothesis, starting with the small
prerequisite of proving the two formulations equivalent under (H) (§7.5 caveat).

---

## 10. One line for the attempt index (for pm-onethird)

> `residual REFUTED → residual EXPLAINED + re-denominated` | **MS near-sandwich stability (mg-0ed7)** |
> ***AMBER-partial-emergence.*** Ma–Shenfeld arXiv:2211.14252v2 re-read from the PDF this session (all
> theorem numbers re-verified; **attribution fix: the `D(x)⊕Q⊕U(x)` normal form is mg-48ab's Cor. 3.2, not
> MS's — MS's poset form is Rem. 1.7 / Prop. 7.5**). New **`k=1` interval translation**: MS's `N^=`
> companion classes are exactly **interval-endpoint classes** of the insertion family, so Lemma 3.3(a) ⟺
> "no `I_x(τ)` has an endpoint at `i`" — a one-line proof of mg-48ab's Window Rigidity. The natural
> near-sandwich distance is forced, not chosen: **`Φ_i = Pr[i` is an endpoint of `I_x(τ) | i ∈ I_x(τ)]`**
> (MS's own Prop. 7.5 reduces their condition to `N^=` alone). New **exact AF-free deficit inequality**
> from MS Lemma 3.1 alone: `deficit ≥ (B−C)² + S(2|N^=|−S) − [P(A+2C)+R(A+2B)+PR]` — **credit minus
> debit**, sharp (verified exactly on `C_2⊔C_2`, `C_3⊔C_3`); the debits are "double-wall" counts at the
> *outer* indices, and **paying them is precisely what AF contributes at `k=1`**. **THE BLOCK, sharpened:**
> on staircase families `Φ_i = h_i` (hazard rate) while `deficit ratio − 1 = (h_i − h_{i−1})/(1−h_i)` —
> **the deficit is an increment, the distance is a level**, so `deficit ≥ cΦ` is impossible and **no
> re-choice of `Φ` repairs it**: `Φ` must vanish on MS's realizable locus `{h≡0}` while the deficit
> vanishes on the larger numerical locus `{h≡const}`, and posets **accumulate** on the difference (the
> geometric ray) at rate `Θ(1/n)`. This **explains** mg-dcae's refutation rather than restating it. **New
> positive:** `δ(C_m ⊔ C_n) ≥ 1/3` for **all** `m,n ≥ 1`, `m+n ≥ 3` (elementary, `f(k) = \binom{m+n-k}{m}/\binom{m+n}{m}`
> hazard-crossing argument) — **no union of two chains is frozen**, so guardrail (a)'s witness (and the
> family Aires–Kahn used to kill CPP Conj. 9.18) is unavailable against a frozen-conditional target.
> **But freezing removes the witness, not the mechanism** — the obstruction is the *regime* `h ≈ const`,
> and freezing constrains pair marginals while the obstruction is about position-law shape (the arc's
> known marginals-vs-joint wall, new direction). **Frozen-conditional attempt:** new approximate Window
> Rigidity `π_T ≥ π(1−WΦ)` and collision `1/3 + 2ε ≤ (1 − π(1−WΦ)) + (Λ+1)/W`, which **recovers mg-48ab
> Thm 5.2 exactly at `Φ=0`** ✔ — but it yields only `Φ ≳ 1/(3W)`, **the trivial averaging bound**,
> degenerating exactly in the geometric regime. **Re-denomination (the useful output):** the deficit was
> never the right currency — a `Φ` lower bound directly gives `Var(pos) = O(Φ^{-2})` via conditional
> uniformity, and **`C_m⊔C_n` has `Φ = 1/2`, i.e. the deficit-refuting family is a *confirming* instance
> for `Φ`-stability.** **Residual converges on an already-named lemma:** `(LOC) Λ = Σ_{z∥x}Pr[y⁻<z<y⁺] = O(1)`
> ⟹ `Φ ≥ cε` ⟹ the variance half of (B); (LOC) is (up to an unproved equivalence, flagged) **mg-dcae
> §7.2's independently-recommended first lemma**, which already closes the *bias* half — **so one lemma
> closes both halves, and two routes designed from opposite ends converge on it.** **Transfer question
> (guardrail (c)) answered sharply:** `Φ` transfers to the gap/slot law **iff `P∖{x}` is the chain**, i.e.
> never usefully — the failure is at the level of coordinates, before any inequality. **Methodological
> caution recorded:** frozen-conditional theorems here are **untestable** (the hypothesis is conjecturally
> empty), so "freezing excludes the counterexample" is **not evidence** — applies to mg-48ab Thm 5.2 too.
> **NO COMPUTATION RUN.**

---

*mg-0ed7. No datasets generated, no enumerations run, no Lean written, no scripts committed. Claims
labelled per §8; Ma–Shenfeld access level: PDF v2 text-extracted and read this session. mg-48ab's
Theorem 5.2 and mg-dcae's Finding 3.1 are both untouched and both remain correct.*
