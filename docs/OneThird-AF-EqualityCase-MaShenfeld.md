# OneThird — AF equality-case theory (Ma–Shenfeld) pointed at the frozen hypothesis

**Work item:** mg-48ab. **Constraint honored:** NO NEW COMPUTATION — no datasets, no enumerations, no
Lean, no scripts. Literature + proof only. Every numeric below is an exact by-hand calculation done
in-line or a verbatim citation.

**READ-FIRST completed.** (1) `drellem2/onethird_program` `STATE.md` — attempt index, the mg-a1ec row,
"Where the threads converge" (the refined target: *use AF equality-case rigidity to force the first
slot-sequence dropout in real frozen posets*). (2) `docs/OneThird-EntropyDiscontinuity-Mechanism.md`
(mg-a1ec): Prop. 5.2, Prop. 5.3, Finding 5.4 (AF saturation), Finding 6.0 (type mismatch), the
Blocking Dichotomy, Theorem-Target B. (3) **Ma–Shenfeld, arXiv:2211.14252v2 (30 Nov 2023), *The
extremals of Stanley's inequalities for partially ordered sets*** — read in full text this session
(PDF obtained and text-extracted; the extraction failure that blocked mg-a1ec §5.3 is resolved).
Per the ticket I do **not** lean on the Aires–Kahn step of mg-a1ec §7; see §7 below.

---

## 0. Verdict

**GREEN-partial — the equality-case classification DOES exclude freezing on the full-support flat
law, and Ma–Shenfeld is load-bearing in the proof. It does NOT close (decay), and the reason is
sharp and new: Ma–Shenfeld is a *qualitative* rigidity theorem, while (decay) needs a *quantitative
stability* theorem that does not exist.**

Four deliverables, labelled per §8:

1. **(a) The characterization is extracted and pinned** (§2), verbatim, with theorem numbers, and
   **specialized to our case `k = 1`** — where Ma–Shenfeld's Remark 1.8 states that *every* poset is
   supercritical, so the clean Theorem 1.3 applies unconditionally. **PROVEN/CITED.**
2. **New lemma: Window Rigidity (§3, Lemma 3.1).** A Stanley-flat run of the absolute-position law
   forces the *entire* insertion-interval family to be rigid: every `τ ∈ L(P∖x)` either gives `x`
   freedom across the whole run or misses the run entirely. **This is strictly stronger than
   flatness** — §3.3 exhibits an interval configuration that is flat but not rigid, which
   Ma–Shenfeld forbids. So MS does real work; it is not a restatement of Finding 5.4. **PROVEN.**
3. **(b/c) The test against `δ < 1/3` is run and it BITES (§4–§5).**
   > **Theorem 5.2.** *If `N_i(x)` is exactly flat across its full support, of length `W ≥ 2`, then
   > `δ(P) ≥ 1/3`.* Equivalently: **no frozen poset admits a full-support flat absolute-position
   > law.** The fatal `r = 1` / `ρ ≡ 1` configuration of `CoreLemma-forDaniel.md` §2.1 form 3 is
   > **excluded**, in the absolute-position formulation. **PROVEN**, sharp (tight3 is the equality
   > case, `W = 3`, `δ = 1/3`).
   >
   > **Proposition 5.3 (quantitative, partial runs).** With `δ(P) = 1/3 − ε`, `m_x := #{z ∥ x}`,
   > `π := Pr[σ(x) ∈ run]`: every exact flat run satisfies
   > `1/3 + 2ε ≤ (m_x(1/3 − ε) + π)/W + (1 − π)`. **PROVEN.**

   The elementary anchor is *used*, not merely cited: it supplies the total order `≺_e`, and §4.2
   proves the new fact that **`Hi = {z : Pr[x < z] > 2/3}` is an `≺_e`-up-set**, which is what
   produces the single threshold pair the whole argument turns on.
4. **(c) The residual, located precisely (§6).** Theorem 5.2 gives `θ ≠ 1`; Prop. 5.2 of mg-a1ec
   needs `θ ≤ 1 − c`. **Ma–Shenfeld distinguishes equality from strict inequality with no gap**, so
   it cannot supply a rate. **The next tool is not another rigidity theorem — it is a stability
   theorem for Stanley's inequality (`N_i² ≥ (1+c)N_{i−1}N_{i+1}` away from the classified
   extremals), which as far as this session's survey goes does not exist.** Plus a second, prior
   obstruction: **object mismatch** (§6.1) — MS governs *absolute*-position sequences; the arc's
   primary `ρ_s` slot law is the *gap* sequence, for which the underlying inequality is itself false
   (mg-2acf).

**What is NOT claimed.** L1b is not closed. (decay) is not proved. (B) is not proved. Theorem 5.2 is
a special case of the 1/3–2/3 conjecture, not the conjecture. Nothing is asserted empirically; no
computation was run.

---

## 1. Anti-drift check

The ticket's target: *does the Stanley equality-case classification exclude frozen posets (⟹ `θ<1`
⟹ L1b closes)?* Section map: §2 extracts the classification; §3 derives the structural consequence
of a flat run; §4 sets up the frozen side (anchor + threshold pair); §5 collides them and gets the
theorem; §6 reports exactly where it stops; §7 literature; §8 status table; §9 forward vectors.

I have **not** re-derived Finding 5.4 (AF saturation), the (B) certificate, `(GID)`, `(★global)`, or
`E[M_{k,l}]`. They are consumed by citation only. §3.3 is precisely the demonstration that this
session is *not* a restatement of Finding 5.4: saturation says AF cannot separate the ray; Lemma 3.1
says the equality *classification* nonetheless pins the combinatorics that AF discarded.

---

## 2. (a) The Ma–Shenfeld characterization, extracted

### 2.1 Their setup (verbatim, arXiv:2211.14252v2 §1.2)

> "Let `ᾱ = {y_1, …, y_{n−k}} ∪ {x_1, …, x_k}` be a partially ordered set (poset) of `n` elements
> with a fixed chain `x_1 < ⋯ < x_k` of length `k`. … Fix `1 ≤ i_1 < ⋯ < i_k ≤ n` and fix `ℓ ∈ [k]`
> such that `i_{ℓ−1} + 1 < i_ℓ < i_{ℓ+1} − 1`. For `◦ ∈ {−, =, +}`, let
> `N^◦ := {σ ∈ N : σ(x_j) = i_j ∀ j ∈ [k]\{ℓ} and σ(x_ℓ) = i_ℓ + 1_◦}`…"
> "In [18, Theorem 3.2], Stanley showed that `|N^=|² ≥ |N^−||N^+|` (1.1) …"
> "To see the relation to log-concave sequences consider the case `k = 1` and set
> `a_i := |{σ ∈ N : σ(x_1) = i}|, i ∈ [n]`. (1.2) Then, (1.1) amounts to the statement that the
> sequence `{a_i}` is log-concave."

Conventions: `x_0` is adjoined below everything and `x_{k+1}` above everything; `i_0 := 0`,
`i_{k+1} := n+1`.

> **Definition 1.2 (companions).** "…The companions of `x_ℓ = σ^{−1}(i_ℓ + 1_◦)` are `σ^{−1}(i_j)`
> for `i_j ∈ {i_ℓ − 1, i_ℓ, i_ℓ + 1}\{i_ℓ + 1_◦}`… The companion lower in ranking is the lower
> companion and the companion higher in ranking is the upper companion."

### 2.2 The two theorems (verbatim)

> **Theorem 1.3 (Supercritical extremals of Stanley's inequalities).** *Suppose the poset `ᾱ` is
> supercritical. The following are equivalent:*
> *(i) `|N^=|² = |N^−||N^+|`.*
> *(ii) `|N^−| = |N^=| = |N^+|`.*
> *(iii) For every linear extension in `N^− ∪ N^= ∪ N^+`, both companions of `x_ℓ` are incomparable
> to `x_ℓ`.*

> **Theorem 1.5 (Critical extremals).** *Suppose the poset `ᾱ` is critical. The following are
> equivalent: (i), (ii) as above; (iii) For every linear extension in `N^− ∪ N^= ∪ N^+`, **at least
> one** companion of `x_ℓ` is incomparable to `x_ℓ`. In addition, there exist nonnegative numbers
> `N_1, N_2` such that [the counts of "only-lower-incomparable", "only-upper-incomparable", and
> "both-incomparable" extensions are the same for each `◦ ∈ {−,=,+}`].*

> **Theorem 1.6 (Extremals of Stanley's inequalities).** *Suppose `ᾱ` is a poset such that
> `|N^=| > 0`. Then … the conclusions of Theorem 1.5 remain true … If `ᾱ` is supercritical then the
> conclusions of Theorem 1.3 remain true.*

Criticality of posets is their Definition 2.11 (a system of counting inequalities over increasing
index sequences `j_0 < ⋯ < j_{p+1}`); it is stated there in terms of the fixed positions `i_j` and
the interval subposets `ᾱ_{>x_{j_q+1}, <x_{j_{(q+1)}}}`. **We do not need it**, by Remark 1.8.

> **Remark 1.8 (`k = 1`).** *"The characterization of the extremals of Stanley's inequalities when
> `k = 1` was done in [17, §15]. **It turns out that, when `k = 1`, the poset must be supercritical**
> and the characterization of [17, §15] in this case is the same as Theorem 1.3 and Remark 1.7."*

> **Remark 1.7 (poset characterization).** *"∀ `y < x_ℓ` : ∃ `s(y) ∈ {0,…,k+1}` s.t. `y < x_{s(y)}`
> and `|{z ∈ ᾱ : y < z < x_{s(y)}}| > i_{s(y)} − i_ℓ`;   ∀ `y > x_ℓ` : ∃ `r(y) ∈ {0,…,k+1}` s.t.
> `y > x_{r(y)}` and `|{z ∈ ᾱ : x_{r(y)} < z < y}| > i_ℓ − i_{r(y)}` (1.6); see Proposition 7.5."*
> (MS also record that Chan–Pak [6, Thm 1.3] make a (1.6)-style *poset* characterization impossible
> for critical posets, on complexity-theoretic grounds — so the clean form really is a `k ≤ 2`
> phenomenon; cf. their Remark 1.9, quoting Chan–Pak [6, Lemma 9.1] for `k = 2`.)

### 2.3 What this says for us — the `k = 1` specialization

Our object is exactly `k = 1`: `x_1 = x` is the single distinguished element and
`N_i(x) = a_i = #{σ : σ(x) = i}` is mg-a1ec's *absolute-position* sequence. Then `N^− , N^=, N^+` are
the extensions with `x` at `i−1, i, i+1`; the admissible indices are `1 < i < n`; and by **Remark
1.8 the poset is automatically supercritical**, so **Theorem 1.3 applies with no side condition**.

> **(MS-1) [CITED, exact].** For any finite poset `P`, any `x ∈ P`, any `1 < i < n` with `N_i > 0`:
> `N_i² = N_{i−1}N_{i+1}` **⟺** `N_{i−1} = N_i = N_{i+1}` **⟺** for every `σ` with
> `σ(x) ∈ {i−1, i, i+1}`, the two elements occupying the other two of those three positions are both
> **incomparable to `x`**.

The parenthetical (ii) is already a real gain over Stanley alone, and MS flag it themselves: a
geometric progression `abc^{−1}, abc, abc^{+1}` satisfies the inequality with equality, and
**Theorem 1.3(ii) excludes it**. This is worth recording against mg-a1ec Finding 5.4:

> **Correction 2.1 to mg-a1ec §2.2/§5.2 [PROVEN, from MS Thm 1.3(ii)].** mg-a1ec asserts that "the
> whole ray `r ∈ (0,1]` is an equality case" of Stanley's inequality and concludes AF "sees the
> geometric ray". **The ray is an equality case only as an abstract numerical sequence.** No poset
> realizes a locally-geometric absolute-position law with ratio `r ≠ 1` at an equality index: MS
> Thm 1.3(i)⟹(ii) forces `r = 1` locally at every equality index. **The realizable part of the
> equality locus is exactly the flat part.** Finding 5.4's *conclusion* (AF cannot separate the KL
> optimum from the flat law, because the inequality is saturated at both) stands; but the geometric
> ray is not a family of realizable equality cases, and the arithmetic-selection framing of Finding
> 5.4 is therefore weaker than stated. This also means the equality-case theory is pointed at a
> *single* object — the flat law — which is the good news for §5.

Also worth stating, because it is what §3 exploits and it is *not* what mg-a1ec expected:

> **(MS-2) [reading].** Theorem 1.3(iii) is a **comparability** condition, and a *local* one. At
> first sight this is Finding 6.0's "type mismatch" all over again — the fatal flat configuration
> has `x` incomparable to everything nearby, so it satisfies (iii) *by construction* and no
> contradiction can come from (iii) alone. **That first reading is correct and is the reason the
> naive attack fails.** The content of §3 is that (iii) applied *simultaneously across a whole flat
> run* is not local at all: it globally rigidifies the insertion-interval family, and *that* is a
> statement with mass-level consequences.

---

## 3. Window Rigidity — what a flat run actually forces

Throughout, `D(x)`, `U(x)` are the strict down/up-sets, `d := |D(x)|`, `u := |U(x)|`,
`m_x := #{z : z ∥ x}`, `n = 1 + d + u + m_x`. We use mg-a1ec Prop. 4.1 (**CU**, conditional
uniformity; proved there, elementary): for `τ ∈ L(P∖x)`, the admissible insertion slots form a
non-empty integer interval `I_x(τ)`, `e(P) = Σ_τ |I_x(τ)|`, and conditionally on `τ` the position of
`x` is **uniform on `I_x(τ)`**. Consequently `N_p(x) = #{τ : p ∈ I_x(τ)}` (mg-a1ec Cor. 4.3): the
position law is a *coverage count of an interval family*.

Call `[i, j] ⊆ [1, n]` a **flat run** if `N_p(x) = c > 0` is constant for `p ∈ [i, j]`, and write
`W := j − i + 1`.

> **Lemma 3.1 (Window Rigidity).** *Let `[i,j]` be a flat run with `W ≥ 3` and `1 ≤ i`, `j ≤ n`.
> Then for every `τ ∈ L(P∖x)`:*
> $$I_x(\tau) \supseteq [i,j] \qquad\text{or}\qquad I_x(\tau) \cap [i,j] = \varnothing .$$
> *In particular `c = #\{τ : I_x(τ) ⊇ [i,j]\}`, and conditionally on `x` landing in the run, `x` is
> uniform on an interval containing the whole run.*
>
> **Proof.** *Step 1 (no interval ends strictly inside the run).* Suppose `I_x(τ)` meets the
> interior `[i+1, j−1]` and `h := \max I_x(τ) ≤ j − 1`. Then `h ∈ [i+1, j−1]`, so `1 < h < n` and
> `N_{h−1} = N_h = N_{h+1} = c > 0` by flatness; hence `|N^=| > 0` at index `h` and, by Remark 1.8,
> `ᾱ` is supercritical there, so **Theorem 1.3(iii)** applies at `h`. Insert `x` into `τ` at slot
> `h`, obtaining `σ ∈ N^=`. Its upper companion is the element at position `h+1` of `σ`, i.e. the
> element at `τ`-position `h`. Since `h = \max I_x(τ)`, slot `h+1` is inadmissible, which (given
> that slot `h` is admissible) happens exactly when that element lies in `U(x)` — i.e. the upper
> companion is **comparable** to `x`. This contradicts Theorem 1.3(iii). Hence `\max I_x(τ) ≥ j`;
> symmetrically `\min I_x(τ) ≤ i`, so `I_x(τ) ⊇ [i,j]`.
> *Step 2 (nothing sits only on an endpoint).* By Step 1, `N_p = #\{τ : I_x(τ) ⊇ [i,j]\} =: c'` for
> every interior `p`, so `c' = c`. Now `N_i = c' + #\{τ : I_x(τ) ∩ [i,j] = \{i\}\}`, and `N_i = c`
> forces the second term to vanish; likewise at `j`. ∎ *(PROVEN, new. Uses MS Thm 1.3 + Rem. 1.8 and
> mg-a1ec Prop. 4.1.)*

### 3.2 The full-support corollary

> **Corollary 3.2 (ordinal-sum rigidity).** *Suppose `N_·(x)` is flat across its **full support**
> `[d+1, n−u]`, of length `W = m_x + 1 ≥ 3`. Then `I_x(τ) = [d+1, n−u]` for **every**
> `τ ∈ L(P∖x)`, and consequently*
> $$P \;=\; D(x) \;\oplus\; Q \;\oplus\; U(x), \qquad x \in Q,\ \ x \parallel z\ \ \forall z \in Q∖\{x\},\ \ |Q| = W .$$
>
> **Proof.** `I_x(τ)` is a non-empty sub-interval of the support `[d+1, n−u] = [i,j]`, so it cannot
> miss `[i,j]`; by Lemma 3.1 it contains `[i,j]`, hence equals it. Then `\min I_x(τ) = d+1` for every
> `τ`, i.e. `\max_{y ∈ D(x)} \mathrm{pos}_τ(y) = d`, i.e. `D(x)` occupies positions `1..d` in *every*
> `τ`. If some `z ∉ D(x) ∪ \{x\}` were not above some `y ∈ D(x)` in `P`, some `τ` would place `z`
> before `y`, pushing `\max_{D(x)} \mathrm{pos}_τ ≥ d+1`. So `D(x) < z` for all such `z`, i.e.
> `P = D(x) ⊕ (P ∖ D(x))`; dually for `U(x)`. Every `z ∈ Q∖\{x\}` occupies a position inside
> `I_x(τ)`, so `x` may be inserted on either side of it: `z ∥ x`. ∎ *(PROVEN, new.)*

### 3.3 Why this is not free — MS is load-bearing

Flatness **alone** does not give Lemma 3.1. Coverage counts of an interval family can be flat
without any interval covering the run: take two extensions `τ_1, τ_2` of `P∖x` with
`I_x(τ_1) = [1,2]` and `I_x(τ_2) = [3,4]`. Then `N = (1,1,1,1)` — perfectly flat on `[1,4]` — yet no
`τ` gives `x` freedom across the run, and the conclusion of Cor. 3.2 fails. Lemma 3.1 says **no
poset realizes this**: at index `h = 2` the equality `N_2² = N_1 N_3` holds while the upper companion
of `x` (the element at position 3) lies in `U(x)`, contradicting MS Thm 1.3(iii).

> **Finding 3.3.** *The Ma–Shenfeld classification converts a **numerical** hypothesis (flat run)
> into a **structural** one (full-window conditional uniformity, and in the full-support case an
> ordinal-sum decomposition with a free element). This is exactly the "support-level ⟶ mass-level"
> upgrade that mg-a1ec §6.2 identified as required and could not supply.* **PROVEN.**

---

## 4. The frozen side: the anchor, the total order, and the threshold pair

`δ(P) := \max` over incomparable pairs of `\min(\Pr[y<z], \Pr[z<y])`; **frozen** means
`δ(P) = 1/3 − ε` for some `ε > 0`, i.e. **every** pair `\{y,z\}` (comparable pairs trivially) has
`\Pr[y <_σ z] ≤ 1/3 − ε` or `≥ 2/3 + ε`.

### 4.1 The anchor (cited, elementary)

`\Pr[y<z] + \Pr[z<w] + \Pr[w<y] ≤ 2` for any triple (mg-a1ec §3.3, exact computation over the six
orders of a triple). Hence the strong-majority tournament `y ≺_e z :⟺ \Pr[y<z] ≥ 2/3 + ε` has no
3-cycle, so under freezing it is a **total order `≺_e` on `P`** (transitive tournament).

### 4.2 The threshold pair (new)

Fix `x`. Put `Hi := \{z ≠ x : \Pr[x<z] ≥ 2/3+ε\}`, `Lo := \{z ≠ x : \Pr[x<z] ≤ 1/3−ε\}`; freezing
makes `\{Lo, Hi\}` a partition of `P ∖ \{x\}`.

> **Lemma 4.1.** *`Hi` is an `≺_e`-up-set and `Lo` an `≺_e`-down-set.*
>
> **Proof.** Let `y ∈ Hi` and `y ≺_e z`. Then
> `\Pr[x<z] ≥ \Pr[x<y \text{ and } y<z] ≥ \Pr[x<y] + \Pr[y<z] − 1 ≥ (2/3+ε)+(2/3+ε)−1 = 1/3+2ε`,
> which exceeds `1/3 − ε`, so `z ∉ Lo`, so `z ∈ Hi`. ∎ *(PROVEN, elementary, new.)*

Hence if `Lo ≠ ∅ ≠ Hi` there is a **unique `≺_e`-consecutive threshold pair** `(y^-, y^+)` with
`y^- = \max_{≺_e} Lo`, `y^+ = \min_{≺_e} Hi`, and:

- **(J) the jump.** `\Pr[y^- <_σ x <_σ y^+] ≥ \Pr[x<y^+] − \Pr[x<y^-] ≥ (2/3+ε)−(1/3−ε) = 1/3 + 2ε.`
  *(The first inequality because `\{x<y^+\}∖\{x<y^-\} ⊆ \{y^- < x < y^+\}`.)*
- **(S) the squeeze.** For every `z ∉ \{x, y^-, y^+\}`: either `z ≺_e y^-`, whence
  `\Pr[y^- <_σ z] ≤ 1/3−ε`, or `z ≻_e y^+`, whence `\Pr[z <_σ y^+] ≤ 1/3−ε`. Either way
  `\Pr[y^- <_σ z <_σ y^+] ≤ 1/3 − ε`.

> This is the exact point where the ticket's requirement "(b) test against the elementary anchor" is
> discharged: **the anchor is what makes `(y^-, y^+)` a single well-defined pair**, so that (J) and
> (S) can be collided. Without transitivity of `≺_e` there is no threshold and no jump.

**(J) says a whole third of `x`'s mass falls into one `≺_e`-gap; (S) says every individual element
can occupy that gap only a third of the time. The collision is a counting contradiction as soon as
the number of elements that can occupy the gap is not much larger than `W`.** Lemma 3.1 is what
bounds that number by `W`.

---

## 5. (b) The collision — freezing versus the flat law

### 5.1 The general inequality

> **Proposition 5.1.** *Let `[i,j]` be a flat run for `x`, `W = j−i+1 ≥ 3`, let
> `π := \Pr[σ(x) ∈ [i,j]]`, and suppose `Lo ≠ ∅ ≠ Hi`. If `δ(P) = 1/3 − ε` then*
> $$\tfrac13 + 2ε \;\le\; \frac{m_x\,(\tfrac13 − ε) \;+\; π}{W} \;+\; (1 − π).$$
>
> **Proof.** Write `T := \{τ : I_x(τ) ⊇ [i,j]\}`; by Lemma 3.1 every other `τ` has
> `I_x(τ) ∩ [i,j] = ∅`, and `|I_x(τ)| ≥ W` for `τ ∈ T`. For each `τ` let `S_τ` be the number of
> admissible `x`-slots lying strictly between `y^-` and `y^+`. Since `e(P) = Σ_τ |I_x(τ)|` and, by
> CU, `x` is uniform on `I_x(τ)`,
> `\Pr[y^- < x < y^+] = \big(Σ_τ S_τ\big)/e(P)`.
> For `τ ∉ T`: bound `S_τ ≤ |I_x(τ)|`; these contribute `Σ_{τ∉T}|I_x(τ)|/e(P) = 1 − π`.
> For `τ ∈ T`: the admissible slots lie inside `I_x(τ)`, and consecutive admissible slots are
> separated by elements occupying `I_x(τ)`-positions — all of which are incomparable to `x`. Hence
> `S_τ ≤ B_τ + 1`, where `B_τ` counts the elements `z ∥ x` positioned strictly between `y^-` and
> `y^+`. Using `|I_x(τ)| ≥ W`,
> `Σ_{τ∈T} S_τ ≤ Σ_{τ∈T}(B_τ+1) ≤ \tfrac1W Σ_{τ∈T}|I_x(τ)|\,(B_τ+1) = \tfrac{e(P)}{W}\,\mathbb E[(B+1)\mathbf 1_T]`,
> where `\mathbb E` is over uniform `σ ∈ L(P)`. Now
> `\mathbb E[B\mathbf 1_T] ≤ Σ_{z ∥ x} \Pr[y^- <_σ z <_σ y^+] ≤ m_x(1/3 − ε)` by (S), and
> `\mathbb E[\mathbf 1_T] = π`. Combining with (J) gives the claim. ∎ *(PROVEN, new.)*

### 5.2 The full-support case: freezing is excluded outright

> **Theorem 5.2.** *Let `P` be a finite poset and `x ∈ P` such that the absolute-position law
> `N_·(x)` is exactly flat across its full support, of length `W ≥ 2`. Then `δ(P) ≥ 1/3`.*
> *Equivalently: **no frozen poset has an element with a full-support flat position law.***
>
> **Proof.** Suppose `δ(P) = 1/3 − ε`, `ε > 0`. For `W = 2`, Cor. 3.2 (whose `W ≥ 3` hypothesis is
> only used via Lemma 3.1; for `W = 2` argue directly, `I_x(τ)` being a sub-interval of a length-2
> support with `N` flat) gives `P = D ⊕ \{x, z\} ⊕ U` with `x ∥ z` and `\Pr[x<z] = 1/2`,
> contradicting freezing. So assume `W ≥ 3`. By Cor. 3.2, `P = D(x) ⊕ Q ⊕ U(x)` with `|Q| = W`,
> `x ∥ Q∖\{x\}`, `m_x = W − 1`, and `I_x(τ) = ` the `W` slots of the `Q`-block for every `τ`; so
> `π = 1`.
>
> *`Lo` and `Hi` are both non-empty.* Write `R := Q ∖ \{x\}`, `|R| = W−1`. By CU,
> `\Pr[x < z] = \mathbb E[\mathrm{pos}_τ(z)]/W` for `z ∈ R` (positions within the block), whence
> `Σ_{z∈R}\Pr[x<z] = (1 + 2 + ⋯ + (W−1))/W = (W−1)/2`, i.e. the average of `\Pr[x<z]` over `R` is
> exactly `1/2`. If `Hi = ∅` the sum would be `< (W−1)/3`; if `Lo = ∅` it would be `> 2(W−1)/3`.
> Both contradict `(W−1)/2`. (Elements of `D(x) ∪ U(x)` lie in `Lo ∪ Hi` too, which only helps.)
>
> *The collision.* Both `y^-, y^+ ∈ Q`: an element of `D(x)` has `\Pr[x<z] = 0` and is `≺_e`-below
> all of `R`, an element of `U(x)` has `\Pr[x<z] = 1` and is `≺_e`-above all of `R`, so the
> `≺_e`-threshold falls inside `R` (as `Lo ∩ R ≠ ∅ ≠ Hi ∩ R` by the display above). Since
> `P = D ⊕ Q ⊕ U`, no element of `D ∪ U` can be positioned strictly between `y^-` and `y^+`, so the
> squeeze (S) ranges over `R ∖ \{y^-, y^+\}`, of size `W − 3`. Applying Prop. 5.1 with `π = 1` and
> this sharper count (`m_x` replaced by `W−3`):
> $$\tfrac13 + 2ε \;\le\; \frac{(W−3)(\tfrac13 − ε) + 1}{W}
>   \;=\; \frac{W/3 − Wε + 3ε}{W} \;=\; \tfrac13 − ε + \tfrac{3ε}{W},$$
> i.e. `3ε ≤ 3ε/W`, i.e. `W ≤ 1` — contradicting `W ≥ 2`. ∎ *(PROVEN, new.)*

**Sharpness.** `tight3 = \{a < b\} ⊔ \{c\}` has `N_·(c) = (1,1,1)` flat on its full support, `W = 3`,
`δ = 1/3`. At `ε = 0` the displayed inequality reads `1/3 ≤ 1/3` — equality. So Theorem 5.2 is
**exactly tight**, and the extremal is exactly the arc's `tight3`. This is a strong internal check:
an argument that proved anything more would be wrong.

**Consistency check (independent of the proof).** Take `P = \{x\} ⊔ C`, `C` a chain of `n−1`
elements, `x` free. Then `N_i(x) ≡ 1` is full-support flat, and `\Pr[x < c_r] = r/n` sweeps `(0,1)`
in steps of `1/n`, so for `n ≥ 3` some pair is balanced and `δ ≥ 1/3`. ✔ Consistent.

**What Theorem 5.2 kills.** `CoreLemma-forDaniel.md` §2.1 form 3 states that (B) fails **iff** a
frozen poset realizes a flat-long slot law `ρ_s ≡ 1`. In the *absolute-position* formulation (the
one on which mg-a1ec's Props. 5.2/5.3 operate, and the only one Stanley/MS governs — see §6.1),
`ρ ≡ 1` across the support is exactly the hypothesis of Theorem 5.2. **That configuration does not
exist.** So on the absolute-position route the answer to the ticket's make-or-break question is:

> **A real frozen poset CANNOT sit at the full-support Stanley equality case. The first strict drop
> `θ < 1` is forced.**

### 5.3 Partial runs: the quantitative statement

> **Proposition 5.3.** *Under the hypotheses of Prop. 5.1, a flat run is impossible whenever*
> `π > 2/3 − 2ε + m_x(1/3−ε)/W`. *In particular, when the run carries essentially all of `x`'s mass
> (`π → 1`) and `m_x ≈ W − 1`, flat runs satisfy* `W ≤ 2/(9ε) + 1/3`.
>
> **Proof.** Rearrange Prop. 5.1. For the special case substitute `π = 1`, `m_x = W−1`:
> `1/3 + 2ε ≤ ((W−1)(1/3−ε)+1)/W` ⟹ `W/3 + 2Wε ≤ W/3 − Wε + 2/3 + ε` ⟹ `3Wε ≤ 2/3 + ε`. ∎
> *(PROVEN.)*

Reading: **for a frozen poset with a constant gap `ε`, exact flat runs that carry `x`'s mass have
length `O(1/ε)`.** They cannot be `Θ(n)`. That is Theorem-Target B of mg-a1ec §5.3, delivered in the
mass-carrying regime.

---

## 6. (c) Where it stops — the two obstructions, stated precisely

### 6.1 Obstruction I — object mismatch (prior, and it is a hard block)

Ma–Shenfeld govern `|N^=|² ≥ |N^−||N^+|` where a chain `x_1 < ⋯ < x_k` is pinned at **fixed absolute
positions** `i_1 < ⋯ < i_k`. At `k=1` this is precisely the absolute-position law `N_i(x)`.

The arc's primary object, however, is the **gap sequence**: `a_m = e(P_m)` = the number of linear
extensions in which exactly `m` elements of an incomparable chain `C = c_1 < ⋯ < c_p` precede `x`
(`CoreLemma-forDaniel.md` §1.3, `ρ_s := a_{s+1}/a_s`). This is *not* an instance of (1.1) for any
`k`: (1.1) pins absolute positions, the gap sequence marginalizes over them. And its log-concavity
is **numerically false** (mg-2acf, recorded in `STATE.md`: "*Slot-law log-concavity … numerically
false; distinct from Stanley's absolute-position approach*").

> **Finding 6.1.** *There is no equality theory to invoke for the arc's `ρ_s` slot law, because
> there is no inequality. Ma–Shenfeld can only ever be applied through the absolute-position
> reduction (mg-a1ec Props. 5.2/5.3). Any statement of the form "the fatal flat slot law is a
> Stanley equality case" must be read in the absolute-position sense or it is ill-typed.* **PROVEN
> (by the type of the objects) — and it means Theorem 5.2 closes the absolute-position form of the
> fatal configuration, not verbatim `CoreLemma-forDaniel.md` §2.1 form 3.** Reconciling the two
> forms is a named, separate obligation (§9, vector 2).

### 6.2 Obstruction II — MS is qualitative; (decay) needs stability

Theorem 5.2 and Prop. 5.3 deliver `θ ≠ 1` (no *exact* flat run of the relevant length). mg-a1ec
Prop. 5.2 delivers geometric decay `N_p ≤ N_{p_0}θ^{p−p_0}` — but **only with a rate `θ` bounded away
from 1**, and thence (B) only with a rate. Ma–Shenfeld's theorem is a dichotomy between `=` and `>`;
it attaches **no gap** to the `>`. A poset whose position law has ratios `1 − 1/n` violates no
equality case and is untouched by everything in §5.

> **Finding 6.2 (the sharp residual — this is the report).** *The remaining lever is not another
> rigidity/classification theorem. It is a **stability theorem for Stanley's inequality**: a bound
> of the form*
> $$N_i^2 \;\ge\; (1 + c\,\Phi(P,x,i))\;N_{i−1}N_{i+1}$$
> *with `Φ` a quantitative distance from the classified extremal locus of Theorem 1.3(iii) — i.e. a
> quantitative measure of how many linear extensions in `N^-∪N^=∪N^+` have a **comparable**
> companion. **No such stability result exists in the literature surveyed this session**
> (Shenfeld–van Handel Acta Math. 231 (2023) characterize AF extremals for polytopes but do not
> quantify the deficit; Chan–Pak–Panova's combinatorial atlas gives the `k=1` extremals, also
> qualitatively; Chan–Pak arXiv:2311.02743 §16 surveys the area).* **BLOCK-AND-REPORT.**

There is a concrete reason to expect this to be hard, and it is worth recording because it is
structural rather than a gap in effort: **Chan–Pak [6, Thm 1.3], as quoted by MS in Remark 1.7,
imply that a poset-level characterization of Stanley's equality cases in the style of (1.6) is
impossible for `k ≥ 3` short of collapsing complexity classes.** A *quantitative* version — which is
strictly more informative than the characterization — inherits that pressure at `k ≥ 3`. At `k = 1`,
our case, (1.6) *does* hold (Remark 1.8), so a `k=1` stability theorem is not obviously blocked by
complexity; that narrow target is the recommended next tool-build (§9, vector 1).

### 6.3 What is *not* the obstruction any more

- **Not** "AF is saturated so equality-case theory is the only lever and is untried" (mg-a1ec §9
  table, last row). The lever has now been pulled: it *is* effective (Lemma 3.1, Theorem 5.2), and
  Correction 2.1 shows the equality locus is smaller than mg-a1ec thought.
- **Not** Finding 6.0's "support-level vs mass-level" mismatch. Lemma 3.1 performs exactly that
  upgrade (Finding 3.3).
- **Not** the two-atom law (already retired by mg-a1ec §6).

The wall has moved from *"we have no tool at the equality case"* to *"the tool is exact-equality-only
and we need a rate"*. That is a strictly better place to stand.

---

## 7. Literature notes

- **Ma–Shenfeld, arXiv:2211.14252v2 (30 Nov 2023, 54 pp.), *Adv. Math.***— read in full this
  session. Theorems 1.3 / 1.5 / 1.6, Definition 1.2 (companions), Definition 2.11 (criticality),
  Remark 1.7 (poset form (1.6)), **Remark 1.8 (`k=1` ⟹ supercritical)**, Remark 1.9 (`k=2` via
  Chan–Pak), Theorem 5.3 (the `|N^=| = 0` trivial extremals, via splitting pairs). All quotations in
  §2 are verbatim from the PDF text layer.
- **Shenfeld–van Handel**, Acta Math. 231 (2023) — AF extremals for polytopes; the `k=1` poset
  characterization is their §15, per MS Remark 1.8. **Not read this session**; used only as MS cite
  it.
- **Chan–Pak** arXiv:2311.02743 (survey) and **Chan–Pak–Panova** arXiv:2005.08390 (combinatorial
  atlas), and Chan–Pak's complexity theorem — **not read this session**; used only as MS cite them,
  and labelled accordingly in §6.2.
- **Aires–Kahn, arXiv:2509.11549.** Per the ticket's explicit instruction, **the mg-a1ec §7
  "`O(log n)` minimal elements" consequence is NOT used anywhere above.** I fetched the abstract
  page this session; what I could read confirms the paper is titled *Balancing Extensions in Posets
  of Large Width* (Aires & Kahn, 15 Sep 2025) and proves `δ(P) → 1/2` under width conditions and
  `δ ≥ 1/e − o(1)` under others. **I could not verify verbatim the `ω(log n)` minimal-elements
  clause** that mg-a1ec §7 quotes and builds consequence (2) on. Following the ticket, I treat that
  consequence as unavailable. Nothing in §3–§5 depends on it. **Recommend mg-a1ec §7 be re-audited
  or struck.**
- **Sah arXiv:1811.01500** (width-2 gap, `β ≈ 0.348843`) — cited by mg-a1ec only; not used here.
- **Novelty, honestly reported.** Theorem 5.2's *conclusion* restricted to Cor. 3.2's normal form
  ("a poset with an element incomparable to all others satisfies 1/3–2/3") is very plausibly
  **folklore** — I did not survey for it and make no novelty claim. The claimed contributions are
  Lemma 3.1 (the MS ⟹ rigidity step), the Lemma 4.1 threshold-pair mechanism, and the combination.

---

## 8. Status table — proven / cited / conjectured / heuristic, line by line

| # | statement | status |
|---|---|---|
| 2.1–2.2 | MS setup, Thm 1.3 / 1.5 / 1.6, Def. 1.2, Rem. 1.7, **Rem. 1.8 (`k=1` ⟹ supercritical)** | **CITED VERBATIM** (PDF read this session) |
| 2.3 | **(MS-1)** the `k=1` specialization | **PROVEN** (immediate specialization of Thm 1.3 + Rem 1.8) |
| 2.3 | **Correction 2.1** — no poset realizes a locally-geometric equality case with `r ≠ 1` | **PROVEN** (MS Thm 1.3 (i)⟹(ii)) |
| 2.3 | (MS-2) the "first reading" — Thm 1.3(iii) alone yields no contradiction | **PROVEN** (it is satisfied by construction in the fatal configuration) |
| 3.1 | **Lemma 3.1 (Window Rigidity)** | **PROVEN**, new (MS Thm 1.3 + mg-a1ec Prop. 4.1) |
| 3.2 | **Cor. 3.2 (ordinal-sum normal form)** | **PROVEN**, new |
| 3.3 | **Finding 3.3** — MS is load-bearing, flatness alone is insufficient | **PROVEN** (explicit `[1,2] ∪ [3,4]` witness) |
| 4.1 | anchor ⟹ `≺_e` total under freezing | **CITED** (mg-a1ec §3.3, elementary) |
| 4.2 | **Lemma 4.1** (`Hi` is `≺_e`-up-closed); (J); (S) | **PROVEN**, elementary, new |
| 5.1 | **Prop. 5.1** (the general inequality) | **PROVEN**, new |
| 5.2 | **Theorem 5.2** — full-support flat law ⟹ `δ ≥ 1/3` | **PROVEN**, new; **sharp at tight3** |
| 5.2 | consistency check on `\{x\} ⊔` chain | **VERIFIED** by hand |
| 5.3 | **Prop. 5.3** — `W ≤ 2/(9ε) + 1/3` in the mass-carrying regime | **PROVEN** |
| 6.1 | **Finding 6.1** — object mismatch (gap sequence vs absolute position) | **PROVEN** by typing; the false gap-log-concavity is **CITED** (mg-2acf/STATE.md, not re-verified here) |
| 6.2 | **Finding 6.2** — the residual is a *stability* theorem, which does not exist | **BLOCK-AND-REPORT**; the non-existence is "**not found in the surveyed literature**", not a proof of non-existence |
| 6.2 | Chan–Pak complexity pressure on quantitative forms at `k ≥ 3` | **HEURISTIC** (their theorem is cited by MS; I did not read Chan–Pak) |
| 7 | folklore status of Theorem 5.2's normal-form conclusion | **NOT SURVEYED** — no novelty claim |
| — | L1b / (decay) / (B) | **STILL OPEN** — nothing here closes them |

No computation was run. No dataset, enumeration, or Lean file was produced.

---

## 9. Forward vectors (recommendations only; no tickets filed)

1. **[Highest] Build the `k=1` stability theorem.** Target:
   `N_i² ≥ (1 + c·Φ)N_{i−1}N_{i+1}` where `Φ` counts (a normalized version of) the linear extensions
   in `N^-∪N^=∪N^+` having a comparable companion. MS Remark 1.8 says `k=1` is entirely supercritical
   and admits the clean poset form (1.6), so the complexity obstruction MS record for `k ≥ 3` does
   not obviously bite here. This is the single object that upgrades Theorem 5.2 from `θ ≠ 1` to
   `θ ≤ 1 − c`, i.e. from "the flat law is excluded" to **(decay) ⟹ (B) ⟹ L1b**. It is a
   tool-build, not a search: the extremal locus is now known exactly.
2. **Reconcile the two slot laws (Finding 6.1).** Either (i) restate
   `CoreLemma-forDaniel.md` §2.1 form 3 in absolute-position terms — in which case Theorem 5.2
   already kills the `ρ ≡ 1` endpoint and the arc should say so — or (ii) exhibit a frozen
   configuration whose *gap* law is flat while its *absolute-position* law is not, which would show
   the absolute-position route is strictly weaker than the arc has assumed. This is a
   half-session reading/bookkeeping job with high leverage either way.
3. **Push Prop. 5.1 off the `π → 1` hypothesis.** The bound is vacuous when the flat run carries
   less than `2/3 − 2ε` of `x`'s mass. Combining Lemma 3.1 (which forces *every* interval to cover a
   flat run or miss it) with the log-concavity of `N` outside the run may bound the off-run mass;
   that would extend Theorem 5.2 from full-support to long-run.
4. **Housekeeping.** (i) Record Correction 2.1 against mg-a1ec §2.2/§5.2 and §9's last table row —
   the "sole remaining lever, untried" row is now **tried, and partially successful**. (ii) Re-audit
   or strike mg-a1ec §7 (Aires–Kahn), per the ticket's misattribution warning and §7 above.

**One line for the attempt index (for pm-onethird):**

> `Untried → ATTEMPTED · lever pulled` | **AF equality-case attack (mg-48ab)** | ***GREEN-partial.***
> Ma–Shenfeld arXiv:2211.14252 read in full. At `k=1` (our absolute-position law) **every poset is
> supercritical** (their Rem. 1.8), so Thm 1.3 applies unconditionally: equality ⟺ both companions
> of `x` incomparable, ⟺ `N_{i−1}=N_i=N_{i+1}`. New **Window Rigidity Lemma**: a flat run forces
> every insertion interval to cover the run or miss it (strictly stronger than flatness — witness
> given). Full-support flat ⟹ `P = D ⊕ Q ⊕ U` with `x` free in `Q`; colliding this with the
> elementary anchor (new: `Hi` is `≺_e`-up-closed ⟹ a unique threshold pair) gives
> **Theorem: a full-support flat absolute-position law forces `δ(P) ≥ 1/3`** — the fatal `r=1`
> configuration is **excluded**, sharp at tight3. Quantitatively `W ≤ 2/(9ε) + 1/3` when the run
> carries `x`'s mass. **Does NOT close (decay):** MS separates `=` from `>` with **no rate**, so
> `θ ≠ 1` but not `θ ≤ 1−c`. **Residual named: a `k=1` STABILITY theorem for Stanley's inequality
> (deficit vs. distance from the Thm 1.3(iii) locus) — does not exist in the surveyed literature.**
> Second, prior obstruction: **object mismatch** — MS governs absolute positions; the arc's `ρ_s`
> gap law is a different sequence whose log-concavity is false (mg-2acf), so the two "flat law"
> statements must be reconciled. mg-a1ec corrections: the geometric ray is **not** a family of
> realizable equality cases (Correction 2.1); mg-a1ec §7 Aires–Kahn consequence not used and flagged
> for re-audit.

---

*mg-48ab. No datasets generated, no enumerations run, no Lean written, no scripts committed. Claims
labelled per §8. The Ma–Shenfeld PDF was downloaded to a scratch directory for reading only; it is
not committed.*
