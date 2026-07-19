# OneThird — scoping the `k=1` quantitative stability theorem for Stanley's inequality

**Work item:** mg-dcae. **Constraint honored:** NO NEW COMPUTATION — no datasets, no enumerations, no
Lean, no scripts, no numerics. Literature + proof only. Every number below is an exact by-hand
binomial calculation carried out in-line and check-verified at `n = 2`.

**Deliverable type:** SCOPING / SURVEY. This is an approach map plus difficulties, per the ticket's
explicit framing. It is **not** an attempt to prove the theorem and **not** a re-derivation of
mg-48ab Theorem 5.2.

**READ-FIRST completed.** (1) `drellem2/onethird_program` `STATE.md` (fetched this session; the
mg-a1ec and mg-48ab attempt-index rows, "Where the threads converge", "The single lemma to prove",
"Why 1/3 — the elementary anchor"). (2) `docs/OneThird-AF-EqualityCase-MaShenfeld.md` (mg-48ab:
Window Rigidity Lemma 3.1, Cor. 3.2, Theorem 5.2, Prop. 5.3, Finding 6.1 object mismatch, Finding
6.2 residual). (3) `docs/OneThird-L1b-CoreLemma-forDaniel.md` (the `ρ_s` / `M_{k,l}` residual, the
dead-tools appendix §5). (4) The AF-stability, combinatorial-atlas, and complexity literature — see
the citation ledger in §8, which records access level per source. Per the ticket I do **not** use
the mg-a1ec §7 Aires–Kahn step.

---

## 0. Verdict

> **RED-for-the-named-residual / AMBER-with-a-redirect.**
>
> **The residual as named by mg-48ab Finding 6.2 is FALSE at the strength L1b needs, and I can
> exhibit the refutation by hand.** A `k=1` stability theorem of the advertised form
> `N_i² ≥ (1 + c·Φ)·N_{i−1}N_{i+1}` — with `c` absolute and `Φ` the normalized count of extensions
> in `N^-∪N^=∪N^+` having a comparable companion — is **refuted** by `P = C_n ⊔ C_n` (two disjoint
> `n`-chains), `x` the minimum of the first chain, at index `i = 2`: there **`Φ = 1/2` exactly**
> while the deficit is **exactly `1 + 1/(2n−1)`** (§3). The true relation in this family is
> `deficit ≈ Φ/n`, not `1 + cΦ` — a **factor-`n` pricing gap**, and `n` is precisely the factor
> L1b cannot absorb.
>
> **Consequences, in order of importance:**
>
> 1. **No route survives at the required strength, and the obstruction is not a gap in the
>    literature — it is the target being wrong.** Routes (i)–(iv) are surveyed in §4; each breaks,
>    but they all break *downstream* of the fact that the unconditional theorem they are trying to
>    prove does not exist. **BLOCK-AND-REPORT with the obstruction identified precisely.**
> 2. **The residual must be re-named.** Any statement strong enough for L1b must **consume the
>    frozen hypothesis (H)** — it cannot be a theorem about Stanley's inequality, because the
>    unconditional statement at that strength is refuted. So mg-48ab's Finding 6.2 does not reduce
>    L1b to a clean external tool-build; it **re-labels L1b as itself**. `STATE.md`'s own cautious
>    reading of mg-48ab ("a precise *relabeling* of the whole hard part, not a reduction") is
>    **confirmed, and now for a provable reason rather than a suspicion.** (§3.4)
> 3. **The object question (ticket deliverable 2) has a sharper answer than "`N_i` vs `ρ_s`".**
>    §5 gives an elementary exact decomposition of the (B) quantity into a **variance** part and a
>    **bias** part, and shows the variance part splits again into a **diagonal** part that is
>    `Θ(E[inv_e])` **for free with explicit constants** `[4/3, 2]`, and a **covariance** part that
>    carries all the difficulty. **`Var(pos_σ(x))` — not the Stanley deficit, and not `ρ_s` — is
>    what a stability theorem would have had to control**, and controlling it needs a *constant*
>    rate, which §3 prices as unattainable. **PROVEN, new, elementary.**
> 4. **`k=1` IS genuinely exempt from the complexity barrier — but the exemption is worth less than
>    it looks (§6).** In Chan–Pak's indexing our case is `k=0`; `EqualityStanley₀ ∈ P`, and their
>    `k ≥ 2` not-in-PH theorem **explicitly excludes** `k=0`. But (a) the standing conjecture that
>    the `k=0` defect is **not in `#P`** (Pak, Conj. 6.3) is aimed exactly at our object, and (b) it
>    obstructs an **exact combinatorial formula**, *not* an inequality — a point both the literature
>    summaries and mg-48ab's framing blur, and which I correct in §6.3. So the complexity barrier is
>    **not** the obstruction here; §3 is.
> 5. **Recommendation (§7): drop the stability framing entirely.** The concrete first lemma to try
>    is the **per-element inversion-mass bound** `max_x Σ_{y ∥ x} Pr[{x,y} inverts] = O(1)`, which
>    §5.4 proves suffices for the *bias* half of (B) outright, with no Stanley input. This is in the
>    Kahn–Saks / Aires–Kahn architecture — **non-strict** log-concavity plus a mean constraint —
>    which §4.4 documents as the only architecture that has ever produced quantitative balance
>    results, and which has **never once needed a deficit**.

**What is NOT claimed.** L1b is not closed. (decay) is not proved. mg-48ab's Theorem 5.2 is
untouched and remains correct (it is an exact-equality statement; §3 refutes a *stability*
statement, not it). §3's refutation kills the **unconditional** target; it does **not** refute a
frozen-conditional statement, because the refuting family is maximally *un*frozen (`δ = 1/2`, §3.3)
— that caveat is load-bearing and is stated wherever it applies. No computation was run.

---

## 1. Anti-drift check

The ticket asks for four things. Section map: §2 fixes the **ruler** (what rate does L1b actually
need — nothing in the arc had written this down); §3 is the **pricing/refutation**; §4 is
**deliverable 1** (approach survey, routes (i)–(iv), with the break point of each); §5 is
**deliverable 2** (the right object); §6 is **deliverable 3** (the complexity barrier at `k=1`);
§7 is **deliverable 4** (recommendation); §8 is the citation ledger with access levels; §9 the
status table; §10 the attempt-index line.

I have **not** re-derived mg-48ab's Theorem 5.2, Lemma 3.1, Cor. 3.2, or Prop. 5.1/5.3; they are
consumed by citation. I have not re-derived (GID), (DG), (A) SPREAD, or the elementary anchor.
§3 and §5 are the only places new mathematics appears, and both are elementary and self-checking.

---

## 2. The ruler — what rate does L1b actually need?

This section exists because the arc has been asking for "a rate" without recording **which** rate,
and the answer turns out to decide every route in §4.

### 2.1 The propagation mechanism

Stanley's inequality says `N_i² ≥ N_{i−1}N_{i+1}`, i.e. the consecutive ratios
`r_i := N_{i+1}/N_i` are **non-increasing** in `i`. This is the whole reason a *one-index* rate is
worth anything: if `r_{i₀} ≤ θ < 1` at a single index `i₀`, then `r_i ≤ θ` for every `i ≥ i₀`, hence

$$N_{i₀+t} \le N_{i₀}\,\theta^{\,t}\qquad(t \ge 0),$$

which is mg-a1ec Prop. 5.2's geometric decay. **A stability theorem is wanted only as a device to
manufacture that single strict drop with a rate.** This is worth stating explicitly because it means
a *uniform* deficit bound across all `i` was never necessary — a single index suffices. That is the
most favourable possible reading of the target, and §3 refutes it even in that favourable reading.

### 2.2 What a deficit bound converts into, quantitatively

Suppose `N_i² ≥ (1 + γ_i)N_{i−1}N_{i+1}` for `i` in some window. Then
`r_i ≤ r_{i−1}/(1 + γ_i)`, so starting from the mode (where `r ≈ 1`),

$$r_{\text{mode}+t} \;\le\; \prod_{s=1}^{t} (1+\gamma_s)^{-1}.$$

To reach `r ≤ 1 − c` for an **absolute** `c` one needs `Σ_{s≤t} γ_s ≳ c`. Hence:

> **Rate accounting (PROVEN, elementary).** With a deficit rate `γ ≡ γ(n)` uniform over the window,
> geometric decay with an **absolute** rate is reached only after `t ≳ c/γ(n)` indices. Therefore:
> - `γ = Θ(1)` ⟹ the drop happens after `O(1)` indices. **Usable.**
> - `γ = Θ(1/n)` ⟹ the drop happens only after `Θ(n)` indices. **Useless:** the position law can
>   stay flat across a window of length `Θ(n)`, giving `Var(pos_σ(x)) = Θ(n²)` and (by §5)
>   `Σ_x Var = Θ(n³)`, catastrophically worse than the `O(E[inv_e])` that (B) demands.
> - `γ = Θ((t+1)^{-(n+1)})` — the best rate that exists anywhere in the literature for a
>   log-concavity-of-this-type statement (Chan–Pak–Panova, §4.3) — is worse than useless.

**The ruler, in one line: L1b needs `γ = Θ(1)`, an absolute constant, independent of `n`.** Anything
polynomially small in `n` does not merely weaken the conclusion; it fails to produce a conclusion at
all. Every route in §4 must be judged against this and not against "does a stability theorem exist".

### 2.3 A first, free observation: no `Φ`-free bound can exist

A uniform `γ = Θ(1)` with **no** structural factor `Φ` is immediately impossible: the equality case
exists (`P = {x} ⊔ C` with `C` a chain has `N_i ≡ 1`, so `γ = 0`). So the target *must* be of the
form `1 + c·Φ` with `Φ` vanishing exactly on the Ma–Shenfeld / Shenfeld–van Handel extremal locus —
which is exactly why mg-48ab Finding 6.2 was posed in that shape. §3 shows that shape is also
refuted, which is the substantive content.

---

## 3. The pricing — the named residual is FALSE at the needed strength

### 3.1 The family, and an exact deficit formula

Let `m, n ≥ 2` and let

$$P \;=\; C_m \sqcup C_n$$

be the disjoint union of a chain `C_m : u_1 <\cdots< u_m` and a chain `C_n : v_1 <\cdots< v_n`
(so `|P| = m+n`, width 2). Mark `x := u_1`, the minimum of the shorter chain.

Because `x` is below all of `C_m∖{x}` and incomparable to all of `C_n`, its position in a linear
extension is `pos(x) = 1 + \#\{\text{elements of } C_n \text{ before } x\}` (1-indexed). Writing
`j` for that count, the extensions with `pos(x) = 1+j` are obtained by: placing the first `j`
elements of `C_n` before `x`, then freely interleaving the remaining `m−1` elements of `C_m` with
the remaining `n−j` elements of `C_n`. Hence, **exactly**,

$$\boxed{\;N_{1+j} \;=\; \binom{\,n-j+m-1\,}{\,m-1\,}\;}\qquad (0 \le j \le n).$$

*(Check: `Σ_j N_{1+j} = \binom{m+n}{m} = e(P)` by Vandermonde. ✔)*

Put `a := n − j`. Then `N_{1+j}/N_{j} = (a+1)/(a+m)` and `N_{1+j}/N_{2+j} = (a+m-1)/a`, so with
`i = 1+j`:

$$\boxed{\;\frac{N_i^{2}}{N_{i-1}N_{i+1}} \;=\; \frac{(a+1)(a+m-1)}{a\,(a+m)} \;=\; 1 \;+\; \frac{m-1}{a\,(a+m)}\;}$$

*(Algebra: `(a+1)(a+m−1) = a² + am + (m−1)` and `a(a+m) = a² + am`.)* **PROVEN, exact.**

### 3.2 The refuting instance

Take `m = n` (two equal chains, `|P| = 2n`) and `i = 2` (i.e. `j = 1`, `a = n−1`). Then

$$\frac{N_2^{2}}{N_1 N_3} \;=\; 1 + \frac{n-1}{(n-1)(2n-1)} \;=\; \boxed{\,1 + \frac{1}{2n-1}\,}.$$

Now compute mg-48ab's `Φ` — *"a quantitative measure of how many linear extensions in `N^-∪N^=∪N^+`
have a **comparable** companion"*, in its natural normalization as a fraction of `N^=`. Given
`σ(x) = i = 1+j`, everything below `x` in `σ` comes from `C_n` (all of `C_m∖\{x\}` is above `x`), so
the **lower** companion is always incomparable to `x`. The **upper** companion is the first element
of the free interleaving of the `m−1` remaining `C_m`-elements with the `a` remaining
`C_n`-elements, which is a `C_m`-element — i.e. **comparable to `x`** — with probability exactly

$$\Phi_i \;=\; \frac{m-1}{m-1+a}.$$

At `m = n`, `i = 2`, `a = n−1`: **`Φ₂ = (n−1)/(2n−2) = 1/2`, exactly, for every `n`.**

> **Finding 3.1 (PROVEN, new, exact; the headline of this session).**
> *For `P = C_n ⊔ C_n` and `x = \min C_n^{(1)}`, at `i = 2`:*
> $$\Phi_2 = \tfrac12 \quad\text{(independent of } n\text{)},\qquad
>   \frac{N_2^{2}}{N_1N_3} = 1 + \frac{1}{2n-1} \;\xrightarrow[n\to\infty]{}\; 1 .$$
> *Hence **no inequality of the form `N_i² ≥ (1 + c\,Φ_i)\,N_{i−1}N_{i+1}` with `c>0` absolute can
> hold**, for `Φ` = the fraction of `N^=`-extensions with a comparable companion. The largest
> admissible constant is `c ≤ 2/(2n−1) → 0`.*
>
> *More generally, from §3.1, in this family*
> `\frac{N_i^2}{N_{i-1}N_{i+1}} - 1 = \frac{m-1}{a(a+m)}` *while* `Φ_i = \frac{m-1}{m-1+a}`, *so*
> $$\frac{\text{deficit}}{\Phi_i} \;=\; \frac{a+m-1}{a(a+m)} \;\sim\; \frac{1}{a}\;=\;\frac1{n-j}.$$
> ***The deficit is smaller than the natural structural measure by a factor `Θ(n)`.***

**Verification at `n = 2` by full enumeration (by hand, 6 extensions).** `P = \{u_1<u_2\} ⊔
\{v_1<v_2\}`, `x = u_1`. The six linear extensions are
`u_1u_2v_1v_2, u_1v_1u_2v_2, u_1v_1v_2u_2, v_1u_1u_2v_2, v_1u_1v_2u_2, v_1v_2u_1u_2`, giving
`(N_1,N_2,N_3) = (3,2,1)`. Deficit `= 4/(3·1) = 4/3 = 1 + 1/(2·2−1)`. ✔ And `N^=` at `i=2` is
`\{v_1u_1u_2v_2,\; v_1u_1v_2u_2\}`; the upper companions are `u_2` (comparable) and `v_2`
(incomparable), so `Φ_2 = 1/2`. ✔ **Both formulas confirmed exactly.**

### 3.3 The load-bearing caveat: this family is maximally UNfrozen

`δ(C_n ⊔ C_n) = 1/2`: the two chain-minima `u_1, v_1` satisfy `Pr[u_1 ≺_σ v_1] = 1/2` by the
chain-swap symmetry. So Finding 3.1 refutes the **unconditional** stability theorem — a statement
about *all* posets, which is what "a `k=1` stability theorem for Stanley's inequality" means and what
mg-48ab Finding 6.2 asked for — and it does **not** refute a statement conditioned on (H). This
distinction is the entire content of §3.4 and must not be elided.

**Independent corroboration that this is the right extremal family.** The Chan–Pak survey
(arXiv:2311.02743) records, in a footnote, that **Aires and Kahn refuted Chan–Pak–Panova's
Conjecture 9.18** (a second-moment strengthening `E[f(x)²]/E[f(x)]² ≤ 4/3`) using exactly
`P = C_m + C_n` with `m, n/m → ∞` and `x = \min(C_m)` — the same family, the same marked element.
That the field's one recent attempt at a quantitative strengthening of a Stanley-adjacent bound died
on this family is strong evidence that Finding 3.1 is hitting the true extremal structure and not an
artifact of a bad `Φ`. *(CITED — the footnote was read this session in the survey full text; I did
not read Aires–Kahn's own statement of it, and per the ticket's misattribution warning I claim
nothing about Aires–Kahn's paper beyond the survey's report of a private communication.)*

### 3.4 What Finding 3.1 does to the residual

> **Finding 3.2 (the re-naming; PROVEN modulo §2.2's rate accounting).**
> *Any statement strong enough to give L1b its absolute-constant rate must consume the frozen
> hypothesis (H), because the unconditional statement at that strength is false (Finding 3.1).
> Therefore the mg-48ab residual is **not** "a `k=1` stability theorem for Stanley's inequality" —
> no such theorem exists at the needed strength — but rather:*
>
> > *a **frozen-conditional anti-concentration theorem**: for every poset satisfying (H) and every
> > `x`, the absolute-position law `N_·(x)` has consecutive ratio `≤ 1 − c` at some index in the
> > mass-carrying range, `c` absolute.*
>
> *That statement is, up to §5's translation, **`STATE.md`'s "single lemma to prove" restated**. The
> mg-48ab reduction is therefore **circular as a reduction**, though entirely correct as
> mathematics.*

`STATE.md`'s attempt-index row for mg-48ab already flags this ("a precise *relabeling* of the whole
hard part, not a reduction"). §3 upgrades that from an auditor's suspicion to a **proved fact**: the
external tool mg-48ab pointed at does not exist, and cannot, so no amount of tool-building recovers
the reduction.

**Consistency with the arc's own dead-tools list.** `CoreLemma-forDaniel.md` §5 already records
*"Per-pair / marginal freezing is insufficient … Decay must come from the **joint** LE structure, not
the marginals"* and *"the proof must use that `σ` ranges over a genuine poset's linear extensions"*.
Finding 3.2 is the same wall arrived at from the opposite direction: the marginal object (`N_i`, a
single element's position law) admits no unconditional rate, so the rate must come from (H) acting
jointly. ✔ Consistent — and this consistency is a check on Finding 3.1, not a coincidence.

---

## 4. DELIVERABLE 1 — the approach survey

Each route is judged against the §2.2 ruler (`γ = Θ(1)`) and against Finding 3.1.

### 4.1 Route (i) — a quantitative / stability version of Alexandrov–Fenchel, Shenfeld–van Handel style

**What it would give.** Stanley's `k=1` inequality is `N_i = (n−1)!\,V_{n−1}(K^{i−1}, L^{n−i})` for
order polytopes `K, L` (Shenfeld–van Handel §15.1), so an AF deficit bound
`V(K,L,Q_1,…)² − V(K,K,Q)V(L,L,Q) ≥ ξ(\cdot)` would specialize directly to a Stanley deficit.

**Where it breaks — three independent walls, in increasing order of depth.**

1. **No such theorem exists in the required generality, and the existing ones exclude our bodies.**
   The Shenfeld–van Handel Acta paper (arXiv:2011.04059, Acta Math. 231 (2023) 89–204) is a purely
   qualitative characterization; a full-text search of v2 for `stabilit` and `quantitativ` returns
   **zero occurrences**, and stability is not among the three open questions in their §16. The AF
   stability results that do exist — **Schneider**, *manuscripta math.* (1990); **Martínez-Maure**,
   *Monatsh. Math.* **182** (2017) 65–76 — require **full-dimensional convex bodies with `C²₊`
   boundaries**. Order polytopes are polytopes, and the mixed-volume configurations Stanley uses are
   lower-dimensional. **Every existing hypothesis fails on our bodies.** *(VERIFIED for the Acta
   paper by full-text extraction this session; ABSTRACT-ONLY for Schneider and Martínez-Maure.)*
2. **The analytic reason it stalls, stated by the authors themselves.** In the Duke companion paper
   (*The extremals of Minkowski's quadratic inequality*, arXiv:1902.10029, Duke Math. J. **171**
   (2022) 957–1027), **Remark 7.2** identifies the exact structure of a stability proof: it is
   equivalent to **(i)** the kernel of an operator `A` consisting only of linear functions (= the
   extremal characterization, which they prove) **plus (ii)** *"the remainder of the spectrum is
   separated from zero by a positive constant (which quantifies the deficit)"*. They then record
   (VERBATIM, extracted this session): *"If `A` were to have compact resolvent, then (ii) would
   follow directly from (i) by discreteness of the spectrum. Unfortunately … it is not true in
   general that `A` has compact resolvent. For this reason, it is far from clear whether we might
   expect even in principle to replace `μ_M` by `S_{M,M}/h_M` in Theorem 7.1."* **This is the
   cleanest available statement of why "characterization ⟹ stability" fails, and it is an
   obstruction in principle, not a gap in effort.**
3. **Even the one partial result is in the wrong norm.** Their **Theorem 6.1** *is* a genuine
   deficit bound — `V(K,L,M)² ≥ V(K,K,M)V(L,L,M) + C_M V(L,L,M)\inf(\cdots)` — but they immediately
   note (VERBATIM): *"As `supp S_{M,M}` is much smaller than `supp S_{B,M}`, only weak information
   on the extremals may be extracted from this result."* The deficit is measured in a norm too weak
   to see the extremal set. That is precisely the failure mode a `Φ`-shaped target needs to avoid.
4. **And there is a complexity obstruction sitting on top, built out of our own objects.**
   Chan–Pak, *Equality cases of the Alexandrov–Fenchel inequality are not in the polynomial
   hierarchy* (arXiv:2309.05764, Forum of Math. Pi **12** (2024) e21; STOC 2024), **Corollary 1.2**:
   a Bonnesen-type strengthening `δ ≥ ξ` with `ξ` poly-time computable on TU-polytopes forces
   `PH = NP`. Their own gloss: *"for the stability of the AF inequality, one should either avoid
   polytopes altogether and require some regularity conditions for the convex bodies … or be content
   with functions `ξ` which are hard to compute."* **Their proof runs through Stanley's order
   polytopes** — the obstruction is constructed inside our setting.

**Verdict on (i): DEAD, over-determined.** Four independent walls, of which #2 is the deepest and
#4 the most ironic. And note: even a miracle here would still be priced by Finding 3.1 — an AF
stability theorem is an unconditional statement, and unconditional statements at strength `Θ(1)` are
false. **Route (i) cannot in principle deliver what L1b needs, independent of whether it is
provable.**

*Scoping note on Cor. 1.2's applicability, for honesty:* Cor. 1.2 is about AF for TU-polytopes in
general, not about the specific one-parameter family `V(K^{i−1},L^{n−i})` at `k=1`. It does not
formally bite on our slice. I record it as **strong contextual pressure**, not as a proof that our
slice is obstructed. Labelled **HEURISTIC** in §9.

### 4.2 Route (ii) — the combinatorial atlas, run for a deficit rather than the bare inequality

**What it would give.** Chan–Pak's atlas (arXiv:2110.10740, *Log-concave poset inequalities*;
expository version arXiv:2203.01533) proves Stanley's inequality by induction on posets, showing a
family of matrices is **hyperbolic**: `⟨v,Mw⟩² ≥ ⟨v,Mv⟩⟨w,Mw⟩`. If the induction could be made to
carry a *surplus*, one would get a deficit bound with an explicitly tracked constant.

**Where it breaks — the mechanism is a signature theorem, and signature theorems have no modulus.**

1. **The reduction to hyperbolicity is a tautology.** With `C(P,k)` the extension matrix and `f,g`
   indicator vectors, the atlas gives `⟨f,Cg⟩ = N_k`, `⟨f,Cf⟩ = N_{k+1}`, `⟨g,Cg⟩ = N_{k−1}`. So
   `N_k² − N_{k−1}N_{k+1}` **literally is** the hyperbolic form. Nothing is gained or lost in the
   translation; all content sits in *"`C` has signature `(1, n−1)`"*.
2. **Signature is proved by Perron–Frobenius, which produces a dichotomy, not a gap.** The key lemma
   is `(Hyp) ⟺ (OPE)`, where **(OPE)** is *"`M` has at most one positive eigenvalue"*, and the proof
   step is an eigenvalue dichotomy (*"This implies that `λ ≥ 1` or `λ ≤ 0`"*). A dichotomy carries no
   modulus by construction. **This is the exact discrete analogue of Shenfeld–van Handel Remark 7.2
   (§4.1 wall #2): "at most one positive eigenvalue" is a kernel/sign statement; a deficit needs a
   *spectral gap*, and no step of the atlas produces one.** *(PARAPHRASED-FROM-READ-TEXT plus
   verbatim fragments extracted this session from the arXiv source of 2110.10740.)*
3. **A limiting step destroys any constant that survived.** Atlas regularity holds only for
   `0 < t < 1` on `M_t := tC(P,k) + (1−t)C(P,k−1)`; the conclusion for `C(P,k)` and `C(P,k−1)` is
   obtained by *"taking the limit `t→0` and `t→1`"*. **Any uniform-in-`t` constant one managed to
   carry would be evaluated at the endpoints where regularity fails.** This is a concrete, local
   obstruction — arguably the most repairable one in this whole survey, and the reason (ii) is the
   only route I do not classify as fully dead.
4. **The equality theory is a kernel condition, `Mz = 0`, with the proof step *"every term in the
   first sum is equal to 0"*.** Rigidity, no approximate analogue.
5. **The one formally deficit-shaped step is unusable:** the `(NDC) ⟹ (Hyp)` direction yields
   `⟨v,Mw⟩² − ⟨v,Mv⟩⟨w,Mw⟩ ≥ ⟨w,Mw⟩·(−⟨z,Mz⟩) + \text{AM–GM slack}`, but `g` is the **unknown Perron
   eigenvector** and `−⟨z,Mz⟩ ≥ 0` is known only from the spectral fact, with no lower bound. Getting
   a lower bound on `−⟨z,Mz⟩` **is** the spectral-gap problem of wall #2.
6. **Chan–Pak flag the absence themselves.** §16.11 of arXiv:2110.10740 (VERBATIM, extracted):
   *"Strict log-concavity inequalities are especially suggestive of possible quantitative results. …
   There are no explicit stronger bounds implying strict log-concavity in the style of Theorem 1.16
   and [BST]."*

**Verdict on (ii): AMBER-but-priced-out.** This is the only route with a *locally* repairable
obstruction (the `t→0,1` limit). But the repair reduces to lower-bounding the atlas spectral gap,
which is wall #2 of route (i) in discrete clothing — **routes (i) and (ii) converge on the same
missing object**, which is itself a useful scoping conclusion. And Finding 3.1 prices even a
successful repair: the atlas is unconditional, so its output is capped at `Θ(1/n)`.

### 4.3 Route (iii) — a direct combinatorial / injective deficit bound at `k=1`, bypassing AF

**What it would give.** A statement `N_i² − N_{i−1}N_{i+1} ≥ Ψ` with `Ψ` an explicit count of
extensions, proved by an injection. This is the only route whose output could plausibly be
`Φ`-shaped by construction.

**Where it breaks.**

1. **The easy directions already have an injection, and it is the wrong direction.** Shenfeld–van
   Handel note (VERBATIM, extracted this session): *"Once the correct statement has been realized,
   however, it is straightforward to find a direct proof of the easy directions `d ⟹ c ⟹ b ⟹ a` of
   Theorem 15.3."* The mechanism is a rank transposition `Π_{i,j}` giving `N_i^± ⊆ N_{i±1}`, hence
   `N_i ≤ N_{i±1}`. **The hard direction — that this is the *only* equality mechanism — is exactly
   what needs AF.** A deficit bound lives on the hard side.
2. **The precedent is discouraging and specific.** The *only* explicit quantitative strict
   log-concavity in this literature is Chan–Pak–Panova (arXiv:2205.02798, SIAM J. Discrete Math.
   **37** (2023) 1842–1880), for the **order polynomial**:
   `Ω(P,t)² ≥ (1 + (t+1)^{-(n+1)})·Ω(P,t+1)Ω(P,t−1)`. Three facts about it are all bad news:
   the rate is **exponentially small in `n`** (the authors call it *"far from optimal"*); it is for
   `Ω(P,t)` in `t`, **not** `N_i` in `i`; and — decisively — **the injective method demonstrably did
   not extend to the strict version; FKG was required.** That is a documented instance of exactly
   the obstruction route (iii) would hit.
3. **The `#P` conjecture is aimed at our object.** Pak, *What is a combinatorial interpretation?*
   (arXiv:2209.06142), **Conjecture 6.3**, restated as Conjecture 9.2 of the Chan–Pak survey:
   *"The defect of Stanley's inequality (Sta) is not in `#P`."* The survey adds (VERBATIM):
   *"In [CPP23b, §9.12], we wrote 'At this point, it is even hard to guess which way the answer
   would go. While some of us believe the answer should be negative, others disagree.' We have
   stronger convictions now."* And Chan–Pak's own gloss on their Cor. 1.5: *"Corollary 1.5 implies
   that the Stanley inequality (Sta) most likely cannot be proved by a direct injection."*
4. **Positive precedent exists, but only at width two.** Chan–Pak–Panova prove `q`-Stanley and
   `q`-Kahn–Saks **for width-two posets by explicit injection** (survey Thms 9.4, 9.5, from
   [CPP23a, Thms 7.1, 7.2]; VERBATIM: *"Theorems 9.4 and 9.5 are proved by an explicit injection."*).
   Likewise Daykin–Daykin–Paterson's **order-polynomial** Stanley analogue has an explicit injection
   **and its defect is in `#P`**. So the injective method works exactly where the object is either
   width-restricted or is `Ω(P,t)` rather than `N_i`.

**A correction I must make, because two independent literature summaries got it wrong and mg-48ab's
framing invites the same error (see §6.3): Conjecture 9.2 does NOT kill route (iii).** *"Defect not
in `#P`"* says the defect is not the counting function of a poly-time-verifiable witness set — i.e.
there is no exact bijective formula. A **stability theorem is an inequality**, `defect ≥ Ψ` with
`Ψ ∈ #P`, and that is entirely consistent with `defect ∉ #P`. The conjecture obstructs an exact
combinatorial *interpretation*, not a combinatorial *lower bound*.

**Verdict on (iii): AMBER on provability, DEAD on price.** It is the route least obstructed in
principle — Conjecture 9.2 does not bite, and width-two precedent exists. But it is unconditional,
so Finding 3.1 caps its output at `Θ(Φ/n)`, and §2.2 says `Θ(1/n)` is not a weak result but a
non-result. **The honest scoping statement is: (iii) is worth attempting only if one first believes
Finding 3.1 can be evaded, and §3.3 says the only way to evade it is to consume (H) — at which point
it is no longer route (iii).**

### 4.4 Route (iv) — the Kahn–Saks architecture: non-strict log-concavity + a mean constraint

This is the route the ticket asks me to identify, and it is the most important part of the survey
because it is the only architecture in this literature that has **ever** produced a quantitative
balance result — and it has **never needed a deficit**.

**The mechanism, extracted precisely.** Kahn–Saks (1984) get `3/11` from two ingredients, *both
non-strict*:

1. A pigeonhole/averaging fact — some incomparable pair has average-height gap `< 1`, i.e.
   `η(P) < 1`, where `η(P) := \min_{x ∥ y} |h(P,x) − h(P,y)|`. Purely combinatorial, no AF.
2. The **non-strict** log-concavity of `F(P,x,y,a) = \#\{f : f(y) − f(x) = a\}`.

The constant `3/11` comes from an **extremal optimization over log-concave sequences subject to a
mean constraint** — never from strictness. Aires–Kahn make the mechanism explicit in modern form
(arXiv:2509.11549, **Prop. 4.3**, VERBATIM as reported from full text this session): *"If `f` takes
values in the positive integers and is lc-distributed, then (a) `Ef ≤ 1/P(f = 1)`."* Their Lemma
5.2(b) chains this with Kahn–Saks log-concavity to get a pointwise probability lower bound.

**Brightwell–Felsner–Trotter's `(5−√5)/10 ≈ 0.2764` did not change this.** They added a *new
inequality* (the `a=b=1` case of the cross-product conjecture) to the same framework. Same
architecture, more inequalities, still no deficit.

> **Finding 4.1 (the strategic observation; CITED + PROVEN-by-inspection-of-the-literature).**
> *The entire quantitative 1/3–2/3 literature — Kahn–Saks `3/11`, Kahn–Linial `1/2e`,
> Brightwell–Felsner–Trotter `(5−√5)/10`, Aires–Kahn — extracts its numbers from **non-strict**
> log-concavity combined with a **mean or centroid constraint**. **Not one of them has ever used, or
> needed, a strictness or deficit in Stanley's inequality.** The arc's residual is therefore aimed at
> a tool the field has repeatedly and successfully bypassed.*

**What this suggests concretely.** `Ef ≤ 1/P(f=1)` is a genuine *quantitative* consequence of
*non-strict* log-concavity. The analogous device for our object is: for a discrete log-concave law,
the variance is controlled by the reciprocal-squared **mode mass**. Applied to the position law
`p_i(x) = N_i(x)/e(P)`, this would convert the variance half of (B) (§5) into a statement about
`\max_i p_i(x)` — a **mode-mass** statement, requiring no deficit at all.

> **Route (iv-a) [RECOMMENDED for further scoping, see §7]: replace "deficit stability" with
> "mode-mass anti-concentration".** Target shape: under (H), `\max_i N_i(x)/e(P) ≥ c` for every `x`,
> or a summed version. Uses Stanley's inequality **as-is**, in the proven Kahn–Saks style.
>
> **Honest status.** The step "discrete log-concave ⟹ `Var ≍ (\max_i p_i)^{-2}`" is standard
> folklore for log-concave laws on `ℤ` (the `≤` direction is what is needed), but **I did not locate
> and read a citable reference for the discrete case this session**, and I do **not** assert it.
> Labelled **CITED-AS-FOLKLORE / NEEDS-A-REFERENCE** in §9. It is a half-hour library task, not
> research, and it gates whether (iv-a) is real.

### 4.5 Other routes considered and dismissed in one line each

- **Strengthen to the Kahn–Saks inequality (`k=2`-flavoured) instead of Stanley.** Dismissed: the
  complexity barrier *does* bite at `k ≥ 2` in Chan–Pak's indexing (§6), and the equality theory is
  correspondingly worse, not better.
- **Use the order-polynomial deficit (Chan–Pak–Panova Thm 4.8 / Daykin–Daykin–Paterson) and
  transfer to `N_i`.** Dismissed: no transfer map exists — `Ω(P,t)` in `t` and `N_i` in `i` are
  different sequences — and the rate `(t+1)^{-(n+1)}` is exponentially below the §2.2 ruler even if
  one did.
- **Restrict to width 3 and use the width-two injective `q`-Stanley technology.** Not dismissed, but
  **out of scope for L1b**: `STATE.md` is explicit that this program is any-width and that width-3 is
  "old-repo baggage". Recorded as the one genuinely open frontier in route (iii) (the survey does not
  report width-3 as attempted), for whoever wants the width-3 paper rather than L1b.
- **Sharpen mg-48ab's Prop. 5.3 off the `π → 1` hypothesis** (mg-48ab §9 vector 3). Still live, still
  an exact-flatness statement, and therefore still on the wrong side of the `=`-vs-`>` line. Does not
  address the residual.

---

## 5. DELIVERABLE 2 — the right object

The ticket asks: does L1b need a rate on the **absolute-position** sequence `N_i` or on the **`ρ_s`
gap** sequence, and does a theorem on the former transfer to the latter? mg-48ab Finding 6.1 posed
this as "object mismatch" and suspected it was the real difficulty. **The answer is that neither is
the right object, and the correct one is visible from an elementary decomposition nobody in the arc
has written down.**

### 5.1 The decomposition

Recall (B): `E[Σ_x \operatorname{disp}_σ(x)²] = O(E[\operatorname{inv}_e])`, with
`\operatorname{disp}_σ(x) = \operatorname{pos}_σ(x) − \operatorname{rank}_e(x)`. Write
`h(x) := E[\operatorname{pos}_σ(x)]`. Then by `E[(A−c)²] = \operatorname{Var}(A) + (E[A]−c)²`:

> **Identity 5.1 (PROVEN, trivial, apparently unrecorded in the arc).**
> $$E\Big[\sum_x \operatorname{disp}_σ(x)^2\Big]
>  \;=\; \underbrace{\sum_x \operatorname{Var}\big(\operatorname{pos}_σ(x)\big)}_{\textbf{variance part}}
>  \;+\; \underbrace{\sum_x \big(h(x) - \operatorname{rank}_e(x)\big)^2}_{\textbf{bias part}} .$$

**This is a strictly different decomposition from (GID)** (`Σ disp² = 2ΣK_m + 2ΣM_{k,l}`), which is
a pointwise permutation identity; Identity 5.1 is probabilistic. They are complementary, and 5.1 is
the one that exposes the Stanley content, because `\operatorname{Var}(\operatorname{pos}_σ(x))` is
**exactly the variance of the absolute-position law `N_·(x)`** — the object Stanley/Ma–Shenfeld
governs, and the *only* object any `k=1` theorem can ever touch.

### 5.2 The variance part splits again, and its diagonal is free

Write `\operatorname{pos}_σ(x) = Σ_{y≠x} \mathbf 1[y ≺_σ x]` (0-indexed) and `p_{yx} := Pr[y ≺_σ x]`.
Then

$$\operatorname{Var}(\operatorname{pos}_σ(x)) \;=\; \underbrace{\sum_{y} p_{yx}(1-p_{yx})}_{\text{diagonal}}
\;+\; \underbrace{\sum_{y \ne y'} \operatorname{Cov}\big(\mathbf 1[y≺_σ x],\, \mathbf 1[y'≺_σ x]\big)}_{\text{covariance}} .$$

Comparable `y` contribute `0` to the diagonal. For `y ∥ x`, hypothesis (H) says exactly one of
`p_{yx}, 1−p_{yx}` is `< 1/3` — and it is precisely the **inversion probability** `m_{xy}` of the
pair `\{x,y\}` against `e`. Since the other factor lies in `(2/3, 1]`,

$$\tfrac23\, m_{xy} \;<\; p_{yx}(1-p_{yx}) \;\le\; m_{xy}.$$

Summing over `x` counts each incomparable pair twice, and `E[\operatorname{inv}_e] = Σ_{\{x,y\}} m_{xy}`:

> **Proposition 5.2 (PROVEN, new, elementary).** *Under (H),*
> $$\tfrac43\,E[\operatorname{inv}_e] \;<\; \sum_x \sum_{y} p_{yx}(1-p_{yx}) \;\le\; 2\,E[\operatorname{inv}_e].$$
> ***The diagonal of the variance part is `Θ(E[\operatorname{inv}_e])` for free, with explicit
> absolute constants `[4/3, 2]`.***

### 5.3 The consequence — where the difficulty actually lives

> **Finding 5.3 (the answer to deliverable 2; PROVEN, new).**
> *Under (H), combining Identity 5.1 and Prop. 5.2, **(B) is equivalent to***
> $$\underbrace{\sum_x \sum_{y \ne y'} \operatorname{Cov}\big(\mathbf 1[y≺_σ x],\,\mathbf 1[y'≺_σ x]\big)}_{\textbf{(B-cov)}}
> \;+\; \underbrace{\sum_x \big(h(x)-\operatorname{rank}_e(x)\big)^2}_{\textbf{(B-bias)}}
> \;=\; O\big(E[\operatorname{inv}_e]\big).$$
> *So:*
> - ***The Stanley-governed object is `\operatorname{Var}(\operatorname{pos}_σ(x))`** — neither the
>   deficit `N_i² − N_{i−1}N_{i+1}` nor the `ρ_s` gap law. The deficit is only ever a *device* for
>   bounding that variance, via §2.1's ratio propagation.*
> - ***A `k=1` stability theorem could only ever have addressed (B-cov)**, and only at absolute rate:
>   a per-element ratio bound `θ ≤ 1−c` gives `\operatorname{Var}(\operatorname{pos}_σ(x)) = O(c^{-2})`
>   hence `Σ_x \operatorname{Var} = O(n)`. At rate `Θ(1/n)` (Finding 3.1's ceiling) the window can
>   stay flat over `Θ(n)` indices and `Σ_x \operatorname{Var}` reaches `Θ(n³)`. **The gap between
>   "usable" and "achievable" is `n³` vs `n`.***
> - ***(B-bias) has NO Stanley content whatsoever** and is a previously-unnamed obligation. It is not
>   addressed by mg-48ab, by any stability theorem, or by the `ρ_s` route.*

**Sanity check on Identity 5.1 (by hand, no computation).** For `P` an `n`-antichain: `h(x) = (n−1)/2`
for all `x`, so (B-bias) `= Σ_x ((n−1)/2 − x)² = Θ(n³)` while `E[\operatorname{inv}_e] = Θ(n²)` — so
(B) fails, correctly, since the antichain has `δ = 1/2` and is not frozen. ✔ The identity behaves as
it must.

### 5.4 A free consequence: a sufficient condition for the bias half

Under (H), `h(x) = \#\{y <_P x\} + Σ_{y ∥ x} p_{yx}`, and since each incomparable pair is
`>2/3`-decided along `e`, `|h(x) − \operatorname{rank}_e(x)| ≤ Σ_{y ∥ x} m_{xy} =: M_x`, the
**per-element inversion mass**. Then `Σ_x M_x² ≤ (\max_x M_x)·Σ_x M_x = (\max_x M_x)·2E[\operatorname{inv}_e]`, so:

> **Proposition 5.4 (PROVEN, new, elementary).** *Under (H), if*
> `\max_x Σ_{y ∥ x} Pr[\{x,y\} \text{ inverts against } e] = O(1)`, *then* **(B-bias)**
> `= O(E[\operatorname{inv}_e])`, *and (B) reduces to (B-cov) alone.*

This is a clean, self-contained, previously-unnamed sub-lemma, it needs no Stanley input, and it is
in the `η(P)`-flavoured family of quantities Kahn–Saks already work with. It is my recommended first
lemma (§7).

### 5.5 Resolving mg-48ab Finding 6.1 (the object mismatch) explicitly

- **Does a stability theorem on `N_i` transfer to the `ρ_s` gap law?** **No, and for a reason
  stronger than "different objects".** The `ρ_s` route's propagation mechanism *requires*
  log-concavity of the gap sequence to turn a one-index drop into geometric decay (§2.1), and
  `e(P_m)`-log-concavity is **numerically false** (mg-2acf, `STATE.md`). So on the `ρ_s` object the
  propagation step is unavailable *even if a drop were supplied*. **The `ρ_s` route is strictly
  worse off than the `N_i` route, not merely different.** *(The falsity is CITED from
  `STATE.md`/mg-2acf and was not re-verified here — the ticket forbids computation.)*
- **A cheap, high-value check I recommend but did not run.** `q_s = Pr[c_s ≺_σ x] = Σ_{m ≥ s} a_m` is
  the **tail sum** of the gap law `a_m`. Tail sums of a log-concave sequence are log-concave — but
  `a_m` is not log-concave, so nothing follows either way. **Is the tail sequence `q_s` log-concave
  even though `a_m` is not?** If yes, the `ρ_s` are automatically non-increasing and the propagation
  mechanism is restored on the arc's primary object. This is a small enumeration, it is directly
  decisive for whether the `ρ_s` route has a propagation step at all, and to my reading of the arc
  docs **it has never been asked**. Recommended as a separate ticket. *(CONJECTURAL — I ran nothing.)*
- **Which object does L1b actually need?** Per Finding 5.3: **neither**; it needs (B-cov) and
  (B-bias). The `N_i` route is the better *proxy* of the two, because it at least has a working
  propagation mechanism (Stanley) and it directly bounds `\operatorname{Var}(\operatorname{pos}_σ(x))`.

---

## 6. DELIVERABLE 3 — the complexity barrier: is `k=1` genuinely exempt?

### 6.1 The indexing trap (must be stated before anything else)

**Chan–Pak's `k` and Ma–Shenfeld's `k` differ by one.** Ma–Shenfeld's `k` counts the elements of the
pinned chain `x_1 < ⋯ < x_k`; Chan–Pak's subscript on `EqualityStanley_k` counts the **additional**
pinned elements beyond the marked `x`. **Our case — the classical log-concavity of the position
sequence — is `k_{MS} = 1 = k_{CP} + 1`, i.e. `k_{CP} = 0`.** Every statement below is tagged with
its source's own indexing. mg-48ab §6.2's remark that "Chan–Pak [6, Thm 1.3] ... `k ≥ 3`" is
therefore **off by one relative to Chan–Pak's own numbering** (the threshold is `k_{CP} ≥ 2`, i.e.
`k_{MS} ≥ 3` — so mg-48ab's *conclusion* is right in MS indexing; only the attribution of the
indexing is loose). Flagged, not a substantive error.

### 6.2 The actual results

| predicate on the position sequence, at `k_CP = 0` (= our `k_MS = 1`) | status |
|---|---|
| Stanley equality `N_a² =? N_{a+1}N_{a−1}` | **in P** (Shenfeld–van Handel Thm 15.3(d) is poly-time checkable) |
| flat window `N_{a−1} = N_a = N_{a+1}` | **in P** (corollary of `(2)⇔(3)` in the same theorem) |
| adjacent equality `N_a =? N_{a+1}` | **not in PH** unless PH collapses |
| unique mode of `\{N(P,x,a)\}` | **not in PH** unless PH collapses |
| defect `N_a² − N_{a+1}N_{a−1} ∈ #P`? | **OPEN**, conjectured **NO** (Pak Conj. 6.3 / survey Conj. 9.2) |

And at higher `k`: `EqualityStanley_1 ∈ P` (Chan–Pak **Thm 1.4**); `EqualityStanley_k` **not in PH**
for `k_{CP} ≥ 2` (Chan–Pak **Thm 1.3**); `φ_k ∉ #P` unless `PH = Σ₂^p` for `k_{CP} ≥ 2` (Chan–Pak
**Cor. 1.5**) — with `k_{CP}=0` **explicitly excluded**, VERBATIM: *"The case `k = 0`, whether
`φ_0 ∈ #P`, is especially interesting and remains a challenging open problem."*

### 6.3 The answer, with the correction the ticket's non-triviality bar demands

> **Finding 6.1 (deliverable 3).**
> ***Yes, `k=1` is genuinely exempt from the proved complexity barrier*** *— the not-in-PH theorem
> starts at `k_{CP} ≥ 2` and explicitly excludes `k_{CP} = 0`, and the `k=1` equality problem is in
> P. **But the exemption buys nothing**, for two reasons:*
>
> 1. ***The obstruction to a `k=1` deficit bound is not complexity — it is Finding 3.1.*** *The
>    theorem is false at the needed strength, which no complexity result was ever going to tell us.*
> 2. ***The conjecture that does aim at `k=1` (Conj. 9.2, defect `∉ #P`) does not obstruct a
>    stability inequality either.*** *"Not in `#P`" means "no exact combinatorial interpretation".
>    A stability theorem asserts `defect ≥ Ψ` with `Ψ ∈ #P`, which is **consistent** with
>    `defect ∉ #P`. **Both independent literature passes I ran this session slid from "defect not in
>    #P" to "no combinatorial lower bound", and that is a logical overreach.** What Conj. 9.2
>    genuinely obstructs is a **direct injective proof** — Chan–Pak say exactly that: *"Corollary 1.5
>    implies that the Stanley inequality (Sta) most likely cannot be proved by a direct injection."*
>
> *So the correct scoping statement is: **the complexity literature neither blocks nor helps the
> `k=1` stability target. It is a red herring for this residual.** The block is elementary and lives
> in §3.*

**One genuine warning the complexity side does deliver, and it touches mg-48ab directly.** At
`k_{CP}=0`, **triple** flatness is in P but **adjacent-pair** equality `N_a = N_{a+1}` is not in PH,
and locating the mode is not in PH. mg-48ab's Window Rigidity chain reasons about flat *runs*, i.e.
triples — the tractable side. **If any future step weakens a triple-equality to a pair-equality, or
routes through mode identification, it lands in a not-in-PH predicate.** That is not fatal to an
analytic argument, but it means no poly-time-checkable certificate can exist for that step, so it
cannot be the hinge of a decision-procedure-shaped lemma. **Recorded as a design constraint on any
future rigidity argument.** *(HEURISTIC as applied to mg-48ab — I did not re-audit mg-48ab's chain
against it; Theorem 5.2's proof as written uses triples throughout, so I see no present violation.)*

---

## 7. DELIVERABLE 4 — recommendation

### 7.1 The honest headline

**Block-and-report on the named residual.** *The obstruction is:* **the `k=1` quantitative stability
theorem for Stanley's inequality, at the strength L1b requires (`γ = Θ(1)`, §2.2), is FALSE, refuted
by `C_n ⊔ C_n` at `Φ = 1/2` with deficit `1 + 1/(2n−1)` (Finding 3.1).** No route in §4 can deliver
it, and the reason is not that the routes are weak but that the target does not exist. mg-48ab's
Finding 6.2 should be **retired as a residual** and replaced by Finding 3.2's frozen-conditional
restatement — which is `STATE.md`'s "single lemma to prove", i.e. the wall itself.

### 7.2 The single most-promising forward route, if one is wanted anyway

**Not a stability theorem. Route (iv-a) + Prop. 5.4, in the Kahn–Saks architecture.** The case for
it: it is the only architecture that has ever produced quantitative balance numbers (Finding 4.1); it
consumes Stanley's inequality **non-strictly**, so Finding 3.1 does not price it; and §5 shows it
addresses (B) in the coordinates where the difficulty actually is.

**The concrete first lemma to try, in dependency order:**

1. **[Cheapest, highest information/cost ratio — a library task, not research.]** Find and pin a
   citable reference for *"for a log-concave law `p` on `ℤ`, `\operatorname{Var} = O((\max_i p_i)^{-2})`"*.
   This single fact gates whether route (iv-a) is real. Half a session.
2. **[The recommended first lemma.]** **Prop. 5.4's hypothesis:** under (H),
   $$\max_x \sum_{y \,\|\, x} \Pr\big[\{x,y\}\text{ inverts against } e\big] \;=\; O(1).$$
   Proving this closes **(B-bias)** outright (Prop. 5.4, already proven here) and reduces (B) to
   (B-cov) alone. It is self-contained, needs no Stanley input, no AF, no atlas, and no stability
   theorem. It is in the same family as Kahn–Saks's `η(P) < 1`. **This is the recommendation.**
3. **[The residual after step 2.]** **(B-cov)**: `Σ_x Σ_{y≠y'} \operatorname{Cov}(\mathbf 1[y≺x], \mathbf 1[y'≺x]) = O(E[\operatorname{inv}_e])`.
   **Warning, and it is the honest one:** `CoreLemma-forDaniel.md` §5 records that FKG and XYZ force
   exactly these same-side covariances to be **non-negative** — wrong-signed for an upper bound. So
   §5's decomposition **lands on the arc's known wall**, which is a correctness check on §5 and a
   caution against expecting (B-cov) to be easy. It does, however, state the wall in the sharpest and
   most elementary coordinates the arc has had.
4. **[Separate small ticket, decisive either way.]** §5.5's question: **is the tail sequence
   `q_s = Σ_{m≥s} a_m` log-concave even though `a_m` is not?** A small enumeration. If yes, the
   `ρ_s` route regains a propagation mechanism; if no, the `ρ_s` route should be retired in favour of
   the `N_i`/variance coordinates of §5.

### 7.3 What NOT to do

- **Do not commission a `k=1` Stanley stability tool-build** (mg-48ab §9 vector 1). Finding 3.1
  prices it out; it would be a multi-month effort against a false statement.
- **Do not pursue route (i).** Four independent walls, the deepest of which (no compact resolvent,
  hence no spectral gap) is an in-principle obstruction stated by the authors.
- **Do not read "defect not in `#P`" as closing route (iii)**, and do not repeat that inference into
  `STATE.md` — it is an overreach (§6.3).
- **Do not re-run the AF-stability literature search.** It was run properly this session across four
  independent passes with full-text extraction on the primary sources; the negative result is solid
  and is recorded with access levels in §8.

---

## 8. Citation ledger — what was actually read, at what access level

Per the ticket's explicit anti-misattribution instruction (the mg-a1ec Aires–Kahn incident), every
source below carries its access level. **Nothing is quoted from a PDF that was not opened.**

| source | id / venue | access this session | used for |
|---|---|---|---|
| Shenfeld–van Handel, *Extremals of the AF inequality for convex polytopes* | arXiv:2011.04059 v2; Acta Math. **231** (2023) 89–204 | **FULL TEXT extracted**; §15 and §16 read; `stabilit`/`quantitativ` grep = 0 hits | §4.1 wall 1; §4.3 (the `d⟹c⟹b⟹a` injection); §6.2 (Thm 15.3) |
| Shenfeld–van Handel, *Extremals of Minkowski's quadratic inequality* | arXiv:1902.10029; Duke Math. J. **171** (2022) 957–1027 | **FULL TEXT extracted**; Thm 6.1 and Remark 7.2 verbatim | §4.1 walls 2–3 — **the deepest obstruction in this document** |
| Chan–Pak, *Equality cases of AF are not in PH* | arXiv:2309.05764; Forum Math. Pi **12** (2024) e21; STOC 2024 | **read** (HTML + verbatim extraction of Thms 1.1/1.3/1.4, Cors 1.2/1.5 incl. the `k=0` exclusion) | §4.1 wall 4; §6 |
| Chan–Pak, *Linear extensions of finite posets* (survey) | arXiv:2311.02743; EMS Surv. Math. Sci. | **FULL TEXT extracted** | §3.3 (Aires–Kahn footnote), §4.3, §4.4, §6 |
| Chan–Pak, *Log-concave poset inequalities* (the atlas) | arXiv:2110.10740 | **arXiv source read**; §5.2, Thm 5.2, Lemma 5.3, Lemma 7.2, Thm 1.39, §16.11 verbatim | §4.2 (whole section) |
| Chan–Pak–Panova, *Effective poset inequalities* | arXiv:2205.02798; SIAM J. Discrete Math. **37** (2023) 1842–1880 | **partial** (abstract + targeted full-text fetches; some truncation) | §4.3 (Thm 4.8's rate + the FKG-not-injection fact) |
| Chan–Pak, *Introduction to the combinatorial atlas* | arXiv:2203.01533; Expo. Math. **40** (2022) 1014–1048 | **source read** (definitions only) | §4.2 definitions |
| Pak, *What is a combinatorial interpretation?* | arXiv:2209.06142 | **second-hand** (via the survey's restatement as Conj. 9.2) | §4.3, §6.2 — **Conj. 6.3 quoted only as the survey states it** |
| Ma–Shenfeld, *Extremals of Stanley's inequalities for posets* | arXiv:2211.14252; Adv. Math. **436** (2024) | **read in mg-48ab's session, not re-read here**; consumed via mg-48ab §2 | §2.1, §6.1 indexing |
| Chan–Pak–Panova, width-two `q`-Stanley / `q`-KS | via survey Thms 9.4, 9.5 ([CPP23a, Thms 7.1, 7.2]) | **ABSTRACT-ONLY** for the primary; the survey's statement read | §4.3 item 4 |
| Aires–Kahn, *Balancing extensions in posets of large width* | arXiv:2509.11549 | **read this session** (Prop. 4.3, Lemma 5.2(b), Thm 4.1) | §4.4 — **and note: per the ticket, nothing from the mg-a1ec §7 misattributed step is used** |
| Schneider (1990), Martínez-Maure (2017) — AF stability under regularity | manuscripta math.; Monatsh. Math. **182** 65–76 | **ABSTRACT-ONLY** | §4.1 wall 1 — cited only for their *hypotheses*, no theorem quoted |
| Brightwell–Winkler, `#P`-completeness of `e(P)` | *Order* **8** (1991) | **NOT ACCESSED** | not relied on; page range flagged as unverified |

**Citation hygiene notes carried forward.**
(a) The **`k`-indexing collision** (§6.1) is the single likeliest source of a future misattribution
in this arc — Chan–Pak's `k=0` is Ma–Shenfeld's `k=1`.
(b) **arXiv:2309.05764 has no Panova**; she is a coauthor on 2205.02798 and 2110.10740.
(c) **Theorem numbering is version-dependent** in Ma–Shenfeld and in the Chan–Pak survey. Pin
versions when citing.
(d) **"Effective" in *Effective poset inequalities* does not mean "quantitative rate"** — it means
injective proofs putting a defect in `#P`. mg-48ab and any future ticket should not read that title
as promising a deficit bound.

---

## 9. Status table — proven / cited / conjectured / heuristic, line by line

| § | statement | status |
|---|---|---|
| 2.1 | ratio propagation: one strict drop + Stanley ⟹ geometric decay | **PROVEN** (immediate from log-concavity); mechanism CITED from mg-a1ec Prop. 5.2 |
| 2.2 | rate accounting: `γ = Θ(1)` needed; `Θ(1/n)` is a non-result | **PROVEN**, elementary, new |
| 2.3 | no `Φ`-free uniform bound (equality case exists) | **PROVEN**, trivial |
| 3.1 | `N_{1+j} = \binom{n-j+m-1}{m-1}` for `C_m ⊔ C_n` | **PROVEN**, exact; Vandermonde check ✔ |
| 3.1 | deficit `= 1 + (m−1)/(a(a+m))`; `Φ_i = (m−1)/(m−1+a)` | **PROVEN**, exact algebra |
| 3.2 | **Finding 3.1** — `Φ = 1/2`, deficit `= 1 + 1/(2n−1)`; the named target is refuted | **PROVEN**, new; hand-verified at `n=2` by full enumeration of 6 extensions ✔ |
| 3.3 | `δ(C_n ⊔ C_n) = 1/2` — refutation is unconditional-only | **PROVEN** (chain-swap symmetry) |
| 3.3 | Aires–Kahn refuted CPP Conj. 9.18 on the same family | **CITED** (survey footnote, read this session); the primary is **not** relied on |
| 3.4 | **Finding 3.2** — the residual must consume (H); mg-48ab's reduction is circular | **PROVEN** modulo §2.2 |
| 4.1 | SvH Acta contains no stability; Duke Remark 7.2 (no compact resolvent) | **CITED VERBATIM** (full text extracted) |
| 4.1 | Chan–Pak Cor. 1.2 as pressure on route (i) | **CITED** for the theorem; **HEURISTIC** as applied to our `k=1` slice (Cor. 1.2 is about general TU-polytope AF) |
| 4.2 | atlas is a signature argument; no defect; `t→0,1` limit kills constants | **CITED** (source read) + **PROVEN-by-inspection** that no step carries a modulus |
| 4.2 | routes (i) and (ii) converge on the same missing spectral gap | **OBSERVATION**, new |
| 4.3 | Conj. 9.2 does **not** obstruct a stability *inequality* | **PROVEN** (logic: `#P`-membership vs. lower bound) — **corrects two literature summaries** |
| 4.3 | CPP order-polynomial rate `(t+1)^{-(n+1)}`, FKG-not-injection | **CITED** |
| 4.4 | **Finding 4.1** — the whole quantitative 1/3–2/3 literature bypasses deficits | **CITED**, cross-checked across Kahn–Saks, BFT, Kahn–Linial, Aires–Kahn |
| 4.4 | route (iv-a): `Var ≍ (\max p_i)^{-2}` for discrete log-concave | **CITED-AS-FOLKLORE / NEEDS-A-REFERENCE** — *not asserted*; gates (iv-a) |
| 5.1 | **Identity 5.1** — variance/bias split of the (B) quantity | **PROVEN**, trivial, new to the arc |
| 5.2 | **Prop. 5.2** — diagonal is in `[4/3, 2]·E[inv_e]` under (H) | **PROVEN**, new, elementary |
| 5.3 | **Finding 5.3** — (B) ⟺ (B-cov) + (B-bias); the right object is `\operatorname{Var}(\operatorname{pos})` | **PROVEN**, new |
| 5.4 | **Prop. 5.4** — per-element inversion mass `O(1)` ⟹ (B-bias) closes | **PROVEN**, new, elementary |
| 5.5 | `ρ_s` route lacks a propagation step (gap-law log-concavity false) | **CITED** (mg-2acf / `STATE.md`); not re-verified — no computation run |
| 5.5 | is the **tail** `q_s` log-concave though `a_m` is not? | **CONJECTURAL / OPEN** — recommended as a separate ticket; **nothing was run** |
| 6.1 | `k_{CP} = k_{MS} − 1`; mg-48ab's "`k≥3`" is right in MS indexing | **CITED**, verified against both sources |
| 6.2 | the four-row tractability table at `k_{CP}=0` | **CITED VERBATIM** from the survey + Chan–Pak |
| 6.3 | **Finding 6.1** — `k=1` is exempt, and the exemption buys nothing | **PROVEN** (combining the citations with §3) |
| 6.3 | pair-equality / mode-location are not-in-PH ⟹ design constraint on rigidity arguments | **CITED** for the complexity facts; **HEURISTIC** as applied to mg-48ab's chain |
| — | mg-48ab Theorem 5.2, Lemma 3.1, Cor. 3.2 | **UNTOUCHED** — nothing here contradicts them |
| — | L1b / (decay) / (B) | **STILL OPEN** — nothing here closes them |

**No computation was run.** No dataset, enumeration, script, or Lean file was produced. The only
arithmetic is the binomial algebra of §3.1–§3.2 and the six-extension check at `n=2`, both done by
hand in-line.

---

## 10. One line for the attempt index (for pm-onethird)

> `residual named → residual REFUTED` | **`k=1` Stanley stability scoping (mg-dcae)** |
> ***RED-for-the-residual / AMBER-with-redirect.*** The mg-48ab residual — a `k=1` quantitative
> stability theorem `N_i² ≥ (1+cΦ)N_{i−1}N_{i+1}` — is **FALSE at the strength L1b needs**, refuted
> by hand: for `P = C_n ⊔ C_n`, `x = \min` of one chain, at `i=2` the natural `Φ` (fraction of `N^=`
> extensions with a comparable companion) is **exactly `1/2`** while the deficit is **exactly
> `1 + 1/(2n−1)`**; generally `deficit/Φ ∼ 1/n`. Exact formula `N_{1+j} = \binom{n-j+m-1}{m-1}`,
> deficit `= 1 + (m−1)/(a(a+m))`, `a = n−j`; verified at `n=2` by enumerating 6 extensions. **Rate
> accounting** (new): L1b needs `γ = Θ(1)`; `γ = Θ(1/n)` lets the position law stay flat over `Θ(n)`
> indices, giving `Σ_x Var = Θ(n³)` vs the `O(n)` needed — a non-result, not a weak result.
> **Consequence: any usable statement must consume (H), so the residual is NOT a Stanley theorem but
> a frozen-conditional anti-concentration theorem = `STATE.md`'s "single lemma to prove". mg-48ab's
> reduction is confirmed CIRCULAR** (STATE.md's own "relabeling, not a reduction" reading upgraded
> from suspicion to proof). **Route survey:** (i) AF-stability **DEAD** on four independent walls,
> deepest being Shenfeld–van Handel Duke Remark 7.2 — stability ⟺ kernel + spectral gap, and the
> operator has **no compact resolvent**, so "characterization ⟹ stability" fails *in principle*;
> existing AF stability (Schneider 1990, Martínez-Maure 2017) needs `C²₊` full-dimensional bodies,
> excluding order polytopes; Chan–Pak Cor. 1.2 obstructs poly-computable Bonnesen `ξ` on
> TU-polytopes *and is built from order polytopes*. (ii) combinatorial atlas **AMBER-but-priced-out**
> — the atlas proof is a *signature* argument ("at most one positive eigenvalue"), carries no
> modulus, and a `t→0,1` limit kills any constant; repairing it reduces to the **same spectral-gap
> object as (i)** — the two routes converge. (iii) direct injective **AMBER on provability, DEAD on
> price**; **important correction: Conj. 9.2 ("Stanley defect not in `#P`") does NOT kill it** —
> "not in `#P`" forbids an exact combinatorial *interpretation*, not an *inequality* `defect ≥ Ψ`;
> two independent literature passes made this overreach and it should not enter STATE.md. (iv)
> **Kahn–Saks architecture — the only one that has ever produced quantitative balance numbers
> (3/11, 1/2e, (5−√5)/10, Aires–Kahn) and it has NEVER used a deficit**; it runs on *non-strict*
> log-concavity + a mean constraint, so Finding 3.1 does not price it. **Object question (mg-48ab
> Finding 6.1) resolved, and sharper than "`N_i` vs `ρ_s`":** new elementary identity
> `E[Σ disp²] = Σ_x Var(pos(x)) + Σ_x (h(x) − rank_e(x))²`, and under (H) the *diagonal* of the
> variance part is `Θ(E[inv_e])` **free with explicit constants `[4/3,2]`**; hence **(B) ⟺ (B-cov) +
> (B-bias) = O(E[inv_e])**. So the Stanley-governed object is `Var(pos_σ(x))` — neither the deficit
> nor `ρ_s` — and **(B-bias) has no Stanley content at all** (a previously-unnamed obligation).
> New **Prop. 5.4**: `max_x Σ_{y∥x} Pr[{x,y} inverts] = O(1)` ⟹ (B-bias) closes outright. `ρ_s` is
> *strictly worse* than `N_i`: its propagation step needs gap-law log-concavity, which is false. **On
> the complexity barrier:** `k=1` **IS** genuinely exempt (Chan–Pak's not-in-PH starts at `k_CP ≥ 2`
> and Cor. 1.5 *explicitly excludes* `k_CP=0`; `EqualityStanley₀ ∈ P`) — **but the exemption buys
> nothing, because the block is elementary (§3), not complexity-theoretic**. Beware the `k`-indexing
> collision: Chan–Pak `k=0` = Ma–Shenfeld `k=1`. One design constraint delivered: at `k_CP=0`
> *triple* flatness is in P but *pair* equality and *mode location* are **not in PH**, so no rigidity
> step may weaken a triple to a pair. **Recommendation: retire mg-48ab Finding 6.2 as a residual;
> do NOT commission a Stanley stability tool-build; first lemma to try = Prop. 5.4's per-element
> inversion-mass bound `max_x Σ_{y∥x} Pr[invert] = O(1)`** (self-contained, no AF/atlas/stability
> input, closes (B-bias)), gated by one cheap library task (a citable discrete-log-concave
> `Var = O(p_max^{-2})`), plus one cheap separate ticket: **is the tail `q_s = Σ_{m≥s} a_m`
> log-concave even though `a_m` is not?** — decisive for whether the `ρ_s` route has any propagation
> step at all, and apparently never asked. **NO COMPUTATION RUN.**

---

*mg-dcae. Scoping deliverable: approach map + difficulties. No datasets generated, no enumerations
run, no Lean written, no scripts committed. Claims labelled per §9; source access levels per §8.
mg-48ab Theorem 5.2 is untouched and remains correct.*
