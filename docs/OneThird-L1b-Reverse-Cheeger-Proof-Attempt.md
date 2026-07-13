# OneThird L1b — Buser-type reverse Cheeger for width-3 pair cuts (bounded PROOF attempt)

**Work item:** `mg-7ae7` (high, repo `one_third_width_three`). Daniel full-speed GO,
gate lifted. LaTeX-first, prove-it-**or**-name-the-wall (block-and-report). Bounded
first proof-attempt of **L1b**, the sole surviving gap in the spectral / near-ordinal-sum
falsification chain after `mg-b0a6` (kill-shot, ALIVE), `mg-3ce3` (L4, GREEN),
`mg-8b64` (BK→transport transfer probe, AMBER/GREEN-in-regime).

---

## Verdict: **WALL — reduced to a single named correlation inequality (LIB).**

This attempt does **not** close L1b, but it is not an open grind either: it collapses the
whole transfer to one clean, precisely-stated obstruction and proves everything up to it.

**What is proved here (rigorous, no new hypotheses, numerically re-verified §8):**

1. **Transport Dirichlet identity** (§1). For every label function `f`,
   `⟨f,(I−S_P)f⟩ = ½·E_σ Σ_a (f(a) − f(σ(a)))²`, so `1 − λ_std` is a genuine
   variational (spectral-gap) quantity over label functions.
2. **Reverse-Cheeger reduction** (§2). For **every** label cut `A ⊆ [n]`,
   ```
   1 − λ_std(P)  ≤  n·leak(A) / (|A|·|Aᶜ|),      leak(A) := E_σ |A \ σ(A)|.
   ```
   Hence the *entire* Buser-type transfer reduces to producing **one balanced label cut
   with `O(1/γ)` expected leakage** (a thin interface). This is the easy/Buser direction of
   Cheeger done *exactly*, at the transport level — no √-slack, no spectral black box.
3. **Leak → displacement → inversions** (§3). Summing the reduction over threshold cuts
   in the distinguished order `e`,
   ```
   Σ_k leak({1..k}_e) = ½·E_σ Σ_x |σ⁻¹(x) − rank_e(x)|  ≤  E_σ[ inv_e(σ) ],
   ```
   an **exact identity** plus a clean bound. Averaging over balanced cuts gives
   `min_{balanced k} leak(k) ≤ 2·E[inv_e]/n`, so
   ```
   1 − λ_std(P)  ≤  O( E_σ[inv_e(σ)] / n² ).
   ```
   The target `1 − λ_std ≤ C/(γn)` therefore holds **iff** `E_σ[inv_e] = O(n/γ)`.
4. **Chain-monotonicity** (§4.1). Backward pair-probabilities decay monotonically along
   each of the 3 Dilworth chains — the only structural decay pairwise-freezing supplies.

**The wall (§4).** Everything rests on

> **LIB (Linear Inversion Bound).** For a width-3 indecomposable γ-counterexample `P`
> with distinguished order `e`, `E_σ[inv_e(σ)] = Σ_{x<_e y} Pr[y <_σ x] = O(n/γ)` —
> the expected number of `e`-inversions is **linear**, not quadratic, in `n`.

Pairwise freezing gives each backward probability `< 1/3`, hence only the **trivial
`O(n²)`** bound. The gap between `O(n²)` (marginals) and the needed `O(n)` (truth) is a
genuine **joint-law / correlation** statement, and §4.2 exhibits an abstract
all-pairs-frozen distribution with `Θ(n²)` inversions — so **LIB is false for abstract
frozen distributions and any proof must use that `L(P)` is the uniform measure on the
linear extensions of a real width-3 poset.** LIB is a poset-specific correlation
inequality, the same class of input as the BK-bad-mixing crux the Čech/F-series program
also stalls on (`project_cech_bias_program`).

**Dual reading, data-confirmed (§5).** The transfer L1b is *exactly* the statement
"**standard dominance holds for counterexamples**": the slow BK mode lives in the
standard (transport) sector. The `mg-8b64` data shows standard dominance **fails
off-regime** (the 166 refuters: BK gap ≈ 0.02 while transport gap ≈ 0.23 — the slow mode
is a non-standard, degree-≥2 pair mode invisible to the transport quotient) and **holds
in-regime** (δ→1/3: BK gap ≈ transport gap). All-pairs-frozen is precisely the hypothesis
that must force the slow mode into the standard sector — and LIB is the quantitative form
of that forcing.

**Skeptical bar honoured** (`feedback_empirical_green_is_not_proven`). §5's data is
evidence for *where the wall is*, not a proof. The rigorous content is §1–§4.1 and §8;
LIB is stated as an open obstruction, not asserted.

---

## 0. Setup and notation

`P` is a width-3 indecomposable **γ-counterexample** on `[n]`, `γ ∈ (0,1/3]`: every
incomparable pair `x ∥ y` has `p_xy := Pr_σ[x <_σ y] ∈ [γ,1/3) ∪ (2/3,1−γ]`, where `σ`
is a uniform linear extension of `P`, written as a bijection `[n]→[n]`, `σ(a)` = element
at position `a`, `σ⁻¹(x)` = position of element `x`. Equivalently `δ(P) := max_{x∥y}
min(p_xy,1−p_xy) < 1/3` (every pair frozen).

**Distinguished order `e`** (kill-shot 1, `mg-b0a6`, GREEN/well-stressed): a linear
extension of `P` consistent with every `>2/3`-strong majority orientation; relabel so
`e = (1,2,…,n)`, i.e. `rank_e(x)=x`. For an incomparable pair `i<_e j` we then have
`p_ij = Pr[i<_σ j] > 2/3`, so the **backward probability** `Pr[j<_σ i] = 1−p_ij < 1/3`.
Comparable pairs contribute `0`. (Existence of `e` for a *true* counterexample is itself
the kill-shot-1 assumption — GREEN but unproven; flagged as a secondary input.)

**Transport quotient** (`mg-b0a6` §Method). `(T_P)_{x,a} = Pr_σ[σ(a)=x]` (doubly
stochastic `n×n`); `S_P = (T_P + T_Pᵀ)/2` on `H = 1⊥`; `λ_std(P)` = top eigenvalue of
`S_P` on `H`. `λ_std = 1` iff `P` is an ordinal sum; the **transport gap** is
`1 − λ_std ≥ 0`. `I − S_P ⪰ 0` (since `S_P` symmetric doubly stochastic has spectrum in
`[−1,1]`, top eigenvalue `1` on the constants), so

```
1 − λ_std(P)  =  min_{f ⊥ 1, f≠0}  ⟨f,(I−S_P)f⟩ / ‖f‖² .        (0.1)
```

Here `f: [n] → ℝ` is a **label** function, `‖f‖² = Σ_x f(x)²`, `⟨·,·⟩` the standard inner
product on `ℝ^n`.

**BK side (proven input, Theorem E, `step8.tex`).** `lem:frozen-pair-existence` +
`lem:dirichlet-conductance` give an incomparable pair `(x*,y*)` with BK Dirichlet ratio
`E_BK(f_{x*y*})/Var(f_{x*y*}) ≤ 2/(γn)` and a cut `S_{x*y*}` of BK conductance
`Φ ≤ 2/(γn) =: η(γ,n)`. This is the *combinatorial* low-conductance input we try to
transfer to (0.1).

---

## 1. The transport Dirichlet identity (proved)

**Lemma 1.** For every `f: [n] → ℝ`,
```
⟨f,(I−S_P)f⟩  =  ½ · E_σ Σ_{a=1}^n ( f(a) − f(σ(a)) )² .            (1.1)
```
In particular the RHS is `≥ 0` and equals `0` iff `f` is `σ`-a.s. constant on the support
of the transport walk.

*Proof.* Since the quadratic form uses `S_P = (T_P+T_Pᵀ)/2` and the double sum is
symmetric, `⟨f,S_P f⟩ = Σ_{x,a}(T_P)_{x,a} f(x)f(a) = Σ_{x,a} Pr[σ(a)=x] f(x) f(a) =
E_σ Σ_a f(a) f(σ(a))`. Because `σ` is a bijection, `E_σ Σ_a f(σ(a))² = Σ_x f(x)² = ‖f‖²`.
Hence
```
E_σ Σ_a (f(a) − f(σ(a)))²  =  ‖f‖² − 2⟨f,S_P f⟩ + ‖f‖²  =  2⟨f,(I−S_P)f⟩ .   ∎
```

**Interpretation.** Read `σ` as arranging labels along positions; `a ↦ f(a)` is the
value carried by the *reference* arrangement `e = id` at position `a`, and `a ↦ f(σ(a))`
the value carried by `σ`. So `1 − λ_std` measures, in `L²`, how far the label-values are
displaced from the reference `e`. Combined with (0.1): the transport gap is small iff
some mean-zero label test function is nearly `σ`-invariant relative to `e`.

**Leakage.** For a set `A ⊆ [n]` put `leak(A) := E_σ|A \ σ(A)|` where `σ(A) =
{σ(a):a∈A}`. Taking `f = 1_A`, (1.1) gives `⟨1_A,(I−S_P)1_A⟩ = leak(A)` (positions in `A`
holding a label outside `A`; equivalently, by bijection, labels of `A` sitting outside the
`A`-positions).

---

## 2. The reverse-Cheeger reduction (proved)

**Proposition 2 (Buser/easy direction, exact, transport level).** For every `A ⊆ [n]`
with `0 < |A| < n`,
```
1 − λ_std(P)  ≤  n · leak(A) / ( |A| · |Aᶜ| ) .                    (2.1)
```
Consequently, if there is a **balanced** label cut (`|A|,|Aᶜ| ≥ cn`) with
`leak(A) = O(1/γ)`, then `1 − λ_std = O(1/(γn))`.

*Proof.* Take `f = 1_A − (|A|/n)·1`, so `f ⊥ 1`. Because `(I−S_P)1 = 0` (row sums of
`S_P` are `1`), `⟨f,(I−S_P)f⟩ = ⟨1_A,(I−S_P)1_A⟩ = leak(A)` by Lemma 1. And
`‖f‖² = |A| − |A|²/n = |A||Aᶜ|/n`. Plug into (0.1). For balanced `A`,
`|A||Aᶜ| ≥ c(1−c)n²`, and `leak(A) = O(1/γ)` gives RHS `= O(1/(γn))`. ∎

This is the crux simplification. **To upper-bound the min in (0.1) it suffices to
exhibit one good cut** — the classical Buser inequality (low-conductance set ⇒ small
spectral gap), here at the level of the `n`-state transport quotient, with no √-loss and
no appeal to the BK spectrum. The Cheeger √-slack flagged in the cuts-by-pairs scoping
(`compatibility-geometry-cuts-by-pairs-scoping.md` §5.1–5.2) simply does **not arise**:
the transport quotient is the object whose gap we want, and a set of low leakage bounds
that gap *linearly* by (2.1). The scoping doc's "missing Buser-type modulus" is supplied,
in closed form, by (2.1). **The whole difficulty is now purely: does a thin balanced cut
exist?**

`leak(A)` is exactly `mg-b0a6`'s interface-leakage `⟨1_A,(I−S_P)1_A⟩ = E_σ|A∖σ(A)|`;
`leak(A) = O(1/γ)` at a balanced cut is `Δ₁(A) = leak(A)/min(|A|,|Aᶜ|) = O(1/(γn)) → 0`,
i.e. a **thin interface** in the near-ordinal-sum sense.

---

## 3. Reducing the thin cut to a linear inversion bound (proved)

Fix the distinguished order `e` and use **threshold cuts** `A_k := {1,…,k}` (labels of
`e`-rank `≤ k`).

**Lemma 3.1 (leakage ≤ backward straddle mass).** `leak(A_k) ≤ Σ_{i≤k<j} Pr[j <_σ i]`,
the sum over incomparable straddling pairs of the backward probability.

*Proof.* `leak(A_k) = Σ_{x≤k} Pr[σ⁻¹(x) > k]`. If a low label `x ≤ k` occupies a
high position `> k`, then `≥ k` labels precede it, of which at most `k−1` are low, so at
least one **high** label `j > k` has `j <_σ x`. Thus `Pr[σ⁻¹(x)>k] ≤ Σ_{j>k} Pr[j<_σ x]`;
comparable straddling pairs have `Pr = 0` (with `i<_e j`, `i` before `j` always if
comparable), leaving incomparable pairs. Sum over `x ≤ k`. ∎

**Lemma 3.2 (cut-sum = displacement, exact).**
```
Σ_{k=1}^{n-1} leak(A_k)  =  ½ · E_σ Σ_{x=1}^n | σ⁻¹(x) − rank_e(x) | .   (3.1)
```

*Proof.* `Σ_k leak(A_k) = Σ_k Σ_{x≤k} Pr[σ⁻¹(x)>k] = Σ_x Σ_{k≥ rank_e(x)}
Pr[σ⁻¹(x) > k] = Σ_x E_σ[(σ⁻¹(x) − rank_e(x))⁺]` (the count of integers `k` in
`[rank_e(x), σ⁻¹(x))`). Since Σ_x σ⁻¹(x) = Σ_x rank_e(x) = n(n+1)/2, total rightward
displacement = total leftward, so `Σ_x (σ⁻¹(x)−rank_e(x))⁺ = ½ Σ_x |σ⁻¹(x)−rank_e(x)|`.
Take `E_σ`. ∎ *(verified exactly, error `0.0`, §8.)*

**Lemma 3.3 (displacement ≤ 2·inversions).** `Σ_x |σ⁻¹(x) − rank_e(x)| ≤ 2·inv_e(σ)`,
where `inv_e(σ) = #{x<_e y : y<_σ x}`.

*Proof.* `σ⁻¹(x) − rank_e(x) = Σ_{y≠x}(1[y<_σ x] − 1[y<_e x]) = #{y >_e x: y<_σ x} −
#{y <_e x: x<_σ y}`, so `|σ⁻¹(x)−rank_e(x)| ≤ #{y : x,y inverted by σ vs e}`. Sum over
`x`; each inversion is counted twice. ∎ *(verified, §8.)*

**Proposition 3 (reduction to LIB).** With `E[inv_e] := E_σ[inv_e(σ)]`,
```
min_{balanced k} leak(A_k)  ≤  (2/n)·E[inv_e],     hence     1 − λ_std(P)  ≤  O( E[inv_e]/n² ).
```

*Proof.* Restrict (3.1)+3.3 to balanced `k ∈ [n/4, 3n/4]` (≥ n/2 values), each `leak ≥ 0`:
`min_{balanced} leak(A_k) ≤ (2/n)Σ_k leak(A_k) ≤ (2/n)·E[inv_e]`. Feed into Prop. 2 with
`|A_k||A_kᶜ| ≥ (3/16)n²`. ∎

So the target `1 − λ_std ≤ C/(γn)` is **equivalent to** `E[inv_e] = O(n/γ)` — the
**Linear Inversion Bound**.

---

## 4. The wall: the Linear Inversion Bound

> **LIB.** For a width-3 indecomposable γ-counterexample with distinguished order `e`,
> ```
> E_σ[ inv_e(σ) ]  =  Σ_{i <_e j,  i ∥ j} Pr[ j <_σ i ]  =  O(n/γ).
> ```

### 4.1 What freezing does give: chain monotonicity (proved)

By Dilworth, `P` is 3 chains `C₁,C₂,C₃`. Within a chain there are no inversions
(comparable). Across two chains:

**Lemma 4.1.** If `i ∈ C_a`, and `j,j' ∈ C_b` with `j <_P j'`, then
`Pr[j' <_σ i] ≤ Pr[j <_σ i]`. Likewise monotone in `i` along `C_a`.

*Proof.* `j <_P j' ⇒ j <_σ j'` always; so `{j' <_σ i} ⊆ {j <_σ i}`. ∎

Thus backward probabilities **decay** as one moves up a chain away from the cut — the
only decay pairwise-freezing supplies. It localizes inversions *within a chain pair* but
does **not** bound the total: `Σ_{j∈C_b} Pr[j<_σ i] = E[#{C_b-elements before i}]`, the
expected `C_b`-contribution to `rank_σ(i)`, can be as large as `Θ(n)` from monotone
marginals alone (a slowly-decaying tail).

### 4.2 Why marginals cannot suffice: LIB is false for abstract frozen laws

**Proposition 4 (marginals are insufficient).** There is a probability law `μ` on
interleavings of two length-`m` chains (`n = 2m`) in which **every** incomparable pair is
frozen at bias `> 2/3` toward a fixed reference order `e`, yet `E_μ[inv_e] = Θ(n²)`.

*Construction.* Let `e = u₁v₁u₂v₂⋯` (alternating) and `e' = v₁⋯v_m u₁⋯u_m` (all of `C_b`
before all of `C_a`), which inverts all `m²` cross pairs relative to `e`. Set
`μ = (2/3+ε)·δ_e + (1/3−ε)·δ_{e'}`. Every cross pair `(u_i,v_j)` is inverted only under
`e'`, so its backward probability is `1/3−ε < 1/3` (frozen), while
`E_μ[inv_e] = (1/3−ε)·m² = Θ(n²)`. ∎

Hence LIB **cannot** follow from the per-pair `< 1/3` bounds (nor from Lemma 4.1, which
`μ` also satisfies). Any proof must use a property that separates the **uniform measure on
all linear extensions of a genuine width-3 poset** from adversarial low-atom mixtures like
`μ`. Uniform-on-`L(P)` is highly spread (its support is an order polytope's lattice
points, not two atoms); LIB is a statement about that specific geometry — a **poset
correlation inequality**, not a soft averaging fact. This is exactly the flavour of the
BK-bad-mixing input the note (`spectral_near_ordinal_sum_program.tex`, and the PM review)
identifies as the shared crux with the Čech/F-series program: control of the **joint law**
of a random linear extension of a frozen width-3 poset, beyond its pairwise marginals.

### 4.3 Equivalent forms of the wall (all open)

The following are equivalent (up to the `O(·)` in Prop. 3 / Prop. 2) to LIB, and each is a
legitimate restatement of the obstruction:

- **Linear inversions:** `E[inv_e] = O(n/γ)`.
- **Bounded displacement:** `E_σ Σ_x |σ⁻¹(x) − x| = O(n/γ)` (average element moves `O(1/γ)`
  from its `e`-rank) — i.e. a random extension is `O(1/γ)`-rigid around `e` in `L¹`.
- **Thin balanced cut:** `∃` balanced `A` with `leak(A) = O(1/γ)`.
- **Standard dominance (quantitative):** the slowest BK mode has an `Ω(1)` component in
  the standard sector (§5).

None follows from Theorem E's single-cut output, and §4.2 shows none follows from the full
family of pairwise-frozen marginals.

---

## 5. Dual view: L1b = standard dominance, and it is *not* universal (data-confirmed)

The reduction (0.1) says `1 − λ_std` is the Rayleigh minimum over the `(n−1)`-dim
**standard/label sector**. Theorem E instead gives a low-energy function on `L(P)` — the
pair indicator `f_{x*y*}`, a **degree-2** object (it depends on the relative order of two
elements), living in the trivial ⊕ standard ⊕ degree-2 irreps. Two facts follow:

- **`1 − λ₂^{BK} ≤ 2/(γn)` is rigorous** (Theorem E: the BK spectral gap is small — some
  mode mixes slowly).
- **But `λ_std ≤ λ₂^{BK}`** (the standard sector is a subspace): Theorem E bounds the gap
  in the *wrong direction* for the transport quotient. The transfer needs the slow mode to
  have a real standard-sector component — **standard dominance**.

**Standard dominance is not universal**, and the `mg-8b64` data pins exactly where it
fails and holds (BK-lazy-walk gap `bk_gap = 1−λ₂^{BK}` vs transport gap `1−λ_std`):

| regime | poset | δ | transport gap `1−λ_std` | BK gap `1−λ₂^{BK}` | frozen `E/Var` |
|---|---|---|---|---|---|
| **off-regime refuters** (single frozen pair, *not* counterexamples) | enum-n7-#600 | 0.500 | **0.226** | **0.020** | 0.111 |
| | enum-n7-#3   | 0.500 | 0.215 | 0.019 | 0.111 |
| | enum-n7-#20  | 0.500 | 0.232 | 0.019 | 0.111 |
| **in-regime** (all pairs frozen, δ→1/3) | enum-n7-#945 | 0.381 | 0.056 | **0.057** | 0.219 |
| | enum-n6-#103 | 0.385 | 0.076 | 0.071 | 0.260 |
| | enum-n7-#809 | 0.360 | 0.098 | 0.031 | 0.165 |

- **Off-regime:** `bk_gap ≈ 0.02 ≪ 0.23 ≈` transport gap. A genuinely slow BK mode exists
  (`λ₂^{BK} ≈ 0.98`), but it is **non-standard** (degree-2, the lone frozen pair): the
  transport quotient still mixes fine (`λ_std ≈ 0.77`). This is *precisely* why the naive
  single-cut L1b is false — the low-energy cut lands in the wrong irrep. It is the
  irrep-level mechanism behind `mg-8b64`'s 166 refuters.
- **In-regime:** `bk_gap ≈` transport gap (#945: 0.057 ≈ 0.056). All-pairs-frozen pushes
  the slow mode **into** the standard sector; standard dominance is restored.

So **L1b ⟺ "all-pairs-frozen ⇒ standard dominance,"** and LIB (§4) is its quantitative
form. (Kill-shot 2 in `mg-b0a6` reported standard dominance "universal," but only checked
`n≤6` exhaustively and `n=7` at the *highest*-λ posets; the moderate-λ `n=7` refuters,
outside that spot-check, violate it — consistent with the numbers above, where
`λ₂^{BK} ≈ 0.98 ≠ 0.77 ≈ λ_std`. This is a small correction to that kill-shot's scope, not
a contradiction of its in-regime reading.)

---

## 6. Why all-pairs-frozen is *necessary* (reconciling mg-8b64) but not *sufficient for a proof*

`mg-8b64` established empirically that the single frozen cut is insufficient and the global
δ<1/3 hypothesis is needed (corr → +0.93 in-regime, zero refuters). The analysis here
explains both halves rigorously:

- **Necessity.** A single balanced pair destroys the distinguished order `e` (a balanced
  pair has no strong orientation), so §3's threshold machinery has no reference; and §5
  shows the lone-frozen-pair mode is non-standard. All-pairs-frozen is what makes `e`
  well-defined *and* (empirically) forces the slow mode standard. The refuters are outside
  LIB's hypothesis, not counterexamples to it.
- **Insufficiency for a proof.** All-pairs-frozen delivers exactly the pairwise marginals
  `Pr[j<_σ i] < 1/3` — and §4.2 shows those marginals are consistent with `Θ(n²)`
  inversions. So the hypothesis, *used only through its marginals*, cannot prove LIB. The
  proof must reach into the joint law. mg-8b64's empirical modulus `1−λ_std ≲ 3.6·Φ_BK`
  is the *shadow* of LIB holding on the tested ensemble; it is not a theorem
  (`feedback_empirical_green_is_not_proven`).

---

## 7. What would close it — candidate routes to LIB

LIB is the single remaining obligation. Genuinely promising attacks (none completed here):

1. **Chain-pair correlation inequality.** Prove `E[inv_{ab}] = O(n/γ)` for each of the 3
   chain pairs directly, using that the interleaving of two chains inside `L(P)` is a
   *ballot-type* measure (a random lattice path weighted by the third chain). FKG /
   Ahlswede–Daykin / Brightwell-style positive-correlation on the interleaving lattice is
   the natural hammer; the obstruction in §4.2 (two-atom mixture) is *not* such a measure,
   so a genuine correlation inequality can separate them. This is the highest-value lead.
2. **Rank-variance route.** LIB's displacement form is `E Σ_x Var-like|σ⁻¹(x)−x| = O(n/γ)`.
   `Var(σ⁻¹(x)) = Σ_{y,y'} Cov(1[y<_σx],1[y'<_σx])`; the diagonal is `O(n)` (frozen), so
   the whole content is that the **off-diagonal covariances telescope/cancel** — a
   second-moment identity for linear extensions. Step 5's second-moment machinery
   (`step5.tex`, `cor:second-moment`) is the in-house tool of exactly this type.
3. **Geometric freezing.** Strengthen Lemma 4.1 to *geometric* decay
   `Pr[v_j <_σ u_i] ≤ ρ^{j}` for some `ρ = ρ(γ) < 1`, along a chain, which would sum to
   `O(1/(1−ρ))` per element and give LIB. Geometric (not just monotone) decay is a
   transfer-matrix / mixing statement about the 3-chain interleaving — again joint-law,
   but a very structured one (width 3 ⇒ a bounded-state transfer operator).
4. **Import Čech/F-series output.** Per the strategic note, LIB is the shared crux; a
   proof of BK-bad-mixing-with-standard-component from that program ports directly here via
   §5.

**Bounded-attempt boundary.** Each of routes 1–3 is a multi-session correlation-inequality
push, beyond a bounded first attempt; route 4 is cross-program. Per block-and-report, this
attempt stops at the precisely-isolated wall.

---

## 8. Numerical verification of the rigorous content

Re-verified with the `mg-b0a6` engine (`transport_matrix`, `standard_block_and_lambda`,
`enumerate_both_connected`) on 25 both-connected posets at `n=5,6`, `e` = a fixed linear
extension:

- **Prop. 2** `1 − λ_std ≤ n·leak(A)/(|A||Aᶜ|)`: held for every threshold cut of every
  poset (all assertions passed).
- **Lemma 3.2** `Σ_k leak(A_k) = ½ E Σ_x|σ⁻¹(x)−rank_e(x)|`: exact, max error `0.0`.
- **Lemma 3.3** `E[displ] ≤ 2 E[inv_e]`: held for all.

Off-vs-in-regime `bk_gap` vs transport gap table (§5) read directly from
`data/onethird-mg8b64-L1b-bk-transport-transfer.json` (`bk_gap`, `transport_gap`,
`frozen_ratio`, `delta` columns).

---

## 9. Cross-references

- **Theorem E** — `step8.tex` §sec:G1: `thm:cex-implies-low-expansion`,
  `lem:dirichlet-conductance`, `lem:frozen-pair-existence` (the proven BK input).
- **mg-8b64** — `docs/OneThird-L1b-BK-Transport-Transfer-Probe.md` (empirical modulus +
  166 refuters; this doc explains them via §5 irrep mechanism and §6 necessity).
- **mg-b0a6** — `docs/OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md` (transport
  quotient, standard dominance kill-shot 2 — scope-corrected in §5, distinguished order
  kill-shot 1).
- **Cuts-by-pairs scoping (mg-d4ed)** —
  `docs/compatibility-geometry-cuts-by-pairs-scoping.md` §5.2 (the "missing Buser-type
  modulus" — supplied here in closed form by Prop. 2; the residual difficulty relocated
  from "Buser slack" to LIB).
- **pm-onethird memory** — `project_spectral_near_ordinal_sum_program.md`,
  `project_cech_bias_program` (LIB = shared crux), `feedback_empirical_green_is_not_proven`,
  `feedback_n_poset_is_not_ordinal_sum`.

---

*Bottom line for Daniel.* The Buser-type reverse-Cheeger transfer **cleanly reduces to one
inequality** — `E[inv_e] = O(n/γ)` (LIB) — with the reduction fully proved and re-verified.
The single-cut version dies for an identifiable reason (non-standard slow mode, §5); the
correct hypothesis (all pairs frozen) is *necessary* and, used only through its pairwise
marginals, *provably insufficient* (§4.2). What remains is a genuine, poset-specific
**correlation inequality** for the joint law of a random linear extension of a frozen
width-3 poset — the same joint-law crux the Čech/F-series program faces. That is the wall,
named to the inequality.
