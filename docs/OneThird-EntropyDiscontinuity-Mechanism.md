# OneThird — The entropy-discontinuity route to L1b / Brightwell: making the mechanism precise

**Work item:** mg-a1ec. **Constraint honored:** NO NEW COMPUTATION — no datasets, no enumerations, no
Lean. Analysis, proof-attempt, and literature only. Every numeric quoted below is either an exact
elementary calculation done by hand in-line, or a citation.

**READ-FIRST completed:** `drellem2/onethird_program` `STATE.md` (two axes, proof chain, L1b, attempt
index); `docs/OneThird-L1b-general-Bwall-state.md`; `docs/OneThird-L1b-CoreLemma-forDaniel.md`.

---

## 0. Verdict

**AMBER-with-substantive-mechanism — new family, trip-wire NOT re-fired.**

The mg-0508 trip-wire fired on two consecutive AMBERs *in the tail-decay/realizability family*. This
session's residual is **not** in that family: it does not attempt (decay), does not re-derive the (B)
certificate, and does not touch `E[M_{k,l}]`. It attacks the mechanism question and delivers:

1. **(a) DELIVERED — the discontinuous quantity is named, and it is not any functional of a single
   poset.** It is the **balance spectrum** `Δ = {δ(P)}` and its **realizability profile**; the
   discontinuity is *isolation of 1/3 from above*, and I show why **no convex/entropy relaxation can
   ever exhibit it** (§3, Prop. 3.2 — proved, modulo one cleanly-flagged literature fact (R1)).
   The companion "entropy" object — the correct replacement for scalar `log e(P)` — is the
   **per-element log-mobility profile** `(log E[L_x])_x` from an exact entropy decomposition proved
   here (§4, Prop. 4.2).
2. **(b) DELIVERED with a concrete reach report.** Stanley's *absolute-position* AF inequality is
   pointed at the gap. **Result: it kills the two-atom law outright and reduces (B) from a
   second-moment to a first-moment statement (§5, Prop. 5.3) — and then stops dead, because the
   fatal flat configuration is an *equality case* of Stanley's inequality.** The AF machinery is not
   merely insufficient, it is **saturated**. The unique remaining lever is therefore the
   **equality-case theory** (Ma–Shenfeld 2022/2023), which is new since this arc's tool survey and
   is **not** in the attempt index.
3. **New proved lemma (§6, Lemma 6.1 — the Blocking Dichotomy)**, from a structural fact about
   `L(P)` (conditional uniformity, §4) that this arc has not used anywhere. It converts the flat-tail
   threat into an explicit trichotomy, and (c) reports precisely which branch resists.
4. **Literature correction (§7): Aires–Kahn, arXiv:2509.11549 (Sept 2025) is not in the arc's
   record and materially changes the scope.** Large width is *settled*: `δ(P) → 1/2` when the width
   is `Ω(n)` or there are `ω(log n)` minimal elements. A frozen counterexample therefore has
   **`O(log n)` minimal elements** — a hypothesis the any-width re-scope (mg-a7c5/mg-0508) did not
   have and that the Blocking Dichotomy can consume.

**What is NOT claimed.** L1b is not closed. (decay) is not proved. Nothing here is "empirical-GREEN";
§8 tabulates proven / conjectured / heuristic line by line.

---

## 1. Anti-drift check against the vision

The ticket's vision: *the continuous Kahn–Linial entropy method plateaus at the irrational 0.2764 and
structurally cannot reach 1/3; the conjectured truth is rational and attained by a discrete gadget;
the coherence fact at δ<1/3 induces a discontinuity the smooth method is blind to.*

Every section below is a step of exactly that argument, in this order:

| § | step of the vision |
|---|---|
| 2 | the two extremal configurations are the **same object** (slot law of an element vs a chain) at two different **arithmetic types** — this is where 0.2764 vs 1/3 comes from |
| 3 | what "discontinuity" means precisely, and the **proof that a relaxation cannot see it** |
| 4 | the exact entropy decomposition — the replacement for the (continuous, useless) scalar `log e(P)` |
| 5 | the AF/atlas attempt: how far it reaches, and the exact saturation point |
| 6 | the two-atom law confronted; the new Blocking Dichotomy |
| 7 | literature; 8 | status table; 9 | forward vectors |

I have **not** re-derived the (B) certificate, `(GID)`, `(★global)`, `(decay)`, or the elementary
3-element anchor; they are cited and consumed only.

---

## 2. Why 0.2764 and 1/3 are the same variational problem at two arithmetic types

### 2.1 The shared object

Both extremal problems live on one object: **the position law of a single element**.

- Kahn–Saks (1984) / Kahn–Linial (1991) / Brightwell–Felsner–Trotter (1995) bound `δ` by applying
  Alexandrov–Fenchel, resp. Brunn–Minkowski on the order polytope `O(P)`, to a **slot/position
  sequence**, then optimizing a ratio over all sequences the inequality permits. The optimum is
  `(5−√5)/10 = 0.27639…` (BFT), and it is attained in the limit by a **geometric** sequence.
- The conjectured truth `1/3` is attained exactly by **tight3** = `{a <_P b}` ⊔ `{c}` (`c` free).

### 2.2 The exact computation at both endpoints (elementary, done here)

**tight3.** `L(P) = {cab, acb, abc}`, `e(P)=3`. Absolute-position counts of `c`:
`N_0 = N_1 = N_2 = 1` — **flat**. Pair biases: `Pr[c ≺ a] = 1/3`, `Pr[c ≺ b] = 2/3`, so
`δ(tight3) = 1/3` **exactly**.

**The AF/BM family.** A geometric sequence `N_i = C r^i` satisfies Stanley's log-concavity
`N_i² ≥ N_{i−1}N_{i+1}` **with equality for every `i`** (`C²r^{2i} = C²r^{2i}`). The whole ray
`r ∈ (0,1]` is an equality case. The BFT optimum sits at `r = 1/φ = (√5−1)/2`, the fixed point of the
two-term recursion the log-concave optimization produces; the irrationality of `0.2764` is exactly
the irrationality of that quadratic fixed point.

### 2.3 The reading

> **The smooth method optimizes over the geometric ray `r ∈ (0,1]` and lands at `r = 1/φ`
> (`δ = 0.2764`, irrational). The realizable truth sits at the ray's endpoint `r = 1` — the FLAT law
> — which is `tight3` (`δ = 1/3`, rational).**

Two verified data points, not a proof of a monotone family. But they are the two endpoints the whole
gap is about, and they explain both the *value* and the *arithmetic type* of each constant:

| | extremal shape | ratio `r` | value of `δ` | arithmetic type | source |
|---|---|---|---|---|---|
| smooth (AF / BM) optimum | geometric | `1/φ` | `(5−√5)/10 ≈ 0.2764` | irrational, quadratic | BFT 1995 |
| realizable optimum | **flat** | `1` | `1/3` | rational | tight3 |

**And the flat law is the arc's own fatal object.** `docs/OneThird-L1b-CoreLemma-forDaniel.md` §2.1
form 3: (B) fails **iff** a frozen poset realizes a flat-long slot law (`ρ_s ≡ 1`). So the
configuration L1b must exclude and the configuration that attains `δ = 1/3` are **the same shape**.
That is not a coincidence to be explained away — it is the mechanism. *(CONJECTURAL as a general
identification; PROVEN at the two endpoints computed above.)*

---

## 3. (a) The precise discontinuous quantity — and why a relaxation is blind to it

### 3.1 What is *not* discontinuous

Per the ticket's own warning: `log e(P)`, `δ(P)`, and every pair bias `p_{xy} = e(P_{x<y})/e(P)` are
ratios of counts over a discrete family; there is no topology on poset-space in which any of them
"jumps". **Chasing a discontinuous scalar functional of a single poset is a category error.** The
discontinuity is in the **range**, not in any map.

### 3.2 The right object: the balance spectrum

> **Definition.** `Δ := { δ(P) : P a finite poset, not a chain } ⊆ [0, 1/2]`.

> **THEOREM-TARGET A (isolation of 1/3 from above).** There is `η > 0` with
> `Δ ∩ (1/3, 1/3 + η) = ∅`.

> **THEOREM-TARGET A′ (rigidity at the floor).** `{P : δ(P) = 1/3}` is exactly the ordinal-sum
> closure of `{singleton, tight3}`.

**These are not speculation — they are PROVEN at width 2.** Sah (arXiv:1811.01500, *Combinatorica*):
for every width-2 poset **not** built from the singleton and tight3 by (ordinal) sum,
`δ(P) ≥ (−3+5√17)/52 ≈ 0.33876`; and there are width-2 `T_n` with `δ(T_n) → β ≈ 0.348843`. So at
width 2:

- A′ holds — the exception class is **exactly** the ordinal-sum closure of `{singleton, tight3}`,
  which is the class I independently arrived at in §2 as the "flat/rational" family. (Ordinal sum
  preserves within-factor pair probabilities, so `δ(P ⊕ Q) = max(δ(P), δ(Q))`; the closure has
  `δ ≡ 1/3` throughout. Elementary, verified here.)
- A holds with `η ≈ 0.0054` (`= 0.33876 − 1/3`), and the true `η` at width 2 is
  `β − 1/3 ≈ 0.01551`.

This is the ticket's "PROVEN for width-2 by opaque casework with NO articulated reason". **A and A′
are the articulated statement of what that casework proves**, and the arc's empirical "no poset in
`(1/3, 0.354)`, constructions plateau near 0.349" (STATE.md, Convergence Point) is the *any-width*
shadow of exactly Sah's `β ≈ 0.348843`. The empirical forbidden band **is** the width-2 theorem,
observed at higher width. That identification is new to this arc's record.

### 3.3 Why the entropy method is structurally blind — this is the mechanism, and it is provable

Let `𝓡` be the feasible set of the AF/Brunn–Minkowski relaxation: all position/slot data satisfying
the log-concavity (resp. `(n−1)`-th-root-concavity) constraints the method imposes, together with the
pairwise-consistency constraints, but **without** the requirement of being realized by an actual
poset. The method's output is `inf{ δ(y) : y ∈ 𝓡 }`.

> **(R1) [flagged literature fact].** `𝓡` is convex (log-concavity constraints on the log-data and
> BM-concavity constraints are convex), and `δ(·)` restricted to `𝓡` is continuous. BFT's tightness
> shows `inf_{𝓡} δ = (5−√5)/10` **and is attained/approached inside `𝓡`**.

> **Proposition 3.2 (blindness).** *Assume (R1). Then `δ(𝓡) ⊇ [(5−√5)/10, 1/2]` — an interval.
> Consequently:*
> 1. *No bound obtained by minimizing `δ` over `𝓡` can exceed `0.2764`; in particular the method
>    cannot prove `δ ≥ 1/3`.*
> 2. ***The method cannot exhibit a forbidden band at all.*** *`δ(𝓡)` is the continuous image of a
>    connected set, hence an interval, hence contains `(1/3, 1/3+η)` for every `η`. A gap in the
>    range is invisible to any relaxation with connected feasible set.*
>
> *Proof.* `𝓡` convex ⟹ connected; `δ` continuous on it ⟹ `δ(𝓡)` connected in `ℝ` ⟹ an interval.
> It contains `1/2` (the free/antichain data) and infimum `0.2764` by (R1). ∎

**This is the precise content of "the smooth method structurally cannot reach 1/3."** It is not that
`0.2764 < 1/3` by an unlucky constant that a sharper inequality might close. It is that the *shape*
of the true statement — **a gap in a range** — is of a type that a connected relaxation provably
cannot certify, for any inequality one puts into `𝓡`. Getting to `1/3` requires an ingredient that
is **not** a valid inequality on relaxed data: it must be an **arithmetic/realizability constraint**,
i.e. one that carves a disconnected subset out of `𝓡`.

**Where coherence enters.** The elementary anchor (`Pr[x≺y]+Pr[y≺z]+Pr[z≺x] ≤ 2`, so `δ<1/3` ⟹ the
strong-majority tournament is 3-cycle-free ⟹ transitive ⟹ the distinguished order `e`) is exactly
such a constraint: it is a **combinatorial dichotomy** (coherent / not), not an inequality on
continuous data, and its threshold is `2/3` because 3 of the 6 orders of a triple realize 2 cyclic
events and 3 realize 1. Sharpening §3.3's remark: writing `D(x,y,z) := 2 − (p_{xy}+p_{yz}+p_{zx})`,
an exact computation over the six orders gives

> `p_{xy}+p_{yz}+p_{zx} = 1 + μ_{xyz}(A)`, where `A` = the three cyclic rotations of `xyz`;
> hence `D = μ_{xyz}(B) ∈ [0,1]` and `D(x,y,z) + D(x,z,y) = 1`.  *(PROVEN, elementary, here.)*

So `D` is a genuine coherence potential on triples, `D ≥ 0` is the anchor, and the coherence
dichotomy is `{D < 3ε for all triples}` vs not. **This is the discrete object that disconnects `𝓡`.**
It is invisible to AF/BM because AF/BM never look at triples of *elements*; they look at one pair and
one position sequence.

**Answer to (a), stated as the target:** the quantity whose behaviour is discontinuous at `δ = 1/3`
is the **realizability indicator of `𝓡`** — equivalently the range `Δ` — and the mechanism of the
discontinuity is the coherence dichotomy `D`. Theorem-Targets A/A′ are the statements to prove;
Prop. 3.2 is the proof that they cannot be proved inside the entropy method.

---

## 4. The correct entropy object: an exact per-element decomposition

Scalar `log e(P)` is useless (continuous, and it is the *total*). The right object is its
**decomposition**, which requires a structural fact about `L(P)` that this arc has not used.

> **Proposition 4.1 (CU — conditional uniformity).** *Let `P` be a finite poset, `x ∈ P`, and let
> `Φ : L(P) → L(P∖x)` delete `x`. For `τ ∈ L(P∖x)` let*
> `I_x(τ) := { k : max_{d ∈ D(x)} pos_τ(d) < k ≤ min_{u ∈ U(x)} pos_τ(u) }`
> *(`D(x), U(x)` the strict down/up-sets). Then `I_x(τ)` is a non-empty integer interval,
> `Φ^{-1}(τ)` is exactly the set of insertions of `x` into the slots of `I_x(τ)`, and these are all
> distinct linear extensions of `P`. Consequently, for uniform `σ ∈ L(P)`:*
> - `e(P) = Σ_τ |I_x(τ)|`;
> - *`τ = Φ(σ)` has law `∝ |I_x(τ)|` (size-biased), and*
> - ***`pos_σ(x) | τ ~ Uniform(I_x(τ))`.***
>
> *Proof.* The only order constraints on `x` are with `D(x)` and `U(x)`, so a slot is admissible iff
> it is after all of `D(x)` and before all of `U(x)` — an interval; it is non-empty because
> `d <_P x <_P u ⟹ d <_P u ⟹ pos_τ(d) < pos_τ(u)`. Every admissible insertion refines `P`, and
> distinct slots give distinct linear extensions with the same deletion. The fibre sizes are
> `|I_x(τ)|`, giving the count and both laws. ∎ *(PROVEN, elementary. Classical in spirit; not used
> anywhere in this arc's documents.)*

Two immediate consequences.

> **Proposition 4.2 (exact entropy decomposition).** *Deleting elements one at a time along any
> order `x_1, …, x_n`, with `P_j := P ∖ {x_1,…,x_{j−1}}`,*
> $$\log e(P) \;=\; \sum_{j=1}^{n} \log \mathbb E^{\mathrm{unif}}_{\tau \in L(P_j \setminus x_j)}\big[\,|I_{x_j}(\tau)|\,\big].$$
> *Each summand is the **log-mobility** of one element: the log of its expected number of admissible
> slots.* *(PROVEN — immediate from `e(P_j) = e(P_j∖x_j)·E[|I_{x_j}|]`.)*

> **Corollary 4.3 (`N_i` is an interval-coverage function).**
> `N_i(x) := #{σ ∈ L(P) : pos_σ(x) = i} = #{ τ ∈ L(P∖x) : i ∈ I_x(τ) }`.
> *So the position law of any element of any poset is an **unweighted superposition of uniform laws
> on intervals**. The **extreme rays of the realizable cone are the FLAT laws** — `r = 1` in §2.*
> *(PROVEN.)*

**This answers the "which entropy" question of deliverable (a) in its second form.** The entropy the
method should be tracking is not the scalar but the **profile** `(log E[L_x])_x`, `L_x := |I_x(τ)|`.
Prop. 4.2 says the profile's sum is exactly `log e(P)`; §5 says (B) is exactly an `ℓ²`-vs-`ℓ¹`
statement about the profile. The "discontinuity" in the profile language is a
**localization/delocalization** statement: whether `log e(P)` is carried by `Θ(n)` elements of `O(1)`
mobility (near-ordinal-sum, (B) TRUE) or by `O(1)` elements of `Θ(n)` mobility (flat-long block-cross,
(B) FALSE). Note Cor. 4.3 makes the arc's `p_{xy} = e(P_{x<y})/e(P)` "discrete derivative" picture
exact: the biases are ratios of coverage counts of the same interval family.

---

## 5. (b) Pointing Stanley absolute-position AF at the gap — reach report

The attempt index records: *"Dead ≠ AF | Slot-law log-concavity | Numerically false; ignores
Stanley's **absolute**-position AF"* and *"Untried · convergent | Convexity forbids flat slot law |
Weak-Bruhat + Stanley absolute-position AF untried."* This section does that.

**The tool.** Stanley (1981, *Two combinatorial applications of the Alexandrov–Fenchel inequalities*):
for any finite poset `P` and any `x ∈ P`, the absolute-position sequence `N_i(x)` is **log-concave**:
`N_i² ≥ N_{i−1}N_{i+1}`. This is a *theorem* (via AF on order-polytope mixed volumes), unconditional,
any width. It is **not** the refuted object: the numerically-false log-concavity of mg-2acf is the
*relative*-to-chain slot polynomial `e(P_m)` (Neggers–Stanley). The distinction is real and the arc
flagged it correctly.

### 5.1 What it reaches — three genuine gains

> **Prop. 5.1 (two-atom law refuted by AF).** No poset's uniform LE law is a two-atom law
> `μ = (2/3+ε)δ_e + (1/3−ε)δ_{e'}` with `e, e'` at Kendall distance `≥ 2`. *Proof.* For `x` with
> `pos_e(x) ≠ pos_{e'}(x)`, `N_i(x)` has an interior zero with positive mass on both sides,
> contradicting log-concavity. ∎

> **Prop. 5.2 (geometric tail after the first drop).** Log-concavity ⟹ the ratios
> `r_i := N_{i+1}/N_i` are non-increasing. Hence if `r_{i_0} = θ < 1` then `N_i ≤ N_{i_0} θ^{\,i−i_0}`
> for all `i > i_0`. **This is literally `(decay)`'s conclusion**, with rate `θ`. So AF *does*
> deliver the geometric far-tail decay the Core Lemma asks for — *conditionally on `θ` being bounded
> away from `1`.*

> **Prop. 5.3 (AF collapses (B) from second moment to first moment).** For a log-concave law all
> moments are comparable: `E[|Z−m|²] ≍ (E|Z−m|)²`. Applying this to `pos_σ(x)` and writing
> `a_x := E|disp_x|`,
> $$\sum_x \mathbb E[\mathrm{disp}_x^2] \;\asymp\; \sum_x a_x^2 ,\qquad\text{so}\qquad
> \textbf{(B)} \iff \sum_x a_x^2 = O\!\big(\textstyle\sum_x a_x\big).$$
> **(B) is therefore an `ℓ²`-vs-`ℓ¹` statement on the first-moment displacement profile** — no
> second moments anywhere. In particular `max_x a_x = O(1)` ⟹ (B); and (B) fails only via a *few*
> elements with `a_x` growing. *(PROVEN, modulo the standard log-concave moment-comparison constant.)*

Prop. 5.3 is a real simplification of L1b's shape and is, as far as this arc's docs record,
**new**: it removes the entire second-moment layer that `(GID)` / `(★global)` / `E[M_{k,l}]` was
built to manage. Combining with Prop. 4.1: since `pos(x)|τ ~ Unif(I_x(τ))`, `a_x ≍ E[\max(|m_x|, L_x)]`
where `L_x = |I_x(τ)|` and `m_x` is the offset of `I_x`'s midpoint from `x`'s `e`-rank — so the
`ℓ²/ℓ¹` statement is literally about the **mobility profile** of §4.

### 5.2 Where it stops — and *why* it stops there

> **The flat law `N_i ≡ c` is log-concave, with EQUALITY at every `i`.**

So `r_i ≡ 1`, `θ = 1`, Prop. 5.2 is vacuous, and Prop. 5.3's residual `Σ a_x² = O(Σ a_x)` is exactly
false for a single element with `L_x = Θ(n)`. **AF does not merely fail to exclude the fatal
configuration; the fatal configuration is an *equality case* of AF.** More: by §2.2 the *entire*
geometric ray `r ∈ (0,1]` is an equality case, so:

> **Finding 5.4 (the saturation).** *Both* extremals of the whole problem — the KL/BFT optimum
> (`r = 1/φ`, `δ = 0.2764`) and the L1b-fatal flat law (`r = 1`, `δ = 1/3`) — lie on the **same
> equality locus of Stanley's inequality**. AF sees the geometric ray and cannot distinguish any
> point of it from any other. *The arithmetic selection of which `r` is realizable is precisely the
> information AF discards.*

This is the sharp form of "the smooth method is blind", now at the level of the *inequality* rather
than the *relaxation* (§3.3): **no strengthening of an AF-type log-concavity inequality can help,
because any such inequality is saturated on the ray containing the answer.**

### 5.3 The consequence: the only remaining lever is the EQUALITY-CASE theory

If the fatal object is an equality case, one must use the classification of equality cases. That
machinery **did not exist when this arc's tool survey was written** and is absent from the attempt
index and from `CoreLemma-forDaniel.md` §5 (Appendix — tools known DEAD):

- **Shenfeld–van Handel**, *The extremals of the Alexandrov–Fenchel inequality for convex polytopes*,
  Acta Math. 231 (2023) — the AF extremals, for polytopes.
- **Ma–Shenfeld**, *The extremals of Stanley's inequalities for partially ordered sets*,
  arXiv:2211.14252, Adv. Math. (2023) — **a complete characterization of the equality cases of
  Stanley's inequality**, via a poset↔polytope "dictionary", organizing posets as
  *subcritical ⊃ critical ⊃ supercritical*.
- **Chan–Pak–Panova**, arXiv:2005.08390 (combinatorial atlas) and the Kahn–Saks extremals; survey
  Chan–Pak arXiv:2311.02743 §16.

> **THEOREM-TARGET B (the AF-equality attack on L1b).** *Let `P` be frozen (`δ(P) < 1/3`) and let
> `x ∈ P`. Show that `N_i(x)` cannot be equality-flat (`N_i = N_{i+1}`) over a range of length
> `Θ(n)`. Equivalently: a `Θ(n)`-fold Stanley equality case is incompatible with `δ(P) < 1/3`.*
>
> By Prop. 5.2 + Prop. 5.3, **Theorem-Target B ⟹ (decay) ⟹ (B) ⟹ L1b, at any width.**

This is the concrete, checkable reduction the ticket asked for under (b). It is a *good* target for
this machinery: `Θ(n)` simultaneous equalities is an extraordinarily rigid hypothesis, and Ma–Shenfeld
is exactly a rigidity classification. Whether the resulting structure contradicts freezing is
**open and untried** — I could not verify the precise statement of the Ma–Shenfeld characterization
in-session (arXiv PDFs did not text-extract in this environment; `pdftoppm`/`pypdf` unavailable, and
the constraint forbade installing tooling). **That verification is the single concrete next step**,
and it is reading, not computation.

---

## 6. The two-atom law, confronted — and the Blocking Dichotomy

The ticket requires confronting the two-atom law explicitly: why connectedness/uniformity excludes
it, and whether that argument reaches the flat slot law.

### 6.1 The two-atom law is excluded three times over — all of them cheaply

1. **Uniformity.** A poset's LE law is uniform on `L(P)`; masses `(2/3+ε, 1/3−ε)` are not.
2. **Support (this is "connectedness", made sharp by Prop. 4.1).** If `|L(P)| = 2`, then
   `2 = Σ_τ |I_x(τ)|` for every `x`, so either one `τ` has `|I_x| = 2` (i.e. `e, e'` differ by moving
   `x` one slot) or the projections differ. Iterating over `x`: **`e` and `e'` differ by a single
   adjacent transposition of an incomparable pair.** Kendall distance `Θ(n²)` is therefore impossible
   — a strictly stronger conclusion than "the LE graph is connected".
3. **Mass (AF).** Prop. 5.1.

### 6.2 The honest finding: that argument provably CANNOT reach the flat slot law

This is the ticket's target gap, and the finding is not "we haven't tried hard enough":

> **Finding 6.0 (type mismatch).** All three exclusions of the two-atom law are statements about
> **support and normalization**: (1) is normalization, (2) bounds the support's diameter, (3) forbids
> an interior *zero*. **The flat-long block-cross has full support, is uniform, and has no interior
> zero.** Every exclusion above is *vacuous* on it. So no sharpening of the connectedness/uniformity
> argument can reach the flat law — the arc's suspicion is correct, and the reason is structural,
> not effort.

The two-atom law is thus, as an obstruction, a **red herring**: it is what a *measure-theoretic*
relaxation of `L(P)` produces, and it dies to trivia. The real obstruction, the flat law, is what an
*AF-relaxation* of `L(P)` produces, and it dies to nothing currently available (§5.2). The upgrade
required is exactly **support-level ⟶ mass-level**, which is §5.3.

### 6.3 A new proved lemma: the Blocking Dichotomy

Prop. 4.1 does give something the support arguments do not. Setup as in
`CoreLemma-forDaniel.md` §1.3: `P` frozen, labelled by `e`; `x ∈ P`; `C : c_1 <_P ⋯ <_P c_p` a chain
with every `c_s ∥ x` and `x` `e`-below all of `C`; `g := #\{s : c_s ≺_σ x\}`.

> **Lemma 6.1 (Blocking Dichotomy).** *For every `τ ∈ L(P∖x)`, exactly one of:*
> - **(i) spread:** *every `c_s` lies strictly inside `I_x(τ)`, and then*
>   `Pr[g = s \mid τ] ≥ 1/|I_x(τ)|` *for **every** `s ∈ \{0,1,…,p\}`;*
> - **(ii) blocked:** *some `d ∈ D(x)` satisfies `pos_τ(d) ≥ pos_τ(c_s)` for some `s` — and then
>   necessarily `d ∥ c_s` and `\{d, c_s\}` is an **`e`-inverted incomparable pair**.*
>
> *Proof.* By Prop. 4.1, conditionally on `τ` the element `x` is uniform on the `|I_x(τ)|` slots of
> `I_x(τ)`, and `g` is the number of `c_s` at `τ`-positions below the chosen slot. If all `c_s` lie
> inside `I_x(τ)` then for each `s` the slot immediately after `c_s` and the slot immediately before
> `c_{s+1}` are admissible, so each value `s ∈ \{0,…,p\}` is attained by at least one slot: this is
> (i). Otherwise some `c_s` is at or below `max_{d∈D(x)} pos_τ(d)` (the up-set side is symmetric and
> handled identically), giving `d ∈ D(x)` with `pos_τ(d) ≥ pos_τ(c_s)`. Then `d <_P x`; `d >_P c_s`
> is impossible (it would force `c_s <_P x`, contradicting `c_s ∥ x`) and `d <_P c_s` is impossible
> (comparable pairs never `e`-invert, yet `d` is after `c_s`); so `d ∥ c_s`. Since `x` is `e`-below
> all of `C` and `d <_P x`, `d` is `e`-below `c_s`, so `d` after `c_s` is an `e`-inversion. ∎
> *(PROVEN, elementary, new.)*

> **Corollary 6.2 (mass floor on the interior slots).** With `B` := the event of branch (ii),
> $$\sum_{s=1}^{p-1} \Pr[g = s] \;\ge\; (p-1)\cdot \mathbb E\!\left[\frac{\mathbf 1_{B^c}}{|I_x|}\right].$$

**What this buys.** The flat-long block-cross requires the interior slot mass to be `≈ 0`. Cor. 6.2
turns that into an explicit **trichotomy**: a frozen flat-long block-cross forces **at least one** of

- **(T1)** `Pr[B] ≈ 1` — *`x`'s strict down-set `e`-inverts with the chain `C` essentially always*;
- **(T2)** `E[|I_x|] ≫ p` — *`x`'s own mobility exceeds the block length*;
- **(T3)** `p = O(1)` — not the threat regime.

Each branch is a *structural* consequence, not a restatement. (T1) says the deep-crosser must be
**propped up from below by another deep-crosser** — and `d <_P x` is strictly `P`-lower, so the
argument descends. (T2) says the fatal element is not "one long jump" but "one hugely mobile
element", which is precisely the `a_x = Θ(n)` singleton that Prop. 5.3 isolates.

---

## 7. Literature: a correction the arc's record does not contain

**Aires–Kahn, *Balancing Extensions in Posets of Large Width*, arXiv:2509.11549 (15 Sep 2025).**
`δ(P) → 1/2` as `n → ∞` for posets of width `Ω(n)`, and **also for posets with `ω(log n)` minimal
elements**; `δ(P) ≥ 1/e − o(1)` for width `ω(√n)` or height `o(n)`.

This is **not** in `STATE.md`, the attempt index, or any L1b doc, and it matters on three counts:

1. **It partly deflates the any-width re-scope (mg-a7c5 / mg-0508 / mg-c899).** The drift audit
   pushed the arc from width 3 to any width. Aires–Kahn settles the large-width end
   asymptotically, so the frozen regime is confined to **small width / large height**. The width-3
   focus of `main.tex` was closer to the real difficulty than the drift audit credited.
2. **It hands the Blocking Dichotomy a hypothesis it did not have.** A frozen poset has
   **`O(log n)` minimal elements**. Lemma 6.1's branch (T1) descends strictly downward in `P`; the
   descent terminates at minimal elements, of which there are now only `O(log n)`. This is exactly
   the kind of finiteness that could close a descent argument, and it was unavailable before
   Sep 2025.
3. **It is a live-tool citation for the `.tex`'s any-width claims**, which should be checked against
   it before circulation.

Other citations used above: Sah arXiv:1811.01500 (width-2 gap, the `tight3`-sum exception class,
`β ≈ 0.348843`); Brightwell–Felsner–Trotter, *Balancing pairs and the cross product conjecture*,
Order (1995) — `(5±√5)/10`; Kahn–Saks (1984) — `3/11`; Stanley (1981); Shenfeld–van Handel Acta Math.
231 (2023); Ma–Shenfeld arXiv:2211.14252; Chan–Pak–Panova arXiv:2005.08390; Chan–Pak survey
arXiv:2311.02743 §16.

**Novelty check, honestly reported.** I found no source stating an entropy/AF discontinuity at `1/3`.
What §3 shows is weaker and cleaner than "an entropy is discontinuous": it is that the true statement
is a *gap in a range*, which no connected relaxation can certify. I believe **that** framing is new;
I did not find it in the literature surveyed.

---

## 8. Status table — proven / conjectured / heuristic, line by line

| # | statement | status |
|---|---|---|
| 2.2 | `δ(tight3) = 1/3`; `N_i(c)` flat; geometric `N_i` saturates Stanley | **PROVEN** (elementary, here) |
| 2.3 | the smooth optimum is `r = 1/φ` and the realizable one is `r = 1` as a *general* principle | **CONJECTURED** (two endpoints verified) |
| 3.2 | Theorem-Targets **A**, **A′** | **PROVEN at width 2** (Sah); **CONJECTURED** in general |
| 3.2 | the width-2 exception class = ordinal-sum closure of `{singleton, tight3}`; `δ(P⊕Q)=max` | **PROVEN** (Sah + elementary here) |
| 3.2 | the arc's empirical forbidden band ≡ Sah's `β ≈ 0.348843` | **IDENTIFICATION** (heuristic; matches to 3 d.p.) |
| 3.3 | `p_{xy}+p_{yz}+p_{zx} = 1 + μ(A)`; `D + D^{rev} = 1` | **PROVEN** (elementary, here) |
| 3.3 | **Prop. 3.2 (blindness of relaxations)** | **PROVEN modulo (R1)**; (R1) is flagged, not verified in-session |
| 4.1 | **Prop. 4.1 (CU)** | **PROVEN** (elementary) |
| 4.2 | **Prop. 4.2 (entropy decomposition)**, **Cor. 4.3 (interval coverage)** | **PROVEN** |
| 4.3 | localization/delocalization reading of the profile | **HEURISTIC framing** |
| 5.1 | Props. 5.1, 5.2 | **PROVEN** (from Stanley 1981) |
| 5.1 | **Prop. 5.3 ((B) ⟺ `Σa_x² = O(Σa_x)`)** | **PROVEN** modulo the standard log-concave moment constant |
| 5.2 | **Finding 5.4 (AF saturation on the geometric ray)** | **PROVEN** |
| 5.3 | **Theorem-Target B** and `B ⟹ (decay) ⟹ (B) ⟹ L1b` | implication **PROVEN**; the target itself **OPEN/UNTRIED** |
| 5.3 | the precise Ma–Shenfeld extremal characterization | **NOT VERIFIED in-session** (PDF extraction unavailable) |
| 6.1 | three exclusions of the two-atom law; adjacent-transposition sharpening | **PROVEN** |
| 6.2 | **Finding 6.0 (type mismatch — support args cannot reach the flat law)** | **PROVEN** in the stated form |
| 6.3 | **Lemma 6.1 (Blocking Dichotomy)**, **Cor. 6.2**, trichotomy (T1)/(T2)/(T3) | **PROVEN** (elementary, new) |
| 7 | Aires–Kahn consequences (1)–(3) | citation **VERIFIED** (abstract); consequence (2) is a **PROPOSED USE**, not a proof |

Nothing here is asserted on empirical grounds. No computation was run.

---

## 9. (c) The precise obstruction, and the forward vectors

**Where coherence + realizability still fails to yield the discontinuity — exactly.**

Coherence (`δ < 1/3` ⟹ total order `e`) is a constraint on the **sign pattern** of the pair biases.
The flat law is a constraint on the **magnitude profile** of a single element's position law. The two
constrain *disjoint coordinates*: §2.3's flat law `q_s ≡ q < 1/3` satisfies every coherence
constraint by construction (all biases point the same way), and coherence says nothing whatever about
the ratios `ρ_s`. **That is the gap, and it is the same gap at every level of the tower:**

| level | what excludes the bad object | does it reach the flat law? |
|---|---|---|
| measure (two-atom law) | uniformity + support diameter (§6.1) | **No** — vacuous on full-support objects (Finding 6.0) |
| AF inequality (Stanley) | interior zeros (Prop. 5.1) | **No** — flat is an *equality case* (Finding 5.4) |
| relaxation (KL/BM) | nothing above `0.2764` | **No, and provably never** (Prop. 3.2) |
| AF **equality cases** (Ma–Shenfeld) | ? | **UNTRIED — the only lever left** |

The obstruction is therefore located with unusual precision: **every tool the arc has used lives on
the wrong side of an equality case.** The flat law is not "hard to exclude"; it is the *extremal* of
every inequality deployed against it. The single remaining move is to stop deploying inequalities and
deploy the classification of their extremals.

**Recommended vectors, in priority order (recommendations only; no tickets filed):**

1. **[Highest] Pin Ma–Shenfeld and test Theorem-Target B.** Read arXiv:2211.14252 (and the
   Kahn–Saks-extremals companion) and determine what a `Θ(n)`-fold equality case of Stanley's
   inequality forces structurally (subcritical/critical/supercritical), then test that structure
   against `δ(P) < 1/3`. This is *reading*, satisfies the no-computation constraint, is in a **new
   tool family** (so the mg-0508 trip-wire does not bind), and closes L1b at any width if it lands.
   Environment note: whoever takes it needs working PDF text extraction (`poppler`/`pypdf`), which
   this session lacked.
2. **Prosecute Theorem-Target A′ at width 3.** Sah proves A/A′ at width 2 by casework. §2–§3 supply
   the *reason* the casework should generalize (the exception class is exactly the flat/rational
   family). Width 3 is where `main.tex` already lives, so a width-3 A′ would be immediately
   consumable — and would be the first *articulated* proof of the phenomenon rather than casework.
3. **Feed Aires–Kahn into the Blocking Dichotomy.** `O(log n)` minimal elements + the strict downward
   descent of branch (T1) is a genuinely new combination; see whether the descent terminates.
4. **Retire "two-atom law" as the framing obstruction** in `STATE.md` and the L1b docs, replacing it
   with the flat-law/equality-case framing (Findings 5.4, 6.0). The two-atom law dies to trivia and
   is actively misleading about what needs excluding.

**One line for the attempt index (for pm-onethird):**

> `Untried → ATTEMPTED · new family` | **Entropy-discontinuity mechanism (mg-a1ec)** | *AMBER-substantive.*
> Discontinuity relocated from "a functional of `P`" to **a gap in the range `Δ = {δ(P)}`**; proved no
> connected relaxation can certify such a gap (blindness of KL/BM is structural, not numerical).
> Theorem-Targets A/A′ identified as the general-width form of Sah's width-2 theorem, exception class
> `= ordinal-sum closure of {singleton, tight3}` `=` the flat/`r=1` extremal. Stanley absolute-position
> AF: reaches (kills two-atom; collapses (B) to `Σa_x² = O(Σa_x)`, first moments only) then
> **saturates** — flat is an AF equality case, as is the `1/φ` KL extremal. New elementary tools:
> conditional uniformity (CU) + exact entropy decomposition + Blocking Dichotomy. **Sole remaining
> lever: AF equality-case theory (Ma–Shenfeld 2022/23) — untried, not in the index.** Literature
> correction: **Aires–Kahn arXiv:2509.11549 (Sep 2025)** settles large width (`δ→1/2` at width `Ω(n)`
> or `ω(log n)` minimal elements) — absent from the arc's record.

---

*mg-a1ec. No datasets generated, no enumerations run, no Lean written. Claims labelled per §8.*
