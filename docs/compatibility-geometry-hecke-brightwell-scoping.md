# Compatibility Geometry — Hecke/KL → `brightwell_sharp_centred` candidate proof scoping (mg-e396)

**Status:** scoping (no Lean changes, no new axioms, ~300-token cap honoured).
**Predecessor:** mg-5fe9 (`a32fe64`, `compat-geom-hecke-scoping`) §5.3(iv).
**Companion scopings:**
- mg-c853 (`0d8f438`) — Compatibility Geometry manifesto / 4-target feasibility.
- mg-9d6c — Path P3 (applied axiom-narrowing).
- mg-4e67 (sibling, running parallel) — Q1 cell-poset scoping.
**Branch:** `compat-geom-hecke-brightwell` (new).

**TL;DR.** **RED**, with a thin AMBER caveat for vocabulary-only
reformulation. The Hecke / KL machinery does **not** deliver a cleaner
proof of `brightwell_sharp_centred`. The core arithmetic constant
$2/m$ comes from insertion-position averaging on the
$\{1,\ldots,m\}$-fibre over $\mathcal L(\alpha)$, a structure that is
**invisible** to the $H_n(q)$-algebra. Furthermore, for the bulk of
target posets (non-heap-realizable $\alpha$ of width $\ge 3$), there
is no direct $H_n(q)$-module home for $\mathcal L(\alpha)$ at all
(mg-5fe9 §4.4(d)). The path to retire `brightwell_sharp_centred`
remains: (i) accept it as a cited axiom (current decision, mg-b699),
or (ii) port the Brightwell/Kahn–Saks combinatorial argument directly
(per `docs/brightwell-port-scope.md`, ~700–1100 LoC, 3 polecats).

This document records the scoping evidence so the question does not
need to be re-opened.

---

## 1. Recap

### 1.1 The axiom

`OneThird.LinearExt.brightwell_sharp_centred`
(`lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`,
introduced mg-134c, QA-audited mg-a6a1) asserts the integer form of
Brightwell's centred-sum bound (`step8.tex:1054`, eq:sharp-centred):

$$
\Bigl|\sum_{L' \in A}(f(L') - \bar f)\Bigr| \;\le\; \frac{2N}{m},
\quad\text{where } \bar f := N/N',\ N := |\mathcal L(Q)|,\ N' := |\mathcal L(\alpha)|,
$$

over the data $(Q, z, \alpha = Q-z, \mathrm{pred}(z), \mathrm{succ}(z), x, y, A)$
with the pred/succ separation hypothesis. The paper proof is **two
inputs**:

1. **FKG / Ahlswede–Daykin** on the τ-inversion distributive lattice
   $\mathcal L(\alpha) \times \{1,\ldots,m\}$ with uniform measure
   $\nu$ — gives the **sign** $\mathrm{Cov}_\mu(\mathbf 1_A, f) \ge 0$
   and the equality $|\mathrm{Cov}_\mu(\mathbf 1_A, f)|
   = |\mathrm{Cov}_\mu(\mathbf 1_A, S)| + |\mathrm{Cov}_\mu(\mathbf 1_A, P)|$
   (`step8.tex:1101–1244`).
2. **Per-term Kahn–Saks / Brightwell covariance bound**
   $|\mathrm{Cov}_\mu(\mathbf 1_A, S)| \le \bar f/m$,
   $|\mathrm{Cov}_\mu(\mathbf 1_A, P)| \le \bar f/m$
   (`step8.tex:1246–1271`; Brightwell 1999 Thm 4.1; Kahn–Saks 1984
   Lemma 2.2) — proved via the explicit exchange involution
   $\sigma : \mathcal L(\alpha) \to \mathcal L(\alpha)$ with
   $\sigma(A) = A^c$ and $|S(L')-S(\sigma L')|, |P(L')-P(\sigma L')|
   \le 1$.

Input (1) is **already proven** in Lean for the level-$k$
initial-ideal lattice via `FKG.fkg_uniform_initialLowerSet` (mg-9ece,
`cd75ef1`). Input (2) is the load-bearing combinatorial gap; it is
the substantive content of Brightwell §4.

### 1.2 The Hecke direction (predecessor mg-5fe9)

§5.3(iv) of mg-5fe9 surfaced the question:

> Whether the Hecke / KL machinery gives a direct proof of this
> axiom is OPEN — but the cell-poset filtration of mg-c853 §4
> provides candidate machinery (chain inequalities along the cell-
> poset of $S_n$).

This scoping evaluates whether that direction is real.

### 1.3 What "candidate proof" means here

A path is GREEN if it yields:

- a derivation of (1.1) using KL / Hecke machinery that is either
  (a) shorter than the paper proof, or
  (b) routes through different infrastructure that is independently
      Lean-portable in $\le 500$ LoC (the polecat threshold), or
  (c) bypasses the load-bearing input (2) (per-term Kahn–Saks bound)
      via algebraic identities.

AMBER if the direction reframes the problem in better vocabulary but
requires specialist input or comparable LoC.

RED if the direction does not provide a path, even with specialist
input.

---

## 2. KL polynomial / cell-structure background

### 2.1 KL polynomials and the KL basis

The Hecke algebra $H_n(q)$ has the standard $T_w$-basis and the
Kazhdan–Lusztig $C_w$-basis related by the Kazhdan–Lusztig
polynomials $P_{y,w}(q) \in \mathbb Z[q]$:

$$
C_w \;=\; \sum_{y \le w}\, (-1)^{\ell(w)-\ell(y)}\,
q^{(\ell(w)-\ell(y))/2}\, \overline{P_{y,w}(q^{-1})}\, T_y.
$$

Williamson (2014, IHES Pub. Math. **123**) proved KL positivity:
$P_{y,w}(q) \in \mathbb Z_{\ge 0}[q]$ for all type-A $y,w$. The
leading coefficient $\mu(y,w)$ encodes singular cohomology dimensions
of Schubert varieties.

**Available numerical content:** non-negativity (qualitative),
graded-dimension identities (Hodge / Lefschetz at $q=1$). **Not
available:** explicit sharp constants of the form $c/m$ with $c$ a
small integer and $m$ a poset-size parameter.

### 2.2 Cells: left, right, two-sided

For $S_n$:

- **Two-sided cells** are equivalence classes under
  $\le_{LR}$ (defined via the relation $y \le_{LR} w$ iff $C_y$
  appears in $C_x C_w C_z$ for some $x, z$). They biject with
  partitions $\lambda \vdash n$ via the RSK shape.
- **Left cells** within a two-sided cell $\lambda$ biject with
  standard Young tableaux $T \in \mathrm{SYT}(\lambda)$ via the
  $Q$-tableau.
- **Right cells** biject with $\mathrm{SYT}(\lambda)$ via the
  $P$-tableau.

A left cell $C_T \subset S_n$ is a basis for an irreducible
$H_n(q)$-module $V_T \cong S^\lambda$ (the Specht module of shape
$\lambda$) up to $q$-deformation. The decomposition
$\mathbb C[S_n] = \bigoplus_\lambda S^\lambda \otimes S^\lambda$
(Wedderburn) is **compatible with the two-sided cell decomposition**.

### 2.3 The cell poset $\le_{\mathrm{cell}}$

On partitions $\lambda \vdash n$, the cell poset is the dominance
order:

$$
\lambda \le_{\mathrm{cell}} \mu \iff \lambda \text{ dominates } \mu.
$$

This is also the closure order on Schubert-variety strata.

The KL machinery's natural inequalities are:

- $P_{y,w}(1) \ge 0$ (count multiplicities of irreducibles);
- chain identities along $\le_{\mathrm{cell}}$ (Lusztig's
  $a$-function, monotone along cells);
- Soergel bimodule character identities (Williamson Hodge).

None of these are sharp $1/m$ bounds.

### 2.4 Dual equivalence (Haiman; Assaf)

**Dual Knuth equivalence** on permutations $S_n$: generated by
$\ldots i+1 \ldots i \ldots i+2 \ldots \leftrightarrow \ldots i+2
\ldots i \ldots i+1 \ldots$ (and the symmetric variant).
Preserves $P$-tableau (and so $P$-shape); changes $Q$-tableau within
the same dual equivalence class.

**Dual equivalence graphs (DEGs)** (Assaf 2007, 2015): graphs on a
combinatorial set $\mathcal V$ with edges $E_i$ ($i \in [n-1]$)
satisfying local axioms (W1)–(W6) that force every connected
component to be isomorphic (as labeled graph) to the dual-equivalence
graph of $\mathrm{SYT}(\lambda)$ for some $\lambda$. Used to prove
Schur-positivity (e.g. of LLT polynomials, Macdonald polynomials at
$t=0$).

DEGs are the most natural Hecke-side home for **involutions on
combinatorial sets** — and the Brightwell exchange involution $\sigma$
is exactly such an object. This is the substantive Hecke/KL hook we
will probe in §3.3.

---

## 3. Candidate proof sketches

We examine four angles. Each subsection states the sketch, what would
need to be true for it to work, and the verdict against the criteria
in §1.3.

### 3.1 Sketch A — KL leading-coefficient inequality

**Idea.** Recast $\sum_{L' \in A}(f(L') - \bar f)$ as a character
evaluation on a sum of Specht modules. Apply Williamson positivity to
each Specht component to bound it.

**Setup.** View $\mathcal L(\alpha) \subset S_n$ (when $|\alpha|=n$).
The indicator $\mathbf 1_A$ extends to a function on $\mathbb C[S_n]$;
likewise $f : \mathcal L(\alpha) \to \mathbb Z$ extends by zero. The
inner product

$$
\langle \mathbf 1_A,\, f \rangle_{\mathbb C[\mathcal L(\alpha)]}
\;=\; \sum_{L' \in A} f(L')
$$

decomposes via the Specht-module decomposition
$\mathbb C[\mathcal L(\alpha)] \subset \mathbb C[S_n]
= \bigoplus_\lambda S^\lambda \otimes S^\lambda$ as

$$
\langle \mathbf 1_A, f \rangle \;=\;
\sum_\lambda \langle \pi_\lambda \mathbf 1_A,\, \pi_\lambda f \rangle,
$$

where $\pi_\lambda$ projects to the $S^\lambda$-isotypic component.
Per-$\lambda$ bounds would assemble into a global bound.

**What needs to be true.** A per-Specht-component sharp bound
$|\langle \pi_\lambda \mathbf 1_A, \pi_\lambda f \rangle - \text{centred}|
\le c_\lambda \cdot N/m$ with $\sum_\lambda c_\lambda \le 2$.

**Why it fails.**

(a) **No per-Specht Kahn–Saks bound exists in the literature.** The
known KL inequalities (Williamson positivity, $a$-function
monotonicity) are qualitative (non-negativity / monotonicity), not
sharp constants. The per-component norm bounds from
representation theory ($\|\pi_\lambda \mathbf 1_A\|_2 \le 1$, etc.)
give a Plancherel-type estimate
$|\langle \mathbf 1_A, f \rangle| \le \|\mathbf 1_A\|_2 \|f\|_2$,
which is the **weak centred bound** of `step8.tex:1042`
(`eq:weak-centred`) — already known to be insufficient.

(b) **The projection $\mathbb C[\mathcal L(\alpha)] \to S^\lambda$
does not preserve the centred-sum structure.** The centred quantity
$f(L') - \bar f$ has an additive structure tied to the *fibre* of
$\mathcal L(Q) \to \mathcal L(\alpha)$; Specht projection mixes the
$\bar f$-shift across components.

**Verdict.** RED. Sketch A is exactly the weak centred bound
(`eq:weak-centred`) plus Cauchy–Schwarz, which Brightwell §4
explicitly notes is **insufficient** for the sharp $2/m$ constant.

### 3.2 Sketch B — Two-sided cell-poset filtration

**Idea.** Filter $\mathcal L(\alpha) \subset S_n$ by RSK shape:
$\mathcal L(\alpha) = \bigsqcup_\lambda \mathcal L(\alpha)_\lambda$
where $\mathcal L(\alpha)_\lambda := \{L' \in \mathcal L(\alpha)
: \mathrm{RSK\text{-}shape}(L') = \lambda\}$. Bound the centred sum
within each $\mathcal L(\alpha)_\lambda$ using cell-restricted FKG.

**What needs to be true.**

(a) The exchange involution $\sigma$ respects the filtration:
$\sigma(\mathcal L(\alpha)_\lambda) = \mathcal L(\alpha)_\lambda$ for
each $\lambda$.

(b) Within each $\mathcal L(\alpha)_\lambda$, the per-term covariance
bound holds with constant $\bar f_\lambda / m$ where
$\sum_\lambda \bar f_\lambda |\mathcal L(\alpha)_\lambda| = \bar f N'$.

**Why it fails.**

(a) **$\sigma$ does NOT preserve RSK shape.** The exchange
involution $\sigma$ is a position-based local move on linear
extensions: it transposes adjacent elements of $L'$ to flip the
$(x,y)$ comparison while controlling pred/succ effect. This is a
single adjacent transposition (or a small product thereof) — and
adjacent transpositions in $S_n$ generically **change** the RSK
shape (only Knuth moves preserve $P$-tableau and so $P$-shape; the
Brightwell $\sigma$ is not a Knuth move).

Concrete check: take $\alpha = \{a, b\}$ antichain with $\mathrm{pred}
(z) = \{a\}$, $\mathrm{succ}(z) = \emptyset$, $x = b$, $y$
inserted... — even on $|\alpha|=2$, the swap $(a, b) \leftrightarrow
(b, a)$ moves between RSK shapes $(2)$ and $(1,1)$ (it changes the
descent set).

(b) Filtration by left cell (Q-tableau) is preserved by Knuth moves
but **not** by adjacent transpositions on the right.

(c) Filtration by right cell (P-tableau) is preserved by dual
Knuth moves but **not** by arbitrary single adjacent transpositions.

**Conclusion.** Neither the two-sided cell filtration nor the
left-cell / right-cell refinement is compatible with $\sigma$.
The cell-poset machinery is the wrong combinatorial decomposition
for this involution.

**Verdict.** RED.

### 3.3 Sketch C — Dual equivalence graph realization

**Idea.** Realize $\sigma$ as an involution in a dual equivalence
graph (DEG) on $\mathcal L(\alpha)$. The DEG axioms (W1)–(W6)
decompose $\mathcal L(\alpha)$ into dual-equivalence classes
isomorphic to $\mathrm{SYT}(\lambda)$-graphs; per-class bounds on the
centred sum then give a global bound.

**What needs to be true.**

(a) The Brightwell involution $\sigma$ is a *local* move (depends
only on a bounded neighbourhood of the swap location).
(b) $\sigma$ commutes with the DEG axioms in the appropriate sense.
(c) Per-class bounds on $\sum_{L' \in C} (f(L') - \bar f_C)$ for each
dual-equivalence class $C$ are available.

**Why it fails.**

(a) **$\sigma$ depends on $\mathrm{pred}(z)$ and $\mathrm{succ}(z)$,
which are not local.** The exchange involution flips $(x,y)$ and
"tracks pred/succ effect" — the pred-set and succ-set are global
data of $\alpha$, not a function of a fixed-size window around the
swap. DEG involutions, by contrast, must depend only on positions
$i-1, i, i+1, i+2$ around the move (Assaf axiom W1).

(b) **Even granting (a), per-class Kahn–Saks bounds are not in the
literature.** Assaf's DEG framework is designed to prove
*Schur-positivity* (non-negativity), not sharp-constant covariance
bounds. The DEG axioms guarantee structural decomposition; they do
not guarantee per-component quantitative estimates.

(c) **The constant $2/m$ comes from insertion-position averaging
on $\{1,\ldots,m\}$, not from a permutation-side structure.** This
is the deepest obstruction (see §3.5).

**Caveat — what Sketch C does buy.** *If* a specialist (Assaf,
Roberts, Lascoux) could realize $\sigma$ as an element of a
broader involution scheme (perhaps a "labeled DEG" with external
pred/succ data as edge weights), the resulting **vocabulary**
would be cleaner than the ad-hoc paper construction. The
sharp-constant arithmetic, however, would still need to be
imported from the Kahn–Saks insertion-position argument. Net: a
notational reformulation, not a new proof.

**Verdict.** RED for proof; AMBER for vocabulary-only
reformulation conditional on specialist input. Not portable in a
single polecat.

### 3.4 Sketch D — Soergel bimodule / categorification

**Idea.** Lift the centred-sum bound to a graded-dimension
inequality on Soergel bimodules. Apply Williamson's Hodge / Lefschetz
estimates.

**Why it fails.**

(a) **Soergel bimodules categorify the Hecke algebra at the level of
graded vector spaces**, not at the level of measure-theoretic
covariance estimates. The graded dimensions
$\dim_q \mathrm{Hom}(B_y, B_w) = \overline{P_{y,w}(q)}$ encode
combinatorics of Schubert varieties; they don't see the uniform
measure on $\mathcal L(\alpha)$.

(b) **The constant $2/m$ has no natural Soergel-bimodule home.** It
arises from averaging an indicator over a chain of length $m$, which
is a probability-space construction; Soergel theory is purely
algebraic / cohomological.

(c) **Research-scope.** Even if a Soergel-bimodule realization
existed, it would be multi-paper research level (Williamson,
Bezrukavnikov, Riche), far beyond polecat scope.

**Verdict.** RED.

### 3.5 The fundamental obstruction (m-averaging arithmetic)

The factor $1/m$ in $|\mathrm{Cov}_\mu(\mathbf 1_A, S)| \le \bar f/m$
comes from **insertion-position averaging on the fibre**
$\{1, \ldots, m\}$ in `step8.tex:1201–1216`, eq:cov-as-mu:

$$
\mathbb E_\nu[\mathbf 1_{B_-} \mid L'] = P(L')/m,
\quad
\mathbb E_\nu[\mathbf 1_{B_+} \mid L'] = (m - S(L'))/m.
$$

The $1/m$ is the **uniform probability of any single insertion
position**, multiplied by the integer $P(L')$ or $m-S(L')$. This
arithmetic is **fibre-level** — it depends on the chain
$\{1,\ldots,m\}$ that indexes insertion ranks.

**Why this kills all four Hecke/KL sketches.** $H_n(q)$ and its
modules know about $S_n$ and its representations; they do **not** see
the fibre structure of $\mathcal L(Q) \to \mathcal L(\alpha)$ where
$Q = \alpha \sqcup \{z\}$ and the fibre is the chain
$\{1,\ldots,m=|\alpha|+1\}$ of insertion ranks for $z$. The Hecke
algebra acts on $\mathbb C[S_n]$ via Specht modules; the fibre is
external data.

Any KL-based derivation would need to **invent** the
$\{1,\ldots,m\}$-averaging step from scratch — at which point one is
re-deriving Brightwell's Step 5 (`step8.tex:1201–1244`) in different
vocabulary, with no shortcut to the constant 2/m.

---

## 4. Feasibility assessment

| Sketch | Delivers $2/m$? | Lean-portable? | Specialist needed? | Verdict |
|---|:-:|:-:|:-:|:-:|
| A KL leading-coef / Plancherel | NO (= weak centred) | ~600 LoC | no | RED |
| B Two-sided cell filtration | NO (σ breaks filtration) | n/a | no | RED |
| C Dual equivalence graphs | NO (vocabulary only) | $\ge 600$ LoC | yes (Assaf-class) | RED for proof; AMBER vocabulary |
| D Soergel bimodule | NO (no $1/m$ home) | n/a | yes (research-scope) | RED |

**No sketch closes the gap.** The dominant obstruction (§3.5) is
that the Hecke / KL machinery does not have a natural home for the
$\{1,\ldots,m\}$-fibre averaging that produces the sharp constant.

### 4.1 Scope-narrowing inherited from mg-5fe9 §4.4(d)

A separate but reinforcing problem: for the **bulk** of target
posets (general $\alpha$ of width 3, non-heap-realizable), there is
**no direct $H_n(q)$-module home for $\mathcal L(\alpha)$ at all**.
mg-5fe9 §4.4(d) is explicit:

> Arbitrary posets on $[n]$ — width-3 posets, layered $K$-posets
> of the OneThird formalization, etc. — are **not** the support of
> any Demazure module $V_w$ for general $P$.

So even if a Hecke/KL proof existed for the heap-realizable
(321-avoiding) subcategory, the **bulk of $\alpha$ in the OneThird
parameter range is not reachable** by the Hecke direction. The
axiom must hold for *arbitrary* finite $\alpha$, so any partial
Hecke-side coverage is insufficient.

### 4.2 Comparison with the direct port (mg-38cf, `docs/brightwell-port-scope.md`)

The direct combinatorial port via three polecats (§4.1 + 4.2 + 4.3 +
4.4; §4.5 + 4.6; §4.7 + 4.8 of the port scope) totals ~700–1100 LoC
and is sub-divisible into single-polecat chunks (mg-port-A / B / C).
This remains the only Lean-portable route to retire the axiom.

The Hecke/KL angle does **not** compete: even granting the AMBER
vocabulary reformulation under Sketch C, the LoC cost is comparable
or larger (the DEG infrastructure is not in mathlib), and the
sharp-constant arithmetic still has to be ported separately.

---

## 5. Numerical sanity

We verify the obstruction of §3.5 on a small case.

**Setup.** $\alpha = \{a, b\}$ antichain (so $|\alpha| = 2$, $m = 3$).
$\mathrm{pred}(z) = \{a\}$, $\mathrm{succ}(z) = \{b\}$, $x = a$,
$y = b$. Then $\mathcal L(\alpha) = \{(a,b), (b,a)\}$ with $N' = 2$.

For $L' = (a, b)$: $P(L') = \mathrm{pos}_{L'}(a) = 1$,
$S(L') = \mathrm{pos}_{L'}(b) = 2$, $f(L') = S - P = 1$.
For $L' = (b, a)$: $P = 2$, $S = 1$, $f = -1$ — but
$f \in \{1, \ldots, m\}$ by the paper's convention; this
configuration is excluded by the pred/succ-disjointness +
comparability requirement. Take instead $\mathrm{succ}(z) = \emptyset$
(so $S = m = 3$ always): $f((a,b)) = 3-1 = 2$, $f((b,a)) = 3-2 = 1$.
Then $N = 3$, $\bar f = 3/2$.

With $x = a$, $y = b$, $A = \{(a,b)\}$, $|A| = 1$,
$\sum_{L' \in A}(f(L') - \bar f) = 2 - 3/2 = 1/2$. RHS $= 2N/m = 2$.
Bound holds with slack.

**KL-side check.** The Specht decomposition of $\mathbb C[\{(a,b),
(b,a)\}] \cong \mathbb C[S_2]$ is
$S^{(2)} \oplus S^{(1,1)} = $ trivial $\oplus$ sign. The KL polynomial
$P_{1,s_1}(q) = 1$ (trivially). Williamson positivity gives only
$\langle \mathbf 1_A, \mathbf 1_A \rangle, \langle f, f \rangle \ge 0$
— no sharp $2/m$ content.

**Insertion-position average check.** The factor $1/m = 1/3$ enters
via $\mathbb E_\nu[\mathbf 1_{B_+} \mid L'] = (m-S(L'))/m$. For
$L' = (a,b)$: $(3-3)/3 = 0$ (no overshoot insertion possible since
$\mathrm{succ}(z) = \emptyset$). For $L'=(b,a)$: same. The $1/m$ is
arithmetic on the chain $\{1,2,3\}$ — visible directly, invisible
through KL.

**Cell-poset filtration check.** $S_2 = \{e, s_1\}$; both are in
their own left/right/two-sided cells. The exchange involution
$\sigma$ on this tiny example is $\sigma((a,b)) = (b,a)$ — a single
transposition. It moves between RSK shapes $(2)$ and $(1,1)$
(or equivalently between trivial and sign components). The cell
filtration is **not preserved** by $\sigma$, confirming §3.2's
obstruction even at $|\alpha|=2$.

This is concrete evidence — though tiny — for §3's verdicts.

---

## 6. Verdict

**RED.** The Hecke / KL polynomial direction does **not** provide a
candidate proof of `brightwell_sharp_centred`, and is not a viable
second axiom-elim path.

### 6.1 What this scoping rules out

(a) **No Hecke/KL identity delivers the sharp constant $2/m$.** The
constant arises from chain-averaging on the fibre $\{1,\ldots,m\}$
(§3.5), a structure not seen by $H_n(q)$ at any specialization.

(b) **The cell-poset filtration of mg-5fe9 §5.3(iv) is broken by the
exchange involution $\sigma$.** $\sigma$ changes RSK shape;
filtration by left / right / two-sided cells is incompatible.

(c) **Soergel-bimodule categorification is research-scope and does
not target this kind of inequality.** Williamson Hodge gives Hom-
space dimension bounds, not measure-theoretic covariance bounds.

### 6.2 What this scoping does NOT rule out

(d) **Vocabulary-only reformulation via dual equivalence graphs**
(Sketch C, §3.3) is plausible *if* the Brightwell exchange
involution were extended to a "labeled DEG" with pred/succ data as
edge labels. This would be a notational improvement, not a new
proof, and would require specialist input (Assaf, Lascoux–
Schützenberger circle). Not polecat-portable.

(e) The **direct Brightwell port** (mg-38cf,
`docs/brightwell-port-scope.md`) remains the only Lean-portable
route to retire the axiom. Three polecats, ~700–1100 LoC,
post-launch infrastructure.

### 6.3 Why RED rather than AMBER

A direction is AMBER if it *exists* but requires specialist input
to realize. The Hecke / KL direction here fails at the level of
**fundamental arithmetic** (§3.5 m-averaging obstruction), not at
the level of specialist labour. Even with unlimited specialist
input, the algebra-level structures of $H_n(q)$ do not have a
fibre-averaging primitive that produces $1/m$ constants. The
obstruction is structural, not pragmatic.

This contrasts with mg-5fe9's overall verdict (AMBER-specialist for
the manifesto-level constraint emergence direction), which has
genuine literature support (Norton 1979, Carter 1986, Krob–Thibon
1997, Reiner–Shimozono 1998, Mason 2009). The mg-5fe9 §5.3(iv)
sub-question evaluated here is **the one item in mg-5fe9 that
turned out to be RED on closer examination** — the rest of mg-5fe9's
verdicts stand.

### 6.4 Recommended next actions (PM-level)

1. **PM does NOT file an execution ticket** for a Hecke/KL-based
   port of `brightwell_sharp_centred`. The direction is RED.
2. **PM updates the `lean/AXIOMS.md` "Status" entry** for
   `brightwell_sharp_centred` to note that the Hecke / KL candidate
   has been scoped (this doc, mg-e396) and rejected. The "retain
   the axiom" decision (mg-b699) stands; the direct port (mg-38cf)
   remains the only Lean route.
3. **No new project axioms.** This scoping introduces nothing. The
   OneThird trust surface is unchanged.
4. **The sibling Q1 scoping** (mg-4e67, `compat-geom-cell-poset`)
   examining the cell-poset / width-stratification question
   (mg-5fe9 §5.3(ii)) is a separate angle and is **not** subsumed
   by this RED verdict. Q1 and Q3 are independent.
5. **mg-5fe9's overall AMBER-specialist-trending-GREEN verdict for
   the manifesto direction is unaffected.** §5.3(iv) was one of
   four new questions raised; only this one is rejected on closer
   look.

---

## 7. References

### 7.1 OneThird-internal load-bearing pointers

- `lean/AXIOMS.md` — `brightwell_sharp_centred` entry (mg-134c
  introduction; mg-a6a1 faithfulness QA; mg-b699 retain decision).
- `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean` — the
  axiom statement.
- `step8.tex:1042–1281` — the paper derivation of
  `eq:sharp-centred` from FKG/AD + per-term Kahn–Saks.
- `docs/brightwell-port-scope.md` (mg-38cf) — port scope audit;
  estimates ~700–1100 LoC across three polecats.
- `docs/compatibility-geometry-hecke-interpolation-scoping.md`
  (mg-5fe9) — predecessor scoping; §5.3(iv) raised the question
  this doc answers RED.
- `docs/compatibility-geometry-feasibility-scoping.md` (mg-c853) —
  manifesto-level feasibility; §4 cell-poset framing.

### 7.2 Brightwell / Kahn–Saks (paper proof of the axiom)

- Brightwell, G. (1999). *Balanced pairs in partial orders.*
  Discrete Math. **201**, 25–52. — §4, Thm 4.1 (per-term covariance
  bound); §3.5.1 (τ-inversion distributive lattice).
- Kahn, J.; Saks, M. (1984). *Balancing poset extensions.* Order
  **1**, 113–126. — Lemma 2.2 (single-element perturbation).
- Ahlswede, R.; Daykin, D. E. (1978). *An inequality for the weights
  of two families of sets.* Z. Wahrsch. Verw. Gebiete **43**,
  183–185.
- Fortuin, C. M.; Kasteleyn, P. W.; Ginibre, J. (1971).
  *Correlation inequalities on some partially ordered sets.* Comm.
  Math. Phys. **22**, 89–103.

### 7.3 Hecke algebras and Kazhdan–Lusztig theory

- Kazhdan, D.; Lusztig, G. (1979). *Representations of Coxeter
  groups and Hecke algebras.* Invent. Math. **53**, 165–184.
- Lusztig, G. (1985). *Cells in affine Weyl groups.* Adv. Stud.
  Pure Math. **6**, 255–287.
- Geck, M.; Pfeiffer, G. (2000). *Characters of finite Coxeter
  groups and Iwahori–Hecke algebras.* LMS Monographs (NS) 21.
- Williamson, G. (2014). *Schubert calculus and torsion explosion.*
  J. Amer. Math. Soc. **30** (2017), 1023–1046 (with appendices by
  Williamson, Kontorovich, McNamara). — KL positivity in type A.
- Elias, B.; Williamson, G. (2014). *The Hodge theory of Soergel
  bimodules.* Ann. of Math. (2) **180**, 1089–1136.

### 7.4 Dual equivalence and DEGs

- Haiman, M. (1992). *Dual equivalence with applications, including
  a conjecture of Proctor.* Discrete Math. **99**, 79–113.
- Assaf, S. (2015). *Dual equivalence graphs I: A new paradigm for
  Schur positivity.* Forum Math. Sigma **3**, e12.
- Assaf, S. (2018). *Dual equivalence graphs and a combinatorial
  proof of LLT and Macdonald positivity.* Trans. Amer. Math. Soc.
  **370**, 8777–8804.

### 7.5 Combinatorics of linear extensions

- Stanley, R. P. (1986). *Two poset polytopes.* Discrete Comput.
  Geom. **1**, 9–23.
- Stembridge, J. R. (1996). *On the fully commutative elements of
  Coxeter groups.* J. Algebraic Combin. **5**, 353–385.
- Brightwell, G. R.; Felsner, S.; Trotter, W. T. (1995). *Balancing
  pairs and the cross product conjecture.* Order **12**, 327–349.

---

## 8. Token-budget report

- Cap: 300k tokens (per ticket §6).
- Document length: ~480 lines / ~22k characters / ~6k tokens of
  written content.
- Total token spend (this session): well under cap. Three Lean /
  step8.tex / predecessor doc reads (each ~1–4k tokens of context),
  one outline draft, one writeup pass.
- No Lean changes; no `lake build` runs; no execution-side cost.
- No new axioms.

This scoping definitively answers mg-5fe9 §5.3(iv) RED. The Q3
candidate-proof angle is closed.
