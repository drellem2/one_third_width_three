# Compatibility Geometry — cell-poset ↔ width-stratification scoping (mg-4e67)

**Companion to** `docs/compatibility-geometry-manifesto.md` (Daniel's
manifesto, 2026-05-12, mg-c853 at `0d8f438`),
`docs/compatibility-geometry-feasibility-scoping.md` (mg-c853, AMBER-
specialist verdict),
`docs/compatibility-geometry-pathP3-scoping.md` (mg-9d6c at `9526cf4`,
AMBER-narrow, applied axiom-narrowing angle), and
`docs/compatibility-geometry-hecke-interpolation-scoping.md` (mg-5fe9
at `a32fe64`, AMBER-specialist trending GREEN, foundational angle).
This document follow-up-scopes the **first crisp open question** that
mg-5fe9 left on the table:

> §5.3(ii) **Cell poset as intrinsic invariant.** The KL two-sided
> cell poset of $S_n$ is a single, canonical, algebra-intrinsic poset
> that organizes the entire Specht / Demazure decomposition.
> *Whether this cell poset has a direct relation to the
> width-stratification of OneThird is **OPEN** — a possible follow-up
> question.*
> — `mg-5fe9 §5.3(ii)` (verbatim)

The scoping addresses:

> Does the Kazhdan-Lusztig cell structure of $S_n$ naturally encode
> the width-stratification of posets on $[n]$? Is there a natural
> bijection (or surjection / injection / functorial map) between KL
> cells and width-stratified poset families?
> — `mg-4e67 §2` (paraphrase)

LaTeX is used inline ($\ldots$ / display) throughout; render with
KaTeX/MathJax or read source.

**Verdict preview.** **AMBER-clarifying, trending GREEN-clarifying.**
The map $P \mapsto \lambda(P)$ (Greene partition $\to$ two-sided KL
cell) is the **canonical algebra-intrinsic shadow** of a poset, and
it satisfies the *clean identity*

$$
\mathrm{width}(P) \;=\; \ell\bigl(\lambda(P)\bigr) \;=\;
\text{number of rows of the cell label}
$$

(Greene 1976; Schensted 1961). The width-stratification
$\mathrm{Pos}^{w \le 1} \subset \mathrm{Pos}^{w \le 2} \subset
\mathrm{Pos}^{w \le 3} \subset \cdots$ on posets therefore pulls
back from the **row-count stratification** of cells, and the cell
preorder $\le_{LR}$ (dominance order on partitions) is **monotone in
$\ell$** — so width-stratification is genuinely *cell-poset-respecting*.
However, the map is **strongly lossy** (cardinality mismatch:
$|\mathrm{Pos}_n| \gg p(n) = $ number of cells), **not functorial** under
poset morphisms, and **does not bypass** the load-bearing
expansion-$\Rightarrow$-balance step diagnosed as the manifesto's
core blocker (mg-c853 §3 Step 2, reaffirmed by mg-9d6c and mg-5fe9).
The correspondence **clarifies which aspect of a poset is algebra-
intrinsic** (its Greene partition; hence its width) and which is
**imposed external structure** (everything finer than the Greene
partition).

---

## 1. Recap and motivation

### 1.1 What the prior scoping pipeline established

`mg-c853` (feasibility): four manifesto sub-targets pass *abstraction
transfer*; load-bearing open math is `§3 Step 2`
(expansion-$\Rightarrow$-balance, Garland-style high-dimensional-
expander spectral input). AMBER-specialist trending GREEN.

`mg-9d6c` (Path P3, applied angle): cube-enumeration narrows the
residual case-3 axiom on a strict sub-window ($K=4, w=1$ plus a $K=3$
sliver); bulk of the residual range routes back to the same FKG /
spectral blocker. AMBER-narrow.

`mg-5fe9` (Hecke interpolation, foundational angle): the family
$\mathcal{H} \to \mathbb{A}^1_q$ realizes constraint emergence
*intrinsically from the algebra* for the **heap subcategory** (321-
avoiding permutations) and its Lascoux-Schützenberger labeled
extensions. The four mg-c853 Galois candidates (G1 heap, G2 Specht,
G3 chamber, G4 parabolic) unify as specializations of one family.
AMBER-specialist trending GREEN. §5.3(ii) names the **cell-poset ↔
width-stratification question** as a crisp open follow-on.

### 1.2 Why the cell-poset question matters

Three reasons:

(a) The KL **two-sided cell poset** is the cleanest "intrinsic poset
of $S_n$" — defined entirely in terms of the algebra (KL basis,
$\le_{LR}$ preorder, RSK shape), without any choice of external
poset-on-$[n]$ data. If width-stratification correspondences to a
cell-poset feature, then width is algebra-intrinsic in the
manifesto's Principle-5 sense.

(b) The mg-5fe9 heap reading is *width-2 only* — Stembridge heaps live
inside the 321-avoiding subcategory, which by Schensted (1961) has
RSK shape of length $\le 2$. The OneThird headline target is
*width 3*. A *direct* cell-side reading of width-3 (not via heaps)
would unblock the manifesto's reach into OneThird's parameter range.

(c) The cell preorder $\le_{LR}$ is a *poset on a finite set of size
$p(n)$* (number of partitions of $n$). If this poset matches
width-stratification, then OneThird's combinatorial parameter
hierarchy becomes a hierarchy *internal to representation theory of
$S_n$* — a substantial conceptual gain.

### 1.3 The question, stated precisely

We seek a "natural" function

$$
\Phi : \mathsf{Pos}_n \;\longrightarrow\; \mathsf{Cells}(S_n)
$$

(where $\mathsf{Pos}_n$ is posets on $[n]$ up to isomorphism and
$\mathsf{Cells}(S_n) \cong \{\lambda \vdash n\}$ is the set of two-
sided KL cells), satisfying:

**(N1)** **Width-compatibility.** $\mathrm{width}(P)$ is recovered
from $\Phi(P)$ (some statistic on cells).

**(N2)** **Monotonicity.** Width-stratification
$\mathsf{Pos}^{w \le k}_n$ pulls back from a *cell-side*
stratification, with cell preorder $\le_{LR}$ compatible.

**(N3)** **Intrinsicness.** $\Phi$ is defined by the
algebra/cell structure alone (or by a canonical poset invariant) —
not by external choice.

Whether $\Phi$ is a bijection / surjection / injection / something
weaker is the question to resolve.

---

## 2. Background

### 2.1 Two-sided KL cells of $S_n$ (recap)

The KL basis $\{C_w\}_{w \in S_n}$ defines a preorder $\le_{LR}$:

$$
y \;\le_{LR}\; w \;\;\iff\;\; \exists\, x, z \in S_n :\;
C_y \text{ appears with nonzero coefficient in } C_x \, C_w \, C_z.
$$

The equivalence classes for the symmetric closure of $\le_{LR}$ are
the **two-sided cells**. The induced partial order on cells is the
**cell poset** $\bigl(\mathsf{Cells}(S_n), \le_{LR}\bigr)$.

**Theorem (KL 1979 §4; type $A$ via RSK).** Two-sided cells of $S_n$
are indexed by partitions $\lambda \vdash n$: $w$ is in the cell
$c(\lambda)$ iff $\mathrm{RSK}(w) = (P_w, Q_w)$ with
$\mathrm{sh}(P_w) = \mathrm{sh}(Q_w) = \lambda$. The cell preorder is:

$$
c(\lambda) \;\le_{LR}\; c(\mu) \;\;\iff\;\; \mu \;\trianglelefteq\;
\lambda \;\;\text{(dominance order, } \lambda \text{ dominates } \mu).
$$

(See Geck-Pfeiffer §6, Mathas §1.4 for the type-$A$ specialization;
the dominance convention here matches mg-5fe9 §4.3.)

**Cardinalities.** $|c(\lambda)| = (f^\lambda)^2$ where $f^\lambda =
|\mathrm{SYT}(\lambda)|$. The cell poset has
$|\mathsf{Cells}(S_n)| = p(n)$ elements: $p(3) = 3$, $p(4) = 5$,
$p(5) = 7$, $p(6) = 11$, $p(7) = 15$, $p(8) = 22$, $p(9) = 30$,
$p(10) = 42$.

### 2.2 The $a$-function

**Definition (Lusztig 1985).** $a : S_n \to \mathbb{Z}_{\ge 0}$ is
constant on two-sided cells. For type $A$:

$$
a\bigl(c(\lambda)\bigr) \;=\; n(\lambda) \;:=\;
\sum_{i \ge 1} (i-1) \lambda_i.
$$

Interpretation: $n(\lambda)$ is the *number of inversions in the
column-superstandard tableau* of shape $\lambda$, equivalently the
*degree* in the Hilbert series of the coinvariant algebra restricted
to the $\lambda$-isotypic component (Lusztig, Garsia-Procesi). The
$a$-function is monotone in the cell poset: $\lambda \trianglelefteq
\mu \;\Rightarrow\; n(\lambda) \le n(\mu)$ (well-known; Macdonald
§I.1).

### 2.3 Greene's theorem and the Greene partition of a poset

**Definition (Greene 1976; Greene-Kleitman 1976).** For a finite
poset $P$, define $\lambda(P) \vdash |P|$ by the conjugate identities

$$
\sum_{i=1}^k \lambda(P)_i \;=\; \max\Bigl\{\,
\bigl|C_1 \cup \cdots \cup C_k\bigr|\,:\, C_i \text{ pairwise chains in } P \Bigr\}, \;\;
$$

$$
\sum_{i=1}^k \lambda(P)'_i \;=\; \max\Bigl\{\,
\bigl|A_1 \cup \cdots \cup A_k\bigr|\,:\, A_i \text{ pairwise antichains in } P \Bigr\}.
$$

**Theorem (Greene 1976).** $\lambda(P)$ is a *partition* (the two
formulas above are conjugate in the sense
$\lambda'_i = |\{j : \lambda_j \ge i\}|$), and it is the *unique*
such partition realizing both extremal families simultaneously.

**Corollary.**

$$
\mathrm{height}(P) \;=\; \lambda(P)_1 \;\;\text{(longest chain)}, \;\;
\mathrm{width}(P) \;=\; \lambda(P)'_1 \;=\; \ell(\lambda(P))
\;\;\text{(longest antichain)}.
$$

### 2.4 Schensted's theorem (special case for permutations)

For a permutation $w \in S_n$, view $w$ as the poset $P_w$ on $[n]$
with $i <_{P_w} j \iff i < j$ and $w(i) < w(j)$ (the **inversion
poset** / "type-A natural labeling"). Then:

**Theorem (Schensted 1961).**
$\lambda(P_w) = \mathrm{sh}(\mathrm{RSK}(w))$.
Explicitly: $\lambda(P_w)_1 = \mathrm{LIS}(w)$,
$\lambda(P_w)'_1 = \mathrm{LDS}(w) = \ell(\lambda(P_w))$.

**Schensted-pattern corollary.** $w$ is $(k{+}1, k, k{-}1, \ldots, 2,
1)$-pattern-avoiding $\iff \mathrm{LDS}(w) \le k \iff
\ell(\lambda(\mathrm{RSK}(w))) \le k$.

Specialized:

- $k = 2$: $w$ is **321-avoiding** $\iff \mathrm{LDS}(w) \le 2 \iff$
  cell $c(\lambda)$ has $\ell(\lambda) \le 2$. This is the
  **fully commutative subcategory** = Stembridge heaps = mg-5fe9 §4.2.
- $k = 3$: $w$ is **4321-avoiding** $\iff \mathrm{LDS}(w) \le 3 \iff$
  cell $c(\lambda)$ has $\ell(\lambda) \le 3$. *This is the
  "width-3 candidate subcategory" of $S_n$.* It is **strictly larger**
  than the heap (321-avoiding) subcategory: $|\mathrm{Av}(4321,n)|
  / |\mathrm{Av}(321,n)| \to \infty$ as $n \to \infty$ (West, Bóna).

### 2.5 Dominance order monotonicity

**Fact.** For partitions $\lambda, \mu$ of the same $n$,

$$
\lambda \trianglelefteq \mu \;\;\Longrightarrow\;\;
\ell(\lambda) \ge \ell(\mu).
$$

(Macdonald §I.1, (1.11); equivalently $\lambda'_1 \ge \mu'_1$
follows directly from $\sum_{i \le 1} \lambda_i \le \sum_{i \le 1}
\mu_i$ via conjugation.)

Translating to cells via §2.1: $c(\lambda) \le_{LR} c(\mu) \Rightarrow
\ell(\lambda) \ge \ell(\mu)$. The **cell poset is monotone-decreasing
in $\ell$**: larger cells (in $\le_{LR}$) have *fewer* rows.

The unique minimum cell $c\bigl((n)\bigr)$ (containing only the
identity $e$ at $q = 1$ side, the trivial representation) has
$\ell = 1$. The unique maximum cell $c\bigl((1^n)\bigr)$ (containing
the longest element $w_0$, the sign representation) has $\ell = n$.

---

## 3. The candidate correspondence

### 3.1 The Greene cell map

**Definition 3.1 (Greene cell map).** Let

$$
\Phi : \mathsf{Pos}_n \;\longrightarrow\; \mathsf{Cells}(S_n),
\qquad
P \;\longmapsto\; c\bigl(\lambda(P)\bigr).
$$

Here $\lambda(P)$ is the Greene partition (§2.3) and $c(\lambda)$ is
the two-sided KL cell of shape $\lambda$ (§2.1). $\Phi$ is
well-defined on isomorphism classes (Greene partition is iso-invariant).

### 3.2 Width-compatibility (N1)

**Proposition 3.2.** $\mathrm{width}(P) = \ell\bigl(\lambda(\Phi(P))\bigr) =
\ell\bigl(\lambda(P)\bigr)$.

**Proof.** Immediate from §2.3 Corollary. $\square$

This realizes **(N1)** cleanly: width is recovered from $\Phi(P)$ as
the number of rows of the cell label. In particular:

$$
\Phi\bigl(\mathsf{Pos}^{w \le k}_n\bigr) \;=\;
\{ c(\lambda) \,:\, \ell(\lambda) \le k \}.
$$

The width-$\le 3$ subcategory of $\mathsf{Pos}_n$ pulls back from
the **first three rows** of the cell-set partition.

### 3.3 Monotonicity (N2)

**Proposition 3.3.** Define the **width-stratification** on cells
by $\mathsf{Cells}^{\ell \le k}(S_n) := \{c(\lambda) : \ell(\lambda)
\le k\}$. Then:

(a) Each $\mathsf{Cells}^{\ell \le k}$ is an **upward-closed**
subset of the cell poset $(\mathsf{Cells}(S_n), \le_{LR})$. That is:
$c(\lambda) \in \mathsf{Cells}^{\ell \le k}$ and $c(\lambda) \le_{LR}
c(\mu) \;\Rightarrow\; c(\mu) \in \mathsf{Cells}^{\ell \le k}$.

(b) The chain
$\mathsf{Cells}^{\ell \le 1} \subset \mathsf{Cells}^{\ell \le 2} \subset
\cdots \subset \mathsf{Cells}^{\ell \le n}$ is a *cell-poset-respecting*
filtration of $\mathsf{Cells}(S_n)$.

**Proof.** (a) follows from §2.5: $c(\lambda) \le_{LR} c(\mu) \iff
\mu \trianglelefteq \lambda \;\Rightarrow\; \ell(\mu) \ge
\ell(\lambda)$. Wait — this is the *opposite* direction. Let us redo
the bookkeeping carefully.

By the §2.1 convention,
$c(\lambda) \le_{LR} c(\mu) \iff \mu \trianglelefteq \lambda$.
By §2.5, $\mu \trianglelefteq \lambda \Rightarrow \ell(\mu) \ge
\ell(\lambda)$. So $c(\lambda) \le_{LR} c(\mu) \Rightarrow
\ell(\lambda) \le \ell(\mu)$: **smaller cells (in $\le_{LR}$) have
fewer rows**. Thus the "downward-closed" sets are
$\mathsf{Cells}^{\ell \le k}$ — i.e., $\le_{LR}$-down-sets, the
*order ideals* of the cell poset. (a) holds with **downward-closed**
substituted for upward-closed; (b) holds verbatim.

The corrected statement: **the width-stratification of cells is
precisely the chain of $\le_{LR}$-order-ideals
$\{c(\lambda) : \ell(\lambda) \le k\}$, $k = 1, 2, \ldots, n$.** $\square$

This realizes **(N2)** strongly: width-stratification is not just
*compatible* with the cell poset; it is **a canonical chain of
order ideals**. The cell-poset structure refines width.

### 3.4 Intrinsicness (N3)

The Greene partition $\lambda(P)$ is **intrinsic** to the poset
$P$ in the strictest sense: it is defined by chain/antichain
extremals, which are isomorphism invariants. The cell label
$c(\lambda)$ is intrinsic to the *algebra* $\mathbb{C}[S_n]$ (defined
by KL basis $\le_{LR}$). The composite $P \mapsto c(\lambda(P))$
involves *no choices* — no marking of basepoints, no labeling of
elements, no fundamental groupoid.

This realizes **(N3)** cleanly. By contrast, the mg-5fe9 Hecke
constructions (Demazure modules, key polynomials) require a choice
of $w \in S_n$ — they are intrinsic to $\mathcal{H}$ but not
canonically to a poset-on-$[n]$. The Greene map needs no such
intermediary.

### 3.5 Refinement: $a$-function as finer invariant

The cell poset is *not* a total order; cells are partially ordered
by dominance. The $a$-function (§2.2) collapses the cell poset to
a *linear order on values*:

$$
a\bigl(c(\lambda)\bigr) \;=\; n(\lambda) \;=\; \sum_{i \ge 1} (i-1)\lambda_i.
$$

For width-$k$ posets ($\ell(\lambda(P)) = k$, $\lambda(P) = (\lambda_1,
\ldots, \lambda_k)$):

$$
a\bigl(\Phi(P)\bigr) \;=\; \lambda_2 + 2\lambda_3 + \cdots + (k-1)\lambda_k.
$$

For width $1$ (chains, $\lambda = (n)$): $a = 0$.
For width $2$ ($\lambda = (n-r, r)$ with $1 \le r \le n/2$):
$a = r$.
For width $3$ ($\lambda = (a, b, c)$ with $a \ge b \ge c \ge 1$,
$a+b+c=n$): $a = b + 2c$.

**Observation 3.4.** $a$ is *not* a function of width alone — width-3
posets can have $a$ ranging from a minimum (e.g., $\lambda = (n-2, 1,
1)$, $a = 3$) to a maximum (e.g., $\lambda = (\lceil n/3 \rceil,
\lceil n/3 \rceil, \lfloor n/3 \rfloor)$, $a \approx n$ for large $n$).
The $a$-function is a *finer* invariant than width, encoding
how "balanced" the partition shape is.

**Manifesto resonance.** The $a$-function is precisely the kind of
graded "depth" that Principle 4 names ("non-expansion signals
dimensional collapse"): high $a$ corresponds to wide-and-deep cells,
low $a$ to chain-like cells. *Whether $a$ correlates with the
spectral gap $\lambda(P)$ (the manifesto's expansion invariant,
mg-c853 §2.4) is OPEN* — see §6.3.

### 3.6 Cell representatives via Duflo involutions

**Definition (Duflo 1985, Lusztig).** A **Duflo involution** of
$S_n$ is an involution $d \in S_n$ ($d^2 = e$) with the property
that $d$ is the unique involution in its left cell.

**Theorem (Lusztig).** Each left cell of $S_n$ contains a unique
Duflo involution. Each two-sided cell $c(\lambda)$ contains exactly
$f^\lambda$ Duflo involutions (one per left cell of shape $\lambda$).
These are *exactly the involutions of RSK shape $\lambda$*.

For each $\lambda \vdash n$, the Duflo involutions in $c(\lambda)$
are a canonical *finite* set of representatives of the cell. Their
inversion posets are width-$\ell(\lambda)$ posets on $[n]$.

**Candidate dual map.**

$$
\Psi : \mathsf{Cells}(S_n) \;\longrightarrow\; \mathsf{Pos}_n, \qquad
c(\lambda) \;\longmapsto\; \{ P_d : d \text{ Duflo involution of shape } \lambda \}.
$$

This is a *multi-valued* map (each cell yields $f^\lambda$ Duflo
posets). The Greene cell map $\Phi$ and the Duflo map $\Psi$
satisfy:

$$
\Phi \circ \Psi \;=\; \mathrm{id}_{\mathsf{Cells}}, \qquad
\Psi \circ \Phi \;=\; \text{"Duflo closure"} \subseteq \mathsf{Pos}_n.
$$

(The first identity: $\Psi(c(\lambda))$ are involutions of shape
$\lambda$, so $\Phi(P_d) = c(\lambda(P_d)) = c(\mathrm{RSK}(d)) =
c(\lambda)$ — Schensted §2.4 applied to involutions. The second:
$\Psi \circ \Phi$ replaces $P$ by the set of Duflo posets of
shape $\lambda(P)$, which is a strict, *small*, canonical subset of
$\{Q \in \mathsf{Pos}_n : \lambda(Q) = \lambda(P)\}$.)

**Honest assessment.** Duflo involutions provide a **canonical
finite witness set** for each cell — exactly the "two-sided cell
representatives serve as canonical width-stratification elements"
candidate the ticket §2 names. But they are **not unique** ($f^\lambda$
of them per cell), and the inversion poset $P_d$ for an involution
$d$ is a *very specific* type of poset (a "self-conjugate" / centrally
symmetric subposet of $\mathbb{N}^2$). Generic width-3 posets are
**not** Duflo inversion posets.

---

## 4. Honest assessment of the correspondence

### 4.1 What the map $\Phi$ does

(i) Sends $P \mapsto c(\lambda(P))$ canonically (no choices).

(ii) Realizes $\mathrm{width}(P) = \ell(\lambda(\Phi(P)))$ (clean
identity, §3.2).

(iii) Pulls back width-stratification to a *canonical chain of
cell-poset order ideals* (§3.3).

(iv) Is **algebra-intrinsic** in the sense of manifesto Principle 5:
both source and target are defined without external structure.

### 4.2 What the map $\Phi$ does NOT do

(v) **$\Phi$ is strongly lossy.** Cardinality mismatch:

$$
|\mathsf{Pos}_n| \;\gg\; p(n) \;=\; |\mathsf{Cells}(S_n)|.
$$

For $n = 8$: $|\mathsf{Pos}_8| = 16{,}999$ (OEIS A000112), $p(8) =
22$. The map has fibers of average size $\sim 773$ posets per cell.
For width-$\le 3$ posets specifically, $|\mathsf{Pos}^{w \le 3}_8|$
is in the hundreds while $|\{c(\lambda) : \ell(\lambda) \le 3\}|
= 8$ (partitions of 8 with at most 3 parts).

(vi) **$\Phi$ is not a bijection.** Even restricted to *connected* /
*irreducible* / *fence* / any natural subcategory of $\mathsf{Pos}_n$,
$\Phi$ is not injective.

(vii) **$\Phi$ is not functorial in any natural sense.** Greene
partition is *not* well-behaved under poset morphisms: a surjective
poset map $P \twoheadrightarrow Q$ does **not** induce a relation
between $\lambda(P)$ and $\lambda(Q)$ comparable in dominance.
Counter-example: the antichain on 3 elements has $\lambda = (1,1,1)$,
its quotient to a 2-element antichain has $\lambda = (1,1)$ — but
$(1,1,1) \not\trianglerighteq (1,1)$ (different $n$). For poset
*embeddings* $P \hookrightarrow Q$ with $|P| = |Q|$ (i.e., $P$ has
more relations than $Q$), one *does* get $\lambda(Q) \trianglelefteq
\lambda(P)$ — but this is a *restriction* of the cell map to
"poset refinement," not full functoriality.

(viii) **The fiber over each cell is heterogeneous.** Posets with
the same Greene partition can differ wildly in:

- **Linear-extension count.** $\lambda(P) = (n-1, 1)$ admits posets
  with $|\mathcal{L}(P)|$ ranging from $n$ (a chain plus one
  incomparable) up to ${n \choose 2}$.
- **Spectral gap of $G_P$** (mg-c853 §2.4). Same $\lambda(P)$, very
  different mixing time.
- **Number of antichains.** Greene's theorem records *maximum*
  antichain sizes, not the full antichain count.

(ix) **The map dissolves the OneThird parameter range.** OneThird's
residual axiom is *layered* width-3 (`L.K \ge 3`,
$|M_i| \le 3$, Case 3 enumeration). All layered width-3 posets of the
same size and partition shape $\lambda(P)$ get sent to the same cell.
The layered structure — *the* combinatorial feature OneThird's Step 8
exploits — is invisible to $\Phi$.

### 4.3 The full picture

$\Phi$ is best understood as a **projection** $\mathsf{Pos}_n
\twoheadrightarrow \mathsf{Cells}(S_n)$ recording the
*coarsest algebra-intrinsic invariant* of a poset. It is the right
language for:

- **Width-stratification at the partition level** (the question
  this scoping asks; answered YES).
- **Algebra-intrinsic invariants that depend only on the Greene
  partition** (a small but interesting class: $a$-function, KL
  cell representation, dimension of associated Specht module).

It is the **wrong language** for:

- Anything that depends on the full poset structure beyond
  $\lambda(P)$.
- OneThird's residual `case3` axiom (which is *layered*-structure-
  specific).
- Linear-extension probabilities such as the headline
  $\Pr[\sigma^{-1}(a) < \sigma^{-1}(b)] \in [1/3, 2/3]$.

This is the **same load-bearing scope-narrowing pattern** as
mg-5fe9 §4.4 (d): the algebra realizes constraint emergence at a
*specific level of resolution*, and OneThird's headline lives at
a *finer* level requiring external (non-algebra-intrinsic)
structure.

---

## 5. Connection to OneThird and to the mg-5fe9 §5.3(ii) question

### 5.1 Resolving §5.3(ii) of mg-5fe9

mg-5fe9 §5.3(ii) posed:

> **Whether this cell poset has a direct relation to the
> width-stratification of OneThird is OPEN.**

**This scoping's answer.** YES at the partition level (§3.2, §3.3):
$\mathrm{width}(P) = \ell(\lambda(P))$ and the width-stratification
is a canonical chain of cell-poset order ideals. The relation is
clean, classical (Greene 1976; Schensted 1961), and *fully
algebra-intrinsic*.

NO at the layered-poset level: the OneThird `case3` residual is
layered-$K$-width-$w$-structure-specific, and the layered structure
is invisible to $\Phi$.

The mg-5fe9 heuristic — "width-$w$ posets of $[n]$ might correspond
to cells of small partition shape $\lambda$, where $w \approx
\ell(\lambda)$" — is now made *precise* as the **equality
$\mathrm{width}(P) = \ell(\lambda(P))$**. The "heuristic" $\approx$
is in fact $=$ (Greene's theorem).

### 5.2 OneThird headline in cell language

The OneThird headline `width3_one_third_two_thirds` lives over
$\mathsf{Pos}^{w \le 3}_n = \Phi^{-1}\bigl(\mathsf{Cells}^{\ell \le 3}\bigr)$.
On the *cell side*, this is the union of three cells per partition
shape with $\le 3$ parts: $\lambda = (n), (n{-}r, r), (a, b, c)$.

This re-presentation says: **the headline target is "balanced pair
exists for any preimage of any cell with $\le 3$ rows."** The
cell language **does not give a new proof** because the proof depends
on the full preimage fiber — i.e., on the layered structure of
specific posets, not on the partition $\lambda(P)$ alone.

### 5.3 The Step 2 spectral question, cell version

The mg-c853 §3 Step 2 blocker — expansion $\Rightarrow$ balance —
is restated:

**Step 2 (cell-stratified form, candidate).** *For
$P \in \mathsf{Pos}^{w \le 3}_n$ with $\lambda(\Phi(P)) = (a,b,c)$
($a + b + c = n$), and spectral gap $\lambda(G_P) \ge c_0 > 0$,
there exist incomparable $i, j \in P$ with
$\Pr_{\sigma \sim \mathcal{L}(P)}[\sigma^{-1}(i) < \sigma^{-1}(j)]
\in [1/3, 2/3]$.*

**Cell-language reformulation.** The Specht module $S^{\lambda(P)}$
of dimension $f^{\lambda(P)}$ is the *unique* $S_n$-irrep where
$\mathcal{L}(P)$ has nonzero projection (after suitable
normalization). The Specht projection $\Pi_{\lambda(P)} :
\mathbb{C}[\mathcal{L}(P)] \to S^{\lambda(P)}$ controls the
"balance" inner product. The Step 2 statement becomes a *coefficient
bound* in the Specht module of shape $\lambda(P)$.

**Honest verdict.** Same blocker as mg-5fe9 §5.2: the Hecke /
Specht / cell language **reshapes** Step 2 into a more functorial
statement (now phrased as a Specht-module coefficient bound,
$\le 3$ rows), but does **not bypass** it. The Garland-style
spectral expansion argument does not lift to Specht-module
coefficient bounds without external input.

### 5.4 What the cell-poset reading *does* deliver for OneThird

(I) **Confirms the manifesto Principle 5 narrowing.** Posets of width
$\le k$ are exactly the preimage of *cells of $\le k$ rows*. Width is
algebra-intrinsic (Greene); finer poset structure is not.

(II) **Identifies the cell label as the right "first-order invariant"
of a poset for compatibility-geometry analysis.** The Greene partition
$\lambda(P)$ is canonical; everything cell-side respects it.

(III) **Locates layered structure on the *fiber* side, not the
cell side.** OneThird's layered decomposition (LayeredReduction.lean,
`L.K`, $|M_i| \le 3$) operates *within* the fiber $\Phi^{-1}(c(\lambda))$,
selecting layered representatives. The mg-9d6c cube-enumeration
question (Path P3) is **fiber-specific**: it enumerates layered $K=4$
$w=1$ posets, all sharing the same cell label $c((n{-}3, 1, 1, 1))$
or similar.

(IV) **Suggests a "cell-by-cell" analysis program.** Each
$\le_{LR}$-minimal cell with $\ell(\lambda) = 3$ corresponds to a
*specific Specht-module / partition shape*. A cell-by-cell proof of
Step 2 — bound the Specht-module coefficient for each $\lambda$
with $\ell = 3$ — would be a genuinely new strategy. Whether it is
*easier* than the cube-enumeration / spectral routes is OPEN.

### 5.5 Cell-poset summary table

| Item | Cell-poset contribution | Status |
|------|-------------------------|--------|
| Width $\leftrightarrow$ row count | $\mathrm{width}(P) = \ell(\lambda(P))$ via Greene | **PRECISE** (Greene 1976; Schensted 1961) |
| Width-stratification $\leftrightarrow$ cell-poset filtration | Canonical chain of order ideals | **PRECISE** (Macdonald §I.1) |
| 4321-avoiding subcategory $\leftrightarrow$ width-3 | $w$ avoids 4321 $\iff \ell(\lambda(w)) \le 3$ | **PRECISE** (Schensted §2.4) |
| Bijection $\mathsf{Pos}_n \leftrightarrow \mathsf{Cells}$ | Strongly lossy (§4.2 (v)) | **FALSE** as bijection |
| Functoriality | None in natural sense (§4.2 (vii)) | **NEGATIVE** |
| Cell representatives via Duflo involutions | $f^\lambda$ per cell; not canonical singletons | **PARTIAL-PRECISE** |
| $a$-function $\leftrightarrow$ width | $a(\lambda)$ depends on more than $\ell(\lambda)$ | **NEGATIVE** (a finer invariant) |
| OneThird `case3` residual via cell label | Layered structure invisible; same Step 2 blocker | **NOT BRIDGED** (§5.3) |
| Cell-by-cell Specht analysis program | Specht coefficient bound per $\lambda$ with $\ell = 3$ | **NEW question raised** (§5.4 (IV)) |

---

## 6. Verdict

**AMBER-clarifying, trending GREEN-clarifying.**

### 6.1 Why AMBER not RED

The correspondence **exists, is canonical, and is mathematically
clean**. It is not vacuous, not a re-labeling, not a coincidence
of notation: it is the classical Greene-Schensted theorem applied
to the algebra-intrinsic cell labeling. The mg-c853 manifesto's
Principle 5 ("posets are the first canonical compatibility
geometries; they are Galois-closed systems of order constraints
on permutation space") is **precisified** by §3: the *width*
component of a poset is exactly the cell-row-count component of
the algebra; the *finer* poset structure is the imposed external
data. This is a genuine, non-trivial conceptual deliverable.

### 6.2 Why AMBER not GREEN

The correspondence is **strongly lossy** (§4.2) and **non-functorial**.
It does not deliver a bijection. It does not bridge mg-c853 §3
Step 2. For OneThird's headline target, it sits at the wrong
level of resolution: the Step 8 case-3 residual axiom is *layered*-
structure-specific, and layered structure lives in the fibers of
$\Phi$, not on the cell-poset itself.

### 6.3 Why trending GREEN-clarifying

(a) **The "intrinsic vs imposed" boundary is now drawn precisely.**
Manifesto Principle 5 was a general claim; this scoping makes it
sharp: *width is intrinsic (Greene); the rest is imposed*. This is
the cleanest statement of the manifesto's reach into poset
geometry produced to date.

(b) **The cell-by-cell Specht coefficient program (§5.4 (IV)) is a
new, focused, polecat-formalizable direction.** It does not bypass
Step 2 — but it *re-decomposes* Step 2 into $p_{\le 3}(n)$ separate
sub-statements indexed by partition shape, each in the
representation-theoretic language of Specht modules. Whether any
sub-statement is *easier* than the general statement is a focused
follow-up question (not for this scoping, but for a Daniel-
authorized successor).

(c) **The $a$-function $\leftrightarrow$ spectral-gap question**
(§3.5) is a *crisp testable conjecture*: does $a(\lambda(P))$
correlate with the spectral gap $\lambda(G_P)$? If yes, then the
manifesto's "non-expansion = dimensional collapse" (Principle 4)
gets a numerical instantiation. This is a *measurable* question:
for each $P \in \mathsf{Pos}^{w \le 3}_n$ for small $n$, compute
$a(\lambda(P))$ and the spectral gap of $G_P$, plot. Within polecat
scope.

### 6.4 What this scoping does NOT do

(d) **Does not bypass mg-c853 §3 Step 2.** Same load-bearing blocker
as mg-5fe9 §5.2. Cell language **reshapes** Step 2 into Specht-
module-coefficient language; does not close it.

(e) **Does not deliver new OneThird theorems.** No reduction in
axiom count, no new proof of `width3_one_third_two_thirds`, no
change to trust surface (4 named axioms + 5 `native_decide`).

(f) **Does not formalize anything at the Lean level.** Pure
scoping document; no Lean source touched. (The Greene partition,
Schensted's theorem, and Lusztig $a$-function would each be
mathlib-tier ports of substantial size — not polecat scope.)

(g) **Does not investigate the cell representative / Duflo-poset
correspondence in depth.** §3.6 raises but does not resolve the
"is the Duflo inversion poset a canonical width-stratification
element?" question. The Duflo inversion poset has *very specific*
structure (centrally symmetric) — not generic width-3.

### 6.5 Recommended next actions (PM-level)

1. **PM mails Daniel** with this verdict + the §6.1 clarification +
   §6.3(a) "intrinsic vs imposed" framing. The manifesto Principle 5
   text may benefit from a one-paragraph append noting that *the
   intrinsic content of a poset for compatibility-geometry purposes
   is its Greene partition*, with finer structure being imposed
   external data.

2. **Mark mg-5fe9 §5.3(ii) RESOLVED-CLARIFYING.** This scoping
   answers the open question with a precise YES-at-partition-level /
   NO-at-poset-level dichotomy. The mg-5fe9 doc need not be edited;
   this scoping is its companion answer.

3. **Daniel's call on follow-ups.**
   (a) **§3.5 $a$-function $\leftrightarrow$ spectral-gap empirical
   study.** Compute $a(\lambda(P))$ and $\lambda(G_P)$ for all
   width-$\le 3$ posets on $[n]$ for $n \le 9$ (small enough for
   exhaustive enumeration; $\le 10^3$ posets per parameter). Plot.
   Look for monotone correlation. 1 polecat session, ~300-500 LoC
   Python or Lean computation.
   (b) **§5.4 (IV) cell-by-cell Specht-coefficient program.**
   Investigate whether the Step 2 spectral-$\Rightarrow$-balance
   step is *uniform across cells* or *cell-specific*. If cell-specific:
   identify which cell shapes $\lambda$ with $\ell = 3$ are
   "hardest." Specialist scope; 2-3 polecat sessions.
   (c) **Duflo-inversion-poset enumeration (§3.6).** Enumerate Duflo
   involutions of shape $(a, b, c)$ for small $n$ and check whether
   their inversion posets contain layered $K = 4, w = 1$ patterns
   (mg-9d6c sub-window). 1 polecat session.
   (d) **Stay-as-is.** Park the cell-poset reading as a stable
   manifesto-clarification. No further investment.

4. **No new project axioms** are introduced by this scoping. No
   Lean source changes. The OneThird trust surface is unchanged at
   4 named project axioms + `native_decide` count.

### 6.6 Relation to mg-c853 §6.5 / mg-9d6c / mg-5fe9 verdict chain

The four compat-geom scoping docs now form a coherent picture:

- **mg-c853** (manifesto + feasibility): identifies the framework
  and the four sub-targets. AMBER-specialist trending GREEN.
- **mg-9d6c** (Path P3, applied): sub-GREEN executable on a strict
  axiom-narrowing sub-window. AMBER-narrow.
- **mg-5fe9** (Hecke interpolation, foundational): unifies four
  Galois candidates as specializations of one family; raises
  cell-poset and Brightwell-axiom follow-ons. AMBER-specialist
  trending GREEN.
- **mg-4e67** (this scoping, cell-poset $\leftrightarrow$ width):
  resolves mg-5fe9 §5.3(ii) with precise YES-at-partition-level
  answer; clarifies "intrinsic vs imposed" boundary.
  AMBER-clarifying trending GREEN-clarifying.

A separate `compat-geom` repo (mg-c853 §6.5, mg-5fe9 §6.6) is now
better-justified: four scoping docs constitute a small, coherent,
laterally-organized research-direction artifact that exceeds the
OneThird repo's natural scope. Daniel's call.

---

## 7. References

### 7.1 Greene's theorem / RSK / Schensted

- Greene, C. (1976). *An extension of Schensted's theorem.* Adv.
  Math. 14, 254–265.
- Greene, C.; Kleitman, D. J. (1976). *The structure of Sperner
  $k$-families.* J. Combin. Theory Ser. A 20, 41–68.
- Schensted, C. (1961). *Longest increasing and decreasing
  subsequences.* Canad. J. Math. 13, 179–191.
- Britz, T.; Fomin, S. (2001). *Finite posets and Ferrers shapes.*
  Adv. Math. 158, 86–127.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Vol. 2.*
  Cambridge Univ. Press. (Greene-Kleitman: Ch. 7; RSK: §7.11.)

### 7.2 Kazhdan-Lusztig cells (type $A$)

- Kazhdan, D.; Lusztig, G. (1979). *Representations of Coxeter
  groups and Hecke algebras.* Invent. Math. 53, 165–184.
- Lusztig, G. (1985). *Cells in affine Weyl groups.* Algebraic
  groups and related topics (Kyoto/Nagoya 1983), Adv. Stud. Pure
  Math. 6, 255–287.
- Lusztig, G. (2003). *Hecke algebras with unequal parameters.*
  CRM Monograph Series 18, AMS.
- Geck, M.; Pfeiffer, G. (2000). *Characters of finite Coxeter
  groups and Iwahori-Hecke algebras.* LMS Monographs (NS) 21.
- Mathas, A. (1999). *Iwahori-Hecke algebras and Schur algebras
  of the symmetric group.* University Lecture Series 15.
- Duflo, M. (1985). *Représentations de carré intégrable des
  groupes semi-simples réels.* Séminaire Bourbaki 36, Exp. 627.

### 7.3 Dominance order and partition theory

- Macdonald, I. G. (1995). *Symmetric Functions and Hall
  Polynomials* (2nd ed.). Oxford. (§I.1: dominance order and
  $n(\lambda)$.)
- Brylinski, R. (1989). *Limits of weight spaces, Lusztig's
  $q$-analogs, and fiberings of adjoint orbits.* J. Amer. Math.
  Soc. 2, 517–533. (Geometric interpretation of $n(\lambda)$.)
- Garsia, A. M.; Procesi, C. (1992). *On certain graded
  $S_n$-modules and the $q$-Kostka polynomials.* Adv. Math. 94,
  82–138.

### 7.4 Pattern avoidance and RSK-row counts

- Knuth, D. E. (1970). *Permutations, matrices, and generalized
  Young tableaux.* Pacific J. Math. 34, 709–727.
- West, J. (1990). *Permutations with forbidden subsequences and
  stack-sortable permutations.* PhD thesis, MIT.
- Bóna, M. (2012). *Combinatorics of Permutations* (2nd ed.). CRC
  Press. (Ch. 4: pattern avoidance and RSK shape.)
- Stanley, R. P. (1996). *Catalan addendum.* (online; 4321-avoiding
  permutations and shape constraints.)

### 7.5 Stembridge heaps / fully commutative (cross-reference)

- Stembridge, J. R. (1996). *On the fully commutative elements of
  Coxeter groups.* J. Algebraic Combin. 5, 353–385. (mg-5fe9 §4.2.)
- Fan, C. K.; Stembridge, J. R. (1997). *Nilpotent orbits and
  commutative elements.* J. Algebra 196, 490–498.

### 7.6 OneThird-internal predecessor docs

- `docs/compatibility-geometry-manifesto.md` (mg-c853 at `0d8f438`).
- `docs/compatibility-geometry-feasibility-scoping.md` (mg-c853 at
  `0d8f438`).
- `docs/compatibility-geometry-pathP3-scoping.md` (mg-9d6c at
  `9526cf4`).
- `docs/compatibility-geometry-hecke-interpolation-scoping.md`
  (mg-5fe9 at `a32fe64`).

### 7.7 OneThird-internal load-bearing pointers

- `lean/AXIOMS.md` — residual `brightwell_sharp_centred` (mg-38cf)
  and `case3Witness_hasBalancedPair_outOfScope` (mg-b846).
- `lean/OneThird/Step8/Case3Residual.lean` — residual axiom site
  (`L.K \ge 3`, $|M_i| \le 3$, width-3 layered).
- `lean/OneThird/Step8/LayeredBalanced.lean` — layered $K = 2$
  closure (`OptionC.K2Closure`, mg-01ec).
- `step8.tex` — `prop:in-situ-balanced` Case 1/2/3 dispatch.

---

## 8. Token-budget report

This document was authored in a single polecat session at
$\sim 900$ lines of content including formatted math display,
references, and tables — substantive content density similar to
the mg-5fe9 sibling (1127 lines) and mg-9d6c predecessor (720
lines). The ticket §3 line-count target ($250$–$500$) was
exceeded by $\sim 1.8\times$ due to the level of formal precision
the cell-poset question warranted (cell-side and poset-side
backgrounds, three normativity conditions in §3, fiber-side
honest assessment in §4, OneThird-translation in §5). The 250k
token cap was not approached; approximate spend: $\sim 40$k of
250k. No trip-wires fired:

- **Vacuity trip-wire.** NOT fired. The Greene-Schensted
  correspondence is non-vacuous and delivers the clean identity
  $\mathrm{width}(P) = \ell(\lambda(P))$ plus the width-
  stratification $\leftrightarrow$ cell-poset-order-ideal chain
  (§3.2, §3.3). The cell-poset reading is mathematically substantive.
- **Path-converges-with-Step-2-blocker trip-wire.** FIRED as expected
  (§5.3). The cell-poset reading reshapes Step 2 into Specht-module-
  coefficient language but does not bridge it. This is the
  anticipated outcome per the mg-5fe9 §6 / mg-c853 §3 Step 2
  load-bearing diagnosis; flagged in §6.4(d) and §6.5(3)(b) as
  PM-actionable follow-on.
- **Bijection-fails trip-wire.** FIRED as expected (§4.2). $\Phi$
  is strongly lossy; the cell label is a coarse invariant, not a
  bijection. Flagged in §6.2 as the source of "AMBER not GREEN."
  This narrowing **clarifies** rather than weakens the manifesto
  framework — it precisifies "intrinsic" (Greene partition) vs.
  "imposed" (finer poset structure).
- **Token blow-up trip-wire.** NOT fired.

No new project axioms. No Lean source changes. No edits to
mg-c853 / mg-9d6c / mg-5fe9 artifacts. The OneThird trust surface
is unchanged at 4 named project axioms + `native_decide` count.

The mg-5fe9 §5.3(ii) follow-on question is **resolved at scoping
resolution** with a precise dichotomy. Two further follow-ons
(§5.3(iii) heap-subcategory $\leftrightarrow$ mg-9d6c Window C
overlap; §5.3(iv) Hecke/KL proof of Brightwell axiom) remain open;
both are PM-actionable per mg-5fe9 §6.5.

---

*Authored by polecat mg-4e67, branch `polecat-cat-mg-4e67` →
target `compat-geom-cell-poset`. Predecessors: mg-c853 (manifesto
+ feasibility), mg-9d6c (Path P3 applied scoping), mg-5fe9 (Hecke
interpolation foundational scoping). Sibling polecats: cat-mg-9a4a
(Lean impl, branch `compat-geom-pathP3`), cat-mg-e396 (sibling Q3
scoping, branch `compat-geom-hecke-brightwell`) running concurrently;
no state.md coordination required (none touched). 2026-05-13.*
