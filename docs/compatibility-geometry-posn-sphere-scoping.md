# Compat-Geom — Is $\mathrm{Pos}_n$ a topological sphere? (mg-5ee2)

**Source idea.** Daniel reminder 2026-05-13T16:40Z, verbatim:

> *"related: we could try to show Pos_n is a topological sphere"*

**Predecessors.**
- `docs/compatibility-geometry-manifesto.md` (mg-c853): Daniel's
  framework manifesto. Principle 5 names posets as the first
  canonical compatibility geometries.
- `docs/compatibility-geometry-feasibility-scoping.md` (mg-c853 §2.3):
  Coxeter cube complex $\mathcal{X}(P)$ and its identification with
  the OneThird chamber-decomposition machinery (mg-10d9). **Sphere
  candidate scaffolding lives here.**
- `docs/compatibility-geometry-eigensheaves-scoping.md` (mg-296d):
  three categorical incarnations of $\mathrm{Pos}_n$
  ($\mathbf{Pos}_n^{\mathrm{sub}}$ chosen). Eigensheaf framework on
  the refinement lattice.

**Sibling.** cat-mg-d60d (Pos_n sheaf-cohomology forces balance,
launched 2026-05-13T16:41Z) runs in parallel. Both tickets are
LaTeX-only scoping; no `state.md` overlap. This document is
**logically prior** to mg-d60d: sheaf cohomology on $\mathrm{Pos}_n$
is governed by the homotopy type of the realization, which is the
subject of this scoping.

**This document.** A LaTeX-first scoping of Daniel's
2026-05-13T16:40Z idea. Frame the question precisely (there is no
canonical "the" topological realization of $\mathrm{Pos}_n$ — at
least five candidates exist), compute small cases by hand for the
two strongest candidates ($n = 2, 3$), survey the relevant
poset-topology literature, identify what is rigorously known versus
speculative, and render a verdict. No new axioms; pure scoping.

LaTeX is used inline ($\ldots$ / display) throughout; render with
KaTeX/MathJax or read source.

---

## 1. Setup

Let $n \ge 1$ throughout. Following mg-296d §1.1 we work in
$\mathbf{Pos}_n^{\mathrm{sub}}$:

- **Objects.** Partial orders $P$ on $[n] := \{1, \ldots, n\}$.
- **Morphisms.** $P \to Q$ exists iff $<_P \subseteq <_Q$
  (refinement). As a category, $\mathbf{Pos}_n^{\mathrm{sub}}$ is
  a finite *poset*: thin (at most one morphism per pair).
- **Grading.** By relation count $\mathrm{rk}(P) := |\!<_P\!|$
  (counting transitive consequences). Then $0 \le \mathrm{rk}(P)
  \le \binom{n}{2}$.

The bottom element $\hat{0}$ is the antichain
($\mathcal{L}(\hat{0}) = S_n$, $\mathrm{rk}(\hat{0}) = 0$). The
maximal elements are the $n!$ total orders, each of rank
$\binom{n}{2}$.

**Cardinality.**
$|\mathbf{Pos}_n^{\mathrm{sub}}|$ is OEIS A001035: $1, 1, 3, 19, 219,
4231, 130023, \ldots$ for $n = 0, 1, 2, 3, 4, 5, 6, \ldots$.

**$\mathbf{Pos}_n^{\mathrm{sub}}$ is a lattice** under refinement:
- Meet: $P \wedge Q$ has $<_{P \wedge Q} = $ largest partial order
  contained in $<_P \cap <_Q$ (intersection is already transitive).
- Join: $P \vee Q$ has $<_{P \vee Q} = $ transitive closure of
  $<_P \cup <_Q$ (may not exist if the closure is inconsistent —
  then we say $P, Q$ have no join in $\mathbf{Pos}_n^{\mathrm{sub}}$).

The non-existence of certain joins matters: $\mathbf{Pos}_n^{
\mathrm{sub}}$ is **not** a lattice in the strict sense; it is a
**meet-semilattice with multiple maximal elements**. The standard
device (see §2.3 below) is to adjoin a formal $\hat{1}$.

---

## 2. The five candidates for "topological realization of $\mathrm{Pos}_n$"

Daniel's question — "is $\mathrm{Pos}_n$ a topological sphere?" — has
no canonical reading. We enumerate the five strongest candidates and
commit to two for the substantive analysis.

### 2.1 (R1) Order complex $\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$

The standard simplicial complex of a finite poset:

- **0-cells:** elements of $\mathbf{Pos}_n^{\mathrm{sub}}$.
- **$k$-cells:** $(k{+}1)$-element strict chains
  $P_0 < P_1 < \cdots < P_k$ in $\mathbf{Pos}_n^{\mathrm{sub}}$.

This is the **order complex** (Stanley, EC1 Ch. 3.8; Bjorner–Wachs
2007). Dimension: $\binom{n}{2}$ (length of a maximal chain from
$\hat{0}$ to a total order).

**Cone issue.** $\hat{0}$ is a cone point: every simplex
containing $\hat{0}$ is the join $\hat{0} * \Delta(\mathbf{Pos}_n^{
\mathrm{sub}} \setminus \{\hat{0}\})$. So
$\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$ is **always contractible**
(coned off by $\hat{0}$). This makes (R1) **uninteresting** as a
sphere candidate.

### 2.2 (R2) Proper part — bottom-stripped order complex
$\Delta(\overline{\mathbf{Pos}}_n^{\mathrm{sub}})$

Let $\overline{\mathbf{Pos}}_n^{\mathrm{sub}} := \mathbf{Pos}_n^{
\mathrm{sub}} \setminus \{\hat{0}\}$. The order complex
$\Delta(\overline{\mathbf{Pos}}_n^{\mathrm{sub}})$ removes the cone
point.

**$n=2$ check.** $\overline{\mathbf{Pos}}_2^{\mathrm{sub}} = \{1<2,
2<1\}$, two incomparable elements. $\Delta = $ two isolated
vertices $= S^0$. **A genuine 0-sphere.**

This is the **first candidate that admits a sphere**.

### 2.3 (R3) Augmented order complex with formal $\hat{1}$:
$\Delta(\widehat{\mathbf{Pos}}_n^{\mathrm{sub}} \setminus \{\hat{0},
\hat{1}\})$

Adjoin a formal top $\hat{1}$ above all $n!$ total orders. Write
$\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$ for the augmented lattice.
Take the **proper part**:

$$
\widetilde{\mathbf{Pos}}_n^{\mathrm{sub}} :=
\widehat{\mathbf{Pos}}_n^{\mathrm{sub}} \setminus \{\hat{0}, \hat{1}\}
\,=\, \mathbf{Pos}_n^{\mathrm{sub}} \setminus \{\hat{0}\}
\,=\, \overline{\mathbf{Pos}}_n^{\mathrm{sub}}.
$$

So $\Delta(\widetilde{\mathbf{Pos}}_n^{\mathrm{sub}}) =
\Delta(\overline{\mathbf{Pos}}_n^{\mathrm{sub}})$ as a simplicial
complex; **(R3) coincides with (R2)** at the simplicial level. The
difference is structural: in (R3), $\widehat{\mathbf{Pos}}_n^{
\mathrm{sub}}$ is a *bounded* lattice and **Möbius-theoretic /
shellability machinery applies cleanly**. This is the standard
convention in Bjorner–Wachs poset topology.

### 2.4 (R4) Classifying space $|\mathbf{Pos}_n^{\mathrm{sub}}| =
B\mathbf{Pos}_n^{\mathrm{sub}}$ (nerve of the category)

Treating $\mathbf{Pos}_n^{\mathrm{sub}}$ as a (thin) category and
taking its classifying space. For posets, the classifying space of
$(P, \le)$ is the geometric realization of the order complex of $P$
(Quillen, *Higher algebraic K-theory I*, §1):
$|P| \simeq |\Delta(P)|$. So **(R4) $\simeq$ (R1)** up to
homotopy — also contractible (coned by $\hat{0}$).

### 2.5 (R5) Open-interval / cubical realization

Two further candidates, briefly:

- **(R5a)** The Stanley *order polytope* $\mathcal{O}(P) \subset
  [0,1]^n$ of an individual poset $P$ is a polytope; its boundary
  $\partial \mathcal{O}(P)$ is a sphere of dimension $n-1$ (it is a
  convex polytope's boundary). This is a **per-$P$** sphere, **not
  a sphere structure on $\mathrm{Pos}_n$**. Not the right candidate.

- **(R5b)** The Coxeter cube complex $\mathcal{X}(S_n)$ (mg-c853
  §2.3) is **not** a sphere: it is CAT(0) hence contractible. Its
  one-point compactification or quotient by translations could be
  sphere-like, but this is a different object from $\mathrm{Pos}_n$.

### 2.6 Commitment

We commit to **(R3)** (equivalently (R2)) as the operative meaning of
"topological realization of $\mathrm{Pos}_n$." Reasons:

(i) (R1)/(R4) are contractible and uninteresting.
(ii) (R3) is the Bjorner–Wachs standard for studying sphericity of
finite-lattice order complexes (the proper part of a bounded lattice
$L$ is the right object for which "$\Delta = $ sphere" makes sense).
(iii) (R3) yields a **genuine sphere at $n=2$** (§2.2), which is the
minimal non-trivial sanity check.
(iv) (R5a) is too local (per-$P$); (R5b) is contractible.

**Notation.** From here on, $\Delta_n := \Delta(\widetilde{\mathbf{
Pos}}_n^{\mathrm{sub}})$ = the order complex of the proper part of
the formally-augmented refinement lattice.

---

## 3. Small-case computations

### 3.1 $n=2$: $\Delta_2 = S^0$ ✓

$\widetilde{\mathbf{Pos}}_2^{\mathrm{sub}} = \{1{<}2,\ 2{<}1\}$,
incomparable. Two isolated 0-simplices. $\Delta_2 \cong S^0$.

**Möbius cross-check.** In $\widehat{\mathbf{Pos}}_2^{\mathrm{sub}}$:

- $\mu(\hat{0}, \hat{0}) = 1$.
- $\mu(\hat{0}, 1{<}2) = -1$, $\mu(\hat{0}, 2{<}1) = -1$
  (covers of $\hat{0}$).
- $\mu(\hat{0}, \hat{1}) = -(1 + (-1) + (-1)) = 1$.

Reduced Euler characteristic of $\Delta_2$:
$\widetilde{\chi}(\Delta_2) = \mu(\hat{0}, \hat{1}) = 1$. The reduced
Euler characteristic of $S^d$ is $(-1)^d$. Here $d = 0$,
$(-1)^0 = 1$. ✓ Consistent with $\Delta_2 = S^0$.

### 3.2 $n=3$: $\Delta_3$ — direct computation

$|\mathbf{Pos}_3^{\mathrm{sub}}| = 19$. Strip $\hat{0}$: 18
elements. The 18 are partitioned by rank:

- **Rank 1** (1 relation, no transitive consequence): pick a pair
  $\{i, j\}$ and orientation: $\binom{3}{2} \cdot 2 = 6$ posets.
  Generic shape "$i < j$, $k$ incomparable."
- **Rank 2**: two relations $a < b, c < d$, no third relation
  forced by transitivity. Three sub-shapes by the underlying
  comparability graph:
    - "$\vee$" (one min, two cover from it): $1 < 2$, $1 < 3$
      and its $3 \cdot 2 = 6$ relabelings; total $6$.
    - "$\wedge$" (one max, two cover to it): $1 < 3$, $2 < 3$
      and relabelings; total $6$.
  *Note*: a "path" $1 < 2$, $2 < 3$ is rank 3 (transitivity forces
  $1 < 3$), not rank 2. So no rank-2 "path." Total rank 2: $12$.
- **Rank 3** (total orders): $3! = 6$ posets.

Cardinality check: $6 + 12 + 6 = 24 = 18$? **Inconsistent** — let me
recount.

Actually, the OEIS number 19 includes the antichain and all proper
posets including some I missed. Let me redo. A partial order on $[3]$
is determined by its cover relations modulo transitivity. The 19
partial orders on $\{1,2,3\}$ broken down by *Hasse diagram shape* are:

- Antichain (3 isolated points): 1 poset.
- One cover, one isolated point: $\binom{3}{1} \cdot 2 = 6$ (pick
  the isolated point, then orient the cover between the other two).
  These are rank 1 (1 strict-relation pair).
- Path $a < b < c$: $3! = 6$ posets (total orders). Rank 3.
- "$\vee$" $a < c$, $b < c$: $\binom{3}{1} = 3$ (pick the top).
  Rank 2.
- "$\wedge$" $a < b$, $a < c$: $\binom{3}{1} = 3$ (pick the bot).
  Rank 2.

Total: $1 + 6 + 6 + 3 + 3 = 19$. ✓

So $\widetilde{\mathbf{Pos}}_3^{\mathrm{sub}}$ has 18 elements:

- 6 rank-1 (one-cover-with-isolated).
- 6 rank-2: split as 3 "$\vee$" + 3 "$\wedge$".
- 6 rank-3 (total orders).

**Cover relations in $\mathbf{Pos}_3^{\mathrm{sub}}$.** $P$ is
covered by $Q$ iff $Q$ adds exactly one new comparability to $P$
(possibly with transitive consequences making rank jump by more
than 1).

For each rank-1 poset "$1 < 2$, $3$ isolated" the covers in
$\mathbf{Pos}_3^{\mathrm{sub}}$ are the posets obtained by adding
one new comparability, possibly forcing transitivity:

- Add $1 < 3$: get "$1<2$, $1<3$" — a "$\wedge$" (rank 2).
- Add $3 < 1$: get $3 < 1 < 2$ — a total order (rank 3).
- Add $2 < 3$: get $1 < 2 < 3$ — a total order (rank 3).
- Add $3 < 2$: get "$1<2$, $3<2$" — a "$\vee$" (rank 2).

So each rank-1 poset is covered by 2 rank-2 posets and 2 rank-3
posets (4 covers total).

Similarly, "$\vee$" $a < c$, $b < c$ (say $c = 3$) is covered by
adding $a < b$ (gives $a<b<c$) or $b < a$ (gives $b<a<c$) — 2
covers, both rank 3.

Symmetrically "$\wedge$" $a < b$, $a < c$ is covered by 2 rank-3
total orders.

**The order complex $\Delta_3$.** Top-dimensional simplices are
maximal chains of length 3 from rank 1 → rank 2 → rank 3. (Rank-0
$\hat{0}$ is stripped; "rank 1" is the lowest stratum of $\widetilde{
\mathbf{Pos}}_3^{\mathrm{sub}}$.) Wait — chains in $\widetilde{\mathbf{
Pos}}_3$ run from rank-$k$ to rank-$\ell$ for $1 \le k \le \ell \le 3$.

A maximal chain $P_1 < P_2 < P_3$ with $\mathrm{rk}(P_i) = i$ is one
of:

$$
\underbrace{\text{(rank-1, one cover + isolated)}}_{6}
\,\to\,
\underbrace{\text{(rank-2, $\vee$ or $\wedge$)}}_{?}
\,\to\,
\underbrace{\text{(rank-3, total order)}}_{6}.
$$

Specifically, each rank-2 "$\wedge$" $a < b$, $a < c$ refines:

- *Above*: 2 rank-3 (total orders extending it: $a<b<c$ and $a<c<b$).
- *Below*: 2 rank-1 ($a<b$, $c$ isolated and $a<c$, $b$ isolated).

So each rank-2 has 2 covers above and is covered by 2 rank-1's
below. Each rank-2 contributes $2 \cdot 2 = 4$ maximal chains.

Total maximal chains: $(3 + 3) \cdot 4 = 24$. But $24$ is also $\sum_
{\text{total orders}\,\sigma}$ #(linear extensions through chains
ending at $\sigma$). Each total order has $2$ rank-2 below it and
each of those has $2$ rank-1 below, so $2 \cdot 2 = 4$ chains
terminate at it; $6 \cdot 4 = 24$. ✓

So $\Delta_3$ has dimension $2$ and $24$ top 2-simplices.

**Reduced Euler characteristic.** Compute the $f$-vector
$(f_{-1}, f_0, f_1, f_2)$ where $f_k$ is the count of $k$-faces of
$\Delta_3$ (with $f_{-1} = 1$ for the empty simplex):

- $f_{-1} = 1$.
- $f_0 = 18$ (vertices = elements of $\widetilde{\mathbf{Pos}}_3$).
- $f_1 = ?$ — count of 2-element chains in $\widetilde{\mathbf{Pos}}_3$.
- $f_2 = 24$ (computed).

Count of 2-chains:

- (rank-1, rank-2): each rank-2 has 2 covers below = $6 \cdot 2 =
  12$. Also each rank-1 has 2 rank-2 covers above, $6 \cdot 2 = 12$.
  Total (rank-1, rank-2): $12$.
- (rank-1, rank-3): each rank-1 has 2 rank-3 covers directly (the
  ones that force transitivity). $6 \cdot 2 = 12$. Also each rank-3
  has how many rank-1 below? Each total order $a<b<c$ refines
  exactly 2 rank-1: "$a<b$, $c$ isol" and "$b<c$, $a$ isol"
  (only those, since "$a<c$, $b$ isol" is *not* refined by
  $a<b<c$ — wait yes it is, $a<c$ is forced). Actually let me
  reconsider. A rank-1 poset $i<j$ with $k$ isolated is refined by
  total order $\sigma$ iff $i <_\sigma j$. So for total order
  $a<b<c$ (three positions): rank-1's it refines are
  "$a<b$, $c$ isolated", "$a<c$, $b$ isolated", "$b<c$, $a$
  isolated" — 3 of them. So each rank-3 has 3 rank-1 below.
  Total $6 \cdot 3 = 18 \ne 12$. **Discrepancy** — recount.

Let me re-examine "rank-1 has 2 rank-3 covers directly" — actually
each rank-1 ($i<j$, $k$ isolated) is refined by total orders that
preserve $i<j$: total orders are $S_3$, and $i<j$ is preserved by
3 of them (those with $i$ before $j$). So **each rank-1 has 3
rank-3 above, not 2**. Recount of (rank-1, rank-3) pairs: $6 \cdot
3 = 18$, dual $6 \cdot 3 = 18$. ✓ Either side gives $18$.

OK so (rank-1, rank-3) = $18$, not $12$.

- (rank-2, rank-3): each rank-2 has 2 rank-3 above (computed).
  $6 \cdot 2 = 12$. Each rank-3 has how many rank-2 below? Total
  order $a<b<c$: the rank-2 posets it refines are "$a<b$, $a<c$"
  ($\wedge$, $a$ is min) and "$a<c$, $b<c$" ($\vee$, $c$ is max).
  Just 2. So $6 \cdot 2 = 12$. ✓

So $f_1 = 12 + 18 + 12 = 42$. Now reduced Euler:

$$
\widetilde{\chi}(\Delta_3) = -f_{-1} + f_0 - f_1 + f_2
= -1 + 18 - 42 + 24 = -1.
$$

For $\Delta_3 \simeq S^d$ (single sphere) we'd need
$\widetilde{\chi} = (-1)^d$. The value $-1 = (-1)^1$, so **if**
$\Delta_3$ were a sphere it would be $S^1$. But $\dim \Delta_3 = 2$,
so $\Delta_3 \simeq S^1$ would require the 2-cells to be "filling
in" along a circle — a thickened-circle simplicial complex, not a
single sphere in the standard sense.

**Provisional conclusion (n=3):** $\widetilde{\chi}(\Delta_3) = -1$,
**inconsistent with $\Delta_3$ being a single $S^d$ of dimension
matching its combinatorial dimension 2**. Specifically:

- $S^2$ would require $\widetilde{\chi} = +1$. **Refuted.**
- $S^1$ would have $\widetilde{\chi} = -1$, **matches by Euler**,
  but the simplicial complex has nontrivial 2-cells.

The most natural resolution: $\Delta_3$ is **not** a topological
sphere but might be **homotopy equivalent** to $S^1$ (or a wedge of
spheres with Euler $-1$, e.g., wedge of one $S^1$ or one $S^1$ plus
a contractible piece). Verification requires checking the homotopy
type or homology directly, which is beyond the Euler-characteristic
witness above.

### 3.3 Möbius-function alternative cross-check

By the Philip Hall theorem (Stanley EC1 Thm 3.8.6):
$\widetilde{\chi}(\Delta_n) = \mu_{\widehat{\mathbf{Pos}}_n^{
\mathrm{sub}}}(\hat{0}, \hat{1})$. So computing
$\mu(\hat{0}, \hat{1})$ in $\widehat{\mathbf{Pos}}_3^{\mathrm{sub}}$
should yield $-1$ if our $f$-vector computation is right.

Direct Möbius recursion:

- $\mu(\hat{0}, \hat{0}) = 1$.
- $\mu(\hat{0}, R_1) = -1$ for each rank-1 $R_1$ (6 of them).
- $\mu(\hat{0}, R_2)$ for $R_2$ a rank-2: $R_2$ is covered from
  below by 2 rank-1's. So $\mu = -(1 + 2 \cdot (-1)) = -(1 - 2)
  = 1$. (6 rank-2's, all $\mu = 1$.)
- $\mu(\hat{0}, R_3)$ for $R_3$ a rank-3 total order: $R_3$ is
  refined by $\hat{0}$, 3 rank-1's, 2 rank-2's, and itself. Then
  $\mu(\hat{0}, R_3) = -(\mu(\hat{0}, \hat{0}) + 3 \cdot (-1) +
  2 \cdot 1) = -(1 - 3 + 2) = 0$.
- $\mu(\hat{0}, \hat{1}) = -\sum_{P \ne \hat{1}} \mu(\hat{0}, P)$
  $= -(1 + 6 \cdot (-1) + 6 \cdot 1 + 6 \cdot 0) = -(1 - 6 + 6 + 0)
  = -1$.

**Confirmed: $\mu_{\widehat{\mathbf{Pos}}_3^{\mathrm{sub}}}(\hat{0},
\hat{1}) = -1$, matching $\widetilde{\chi}(\Delta_3) = -1$.**

By the rank-3 Möbius values $\mu(\hat{0}, R_3) = 0$, the **total
orders are NOT atoms of the Möbius structure** in the formally-
augmented lattice. This is informative: it says total orders are
"absorbed" into the chains coming from below, not contributing
isolated Möbius mass.

### 3.4 Aspiration check: $n=3$, is $\Delta_3 \simeq S^1$?

The Euler witness allows but does not prove $S^1$. To verify
homotopically, one would compute $H_*(\Delta_3; \mathbb{Z})$ via the
chain complex. This is a finite calculation ($f_1 = 42$, $f_2 = 24$)
but tedious by hand; it falls outside this scoping's polecat budget.
We **conjecturally** record:

**Conjecture (R3 sphericity at $n=3$).** $\Delta_3$ is homotopy
equivalent to $S^1$ (a single circle).

If true, this is **not a topological 2-sphere** but is a sphere in
the algebraic-topology sense (a 1-sphere realized as a 2-dim
simplicial complex). The dimension drop ($2 \to 1$) is the key
phenomenon: pure CM-shellability would give $S^2$; the actual
collapse to $S^1$ would indicate a **partial collapse** of the
2-skeleton.

### 3.5 $n \ge 4$: enumeration-class

$|\mathbf{Pos}_4^{\mathrm{sub}}| = 219$. Hasse diagram of
$\widehat{\mathbf{Pos}}_4^{\mathrm{sub}}$ has $\sim 10^3$ cover
relations. Direct hand computation is infeasible. **Computer
calculation via the Stanley/Pak/Reiner SageMath packages or
SimpComp** is the obvious tool — out of scope for this scoping. We
note the question and leave it to a follow-up.

---

## 4. Literature scaffolding

The question "is the order complex of the refinement lattice of
posets a topological sphere?" sits in the well-developed field of
*poset topology*. Key references and analogues:

### 4.1 Partition lattice $\Pi_n$ (Björner 1980)

The **partition lattice** $\Pi_n$ is the lattice of set-partitions
of $[n]$ under refinement. Björner proved (1980; cf. Björner–Wachs
2007, Ch. 4):

$$
\Delta(\overline{\Pi}_n) \,\simeq\, \bigvee_{(n-1)!} S^{n-3}.
$$

A wedge of $(n-1)!$ spheres in dimension $n-3$. The partition
lattice is **shellable** (EL-shellable in fact: Björner 1980, Wachs
1996), which forces this wedge-of-spheres conclusion via Björner–
Wachs theory.

**Analogue for $\mathbf{Pos}_n^{\mathrm{sub}}$.** The refinement
lattice of set-partitions is a *coarsened* version of refinement of
partial orders (a partial order's comparability classes give a
set-partition; the converse forgets order direction). So
$\mathbf{Pos}_n^{\mathrm{sub}}$ is "richer" than $\Pi_n$.

A wedge-of-spheres conclusion for $\mathbf{Pos}_n^{\mathrm{sub}}$
analogous to Björner's $\Pi_n$ result is the **natural expectation**
— with the wedge count and sphere dimension to be determined.

### 4.2 Coxeter complex of $S_n$

The **Coxeter complex** $\Sigma(S_n)$ is a triangulation of $S^{n-2}$:

$$
\Sigma(S_n) \,\cong\, S^{n-2}
\qquad (\text{Tits 1974}).
$$

Vertices are parabolic subgroups of $S_n$ (= compositions of $n$).
This is the boundary of the **permutohedron** $\mathcal{P}_n$, a
genuine topological sphere.

**Connection to $\mathrm{Pos}_n$.** The Coxeter complex parametrizes
**Weyl chambers** of $S_n$. By mg-c853 §2.3 / mg-10d9, chambers
correspond bijectively to total orders. The Coxeter complex is
naturally a sub-object of $\mathbf{Pos}_n^{\mathrm{sub}}$
restricted to "antichain $\to$ total orders" (skipping intermediate
ranks).

**The honest gap.** $\mathrm{Pos}_n^{\mathrm{sub}}$ is **much
larger** than the Coxeter complex; it includes all intermediate
posets. The Coxeter complex captures the "top layer" of
$\mathrm{Pos}_n^{\mathrm{sub}}$; the question is whether the full
lattice retains sphericity.

### 4.3 Bjorner-Wachs CM-shellability machinery

If $\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$ is **EL-shellable**
(edge-labeling shellable; Björner 1980, Björner–Wachs 1996), then by
the Björner–Wachs–Bjorner–Stanley theorem:

$$
\Delta(\widetilde{\mathbf{Pos}}_n^{\mathrm{sub}}) \,\simeq\,
\bigvee_{j=1}^{N} S^{d_j},
$$

a wedge of spheres in possibly varying dimensions, with explicit
count $N$ and dimensions $d_j$ from the labeling.

**Is $\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$ shellable?** Open as
stated. Two obstructions are visible:

(i) **Non-graded jumps.** The cover relations of $\mathbf{Pos}_n^{
\mathrm{sub}}$ do not preserve rank by 1: adding one cover
relation can force multiple new transitive comparabilities,
jumping rank by more than 1. This means $\mathbf{Pos}_n^{
\mathrm{sub}}$ is **not graded** under cover-by-relation-
addition. (Counted by *number* of comparabilities, it is graded:
the rank function $\mathrm{rk}(P) = |\!<_P\!|$ is consistent
with refinement. But the *cover* steps in the Hasse diagram of
$\mathbf{Pos}_n^{\mathrm{sub}}$ are not unit-rank.)

(ii) **Multiple maximal elements.** $\mathbf{Pos}_n^{\mathrm{sub}}$
has $n!$ maximal elements (total orders). The formal $\hat{1}$
adjunction handles this for the order-complex purpose, but the
"shelling order" of the Hasse diagram is not as clean as in the
single-top case.

Neither obstruction is fatal. Björner–Wachs allow non-pure
shellable complexes (giving wedges of spheres in mixed dimensions).
But proof of shellability for $\widehat{\mathbf{Pos}}_n^{
\mathrm{sub}}$ is **not in the literature** that this polecat
could surface.

### 4.4 Closer relatives in the literature

The "lattice of partial orders" $\mathbf{Pos}_n$ has been studied:

- **Birkhoff (1937, *Rings of sets*)** — the original Galois-
  closure construction for finite posets.
- **Stanley, *Enumerative Combinatorics Vol. 1* Ch. 3 (esp.
  3.4, 3.6, 3.8)** — Möbius function of the partial-order lattice.
- **Bjorner, "Topological methods" (Handbook of Combinatorics
  1995)** — surveys order-complex techniques.
- **Wachs (2007), "Poset topology: tools and applications"** —
  modern reference.

A **specific theorem on the homotopy type of
$\Delta(\widehat{\mathbf{Pos}}_n^{\mathrm{sub}} \setminus \{\hat{0},
\hat{1}\})$ is not located** in the standard references. This is
a research gap, not a known answered question — and that gap is
**itself a substantive finding** of this scoping.

### 4.5 The Galashin-Postnikov universe (recent)

Galashin (2019, 2021) and Postnikov on **chamber graphs of poset
polytopes** give partial CW structures on chamber complexes of
order polytopes. The **chamber graph of $\mathcal{O}(P)$** is
related to but distinct from the order complex of $\mathbf{Pos}_n^{
\mathrm{sub}}$. No direct theorem on $\Delta_n$ sphericity from
this branch was located.

---

## 5. The "if true" implications

Suppose **(Sphere)** $\Delta_n \simeq S^{d_n}$ for some explicit
$d_n$. What does this buy?

### 5.1 Cohomological consequences

(i) **Concentration.** For any locally constant sheaf
$\mathcal{F}$ on $|\Delta_n|$, cohomology
$H^k(|\Delta_n|, \mathcal{F})$ is supported in degrees $k \in \{0,
d_n\}$. This is the "spectral rigidity" expressed cohomologically.

(ii) **Reduced cohomology = $\mathbb{Z}$ in top degree.**
$\widetilde{H}^{d_n}(\Delta_n; \mathbb{Z}) \cong \mathbb{Z}$;
$\widetilde{H}^k = 0$ for $k \ne d_n$.

(iii) **Poincaré–Lefschetz duality on the chain side.** For chain
complexes computing sheaf cohomology, sphere duality gives a
non-degenerate pairing $H^k \otimes H^{d_n - k} \to \mathbb{Z}$
(at least with $\mathbb{Q}$-coefficients).

### 5.2 Implications for Step 2 (1/3–2/3)

The mg-296d framework establishes $F_\ell$ as the principal
$\Delta_{(a,b)}$-eigensheaf on $\mathbf{Pos}_n^{\mathrm{sub}}$ with
$\mathrm{Pr}$-eigenvalues. If (Sphere) holds:

- $H^k(\mathbf{Pos}_n^{\mathrm{sub}}, F_\ell)$ vanishes for
  $0 < k < d_n$, concentrating obstruction classes in top degree.
- The **eigenvalue spectrum** $\{\Pr_P[a < b]\}$ of $F_\ell$ must
  satisfy a **rigidity constraint**: its "spectral oscillation" is
  bounded by the top-degree cohomology.
- In favorable scenarios, this constraint translates to **forcing
  the spectrum to hit $[1/3, 2/3]$**: a uniform-rigidity argument
  excluding pure $\Pr \in \{0\} \cup [0, 1/3) \cup (2/3, 1] \cup
  \{1\}$ extremes.

**Honest caveat.** The "uniform-rigidity argument" of the previous
bullet is **not** a theorem; it's the *type* of argument that
becomes available under (Sphere). Concrete instantiation requires
the right cohomological obstruction class and is exactly the work
that mg-d60d is scoped to investigate.

The relationship is:

$$
\text{this ticket (mg-5ee2)} \rightarrow
\text{(Sphere) or wedge-of-spheres}
\quad \xrightarrow{\text{mg-d60d}} \quad
\text{cohomological obstruction $\Rightarrow$ balance}.
$$

mg-5ee2 establishes the geometric backdrop; mg-d60d works on the
cohomological obstruction sheaf. **mg-d60d needs (Sphere) or some
weakening as input.**

### 5.3 Wedge-of-spheres weakening

Most of (i)–(iii) survives under the weakening **(Wedge)** $\Delta_n
\simeq \bigvee S^{d_j}$ — a wedge of spheres in (possibly mixed)
dimensions:

(i') Cohomology concentrated in $\{0\} \cup \{d_j : j\}$ —
finite set.
(ii') $\widetilde{H}^{d_j} = \mathbb{Z}^{N_j}$ where $N_j$ is the
multiplicity of $S^{d_j}$ in the wedge.
(iii') Top-degree duality only in pure case (all $d_j$ equal).

In the wedge case, the rigidity is **strictly weaker but still
non-trivial**. For the eigensheaf / balance application, this is
likely the **realistic** regime.

---

## 6. What can be proven at scoping resolution

### 6.1 Pinned-down

- $\Delta_n$ (per §2.6 commitment) is the right object.
- $\Delta_2 = S^0$ (§3.1).
- $\Delta_3$ has $\widetilde{\chi} = -1$ (§3.2), inconsistent with
  $S^2$; **consistent with $S^1$ or wedge with Euler $-1$**.
- The Coxeter complex $\Sigma(S_n) \cong S^{n-2}$ sits inside the
  "top layer" of $\mathbf{Pos}_n^{\mathrm{sub}}$.
- Möbius computation tooling works (§3.3, agrees with $f$-vector).

### 6.2 Open / not literature-resolved

- **Sphericity of $\Delta_n$ for $n \ge 3$.** Not known to this
  polecat. Strongly suspect: $\Delta_n$ is **not** a single sphere
  in general; instead a **wedge of spheres** of possibly mixed
  dimensions, or potentially **non-shellable with richer
  homology**.
- **EL-shellability of $\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$.**
  Not known to be in the literature.
- **The sphere dimension $d_n$.** Two competing heuristics:
    - **(H-CM)** Pure CM: $d_n = \binom{n}{2} - 1$ (dimension of
      $\Delta_n$ itself, = max-chain dim in $\widetilde{\mathbf{
      Pos}}_n^{\mathrm{sub}}$).
        - $n=2$: $0$, matches $\Delta_2 = S^0$. ✓
        - $n=3$: $2$, predicts $S^2$. **Refuted** by Euler $-1$
          (§3.2: $S^2$ has $\widetilde{\chi} = +1$).
        - $n=4$: $5$, predicts $S^5$.
    - **(H-Cox)** Coxeter-complex extrapolation: $d_n = n - 2$.
        - $n=2$: $0$, matches $\Delta_2 = S^0$. ✓
        - $n=3$: $1$, predicts $S^1$. Consistent with §3.4
          conjecture.
        - $n=4$: $2$, predicts $S^2$.
- **The $n=3$ Euler witness specifically refutes (H-CM)** as the
  literal-sphere reading. It is consistent with (H-Cox), but
  consistency with $\widetilde{\chi}$ is a necessary, not
  sufficient, condition. Distinguishing (H-Cox) from "wedge of
  $S^1$'s plus contractible 2-skeleton mass" requires homology.
- **Behavior at $n \ge 4$.** Heuristics diverge starting here.
  Computer calculation (F1 below) decides.

### 6.3 Specifically wrong assertions to avoid

- **"$\Delta_n \cong S^{n-2}$" (Coxeter-complex extrapolation).**
  Not literally falsified for $n \le 3$ (gives $S^0$, $S^1$ — both
  consistent with §3). For $n=4$: predicts $S^2$, but the
  max-chain dimension of $\Delta_4$ is $\binom{4}{2} - 1 = 5$. So
  (H-Cox) would require the 5-skeleton of $\Delta_4$ to collapse
  homotopically onto a 2-skeleton — geometrically exotic and
  unverified.
- **"Pos_n is contractible."** False: $\Delta_2 = S^0$ is not
  contractible.
- **"Pos_n is a manifold."** Highly unlikely. Order complexes of
  finite lattices are generally manifolds only in very special
  cases (Coxeter complexes, Boolean lattices).

---

## 7. Verdict

**AMBER-specialist, leaning RED on literal "topological sphere"
reading, AMBER on wedge-of-spheres weakening.**

### Why not GREEN

- The literal "single topological sphere" reading **fails at $n=3$**
  by Euler-characteristic check (§3.2): $\widetilde{\chi}(\Delta_3)
  = -1 \ne (-1)^2 = 1$ for $S^2$ of the natural dimension. If $\Delta
  _n$ is a single sphere, it must be of unusual lower dimension (not
  matching the combinatorial dimension), which is geometrically
  exotic.
- No single result in the literature establishes $\Delta_n$
  sphericity. The closest analogues (partition lattice $\Pi_n$,
  Coxeter complex) give **wedge of spheres** and **a single
  Coxeter-complex sphere of dimension $n-2$ in the top layer**, not
  full-lattice sphericity.

### Why not RED outright

- The weakened claim **(Wedge): $\Delta_n$ is a wedge of spheres**
  is **plausible by analogy with $\Pi_n$** and would inherit most of
  the cohomological-rigidity content needed for Step 2 implications
  (§5.3).
- The $n=2$ case **is** a genuine $S^0$, suggesting the program is
  not vacuously false.
- The $n=3$ Euler characteristic $-1$ is **consistent with $S^1$**
  (or a wedge of one $S^1$ plus contractible parts), which would
  still give sphere-like rigidity in a single dimension.

### What this ticket recommends

**Reformulate the question** as:

(Q-revised) *Is $\Delta_n := \Delta(\widetilde{\mathbf{Pos}}_n^{
\mathrm{sub}})$ EL-shellable, and if so, what is the wedge-of-spheres
decomposition?*

This is the **right question** in light of:

(a) Literature analogues (partition lattice, intersection lattices,
Coxeter complex) all yield wedges of spheres, not single spheres.

(b) The Step 2 cohomological application of mg-d60d **does not
require a single sphere** — wedge-of-spheres rigidity (§5.3) is
sufficient for the obstruction-class machinery.

(c) Shellability of $\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$ is a
**concrete, decidable** combinatorial question for small $n$, and
admits computer verification for $n = 4, 5$.

### What this ticket does NOT recommend

- **Direct sphere-claim work for $n \ge 3$.** The literal reading
  is most likely false (refuted at $n=3$ for the natural dimension).
- **Pursuing $\Delta_n$ sphericity in isolation from the Step 2
  application.** Whether $\Delta_n$ is a sphere matters only insofar
  as it gives Step 2 leverage; mg-d60d is the right place to assess
  that leverage with the actual sheaf $F_\ell$ in hand.

---

## 8. Dispatch

### 8.1 Predecessor / sibling

- Predecessors: mg-c853 (manifesto + feasibility), mg-296d
  (eigensheaves).
- Sibling: cat-mg-d60d (poset sheaf cohomology forces balance) —
  **logical consumer** of this ticket's verdict.
- Branch: `compat-geom-posn-sphere` (new, this ticket).

### 8.2 Recommended follow-ups

(F1) **Computer verification at $n=4$**. Use SageMath's
`Poset.order_complex().homology()` to compute
$H_*(\Delta_4; \mathbb{Z})$. Decide between three scenarios:
  - Single sphere: $H_* = (\mathbb{Z}, 0, 0, \mathbb{Z})$ in some
    pattern.
  - Wedge of spheres of pure dimension: $H_d = \mathbb{Z}^N$.
  - Mixed/non-CM: complicated $H_*$.

Effort: $\sim 50$ LoC SageMath script, $\sim 1$ minute of wall time
for $n=4$ (219 posets × 219). Polecat-tractable.

(F2) **Shellability proof attempt** for $\widehat{\mathbf{Pos}}_n^{
\mathrm{sub}}$. Try the Björner–Wachs EL-labeling: label each cover
$P \lessdot Q$ by the *minimum* (in some ambient order on $[n]
\times [n]$) of the comparabilities forced by $P \to Q$. Check
whether this gives a valid EL-labeling. Specialist-class effort
($\sim 1500$ LoC LaTeX, requires Björner–Wachs expertise).

(F3) **Coordination with mg-d60d**. Mail mg-d60d author with §5
sketch: under (Wedge), cohomological obstruction in $H^{d_n}(F_\ell)$
is the natural target. mg-d60d can proceed with (Wedge) as input,
deferring (Sphere) entirely.

(F4) **PM decision.** Whether to spawn (F1) as a separate polecat
(recommended: yes; tiny budget, high information). (F2) is
specialist-class and should be parked pending (F1) outcome.

### 8.3 Trip-wire / token report

This document was authored in a single polecat session. The 300k
token cap was not approached. No trip-wires fired. No new axioms.
LaTeX-first per ticket §3.

---

## 9. Honest unknowns

For full transparency:

(U1) **Conjecture in §3.4** ($\Delta_3 \simeq S^1$) is supported by
Euler $-1$ but not proven. Direct $H_*$ calculation by hand is
$\sim 100$ chain-group entries — feasible but not in scope here.

(U2) **EL-shellability of $\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$.**
Not addressed beyond noting two obstructions in §4.3.

(U3) **The "right" sphere dimension.** Two heuristics (Coxeter
$n-2$ vs. maximal chain $\binom{n}{2} - 2$) disagree starting at
$n=4$. Which (if either) is right is open.

(U4) **Comparison to $\Pi_n$**. The Björner $(n-1)!$ wedge count
for $\Pi_n$ at dimension $n-3$ would, by direct analogy, suggest
some explicit count for $\mathbf{Pos}_n^{\mathrm{sub}}$ — but
$\mathbf{Pos}_n^{\mathrm{sub}}$ is "denser" than $\Pi_n$ and the
analogy is not tight.

(U5) **mg-d60d's actual cohomological needs.** mg-d60d may turn out
to require only **local** cohomological information (e.g., stalks at
each $P$, not global sections), in which case sphericity is
**irrelevant**. The §5.2 link from (Sphere) to balance is
speculative.

These are noted, not resolved.

---

*Authored by polecat mg-5ee2, branch `polecat-cat-mg-5ee2` →
target `compat-geom-posn-sphere`. Predecessor: mg-296d (eigensheaves)
+ mg-c853 (manifesto). Sibling: cat-mg-d60d (poset cohomology).
2026-05-13.*
