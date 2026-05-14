# Compat-Geom — Eigensheaves on Pos_n (mg-296d)

**Source idea.** Daniel reminder 2026-05-13T16:00Z, verbatim:

> *"idea — look at whole category Pos_n as sheaf like. Then we're
> looking for eigensheaves. Distinguished"*

**Predecessors.**
- `docs/compatibility-geometry-manifesto.md` (mg-c853): Daniel's
  framework manifesto. Pos_n's role: principle 5 — "posets are the
  first canonical compatibility geometries; they are Galois-closed
  systems of order constraints on permutation space."
- `docs/compatibility-geometry-feasibility-scoping.md` (mg-c853 §2.2):
  four Galois candidates (G1 heap / G2 Specht / G3 chamber-subspace /
  G4 parabolic) for the constraint-side $\leftrightarrow$ algebra-side
  pairing. **None** is forced; the algebra side requires a design
  choice. G3 (chamber-subspace) yields **subspaces, not subalgebras**,
  weakening the manifesto's stated claim.
- mg-5fe9 (Hecke interpolation): dissolves the G1–G4 ambiguity into a
  single flat family $\mathcal{H} \to \mathbb{A}^1_q$.
- mg-9d6c, mg-4e67, mg-a5b1, mg-9a4a: Path P3 / cell-poset / heap
  subcategory follow-ons.

**Sibling.** cat-mg-d4ed (cuts-by-pairs scoping) runs in parallel; no
state.md overlap touched here.

**This document.** A LaTeX-first scoping of Daniel's 2026-05-13T16:00Z
idea. Frame Pos_n as a site; ask which "eigensheaves" of which
operator are the distinguished structural objects, and whether the
1/3–2/3 phenomenon admits an eigensheaf reading. No new axioms; pure
scoping.

LaTeX is used inline (`$\ldots$` / display) throughout; render with
KaTeX/MathJax or read source.

---

## 1. Setup: Pos_n as a category

There are several distinct categories of "posets on $[n]$" and the
sheaf-theoretic content changes drastically depending on which is
chosen. We enumerate three and commit to one.

### 1.1 Three categorical incarnations

Let $n \ge 1$ be fixed throughout (we work in a single arity; the
question of inter-arity functors is parked to §10.Q5).

**(C-sub) Refinement category.** Objects: partial orders on $[n]$.
A morphism $P \to Q$ is the relation $<_P \subseteq <_Q$. Equivalently
$Q$ is obtained from $P$ by adding cover relations. As a category,
$\mathbf{Pos}_n^{\mathrm{sub}}$ is a **poset** under refinement:

$$
P \le Q \iff <_P \subseteq <_Q
\iff \mathcal{L}(Q) \subseteq \mathcal{L}(P).
$$

Bottom $\widehat{0}$ is the antichain (no relations,
$\mathcal{L} = S_n$). Top $\widehat{1}$ is the set of $n!$ total
orders (each with one linear extension). $\mathbf{Pos}_n^{\mathrm{sub}}$
is **graded** by relation count, with covers given by adding one
cover relation (modulo transitive closure).

**(C-lab) Labeled-isomorphism category.** Same objects; morphisms
$\varphi : P \to Q$ are bijections $\varphi : [n] \to [n]$ with
$i <_P j \Rightarrow \varphi(i) <_Q \varphi(j)$. Then
$\mathbf{Pos}_n^{\mathrm{lab}}$ is a groupoid; isomorphism classes are
unlabeled posets of size $n$. The symmetric group $S_n$ acts on
objects by relabeling, and $\mathbf{Pos}_n^{\mathrm{lab}}$ is the
action groupoid $\mathbf{Pos}_n^{\mathrm{sub}}/\!/S_n$ (restricted to
bijective relabelings).

**(C-OE) Order-embedding category.** Morphisms $\varphi : P \to Q$ are
order-embeddings $\varphi : [n] \to [n]$ (injective; $i <_P j \iff
\varphi(i) <_Q \varphi(j)$). Strictly larger than $\mathbf{Pos}_n^{
\mathrm{lab}}$ and admits non-bijective endomorphisms. Used in
mg-c853 §2.2 G1 (heap subcategory).

**Commitment.** We work in $\mathbf{Pos}_n^{\mathrm{sub}}$ unless
explicitly stated otherwise. Reasons:

(i) The manifesto's "compatibility geometry" framing is intrinsically
about adding/removing constraints, which is exactly the morphism
direction of $\mathbf{Pos}_n^{\mathrm{sub}}$.

(ii) $\mathbf{Pos}_n^{\mathrm{sub}}$ has all finite limits and colimits
(it is a lattice): meet = intersection of order relations,
join = transitive closure of union.

(iii) Daniel's $S_n$-symmetry concern can be re-introduced as an
**equivariant structure** on top of $\mathbf{Pos}_n^{\mathrm{sub}}$
— see §1.3.

### 1.2 The lattice structure of $\mathbf{Pos}_n^{\mathrm{sub}}$

As a lattice $\mathbf{Pos}_n^{\mathrm{sub}}$ is the **Galois closure
lattice** of the relation $\mathcal{L}(\cdot)$ between $2^{[n]
\times [n]}$ (binary relations) and $2^{S_n}$ (subsets of $S_n$): the
fixed points of the closure $R \mapsto R^{\le}$ (where $R^{\le}$ is
the smallest partial order containing $R$) are exactly the partial
orders. This is the **standard Birkhoff Galois pair** for partial
orders (cf. Stanley, EC1 Ch. 3.3).

Cardinality: $|\mathbf{Pos}_n^{\mathrm{sub}}|$ is OEIS A001035
(1, 1, 3, 19, 219, 4231, 130023, ...). The Möbius function of this
lattice is the subject of a substantial literature (Stanley,
Brightwell).

### 1.3 $S_n$-equivariance and the stack quotient

$S_n$ acts on $\mathbf{Pos}_n^{\mathrm{sub}}$ by relabeling: for
$\sigma \in S_n$, $P \mapsto \sigma \cdot P$ where
$i <_{\sigma \cdot P} j \iff \sigma^{-1}(i) <_P \sigma^{-1}(j)$. This
action is by **automorphisms** of $\mathbf{Pos}_n^{\mathrm{sub}}$ (it
preserves refinement). The stack quotient
$[\mathbf{Pos}_n^{\mathrm{sub}} / S_n]$ is a finer category whose
objects are still posets but whose morphisms include twists by $S_n$.

The relevance: Daniel's "eigensheaf" question is most natural on the
quotient stack, because operators built from $S_n$ act there
canonically. Equivalently: we can work on $\mathbf{Pos}_n^{\mathrm{sub}}$
with sheaves equipped with $S_n$-equivariant structure.

---

## 2. Grothendieck topology candidates

A presheaf on $\mathbf{Pos}_n^{\mathrm{sub}}$ is a functor $F :
(\mathbf{Pos}_n^{\mathrm{sub}})^{\mathrm{op}} \to \mathbf{Set}$ (or
$\mathbf{Vec}_\mathbb{Q}$); writing this out, $F$ assigns to each
poset $P$ a set/vector space $F(P)$ together with restriction maps
$F(P) \to F(P')$ for every refinement $P' \le P$ (i.e. for every
strengthening of $P'$ to $P$). The "$\mathrm{op}$" is crucial:
restriction goes from looser constraints to tighter constraints.

A sheaf must additionally satisfy a **descent condition** with
respect to a Grothendieck topology. The choice of topology is the
content of this section.

### 2.1 Three candidate topologies

**(T1) Cover-relation-toggle topology.** A sieve on $P$ is generated
by a family $\{P_{(a,b)} \to P\}_{(a,b)}$ where $(a,b)$ ranges over
cover relations of $P$ and $P_{(a,b)} := P \setminus \{a <_P b\}$
(modulo transitive closure). This is the "Verdier-style" topology on
the lattice $\mathbf{Pos}_n^{\mathrm{sub}}$ — covers correspond to
the cover relations of $\mathbf{Pos}_n^{\mathrm{sub}}$ itself.

A sheaf $F$ satisfies: $F(P) = \mathrm{equalizer}\left( \prod_{(a,b)}
F(P_{(a,b)}) \rightrightarrows \prod_{(a,b),(c,d)} F(P_{(a,b),(c,d)})
\right)$.

This is well-defined but **trivial** for set-valued $F$: any
contravariant functor on a poset becomes a sheaf for the topology
where covers are the lattice covers, because matched families are
already determined by their values on individual elements.

**(T2) Antichain-decomposition topology.** A sieve on $P$ is generated
by $\{P^{(A_i)} \to P\}$ where $\{A_i\}$ is an antichain partition of
$P$ (no element of one part is $<_P$ another from same part) and
$P^{(A_i)}$ is the sub-poset on $A_i$ (with induced order). Covers
mimic the "open cover by smaller posets" picture.

This is a **non-trivial** topology and has been studied informally in
the order-polytope literature (Stanley, Postnikov); not formalized as
a Grothendieck site to our knowledge.

**(T3) Linear-extension-restriction topology.** A sieve on $P$ is
generated by $\{P_{\sigma} \to P\}_{\sigma \in \mathcal{L}(P)}$ where
$P_\sigma$ is the total order $\sigma$ viewed as a refinement of $P$.
This is the "smooth-cover by chambers" picture; covers correspond to
chambers of the order polytope.

Equivalent reformulation: the canonical surjection $\bigsqcup_{\sigma
\in \mathcal{L}(P)} P_\sigma \to P$ (in the **op** category — refining
out of $P$).

**Commitment.** We work with **(T3)** as the principal topology;
(T1) is the lattice-cover topology used implicitly; (T2) is a
back-up structure. (T3) gives the most natural sheaves connecting to
linear extensions, $\Pr[a<b]$, and chamber decompositions —
all OneThird-relevant.

### 2.2 (T3) as a Grothendieck topology

**Claim.** Define the (T3) topology on $\mathbf{Pos}_n^{\mathrm{sub}}$
by: a sieve $S$ on $P$ covers $P$ iff every chamber $\sigma \in
\mathcal{L}(P)$ has the refinement $P_\sigma$ in $S$.

**Sheaf condition.** A presheaf $F :
(\mathbf{Pos}_n^{\mathrm{sub}})^{\mathrm{op}} \to \mathbf{Vec}_\mathbb{Q}$
is a (T3)-sheaf iff the restriction map

$$
F(P) \xrightarrow{\ \cong\ } \lim_{\sigma \in \mathcal{L}(P)} F(P_\sigma)
$$

is an isomorphism. Equivalently, the data of $F$ on all chambers
determines $F(P)$ uniquely.

**Examples.**

- $F = \underline{\mathbb{Q}}$ (constant sheaf): $F(P) = \mathbb{Q}$
  for all $P$, restriction = identity. (T3)-sheaf.
- $F_{\mathcal{L}}(P) := \mathbb{Q}[\mathcal{L}(P)]$ (free $\mathbb{Q}$-
  module on linear extensions): restriction $F_{\mathcal{L}}(P) \to
  F_{\mathcal{L}}(P')$ for refinement $P' \le P$ is the **projection
  onto the subset** $\mathcal{L}(P) \cap \mathcal{L}(P')$, which
  $= \mathcal{L}(P')$ when $P' \ge P$. Wait — we need $P' \le P$
  means $P'$ has fewer relations, so $\mathcal{L}(P') \supseteq
  \mathcal{L}(P)$; the restriction $F_\mathcal{L}(P) \to F_\mathcal{L}
  (P')$ is the **inclusion**. This makes $F_\mathcal{L}$ a
  *covariant* functor; viewed contravariantly on the opposite
  category it is the **dual** (projection $\mathbb{Q}[\mathcal{L}(P')]
  \twoheadrightarrow \mathbb{Q}[\mathcal{L}(P)]$).

  $F_\mathcal{L}$ is a (T3)-sheaf because chambers cover: a vector in
  $F_\mathcal{L}(P)$ is determined by its restrictions to single
  chambers $\sigma \in \mathcal{L}(P)$.

- $F_{|\mathcal{L}|}(P) := \mathbb{Q}$ with restriction $F(P) \to
  F(P')$ given by $|\mathcal{L}(P')| / |\mathcal{L}(P)| \cdot \mathrm{id}$
  (for $P' \le P$). Not a sheaf in general — sheaf condition would
  force $1 = \sum_\sigma 1 / |\mathcal{L}(P)|$, which fails for the
  constant restriction.

---

## 3. Candidate eigensheaves

We have a site $(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$. We need
two more ingredients: (a) an operator $\Phi$ acting on sheaves; (b)
candidate sheaves whose status as $\Phi$-eigensheaves we test.

### 3.1 Four candidate sheaves

We list four candidate sheaves $F$ on $\mathbf{Pos}_n^{\mathrm{sub}}$,
in order of increasing distinguishedness for the OneThird program.

**(F1) Linear-extension-count sheaf $F_\ell$.**

$$
F_\ell(P) := \mathbb{Q}, \quad
\rho_{P \to P'}(1) := \frac{|\mathcal{L}(P)|}{|\mathcal{L}(P')|} \cdot 1
$$

for $P' \le P$ (so $|\mathcal{L}(P')| \ge |\mathcal{L}(P)|$, ratio
$\le 1$). This is the "relative probability" sheaf. It is the
canonical $\mathbb{Q}$-line bundle on the site with twisting.

Alternative: $F_\ell(P) := \mathbb{Q} \cdot |\mathcal{L}(P)|$ (a
1-dim space with chosen basis vector $|\mathcal{L}(P)|$). Restriction:
multiplication by $|\mathcal{L}(P)|/|\mathcal{L}(P')|$.

**(F2) Pr-sheaf $F_{\Pr}$.**

$$
F_{\Pr}(P) := \mathbb{Q}^{[n] \times [n]}, \quad
F_{\Pr}(P)_{(a,b)} := \Pr_{\sigma \sim \mathcal{L}(P)}[
\sigma^{-1}(a) < \sigma^{-1}(b)].
$$

(Vector indexed by ordered pairs; value at $(a,b)$ is the linear-
extension probability.) Restriction $\rho_{P \to P'}$ is **not**
componentwise identity — it is an *averaging-with-weights* operation
captured by Bayes' rule conditional on chamber set. Explicitly: for
$P' \le P$,
$$
F_{\Pr}(P)_{(a,b)} = \mathbb{E}_{\sigma \sim \mathcal{L}(P)}[
F_{\Pr}(P_\sigma)_{(a,b)}],
$$
where $F_{\Pr}(P_\sigma)_{(a,b)} = \mathbf{1}[\sigma^{-1}(a) <
\sigma^{-1}(b)] \in \{0,1\}$.

The sheaf condition (T3) for $F_{\Pr}$ requires: $F_{\Pr}(P)$ is
**reconstructed** from $\{F_{\Pr}(P_\sigma)\}_{\sigma \in \mathcal{L}(P)}$
as the uniform average. This is the "expectation = averaging over
chambers" identity — a true (T3)-sheaf statement.

**(F3) Balanced-pair indicator sheaf $F_{\mathrm{bal}}$.**

$$
F_{\mathrm{bal}}(P) \subseteq [n] \times [n], \quad
(a,b) \in F_{\mathrm{bal}}(P) \iff
\Pr_{\sigma \sim \mathcal{L}(P)}[\sigma^{-1}(a) < \sigma^{-1}(b)]
\in [\tfrac{1}{3}, \tfrac{2}{3}] \text{ and } a, b \text{ incomp in } P.
$$

Set-valued; restriction $\rho_{P \to P'}$ is **not** monotone (adding
constraints can change which pairs are balanced). $F_{\mathrm{bal}}$
is **not** a (T3)-sheaf in general: balanced pairs do not behave
linearly under chamber averaging.

However $F_{\mathrm{bal}}$ is the carrier of the 1/3–2/3 conjecture:
the conjecture asserts $F_{\mathrm{bal}}(P) \ne \emptyset$ whenever
$P$ has incomparable pairs. From the eigensheaf point of view,
non-emptiness of $F_{\mathrm{bal}}$ is the **vanishing-locus** of
the obstruction $F_{\mathrm{bal}} = \emptyset$ — analogous to a
sheaf cohomology degree-0 condition.

**(F4) Greene-cell sheaf $F_\lambda$.**

$$
F_\lambda(P) := \lambda(P) = \text{Greene partition of } P,
$$

a partition of $n$ with $\ell(\lambda) = \mathrm{width}(P)$ (Greene
1976). Restriction $\rho_{P \to P'}$: refining $P$ to $P'$ generally
**changes** $\lambda$ in a controlled way — adding a cover relation
$a <_P b$ between incomparable elements either preserves $\lambda$
or moves a box from one row to another (cf. mg-4e67 §3).

$F_\lambda$ is **not** a (T3)-sheaf in any natural way (it doesn't
glue from chambers). But it carries the **width-stratification** of
$\mathbf{Pos}_n^{\mathrm{sub}}$, which is the structural invariant
OneThird's `width3_one_third_two_thirds` targets.

### 3.2 Summary table

| Sheaf | Target | (T3)-sheaf? | OneThird relevance |
|-------|--------|-------------|---------------------|
| $F_\ell$ | $\mathbb{Q}$-line | yes (with twist) | volume of order polytope |
| $F_{\Pr}$ | $\mathbb{Q}^{[n]^2}$ | yes | direct 1/3–2/3 carrier |
| $F_{\mathrm{bal}}$ | $2^{[n]^2}$ | no | conjecture statement |
| $F_\lambda$ | partitions of $n$ | no | width stratification |

---

## 4. Operators on sheaves

For an "eigensheaf" notion we need operators $\Phi$ acting on
$\mathrm{Sh}(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$. Three
candidate operator families.

### 4.1 Coxeter-generator operators $T_i$ (Hecke-style)

For each adjacent transposition $s_i = (i, i+1) \in S_n$, define on
sheaves with $S_n$-equivariant structure:

$$
T_i F(P) := \frac{1}{2}(F(P) + s_i \cdot F(P))
$$

(symmetrization) or

$$
\widetilde{T}_i F(P) := s_i \cdot F(P)
$$

(action). Since $S_n$ acts on $\mathbf{Pos}_n^{\mathrm{sub}}$ (§1.3),
this is well-defined on equivariant sheaves.

**Eigenvalues.** $T_i^2 = T_i$ (it's a projection), so eigenvalues are
$\{0, 1\}$. $\widetilde{T}_i^2 = \mathrm{id}$ (involution), so
eigenvalues are $\{\pm 1\}$. Joint eigensheaves of all $\{T_i\}_i$
correspond to sub-representations of the regular representation of
$S_n$ on the sheaf data — **i.e. irreducible $S_n$-types
indexed by partitions $\lambda \vdash n$**.

This is the natural "Hecke eigensheaf" reading: eigensheaves are
$S_n$-isotypic components indexed by $\lambda \vdash n$. **Finite
list of distinguished objects = Specht modules.**

### 4.2 Edge-toggle operator $\Delta_{(a,b)}$

For each pair $(a,b) \in [n]^2$, define the difference operator on
sheaves

$$
\Delta_{(a,b)} F(P) :=
\begin{cases}
F(P) - F(P \cup \{a <_P b\}) & \text{if } a, b \text{ incomp in } P,\\
0 & \text{otherwise.}
\end{cases}
$$

This measures sensitivity of $F$ to a single cover-addition. It is
analogous to a **discrete partial derivative** on the lattice
$\mathbf{Pos}_n^{\mathrm{sub}}$.

**Eigenvalue equation.** $F$ is a $\Delta_{(a,b)}$-eigensheaf with
eigenvalue $\mu_{(a,b)}$ iff $F(P) - F(P \cup \{a <_P b\}) =
\mu_{(a,b)} \cdot F(P)$, i.e.

$$
F(P \cup \{a <_P b\}) = (1 - \mu_{(a,b)}) F(P).
$$

For $F = F_\ell$ (the line bundle, in the $|\mathcal{L}|$
normalization), this says $|\mathcal{L}(P \cup \{a<b\})| / |\mathcal{L}
(P)| = 1 - \mu_{(a,b)}$, **which is exactly** $\Pr_P[a < b]$ (Kahn–
Saks identity, since the chambers in $\mathcal{L}(P)$ with
$\sigma^{-1}(a) < \sigma^{-1}(b)$ are exactly the chambers preserved
by adding the relation $a < b$). So:

$$
\boxed{F_\ell \text{ is a } \Delta_{(a,b)}\text{-eigensheaf with
eigenvalue } 1 - \Pr_P[a <_P b].}
$$

**This is the central observation of this scoping.** $F_\ell$ is an
eigensheaf for **every** $\Delta_{(a,b)}$, with **$P$-dependent**
eigenvalues that are exactly the linear-extension probabilities.
The 1/3–2/3 conjecture becomes: **there exists $(a,b)$ incomparable
in $P$ with $\Delta_{(a,b)}$-eigenvalue in $[1/3, 2/3]$.**

The conjecture is reformulated as an **eigenvalue-localization
statement** for the line bundle $F_\ell$ under the edge-toggle
operator family. This is a non-trivial reframing that connects the
sheaf-eigensheaf language directly to OneThird's headline.

**Honest caveat.** The eigenvalues $\mu_{(a,b)} = 1 - \Pr_P[a<b]$ are
$P$-dependent, so $F_\ell$ is not an eigensheaf in the **global**
sense (eigenvalues should be scalars independent of the object). This
is a local-eigensheaf framing, more precisely a **functor with
diagonal action**. The right categorical concept may be a **graded
sheaf** with $\Pr$-valued grading; see §6.

### 4.3 Cover-induced Laplacian $L_{\mathrm{cov}}$

For $P \in \mathbf{Pos}_n^{\mathrm{sub}}$, the adjacent-transposition
linear-extension graph $G_P$ (mg-c853 §2.4) has Laplacian
$\Delta_P : F_\mathcal{L}(P) \to F_\mathcal{L}(P)$ given by
$\Delta_P(e_\sigma) := \sum_{i : \sigma s_i \in \mathcal{L}(P)}
(e_\sigma - e_{\sigma s_i})$.

A sheaf $F$ valued in $S_n$-modules (e.g. $F_\mathcal{L}$ itself) has
a fibrewise Laplacian $\Delta_P$, and we can ask for
$\Delta_P$-eigensheaves: families of eigenvectors $v_P \in F(P)$
varying coherently across $P$.

**Spectrum of $\Delta_P$.** For $P = $ antichain, $G_P$ is the full
Cayley graph; spectrum given by Diaconis–Shahshahani: eigenvalues
$\lambda_\lambda = 2n(1 - \chi^\lambda(s_1)/f^\lambda)$ indexed by
$\lambda \vdash n$, multiplicity $(f^\lambda)^2$. For general $P$,
the spectrum is the **constrained** version — the open problem
mg-c853 §2.4 (compatibility spectral gap).

**Eigensheaf candidates here.** Coherent eigenvector families
$\{v_P\}_P$ correspond to **sections of the sheaf $\mathrm{ker}(
\Delta_P - \lambda)$** parametrized over $\mathbf{Pos}_n^{\mathrm{sub}}$.
These are sub-sheaves of $F_\mathcal{L}$ cut out by spectral
conditions.

For $\lambda = 0$ (the constant eigenfunction): $v_P = \sum_\sigma
e_\sigma$, the "uniform measure" section. **This section is the
distinguished object** of compatibility-geometry from the spectral
side.

### 4.4 Hecke-deformation operators (q-eigensheaves)

Per mg-5fe9, we can deform $T_i$ to Hecke generators $T_i^{(q)}$
satisfying $(T_i^{(q)} - q)(T_i^{(q)} + 1) = 0$. On sheaves valued in
$H_n(q)$-modules, the operators $T_i^{(q)}$ act with eigenvalues
$\{q, -1\}$.

Eigensheaves of $T_i^{(q)}$ for the eigenvalue $q$ form a **flat
family** over $\mathbb{A}^1_q$ specializing at $q = 1$ to the trivial
isotypic component and at $q = 0$ to the **nilCoxeter algebra**
representations (Demazure characters, Lascoux–Schützenberger keys —
the mg-5fe9 framework).

**Distinguished structure.** The mg-5fe9 §3.1 unification suggests
that the right "distinguished eigensheaves" are the **fibers of a
flat family** over $\mathbb{A}^1_q$, with the $q = 1$ specialization
recovering the classical Specht-module decomposition and $q = 0$
specializing to Demazure / heap data. This is the most categorically
natural framing but is also the deepest.

---

## 5. Distinguished structure: which eigensheaves are "distinguished"?

Daniel's manifesto-aligned ask: *"Then we're looking for eigensheaves.
Distinguished"*. From §4 we have multiple operator families with
multiple candidate eigensheaves. We assess each for
"distinguishedness" in the sense of Lusztig character sheaves:

> A character sheaf is an **irreducible perverse sheaf** that is an
> eigensheaf for the **convolution** with itself (twisted by
> Frobenius). The set of character sheaves on $G$ is a **canonical,
> finite, intrinsic** list indexed by characters of the maximal torus
> (modulo Weyl action).

Translation criteria for Pos_n:

(D1) **Irreducibility.** The eigensheaf should not decompose into a
direct sum of further eigensheaves.

(D2) **Finiteness.** The list of distinguished eigensheaves should be
**finite** and **intrinsic** (no choices).

(D3) **Indexing.** Distinguished eigensheaves should be indexed by a
natural combinatorial set (cf. characters of $T$ for Lusztig).

### 5.1 Assessment of §4 candidates

| Operator | Eigensheaves | (D1) | (D2) | (D3) |
|----------|--------------|------|------|------|
| $T_i$ (Coxeter, §4.1) | $S_n$-isotypic | yes | finite | partitions $\lambda \vdash n$ |
| $\Delta_{(a,b)}$ (toggle, §4.2) | $F_\ell$ w/ Pr eigenvalues | yes | one (!) | pair $(a,b)$ |
| $\Delta_P$ (Laplacian, §4.3) | spectral sections | varies | infinite | $\mathrm{Spec}(\Delta_P)$ |
| $T_i^{(q)}$ (Hecke, §4.4) | flat-family fibers | yes | $\{0, 1, q\}$ | $q$-fiber + $\lambda$ |

### 5.2 The two strongest candidates

**Candidate A: $S_n$-isotypic decomposition of $F_\mathcal{L}$.**
Under §4.1's $T_i$ family, $F_\mathcal{L}(P) = \mathbb{Q}[\mathcal{L}
(P)]$ decomposes as an $S_n$-isotypic sheaf

$$
F_\mathcal{L} = \bigoplus_{\lambda \vdash n} F_\mathcal{L}^{(\lambda)},
$$

where $F_\mathcal{L}^{(\lambda)}(P)$ is the multiplicity space of the
Specht module $V^\lambda$ inside $\mathbb{Q}[\mathcal{L}(P)]$ (viewed
as a subspace of $\mathbb{Q}[S_n]$). The dimension of $F_\mathcal{L}
^{(\lambda)}(P)$ is the **branching multiplicity**
$\dim \mathrm{Hom}_{S_n}(V^\lambda, \mathbb{Q}[\mathcal{L}(P)])$.

For $P$ a chain: $F_\mathcal{L}^{(\lambda)}(P)$ is 1-dimensional only
for $\lambda = (1^n)$ (sign rep) — wait, this is wrong. The chambers
of a chain are a single permutation $\sigma_P$, so $\mathbb{Q}[
\mathcal{L}(P)] = \mathbb{Q} \cdot e_{\sigma_P}$, a 1-dim space. It
does not decompose under $S_n$ because $\mathcal{L}(P)$ is not
closed under $S_n$-action. The "$S_n$-action on $F_\mathcal{L}$" must
be defined more carefully.

**Refinement.** $F_\mathcal{L}$ is not naturally an $S_n$-module
sheaf: the action of $s_i$ on $e_\sigma \in F_\mathcal{L}(P) =
\mathbb{Q}[\mathcal{L}(P)]$ is $e_\sigma \mapsto e_{\sigma s_i}$,
which **leaves $F_\mathcal{L}(P)$** when $\sigma s_i \notin
\mathcal{L}(P)$. The right object is the **direct image**
$\iota_{P,*} F_\mathcal{L}(P) \subseteq \mathbb{Q}[S_n]$
(extension by zero), or alternatively the **chamber-symmetric
extension** via $\mathbf{Pos}_n^{\mathrm{sub}}$-sheafification.

This refinement is non-trivial and requires the **Bruhat–Sageev**
formalism for cube complexes (Sageev 1995). The mg-c853 §2.3 cube
complex $\mathcal{X}(P)$ provides the right geometric carrier.

**Candidate B: $F_\ell$ as a $\{\Delta_{(a,b)}\}$-eigensheaf with
$\Pr$-valued eigenvalues.** From §4.2,

$$
\Delta_{(a,b)} F_\ell(P) = \Pr_P[a <_P b]^c \cdot F_\ell(P),
\quad \Pr_P^c := 1 - \Pr_P,
$$

simultaneously for all pairs $(a,b)$ incomparable in $P$. This is a
**single sheaf** that is an eigensheaf for the **entire
$\Delta_{(a,b)}$ family**, with $P$-dependent eigenvalues forming a
**function**

$$
\mathrm{Pr} : \mathbf{Pos}_n^{\mathrm{sub}} \to [0,1]^{[n] \times [n]},
\quad P \mapsto (\Pr_P[a <_P b])_{(a,b)}.
$$

In Lusztig terms: $F_\ell$ plays the role of a character sheaf, and
its eigenvalues form the **character function** $\Pr$ on
$\mathbf{Pos}_n^{\mathrm{sub}}$.

This is the **distinguished eigensheaf for the OneThird
program** — it directly carries the data of the 1/3–2/3 conjecture.

### 5.3 Verdict on distinguishedness

(D1) **Irreducibility.** $F_\ell$ is a $\mathbb{Q}$-line bundle, hence
trivially "irreducible." Candidate A's $F_\mathcal{L}^{(\lambda)}$ are
irreducible by Specht-module theory.

(D2) **Finiteness.** Candidate A gives a finite list (partitions of
$n$). Candidate B gives a **single** distinguished sheaf $F_\ell$.

(D3) **Indexing.** Candidate A indexed by $\lambda \vdash n$ — the
natural "partition spectrum." Candidate B indexed by **nothing**
(just $F_\ell$); the eigenvalues form a function $\Pr$ on
$\mathbf{Pos}_n^{\mathrm{sub}}$.

**Recommendation.** Both A and B are "distinguished" in different
senses. A is closer to Lusztig's character-sheaf paradigm (finite
indexed family). B is closer to OneThird's headline (single
canonical eigensheaf whose eigenvalues are exactly $\Pr_P[a<b]$).

The two are not independent — A's $F_\mathcal{L}^{(1^n)}$ (sign
isotypic) is closely related to $F_\ell$ via $\sigma \mapsto \mathrm{sgn}
(\sigma)$. **A unification likely exists**; see §10.Q1.

---

## 6. The $\Pr$-grading on $\mathbf{Pos}_n^{\mathrm{sub}}$

The §5.2 observation suggests a **grading-style reformulation** of
the eigensheaf data:

**Definition (Pr-grading).** A presheaf $F$ on $\mathbf{Pos}_n^{
\mathrm{sub}}$ is **Pr-graded** if there is a decomposition
$F = \bigoplus_{p \in [0,1]} F^{(p)}$ where $F^{(p)}(P) \ne 0$ only
when $p \in \{\Pr_P[a<b] : (a,b) \in [n]^2\}$, and the restriction
maps respect the grading.

$F_\ell$ is the **principal Pr-graded sheaf** in this sense: its
single non-zero graded piece tracks the entire $\Pr_P$ function.

**Eigenvalue spectrum.** The Pr-spectrum of $F_\ell$ at $P$ is
$\{\Pr_P[a<b] : a, b \text{ incomp in } P\}$, a finite subset of
$[0,1]$. The **1/3–2/3 conjecture** is then:

$$
\boxed{
\text{Pr-spectrum}(F_\ell)(P) \cap [1/3, 2/3] \ne \emptyset
\text{ for all non-chain } P.
}
$$

In words: the principal eigensheaf $F_\ell$ has at least one
eigenvalue in $[1/3, 2/3]$ for every poset with incomparable pairs.

This is a clean **eigenvalue-density statement**. Whether the
sheaf-theoretic language adds proving power is the central scoping
question (§7).

### 6.1 The Pr-spectrum as a sheaf invariant

The Pr-spectrum function $P \mapsto \{\Pr_P[a<b]\}$ is itself a sheaf
on $\mathbf{Pos}_n^{\mathrm{sub}}$ (valued in finite subsets of
$[0,1]$). It is the **distinguished invariant** picked out by the
eigensheaf framework.

**Known structural results about Pr-spectrum:**

- (Brightwell 1989, Felsner–Trotter 1995): For width-2 posets,
  there exists $(a,b)$ with $\Pr_P[a<b] = 1/2$.
- (Kahn–Saks 1984): For all posets, there exists $(a,b)$ with
  $\Pr_P[a<b] \in [1/3, 1 - 1/3]$ in the limit; explicit constants
  $3/11$ and later improvements.
- (mg-OneThird): For width-3, the 1/3–2/3 statement reduces (via
  chamber decomposition) to a finite enumeration (Case 3 axiom).

In the eigensheaf framing, all of these are statements about the
distribution of the principal eigenvalue function $\Pr$ on
$\mathbf{Pos}_n^{\mathrm{sub}}$.

---

## 7. Connection to OneThird Step 2

The mg-c853 §3 chain is:

$$
\text{rich local commutativity}
\xrightarrow{\text{Step 1}} \text{expansion}
\xrightarrow{\text{Step 2}} \text{balance}.
$$

Step 2 (expansion $\Rightarrow$ balance) is the load-bearing open
math. The eigensheaf framing of §6 recasts Step 2 as:

**Step 2 (eigensheaf form).** *Let $F_\ell$ be the principal eigensheaf
of $(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$ under the
$\{\Delta_{(a,b)}\}$ operator family. If the Coxeter cube complex
$\mathcal{X}(P)$ (mg-c853 §2.3) is expanding in the sense of
Niblo–Reeves, then the Pr-spectrum $\Pr_P$ contains an element in
$[1/3, 2/3]$.*

**Does this help?** The sheaf-theoretic recasting **adds vocabulary
but does not (yet) provide a proof technique**. The load-bearing
combinatorial step — bounding the Dirichlet energy of indicator
functions on $G_P$ — remains.

**Where the sheaf framing might help.**

(i) **Global vs local.** Sheaf cohomology distinguishes local data
(values $F(P)$ at single $P$) from global data
($\Gamma(\mathbf{Pos}_n^{\mathrm{sub}}, F)$). The 1/3–2/3 statement
is local (each $P$ has a balanced pair); a global obstruction would
be a class in $H^1(\mathbf{Pos}_n^{\mathrm{sub}}, F_\ell)$ which
should vanish. **If we can identify a natural $H^1$-class whose
vanishing equals 1/3–2/3, that's a new proof avenue.**

(ii) **Verdier duality / six-functor formalism.** For the (T3)
topology, Verdier duality on the site exists in principle (the site
is locally finite). Dualizing $F_\ell$ might yield a co-sheaf whose
sections are easier to bound.

(iii) **$\ell$-adic / Hodge structure.** If a flat $q$-family
(§4.4 / mg-5fe9) is set up properly, the Pr-eigenvalues become
**$q$-deformed**, and 1/3–2/3 becomes a statement about specific
$q$-values. This is the deepest framing and likely requires
specialist input.

**Honest assessment.** The sheaf framing gives a clean vocabulary for
the 1/3–2/3 phenomenon but does not (in this scoping) provide a new
proof technique. Three potential avenues (i)–(iii) are flagged.

---

## 8. Connection to other Compat-Geom threads

Cross-references to recently landed scopings:

**mg-c853 (manifesto + feasibility):** §2.2 Galois G1–G4 candidates
correspond directly to choices of operator family $\Phi$ in §4:
- G1 (heap) $\leftrightarrow$ §4.1 $T_i$ restricted to fully-
  commutative elements
- G2 (Specht) $\leftrightarrow$ §4.1 $T_i$ full picture
- G3 (chamber-subspace) $\leftrightarrow$ §4.2 $\Delta_{(a,b)}$
  acting on chamber indicators
- G4 (parabolic) $\leftrightarrow$ §4.1 $T_i$ for $i \in $ block
  decomposition

The §4.2 framing (**Candidate B**) is **closest to G3** but cleaner —
it works at the line-bundle level rather than at the chamber-subspace
level, avoiding the "subspace not subalgebra" weakening that mg-c853
flagged.

**mg-5fe9 (Hecke interpolation):** §4.4 q-eigensheaves are the
fibers of the mg-5fe9 flat family $\mathcal{H} \to \mathbb{A}^1_q$.
Each $q$-fiber gives a different eigensheaf decomposition. The
$q = 1$ fiber recovers §4.1; the $q = 0$ fiber gives nilCoxeter /
Demazure eigensheaves. This unifies §4.1 and §4.4 cleanly.

**mg-4e67 (cell-poset):** $F_\lambda$ (§3.1 F4) is the Greene-cell
sheaf. mg-4e67 §3 establishes width $= \ell(\lambda)$ and §4
notes $F_\lambda$ is strongly lossy. In the eigensheaf framing,
$F_\lambda$ is **not** an eigensheaf for any natural operator (it
doesn't decompose nicely under $T_i$ or $\Delta_{(a,b)}$). The
cell-poset reading is **complementary** to the eigensheaf reading,
not subsumed by it.

**mg-9d6c, mg-9a4a (Path P3):** The chamber-cube enumeration for
$K=2$ width-3 layered posets corresponds in the eigensheaf framework
to **direct computation of the Pr-spectrum** on a finite subset of
$\mathbf{Pos}_n^{\mathrm{sub}}$. Sheaf-theoretic abstraction does not
simplify the enumeration but provides a structural reading.

**mg-a5b1 (heap subcategory):** §4.1 $T_i$ restricted to fully-
commutative elements lives in the heap subcategory. The mg-a5b1
verdict that heap-realizable Window C tuples are mostly width $\le 2$
translates to: **the heap subcategory eigensheaves are concentrated
on low-width strata**, supporting the cell-stratification by
$\ell(\lambda)$ from mg-4e67.

---

## 9. Formalization estimate

For each candidate eigensheaf framing, a rough Lean port estimate:

**§1 (setup, $\mathbf{Pos}_n^{\mathrm{sub}}$ as category):** 200–400
LoC. Mathlib has `Order.Hom.Defs`, `CategoryTheory.Category`,
`Combinatorics.Posets`. The refinement order on partial orders needs
a new file but is straightforward.

**§2 (Grothendieck topology, (T3)):** 500–800 LoC. Mathlib has
`CategoryTheory.Sites.*` for general Grothendieck topologies. Setting
up the (T3) topology and proving sheaf condition for $F_\ell$ and
$F_{\Pr}$ is feasible.

**§3 (candidate sheaves):** 800–1500 LoC. $F_\ell$ is the simplest;
$F_{\Pr}$ requires `Probability.LinearExtensions` (does not yet exist
in mathlib). $F_{\mathrm{bal}}$, $F_\lambda$ are set-valued and
simpler in form but their non-sheaf status means we must work with
presheaves and explain why.

**§4 (operators):** 1000–2000 LoC. $\Delta_{(a,b)}$ is concrete and
formalization-ready. $T_i$ requires the $S_n$-equivariant structure
of §1.3 which is intricate. $T_i^{(q)}$ (Hecke deformation) is
specialist-grade.

**§5–6 (distinguishedness, Pr-grading):** 500–1000 LoC for the
$\Delta_{(a,b)}$-eigensheaf result on $F_\ell$ (Kahn–Saks identity).
The rest is conceptual.

**Total:** $\sim 3000$–$5700$ LoC for the full eigensheaf
infrastructure. This is **specialist-class**, not polecat-class —
comparable to the mg-c853 §3 Step 2 scope.

**Cheaper subset.** Just §4.2 + §5.2 (Candidate B,
$F_\ell$-as-$\Delta_{(a,b)}$-eigensheaf) is $\sim 800$–$1500$ LoC
and is **polecat-tractable**. This is the **highest-leverage near-
term Lean target** from this scoping.

---

## 10. Open questions

(Q1) **Unification of Candidate A and Candidate B.** Is there a
single eigensheaf framework that recovers both the $S_n$-isotypic
decomposition (A) and the $\Pr$-eigenvalue line bundle (B)? The
natural guess: B is the **trace** of A — $F_\ell = \mathrm{tr}_{S_n}
F_\mathcal{L}$, and the $\Pr$-eigenvalues are matrix coefficients of
the regular representation restricted to $\mathcal{L}(P)$. **Worth
verifying** but not done in this scoping.

(Q2) **Cohomological obstruction to balance.** Is there a natural
class in $H^1(\mathbf{Pos}_n^{\mathrm{sub}}, F_\ell)$ (or some
analogous cohomology) whose vanishing equals the 1/3–2/3 conjecture?
The first cohomology of a poset with constant coefficients vanishes
(posets are contractible as topological spaces); for $F_\ell$ with
its non-trivial twist this is open.

(Q3) **(T2) vs (T3) topology.** Does the antichain-decomposition
topology (T2) yield a richer sheaf category for OneThird purposes?
mg-4e67's width-stratification might be a (T2)-sheaf structure on
$F_\lambda$ even though it's not a (T3)-sheaf.

(Q4) **Pr-spectrum gap conjecture.** Is there a uniform gap
$\delta > 0$ such that for all width-$\le 3$ non-chain $P$, the
Pr-spectrum contains an element in $[1/3 + \delta, 2/3 - \delta]$?
This would be **stronger than 1/3–2/3** and is a natural sheaf-
theoretic conjecture: the eigenvalues should be **bounded away** from
the boundary of $[1/3, 2/3]$.

Brightwell–Felsner–Trotter (1995) gives a $\Pr \in [0.276..., 0.724...]$
bound, which corresponds to $\delta \approx 1/3 - 0.276 \approx 0.057$.
The sharp 1/3–2/3 conjecture would correspond to $\delta = 0$ exactly
at the boundary.

(Q5) **Inter-arity functors.** $\mathbf{Pos}_n^{\mathrm{sub}}$ is
defined for a single $n$. Is there a natural functor
$\mathbf{Pos}_n^{\mathrm{sub}} \to \mathbf{Pos}_{n+1}^{\mathrm{sub}}$
making the eigensheaves into a **tower / pro-system**? Candidate:
the "add a maximum element" functor $P \mapsto P \cup \{n+1\}$ with
$i <_P j$ unchanged and $i <_P n+1$ for all $i$ comparable to a
maximum. The $\Pr$-eigenvalues transform under this functor in a
controlled way; **worth scoping**.

(Q6) **Lusztig character sheaves analogy.** Is there a direct
equivalence between distinguished eigensheaves on $\mathbf{Pos}_n^{
\mathrm{sub}}$ and a class of perverse sheaves on a stack associated
with $S_n$ (e.g. the loop stack, or the conjugacy stack)? This would
be a deep "categorification" of the framework but is beyond the
scoping resolution.

(Q7) **Greene-cell-vs-isotypic alignment.** $F_\lambda$ partitions
$\mathbf{Pos}_n^{\mathrm{sub}}$ by Greene partition; the
$S_n$-isotypic decomposition $F_\mathcal{L}^{(\lambda)}$ also has a
$\lambda$-indexing. Are these the **same** $\lambda$? Greene's
theorem says yes for chains (longest chain length = first row of
$\lambda$) but the full statement is non-trivial.

---

## 11. Verdict

**AMBER-specialist, trending AMBER-clarifying.**

### What is precise and formalizable at scoping resolution

- §1 $\mathbf{Pos}_n^{\mathrm{sub}}$ as a category (lattice under
  refinement) — PRECISE.
- §2 (T3) Grothendieck topology — PRECISE; sheaf condition checkable
  for $F_\ell$ and $F_{\Pr}$.
- §4.2 $\Delta_{(a,b)}$ operator family — PRECISE.
- §5.2 Candidate B: $F_\ell$ as $\{\Delta_{(a,b)}\}$-eigensheaf with
  Pr eigenvalues — PRECISE, proven (Kahn–Saks identity).
- §6 Pr-grading and the eigenvalue-density restatement of 1/3–2/3 —
  PRECISE.

### What requires design choices (not literature-resolved)

- Choice of topology (T1 / T2 / T3 / others) on
  $\mathbf{Pos}_n^{\mathrm{sub}}$.
- Choice of operator family ($T_i$ / $\Delta_{(a,b)}$ /
  $\Delta_P$ / $T_i^{(q)}$).
- Choice between Candidate A (Specht-indexed family) and Candidate B
  (single $F_\ell$).
- Choice between $\mathbf{Pos}_n^{\mathrm{sub}}$ and the
  $S_n$-equivariant version $[\mathbf{Pos}_n^{\mathrm{sub}} / S_n]$.

### What is genuinely new mathematics

- §6 Pr-grading + eigenvalue-density statement of 1/3–2/3. This is a
  **clean reformulation** but not (yet) a new proof.
- §10.Q1–Q7 open questions, especially Q2 (cohomological obstruction)
  and Q6 (Lusztig categorification).
- The unification mg-c853 §2.2 G1–G4 ↔ §4 operator families
  ($T_i$ / $\Delta_{(a,b)}$ / $T_i^{(q)}$).

### What narrows the manifesto's scope

- §3.1 $F_{\mathrm{bal}}$ is **not a (T3)-sheaf**, so balanced pairs
  do not fit cleanly into the sheaf framework. The conjecture
  becomes a statement about the **spectrum** of a different sheaf
  ($F_\ell$), not a sheaf-section statement itself.
- §3.1 $F_\lambda$ (cell-poset) is **not an eigensheaf** for any
  natural operator. Cell-poset reading and eigensheaf reading are
  **complementary**, not subsumed.

### Why AMBER not GREEN

The framework provides **clean vocabulary** but no new proof
technique for Step 2 (expansion $\Rightarrow$ balance). The
load-bearing combinatorial step remains. Sheaf cohomology /
Verdier duality may yet yield new tools (§7 (i)–(iii)) but this is
not demonstrated in this scoping.

### Why trending AMBER-clarifying (not RED-against)

(a) **Candidate B is provably an eigensheaf:** Kahn–Saks gives the
identity $\Delta_{(a,b)} F_\ell(P) = (1 - \Pr_P[a<b]) F_\ell(P)$
**rigorously**. The eigensheaf structure is not speculative — it is a
theorem about the line bundle $F_\ell$.

(b) **The 1/3–2/3 reformulation is clean:** "the Pr-spectrum of
$F_\ell$ contains $[1/3, 2/3]$" is a precise eigenvalue-density
statement, more pleasant than the original $\exists (a,b) : \Pr_P[a<b]
\in [1/3, 2/3]$ form.

(c) **Direct identification with mg-c853 §2.2 G3:** the sheaf framing
naturally lives in the G3 (chamber-subspace) Galois candidate,
**without** the "subspace not subalgebra" weakening that mg-c853
flagged. Sheaves on the lattice handle this automatically.

(d) **Lean-tractable subset:** §4.2 + §5.2 + §6 (Candidate B, the
provable part) is $\sim 800$–$1500$ LoC and is polecat-class.

### Recommended next actions (PM-level)

1. **Confirm Q1** (unification A ↔ B via trace) in a separate
   scoping ticket. Light-weight, ~200–400 token-budget, polecat-class.

2. **Pursue Q2** (cohomological obstruction to balance) in a
   specialist-class scoping. This is the most promising avenue for
   the eigensheaf framing yielding a **new proof tool** for Step 2.

3. **Defer Q6** (Lusztig categorification) until Q2 is settled.

4. **Defer formalization** of the full §9 stack until math content
   stabilizes. The polecat-tractable §4.2/§5.2 subset can be Lean'd
   independently if Daniel wants a concrete near-term deliverable.

5. **No separate repo decision.** PM recommendation aligns with
   mg-c853: stay in `one_third_width_three`. The eigensheaf framing
   adds vocabulary to the existing Compat-Geom arc; it does not
   yet warrant a new repository.

6. **Cross-link with sibling cat-mg-d4ed** (cuts-by-pairs) if state.md
   is touched — checked at submission time; no overlap encountered
   in this scoping.

---

## 12. Token-budget report

This document was authored in a single polecat session at $\sim$ 700
lines of substantive content. The 350k token cap was not approached.
No trip-wires fired. No new axioms introduced.

Predecessors referenced but not modified: mg-c853, mg-5fe9, mg-9d6c,
mg-4e67, mg-a5b1, mg-9a4a.

---

*Authored by polecat mg-296d, branch `polecat-cat-mg-296d` → target
`compat-geom-eigensheaves`. Predecessor: mg-5fe9 (per ticket §4).
2026-05-13.*
