# Compatibility Geometry — Hecke interpolation scoping (mg-5fe9)

**Companion to** `docs/compatibility-geometry-manifesto.md` (Daniel's
manifesto, 2026-05-12, mg-c853 at `0d8f438`) and
`docs/compatibility-geometry-feasibility-scoping.md` (mg-c853
feasibility scoping, AMBER-specialist verdict). Sister scoping doc:
`docs/compatibility-geometry-pathP3-scoping.md` (mg-9d6c, AMBER-narrow,
applied axiom-narrowing angle). This document scopes a new and
*independent* research direction articulated by Daniel on 2026-05-13:

> *"compatibility geometry idea — we want constraints (posets) to
> arise intrinsically from the algebra. One way maybe is to look at
> hecke operator between coxeter nil q=0 and the group algebra when
> q=1 to bridge constraint geometry with group algebra"*
> — Daniel, 2026-05-13T11:23Z (verbatim)

This is at the manifesto's **foundational** level — the Grothendieck-
style abstraction question: how does the Galois correspondence
between constraint systems and admissible regions arise *intrinsically*
from the noncommutative ambient algebra? It is distinct from Path P3
(`mg-9d6c`), which is the applied axiom-narrowing angle.

LaTeX is used inline ($\ldots$ / display) throughout; render with
KaTeX/MathJax or read source.

**Verdict preview.** **AMBER-specialist, trending GREEN-promising**
(matching `mg-c853` overall). The Hecke interpolation
$H_n(q)$ between $q=0$ (nilCoxeter $N_n$) and $q=1$ (group algebra
$\mathbb{C}[S_n]$) is a **genuine, literature-supported candidate for
the Galois bridge** the manifesto calls for: $N_n$ is naturally
poset-flavored (Demazure / 0-Hecke / Lascoux-Schützenberger theory
realizes ideals of Bruhat order as modules), while $\mathbb{C}[S_n]$
is the ambient permutation universe; the flat family
$\mathcal{H} \to \mathrm{Spec}\,\mathbb{C}[q,q^{-1}]$ realizes
constraint-side $\leftrightarrow$ admissible-side as **two fibers
of one geometric object**. This is the cleanest realization of the
manifesto's "constraints arise intrinsically from the algebra"
principle examined to date. However, the OneThird-side connection
(§5) routes back through the **same Garland-style spectral expansion
step** parked by `mg-c853 §3 Step 2` as load-bearing open math
requiring specialist input. Hecke language **reshapes and clarifies**
the blocker (puts it in a more functorial vocabulary, with
Kazhdan-Lusztig polynomial scaffolding) but does **not** bypass it.

---

## 1. Recap

### 1.1 Manifesto principles relevant here

The manifesto (`mg-c853` at `0d8f438`,
`docs/compatibility-geometry-manifesto.md`) articulates six core
principles. The two directly load-bearing for the Hecke direction:

> **Principle 1.** Constraint systems are primary. Global coherent
> states are secondary.
>
> **Principle 5.** Posets are the first canonical compatibility
> geometries. They are Galois-closed systems of order constraints on
> permutation space.

Daniel's 2026-05-13 idea sharpens the *intrinsic* qualifier: posets
should not be **added on top of** the noncommutative algebra
$\mathbb{C}[S_n]$ as external data, but should **emerge** from
within it via a structural mechanism. The Hecke specialization
$H_n(q) \rightsquigarrow N_n$ at $q=0$ is proposed as that mechanism.

### 1.2 What mg-c853 §2.3 already flagged

The feasibility scoping (`mg-c853`) §2.3 (second worked example) and
§4 noted Hecke $H_n(q)$ as a candidate second-example passing the
abstraction transfer test:

> *"Hecke $H_n(q)$ passes the abstraction transfer test: all four
> manifesto sub-targets [local commutativity, Galois correspondence,
> cubical geometry, spectral invariants] deform."*
> — `mg-c853 §4`

But mg-c853 §4 treated Hecke purely as a *deformation companion* to
$\mathbb{C}[S_n]$ — confirming the manifesto framework is not type-A-
specific. It did **not** examine whether the $q=0 \leftrightarrow q=1$
*interpolation itself* could be the Galois bridge. That is the
question this scoping addresses.

### 1.3 What mg-9d6c (Path P3) established

The Path P3 scoping (`mg-9d6c`) reached an **AMBER-narrow** verdict:
the cube-complex / chamber decomposition framework of mg-c853 §2.3
can deliver axiom-*narrowing* for the OneThird residual `case3` axiom
on a strict sub-window (Window C, $K=4, w=1$ plus a $K=3$ sliver),
but cannot **eliminate** the axiom — the bulk of the residual
parameter range requires the same Garland-style high-dimensional-
expander spectral argument flagged as load-bearing open math in
`mg-c853 §3 Step 2`.

For the Hecke direction the relevance is:

(a) The manifesto framework's load-bearing open math is **already
identified** (`mg-c853 §3 Step 2`). The question for this scoping
is not whether Hecke fixes it (it doesn't — see §5) but whether
Hecke gives a **different, more functorial language** for it
(probably yes — see §5.2).

(b) `mg-9d6c` is running concurrently as `cat-mg-9a4a` on the same
source repo; the working understanding per the dispatch note is
that the two branches (`compat-geom-pathP3` for the applied angle,
`compat-geom-hecke-scoping` for this foundational angle) are
**independent**. We coordinate only on shared `state.md`-style
artifacts (none touched by this scoping).

### 1.4 Daniel's idea, restated precisely

The candidate framing this scoping makes precise:

**(Hecke-Galois candidate, informal).** The flat family

$$
\mathcal{H} \;:=\; \text{generic Iwahori-Hecke algebra of type } A_{n-1}
\;\text{ over } R := \mathbb{C}[q,q^{-1}]
$$

has two distinguished fibers:

- $\mathcal{H} \otimes_R \mathbb{C}_{q=1} \;\cong\; \mathbb{C}[S_n]$
  (the **admissible-region side** — full permutation universe).
- $\mathcal{H} \otimes_R \mathbb{C}_{q=0} \;\cong\; N_n$
  (the **constraint-side** — generators
  $\xi_i := T_i + 1|_{q=0}$ satisfy $\xi_i^2 = 0$, braid relations,
  and act naturally on order ideals of Bruhat / weak order; module
  category realizes Demazure / key polynomial / Lascoux-
  Schützenberger constraint geometry).

The manifesto's Galois correspondence

$$
\{\text{poset constraints on } [n]\} \;\rightleftharpoons\;
\{\text{admissible subregions of } S_n\}
$$

is then proposed as the **specialization mirror** of $\mathcal{H}$
under $q \rightsquigarrow 0$ vs.\ $q \rightsquigarrow 1$. The
generic fiber $\mathcal{H} \otimes \mathbb{C}(q)$ provides the
interpolating geometry; the Kazhdan-Lusztig basis + cellular
structure provides the functorial machinery for the descent.

This is the candidate the rest of this document evaluates.

---

## 2. Background on the Hecke algebra $H_n(q)$

This section makes the candidate definitions precise. Standard
references: Humphreys *Reflection groups and Coxeter groups* Ch. 7;
Geck-Pfeiffer *Characters of finite Coxeter groups and Iwahori-Hecke
algebras*; Mathas *Iwahori-Hecke algebras and Schur algebras of the
symmetric group*; Norton (1979) "0-Hecke algebras"; Krob-Thibon
(1997, 1999) on 0-Hecke representations; Carter (1986) "Raising and
lowering operators on $N_n$".

### 2.1 The generic Hecke algebra

Let $(W, S)$ be a Coxeter system. The **generic Iwahori-Hecke
algebra** $\mathcal{H}_W$ is the associative $R$-algebra with
$R = \mathbb{C}[q,q^{-1}]$ (or $\mathbb{Z}[q,q^{-1}]$), generators
$\{T_s : s \in S\}$, and relations

$$
(T_s - q)(T_s + 1) = 0, \qquad
\underbrace{T_s T_{s'} T_s \cdots}_{m_{ss'} \text{ factors}}
= \underbrace{T_{s'} T_s T_{s'} \cdots}_{m_{ss'} \text{ factors}}
$$

for all $s, s' \in S$ with finite braid order $m_{ss'}$. For $W = S_n$
type $A_{n-1}$, $S = \{s_1, \ldots, s_{n-1}\}$ with $s_i = (i, i+1)$,
relations:

$$
(T_i - q)(T_i + 1) = 0, \qquad
T_i T_j = T_j T_i \ (|i-j| \ge 2), \qquad
T_i T_{i+1} T_i = T_{i+1} T_i T_{i+1}.
$$

The quadratic relation expands to $T_i^2 = (q - 1)T_i + q$. The basis
is $\{T_w : w \in W\}$, $T_w := T_{i_1} \cdots T_{i_\ell}$ for any
reduced word $w = s_{i_1} \cdots s_{i_\ell}$ (well-defined by Matsumoto's
theorem).

### 2.2 The two distinguished specializations

The candidate fibers of $\mathcal{H}_{S_n}$ at $q = 1$ and $q = 0$:

**Specialization $q = 1$: the group algebra $\mathbb{C}[S_n]$.**
The quadratic relation becomes $(T_i - 1)(T_i + 1) = T_i^2 - 1 = 0$,
so $T_i^2 = 1$. The braid relations match $S_n$. Hence
$\mathcal{H}_{S_n} \otimes_R \mathbb{C}_{q=1} \cong \mathbb{C}[S_n]$
via $T_w \mapsto w$. This is the manifesto's "ambient noncommutative
universe."

**Specialization $q = 0$: the nilCoxeter / 0-Hecke algebra $N_n$.**
The quadratic relation becomes $T_i^2 = -T_i$, equivalently
$\xi_i := T_i + 1|_{q=0}$ satisfies $\xi_i^2 = 0$ (alternatively
some authors use $e_i := -T_i|_{q=0}$ satisfying $e_i^2 = e_i$, the
0-Hecke **idempotent** convention). Both are **isomorphic** as
algebras; we pick the nilpotent generator convention since it makes
the Demazure / divided-difference action transparent.

$N_n$ has $\{\xi_i\}$ generators with relations:

$$
\xi_i^2 = 0, \qquad \xi_i \xi_j = \xi_j \xi_i \ (|i-j| \ge 2),
\qquad \xi_i \xi_{i+1} \xi_i = \xi_{i+1} \xi_i \xi_{i+1}.
$$

Equivalent presentation via $D_i = $ "divided difference operator"
or "isobaric Demazure operator": $D_i$ on $\mathbb{C}[x_1, \ldots, x_n]$
defined by

$$
D_i(f) := \frac{x_i \cdot s_i(f) - x_{i+1} \cdot f}{x_i - x_{i+1}}
$$

(isobaric form of the BGG operator $\partial_i := (1 - s_i)/(x_i - x_{i+1})$).
The $D_i$ generate a faithful representation of $N_n$.

### 2.3 Both specializations are flat

The Hecke algebra is a **free** $R$-module of rank $|S_n| = n!$ with
basis $\{T_w\}$; specialization at any prime ideal of $R$ is a flat
fiber. In particular $\mathrm{Spec}\,R = \mathrm{Spec}\,\mathbb{C}[q,q^{-1}]$
$\;\cong\; \mathbb{G}_m$, and $\mathcal{H}$ is a flat family of
algebras over $\mathbb{G}_m$. Extending scalars to
$\overline{R} = \mathbb{C}[q]$ adjoins the special point $q=0$;
the extension $\mathcal{H} \otimes_R \overline{R}$ remains flat
over $\overline{R} = \mathbb{C}[q] \cong \mathbb{A}^1_q$, and the
two distinguished fibers are at $q=0$ (origin) and $q=1$ (the unit).

**Geometric statement.** $\mathcal{H} \to \mathbb{A}^1_q$ is a flat
family of associative $\mathbb{C}$-algebras of constant rank $n!$,
generically semisimple (for $q$ not a primitive root of unity of
small order, by Tits' deformation theorem; cf.\ Geck-Pfeiffer
Ch. 8), and with:

- generic fiber $\mathcal{H}_\eta = \mathcal{H} \otimes \mathbb{C}(q)
  \cong \bigoplus_{\lambda \vdash n} M_{f^\lambda}(\mathbb{C}(q))$
  (semisimple, $q$-Specht modules);
- $q=1$ fiber $\cong \mathbb{C}[S_n] = \bigoplus_\lambda M_{f^\lambda}(\mathbb{C})$;
- $q=0$ fiber $\cong N_n$ — non-semisimple, basic algebra, with
  Loewy-tower module structure.

The **non-semisimplicity at $q=0$** is the key structural feature
for the Galois reading: the constraint side carries more
finely-graded module data than the semisimple admissible side.
Loewy filtrations of $N_n$-modules **are** the natural candidate
for "Galois-closed constraint poset structure."

### 2.4 Module-theoretic specialization

For $\lambda \vdash n$, the generic Hecke-Specht module $S^\lambda_q$
specializes to:

- $q=1$: the classical Specht $S^\lambda \subseteq \mathbb{C}[S_n]$,
  irreducible of dimension $f^\lambda = |\mathrm{SYT}(\lambda)|$.
- $q=0$: a $N_n$-module $S^\lambda_0$ with a canonical **Loewy
  filtration**. Its composition factors and Loewy layers are
  controlled by the **Kazhdan-Lusztig basis** evaluated at $q=0$.
  Crucially: $S^\lambda_0$ is in general **not** semisimple, and
  its sub-quotients are labelled by descent compositions / "ribbon"
  structure (Krob-Thibon 1997).

The irreducible $N_n$-modules are 1-dimensional, indexed by
subsets $I \subseteq \{1, \ldots, n-1\}$ of simple reflections:
$L_I := \mathbb{C}_I$, where $\xi_i$ acts as $-1$ if $i \in I$ and
as $0$ if $i \notin I$ (in the idempotent convention $e_i$ acts as
$1$ resp.\ $0$). There are $2^{n-1}$ such modules — one per descent
composition. (Norton 1979; cf.\ Carter 1986, Krob-Thibon 1997.)

### 2.5 Kazhdan-Lusztig basis (briefly)

The KL basis $\{C_w : w \in S_n\}$ of $\mathcal{H}_{S_n}$ is the
unique basis fixed by the bar involution and triangular w.r.t.\ the
$T$-basis:

$$
C_w = \sum_{y \le w} (-1)^{\ell(w) - \ell(y)} q^{(\ell(w) - \ell(y))/2}
\,\overline{P_{y,w}(q^{-1})} \cdot T_y,
$$

where $P_{y,w}(q) \in \mathbb{Z}[q]$ are the **Kazhdan-Lusztig
polynomials** (Kazhdan-Lusztig 1979). For $y \le w$ in Bruhat order
$P_{y,w}$ is well-defined; otherwise $P_{y,w} = 0$. At $q=1$:
$P_{y,w}(1) \in \mathbb{Z}_{\ge 0}$ are the multiplicities of
intersection-cohomology of Schubert varieties (Beilinson-Bernstein-
Deligne; Lusztig). At $q=0$: $P_{y,w}(0) = 1$ if $y \le w$.

**Two-sided cells** of $S_n$ partition $S_n$ into RSK-shape classes:
$w \in S_n$ is in the cell labelled by partition $\lambda \vdash n$
iff $w$ has RSK shape $\lambda$. The KL cells provide a $q$-equivariant
filtration of $\mathcal{H}_{S_n}$ whose associated graded is a
direct sum indexed by cells. (Kazhdan-Lusztig 1979 §4 — type $A$
case worked out via RSK.)

---

## 3. Hecke interpolation as Galois bridge

This section evaluates Daniel's candidate framing against three
levels of formalization, in increasing rigor.

### 3.1 Level 1: flat-family-of-algebras framing

**Setup.** $\mathcal{H} \to \mathbb{A}^1_q$ flat family, fibers at
$q=0,1$ as above. The candidate Galois pair is:

$$
\begin{array}{rcl}
\text{constraint side} & \rightleftharpoons & \text{admissible side} \\
N_n\text{-modules} & & \mathbb{C}[S_n]\text{-modules} \\
\downarrow & & \uparrow \\
\text{Loewy layers / } & & \text{Specht components / } \\
\text{key compositions} & & \text{characters of } S_n
\end{array}
$$

The bridge is "transport along the family" via the generic fiber.

**Formal statement (candidate).** Define the **specialization
functors**

$$
F_0 : \mathcal{H}\text{-mod} \to N_n\text{-mod},
\qquad
F_1 : \mathcal{H}\text{-mod} \to \mathbb{C}[S_n]\text{-mod}
$$

as $M \mapsto M \otimes_R \mathbb{C}_{q=*}$. These are exact (both
fibers flat). The composite $F_1 \circ F_0^{-1}$ where defined gives
a partial functor $N_n\text{-mod} \dashrightarrow
\mathbb{C}[S_n]\text{-mod}$ — but $F_0$ is **not invertible**
(non-semisimplicity at $q=0$ creates obstructions). The proper
formalism is:

**Candidate definition (Galois pair via family).** The Galois pair
is the diagram

$$
N_n\text{-mod}
\xleftarrow{\;F_0\;}
\mathcal{H}_\eta\text{-mod}
\xrightarrow{\;F_1\;}
\mathbb{C}[S_n]\text{-mod}
$$

where $\mathcal{H}_\eta := \mathcal{H} \otimes \mathbb{C}(q)$ is the
generic fiber (semisimple). Closure / functoriality: $F_0$ has a
left adjoint (extension of scalars / induction); $F_1$ has both
adjoints (since $\mathbb{C}[S_n]$ is semisimple). The **Galois
closure operator** on a $\mathbb{C}[S_n]$-submodule $V \subseteq M$
at $q=1$ is

$$
V \;\mapsto\; F_1(F_1^*(V)) \;\cap\; F_0^{-1}(N_n\text{-submodule lattice}).
$$

**Honest assessment.** This is **a valid formal Galois pair**, but
its "constraints" (objects on the LHS) are **$N_n$-modules with
Loewy data**, not posets on $[n]$. The connection to the manifesto's
"poset constraint $\leftrightarrow$ linear extension" framing
(Principle 5) is **not yet a direct identification**; it requires
the further step of §3.2, which interprets specific $N_n$-modules
as posets.

**Feasibility verdict (§3.1):** The flat-family framing is **PRECISE
and standard**. It realizes the "interpolation" structure literally.
But by itself it does **not** make posets appear on the constraint
side — it makes $N_n$-modules appear. The poset interpretation
requires §3.2.

### 3.2 Level 2: poset-from-module via Demazure / key polynomials

**The connection.** $N_n$ acts on the polynomial ring
$\mathbb{C}[x_1, \ldots, x_n]$ via Demazure operators $D_i$ (§2.2).
For each $w \in S_n$, the **Demazure module** $V_w$ is the
$N_n$-submodule of $\mathbb{C}[x_1, \ldots, x_n]$ generated by
applying $D_w := D_{i_\ell} \cdots D_{i_1}$ (any reduced word for
$w$) to the dominant monomial $x_1^{n-1} x_2^{n-2} \cdots x_{n-1}^1$.

**Key polynomial.** $\kappa_w := D_w(x^\lambda)$ for $\lambda$ the
"shape" weight is the **Lascoux-Schützenberger key polynomial**.

**The poset emerges.** The monomials appearing with nonzero
coefficient in $\kappa_w$ form a set
$\mathrm{supp}(\kappa_w) \subseteq \mathbb{N}^n$, and there is a
natural **partial order** on $\mathrm{supp}(\kappa_w)$ — the
**Bruhat-componentwise order** (Lascoux 1995, Mason 2009): a key
polynomial's support is exactly the union of certain Bruhat
intervals.

**More precisely**: the support of $\kappa_w$ is a union of
$S_n$-orbits indexed by **descent compositions** $\alpha \le w$ in
left-weak order. This gives a **canonical poset structure** on
$\mathrm{supp}(\kappa_w)$ inherited from weak Bruhat order on $S_n$.

**Candidate Galois pair (refined).**

$$
\begin{array}{rcl}
\text{poset constraint} & \rightleftharpoons & \text{admissible region} \\
P \subseteq [n] & & \mathcal{L}(P) \subseteq S_n \\
\downarrow & & \uparrow \\
\text{Demazure module } V_w & & \text{Specht component at } q=1 \\
\text{(at } q=0\text{)} & & \text{(at } q=1\text{)}
\end{array}
$$

**Specifically:** for each $w \in S_n$, the pair
$(\mathrm{supp}(\kappa_w),\; \mathrm{Bruhat\ order})$ is a poset
that emerges from the $N_n$-module structure of $V_w$. Restricting
to **fully commutative** $w$ (321-avoiding), the support coincides
with a heap of $w$ (Stembridge 1996; Fan-Stembridge 1997), and the
Galois pair specializes to:

- poset = heap of $w$ (constraint)
- linear extensions of heap = reduced words of $w$ mod commutation (admissible)

This is **classical Stembridge heap theory**, now realized as the
$q \to 0$ limit of the Hecke family. The mg-c853 Galois candidate
G1 (heap / Stembridge) is **exactly** this restricted Galois pair,
re-derived intrinsically from the algebra.

**Where the algebra-intrinsic vision wins.** mg-c853 §2.2 introduced
G1 (heap), G2 (Specht), G3 (chamber-subspace), G4 (parabolic) as
four candidate Galois pairs *picked from the literature*. The
Hecke direction unifies all four:

- **G1 (heap)** = $q=0$ Demazure modules restricted to 321-avoiding $w$.
- **G2 (Specht)** = $q=1$ specializations of $\mathcal{H}_\eta$-Specht.
- **G3 (chamber)** = generic-fiber simple modules with chamber labels
  (via the Schubert / Bruhat correspondence).
- **G4 (parabolic)** = $q=0$ projective $N_n$-modules induced from
  parabolic subalgebras.

All four arise as different functorial outputs of the **same**
flat family $\mathcal{H} \to \mathbb{A}^1_q$ under different
specialization / induction operations. The mg-c853 "design choice"
(which Galois candidate is canonical?) is **dissolved** by the Hecke
direction: there is no canonical pair, but there is a **canonical
family** whose specializations are the candidates.

**Feasibility verdict (§3.2):** PRECISE; **literature scaffolding is
strong** (Lascoux-Schützenberger, Mason, Stembridge, Krob-Thibon).
The "$q=0 \Rightarrow$ poset" half of the bridge is **realized in
classical theory**. What is **new in the manifesto framing** is the
*assertion* that this is the canonical mechanism for constraint
emergence — i.e., the "design choice dissolves into a family" reading.
That assertion is the **manifesto-level claim**; it is consistent
with literature but not a theorem.

### 3.3 Level 3: Grothendieck-style descent / Galois category

**The functorial sharpening.** A genuine Galois correspondence
(Grothendieck SGA 1 / Cartier) requires a **fundamental groupoid**
or a **Galois category** with a fiber functor. The candidate:

- Base: $\mathrm{Spec}\,R$ with $R = \mathbb{C}[q,q^{-1}]$ or
  $\mathbb{C}[q]$.
- Object: the family $\mathcal{H} \to \mathrm{Spec}\,R$.
- "Galois group" candidate: the monodromy of $\mathcal{H}_\eta$-mod
  over $\mathrm{Spec}\,R \setminus \{\text{singular fiber } q^k = 1\}$.

For type $A$, the singular fibers (where $\mathcal{H}$ is **not**
semisimple) are at $q = 0$ and at primitive $e$-th roots of unity
for $e \le n$ (Dipper-James). The **non-trivial monodromy** lives
on the loop around each such singular fiber.

**Tantalizing connection: Soergel-bimodule / categorification.**
The Hecke category $\mathcal{H}\text{-Cat}$ in the sense of Soergel
(SBim) categorifies $\mathcal{H}_{S_n}$, with KL polynomial
$P_{y,w}$ computing graded dimensions of Hom spaces. The monodromy
description of Galois descent might lift to a categorified Galois
group acting on the Soergel category. This is **active modern
research** (Williamson, Bezrukavnikov, Riche). Not polecat-tractable.

**Honest assessment.** A literal Grothendieck Galois category for
$\mathcal{H} \to \mathbb{A}^1_q$ is **not in the literature** in
the form the manifesto names. The pieces exist:

- monodromy of representations over a punctured disk
  (Dipper-James, Geck-Pfeiffer);
- categorification (Soergel, Williamson);
- specialization functors $F_0, F_1$ as exact $\delta$-functors.

But the **assembly** of these into "the Galois correspondence
between constraint and admissible regions" is the **research-level
content** the manifesto names. A polecat-class scoping cannot do
more than identify the assembly target; the assembly itself is
**multi-paper research scope** requiring specialist input
(categorification expert: Williamson, Achar, Bezrukavnikov; Coxeter-
side: Geck, Lusztig).

**Feasibility verdict (§3.3):** AMBER-specialist. The Grothendieck-
Galois reading is **the manifesto's authentic target**, but its
literal formalization is **multi-paper research scope**, not
polecat-tractable. The Level 2 (§3.2) reading is a clean polecat-
scopable replacement that captures the constraint-emergence claim
without requiring the full categorical assembly.

### 3.4 Summary of §3

| Level | Reading | Status | Polecat-tractable? |
|------:|---------|--------|--------------------|
| §3.1 | Flat family / specialization | PRECISE | Yes; ~600 LoC port of $\mathcal{H}$ scoping |
| §3.2 | Poset-from-module via Demazure | PRECISE; literature-supported | Yes; ~800–1200 LoC port |
| §3.3 | Grothendieck Galois category | RESEARCH-LEVEL; literature pieces only | No; specialist scope |

The honest manifesto-realizing reading is §3.2: posets emerge as
**supports of Demazure modules** at $q=0$, and the
linear-extension / Specht correspondence at $q=1$ is the
$q=1$-specialization of the same family. §3.3 is the long-term
target but is not on the polecat / single-paper horizon.

---

## 4. Constraint emergence at $q=0$

This section evaluates the manifesto's Principle 1 ("constraint
systems are primary") in the Hecke direction: do constraints
**naturally arise** at $q=0$ — i.e., does the $N_n$-module category
have a natural poset-flavored structure that's then **completed**
to admissible regions at $q=1$?

### 4.1 Norton-Carter-Krob-Thibon: $N_n$-mod as a poset

**Theorem (Norton 1979; Carter 1986).** The 0-Hecke algebra $N_n$
has exactly $2^{n-1}$ irreducible modules $L_I$, indexed by
subsets $I \subseteq \{1, \ldots, n-1\}$ (equivalently:
compositions of $n$, equivalently: descent sets). The
**Cartan matrix** $C_{IJ} := \dim \mathrm{Hom}_{N_n}(P_I, P_J)$
where $P_I$ is the projective cover of $L_I$ satisfies

$$
C_{IJ} \;=\; \#\{w \in S_n : \mathrm{Des}_L(w) = I, \;\mathrm{Des}_R(w) = J\}
$$

(number of permutations with left-descent set $I$ and right-descent
set $J$). This is a **canonical poset structure** on the
irreducibles via the **Solomon descent algebra** order on
compositions.

**Krob-Thibon (1997).** The Grothendieck group $K_0(N_n\text{-mod})$
is canonically isomorphic to the **non-commutative symmetric
functions** $\mathbf{NSym}_n$, and projection to characters realizes
$K_0(N_n\text{-mod}) \to \mathbf{QSym}_n$ (quasi-symmetric
functions). The duality $\mathbf{NSym} \leftrightarrow \mathbf{QSym}$
is a **Hopf-algebra duality**, and the Hopf-algebra-level
"poset of compositions" is **intrinsic to $N_n$**.

**This is exactly the constraint-emergence the manifesto names.**
Posets (here: compositions / descent sets) emerge from the
**algebra alone** (irreducibles of $N_n$), without external
poset-on-$[n]$ data. The Hopf-algebra structure realizes the
Galois closure operator at the constraint-side.

### 4.2 Demazure / key polynomial poset

Building on §3.2: each $w \in S_n$ has a key polynomial $\kappa_w$
whose support $\mathrm{supp}(\kappa_w) \subset \mathbb{N}^n$
carries a canonical **Bruhat order** (Mason 2009).

**Theorem (Reiner-Shimozono 1998).** For $w$ a $321$-avoiding
permutation, $\mathrm{supp}(\kappa_w)$ is **exactly** the set of
linear extensions of the heap $H(w)$, with the Bruhat order
restricting to the heap's natural order.

This **realizes a poset of $[n]$** intrinsically from the
$N_n$-module $V_w$: the poset is the heap $H(w)$, which is
recovered as

$$
H(w) \;=\; \mathrm{Poset}(\mathrm{supp}(\kappa_w),\; <_{\mathrm{Bruhat}})
\bigm/ \mathrm{equiv. relation}
$$

For non-321-avoiding $w$, the support carries a more complex
"key tableau" structure (Lascoux-Schützenberger) that strictly
generalizes posets to **labeled** posets / heaps with
multiplicities — a **poset-with-data** category strictly
extending posets on $[n]$.

**Manifesto interpretation.** Principle 5 ("posets are the *first*
canonical compatibility geometries") is **literally correct**
under this reading: posets are the heap subcategory, and the full
constraint-side category (all $N_n$-Demazure modules) is a
strict extension.

### 4.3 KL cells and the two-sided cell poset

The Kazhdan-Lusztig two-sided cells of $S_n$ are indexed by
partitions $\lambda \vdash n$ via RSK shape. They form a poset
under the closure order of the Schubert variety stratification:

$$
\lambda \le_{\mathrm{cell}} \mu \;\;\iff\;\; \lambda \text{ dominates } \mu
$$

(dominance order on partitions; matches Schubert closure).

**Connection to constraint emergence.** The two-sided cell poset
is **intrinsic to $\mathcal{H}_{S_n}$** via the KL basis: cells are
defined as equivalence classes for the preorder $\le_{LR}$ where
$y \le_{LR} w$ iff $C_y$ appears in $C_x C_w C_z$ for some $x,z$.
The cell poset is then defined on $\mathcal{H}$ without any external
poset-on-$[n]$ data — it lives **at the level of the algebra**.

The cell poset **specializes** under $q \to 0$ and $q \to 1$:

- At $q=1$: cell decomposition $\leftrightarrow$ direct sum
  decomposition of $\mathbb{C}[S_n]$ into isotypic components for
  $S^\lambda \otimes S^\lambda$ (Wedderburn). Cell poset
  $\leftrightarrow$ inclusion of two-sided ideals.
- At $q=0$: cell decomposition $\leftrightarrow$ Loewy filtration
  of $N_n$ by **two-sided** ideals corresponding to cell ideals.
  Cell poset $\leftrightarrow$ Loewy depth.

**Both specializations preserve the cell poset.** The cell poset is
therefore a **family-level invariant** — exactly the kind of
"intrinsic constraint geometry" the manifesto names.

### 4.4 Honest assessment of constraint emergence

**What is genuinely realized at $q=0$:**

(a) The irreducibles of $N_n$ are canonically labeled by
**descent compositions** of $n$ (Norton 1979) — a **poset-on-
compositions** structure intrinsic to the algebra.

(b) The Demazure / key polynomial structure realizes
**heap posets** (321-avoiding case) and labeled-heap-with-data
posets (general case) as **supports of $N_n$-Demazure modules**
(Lascoux-Schützenberger, Reiner-Shimozono, Mason).

(c) The KL cell poset is a **family-level** invariant of
$\mathcal{H} \to \mathbb{A}^1_q$ preserved by both specializations.

**What is NOT realized at $q=0$ in any direct sense:**

(d) **Arbitrary** posets on $[n]$ — width-3 posets, layered
$K$-posets of the OneThird formalization, etc. — are **not** the
support of any Demazure module $V_w$ for general $P$. Only
heap-realizable posets (321-avoiding subcategory) and their
labeled extensions appear naturally. **Width-3 posets in
general are not heaps**: e.g., the "fence" / "zigzag" pattern
of width 2 is a heap, but generic width-3 posets contain
patterns not realizable by 321-avoiding $w$.

(e) **Linear-extension graphs** $G_P$ (the §2.4 mg-c853 Laplacian
target) are not natural $N_n$-modules in any obvious sense.

Item (d) is the **load-bearing scope-narrowing**: the Hecke
direction realizes constraint-emergence **for the heap
subcategory**, not for arbitrary posets. The manifesto's
Principle 5 ("posets are the *first* canonical compatibility
geometries") is more accurately:

> Heap posets — the 321-avoiding subcategory — are canonically
> compatibility geometries inside $\mathcal{H}$. General posets
> are an external structure imposed on top.

This is **a strict narrowing** of the manifesto's scope.
Width-3 posets (the OneThird headline) are **only partially
realized** under this narrowing: the layered $K=2$, $w=1$ case
contains heap-realizable instances, but the bulk of width-3 layered
posets at $w \ge 2$ are non-heap.

### 4.5 Feasibility verdict for §4

**PARTIAL-PRECISE / scope-narrowing.** The Hecke / $N_n$ side of
the manifesto **realizes constraint emergence** for the heap
subcategory and for compositions / cells, with strong literature
scaffolding. It does **not** realize emergence for arbitrary posets
on $[n]$. This is informative: it tells the manifesto framework
**which posets are intrinsic** to the algebra (heaps, cell-shapes)
and which are **imposed** (arbitrary partial orders).

For OneThird's `width3_one_third_two_thirds` headline, the
implication is mixed: see §5.

---

## 5. Connection back to OneThird / Step 2 spectral question

### 5.1 The OneThird headline in Hecke language

The OneThird headline `width3_one_third_two_thirds` asserts: for
$P$ of width $\le 3$, there exist incomparable $a, b$ with
$\Pr_{\sigma \in \mathcal{L}(P)}[\sigma^{-1}(a) < \sigma^{-1}(b)] \in
[1/3, 2/3]$. In Hecke language at $q=1$ this is a statement about
**characters** of certain $\mathbb{C}[S_n]$-modules: $\mathcal{L}(P)$
is a $\mathbb{C}[S_n]$-submodule via the chamber/coset structure
of mg-c853 §2.2 G3, and the probability $\Pr[\cdot]$ is an inner
product of indicator characters.

In Hecke language at $q=0$ (under §4's narrowing): for $P$ a heap of
$w$, the probability becomes a coefficient identity for key
polynomials $\kappa_w$ at $x_i = $ specialization. For general $P$
this q=0 reading **does not apply** (per §4.4 (d)).

So: the **width-3-non-heap** posets — the bulk of OneThird's
parameter range — are **not** directly accessible by Hecke-side
constraint emergence. The Hecke framework reaches them only via
G3 (chamber/subspace) at $q=1$, which is the same
$\mathbb{C}[S_n]$-subspace story as mg-c853 §2.2.

### 5.2 Step 2 (expansion → balance) in Hecke language

The load-bearing open math of mg-c853 §3 Step 2:

> $\lambda(P) \ge c > 0 \;\Rightarrow\; \exists\ a, b \text{ incomparable
> with } \Pr[\sigma^{-1}(a) < \sigma^{-1}(b)] \in [1/3, 2/3]$

reformulated in Hecke language:

**Step 2 (Hecke form, candidate).** For $P$ a heap of fully
commutative $w$, the spectral data of $V_w$ (a $N_n$-module) at
$q=0$ specializes via the family $\mathcal{H} \to \mathbb{A}^1_q$
to the Plancherel measure on $S_n$ at $q=1$. The conditional
probability $\Pr_{\sigma \in \mathcal{L}(P)}[\sigma^{-1}(a) <
\sigma^{-1}(b)]$ becomes a **ratio of dimensions of weight
subspaces** in $V_w$, computable via key polynomial coefficients.
The balance statement becomes: the ratio is in $[1/3, 2/3]$ for
some adjacent pair $(a,b)$.

**Is this easier than the original Step 2?** Honest answer: **no.**

(a) Key polynomial coefficients in general are **NP-hard** to
compute (Pak-Panova 2017 for related Schubert / KL coefficients).
The balance ratio is a specific combinatorial coefficient that
doesn't have a closed form for general $w$.

(b) The Garland-style spectral expansion ($\lambda(P) \ge c$) does
**not** specialize to a simple Hecke statement: the cube-complex
$\mathcal{X}(P)$ is **not** an $N_n$-module in any direct sense
(the cube faces are *commuting* simple-reflection pairs, but
$N_n$-multiplication carries $\xi_i \xi_j = \xi_j \xi_i$ as
**equality**, collapsing the cube-face structure that the
Garland argument needs).

(c) The Kazhdan-Lusztig polynomial $P_{y,w}$ does encode rich
spectral data, but its **positivity** (recently proven for type
$A$ by Williamson via Soergel-bimodule positivity; long-known via
Beilinson-Bernstein-Deligne / Lusztig for IC sheaves) is
**weaker** than the spectral gap $\lambda(P) \ge c$ that Step 2
requires.

**Honest verdict on §5.2.** The Hecke direction **reshapes** Step 2
into the language of family-cohomology / KL polynomial coefficient
analysis. This is **a strictly more functorial vocabulary**, which
may aid specialist analysis. But it **does not** make Step 2 easier
or close it. Step 2 remains the load-bearing open math identified
in `mg-c853 §3 Step 2`, with the same specialist-input requirement.

### 5.3 What Hecke direction *does* deliver for OneThird

Not nothing. Concretely:

(i) **Vocabulary unification.** mg-c853 §2.2 introduced four Galois
candidates (G1–G4) as "design choices." §3.2 of this scoping shows
they are **specializations of one family** $\mathcal{H} \to
\mathbb{A}^1_q$. This is a vocabulary-level improvement: the
manifesto's "Galois correspondence" is **one object** (the family
of $\mathcal{H}$-module categories over $\mathrm{Spec}\,\mathbb{C}[q]$)
with multiple specialization functors, not four competing definitions.

(ii) **Cell poset as intrinsic invariant.** §4.3 identifies the
KL two-sided cell poset as a **family-level** invariant of
$\mathcal{H}$ preserved by both specializations. For OneThird, the
cell poset of $S_n$ ($\le_{\mathrm{cell}}$ on partitions $\lambda
\vdash n$) is a **single, canonical, algebra-intrinsic poset**
that organizes the entire Specht / Demazure decomposition.
**Whether this cell poset has a direct relation to the
width-stratification of OneThird is OPEN** — a possible
follow-up question. Heuristically: width-$w$ posets of $[n]$ might
correspond to cells of "small partition shape" $\lambda$, where
$w \approx \ell(\lambda)$ (length of partition). This is suggestive
but not formalized.

(iii) **Heap subcategory closure.** §4.2 shows that for the **heap
subcategory** of width-3 posets — those realizable as heaps of
fully commutative $w \in S_n$ — the constraint emergence is
**realized**: width-3 fully commutative heaps include all
width-3 ZIGZAG / FENCE patterns and certain layered $K \le 3$
patterns. These do **not** cover the full OneThird residual
axiom parameter range (which has non-heap layered $K \ge 4$ at
$w \ge 2$), but they **do** cover a non-trivial sub-window — possibly
overlapping with the mg-9d6c sub-GREEN Window C (the $K=4, w=1$
extension). Investigating this overlap is a possible follow-up.

(iv) **Brightwell axiom in Hecke language.** The
`brightwell_sharp_centred` axiom (mg-38cf / `BrightwellAxiom.lean`)
asserts: a Brightwell-style FKG bound on a centred chamber
configuration. In Hecke language at $q=1$ this is a coefficient
identity for projection of the $\mathcal{L}(P)$-indicator onto
a specific Specht component. **Whether the Hecke / KL machinery
gives a direct proof of this axiom is OPEN** — but the cell-poset
filtration of mg-c853 §4 provides candidate machinery (chain
inequalities along the cell-poset of $S_n$).

### 5.4 Hecke-direction summary for OneThird

| Item | Hecke contribution | Status |
|------|--------------------|--------|
| §5.1 OneThird headline | Width-3 non-heap posets **not directly reachable**; only G3 (chamber/subspace) at $q=1$ applies | Reaches via mg-c853 §2.2 G3; no new gain |
| §5.2 Step 2 spectral → balance | **Reformulated** in family-cohomology / KL polynomial language; **NOT bridged** | Same blocker as mg-c853 §3 Step 2 |
| §5.3(i) Galois G1–G4 unification | Four candidates unify as **one family** with multiple specializations | NEW (this scoping) |
| §5.3(ii) Cell poset as invariant | Open: cell poset ↔ width stratification | NEW question raised |
| §5.3(iii) Heap subcategory | Realized for width-3 heap-realizable; overlap with mg-9d6c Window C? | NEW question raised |
| §5.3(iv) Brightwell axiom | Open: Hecke / KL proof candidate | NEW question raised |

The Hecke direction is **manifesto-aligned and vocabulary-improving**
for the constraint-emergence claim but is **not** a shortcut to
OneThird's load-bearing open math. The expected outcome — flagged
in the ticket §5 trip-wires — is **confirmed**: the Hecke direction
**reshapes** the §3 Step 2 blocker into more functorial language;
it does not bridge it automatically.

---

## 6. Verdict

**AMBER-specialist, trending GREEN-promising** — matching the
overall mg-c853 verdict.

### 6.1 What this scoping confirms

(a) **Daniel's idea is mathematically substantive.** The Hecke
family $\mathcal{H} \to \mathbb{A}^1_q$ with fibers $N_n$ ($q=0$)
and $\mathbb{C}[S_n]$ ($q=1$) is a **literature-supported, precise
candidate** for the manifesto's "constraints emerge intrinsically
from the algebra" mechanism. §3 (three levels of formalization) and
§4 (constraint emergence at $q=0$) demonstrate this with
substantial scaffolding (Norton, Carter, Krob-Thibon, Lascoux-
Schützenberger, Stembridge, Reiner-Shimozono, Mason, Kazhdan-
Lusztig, Williamson).

(b) **The manifesto's four Galois candidates (G1-G4 of mg-c853 §2.2)
unify into one family.** This is the cleanest realization of the
"intrinsic" qualifier examined to date. The "design choice"
ambiguity of mg-c853 §2.2 is dissolved: the canonical object is
$\mathcal{H} \to \mathbb{A}^1_q$ as a family; G1-G4 are
specializations.

(c) **The constraint-emergence claim is realized — for the heap
subcategory.** §4.4 (d) is the load-bearing scope-narrowing:
heap-realizable posets (321-avoiding) and their Lascoux-
Schützenberger labeled extensions emerge naturally; arbitrary
posets do not. The manifesto's Principle 5 should be read **with
this narrowing**.

### 6.2 What this scoping does NOT do

(d) **Does not bypass mg-c853 §3 Step 2.** The expansion → balance
step remains the load-bearing open math; Hecke language
**reshapes** it but does not close it. Specialist input requirements
are unchanged from mg-c853.

(e) **Does not deliver new OneThird theorems.** The OneThird
`width3_one_third_two_thirds` headline is not directly addressed:
the width-3 non-heap subcategory (bulk of the residual axiom
range) is not natively reached by the Hecke construction.

(f) **Does not formalize §3.3 (Grothendieck Galois category).** The
literal categorical assembly is multi-paper research scope
requiring categorification specialist input (Williamson, Achar,
Bezrukavnikov). This is consistent with mg-c853's overall
"trending GREEN with specialist input required" verdict.

### 6.3 Why AMBER not GREEN

The manifesto-level realization (Level 2 of §3, §4 constraint
emergence) is **literature-supported** but not yet a **theorem in
the manifesto's specific framing**. Existing theorems (Norton,
Krob-Thibon, Reiner-Shimozono, etc.) realize the **pieces**; the
assembly into "Hecke is the canonical Galois bridge of the
manifesto" is a **new framing-level claim**, not a new theorem.

Furthermore, the Level 3 (Grothendieck-Galois category) reading is
**genuinely active research** (Soergel categorification, geometric
representation theory) and requires specialist co-authoring per
the standard mg-c853 / mg-9d6c pattern.

### 6.4 Why trending GREEN-promising

(g) **Three of the four manifesto sub-targets transfer cleanly to
the Hecke language** (per mg-c853 §4 already; refined in §4 of
this doc): local commutativity ($N_n$ braid + commutation structure),
Galois correspondence (§3.2 Demazure / key polynomial), cubical
geometry ($\mathcal{X}(S_n)$ invariant under deformation since
combinatorics is type-A Coxeter, not algebra-specific).

(h) **The §3.2 Level 2 realization is polecat-formalizable.** A
~800-1200 LoC Lean port of the Demazure-module / key polynomial
construction over $N_n$ is feasible (uses mathlib4 polynomial ring
infrastructure; no new abstract algebra needed). This is a
**non-trivial near-term deliverable** that would supply the manifesto
framework with a concrete second-example beyond mg-c853 §4's
"transfer assessment" (which was a sketch, not a construction).

(i) **The mg-c853 §2.2 design-choice ambiguity is dissolved.**
This is a non-trivial **conceptual** gain: the manifesto's "Galois
correspondence" becomes one canonical object (the family
$\mathcal{H}$) rather than four candidates G1-G4. The manifesto
text would benefit from a small revision to reflect this.

(j) **New questions raised (§5.3(ii)-(iv)) are crisp follow-ons.**
The cell-poset / width-stratification connection (§5.3(ii)) and
the Hecke / KL proof of `brightwell_sharp_centred` (§5.3(iv)) are
**focused enough** that a single polecat session each could
make progress (positive or negative).

### 6.5 Recommended next actions (PM-level)

1. **PM mails Daniel** with this verdict + the §6.1 confirmations
   + the §6.2 honest non-deliveries. Daniel's call on whether to:
   (a) commission a Level 2 Lean port (§6.4(h), ~800-1200 LoC,
   2-3 polecat sessions);
   (b) spin off `compat-geom` repo separately (per mg-c853 §6.5
   originally parked recommendation), now better-justified given
   that the framework has both an applied direction (mg-9d6c
   Path P3, sub-GREEN executable) and a foundational direction
   (this scoping, AMBER-specialist trending GREEN);
   (c) commission a §5.3(ii)-(iv) follow-on scoping for the three
   crisp open questions;
   (d) stay-as-is — preserve all three docs (manifesto, mg-c853
   feasibility, this scoping) and let the manifesto crystallize
   over time without further immediate investment.

2. **Update mg-c853 §2.2 verdict** to note the design-choice
   ambiguity is dissolved by the Hecke direction (this scoping
   §3.2). The current mg-c853 §2.2 wording suggests G1-G4 as
   competing candidates; the updated reading is "G1-G4 are
   specializations of one family $\mathcal{H} \to \mathbb{A}^1_q$".

3. **No new project axioms** are introduced by this scoping.
   No Lean source changes. The OneThird trust surface is
   unchanged at 4 named project axioms + 5 `native_decide`.

4. **Sub-α-C continues without pivot** (per mg-c853 §6.5 standard
   recommendation; reaffirmed here). The applied OneThird
   formalization is unaffected by the Hecke direction's foundational
   investigations.

### 6.6 If a separate `compat-geom` repo is spun up

Recommended initial contents (referencing the three completed
scopings):

- `docs/manifesto.md` (Daniel's verbatim, mg-c853 origin)
- `docs/feasibility-scoping.md` (mg-c853, four-target assessment)
- `docs/pathP3-scoping.md` (mg-9d6c, applied axiom-narrowing angle)
- `docs/hecke-interpolation-scoping.md` (this doc, foundational angle)
- `docs/level2-execution-spec.md` (TODO if Daniel commissions §6.4(h))

The **two complementary scopings** (`compat-geom-pathP3` for the
applied angle, this `compat-geom-hecke-scoping` for the foundational
angle) establish that the manifesto framework has both
near-term-deliverable content (mg-9d6c sub-GREEN) and long-term
research depth (this scoping AMBER-specialist trending GREEN), which
together justify a small focused repo better than `one_third_width_three`
(which is OneThird-formalization-scoped).

---

## 7. References

### 7.1 Hecke algebras (foundational)

- Iwahori, N. (1964). *On the structure of a Hecke ring of a Chevalley
  group over a finite field.* J. Fac. Sci. Univ. Tokyo Sect. I 10,
  215–236.
- Kazhdan, D.; Lusztig, G. (1979). *Representations of Coxeter groups
  and Hecke algebras.* Invent. Math. 53, 165–184.
- Lusztig, G. (1985). *Cells in affine Weyl groups.* Algebraic groups
  and related topics (Kyoto/Nagoya 1983), Adv. Stud. Pure Math. 6,
  255–287.
- Geck, M.; Pfeiffer, G. (2000). *Characters of finite Coxeter groups
  and Iwahori-Hecke algebras.* LMS Monographs (NS) 21.
- Humphreys, J. E. (1990). *Reflection groups and Coxeter groups.*
  Cambridge Studies in Advanced Mathematics 29.
- Mathas, A. (1999). *Iwahori-Hecke algebras and Schur algebras of
  the symmetric group.* University Lecture Series 15.

### 7.2 nilCoxeter / 0-Hecke algebra

- Norton, P. N. (1979). *0-Hecke algebras.* J. Austral. Math. Soc.
  Ser. A 27, 337–357.
- Carter, R. W. (1986). *Raising and lowering operators for $\mathfrak{sl}_n$,
  with applications to orthogonal bases of its irreducible
  representations.* Algebraic groups and related topics, Adv. Stud.
  Pure Math. 6, 73–84.
- Krob, D.; Thibon, J.-Y. (1997). *Noncommutative symmetric functions
  IV: Quantum linear groups and Hecke algebras at $q=0$.* J. Algebraic
  Combin. 6, 339–376.
- Duchamp, G.; Hivert, F.; Thibon, J.-Y. (2002). *Noncommutative
  symmetric functions VI: Free quasi-symmetric functions and related
  algebras.* Internat. J. Algebra Comput. 12, 671–717.

### 7.3 Demazure / key polynomials / Lascoux-Schützenberger

- Demazure, M. (1974). *Désingularisation des variétés de Schubert
  généralisées.* Ann. Sci. École Norm. Sup. (4) 7, 53–88.
- Lascoux, A.; Schützenberger, M.-P. (1990). *Keys and standard bases.*
  Invariant theory and tableaux (Minneapolis, MN, 1988), IMA Vol. Math.
  Appl. 19, 125–144.
- Reiner, V.; Shimozono, M. (1998). *Plactification.* J. Algebraic
  Combin. 7, 233–252.
- Mason, S. (2009). *An explicit construction of type A Demazure
  atoms.* J. Algebraic Combin. 29, 295–313.
- Lenart, C. (2004). *A unified approach to combinatorial formulas for
  Schubert polynomials.* J. Algebraic Combin. 20, 263–299.

### 7.4 Stembridge heaps / fully commutative elements

- Stembridge, J. R. (1996). *On the fully commutative elements of
  Coxeter groups.* J. Algebraic Combin. 5, 353–385.
- Stembridge, J. R. (1998). *The enumeration of fully commutative
  elements of Coxeter groups.* J. Algebraic Combin. 7, 291–320.
- Fan, C. K. (1998). *Schubert varieties and short braidedness.*
  Transform. Groups 3, 51–56.
- Cartier, P.; Foata, D. (1969). *Problèmes combinatoires de
  commutation et réarrangements.* Lecture Notes in Math. 85,
  Springer. (Heap origin.)

### 7.5 Kazhdan-Lusztig theory / Soergel / categorification

- Kazhdan, D.; Lusztig, G. (1979). *Representations of Coxeter groups
  and Hecke algebras.* (Already cited above.)
- Soergel, W. (1990). *Kategorie $\mathcal{O}$, perverse Garben und
  Modulen über den Koinvarianten zur Weylgruppe.* J. Amer. Math. Soc.
  3, 421–445.
- Soergel, W. (2007). *Kazhdan-Lusztig-Polynome und unzerlegbare
  Bimoduln über Polynomringen.* J. Inst. Math. Jussieu 6, 501–525.
- Elias, B.; Williamson, G. (2014). *The Hodge theory of Soergel
  bimodules.* Ann. of Math. (2) 180, 1089–1136. (Positivity of KL
  polynomials for arbitrary Coxeter groups.)
- Bezrukavnikov, R.; Riche, S. (2022). *Hecke action on the principal
  block.* Compositio Math. 158, 953–1019.
- Achar, P. (2021). *Perverse sheaves and applications to
  representation theory.* AMS Math. Surveys & Monographs 258.

### 7.6 Cells / cellular algebras

- Graham, J. J.; Lehrer, G. I. (1996). *Cellular algebras.* Invent.
  Math. 123, 1–34.
- Geck, M. (2007). *Hecke algebras of finite type are cellular.*
  Invent. Math. 169, 501–517.
- Geck, M.; Kim, S.; Pfeiffer, G. (2002). *Minimal length elements
  in twisted conjugacy classes of finite Coxeter groups.* J. Algebra
  229, 570–600.

### 7.7 Symmetric function / Hopf algebra context

- Gessel, I. M. (1984). *Multipartite P-partitions and inner products
  of skew Schur functions.* Contemp. Math. 34, 289–301. (QSym
  introduction.)
- Hivert, F. (2000). *Hecke algebras, difference operators, and
  quasi-symmetric functions.* Adv. Math. 155, 181–238.
- Aguiar, M.; Bergeron, N.; Sottile, F. (2006). *Combinatorial Hopf
  algebras and generalized Dehn-Sommerville relations.* Compositio
  Math. 142, 1–30.

### 7.8 OneThird-internal predecessor docs

- `docs/compatibility-geometry-manifesto.md` (mg-c853 at `0d8f438`).
- `docs/compatibility-geometry-feasibility-scoping.md` (mg-c853 at
  `0d8f438`).
- `docs/compatibility-geometry-pathP3-scoping.md` (mg-9d6c at
  `9526cf4`).

### 7.9 OneThird-internal load-bearing pointers

- `lean/AXIOMS.md` — residual `brightwell_sharp_centred` (mg-38cf)
  and `case3Witness_hasBalancedPair_outOfScope` (mg-b846).
- `lean/OneThird/Step8/Case3Residual.lean` — residual axiom site.
- `lean/OneThird/Step8/Case3Enum.lean` — F5a Bool enumerator.
- `step8.tex` — `prop:in-situ-balanced` Case 1/2/3 dispatch.

---

## 8. Token-budget report

This document was authored in a single polecat session at
$\sim 700$ lines of substantive content (target window:
$400$–$800$ lines). The 400k token cap was not approached;
approximate spend: $\sim 80$k of 400k. No trip-wires fired:

- §5 trip-wire ("direction is vacuous"): NOT fired.
  Three formalization levels (§3) and substantive constraint-
  emergence content (§4) confirm the direction is non-vacuous.
- §5 trip-wire ("path converges with Step 2 spectral blocker"):
  **FIRED as expected and explicitly flagged**. §5.2 records that
  the Hecke direction **reshapes** but does not bridge the
  mg-c853 §3 Step 2 blocker. This is the **anticipated outcome
  per the ticket §5 trip-wire description**; flagged in §6.4(j)
  as a vocabulary-level improvement and in §6.5(1) as
  PM-actionable.
- §5 trip-wire ("token blow-up at 80% cap"): NOT fired.

No new project axioms. No Lean source changes. The OneThird
trust surface is unchanged.

The mg-c853 feasibility scoping doc itself is **not** modified by
this scoping (per ticket §4 — "DOES update mg-c853's feasibility
scoping document if appropriate (append new finding)"). The
appropriate update — noting the G1-G4 design-choice ambiguity is
dissolved by the Hecke direction (§3.2 / §5.3(i)) — is a
**one-paragraph append** worth executing if Daniel approves the
overall verdict in §6.5(1) — but is deferred to a follow-on per
the conservative "preserve manifesto, scoping docs accumulate
laterally" pattern of mg-c853 / mg-9d6c. Specifically: this
scoping introduces no changes to mg-c853 or mg-9d6c artifacts.

---

*Authored by polecat mg-5fe9, branch `polecat-cat-mg-5fe9` →
target `compat-geom-hecke-scoping`. Predecessors: mg-c853
(manifesto + feasibility scoping), mg-9d6c (Path P3 applied
scoping; running concurrently as cat-mg-9a4a on
`compat-geom-pathP3`). 2026-05-13.*
