# Compat-Geom — Pos_n sheaf cohomology forces balance (mg-d60d)

**Source idea.** Daniel reminder 2026-05-13T16:37Z, verbatim:

> *"idea: use poset sheaf which is just Pos_n and take its cohomology:
> Pos_n has enough categorical regularity that semantic local data
> glues globally, forcing balance unless a refinement-collapse is
> visible inside the order structure itself"*

**Predecessor.** `docs/compatibility-geometry-eigensheaves-scoping.md`
(mg-296d, commit `fc63f63`). §5.2 establishes the central scoping
result: $F_\ell$ — the linear-extension count line bundle on
$\mathbf{Pos}_n^{\mathrm{sub}}$ with restriction
$\rho_{P\to P'}(1) = |\mathcal{L}(P)|/|\mathcal{L}(P')|$ for refinements
$P' \le P$ — is a $\Delta_{(a,b)}$-eigensheaf with eigenvalue
$1 - \Pr_P[a <_P b]$. §10.Q2 flagged the cohomological-obstruction
avenue as the most promising follow-on; the present document scopes it.

**Companion.** `docs/compatibility-geometry-manifesto.md` (mg-c853);
`docs/compatibility-geometry-feasibility-scoping.md` (mg-c853) §3 Step 2
chain *expansion $\Rightarrow$ balance*.

**Sibling.** cat-mg-5ee2 (Pos_n-as-sphere scoping) runs in parallel.
That ticket asks whether $|\Delta(\mathbf{Pos}_n^{\mathrm{sub}})|$ is a
topological sphere. If TRUE, the rigidity has direct consequences for
the present analysis (§3.3 below); we cross-reference but do not
duplicate. No `state.md` overlap touched here (the file does not exist
yet in the repo; the ticket's coordination note is preserved for
future-state).

**This document.** A LaTeX-first scoping of Daniel's
2026-05-13T16:37Z cohomological-gluing idea. Frame
$H^*(\mathbf{Pos}_n^{\mathrm{sub}}, F_\ell)$ as the natural carrier of
the local-to-global obstruction; ask whether vanishing of an explicit
class equals the 1/3–2/3 balance condition; characterize the
*refinement-collapse* exception locus inside the order structure. No
new axioms; pure scoping. Three candidate proof avenues identified in
mg-296d §7 — (i) cohomological obstruction (this ticket), (ii) Verdier
duality, (iii) $q$-flat-family — we focus on (i).

LaTeX is used inline (`$\ldots$` / display) throughout; render with
KaTeX/MathJax or read source.

---

## 1. Recap: the site and the principal eigensheaf

### 1.1 The site $(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$

From mg-296d §1–§2 (we cite without re-deriving). The category
$\mathbf{Pos}_n^{\mathrm{sub}}$ has objects partial orders on $[n]$ and
a unique morphism $P' \to P$ iff $<_{P'} \subseteq <_P$ (i.e. $P$
refines $P'$). It is a bounded lattice: bottom $\widehat 0$ is the
antichain ($\mathcal{L}(\widehat 0) = S_n$), top $\widehat 1$ is the
$n!$ total orders, each with a single linear extension. As a lattice
$\mathbf{Pos}_n^{\mathrm{sub}}$ is graded by the count of cover
relations; it is the Galois-closure lattice for the relation
$\mathcal{L}(\cdot)$ between $2^{[n]\times[n]}$ and $2^{S_n}$
(mg-296d §1.2; Stanley EC1 Ch. 3.3).

The (T3) **linear-extension-restriction topology** has sieves: $S$
covers $P$ iff every chamber $\sigma \in \mathcal{L}(P)$ lifts to a
refinement $P_\sigma \to P$ in $S$ (here $P_\sigma$ is the total order
$\sigma$ viewed as a maximal refinement of $P$). A presheaf
$F : (\mathbf{Pos}_n^{\mathrm{sub}})^{\mathrm{op}} \to
\mathbf{Vec}_\mathbb{Q}$ is a (T3)-sheaf iff

$$
F(P) \xrightarrow{\ \cong\ } \lim_{\sigma \in \mathcal{L}(P)} F(P_\sigma).
$$

### 1.2 The principal eigensheaf $F_\ell$

$F_\ell(P) := \mathbb{Q}$ for all $P$, with restriction
$\rho_{P \to P'} : F_\ell(P) \to F_\ell(P')$ given by multiplication
by $|\mathcal{L}(P)|/|\mathcal{L}(P')| \in (0, 1]$ for any refinement
$P' \le P$. The ratio is $\le 1$ because $\mathcal{L}(P) \subseteq
\mathcal{L}(P')$.

$F_\ell$ is a (T3)-sheaf: a global value at $P$ is determined by its
values at chambers $P_\sigma$ via $F_\ell(P) = (1/|\mathcal{L}(P)|)
\sum_\sigma F_\ell(P_\sigma)$ under the canonical normalization
$F_\ell(P_\sigma) = 1$. Equivalently $|\mathcal{L}(P)| \cdot
F_\ell(P)$ is the constant "1" function on the chamber site.

### 1.3 The eigenvalue function $\Pr$

mg-296d §4.2 / §5.2 establishes: $F_\ell$ is a simultaneous
eigensheaf for the family $\{\Delta_{(a,b)}\}_{(a,b)}$ of
cover-toggle operators with $P$-dependent eigenvalues

$$
\mu_{(a,b)}(P) := 1 - \Pr_P[a <_P b].
$$

The conjecture `width3_one_third_two_thirds` reformulates (mg-296d
§6) as the eigenvalue-density statement

$$
\text{Pr-spectrum}(F_\ell)(P) \cap [1/3, 2/3] \ne \emptyset
\quad \text{for all non-chain } P \text{ of width} \le 3.
$$

The present scoping asks whether **cohomology** of $F_\ell$ on the
site $(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$ controls this
eigenvalue-density statement.

---

## 2. Sheaf cohomology on $\mathbf{Pos}_n^{\mathrm{sub}}$: which theory?

The single phrase "sheaf cohomology of $F_\ell$ on $\mathbf{Pos}_n^
{\mathrm{sub}}$" is not yet a well-defined object; several flavors of
cohomology coexist on a site. We enumerate three; one is canonical for
the (T3) topology and we commit to it.

### 2.1 Three candidate cohomology theories

**(H-α) Topos cohomology $H^*_\tau$.** Right derived functors of the
global-sections functor $\Gamma : \mathrm{Sh}(\mathbf{Pos}_n^{\mathrm{
sub}}, \tau_{T3}) \to \mathbf{Vec}_\mathbb{Q}$, where $\Gamma(F) :=
F(\widehat 1)$ — wait. The site has no terminal object naturally
adapted to "global sections": the lattice top $\widehat 1$ is the
*disjoint union* of $n!$ total orders, not a single chamber. The
correct $\Gamma$ takes the **limit** over the entire site:

$$
\Gamma(F) := \lim_{P \in \mathbf{Pos}_n^{\mathrm{sub}}} F(P)
= \mathrm{Hom}(\underline{\mathbb{Q}}, F).
$$

Under (T3) and the sheaf condition for $F_\ell$, $\Gamma(F_\ell) =
\mathbb{Q}$: a global section is determined by a single scalar $c$
with $c \cdot |\mathcal{L}(P)|$ constant across $P$ (which is what
the restriction formula forces — see §3.1). Then

$$
H^i_\tau(\mathbf{Pos}_n^{\mathrm{sub}}, F_\ell) := R^i \Gamma(F_\ell).
$$

**(H-β) Order-complex / Alexandrov-topos cohomology $H^*_{\Delta}$.**
The order complex $\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$ is the
simplicial complex with vertices = posets and $k$-simplices = chains
$P_0 < P_1 < \cdots < P_k$ in the refinement order. Equivalently,
$\mathbf{Pos}_n^{\mathrm{sub}}$ carries the **Alexandrov topology**
(open sets = down-closed sets); presheaves on the poset become
sheaves on this topology, and sheaf cohomology computes the
cohomology of $|\Delta(\mathbf{Pos}_n^{\mathrm{sub}})|$ with the
corresponding **constructible** coefficient system.

For a poset $\mathcal{P}$ and a presheaf $F$ on $\mathcal{P}^{
\mathrm{op}}$, the standard cosimplicial cochain complex
$C^k(\mathcal{P}, F) := \prod_{P_0 < \cdots < P_k} F(P_0)$ with
Čech-style coboundary computes
$H^*_{\Delta}(\mathcal{P}, F) = H^*(\mathrm{Tot}\ C^\bullet)$ —
the **Roos / Mitchell cohomology** of a small category. See Mitchell
1972 ("Rings with several objects"), Quillen 1973 ("Higher algebraic
K-theory I" §1, the nerve construction), Baues–Wirsching 1985.

**(H-γ) Čech cohomology $\check H^*$ for the (T3) topology.** The
(T3) topology has natural covers
$\mathcal{U}_P := \{P_\sigma \to P\}_{\sigma \in \mathcal{L}(P)}$.
Čech cohomology w.r.t. these:

$$
\check H^k(P, F) := H^k\left(\prod_{\sigma_0} F(P_{\sigma_0})
\to \prod_{\sigma_0, \sigma_1} F(P_{\sigma_0} \wedge P_{\sigma_1})
\to \cdots\right).
$$

Since meets of distinct chambers are non-chamber posets (specifically,
$P_\sigma \wedge P_\tau$ is the largest common refinement-precedent of
$\sigma, \tau$ — which for distinct $\sigma, \tau$ in $\mathcal{L}(P)$
is a proper sub-refinement of $P$), $\check H^k(P, F_\ell)$ is
non-trivial in general.

### 2.2 Comparison and commitment

For a site with **enough points** and a sheaf, all three theories
coincide in low degrees (Tamme 1994, "Introduction to étale
cohomology" §I.3). For our (T3) site:

- (H-α) and (H-γ) agree by SGA 4 II.5.1 (Čech-derived functor
  agreement when covers form a basis). The (T3) covers are a basis;
  (H-γ) computes (H-α).
- (H-β) is the cohomology of the **underlying poset as a topological
  space** (Alexandrov topology) and computes a generally *finer*
  invariant than (H-α): it sees the entire chain structure of
  $\mathbf{Pos}_n^{\mathrm{sub}}$, not just the (T3)-covers. In
  particular (H-β) is sensitive to **non-chamber refinements**.

**Commitment.** We work with **(H-β)** as the principal cohomology
theory. Reasons:

(i) Daniel's framing ("categorical regularity"; "semantic local data
glues globally") is most natural for the Alexandrov-topos / Mitchell-
Baues–Wirsching cohomology, which directly measures the obstruction
to extending presheaves along refinement chains.

(ii) (H-β) is **computable** for small $n$ by explicit chain
complexes; (H-α)/(H-γ) require more machinery.

(iii) The order complex $\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$ has
classical combinatorial-topology literature scaffolding (Björner–
Wachs, Stanley) that does not exist for the (T3)-Čech version.

(iv) The sibling cat-mg-5ee2 (Pos_n-as-sphere) operates directly on
$|\Delta(\mathbf{Pos}_n^{\mathrm{sub}})|$; choosing (H-β) maximizes
shared infrastructure between the two scopings.

We denote the resulting cohomology simply $H^k(\mathbf{Pos}_n,
F_\ell)$ for brevity, suppressing the (H-β) decoration.

### 2.3 The chain complex

Concretely $H^k(\mathbf{Pos}_n, F_\ell)$ is the $k$-th cohomology of

$$
0 \to C^0 \xrightarrow{d^0} C^1 \xrightarrow{d^1} C^2 \to \cdots,
\qquad
C^k := \prod_{P_0 < P_1 < \cdots < P_k} F_\ell(P_0) = \mathbb{Q}^{N_k},
$$

where $N_k$ is the number of strictly-increasing $(k+1)$-chains in
$\mathbf{Pos}_n^{\mathrm{sub}}$ and the coboundary is the alternating-
sum-of-restrictions:

$$
(d^k \alpha)_{P_0 < \cdots < P_{k+1}} :=
\sum_{i=0}^{k+1} (-1)^i \cdot \rho_{P_0 \to P_{0,i}}\bigl(
\alpha_{P_0 < \cdots < \widehat{P_i} < \cdots < P_{k+1}}\bigr),
$$

with the convention that $\rho_{P_0 \to P_0} = \mathrm{id}$ and that
the term for $i = 0$ uses the canonical degeneracy
$P_0 \to P_1$ — i.e., the restriction $F_\ell(P_0) \to F_\ell(P_1)$,
which is multiplication by $|\mathcal{L}(P_0)| / |\mathcal{L}(P_1)|$.

The multiplicative-by-$|\mathcal{L}|$ structure of $F_\ell$'s
restriction makes $C^\bullet$ a **logarithmic** chain complex: in
terms of the variable $\beta_P := |\mathcal{L}(P)| \cdot \alpha_P$,
the coboundary is independent of $P$ and reduces to the **standard
constant-coefficient chain complex** of $\Delta(\mathbf{Pos}_n^{
\mathrm{sub}})$. This is the key calculational simplification.

### 2.4 Consequence: $F_\ell \cong \underline{\mathbb{Q}}$ as a sheaf

The change of variables $\beta_P := |\mathcal{L}(P)| \cdot \alpha_P$
identifies $F_\ell$ with the **constant sheaf** $\underline{\mathbb{Q}}$
on $\mathbf{Pos}_n^{\mathrm{sub}}$. Indeed:

$$
F_\ell(P) \xrightarrow{\ |\mathcal{L}(P)| \cdot\ }
\underline{\mathbb{Q}}(P) = \mathbb{Q}, \qquad
\rho^{F_\ell}_{P \to P'} = \frac{|\mathcal{L}(P)|}{|\mathcal{L}(P')|}
\cdot \mathrm{id}_\mathbb{Q}, \quad
\rho^{\underline{\mathbb{Q}}}_{P \to P'} = \mathrm{id}_\mathbb{Q},
$$

and the diagram commutes:
$|\mathcal{L}(P')| \cdot \rho^{F_\ell}_{P\to P'}(\alpha_P)
= |\mathcal{L}(P)| \cdot \alpha_P$.

This isomorphism is **canonical** (it uses only the structural data
$|\mathcal{L}(P)|$, no auxiliary choices). Therefore:

$$
\boxed{H^k(\mathbf{Pos}_n, F_\ell) \cong
H^k(\mathbf{Pos}_n, \underline{\mathbb{Q}}) =
H^k(|\Delta(\mathbf{Pos}_n^{\mathrm{sub}})|; \mathbb{Q}).}
$$

**This is the first non-trivial observation of the scoping.** The
twist in $F_\ell$ is **trivializable** — it's a "constant sheaf in
disguise" — and its cohomology reduces to the ordinary singular
cohomology of the order complex of the refinement lattice.

### 2.5 Honest consequence for the gluing idea

Daniel's framing implicitly asks: *does the twist in $F_\ell$ encode
information that the constant sheaf doesn't?* The answer per §2.4 is
**no** at the level of cohomology groups. However:

- The **specific cocycles** representing the same cohomology class
  differ between $F_\ell$ and $\underline{\mathbb{Q}}$ — the
  $|\mathcal{L}|$ scaling matters for the **interpretation** of
  cocycles as eigenvalue data.
- The **operator-twisted cohomology** $H^*(\mathbf{Pos}_n, F_\ell)^{
  \{\Delta_{(a,b)}\}}$ — eigenvectors of the $\Delta$-action on
  cohomology — sees the eigenvalue spectrum and is the **right**
  refined invariant. This is computed below.

So the framework refines: we need $H^*$ **with the $\Delta$-action**,
not bare $H^*$.

---

## 3. What does $H^*$ compute? Three explicit cases

### 3.1 $H^0(\mathbf{Pos}_n, F_\ell) = \mathbb{Q}$ (global sections)

By §2.4 + the fact that $\mathbf{Pos}_n^{\mathrm{sub}}$ is connected
(every poset on $[n]$ is refinement-comparable to the antichain),
$H^0(\mathbf{Pos}_n, F_\ell) \cong H^0(\Delta; \mathbb{Q}) =
\mathbb{Q}$.

**Interpretation.** A global section of $F_\ell$ is a single scalar
$c$ such that $|\mathcal{L}(P)| \cdot \alpha_P = c$ for all $P$.
Setting $c = 1$ gives the **canonical normalized section** —
$\alpha_P = 1/|\mathcal{L}(P)|$ — which assigns to each poset the
inverse of its linear-extension count. This is the **uniform-measure
density** on chambers.

The global section is the "averaged" data; it captures no eigenvalue
information directly (eigenvalues are *local* invariants).

### 3.2 $H^1(\mathbf{Pos}_n, F_\ell)$: cocycle data

For $P_0 < P_1$ a refinement edge, a 1-cochain assigns
$\alpha_{(P_0, P_1)} \in F_\ell(P_0) = \mathbb{Q}$ — equivalently,
after multiplication by $|\mathcal{L}(P_0)|$, an element of $\mathbb{Q}$.

The coboundary of a 0-cochain $\beta_P$:
$(d^0 \beta)_{(P_0, P_1)} = \rho_{P_0 \to P_1}(\beta_{P_0}) -
\beta_{P_1} \cdot |\mathcal{L}(P_1)|/|\mathcal{L}(P_1)|$ — being
careful, in normalized variables $\gamma_P := |\mathcal{L}(P)|
\alpha_P$, we have $(d^0 \gamma)_{(P_0, P_1)} = \gamma_{P_0} -
\gamma_{P_1}$. So $\ker d^1 / \mathrm{im}\ d^0$ is exactly
$H^1(\Delta; \mathbb{Q})$.

**Topology of $\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$.** The order
complex of a bounded lattice is **contractible**: cone from
$\widehat 0$ (or $\widehat 1$). So $|\Delta(\mathbf{Pos}_n^{\mathrm{sub
}})| \simeq *$ and $H^k(\Delta; \mathbb{Q}) = 0$ for $k \ge 1$.

**Consequence (naive).**

$$
H^k(\mathbf{Pos}_n, F_\ell) \cong
\begin{cases} \mathbb{Q} & k = 0 \\ 0 & k \ge 1. \end{cases}
$$

**This is a problem for Daniel's framing.** If cohomology vanishes in
positive degrees, there are *no* obstruction classes to constrain
local data, and the cohomological-obstruction proof avenue
**collapses** in its naive form.

### 3.3 Restoring obstructions: pass to the **proper** lattice

The contractibility argument uses the cone-point $\widehat 0$ (the
antichain). To get non-trivial cohomology one removes the cone points.

**Definition.** Let
$\overline{\mathbf{Pos}_n^{\mathrm{sub}}} := \mathbf{Pos}_n^{
\mathrm{sub}} \setminus \{\widehat 0, \widehat 1\}$ be the **proper
part** of the refinement lattice (all posets that are neither
antichain nor a total order).

The order complex $\Delta(\overline{\mathbf{Pos}_n^{\mathrm{sub}}})$
is generally **not contractible**. The Björner–Wachs literature on
poset complexes (see e.g. *Combinatorics of Coxeter Groups* §A2 and
Wachs's *Poset topology* survey, 2007) describes the homotopy type
in many cases.

For small $n$:

- $n = 2$: $\overline{\mathbf{Pos}_2^{\mathrm{sub}}}$ is empty (there
  are 3 posets, all extremal: antichain, $1<2$, $2<1$). So
  $\Delta = \emptyset$ and $H^* = 0$. No content.

- $n = 3$: $|\mathbf{Pos}_3^{\mathrm{sub}}| = 19$, so
  $|\overline{\mathbf{Pos}_3^{\mathrm{sub}}}| = 19 - 1 - 6 = 12$
  (subtracting antichain plus $3! = 6$ total orders). The proper
  lattice has rank $\binom{3}{2} - 1 = 2$ (the antichain has rank 0,
  total orders have rank 3 = number of cover relations of a total
  order on 3 elements). The order complex of the proper part is
  expected (by Björner–Wachs general principles for "interval-thin"
  graded lattices) to be **homotopy equivalent to a wedge of spheres
  of dimension $\le 1$**. Explicit computation deferred.

- $n = 4$: $|\mathbf{Pos}_4^{\mathrm{sub}}| = 219$. The proper part
  has rank $\binom{4}{2} - 1 = 5$ on top. Topology of
  $\Delta(\overline{\mathbf{Pos}_4})$ is **not in the literature**
  (to scoping-author's knowledge) and is the natural target of the
  sibling cat-mg-5ee2.

**Cross-reference to cat-mg-5ee2.** If the sibling scoping confirms
that $|\Delta(\overline{\mathbf{Pos}_n^{\mathrm{sub}}})|$ is a
sphere $S^{d_n}$ of explicit dimension $d_n$, then

$$
H^k(\overline{\mathbf{Pos}_n^{\mathrm{sub}}}, F_\ell) \cong
H^k(S^{d_n}; \mathbb{Q}) =
\begin{cases} \mathbb{Q} & k = 0 \text{ or } d_n \\ 0 & \text{else.} \end{cases}
$$

The **top-degree class** $H^{d_n}(\Delta) \cong \mathbb{Q}$ would
then be the **distinguished cohomological obstruction** sought by
Daniel's framing. This conditional is the load-bearing dependency on
cat-mg-5ee2.

### 3.4 What the top class would mean

Suppose (conditionally on cat-mg-5ee2) that $H^{d_n}(\overline{
\mathbf{Pos}_n^{\mathrm{sub}}}, F_\ell) \cong \mathbb{Q}$. A class
$\omega \in H^{d_n}$ is represented by a $d_n$-cocycle assigning
ratios of linear-extension counts to maximal chains in
$\overline{\mathbf{Pos}_n^{\mathrm{sub}}}$.

A maximal chain in $\overline{\mathbf{Pos}_n^{\mathrm{sub}}}$ is a
sequence

$$
P_1 < P_2 < \cdots < P_{d_n + 1}
$$

of proper posets, each refining the previous by one cover relation,
with $P_1$ having exactly one cover relation (not the antichain) and
$P_{d_n + 1}$ being a "near-total" order (one missing cover from a
total order). Each consecutive ratio
$|\mathcal{L}(P_i)| / |\mathcal{L}(P_{i+1})|$ is exactly the
eigenvalue $1 - \mu_{(a_i, b_i)}(P_i) = \Pr_{P_i}[a_i <_{P_i} b_i]$
where $(a_i, b_i)$ is the newly added cover relation.

**Therefore the top cohomology class is the cup product of $\Pr$-
eigenvalues along a maximal chain:**

$$
\omega(P_1 < \cdots < P_{d_n+1}) = \prod_{i=1}^{d_n}
\Pr_{P_i}[a_i <_{P_i} b_i] \cdot |\mathcal{L}(\widehat 1\text{-near})|.
$$

This is the **product-over-chain** functional on Pr-spectra.

### 3.5 The cohomological balance conjecture

We can now state Daniel's cohomological framing precisely:

**Conjecture (CB, cohomological balance).** *There exists a class
$\omega_{\mathrm{bal}} \in H^{d_n}(\overline{\mathbf{Pos}_n^{\mathrm{
sub}}}, F_\ell)$ such that, for every poset $P \in
\overline{\mathbf{Pos}_n^{\mathrm{sub}}}$ of width $\le 3$, the
restriction of $\omega_{\mathrm{bal}}$ to the link of $P$ vanishes
iff $P$ has a pair $(a,b)$ with $\Pr_P[a <_P b] \in [1/3, 2/3]$.*

In words: vanishing of an explicit top-degree cohomology class on
the link is **equivalent** to the local balance condition at $P$.
Daniel's gluing principle then says: the link vanishing extends to
global vanishing of $\omega_{\mathrm{bal}}$ unless an obstruction is
visible — and the obstruction is the *refinement-collapse* locus
(§4).

**Honest status.** (CB) is **not proven** in this scoping; we have
identified the class and its eigenvalue interpretation. Whether the
vanishing-on-link condition is **equivalent** to local balance is
open and requires further work.

---

## 4. Refinement-collapse: definition and characterization

Daniel's phrasing "refinement-collapse is visible inside the order
structure itself" suggests a structural exception class. We
formalize:

### 4.1 Two senses of "collapse"

**(RC-up) Implied-relation collapse.** A pair $(a,b)$ exhibits an
*upward refinement-collapse at $P$* if $a, b$ are incomparable in $P$
but $\mathcal{L}(P) = \mathcal{L}(P \cup \{a < b\})$ — equivalently,
$\Pr_P[a <_P b] = 1$. The relation $a < b$ is **forced** by the
chamber set even though not in $<_P$ explicitly.

**(RC-down) Forbidden-relation collapse.** Symmetric: $a, b$
incomparable but $\Pr_P[a <_P b] = 0$, i.e., $a > b$ is forced by
$\mathcal{L}(P)$.

**(RC-mixed) Bracket-collapse.** No single pair exhibits (RC-up) or
(RC-down) but the chamber set $\mathcal{L}(P)$ admits a non-trivial
partition by a cover-toggle that is not visible in $<_P$. Formally,
there exist disjoint $\{(a_i, b_i)\}_{i=1}^k$ incomparable pairs
such that $\mathcal{L}(P) = \bigsqcup_S \mathcal{L}_S$ where $S
\subseteq [k]$ and $\mathcal{L}_S = \{\sigma \in \mathcal{L}(P) :
\sigma^{-1}(a_i) <\sigma^{-1}(b_i) \iff i \in S\}$, with at least
one block empty and at least one full. (RC-up) and (RC-down) are
the $k=1$ cases.

### 4.2 (RC-up) and (RC-down) are visible in $<_P$

**Lemma (folklore; cf. Stanley EC1 Lemma 3.3.1).** *Let $P$ be a
poset on $[n]$ and let $a, b$ be incomparable in $P$. The following
are equivalent:*

(i) $\Pr_P[a <_P b] = 1$ (= (RC-up) at $(a,b)$).

(ii) $a < b$ is in the **transitive closure** of $<_P \cup \{a < b\}$
already restricted to chambers — equivalently, every $\sigma \in
\mathcal{L}(P)$ has $\sigma^{-1}(a) < \sigma^{-1}(b)$.

(iii) There exists a sequence $c_0 = a, c_1, \ldots, c_m = b$ with
$c_i, c_{i+1}$ comparable in $P$ and $c_i <_P c_{i+1}$ for all $i$.

*Proof sketch.* (iii) ⇒ (ii) by transitivity. (ii) ⇒ (i) trivially.
(i) ⇒ (iii) is the contrapositive: if no such chain exists, the
"swap $a$ and $b$ at one step" argument (cf. Kahn–Saks 1984) gives
a chamber $\sigma$ with $\sigma^{-1}(b) < \sigma^{-1}(a)$. □

**Consequence.** (RC-up) and (RC-down) are **immediate from the
transitive closure of $<_P$**. The pair $(a,b)$ exhibits (RC-up) at
$P$ iff $P^* := <_P^*$ (transitive closure) contains $a < b$.

**This is exactly Daniel's "visible inside the order structure
itself."** The (RC-up)/(RC-down) collapses are read off from $P$ by
computing transitive closure — a quadratic-time algorithm with no
chamber enumeration required.

### 4.3 (RC-mixed) is not visible in the same sense

For $k \ge 2$, the partition $\mathcal{L}(P) = \bigsqcup_S \mathcal{L
}_S$ requires checking chambers — *not* derivable from $<_P$
alone. Whether (RC-mixed) collapses exist beyond what (RC-up) +
(RC-down) detect is the **content of the 1/3–2/3 conjecture** in
this framing.

**Claim (RC = balance).** *For width-$\le 3$ posets, every
refinement-collapse is either (RC-up) or (RC-down) — i.e., (RC-
mixed) ⇒ (RC-up) ∨ (RC-down).*

If true, this equates "all refinement-collapses are order-visible"
with "1/3–2/3 holds for width-3." The intuition: a (RC-mixed)
collapse without (RC-up)/(RC-down) would mean the chambers split
along a bipartition that no single cover relation captures —
geometrically, a "wall" in the chamber complex that is not a
hyperplane in the order polytope. For width-3 the cube complex
$\mathcal{X}(P)$ (mg-c853 §2.3) has dimension bounded by the width
parameter; the local-to-global Niblo–Reeves argument should rule out
non-hyperplane walls in low dimension.

**Status.** This claim is the **load-bearing reduction** of the
cohomological framework to the 1/3–2/3 conjecture. We have not
proven it; we have *identified* it as the bridge.

### 4.4 The refinement-collapse locus as a subcomplex

Inside $\mathbf{Pos}_n^{\mathrm{sub}}$, the **RC-locus**
$\mathrm{RC}_n \subseteq \mathbf{Pos}_n^{\mathrm{sub}}$ consists of
posets $P$ admitting at least one (RC-up) or (RC-down) pair.

**Structural facts.**

(i) $\mathrm{RC}_n$ is **upward-closed** under refinement (adding
relations preserves (RC-up)/(RC-down) at remaining incomparable
pairs): if $P \in \mathrm{RC}_n$ and $P' > P$ adds a cover compatible
with the existing collapse, then $P' \in \mathrm{RC}_n$.

(ii) The complement $\mathbf{Pos}_n^{\mathrm{sub}} \setminus
\mathrm{RC}_n$ is the **closure-stable** locus — posets $P$ for which
$<_P^* = <_P$ within the transitive closure of any chamber-induced
relation. These are exactly the posets where no incomparable pair is
order-implied — the "honestly incomparable" locus.

(iii) The 1/3–2/3 conjecture for width-3 asserts: every $P$ in
$\mathbf{Pos}_n^{\mathrm{sub}} \setminus \mathrm{RC}_n$ of width 3
has a (non-RC, hence genuine) balanced pair.

(iv) Equivalently in §3.5 cohomological terms: $\omega_{\mathrm{bal}}$
should restrict trivially to the **complement** of $\mathrm{RC}_n$.

So Daniel's framing translates to:

$$
\boxed{
\omega_{\mathrm{bal}}\bigl|_{\mathbf{Pos}_n^{\mathrm{sub}} \setminus
\mathrm{RC}_n} = 0
\quad \iff \quad
\text{1/3–2/3 holds outside refinement-collapse.}
}
$$

### 4.5 What "visible in the order structure" buys us

The visibility of $\mathrm{RC}_n$ from $<_P$ alone (without chamber
enumeration) means:

(a) Decomposing $\mathbf{Pos}_n^{\mathrm{sub}} = \mathrm{RC}_n \sqcup
\mathrm{RC}_n^c$ is **effective** — done by transitive-closure
computation.

(b) Cohomology localization is meaningful: the Mayer–Vietoris-style
sequence

$$
\cdots \to H^k(\mathbf{Pos}_n, F_\ell) \to
H^k(\mathrm{RC}_n, F_\ell) \oplus H^k(\mathrm{RC}_n^c, F_\ell) \to
H^k(\mathrm{RC}_n \cap \mathrm{RC}_n^c, F_\ell) \to \cdots
$$

becomes computable in principle, with $\mathrm{RC}_n \cap
\mathrm{RC}_n^c$ being the "boundary" of the collapse locus.

(c) **Polecat-tractability.** Enumerating $\mathrm{RC}_n$ for small
$n$ is a quadratic-time-per-poset task; total cost $O(|\mathbf{Pos}_n
^{\mathrm{sub}}| \cdot n^2)$, polynomial in the OEIS A001035 size.

---

## 5. Local-to-global: what "forces balance"?

Daniel's framing: "Pos_n has enough categorical regularity that
semantic local data glues globally, forcing balance unless a
refinement-collapse is visible." We unpack:

### 5.1 Local data = link cohomology

For $P \in \overline{\mathbf{Pos}_n^{\mathrm{sub}}}$, the **link**
$\mathrm{lk}(P) := \Delta_{> P}(\overline{\mathbf{Pos}_n^{\mathrm{sub
}}})$ is the order complex of the upper interval — all proper
refinements of $P$. Local cohomology
$H^*(\mathrm{lk}(P), F_\ell|_{\mathrm{lk}(P)})$ measures obstruction
to extending sections defined near $P$.

### 5.2 The local balance condition

Define $\beta_{\mathrm{loc}}(P) \in \mathbb{Q}$ as

$$
\beta_{\mathrm{loc}}(P) := \min\bigl\{
\Pr_P[a <_P b] \cdot (1 - \Pr_P[a <_P b])
: (a,b) \text{ incomp. in } P\bigr\}.
$$

Balance at $P$ is $\beta_{\mathrm{loc}}(P) \ge 1/3 \cdot 2/3 = 2/9$.
Anti-balance is $\beta_{\mathrm{loc}}(P) < 2/9$.

$\beta_{\mathrm{loc}}$ is a function $\mathbf{Pos}_n^{\mathrm{sub}}
\to \mathbb{Q}_{\ge 0}$; it is **not** a sheaf section (min is not
linear) but its sublevel sets define subcomplexes
$\mathbf{Pos}^{\ge t} := \{P : \beta_{\mathrm{loc}}(P) \ge t\}$.

### 5.3 Categorical regularity = persistent sheaf structure

The "categorical regularity" of $\mathbf{Pos}_n^{\mathrm{sub}}$
manifests as:

(R1) **Galois closure.** Every chamber subset $A \subseteq S_n$ has
a unique poset $P(A)$ with $\mathcal{L}(P(A)) \supseteq A$
maximally constrained; the closure $A \mapsto \mathcal{L}(P(A))$ is
**idempotent** (mg-296d §1.2).

(R2) **Cover-relation gradedness.** $\mathbf{Pos}_n^{\mathrm{sub}}$
is graded by relation count, with covers given by adding a single
cover relation modulo transitive closure. Covers are local.

(R3) **(T3)-sheaf condition for $F_\ell$.** Chamber covers determine
$F_\ell$ globally (§1.1).

(R4) **Eigensheaf structure.** $F_\ell$ is a $\Delta_{(a,b)}$-
eigensheaf with $P$-dependent eigenvalue $1 - \Pr_P[a<b]$ (mg-296d
§5.2).

(R1)–(R4) are the structural facts that make "local-to-global"
meaningful here. (R1)+(R2) give the lattice structure; (R3)+(R4)
give the sheaf structure with rich operator action.

### 5.4 The forcing principle (informal)

Daniel's principle:

*If $\beta_{\mathrm{loc}}(P) < 2/9$ holds for every $P$ in some
open neighborhood $U \subseteq \mathbf{Pos}_n^{\mathrm{sub}}$, then
either $U \subseteq \mathrm{RC}_n$ or there is a global obstruction
class in $H^*(U, F_\ell)$ that detects the failure.*

To make this rigorous we'd need:

(P1) A precise "open neighborhood" notion. For (H-β), $U$ would be
a down-closed subset of $\overline{\mathbf{Pos}_n^{\mathrm{sub}}}$
under refinement.

(P2) The obstruction class. The candidate is
$\omega_{\mathrm{bal}} \in H^{d_n}(\overline{\mathbf{Pos}_n^{\mathrm{
sub}}}, F_\ell)$ as in §3.4.

(P3) The implication "$\omega_{\mathrm{bal}}|_U = 0 \Rightarrow$ a
balanced pair exists in $U$." This is the load-bearing step.

### 5.5 Where the proof might (or might not) come from

**Optimistic route.** If cat-mg-5ee2 shows $|\Delta(\overline{
\mathbf{Pos}_n^{\mathrm{sub}}})| \simeq S^{d_n}$:

(i) $H^{d_n} = \mathbb{Q}$ is 1-dimensional; the fundamental class
$\omega_{\mathrm{bal}}$ is unique up to scale.

(ii) For width-$\le 3$ posets, the link $\mathrm{lk}(P)$ inside the
width-3 stratum has bounded topological complexity (sphere of lower
dimension, by an induction).

(iii) Vanishing of the restricted class on $\mathrm{lk}(P)$ would
follow from a Poincaré-dual integration argument: $\omega_{\mathrm{
bal}}$ pairs with a "balance functional" to give a numerical
invariant; vanishing iff the functional has a kernel at $P$ —
iff $\beta_{\mathrm{loc}}(P) \ge 2/9$.

**Skeptical route.** The contractibility argument (§3.2) shows that
the *full* $\mathbf{Pos}_n^{\mathrm{sub}}$ has trivial cohomology;
removing the apex points doesn't automatically produce sphere
topology, and the (R4) eigenvalue structure may not survive passage
to the proper part as cleanly as desired.

**Honest middle ground.** The cohomological framework gives a
**clean target invariant** (the top class $\omega_{\mathrm{bal}}$);
it does **not** automatically give a proof technique. The proof
would need either (a) the sphere-topology lemma from cat-mg-5ee2, or
(b) an explicit construction of $\omega_{\mathrm{bal}}$ as a
representable functional whose vanishing is balance — a substantive
new combinatorial theorem.

---

## 6. Connection to the Step 2 chain

mg-c853 §3:

$$
\text{rich local commutativity}
\xrightarrow{\text{Step 1}} \text{expansion}
\xrightarrow{\text{Step 2}} \text{balance}.
$$

The present framework recasts Step 2 as:

**Step 2 (cohomological form).** *For width-$\le 3$ posets, the
top-degree cohomology class $\omega_{\mathrm{bal}} \in
H^{d_n}(\overline{\mathbf{Pos}_n^{\mathrm{sub}}}, F_\ell)$ vanishes
on every cell of $\Delta(\mathbf{Pos}_n^{\mathrm{sub}} \setminus
\mathrm{RC}_n)$.*

**Compared to other Step 2 framings.**

| Framing | Carrier | Load-bearing math |
|---------|---------|-------------------|
| Spectral (mg-c853 §2.4) | Poincaré inequality on $G_P$ | Dirichlet-energy bound |
| Eigensheaf-direct (mg-296d §7.ii) | Verdier duality of $F_\ell$ | Find Verdier dual co-sheaf |
| **Cohomological (this ticket)** | $\omega_{\mathrm{bal}}|_{\mathrm{RC}_n^c} = 0$ | Sphere topology of $\Delta(\overline{\mathbf{Pos}_n})$ + Poincaré-dual integration |
| $q$-family (mg-296d §7.iii) | Flat family over $\mathbb{A}^1_q$ | Specialization at $q$-special values |

**Distinguishing feature of cohomological framing.** Unlike the
spectral framing (which needs a *quantitative* Dirichlet-energy
bound) and the Verdier framing (which needs a specific dual
construction), the cohomological framing reduces 1/3–2/3 to a
**topological** question about $\Delta(\overline{\mathbf{Pos}_n^{
\mathrm{sub}}})$. This is a different proof-shape — finite-
dimensional homotopy theory rather than analysis.

**Risk.** The cohomological framing is **conditional** on three
non-trivial inputs:

(C1) $|\Delta(\overline{\mathbf{Pos}_n^{\mathrm{sub}}})|$ has the
sphere topology (cat-mg-5ee2).

(C2) The fundamental class $\omega_{\mathrm{bal}}$ admits a Poincaré-
dual representation as a balance functional (open).

(C3) (RC = balance) for width $\le 3$ (§4.3 claim, open).

Without (C1) the top class is undefined. Without (C2) the class is
formal and disconnected from $\Pr$-eigenvalues. Without (C3) the
"refinement-collapse exception" doesn't match the conjecture's
exception class.

---

## 7. Connection to other Compat-Geom threads

### 7.1 mg-296d (eigensheaves) — direct predecessor

§4.2 $\Delta_{(a,b)}$ acts on cocycles in $C^k(\overline{\mathbf{Pos}
_n^{\mathrm{sub}}}, F_\ell)$. Since $\Delta_{(a,b)}$ is an
endofunctor on sheaves, it induces an action on cohomology
$\Delta_{(a,b)}^* : H^*(\overline{\mathbf{Pos}_n}, F_\ell) \to
H^*(\overline{\mathbf{Pos}_n}, F_\ell)$.

The eigenvalue spectrum of $\Delta_{(a,b)}^*$ on $H^{d_n}$ is the
spectrum of multiplication by $(1 - \Pr_P[a<b])$ at each $P$,
projected to top cohomology — i.e., a **trace** $\mathrm{tr}_P(1 -
\Pr_P[a<b])$ over the cells of $\Delta$.

This trace is the **expected eigenvalue** under the uniform measure
on cells, and the 1/3–2/3 conjecture restated:

*The mean of $\Delta_{(a,b)}^*$-eigenvalue over $\Delta(\overline{
\mathbf{Pos}_n})$ lies in $[1/3, 2/3]$ for some $(a,b)$.*

This recovers mg-296d §6 (Pr-spectrum statement) but **averaged
over the cell complex** rather than localized at a single $P$. The
cohomological framing trades pointwise statements for integrated
ones.

### 7.2 cat-mg-5ee2 (Pos_n-as-sphere) — load-bearing dependency

(C1) above directly. If cat-mg-5ee2 verdict is RED (Pos_n is *not*
a sphere), the cohomological framing **collapses** to the bare
contractibility result (§3.2) and the obstruction-class avenue
fails. If GREEN, §3.4–§3.5 become operational.

**Recommended PM action.** Wait for cat-mg-5ee2's verdict before
investing in cohomological Step 2 proof attempts.

### 7.3 mg-c853 (manifesto + feasibility)

§3 Step 2 is recast in cohomological language here. The
identification §2.4 ("$F_\ell \cong \underline{\mathbb{Q}}$ as a
sheaf") narrows mg-c853's claim that "the eigensheaf structure
encodes the Pr-spectrum": at the cohomology level the twist is
trivializable, and the genuine eigenvalue information lives in the
$\Delta_{(a,b)}^*$-action on cohomology, not in the cohomology
group itself.

### 7.4 mg-5fe9 (Hecke / q-family)

§7.iii of mg-296d. If a $q$-deformation of $F_\ell$ exists (a flat
family $F_\ell^{(q)}$ over $\mathbb{A}^1_q$), then
$H^*(\overline{\mathbf{Pos}_n}, F_\ell^{(q)})$ is a $\mathbb{Q}[q]$-
module with rank computable from the $q=1$ fiber. The 1/3–2/3
conjecture deforms to "$q$-Pr-spectrum contains an interval" — a
different proof avenue with the same target. Out of scope here.

### 7.5 mg-4e67 (cell-poset)

The width stratification of $\mathbf{Pos}_n^{\mathrm{sub}}$ by
Greene-shape $\lambda \vdash n$ induces a filtration of
$\Delta(\overline{\mathbf{Pos}_n^{\mathrm{sub}}})$ by sub-
complexes $\Delta_\lambda$. The cohomological localization of
$\omega_{\mathrm{bal}}$ to width-3 strata
($\ell(\lambda) \le 3$, i.e., $\lambda \in \{(n), (n-1, 1), (n-2,
1, 1), (n-2, 2)\}$ and similar low-multiplicity shapes) is the
natural refined target for the OneThird headline.

### 7.6 sub-α-C / Brightwell axiom (mg-38cf, mg-b699)

The residual `brightwell_sharp_centred` axiom in `step8.tex`
asserts a specific Pr-bound. In the cohomological framework this
becomes a statement about the **value** of $\omega_{\mathrm{bal}}$
on a specific subcomplex (the layered $K=2$ width-3 stratum). The
Path P3 enumeration (mg-9d6c, mg-9a4a, mg-a5b1) computes this
value directly; the cohomological reframe doesn't shortcut the
computation but provides structural understanding.

---

## 8. Lean formalization estimate

The full cohomological framework is **specialist-class** to
formalize; we estimate a polecat-tractable subset below.

**§2 (cohomology theory setup):** 800–1500 LoC. Mathlib has
`AlgebraicTopology.SimplicialSet`, `CategoryTheory.Sites.*`. The
order-complex / Mitchell cohomology of a small category is
implementable but not directly in mathlib. Implementing
$\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$ + its cochain complex would
require a new file `Mathlib/AlgebraicTopology/OrderComplex.lean` or
similar; ~500 LoC for definitions, ~500 LoC for the
contractibility-via-cone-point lemma (§3.2).

**§2.4 (trivialization $F_\ell \cong \underline{\mathbb{Q}}$):**
~200 LoC. Direct computation given §1.2 + the definitions.

**§3.3 (proper part, removal of $\widehat 0, \widehat 1$):** ~300
LoC. Set-up plus the resulting cochain complex.

**§4 (RC locus definition + transitive-closure characterization):**
~400 LoC. Definition of (RC-up)/(RC-down)/(RC-mixed) + Lemma 4.2
(transitive-closure characterization, standard from Stanley EC1).

**§5–§6 (cohomological balance conjecture statement):** ~200 LoC
just for the statement; the **proof** is conditional and not
polecat-class.

**Cumulative polecat-tractable scope (assuming cat-mg-5ee2 lands a
sphere result):** ~1500–2500 LoC for §2 + §3.3 + §4 + §6 statement.
This is **specialist-near** — at the boundary of polecat capacity.

**Out of scope for polecat:** the proof of (CB) itself; the Poincaré-
dual representation of $\omega_{\mathrm{bal}}$; the (RC = balance)
equivalence.

---

## 9. Open questions

(Q1) **Sphere topology of $\Delta(\overline{\mathbf{Pos}_n^{
\mathrm{sub}}})$.** The load-bearing question; deferred to
cat-mg-5ee2. Concrete sub-questions:

- (Q1a) Is $\Delta(\overline{\mathbf{Pos}_3^{\mathrm{sub}}})$
  homotopy-equivalent to $S^1$? Explicit calculation feasible from
  the 12-element proper part.
- (Q1b) If so, does $\Delta(\overline{\mathbf{Pos}_n^{\mathrm{sub}}})
  \simeq S^{\binom{n}{2} - 2}$ for $n \ge 3$? (The expected
  dimension if the proper-part is "(n-1)-spherical" in Björner–Wachs
  sense.)

(Q2) **Refinement-collapse classification.** Is the (RC = balance)
claim (§4.3) provable for width $\le 3$? Concrete sub-question:

- (Q2a) Construct a width-3 poset $P$ with (RC-mixed) collapse
  that is NOT (RC-up) ∨ (RC-down). If exists, refutes (RC = balance);
  if none exists for $n \le 6$, evidence for the claim.

(Q3) **Poincaré-dual functional.** Find a $d_n$-form (cellular
representative) $\omega_{\mathrm{bal}}$ whose value on a cell
$P_1 < \cdots < P_{d_n+1}$ is the product
$\prod_i \Pr_{P_i}[a_i <_{P_i} b_i]$ (§3.4). Is this a
cocycle? Is its cohomology class non-zero in $H^{d_n}$?

(Q4) **Mayer–Vietoris for $\mathrm{RC}_n \sqcup \mathrm{RC}_n^c$.**
Make §4.5 (b) precise: compute the long exact sequence; identify
the boundary class as a function of (RC-up)/(RC-down) counts.

(Q5) **Equivariance.** $S_n$ acts on $\mathbf{Pos}_n^{\mathrm{sub}}$
by relabeling (mg-296d §1.3); the cohomology
$H^*(\overline{\mathbf{Pos}_n^{\mathrm{sub}}}, F_\ell)$ inherits an
$S_n$-action. What are the irreducible components? Does
$\omega_{\mathrm{bal}}$ live in the trivial or sign representation?

(Q6) **Comparison with cuts-by-pairs (mg-d4ed).** The cuts-by-pairs
framework gives a different stratification of $\mathbf{Pos}_n^{
\mathrm{sub}}$ by "low-energy cuts." Does the cuts complex coincide
with $\Delta(\overline{\mathbf{Pos}_n})$ up to homotopy? If so, both
scopings target the same topological invariant.

(Q7) **Spectral sequence for the width-stratification.** The Greene
shape stratifies $\overline{\mathbf{Pos}_n}$. The induced spectral
sequence

$$
E_1^{p,q} = H^q(\Delta_p^c, F_\ell) \Rightarrow H^{p+q}(\overline{
\mathbf{Pos}_n}, F_\ell)
$$

(where $\Delta_p^c$ is the width-$p$ stratum closure) might collapse
on the $E_1$ page, exposing the width-3 contribution directly.

---

## 10. Verdict

**AMBER-specialist, conditional on cat-mg-5ee2.**

### What is precise and formalizable at scoping resolution

- §1 recap from mg-296d — PRECISE (cited).
- §2.4 trivialization $F_\ell \cong \underline{\mathbb{Q}}$ —
  PRECISE, proven.
- §3.2 contractibility of $\Delta(\mathbf{Pos}_n^{\mathrm{sub}})$ —
  PRECISE, follows from the cone-point argument.
- §4.1–§4.2 (RC-up)/(RC-down) definitions + transitive-closure
  characterization — PRECISE (Stanley EC1).
- §4.4 $\mathrm{RC}_n$ as an upward-closed subset of $\mathbf{Pos}_n
  ^{\mathrm{sub}}$ — PRECISE.

### What is conditional (depends on cat-mg-5ee2 or further work)

- §3.3–§3.4 top-degree class $\omega_{\mathrm{bal}}$ — CONDITIONAL
  on $|\Delta(\overline{\mathbf{Pos}_n^{\mathrm{sub}}})| \simeq
  S^{d_n}$.
- §3.5 (CB) cohomological balance conjecture — CONJECTURE.
- §4.3 (RC = balance) for width-3 — CONJECTURE.
- §5 local-to-global forcing principle — IMPRECISE STATEMENT
  pending (CB) + (C2) Poincaré-dual representation.

### What is genuinely new mathematics in this scoping

- §2.4 the *cohomological triviality* of $F_\ell$ under the change
  of variables $\beta_P = |\mathcal{L}(P)| \alpha_P$. This is a
  scoping-level observation but had not been articulated in
  predecessor docs (mg-296d §6 stops at the eigenvalue-density
  statement).
- §3.5 (CB) — the specific cohomological-class-vanishing reformula-
  tion of 1/3–2/3.
- §4.4–§4.5 the **explicit identification** of "refinement-collapse"
  as the (RC-up) ∪ (RC-down) ∪ (RC-mixed) locus, with (RC-up)/(RC-
  down) **order-visible** via transitive closure. This makes
  Daniel's phrase precise.

### What narrows the manifesto's scope

- The naive cohomological-obstruction avenue (mg-296d §7.i)
  **fails** on $\mathbf{Pos}_n^{\mathrm{sub}}$ itself (contract-
  ibility, §3.2). The avenue is only viable on the **proper part**
  $\overline{\mathbf{Pos}_n^{\mathrm{sub}}}$.
- The avenue is **conditional** on sphere topology (cat-mg-5ee2).
- The avenue **does not** automatically give a proof — it gives a
  **target invariant**. Reaching the target requires solving (Q2)
  + (Q3) independently.

### Why AMBER not GREEN

Three load-bearing conjectures stand between scoping and proof:
(C1) sphere topology, (C2) Poincaré-dual representation, (C3) RC =
balance. Each is non-trivial. No single one has a known proof
sketch in this scoping.

### Why trending AMBER-clarifying (not RED-against)

(a) **§2.4 triviality is unexpected and clean.** The $|\mathcal{L}|$
change of variables converts the eigensheaf into the constant sheaf
canonically. This means cohomology of the proper part is computable
in principle for any small $n$ (combinatorial-topology textbook
exercise), and the resulting obstruction is intrinsic.

(b) **Refinement-collapse is order-visible.** (RC-up)/(RC-down) are
detectable by transitive closure (Lemma §4.2). Daniel's phrasing —
"refinement-collapse is visible inside the order structure" —
is **literally true** for these two types. The (RC-mixed) case is
where the genuine 1/3–2/3 content lives.

(c) **Conditional on cat-mg-5ee2.** If the sibling scoping confirms
sphere topology, the framework gains a **concrete and computable**
target invariant. If not, the avenue collapses cleanly to "not a
proof technique" — no false starts.

(d) **Polecat-tractable subset exists.** §2–§4 (excluding the
load-bearing §5–§6) is ~1500–2500 LoC and could be Lean'd
independently as foundation infrastructure for any of the three
mg-296d §7 avenues. Highest near-term leverage.

### Recommended next actions (PM-level)

1. **Wait for cat-mg-5ee2's verdict.** The cohomological avenue is
   conditional on sphere topology. If cat-mg-5ee2 reports RED, this
   ticket's recommended follow-on (specialist-class proof of CB) is
   wasted; if AMBER/GREEN, this ticket's framework becomes
   immediately operational.

2. **Compute Q1a explicitly.** $\Delta(\overline{\mathbf{Pos}_3^{
   \mathrm{sub}}})$ has 12 vertices and a tractable simplicial
   structure. A polecat-class follow-on can compute its homotopy
   type by hand or by Lean enumeration. This is the **smallest
   non-trivial test case** of cat-mg-5ee2's sphere hypothesis.

3. **Investigate Q2a (RC = balance counter-examples).** Enumerate
   width-3 posets on $n \le 6$, identify (RC-mixed) examples that
   are not (RC-up) ∨ (RC-down), check if any have balanced pairs.
   Polecat-class, ~300k token budget.

4. **Defer Q3 (Poincaré-dual functional).** Requires specialist
   input on cellular cohomology of poset complexes; not polecat
   resolvable.

5. **Defer formalization** of the cohomology infrastructure until
   the conditional inputs (C1)–(C3) resolve.

6. **No separate repo decision.** Aligns with mg-c853 / mg-296d
   recommendation: stay in `one_third_width_three`.

7. **State.md coordination.** No `state.md` exists in the repo at
   the time of this scoping; sibling cat-mg-5ee2 will not touch
   `state.md` either (only docs/). The ticket's coordination note
   is preserved for forward-state.

---

## 11. Token-budget report

This document is ~600 lines of substantive content authored in a
single polecat session. The 400k token cap was not approached. No
trip-wires fired. No new axioms introduced.

Predecessors referenced but not modified: mg-c853 (manifesto +
feasibility), mg-296d (eigensheaves), mg-5fe9 (q-family), mg-4e67
(cell-poset), mg-d4ed (cuts-by-pairs), mg-38cf / mg-b699 (Brightwell
axiom thread), mg-9d6c / mg-9a4a / mg-a5b1 (Path P3).

Sibling cross-referenced but not coordinated through `state.md`
(file does not exist yet): cat-mg-5ee2 (Pos_n-as-sphere).

---

*Authored by polecat mg-d60d, branch `polecat-cat-mg-d60d` → target
`compat-geom-poset-cohomology`. Predecessor: mg-296d (per ticket §1).
2026-05-13.*
