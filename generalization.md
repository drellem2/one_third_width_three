# Generalization to width $w \ge 4$: where the proof depends on width-3

**Scope.** This document is *expository*. It catalogues every place in
the eight-step proof program (`step1.tex`–`step8.tex`) where the
hypothesis $w(P)=3$ is used, classifies each use as

- **(a)** easily generalizable to width $w$ (the argument goes through
  with $3$ replaced by $w$ and at most cosmetic constant changes),
- **(b)** requires new ideas, but the natural extension is plausible
  (the existing argument breaks, but a recognizable analogue ought to
  work after substantial new work), or
- **(c)** fundamentally width-3-specific (no clear analogue, or the
  obstruction is of a different *kind* in higher width),

and discusses how the BK-graph geometry, the natural extension
strategy, and the main obstacles change as $w$ grows. No proof is
attempted; the goal is to delimit what would and would not survive a
naive translation, and to point at where the genuinely new mathematics
would be needed.

A short reading: **most of the analytic and combinatorial machinery in
Steps 5–8 is class (a) or (b) — what is class (c) is the geometric
*core*, namely the width-3 fiber model in Step 1 and its triple-overlap
$\mathbb Z^3$-cube corollary in Step 7**. Without those, the entire
incompatibility/coherence dichotomy loses its ambient coordinate
system. There is also a hard ceiling on the minimal-counterexample
reduction at Step 7/8: it bottoms out in **Linial's width-2 theorem**,
which has no known $w \ge 3$ analogue.

---

## 1. The width-3 hypothesis at a glance

Width-3 enters the proof through three structurally distinct
mechanisms:

1. **Antichain bound.** Every antichain of $P$ has $\le 3$ elements.
   This is what is used most often, and it appears in two slightly
   different forms:
   - "no $4$-element antichain" (used in Step 1 to force $N(x,y)$ to
     be a chain, and in Step 7 to embed pairwise common chains in a
     common ambient chain), and
   - $|L_k| \le 3$ for each level of a layered decomposition (Step 7,
     Step 8 G3/G4).
2. **Dilworth chain count.** $P$ partitions into $\le 3$ chains, hence
   $\binom{3}{2} = 3$ chain-pair types. This appears in Steps 4, 5, 6
   as the bookkeeping that makes overlap-counting constants $O(1)$
   with no $n$-dependence.
3. **Base case for minimal-counterexample reduction.** When the
   minimal counterexample reduces to a strictly smaller $P'$, "width
   drops to $2$" is one of the two terminal cases, discharged by
   Linial's width-2 theorem. This appears in Step 7 Prop. 7.3 and is
   indirectly inherited by Step 8 G3.

Mechanism (1) is the tightest and is the source of essentially all
class (c) uses below. Mechanisms (2) and (3) drive most class (b)
issues.

---

## 2. Per-step inventory

For each step we list every distinguishable place width-3 is invoked,
classify it (a)/(b)/(c), and quote the relevant LaTeX label or line.

### Step 1 — Interface theorem and triple-overlap cube

This step is by far the **most width-3-dependent step in the program**.
Its conclusions are the geometric inputs that every later step
consumes.

| # | Use | Where | Class |
|---|-----|-------|-------|
| 1.1 | $N(x,y)$ is a chain (Lemma `lem:CNchain-width3`) — "if two common neighbors $z, z'$ of an incomparable pair $x \parallel y$ were themselves incomparable, $\{x,y,z,z'\}$ would be a $4$-antichain". | `step1.tex:40–46` | **(c)** |
| 1.2 | A single global "external" element $z \notin \{x,y\} \cup C_{xy}$ has at most $|I(z)| \le 2$ values of $k$ with $z \parallel c_k$ — otherwise $\{z, c_{k_1}, c_{k_2}, c_{k_3}\}$ together with $\{x, y\}$ produces a width-$4$ configuration. This is what makes the bad set a $1$-dimensional strip family. | `step1.tex:259–262` | **(c)** |
| 1.3 | The local coordinate space $D_{x,y} \subseteq [0, t_{xy}]^2$ is $2$-dimensional because the "third chain" is exactly one chain. | `step1.tex:82–87` (Definition) and §2 | **(c)** |
| 1.4 | The triple-overlap $\mathbb Z^3$-cube corollary: three rich pairs $(x,y), (y,z), (x,z)$ share a common chain window $W$, on which the three coordinate systems generate a commuting $\mathbb Z^3$ action. | `step1.tex` `cor:triple-overlap` | **(c)** |

**Why (c).** Each item depends on the assertion *"a 4-element antichain
is forbidden."* In width $w$, $N(x,y)$ is a poset of width $\le w-2$.
By Dilworth it splits into $\le w-2$ chains, not one. The local
coordinate space therefore lives in $[0,t]^2 \times \mathbb Z^{w-3}$
(coarsely), with bad-set strips becoming bad-set codimension-$1$
hyperplanes in dimension $\ge 3$. The clean $\mathbb Z^2$ rectangle
model is structurally lost in width $\ge 4$, and the $\mathbb Z^3$
cube of `cor:triple-overlap` becomes a $\mathbb Z^{1 + 3(w-2)}$ flag
of common-chain coordinates with no obvious normal form.

The *ideas* survive — there is still a fiber, still a polytope of
local coordinates, still BK moves acting as unit translations — but
the geometric object that Steps 2–7 manipulate is no longer a planar
staircase, no longer a single threshold $\tau \in \mathbb Z$, and no
longer a $3$-cycle $\tau_{xz} = \tau_{xy} + \tau_{yz} + O(1)$.

### Step 2 — Per-fiber staircase

Step 2 is parasitic on Step 1's fiber model.

| # | Use | Where | Class |
|---|-----|-------|-------|
| 2.1 | The monotone-staircase target shape $M_{x,y}$ lives in a $2$D order-convex domain, hence is $1$D in its boundary — what gives the staircase its name. | `step2.tex` Lemma 2.4 statement; `step4.tex:56–67` (cited form) | **(b)** in form, **(c)** in current proof |
| 2.2 | The "weak grid stability" Lemma 2.4 uses unit-step BK moves in the $\mathbb Z^2$ coordinate system. | `step2.tex:88` (cited width-3 normal form) | **(b)** |
| 2.3 | The bounded-multiplicity constant $K = O(1)$ from Step 1 (S1.6) appears as a cited width-3 input in Lemma 3.1. | `step2.tex:917` | **(b)** |

**Why (b) rather than (c).** Step 2's *technique* — random-cluster /
monotone shape stability for low-conductance cuts — is generic
combinatorics. In higher width, the staircase becomes a monotone
hyperregion in $[0,t]^2 \times \mathbb Z^{w-3}$, and the "weak grid
stability" lemma extends conjecturally with the same proof template
once the higher-dimensional analogue of the order-convexity (S1.1) and
unit-grid moves (S1.2) is in place from Step 1's generalization. The
real content stays in Step 1.

### Step 3 — Canonical axes / signs

| # | Use | Where | Class |
|---|-----|-------|-------|
| 3.1 | Each rich pair carries a *single* sign $\eta_{xy}(L) \in \{\pm 1\}$ — the orientation of the staircase in the $1$D boundary direction. | `step3.tex` G5–G7 | **(b)** in dimension, becomes a vector $\eta \in \{\pm 1\}^{w-2}$ in width-$w$ |
| 3.2 | "Bad set covered by $O(1)$ strips of width $O(t)$" is invoked verbatim when bounding two-interface overlap bad sets. | `step3.tex:1029` | **(b)** |

**Generalization.** In width $w$ the relevant "sign" is the
multidirectional orientation of a monotone hyperregion in
$\mathbb Z^{w-1}$, with $w-2$ binary degrees of freedom (one per
"third-chain" component). The cocycle/coherence framework downstream
(Steps 4, 6, 7) is built around scalar signs and scalar thresholds; it
must be reformulated for vector-valued signs and integer-vector
thresholds. This is plausibly mechanical but has not been done.

### Step 4 — Two-interface incompatibility

| # | Use | Where | Class |
|---|-----|-------|-------|
| 4.1 | "By Dilworth, $P$ decomposes into at most $3$ chains $C_1, C_2, C_3$, and any incomparable pair lies in two distinct chains" — gives $\binom{3}{2} = 3$ chain-pair types. | `step4.tex:961–967` (Lemma G6 proof, Step 4) | **(a)** |
| 4.2 | Edge multiplicity $M = O(1)$ depends only on the width ($=3$), not on $|P|$ or $T$ (cited explicit reliance). | `step4.tex:1015–1017` | **(a)** |
| 4.3 | The rectangle model of §`sec:rectangle-model` is $2 \times 2$ (two interfaces, two BK directions, one square per overlap block). | `step4.tex:111–125` | **(b)** |

**Generalization.** Replacing $3$ by $w$ gives $\binom{w}{2}$
chain-pair types and $M = O(w^2)$. The double-counting argument is
unchanged; only the constant scales. The rectangle model becomes a
hypercube model — two interfaces still produce $\mathbb Z^2$
(transpositions are always pairwise!) — but the *ambient* fiber on
which the rectangle sits is higher-dimensional, so the inheritance
from Step 1 is what carries the (c) burden.

### Step 5 — Rich/Collapse dichotomy

| # | Use | Where | Class |
|---|-----|-------|-------|
| 5.1 | "Fix a Dilworth decomposition $P = A \sqcup B \sqcup C$ into three chains." Without exactly three chains the entire setup breaks: the dichotomy is stated against a fixed *partition*. | `step5.tex:18–27` | **(a)** in form, but inflates the case analysis |
| 5.2 | Three chain-pair types $(AB \mid C), (AC \mid B), (BC \mid A)$ appear by name in the dichotomy theorem. | `step5.tex:82–88, 140–143` | **(a)** |
| 5.3 | Collapse case produces three monotone maps $f_{AB}, f_{AC}, f_{BC}$ — one per chain pair. | `step5.tex:96–101` | **(a)** |
| 5.4 | "Common neighbors lie entirely inside the third chain": $C(x,y) = \mathrm{IC}(x) \cap \mathrm{IC}(y)$, both intervals in chain $C$. | `step5.tex:54–62` | **(b)** |

**Generalization.** With $w$ chains $C_1, \ldots, C_w$ the
Rich/Collapse dichotomy becomes an *enumerated* dichotomy over
$\binom{w}{2}$ ordered chain-pair types. The Collapse case must
produce $\binom{w}{2}$ monotone synchronization maps. Item 5.4 is the
genuinely awkward one: in width-$w$, an incomparable pair $(x,y)$ has
common neighbors potentially distributed over $w-2$ chains, and
$C(x,y) = \bigsqcup_{c} \mathrm{IC}_{C_c}(x) \cap \mathrm{IC}_{C_c}(y)$
is a *union of intervals*, no longer a single chain. This is what
makes Step 5's "interval form" only weakly generalizable.

### Step 6 — Incompatibility engine

| # | Use | Where | Class |
|---|-----|-------|-------|
| 6.1 | "By Dilworth's theorem the width-3 poset $P$ partitions into at most three chains $C_1, C_2, C_3$; any incomparable pair is drawn from two distinct chains, so there are $\binom{3}{2} = 3$ chain-pair types." | `step6.tex:418–423` (Lemma G4, overlap counting) | **(a)** |
| 6.2 | "At most one $\gamma$ per (chain-pair type, adjacent position pair)": at adjacent positions $(j, j+1)$, two distinct rich interfaces of the same chain-pair type would force $\gamma = \gamma'$ since each adjacent position pair contains exactly one element of each chain. | `step6.tex:425–431` | **(a)**/**(b)** |
| 6.3 | $M_0 = O(1)$ overlap-counting constant depends only on the width and the threshold. | `step6.tex:467–468` | **(a)** |
| 6.4 | "$\mathrm{vol}(S) = \sum_L \deg_{G_{\BK}}(L)$, width-3 caps the BK-degree" — bounded BK-degree is used as a width consequence. | `step6.tex:1286` | **(a)** |
| 6.5 | The proof of Step 6 inherits Step 1's $1$-dimensional bad set (used in `lem:overlap-counting` Step 3 and in §`sec:dichotomy-theorem`). | `step6.tex:202–207, 1146–1149` | **(b)** (via Step 1) |

**Generalization.** Items 6.1–6.4 are entirely about counting chain
pairs, and they go through with $\binom{w}{2}$ types and an
overlap-counting constant $M_0(w) = O(w^2)$. The interesting subtlety
is in 6.2: in width $w$, the adjacent position pair $(j, j+1)$ at $L$
no longer determines the elements uniquely from the chain-pair type
alone, because the *third chain* might also contribute elements at
nearby positions. The argument extends with case work, but the count
becomes per-window rather than per-position.

### Step 7 — Cocycle to potential, layered structure

This step has the second-largest concentration of width-3-specific
content after Step 1, and contains the most consequential class (c)
use elsewhere in the proof.

| # | Use | Where | Class |
|---|-----|-------|-------|
| 7.1 | "$C(x, y) = N(x) \cap N(y)$ is a chain by width 3." Used to state the cocycle hypothesis. | `step7.tex:27–28` | **(c)** (inherits from Step 1) |
| 7.2 | The threshold cocycle $\tau_{xz} = \tau_{xy} + \tau_{yz} + O(1)$ — the *core new lemma* of the program — relies on the three pairwise common chains $C(x,y), C(y,z), C(x,z)$ embedding in a single ambient chain $W$ of length $\ge t - O(1)$. This in turn uses width-3. | `step7.tex:418–458` (Lemma B, `lem:cocycle`) | **(c)** |
| 7.3 | Layered decomposition has $|L_k| \le 3$ — each level is an antichain of width $\le 3$. | `step7.tex:1130–1135`; cited from `step8.tex` Def. 5.1 | **(a)** in form, but interacts with class (c) below |
| 7.4 | Width-3 forces a *full* layer of size 3 — used in Prop. 7.3 (layered ⇒ balanced/reducible). "Otherwise $P$ would be a union of antichains of size $\le 2$ with the layered order, hence of width $\le 2$." | `step7.tex:1130–1135` | **(c)** |
| 7.5 | Linial's width-2 theorem is invoked as the base case when the minimal counterexample's induced subposet drops to width $\le 2$. | `step7.tex:1153–1154` | **(c)** — see §3 |
| 7.6 | "Width-3 guarantees" the Dilworth decomposition into three chains used to set up the bandwidth lemma. | `step7.tex:912–913` | **(a)** |
| 7.7 | "Width-3 chain geometry" + bandwidth lemma assembles the layered decomposition; bandwidth $K = O_T(1)$ uses three chains. | `step7.tex:927–965, 980–992` | **(a)** with $w$ in place of $3$ |
| 7.8 | "Width-3 normal form on triple overlaps" cited at multiple points. | `step7.tex:1486–1500, 1547, 1558` | **(c)** (inherits from Step 1) |

**Why 7.2 is the load-bearing (c) item.** The cocycle relation
$\tau_{xz} = \tau_{xy} + \tau_{yz} + O(1)$ is what lets the three
local thresholds integrate into a single global element-potential
$a \colon P \to \mathbb R$ (Prop. 7.1). Its proof builds a single
linearly-ordered ambient chain $W$ that simultaneously hosts $C(x,y),
C(y,z), C(x,z)$ up to $O(1)$ symmetric difference. In width-$w$, the
three pairwise common neighborhoods are themselves width-$\le w-2$
posets, not chains; they need not embed in a common chain. The natural
generalization replaces the single threshold $\tau_{uv} \in \mathbb Z$
with a vector $\boldsymbol\tau_{uv} \in \mathbb Z^{w-2}$ indexed by
the components of the multi-chain common neighborhood, and the cocycle
becomes a system of cocycle relations — one per "common ambient
hyperplane." This is plausible (de Rham-style), but it is genuinely
new work, and there is no a priori reason the resulting cocycle has a
common potential.

**Why 7.4 is independently (c).** The proof uses the *equivalence*
$\text{width}(P) = 3 \;\Leftrightarrow\;$ at least one antichain in
the cover has size exactly $3$. In width $w$, "at least one antichain
of size $w$" is the analogue, and forcing existence of such a layer
requires that every Dilworth-minimal cover of a width-$w$ poset
contains an antichain of size $w$ — which is true (by definition of
width!) but the *consequence* in the proof — that removing this layer
drops width strictly to $w-1$, allowing minimality induction — only
*helps* if a width-$(w-1)$ analogue of the conjecture is already
established. See §3.

### Step 8 — Assembly

| # | Use | Where | Class |
|---|-----|-------|-------|
| 8.1 | Dirichlet–conductance packaging (`lem:dirichlet-conductance`) holds for arbitrary BK graphs. | `step8.tex:114–152` | **(a)** |
| 8.2 | Indecomposable $\Rightarrow I(P) \ge n/2$ uses no width hypothesis. | `step8.tex:164–192` | **(a)** |
| 8.3 | Frozen-pair existence by averaging (`lem:frozen-pair-existence`) — the elementary Dirichlet-energy averaging argument that gives $\eta(\gamma, n) = 2/(\gamma n)$. **Uses no width hypothesis** beyond bounding $|L_i| \le w$ implicitly through the indecomposable count. | `step8.tex:194–271` | **(a)** |
| 8.4 | Theorem E (`thm:cex-implies-low-expansion`) packages Steps 8.1–8.3; the Cheeger inequality input is generic. | `step8.tex:154–315` | **(a)** |
| 8.5 | $|W| \le 6w$ in the layered-reduction lemma comes from $|L_i| \le 3$. | `step8.tex:1080` | **(a)** with $|W| \le 2w \cdot w$ |
| 8.6 | Layered ⇒ balanced/reducible (G3 + G4) reduces to a bipartite balanced-pair lemma on bands of width $\le 3$. | `step8.tex:1295–1402` | **(b)** |
| 8.7 | Bipartite balanced-pair proof handles $m \in \{2, 3\}$ by direct case analysis (sub-claim + telescoping average + finite enumeration). | `step8.tex:1295–1402` | **(b)** for $m \le w$ |
| 8.8 | Linial's width-2 theorem invoked for the minimality base case (inherits the Step 7 reliance). | implicit through `step7.tex:1153–1154` | **(c)** — see §3 |

**Generalization.** The Cheeger inequality / averaging argument in
8.1–8.4 is width-agnostic and goes through verbatim: counterexample
$\Rightarrow$ low BK conductance for *any* width. (The Dirichlet
energy bound $\sum \mathcal E(f_{xy}) \le 1/2$ is a count of
incomparable adjacent positions, which is at most $n-1$ regardless of
width.) The layered-reduction (G3) generalizes by replacing $|L_i| \le
3$ with $|L_i| \le w$ throughout, with $|W| \le 2w \cdot w$ in place
of $6w$. The bipartite balanced-pair lemma (G4) is the only Step 8
item that *case-explodes*: in width-$w$, "bipartite of antichain size
$\le w$" requires a finite-enumeration / FKG / averaging argument over
much larger configurations, and the clean inclusion–exclusion for
$m=3$ in `prop:bipartite-balanced` no longer suffices.

---

## 3. The Linial-width-2 ceiling

The single hardest obstruction to a width-$w$ generalization is **not**
in Step 1's geometry. It is in the *recursion*: the proof reduces a
width-3 minimal counterexample to a width-2 induced subposet via the
layered reduction (Step 7 Prop. 7.3, Step 8 G3). The width-2 case is
discharged by Linial's theorem (Linial 1984), which proves the
1/3–2/3 conjecture for posets of width $\le 2$.

**There is no analogous theorem for width $\ge 3$ — that is what the
present program is trying to prove.** Hence the natural inductive
strategy

> width-$w$ counterexample $\Rightarrow$ Step 7-style layered
> reduction $\Rightarrow$ width-$(w-1)$ counterexample $\Rightarrow$
> apply already-known width-$(w-1)$ result

reduces the width-$w$ conjecture to the width-$(w-1)$ conjecture. So
either:

- one proves width-$w$ inductively given width-$(w-1)$ — in which case
  this entire program *is* the inductive step at $w = 3$, and the
  argument can be re-run for each successive $w$, **provided** the
  Step 1 fiber model and the Step 7 cocycle relation generalize (both
  currently class (c)); or
- one proves width-$w$ outright for every $w$, with the same $w-2$
  fall-through to Linial.

Neither is currently in evidence. The architecture of the program is
strongly compatible with the first option, but Step 1 (geometric
$\mathbb Z^2$ fiber model) and Step 7 (cocycle on a single ambient
chain) appear to *break* at $w = 4$ in ways that are not just constant
inflation.

---

## 4. How the BK graph changes with width

The BK graph $G_{\BK}(P)$ — vertices $= \mathcal L(P)$, edges =
adjacent transpositions of incomparable pairs — is defined for any
poset, but its geometry is qualitatively different in higher width.

**Diameter and degree.** The maximum BK-degree of a linear extension
is $n - 1$ (one per adjacent position pair). Width-3 caps the
*expected* degree at a constant times $n / w$, since most adjacent
pairs are comparable. In width-$w$ the BK-degree concentrates around
$(1 - 1/w)(n-1)$, *increasing* with $w$. This is good for spectral
gap estimates but bad for sparsity-based combinatorial bookkeeping
(e.g., the overlap-counting constant $M_0$).

**Local structure at fibers.** The Step 1 fiber $\mathcal F_{x,y}$ is
the set of linear extensions in which the pair $(x, y)$ together with
its common-neighborhood chain $C_{x,y}$ are coordinatized. In width-3
this is a $\mathbb Z^2$ grid plus a sign $\sigma$, dimension 2.5
(non-integer because of the diagonal sign-flip). In width-$w$,
$N(x,y)$ has Dilworth complexity $w-2$, and the fiber locally looks
like a $\mathbb Z^2$ grid bundled over a $(w-3)$-dimensional discrete
torus of "which chain of $N(x,y)$ each common neighbor sits in."
Roughly, $\dim \mathcal F_{x,y} = 2 + (w-3)$ moves, all unit BK
moves but no longer in a planar diagram.

**Triple overlaps.** Step 1's triple-overlap corollary produces a
$\mathbb Z^3$-cube on three pairwise-rich interfaces sharing a common
chain window. In width-$w$, three rich interfaces $(x,y), (y,z),
(x,z)$ have common neighborhoods that are width-$\le w-2$ posets;
their pairwise intersections fragment into multiple chains; the
triple overlap is a $\mathbb Z^{1 + 3(w-3)}$ complex with rectangular
fibers, not a cube. In width-3 the three coordinate systems share a
single ambient chain $W$, which is why they all see *the same* one-
dimensional projection $d_{uv} = j_{uv} - i_{uv}$ and the cocycle
identity holds. In higher width, each pair sees a different
"sub-chain" of the common neighborhood, and there is no canonical
ambient chain — only a partial poset.

**Layered structure.** A "layered" decomposition $X = L_1 \sqcup
\cdots \sqcup L_K$ with $|L_k| \le w$ is a $w$-band poset. The
interaction window $|W|$ of the cutting lemma scales as $w \cdot
(2w+1)$. The Dilworth-style argument for picking the cut still works
verbatim. **What does not generalize** is that in width-3 the layered
poset always has at least one layer of full size 3 (else width
$\le 2$), and removing such a layer is a strictly width-decreasing
move *into the regime where Linial applies*. In width-$w$, removing a
size-$w$ layer goes to width $w - 1$, which is undecided.

---

## 5. Natural extension strategy and main obstacles

**Strategy.**

1. **Generalize Step 1.** Build a width-$w$ fiber model: define a
   higher-dimensional good fiber $\mathcal F_{x,y}$ on which BK moves
   act as commuting unit translations; prove an order-convex domain
   theorem; derive a higher-codimension bad-set bound. The natural
   target is a $(2 + (w-3))$-dimensional polytope with bad set in
   codimension $\ge 1$.
2. **Generalize Step 7's cocycle (Lemma B).** Define vector-valued
   thresholds $\boldsymbol\tau_{uv} \in \mathbb Z^{w-2}$ and show
   that on most active triples,
   $\boldsymbol\tau_{xz} = \boldsymbol\tau_{xy} + \boldsymbol\tau_{yz}
   + O(1)$ component-wise. From the cocycle, integrate to a
   vector-valued potential $\mathbf a \colon P \to \mathbb R^{w-2}$
   and a vector threshold $\mathbf c$.
3. **Re-derive layered structure.** With the vector potential, the
   level structure becomes $w-2$ simultaneous bandwidth conditions,
   and the layered decomposition has $|L_k| \le w$.
4. **Recursive base case.** Either accept that the program is an
   *inductive step* (assuming width-$(w-1)$) or build a bipartite
   balanced-pair lemma for arbitrary width-$w$ height-$2$ posets.

**Main obstacles.**

- **(O1) Common-neighborhood is no longer a chain.** Every appeal to
  `lem:CNchain-width3` (Steps 1, 5, 6, 7) needs replacement. The
  natural replacement is "common neighborhood is a width-$\le (w-2)$
  poset," which is much weaker structurally.
- **(O2) The $\mathbb Z^2$ rectangle model becomes a higher-cube
  bundle.** Step 4's two-interface incompatibility lemma uses a
  $2 \times 2$ rectangle on each overlap block (`step4.tex:111–125`).
  In higher width the relevant local model is still a $2 \times 2$
  *square in two transposition directions*, but it is fibered over a
  higher-dimensional base. The proof has to track all the bundled
  directions.
- **(O3) The cocycle has no canonical ambient chain.** Step 7 Lemma B
  reduces the cocycle to additivity in a single linearly-ordered
  window. In width-$w$ no such window exists; the additive identity
  must be proven coordinate-by-coordinate over a poset of common
  neighbors. Whether the resulting system is integrable (admits a
  scalar/vector potential) is a genuine new question.
- **(O4) Linial's theorem caps the recursion at $w = 2$.** Without an
  external proof of the conjecture for width $w-1$, the layered
  reduction is incomplete. This is the single largest obstacle and is
  unrelated to any of the geometry above.
- **(O5) Bipartite case-analysis explodes.** The finite-enumeration
  proof of `prop:bipartite-balanced` (Step 8 G4) handles bipartite
  layerings of size $\le 3$ in each layer by a clean inclusion–
  exclusion ($m = 3$ case, `step8.tex:1359–1379`). For general $w$,
  the analogous statement is "bipartite layered with $|A|, |B| \le w$
  has a balanced pair," and the FKG / sub-claim argument scales but
  the finite enumeration grows as $2^{w^2}$ configurations (modulo
  symmetry).

---

## 6. Summary classification

| Step | Class (a) (easy) | Class (b) (plausible) | Class (c) (hard) |
|------|------------------|------------------------|------------------|
| 1 | — | — | 1.1, 1.2, 1.3, 1.4 |
| 2 | — | 2.1, 2.2, 2.3 | (inherited) |
| 3 | — | 3.1, 3.2 | (inherited) |
| 4 | 4.1, 4.2 | 4.3 | (inherited) |
| 5 | 5.1, 5.2, 5.3 | 5.4 | (inherited) |
| 6 | 6.1, 6.3, 6.4 | 6.2, 6.5 | (inherited) |
| 7 | 7.3, 7.6, 7.7 | (none cleanly) | 7.1, 7.2, 7.4, 7.5, 7.8 |
| 8 | 8.1, 8.2, 8.3, 8.4, 8.5 | 8.6, 8.7 | 8.8 |

**Hard core.** The width-3-specific mathematics is concentrated in
**Step 1's fiber model** and the **Step 7 cocycle**, with the
**Linial-width-2 base case** providing an independent, structural
ceiling. Everything else is generalizable in principle — the
analytical engine of Steps 5, 6, 8 is essentially width-agnostic, and
the case-counting in Steps 4 and 6 only inflates polynomially in $w$.

**Practical consequence.** A width-4 attack on the conjecture along
the same lines would require, at minimum:

- a $3$-dimensional fiber theorem replacing Step 1 (with the bad set
  in codimension $1$ and a $\mathbb Z^3$ unit-grid action),
- a vector-valued cocycle theorem replacing Step 7 Lemma B, with
  proof of integrability,
- a width-3 base case for the minimal-counterexample reduction —
  i.e., the present program completed as an *unconditional* width-3
  theorem.

Items 1 and 2 are substantial new combinatorial work. Item 3 makes
the present width-3 program the *first* step in a longer induction,
not the final goal — which puts more pressure on the present program
to be airtight, since downstream extensions will inherit any of its
gaps.

---

## 7. References to specific files and lines

For a reader cross-checking each classification:

- Step 1: `step1.tex:40–46, 82–87, 209–217, 259–262`, and
  `cor:triple-overlap` (~line 320 onwards).
- Step 4: `step4.tex:23, 950–985, 1015–1017`.
- Step 5: `step5.tex:5–9, 18–27, 54–62, 76–101`.
- Step 6: `step6.tex:418–476, 1146–1149, 1286`.
- Step 7: `step7.tex:22–28, 384–458` (cocycle), `855–965`
  (bandwidth/layered), `1117–1184` (Prop. 7.3 reduction),
  `1486–1558` (triangle remarks).
- Step 8: `step8.tex:60, 154–315, 996–1015, 1080, 1216–1454`.

These line ranges are stable as of the 2026-04-18 / 2026-04-19 state
of the manuscript.
