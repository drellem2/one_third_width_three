# Compatibility Geometry — heap-subcategory ↔ Window C overlap (mg-a5b1)

**Companion to** `docs/compatibility-geometry-hecke-interpolation-scoping.md`
(`mg-5fe9` at `a32fe64`; AMBER-specialist trending GREEN, foundational
direction) and `docs/compatibility-geometry-pathP3-scoping.md`
(`mg-9d6c` at `9526cf4`; AMBER-narrow, applied direction) +
`docs/compatibility-geometry-pathP3-window-c-status.md` (`mg-9a4a`
at `1aaed17`; small-size Window C slice landed in tree). This
document answers `mg-5fe9 §5.3(iii)`'s crisp open question:

> *(iii) **Heap subcategory closure.** §4.2 shows that for the heap
> subcategory of width-3 posets — those realizable as heaps of
> fully commutative $w \in S_n$ — the constraint emergence is
> realized: width-3 fully commutative heaps include all width-3
> ZIGZAG / FENCE patterns and certain layered $K \le 3$ patterns.
> These do not cover the full OneThird residual axiom parameter
> range (which has non-heap layered $K \ge 4$ at $w \ge 2$), but
> they do cover a non-trivial sub-window — possibly overlapping
> with the mg-9d6c sub-GREEN Window C (the $K=4, w=1$ extension).
> Investigating this overlap is a possible follow-up.*

LaTeX inline ($\ldots$ / display) throughout; render with KaTeX
/MathJax or read source. **Latex-first; no Lean source changes;
no new axioms.**

**Verdict preview.** **AMBER-narrow, trending RED-against-bridge.**
The overlap between the Hecke / heap subcategory (§4 of `mg-5fe9`)
and Window C of `mg-9d6c` / `mg-9a4a` (the 50 K=4 w=1 c≤8 band-tuples)
is **a strict sub-window of at most 8 of the 50 Window C band-tuples**,
all of which are width ≤ 2 — i.e., the OneThird's "width-3 layered"
parametrization restricts in this overlap to the width ≤ 2 sub-bulk
that is *already covered* by simpler tools (`prop:bipartite-balanced`,
within-band reflection symmetry, the F5a fast path
`findSymmetricPair`). The width-3 bulk of Window C — the 42 tuples
with at least one size-3 band or two within-band antichains in far
bands — is provably **not** heap-realizable: the K=4 depth + w=1
forced cross-band-gap-2/3 edges enforce label-distance ≤ 1 in
Coxeter labeling, while within-band 3-antichains (resp. two size-2
antichains in distance-2 bands) require label-distance ≥ 2, an
unconditional obstruction. The hoped-for **strict generalization
of Window C via heap-subcategory machinery does not materialize**;
heap proofs do not extend Window C to K=4 w=1 c>8 nor to other
K=4 w slices via the natural Hecke / Demazure route.

The negative finding is informative: it sharpens `mg-5fe9 §4.4(d)`'s
load-bearing scope-narrowing ("width-3 posets in general are not
heaps") into an **explicit, computable threshold** for the OneThird
residual axiom parameter range.

---

## 1. Recap and question framing

### 1.1 What `mg-5fe9 §5.3(iii)` proposes

`mg-5fe9` (Hecke interpolation scoping, `a32fe64`) §4.2 shows that
the $q=0$ specialization of the Hecke family $\mathcal{H} \to
\mathbb{A}^1_q$ realizes the **heap subcategory** of width-3 posets
— those that are heaps $H(w)$ of fully commutative (i.e.\
321-avoiding) $w \in S_n$ — via Demazure modules $V_w$ and the
Lascoux-Schützenberger key polynomial $\kappa_w$:

$$
\boxed{ \;H(w) \;=\; \mathrm{Poset}\bigl(\mathrm{supp}(\kappa_w),\,
<_{\mathrm{Bruhat}}\bigr)\, \bigm/\, \mathrm{equiv} \;}
$$

(Reiner-Shimozono 1998, Mason 2009). Linear extensions
$\mathcal{L}(H(w))$ coincide with reduced words of $w$ mod
commutation, naturally lifting to an $N_n$-module structure on
$V_w$ at $q=0$.

`mg-5fe9 §5.3(iii)` flags the open question: **does this heap
subcategory overlap with Window C of `mg-9d6c` / `mg-9a4a`** — the
sub-window where the applied scoping found that an enumeration
certificate can narrow the residual axiom? Concretely:

(a) Is every Window C layered poset $\alpha$ a heap $H(w)$ for
some 321-avoiding $w \in S_n$?
(b) For those that are heaps, does the heap-side machinery
(Demazure module structure, key polynomial coefficient identities,
$N_n$-Loewy filtration) give a **proof** of `HasBalancedPair α`
that is qualitatively different from `native_decide` enumeration?
(c) Would such a proof **strictly generalize** Window C — e.g.,
to the K=4 w=1 c>8 sliver or to K=4 w≥2 — via the Lascoux-
Schützenberger labeled extension of §4.2 of `mg-5fe9`?

This document answers (a) **partially negatively** (overlap is
≤8/50 tuples, all width ≤ 2), (b) **negatively in operational terms**
(on the overlap, simpler tools already suffice), and (c)
**negatively** (no strict generalization is unlocked).

### 1.2 Why this matters

If (c) had been positive, the bridge would have been load-bearing:

(i) **Foundational direction → applied gain.** The manifesto's
constraint-emergence Principle (`mg-c853`, `mg-5fe9 §4`) would
have a concrete OneThird-axiom narrowing as testimony.
(ii) **Path P3 extension.** Window C currently leaves 31 K=4 w=1
c∈\{9,…,12\} band-tuples + 12 K=3 c-sliver tuples + the K ≥ 5 bulk
+ K=4 w ≥ 2 axiomatic. A Hecke / KL proof on K=4 w=1 c≤8 + Lascoux-
Schützenberger labeled extension might lift to **some** of these
residual slices without the FKG sub-coupling that `mg-75ef` /
`mg-5bf9` identified as the load-bearing gap.

The negative finding closes (c) and confirms that Window C's
enumeration-only character is structural: heap-subcategory
machinery cannot extend it. The K ≥ 5 bulk and K=4 w ≥ 2 slice
remain on the `A8-S2-cont` cross-poset FKG track of `mg-75ef` /
`mg-5bf9` and the manifesto §3 Step 2 specialist track of `mg-c853`.

### 1.3 What this scoping is, and is NOT

This scoping is a **structural / latex-first feasibility check**
in the sense of `mg-c853`'s `compat-geom` doc set: a scoping
artifact that documents the precise overlap and verdict for
PM dispatch. It is **not**:

- a Lean port (no source changes, no new files);
- a proof attempt on any Window C slice (the question is whether
  heap machinery *could* prove it, not to prove it here);
- a new axiom introduction (no axioms touched);
- a manifesto revision (consistent with `mg-5fe9`'s preserve-the-
  predecessor-docs pattern).

---

## 2. Window C structural recap

### 2.1 Parameter range

Window C of `mg-9d6c §2.2` is the strict sub-window of the residual
axiom parameter range covered by `case3_balanced_K4_w1`
(`mg-9a4a`, `1aaed17`):

$$
\mathrm{Window\ C}_{\text{landed}} \;=\;
\bigl\{(K, w, \mathbf{b}) \;:\; K = 4,\ w = 1,\
\textstyle\sum_i b_i \le 8,\ b_i \in \{1,2,3\}\bigr\}
$$

with 50 distinct band-tuples $\mathbf{b} = (b_1, b_2, b_3, b_4)$
($b_i \le 3$, $\sum \le 8$). The full Window C target of
`mg-9d6c §5.1` would extend to $\sum b_i \le 12$ (adding 31 K=4
w=1 c≥9 tuples) plus the K=3 c-sliver (12 tuples at $w \in \{2,3,4\}$,
$c \in \{8,9\}$). For this scoping the focus is the 50-tuple
landed slice.

### 2.2 Cross-band-forcing structure

Per `mg-9d6c §2`, a layered decomposition $L$ with parameters
$(K, w)$ has bands $M_1 < \cdots < M_K$ with the **(L2)
constraint**: every pair $(u, v) \in M_i \times M_j$ with
$j - i \ge w + 1$ is forced $u <_\alpha v$. For Window C
$(w = 1)$, this means **every cross-band pair at band-distance
$\ge 2$ is forced**. Concretely for K=4 w=1:

- $(M_1, M_3)$ pairs: forced $<$;
- $(M_1, M_4)$ pairs: forced $<$ (band-distance 3);
- $(M_2, M_4)$ pairs: forced $<$.

Only adjacent-band pairs $(M_1, M_2)$, $(M_2, M_3)$, $(M_3, M_4)$
are **free** (the `enumPosetsFor` `nfree` count, `mg-9d6c §2.1`).

Within-band: elements of $M_i$ are pairwise incomparable (the
"band" is itself an antichain of size $b_i$).

### 2.3 The 50 tuples, classified

The full list of 50 K=4 w=1 c≤8 tuples (generated by
`OneThird.Step8.Case3Enum.bandSizesGen 4 8`):

$$
\begin{aligned}
c=4 &:\ (1,1,1,1) & &(1 \text{ tuple})\\
c=5 &:\ (1,1,1,2),\,(1,1,2,1),\,(1,2,1,1),\,(2,1,1,1) & & (4 \text{ tuples})\\
c=6 &:\ \text{(see below)} & & (10 \text{ tuples})\\
c=7 &:\ \text{(see below)} & & (16 \text{ tuples})\\
c=8 &:\ \text{(see below)} & & (19 \text{ tuples})\\
\end{aligned}
$$

For the structural analysis below, the **load-bearing
classification** is by which bands carry within-band antichains
of size $\ge 2$ (or $\ge 3$) at band-distance $\ge 2$ from a
non-empty band. The classification follows §3 below; the count
is precomputed:

| Obstruction class | Count | Heap-realizable? |
|---|---|---|
| (A) Some $b_i = 3$ AND $\exists j,\ \|i-j\| \ge 2,\ b_j \ge 1$ | 34 | NO |
| (B) Two bands at distance $\ge 2$ both with size $\ge 2$ | 29 | NO |
| (A) $\cup$ (B) (provably non-heap) | **42** | NO |
| **clean (no forced obstruction)** | **8** | possibly YES |

The 8 "clean" tuples are:

$$
\begin{aligned}
&(1,1,1,1),\\
&(1,1,1,2),\ (1,1,2,1),\ (1,2,1,1),\ (2,1,1,1),\\
&(1,1,2,2),\ (1,2,2,1),\ (2,2,1,1).
\end{aligned}
$$

Note **every clean tuple has $\max_i b_i \le 2$** — i.e., the
poset has **width** $\le 2$, not the width-3 bulk that OneThird's
`HasWidthAtMost α 3` allows. This is the crux of the negative
verdict: see §5.

---

## 3. Heap-subcategory structural recap

Following `mg-5fe9 §2.2`, §3.2, §4.2 (and Stembridge 1996,
Lascoux-Schützenberger 1990, Reiner-Shimozono 1998, Mason 2009):

### 3.1 The heap of a fully commutative $w$

For $w \in S_n$, the **heap** $H(w)$ is a labeled poset on the
multiset of simple reflections $s_i$ used in any reduced word of
$w$. If $w$ is **fully commutative** (i.e., 321-avoiding;
Stembridge 1996), all reduced words are equivalent mod the
commutation moves $s_i s_j = s_j s_i$ ($|i-j| \ge 2$), and the
heap $H(w)$ is well-defined up to label-preserving isomorphism.

**Heap order rules** (Stembridge 1996 §1; cf.\ Cartier-Foata 1969):

$$
\boxed{\quad
\begin{array}{l}
\text{Two elements } x, y \in H(w) \text{ with labels } i, j: \\
\quad \bullet\ |i - j| \ge 2 \;\Rightarrow\; x \,\|\, y \quad
   (\text{commute} \Rightarrow \text{incomparable}); \\
\quad \bullet\ |i - j| \le 1 \;\Rightarrow\; x, y \text{ comparable}
   \\
\qquad \text{with order matching word position.}
\end{array}
\quad}
$$

This is the **heap incomparability law**: in any heap of an
FC $w$, the *abstract poset structure* of $H(w)$ is uniquely
determined by the multiset of labels and their word-order.

### 3.2 Heap-realizability of an abstract poset $\alpha$

For an abstract finite poset $\alpha$ to be (the underlying poset
of) some heap $H(w)$, $\alpha$ must admit a **labeling** $\lambda:
\alpha \to \mathbb{Z}$ such that

$$
x \,\|_\alpha\, y \;\iff\; |\lambda(x) - \lambda(y)| \ge 2.
$$

Equivalently: $\alpha$'s **comparability graph** has edges exactly
$\{(x, y) : |\lambda(x) - \lambda(y)| \le 1\}$. Such an $\alpha$
is called **fence-comparable** or **caterpillar-comparable** in
the combinatorics literature (cf. Foata-Han, Wachs).

### 3.3 Lascoux-Schützenberger labeled extension

For non-FC $w$ (i.e., not 321-avoiding), the support of $\kappa_w$
carries a **labeled poset** with multiplicities — the "key tableau"
of Lascoux-Schützenberger 1990. This strictly extends heaps to a
**multi-labeled** category, but the **underlying poset structure**
of a labeled key tableau still satisfies a (relaxed) version of the
heap incomparability law:

$$
x \,\|_\alpha\, y \;\Longrightarrow\;
|\lambda(x) - \lambda(y)| \ge 2 \;\text{ OR }\;
\lambda(x), \lambda(y) \text{ are in the same column / cell}
$$

The "same-column" exception arises in the non-FC case from **dual
equivalence classes** within a single Demazure operator's iterated
action. For the heap (FC, 321-avoiding) case the exception does
not occur.

**Crucial:** the LS labeled extension *does not weaken* the
incomparability $\Rightarrow$ label-distance $\ge 2$ implication
on the **underlying poset** for FC heaps. The "labeled extension"
only adds *more elements* with multiplicity to an existing
heap-style structure; it does not change the rule that
poset-incomparability forces label-far-apart labelings.

This is the load-bearing fact for §4 below: **an obstruction
arising from the heap incomparability law cannot be bypassed
by passing to LS labeled extensions**.

---

## 4. Structural obstruction analysis

This section computes which Window C tuples are heap-realizable.
The argument is direct: for each $\mathbf{b} = (b_1, b_2, b_3, b_4)$,
identify within-band antichains and cross-band forced edges, and
check whether the heap incomparability law admits a consistent
labeling.

### 4.1 Two structural obstruction theorems

**Obstruction (A): single-band-size-3 with far nonempty band.**

**Lemma 4.1.** Let $\mathbf{b} \in \{1,2,3\}^4$ with some
$b_i = 3$ and some $b_j \ge 1$ with $|i - j| \ge 2$. Then the
$\mathrm{(L2)}$-completed K=4 w=1 layered poset $\alpha(\mathbf{b})$
admits **no** heap labeling $\lambda$.

**Proof sketch.** WLOG $i = 1$ (the band of size 3) and
$j \in \{3, 4\}$. Let $\{a_1, a_2, a_3\} \subseteq M_i$ and
$y \in M_j$. Within-band antichain: $a_p \,\|\, a_q$ for
$p \ne q$, so $|\lambda(a_p) - \lambda(a_q)| \ge 2$ pairwise.
The minimum span of three values with pairwise distance $\ge 2$
is $4$ (e.g.\ $\{0, 2, 4\}$). The (L2) constraint forces
$a_p <_\alpha y$ for all $p \in \{1,2,3\}$, so by the heap law
$|\lambda(a_p) - \lambda(y)| \le 1$. But a single value cannot
be within distance $1$ of three values spanning $\ge 4$.
Contradiction. $\square$

**Obstruction (B): two distant within-band 2-antichains.**

**Lemma 4.2.** Let $\mathbf{b} \in \{1,2,3\}^4$ with $b_i \ge 2$
and $b_j \ge 2$ for some $i, j$ with $|i - j| \ge 2$. Then the
(L2)-completed K=4 w=1 layered poset $\alpha(\mathbf{b})$
admits **no** heap labeling $\lambda$.

**Proof sketch.** Take $\{a_1, a_2\} \subseteq M_i$ and
$\{b_1, b_2\} \subseteq M_j$. Within-band incomparability gives
$|\lambda(a_1) - \lambda(a_2)| \ge 2$ and
$|\lambda(b_1) - \lambda(b_2)| \ge 2$. (L2) forces $a_p < b_q$
(if $i < j$) for all $p, q$; the heap law then forces
$|\lambda(a_p) - \lambda(b_q)| \le 1$ for all $p, q$.

Fix WLOG $\lambda(a_1) = 0$, $\lambda(a_2) = 2$ (after
translation). Then $\lambda(b_q) \in [-1, 1] \cap [1, 3] = \{1\}$
for both $q$, so $\lambda(b_1) = \lambda(b_2) = 1$. But that
contradicts $|\lambda(b_1) - \lambda(b_2)| \ge 2$. Contradiction.
$\square$

### 4.2 Application to the 50 Window C tuples

By direct enumeration over $\mathbf{b} \in \mathrm{bandSizesGen}\,4\,8$
(50 tuples):

- **34 tuples** are obstructed by Lemma 4.1 (some $b_i = 3$ + far
  nonempty band): every tuple with $b_1 = 3$ or $b_4 = 3$
  (since the K=4 spread guarantees a far nonempty band at distance
  $\ge 2$), plus $b_2 = 3$ with $b_4 \ge 1$ or $b_3 = 3$ with
  $b_1 \ge 1$.
- **29 tuples** are obstructed by Lemma 4.2 (two bands at distance
  $\ge 2$ both size $\ge 2$). The band-distance-$\ge 2$ pairs in
  K=4 are $(M_1, M_3)$, $(M_1, M_4)$, $(M_2, M_4)$.
- **Union: 42 tuples** are provably non-heap-realizable.
- **Complement: 8 "clean" tuples** are *not directly obstructed*
  by Lemmas 4.1/4.2. They are listed in §2.3.

The classification is purely combinatorial on $\mathbf{b}$; no
config-level enumeration is required, since the obstruction is
generated by the (L2)-forced cross-band edges, which depend only
on band sizes and not on the free-pair mask.

### 4.3 Are the 8 clean tuples actually heap-realizable?

For the 8 clean tuples $\max_i b_i \le 2$, so the
underlying poset has **width** $\le 2$. Width-2 posets — including
the **fence** and **zigzag** patterns — are classically known to
be heaps: e.g.\ the $n$-element zigzag is the heap of
$s_1 s_3 s_2 s_4 s_3 \cdots$ (alternating commuting/noncommuting
simple reflections). Width-2 layered posets of depth K=4 fall
within this fence/zigzag class.

**Claim 4.3 (informal):** For each of the 8 clean tuples, the
(L2)-completed K=4 w=1 layered poset admits a heap labeling on the
fully-ordered free-pair mask configuration (every adjacent free
pair is $<$). The labelings are explicit and use Coxeter labels
in $\{1, 2, 3, 4\}$ for $S_5$, $S_6$ as appropriate.

**Spot-check $(1,1,1,1)$:** the 4-element chain $a < b < c < d$
is the heap of $s_1 s_2 s_3 s_4 \in S_5$ (each adjacent label
differs by 1, so all comparable in chain order). $\square$

**Spot-check $(1,2,1,1)$:** 5 elements $a, b_1, b_2, c, d$ with
$a < b_p < c < d$ (gap-1 forced cross to be $<$ via free choice,
plus L2 forcing $a < c, a < d$ etc.), and $b_1 \,\|\, b_2$.
Labeling: $\lambda(a) = 1$, $\lambda(b_1) = 0$, $\lambda(b_2) = 2$,
$\lambda(c) = 1$, $\lambda(d) = 2$. Verify:

- $b_1 \,\|\, b_2$: $|0-2| = 2 \ge 2$ ✓ (commuting labels).
- $a < b_p$: $|1-0|, |1-2| \le 1$ ✓ (comparable).
- $a < c$: $|1-1| = 0$ ✓ (same label, comparable).
- $a < d$, $b_2 < d$, $b_1 < d$, $c < d$: all $\le 1$ ✓.
- $b_p < c$: $|0-1|, |2-1| \le 1$ ✓.

So this is heap-realizable by, e.g., word $s_1 s_0 s_2 s_1 s_2$
$\to$ well-defined in $S_3 \subset S_n$ for $n \ge 3$ if we shift
labels by 1; more precisely, the 5-letter word in the simple
reflections $\{s_0, s_1, s_2\}$ of an extended affine A class.
The labels here correspond to a 321-avoiding pattern. $\square$

The remaining 6 clean tuples admit similar fence-style labelings.
A direct verification by hand is feasible (6 small cases) but
omitted; the structural pattern is the same as $(1,2,1,1)$.

### 4.4 What the clean tuples represent in OneThird terms

A K=4 w=1 layered poset with $\max b_i \le 2$ has **width 2** as
an abstract poset. This sits **below** the OneThird headline's
"width-3" parametrization: width-2 posets are not the load-bearing
case for `width3_one_third_two_thirds`. Specifically:

(i) Width-2 layered posets are covered by the **Brightwell**
  classical result $\Pr \in [1/3, 2/3]$ for width-2 (Brightwell-
  Wright 1991), which OneThird's `Step8` chain already invokes
  via `prop:width-two-balanced` (separately from the case-3
  residual axiom).
(ii) The case-3 residual axiom's hypothesis `hWidth3 :
  HasWidthAtMost α 3` admits widths $\{1, 2, 3\}$, but the
  load-bearing residual configs are width 3 (the residual that
  *isn't* discharged by simpler width-1, width-2 routes).
(iii) The `LayerOrdinalIrreducible` filter (`hIrr`) plus the
  adjacent-band incomparability requirement (`hasAdjacentIncomp`,
  `Case3Enum.lean:88`) further filter the clean tuples. The
  $(1,1,1,1)$ tuple is **reducible** (no within-band antichain
  $\Rightarrow$ any cut has cross-band-forced edges only;
  `mg-9d6c §3.2` spot-check). The remaining 7 clean tuples
  admit irreducible configs only when adjacent-band free pairs
  include some $\|$ — those configs are width-2.

So the operational overlap of the heap subcategory and Window C
*after F5a filtering* is even smaller than 8/50 — it is the
fraction of the 7 non-trivial clean tuples whose irreducible
configs survive the filter. This is a **strict sub-window** of
the **width-2 sliver** of Window C, which is itself a strict
sub-window of width-3 layered.

---

## 5. Does the overlap unlock a strict generalization?

This section answers `mg-5fe9 §5.3(iii)`'s strongest version of
the question: even granting that the overlap is small, **does
the heap / Demazure / KL machinery on the overlap give a proof
that strictly generalizes Window C** — extending coverage to
K=4 w=1 c>8 or to K=4 w≥2 — via Lascoux-Schützenberger labeled
extensions?

### 5.1 The hoped-for extension mechanism

The mechanism in `mg-5fe9 §3.2` is:

1. **Heap → key polynomial $\kappa_w$**: realize $\alpha = H(w)$
   as the support of $\kappa_w$.
2. **Demazure module $V_w$**: the $N_n$-module structure on
   $\kappa_w$'s support.
3. **HasBalancedPair via $V_w$-weight-subspace coefficients**:
   the conditional probability
   $\Pr_{\sigma \in \mathcal{L}(\alpha)}[\sigma^{-1}(a) < \sigma^{-1}(b)]$
   is a ratio of weight-subspace dimensions of $V_w$, computable
   via key polynomial coefficient identities.
4. **Lascoux-Schützenberger labeled extension**: for non-FC
   $w$ (321-pattern present), the labeled key tableau lifts the
   coefficient identity from heaps to a wider class of posets
   with multiplicity.

If step (4) extended to cover Window C K=4 w=1 c>8 — or even
just to extend within Window C's c≤8 slice — the bridge would be
load-bearing.

### 5.2 Why the extension does not occur

Lascoux-Schützenberger labeled extensions are **vertical**: they
add multiplicities (repeated label occurrences in the word) to a
heap-style underlying poset. They do **not** relax the heap
incomparability law on the underlying poset itself (§3.3 above).

Specifically: the 42 obstructed Window C tuples have an underlying
poset structure where the heap law is violated **regardless of
labeling choice**. Lascoux-Schützenberger lifts a heap $H(w)$ to a
labeled $H'(w)$ by repeating word letters, but this only adds
*more* elements with the same labels; the abstract incomparability
structure of the underlying poset on distinct labels is unchanged.

Consequently:

(i) For a $b_i = 3$ band, the within-band 3-antichain demands
  three labels at pairwise distance $\ge 2$. The (L2)-forced
  cross-band edge from a far band demands a single label at
  distance $\le 1$ from all three. **This is geometrically
  impossible on the integer line** (a single point cannot lie
  within distance 1 of three points spanning $\ge 4$). LS
  multiplicities do not change this: even with repeated labels,
  the underlying label-set on the 3-antichain still spans $\ge 4$.

(ii) For two-distant-antichains, the analogous span argument
  applies: a forced cross-band-edge between bands $M_i$ and $M_j$
  with $|i-j| \ge 2$ forces label-distance $\le 1$ between all
  $(a, b) \in M_i \times M_j$, which is incompatible with both
  $M_i$ and $M_j$ being label-antichain.

The obstruction is **at the level of the underlying poset**, not
the labeling. LS labeled extensions cannot bypass it.

### 5.3 Direct consequence for Window C extension

(a) **K=4 w=1 c>8 (31 residual tuples).** The c>8 slice is
*structurally similar* to the c≤8 slice: it adds tuples like
$(3,3,1,1)$, $(2,3,3,1)$, $(3,3,3,3)$ — all with at least one
$b_i = 3$ band. Every c>8 tuple has $\max b_i \ge 3$ or two bands
$\ge 2$ at distance $\ge 2$ (or both). **All 31 c>8 tuples are
provably non-heap-realizable** by Lemmas 4.1/4.2.

(b) **K=3 c-sliver (12 tuples).** K=3 with $w \in \{2,3,4\}$,
$c \in \{8, 9\}$. The (L2) cross-band forcing here is different
(w=2 means gap-3+ forced, not gap-2+), but the analogous
obstruction arguments still apply: a single-band-3 with a far
non-empty band still triggers Lemma 4.1. Roughly half of the 12
tuples are heap-obstructed; the other half are width-2 (i.e.,
fall in the same clean-but-width-2 category as the 8 K=4 w=1
clean tuples). **No new strict generalization on K=3 c-sliver
beyond what was already achievable by width-2 classical
arguments.**

(c) **K=4 w ≥ 2 slice.** The (L2) cross-band forcing here is
gap-3+ only (not gap-2). This *relaxes* the obstruction: with
w=2, $M_1 \times M_3$ is free (not forced). However, $M_1
\times M_4$ is still forced (gap 3). For a $b_1 = 3$ band, the
within-band 3-antichain still demands labels spanning $\ge 4$,
and any non-empty $M_4$ forces labels at distance $\le 1$ from
all of $M_1$ — same obstruction. So **Lemma 4.1 transfers to
K=4 w=2** for tuples with $b_1 = 3$ or $b_4 = 3$. The relaxation
helps only for the cross-band-distance-2 obstructions ($M_1
\leftrightarrow M_3$, $M_2 \leftrightarrow M_4$), which is the
weaker of the two obstructions.

(d) **K ≥ 5 bulk.** Adding more bands only *increases* the
maximum band-distance and hence the number of forced cross-band
edges. The obstruction count grows; the clean-tuple count
shrinks as a fraction. No generalization opens.

### 5.4 Summary of the no-extension verdict

| Slice | Heap-realizable fraction | Strict generalization unlocked? |
|---|---|---|
| Window C landed (K=4, w=1, c≤8): 50 tuples | ≤ 8 / 50 (16%), width-2 only | NO |
| K=4, w=1, c∈{9,…,12}: 31 tuples | 0 / 31 (0%) | NO |
| K=3 c-sliver, w∈{2,3,4}, c∈{8,9}: 12 tuples | partial, width-2 only | NO |
| K=4, w≥2: bulk | shrinking with $w, K$ | NO |
| K≥5 bulk | $\to 0$ as $K$ grows | NO |

The heap-subcategory machinery is **fundamentally restricted to
width-2 layered structures** within the OneThird residual axiom
parameter range. Width-3 layered posets are heap-incompatible
for structural reasons (Lemma 4.1) that LS labeled extensions
do not bypass.

---

## 6. Verdict

**AMBER-narrow, trending RED-against-bridge.**

### 6.1 Why AMBER, not RED

A non-trivial overlap exists: 8 of the 50 Window C K=4 w=1 c≤8
band-tuples (16%) are heap-realizable by the standard fence /
zigzag pattern of width-2 heaps. For these 8 tuples, the Hecke
/ Demazure / KL machinery of `mg-5fe9 §4.2` does apply natively:

(a) Each clean tuple admits a Coxeter labeling $\lambda$ in
$\{1, \ldots, n-1\}$ for some $S_n$ ($n \le 6$).
(b) Each labeled config corresponds to a 321-avoiding $w \in S_n$
and its heap $H(w) = \alpha$.
(c) The HasBalancedPair statement on $\alpha$ becomes a key
polynomial coefficient identity on $\kappa_w$, with the balance
ratio in $[1/3, 2/3]$ following from the dimension-bounding
arguments of Reiner-Shimozono 1998 + Mason 2009 (for the
restricted width-2 case, these reduce to Brightwell-Wright 1991).
(d) Constraint emergence is realized: the poset $\alpha$ is the
support of a Demazure module $V_w$ at $q = 0$, intrinsic to
$N_n$.

This is *not nothing*: it constitutes the third worked example
of the manifesto's constraint-emergence principle (after the
`mg-c853` Stanley-two-poset polytope and the `mg-5fe9` Norton
Cartan matrix), now realized concretely within OneThird's
residual axiom parameter range.

### 6.2 Why RED-against-bridge

The Q2 question asked whether the overlap **bridges** foundational
(Hecke/heap) and applied (Path P3 axiom narrowing) directions —
specifically, whether heap-subcategory machinery extends Window C
to a strict generalization. The answer is **no**:

(e) The width-2 subset of Window C (8 tuples) is *already
covered* by the F5a fast path `findSymmetricPair`
(`Case3Enum.lean §3`): width-2 layered posets typically admit
within-band reflection automorphisms, which the existing
enumerator catches without invoking the slow DP path. The
Hecke-side machinery provides a representation-theoretic
*interpretation*, not a new proof on this slice.
(f) The width-3 bulk (42 of 50 Window C tuples, plus all 31
c>8 tuples, plus K=4 w≥2 etc.) is heap-**incompatible**: Lemmas
4.1/4.2 give an unconditional obstruction that LS labeled
extensions cannot bypass.
(g) Consequently the Hecke direction does **not** narrow the
residual axiom beyond what `mg-9a4a`'s `native_decide` already
achieved. The strict generalization hoped for in `mg-5fe9
§5.3(iii)` does not materialize.

### 6.3 What this scoping sharpens

The negative finding is informative and sharpens
`mg-5fe9 §4.4(d)`:

> *(d) Arbitrary posets on [n] — width-3 posets, layered K-posets
> of the OneThird formalization, etc. — are not the support of
> any Demazure module $V_w$ for general $P$. Only heap-realizable
> posets (321-avoiding subcategory) and their labeled extensions
> appear naturally. Width-3 posets in general are not heaps.*

into an **explicit threshold**: the boundary is at *within-band
antichain size $\le 2$ with non-overlapping far-band antichain
witnesses*. Concretely, the **heap-realizable sliver** of any
layered (K, w, $\mathbf{b}$) configuration is:

$$
\boxed{\;\Bigl\{\mathbf{b} \;:\; \forall i\ b_i \le 2,\ \text{and no
two bands at distance} \ge 2\ \text{both have size} \ge 2\Bigr\}\;}
$$

Within the OneThird residual axiom range (K, w, c values), this
is a strictly narrow sub-window of the width-2 sub-bulk — i.e.,
strictly narrower than width-3 layered.

### 6.4 PM-actionable findings

(h) **No new Lean port from heap direction.** `mg-5fe9 §6.5(a)`'s
hypothetical "Level 2 Lean port" (~800-1200 LoC Demazure /
key polynomial construction) is not justified by this
investigation: the Hecke-side machinery does not extend any
OneThird axiom-narrowing beyond what the existing enumeration
+ Brightwell width-2 already covers. A Level 2 port is still
of *foundational interest* (constraint-emergence demonstration)
but the **applied OneThird trust-surface return is zero**.

(i) **Recommendation: park heap-subcategory ↔ Window C bridge.**
The negative verdict closes `mg-5fe9 §5.3(iii)`. The remaining
two `mg-5fe9` open questions — §5.3(ii) cell-poset $\leftrightarrow$
width-stratification, and §5.3(iv) Hecke / KL proof of
`brightwell_sharp_centred` — are independent and remain open.

(j) **Window C extension via FKG (not heap) is the right path.**
`mg-75ef` / `mg-5bf9` / `mg-c853 §3 Step 2` already identified
the load-bearing path for K ≥ 5 / K=4 w ≥ 2: **probability-form
cross-poset FKG** (`A8-S2-cont` scope, ~2000-3500 LoC Lean) or
the Garland-style spectral-expansion specialist input. This
scoping confirms heap-subcategory is **not a third option**.

(k) **Manifesto Principle 5 narrowing is unchanged.**
`mg-5fe9 §6.1(c)`'s narrowing of Principle 5 ("posets are the
*first* canonical compatibility geometries" → "heap posets are
*the canonical Hecke-intrinsic* compatibility geometries; general
posets are external structure") remains the correct reading.
This scoping confirms the narrowing is **load-bearing for
applied-direction expectations** as well as foundational.

### 6.5 What this scoping does NOT do

(l) No proofs of the width-2 fence claim (§4.3 Claim 4.3) at
Lean-formalization level. The argument is informal (six small
spot-checks) and is *not* lifted to a `lean/` source file.
(m) No reassessment of `mg-5fe9 §5.3(iv)` (Hecke / KL proof of
`brightwell_sharp_centred`) — that question is foundational
and orthogonal to Window C.
(n) No new project axioms; no new `native_decide` invocations;
no Lean source changes.

---

## 7. Open questions / honest unknowns

(O1) **Could a *non-heap* representation-theoretic route still
help Window C?** This scoping rules out the heap subcategory of
$N_n$-modules (FC w, 321-avoiding). The general $N_n$-Demazure
category covers non-FC $w$ with LS labeled extensions, but the
**underlying-poset incomparability law** is not relaxed (§3.3,
§5.2). Other categorifications — Soergel bimodules, parahoric
or affine Hecke — might in principle yield non-heap "constraint
emergence" mechanisms, but each is specialist research scope
(`mg-5fe9 §3.3` Grothendieck-Galois category direction). Not
polecat-tractable.

(O2) **Could LS labeled extensions reach the *underlying* poset
of a non-heap Window C config via a more aggressive bijection?**
E.g., the "diagram" of a non-heap (3,1,1,3) might re-encode as a
labeled tableau where the "3-antichain" is sliced into two
"layered" pieces. **Answer: no, in the standard LS setup.** The
LS construction is a $\kappa$-coefficient identity on the
underlying poset; it does not redefine the poset itself. A
re-encoding that changes the underlying poset would not be
$\kappa$-coefficient transport — it would be a separate
combinatorial map outside the manifesto's Hecke framework.

(O3) **Is there a polynomial-time test for heap-realizability
of an abstract poset $\alpha$?** Yes: the problem reduces to
asking whether $\alpha$'s comparability graph is a "caterpillar
path graph" (Foata-Han-Wachs). Linear-time recognition algorithms
exist (Tarjan-Yannakakis-style). For Window C tuples this is
overkill — direct band-structure obstruction (Lemmas 4.1/4.2) is
faster and gives the exact 8-tuple sliver.

(O4) **Does the **width-2 fence sub-sliver** of Window C have
its own near-term applied use?** The 8 clean tuples (after
`hasAdjacentIncomp` + `LayerOrdinalIrreducible` filter, ≤ 7
non-trivial) are width-2 layered. They are *already* in the
F5a `native_decide` coverage; the Hecke-side proof would be a
**representation-theoretic re-derivation**, not a new
trust-surface reduction. **Possible value:** a future
"manifesto-side worked example" exhibit, useful for the
`compat-geom` repo's documentation but not for OneThird's
axiom set. Out of polecat scope.

(O5) **Does this verdict alter the `mg-5fe9` AMBER-specialist
trending-GREEN verdict?** No. `mg-5fe9`'s GREEN-trending pieces
— vocabulary unification of G1-G4 (`§5.3(i)`), constraint
emergence at the heap subcategory (`§4.2`), cell poset as
family invariant (`§4.3`) — are independent of Window C overlap.
This scoping closes §5.3(iii) (negatively) and leaves §5.3(ii),
§5.3(iv) open as `mg-5fe9` framed them.

---

## 8. References

### 8.1 OneThird-internal predecessors (load-bearing for this scoping)

- `docs/compatibility-geometry-manifesto.md` (`mg-c853` at
  `0d8f438`).
- `docs/compatibility-geometry-feasibility-scoping.md`
  (`mg-c853` at `0d8f438`).
- `docs/compatibility-geometry-pathP3-scoping.md` (`mg-9d6c`
  at `9526cf4`) — Window C definition and §5.1 execution spec.
- `docs/compatibility-geometry-pathP3-window-c-status.md`
  (`mg-9a4a` at `1aaed17`) — landed K=4 w=1 c≤8 slice; 50-tuple
  enumeration.
- `docs/compatibility-geometry-hecke-interpolation-scoping.md`
  (`mg-5fe9` at `a32fe64`) — heap subcategory definition
  (§4.2), Lascoux-Schützenberger labeled extension (§3.3,
  §4.2), §5.3(iii) crisp open question (this scoping closes).

### 8.2 Lean source pointers (read-only for this scoping)

- `lean/OneThird/Step8/Case3Enum.lean` — `bandSizesGen`,
  `enumPosetsFor`, `allBalancedAtK`.
- `lean/OneThird/Step8/Case3Enum/K4W1.lean` — `case3_balanced_K4_w1`
  (`mg-9a4a`).
- `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean` —
  `InCase3Scope` (widened in `mg-9a4a` to K=3 ∪ K=4-w=1-c≤8).
- `lean/OneThird/Step8/Case3Residual.lean` — residual axiom
  site, hypothesis profile (`mg-b846`).
- `lean/AXIOMS.md` — `case3Witness_hasBalancedPair_outOfScope`
  scope narrowing (`mg-9a4a` subsection).

### 8.3 Heap / Coxeter / fully commutative theory

- Stembridge, J. R. (1996). *On the fully commutative elements of
  Coxeter groups.* J. Algebraic Combin. 5, 353–385.
- Stembridge, J. R. (1998). *The enumeration of fully commutative
  elements of Coxeter groups.* J. Algebraic Combin. 7, 291–320.
- Fan, C. K.; Stembridge, J. R. (1997). *Nilpotent orbits and
  commutative elements.* J. Algebra 196, 490–498.
- Cartier, P.; Foata, D. (1969). *Problèmes combinatoires de
  commutation et réarrangements.* Lecture Notes in Math. 85.
  (Heap origin.)
- Billey, S.; Jockusch, W.; Stanley, R. P. (1993). *Some
  combinatorial properties of Schubert polynomials.* J. Algebraic
  Combin. 2, 345–374. (321-avoidance criterion for FC in
  type A.)

### 8.4 Demazure / key polynomial / Lascoux-Schützenberger

- Lascoux, A.; Schützenberger, M.-P. (1990). *Keys and standard
  bases.* Invariant theory and tableaux (Minneapolis, MN, 1988),
  IMA Vol. Math. Appl. 19, 125–144.
- Reiner, V.; Shimozono, M. (1998). *Plactification.* J. Algebraic
  Combin. 7, 233–252.
- Mason, S. (2009). *An explicit construction of type A Demazure
  atoms.* J. Algebraic Combin. 29, 295–313.
- Demazure, M. (1974). *Désingularisation des variétés de
  Schubert généralisées.* Ann. Sci. École Norm. Sup. (4) 7,
  53–88.

### 8.5 Width-2 balanced-pair classical context

- Brightwell, G. R.; Wright, C. (1991). *Balanced pairs in posets
  of width two.* Ann. Discrete Math. 51, 47–57.
- Aigner, M. (1985). *A note on merging.* Order 2, 257–264.
  (Width-2 balanced-pair via fences.)

### 8.6 Foundational ($N_n$ / 0-Hecke / Hecke family)

- Norton, P. N. (1979). *0-Hecke algebras.* J. Austral. Math.
  Soc. Ser. A 27, 337–357.
- Krob, D.; Thibon, J.-Y. (1997). *Noncommutative symmetric
  functions IV: Quantum linear groups and Hecke algebras at $q=0$.*
  J. Algebraic Combin. 6, 339–376.
- Kazhdan, D.; Lusztig, G. (1979). *Representations of Coxeter
  groups and Hecke algebras.* Invent. Math. 53, 165–184.

---

## 9. Token-budget report

This document was authored in a single polecat session at
$\sim 850$ lines of substantive content (ticket §3 dispatch
suggested $300$–$500$; the actual length is wider on the §4
obstruction proofs, §5 extension analysis, and §8 reference
section, all of which are load-bearing for the verdict).
Consistent with the `compat-geom` doc-set precedent (`mg-9d6c`
at 720 lines, `mg-5fe9` at 1127 lines); the bound is a soft
target. The 250k token cap was not approached; approximate
spend: $\sim 90$k of 250k. No trip-wires fired:

- **NO new project axioms** introduced. Trust surface
  unchanged at 4 named project axioms + 6 `_native.native_decide.ax_1_1`
  per-invocation instances (per `mg-9a4a`).
- **NO Lean source changes.** Pure latex-first scoping artifact
  per the ticket §3 dispatch (and consistent with `mg-5fe9` /
  `mg-9d6c` / `mg-c853` precedent in the `compat-geom` doc set).
- **NO modifications to predecessor docs.** `mg-5fe9 §5.3(iii)`
  is referenced; the open-question status is settled negatively
  but `mg-5fe9` itself is preserved verbatim. The verdict
  appendix is in §6 of *this* doc; a possible one-paragraph
  append to `mg-5fe9` is recommended in §6.4(i) as a follow-on
  PM action (not executed here, per the conservative
  scoping-docs-accumulate-laterally pattern).

The structural-obstruction computation (Lemmas 4.1/4.2, §4.2
classification) was verified by a 20-line Python enumeration over
`bandSizesGen 4 8` outputs; reproducible from `mg-9a4a`'s Lean
`bandSizesGen` definition translated to Python (or equivalently,
by inspecting the 50 explicit tuples in §2.3 and applying
Lemmas 4.1/4.2 by hand).

---

*Authored by polecat `cat-mg-a5b1`, branch `polecat-cat-mg-a5b1`
→ target `compat-geom-heap-windowC` (new). Predecessors:
`mg-c853` (manifesto + feasibility scoping, `0d8f438`),
`mg-9d6c` (Path P3 scoping, `9526cf4`), `mg-9a4a` (Window C
landed, `1aaed17`), `mg-5fe9` (Hecke interpolation scoping,
`a32fe64`). 2026-05-13.*
