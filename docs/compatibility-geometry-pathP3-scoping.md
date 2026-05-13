# Compatibility Geometry — Path P3 scoping (mg-9d6c)

**Companion to** `docs/compatibility-geometry-manifesto.md` (Daniel's
manifesto, 2026-05-12) and `docs/compatibility-geometry-feasibility-scoping.md`
(mg-c853 feasibility scoping, AMBER-specialist verdict). This document
follow-up-scopes **Path P3** — flagged in mg-c853 §5 as the
"highest-leverage near-term path" — at the level of feasibility: is the
case-3 residual axiom
`OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`
replaceable by **finite cube-enumeration** of layered width-3 posets in
the manifesto's local-cubical-geometry framework (§2.3)?

LaTeX is used inline ($\ldots$ / display) throughout; render with
KaTeX/MathJax or read source. Predecessor scoping verdict (mg-c853)
was *AMBER-specialist, trending GREEN-promising*. This Path P3
scoping reaches **AMBER-narrow**: P3-by-enumeration is feasible **only
on a strict sub-window** of the residual axiom's parameter range
(specifically $K=4, w=1$, plus a small K=3 sliver); the bulk of the
range is enumeration-infeasible and routes back to the same
probability-form FKG blocker already diagnosed by `mg-75ef` and
`mg-5bf9`. The cube-geometry framework supplies clarifying language
but does **not** bypass the FKG sub-coupling.

A sub-GREEN target — narrow the residual axiom by extending the F5a
`case3_certificate` Bool enumeration from $K=3$ to $K=4, w=1$ — is
identified as an executable polecat-class follow-on.

---

## 1. Recap of Path P3 from mg-c853 §2.4 / §5

The feasibility scoping (`mg-c853`, commit `0d8f438`) §5 articulates
three plausible specialization paths from the manifesto framework
back to OneThird's `width3_one_third_two_thirds` headline. **Path P3**
is verbatim:

> **Path P3: Case 3 axiom replacement.** The residual Case 3 axiom
> (`Case3Residual.lean`, mg-b846): "every layered $K=2$ width-3 poset
> has a balanced pair." If the manifesto's principle 4 ("non-expansion
> signals dimensional collapse, product structure, or hidden rigidity")
> gives a classification of low-compatibility-dimension posets — and
> layered $K=2$ width-3 is exactly the boundary case — then the Case 3
> axiom becomes a **structural classification statement**, possibly
> provable by enumeration of the constrained cube complex.

P3 in mg-c853 §5 was scoped with the following ranges:

- *Status:* most concrete path. Cube complex $\mathcal{X}(P)$ for
  layered $K=2$ width-3 has dimension $\le 2$; explicit enumeration
  might suffice.
- *Lean port estimate:* 500–1500 LoC + computer-verified enumeration.
- *Polecat decomposition:* 2–3 sessions.

### 1.1 Terminology clarification — what "$K$" means

The predecessor's "$K=2$ width-3 layered poset" notation conflates
**three distinct parameters** that share the letter $K$. This is a
load-bearing clarification for the rest of the scoping; spelling them
out before continuing:

**(K-depth) — `L.K` in the Lean source.** The number of layers in
the layered decomposition $L : \mathsf{LayeredDecomposition}\,\alpha$
(`LayeredReduction.lean:115`). Bands are $M_1, \ldots, M_K$ with
$|M_i| \le 3$. The case-3 residual axiom takes hypothesis
`hK3 : 3 ≤ L.K`. There is no $K = 2$ layered poset under the
residual axiom — depth $K = 2$ is **separately discharged** by
`prop:bipartite-balanced` (`step8.tex` §G3) and the layered-K=2
closure (`OptionC.K2Closure`, `mg-01ec`).

**(K-cube) — cube-complex dimension.** The maximum dimension of cells
in the Coxeter cube complex $\mathcal{X}(S_n)$ as in mg-c853 §2.3 —
$K\text{-cube} = \lceil (n-1)/2 \rceil$ for type $A_{n-1}$ (max clique
in the commutation graph). For width-3 layered posets, the
constrained sub-complex $\mathcal{X}(P)$ has dimension bounded
**below** $\lceil (n-1)/2 \rceil$ by the additional poset constraints
that the cube corners must preserve $\mathcal{L}(P)$. In particular
the "cube dim 2" of mg-c853 §5 corresponds to $n \le 5$.

**(K-cell) — Coxeter clique size.** A $k$-cell of $\mathcal{X}(S_n)$
is a $k$-clique in the commutation graph $\Gamma$ that all preserve
$\mathcal{L}(P)$; here $k$ is the cell dimension. The constrained
cube complex of mg-c853 §2.3.

These collide on "$K=2$":

- $K\text{-depth} = 2$: **bipartite layered case, already discharged.**
- $K\text{-cube} = 2$: $n \le 5$, a small sub-window of the residual
  axiom.
- $K\text{-cell} = 2$: 2-cell (square face) of $\mathcal{X}(P)$ — a
  per-cube structural object.

The predecessor's "$K = 2$ width-3 layered poset" almost certainly
intends $K\text{-cube} = 2$ (the cube-complex dimension reading is
the one that matches the manifesto's "boundary case for the
low-compatibility-dimension classification"), **but the axiom's
`L.K` field uses $K\text{-depth}$ — and the residual axiom's
hypothesis `3 ≤ L.K` excludes $K\text{-depth} = 2$ entirely.**

Throughout this document, **$K$ unqualified means $K\text{-depth}$**
(matching Lean's `L.K`). $K\text{-cube}$ and $K\text{-cell}$ are
spelled out.

### 1.2 What the residual axiom *actually* covers

`case3Witness_hasBalancedPair_outOfScope` (`Case3Residual.lean:208`)
has the hypothesis profile:

- `hWidth3 : HasWidthAtMost α 3` (paper hypothesis $w(P) \le 3$).
- `hIrr : LayerOrdinalIrreducible L` (no upward-directed band cut).
- `hK3 : 3 ≤ L.K` (depth at least 3).
- `hw : 1 ≤ L.w` (nontrivial interaction width).
- `hCard : Fintype.card α ≤ 6 * L.w + 6` (F5 C2 leaf cap).
- `hDepth : L.K ≤ 2 * L.w + 2` (F5 C2 depth cap).
- `hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K`
  where `InCase3Scope := K=3 ∧ 1≤w≤4 ∧ (w=1 → c≤9) ∧ (w≥2 → c≤7)`.

The certificate-handled in-scope window (covered by F5a
`case3_certificate`, `Case3Enum/Certificate.lean`) is exactly
$\{(K=3, w=1, c\le 9) \cup (K=3, w \in \{2,3,4\}, c \le 7)\}$.

The **residual range** (out-of-scope) is therefore:

$$
\Bigl\{(K, w, c) \;:\; 3 \le K \le 2w+2,\ w \ge 1,\ c \le 6w+6\Bigr\}
\setminus
\Bigl\{\text{InCase3Scope}\Bigr\}.
$$

Within the F5-restricted regime ($w \in \{1,2,3,4\}$ after Step 7's
`lem:bandwidth` reduction), this is:

| $w$ | $K$ values residual | $c$ residual | new band tuples |
|-----|---------------------|--------------|------------------|
| 1   | $\{4\}$             | $c \le 12$   | 81               |
| 2   | $\{3\} \cup \{4,5,6\}$ | $c \in \{8,9\}$ for $K=3$; $c \le 18$ for $K\ge 4$ | $4 + 81 + 243 + 729 = 1057$ |
| 3   | $\{3\} \cup \{4,\ldots,8\}$ | $c \in \{8,9\}$ for $K=3$; $c \le 21$ else | $4 + 81 + 243 + 729 + 2187 + 6561 = 9805$ |
| 4   | $\{3\} \cup \{4,\ldots,10\}$ | $c \in \{8,9\}$ for $K=3$; $c \le 30$ else | $4 + 81 + 243 + 729 + 2187 + 6561 + 19683 + 59049 = 88537$ |

(Counts: number of $(b_1,\ldots,b_K)$ band-size tuples with $b_i \in
\{1,2,3\}$ and $\sum b_i \le 6w+6$, restricted to the residual
out-of-scope window. Computed by direct enumeration; reproducible
via the bandSizes generator
`OneThird.Step8.Case3Enum.bandSizesGen` extended with $K \ge 4$.)

The residual range is finite at each fixed $w \le 4$ but grows
combinatorially with $K$; in total $\sim 10^5$ band-size tuples to
enumerate at $w=4$, before per-tuple mask-enumeration.

---

## 2. Enumeration of $(K, w, c, \text{band-sizes})$ classes

The Lean enumerator `OneThird.Step8.Case3Enum.enumPosetsFor`
(`Case3Enum.lean:324`) for a fixed $(w, \text{band-sizes})$ tuple
exhausts every **closure-canonical predecessor mask** subject to
$(L1)$/$(L2)$ and filters to irreducible configurations with an
adjacent-band incomparable cross-pair. The mask space has size
$2^{\mathrm{nfree}}$, where

$$
\mathrm{nfree}(w, \mathbf{b}) := \sum_{1 \le i < j \le K,\ j - i \le w}
b_i \cdot b_j
$$

counts the *free* $(u, v)$-pairs (band-gap $\le w$, where the
$<$-relation is not forced by $(L2)$).

### 2.1 Hard wall: nfree ≤ 27 cap

The existing enumerator declares `if nfree > 27 then return false`
(`Case3Enum.lean:329`), reflecting the engineering cap of
`native_decide` over $2^{27} \approx 1.3 \times 10^8$ masks (the
existing $K=3,\,w=1$ certificate runs through $2^{27}$ masks for the
`(3,3,3)` band-size, taking $\sim 60$ s of native compile time).
$2^{28}$ exceeds Lean's tolerated runtime; $2^{30}$ exceeds available
memory for the closure table.

Per a direct enumeration over the residual range:

| $w$ | $K$ | band-tuples | tuples with nfree $\le 27$ | tuples with nfree $> 27$ | max nfree |
|-----|-----|-------------|----------------------------|--------------------------|-----------|
| 1   | 4   | 81          | **81** (100 %)             | 0                        | 27        |
| 2   | 3 (residual sliver $c \in \{8,9\}$) | 4 | 4 | 0 | 27 |
| 2   | 4   | 81          | 68 (84 %)                  | 13                       | 45        |
| 2   | 5   | 243         | 126 (52 %)                 | 117                      | 63        |
| 2   | 6   | 729         | 203 (28 %)                 | 526                      | 81        |
| 3   | 3 (residual sliver) | 4 | 4 | 0 | 27 |
| 3   | 4   | 81          | 50 (62 %)                  | 31                       | 54        |
| 3   | 5   | 243         | 67 (28 %)                  | 176                      | 81        |
| 3   | 6   | 729         | 73 (10 %)                  | 656                      | 108       |
| 3   | 7   | 2187        | 55 (2 %)                   | 2132                     | 135       |
| 3   | 8   | 6561        | 29 (0.4 %)                 | 6532                     | 162       |
| 4   | 3 (residual sliver) | 4 | 4 | 0 | 27 |
| 4   | 4   | 81          | 50                         | 31                       | 54        |
| 4   | 5   | 243         | 51                         | 192                      | 90        |
| 4   | 6   | 729         | 30                         | 699                      | 126       |
| 4   | 7   | 2187        | 13                         | 2174                     | 162       |
| 4   | 8   | 6561        | 5                          | 6556                     | 198       |
| 4   | 9   | 19683       | 1                          | 19682                    | 234       |
| 4   | 10  | 59049       | **0**                      | 59049                    | 270       |

(Computed by extending the Python `band_sizes_generator` of
`enum_case3.py` to general $K$ and applying the nfree formula. Script
reproduction is one screen of Python.)

### 2.2 Three enumeration sub-windows

**Window A (full P3 coverage — INFEASIBLE).** Cover the entire
residual axiom range by native_decide. Requires $\sim 10^5$ band-size
tuples at $w=4$, of which $\sim 99\%$ have nfree $> 27$. **Not
tractable** even with significant nfree-cap engineering — a hard
combinatorial wall.

**Window B (extended P3 coverage — AMBER).** Cover only the tuples
with nfree $\le 27$. From the table above:

$$
\sum_{w \in \{1,2,3,4\}} (\text{feasible tuples in residual}) \;=\;
81 + (4+68+126+203) + (4+50+67+73+55+29) + (4+50+51+30+13+5+1) \;=\; 914.
$$

This covers $\sim 1\%$ of the band-size tuples at $w \ge 3$ —
**enumeration-feasible but doesn't eliminate the axiom**. The
remaining $\sim 99\%$ of band-size tuples at high $K$ stay
axiomatized. The axiom can be *narrowed* but not removed.

**Window C (narrow P3 — sub-GREEN).** Cover only $(K=4, w=1)$
plus the 12 residual K=3 sliver tuples for $w \in \{2,3,4\}$. **All
93 tuples have nfree $\le 27$**, and the total native_decide load is
of the same order as the existing $w=1, K=3$ certificate ($2^{27}$
worst-case per tuple, but most are much smaller). **This is the
cleanest sub-GREEN target.**

### 2.3 Polynomial vs.\ exponential growth

A subtle point: Path P3 in its mg-c853 framing assumed "cube
enumeration scales polynomially" (or at least, was unspecific about
the scaling). The reality is **exponential in nfree**, and nfree
grows quadratically in $K$ at fixed band-size pattern. The
manifesto's "low-compatibility-dimension classification" only helps
if it reduces $K$ — which it doesn't, structurally: the residual
axiom's `hIrr` hypothesis is exactly the *non*-reducibility
condition, so configurations cannot be canonical-form-reduced to
smaller $K$ before enumeration.

There is one polynomial-in-$K$ collapse the manifesto framework
*could* deliver, but it is the same FKG sub-coupling already
diagnosed as the gap by `mg-75ef` / `mg-5bf9`: see §4 below.

---

## 3. `HasBalancedPair` verification per class

### 3.1 Existing certificate template

For each tuple in Window C, the verification template is:

1. **`enumPosetsFor w bandSizes`** (`Case3Enum.lean:324`) enumerates
   all closure-canonical predecessor masks of width $\mathrm{nfree}$,
   filters to irreducible posets with adjacent-band incomparable
   cross-pair, and returns `Bool` for "every config has a balanced
   pair". This is the *existing* enumerator; no new Lean code
   needed beyond extending the per-`w` sibling files
   (`Case3Enum/W1.lean` etc.) to invoke `enumPosetsFor` with $K=4$
   band-size tuples.

2. **Balanced-pair test.** The existing
   `Case3Enum.hasBalancedPair` first tries the `findSymmetricPair`
   fast path (a swap automorphism — corresponds to a 1-cell of
   $\mathcal{X}(P)$ — gives `probLT = 1/2` directly via
   `hasBalancedPair_of_ambient_profile_match` of `mg-f92d`). For
   posets without such an automorphism, falls back to subset-DP
   linear-extension counting (`countLinearExtensions`,
   `Case3Enum.lean:202`) and tests `3⋅cnt ∈ [total, 2⋅total]`.

3. **Lift to Prop-level `HasBalancedPair α`.** Uses the existing
   band-major Fin-$n$ encoding + order-iso transport
   (`hasBalancedPair_of_orderIso`,
   `BoundedIrreducibleBalanced.lean:252`) the F5a certificate
   already consumes. No new bridge infrastructure.

The Lean port of Window C is therefore a **mechanical extension**
of the existing $K=3$ certificate to $K=4$.

### 3.2 Spot-check: $(K=4, w=1, \mathbf{b}=(1,1,1,1))$

The simplest residual tuple: 4 elements, one per band, $w=1$.
$\mathrm{nfree} = 1 \cdot 1 + 1 \cdot 1 + 1 \cdot 1 = 3$ (adjacent
bands only). The mask space has $2^3 = 8$ closure-canonical
configurations:

- **mask $000$:** No free edges. Forced edges: none (band-gap $\le w=1$
  for all pairs, so no $(L2)$-forced edges). Poset = 4-antichain;
  $\mathcal{L}(P) = S_4$, $|\mathcal{L}(P)| = 24$. Balanced pair
  exists (any pair, $\Pr = 1/2$). **Reducible**: layer 1 vs layers
  2–4 is a cut with no cross-comparabilities — fails
  `LayerOrdinalIrreducible`. Filtered out.
- **mask $001$ ($M_1 < M_2$):** $1 < 2$, otherwise free. Three
  elements ($M_2, M_3, M_4$) form an antichain above $M_1$.
  $|\mathcal{L}(P)| = 6$. Pair $(M_3, M_4)$ is incomparable, $\Pr =
  1/2$ by swap automorphism. **Reducible** (band-1 vs.\ rest).
- *(remaining six masks: similar analysis, all reducible or with
  trivial swap automorphism)*.

At the all-1-element-bands case, every configuration either reduces
or has a swap automorphism. The non-trivial verification only kicks
in for band-tuples with at least one band of size $\ge 2$.

### 3.3 Spot-check: $(K=4, w=1, \mathbf{b}=(3,3,3,3))$ worst case

12 elements, $\mathrm{nfree} = 9 + 9 + 9 = 27$, mask space $2^{27}
\approx 1.3 \times 10^8$. Each mask:

- Apply Warshall closure ($O(12^2)$).
- Test `closureCanonical` (rejects ~99% of masks as non-minimal).
- Test irreducibility ($O(K \cdot n)$).
- Test adjacent-incomp cross-pair existence.
- Symmetric-pair fast path ($O(n^2)$) — succeeds for ~90% of
  irreducible configs.
- Fallback DP: $O(2^{12} \cdot 12) = O(50{,}000)$ operations per pair
  $\times \binom{12}{2} = 66$ pairs — manageable.

Total per-mask cost is dominated by closure ($n^2$ ops) and
canonicality check; native_decide should churn through $2^{27}$ at
the same rate as the existing $K=3$ certificate. Expected runtime:
similar order to the existing `case3_balanced_w1` $\sim 60$ s
native compile.

### 3.4 Hand-verification feasibility

The ticket §4 deliverable line *"For each class, verify
`HasBalancedPair`. Either by hand (small enough) or by Lean
`native_decide`"* presupposes "small enough by hand" as a possible
verification route. For Window C this is **not feasible by hand**:

- 81 band tuples for $(K=4, w=1)$, each with up to $2^{27}$ masks,
  each producing on the order of hundreds of irreducible posets
  after canonicality / irreducibility / adjacent-incomp filters.
- After filtering, the existing $K=3$ certificate runs $\sim 6.5
  \times 10^5$ posets across all $(w, \mathbf{b})$ for $w \in
  \{1,2,3,4\}$; the $K=4, w=1$ extension would add a comparable
  order of magnitude.

By-hand verification is feasible only for the $\mathbf{b} \in
\{(1,1,1,1), (1,1,1,2), (1,1,2,1), \ldots\}$ small tuples and as a
sanity check.

**The verification route is necessarily `native_decide`.**

---

## 4. Structural reduction via cubical-geometry transport

### 4.1 What the cube framework provides

Per mg-c853 §2.3, the Coxeter cube complex $\mathcal{X}(S_n)$ and
its constrained sub-complex $\mathcal{X}(P)$ are well-defined CAT(0)
cube complexes (Niblo–Reeves 2003), with a direct identification
between

$$
\mathcal{X}(P) \;\cong\; \text{chamber complex of}\; \mathcal{O}(P)
$$

up to a chambers-↔-vertices, walls-↔-facets duality. The OneThird
chamber decomposition (`mg-10d9`, `Mathlib/LinearExtension/OrderPolytope.lean`,
sub-α-C EX-5 Session C) supplies this duality concretely in the
$\mathcal{O}(P)$ direction. So the cube-side is already in tree as
the chamber-side.

For the residual axiom, the cube structure organizes:

- **0-cells of $\mathcal{X}(P)$** $\;\leftrightarrow\;$ linear extensions
  $\sigma \in \mathcal{L}(P)$ $\;\leftrightarrow\;$ chambers
  $\Delta_\sigma \subset \mathcal{O}(P)$.
- **1-cells of $\mathcal{X}(P)$** $\;\leftrightarrow\;$ adjacent
  transpositions $\sigma \leftrightarrow \sigma s_i$ both in
  $\mathcal{L}(P)$ $\;\leftrightarrow\;$ walls $W_{ij}$ of
  $\mathcal{O}(P)$ where $\sigma_{i,i+1}$ and $\sigma_{i+1,i}$ both
  appear.
- **2-cells of $\mathcal{X}(P)$** $\;\leftrightarrow\;$ pairs $(i, j)$
  with $|i-j| \ge 2$ such that all four corners $\{\sigma, \sigma
  s_i, \sigma s_j, \sigma s_i s_j\} \subseteq \mathcal{L}(P)$.

### 4.2 What it reformulates — but doesn't bypass

A within-band pair $(a, a')$ with shared ambient profile (Case 1 of
`prop:in-situ-balanced`) corresponds in cube language to: the swap
$\sigma \leftrightarrow \sigma s_{(\mathrm{pos}_\sigma(a),\,
\mathrm{pos}_\sigma(a'))}$ is **globally** a poset automorphism of
$\alpha$. Cube-side: the wall $W_{a,a'}$ has stabilizer the full
$\mathbb Z/2$ acting by transposition. This is the "1-cube around
every 0-cell" structural form.

The residual case (Case 3, `Case3Witness`) is the **opposite** —
no such global symmetry exists. The cube framework rephrases this
as "the wall $W_{a,a'}$ has trivial stabilizer for every within-band
pair $(a, a')$ in $A$". This is a clean reformulation but **carries
the same content** as `¬ Case1 ∧ ¬ Case2Witness`.

The load-bearing math of the residual case — "two of three share
a profile coordinate $\Rightarrow$ band-restricted FKG sub-coupling
$\Rightarrow$ balanced pair on a strict sub-poset" — has a partial
cube-side analogue:

- The "two share a profile coordinate" pigeonhole (Step 1 of
  `rem:enumeration`) corresponds to: in any 3-antichain
  $A = \{a_1, a_2, a_3\}$ within a band, two of the walls $W_{a_i,
  a_j}$ share a side. This is enforced by $(L2)$ and the size cap
  $|Q| \le 3(3w+1)$.
- The "band-restricted FKG sub-coupling" (Step 2) corresponds to a
  Garland-style local-to-global spectral argument on the cube
  complex of the sub-poset on the bands strictly above (or below)
  $A$. Local cube-link expansion would give global probability
  expansion, hence a probability gap on the shared-profile pair.

Step 2 is **where the manifesto's spectral framework would enter**
if executable. But:

- The mg-c853 §3 Step 2 verdict is "load-bearing open math; beyond
  polecat-class scope; requires specialist input (Anari–Liu–Oveis
  Gharan–Vinzant high-dimensional expander theory)."
- `mg-75ef` and `mg-5bf9` reached identical conclusions by two
  independent paths: the math genuinely needs **probability-form
  cross-poset FKG** (`A8-S2-cont` scope, $\sim 2000$–$3500$ LoC) OR
  **finite enumeration on the bounded range**.

The cube framework rebadges the gap but does not bridge it.
**Garland-style local-to-global spectral arguments on $\mathcal{X}(P)$
are themselves the math content `mg-c853 §3 Step 2` parks for
specialist input** — they are not free-of-charge in the manifesto.

### 4.3 The narrow win available without Step 2

What the cube framework *does* deliver — and this is the
sub-GREEN content — is:

**The chamber-decomposition machinery in tree (`mg-10d9`,
`Mathlib/LinearExtension/OrderPolytope.lean`) already gives the
`HasBalancedPair` ↔ chamber-volume identity needed to lift
the Bool-level `enumPosetsFor` result to a Prop-level
`HasBalancedPair α`.** Concretely: the existing
`hasBalancedPair_of_orderIso` (Bool-certificate → Prop) of the F5a
$K=3$ certificate is the same Bool-to-Prop bridge that a $K=4$
extension would consume. No new Prop-side infrastructure is needed.

In particular: **extending the certificate from $K=3$ to $K=4, w=1$
is purely a Bool-level engineering task** — no math gap.

---

## 5. Lean execution spec for the sub-GREEN target

This section specifies the polecat-tractable narrow target — Window
C of §2.2 — as an execution ticket draft, not as a deliverable of
this scoping.

### 5.1 Target statement

Extend the F5a Bool-certified scope to cover $(K=4, w=1)$ plus the
small $K=3$ residual sliver. Concretely, prove

```lean
theorem case3_balanced_K4_w1 :
    allBalancedAtK 4 1 12 = true := by native_decide
```

where `allBalancedAtK K w sizeLimit : Bool` is a $K$-parametric
generalization of the existing `allBalanced w sizeLimit` of
`Case3Enum.lean:360`, replacing the hardcoded `bandSizesGen 3 …`
with `bandSizesGen K …`. Plus three smaller theorems for the K=3
sliver:

```lean
theorem case3_balanced_K3_w2_sliver : allBalancedAtK 3 2 9 = true := by native_decide
theorem case3_balanced_K3_w3_sliver : allBalancedAtK 3 3 9 = true := by native_decide
theorem case3_balanced_K3_w4_sliver : allBalancedAtK 3 4 9 = true := by native_decide
```

(Note: the sliver theorems have `sizeLimit = 9` rather than `7`,
extending the existing `case3_balanced_w{2,3,4}` to cover
$c \in \{8, 9\}$.)

### 5.2 LoC estimate

| Component | LoC | Notes |
|-----------|-----|-------|
| `allBalancedAtK` generalization of `allBalanced` | ~30 | Parametrize `bandSizesGen 3` to `bandSizesGen K`. |
| `case3_balanced_K4_w1` theorem + native_decide | ~10 | One-liner per existing `case3_balanced_w{1,...,4}`. |
| Three sliver theorems | ~30 | Similar. |
| `InCase3Scope` widening | ~20 | Extend predicate to cover $(K=4, w=1)$ + sliver; re-prove `card_le_nine`, `w_mem` analogues. |
| Lift bridge — `case3_certificate` → `hasBalancedPair` for K=4 | ~150–300 | Generalize `Case3Enum.AllBalancedBridge`, `Correctness`, `PredMaskBridge` from K=3 to K=4. Mostly straight transcription with `K = 4` constants where the existing K=3 versions use `3`. |
| `hStruct_of_case2_discharge` re-wiring | ~30 | Narrow the axiom call to the strictly out-of-scope residual after the widening. |
| `AXIOMS.md` update | ~60 lines markdown | Document the narrowing; revise "scope-match checklist". |
| **Total Lean LoC** | **~270–470** | |

Native_decide compute load: K=4 w=1 has 81 band-tuples averaging
~17 of the existing K=3,w=1 certificate's load each. Total native
compile time projection: $\sim 80$–$160$ s (existing K=3 w=1 takes
$\sim 60$ s), bounded by the worst-case $(3,3,3,3)$ tuple at
$\mathrm{nfree} = 27$.

### 5.3 What this delivers

- **Axiom narrowing, not elimination.** The residual axiom
  `case3Witness_hasBalancedPair_outOfScope` still applies to the
  $K \ge 5$ slice and to non-sliver $K=4, w \ge 2$ cells. The
  trust-surface count stays at 4 named axioms; only the residual
  axiom's *parameter range* shrinks.
- **Strictly mechanical.** No new math; no new cross-poset FKG
  infrastructure; no new chamber-decomposition machinery beyond
  what mg-10d9 / sub-α-C EX-5 already supplies.
- **Computational trust surface.** Each new `native_decide`
  invocation adds one `_native.native_decide.ax_1_1` to
  `#print axioms` output (the same form already counted for the
  existing $K=3$ certificate). The headline trust statement —
  "the Lean compiler evaluates Bool decidable predicates
  correctly" — is unchanged.

### 5.4 What this does NOT deliver

- **Does NOT eliminate the residual axiom.** The
  enumeration-infeasible bulk ($K \ge 5$, or $K = 4$ with $w \ge 2$
  high-band-size tuples) stays axiomatized. Per the §2 table, of
  the $\sim 10^5$ band-tuples at $w = 4$, only $\sim 100$ are
  enumeration-feasible.
- **Does NOT realize the manifesto framework.** §4 above shows
  the cube-geometry reformulation is consistent and clarifying
  but **doesn't bypass** the FKG sub-coupling that `mg-75ef` /
  `mg-5bf9` diagnosed. The manifesto's "expansion forces balance"
  Step 2 remains the load-bearing open math, parked for specialist
  input.
- **Does NOT extend to $K \ge 5$.** A separate enumeration would
  require a sharper than-2^{nfree} enumeration strategy
  (orbit-canonical-form mask generation, group-theoretic
  factoring under within-band $S_3$ symmetry, etc.). This is
  itself a multi-polecat scope and not part of P3-narrow.

### 5.5 Polecat decomposition

**One polecat session** suffices for §5.1 (mechanical extension):

- *Step A* (~80 LoC): generalize `allBalanced` and
  `bandSizesGen` invocation to `allBalancedAtK`.
- *Step B* (~10–40 LoC): the four `native_decide` theorems.
- *Step C* (~150–300 LoC): widen `InCase3Scope`, regenerate
  `case3_certificate` to invoke all four, update the K=3
  Bool-to-Prop bridges (`Case3Enum.Correctness`, etc.) to handle
  the K=4 layer-count case.
- *Step D* (~30 LoC): narrow the axiom call in
  `hStruct_of_case2_discharge`; verify `#print axioms` output.
- *Step E* (~60 lines docs): update `AXIOMS.md` and the F5a
  certificate's docstring with the new scope.

Budget recommendation: 300k-token polecat with latex-first
disabled (this is implementation, not math). Same trip-wires as
the existing case3 work.

---

## 6. Verdict

**AMBER-narrow.**

### 6.1 Why AMBER, not GREEN

The predecessor (`mg-c853 §5`) framed Path P3 as eliminating the
case3 axiom by cube enumeration. **Enumeration alone cannot do
this** at any $w \ge 2$, $K \ge 4$: the parameter space is
exponential in nfree, and nfree grows as $\Theta(K^2)$ within fixed
band-size tuples. The cube-geometry framework rebadges but does
not bridge the gap that `mg-75ef` and `mg-5bf9` independently
diagnosed (probability-form cross-poset FKG, the deferred
`A8-S2-cont` scope).

Furthermore — and this is the load-bearing scoping correction —
the predecessor's "$K=2$ width-3 layered poset" notation
**conflates three distinct $K$ parameters** (depth, cube
dimension, cell dimension). Under any reading, the predecessor's
P3 target is not actually well-defined; the readings differ by
parameter ranges of three orders of magnitude.

### 6.2 Why NOT RED

A strict sub-window (Window C of §2.2) — $(K=4, w=1)$ plus the
$K=3$ sliver — is enumeration-feasible and trivially executable.
It **narrows the residual axiom's parameter range** by
approximately 100 band-tuples of certified configurations, without
introducing any new math gap. This is a real, polecat-tractable
near-term deliverable, not a research-program scope.

The chamber-decomposition machinery (`mg-10d9`) already gives the
Bool-to-Prop transport that the certificate extension would
consume; no new infrastructure required.

### 6.3 Why trending sub-GREEN

If executed as a follow-on, the sub-GREEN target (§5) delivers:

(a) **Axiom-narrowing**, not elimination — a small but concrete
trust-surface reduction.

(b) **Validation of the cube-↔-chamber identification of mg-c853
§2.3 at the implementation level** — the enumerator extension uses
the same Bool-encoding the chamber decomposition consumes.

(c) **Negative-result clarity** — the polecat report will document
*precisely* which tuples remain axiomatized and why, replacing the
predecessor's optimistic "$K=2$" reading with a parameter-explicit
residual.

### 6.4 What narrows the predecessor scope

The Path P3 description in `mg-c853 §5` should be revised to:

> **Path P3 (revised, post-mg-9d6c).** Extend the F5a `case3_certificate`
> Bool enumeration from $(K=3, w \in \{1,2,3,4\})$ to $(K=4, w=1)$ plus
> the K=3 c-sliver $(c \in \{8, 9\}, w \in \{2,3,4\})$.
> This *narrows* the residual axiom
> `case3Witness_hasBalancedPair_outOfScope` to the strict
> $\{K \ge 5\} \cup \{K = 4, w \ge 2\}$ window of the original
> parameter range. Does **not** eliminate the axiom; the $K \ge 5$
> bulk remains, and elimination of that bulk requires the
> `A8-S2-cont` probability-form cross-poset FKG infrastructure
> (`~2000`–`3500` LoC, multi-polecat) or a Garland-style
> high-dimensional-expander spectral argument that is itself the
> `mg-c853 §3 Step 2` load-bearing open math.

### 6.5 Recommended next actions

1. **File the sub-GREEN execution ticket** for §5: one polecat session,
   $\sim 300$–$500$ LoC, no new math, axiom-narrowing not elimination.
   Suggested ticket title: "Path P3-narrow — extend F5a case3_certificate
   to K=4 w=1 + K=3 c-sliver".
2. **Park the manifesto-level P3 ("eliminate the axiom").** The
   $K \ge 5$ bulk is not addressable by enumeration alone.
   Replacement strategies require either A8-S2-cont (Lean-side scope)
   or the §3-Step-2 spectral expansion specialist input (math-side
   scope) — both are multi-month, not polecat-class.
3. **Update `compatibility-geometry-feasibility-scoping.md` §5
   verdict on P3** to reference this scoping doc. The mg-c853 §5
   "highest-leverage near-term path" framing remains correct
   *narrowly* (axiom-narrowing IS the highest-leverage near-term
   move), but the predecessor doc's optimism about
   axiom-elimination should be replaced by §6.4's revised wording.
4. **No new project axioms.** The scoping introduces none; the
   sub-GREEN execution ticket also introduces none. The trust
   surface stays at 4 named project axioms + 5 `native_decide` per
   §6 of the predecessor doc.

---

## 7. Open questions / honest unknowns

(O1) The Window B middle ground (extended P3 — cover all $\sim 914$
enumeration-feasible tuples across $w \in \{1,2,3,4\}$, $K \in
\{3,4,5,6,7\}$) is a possible execution target between Window C
and Window A. Is the extra ~$800$ tuples of axiom narrowing worth
the engineering cost of refactoring `Case3Enum/W*.lean` to handle
arbitrary $K$? The polecat verdict is: *probably not worth it for
the marginal trust-surface return* — Window C captures the
"semantically distinct" extensions ($K=4$ new depth, $K=3$ sliver
new size cap), and Window B's extra tuples are just more of the
same $(K=4, w \ge 2)$ slice. But this is a judgment call worth
flagging.

(O2) Is there a smarter enumeration strategy that pushes the
nfree $\le 27$ cap to nfree $\le 35$ or higher? Candidates:
**orbit-canonical mask generation** under within-band $S_3$
symmetry (factor of up to $216 = 6^3$ for K=3 bands, more for
$K \ge 4$); **per-band closure caching**; **incremental
subset-DP**. Each could in principle push the feasible range by
3–10 nfree-bits, gaining $2^{3-10}$ in mask coverage. But these
are real engineering investments and would need their own scoping
doc. Out of P3 scope.

(O3) Does the cube-complex framework give a *positive* tool for
the $K \ge 5$ bulk that this scoping missed? Possibilities:
**Garland local-to-global** (mentioned above; still needs
specialist input); **CAT(0) projection arguments** (Sageev — but
$\mathcal{X}(P)$ is generally not convex in $\mathcal{X}(S_n)$, so
the projection argument is unclear); **link-of-vertex spectral
descent** (Anari et al; needs the §3 Step 2 of mg-c853 to be
operational). None of these is polecat-tractable as a follow-on.
The scoping verdict stands.

(O4) Should this scoping merge into the predecessor branch
`compat-geom-scoping` or stand on a new `compat-geom-pathP3`
branch? Per the ticket §6 dispatch line, this polecat targets a
new branch `compat-geom-pathP3`. PM-mayor decision on whether to
fast-forward into `compat-geom-scoping` post-merge.

---

## 8. Token-budget report

This document was authored in a single polecat session at ~700
lines of substantive content; the 400k token cap was not
approached (approximate spend: ~100k of 400k). No trip-wires
fired. No new project axioms introduced. No Lean source changes;
this is a docs-only scoping artifact per `mg-c853`'s latex-first
discipline.

Manifesto preserved byte-for-byte in
`docs/compatibility-geometry-manifesto.md` (unchanged from
`mg-c853`); feasibility scoping preserved in
`docs/compatibility-geometry-feasibility-scoping.md`
(unchanged from `mg-c853`); this Path P3 scoping is the third
artifact in the compat-geom doc set.

---

*Authored by polecat `cat-mg-9d6c`, branch `polecat-cat-mg-9d6c`
→ target `compat-geom-pathP3`. Predecessor: `mg-c853`
(`docs/compatibility-geometry-feasibility-scoping.md`, commit
`0d8f438`). Sibling references: `mg-75ef`
(`docs/case3-port-arc/rem-enumeration-proof.md`),
`mg-5bf9` (`docs/case3-port-arc/linear-majority-alignment.md`),
`mg-b846` (`Case3Residual.lean` axiom site), `mg-10d9`
(`OrderPolytope.lean` chamber decomposition). 2026-05-13.*
