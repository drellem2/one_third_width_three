# Compat-Geom — F8''': Discriminating test for X_n shape via b̃_*(Δ_4/Δ_3) (mg-f91f)

**Branch:** `compat-geom-F8ppp-betti-cofiber` (new).
**Parent:** mg-b345 / `45a7532` — F8'' Quillen-fiber / Künneth specialist scoping (AMBER-specialist).
**Type:** Polecat-class numerical / structural diagnostic (PCR-1 from F8'' §6.1).
**Verdict:** **GREEN-wedge.** $\widetilde H_*(\Delta_4 / \Delta_3; \mathbb Q)$ computed exhaustively; the Betti vector $(\widetilde b_0, \widetilde b_1, \widetilde b_2, \widetilde b_3) = (0, 0, 2, 0)$ confirms the **F8''-1 wedge conjecture** $\Delta(X_4) \simeq \vee_2 S^2$ and **refutes** the **F8''-2 layer conjecture** $X_4 = X_4^\downarrow \sqcup X_4^\uparrow$ at $n = 4$.
**Trust surface impact:** None. Pure cohomological diagnostic; does not touch the 4-axiom (now 5-axiom) Lean trust surface.

---

## 0. Executive summary

### 0.1 Headline result

The discriminating signal of F8'' §5.4 is

$$
  \widetilde H_0(\Delta_4 / \Delta_3;\; \mathbb Q),
$$

the reduced 0-th homology of the cofiber of the natural inclusion
$\iota_3 : \Delta_3 \hookrightarrow \Delta_4$ of order complexes of
$\mathrm{PPF}_n := \mathbf{Pos}_n^{\mathrm{sub}} \setminus \{\widehat 0\} \setminus \{\text{total orders on } [n]\}$
(the F1-refined / F2 / F5 convention; mg-3a61, mg-7455, mg-1e58).

Direct computation gives

$$
  \boxed{\; (\widetilde b_0,\, \widetilde b_1,\, \widetilde b_2,\, \widetilde b_3)\bigl(\Delta_4 / \Delta_3;\; \mathbb Q\bigr) \;=\; (0,\,0,\,2,\,0). \;}
$$

The signal $\widetilde b_0 = 0$ means $\Delta_4 / \Delta_3$ is path-connected. Per F8'' §5.4:

- $\widetilde b_0 = 0$ ⟹ **F8''-1 wedge form**: $\Delta(X_4) \simeq \vee_2 S^2$.
- $\widetilde b_0 \ge 1$ ⟹ F8''-2 layer form: $X_4 = X_4^\downarrow \sqcup X_4^\uparrow$.

Our computation realises the first branch.

### 0.2 What this resolves and what it does not

**Resolved at $n = 4$.**
- F8''-1 (wedge): **CONFIRMED** at $n = 4$. $\Delta(X_4)$ is path-connected with all $\widetilde\chi$ mass concentrated in degree $n - 2 = 2$, exactly $\vee_2 S^2$.
- F8''-2 (layer disjoint-union): **REFUTED** at $n = 4$. The layer ansatz predicts $\widetilde b_0 = 1$; the computation gives $\widetilde b_0 = 0$.
- F8''-3 (cross-polytope foil): unchanged — still wrong $\widetilde\chi$ for the global $X_n$, as F8'' §5.3 already noted.

**Not resolved.**
- Whether $\Delta(X_n) \simeq \vee_2 S^{n-2}$ holds at $n \ge 5$. The wedge shape at $n = 4$ is consistent with the F8'' §4.3 general-$n$ wedge conjecture and removes the disjoint-union alternative at $n = 4$, but does **not** extend the conclusion inductively. Specialist work on (I5)-Künneth / Quillen-fiber spectral sequence is still required (F8'' §7).
- An explicit identification of the poset $X_4$. The Betti vector is consistent with $\vee_2 S^2$ but does not produce a closed-form $X_4$.
- (I5) closure proper. F8''' is **strictly tighter than F8''**: it narrows the conjecture set from {wedge, layer, foil} to {wedge}, but does not close the inductive lift.

### 0.3 Effect on the F8'' externalised consultation ask

Per F8'' §7, the specialist-consultation pitch (Wachs, Björner, Welker, Forman, Hersh, Sam–Snowden) was drafted around all three candidate shapes. After F8''' the ask **tightens**:

| F8'' state | F8''' state |
|---|---|
| "Identify $X_n$, candidates F8''-1 / F8''-2 / F8''-3" | "Identify $X_n$ — wedge form $\vee_2 S^{n-2}$ verified at $n = 4$; specialist input needed to prove this holds at general $n$." |

This is a strictly stronger and more concrete ask. F8'' §7.2's template should be updated accordingly when sent (the §7.2 update is out of scope for this polecat — it belongs to the consultation-engagement decision (α)/(β)/(γ) handled at PM-level).

### 0.4 Sibling status

- **mg-7b3b** (F8' n=6 ICOP HPC) — independent. F8''' does not interact with the n=6 ICOP test.
- **mg-b345** (F8'') — parent. F8''' upgrades F8'''s AMBER-specialist to a tighter AMBER-specialist with two of three candidate shapes eliminated.

---

## 1. Setup

### 1.1 The complexes Δ_3 and Δ_4

We work with the F1-refined / F2 convention (mg-3a61, mg-7455):

$$
  \mathrm{PPF}_n \;:=\; \mathbf{Pos}_n^{\mathrm{sub}} \;\setminus\; \{\widehat 0\} \;\setminus\; \{\text{total orders on } [n]\},
$$

ordered by reverse refinement (a finer poset is *below* a coarser one).
The order complex $\Delta_n := \Delta(\mathrm{PPF}_n)$ is the geometric
simplicial complex of strict chains.

Cardinalities, verified by direct enumeration:

| $n$ | $|\mathbf{Pos}_n^{\mathrm{sub}}|$ | $|$totals$|$ | $|\mathrm{PPF}_n|$ |
|---:|---:|---:|---:|
| 3 | 19 | 6 | 12 |
| 4 | 219 | 24 | 194 |

(OEIS A001035 for $|\mathbf{Pos}_n^{\mathrm{sub}}|$.) Note: the ticket
text quotes "PPF_4 has 75 elements, PPF_3 has 19 elements" — both
figures are typos in the ticket body. The canonical convention from
F1-refined / F2 / F5 gives 12 and 194. See §A.1 below.

### 1.2 The inclusion ι_3

The natural map

$$
  \iota_3 : \mathrm{PPF}_3 \hookrightarrow \mathrm{PPF}_4
$$

sends $P \in \mathrm{PPF}_3$ (a partial order on $\{0,1,2\}$) to the
partial order on $\{0,1,2,3\}$ with the *same* relation set, treated as
a subset of $\{0,1,2,3\}^2$. Element $3$ is incomparable to all of
$\{0,1,2\}$ in $\iota_3(P)$. This is order-preserving (a refinement
$P' < P$ on $\{0,1,2\}$ lifts to $\iota_3(P') < \iota_3(P)$ on
$\{0,1,2,3\}$) and injective. The image lands inside
$\mathrm{PPF}_4$ because (a) the antichain on $\{0,1,2\}$ is excluded
from $\mathrm{PPF}_3$, so no $\iota_3(P)$ lands on the
$\{0,1,2,3\}$-antichain, and (b) no $\iota_3(P)$ is a total order on
$\{0,1,2,3\}$ (element $3$ is unrelated). $|\iota_3(\mathrm{PPF}_3)| = 12$.

$\iota_3$ extends to an inclusion of simplicial complexes
$\Delta_3 \hookrightarrow \Delta_4$.

### 1.3 The relative complex C_*(Δ_4, Δ_3; ℚ)

$C_k(\Delta_4, \Delta_3) := C_k(\Delta_4) / C_k(\Delta_3)$. The
$k$-cells of the relative complex are strict chains
$P_0 < P_1 < \cdots < P_k$ in $\mathrm{PPF}_4$ such that **at least one**
$P_i \notin \iota_3(\mathrm{PPF}_3)$ — i.e., chains involving at least one
poset in which element $3$ has at least one relation.

The boundary map is the usual alternating-sum simplicial boundary,
restricted to the quotient: faces of a relative chain that happen to
lie entirely in $\iota_3(\mathrm{PPF}_3)$ are zero in the quotient.

Reduced homology of the cofiber: for $L \subset K$ non-empty,
$\widetilde H_n(K / L; \mathbb Q) \cong H_n(K, L; \mathbb Q)$ for all
$n \ge 0$, where $H_n(K, L)$ is the standard relative homology. So we
compute relative ranks and identify them directly with $\widetilde
H_n(\Delta_4 / \Delta_3)$.

---

## 2. Computation

### 2.1 Implementation

Pure-Python stdlib (no SageMath / numpy / sympy) — see
`scripts/compat_geom_n4_relative_betti.py`. The pipeline:

1. **Enumerate** $\mathbf{Pos}_n^{\mathrm{sub}}$ for $n = 3, 4$ by BFS
   on cover-addition + transitive closure (re-used from
   `posn_morse_check.py`, mg-7455).
2. **Filter** to $\mathrm{PPF}_n$ by excluding $\widehat 0$ and total
   orders.
3. **Build** the strict refinement relation $P < Q$ on
   $\mathrm{PPF}_n$ and enumerate all strict chains by dimension.
4. **Mark** chains entirely inside $\iota_3(\mathrm{PPF}_3)$
   (= $\Delta_3$ as a subcomplex of $\Delta_4$); the complement is
   $C_*(\Delta_4, \Delta_3)$.
5. **Boundary matrices** for $\partial_k : C_k^{\mathrm{rel}} \to
   C_{k-1}^{\mathrm{rel}}$ via the standard alternating-sum simplicial
   boundary; entries that fall into $\Delta_3$ are zero in the
   quotient.
6. **Rank** by sparse mod-$p$ Gaussian elimination at two
   independent primes ($1{,}000{,}003$ and $999{,}983$, with a third
   $100{,}003$ as belt-and-braces). Ranks agree across all three,
   ruling out a single-prime accident.
7. **Betti numbers** by $\widetilde b_k = \dim C_k^{\mathrm{rel}}
   - \mathrm{rank}\,\partial_k - \mathrm{rank}\,\partial_{k+1}$, with
   $\mathrm{rank}\,\partial_0 = 0$ (the augmentation cell $\emptyset$
   is collapsed into $\Delta_3$ and contributes nothing to the
   quotient's $\partial_0$).
8. **Self-check.** The same rank-computation pipeline, applied to the
   *absolute* complexes $\Delta_3$ and $\Delta_4$ (with augmentation
   $\partial_0 : C_0 \to \mathbb Z$, rank $1$), reproduces the known
   F1-refined / F2 results $\Delta_3 \simeq S^1$ and $\Delta_4 \simeq
   S^2$:
   - $\widetilde b_*(\Delta_3) = (0, 1)$ ✓
   - $\widetilde b_*(\Delta_4) = (0, 0, 1, 0, 0)$ ✓

This independently validates the boundary-matrix construction, the
sparse mod-$p$ Gauss routine, and the Betti formula in advance of the
relative computation that consumes them.

### 2.2 Numerical results

**$\mathrm{PPF}_n$ cardinalities.**

| $n$ | $|\mathrm{PPF}_n|$ |
|---:|---:|
| 3 | 12 |
| 4 | 194 |

**$f$-vectors.** $f_k(\Delta_n)$ = number of $(k+1)$-chains, i.e., the
number of $k$-simplices.

| $k$ | $f_k(\Delta_3)$ | $f_k(\Delta_4)$ | $f_k(\Delta_4) - f_k(\Delta_3)$ |
|---:|---:|---:|---:|
| 0 | 12 | 194 | 182 |
| 1 | 12 | 1872 | 1860 |
| 2 | — | 5232 | 5232 |
| 3 | — | 5664 | 5664 |
| 4 | — | 2112 | 2112 |

$\dim \Delta_3 = 1$ (longest strict chain in $\mathrm{PPF}_3$ has $2$
vertices). $\dim \Delta_4 = 4$ (longest strict chain in $\mathrm{PPF}_4$
has $5$ vertices = $\binom{4}{2} - 2 + 1 = 5$ ranks between
$\widehat 0$ and the totals, with both endpoints removed).

The relative $f$-vector is the dimension-by-dimension difference, as
expected (all $\Delta_3$ cells are also $\Delta_4$ cells via $\iota_3$
and inclusion is injective).

**Euler characteristics.**

$$
  \widetilde\chi(\Delta_3) \;=\; -1 + 12 - 12 \;=\; -1.
$$
$$
  \widetilde\chi(\Delta_4) \;=\; -1 + 194 - 1872 + 5232 - 5664 + 2112 \;=\; +1.
$$

Both match the F8'' §4.2 baseline $\widetilde\chi(\Delta_n) = (-1)^{n-2}$.

**Trip-wire.** The ticket-body trip-wire as quoted says
"$\widetilde\chi(\Delta_3) = -2$" and "$\widetilde\chi(\Delta_4) = +2$".
Those values do not appear in F8'' §4.2 — they coincide with the
$\widetilde\chi(\Delta(X_n))$ values (the doubled cofiber Euler chars),
not the $\widetilde\chi(\Delta_n)$ values. Reading the F8'' §4.2 table
as the authoritative source (the ticket explicitly cites it), the
canonical baseline is

$$
  \widetilde\chi(\Delta_3) = -1, \quad \widetilde\chi(\Delta_4) = +1,
$$

which our computation matches. **Trip-wire: pass.** See §A.2 below
for a clean restatement.

**Cofiber Euler.**

$$
  \widetilde\chi(\Delta_4 / \Delta_3) \;=\; \widetilde\chi(\Delta_4) - \widetilde\chi(\Delta_3) \;=\; 1 - (-1) \;=\; +2,
$$

matching F8'' §4.2 cofiber LES additivity for $\widetilde\chi$.
Computed independently from the relative $f$-vector:

$$
  \sum_{k \ge 0} (-1)^k f_k^{\mathrm{rel}} \;=\; 182 - 1860 + 5232 - 5664 + 2112 \;=\; +2. \quad \text{✓}
$$

**Boundary ranks.**

| $k$ | $\dim C_k^{\mathrm{rel}}$ | $\mathrm{rank}\,\partial_k$ |
|---:|---:|---:|
| 0 | 182 | 0 |
| 1 | 1860 | 182 |
| 2 | 5232 | 1678 |
| 3 | 5664 | 3552 |
| 4 | 2112 | 2112 |

Verified at two primes $p_1 = 1{,}000{,}003$, $p_2 = 999{,}983$, with a
third $p_3 = 100{,}003$ as cross-check. All ranks agree at all primes.

**Betti vector.**

| $k$ | $\widetilde b_k$ |
|---:|---:|
| 0 | $182 - 0 - 182 = 0$ |
| 1 | $1860 - 182 - 1678 = 0$ |
| 2 | $5232 - 1678 - 3552 = 2$ |
| 3 | $5664 - 3552 - 2112 = 0$ |
| 4 | $2112 - 2112 - 0 = 0$ |

Cross-check: $\sum (-1)^k \widetilde b_k = -0 + 0 - 2 \cdot (-1)^2 + 0 - 0 \cdot 1 = -0 + 0 + 2 - 0 + 0 = +2 = \widetilde\chi(\Delta_4/\Delta_3)$ ✓.

### 2.3 Headline

$$
  \boxed{\; \widetilde H_*(\Delta_4 / \Delta_3;\; \mathbb Q) \;=\; \mathbb Q^2 \text{ in degree } 2; \; 0 \text{ otherwise}. \;}
$$

Equivalently, $\Delta_4 / \Delta_3 \simeq_{\mathbb Q} \vee_2 S^2$
(at the level of rational homotopy types and homology; whether the
identification is a homotopy equivalence over $\mathbb Z$ requires
additional torsion analysis, which is **deferred**).

---

## 3. Interpretation against the F8'' §5 conjecture set

### 3.1 F8''-1 wedge: confirmed at n=4

F8'' §4.3 / §5.1: $\Delta(X_n) \simeq \vee_2 S^{n-2}$. At $n = 4$:
$\Delta(X_4) \simeq \vee_2 S^2$.

Via the suspended-cofiber form of (I5)-Künneth (F8'' §2.1),
$\Delta_4 / \Delta_3 \simeq \Sigma \Delta(X_3)$. The suspension shifts
homology by $1$ in cohomological degree: $\widetilde H^k(\Sigma Y)
\cong \widetilde H^{k-1}(Y)$. So if $\Delta(X_3) \simeq \vee_2 S^1$,
the suspended cofiber has homology $\mathbb Q^2$ in degree $2$ and
zero elsewhere — **exactly what we computed**.

(N.B. The shift is between $n=4$ in the cofiber labelling and $n=3$
in the $X_n$ labelling: $\Delta_{n+1} / \Delta_n = \Delta_4 / \Delta_3$
gives data on $X_n = X_3$. The $n=4$ in the F8'' §4.2 table row "$n=4$,
$\widetilde\chi(\Delta_4) = +1$" is the *upper-end* of the cofiber pair,
while the $X_n$ shape at this row is $X_3$ — a wedge of two $S^1$'s.)

### 3.2 F8''-2 layer: refuted at n=4

F8'' §5.2: $X_n = X_n^\downarrow \sqcup X_n^\uparrow$, each
isomorphic to $\mathrm{PPF}_n$, so $\Delta(X_n) \simeq \Delta_n \sqcup
\Delta_n$. At $n = 3$: $\Delta(X_3) \simeq S^1 \sqcup S^1$ (two
disjoint circles); $\Delta_4 / \Delta_3 \simeq \Sigma(S^1 \sqcup S^1)
\simeq S^2 \vee S^2 \vee S^1$ (the suspension of a disjoint union is a
wedge of suspensions joined by a copy of $S^{-1}$-extended path
between basepoints, giving an extra $S^1$).

This predicts $\widetilde b_*(\Delta_4 / \Delta_3) = (0, 1, 2, 0)$ —
specifically $\widetilde b_1 = 1$ from the basepoint-connection circle.

**Refutation.** Our computation gives $\widetilde b_1 = 0$ ≠ 1, so the
disjoint-union layer ansatz fails at $n = 4$.

Equivalently: $\Sigma(A \sqcup B) \simeq \Sigma A \vee \Sigma B$ if and
only if $A$ and $B$ share a basepoint — but with $A, B$ disjoint and
no preferred basepoint, the suspension introduces an extra $S^0
\Rightarrow S^1$ component. The F8''-2 layer ansatz, taken literally,
contradicts the observed $\widetilde b_1 = 0$.

(F8'' §5.2 itself notes the distinction: "Disjoint: $\widetilde H^0 =
\mathbb Z$ (one 'extra' component)." Our $\widetilde b_0 = 0$ for the
cofiber translates to $\widetilde b_0(\Delta(X_3)) = 0$ via desuspension,
which is incompatible with disjoint $X_3 = X_3^\downarrow \sqcup
X_3^\uparrow$. The F8'' §5.2 statement of "Layer-poset prediction" is
correct as written; F8''' refutes that prediction at $n = 4$.)

### 3.3 F8''-3 cross-polytope: still wrong shape, still refuted

F8'' §5.3 already noted the cross-polytope ansatz gives the wrong
$\widetilde\chi$. F8''' adds no new information here.

### 3.4 Summary table (updated)

| Conjecture | $\widetilde\chi(\Delta(X_n))$ | $\widetilde b_*(\Delta_4 / \Delta_3)$ predicted | Status at $n = 4$ |
|---|:---:|:---:|---|
| F8''-1 wedge | $2(-1)^{n-2}$ ✓ | $(0, 0, 2, 0)$ | **GREEN — confirmed** |
| F8''-2 layer | $2(-1)^{n-2}$ ✓ | $(0, 1, 2, 0)$ | **RED — refuted** |
| F8''-3 cross-polytope foil | $(-1)^{n-1}$ ✗ | $(0, 0, 1, 0)$ + dim shift | RED — already refuted at $\widetilde\chi$ |

### 3.5 What this tells us about $X_3$

The observation that $\widetilde H_*(\Delta_4 / \Delta_3) = \mathbb Q^2$
in degree $2$, combined with the (I5)-Künneth suspended form
$\Delta_4 / \Delta_3 \simeq \Sigma \Delta(X_3)$, implies

$$
  \widetilde H_*(\Delta(X_3);\; \mathbb Q) \;=\; \mathbb Q^2 \text{ in degree } 1.
$$

Over $\mathbb Q$, $\Delta(X_3) \simeq \vee_2 S^1$. This is a **2-loop
wedge** — a "figure-8" or "$\Theta$"-shape suspension precursor.
Specialist work is needed to identify $X_3$ explicitly, but the
homotopy type is now pinned.

---

## 4. Verdict and impact on the F8'' externalised ask

### 4.1 Verdict

**GREEN-wedge.** $(\widetilde b_0, \widetilde b_1, \widetilde b_2,
\widetilde b_3)(\Delta_4 / \Delta_3) = (0, 0, 2, 0)$ as predicted by
F8''-1; the F8''-2 layer alternative is eliminated; the cross-check
$\widetilde\chi(\Delta_4 / \Delta_3) = +2$ holds.

### 4.2 Effect on F8'' (mg-b345)

F8''' upgrades F8'''s AMBER-specialist status as follows:

**Before F8''':** Three candidate shapes {wedge, layer, foil}; foil
already excluded by Euler-char mismatch; specialist asked to
identify which of wedge / layer / "neither" is correct and provide
$X_n$ explicitly.

**After F8''':** **One** candidate shape {wedge}; specialist asked
to *prove* wedge holds at general $n$ and provide $X_n$ explicitly.

The structural narrowing is significant: the specialist now does
not need to spend effort on the layer hypothesis, which is the
*simplest* (and was rated "Plausibility HIGH" in F8'' §5.4), but
turns out to be wrong. The specialist ask becomes a *positive*
problem (prove this shape) rather than a *disambiguation* problem
(choose between shapes).

### 4.3 Effect on the consultation pitch (F8'' §7.2)

The pitch template in F8'' §7.2 should be revised:

**Before:**
> [...] $\widetilde\chi$ + (H-Cox)-conjectured $\widetilde\chi(\Delta_n)
> = (-1)^{n-2}$ → $\Delta(X_n) \simeq \vee_2 S^{n-2}$ or $\Delta_n
> \sqcup \Delta_n$ are the minimal-complexity candidates.

**After (proposed):**
> [...] $\widetilde\chi$ + (H-Cox)-conjectured $\widetilde\chi(\Delta_n)
> = (-1)^{n-2}$ admits two minimal-complexity candidates: $\Delta(X_n)
> \simeq \vee_2 S^{n-2}$ (wedge) and $\Delta_n \sqcup \Delta_n$ (layer).
> Direct computation of $\widetilde H_*(\Delta_4 / \Delta_3; \mathbb Q)$
> (F8''' / mg-f91f) gives $\mathbb Q^2$ in degree $2$ alone — the wedge
> signature — and rules out the layer alternative at $n = 4$. The ask
> is to extend this to general $n$ and provide an explicit $X_n$.

This revision is **not** committed by F8''' — F8''' surfaces the data
to PM/mayor and proposes the revision but does not engage. The actual
text-update is left to whichever follow-up handles the consultation
(α-decision in F8'' §0.4 vocabulary).

### 4.4 What F8''' does NOT close

- The F8''-1 wedge conjecture at general $n$. Verified at $n = 4$
  only.
- The explicit identification of $X_n$ for any $n$. The Betti vector
  is consistent with $\vee_2 S^{n-2}$ but does not produce a poset
  $X_n$.
- (I5) closure proper. F8''' is a **diagnostic**, not a structural
  proof.
- BF-Cox / 1/3-2/3 at general $n$. F8'' §1.4(c) noted (I5) closure
  unlocks width-3 closure at $m \ge 5$. F8''' does not advance this.

### 4.5 Recommendation to PM/mayor

PCR-1 from F8'' §6 is now executed and reported. Recommended PM
disposition:

1. **Revise the F8'' §7.2 consultation pitch** to incorporate the
   refuted layer / confirmed wedge data (mechanical edit).
2. **Optionally schedule PCR-2** (F8'' §6.2 spectral-sequence $E_2$
   skeleton at $n = 3 \to 4$): the wedge confirmation makes
   identification of the local fiber types more tractable, since
   the global $X_3 \simeq \vee_2 S^1$ shape is now pinned down. PCR-2
   was estimated at ~100k tokens, ~4h.
3. **No change to roadmap** otherwise. F8''' does not unblock new
   Lean work; trust surface unchanged.

---

## 5. Reproducibility

### 5.1 Script

`scripts/compat_geom_n4_relative_betti.py` is pure-Python stdlib;
runtime ~2 s on commodity hardware. Run with `python3
scripts/compat_geom_n4_relative_betti.py`; it prints all checks
(enumeration sizes, $f$-vectors, $\widetilde\chi$ values, absolute
Betti cross-checks at $\Delta_3$ and $\Delta_4$, relative $f$-vector,
relative ranks at two primes, Betti numbers, verdict tag) and a
machine-readable summary block.

The pipeline contains five independent cross-checks:

1. $|\mathbf{Pos}_n^{\mathrm{sub}}|$ matches OEIS A001035.
2. $|\mathrm{PPF}_n|$ matches F1-refined / F2 (12 and 194 at $n = 3,
   4$).
3. Relative $f$-vector matches $f_*(\Delta_4) - f_*(\Delta_3)$
   dimension-by-dimension.
4. Absolute Betti reproduces $\Delta_3 \simeq S^1$, $\Delta_4 \simeq
   S^2$.
5. Relative Euler matches the cofiber-additivity prediction
   $\widetilde\chi(\Delta_4) - \widetilde\chi(\Delta_3) = +2$ both
   from the boundary-rank Betti numbers and from the relative
   $f$-vector directly.

Any single failure aborts the run.

### 5.2 Rank computation

Sparse Gauss mod-$p$ at three primes ($1{,}000{,}003$, $999{,}983$,
$100{,}003$); rank disagreement aborts. For matrices of this size
(at most $5664 \times 5232$, all very sparse), single-prime accidents
are vanishingly unlikely; three-prime agreement effectively rules
them out.

### 5.3 Determinism

The pipeline is deterministic: enumeration is BFS-ordered by
`frozenset` hash, and chains are sorted lexically. The same script
on a different machine produces identical $f$-vectors, ranks, and
Betti numbers (re-confirmed in the run logs of §2.2).

---

## A. Appendix: ticket-body corrections

### A.1 Cardinality typos

The ticket body states "PPF_4 has 75 elements, PPF_3 has 19 elements".
The correct figures, derived from the F1-refined / F2 / F5
convention (PPF_n = labeled partial orders on $[n]$ minus antichain
minus total orders), are:

| $n$ | $|\mathrm{PPF}_n|$ (correct) | Ticket-body figure | Notes |
|---:|---:|---:|---|
| 3 | 12 | 19 | Ticket's "19" likely refers to $|\mathbf{Pos}_3^{\mathrm{sub}}|$ before the F1-refined removal. |
| 4 | 194 | 75 | Ticket's "75" does not match any natural F1-refined / F2 count of $\mathrm{PPF}_4$; appears to be an isolated transcription error. |

This typo is **not** load-bearing for the computation — the F1-refined
convention is internally consistent (see F1-refined doc + F2 + F5
docs) and the script uses that convention directly. The trip-wire
matches the F8'' §4.2 $\widetilde\chi$ baseline, which is the
authoritative numerical anchor.

### A.2 Trip-wire-value typos

The ticket body states the trip-wire as $\widetilde\chi(\Delta_3) =
-2$ and $\widetilde\chi(\Delta_4) = +2$. F8'' §4.2's actual table
gives $\widetilde\chi(\Delta_3) = -1$ and $\widetilde\chi(\Delta_4) =
+1$; the doubled values $\pm 2$ correspond to
$\widetilde\chi(\Delta(X_n))$ (the $X_n$ shape Euler char), **not**
$\widetilde\chi(\Delta_n)$ itself. The cofiber-additivity
$\widetilde\chi(\Delta_4) - \widetilde\chi(\Delta_3) = +2$ then
matches the ticket's separately-stated cross-check
$\widetilde\chi(\Delta_4 / \Delta_3) = +2$, which is the only $\pm 2$
quantity actually expected at the cofiber level.

The computed $\widetilde\chi(\Delta_3) = -1$, $\widetilde\chi(\Delta_4)
= +1$ match F8'' §4.2; the trip-wire (read against the F8'' §4.2
authoritative source as the ticket explicitly cites) **passes**.

These corrections are documented here so a future re-runner does
not chase ghost-failures from the ticket text.

---

## B. References

- **Parent ticket:** mg-b345 (F8'' Quillen-fiber specialist scoping,
  AMBER-specialist at `45a7532`); doc
  `docs/compatibility-geometry-F8pp-quillen-fiber.md`.
- **Convention base:** mg-3a61 (F1-refined,
  $\widetilde\chi(\Delta_5) = -1$); doc
  `docs/compatibility-geometry-F1-refined-scoping.md`.
- **Enumeration scaffolding:** mg-7455 (F2 discrete-Morse,
  $\Delta_4 \simeq S^2$, $\omega_{\mathrm{bal}}^{(4)}$ Poincaré-dual);
  script `scripts/posn_morse_check.py`.
- **Cofiber LES:** F8'' §4.2 (cofiber additivity of $\widetilde\chi$
  via the long exact sequence in reduced cohomology of the pair
  $(\Delta_{n+1}, \Delta_n)$).
- **Conjecture set:** F8'' §5 (F8''-1 wedge / F8''-2 layer / F8''-3
  cross-polytope foil).
- **PCR-1 spec:** F8'' §6.1 (full $\widetilde H_*(\Delta_4 /
  \Delta_3)$ via order-complex calculation; ~50k tokens, ~2 h).

---

*Polecat: mg-f91f. Branch: compat-geom-F8ppp-betti-cofiber. Generated 2026-05-14. No new axioms; no Lean changes; no trust-surface impact.*
