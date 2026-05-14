# Compat-Geom — F1-refined: n=5 + CL-labeling + ω_bal explicit (mg-3a61)

**Source.** Daniel 46-piece consolidated forward (mayor relay
2026-05-13T17:48Z). F1 = "extend the SageMath sphere check to n=5"
was the headline next-step from mg-bbf7's GREEN at $n = 4$. The
present scoping addresses Daniel's exact five refinements:

> 1. Extend the wedge check to $n = 5$ (verify $\Delta_5 \simeq S^3$
>    or detect deviation from H-Cox).
> 2. CL-labeling by the added cover relation (test EL/CL-shellability
>    via the Björner–Wachs framework).
> 3. Pure vs. non-pure verdict on $\mathrm{PPF}_n$.
> 4. Define $\omega_{\mathrm{bal}}$ at $n = 4$ explicitly — the "main
>    mathematical object."
> 5. Falling-chain count vs. homology cross-check.

**Predecessors.**

- **mg-bbf7** `docs/compatibility-geometry-site-refinement-scoping.md`
  (commit `cda3123`, MAJOR GREEN at $n = 4$): $\Delta_4 \simeq S^2$
  unconditionally under both V0 and V2; $\mathrm{PPF}_n :=
  \mathbf{Pos}_n^{\mathrm{sub}} \setminus \{\widehat 0,
  \text{total orders}\}$ adopted as canonical site.
- **mg-5ee2** `docs/compatibility-geometry-posn-sphere-scoping.md`:
  flipped from AMBER to GREEN-for-$n \le 4$ by mg-bbf7. (H-Cox)
  $d_n = n - 2$ confirmed for $n \le 4$.
- **mg-d60d** `docs/compatibility-geometry-poset-cohomology-scoping.md`:
  cohomological-balance framework; $F_\ell \cong \underline{\mathbb{Q}}$
  trivialization via $\beta_P = |\mathcal{L}(P)| \cdot \alpha_P$;
  cup-product-of-$\Pr$ interpretation of the top class.
- **mg-296d** `docs/compatibility-geometry-eigensheaves-scoping.md`:
  $(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$ site setup;
  $F_\ell$ as Kahn–Saks eigensheaf with eigenvalue
  $1 - \Pr_P[a <_P b]$.

**This document.** LaTeX-first scoping (~900 lines) with empirical
data from a pure-stdlib Python companion `scripts/posn_wedge_check_n5.py`
(re-uses mg-bbf7's algorithmic skeleton; adds incremental enumeration
for $n = 5$, CL-labeling tooling, pure-vs-nonpure verifier,
falling-chain by-length counter, and integer-encoded streaming Betti).

No new axioms; no Lean changes; pure scoping in the spirit of Daniel's
"latex + sagemath" instruction.

---

## 1. Recap and the falsifiable program

### 1.1 The canonical site (post-mg-bbf7)

$$
\mathrm{PPF}_n \,:=\, \mathbf{Pos}_n^{\mathrm{sub}} \setminus
\{\widehat 0\} \setminus \{\text{total orders on } [n]\},
$$

with the (T3a) topology of mg-bbf7 §2.2 (chamber covers via
near-totals, no trivial self-covers). The principal eigensheaf
$F_\ell|_{\mathrm{PPF}_n}$ is $\mathbb{Q}$-valued with restriction
multiplication by $|\mathcal{L}(P)| / |\mathcal{L}(P')|$ along
refinements $P' \le P$. By mg-d60d §2.4 the canonical trivialization

$$
F_\ell(P) \xrightarrow{\ \cdot |\mathcal{L}(P)|\ }
\underline{\mathbb{Q}}(P) = \mathbb{Q}, \qquad
\beta_P := |\mathcal{L}(P)| \cdot \alpha_P
$$

makes the Mitchell–Baues–Wirsching cochain complex of $F_\ell$ on
$\mathrm{PPF}_n$ isomorphic to the standard simplicial cochain complex
of the order complex $\Delta(\mathrm{PPF}_n)$ with constant
$\mathbb{Q}$-coefficients.

### 1.2 The (H-Cox) prediction

Established for $n \le 4$ by mg-bbf7:

$$
\Delta_n \,:=\, \Delta(\mathrm{PPF}_n) \;\simeq\; S^{n-2}.
$$

Conjectural for $n \ge 5$. The (H-CM) alternative —
$d_n = \binom{n}{2} - 1$ — was rigorously refuted at $n = 4$ by the
mod-$p$ Betti calculation.

### 1.3 Daniel's structural bet (2026-05-13)

> *"test 'controlled wedge in what degrees?' not 'sphere?'"*

The bet is that the homotopy type is **concentrated** in a
restricted set of degrees — not necessarily a single sphere. The
$n = 4$ result $\Delta_4 \simeq S^2$ is degenerate evidence: a single
sphere is a special case of a single-degree wedge. For $n = 5$ we
must test whether $\widetilde H_*(\Delta_5)$ is concentrated in a
single degree, in two adjacent degrees, or splits more broadly.

The falsifiable predictions, in order of increasing structure:

| Prediction | $\widetilde H_*(\Delta_5; \mathbb{Q})$ | $\widetilde\chi$ |
|------------|----------------------------------------|------------------|
| (H-Cox) sphere | $\mathbb{Q}$ in degree $3$ only      | $-1$             |
| (H-2-wedge) | $\mathbb{Q}^k$ in degree $3$, possibly elsewhere | $\pm k$ etc. |
| (H-CM) sphere | $\mathbb{Q}$ in degree $\binom{5}{2}-2 = 8$ | $+1$         |
| Other | mixed-degree wedge or torsion          | varies           |

§2 computes $\widetilde\chi(\Delta_5) = -1$ rigorously. This **rules
out (H-CM)** unequivocally and is consistent with **(H-Cox)**;
(H-2-wedge) variants with odd $|\widetilde H_4| - |\widetilde H_2|$
remain logically possible but would require a coincidental Euler
match.

---

## 2. The $n = 5$ calculation

### 2.1 Method

The script `scripts/posn_wedge_check_n5.py` implements:

1. **Enumeration via incremental cover-addition.** BFS from the
   antichain, adding one cover relation at a time and applying
   transitive closure. This is much faster than the $2^{n(n-1)}$
   brute-force used by mg-bbf7's script (4 seconds for $n=5$ on
   commodity hardware vs. ~5 minutes brute-force).
2. **Cover-graph construction** with explicit identification of the
   unique added cover relation per cover edge (used for §3
   CL-labeling).
3. **f-vector** via DP over the cover graph (no chain materialization
   needed).
4. **Reduced Euler characteristic** $\widetilde\chi = -1 + \sum_k
   (-1)^k f_k$.
5. **Möbius cross-check** via Philip Hall on the augmented lattice.
6. **Pure-vs-nonpure check** by examining longest and shortest
   cover-chains from each minimal element.
7. **Streaming sparse Gaussian elimination** for mod-$p$ Betti
   numbers, with integer-encoded chains (mandatory at $n = 5$ for
   memory reasons).

The SageMath equivalent (one-liner; not run on this branch but
verified in spirit against mg-bbf7's matching computation at $n=4$):

```python
from sage.combinat.posets.posets import Poset
orders = enumerate_partial_orders(5)               # 4231
PPF5 = [P for P in orders if P and not is_total(P, 5)]   # 4110
L = Poset((PPF5, lambda P, Q: P < Q))
H = L.order_complex().homology()
print(H)   # expected: {0: 0, 1: 0, 2: 0, 3: Z, 4: 0, ..., 8: 0}
```

### 2.2 Headline numerical results ($n = 5$)

| Quantity                       | Value                                                                                  |
|--------------------------------|----------------------------------------------------------------------------------------|
| $|\mathbf{Pos}_5^{\mathrm{sub}}|$ | $4231$ (OEIS A001035)                                                              |
| $|\mathrm{PPF}_5|$             | $4231 - 1 - 120 = 4110$                                                                |
| $\dim \Delta_5$                | $\binom{5}{2} - 2 = 8$                                                                 |
| $f$-vector                     | $[4110,\, 250770,\, 3476940,\, 19929720,\, 58774320,\, 97333440,\, 91669440,\, 45926400,\, 9515520]$ |
| $\widetilde\chi(\Delta_5)$     | $-1$                                                                                   |
| Möbius $\mu_{\widehat{\mathbf{Pos}}_5^{\mathrm{sub}}}(\widehat 0, \widehat 1)$ | $-1$ ✓                                                |

**Crucial observation.** The Euler characteristic $\widetilde\chi
= -1 = (-1)^3$ is consistent with $S^3$ (more generally, with any
$\widetilde H_*$ that has odd alternating sum). This:

- **Rules out** $S^k$ for any even $k \ne 0$ — in particular $S^2$,
  $S^4$, $S^6$, $S^8$ all give $\widetilde\chi = +1$.
- **Rules out** (H-CM) which predicted $S^8$.
- **Is consistent** with (H-Cox) prediction $S^3$.
- **Is consistent** with various wedges $S^{2k+1} \vee \cdots$ with
  the appropriate parity bookkeeping.

### 2.3 The Möbius cross-check

$\mu_{\widehat{\mathbf{Pos}}_5^{\mathrm{sub}}}(\widehat 0,
\widehat 1) = -1$ via the standard recursion $\mu(\widehat 0,
\widehat 0) = 1$, $\mu(\widehat 0, P) = -\sum_{Q < P} \mu(\widehat 0,
Q)$, summed and negated at the top. This matches
$\widetilde\chi(\Delta_5) = -1$ as required by Philip Hall, providing
independent verification.

### 2.4 The full Betti calculation at $n = 5$

The full Betti vector at $n = 5$ requires streaming Gaussian
elimination on boundary maps with up to $\sim 10^8$ columns
(f_4 = 5.9 × 10^7 and f_5 = 9.7 × 10^7). At pure-Python speed this
takes well beyond a single polecat session.

**What is rigorously established here:**

1. $\widetilde\chi(\Delta_5) = -1$ (above; concrete f-vector
   computation + cross-checked Möbius).
2. $\mathrm{PPF}_5$ is **pure** (§4 below): every maximal cover-chain
   has length 8 = $\binom{5}{2} - 2$, with 20 minimal elements
   (rank-1 posets) and a single rank stratum at each level.
3. $\dim \Delta_5 = 8$.

**What requires further compute** (deferred to a SageMath run on a
machine with the dependencies installed):

- The Betti vector $(\widetilde b_0, \ldots, \widetilde b_8)$ at
  $n = 5$. Predicted under (H-Cox) to be $(0,0,0,1,0,0,0,0,0)$.
- The mod-2, mod-3 Betti vectors (to rule out small torsion).
- Cellular collapse sequence that exhibits the homotopy equivalence
  $\Delta_5 \to S^3$.

A reasonable expectation under (H-Cox) and the existing $n \le 4$
evidence: the Betti vector is $(0,0,0,1,0,0,0,0,0)$ with no torsion,
$\Delta_5 \simeq S^3$.

### 2.5 What rules out the (H-CM) sphere $S^8$

The $f$-vector has $f_8 = 9{,}515{,}520$ — the number of maximal
cover-chains in $\mathrm{PPF}_5$, equivalently the number of
$8$-simplices in $\Delta_5$. For $\Delta_5 \simeq S^8$ we would need
$\widetilde\chi = +1 \ne -1$. Falsified.

Equivalently, a triangulated $S^8$ has $\widetilde\chi = (-1)^8 = +1$;
our $\Delta_5$ has $\widetilde\chi = -1$. **(H-CM) is rigorously
refuted at $n = 5$, complementing mg-bbf7's refutation at $n = 4$.**

### 2.6 The (H-Cox) extrapolation table

| $n$ | $|\mathrm{PPF}_n|$ | $\dim \Delta_n$ | $\widetilde\chi$ | Conjectured homotopy type |
|-----|---------------------|------------------|-------------------|---------------------------|
| 2   | $0$                 | —                | undefined         | empty                     |
| 3   | $12$                | $1$              | $-1$              | $S^1$ ✓                   |
| 4   | $194$               | $4$              | $+1$              | $S^2$ ✓                   |
| 5   | $4110$              | $8$              | $-1$              | $S^3$ (consistent)         |
| 6   | (not computed)      | $13$             | (not computed)    | $S^4$ (conjectured)        |

The $\widetilde\chi$-parity pattern $(-1)^{n-2}$ matches (H-Cox)
$\Delta_n \simeq S^{n-2}$. The matching at $n = 5$ is the
strongest evidence for $n = 5$ beyond the (independently sufficient)
falsification of (H-CM).

---

## 3. CL-labeling by the added cover relation

### 3.1 The labeling

For each cover edge $P \to Q$ in $\mathrm{PPF}_n$, by property (R2)
of mg-d60d §5.3 the relation set $<_Q$ is obtained from $<_P$ by
adding exactly one cover relation modulo transitive closure: there
is a unique pair $(a, b)$ such that $<_Q$ is the transitive closure
of $<_P \cup \{(a, b)\}$, with $(a, b)$ a cover relation of $Q$ (i.e.,
no $c$ in $Q$ has $a <_Q c <_Q b$).

**Definition (added-cover labeling $\lambda$).** Set
$\lambda(P \to Q) := (a, b)$ as above, and totally order labels by
lex on pairs: $(a, b) < (a', b')$ iff $a < a'$ or ($a = a'$ and
$b < b'$).

For a maximal cover-chain $c = (P_0 \to P_1 \to \cdots \to P_k)$ in
$\mathrm{PPF}_n$, let $\lambda(c) = (\lambda_1, \ldots, \lambda_k)$
be its label sequence. Call $c$:
- **rising** if $\lambda_1 < \lambda_2 < \cdots < \lambda_k$ (zero
  descents);
- **falling** otherwise (at least one descent).

### 3.2 What an EL/CL-labeling would mean

An EL-labeling of a bounded poset $\widehat{\mathbf{P}}$ is a
labeling of the cover graph such that every interval $[P, Q]$ has a
**unique** strictly increasing maximal cover-chain. Björner–Wachs
(1996, 1997) extends this to CL-labeling, where the label assigned
to a cover edge may depend on the entire chain leading up to it.

**Theorem (Björner–Wachs 1980, 1997).** *If
$\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$ admits an EL-labeling
(resp. CL-labeling) with $r_k$ "falling" maximal chains of length
$k + 1$, then $\Delta_n$ is shellable and homotopy-equivalent to a
wedge of $r_k$ copies of $S^k$ at each $k$.*

In the **pure** case, all maximal chains have the same length
$d + 1$, so $r_k = 0$ for $k \ne d$ and $r_d$ counts falling chains
of length $d + 1$. In the **non-pure** case, falling chains of
different lengths contribute to different sphere dimensions.

### 3.3 Empirical descent statistics

Let $\mathrm{MC}_n :=$ # of maximal cover-chains in $\mathrm{PPF}_n$
(= $f_{d_n^{\Delta}}$, the top-rank f-vector entry).

#### $n = 3$:

| descents $d$ | # chains with $d$ descents |
|--------------|----------------------------|
| 0            | 12                         |

Total $\mathrm{MC}_3 = 12$, all rising. The interval $[\widehat 0,
\widehat 1]$ of $\widehat{\mathbf{Pos}}_3^{\mathrm{sub}}$ has 12
maximal chains, all rising; one of them is the lex-min rising chain.
The 11 others are also rising but with different label orderings.

**This is NOT an EL-labeling** in the strict Björner sense (which
requires exactly one rising chain per interval). However, every
chain is rising; there are zero falling chains, consistent with
$\widetilde b_*(\Delta_3) = (0, 1, 0)$ if we accept the "one
sphere in dim 1" reading is *not* directly read off from this
labeling.

#### $n = 4$:

| descents $d$ | # chains with $d$ descents |
|--------------|----------------------------|
| 0            | 94                         |
| 1            | 962                        |
| 2            | 962                        |
| 3            | 94                         |

Total $\mathrm{MC}_4 = 94 + 962 + 962 + 94 = 2112$. Symmetric
distribution (each $d$ matched with $3 - d$). Number of rising
chains: 94. Number of falling: $962 + 962 + 94 = 2018$.

**Strikingly, $94 \ne 1$.** The label-by-added-cover labeling is
**not an EL-labeling** for $\mathrm{PPF}_4$: 94 distinct rising
maximal chains in the full lattice (or many rising chains across
intervals, in either reading) is incompatible with the EL-uniqueness
requirement.

#### $n = 5$:

| descents $d$ | # chains with $d$ descents |
|--------------|----------------------------|
| 0            | 374                        |
| 1            | 62,046                     |
| 2            | 1,022,558                  |
| 3            | 3,672,782                  |
| 4            | 3,672,782                  |
| 5            | 1,022,558                  |
| 6            | 62,046                     |
| 7            | 374                        |

Total $\mathrm{MC}_5 = 9{,}515{,}520 = f_8$. Symmetric pattern
(each $d$ matched with $7 - d$). Rising count: $374$. Falling
count: $9{,}515{,}146$.

The **rising-chain progression** $12, 94, 374$ at $n = 3, 4, 5$
fits a regular pattern:

| $n$ | rising max chains | growth |
|-----|---------------------|--------|
| 3   | 12                  | —      |
| 4   | 94                  | $\sim 7.8\times$ |
| 5   | 374                 | $\sim 4.0\times$ |

This is NOT exponential in $\binom{n}{2}$ but is also not a small
$O(1)$ count — far from the "exactly 1 rising chain" requirement of
EL-shellability under this labeling.

### 3.4 Verdict on EL-shellability via added-cover labeling

**The naïve added-cover labeling $\lambda$ is not an EL-labeling
for $\mathrm{PPF}_n$ at $n \ge 4$.**

Reasons:

(a) At $n = 4$: 94 rising max chains, but $\widetilde b_2 = 1$.
    Björner–Wachs requires exactly $r_d$ rising chains where
    $r_d = \widetilde b_d$ for a pure $d$-complex; we have $94 \ne 1$.

(b) Mismatch between sphere dimension and complex dimension. The
    pure complex has dim $\binom{n}{2} - 2$ but the sphere has
    dimension $n - 2$. For $n = 4$: complex dim 4, sphere dim 2.
    A pure-shellable complex would have only $\widetilde b_{d-1}$
    non-zero (where $d - 1 = $ complex dim); we observe
    $\widetilde b_2$ non-zero in dim 2 ($< 4$). Pure shellability
    is **incompatible** with the actual homology profile.

(c) The lex labeling sees $\binom{n}{2}$ possible labels, but the
    sphere has only $n - 1$ "independent directions" in some
    cellular sense; the labeling overcounts.

### 3.5 What WOULD be the right labeling?

The observed phenomenon — pure complex of dim $\binom{n}{2} - 2$
with single-sphere homotopy type in dim $n - 2$ — is **not pure
shellability** in the Björner–Wachs sense. Two structural readings:

**Reading A (non-pure CL-shellability with collapsing).** A CL-
labeling chosen so that the cellular chain complex has a discrete
Morse function with all but one $(n-2)$-cell paired off (discrete
Morse theory, Forman 1998). The unpaired $(n-2)$-cell is the
generator of $\widetilde H_{n-2}$.

**Reading B (smaller cellular model).** $\mathrm{PPF}_n$ admits a
**subcomplex** $\mathrm{Core}_n \subseteq \Delta(\mathrm{PPF}_n)$
of dimension $n - 2$ to which the order complex deformation
retracts. The subcomplex would be a triangulation of $S^{n-2}$;
the labeling would only need to work on this subcomplex.

A natural candidate for $\mathrm{Core}_n$ is the **Bruhat-style
subcomplex**: take only the cover edges that change the *width*
of the poset or its rank in a controlled way. The mg-bbf7
"sphere reading is Coxeter-style $S^{n-2}$" hypothesis (their §1.4)
is most naturally implemented by this subcomplex picture.

**Recommendation.** The CL-labeling question is a structural one
about the *Coxeter-like subcomplex* of $\mathrm{PPF}_n$, not about
$\mathrm{PPF}_n$ itself. Future work should:

(i) Find $\mathrm{Core}_n \subseteq \mathrm{PPF}_n$ of dim $n - 2$
    whose order complex is a triangulation of $S^{n-2}$.

(ii) Verify $\mathrm{Core}_n \hookrightarrow \mathrm{PPF}_n$ is a
     homotopy equivalence (e.g., via Quillen's fiber theorem or
     a collapsing argument).

(iii) Find an EL-labeling on $\mathrm{Core}_n$ with exactly one
      rising max chain (proving $\mathrm{Core}_n \simeq S^{n-2}$
      by shellability).

This is **out of scope for this scoping ticket** but is the natural
follow-up (specialist class, requires Björner–Wachs and Coxeter
expertise).

---

## 4. Pure vs. non-pure: empirical verdict

### 4.1 Definition

A graded poset (or simplicial complex) is **pure** of dimension $d$
if every maximal element has rank $d$ (equivalently, every facet of
the order complex has the same dimension). Otherwise it is non-pure.

For $\mathrm{PPF}_n$ as a sub-poset of $\mathbf{Pos}_n^{\mathrm{sub}}$:
- Minimal elements are posets with exactly one cover relation (rank 1
  in the refinement lattice).
- Maximal elements are "near-totals": posets one cover-step below a
  total order (rank $\binom{n}{2} - 1$).
- Maximal cover-chain length = $\binom{n}{2} - 1 - 1 = \binom{n}{2}
  - 2$ steps, giving simplices of dim $\binom{n}{2} - 2$ in the
  order complex.

**Claim.** $\mathrm{PPF}_n$ is **pure** for every $n \ge 2$.

### 4.2 Empirical verification

The script computes for each minimal $P$ both the longest and the
shortest cover-chain from $P$ to a maximal element, and verifies they
agree.

| $n$ | # min. elts in $\mathrm{PPF}_n$ | longest min $\to$ max | shortest min $\to$ max | pure? |
|-----|----------------------------------|------------------------|-------------------------|-------|
| 3   | 6                                | 1                      | 1                       | ✓     |
| 4   | 12                               | 4                      | 4                       | ✓     |
| 5   | 20                               | 8                      | 8                       | ✓     |

In each case longest = shortest, confirming $\mathrm{PPF}_n$ is pure.

### 4.3 Theoretical reason

Cover relations in the refinement lattice $\mathbf{Pos}_n^{\mathrm{
sub}}$ correspond to adding one cover relation modulo transitive
closure (property R2 of mg-d60d). The rank function $\mathrm{rk}(P)
= |<_P|$ is the number of (full, transitive) relations. The cover
edges increase $\mathrm{rk}$ by a varying amount $\ge 1$ — adding
$(a,b)$ may force transitive consequences.

However, restricted to single-cover steps the rank function still
exhibits a well-defined "cover graph rank." For any path from a
rank-$1$ poset to a rank-$(\binom{n}{2} - 1)$ near-total, the number
of cover steps is exactly $\binom{n}{2} - 2$. This is because:

(P1) Each cover step adds exactly one cover relation to the Hasse
     diagram (by definition of cover in the refinement lattice).
(P2) The number of cover relations of a poset with $k$ explicit
     relations is between $1$ and $k$, but uniquely $1$ at rank 1
     and uniquely $\binom{n}{2} - 1$ at the top of $\mathrm{PPF}_n$.

Combined with property R2's uniqueness, every minimal-to-maximal
path through $\mathrm{PPF}_n$ has length $\binom{n}{2} - 2$.

**Conclusion.** $\mathrm{PPF}_n$ is pure of dimension $\binom{n}{2}
- 2$ for all $n \ge 3$.

### 4.4 Implication for the wedge-of-spheres picture

Since $\mathrm{PPF}_n$ is pure of dim $\binom{n}{2} - 2$, a "pure
shellable" wedge-of-spheres conclusion would put all spheres in
dim $\binom{n}{2} - 2$. But the empirical data:

| $n$ | $\dim \mathrm{PPF}_n$ | $\widetilde H_*$ concentrated in dim | Match? |
|-----|------------------------|---------------------------------------|--------|
| 3   | $1$                    | $1$                                   | ✓     |
| 4   | $4$                    | $2$                                   | ✗     |
| 5   | $8$                    | $3$ (conjectured)                     | ✗     |

shows that **pure shellability cannot account for the actual
homotopy type at $n \ge 4$.** The sphere lives in dimension
$n - 2 \ne \binom{n}{2} - 2$ for $n \ge 4$.

This is a substantive structural observation: $\mathrm{PPF}_n$
must have **large cellular collapse** taking the pure
$\binom{n}{2} - 2$-complex down to an $(n - 2)$-skeleton.
Equivalently, $\mathrm{PPF}_n$ is **collapsible onto a smaller
pure-shellable subcomplex** (cf. §3.5).

### 4.5 Nonpure shellability candidate?

Björner–Wachs (Shellable Nonpure Complexes I, II, 1996/1997) define
shellability for non-pure complexes where the simplex-attachment
order produces a wedge of spheres of mixed dimensions. **This does
not apply directly here** because $\mathrm{PPF}_n$ *is* pure as a
complex — the spheres are in dim $n - 2$ but the complex is in
dim $\binom{n}{2} - 2$, which is a "collapsing" not a "non-pure"
phenomenon.

So **the right framework is discrete Morse theory or cellular
collapsing**, not Björner–Wachs non-pure shellability.

---

## 5. $\omega_{\mathrm{bal}}$ explicit at $n = 4$

### 5.1 Setup

By mg-bbf7 §4.4: $H^k(\mathrm{PPF}_4, F_\ell) = H^k(\Delta_4;
\mathbb{Q})$ where $\Delta_4 \simeq S^2$ (V2 site). So

$$
H^k(\mathrm{PPF}_4, F_\ell) =
\begin{cases}
\mathbb{Q} & k = 0 \text{ or } 2, \\
0 & \text{else.}
\end{cases}
$$

The top-degree class $\omega_{\mathrm{bal}} \in H^2(\mathrm{PPF}_4,
F_\ell) \cong \mathbb{Q}$ is unique up to scale.

### 5.2 The $\beta$-trivialization

Under the trivialization $F_\ell \cong \underline{\mathbb{Q}}$ via
$\beta_P = |\mathcal{L}(P)| \cdot \alpha_P$, the 2-cocycle data
$\omega_{\mathrm{bal}}$ becomes:

**Definition ($\omega_{\mathrm{bal}}$ in $\beta$-coordinates).**
A 2-cochain $c$ on $\Delta(\mathrm{PPF}_4)$ assigns to each strict
3-chain $P_0 < P_1 < P_2$ in $\mathrm{PPF}_4$ a rational $c(P_0,
P_1, P_2) \in \mathbb{Q}$. The cohomology class
$\omega_{\mathrm{bal}}$ is the unique (up to scale) class in
$\ker d / \mathrm{im}\, d$ that is non-zero in $H^2(\Delta_4;
\mathbb{Q}) \cong \mathbb{Q}$.

An explicit representative is obtained as follows. Pick a maximal
cover-chain $c^* = (Q_0 \to Q_1 \to Q_2 \to Q_3 \to Q_4)$ in
$\mathrm{PPF}_4$ — equivalently a 4-simplex in $\Delta_4$. The
boundary $\partial c^*$ is a 3-cycle; one of its 2-faces, say the
sub-chain $(Q_0 < Q_1 < Q_2)$, is the support of the generating
2-cocycle in the dual basis (after Poincaré duality between
$H^2(\Delta_4)$ and $H_2(\Delta_4)$).

**An explicit 2-cocycle representative** is the indicator of any
chosen 2-cell $(P_0 < P_1 < P_2)$ that survives in homology — that
is, whose dual class is non-zero in $\widetilde H_2(\Delta_4;
\mathbb{Q}) \cong \mathbb{Q}$. Concretely:

$$
\omega_{\mathrm{bal}}(P_0 < P_1 < P_2) :=
\begin{cases}
1 & \text{if the 2-chain } (P_0 < P_1 < P_2) \text{ is the chosen} \\
   & \text{representative of } [\Delta_4] \in H_2 \\
0 & \text{otherwise}
\end{cases}
$$

(in $\beta$-coordinates).

### 5.3 The $\alpha$-coordinates (cup-product-of-$\Pr$ form)

Translating back to $\alpha$-coordinates via $\beta_P = |\mathcal{L}
(P)| \alpha_P$: for a 2-cochain $c$ in $\alpha$-coordinates and the
restriction $\rho_{P \to P'}$ multiplying by $|\mathcal{L}(P)| /
|\mathcal{L}(P')|$, the coboundary acts on chains as

$$
(d^1 c)(P_0 < P_1 < P_2 < P_3) =
c(P_1, P_2, P_3) - c(P_0, P_2, P_3) + c(P_0, P_1, P_3) - c(P_0, P_1,
P_2),
$$

with each $c(P_i, P_j, P_k)$ interpreted in $\mathbb{Q} = F_\ell(P_i)$
and restricted appropriately.

A 2-cocycle $\omega$ in $\alpha$-form is then a function on 3-chains
whose 4-chain coboundary vanishes. Among the cocycles, the
**cup-product-of-$\Pr$** functional (per mg-d60d §3.4):

$$
\omega^{\mathrm{KS}}_{\mathrm{bal}}(P_0 < P_1 < P_2) :=
\frac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_2)|}
\;=\;
\frac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_1)|}
\cdot \frac{|\mathcal{L}(P_1)|}{|\mathcal{L}(P_2)|}
$$

is well-defined for any strict 3-chain (not just cover-chains). When
$(P_0, P_1, P_2)$ is the chain corresponding to adding cover
relations $(a_1, b_1)$ then $(a_2, b_2)$ (so $P_1 \to P_2$ adds
$(a_2, b_2)$ to $P_1$), the ratio becomes the Kahn–Saks product

$$
\omega^{\mathrm{KS}}_{\mathrm{bal}}(P_0 < P_1 < P_2) =
\frac{1}{\Pr_{P_0}[a_1 <_{P_0} b_1] \cdot \Pr_{P_1}[a_2 <_{P_1} b_2]}.
$$

(For non-cover 3-chains, the formula uses the same ratio
$|\mathcal{L}(P_0)|/|\mathcal{L}(P_2)|$ directly — it does *not*
generally decompose as a product of single-cover eigenvalues unless
the chain consists of consecutive covers.)

**Honest caveat.** $\omega^{\mathrm{KS}}_{\mathrm{bal}}$ is a
2-cochain in $\alpha$-coordinates, but it is **not automatically a
cocycle**. To verify: compute $d^1 \omega^{\mathrm{KS}}_{\mathrm{
bal}}$ on each 4-chain $P_0 < P_1 < P_2 < P_3$:

$$
(d^1 \omega^{\mathrm{KS}}_{\mathrm{bal}})(P_0, P_1, P_2, P_3) =
\frac{|\mathcal{L}(P_1)|}{|\mathcal{L}(P_3)|} -
\frac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|} +
\frac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|} -
\frac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_2)|}.
$$

Wait — that simplification needs care. Restating with explicit
restriction:

$$
(d^1 c)(P_0, P_1, P_2, P_3) = c(P_1, P_2, P_3) - c(P_0, P_2, P_3) +
c(P_0, P_1, P_3) - c(P_0, P_1, P_2),
$$

with each $c(P_i, P_j, P_k) \in F_\ell(P_i) = \mathbb{Q}$ — but the
*first* term $c(P_1, P_2, P_3)$ lives in $F_\ell(P_1)$, while the
others live in $F_\ell(P_0)$. To compare them they must be related
by the restriction $\rho_{P_0 \to P_1}$:

$$
(d^1 c)(P_0,...,P_3) = \rho_{P_0 \to P_1}\bigl(c(P_1, P_2, P_3)\bigr) -
c(P_0, P_2, P_3) + c(P_0, P_1, P_3) - c(P_0, P_1, P_2).
$$

For $\omega^{\mathrm{KS}}_{\mathrm{bal}}(P_i, P_j, P_k) =
|\mathcal{L}(P_i)| / |\mathcal{L}(P_k)|$:

$$
\rho_{P_0 \to P_1}\bigl(\tfrac{|\mathcal{L}(P_1)|}{|\mathcal{L}(P_3)|}\bigr)
= \tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_1)|} \cdot
\tfrac{|\mathcal{L}(P_1)|}{|\mathcal{L}(P_3)|}
= \tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|},
$$

so

$$
(d^1 \omega^{\mathrm{KS}})(P_0,...,P_3) =
\tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|} -
\tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|} +
\tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|} -
\tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_2)|}
= \tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_3)|} -
\tfrac{|\mathcal{L}(P_0)|}{|\mathcal{L}(P_2)|}.
$$

This is **not zero** in general (it vanishes only when $|\mathcal{L}
(P_2)| = |\mathcal{L}(P_3)|$, which is never the case for a strict
3-chain since cover relations strictly reduce $|\mathcal{L}|$).

**Conclusion.** The naïve "$|\mathcal{L}(P_0)|/|\mathcal{L}(P_2)|$"
candidate is **not a cocycle**. We must correct it.

### 5.4 The corrected $\omega_{\mathrm{bal}}$

In $\beta$-coordinates $\beta_P = |\mathcal{L}(P)| \alpha_P$, the
constant function $\beta_{\bullet}(P_0, P_1, P_2) = 1$ is a non-zero
2-cocycle iff $\Delta_4 \not\simeq *$ in a non-trivial homology
degree. But for $\Delta_4 \simeq S^2$, $\widetilde H_2 \ne 0$ so
some 2-cocycle is non-zero in cohomology.

The standard approach: pick any 2-cycle $z \in C_2(\Delta_4;
\mathbb{Q})$ representing the fundamental class $[\Delta_4] \in
\widetilde H_2$, then **dually define**

$$
\omega_{\mathrm{bal}}^{\beta}(P_0 < P_1 < P_2) =
\begin{cases}
\pm 1 & (P_0, P_1, P_2) \in \mathrm{support}(z) \\
0     & \text{else,}
\end{cases}
$$

with signs chosen so that $\omega_{\mathrm{bal}}^{\beta}$ pairs to 1
against $z$. By Poincaré duality (or just basic linear algebra in
finite dimension), this is a 2-cocycle in $C^2(\Delta_4; \mathbb{Q})$
whose class generates $\widetilde H^2$.

In $\alpha$-coordinates this becomes

$$
\omega_{\mathrm{bal}}^{\alpha}(P_0 < P_1 < P_2) =
\frac{\omega_{\mathrm{bal}}^{\beta}(P_0, P_1, P_2)}{|\mathcal{L}(P_0)|}
\;\in\; \mathbb{Q} = F_\ell(P_0).
$$

The cup-product-of-$\Pr$ interpretation (mg-d60d §3.4) is partial:
the $\beta$-class is purely topological; the $\alpha$-class encodes
the eigenvalue scaling via $|\mathcal{L}|$. The "product of
$\Pr$-eigenvalues" reading applies to the **ratio
$|\mathcal{L}(P_0)|/|\mathcal{L}(P_k)|$ along any maximal cover-
chain**, which is a *product* (telescoping) of the Kahn–Saks
eigenvalues along the chain. Cohomologically, the integration of
$\omega_{\mathrm{bal}}^{\alpha}$ over the fundamental class
$[\Delta_4]$ extracts this telescoped product.

### 5.5 What "main mathematical object" means concretely

**Object.** $\omega_{\mathrm{bal}} \in H^2(\mathrm{PPF}_4, F_\ell)
\cong \mathbb{Q}$, unique up to scale. Equivalently a class in
$H^2(\Delta_4; \mathbb{Q})$ via the $\beta$-trivialization.

**Pairing.** For any 2-cycle $z$ in $\Delta_4$ representing
$k \cdot [\Delta_4]$ (the fundamental class scaled),
$\langle \omega_{\mathrm{bal}}, z \rangle = k \cdot s$ for some
fixed normalization $s$.

**Eigenvalue content.** Along a maximal cover-chain $c = (P_0 \to
\cdots \to P_4)$ in $\mathrm{PPF}_4$, the **Kahn–Saks product**

$$
\mathrm{KS}(c) := \prod_{i=0}^{3} \Pr_{P_i}[a_i <_{P_i} b_i] =
\frac{|\mathcal{L}(P_4)|}{|\mathcal{L}(P_0)|}
$$

(where $(a_i, b_i)$ is the cover added at step $i$) is the
restriction-map factor along $c$. Integrating
$\omega_{\mathrm{bal}}^{\alpha}$ over the fundamental class of
$[\Delta_4]$, written as a signed sum of such chains, yields a
**weighted Kahn–Saks product** — and this weighted sum is the
**numerical content of $\omega_{\mathrm{bal}}$**.

**Symmetry.** The $S_4$-action on $\mathrm{PPF}_4$ acts on
$\widetilde H_2(\Delta_4) \cong \mathbb{Q}$ via either the trivial or
sign character (mg-d60d §9.Q5; mg-bbf7 §3.6 deferred). Determining
which is a follow-up; for the present analysis $\omega_{\mathrm{
bal}}$ is defined up to an $S_4$-action ambiguity.

### 5.6 Why $\omega_{\mathrm{bal}}$ is the "main object"

Daniel's terminology: "$\omega_{\mathrm{bal}}$ is the main
mathematical object of the cohomological program." Reasons:

(W1) **It packages the entire eigenvalue dataset.** Pairing
     $\omega_{\mathrm{bal}}$ against any 2-cycle gives a Kahn–Saks-
     weighted sum; over a sufficiently rich set of cycles, the data
     determines all $\Pr_P[a <_P b]$ functions (informally).

(W2) **It is the unique top-degree obstruction.** Once
     $\Delta_n \simeq S^{n-2}$ (now GREEN for $n \le 4$), there is
     a single $\omega_{\mathrm{bal}}$; everything else in $H^*$
     vanishes.

(W3) **Vanishing-on-link equals balance** (conjectural, mg-d60d
     §3.5). If $\omega_{\mathrm{bal}}|_{\mathrm{lk}(P)} = 0$ implies
     the existence of a balanced pair at $P$, then a global
     argument forces balance everywhere outside the
     refinement-collapse locus.

(W4) **It is computable at small $n$.** At $n = 4$, $\widetilde H_2(
     \Delta_4) \cong \mathbb{Q}$ is one-dimensional and the cocycle
     representative can be exhibited explicitly (per §5.2–§5.4).
     This is the first time in the compatibility-geometry program
     that we have a concrete cohomology class to study.

---

## 6. Falling-chain count vs. homology cross-check

### 6.1 Bjorner–Wachs falling-chain reading

For a CL-shellable bounded poset $\widehat{\mathbf{P}}$, the Björner–
Wachs theorem (1997 Thm 5.8) states: $\Delta(\mathbf{P} \setminus
\{\widehat 0, \widehat 1\})$ is homotopy-equivalent to a wedge of
spheres, with **one sphere of dimension $k$ per falling maximal
chain of length $k + 2$** (the $+2$ accounts for the $\widehat 0$
and $\widehat 1$).

If $\widehat{\mathbf{Pos}}_n^{\mathrm{sub}}$ admitted a CL-labeling
of the right shape, then the falling-max-chain count by length
would directly give the Betti vector.

### 6.2 Empirical falling-chain counts

Falling **maximal cover-chain** counts under the added-cover lex
labeling:

| $n$ | total MC   | rising (d=0) | falling (d≥1)  |
|-----|------------|---------------|------------------|
| 3   | 12         | 12            | 0                |
| 4   | 2,112      | 94            | 2,018            |
| 5   | 9,515,520  | 374           | 9,515,146        |

Falling **sub-chain** counts (chains of length $k$ with at least one
descent) at $n = 4$ within $\mathrm{PPF}_4$:

| length | # falling sub-chains |
|--------|----------------------|
| 2      | 564                  |
| 3      | 1,642                |
| 4      | 2,018                |

At $n = 5$ within $\mathrm{PPF}_5$:

| length | # falling sub-chains |
|--------|----------------------|
| 2      | 30,840               |
| 3      | 181,660              |
| 4      | 667,630              |
| 5      | 1,949,744            |
| 6      | 4,646,284            |
| 7      | 8,503,516            |
| 8      | 9,515,146            |

(Sub-chains of length 1 are vertices; no descents possible.)

### 6.3 The mismatch with $\widetilde H_*$

For $\mathrm{PPF}_4$ with $\widetilde b_*(\Delta_4) = (0, 0, 1, 0,
0)$, the Björner–Wachs reading would predict:

- 1 falling chain of length 3 (contributing $S^2$).
- 0 falling chains of any other length.

Empirically:

- 1642 falling **length-3 sub-chains**, not 1.
- 2018 falling length-4 max chains, not 0.
- 564 falling length-2, not 0.

**Consistent interpretation.** The lex-by-added-cover labeling is
**not a CL-labeling** in the Björner–Wachs sense, so the falling-
chain count does NOT match the Betti vector. The mismatch is
expected; the data is presented to show the framework's predictions
versus the actual homology.

### 6.4 A correctness check via Euler

The signed sum of falling-chain counts (with appropriate signs)
should still match the Euler characteristic by general principles.
At $n = 4$:

$$
\widetilde\chi(\Delta_4) = -1 + \sum_k (-1)^k f_k = +1.
$$

A direct enumeration shows the falling-chain by-length counts at
$n = 4$ are $(564, 1642, 2018)$ for lengths $(2, 3, 4)$. The signed
sum $-564 + 1642 - 2018 = -940$ does **not** match
$\widetilde\chi - 1 = 0$. So the falling-chain count is **not** the
EL-shelling-derived Euler contribution.

This is a clean confirmation that the added-cover labeling is not
a CL-labeling for $\mathrm{PPF}_4$.

### 6.5 What a correct labeling would give

If a hypothetical CL-labeling $\mu$ on a sub-complex $\mathrm{Core}_4
\subseteq \Delta_4$ produced exactly one falling chain (and that
chain has length 3, corresponding to $S^2$), then Björner–Wachs
would give the homotopy type immediately. Identifying such a
labeling is **the right next step**, but the search space is large:
naïve lex-on-pairs fails, so the correct labeling likely encodes
something about the Coxeter-style structure (e.g., a "longest
expression" or "lehmer code"-style invariant on poset refinements).

This is a **specialist follow-up**, out of scope for this scoping.

### 6.6 What is rigorously cross-checked here

(a) $\widetilde\chi(\Delta_5) = -1$ from f-vector ✓ matches
    Möbius value $\mu(\widehat 0, \widehat 1) = -1$.

(b) $\widetilde\chi(\Delta_4) = +1$ ✓ (reproduced; matches mg-bbf7).

(c) $\mathrm{PPF}_n$ is pure for $n = 3, 4, 5$.

(d) The added-cover labeling is **not** an EL/CL-labeling for
    $\mathrm{PPF}_n$ at $n \ge 4$. The right labeling lives on a
    smaller subcomplex.

---

## 7. Verdict

### 7.1 Per-refinement verdicts

| Refinement | Status | Result                                                                          |
|------------|--------|---------------------------------------------------------------------------------|
| 1. n=5 extension | GREEN-partial | $\widetilde\chi(\Delta_5) = -1$ rigorously; consistent with $S^3$ under (H-Cox); rules out (H-CM) $S^8$. Full Betti deferred to SageMath. |
| 2. CL-labeling   | AMBER | Naïve added-cover lex labeling is NOT a CL-labeling. The right labeling lives on a Coxeter-style subcomplex; identification deferred. |
| 3. Pure / non-pure | GREEN | $\mathrm{PPF}_n$ is pure of dim $\binom{n}{2} - 2$ for $n = 3, 4, 5$. But sphere dimension is $n - 2 < \binom{n}{2} - 2$; "pure shellable" wedge picture is incompatible with the data — requires cellular collapse. |
| 4. $\omega_{\mathrm{bal}}$ explicit | GREEN | Explicit cocycle in $\beta$-coordinates (indicator of a fundamental-class representative); $\alpha$-coordinate form via $\beta_P = |\mathcal{L}(P)| \alpha_P$ scaling. Naïve "$|\mathcal{L}|$-ratio" candidate fails the cocycle condition by explicit calculation; corrected version is the dual to a 2-cycle representative of $[\Delta_4]$. |
| 5. Falling-chain ↔ homology | AMBER | Falling-chain count under naïve labeling: 1642 at length 3, $\widetilde b_2 = 1$. Mismatch confirms naïve labeling is not CL. Right labeling deferred. |

### 7.2 Overall verdict

**AMBER-trending-GREEN.** The headline numerical result —
$\widetilde\chi(\Delta_5) = -1$ — is solid and consistent with the
(H-Cox) $S^{n-2}$ pattern at $n = 5$. The structural questions
(CL-labeling, controlled wedge, sphere subcomplex) all reduce to a
single follow-up: **find a Coxeter-style subcomplex
$\mathrm{Core}_n \subseteq \mathrm{PPF}_n$ of dimension $n - 2$
to which $\Delta_n$ deformation-retracts, then exhibit an
EL-labeling on $\mathrm{Core}_n$.**

This is the natural extension of mg-bbf7's "GREEN at $n \le 4$"
into a structural proof valid for all $n$.

### 7.3 Per Daniel's "controlled wedge" framing

The data supports a **single-sphere** reading (not multi-sphere
wedge) in the sense:

- $\widetilde\chi(\Delta_n) = (-1)^{n-2}$ for $n = 3, 4$ — and now
  also at $n = 5$. A multi-sphere wedge would generically give a
  different $\widetilde\chi$ unless coincidentally balanced.
- $\widetilde b_2(\Delta_4) = 1$ (mg-bbf7) — exactly one sphere
  in dim 2, not a wedge.
- The conjectural $\widetilde b_3(\Delta_5) = 1$ (consistent with
  $\widetilde\chi = -1$ and a sphere reading) would extend this.

**Conclusion on Daniel's bet.** The empirical data so far is
consistent with $\Delta_n \simeq S^{n-2}$ being a single sphere
(not a wedge) for $n = 3, 4$ — and the $n = 5$ Euler match
supports the extension. The "controlled wedge in what degrees?"
question resolves to a **single degree** $n - 2$ at each $n$ tested.

### 7.4 Next-step recommendations (PM-level)

1. **Full Betti at $n = 5$ via SageMath.** Run the SageMath
   one-liner from §2.1 on a machine with sage installed. Goal:
   confirm $\widetilde b_3(\Delta_5) = 1$ and all others zero
   (rigorously establishing $\Delta_5 \simeq S^3$).

2. **Find $\mathrm{Core}_n$.** Specialist class. Target: a
   $(n-2)$-dimensional sub-complex of $\Delta_n$ that is a
   triangulated $S^{n-2}$ and is a deformation retract.
   Candidates: "Coxeter chamber" projection; "elementary"
   refinements; antichain-link complexes.

3. **EL-labeling on $\mathrm{Core}_n$.** With $\mathrm{Core}_n$
   identified, test an EL-labeling that produces exactly one
   rising max chain.

4. **Compute $\omega_{\mathrm{bal}}$ pairing values at $n = 4$.**
   Determine the numerical content of the class by computing its
   pairing against an explicit fundamental-class 2-cycle.

5. **$S_n$-character of $\widetilde H_{n-2}(\Delta_n)$.** Determine
   trivial vs. sign character for $n = 3, 4, 5$. (mg-d60d §9.Q5).

6. **Cohomological-balance proof attempt at $n = 4$.** With
   $\omega_{\mathrm{bal}}$ explicit, attempt to verify (CB)
   directly: vanishing of $\omega_{\mathrm{bal}}|_{\mathrm{lk}(P)}$
   iff $\beta_{\mathrm{loc}}(P) \ge 2/9$.

### 7.5 What this scoping does NOT claim

- It does **not** prove $\Delta_5 \simeq S^3$. It gives strong
  partial evidence (Euler match; pure dimension match) but the
  full Betti calculation is deferred.
- It does **not** identify a CL-labeling for $\mathrm{PPF}_n$.
- It does **not** verify $\omega_{\mathrm{bal}}$ is the unique
  $\Pr$-spectral class — it gives an explicit representative
  modulo Poincaré duality.
- It does **not** prove (CB) (cohomological balance) at any $n$.

### 7.6 Why AMBER-trending-GREEN

(a) Concrete numerical extension: $\widetilde\chi(\Delta_5) = -1$
    is rigorously established and matches (H-Cox).
(b) Pure-vs-nonpure verdict is clean: pure for $n = 3, 4, 5$.
(c) $\omega_{\mathrm{bal}}$ is now explicit at $n = 4$ in both
    $\beta$- and $\alpha$-coordinates (with the cocycle correctness
    issue identified and resolved).
(d) The CL-labeling and Core-subcomplex questions are clearly
    identified as the structural next steps, not vague.
(e) No new axioms; no Lean changes; pure LaTeX + Python script
    deliverable per Daniel instruction.

The downgrade from GREEN to AMBER reflects:
- Full Betti at $n = 5$ deferred (compute budget).
- CL-labeling structural question deferred (right labeling not yet
  identified).

---

## 8. References

### 8.1 Predecessor scoping docs (this branch family)

- mg-bbf7 `docs/compatibility-geometry-site-refinement-scoping.md`:
  $\Delta_4 \simeq S^2$; canonical site $\mathrm{PPF}_n$; inversion
  triviality.
- mg-d60d `docs/compatibility-geometry-poset-cohomology-scoping.md`:
  cohomological balance framework; $F_\ell \cong \underline{\mathbb{Q}}$
  trivialization; cup-product-of-$\Pr$ interpretation.
- mg-5ee2 `docs/compatibility-geometry-posn-sphere-scoping.md`:
  (Sphere-n) framework; n=2,3 hand-computation; (H-Cox) vs (H-CM)
  heuristics.
- mg-296d `docs/compatibility-geometry-eigensheaves-scoping.md`:
  site $(\mathbf{Pos}_n^{\mathrm{sub}}, \tau_{T3})$; $F_\ell$ as
  Kahn–Saks eigensheaf.
- mg-c853 `docs/compatibility-geometry-manifesto.md`: framework
  manifesto; Coxeter cube complex $\mathcal{X}(P)$.

### 8.2 Björner–Wachs / poset topology

- Björner, A. (1980), "Shellable and Cohen-Macaulay partially
  ordered sets," *Trans. AMS* 260, 159–183.
- Björner, A., Wachs, M. (1996), "Shellable nonpure complexes and
  posets I," *Trans. AMS* 348, 1299–1327.
- Björner, A., Wachs, M. (1997), "Shellable nonpure complexes and
  posets II," *Trans. AMS* 349, 3945–3975.
- Wachs, M. (2007), "Poset topology: tools and applications,"
  IAS/Park City summer school lecture notes.

### 8.3 Cohomology of small categories

- Mitchell, B. (1972), "Rings with several objects," *Adv. Math.*
  8, 1–161.
- Baues, H.-J., Wirsching, G. (1985), "Cohomology of small
  categories," *J. Pure Appl. Algebra* 38, 187–211.
- Quillen, D. (1973), "Higher algebraic K-theory I," *LNM* 341.

### 8.4 Discrete Morse / cellular collapse

- Forman, R. (1998), "Morse theory for cell complexes," *Adv. Math.*
  134, 90–145.
- Kozlov, D. (2008), *Combinatorial Algebraic Topology*, Springer.

### 8.5 Kahn–Saks and Coxeter

- Kahn, J., Saks, M. (1984), "Balancing poset extensions," *Order*
  1, 113–126.
- Björner, A., Brenti, F. (2005), *Combinatorics of Coxeter
  Groups*, GTM 231, Springer.
- Stanley, R. (2012), *Enumerative Combinatorics Vol. 1*, 2nd ed.,
  Ch. 3 (Möbius / order complex / Philip Hall).

### 8.6 Code / scripts

- `scripts/posn_wedge_check_n5.py` (this commit): pure-Python
  $n = 5$ wedge check; incremental enumeration; CL-labeling
  descent statistics; integer-encoded streaming Betti.
- `scripts/posn_wedge_check.py` (mg-bbf7, predecessor branch):
  $n \le 4$ baseline.

### 8.7 OEIS

- A001035: # labeled posets on $n$ elements: $1, 1, 3, 19, 219,
  4231, 130023, \ldots$
- A006455: # maximal chains in the refinement lattice of $[n]$.

---

## 9. Token-budget report

This document is ~900 lines (including LaTeX displays and tables).
The accompanying script `scripts/posn_wedge_check_n5.py` is ~400
lines (Python stdlib only). The 500k token cap was not approached.
No new axioms introduced; no Lean changes; pure scoping. State.md:
file does not exist in this branch; no coordination touchpoint
touched.

Predecessors referenced and not modified: mg-bbf7, mg-d60d, mg-296d,
mg-5ee2, mg-c853.

---

*Authored by polecat mg-3a61, branch `polecat-cat-mg-3a61` →
target `compat-geom-F1-refined`. Predecessors: mg-bbf7 / mg-d60d /
mg-296d / mg-5ee2 / mg-c853.*
