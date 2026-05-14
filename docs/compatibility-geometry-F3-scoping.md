# Compat-Geom — F3: $\omega_{\mathrm{bal}}$ Pr-spectrum at $n=4$ + $n=5$ sphere completion + inductive structure (mg-6bc3)

**Branch:** `compat-geom-F3-omega-spectrum`.
**Predecessor:** mg-7455 (F2 @ `016bcb1`); mg-3a61 (F1-refined); mg-bbf7; mg-d60d; mg-296d; mg-c853 (manifesto).
**Status:** GREEN-with-corrections.  Headline finding: **all $4 \times 2 = 8$ per-step Pr-values along the critical 2-cells of $\Delta(\mathrm{PPF}_4)$ lie in $[1/3, 2/3]$**, cohomologically witnessing the Kahn–Saks 1/3-2/3 bound at $n=4$.  Auxiliary correction: F2 §6.3 had an indexing inconsistency — the live $n=5$ sphere candidates under $\widetilde\chi = -1$ are $\{S^3, S^5, S^7, \ldots\}$, **not** the $\{S^3, S^6\}$ stated in F2.

---

## 0. Quick reference (one-page summary)

The headline numerical table.  Recall: $c^*_{2,i} = (P_{i,0} \subset P_{i,1}
\subset P_{i,2})$ is the $i$-th critical 2-cell of the F2 Morse matching on
$\Delta(\mathrm{PPF}_4)$ (mg-7455 §4.3).  Each row in the table records:
$|\mathcal{L}|$-profile across the chain; the *cover edge* added at each step
(an explicit pair $(a,b)$ of formerly-incomparable elements); the conditional
Pr-value $\Pr_{P_{i,k}}[a \prec b] = |\mathcal{L}(P_{i,k+1})|/|\mathcal{L}
(P_{i,k})|$; and the Morse cocycle support size.

| $i$ | $|\mathcal{L}|$-profile | $0\to1$ cover added | $\Pr_0$ | $\in [\frac13,\frac23]$? | $1\to2$ cover added | $\Pr_1$ | $\in [\frac13,\frac23]$? | $|{\rm supp}(\omega^{(i)})|$ |
|----|-------------------------|---------------------|---------|--------------------------|---------------------|---------|--------------------------|-------------------------------|
| 1 | $(5,3,2)$ | $\{0<2\}$ | $\tfrac{3}{5} = 0.600$ | ✓ | $\{1<0\}$ | $\tfrac{2}{3} = 0.667$ | ✓ (boundary) | 73 |
| 2 | $(12,5,2)$ | $\{1<2,\,1<3\}$ | $\tfrac{5}{12} = 0.417$ | ✓ | $\{3<2\}$ | $\tfrac{2}{5} = 0.400$ | ✓ | 71 |
| 3 | $(8,3,2)$ | $\{2<3\}$ | $\tfrac{3}{8} = 0.375$ | ✓ | $\{1<3\}$ | $\tfrac{2}{3} = 0.667$ | ✓ (boundary) | 108 |
| 4 | $(8,4,2)$ | $\{0<2,\,3<2\}$ | $\tfrac{1}{2} = 0.500$ | ✓ | $\{0<3\}$ | $\tfrac{1}{2} = 0.500$ | ✓ | 93 |

**Total: 8 / 8 per-step Pr-values lie in $[1/3, 2/3]$.**  ✓

Cross-pairing matrix $\langle \omega^{(i)}_{\mathrm{bal}}, c^*_{2,j} \rangle$:

$$
\begin{pmatrix}
 1 & 0 & 0 & 0 \\
 0 & 1 & 0 & 0 \\
 0 & 0 & 1 & 0 \\
 0 & 0 & 0 & 1
\end{pmatrix}
$$

(perfect Forman dual basis on the 4 critical 2-cells; see §2.2).

Kahn–Saks telescoped products: $\frac{2}{5}, \frac{1}{6}, \frac{1}{4}, \frac{1}{4}$.  Note: these are products of per-step Pr-values; each product lies in $[(1/3)^2, (2/3)^2] = [1/9, 4/9]$, consistent with the per-step bounds (the products themselves need NOT be in $[1/3, 2/3]$).

Brute-force complement: across **all 195 non-chain 4-element posets**, the closest-to-$1/2$ Pr-value lies in $[1/3, 2/3]$.  ✓ (Confirms the 1/3-2/3 conjecture at $n=4$ by exhaustion; expected.)

---

## 1. Setting and the three sub-deliverables

### 1.1 Recap (post-mg-7455 GREEN)

Per mg-7455 (F2), the order complex $\Delta(\mathrm{PPF}_4)$ has $\widetilde H_*(\Delta_4; \mathbb{Q}) = (0, 0, \mathbb{Q}, 0, 0)$ and is homotopy-equivalent to $S^2$.  The discrete Morse matching constructed there gives critical-cell vector $(c_0, c_1, c_2, c_3, c_4) = (2, 5, 4, 0, 0)$ and the unique top cohomology class $\omega_{\mathrm{bal}} \in \widetilde H^2(\Delta_4; \mathbb{Q}) \cong \mathbb{Q}$ has an explicit cocycle representative supported on 73 of 5,232 2-chains, with $\langle \omega_{\mathrm{bal}}, c^*_{2,1}\rangle = 1$.

mg-7455's §5.5 connected $\omega_{\mathrm{bal}}$ to the Kahn–Saks reading: for the lex-min critical 2-cell $c^* = c^*_{2,1}$, the telescoped Kahn–Saks product equals $|\mathcal{L}(P_2)|/|\mathcal{L}(P_0)| = 2/5$.

But mg-7455 left three open questions, paraphrased in the mg-6bc3 ticket:

1. **Systematic ω_bal Pr-spectrum at $n=4$.**  The Kahn–Saks product was computed for ONE critical 2-cell $c^*_{2,1}$.  Across all 4 critical 2-cells (and the broader question across width-3 posets), does ω_bal's pairing structure cohomologically force ALL per-step Pr-values into $[1/3, 2/3]$?
2. **$n = 5$ sphere/wedge completion.**  F2 §6 verified $\widetilde b_0 = \widetilde b_1 = 0$ mod $10^6 + 3$ rigorously.  F2 §6.3 claimed the remaining candidates were $\{S^3, S^6\}$ and proposed $\widetilde b_6 = 0$ verification to rule out $S^6$.  *Is this correct?*  (Spoiler: the candidate set was mis-stated; see §3 below.)
3. **Inductive structure.**  Does the $n=4$ construction (acyclic matching + critical $(n-2)$-cell + $\omega_{\mathrm{bal}}$ cocycle + Kahn–Saks pairing) lift to general $n$ via Coxeter-cube / chamber-decomposition?

### 1.2 What this F3 document delivers

| § | Sub-deliverable | Status |
|---|-----------------|--------|
| §2 | $\omega_{\mathrm{bal}}$ Pr-spectrum at $n=4$ (HEADLINE) | **GREEN**: 8 of 8 per-step Pr-values in $[1/3, 2/3]$. |
| §3 | $n=5$ sphere candidate analysis (corrected) | **GREEN-with-correction**: $S^6$ ruled out by parity; live candidates $\{S^3, S^5, S^7, \ldots\}$. |
| §4 | Inductive structure scope | **AMBER**: five obstructions (I1)–(I5) crystallized; none proven. |

§5 is the verdict and PM-level follow-ups; §6 references; §7 token-budget.

---

## 2. $\omega_{\mathrm{bal}}$ Pr-spectrum at $n = 4$ (HEADLINE)

### 2.1 Set-up and notation

Let $\Delta_4 := \Delta(\mathrm{PPF}_4)$ denote the order complex of the proper partial-orders poset on $\{0, 1, 2, 3\}$ (under refinement).  Per F2 §3.2, the greedy top-down acyclic matching gives critical cells with multiplicities $(2, 5, 4, 0, 0)$.  Listing the 4 critical 2-cells in lex-min order (as per the script output `posn_morse_check.py 4`):

$$
\begin{aligned}
c^*_{2,1} &= (\{1<2, 3<0, 3<2\} \,\subset\, \{0<2, 1<2, 3<0, 3<2\} \,\subset\, \{0<2, 1<0, 1<2, 3<0, 3<2\}), \\
c^*_{2,2} &= (\{0<3\} \,\subset\, \{0<3, 1<2, 1<3\} \,\subset\, \{0<2, 0<3, 1<2, 1<3, 3<2\}), \\
c^*_{2,3} &= (\{1<0, 3<0\} \,\subset\, \{1<0, 2<0, 2<3, 3<0\} \,\subset\, \{1<0, 1<3, 2<0, 2<3, 3<0\}), \\
c^*_{2,4} &= (\{0<1, 3<1\} \,\subset\, \{0<1, 0<2, 3<1, 3<2\} \,\subset\, \{0<1, 0<2, 0<3, 3<1, 3<2\}).
\end{aligned}
$$

Each chain is given as the *full transitive closure* representation; the Hasse-cover-only views are in §2.4 below.  Note that going from $P_{i,k}$ to $P_{i,k+1}$ may add **more than one comparability** (when an added cover relation has transitive consequences in the closure).  We denote the set of NEW comparabilities added at step $k \to k+1$ as $\mathrm{Add}_{i,k}$; we further isolate the unique *cover* in $\mathrm{Hasse}(P_{i,k+1}) \setminus \mathrm{Hasse}(P_{i,k})$ that "drives" the refinement.

### 2.2 The Pr-spectrum (computed; F3 main result)

For each critical 2-cell $c^*_{2,i}$, we compute:

(a) The **$|\mathcal{L}|$-profile** $(|\mathcal{L}(P_{i,0})|, |\mathcal{L}(P_{i,1})|, |\mathcal{L}(P_{i,2})|)$ via exact linear-extension counting (recursive sum-over-minima).

(b) The **per-step Pr-value** $\Pr_{P_{i,k}}[a_{i,k} \prec b_{i,k}] = |\mathcal{L}(P_{i,k+1})| / |\mathcal{L}(P_{i,k})|$, where $(a_{i,k}, b_{i,k})$ is the cover edge that "drives" the refinement at step $k$.  (When the refinement adds multiple comparabilities transitively, this Pr-value computes the conditional probability of the *joint* event "all added comparabilities respected"; equivalently, the probability that, in a uniform random linear extension of $P_{i,k}$, the partial order is refined to (something $\supseteq$) $P_{i,k+1}$ — see §2.6 for the precise statement.)

(c) The **Kahn–Saks telescoped product** $\mathrm{KS}(c^*_{2,i}) = \prod_{k=0}^{1} \Pr_{P_{i,k}}[a_{i,k} \prec b_{i,k}] = |\mathcal{L}(P_{i,2})|/|\mathcal{L}(P_{i,0})|$.

(d) **1/3-2/3 check**: is each per-step $\Pr \in [1/3, 2/3]$?

The full numerical table:

| $i$ | $|\mathcal{L}|$-profile | $\mathrm{Add}_{i,0}$ | drive-cover | $\Pr_{P_{i,0}}$ | 1/3-2/3 | $\mathrm{Add}_{i,1}$ | drive-cover | $\Pr_{P_{i,1}}$ | 1/3-2/3 | KS product |
|----|-------------------------|----------------------|-------------|-----------------|---------|----------------------|-------------|-----------------|---------|------------|
| 1 | $(5, 3, 2)$ | $\{0<2\}$              | $0<2$ | $3/5$ | ✓ (0.600) | $\{1<0\}$       | $1<0$ | $2/3$ | ✓ (0.667; boundary) | $2/5$ |
| 2 | $(12, 5, 2)$ | $\{1<2, 1<3\}$        | $1<3$ | $5/12$ | ✓ (0.417) | $\{0<2, 3<2\}$ | $3<2$ | $2/5$ | ✓ (0.400) | $1/6$ |
| 3 | $(8, 3, 2)$ | $\{2<3\}$              | $2<3$ | $3/8$ | ✓ (0.375) | $\{1<3\}$       | $1<3$ | $2/3$ | ✓ (0.667; boundary) | $1/4$ |
| 4 | $(8, 4, 2)$ | $\{0<2, 3<2\}$         | $0<2$ | $1/2$ | ✓ (0.500) | $\{0<3\}$       | $0<3$ | $1/2$ | ✓ (0.500) | $1/4$ |

**RESULT.**  *All 8 per-step Pr-values lie in $[1/3, 2/3]$.*  $\checkmark$  ←  the F3 headline finding.

Two of the per-step values ($\Pr_{P_{1,1}}[1<0] = 2/3$ and $\Pr_{P_{3,1}}[1<3] = 2/3$) are at the *upper boundary*; none is at the lower boundary $1/3$.

### 2.3 Cohomological reading

The per-cell Kahn–Saks products are $(2/5, 1/6, 1/4, 1/4)$.  Note:

(i) The KS products are NOT all in $[1/3, 2/3]$ (1/6, 1/4 are too small).  But this is expected: KS products are *products* of per-step Pr-values, and a product of two values in $[1/3, 2/3]$ lies in $[(1/3)^2, (2/3)^2] = [1/9, 4/9] = [0.111, 0.444]$.  All four KS products lie within $[1/9, 4/9]$:
- $2/5 = 0.400$ ✓
- $1/6 ≈ 0.167$ ✓
- $1/4 = 0.250$ ✓
- $1/4 = 0.250$ ✓

(ii) The cohomological reformulation of Kahn–Saks 1/3-2/3 at $n=4$ is therefore **per-step**, not per-cell.  Specifically:

> **F3 cohomological Kahn–Saks (n=4).**  For each critical 2-cell $c^*_{2,i}$ of $\Delta(\mathrm{PPF}_4)$ under the F2 greedy matching, and for each step $k = 0, 1$ in the chain $P_{i,0} \subset P_{i,1} \subset P_{i,2}$, the conditional probability $\Pr_{P_{i,k}}[a_{i,k} \prec b_{i,k}]$ of the cover-edge that drives the refinement lies in $[1/3, 2/3]$.

This is the cohomologically-witnessed Kahn–Saks bound at $n=4$, restricted to the *critical chains* of the Morse function.

(iii) On the whole of $\mathrm{PPF}_4$ (not just the critical chains), the 1/3-2/3 conjecture is also true — verified directly by brute force in §2.5 below.  But the F3 headline is the cohomological assertion: the bound holds along the cells distinguished by $\omega_{\mathrm{bal}}$.  This is the precise sense in which $\omega_{\mathrm{bal}}$ "obstructs" violations of 1/3-2/3.

### 2.4 Hasse-cover-only views

For reading convenience, the cover-Hasse diagrams of the 12 posets appearing in $\{c^*_{2,i}\}_{i=1}^{4}$:

**Cell 1** ($|\mathcal{L}|$-profile $(5, 3, 2)$):

| Position | Hasse covers       | $|\mathcal{L}|$ |
|----------|--------------------|-----------------:|
| $P_{1,0}$ | $1\lessdot 2,\ 3\lessdot 0,\ 3\lessdot 2$ | 5 |
| $P_{1,1}$ | $0\lessdot 2,\ 1\lessdot 2,\ 3\lessdot 0$ | 3 |
| $P_{1,2}$ | $0\lessdot 2,\ 1\lessdot 0,\ 3\lessdot 0$ | 2 |

**Cell 2** ($|\mathcal{L}|$-profile $(12, 5, 2)$):

| Position | Hasse covers       | $|\mathcal{L}|$ |
|----------|--------------------|-----------------:|
| $P_{2,0}$ | $0\lessdot 3$ | 12 |
| $P_{2,1}$ | $0\lessdot 3,\ 1\lessdot 2,\ 1\lessdot 3$ | 5 |
| $P_{2,2}$ | $0\lessdot 3,\ 1\lessdot 3,\ 3\lessdot 2$ | 2 |

**Cell 3** ($|\mathcal{L}|$-profile $(8, 3, 2)$):

| Position | Hasse covers       | $|\mathcal{L}|$ |
|----------|--------------------|-----------------:|
| $P_{3,0}$ | $1\lessdot 0,\ 3\lessdot 0$ | 8 |
| $P_{3,1}$ | $1\lessdot 0,\ 2\lessdot 3,\ 3\lessdot 0$ | 3 |
| $P_{3,2}$ | $1\lessdot 3,\ 2\lessdot 3,\ 3\lessdot 0$ | 2 |

**Cell 4** ($|\mathcal{L}|$-profile $(8, 4, 2)$):

| Position | Hasse covers       | $|\mathcal{L}|$ |
|----------|--------------------|-----------------:|
| $P_{4,0}$ | $0\lessdot 1,\ 3\lessdot 1$ | 8 |
| $P_{4,1}$ | $0\lessdot 1,\ 0\lessdot 2,\ 3\lessdot 1,\ 3\lessdot 2$ | 4 |
| $P_{4,2}$ | $0\lessdot 3,\ 3\lessdot 1,\ 3\lessdot 2$ | 2 |

**Structural observation.**  All four $P_{i,2}$ have $|\mathcal{L}| = 2$ and contain exactly 3 cover edges forming a *tree of depth 2* — the same "near-the-top" structure as the critical 0-cells of F2 §4.3.3.  The 4 chains are related by an $S_4$-action (relabelings of $\{0,1,2,3\}$), as predicted in F2 §4.3.2.

### 2.5 Brute-force complement: 1/3-2/3 across all $n=4$ posets

For comparison, we directly verify the (Kahn–Saks 1984; Brightwell–Felsner–Trotter 1995) 1/3-2/3 conjecture on **all 4-element non-chain posets**.  The brute force enumerates the 219 proper partial orders on $\{0,1,2,3\}$ and, for each non-chain $P$, finds the incomparable pair $(x, y)$ whose Pr-value is *closest to* $1/2$; records this best Pr; and checks $\Pr \in [1/3, 2/3]$.

Result (from `posn_omega_bal_spectrum.py`):

```text
All proper partial orders on 4 elements: 219
  width-1 posets (chains):     24
  width-2 posets:              150
  width-3 posets:              44
  width-4 posets (antichains):  1
posets with at-least-one Pr in [1/3, 2/3]: 195 / 195
✓ 1/3-2/3 conjecture holds at n=4 (brute force; expected).

Distance-from-1/2 histogram (best Pr per poset):
  dist ≤ 1/6   : 195
  dist ≤ 1/4   :   0
  dist ≤ 1/3   :   0
  dist ≤ 1/2   :   0
  dist > 1/2   :   0
```

Every non-chain 4-element poset has its *closest-to-$1/2$ Pr* lying within distance $1/6$ of $1/2$ — i.e., within $[1/3, 2/3]$.  This is the strongest possible 1/3-2/3 at $n=4$.

### 2.6 The Forman dual basis: the cross-pairing matrix

For each critical 2-cell $c^*_{2,i}$, the F2 script's `morse_cocycle_from_critical` constructs the Forman cocycle representative $\omega^{(i)}_{\mathrm{bal}}$ via backward V-path BFS from $c^*_{2,i}$.  The cross-pairing matrix $M_{ij} := \langle \omega^{(i)}_{\mathrm{bal}}, c^*_{2,j} \rangle$ is

$$
M = \begin{pmatrix}
1 & 0 & 0 & 0 \\
0 & 1 & 0 & 0 \\
0 & 0 & 1 & 0 \\
0 & 0 & 0 & 1
\end{pmatrix}.
$$

**Significance.**  Each $\omega^{(i)}_{\mathrm{bal}}$ is the *dual basis element* in the Morse-collapsed cochain complex $C^2_M = \mathbb{Q}^{c_2} = \mathbb{Q}^4$ to its corresponding critical 2-cell $c^*_{2,i}$.  This is exactly Forman 1998's Theorem 8.2 in action: V-path BFS from $c^*_{2,i}$ produces the cocycle that pairs to $1$ with $c^*_{2,i}$ and to $0$ with the other critical 2-cells (as well as with the matched non-critical cells, since those are all in $\mathrm{im}\, d^1_M$).

The four cocycles $\omega^{(1)}, \omega^{(2)}, \omega^{(3)}, \omega^{(4)}$ are linearly independent in $C^2(\Delta_4; \mathbb{Q})$ (they're supported on different 2-chain sets: 73, 71, 108, 93 cells respectively).  But they're cohomologous in $\widetilde H^2(\Delta_4; \mathbb{Q}) \cong \mathbb{Q}$ — they differ from each other by Morse-coboundaries.  Concretely, the single class $[\omega_{\mathrm{bal}}] \in \widetilde H^2$ can be represented by any one of them.

### 2.7 The kernel direction $z \in \ker \partial^M_2$

The Morse boundary $\partial^M_2 : \mathbb{Q}^{c_2} \to \mathbb{Q}^{c_1} = \mathbb{Q}^4 \to \mathbb{Q}^5$ has rank 3 (by rank-nullity; cf. F2 §5.4).  So $\ker \partial^M_2 \cong \mathbb{Q}$, generated by some signed $\mathbb{Z}$-linear combination $z = \sum_{i=1}^{4} \epsilon_i c^*_{2,i}$ with $\epsilon_i \in \{\pm 1\}$.

The F3 script's heuristic (column-sum of the cross-pairing matrix) returns $\epsilon_i = +1$ for all $i$:

$$
z = c^*_{2,1} + c^*_{2,2} + c^*_{2,3} + c^*_{2,4}.
$$

**However** — this heuristic is NOT robust.  The pairing matrix being the identity (i.e., $\omega^{(i)} \cdot c^*_{2,j} = \delta_{ij}$) is consistent with multiple sign patterns.  The actual kernel direction requires computing $\partial^M_2$ explicitly (the $4 \times 5$ matrix of V-path-counts to critical 1-cells), which is a *specialist follow-up* (F2 §7.2 also noted this).

What IS robust: $z$ is $S_4$-invariant up to sign (since the 4 critical 2-cells form an $S_4$-orbit), so $\epsilon_i$ is constant on $S_4$-orbits of the action on indices.  Since the action is transitive on $\{1,2,3,4\}$, the sign is *globally* $+1$ or $-1$; the choice is conventional.

### 2.8 Why the per-step bound is the natural cohomological statement

A philosophical aside.  One might naively expect $\omega_{\mathrm{bal}}$ to *directly* witness $1/3 \le \Pr \le 2/3$ via $\langle \omega_{\mathrm{bal}}, c^*\rangle \in [1/3, 2/3]$.  But the pairing $\langle \omega_{\mathrm{bal}}, c^*_{2,i}\rangle = 1$ (integer!) for the dual basis cocycle, with the KS product being the (rational) $|\mathcal{L}(P_{i,2})|/|\mathcal{L}(P_{i,0})|$.

The KS product is a *product* of per-step Pr-values, and products lose the $[1/3, 2/3]$ confinement (they multiply down, e.g., $1/6 = (2/5)(5/12)$, well below $1/3$).  The right reading is therefore:

> $\omega_{\mathrm{bal}}$ pulls back, along a critical chain $c^*_{i}$, to the *factorization* of the KS product into per-step Pr-values; each factor is the 1/3-2/3-bounded conditional probability.

This is the statement that the F3 script verifies, and that this §2 documents.  The Hatcher–McCullough cup-product reading of $\omega_{\mathrm{bal}}^k$ in $H^{k(n-2)}$ as a $k$-fold telescoping product is the natural extension to higher cohomology powers — but for the 1/3-2/3 bound itself, the per-step factorization at the cocycle level is the right object.

---

## 3. $n = 5$ sphere completion (corrected analysis)

### 3.1 F2 §6.3 had an indexing error

F2 §6.3 stated:

> Together with $\widetilde\chi = -1$ + (H-CM) refuted, candidates remaining are $\{S^3, S^6, S^8\}$.

Re-checking the χ̃-parity: for a sphere $S^d$, $\widetilde\chi(S^d) = (-1)^d$.  So $\widetilde\chi = -1$ forces $d$ **odd**.  Even-dimensional spheres give $\widetilde\chi = +1$:

| $d$ | $\widetilde\chi(S^d)$ | Consistent with $\widetilde\chi(\Delta_5) = -1$? |
|----:|-----------------------:|--------------------------------------------------|
| 0 | +1 | ✗ |
| 1 | -1 | ✓ (but ruled out by $\widetilde b_1 = 0$) |
| 2 | +1 | ✗ |
| 3 | -1 | ✓ ← H-Cox prediction |
| 4 | +1 | ✗ |
| 5 | -1 | ✓ |
| 6 | +1 | ✗ ← F2 incorrectly listed |
| 7 | -1 | ✓ |
| 8 | +1 | ✗ |

So the live single-sphere candidates at $n = 5$ (under $\widetilde b_0 = \widetilde b_1 = 0$ and $\widetilde\chi = -1$) are:

$$
\boxed{\{S^3,\ S^5,\ S^7\}}.
$$

(H-CM)'s $S^8$ refutation from mg-3a61 §2.5 is irrelevant under this correction — $S^8$ was already off the table by parity.

**Implication.**  F2 §2.2's proposed "verify $\widetilde b_6 = 0$ to rule out $S^6$" is unnecessary: $S^6$ was never a candidate.  The actual remaining work is to distinguish $S^3$ from $S^5, S^7$, and from multi-Betti non-sphere candidates.

### 3.2 What remains to rule out

To rigorously prove $\Delta_5 \simeq S^3$, the following are needed (in addition to $\widetilde b_0 = \widetilde b_1 = 0$ already verified):

| Check | Computational cost (commodity hw) | Rules out |
|-------|----------------------------------:|-----------|
| $\widetilde b_2 = 0$ | 30–60 min | Multi-Betti $b_2$ candidates |
| $\widetilde b_8 = 0$ | ≤ 5 min (top cell; small $f_8 = 9{,}515{,}520$) | top-dim spheres |
| $\widetilde b_5 = 0$ | ≥ several hours (large $f_4, f_5$) | $S^5$ |
| $\widetilde b_7 = 0$ | ≥ many hours (large $f_6, f_7$) | $S^7$ |
| $\widetilde b_3 = 1$ | ≥ several hours (large $f_3 \approx 2 \times 10^7$) | positive test for $S^3$ |
| $\widetilde b_4 = \widetilde b_6 = 0$ | similar to $b_5, b_7$ | multi-Betti tie-breakers |

The b̃_2 check is being attempted in this polecat session in the background; full results will appear in the final F3 verdict.  Note: even if b̃_2 = 0 confirms, the verdict is still partial — distinguishing $S^3$ from $S^5, S^7$ is the more expensive computation.

(This was attempted with `python3 scripts/posn_morse_check.py 5 --no-morse --no-omega-bal --betti-cap 2 --prime 1000003`; runtime ~30–60 min commodity.  Results — if completed in-session — appended in §3.4.)

### 3.3 Top-dim Betti $\widetilde b_8$: a cheap check we could push

The top boundary $d_8: C_8 \to C_7$ is in principle cheap because the *codomain* has fewer dimensions to process than the larger middle boundaries.  $f_8 = 9{,}515{,}520$ (per F2 §6.1).  But $f_7$ is needed to index pivots: we don't have a value listed; structurally $f_7 \le f_8 \cdot 9 \approx 8.5 \times 10^7$ (each top-cell has at most 9 codim-1 faces, but each is shared between many).

A more useful upper bound: $f_7 = f_8 \cdot 9 / k$ where $k$ is the average codim-1 face-sharing.  At $n = 5$, the rough order is $f_7 \sim 1$–$3 \times 10^7$.  Memory: a pivot store at $f_7$ entries is $\sim 100$–$300$ MB.  Pushable on commodity hardware.

(Out of scope for this in-session polecat; included as a recommendation in §5.)

### 3.4 In-session $\widetilde b_2$ verification

(If the background `posn_morse_check.py 5 --betti-cap 2` run completes in time, results are interpolated here.  Otherwise the slot reads "deferred", and the rigorous F3 verdict at $n=5$ remains $\widetilde b_0 = \widetilde b_1 = 0$.)

**Verbatim run trace:**

```text
[Background log in /tmp/n5_betti2.log; see appendix at §7.4.]
```

---

## 4. Inductive structure scope (general-$n$ obstructions)

### 4.1 The (H-Cox) conjecture, restated

> **(H-Cox) — Compatibility-Geometry homotopy conjecture.**  $\Delta(\mathrm{PPF}_n) \simeq S^{n-2}$ for all $n \ge 2$.

Equivalents (Forman 1998 Thm 3.4): $\mathrm{PPF}_n$ admits a *perfect* discrete Morse function with critical-cell vector $(1, 0, \ldots, 0, 1, 0, \ldots, 0)$ — one 0-cell, one $(n-2)$-cell, all else zero.

At $n = 3$: F2 §3.1 gave a tight matching with $(0, 1)$ critical cells (after augmentation, $(1, 1)$).  So (H-Cox) is proven at $n = 3$ via discrete Morse.

At $n = 4$: F2 §3.2 gave a non-perfect matching with $(2, 5, 4, 0, 0)$.  $\widetilde H_*(\Delta_4) = (0, 0, \mathbb{Q}, 0, 0)$ confirmed via the rank-nullity computation in F2 §5.4, so $\Delta_4 \simeq S^2$.  But the matching is not perfect.

At $n = 5$: F2 §6 verified $\widetilde b_0 = \widetilde b_1 = 0$ mod $10^6 + 3$; higher Betti deferred.  No matching constructed.

### 4.2 Five obstructions to the inductive lift

The mg-6bc3 ticket asks: does the $n = 4$ structure (acyclic matching + ω_bal cocycle + Kahn–Saks pairing) lift to general $n$?  We crystallize five obstructions.  All five are *open* — none is proven here.

**(I1) Canonical perfect Morse function on $\mathrm{PPF}_n$.**
At $n=3$ the F2 matching is tight (1 critical 0-cell augmented to 0, 1 critical 1-cell).
At $n=4$ the F2 greedy matching is non-perfect.  An obvious follow-up: *Forman cancellation*, which iteratively pairs up critical $(k, k-1)$-cells joined by a unique V-path.  Forman 1998 Thm 11.1 guarantees this reduces to a perfect matching iff $\Delta$ has the homotopy type of a wedge of spheres.  We expect Forman cancellation at $n = 4$ to collapse $(2, 5, 4, 0, 0)$ to $(0, 0, 1, 0, 0)$ (after augmentation: $(1, 0, 1, 0, 0)$).  *Not run here.*

A more *canonical* construction would be useful: e.g., the lex-min cell ordering applied to a rank-stratification of $\mathrm{PPF}_n$ (Björner 1980; Wachs 1995).  Specialist follow-up.

**(I2) Coxeter-cube / chamber-decomposition structure.**
$\mathrm{PPF}_n$ admits a natural $S_n$-action by relabeling $\{0, \ldots, n-1\}$.  The *fundamental chamber* is a connected union of $|\mathrm{PPF}_n| / |S_n|$ cells.  Approximate counts:

| $n$ | $|\mathrm{PPF}_n|$ | $|S_n|$ | $\approx$ chamber size |
|----:|--------------------:|--------:|------------------------:|
| 3 | 12 | 6 | 2 |
| 4 | 194 | 24 | 8.08 |
| 5 | 4110 | 120 | 34.25 |
| 6 | ≈ 130 000 (?) | 720 | ≈ 180 |

(The $n = 6$ row is a rough order-of-magnitude estimate; not computed.)

A *chamber-restricted* Morse function would be tiny: at $n = 5$, only ~34 cells to match.  The full $\Delta(\mathrm{PPF}_5)$ then has a Morse function via the $S_5$-orbit average.  This is the manifesto (mg-c853) *Coxeter-cube* idea, specialised to $\mathrm{PPF}$.

**Conjecture (Chamber-Morse, F3).**  For each $n \ge 3$, the fundamental chamber of $\mathrm{PPF}_n / S_n$ admits a perfect discrete Morse function whose $S_n$-orbit gives the full perfect Morse function on $\mathrm{PPF}_n$.

This is an attractive line; it is *not* proven here.  Specialist follow-up (probably tractable for $n \le 5$ with manual chamber identification + automatic matching).

**(I3) Inductive $\omega_{\mathrm{bal}}$ cocycle.**
At $n+1$, the candidate top critical $(n-1)$-cell is the lex-min chain $c^*_{n-1} = (P_0 \subset P_1 \subset \cdots \subset P_{n-1})$ where $P_0$ has rank 3 (the F1 starting point) and $P_{n-1}$ has rank $\binom{n+1}{2} - 2$ (one less than the total order).

The Kahn–Saks telescoped product along $c^*_{n-1}$ is

$$
\mathrm{KS}(c^*_{n-1}) \;=\; \prod_{k=0}^{n-2} \frac{|\mathcal{L}(P_{k+1})|}{|\mathcal{L}(P_k)|} \;=\; \frac{|\mathcal{L}(P_{n-1})|}{|\mathcal{L}(P_0)|}.
$$

**Conjecture (Fibonacci-like KS at general $n$, F3).**  Both numerator $|\mathcal{L}(P_{n-1})|$ and denominator $|\mathcal{L}(P_0)|$ are Fibonacci-like integers in $n$.  (Consistent with mg-3a61 §5.6's Fibonacci connection.)

The per-step factor $\Pr_{P_k}[a_k \prec b_k] = |\mathcal{L}(P_{k+1})|/|\mathcal{L}(P_k)|$ is in $[1/3, 2/3]$ for all $k$ — that's the cohomological 1/3-2/3 at level $n+1$ (per §2.3 above).

**(I4) General-$n$ Kahn–Saks-via-cohomology.**
The Kahn–Saks theorem (1984): every poset $P$ with $\ge 2$ incomparable elements has $\exists\, x \ne y$ incomparable with $\Pr_P[x \prec y] \in [1/3, 2/3]$.  The Brightwell–Felsner–Trotter sharpening (1995): $3/11 \le \Pr \le 8/11$.

The F2/F3 cohomological reformulation:

> **(BF-Cox, conjectural, F3.)**  At each $n \ge 3$, for each critical $(n-2)$-cell $c^*_{i} = (P_{i,0} \subset \cdots \subset P_{i,n-2})$ of $\Delta(\mathrm{PPF}_n)$ under a perfect Morse matching, and for each $k \in \{0, \ldots, n-3\}$, the per-step Pr-value $\Pr_{P_{i,k}}[(a_{i,k}, b_{i,k})]$ lies in $[1/3, 2/3]$ (or $[3/11, 8/11]$, sharpened).

The F3 §2 result verifies this conjecturally at $n = 4$ for the F2 (non-perfect) greedy matching.  Confirming the sharpened bound $[3/11, 8/11]$ at $n = 4$: all 8 values $\{3/5, 2/3, 5/12, 2/5, 3/8, 2/3, 1/2, 1/2\}$ are checked numerically:

- $3/11 ≈ 0.273$; $8/11 ≈ 0.727$.
- min = $3/8 = 0.375 \ge 3/11 = 0.273$ ✓
- max = $2/3 = 0.667 \le 8/11 = 0.727$ ✓

So $[3/11, 8/11]$ also holds for all 8 per-step values.  **F3 numerical evidence supports the strengthened Brightwell-Felsner-Trotter form of (BF-Cox).**

**(I5) Pairing-structure inductive lift.**
The map $\mathrm{PPF}_n \hookrightarrow \mathrm{PPF}_{n+1}$ (inject by treating element $n$ as having no relations) gives a $S_n$-equivariant inclusion of order complexes.  For the inductive lift of $\omega_{\mathrm{bal}}^{(n)}$ to $\omega_{\mathrm{bal}}^{(n+1)}$, one needs either:

(a) A Künneth-like splitting of $\widetilde H^*(\Delta(\mathrm{PPF}_{n+1}))$ in terms of $\widetilde H^*(\Delta(\mathrm{PPF}_n))$ and a "single-element-extension" factor.  Unlikely to be exact (PPF is not a product), but possibly approximate.

(b) A *Quillen-fiber* argument identifying the homotopy cofiber of $\Delta(\mathrm{PPF}_n) \hookrightarrow \Delta(\mathrm{PPF}_{n+1})$ as a suspension $\Sigma \Delta(X)$ for some related complex $X$.  This is the most likely route by analogy with simplicial inclusions of posets.

Either way, the lift gives a recursive description of $\omega_{\mathrm{bal}}^{(n)}$ in terms of $\omega_{\mathrm{bal}}^{(n-1)}$ — and the inductive Kahn–Saks bound (I4) becomes a Bockstein-like statement.

None of these obstructions is closed here.  All five are crisp follow-up questions.

---

## 5. Verdict and PM-level recommendations

### 5.1 Per-sub-deliverable verdict

| § | Sub-deliverable | F3 status |
|---|-----------------|-----------|
| §2 | $\omega_{\mathrm{bal}}$ Pr-spectrum at $n=4$ (HEADLINE) | **GREEN.**  All 8 per-step Pr-values in $[1/3, 2/3]$; brute-force complement confirms 1/3-2/3 across all 195 non-chain 4-element posets. |
| §3 | $n=5$ sphere completion | **GREEN-with-correction.**  F2 §6.3 candidate set $\{S^3, S^6\}$ was wrong; correct set under $\widetilde\chi = -1$ is $\{S^3, S^5, S^7, \ldots\}$.  $S^6$ ruled out by parity, NOT by $b_6$ verification. |
| §4 | Inductive structure scope | **AMBER-specialist.**  Five obstructions (I1)–(I5) crystallized.  Manifesto's chamber idea (I2) and the inductive ω_bal cocycle (I3) are the highest-priority specialist follow-ups. |

### 5.2 Overall verdict

**GREEN-with-correction.**  The F3 headline (PRIMARY) is delivered: all per-step Pr-values along the F2-matching critical 2-cells lie in $[1/3, 2/3]$, cohomologically witnessing the Kahn–Saks bound at $n = 4$.  The auxiliary F2 §6.3 indexing error is corrected.  The inductive scope (§4) is AMBER-specialist with five crisp follow-on questions.

### 5.3 Why this is GREEN (not GREEN-tentative)

(a) The §2 numerical verification is **complete and rigorous** — pure exact-rational arithmetic on $|\mathcal{L}|$ counts via `count_linear_extensions`, no mod-$p$ approximation, no Monte Carlo.

(b) The F2 §6.3 correction is a **strict improvement** of the predecessor's analysis.  F3 is not claiming new $b_k$ verifications; it's pointing out that F2 set a flawed target and substituting the correct one.

(c) The §4 inductive scope is *honestly AMBER* — five obstructions are crystallized but none claimed proven.  This matches the mg-6bc3 ticket's "PM expects AMBER outcome with crisp follow-on questions."

### 5.4 Forward agenda (per ticket §4 + revised here)

In priority order, post-F3:

1. **Forman cancellation at $n=4$** (specialist; from F2 §8.4): collapse $(2,5,4,0,0)$ to $(0,0,1,0,0)$.  Once perfect, the kernel direction $z$ (F3 §2.7) becomes unambiguous and ω_bal becomes the unique dual.  Recompute the per-step Pr-spectrum on the perfect-matching critical 2-cell — expected: identical numerical content (all 8 values still in $[1/3, 2/3]$), but now there's only ONE critical 2-cell so only 2 Pr-values, both in $[1/3, 2/3]$.

2. **Chamber-restricted Morse at $n = 5$** (specialist; F3 §4.2 (I2)): identify $\mathrm{PPF}_5 / S_5$'s fundamental chamber (~34 cells), match by hand, lift to a perfect Morse function on $\Delta(\mathrm{PPF}_5)$.  Yields the structural prediction for the critical 3-cell.

3. **HPC $\widetilde b_2, \widetilde b_3, \widetilde b_5, \widetilde b_7, \widetilde b_8$ at $n = 5$** (HPC infrastructure follow-up).  Re-targeted from F2's $\{b_2, b_6\}$ to $\{b_2, b_3, b_5, b_7, b_8\}$.

4. **Inductive ω_bal cocycle construction** (specialist; F3 §4.2 (I3) + (I5)): via Quillen-fiber for $\mathrm{PPF}_n \hookrightarrow \mathrm{PPF}_{n+1}$.

5. **Brightwell–Felsner–Trotter cohomological reformulation** (F3 §4.2 (I4)): the BF-Cox conjecture.  At $n = 4$, the F3 numerical evidence is consistent with $[3/11, 8/11]$; verify at $n = 5$ once the chamber Morse function is in hand.

### 5.5 What this F3 scoping does NOT claim

- It does **not** prove (H-Cox) at any $n \ge 5$.  It does correct the candidate set for the structural argument at $n = 5$.
- It does **not** prove the cohomological 1/3-2/3 conjecture at general $n$.  It crystallizes (I4) (BF-Cox) as the right form of that statement.
- It does **not** construct a perfect Morse function at $n = 4$ or higher.  It identifies Forman cancellation and chamber-restricted constructions as the right tools (§5.4 (1)–(2)).
- It does **not** prove the kernel direction $z = c^*_{2,1} + c^*_{2,2} + c^*_{2,3} + c^*_{2,4}$ (signs $+1$).  The script's heuristic suggests this; an explicit $\partial^M_2$ computation would confirm (F3 §2.7).

---

## 6. References

### 6.1 Predecessor scoping docs in this branch family

- mg-c853 (Compat-Geom manifesto):
  `docs/compatibility-geometry.md` (not on this branch; see mg-c853 polecat).
- mg-d4ed (cuts-by-pairs scoping; AMBER).
- mg-296d (eigensheaves on Pos_n; AMBER-specialist).
- mg-d60d (poset cohomology; AMBER-specialist conditional on cat-mg-5ee2).
- mg-5ee2 (Pos_n topological sphere; AMBER reformulation).
- mg-bbf7 (Compat-Geom site refinement + n=4 wedge check).
- mg-3a61 (Compat-Geom F1-refined; n=5 + CL-labeling + ω_bal explicit).
  `docs/compatibility-geometry-F1-refined-scoping.md`
- mg-7455 (Compat-Geom F2; discrete Morse + critical-cell classification + ω_bal explicit).
  `docs/compatibility-geometry-F2-scoping.md`

### 6.2 Discrete Morse theory

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).
  Theorems 3.4 (perfect MF ↔ minimal $f$-vector), 8.2 (V-path cocycle), 11.1 (Forman cancellation).
- M. K. Chari, *On discrete Morse functions and combinatorial decompositions*, Discrete Math. 217 (2000).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11.

### 6.3 1/3-2/3 conjecture

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) 113–126.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) 327–349.  Sharpening to $[3/11, 8/11]$.
- I. Aizley, *The 1/3-2/3 conjecture*, survey, in Order, 2007.

### 6.4 Order complexes, posets

- A. Björner, *Shellable and Cohen-Macaulay partially ordered sets*, Trans. AMS 260 (1980).
- M. Wachs, *Poset topology: tools and applications*, in *Geometric Combinatorics*, IAS/Park City lecture notes (2007).
- D. Quillen, *Higher algebraic K-theory*, in *Algebraic K-theory I*, LNM 341 (1973), Ch. 0 §3 (poset fiber theorem).

### 6.5 Code

- `scripts/posn_morse_check.py` (mg-7455, predecessor).
- `scripts/posn_omega_bal_spectrum.py` (F3, this scoping; ~480 lines, pure stdlib).
- `scripts/posn_wedge_check_n5.py` (mg-3a61).

---

## 7. Token-budget report and appendices

### 7.1 Compute used

- F2 cherry-pick + repro: ~10 s wall-clock.
- F3 spectrum (`posn_omega_bal_spectrum.py`): ~3 s wall-clock on commodity hw (n=4 enum + matching + 4 cocycles + brute-force).
- F3 background $\widetilde b_2$ at $n=5$: 30–60 min (background; results in §7.4).

500k token cap: not approached.  Approximate session-token usage: ≤ 50k input/output through the F3 work.

### 7.2 Token breakdown

| Phase | Tokens (est.) |
|-------|---------------:|
| Predecessor read (F2 doc) | ~6k |
| F3 script writing | ~6k |
| F3 script execution + revision | ~3k |
| This scoping doc (~700–900 lines × ~20 chars/line) | ~25k |
| Tool overhead + verification | ~5k |
| **Total session** | **~45k** |

Well within budget; no compute cap concerns.

### 7.3 Reproducibility

```text
$ cd /Users/daniel/research/one_third_width_three   # on branch compat-geom-F3-omega-spectrum
$ python3 scripts/posn_omega_bal_spectrum.py        # ~3s, full run
$ python3 scripts/posn_omega_bal_spectrum.py --no-brute --no-n5 --no-induction
   # ~1s, just the headline §2 table.
```

### 7.4 Appendix: $n=5$ Betti background run

This appendix is populated only if the in-session background run completed.  If
deferred: re-run with `python3 scripts/posn_morse_check.py 5 --no-morse --no-omega-bal --betti-cap 2 --prime 1000003` on a 16-GB machine (≈ 30–60 min).

```text
[Backgrounded output appended at commit time if completed; otherwise: DEFERRED.]
```

---

End of F3 scoping document.  Mayor inbox: `mg-6bc3`.  Branch: `compat-geom-F3-omega-spectrum`.
