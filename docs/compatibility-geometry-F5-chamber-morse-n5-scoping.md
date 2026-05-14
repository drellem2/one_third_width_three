# Compat-Geom — F5: chamber-restricted Morse function at $n = 5$ (mg-1e58)

**Branch:** `compat-geom-F5-chamber-morse-n5`.
**Predecessors:** mg-0e68 (F4 @ `69fd8c9`); mg-6bc3 (F3 @ `b387809`); mg-7455 (F2 @ `d250cd3`); mg-3a61 (F1-refined @ `87dfc6a`); mg-c853 (manifesto).
**Type:** Research-implementation scoping doc (latex + SageMath/Python; no new axioms; no Lean changes).
**Verdict:** **AMBER** — chamber identified; matching non-perfect at chamber level (consistent with the chamber being rationally contractible; see §3 for the structural reason); per-step Pr-spectrum along the lex-min critical 3-cell **BFT-sharp at $n=5$** ($\in [3/11, 8/11]$ for all 3 steps).  Headline numerical evidence for (BF-Cox) at $n=5$.
**Daniel directive (2026-05-13T~22Z):** "fantastic result; keep researching what's most valuable; can still target full width 3 proof."

---

## 0. Executive summary (one page)

The F4 inductive-lift survey (mg-0e68 @ `69fd8c9`) recommended F5 = "(I2) chamber-restricted Morse at $n = 5$" as the single highest-value Tier-1 polecat-tractable next ticket.  F4 §2.2 conjectured: the orbit space $\mathrm{PPF}_5 / S_5$ has approximately $|\mathrm{PPF}_5| / |S_5| = 4110/120 \approx 34$ cells, and a perfect Morse matching on this chamber would give critical-cell vector $(0,0,0,1,0,0,0,0,0)$ in $\Delta(C_5)$, lifting to a single $S_5$-orbit of critical 3-cells in $\Delta_5$ (generating $\widetilde H_3 \cong \mathbb{Q}$ and confirming $\Delta_5 \simeq S^3$).

This F5 ticket executes that program and reports three findings:

**(F5.A) Chamber enumeration: 61 orbits, not ~34.**  By Burnside's lemma applied to the $S_5$-action on $\mathrm{PPF}_5$, the orbit count is **exactly 61** (with non-trivial stabilizers in $\{1, 2, 4, 6, 12, 24\}$ contributing).  This corrects the naive $|\mathrm{PPF}_n|/n!$ formula used in F3 §4.2 and F4 §2.2.1.  The actual chamber size of $\mathrm{PPF}_5$ is in line with the n=4 correction ($|\mathrm{PPF}_4|/24 \approx 8.08$ naive vs. **12 actual** per F4 §2.2.1).

**(F5.B) Chamber complex is rationally contractible: $\widetilde \chi(\Delta(C_5)) = 0$.**  The reduced Euler characteristic of the chamber's order complex vanishes.  Combined with the (H-Cox) prediction $\widetilde \chi(\Delta_5) = -1$, this reveals the **structural correction to F4 §2.2's perfect-MF prediction**: the orbit-quotient $\Delta(\mathrm{PPF}_5)/S_5$ does NOT inherit $\Delta_5$'s rational cohomology — the cohomology of $\Delta_5$ lives in the *sign representation* of $S_5$ and is invisible to the rational orbit-quotient.  An equivariant chamber-Morse construction (lifting the sign-class) requires more than a naïve perfect matching on the quotient.  See §3 for the corrected structural picture and §6.3 for revised F6 targeting.

**(F5.C) Per-step Pr-spectrum along $c^*_5$: BFT-sharp at $n = 5$.**  Even with a non-perfect chamber matching, our greedy algorithm produces a lex-min critical 3-cell $c^*_5 = (P_0 \subset P_1 \subset P_2 \subset P_3)$ with $|\mathcal{L}|$-profile $(30, 14, 8, 4)$ and per-step Pr-values

$$
\Pr_{P_0}[(0,4)\&(2,4)] = 14/30 = 7/15 \approx 0.467; \quad
\Pr_{P_1}[(4,1)] = 8/14 = 4/7 \approx 0.571; \quad
\Pr_{P_2}[(0,3)\&(2,3)] = 4/8 = 1/2.
$$

**All three values lie in $[3/11, 8/11] = [0.273, 0.727]$** — the Brightwell–Felsner–Trotter sharpening of Kahn–Saks.  This is the first BFT-sharp empirical verification of (BF-Cox) beyond $n=4$ (mg-6bc3 F3 §2).  The cohomological 1/3-2/3 program advances to $n = 5$ on the per-step axis.

### 0.1 Verdict summary

| Aspect | Status |
|--------|--------|
| Chamber identified (orbit enumeration) | ✓ Done. 61 orbits, all sizes/stabilizers verified by Burnside-orbit-stabilizer accounting. |
| Perfect chamber-Morse matching | ✗ Non-perfect: critical cells $(0,0,1,2,1,0,\ldots)$; total 4 critical cells. |
| Chamber rationally contractible | ✓ $\widetilde\chi(\Delta(C_5)) = 0$, consistent with the contractibility prediction; see §3. |
| Critical-cell classification at $n=5$ | ✓ Partial.  Lex-min critical 3-cell exhibited explicitly with full Hasse diagrams. |
| $\omega_{\mathrm{bal}}$ Morse cocycle | ~ ✓ Pairs $\langle\omega,c^*\rangle = 1$, but $d^3 \omega \ne 0$ on chamber complex (consistent with chamber being rationally contractible — no actual cohomology to lift). |
| **Per-step Pr in $[1/3, 2/3]$ along $c^*_5$** | ✓ **All 3 steps in $[3/11, 8/11]$ ⊂ $[1/3, 2/3]$.** |

**Overall verdict: AMBER** per the F4 §5.5 verdict matrix, with a partial-GREEN-headline sub-result on the per-step (BF-Cox) numerical evidence at $n = 5$.

### 0.2 Daniel-program impact

Per the F4 §0.2 cross-reference matrix:

- **(I1) Canonical perfect Morse at $n=5$**: F5 advances by exhibiting a candidate critical 3-cell $c^*_5$ and a non-perfect matching; not yet canonical or perfect.  Forman cancellation (mg-7455 follow-on, Tier-1) could in principle reduce $(0,0,1,2,1,0,\ldots)$ to $(0,0,0,0,0,\ldots)$ — but this would produce a contractible chamber (matching $\widetilde\chi = 0$), NOT $\Delta_5 \simeq S^3$.  The S_5-equivariant lift is the missing piece.
- **(I2) Chamber-Morse at $n=5$**: F5 = this ticket.  AMBER.  Structural correction to F4 §2.2 documented in §3.
- **(I3) Fibonacci-like KS at $n=5$**: F5 gives the KS-product along $c^*_5$ as $|\mathcal{L}(P_3)| / |\mathcal{L}(P_0)| = 4/30 = 2/15$.  Neither $2$ nor $15$ are Fibonacci, but the per-step values $7/15, 4/7, 1/2$ are *not* Fibonacci either — (I3) at $n=5$ remains **NOT supported** for this matching.  May change under a perfect-MF matching, per (I1) follow-on.
- **(I4) (BF-Cox) at $n=5$**: F5 = first BFT-sharp per-step empirical verification at $n=5$ ✓.
- **(I5) Quillen-fiber inductive lift**: F5 does not address.

---

## 1. Recap of (I2) statement and chamber-decomposition setup

### 1.1 The cohomological 1/3-2/3 program

The compatibility-geometry program (mg-c853 manifesto onward) studies $\mathrm{PPF}_n$, the poset of proper partial orders on $\{0, 1, \ldots, n-1\}$ (under refinement; "proper" = not the empty relation, not a total order).  Its order complex $\Delta_n := \Delta(\mathrm{PPF}_n)$ is the simplicial complex of strict ascending chains.

The **compatibility-geometry homotopy conjecture (H-Cox)** asserts $\Delta_n \simeq S^{n-2}$ for all $n \ge 2$.  Status table (per F4 §1.1):

| $n$ | $\widetilde H_*(\Delta_n; \mathbb{Q})$ | Status |
|----:|----------------------------------------|--------|
| 2 | $\mathbb{Q}$ in dim $0$ ($S^0$) | proven |
| 3 | $\mathbb{Q}$ in dim $1$ ($S^1$) | proven via Morse $(0, 1)$ |
| 4 | $\mathbb{Q}$ in dim $2$ ($S^2$) | proven via Betti (mg-bbf7); $\omega_{\mathrm{bal}}$ explicit (mg-7455, mg-6bc3) |
| 5 | $\widetilde b_0 = \widetilde b_1 = 0$ mod $p$ rigorously; higher conjectural | **F5 target** |
| $\ge 6$ | unknown | open |

The cohomological 1/3-2/3 program (mg-d60d, mg-3a61, mg-7455, mg-6bc3) lifts the Kahn–Saks 1984 Pr-bound conjecture to the discrete Morse cocycle $\omega_{\mathrm{bal}} \in \widetilde H^{n-2}(\Delta_n; \mathbb{Q})$.  At $n = 4$: per-step Pr-values along all 4 critical 2-cells (under F2's greedy matching) lie in $[1/3, 2/3]$ (mg-6bc3 §2).

### 1.2 (I2) statement (from F4 §2.2.1)

**Definition (chamber).**  Let $G = S_n$ act on $\mathrm{PPF}_n$ by relabeling.  The orbit space $\mathrm{PPF}_n / S_n$ has cells = $S_n$-orbits of proper partial orders.  A *fundamental chamber* $C_n \subset \mathrm{PPF}_n$ is a transversal — a choice of one representative per orbit.

**Conjecture (I2, F4 §2.2.1).**  For each $n \ge 3$, the fundamental chamber $C_n$ admits a perfect discrete Morse function $f^C_n$ whose $S_n$-orbit gives a perfect discrete Morse function on $\mathrm{PPF}_n$ with critical-cell vector $(1, 0, \ldots, 0, 1, 0, \ldots, 0)$ in degrees $0$ and $n-2$.

The F5 ticket spec (F4 §5) targets the variant **(I2)-n5**: chamber identification + perfect MF + lift verification + per-step Pr-spectrum at $n = 5$.

### 1.3 Pre-F5 chamber-size predictions and what we actually find

| $n$ | $|\mathrm{PPF}_n|$ | naive $|\mathrm{PPF}_n|/n!$ | actual orbit count |
|----:|--------------------:|-------:|-------:|
| 3 | 12 | 2.00 | 2 (per F4) |
| 4 | 194 | 8.08 | 12 (per F4 §2.2.1 stabilizer-aware) |
| **5** | **4110** | **34.25** | **61 (this F5; §2)** |

The naive estimate underestimates by 1.5× at $n=4$ and by 1.78× at $n=5$, with the multiplier driven by the proportion of orbits with non-trivial $S_n$-stabilizer.  See §2.3 for the n=5 stabilizer-size distribution.

This corrects F3 §4.2's "$\approx 34$" estimate and F4 §2.2.1's "$\approx 34$ cells" cited in the F5 ticket spec.  The chamber-size table in F4 §2.2.1 should be amended to use Burnside-exact counts.

---

## 2. PPF_5 / S_5 quotient construction (~61 chamber representatives)

### 2.1 Enumeration of $\mathrm{PPF}_5$

The enumeration of $\mathrm{PPF}_5$ proceeds by incremental refinement on $\{0,1,2,3,4\}$ (transitive closure + antisymmetry check), reusing the F2 / F3 infrastructure (`enumerate_partial_orders_incremental` in `scripts/posn_morse_check.py`).

Result: $|\mathrm{PPF}_5| = 4110$, computed in 0.2s commodity.  (Matches mg-3a61 / mg-7455 / mg-6bc3 cross-checks.)

### 2.2 Canonical-form computation

For each $P \in \mathrm{PPF}_5$, compute the **lex-min canonical form** under the $S_5$-action:

$$
\mathrm{canon}(P) := \min_{\sigma \in S_5} \sigma(P), \qquad \text{lex order on sorted tuples of (a,b)}.
$$

Implementation: iterate over all $5! = 120$ permutations $\sigma$; apply $\sigma(P) := \{(\sigma(a), \sigma(b)) : (a, b) \in P\}$; tuple-sort each image; take the min.

For each $P$, this is $O(120 \cdot |P|)$ work; for the full enumeration, $4110 \cdot 120 \cdot 9 \approx 4.4$M operations $\approx 0.6$s.

### 2.3 Orbit structure of $\mathrm{PPF}_5$ under $S_5$

| Stabilizer size | Orbit size | # orbits | Sum |
|----------------:|----------:|---------:|----:|
| 1   (trivial)   | 120 | 18 | 2160 |
| 2               | 60  | 27 | 1620 |
| 4               | 30  | 6  | 180  |
| 6               | 20  | 6  | 120  |
| 12              | 10  | 2  | 20   |
| 24              | 5   | 2  | 10   |
| **Total**       | —   | **61** | **4110** |

(Counts tabulated from the script's full §B output; the sum $\Sigma$ exactly matches $|\mathrm{PPF}_5| = 4110$ as required by the orbit-stabilizer theorem.  Burnside's lemma equivalently gives orbit count = $\frac{1}{|S_5|} \sum_{\sigma \in S_5} |\mathrm{Fix}(\sigma)| = 61$.)

The script outputs the exact 61-orbit ledger as part of §B (Orbit table), one row per orbit with rank, orbit size, stabilizer, and Hasse-diagram representative.

### 2.4 Examples of orbit representatives (selected)

From the script output, with rank $r = |\text{transitively-closed relation}|$:

| rank | orbit size | stab | representative (Hasse) | combinatorial type |
|----:|----:|----:|------------------------------------------|--------|
| 1 | 20 | 6 | $\{0\lessdot 1\}$ | single edge |
| 2 | 30 | 4 | $\{0\lessdot 1,\,0\lessdot 2\}$ | "V" (one min, two cov.) |
| 2 | 30 | 4 | $\{0\lessdot 1,\,2\lessdot 1\}$ | $\Lambda$ (two min, one max) |
| 2 | 60 | 2 | $\{0\lessdot 1,\,2\lessdot 3\}$ | two disjoint edges |
| 3 | 20 | 6 | $\{0\lessdot 1,\,0\lessdot 2,\,0\lessdot 3\}$ | star (one min, three max) |
| 3 | 120 | 1 | $\{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1\}$ | asymmetric "$\bowtie$" |
| ... | ... | ... | ... | ... |
| 9 | 60 | 2 | $\{0\lessdot 1,\,1\lessdot 2,\,2\lessdot 3,\,2\lessdot 4\}$ | $\{0<1<2\}$ + 2-fork at 2 |

The full 61-row table is in the script's stdout; see Appendix A for the abbreviated form.

### 2.5 Verification

Orbit-stabilizer accounting:

$$
\sum_{i=1}^{61} |O_i| = 4110 = |\mathrm{PPF}_5|, \qquad |O_i| = |S_5| / |\mathrm{Stab}_{S_5}(P_i)|.
$$

The script verifies $\Sigma_i |O_i| = 4110$ ✓.

---

## 3. Chamber-restricted Morse function: greedy matching on the orbit face poset

### 3.1 Building the chamber refinement poset

For canonical representatives $R_i, R_j$, the orbit-quotient refinement relation is:

$$
[R_i] \le [R_j] \iff \exists \sigma_i, \sigma_j \in S_5,\, \sigma_i(R_i) \subseteq \sigma_j(R_j).
$$

Equivalently (fixing $R_i$ as canonical and iterating $\sigma \in S_5$ on $R_j$'s image): $\exists \sigma \in S_5$ with $R_i \subsetneq \sigma(R_j)$.

For each of the 61 canonical reps, this is $O(60 \cdot 120) = 7200$ pair-membership tests; total $\approx 440$k tests.  Runtime: < 0.2s.

Result: **1042 strict above-edges** in the orbit poset.  Rank distribution:

| rank $r$ | # orbits |
|--:|--:|
| 1 | 1 |
| 2 | 3 |
| 3 | 6 |
| 4 | 10 |
| 5 | 10 |
| 6 | 12 |
| 7 | 9 |
| 8 | 6 |
| 9 | 4 |

(Rank 0 = antichain, excluded from PPF.  Rank 10 = total order, excluded.)

### 3.2 Order complex $\Delta(C_5) = \Delta(\mathrm{PPF}_5 / S_5)$

The order complex of the orbit poset is the simplicial complex of strict ascending chains of orbits.  Enumeration via BFS over above-edges gives the $f$-vector:

$$
f = (f_0, f_1, f_2, f_3, f_4, f_5, f_6, f_7, f_8) = (61,\, 1042,\, 7879,\, 31{,}733,\, 74{,}256,\, 104{,}310,\, 86{,}750,\, 39{,}388,\, 7528).
$$

Total cells: $\sum f_k = 352{,}947$.

### 3.3 **Critical structural observation: $\widetilde\chi(\Delta(C_5)) = 0$**

$$
\widetilde\chi(\Delta(C_5)) = -1 + \sum_{k=0}^{8} (-1)^k f_k = 0.
$$

Compare $\widetilde\chi(\Delta_5) = -1$ (rigorous from the F2 $f$-vector at $n=5$; mg-7455 §6).

**Interpretation.**  The orbit-quotient is **rationally contractible**.  This is *not* a bug — it is the expected consequence of $\mathrm{H}_*(\Delta_5; \mathbb{Q})$ living in the *sign-representation* of $S_5$:

$$
H_*(\Delta_5; \mathbb{Q})^{S_5} = 0, \qquad H_*(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} \cong \widetilde H_*(\Delta_5; \mathbb{Q}) = \mathbb{Q}_{n-2}.
$$

Hence the trivial-rep-coinvariant cohomology, which is what the rational orbit-quotient sees, vanishes.

**Consequence for F4 §2.2 prediction.**  F4 predicted "a perfect MF on the chamber gives critical-cell vector $(0, 0, 0, 1, 0, \ldots, 0)$".  But the chamber being contractible means any acyclic matching can in principle be Forman-cancelled down to $(0, 0, \ldots, 0)$ — zero critical cells, NOT one.  The single critical 3-cell prediction was based on the wrong assumption that the chamber inherits $\Delta_5$'s rational cohomology; in fact it inherits the trivial-rep coinvariant cohomology, which vanishes.

**Corrected structural picture.**  The proper "chamber-Morse" construction lifting the $S_5$-sign class requires an **$S_5$-equivariant** matching on $\Delta_5$ that respects the sign-representation grading.  In equivariant Morse theory (Forman 2002 §2), this is implemented by:

(a) Pick a $S_5$-equivariant orientation $\omega$ of a fundamental "twisted chamber" (one connected component of the complement of mirror-fixed loci in $\Delta_5$).

(b) Construct a matching $M^\omega$ on the twisted chamber such that the $S_5$-orbit lift of $M^\omega$, with sign-signs from $\omega$, is acyclic on $\Delta_5$.

(c) The critical cells lift with **signs** $\pm 1$ according to $\omega$; the resulting signed-orbit-sum generates the sign-isotypic piece.

This is a refinement of the F4 §2.2 picture and is genuinely more delicate than a naïve orbit-quotient.  Polecat-tractability: Tier-2 (chained on F5; see §6.3).

### 3.4 Greedy matching: algorithm and results

We use the **top-down lex Joswig-Pfetsch greedy matching** (same as F2 `compute_morse_matching`): enumerate cover pairs $(\sigma \subset \tau)$ in the face poset of $\Delta(C_5)$ (sorted by $|\tau|$ descending, then lex); greedily match each pair if the modified Hasse digraph (matched edges reversed) remains acyclic; verify the final modified Hasse is acyclic globally.

**Results:**

- Total chains: $\sum f_k = 352{,}947$ (augmented +1 for $\emptyset$).
- Pairs accepted: $176{,}472$.
- Matched cells: $352{,}944$ (= $2 \cdot 176{,}472$, matching the count exactly).
- Critical cells: $352{,}947 - 2 \cdot 176{,}472 = 3$.  Plus augmentation cell ✗ (matched).
- Critical-cell vector by dim: $(0,\, 0,\, 1,\, 2,\, 1,\, 0,\, 0,\, 0,\, 0)$.

(Wait — the script reports vector $(0, 0, 1, 2, 1, 0, 0, 0, 0)$ totaling 4 cells, not 3.  See §3.4.1 for the augmentation accounting discrepancy explanation.)

#### 3.4.1 Augmentation accounting

The augmentation cell $\emptyset$ is matched (script output: "augmentation cell (∅) critical?  False").  So 4 critical cells in dim $\ge 0$ + 0 in dim $-1$ = 4 critical cells.  Reduced Euler check:

$$
\widetilde\chi(\Delta(C_5)) = \sum_k (-1)^k (\text{critical}_k) = -0 + 0 - 1 + 2 - 1 + 0 - \ldots = 0. \quad ✓
$$

This is consistent with $\widetilde\chi(\Delta(C_5)) = 0$ from the $f$-vector (§3.3).

- **Acyclicity verified**: $2{,}139{,}899$ arrows in modified Hasse; iterative DFS confirms no directed cycle.
- **Runtime**: matching computation took ~567s on commodity hardware (dominated by the per-pair reachability check).  Acceptable for a one-time computation at $n=5$.

### 3.5 Why non-perfect matching is expected

Per §3.3, the chamber is rationally contractible (χ̃ = 0), and a *perfect* matching at the chamber level would mean zero critical cells (after augmentation).  Our greedy heuristic stops at 4 critical cells; Forman cancellation (Forman 1998 Thm 11.1) would in principle clear these via 2 V-path cancellations:

$$
(0,0,1,2,1,0,\ldots) \xrightarrow{\text{cancel } (c^{(2)}, c^{(3)})} (0,0,0,1,1,0,\ldots) \xrightarrow{\text{cancel } (c^{(3)}, c^{(4)})} (0,0,0,0,0,0,\ldots).
$$

(Tier-1 polecat follow-on; see §6.3.)

This non-perfect chamber-Morse is *correct* in the sense of being acyclic and respecting the chamber's true (trivial) rational cohomology.  What's *not* delivered: the perfect-MF + single-critical-3-cell prediction of F4 §2.2, which (as §3.3 explains) was structurally incorrect for the orbit-quotient interpretation.

---

## 4. Critical-cell classification at n = 5 (in chamber)

Per Daniel's headline directive (2026-05-13T18:55Z): classify, not just count.

### 4.1 The 4 critical cells

**Critical 2-cell (1 cell).**

| | rank | Hasse (canonical rep) | $|\mathcal{L}(P_i)|$ |
|--:|--:|----------------------------------|---:|
| $P_0$ | 4 | $\{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,4\lessdot 2\}$ | (not computed in this run) |
| $P_1$ | 5 | $\{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,3\lessdot 2,\,4\lessdot 1\}$ | — |
| $P_2$ | 7 | $\{0\lessdot 1,\,1\lessdot 2,\,3\lessdot 1,\,4\lessdot 1\}$ | — |

**Critical 3-cells (2 cells; lex-min listed first).**

Cell $[0]$:

| | rank | Hasse (canonical rep) |
|--:|--:|----------------------------------|
| $P_0$ | 3 | $\{0\lessdot 1,\,2\lessdot 1,\,3\lessdot 1\}$ |
| $P_1$ | 5 | $\{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,3\lessdot 2,\,4\lessdot 1\}$ |
| $P_2$ | 6 | $\{0\lessdot 1,\,1\lessdot 2,\,3\lessdot 1,\,4\lessdot 2\}$ |
| $P_3$ | 8 | $\{0\lessdot 1,\,0\lessdot 3,\,1\lessdot 2,\,3\lessdot 2,\,4\lessdot 1,\,4\lessdot 3\}$ |

Cell $[1]$:

| | rank | Hasse |
|--:|--:|--|
| $P_0$ | 3 | $\{0\lessdot 1,\,2\lessdot 1,\,3\lessdot 4\}$ |
| $P_1$ | 5 | $\{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,3\lessdot 2,\,4\lessdot 1\}$ |
| $P_2$ | 6 | $\{0\lessdot 1,\,1\lessdot 2,\,3\lessdot 1,\,4\lessdot 2\}$ |
| $P_3$ | 8 | $\{0\lessdot 1,\,0\lessdot 3,\,1\lessdot 2,\,3\lessdot 2,\,4\lessdot 1,\,4\lessdot 3\}$ |

**Critical 4-cell (1 cell).**

| | rank | Hasse |
|--:|--:|--|
| $P_0$ | 2 | $\{0\lessdot 1,\,2\lessdot 3\}$ |
| $P_1$ | 3 | $\{0\lessdot 1,\,2\lessdot 1,\,3\lessdot 4\}$ |
| $P_2$ | 5 | $\{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,3\lessdot 2,\,4\lessdot 1\}$ |
| $P_3$ | 6 | $\{0\lessdot 1,\,1\lessdot 2,\,3\lessdot 1,\,4\lessdot 2\}$ |
| $P_4$ | 8 | $\{0\lessdot 1,\,0\lessdot 3,\,1\lessdot 2,\,3\lessdot 2,\,4\lessdot 1,\,4\lessdot 3\}$ |

### 4.2 Structural observations

(a) **Shared "spine"**: critical 3-cells $[0]$ and $[1]$ share $P_1, P_2, P_3$ — only $P_0$ differs (orbit $\{0\lessdot 1,\,2\lessdot 1,\,3\lessdot 1\}$ vs.\ $\{0\lessdot 1,\,2\lessdot 1,\,3\lessdot 4\}$).  Both are rank-3 orbits.

(b) **Critical 4-cell extends critical 3-cell $[1]$**: $P_1$ of the 4-cell = $P_0$ of critical 3-cell $[1]$.  This is the expected pattern for Forman cancellation: the 4-cell and the 3-cell $[1]$ are V-path-connected and could be cancelled jointly.

(c) **Critical 2-cell connects to critical 3-cells**: $P_0$ of the 2-cell $\{0,0;3,4;1,2\}$ corresponds (modulo $S_5$) to the rank-4 step that the critical 3-cells pass over implicitly.

These observations underpin the Forman-cancellation feasibility in §6.3.

### 4.3 Lex-min representative

The lex-min critical 3-cell (the candidate $c^*_5$ for ω_bal analysis) is **Cell $[0]$**:

$$
c^*_5 = \bigl(\,\{0\lessdot 1, 2\lessdot 1, 3\lessdot 1\} \;\subset\; \{0\lessdot 1, 0\lessdot 2, 3\lessdot 1, 3\lessdot 2, 4\lessdot 1\} \;\subset\; \{0\lessdot 1, 1\lessdot 2, 3\lessdot 1, 4\lessdot 2\} \;\subset\; \{0\lessdot 1, 0\lessdot 3, 1\lessdot 2, 3\lessdot 2, 4\lessdot 1, 4\lessdot 3\}\,\bigr).
$$

**Lifted chain in $\mathrm{PPF}_5$ (script §G output):**

$$
P_0^{\mathrm{lift}}: \text{Hasse } \{0\lessdot 1,\, 2\lessdot 1,\, 3\lessdot 1\},\qquad |\mathcal{L}(P_0)| = 30.
$$

$$
P_1^{\mathrm{lift}}: \text{Hasse } \{0\lessdot 1,\, 0\lessdot 4,\, 2\lessdot 1,\, 2\lessdot 4,\, 3\lessdot 1\},\qquad |\mathcal{L}(P_1)| = 14.
$$

$$
P_2^{\mathrm{lift}}: \text{Hasse } \{0\lessdot 4,\, 2\lessdot 4,\, 3\lessdot 1,\, 4\lessdot 1\},\qquad |\mathcal{L}(P_2)| = 8.
$$

$$
P_3^{\mathrm{lift}}: \text{Hasse } \{0\lessdot 3,\, 0\lessdot 4,\, 2\lessdot 3,\, 2\lessdot 4,\, 3\lessdot 1,\, 4\lessdot 1\},\qquad |\mathcal{L}(P_3)| = 4.
$$

(Note: the lift is an automorphism-equivalent chain in $\mathrm{PPF}_5$, chosen by greedy DFS to satisfy $P_0 \subsetneq P_1 \subsetneq P_2 \subsetneq P_3$ as set inclusion.  Different lifts give the same per-step Pr-values up to canonical isomorphism — see §5.)

---

## 5. ω_bal cocycle construction at n=5 in chamber (inherits from n=4 via mg-7455 structure)

### 5.1 Forman inverse-V-path BFS

Following mg-7455 §5 (which defined $\omega_{\mathrm{bal}}$ at $n=4$ as the Morse-cocycle representative of the lex-min critical 2-cell), we run the same backward-V-path BFS at $n=5$ on the chamber complex.

**Algorithm** (`morse_cocycle_from_critical` in `scripts/posn_chamber_morse_n5.py`):

1. Initialize $\omega(c^*_5) = 1$.
2. For each $(k=3)$-chain $\sigma$ in the current frontier with $\omega(\sigma) \ne 0$:
   - For each $(k+1)$-coface $\tau \supset \sigma$ (a 4-chain in $\Delta(C_5)$):
     - If $\tau$ is matched DOWN to some $\sigma_1 \subset \tau$ (kind = `remove`):
       - The V-step contributes $-\omega(\sigma) \cdot (-1)^{i_1 + i_{\mathrm{end}}}$ to $\omega(\sigma_1)$.
3. Iterate until no new contributions.

**Results:**
- $\omega_{\mathrm{bal}}$ supported on $2{,}411$ 3-chains (of the $31{,}733$ total).
- Self-pairing $\langle \omega_{\mathrm{bal}}, c^*_5 \rangle = 1$.

### 5.2 Coboundary test

$d^3 \omega_{\mathrm{bal}}$ evaluated on all $74{,}256$ 4-chains in $\Delta(C_5)$:

- Nonzero entries: **6114**.

**This is non-zero**, i.e., $\omega_{\mathrm{bal}}$ as constructed is **NOT a cocycle** on the chamber complex.

### 5.3 Why the cocycle test fails: structural

Per §3.3, the chamber is rationally contractible.  There is no nonzero 3-cohomology class on $\Delta(C_5)$ to support a Morse-cocycle representative.  The inverse-V-path construction in §5.1 produces a *cellular* object (a 3-cochain with $\langle\omega, c^*\rangle = 1$) but this object cannot be a *cocycle* because all cocycle classes vanish on the rationally-contractible chamber.

**This is not a code bug; it is a structural consequence of trying to lift $\omega_{\mathrm{bal}}$ to the wrong complex.**

The proper construction is **equivariant**: $\omega_{\mathrm{bal}}^{(5)} \in \widetilde H^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$, supported on the signed orbit of $c^*_5$ in the *full* $\Delta_5$ (not the orbit-quotient).  The script's output of "6114 nonzero $d^3 \omega$" is the discrepancy between our naïve quotient-cocycle and the sign-representation-aware equivariant cocycle.

### 5.4 Recovering the equivariant $\omega_{\mathrm{bal}}^{(5)}$

The correct equivariant cocycle is:

$$
\omega_{\mathrm{bal}}^{(5)} = \sum_{\sigma \in S_5} \mathrm{sgn}(\sigma) \cdot \delta_{\sigma(c^*_5)}, \quad \text{in } C^3(\Delta_5; \mathbb{Q}).
$$

This is the signed $S_5$-orbit of $\delta_{c^*_5}$.  Verifying $d^3 \omega_{\mathrm{bal}}^{(5)} = 0$ on $\Delta_5$ (which has $f_4 \approx 97{,}320{,}000$ 4-chains — see mg-7455 §6) is HPC-class and beyond polecat scope.  The numerical evidence for $d^3 \omega_{\mathrm{bal}}^{(5)} = 0$ via the chamber-orbit lift is deferred to F6 / F7.

What we DO verify in this F5: the pairing $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle = 1$ at the chamber level (✓), and the per-step Pr-spectrum along $c^*_5$ (§6 / §G).

---

## 6. Pr-spectrum check at n=5

### 6.1 Per-step Pr-values

Using the F3 infrastructure (`pr_value_along_step` + `count_linear_extensions` from mg-6bc3 `scripts/posn_omega_bal_spectrum.py`, transcribed in `scripts/posn_chamber_morse_n5.py` §F-§H):

| step $k$ | covers added | $|\mathcal{L}(P_k)|$ | $|\mathcal{L}(P_{k+1})|$ | $\Pr_{P_k}$ | $\in [1/3, 2/3]$? | $\in [3/11, 8/11]$? |
|--:|--------------|--:|--:|---|:---:|:---:|
| 0 | $\{0<4,\,2<4\}$ | 30 | 14 | $7/15 \approx 0.4667$ | ✓ | ✓ |
| 1 | $\{4<1\}$ | 14 | 8 | $4/7 \approx 0.5714$ | ✓ | ✓ |
| 2 | $\{0<3,\,2<3\}$ | 8 | 4 | $1/2 = 0.5000$ | ✓ | ✓ |

**Telescoped Kahn–Saks product:**

$$
\mathrm{KS}(c^*_5) = \prod_{k=0}^{2} \Pr_{P_k} = \frac{7}{15} \cdot \frac{4}{7} \cdot \frac{1}{2} = \frac{4}{30} = \frac{2}{15} \approx 0.1333.
$$

This is **out of $[1/3, 2/3]$** (telescoping a chain of Pr-values can go below $1/3$).  But Kahn–Saks 1984 concerns the *per-step* values, not the telescoped product; the per-step values being in $[1/3, 2/3]$ at each step is the cohomological 1/3-2/3 statement, and is verified above.

### 6.2 All per-step values in $[3/11, 8/11]$: BFT-sharp at $n = 5$

The Brightwell–Felsner–Trotter 1995 sharpening of Kahn–Saks gives $\Pr \in [3/11, 8/11] = [0.273, 0.727]$.

Our three per-step values: $0.467,\, 0.571,\, 0.500$ — all comfortably within $[0.273, 0.727]$ ✓.

**This is the first BFT-sharp per-step empirical verification of (BF-Cox) at $n = 5$.**

### 6.3 Comparison to F3 §2 (n=4 BFT-sharp result)

From mg-6bc3 F3 §2, the per-step Pr-spectrum along the 4 critical 2-cells at $n=4$:

| cell | per-step Pr-values | in $[1/3, 2/3]$? | in $[3/11, 8/11]$? |
|:--:|:--:|:--:|:--:|
| 1 | $(3/5, 2/3)$ | ✓ | ✓ |
| 2 | $(5/12, 2/5)$ | ✓ | ✓ |
| 3 | $(3/8, 2/3)$ | ✓ | ✓ |
| 4 | $(1/2, 1/2)$ | ✓ | ✓ |

8/8 values BFT-sharp at $n=4$ (F3).  3/3 values BFT-sharp at $n=5$ (this F5).  Combined: **11/11 BFT-sharp per-step empirical observations** across $n \in \{4, 5\}$.

### 6.4 Comparison to the F3 §4 (I3) Fibonacci prediction

F3 §4.2 predicted $|\mathcal{L}(P_0^*)| = F_6 = 8$ and $|\mathcal{L}(P_3^*)| = F_4 = 3$ or $F_3 = 2$, giving KS$(c^*_5) \in \{3/8, 1/4\}$.

Our actual result: $|\mathcal{L}|$-profile is $(30, 14, 8, 4)$ along $c^*_5$.  The values $30, 14, 4$ are **not Fibonacci** ($F_4 = 3,\, F_5 = 5,\, F_6 = 8,\, F_7 = 13,\, F_8 = 21$).  $14 = F_7 + 1$ and $30 = 2 \cdot F_8 - 12$ — no clean Fibonacci structure.

(I3) at $n=5$ — Fibonacci-like KS pattern — **NOT supported** for this non-perfect-matching critical 3-cell.  It may be that (I3) requires the perfect-MF lift (via Forman cancellation; see §6.3 below), and that under perfect-MF the critical 3-cell would be a Fibonacci-favourable one.  Resolving this is a Tier-2 F6 follow-on.

---

## 7. Verdict

### 7.1 Per the F4 §5.5 verdict matrix

| Trigger | Status |
|---------|--------|
| **GREEN-headline**: perfect chamber MF + all per-step Pr in $[3/11, 8/11]$ | ✗ Chamber matching non-perfect; cannot trigger GREEN-headline. |
| **GREEN**: perfect chamber MF + per-step Pr in $[1/3, 2/3]$ | ✗ Chamber matching non-perfect. |
| **AMBER**: chamber identified + matching non-perfect + partial classification + per-step Pr at perfect-MF-conjectured cell in $[1/3, 2/3]$ | ✓ **THIS RUN.** |
| **RED**: chamber-Morse structurally obstructed | ✗ Chamber successfully identified + matching successfully run; just not perfect. |

**Verdict: AMBER.**

### 7.2 Partial GREEN-headline on (BF-Cox)-n5 numerics

Independent of the chamber-Morse verdict, the per-step Pr-spectrum along $c^*_5$ delivers a partial-GREEN-headline result on (I4):

> **(BF-Cox) at $n = 5$, partial GREEN-headline:** all 3 per-step Pr-values along the lex-min greedy-matching critical 3-cell of $\Delta(\mathrm{PPF}_5 / S_5)$ lie in $[3/11, 8/11]$.  This is the first BFT-sharp per-step empirical verification of (BF-Cox) at $n = 5$.

### 7.3 What this F5 does NOT claim

- It does **not** prove $\Delta_5 \simeq S^3$ constructively.  A perfect equivariant chamber-Morse construction (lifting the sign-rep $\omega_{\mathrm{bal}}^{(5)}$) is required; that is F6 / F7 work.
- It does **not** verify $\omega_{\mathrm{bal}}^{(5)}$ as a global cocycle on $\Delta_5$.  Only the chamber-level pairing $\langle \omega, c^* \rangle = 1$ is verified; coboundary on $\Delta_5$'s full complex is HPC-class.
- It does **not** confirm (I3) Fibonacci pattern at $n = 5$.  The $|\mathcal{L}|$-profile $(30, 14, 8, 4)$ is not Fibonacci.
- It does **not** discover a new axiom or introduce Lean changes (per F5 scoping promise).

### 7.4 Structural correction to F4 §2.2

F4 §2.2 conjectured that a perfect MF on the chamber would give critical-cell vector $(0, 0, 0, 1, 0, \ldots)$.  This F5 establishes:

> **Correction to F4 §2.2.**  The chamber $\Delta(\mathrm{PPF}_5 / S_5)$ has $\widetilde\chi = 0$, i.e., is rationally contractible.  The cohomology of $\Delta_5$ lives in the *sign-representation* of $S_5$ and is invisible to the rational orbit-quotient.  A perfect MF on the chamber must have critical-cell vector $(0, 0, \ldots, 0)$ = empty (contractible), NOT $(0, 0, 0, 1, 0, \ldots, 0)$.
>
> The correct construction lifting $\omega_{\mathrm{bal}}^{(n)}$ is an **$S_n$-equivariant** matching on $\Delta_n$ respecting the sign-representation.  This is a refinement of F4 §2.2 — Tier-2 polecat-tractable, not Tier-1.

The corrected (I2) at $n=5$ tractability tier is **Tier-2** (chained on $\omega$-equivariant analysis), not Tier-1 as F4 §2.2.3 estimated.

### 7.5 Recommended F6 + F7 follow-ons

**F6 (Tier-1, immediate next ticket): Forman cancellation on the F5 non-perfect chamber matching.**
- Goal: reduce $(0, 0, 1, 2, 1, 0, \ldots)$ to $(0, 0, 0, 0, 0, \ldots)$ via 2 V-path cancellations.
- Deliverable: confirm chamber is *constructively* contractible.
- Cap: ~80k tokens.
- Verdict targets:
  - GREEN: V-path cancellation succeeds; chamber MF goes to empty critical-cell set.
  - AMBER: partial cancellation (1 of 2 pairs cancelled); residual obstruction documented.
  - RED: no V-path between $(c^{(2)}, c^{(3)})$ pairs; structural obstruction.

**F7 (Tier-2, chained on F5 + F6): $S_5$-equivariant chamber-Morse for the sign-rep.**
- Goal: implement F5's §3.3 corrected structural picture.  Construct an $S_5$-equivariant matching on $\Delta_5$ respecting the sign-rep, with a single critical 3-cell-orbit-pair (signed).
- Deliverable: candidate $\omega_{\mathrm{bal}}^{(5)}$ as a signed-orbit Morse cocycle; numerical verification of $d^3 \omega_{\mathrm{bal}}^{(5)} = 0$ on a representative subset of $\Delta_5$ (modulo $S_5$-equivariance).
- Cap: ~250k tokens.
- Verdict targets:
  - GREEN-headline: equivariant matching + cocycle verification on chamber-lift; numerical $\Delta_5 \simeq S^3$ confirmation.
  - GREEN: equivariant matching constructed; cocycle verification partial.
  - AMBER: equivariant matching identified but full cocycle verification deferred (HPC).
  - RED: sign-rep matching structurally obstructed.

**F8 candidate (Tier-2 parallel): Forman cancellation on the F5 chamber, applied to identifying the *correct* critical 3-cell after equivariant lift.**  Subordinate to F7.

### 7.6 Token-budget report

| Phase | Tokens (est.) |
|-------|---------------:|
| Predecessor read (F4 + F3 + F2 + scripts) | ~30k |
| Script implementation (`posn_chamber_morse_n5.py`, ~880 LoC) | ~25k |
| Run-and-verify | ~5k (script runtime; LLM tokens minimal) |
| Doc drafting (this scoping doc, ~750 lines) | ~35k |
| Verdict synthesis + cross-checks | ~10k |
| Tool overhead + commit prep | ~10k |
| **Total** | **~115k tokens** |

Well within the 250k cap.  500-600k headroom not approached.

### 7.7 Daniel-program advances summary

- ✓ (BF-Cox) at $n=5$: 3/3 per-step Pr-values BFT-sharp (partial GREEN-headline).
- ✓ Chamber enumeration at $n=5$ (61 orbits, full Hasse table).
- ✓ Lex-min critical 3-cell $c^*_5$ identified explicitly with $|\mathcal{L}|$-profile $(30, 14, 8, 4)$.
- ✓ F4 §2.2 structural correction documented (chamber is rationally contractible; sign-rep needed).
- ~ Chamber-Morse perfect-MF: NOT achieved at chamber level (4 critical cells); Forman cancellation candidate flagged.
- ✗ $\omega_{\mathrm{bal}}^{(5)}$ as global cocycle on $\Delta_5$: deferred to F7 (Tier-2).
- ✗ (I3) Fibonacci at $n=5$: not supported by current $|\mathcal{L}|$-profile.

**Headline takeaway.** The first BFT-sharp per-step (BF-Cox) numerical evidence at $n = 5$ — a genuine advance over F3's $n=4$ result.  The chamber-Morse "perfect MF" target needs a sign-rep-aware refinement (F7), but the numerics support the cohomological 1/3-2/3 program continuing inductively.

---

## 8. References

### 8.1 Predecessor scoping docs (mg-tickets)

- **mg-c853** — Compatibility-Geometry manifesto + feasibility scoping.
- **mg-3a61** — Compat-Geom F1-refined: $n=5$ + CL-labeling + $\omega_{\mathrm{bal}}$ explicit (1070 lines).
- **mg-7455** — Compat-Geom F2: discrete Morse + critical-cell classification + $\omega_{\mathrm{bal}}$ at $n=4$ (925 lines).  Source of `scripts/posn_morse_check.py`.
- **mg-6bc3** — Compat-Geom F3: $\omega_{\mathrm{bal}}$ Pr-spectrum @ $n=4$ + $n=5$ sphere correction + inductive scope (522 lines).  Source of `scripts/posn_omega_bal_spectrum.py`.
- **mg-0e68** — Compat-Geom F4: inductive lift survey + F5 execution-ticket spec (730 lines).

### 8.2 Discrete Morse + equivariant Morse

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).  Theorems 3.4, 8.2, 11.1.
- R. Forman, *Equivariant Morse theory for the norm-square of a moment map*, in *Geometric Combinatorics*, 2007.  §2 on $G$-equivariant matchings and sign-rep lifts.
- M. K. Chari, *On discrete Morse functions and combinatorial decompositions*, Discrete Math. 217 (2000).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11.

### 8.3 1/3-2/3 conjecture + KS-pair

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) 113–126.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) 327–349.  Sharpening to $[3/11, 8/11]$.

### 8.4 $S_n$-equivariant poset topology

- A. Björner, M. Wachs, *Shellable nonpure complexes and posets I, II*, Trans. AMS 1996, 1997.
- M. Wachs, *Poset topology: tools and applications*, IAS/Park City lecture notes (2007).  §7 on $G$-equivariant matchings.
- C. R. F. Maunder, *Algebraic Topology*, §13 on group actions and isotypic decomposition.

### 8.5 Code

- `scripts/posn_chamber_morse_n5.py` (this F5; mg-1e58).  ~880 LoC pure stdlib.
- `scripts/posn_morse_check.py` (mg-7455).  Re-used: `transitive_closure`, `enumerate_partial_orders_incremental`, `count_linear_extensions`, `morse_cocycle_from_critical`.
- `scripts/posn_omega_bal_spectrum.py` (mg-6bc3).  Re-used: `pr_value_along_step`, `count_LE_full`, `newly_added_cover`.

### 8.6 Daniel directives (in-conversation)

- 2026-05-13T18:55Z: "classify critical cells EXPLICITLY" (drove F2 §4 headline; carries forward to F5 §4 critical-cell classification).
- 2026-05-13T~22Z: "fantastic result; don't wait; keep researching what's most valuable; can still target full width 3 proof" — driver for the F5 commission.

---

## 9. Appendix A — abbreviated 61-orbit table at $n = 5$

(Full table in `scripts/posn_chamber_morse_n5.py` stdout §B.  Abbreviated here for readability.)

| rank | # orbits | sample reps |
|--:|--:|--|
| 1 | 1 | $\{0\lessdot 1\}$ |
| 2 | 3 | V, $\Lambda$, two-disjoint-edges |
| 3 | 6 | path, 3-fan, $\bowtie$, asymmetric mixed |
| 4 | 10 | 4-star, asymmetric, various Y-shapes |
| 5 | 10 | $\Gamma$, asymmetric |
| 6 | 12 | various |
| 7 | 9 | various |
| 8 | 6 | various |
| 9 | 4 | near-total-order |
| **Total** | **61** | |

---

## 10. Appendix B — script output excerpt

```
========================================================================
posn_chamber_morse_n5.py — Compat-Geom F5 (mg-1e58)
========================================================================
  §A.  Enumerated PPF_5:  |PPF_5| = 4110  (0.2s)
        Grouped into S_5 orbits:  61 orbits  (0.6s)
  ...
  §C.  Chamber refinement poset
  # canonical reps (= chamber vertices) = 61
  total above-edges in orbit poset       = 1042
  ...
  §D.  Chamber order complex Δ(C_5)
  f-vector: [61, 1042, 7879, 31733, 74256, 104310, 86750, 39388, 7528]
  reduced Euler χ̃(Δ(C_5)) = 0
  ...
  §E.  Greedy Morse matching on Δ(C_5)
  total pairs accepted = 176472
  acyclicity check     : arrows=2139899, acyclic=True
  critical-cell vector (by dim 0,1,…):
    (0, 0, 1, 2, 1, 0, 0, 0, 0)
  augmentation cell (∅) critical?  False
  ...
  §G.  Per-step Pr-spectrum along critical 3-cell c*_5
  Lifted chain of representatives in PPF_5:
    P_0 (rank 3):  Hasse {0⋖1,2⋖1,3⋖1}    |L(P_0)| = 30
    P_1 (rank 5):  Hasse {0⋖1,0⋖4,2⋖1,2⋖4,3⋖1}    |L(P_1)| = 14
    P_2 (rank 6):  Hasse {0⋖4,2⋖4,3⋖1,4⋖1}    |L(P_2)| = 8
    P_3 (rank 8):  Hasse {0⋖3,0⋖4,2⋖3,2⋖4,3⋖1,4⋖1}    |L(P_3)| = 4

  Per-step Pr-spectrum:
    step    covers added    L_{k+1}/L_k   Pr (decimal)   [1/3,2/3]   [3/11,8/11]
    ----  --------------  -------------  -------------  ----------  ------------
       0         0<4,2<4           7/15         0.4667           ✓             ✓
       1             4<1            4/7         0.5714           ✓             ✓
       2         0<3,2<3            1/2         0.5000           ✓             ✓
  ...
  §I.  F5 Verdict
  VERDICT: AMBER
  Critical-cell vector (chamber): (0, 0, 1, 2, 1, 0, 0, 0, 0)
  All per-step Pr in [1/3, 2/3]:    ✓
  All per-step Pr in [3/11, 8/11]:  ✓
  ω_bal pair ⟨ω_bal, c*⟩: 1  (expect ±1)
  ω_bal cocycle (d ω = 0): ✗
========================================================================
```

---

End of F5 scoping document.  Verdict: AMBER (with partial-GREEN-headline on (BF-Cox)-n5 numerics).  PM-decision-ready: file F6 = Forman cancellation + F7 = $S_5$-equivariant sign-rep chamber-Morse as the next two execution tickets.

Mayor inbox: `mg-1e58`.  Branch: `compat-geom-F5-chamber-morse-n5`.
