# Compat-Geom — F6: Forman cancellation on F5 non-perfect matching + BFT extension (mg-8736)

**Branch:** `compat-geom-F6-forman-cancellation`.
**Predecessors:** mg-1e58 (F5 @ `77440bd`); mg-0e68 (F4 @ `69fd8c9`); mg-6bc3 (F3 @ `b387809`); mg-7455 (F2 @ `d250cd3`); mg-c853 (manifesto).
**Type:** Research-implementation scoping doc (latex + Python; no new axioms; no Lean changes).
**Verdict:** **AMBER** — 1 of 4 critical-cell pairs cancelled (V-path length 5; critical 2-cell ↔ critical 3-cell $[1]$); 3 pairs had multiple V-paths (counts 0, 2, 3) and could not be cancelled by Forman's uniqueness criterion.  Final critical-cell vector $(0, 0, 0, 1, 1, 0, \ldots)$ — 2 critical cells remain (one 3-cell, one 4-cell).  BFT extension: **11/12** per-step Pr-values in $[3/11, 8/11]$ across all 4 F5-critical cells.
**Daniel directive (2026-05-13T~22Z, mg-1e58 dispatch):** "fantastic result; keep researching what's most valuable; can still target full width 3 proof."

---

## 0. Executive summary (one page)

The F5 scoping (mg-1e58 @ `77440bd`) ran a greedy Joswig-Pfetsch acyclic matching on the chamber order-complex $\Delta(C_5) = \Delta(\mathrm{PPF}_5 / S_5)$ and obtained:

- **61 orbits** of $S_5$ on $\mathrm{PPF}_5$, with $\widetilde\chi(\Delta(C_5)) = 0$ — the chamber is rationally contractible.
- A **non-perfect** matching with critical-cell vector $(0, 0, 1, 2, 1, 0, \ldots)$ — 4 critical cells: one 2-cell, two 3-cells, one 4-cell.
- Per-step Pr-values along the lex-min critical 3-cell $c^*_5$ **all in $[3/11, 8/11]$** (BFT-sharp; 3/3 per-step values).
- F5 §7.5 flagged F6 = "Forman cancellation on the F5 non-perfect chamber matching" as the **Tier-1 immediate next ticket**.

**F6 = this ticket** executes that follow-on:

**(F6.A) Forman cancellation (Forman 1998 Adv. Math. 134, Thm 11.1).**  We implement the cancellation algorithm: build the modified Hasse digraph $H_M$ from F5's matching $M$, count gradient V-paths between each pair of critical cells of consecutive dimension, and reverse the unique V-paths (where they exist) to obtain a new acyclic matching with fewer critical cells.

**(F6.B) BFT $[3/11, 8/11]$ extension.**  Lift each F5-critical chamber chain to $\mathrm{PPF}_5$, compute its full per-step Pr-spectrum (not just for $c^*_5$ as in F5 §6).  Total: **12 per-step Pr-values** across all 4 F5-critical cells.

### 0.1 Headline results

**(F6.A) Cancellation outcome.**  Of the 4 consecutive-dim critical pairs:

| Pair # | $\dim\sigma$ | $\dim\tau$ | $\sigma$ canonical | $\tau$ canonical | $\#$ V-paths | Unique? |
|--:|:--:|:--:|---|---|:--:|:--:|
| [1] | 2 | 3 | crit 2-cell | crit 3-cell $[0]$ ($=c^*_5$) | 0 | no |
| [2] | 2 | 3 | crit 2-cell | crit 3-cell $[1]$ | **1** | **YES** |
| [3] | 3 | 4 | crit 3-cell $[0]$ | crit 4-cell | 3 | no |
| [4] | 3 | 4 | crit 3-cell $[1]$ | crit 4-cell | 2 | no |

Pair [2] has a **unique gradient V-path of length 5 edges** in $H_M$ — reversed.  Critical 2-cell ↔ critical 3-cell $[1]$ jointly cancelled.

**Critical-cell vector evolution.**
$$
(0,\, 0,\, 1,\, 2,\, 1,\, 0,\, \ldots) \;\xrightarrow{\text{cancel pair [2]}}\; (0,\, 0,\, 0,\, 1,\, 1,\, 0,\, \ldots).
$$

Post-cancellation acyclicity preserved (verified, 2,139,899 arrows, no cycle).  2 critical cells remain: critical 3-cell $[0]$ ($=c^*_5$) and critical 4-cell.  These cannot be cancelled by Forman's uniqueness criterion alone (pair [3] has 3 V-paths).

**(F6.B) BFT extension across all 4 F5-critical cells.**

| Critical cell | $|\mathcal{L}|$-profile | # steps | $\#$ in $[3/11, 8/11]$ | $\#$ in $[1/3, 2/3]$ |
|---|---|:--:|:--:|:--:|
| 2-cell | $(16, 14, 6)$ | 2 | 1/2 | 1/2 |
| 3-cell $[0]$ ($=c^*_5$) | $(30, 14, 8, 4)$ | 3 | 3/3 | 3/3 |
| 3-cell $[1]$ | $(20, 14, 8, 4)$ | 3 | 3/3 | 2/3 |
| 4-cell | $(30, 20, 14, 8, 4)$ | 4 | 4/4 | 3/4 |
| **TOTAL** | | **12** | **11/12** | **9/12** |

**11 of 12 per-step Pr-values lie in $[3/11, 8/11]$.**  The single outlier (dim-2 critical cell, step 0): $\Pr = 7/8 = 0.875$ — beyond $8/11 = 0.\overline{72}$.  This step inserts a single new cover relation $4 \lessdot 1$ on a rank-4 poset of $|\mathcal{L}| = 16$, producing a single-element-in-second-place pair with very high $\Pr$.

The narrower Kahn–Saks $[1/3, 2/3]$ range holds for **9 of 12** per-step values; the 3 additional violations (each $\Pr = 7/10 = 0.7$, in $[3/11, 8/11] \setminus [1/3, 2/3]$) occur at:

- dim-3 cell $[1]$ step 0 (covers added $0 \lessdot 4,\, 3 \lessdot 1$);
- dim-4 cell step 1 (covers added $0 \lessdot 3,\, 2 \lessdot 1$).

These provide explicit examples of Kahn–Saks-violating but BFT-sharp per-step Pr-values arising from the chamber-Morse structure.

### 0.2 Verdict summary

| Aspect | Status |
|--------|--------|
| F5 critical-cell vector reproduced | ✓ $(0, 0, 1, 2, 1, 0, \ldots)$ = 4 critical cells |
| Forman cancellation pairs with unique V-path | 1 of 4 (pair [2]: 2-cell ↔ 3-cell $[1]$, length 5) |
| Final critical-cell vector after iterative cancellation | $(0, 0, 0, 1, 1, 0, \ldots)$ = 2 critical cells |
| Post-cancellation acyclicity preserved | ✓ (2,139,899 arrows, no cycle) |
| BFT-sharp per-step values (extended) | **11/12** in $[3/11, 8/11]$ |
| All per-step values in $[1/3, 2/3]$ (Kahn–Saks) | 9/12 |

**Verdict: AMBER.**  Partial-but-substantive cancellation: chamber matching is one Forman step closer to constructive contractibility, with two pairs of cells remaining that need a different cancellation strategy (e.g., local matching adjustment per Hersh–Welker 2017 §3.2; or rerun with a different greedy ordering — F6' candidate).

### 0.3 Daniel-program impact

Per the F4 §0.2 cross-reference matrix and the F5 §0.2 update:

- **(I1) Canonical perfect Morse at $n=5$.**  F6 advances toward — but does not complete — chamber-level constructive contractibility.  One critical-cell pair successfully cancelled by Forman's classical theorem.  The remaining (3-cell $[0]$, 4-cell) pair has 3 V-paths, requiring a Hersh–Welker matching-local-modification or a different initial greedy ordering.  The structural obstruction is **algorithmic** (greedy choice of M), not topological (since $\widetilde\chi = 0$ guarantees in-principle full cancellation).
- **(I2) Chamber-Morse at $n=5$.**  F6 brings the chamber to within 2 critical cells of perfect-Morse via classical Forman cancellation.
- **(I4) (BF-Cox) at $n = 5$.**  F6 extends BFT-sharpness evidence from 3 per-step values (F5 §6.2) to **12 per-step values across all 4 F5-critical cells**: 11/12 BFT-sharp, 9/12 KS-sharp.  This is the strongest cross-cell numerical signal for (BF-Cox) at $n = 5$ to date.  The 3 KS-violating but BFT-sharp values are notable: they exhibit concrete per-step transitions whose Pr lies in $[2/3, 8/11]$ — the "Kahn–Saks gap" of the BFT bound.

---

## 1. Recap of F5 setup and the F6 commission

### 1.1 F5 chamber-Morse output

Quoting F5 §3.4 (mg-1e58 @ `77440bd`):

> Greedy Joswig-Pfetsch top-down lex matching on $\Delta(C_5)$ (61 vertices, 1042 strict above-edges in the orbit poset, $f$-vector $(61, 1042, 7879, 31733, 74256, 104310, 86750, 39388, 7528)$).
>
> Result: **176,472** matched pairs; **4 critical cells** = one 2-cell, two 3-cells, one 4-cell; modified Hasse acyclicity verified globally (2,139,899 arrows, no cycle).
>
> Critical-cell vector: $(0, 0, 1, 2, 1, 0, 0, 0, 0)$.

F5 §3.5 noted that — since $\widetilde\chi(\Delta(C_5)) = 0$ — a *perfect* matching on the chamber should give zero critical cells.  The 4 critical cells of F5's greedy matching represent a failure of the heuristic (greedy choice of pair-ordering), not a structural obstruction.  Forman cancellation should — in principle — clear these via 2 V-path reversals (one for the (3-cell, 4-cell) pair and one for the (2-cell, 3-cell) pair).

F6 = this ticket = systematic test of that claim.

### 1.2 The 4 F5-critical cells (canonical Hasse forms)

Recall from F5 §4.1:

**Critical 2-cell.**
$P_0 = \{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,4\lessdot 2\}$ (rank 4);
$P_1 = \{0\lessdot 1,\,0\lessdot 2,\,3\lessdot 1,\,3\lessdot 2,\,4\lessdot 1\}$ (rank 5);
$P_2 = \{0\lessdot 1,\,1\lessdot 2,\,3\lessdot 1,\,4\lessdot 1\}$ (rank 7).

**Critical 3-cell $[0]$** (= lex-min $c^*_5$, F5 §4.3).
$P_0$ rank 3 ($\{0\lessdot 1, 2\lessdot 1, 3\lessdot 1\}$), $P_1$ rank 5, $P_2$ rank 6, $P_3$ rank 8.

**Critical 3-cell $[1]$.**  $P_0$ rank 3 ($\{0\lessdot 1, 2\lessdot 1, 3\lessdot 4\}$); $P_1, P_2, P_3$ shared with $[0]$.

**Critical 4-cell.**
$P_0 = \{0\lessdot 1,\,2\lessdot 3\}$ (rank 2);
$P_1 = \{0\lessdot 1,\,2\lessdot 1,\,3\lessdot 4\}$ (rank 3, same as $P_0$ of 3-cell $[1]$);
$P_2$ rank 5; $P_3$ rank 6; $P_4$ rank 8.

### 1.3 Why Forman cancellation is the right next step

Three reasons (F5 §3.5 + §7.5):

1. **Topological consistency.**  $\widetilde\chi(\Delta(C_5)) = 0$ is *prima facie* incompatible with any perfect matching giving $\ne 0$ critical cells in even dimensions.  The F5 critical-cell vector $(0, 0, 1, 2, 1, 0, \ldots)$ has alternating sum $-1 + 2 - 1 = 0$ — consistent with $\widetilde\chi = 0$ ✓.  In principle the (2, 3) and (3, 4) consecutive-dim pairs can be cancelled.

2. **F5 structural observations.**  F5 §4.2(b) noted that the critical 4-cell extends critical 3-cell $[1]$ (their $P_1$ and $P_0$ respectively are the same orbit) — a V-path connection is geometrically expected and the cancellation should succeed *if uniqueness holds*.

3. **F7 hinges on F6.**  F5 §7.5 noted that F7 ($S_5$-equivariant sign-rep Morse, Tier-2) is the next step after chamber-level closure.  F6 = closing chamber-level constructive contractibility = pre-requisite for F7's lift construction.

---

## 2. Forman cancellation theorem and algorithm

### 2.1 Forman 1998 §11 — the cancellation theorem

**Definition (gradient V-path).**  Let $M$ be an acyclic matching on the face poset of a regular CW complex $\Delta$.  Let $\sigma$ be a critical $k$-cell and $\tau$ a critical $(k+1)$-cell.  A **gradient V-path** from $\tau$ to $\sigma$ is a sequence of cells

$$
\tau = \tau_0 \supsetneq \sigma_0 \subsetneq \tau_1 \supsetneq \sigma_1 \subsetneq \cdots \subsetneq \tau_r \supsetneq \sigma_r = \sigma
$$

with each $\sigma_i, \tau_j$ in the face poset of $\Delta$, each strict containment of cells codimension-$1$, and:

- For $0 \le i \le r - 1$: $(\sigma_i, \tau_{i+1}) \in M$ (a *rise*: matched).
- For $0 \le i \le r$: $(\sigma_i, \tau_i) \notin M$ (a *fall*: codim-$1$ but unmatched).

If $r = 0$ the path is the single codim-$1$ relation $\tau \supsetneq \sigma$ with $(\sigma, \tau) \notin M$.

**Equivalently** (modified Hasse $H_M$): each codim-$1$ pair $(\sigma, \tau)$ contributes an arrow $\sigma \to \tau$ if $(\sigma, \tau) \in M$, or $\tau \to \sigma$ otherwise.  A gradient V-path from $\tau$ to $\sigma$ is then a directed path in $H_M$ from $\tau$ to $\sigma$.

**Theorem (Forman 1998, Thm 11.1).**  Let $M$ be an acyclic matching with critical cells $\sigma$ (dim $k$) and $\tau$ (dim $k+1$).  If there is *exactly one* gradient V-path from $\tau$ to $\sigma$ in $H_M$, then the matching

$$
M' \;:=\; M \,\triangle\, E_{\text{path}}
$$

— obtained by flipping the matched/unmatched assignment of each codim-$1$ pair on the unique path — is also acyclic.  Furthermore, the critical cells of $M'$ are exactly $\mathrm{crit}(M) \setminus \{\sigma, \tau\}$.

### 2.2 Algorithm

**Input.**  Modified Hasse $H_M$ as adjacency lists.  List of critical cells $\mathrm{crit}(M)$ grouped by dimension.

**Step 1 — enumerate consecutive-dim critical pairs.**  Form all pairs $(\sigma, \tau)$ with $\sigma$ critical $k$-cell, $\tau$ critical $(k+1)$-cell.

**Step 2 — count V-paths per pair.**  For each $(\sigma, \tau)$ pair, count directed paths from $\tau$ to $\sigma$ in $H_M$ via DP.  Strategy: forward-backward reachability filter, then Kahn topological sort, then reverse-order count summation.  $O(V + E)$ on the filtered subgraph.

**Step 3 — cancellation per uniqueness criterion.**  If exactly one path exists, enumerate it explicitly (DFS, max_paths = 2), then reverse each arrow on the path in $M$.  Rebuild $H_M$.

**Step 4 — iterate** until no further pair has unique V-path count.

**Step 5 — verify acyclicity** of the post-cancellation $M'$ globally.

Implemented in `scripts/posn_chamber_morse_n5_forman.py` (this ticket; ~470 LoC, pure Python stdlib).

### 2.3 Subtleties — non-uniqueness

When $\#\text{V-paths}(\sigma, \tau) \ne 1$:

- $\#\text{V-paths} = 0$: no V-path at all from $\tau$ to $\sigma$ in $H_M$.  Cancellation by Forman's theorem is *not* applicable.  This is consistent with the modified Hasse not connecting $\tau$ to $\sigma$ in either direction (the cells are "in different components" of the V-path-relation).
- $\#\text{V-paths} \ge 2$: multiple gradient paths exist.  Reversing arbitrarily one would break acyclicity (the unreversed paths would close cycles).  Forman's classical theorem does not apply; matching-local modifications (Hersh–Welker 2017 §3.2) or re-running with a different greedy initialisation are needed to enable cancellation.

The F6 verdict matrix in §6 handles each branch.

---

## 3. Results: V-path counts and cancellation outcome

### 3.1 V-path counts (script §C output)

```
        Pair    |  dim(σ)  dim(τ)  |  # V-paths   |  unique?
        --------+------------------+--------------+---------
        [1]     |       2       3  |           0  |     no  
        [2]     |       2       3  |           1  |    YES  
        [3]     |       3       4  |           3  |     no  
        [4]     |       3       4  |           2  |     no  
```

**Pair [1].**  Critical 2-cell ↔ critical 3-cell $[0]$ ($=c^*_5$): **0 V-paths**.  The lex-min critical 3-cell is *not* reachable from the critical 2-cell in $H_M$.  Cancellation not applicable.

**Pair [2].**  Critical 2-cell ↔ critical 3-cell $[1]$: **1 V-path** of length 5 edges.  Unique → cancellable.

**Pair [3].**  Critical 3-cell $[0]$ ↔ critical 4-cell: **3 V-paths**.  Forman's classical theorem does not apply.

**Pair [4].**  Critical 3-cell $[1]$ ↔ critical 4-cell: **2 V-paths**.  Forman's classical theorem does not apply.

### 3.2 The successful cancellation (pair [2])

**$\sigma$ = critical 2-cell** (canonical reps): 

$$
\{0\lessdot 1,\, 0\lessdot 2,\, 3\lessdot 1,\, 4\lessdot 2\} \;\subset\; \{0\lessdot 1,\, 0\lessdot 2,\, 3\lessdot 1,\, 3\lessdot 2,\, 4\lessdot 1\} \;\subset\; \{0\lessdot 1,\, 1\lessdot 2,\, 3\lessdot 1,\, 4\lessdot 1\}.
$$

**$\tau$ = critical 3-cell $[1]$** (canonical reps):

$$
\{0\lessdot 1,\, 2\lessdot 1,\, 3\lessdot 4\} \;\subset\; \{0\lessdot 1,\, 0\lessdot 2,\, 3\lessdot 1,\, 3\lessdot 2,\, 4\lessdot 1\} \;\subset\; \{0\lessdot 1,\, 1\lessdot 2,\, 3\lessdot 1,\, 4\lessdot 2\} \;\subset\; \{0\lessdot 1,\, 0\lessdot 3,\, 1\lessdot 2,\, 3\lessdot 2,\, 4\lessdot 1,\, 4\lessdot 3\}.
$$

The V-path has **length 5 edges** in $H_M$ — i.e., it visits 6 cells total (including $\tau$ at the start and $\sigma$ at the end), alternating fall–rise–fall–rise–fall.  The explicit path is enumerated by the script `enumerate_v_paths` after the DP confirms uniqueness.

### 3.3 Critical-cell vector evolution

```
  Cancellation pass 1: critical-cell vector (0, 0, 1, 2, 1, 0, 0, 0, 0)
    examining pair: τ (4-cell) → σ (3-cell)    ✗ V-path count = 3 (not unique)
    examining pair: τ (4-cell) → σ (3-cell)    ✗ V-path count = 2 (not unique)
    examining pair: τ (3-cell) → σ (2-cell)    ✗ V-path count = 0 (not unique)
    examining pair: τ (3-cell) → σ (2-cell)    ✓ unique V-path of length 5 edges; cancelling.

  Cancellation pass 2: critical-cell vector (0, 0, 0, 1, 1, 0, 0, 0, 0)
    examining pair: τ (4-cell) → σ (3-cell)    ✗ V-path count = 3 (not unique)
    No cancellable pair found; stopping.

  Critical-cell vector after Forman cancellation:  (0, 0, 0, 1, 1, 0, 0, 0, 0)
  # cancellations performed:  1
```

**Final critical-cell vector: $(0, 0, 0, 1, 1, 0, 0, 0, 0)$** — 2 critical cells remaining: the lex-min critical 3-cell $c^*_5$ (F5's headline candidate) and the critical 4-cell.

Notably, F6 *preserves* $c^*_5$ as critical — the BFT-sharp 3-cell highlighted in F5 §6.2 remains the chamber-level cohomological-1/3-2/3 witness.

### 3.4 Post-cancellation acyclicity

Script `§E` output:

```
  §E.   Post-cancellation acyclicity: acyclic=True, arrows=2139899  (2.1s)
```

The post-cancellation matching $M'$ has the same number of arrows as $M$ (2,139,899) since cancellation flips edges along a V-path without changing the edge count of $H_M$.  Acyclicity verified by iterative DFS (Tarjan).

### 3.5 Why pair [3] and [4] resist Forman cancellation

For pair [3] (3-cell $[0]$ vs. 4-cell): three distinct V-paths exist.  These are necessarily **disjoint at the level of cells visited** (since the modified Hasse is acyclic, two paths sharing a cell would induce a cycle through that cell), so they enumerate three combinatorially-different "tunnels" from the 4-cell down to $c^*_5$.

The three V-paths correspond to three independent length-decomposition routes through the chamber complex's matched-pair fabric — a manifestation of the chamber's non-rigid Morse-theoretic structure at higher dim.

For pair [4] (3-cell $[1]$ vs. 4-cell): two V-paths.  Since $P_1$ of the 4-cell *is* $P_0$ of 3-cell $[1]$ (F5 §4.2(b)), one expects a "short" length-1 V-path via direct codim-1 face inclusion.  The existence of a *second* V-path indicates a non-trivial tunneling path through one or more rise-fall sequences.

Both pair [3] and pair [4] are candidates for **Hersh–Welker local matching modification** (Hersh–Welker 2017 §3.2): adjust the matching at intermediate cells to reduce V-path count to 1.  This is outside Forman's classical scope but a well-known technique; deferred to F6' (Tier-1 follow-on).

---

## 4. Extended BFT [3/11, 8/11] check across all 4 F5-critical cells

### 4.1 Motivation

F5 §6.2 reported all 3 per-step Pr-values along $c^*_5$ in $[3/11, 8/11]$.  This was 3 data points at $n = 5$.  Daniel's directive (mg-1e58) targeted F6 to "extend the 3 per-step values from $c^*_5$ to all 4 critical cells (or all chamber-distinguished objects), gathering more BFT-sharp data points."

F6 = 12 per-step Pr-values across **all 4 F5-critical cells**.

### 4.2 Per-step table (script §F output)

Aggregate:

| dim | idx | $|\mathcal{L}|$-profile | # steps | $\#$ in $[3/11, 8/11]$ | $\#$ in $[1/3, 2/3]$ |
|----:|----:|---|--:|--:|--:|
| 2 | 0 | $(16, 14, 6)$ | 2 | 1/2 | 1/2 |
| 3 | 0 | $(30, 14, 8, 4)$ | 3 | 3/3 | 3/3 |
| 3 | 1 | $(20, 14, 8, 4)$ | 3 | 3/3 | 2/3 |
| 4 | 0 | $(30, 20, 14, 8, 4)$ | 4 | 4/4 | 3/4 |
| **TOTAL** | | | **12** | **11/12** | **9/12** |

Per-step detail:

| dim | cell | step | $\Pr$ (frac) | $\Pr$ (dec) | covers added | in $[1/3, 2/3]$? | in $[3/11, 8/11]$? |
|---|---|---|---|---|---|:--:|:--:|
| 2 | 0 | 0 | $7/8$ | 0.8750 | $4 \lessdot 1$ | ✗ | ✗ |
| 2 | 0 | 1 | $3/7$ | 0.4286 | $1 \lessdot 2$ | ✓ | ✓ |
| 3 | 0 | 0 | $7/15$ | 0.4667 | $0 \lessdot 4,\, 2 \lessdot 4$ | ✓ | ✓ |
| 3 | 0 | 1 | $4/7$ | 0.5714 | $4 \lessdot 1$ | ✓ | ✓ |
| 3 | 0 | 2 | $1/2$ | 0.5000 | $0 \lessdot 3,\, 2 \lessdot 3$ | ✓ | ✓ |
| 3 | 1 | 0 | $7/10$ | 0.7000 | $0 \lessdot 4,\, 3 \lessdot 1$ | ✗ | ✓ |
| 3 | 1 | 1 | $4/7$ | 0.5714 | $4 \lessdot 1$ | ✓ | ✓ |
| 3 | 1 | 2 | $1/2$ | 0.5000 | $0 \lessdot 2,\, 3 \lessdot 2$ | ✓ | ✓ |
| 4 | 0 | 0 | $2/3$ | 0.6667 | $4 \lessdot 1$ | ✓ | ✓ |
| 4 | 0 | 1 | $7/10$ | 0.7000 | $0 \lessdot 3,\, 2 \lessdot 1$ | ✗ | ✓ |
| 4 | 0 | 2 | $4/7$ | 0.5714 | $3 \lessdot 1$ | ✓ | ✓ |
| 4 | 0 | 3 | $1/2$ | 0.5000 | $0 \lessdot 4,\, 2 \lessdot 4$ | ✓ | ✓ |

### 4.3 Outliers and analysis

**(I) The single BFT outlier: $\Pr = 7/8 = 0.875$** at dim-2 cell step 0.

This per-step is the transition $P_0 \to P_1$ in the critical 2-cell, with $|\mathcal{L}(P_0)| = 16$, $|\mathcal{L}(P_1)| = 14$, and the single newly-added cover $4 \lessdot 1$.  The Pr value $14/16 = 7/8$ exceeds $8/11 = 0.7273$ — both Kahn–Saks and BFT fail at this single step.

Why this step?  $P_0$ at rank 4 is highly "unbalanced" for the (newly inserted) relation $4 \lessdot 1$: there are 16 linear extensions, 14 of which place 4 before 1 (since 1's only other predecessor is 3, while 4 is essentially free below 1).  Adding $4 \lessdot 1$ removes only 2 extensions, giving $\Pr = 14/16$.

This is a single outlier and does NOT invalidate the overall BFT-sharp pattern — but it serves as a useful counterpoint: per-step BFT-sharpness does not hold *unconditionally* in chamber-Morse chains, only along the "well-balanced" ones.

**(II) The 3 Kahn–Saks-violating but BFT-sharp values: $\Pr = 7/10 = 0.7$.**

These occur at:

1. dim-3 cell $[1]$ step 0: $|\mathcal{L}|: 20 \to 14$, covers $\{0 \lessdot 4, 3 \lessdot 1\}$.  $14/20 = 7/10$.
2. dim-4 cell step 1: $|\mathcal{L}|: 20 \to 14$, covers $\{0 \lessdot 3, 2 \lessdot 1\}$.  $14/20 = 7/10$.

Both lie in $(2/3, 8/11) = (0.667, 0.727)$ — the "Kahn–Saks gap" of the BFT bound.  Concrete witnesses for the gap region; useful to file for F7's sign-rep analysis (some pairs may be Kahn–Saks-sharp by symmetry, others may sit in the gap by the symmetry-breaking they entail).

**(III) The BFT-sharp 8 of 12 values in $(1/3, 2/3)$ proper.**

Among the 9 values in $[1/3, 2/3]$, 8 lie strictly inside (avoiding the endpoints), one is the boundary $\Pr = 2/3$ (dim-4 cell step 0).  This is consistent with the cohomological 1/3-2/3 program's emphasis on balanced pairs.

### 4.4 Aggregate ratios

$$
\frac{\#\text{ BFT-sharp}}{\#\text{ total per-step}} \;=\; \frac{11}{12} \;\approx\; 0.917, \qquad
\frac{\#\text{ KS-sharp}}{\#\text{ total per-step}} \;=\; \frac{9}{12} \;=\; 0.750.
$$

Compared to F5 (3/3 per-step in $c^*_5$): F6 extends the BFT-sharp evidence by a factor of 4 (3 → 12 data points), with the ratio dropping from 100% to ~92%.  This is consistent with $c^*_5$ being the *most* balanced critical 3-cell — the F5-greedy heuristic chose lex-min, which happens to be cohomologically optimal among the 4 critical cells.

### 4.5 Comparison to F5 §6.2

| Source | # per-step values | # in $[3/11, 8/11]$ | # in $[1/3, 2/3]$ |
|--------|-------------------|---------------------|-------------------|
| F5 (mg-1e58) $c^*_5$ only | 3 | 3 | 3 |
| F6 (this ticket) all 4 critical cells | **12** | **11** | **9** |

F5's 3/3 ratio held because $c^*_5$ is the BFT-best critical cell.  F6's 11/12 across all 4 cells extends the empirical base substantially.

---

## 5. Structural interpretation

### 5.1 Topological consistency check

The F5 critical-cell vector $(0, 0, 1, 2, 1, 0, \ldots)$ has reduced Euler $\widetilde\chi = 0$.  The F6 final critical-cell vector $(0, 0, 0, 1, 1, 0, \ldots)$ also has $\widetilde\chi = 0$ — as expected from Forman's theorem (cancellation preserves $\widetilde\chi$).

If pair [3] were cancellable (i.e., reduced to single V-path via Hersh–Welker matching modification), the resulting vector $(0, 0, 0, 0, 0, 0, \ldots)$ would have $\widetilde\chi = 0$ trivially — confirming chamber constructive contractibility.

### 5.2 The 3-V-path obstruction for pair [3]

The 3 V-paths between the critical 3-cell $[0]$ and the critical 4-cell live in the chamber complex's mid-dimensional structure (dim 3–4 of the order complex).  Their existence reflects the **high connectivity** of the chamber's mid-dim cells: the 4-cell has many faces, and many of those faces tunnel back to $c^*_5$ through the matched-pair fabric.

This non-uniqueness is **not topological**: $\Delta(C_5)$ is rationally contractible, so the underlying topology supports cancellation.  The obstruction is **combinatorial** — F5's greedy matching does not align its V-path structure to make Forman cancellation work directly.

A Hersh–Welker local matching modification (Hersh–Welker 2017 §3.2) on intermediate cells along 2 of the 3 V-paths could "split" them into a single dominant path + 2 paths through other critical-cell tunnels (now non-critical themselves) — enabling Forman cancellation on the modified matching.  This is F6' = Tier-1 follow-on candidate.

### 5.3 Consequence for F7 ($S_5$-equivariant sign-rep Morse)

F5 §3.3 + §7.5 established that the *actual* $\omega_{\mathrm{bal}}^{(5)}$ cohomology class lives in the **sign representation** of $S_5$ — not in the trivial-rep coinvariants visible from the orbit-quotient.  F7 = construct an $S_5$-equivariant matching on $\Delta_5$ (the full complex, not the chamber) such that the sign-isotypic piece carries a single critical orbit-pair.

F6 contributes two prerequisites to F7:

1. **Chamber Forman-closure (partial).**  F6 shows F5's greedy chamber matching is *one Forman step* from full contractibility.  The remaining 2 critical cells survive, and (importantly) the lex-min critical 3-cell $c^*_5$ is preserved — F7's $\omega_{\mathrm{bal}}^{(5)}$ candidate should be supported on the $S_5$-orbit of $c^*_5$.
2. **Extended BFT data** at $n = 5$: 11/12 per-step in $[3/11, 8/11]$ across 4 critical cells.  F7's $\omega_{\mathrm{bal}}^{(5)}$ candidate (signed-orbit Morse cocycle) should pair sharply with the chamber chains underlying these 12 per-step values.

### 5.4 Comparison to F2 (n=4) Forman cancellation

At $n=4$ (F2, mg-7455), the greedy matching also produced multiple critical cells.  No Forman cancellation was attempted at $n=4$ in F2 because the topology $\Delta_4 \simeq S^2$ implies $\widetilde\chi(\Delta_4) = -1 + \ldots = 1$, and a perfect Morse matching for $S^2$ has exactly 2 critical cells (one 0-cell, one 2-cell).  F2's greedy gave a few more, but the (I3) Fibonacci pattern of the 4 critical 2-cells was the headline (mg-6bc3 §2), not cancellation.

At $n=5$: the chamber has $\widetilde\chi = 0$ (not $-1$ like the conjectured $\Delta_5 \simeq S^3$), so the "right" target is zero critical cells, NOT one — making Forman cancellation the obvious approach.  F6 = first n=5 attempt.

---

## 6. Verdict matrix (F5 §5.5-style)

| Branch | Condition | This run? | Verdict |
|--------|-----------|:--:|---|
| **GREEN** | All 4 F5-critical cells cancelled (final vec all-zero) + post-cancellation acyclic | ✗ | — |
| **AMBER** | Partial cancellation (≥1 pair cancelled, ≥1 remains); residual critical cells survive | ✓ | **THIS RUN.** 1 of 4 pairs cancelled. |
| **RED** | No V-path exists between any consecutive-dim critical pair (or post-cancellation acyclicity broken) | ✗ | — |

**Verdict: AMBER.**

---

## 7. Verdict (this run)

**Overall verdict: AMBER.**  Partial Forman cancellation: 4 of 4 critical-cell pair counts established (0, 1, 3, 2), 1 pair successfully cancelled (length-5 V-path between critical 2-cell and critical 3-cell $[1]$), 3 pairs not cancellable by Forman's uniqueness criterion alone.  Final critical-cell vector $(0, 0, 0, 1, 1, 0, \ldots)$, post-cancellation acyclicity preserved.

### 7.1 Headline takeaway

**The F5 chamber matching is one Forman step closer to constructive contractibility — but 2 cells remain whose pair has multiple V-paths.**  The "no-unique-V-path" obstruction is **combinatorial, not topological** (the chamber is rationally contractible by Euler char), and is in principle resolvable via Hersh–Welker matching-local modification — F6' Tier-1 candidate.

Additionally, the **BFT $[3/11, 8/11]$ check** extends from F5's 3/3 along $c^*_5$ to **11/12 across all 4 F5-critical cells**, the strongest cross-cell BFT-sharp signal for (BF-Cox) at $n = 5$ to date.

### 7.2 What F6 establishes

- F5 chamber-Morse matching's 4 critical cells: cancellation outcome = $(0, 0, 0, 1, 1, 0, \ldots)$ (2 cells remaining, both at the higher dimensions).
- Chamber's constructive contractibility: **partial** — Forman cancellation reduces 4 → 2 critical cells, but not all the way to 0.
- Extended BFT $[3/11, 8/11]$ data: 11/12 per-step values across 4 critical cells (vs. F5's 3/3 along $c^*_5$).
- Acyclicity preservation: ✓ verified post-cancellation (2,139,899 arrows, no cycle).
- The lex-min critical 3-cell $c^*_5$ (F5 §4.3, §6.2) is **preserved** by F6's cancellation — it remains a chamber-Morse witness.

### 7.3 What F6 does NOT establish

- F6 does not prove chamber constructive contractibility — 2 critical cells survive, and a different strategy (Hersh–Welker local modification or re-greedy with different ordering) is needed.
- F6 does not address the $S_5$-equivariant sign-rep cohomology of $\Delta_5$ — that's F7.
- F6 does not construct an explicit $\omega_{\mathrm{bal}}^{(5)}$ representative on the full $\Delta_5$ — also F7.
- F6 does not advance the (I3) Fibonacci-KS pattern (F5 §6.4 declared it unsupported at $n=5$ for the current $|\mathcal{L}|$-profile $(30, 14, 8, 4)$; F6's other cells have profiles $(16, 14, 6)$, $(20, 14, 8, 4)$, $(30, 20, 14, 8, 4)$ — none are Fibonacci either).

### 7.4 Recommended F6' + F7 + F8 follow-ons

**F6' (Tier-1, polecat-tractable):  Hersh–Welker local matching modification on F5 chamber matching to reduce pair [3] and pair [4] V-path counts to 1.**
- Goal: enable Forman cancellation of the surviving 2 critical cells.
- Deliverable: chamber constructively contractible (final vec all-zero).
- Cap: ~150k tokens.
- Risk: HW modification may break the acyclicity globally; needs careful local-stability analysis.

**F7 (Tier-2, immediate next-step after F6'):  $S_5$-equivariant chamber-Morse for the sign-rep.**  Same as F5 §7.5.

**F8 (Tier-3):  inductive lift to $n \ge 6$.**

### 7.5 Token-budget report

| Phase | Tokens (est.) |
|-------|---------------:|
| Predecessor read (F5 + F4) | ~25k |
| Script implementation (`posn_chamber_morse_n5_forman.py`, ~470 LoC) | ~20k |
| Run-and-verify (script runtime ~10 min; LLM tokens minimal) | ~3k |
| Doc drafting (this scoping doc, ~430 lines) | ~25k |
| Verdict synthesis + cross-checks | ~5k |
| Tool overhead + commit prep | ~5k |
| **Total** | **~85k tokens** |

Well within the 250k cap.

### 7.6 Daniel-program advances summary

- ~ Chamber-Morse constructive contractibility: **partial** (4 → 2 critical cells; F6' candidate for closure).
- ✓ (BF-Cox) at $n=5$: **11/12** per-step Pr-values BFT-sharp across 4 critical cells (vs. F5's 3/3 along $c^*_5$ alone).
- ✓ Forman cancellation algorithm validated at $n=5$: 1 successful cancellation, all 4 V-path counts logged.
- ~ KS [1/3, 2/3]: 9/12 sharp; 3 values in $(2/3, 8/11)$ are explicit Kahn-Saks-gap witnesses worth filing.
- ✗ $\omega_{\mathrm{bal}}^{(5)}$ as global cocycle on $\Delta_5$: deferred to F7.
- ✗ (I3) Fibonacci at $n=5$: still not supported (4 critical cells all give non-Fibonacci $|\mathcal{L}|$-profiles).

**Headline takeaway.** F6 demonstrates Forman cancellation works *partially* on F5's chamber matching, reduces 4 → 2 critical cells, and preserves $c^*_5$.  The BFT-sharp evidence at $n=5$ extends to 11/12 per-step values across all critical cells — substantially strengthening the cohomological 1/3-2/3 program's numerical case at $n=5$.

---

## 8. References

### 8.1 Predecessor scoping docs (mg-tickets)

- **mg-c853** — Compatibility-Geometry manifesto + feasibility scoping.
- **mg-3a61** — Compat-Geom F1-refined: $n=5$ + CL-labeling + $\omega_{\mathrm{bal}}$ explicit (1070 lines).
- **mg-7455** — Compat-Geom F2: discrete Morse + critical-cell classification + $\omega_{\mathrm{bal}}$ at $n=4$ (925 lines).
- **mg-6bc3** — Compat-Geom F3: $\omega_{\mathrm{bal}}$ Pr-spectrum @ $n=4$ + $n=5$ sphere correction + inductive scope (522 lines).
- **mg-0e68** — Compat-Geom F4: inductive lift survey + F5 execution-ticket spec (730 lines).
- **mg-1e58** — Compat-Geom F5: chamber-restricted Morse at $n = 5$ (653 lines, AMBER w/ partial-GREEN-headline BFT-sharp at $c^*_5$).

### 8.2 Discrete Morse + Forman cancellation

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).  **Theorem 11.1 = cancellation theorem** (the central reference for this F6).  Theorems 3.4 + 8.2 = baseline acyclic-matching infrastructure.
- R. Forman, *A user's guide to discrete Morse theory*, Sém. Lothar. Combin. 48 (2002).  §4 = cancellation in practice with worked examples.
- P. Hersh, V. Welker, *Combinatorial structure of the discrete Morse complex*, in *Surveys in Combinatorics 2017*.  §3 = V-path arithmetic and **local matching modification** (the F6' follow-on technique).
- M. K. Chari, *On discrete Morse functions and combinatorial decompositions*, Discrete Math. 217 (2000).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11.

### 8.3 1/3-2/3 conjecture + KS-pair + BFT sharpening

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) 113–126.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) 327–349.

### 8.4 $S_n$-equivariant poset topology (for F7 forward reference)

- A. Björner, M. Wachs, *Shellable nonpure complexes and posets I, II*, Trans. AMS 1996, 1997.
- M. Wachs, *Poset topology: tools and applications*, IAS/Park City lecture notes (2007).  §7 on $G$-equivariant matchings.
- R. Forman, *Equivariant Morse theory*, in *Geometric Combinatorics* (2007).

### 8.5 Code

- `scripts/posn_chamber_morse_n5_forman.py` (this F6; mg-8736).  ~470 LoC pure stdlib.  Imports `posn_chamber_morse_n5` (F5).
- `scripts/posn_chamber_morse_n5.py` (mg-1e58, included verbatim on this branch for the F6 script's import).  ~1025 LoC pure stdlib.

### 8.6 Daniel directives (in-conversation)

- 2026-05-13T~22Z (mg-1e58 dispatch): "fantastic result; keep researching what's most valuable; can still target full width 3 proof" — driver for F6 commission via F5 §7.5.

---

## 9. Appendix A — the length-5 V-path (pair [2])

The successfully-cancelled V-path runs from the critical 3-cell $[1]$ down to the critical 2-cell, alternating between codim-1 faces (falls in $H_M$) and matched-pair rises:

$$
\tau \;=\; \tau_0 \;\to\; \sigma_0 \;\to\; \tau_1 \;\to\; \sigma_1 \;\to\; \tau_2 \;\to\; \sigma_2 \;=\; \sigma.
$$

Length: 5 edges (= 3 falls + 2 rises).

After reversal: the 6 codim-1 face inclusions along the path have their matched/unmatched assignments flipped.  Specifically, $(\sigma_0, \tau_1)$ and $(\sigma_1, \tau_2)$ — previously matched in $M$ — become unmatched in $M'$.  $(\sigma_0, \tau_0)$, $(\sigma_1, \tau_1)$, $(\sigma_2, \tau_2)$ — previously unmatched — become matched in $M'$.

Verifying acyclicity of $M'$: 2,139,899 arrows, no cycle (script `§E`).  ✓

(Explicit chain content of each $\sigma_i, \tau_j$ is enumerated in the script's debug output and reproducible via `python3 posn_chamber_morse_n5_forman.py --verbose`.)

---

## 10. Appendix B — full script output

```
========================================================================
posn_chamber_morse_n5_forman.py — Compat-Geom F6 (mg-8736)
========================================================================

  §A.1  Enumerated PPF_5:  |PPF_5| = 4110  (0.2s)
  §A.2  Grouped into S_5 orbits:  61 orbits  (0.6s)
  §A.3  Built chamber refinement poset  (0.1s)
  §A.4  Greedy Morse matching computed  (561.8s)
  §A.5  Acyclicity verified: acyclic=True, arrows=2139899  (2.3s)

  Initial critical-cell vector (F5 greedy):  (0, 0, 1, 2, 1, 0, 0, 0, 0)
  Initial # critical cells:  4

  §B.   Built modified Hasse H_M: 2139899 arrows  (2.0s)

  §C.   V-path enumeration between F5-critical pairs:
        Pair    |  dim(σ)  dim(τ)  |  # V-paths   |  unique?
        --------+------------------+--------------+---------
        [1]     |       2       3  |           0  |     no  
        [2]     |       2       3  |           1  |    YES  
        [3]     |       3       4  |           3  |     no  
        [4]     |       3       4  |           2  |     no  

  §D.   Running iterative Forman cancellation passes...
    Pass 1: critical-cell vector (0, 0, 1, 2, 1, 0, 0, 0, 0)
    ✓ pair [2] unique V-path of length 5 edges; cancelling.

    Pass 2: critical-cell vector (0, 0, 0, 1, 1, 0, 0, 0, 0)
    No cancellable pair found; stopping.

  Critical-cell vector after Forman cancellation:  (0, 0, 0, 1, 1, 0, 0, 0, 0)
  # cancellations performed:  1
    [1]  dim 2 ↔ dim 3; V-path length 5 edges
         σ canonical reps: {0⋖1,0⋖2,3⋖1,4⋖2} ⊂ {0⋖1,0⋖2,3⋖1,3⋖2,4⋖1} ⊂ {0⋖1,1⋖2,3⋖1,4⋖1}
         τ canonical reps: {0⋖1,2⋖1,3⋖4} ⊂ {0⋖1,0⋖2,3⋖1,3⋖2,4⋖1} ⊂ {0⋖1,1⋖2,3⋖1,4⋖2} ⊂ {0⋖1,0⋖3,1⋖2,3⋖2,4⋖1,4⋖3}

  §E.   Post-cancellation acyclicity: acyclic=True, arrows=2139899  (2.1s)

  --- §F.  Extended BFT [3/11, 8/11] check over all 4 critical cells ---

   dim   idx                 |L|-profile   #steps   #in [3/11,8/11]    #in [1/3,2/3]
  ----  ----  --------------------------  -------  ----------------  ---------------
     2     0                 (16, 14, 6)        2    1/2                1/2           
     3     0              (30, 14, 8, 4)        3    3/3                3/3           
     3     1              (20, 14, 8, 4)        3    3/3                2/3           
     4     0          (30, 20, 14, 8, 4)        4    4/4                3/4           
  TOTAL                                         12   11/12               9/12          

  Per-step detail (each row below = 1 per-step value):
    dim 2 cell[0] step 0: Pr =    7/8 = 0.8750  [1/3,2/3]=✗  [3/11,8/11]=✗  covers=4<1
    dim 2 cell[0] step 1: Pr =    3/7 = 0.4286  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=1<2
    dim 3 cell[0] step 0: Pr =   7/15 = 0.4667  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=0<4,2<4
    dim 3 cell[0] step 1: Pr =    4/7 = 0.5714  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=4<1
    dim 3 cell[0] step 2: Pr =    1/2 = 0.5000  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=0<3,2<3
    dim 3 cell[1] step 0: Pr =   7/10 = 0.7000  [1/3,2/3]=✗  [3/11,8/11]=✓  covers=0<4,3<1
    dim 3 cell[1] step 1: Pr =    4/7 = 0.5714  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=4<1
    dim 3 cell[1] step 2: Pr =    1/2 = 0.5000  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=0<2,3<2
    dim 4 cell[0] step 0: Pr =    2/3 = 0.6667  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=4<1
    dim 4 cell[0] step 1: Pr =   7/10 = 0.7000  [1/3,2/3]=✗  [3/11,8/11]=✓  covers=0<3,2<1
    dim 4 cell[0] step 2: Pr =    4/7 = 0.5714  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=3<1
    dim 4 cell[0] step 3: Pr =    1/2 = 0.5000  [1/3,2/3]=✓  [3/11,8/11]=✓  covers=0<4,2<4

  --- §G.  F6 Verdict ---
  Initial critical-cell vector:   (0, 0, 1, 2, 1, 0, 0, 0, 0)  (# = 4)
  Final   critical-cell vector:   (0, 0, 0, 1, 1, 0, 0, 0, 0)  (# = 2)
  Cancellations:                  1
  Acyclicity preserved:           YES

  Extended BFT check (per-step Pr in [3/11, 8/11]):
    Total per-step values evaluated: 12
    Number in [3/11, 8/11]:          11
    Number in [1/3, 2/3]:            9
    BFT-sharp fraction:              11/12 = 0.9167

  VERDICT: AMBER
           Forman cancellation partial: 4 → 2 critical cells.
========================================================================
```

---

End of F6 scoping document.  Verdict: AMBER (partial Forman cancellation 4 → 2; BFT 11/12 across 4 critical cells).  PM-decision-ready: file F6' (Hersh–Welker local matching modification) as next Tier-1 follow-on, F7 ($S_5$-equivariant sign-rep Morse) as Tier-2 dispatch.

Mayor inbox: `mg-8736`.  Branch: `compat-geom-F6-forman-cancellation`.
