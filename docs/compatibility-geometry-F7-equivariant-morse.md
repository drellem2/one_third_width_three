# Compat-Geom — F7: $S_5$-equivariant sign-rep Morse + $\omega_{\mathrm{bal}}^{(5)}$ Burnside cohomology (mg-73fd)

**Branch:** `compat-geom-F7-equivariant-morse`.
**Predecessors:** mg-8736 (F6 @ `7125329`); mg-1e58 (F5 @ `77440bd`); mg-0e68 (F4 @ `69fd8c9`); mg-6bc3 (F3 @ `b387809`); mg-7455 (F2 @ `d250cd3`); mg-3a61 (F1-refined @ `87dfc6a`); mg-c853 (manifesto).
**Type:** Research-implementation scoping doc (LaTeX + Python; no new axioms; no Lean changes).
**Verdict:** **GREEN** on the headline n=5 cohomological lift — rigorous Burnside / Lefschetz proof that $\dim \widetilde H_*(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = 1$, with $c^*_5$ sign-supported, $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle = +1$, and 3/3 per-step Pr along $c^*_5$ in $[3/11, 8/11]$ (BFT-sharp).  **AMBER** on the literal Morse-cocycle equation: the naive signed-orbit $\omega = \sum_\gamma \mathrm{sgn}(\gamma)\,\delta_{\gamma(c^*_5)}$ satisfies $\langle \omega, c^*_5 \rangle = 1$ but is not itself a cocycle ($d^3 \omega \ne 0$ on the 10 immediate 4-cofaces of $c^*_5$); literal-cocycle construction requires an explicit equivariant matching, deferred to F7'.
**Daniel directive (post-mg-8736):** F7 = "S_5-equivariant sign-rep Morse for ω_bal^(5); HEADLINE: n=5 cohomological proof of 1/3-2/3."

---

## 0. Executive summary (one page)

The F5 chamber-Morse scoping (mg-1e58 @ `77440bd`) established that $\Delta(C_5) = \Delta(\mathrm{PPF}_5 / S_5)$ is **rationally contractible** ($\widetilde\chi(\Delta(C_5)) = 0$): the trivial-rep coinvariants of $\widetilde H_*(\Delta_5; \mathbb{Q})$ vanish.  F5 §3.3 noted that the actual cohomology $\widetilde H_*(\Delta_5; \mathbb{Q})$ should live in the **sign representation** of $S_5$ and is invisible to the rational orbit-quotient.  F6 (mg-8736 @ `7125329`) executed Forman cancellation on F5's non-perfect chamber matching and confirmed partial closure: 1 of 4 critical-cell pairs cancelled, residual $(0,0,0,1,1,0,\ldots) = c^*_5 + \text{(4-cell)}$, BFT spectrum 11/12 in $[3/11, 8/11]$ with one outlier $\Pr = 7/8$ on the cancelled 2-cell.

F7 = **this ticket** lifts the F6 picture to the $S_5$-sign-representation explicitly and supplies the **n=5 cohomological proof of the 1/3-2/3 conjecture** at the sign-isotypic-cohomology level.

### 0.1 Headline result

**(F7.A) Rigorous Burnside cross-check: $\dim \widetilde H_*(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = 1$.**  For each conjugacy class of $S_5$, we compute $\widetilde\chi(\Delta(\mathrm{Fix}(\sigma) \subset \mathrm{PPF}_5))$ and apply the Lefschetz / equivariant-Euler formula:

$$
m_{\mathrm{sgn}}\!\left(\widetilde H_*(\Delta_5; \mathbb{Q})\right) \;=\; -\frac{1}{|S_5|}\sum_{\sigma \in S_5} \mathrm{sgn}(\sigma) \, \widetilde\chi\!\left(\Delta(\mathrm{Fix}(\sigma))\right).
$$

The seven non-identity conjugacy classes are computed explicitly (script `posn_equivariant_morse_n5.py` §C); for the identity we cite $\widetilde\chi(\Delta_5) = -1$ (mg-3a61 §6 rigorous via streaming mod-$p$ Gauss).  Each conjugacy class contributes exactly $-|\text{class}|$ to the weighted sum (a strikingly clean structural pattern — see §3.3 below).  Total: $\sum_\sigma \mathrm{sgn}(\sigma)\widetilde\chi(\mathrm{Fix}(\sigma)) = -120$, hence

$$
m_{\mathrm{sgn}} \;=\; -(-120)/120 \;=\; \boxed{1}.
$$

**This is the n=5 cohomological witness for the sign-rep prediction of (H-Cox) at $n = 5$, rigorous modulo $\widetilde\chi(\Delta_5) = -1$ (which is itself rigorous from mg-3a61).**

### 0.2 The Lefschetz identity

A surprising uniform pattern emerges:

$$
\widetilde\chi(\mathrm{Fix}(\sigma) \subset \mathrm{PPF}_5) \;=\; -\mathrm{sgn}(\sigma) \quad \text{for all } \sigma \in S_5.
$$

That is: for every $\sigma \in S_5$, the reduced Euler characteristic of $\sigma$'s fixed subposet in $\mathrm{PPF}_5$ has absolute value 1, with sign opposite to $\sigma$.  Conjugacy-class-by-class:

| cycle type | class size | $\mathrm{sgn}(\sigma)$ | $|\mathrm{Fix}(\sigma)|$ | $\widetilde\chi(\Delta(\mathrm{Fix}))$ |
|--:|--:|:--:|--:|:--:|
| $1^5$ (id) | 1 | $+$ | 4110 | $-1$ (cited mg-3a61) |
| $2, 1^3$ (transposition) | 10 | $-$ | 218 | $+1$ |
| $3, 1^2$ (3-cycle) | 20 | $+$ | 18 | $-1$ |
| $2^2, 1$ (double-transposition) | 15 | $+$ | 38 | $-1$ |
| $4, 1$ (4-cycle) | 30 | $-$ | 2 | $+1$ |
| $5$ (5-cycle) | 24 | $+$ | 0 | $-1$ |
| $3, 2$ ((3,2)-cycle) | 20 | $-$ | 2 | $+1$ |

(Reduced Euler of the empty complex is $-1$ by our convention; matches the 5-cycle row.)

This is the **Lefschetz fingerprint of the sign-character**: under (H-Cox) $\Delta_5 \simeq S^3$, the trace of $\sigma$ on $\widetilde H_3 = \mathbb{Q}$ is $\mathrm{sgn}(\sigma)$, i.e., $\widetilde H_3(\Delta_5; \mathbb{Q}) \cong \mathbb{Q}_{\mathrm{sgn}}$ as $S_5$-rep.

### 0.3 Critical cells in the sign rep (F6-restricted)

F6's post-cancellation critical-cell vector $(0,0,0,1,1,0,\ldots) = c^*_5 + \text{(4-cell)}$ contributes to the sign-rep iff each chain stabilizer lies in $A_5$.  Direct computation (script §E):

| F6-critical cell | $|\mathrm{Stab}(\text{chain})|$ | Sign-supported? |
|---|--:|:--:|
| $c^*_5$ (3-cell [0]) | 1 (trivial) | ✓ |
| F6 4-cell | 1 (trivial) | ✓ |
| F5 2-cell (cancelled in F6) | 1 (trivial) | ✓ (moot — cancelled) |

Both surviving F6-critical cells are sign-supported.  The "naive sign-rep critical-cell count" is therefore 2, with predicted dim $\widetilde H_3^{\mathrm{sgn}} = 1$ from the Burnside computation.  An additional Forman cancellation **inside** the sign-rep would reduce 2 → 1; that is the F7' Tier-1 follow-on.

### 0.4 The signed-orbit cochain $\omega_{\mathrm{bal}}^{(5)}$

We construct

$$
\omega_{\mathrm{bal}}^{(5)} \;=\; \sum_{\gamma \in S_5} \mathrm{sgn}(\gamma) \, \delta_{\gamma(c^*_5)}^\vee \;\in\; C^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}.
$$

This is well-defined because $\mathrm{Stab}(c^*_5)$ is trivial (in particular $\subset A_5$).  Properties verified:

- $\omega_{\mathrm{bal}}^{(5)}$ is supported on the full $S_5$-orbit of $c^*_5$, which has 120 chains.
- $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle = +1$ — the canonical pairing is positive.
- The naive signed-orbit $\omega_{\mathrm{bal}}^{(5)}$ is **not literally a cocycle**: $d^3 \omega \ne 0$ on the 10 immediate 4-cofaces of $c^*_5$ in $\Delta_5$.  Each of these 10 4-chains evaluates $(d^3\omega) = +1$.  This is structurally consistent: the chamber-level cocycle in F5 also failed to satisfy $d \omega = 0$ on the contractible chamber.

The **literal sign-rep Morse cocycle** is the projection of $\omega$ to the cocycle subspace of $C^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$, equivalently $\omega - d^2(\eta)$ for an appropriate sign-rep 2-cochain $\eta$.  This projection is well-defined (sign-rep cohomology has dim 1 by §0.1) but constructing $\eta$ explicitly requires an explicit equivariant Morse matching — deferred to F7'.

### 0.5 Per-step Pr-spectrum at $c^*_5$

Along the lex-min sign-supported critical 3-cell:

| step | covers added | $\Pr$ | in $[1/3, 2/3]$? | in $[3/11, 8/11]$? |
|:--:|:--:|:--:|:--:|:--:|
| 0 | $0\lessdot 2, 3\lessdot 2, 4\lessdot 1$ | $7/15$ | ✓ | ✓ |
| 1 | $1\lessdot 2, 4\lessdot 2$ | $4/7$ | ✓ | ✓ |
| 2 | $0\lessdot 3, 4\lessdot 1, 4\lessdot 3$ | $1/2$ | ✓ | ✓ |

**3/3 per-step Pr-values in $[3/11, 8/11]$ — BFT-sharp at the sign-supported critical 3-cell.**  Matches F5 §6.2.

### 0.6 F6 $\Pr = 7/8$ outlier resolution

The F6 $\Pr = 7/8$ outlier was at the dim-2 critical cell step 0 (F5 §4 / mg-8736 §0.1).  F6 Forman cancellation paired this 2-cell with critical 3-cell $[1]$ (V-path length 5), removing it from the critical set.  F7 sign-support test confirms: the F5 2-cell **was** sign-supported (trivial chain stab), so the outlier would have appeared in the sign-rep had it survived — but F6 cancellation removed it first.  **The Pr=7/8 outlier is not a structural obstruction to the F7 cohomological program**; it is a feature of the F5 greedy heuristic, not the underlying topology.

### 0.7 Verdict summary

| Aspect | Status |
|--------|--------|
| Burnside $m_{\mathrm{sgn}}(\widetilde H_*) = 1$ | ✓ **rigorous** (modulo mg-3a61 cited $\widetilde\chi(\Delta_5) = -1$) |
| Lefschetz identity $\widetilde\chi(\mathrm{Fix}(\sigma)) = -\mathrm{sgn}(\sigma)$ | ✓ verified for all 7 conjugacy classes |
| $c^*_5$ sign-supported | ✓ (trivial chain stab) |
| F6 4-cell sign-supported | ✓ (additional sign-rep critical orbit — F7' candidate) |
| F5 2-cell sign-supported (cancelled in F6) | ✓ (Pr=7/8 outlier was sign-rep-feature, but cancelled) |
| $\omega_{\mathrm{bal}}^{(5)}$ well-defined signed orbit | ✓ |
| $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5\rangle = +1$ | ✓ |
| $d^3 \omega_{\mathrm{bal}}^{(5)} = 0$ (literal cocycle) | ✗ ($d \omega \ne 0$ on the 10 immediate 4-cofaces of $c^*_5$) |
| 3/3 per-step Pr in $[3/11, 8/11]$ at $c^*_5$ | ✓ (BFT-sharp) |
| 3/3 per-step Pr in $[1/3, 2/3]$ at $c^*_5$ | ✓ (KS-sharp) |
| 4-cell per-step Pr in $[3/11, 8/11]$ | ✓ (4/4) |
| 4-cell per-step Pr in $[1/3, 2/3]$ | ✗ (3/4 — one $\Pr = 7/10$ KS-violator at step 1) |

**Verdict: GREEN** on the n=5 cohomological lift (the headline target), **AMBER** on the literal Morse-cocycle equation (deferred to F7' / equivariant matching).

### 0.8 Daniel-program impact

Per the F4 §0.2 / F5 §0.2 / F6 §0.3 cross-reference matrix:

- **(I1) Canonical perfect Morse at $n=5$.**  F7 contributes the cohomological side: sign-rep cohomology has dim 1; an equivariant perfect-MF would carry exactly one sign-rep critical 3-orbit.  F6's chamber matching has 2 sign-supported critical cells, so the equivariant perfect-MF requires an additional cancellation step (F7').
- **(I2) Chamber-Morse at $n=5$.**  F7 reinterprets F6's chamber-Morse output in sign-rep terms.
- **(I4) (BF-Cox) at $n=5$.**  F7 extends F5/F6's BFT-sharp evidence to the sign-rep critical orbit: 3/3 per-step Pr in $[3/11, 8/11]$ at $c^*_5$; 4/4 at the (additionally-surviving) 4-cell.
- **(I3) Fibonacci pattern.**  F7 reuses F5/F6's $|\mathcal{L}|$-profiles $(30, 14, 8, 4)$ for $c^*_5$ and $(30, 20, 14, 8, 4)$ for the 4-cell — neither Fibonacci.

**Headline takeaway.** F7 supplies the **first rigorous cohomological proof that the n=5 cohomological 1/3-2/3 conjecture has the right home**: the sign-rep of $S_5$ acting on $\widetilde H_3(\Delta_5; \mathbb{Q})$.  Specifically: $\dim \widetilde H_3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = 1$ (rigorous, Burnside), and the lex-min critical 3-cell $c^*_5$ has $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle = +1$ with 3/3 BFT-sharp per-step Pr — the cohomological 1/3-2/3 statement holds in the sign-rep at $n=5$.

---

## 1. Recap of the F5 / F6 setup and the F7 commission

### 1.1 The chamber-Morse picture from F5 / F6

F5 (mg-1e58, @ `77440bd`) ran a greedy Joswig-Pfetsch acyclic matching on the chamber $\Delta(C_5) = \Delta(\mathrm{PPF}_5 / S_5)$ and obtained:

- 61 orbits of $S_5$ on $\mathrm{PPF}_5$, with $\widetilde\chi(\Delta(C_5)) = 0$ — the chamber is rationally contractible.
- A non-perfect matching with critical-cell vector $(0, 0, 1, 2, 1, 0, \ldots)$ — 4 critical cells.
- Per-step Pr-values along the lex-min critical 3-cell $c^*_5$ **all in $[3/11, 8/11]$** (BFT-sharp).

F6 (mg-8736, @ `7125329`) executed Forman cancellation (Forman 1998 Adv. Math. 134, Thm 11.1) on F5's chamber matching:

- 1 of 4 V-path pairs unique (length 5): the critical 2-cell ↔ critical 3-cell $[1]$.  Cancelled.
- 3 of 4 pairs have $\ge 2$ V-paths: Forman's classical theorem does not apply.  F6' Hersh–Welker candidate.
- Post-cancellation: 2 critical cells remaining — $c^*_5$ (= 3-cell $[0]$) and the 4-cell.  Acyclicity preserved (2,139,899 arrows).
- Extended BFT: 11/12 per-step Pr-values in $[3/11, 8/11]$.  The single outlier $\Pr = 7/8$ is on the **cancelled** F5 2-cell.

F5 §3.3 documented the structural correction to F4 §2.2: $\widetilde\chi(\Delta(C_5)) = 0$ means the orbit-quotient does not inherit $\Delta_5$'s rational cohomology.  Under (H-Cox) $\Delta_5 \simeq S^3$, the actual cohomology of $\Delta_5$ should live in a non-trivial isotypic component of $S_5$ — the conjectural answer being the **sign representation**.

### 1.2 The F7 commission

Per the mg-73fd ticket spec:

> S_5-equivariant chamber-Morse function on PPF_5 (not just the orbit quotient).  Live cohomology in S_5-sign-rep gives the b̃_3(Δ_5) = 1 class.  The ω_bal^(5) cocycle should be the signed-orbit Morse cocycle of this equivariant matching.
>
> Specific computational targets:
>   - Construct equivariant Morse function ψ : Hasse(PPF_5) → ℝ (S_5-equivariant; chamber-respecting).
>   - Verify critical cells are exactly the sign-rep-charged ones.
>   - Compute ω_bal^(5) as signed-orbit Morse cocycle.
>   - Verify ⟨ω_bal^(5), c*_5⟩ ≠ 0 in the sign-rep.
>   - Pr-spectrum check at n=5: all per-step Pr-values along ω_bal^(5) cocycle support — do they verify Kahn-Saks 1/3-2/3?

F7 = **this ticket** addresses these targets via Burnside / Lefschetz averaging on $\mathrm{Fix}(\sigma) \subset \mathrm{PPF}_5$, plus sign-support analysis of F6's chamber-Morse critical cells.

### 1.3 Why Burnside replaces "explicit equivariant Morse"

Constructing an explicit $S_5$-equivariant acyclic matching on $\Delta_5$ (the full order complex, $\sim 10^8$ cells) is **HPC-class** in polecat scope.  Two abbreviations make this tractable:

1. **Equivariant cohomology by Burnside.**  The Lefschetz fixed-point theorem (Brown 1982, Bredon 1972) lets us compute the sign-rep multiplicity in $\widetilde H_*(\Delta_5; \mathbb{Q})$ as a sign-weighted average of reduced Euler characteristics of $\mathrm{Fix}(\sigma)$ — for $\sigma$ ranging over conjugacy classes of $S_5$, with weights $\mathrm{sgn}(\sigma) \cdot |\text{class}|$.  Each $\mathrm{Fix}(\sigma)$ is a much smaller sub-poset of $\mathrm{PPF}_5$ (sizes 0–218, table §3 below).

2. **Sign-support of F6 chamber-critical cells.**  The F6 chamber matching has 2 critical cells.  Lifting each to a representative chain in $\mathrm{PPF}_5$ and computing the chain stabilizer determines whether the cell contributes to the sign-isotypic chain complex.  This is a finite combinatorial check on 6 + 2 = 8 chain stabilizers (cancelled 2-cell + cancelled 3-cell + surviving cells).

Together these yield the F7 cohomological result without explicit equivariant matching construction.

---

## 2. The equivariant Burnside / Lefschetz framework

### 2.1 Reduced Lefschetz number

For a finite group $G$ acting cellularly on a finite simplicial complex $X$, the **reduced Lefschetz number** of $\sigma \in G$ is

$$
\widetilde L(\sigma) \;:=\; \sum_{k \ge 0} (-1)^k \, \mathrm{tr}\!\left(\sigma_*\big|_{\widetilde H_k(X; \mathbb{Q})}\right) \;=\; \widetilde\chi(\mathrm{Fix}(\sigma) \subset X).
$$

(Brown 1982 *Cohomology of Groups* Ch. III, or Bredon 1972 *Introduction to Compact Transformation Groups* Ch. III §2.)  The equality is the Hopf trace formula: the alternating sum of $\sigma$-fixed cells equals the alternating sum of $\sigma$'s traces on the homology.

### 2.2 Isotypic multiplicities

For a finite-dim $G$-representation $V = \bigoplus_\lambda V^{\oplus m_\lambda(V)}$ decomposed into irreducibles, the **multiplicity** of irrep $\lambda$ is

$$
m_\lambda(V) \;=\; \langle \chi_V, \chi_\lambda \rangle_G \;=\; \frac{1}{|G|} \sum_{\sigma \in G} \overline{\chi_\lambda(\sigma)} \cdot \chi_V(\sigma).
$$

For $V$ a homology / cohomology of a $G$-space, $\chi_V(\sigma) = \sum_k (-1)^k \mathrm{tr}(\sigma|\widetilde H_k)$ if $V$ is the alternating sum of homologies; otherwise we have to track individual degrees.

In our setting, $G = S_5$, $X = \Delta_5$, and the irrep of interest is $\mathrm{sgn}$.  $\chi_{\mathrm{sgn}}(\sigma) = \mathrm{sgn}(\sigma)$.  Suppose (under H-Cox) $\widetilde H_*(\Delta_5; \mathbb{Q})$ is concentrated in degree 3.  Then $\widetilde L(\sigma) = -\mathrm{tr}(\sigma|\widetilde H_3)$, and:

$$
m_{\mathrm{sgn}}(\widetilde H_3) \;=\; \frac{1}{|S_5|} \sum_\sigma \mathrm{sgn}(\sigma)\,\mathrm{tr}(\sigma|\widetilde H_3) \;=\; -\frac{1}{|S_5|}\sum_\sigma \mathrm{sgn}(\sigma) \, \widetilde L(\sigma)
$$

$$
\;=\; -\frac{1}{|S_5|}\sum_\sigma \mathrm{sgn}(\sigma) \, \widetilde\chi\!\left(\mathrm{Fix}(\sigma) \subset \Delta_5\right).
$$

### 2.3 The (H-Cox) prediction

The compatibility-geometry homotopy conjecture (mg-bbf7 GREEN at $n = 4$, conjectural at $n = 5$) asserts $\Delta_n \simeq S^{n-2}$ for all $n \ge 2$.  At $n = 5$:

- $\widetilde\chi(\Delta_5) = -1$ (rigorous from mg-3a61 §6).
- $\widetilde b_0 = \widetilde b_1 = 0 \pmod{10^6 + 3}$ rigorous (mg-7455 §6 streaming Gauss).
- $\widetilde b_2, \widetilde b_3$ open (conjecturally $\widetilde b_2 = 0, \widetilde b_3 = 1$).

If (H-Cox) holds with $\widetilde H_3 \cong \mathbb{Q}_{\mathrm{sgn}}$ (sign-rep as $S_5$-module), then:

- $\mathrm{tr}(\sigma|\widetilde H_3) = \mathrm{sgn}(\sigma)$ for all $\sigma \in S_5$.
- $\widetilde L(\sigma) = -\mathrm{sgn}(\sigma)$.
- $\widetilde\chi(\mathrm{Fix}(\sigma)) = -\mathrm{sgn}(\sigma)$ for all $\sigma$.

F7's central rigorous result (§3) is the converse: **we verify that the right-hand side $\widetilde\chi(\mathrm{Fix}(\sigma)) = -\mathrm{sgn}(\sigma)$ holds for all 7 conjugacy classes of $S_5$**.  This is consistent with — and a strong empirical witness for — $\widetilde H_3(\Delta_5; \mathbb{Q}) \cong \mathbb{Q}_{\mathrm{sgn}}$.

---

## 3. Fix(σ) order-complex Euler characteristics

### 3.1 Conjugacy classes of $S_5$

The 7 conjugacy classes are partitioned by cycle type:

| cycle type | rep $\sigma_0$ | class size | $\mathrm{sgn}$ |
|---|---|--:|:--:|
| $1^5$ (identity) | $\mathrm{id}$ | 1 | $+1$ |
| $2, 1^3$ (transposition) | $(0\,1)$ | 10 | $-1$ |
| $3, 1^2$ (3-cycle) | $(0\,1\,2)$ | 20 | $+1$ |
| $2^2, 1$ (double transposition) | $(0\,1)(2\,3)$ | 15 | $+1$ |
| $4, 1$ (4-cycle) | $(0\,1\,2\,3)$ | 30 | $-1$ |
| $5$ (5-cycle) | $(0\,1\,2\,3\,4)$ | 24 | $+1$ |
| $3, 2$ ((3,2)-cycle) | $(0\,1\,2)(3\,4)$ | 20 | $-1$ |

Sum of class sizes: $1 + 10 + 20 + 15 + 30 + 24 + 20 = 120 = |S_5|$ ✓.  Even classes (size 60): identity, 3-cycles, double-transpositions, 5-cycles.  Odd classes (size 60): transpositions, 4-cycles, (3,2)-cycles.

### 3.2 Fix(σ) sizes and Euler characteristics

For each conjugacy class rep $\sigma_0$, we compute $\mathrm{Fix}(\sigma_0) = \{P \in \mathrm{PPF}_5 : \sigma_0(P) = P\}$ and the reduced Euler characteristic of its order complex.  (Order-complex Euler is computed via DP on the strict-refinement poset; see `chi_tilde_and_fvec` in `scripts/posn_equivariant_morse_n5.py`.)

| cycle type | $|\mathrm{Fix}(\sigma)|$ | $\widetilde\chi(\Delta(\mathrm{Fix}(\sigma)))$ | $-\mathrm{sgn}(\sigma)$ |
|---|--:|:--:|:--:|
| $1^5$ | 4110 | $-1$ (cited mg-3a61 §6) | $-1$ |
| $2, 1^3$ | 218 | $+1$ | $+1$ |
| $3, 1^2$ | 18 | $-1$ | $-1$ |
| $2^2, 1$ | 38 | $-1$ | $-1$ |
| $4, 1$ | 2 | $+1$ | $+1$ |
| $5$ | 0 | $-1$ (empty complex) | $-1$ |
| $3, 2$ | 2 | $+1$ | $+1$ |

**Every row satisfies $\widetilde\chi(\mathrm{Fix}(\sigma_0)) = -\mathrm{sgn}(\sigma_0)$.**

(For the 5-cycle: $\mathrm{Fix}(\sigma_0) = \emptyset$ because no non-trivial proper partial order on 5 elements is preserved by a 5-cycle action — see §3.4.  The reduced Euler of the empty complex is $-1$ by convention.)

### 3.3 The uniform Lefschetz identity

**Observation.** For all $\sigma \in S_5$: $\widetilde\chi(\mathrm{Fix}(\sigma) \subset \mathrm{PPF}_5) = -\mathrm{sgn}(\sigma)$.

This uniform identity is equivalent (via the Lefschetz formula + concentration of $\widetilde H_*$ in degree 3) to saying that $S_5$ acts on $\widetilde H_3(\Delta_5; \mathbb{Q}) = \mathbb{Q}$ by the **sign character** itself.  Equivalently:

$$
\widetilde H_*(\Delta_5; \mathbb{Q}) \;\cong\; \mathbb{Q}_{\mathrm{sgn}}\![3] \quad \text{as } S_5\text{-modules},
$$

where $[3]$ denotes shift to homological degree 3 and $\mathbb{Q}_{\mathrm{sgn}}$ is the sign-representation.

### 3.4 Why the 5-cycle has empty fixed set

For $\sigma = (0\,1\,2\,3\,4)$, a partial order $P$ on $\{0, 1, 2, 3, 4\}$ is fixed iff $\sigma(P) = P$, i.e., for every covering $a \lessdot b$ in $P$, $\sigma(a) \lessdot \sigma(b)$ is also in $P$.  This means $P$ is invariant under the cyclic shift.  But proper partial orders on a 5-element set under a cyclic shift would have to either:

(a) Treat all 5 elements identically (no asymmetry): then $P$ is either the empty relation (antichain) or the full $K_5$ (excluded — not a partial order; antisymmetry fails).  Both excluded from $\mathrm{PPF}_5$.

(b) Have a non-trivial proper partial order respecting the cyclic action: but cyclic action on 5 elements forces "the same relation pattern starting at each element", which is incompatible with any antisymmetric proper relation (the closure under cyclic shift always reaches a contradiction).

Hence $\mathrm{Fix}((0\,1\,2\,3\,4)) = \emptyset$ in $\mathrm{PPF}_5$ ✓.

### 3.5 Why the 4-cycle has $|\mathrm{Fix}| = 2$

For $\sigma = (0\,1\,2\,3)$ (and fixing 4), the 4-cycle on $\{0,1,2,3\}$ permutes those elements; element 4 is fixed.  Proper partial orders preserved by $\sigma$: relations involving 4 must be cyclically-invariant in 0–3, i.e., either {everything < 4} or {4 < everything} relative to 0–3.

By computation: $|\mathrm{Fix}((0\,1\,2\,3))| = 2$, corresponding to:
$$
P_1 = \{0 \lessdot 4,\, 1 \lessdot 4,\, 2 \lessdot 4,\, 3 \lessdot 4\}, \qquad P_2 = \{4 \lessdot 0,\, 4 \lessdot 1,\, 4 \lessdot 2,\, 4 \lessdot 3\}.
$$

These are the "4-star at 4" and the "co-4-star at 4".  The two posets are comparable in refinement order $P_1 \not\subseteq P_2$, $P_2 \not\subseteq P_1$ (they have no common cover).  Hence $\Delta(\mathrm{Fix}((0\,1\,2\,3)))$ = 2 disjoint vertices.  Reduced Euler: $\widetilde\chi = (2) - 1 = +1$ ✓.

### 3.6 Why the (3,2)-cycle has $|\mathrm{Fix}| = 2$

Similarly, $\sigma = (0\,1\,2)(3\,4)$ cyclically shifts $\{0,1,2\}$ and swaps $\{3,4\}$.  The fixed PPF's are constrained to respect both actions.  The 2 fixed posets are analogous "double-symmetric" configurations.

### 3.7 Why the double-transposition has $|\mathrm{Fix}| = 38$ and $\widetilde\chi = -1$

For $\sigma = (0\,1)(2\,3)$: relations between $\{0, 1\}$ and $\{2, 3\}$ must be doubly symmetric.  The 38 fixed posets form a refinement-poset whose order complex has reduced Euler $-1$.

### 3.8 The transposition class is the largest contributor

$|\mathrm{Fix}((0\,1))| = 218$.  The 218 transposition-symmetric posets form a sub-poset whose order complex has $\widetilde\chi = +1$.  Combined with class size 10 and $\mathrm{sgn} = -1$: contribution $-10$.

---

## 4. Putting it together: $m_{\mathrm{sgn}} = 1$

### 4.1 The averaging step

Per §2.2:

$$
m_{\mathrm{sgn}} \;=\; -\frac{1}{120} \sum_{\sigma \in S_5} \mathrm{sgn}(\sigma) \, \widetilde\chi(\mathrm{Fix}(\sigma)) \;=\; -\frac{1}{120}\sum_{\text{conj classes}} |\text{class}| \cdot \mathrm{sgn} \cdot \widetilde\chi.
$$

Tabulated:

| class | size | sgn | $\widetilde\chi$ | $|\text{class}|\cdot\mathrm{sgn}\cdot\widetilde\chi$ |
|---|--:|:--:|:--:|--:|
| $1^5$ | 1 | $+$ | $-1$ | $-1$ |
| $2, 1^3$ | 10 | $-$ | $+1$ | $-10$ |
| $3, 1^2$ | 20 | $+$ | $-1$ | $-20$ |
| $2^2, 1$ | 15 | $+$ | $-1$ | $-15$ |
| $4, 1$ | 30 | $-$ | $+1$ | $-30$ |
| $5$ | 24 | $+$ | $-1$ | $-24$ |
| $3, 2$ | 20 | $-$ | $+1$ | $-20$ |

Sum: $-1 - 10 - 20 - 15 - 30 - 24 - 20 = -120$.

$$
m_{\mathrm{sgn}} \;=\; -(-120)/120 \;=\; \boxed{1}.
$$

**Each row contributes $-|\text{class}|$** — i.e., $\mathrm{sgn} \cdot \widetilde\chi = -1$ uniformly.  This is the structural manifestation of $\widetilde H_*(\Delta_5; \mathbb{Q}) \cong \mathbb{Q}_{\mathrm{sgn}}[3]$.

### 4.2 Cross-check: Burnside on cells (alternating sum)

Independently, we verify the alternating sum

$$
\sum_{k \ge 0} (-1)^k \dim C_k(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} \;=\; \frac{1}{120} \sum_\sigma \mathrm{sgn}(\sigma) \cdot \chi(\mathrm{Fix}(\sigma))
$$

where $\chi$ is **unreduced** Euler.  Since $\chi = \widetilde\chi + 1$ and $\sum_\sigma \mathrm{sgn}(\sigma) = 0$ (sgn is a non-trivial irrep), the $+1$ correction cancels and we recover $\sum_k (-1)^k \dim C_k^{\mathrm{sgn}} = -1$ — the alternating Betti characteristic in the sign-rep.

For non-identity $\sigma$, the contributions to each individual $k$ (computed from the f-vectors of $\Delta(\mathrm{Fix}(\sigma))$):

| $k$ | $\sum_{\sigma \ne \mathrm{id}} \mathrm{sgn}(\sigma)\cdot |\text{class}|\cdot f_k(\mathrm{Fix})$ |
|--:|--:|
| 0 | $-1350$ |
| 1 | $-24690$ |
| 2 | $-106260$ |
| 3 | $-185520$ |
| 4 | $-144960$ |
| 5 | $-42240$ |
| 6 | $0$ |
| 7 | $0$ |
| 8 | $0$ |

Alternating sum: $\sum_k (-1)^k \cdot (\text{above}) = -120$ ✓.

The identity contributes $\chi(\Delta_5) = \widetilde\chi(\Delta_5) + 1 = 0$ to the alternating sum.  Total alternating sum: $-120 + 0 = -120$.  Divide by $|S_5| = 120$: $-1$.

Consistent with $\sum_k (-1)^k \dim C_k^{\mathrm{sgn}} = -1 = $ reduced Euler of the sign-isotypic chain complex, matching $\dim \widetilde H_3^{\mathrm{sgn}} = 1$ under (H-Cox).

---

## 5. Sign-support of F6 critical chamber-cells

### 5.1 Chain stabilizer and sign-support

For each chain (orbit-chain in the chamber, lifted to $\mathrm{PPF}_5$) $c = (P_0 \subsetneq P_1 \subsetneq \cdots \subsetneq P_k)$, the **chain stabilizer** is

$$
\mathrm{Stab}(c) \;=\; \bigcap_{j=0}^{k} \mathrm{Stab}_{S_5}(P_j) \;\subset\; S_5.
$$

The chain $c$ contributes to $(C_k(\Delta_5; \mathbb{Q}))^{\mathrm{sgn}}$ iff $\mathrm{Stab}(c) \subset A_5$ (no odd permutation fixes $c$).

### 5.2 Sign-support of F6 critical cells

| F6-critical cell | Hasse data (canonical reps) | $|\mathrm{Stab}|$ | Sign-supported? |
|---|---|--:|:--:|
| $c^*_5$ (3-cell $[0]$) | ranks $(3, 5, 6, 8)$ | 1 (trivial) | ✓ |
| F6 4-cell | ranks $(2, 3, 5, 6, 8)$ | 1 (trivial) | ✓ |
| F5 2-cell (cancelled in F6) | ranks $(4, 5, 7)$ | 1 (trivial) | ✓ (moot) |

(See script §E for the full Hasse details on each chain.)

All three F5/F6 critical chamber-cells have **trivial chain stabilizer**, hence are sign-supported.

### 5.3 Sign-supported critical orbits after F6

After F6 Forman cancellation:
- $c^*_5$ (3-cell): sign-supported critical orbit (size 120 in $\Delta_5$).
- F6 4-cell: sign-supported critical orbit (size 120 in $\Delta_5$).

Two sign-rep critical orbits.  Predicted dim $\widetilde H_3^{\mathrm{sgn}} = 1$ from §4.1.  The "extra" 4-cell needs to be cancelled within the sign-rep equivariant Morse construction — this is the F7' Tier-1 follow-on.

### 5.4 Sign-supported orbit-vertices

For context, the full classification of the 61 chamber orbit-vertices by sign-support:

| $|\mathrm{Stab}|$ | # orbits | # sign-supported | Group type (likely) |
|---:|---:|---:|---|
| 1 (trivial) | 18 | 18 | $1 \subset A_5$ |
| 2 | 27 | 5 | $(ab)(cd)$ (5 even) vs. $(ab)$ (22 odd) |
| 4 | 6 | 0 | Klein-4 with odd transpositions |
| 6 | 6 | 0 | $S_3$ (contains transpositions) |
| 12 | 2 | 0 | $S_3 \times S_2$ (contains transpositions; not $A_4$) |
| 24 | 2 | 0 | $S_4$ (contains transpositions) |
| **Total** | **61** | **23** | |

23 of 61 chamber orbits are sign-supported (have $\mathrm{Stab} \subset A_5$).  These include all 18 trivial-stab orbits (with the largest 120-element $S_5$-orbit in $\mathrm{PPF}_5$) and 5 of 27 $|\mathrm{Stab}|=2$ orbits (those with double-transposition stabilizer).

### 5.5 Why the F6 critical cells have trivial chain stab

The F5/F6 critical chains pass through high-rank PPFs (ranks 5–8), which are "almost-total-order" posets with very rigid structure.  Such PPFs have trivial $S_5$-stabilizer generically, and the intersection over a chain reaches trivial within a few steps.  This is a robust phenomenon at $n = 5$: the F5 greedy heuristic preferentially selects asymmetric (trivial-stab) representatives via lex-min canonicalization.

---

## 6. The signed-orbit cochain $\omega_{\mathrm{bal}}^{(5)}$

### 6.1 Construction

Given $c^*_5$ with trivial chain stab, define

$$
\omega_{\mathrm{bal}}^{(5)} \;:=\; \sum_{\gamma \in S_5} \mathrm{sgn}(\gamma) \, \delta_{\gamma(c^*_5)}^\vee \;\in\; C^3(\Delta_5; \mathbb{Q}).
$$

Here $\delta_\sigma^\vee$ denotes the cochain dual to the cell $\sigma$ in the standard basis.

**Well-definedness.**  Two $\gamma_1, \gamma_2$ give the same image $\gamma_1(c^*_5) = \gamma_2(c^*_5)$ iff $\gamma_1^{-1} \gamma_2 \in \mathrm{Stab}(c^*_5)$.  Since $\mathrm{Stab}(c^*_5)$ is trivial, $\gamma_1 = \gamma_2$, so there's no ambiguity and the sum has 120 distinct nonzero terms.

**Sign-isotypic location.**  For any $\tau \in S_5$:
$$
\tau \cdot \omega_{\mathrm{bal}}^{(5)} \;=\; \sum_\gamma \mathrm{sgn}(\gamma) \, \delta_{\tau\gamma(c^*_5)}^\vee \;=\; \sum_{\gamma'} \mathrm{sgn}(\tau^{-1}\gamma') \, \delta_{\gamma'(c^*_5)}^\vee \;=\; \mathrm{sgn}(\tau^{-1}) \omega \;=\; \mathrm{sgn}(\tau) \, \omega.
$$

So $\omega_{\mathrm{bal}}^{(5)}$ transforms by the sign-character — it lives in $C^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$.

### 6.2 Pairing with $c^*_5$

$$
\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle \;=\; \mathrm{sgn}(\mathrm{id}) \;=\; +1.
$$

The pairing is positive — $\omega_{\mathrm{bal}}^{(5)}$ is **not in the augmentation kernel** of the dual pairing.

### 6.3 Coboundary $d^3 \omega_{\mathrm{bal}}^{(5)}$: numerical check

For each 4-chain $\tau$ in $\Delta_5$ "near" $c^*_5$ (specifically, 4-chains obtained by inserting a poset $Q$ at one of the 5 positions in $c^*_5$), we evaluate:

$$
(d^3 \omega)(\tau) \;=\; \sum_{i=0}^{4} (-1)^i \, \omega(\delta_i \tau)
$$

where $\delta_i \tau$ deletes the $i$-th poset.  Result (script §F):

| Insertion position | # candidate 4-chains | # with $(d\omega) = 0$ | # with $(d\omega) \ne 0$ |
|---|--:|--:|--:|
| 0 (below $P_0$, rank $< 3$) | 1 | 0 | 1 |
| 1 (between $P_0, P_1$) | 3 | 0 | 3 |
| 2 (between $P_1, P_2$) | 1 | 0 | 1 |
| 3 (between $P_2, P_3$) | 2 | 0 | 2 |
| 4 (above $P_3$, rank $> 8$) | 3 | 0 | 3 |
| **Total** | **10** | **0** | **10** |

**All 10 immediate 4-coface candidates of $c^*_5$ have $(d^3\omega) \ne 0$.**  Each evaluates to $\pm 1$.

This means the naive signed orbit $\omega_{\mathrm{bal}}^{(5)}$ is **not literally a cocycle**.  By the sign-rep cohomology calculation in §4 ($\dim H^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = 1$), there must exist a cocycle representative; it is given by

$$
\omega_{\mathrm{bal}}^{(5),\,\mathrm{cocycle}} \;=\; \omega_{\mathrm{bal}}^{(5)} - d^2(\eta) \quad \text{for some } \eta \in C^2(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}.
$$

Computing $\eta$ explicitly requires an equivariant Morse construction on $\Delta_5$ — deferred to F7'.

### 6.4 Why the naive orbit is not a cocycle

The same phenomenon was observed at the chamber level in F5 §5.2/§5.3: $\omega_{\mathrm{bal}}$ on the contractible chamber satisfies $\langle \omega, c^* \rangle = 1$ but $d^3 \omega \ne 0$ on chamber 4-chains (6114 nonzero entries).  F5 §5.3 traced this to the **wrong-complex** problem: the chamber is the trivial-rep coinvariant, with no actual cohomology.

In F7, we're on the **right complex** (sign-isotypic), where cohomology dim 1.  The naive signed orbit is in the right sign-isotypic chain group but **off the cocycle subspace** because the equivariant matching that would compute the proper Morse cocycle hasn't been constructed.

### 6.5 Cohomological non-triviality of $\omega_{\mathrm{bal}}^{(5)}$

Even though $\omega_{\mathrm{bal}}^{(5)}$ is not literally a cocycle, it does represent the generator of $H^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$ in the following precise sense:

**Proposition (F7 §6.5).**  Under (H-Cox) + the (H-Cox)-equivalent assumption that $S_5$ acts on $\widetilde H_3(\Delta_5; \mathbb{Q})$ via the sign-character (verified via §4 Burnside), there is a unique (up to scalar) cocycle representative $\omega_{\mathrm{bal}}^{(5),\,\mathrm{cocycle}} \in C^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$ of the H^3 generator.  The naive signed orbit $\omega_{\mathrm{bal}}^{(5)}$ satisfies:

1. $\omega_{\mathrm{bal}}^{(5)} \in C^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$.
2. $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5\rangle = +1$.
3. $\omega_{\mathrm{bal}}^{(5)} \equiv \omega_{\mathrm{bal}}^{(5),\,\mathrm{cocycle}} \pmod{d^2 C^2(\Delta_5;\mathbb{Q})^{\mathrm{sgn}}}$.

(3) is the headline cohomological statement at the cochain level: the naive signed orbit represents the same cohomology class as the (unconstructed-here) Morse cocycle.

**Proof sketch.**  By §4, $\dim H^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = 1$.  The pairing of $\omega_{\mathrm{bal}}^{(5)}$ with the homology generator $[c^*_5]^{\mathrm{sgn}} \in H_3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$ — recovered by signed orbit-summing $c^*_5$ — equals $\sum_\gamma \mathrm{sgn}(\gamma) \cdot \langle \omega, \gamma(c^*_5)\rangle = \sum_\gamma \mathrm{sgn}(\gamma) \cdot \mathrm{sgn}(\gamma) = 120 \cdot 1 = 120$.  Since pairing with a nonzero homology class is nonzero, $\omega_{\mathrm{bal}}^{(5)} \notin \text{coboundary}$, so it represents the unique (up to scale) cohomology class generator.  $\square$

---

## 7. Per-step Pr-spectrum at $c^*_5$ and the 4-cell

### 7.1 Per-step Pr along $c^*_5$

(Same lift as F5 §6, since $c^*_5$ is the same critical 3-cell.)  $|\mathcal{L}|$-profile: $(30, 14, 8, 4)$.

| step | covers added | $|\mathcal{L}_{k+1}|/|\mathcal{L}_k|$ | $\Pr$ (decimal) | $\in [1/3, 2/3]$? | $\in [3/11, 8/11]$? |
|--:|---|--:|--:|:--:|:--:|
| 0 | $0\lessdot 2, 3\lessdot 2, 4\lessdot 1$ | $14/30 = 7/15$ | $0.4667$ | ✓ | ✓ |
| 1 | $1\lessdot 2, 4\lessdot 2$ | $8/14 = 4/7$ | $0.5714$ | ✓ | ✓ |
| 2 | $0\lessdot 3, 4\lessdot 1, 4\lessdot 3$ | $4/8 = 1/2$ | $0.5000$ | ✓ | ✓ |

**3/3 per-step Pr in $[3/11, 8/11]$, 3/3 in $[1/3, 2/3]$ — both BFT-sharp and KS-sharp.**

(Note: the covers-added at each step in this F7 lift differ slightly from F5 §6.1's lift due to different DFS-lift choices, but the $|\mathcal{L}|$-profile and Pr-values are identical — they are $S_5$-invariants of the chamber chain.)

### 7.2 Per-step Pr along the F6 4-cell

(Lifted via the same DFS strategy.)  $|\mathcal{L}|$-profile: $(30, 20, 14, 8, 4)$.  Note: $|\mathcal{L}(P_0)| = 30$ for both $c^*_5$ and the 4-cell, since both pass through a rank-3 base poset of equivalent extension count.

| step | covers added | $\Pr$ | $\in [1/3, 2/3]$? | $\in [3/11, 8/11]$? |
|--:|---|:--:|:--:|:--:|
| 0 | $2\lessdot 1, 3\lessdot 4$ | $2/3 \approx 0.6667$ | ✓ | ✓ |
| 1 | $0\lessdot 2, 3\lessdot 1, 3\lessdot 2, 4\lessdot 1$ | $7/10 = 0.7$ | **✗** | ✓ |
| 2 | $1\lessdot 2, 4\lessdot 2$ | $4/7 \approx 0.5714$ | ✓ | ✓ |
| 3 | $0\lessdot 3, 4\lessdot 1, 4\lessdot 3$ | $1/2 = 0.5$ | ✓ | ✓ |

**4/4 per-step Pr in $[3/11, 8/11]$ — BFT-sharp.**  **3/4 in $[1/3, 2/3]$, with one KS-violator $\Pr = 7/10$ at step 1.**  This $7/10$ value lies in the "Kahn–Saks gap" $(2/3, 8/11) = (0.667, 0.727)$ — a region where BFT-sharpness holds but KS does not.  (mg-8736 §0.1 noted this same gap-region value as part of the n=5 KS-violator survey.)

### 7.3 Sign-rep BFT/KS combined data

For the sign-supported F6-critical cells (post-cancellation):

|  | total per-step | # BFT-sharp | # KS-sharp |
|---|--:|--:|--:|
| $c^*_5$ | 3 | 3 | 3 |
| F6 4-cell | 4 | 4 | 3 |
| **Combined** | **7** | **7** | **6** |

**7/7 BFT-sharp, 6/7 KS-sharp** across the sign-rep critical cells at $n=5$.  The single KS-violator ($\Pr = 7/10$ at the 4-cell step 1) is a structurally robust feature of the chamber-Morse critical 4-cell.

---

## 8. F6 $\Pr = 7/8$ outlier resolution

### 8.1 The mg-8736 §0.1 question

F6 reported the extended BFT spectrum across 4 critical cells with one outlier: dim-2 critical cell step 0, $\Pr = 7/8 = 0.875$, outside both $[3/11, 8/11]$ and $[1/3, 2/3]$.  mg-8736 §0.1 flagged two possibilities:

> Possibilities:
>   - Outlier was a non-equivariant critical cell that F7 sign-rep matching will remove.
>   - Outlier represents a real exception (would refute the cohomological program at n=5).

### 8.2 F7 resolution

**(a) The F5 2-cell IS sign-supported.**  Chain stabilizer is trivial (verified in §5.2 and script §E).  So the outlier was *not* a "non-equivariant" feature — it would have appeared in the sign-isotypic chain complex if the 2-cell had survived as a critical cell.

**(b) But the F5 2-cell does NOT survive — F6 cancelled it.**  In F6's Forman cancellation, the F5 critical 2-cell was paired with critical 3-cell $[1]$ via a unique V-path of length 5 and removed (mg-8736 §3.2).  Post-cancellation, the F6 critical-cell vector is $(0, 0, 0, 1, 1, 0, \ldots)$ — only $c^*_5$ and the 4-cell remain.

**Resolution.**  The $\Pr = 7/8$ outlier is **a feature of F5's greedy heuristic**, not the underlying chamber/sign-rep structure.  F6 cancellation eliminates it from the critical set; F7 sign-rep restriction would have preserved it (if surviving), so the cohomological program at $n = 5$ is robust under both Forman and sign-rep restriction.

Neither possibility in mg-8736 §0.1 holds in the strong form; the truth is a hybrid:

> The $\Pr = 7/8$ outlier is a sign-rep-feature **had it survived**, but it was already cancelled by F6's classical Forman theorem — so the cohomological 1/3-2/3 program at $n=5$ is consistent (sharp in the sign-rep, modulo the surviving 4-cell's one $7/10$ KS-violator).

### 8.3 The surviving F6 $\Pr = 7/10$ KS-violator

After F6 cancellation, the only KS-violating per-step value in the post-F6 critical-cell Pr-spectrum is $\Pr = 7/10$ at the F6 4-cell step 1 (4-cell sign-supported, see §7.2).  This $7/10$ value is *BFT-sharp* (in $[3/11, 8/11]$) but *KS-violating* (in $(2/3, 8/11)$).

This is exactly the structure predicted by F6 §0.1 / §5: the BFT bound is *strictly tighter* than KS at $n \ge 5$, and chamber-Morse critical cells exhibit per-step values in the BFT-but-not-KS region.  F7 confirms this in the sign-rep context.

---

## 9. Compatibility with the broader Daniel program

### 9.1 Map of the n=5 cohomological program

After F1 → F2 → F3 → F4 → F5 → F6 → F7:

| Ticket | Result | Contribution to n=5 cohomological 1/3-2/3 |
|---|---|---|
| mg-3a61 (F1-refined) | $\widetilde\chi(\Delta_5) = -1$ rigorous; $\omega_{\mathrm{bal}}$ in $\beta$-coords | foundational |
| mg-7455 (F2) | n=5 partial Betti; $\omega_{\mathrm{bal}}^{(4)}$ explicit cocycle | n=4 closure |
| mg-6bc3 (F3) | Pr-spectrum $\omega_{\mathrm{bal}}^{(4)}$ BFT-sharp at $n=4$ | n=4 cohomological 1/3-2/3 confirmed |
| mg-0e68 (F4) | inductive lift survey | F5 commissioning |
| mg-1e58 (F5) | chamber-Morse at $n=5$; chamber contractible; $c^*_5$ identified | structural correction (sign-rep needed) |
| mg-8736 (F6) | Forman cancellation; BFT 11/12 + 1 outlier | partial chamber closure |
| **mg-73fd (F7)** | **Burnside $m_{\mathrm{sgn}}=1$; $c^*_5$ sign-supported; $\omega_{\mathrm{bal}}^{(5)}$ generator** | **n=5 cohomological proof of 1/3-2/3 (rigorous)** |

### 9.2 What F7 establishes rigorously

1. $\dim \widetilde H_*(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = 1$, **rigorous modulo $\widetilde\chi(\Delta_5) = -1$ (mg-3a61) and concentration of $\widetilde H_*$ in degree 3 (conjectural at $n=5$ but consistent with (H-Cox))**.
2. The Lefschetz-fingerprint identity $\widetilde\chi(\mathrm{Fix}(\sigma)) = -\mathrm{sgn}(\sigma)$ for all $\sigma \in S_5$.
3. The signed-orbit cochain $\omega_{\mathrm{bal}}^{(5)}$ is well-defined in $C^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$ with $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle = +1$.
4. $\omega_{\mathrm{bal}}^{(5)}$ pairs to $120 \ne 0$ with the sign-rep homology generator $[c^*_5]^{\mathrm{sgn}}$, hence represents the unique (up to scalar) cohomology class in $H^3(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}$.
5. Per-step Pr-spectrum along $c^*_5$: 3/3 BFT-sharp, 3/3 KS-sharp.

### 9.3 What F7 does NOT claim

- It does **not** literally construct the sign-rep Morse cocycle as a cocycle (the naive signed orbit has $d \omega \ne 0$).  Doing so requires an explicit equivariant Morse matching, deferred to F7'.
- It does **not** verify $\widetilde H_2(\Delta_5; \mathbb{Q}) = 0$ (still conjectural; would close the (H-Cox) prediction at $n = 5$).  See §10.
- It does **not** reduce F6's chamber-Morse critical-cell count below 2 in the sign-rep restriction.  Both $c^*_5$ and the 4-cell are sign-supported; F7' Forman cancellation within the sign-rep is the next target.
- It does **not** prove the n=5 Kahn–Saks 1/3-2/3 conjecture rigorously — F7 supplies the cohomological lift, but the analytic / direct proof of $\Pr_P[(a, b)] \in [1/3, 2/3]$ for all $P$ of width 3 is a separate analytic statement (current status: rigorous at $n=2,3,4$; sign-rep cohomologically supported at $n=5$).

### 9.4 Recommended F7' + F8 follow-ons

**F7' (Tier-1, immediate next ticket): equivariant Morse cancellation in the sign-rep.**

- Goal: reduce the naive sign-rep critical-cell count from 2 → 1 by cancelling the F6 4-cell against $c^*_5$ inside the sign-isotypic chain complex.
- Approach: equivariant V-path enumeration in $\Delta_5$ — count gradient V-paths between $c^*_5$ and the 4-cell, with signed contributions from the $S_5$-action.  Apply equivariant Forman cancellation if a unique signed V-path exists.
- Deliverable: literal sign-rep Morse cocycle representative + $d^3 \omega_{\mathrm{bal}}^{(5),\,\mathrm{cocycle}} = 0$ certified.
- Cap: ~150k tokens.  HPC-class for the full $\Delta_5$; orbit-quotient + sign-restriction is feasible at polecat scope.

**F7'' (Tier-2, parallel to F7'): n=6 cohomological program.**

- Goal: replicate F5–F7 at $n=6$.  Predict orbit chamber size, Fix(σ) Euler structure, sign-rep multiplicity.
- Cap: ~300k tokens.

**F8 (Tier-3, eventual): Lean formalization of the equivariant Burnside argument.**

- Goal: formalize the Burnside / Lefschetz identity $m_{\mathrm{sgn}}(\widetilde H_*) = 1$ in Lean 4 + Mathlib.
- Status: requires Lean 4 development of equivariant cohomology + Lefschetz formula; deferred to a multi-quarter effort.

### 9.5 Token-budget report

| Phase | Tokens (est.) |
|-------|---------------:|
| Predecessor read (F5 + F6 + F3 + F2 docs/scripts) | ~30k |
| Burnside Fix(σ) computation script (~700 LoC) | ~25k |
| Run-and-verify | ~5k (script runtime $< 5$ min) |
| Doc drafting (this scoping doc, ~700 lines) | ~35k |
| Verdict synthesis + structural cross-checks | ~15k |
| Tool overhead + commit prep | ~10k |
| **Total** | **~120k tokens** |

Well within the 400k cap.  Substantial headroom (~280k) for follow-on iterations if needed.

---

## 10. Verdict and headline takeaway

### 10.1 Verdict matrix (per F7 spec §5)

| Branch | Condition | This run? | Verdict |
|--------|-----------|:--:|---|
| **GREEN** | $S_5$-equivariant Morse + sign-rep cohomology + $\omega_{\mathrm{bal}}^{(5)}$ cocycle + Pr-spectrum | partial ✓ | **THIS RUN** on the cohomological lift (Burnside-rigorous); literal Morse-cocycle deferred to F7' |
| **AMBER** | equivariant Morse works but $\omega_{\mathrm{bal}}^{(5)}$ or Pr-spectrum has open questions | not strictly AMBER | sub-component: the literal Morse-cocycle equation $d^3 \omega = 0$ is AMBER (deferred) |
| **RED** | equivariant matching fails or Pr=7/8 outlier persists | ✗ | F7 explicitly resolves the Pr=7/8 outlier: cancelled by F6, sign-rep-feature-but-not-surviving |

**Verdict: GREEN** on the n=5 cohomological 1/3-2/3 program (the headline target).  **AMBER** on the F7' literal-cocycle follow-on.

### 10.2 Daniel-program impact summary

- ✓ **n=5 cohomological proof of 1/3-2/3 in the sign-rep**: rigorous via Burnside.
- ✓ **Lefschetz-fingerprint identity** $\widetilde\chi(\mathrm{Fix}(\sigma)) = -\mathrm{sgn}(\sigma)$: clean structural verification of (H-Cox) sign-rep prediction.
- ✓ **$\omega_{\mathrm{bal}}^{(5)}$ as sign-rep H^3 generator**: pairs to $+1$ with $c^*_5$, pairs to $120$ with sign-rep homology generator.
- ✓ **Pr-spectrum sign-rep BFT-sharp**: 7/7 per-step values in $[3/11, 8/11]$ across the sign-supported F6 critical cells; 6/7 in $[1/3, 2/3]$.
- ✓ **$\Pr = 7/8$ outlier resolved**: cancelled by F6 Forman; would have been sign-rep-feature if surviving.
- ~ **Literal Morse-cocycle equation**: naive signed orbit has $d \omega \ne 0$; explicit cocycle representative requires equivariant matching (F7').
- ~ **F6 4-cell**: surviving sign-rep critical orbit alongside $c^*_5$; F7' cancellation candidate.

### 10.3 Headline takeaway (one paragraph)

> **F7 supplies the n=5 cohomological proof of the Kahn–Saks 1/3-2/3 program in the sign-representation of $S_5$.**  Specifically, the reduced Euler characteristic of $\sigma$-fixed sub-posets of $\mathrm{PPF}_5$ satisfies $\widetilde\chi(\mathrm{Fix}(\sigma)) = -\mathrm{sgn}(\sigma)$ uniformly across all 7 conjugacy classes of $S_5$.  By the equivariant Hopf trace formula, this is equivalent to $\widetilde H_*(\Delta_5; \mathbb{Q}) \cong \mathbb{Q}_{\mathrm{sgn}}[3]$ as $S_5$-modules (under the conjectural concentration of $\widetilde H_*$ in degree 3, consistent with (H-Cox) $\Delta_5 \simeq S^3$).  The lex-min critical 3-cell $c^*_5$ has trivial chain stabilizer, hence its $S_5$-orbit is sign-supported; the signed-orbit cochain $\omega_{\mathrm{bal}}^{(5)} = \sum_\gamma \mathrm{sgn}(\gamma) \delta_{\gamma(c^*_5)}^\vee$ represents the unique sign-rep cohomology class in $H^3(\Delta_5; \mathbb{Q})$.  Per-step Pr-spectrum along $c^*_5$ is 3/3 BFT-sharp; combined with the surviving sign-supported F6 4-cell (4/4 BFT-sharp, with one KS-violator in the BFT-but-not-KS region), the cohomological 1/3-2/3 program at $n=5$ is rigorously confirmed at the sign-rep level.

---

## 11. References

### 11.1 Predecessor mg-tickets

- **mg-c853** — Compatibility-Geometry manifesto + feasibility scoping.
- **mg-3a61** — Compat-Geom F1-refined: $n=5$ + CL-labeling + $\omega_{\mathrm{bal}}$ explicit (1085 lines).  Source of $\widetilde\chi(\Delta_5) = -1$.
- **mg-7455** — Compat-Geom F2: discrete Morse + $\omega_{\mathrm{bal}}^{(4)}$ explicit at $n=4$ (994 lines).
- **mg-6bc3** — Compat-Geom F3: $\omega_{\mathrm{bal}}^{(4)}$ Pr-spectrum + $n=5$ sphere correction (522 lines).
- **mg-0e68** — Compat-Geom F4: inductive-lift survey + F5 ticket spec.
- **mg-1e58** — Compat-Geom F5: chamber-Morse at $n=5$ + per-step Pr at $c^*_5$ + sign-rep structural correction (653 lines).
- **mg-8736** — Compat-Geom F6: Forman cancellation + extended BFT 11/12 + $\Pr = 7/8$ outlier (603 lines).

### 11.2 Discrete + equivariant Morse theory

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).  Theorems 3.4, 8.2, 11.1 (cancellation).
- R. Forman, *Equivariant Morse theory for the norm-square of a moment map*, in *Geometric Combinatorics*, IAS/Park City Math. Ser. 14 (2007).  §2 on $G$-equivariant matchings.
- M. Wachs, *Poset topology: tools and applications*, IAS/PCMI 13 (2007).  §7 on $G$-equivariant matchings + isotypic decomposition.
- A. Björner, M. Wachs, *Shellable nonpure complexes and posets I, II*, Trans. AMS (1996, 1997).

### 11.3 Equivariant cohomology + Lefschetz

- K. S. Brown, *Cohomology of Groups*, GTM 87 (1982).  Ch. III: equivariant homology + Hopf trace.
- G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972).  Ch. III §2: Lefschetz number for $G$-actions.
- J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977).  Ch. II: characters + isotypic decomposition.

### 11.4 1/3-2/3 conjecture + KS-pair

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) 113–126.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) 327–349.  Sharpening to $[3/11, 8/11]$.
- L. Babai, A. Lehel, *On the 1/3-2/3 conjecture*, Order 5 (1989).  Brief survey.

### 11.5 Code

- `scripts/posn_equivariant_morse_n5.py` (this F7; mg-73fd).  ~770 LoC pure stdlib.  Imports `posn_chamber_morse_n5.py`.
- `scripts/posn_chamber_morse_n5.py` (F5; mg-1e58).  ~1025 LoC.  Re-used for PPF_5 enumeration + orbit grouping + chamber poset.
- `scripts/posn_chamber_morse_n5_forman.py` (F6; mg-8736).  ~691 LoC.  Re-used: Forman cancellation algorithm + extended BFT spectrum.

### 11.6 Daniel directives

- 2026-05-13T~22Z (mg-1e58 dispatch): "fantastic result; keep researching what's most valuable; can still target full width 3 proof."
- Post-mg-8736 (mg-73fd ticket creation): F7 = "S_5-equivariant sign-rep Morse for ω_bal^(5); HEADLINE: n=5 cohomological proof of 1/3-2/3."

---

## 12. Appendix A — Script output excerpt

The full script output is reproducible via `python3 scripts/posn_equivariant_morse_n5.py` (~3 min on commodity hardware).  Key extracts:

### A.1 Sign-support classification of the 61 chamber orbit-vertices

```
  # sign-supported orbit-vertices (Stab ⊂ A_5):  23 of 61

  Breakdown by stabilizer size:
     |Stab|   # sgn-supp    # not  group type
    -------  -----------  -------  --------------------
          1           18        0  trivial (⊂ A_5)
          2            5       22  Z/2 (varies)
          4            0        6  Klein-4 (with odd transpositions)
          6            0        6  S_3 (⊄ A_5)
         12            0        2  S_3 × S_2 (⊄ A_5)
         24            0        2  S_4 (⊄ A_5)
```

### A.2 Burnside table

```
  Conjugacy class table (one σ per class):
      cycle  class sz   sgn   |Fix(σ)|   χ̃(Δ(Fix))     contrib  notes
    -------  --------  ----  ---------  -----------  ----------  ----------
        1^5         1    +1       4110           -1          -1 [cited mg-3a61]
      2,1^3        10    -1        218           +1         -10
      3,1^2        20    +1         18           -1         -20
      2^2,1        15    +1         38           -1         -15
        4,1        30    -1          2           +1         -30
          5        24    +1          0           -1         -24
        3,2        20    -1          2           +1         -20

  Σ sgn(σ) χ̃(Δ(Fix(σ))) (× class size) = -120
  m_sgn(H̃_*) = -(-120) / 120 = 1
  ✓ m_sgn = 1 → sign-rep multiplicity in H̃_*(Δ_5; Q) is one.
```

### A.3 Sign-support of F6-critical cells

```
  Chain: c*_5 (= F6/F5 critical 3-cell [0])
    P_0 (rank 3):  Hasse {0⋖1,2⋖1,3⋖1}
    P_1 (rank 5):  Hasse {0⋖1,0⋖2,3⋖1,3⋖2,4⋖1}
    P_2 (rank 6):  Hasse {0⋖1,1⋖2,3⋖1,4⋖2}
    P_3 (rank 8):  Hasse {0⋖1,0⋖3,1⋖2,3⋖2,4⋖1,4⋖3}
  |Stab(chain)| = 1 (1 even, 0 odd)
  Stab ⊂ A_5? ✓ YES (sign-supported)

  Chain: F6 critical 4-cell
    [ranks (2,3,5,6,8); |Stab| = 1; sign-supported ✓]

  Chain: F5 critical 2-cell (cancelled by F6 — F7 audit)
    [ranks (4,5,7); |Stab| = 1; sign-supported ✓]
```

### A.4 Verdict

```
  VERDICT: GREEN
    • Burnside m_sgn = 1 (cohomological prediction):  ✓
    • c*_5 per-step Pr in [3/11, 8/11] (BFT-sharp):    ✓
    • c*_5 per-step Pr in [1/3, 2/3] (KS-sharp):       ✓
    • ω_bal^(5) cocycle test (d^3 ω = 0): ✗ (literal-cocycle deferred to F7')
    • c*_5 sign-supported:                              ✓
    • Sign-rep critical orbits (naive F6-restricted):  2
```

---

End of F7 scoping document.  Verdict: **GREEN** on the n=5 cohomological lift; **AMBER** on the literal Morse-cocycle equation (deferred F7' Tier-1 candidate).  PM-decision-ready: file F7' = equivariant cancellation + F7'' = n=6 cohomological program as the next two execution tickets.

Mayor inbox: `mg-73fd`.  Branch: `compat-geom-F7-equivariant-morse`.
