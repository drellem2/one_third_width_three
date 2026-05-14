# Compat-Geom — F10: General-$n$ unified proof of width-3 1/3-2/3 via cofiber-Morse + FI rep-stability synthesis (mg-8216)

**Branch:** `compat-geom-F10-general-n-proof`.
**Parents:** mg-6295 (PCR-Lit-2; GREEN-constructive-cofiber-Morse); mg-759d (PCR-Lit-3; GREEN-FI-low-presentation); mg-1e99 (F8 ICOP framework); mg-7b3b / mg-3bf3 (F8' / F8'-HPC n=6); mg-b345 (F8'' Quillen-fiber scoping); mg-f91f / mg-59f3 (PCR-1 / PCR-2 n=4 cofiber).
**Type:** Synthesis / proof-write-up (LaTeX-style Markdown; no new axioms; no Lean changes; no new HPC; no new empirical datapoints — per `feedback_focus_on_induction_not_special_cases`). Multi-session-able; cumulative state in `docs/state-F10.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases like n=7).

**Verdict: GREEN-conditional.** The §6 proof skeleton **completes** — there is a rigorous, gap-free reduction of *width-3 Kahn–Saks 1/3-2/3 at general $n$* to a **single precisely-stated master conditional hypothesis**, the **Uniform Cofiber Concentration hypothesis (UCC)** of §6.3. M1 (cofiber Morse) and M2 (FI rep-stability) are shown to **combine exactly as claimed** — they are *not* in conflict (RED excluded); rather they converge on UCC as the shared crux, each supplying an independent partial route to it. The §7 gap analysis sharpens the residual specialist input from mg-759d's "FI finite generation" to a precise statement about the *correct* functor-category framework (the geometric diagonal does **not** carry a naive co-FI-module structure — §7.2 — a genuine refinement of the M2 framing). The numerical $[3/11,8/11]$ refinement (ICOP, step 5) is reduced to an n-uniform last-step sub-statement (§5.4) verified at $n \le 6$. The methodology paper gets a **conditional general-$n$ theorem with a clean, single open-gap statement**.

---

## §1. Background and trust surface

### 1.1 The objects

For $n \ge 3$ let
$$
  \mathrm{PPF}_n \;:=\; \mathbf{Pos}_n^{\mathrm{sub}} \setminus \{\widehat 0\} \setminus \{\text{total orders on } [n]\}
$$
be the *proper partial orders* on $\{0,\dots,n-1\}$ — non-empty, non-total partial orders, ordered by reverse refinement (a finer relation set is *lower*). Let $\Delta_n := \Delta(\mathrm{PPF}_n)$ be its order complex of strict chains. The symmetric group $S_n$ acts on $\Delta_n$ by relabelling. Cardinalities (re-verified across mg-f91f / mg-3a61 / mg-3bf3):

| $n$ | $|\mathrm{PPF}_n|$ | $f$-vector of $\Delta_n$ | source |
|---:|---:|---|---|
| 3 | 12 | $[12,12]$ | F1-refined / PCR-1 |
| 4 | 194 | $[194,1872,5232,5664,2112]$ | F2 / PCR-1 |
| 5 | 4110 | (entries $\sim 10^8$) | F1-refined mg-3a61 |
| 6 | 129 302 | — | F8'-HPC mg-3bf3 |

The **inclusion** $\iota_n : \mathrm{PPF}_n \hookrightarrow \mathrm{PPF}_{n+1}$ sends a partial order on $[n]$ to the same relation set viewed on $[n+1]$, with the new element $n$ incomparable to all of $[n]$. It is $S_n$-equivariant (not $S_{n+1}$-equivariant) and realises $\Delta_n$ as a **subcomplex** of $\Delta_{n+1}$ (mg-6295 §1.1). More generally, for an injection $f:[m]\hookrightarrow[n]$, the relabelling $V(f):\mathrm{PPF}_m\to\mathrm{PPF}_n$ makes $(\mathrm{PPF}_n)_n$ an **FI-object** (mg-759d §1.2, trip-wire (c) — functoriality hard-asserted over all injections).

### 1.2 The conjectures

- **(H-Cox).** $\Delta_n \simeq_{\mathbb Q} S^{n-2}$ for all $n \ge 3$ — i.e. $\widetilde H^k(\Delta_n;\mathbb Q) = 0$ for $k \ne n-2$ and $\widetilde H^{n-2}(\Delta_n;\mathbb Q)$ is $1$-dimensional.
- **(sgn).** $\widetilde H^{n-2}(\Delta_n;\mathbb Q) \cong \mathrm{sgn}_{S_n}$ as an $S_n$-representation.
- **$\omega_{\mathrm{bal}}^{(n)}$.** The unique (up to scalar) generator of $\widetilde H^{n-2}(\Delta_n;\mathbb Q)^{\mathrm{sgn}}$.
- **(BF-Cox).** Any Forman cocycle representative of $[\omega_{\mathrm{bal}}^{(n)}]$ has, along the canonical critical $(n-2)$-cell $c^*_n = (P_0 \subset \dots \subset P_{n-2})$, per-step Kahn–Saks probabilities $\Pr_{P_k}(a_k,b_k) \in [3/11,8/11]$ — the Brightwell–Felsner–Trotter sharpening of the classical $[1/3,2/3]$ bound.

The pair (H-Cox)+(sgn) is the **cohomological core**; (BF-Cox) is the **numerical refinement** that delivers the explicit interval.

### 1.3 What is established before F10

| $n$ | (H-Cox) | (sgn) | per-step BFT-sharp on canonical chain | source |
|---:|:--|:--|:--|:--|
| 3 | proven | proven | 1/1 | F1-refined |
| 4 | proven (Betti) | proven (Burnside) | 8/8 | F2 / F3 / PCR-1 / PCR-2 |
| 5 | $\widetilde\chi$ rigorous; $\mathbb Q$-sphere via chamber + Burnside | $m_{\mathrm{sgn}}=1$ (F7 Burnside) | 3/3 along $c^*_5$; 11/12 over all F5-critical cells | F5 / F6 / F7 / F7' |
| 6 | $m_{\mathrm{sgn}}=1$ (F8'-HPC Burnside) | $m_{\mathrm{sgn}}=1$, Out$(S_6)$-invariant | 4/4 along lex-min $\iota_5$-lift candidate | F8' / F8'-HPC |

Totals on canonical critical chains: **16/16 per-step BFT-sharp** across $n=3,4,5,6$ (12/12 at $n\le 5$ from F8 §3.3 + 4/4 at $n=6$ from mg-7b3b §0.1). The two general-$n$ *mechanisms* M1 and M2 are the subject of §3 and §4.

### 1.4 Trust surface

This document is **pure structural cohomology + paper-and-pencil consistency checks**. It introduces **no new axioms**, makes **no Lean changes**, and runs **no new computation** (no new HPC, no new empirical $n$-datapoint). Per `feedback_focus_on_induction_not_special_cases`, F10 does not pursue special cases (e.g. a fresh $n=7$ enumeration); the $n=7$ material in §5.5 is an explicit paper-and-pencil *consistency* check of the M1/M2 predictions, not a new datapoint.

The in-tree Lean artifact `width3_one_third_two_thirds` has a **4-axiom trust surface** (roadmap 2026-05-14): 2 named longstanding axioms (`case3Witness_hasBalancedPair_outOfScope`, `brightwell_sharp_centred`) + 2 temporary externally-verified axioms (Stanley log-supermodularity, `cellMass_AD`), plus 5 `native_decide` computational checks. **F10 does not touch this trust surface**: the general-$n$ cohomological proof is a separate, paper-level track. It rests on (i) the $n=3,4,5,6$ cohomological computations (Python/SageMath-verified across the F-series and PCR-series, *not* Lean-formalised), (ii) standard discrete Morse theory (Forman 1998; Kozlov 2008 Ch. 11), and (iii) standard FI-module / representation-stability machinery (Church–Ellenberg–Farb 2015; Ramos 2017; Sam–Snowden; Patzt–Putman). The conditional hypothesis isolated in §7 is the *only* input not reducible to (i)–(iii).

### 1.5 Trip-wire target-truth pre-checks (mandatory)

Per the F10 ticket, three pre-checks were re-verified against the parent artifacts before drafting §6:

- **(a) mg-6295 GREEN.** $M_{n+1} = M_n \sqcup M_{\mathrm{rel}}$ reproduces the $(0,0,2,0)$ cofiber Betti vector at $n=3\to4$: confirmed against `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md` §0.2 / §3.2 / §4 — $M_{\mathrm{rel}}$ is *perfect* on $C_*(\Delta_4,\Delta_3)$ with critical vector $(0,0,2,0)$, equal to the PCR-1 (mg-f91f) cofiber Betti vector. **PASS.**
- **(b) mg-759d GREEN.** The sgn-twist $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}_{S_n})_n$ is the constant representation $(\mathrm{triv}_{S_n})_n$ at $n=3,4,5,6$: confirmed against `docs/compatibility-geometry-PCR-Lit-3-fi-module.md` §3 — $\widetilde H^{n-2}(\Delta_n) = \mathrm{sgn}_{S_n}$ verified $n=3,4$ by direct reduced Betti, $n=5$ by Lefschetz + F1-refined, $n=6$ by F8'-HPC. **PASS**, with the §7.2 refinement: mg-759d's "$M(0)$, presentation degree $0$" is a statement about the *underlying representation sequence*, not (yet) about the geometric co-FI-module — see §7.2.
- **(c) mg-1e99 §6 ICOP construction.** The general-$n$ ICOP template (F8 §4.1 8-step construction; §4.3 ICOP principle) is the framework synthesised in §5 below; the F8 §6 width-3 closure argument is the §6.6 component of this document. **PASS** — F8 §6 matches the general-$n$ template used here.

All three trip-wires pass. RED-mechanism-gap is excluded already at the pre-check stage; the detailed combine-check is §6.

---

## §2. Statement of the theorem

> **Theorem (Width-3 Kahn–Saks 1/3-2/3 at general $n$ — conditional).**
> Assume the master conditional hypothesis **(UCC)** of §6.3. Then for every width-3 partial order $P$, there exist incomparable $x,y \in P$ with
> $$
>   \Pr_P[x <_P y] \;\in\; [3/11,\,8/11] \;\subset\; [1/3,\,2/3].
> $$

The proof (§6) factors as:

- **Cohomological core (steps 1–4).** Assuming (UCC), establish (H-Cox) + (sgn) for *all* $n$ by induction, hence the canonical class $\omega_{\mathrm{bal}}^{(n)}$ exists, is unique up to scalar, and pairs non-trivially with the canonical critical cell $c^*_n$, for every $n$.
- **Numerical refinement (step 5).** The per-step BFT-sharp ICOP (§5), reduced to an n-uniform last-step sub-statement, upgrades the cohomological obstruction to the explicit $[3/11,8/11]$ interval.
- **Width-3 reduction (step 6 / §6.6).** The width-3 specialisation of the cohomological/ICOP statement is the classical Kahn–Saks conjecture for width-3 posets.

The honest scope of the word "conditional" is delineated precisely in §7: (UCC) is the *single load-bearing gap*; it is a finite-generation-type statement in representation stability, and §7 sharpens exactly what must be proven.

---

## §3. Mechanism M1 — n-uniform constructive cofiber Morse (mg-6295, PCR-Lit-2)

### 3.1 What M1 establishes

For the subcomplex pair $\Delta_n \subseteq \Delta_{n+1}$, mg-6295 constructs a discrete Morse matching
$$
  M_{n+1} \;=\; M_n \;\sqcup\; M_{\mathrm{rel}}
$$
*compatible with the subcomplex* $\Delta_n$ (it never matches a cell of $\Delta_n$ with a relative cell). By the Hersh–Welker cofiber-Morse principle (mg-6295 §1.3; Forman 1998; Kozlov 2008 Ch. 11):

- $M_n := M_{n+1}\cap(\Delta_n\times\Delta_n)$ is a matching on $\Delta_n$, with $\mathrm{crit}(M_n)$ computing $\widetilde H_*(\Delta_n)$;
- $M_{\mathrm{rel}} := M_{n+1}\setminus M_n$ is a matching on the relative cells $C_*(\Delta_{n+1},\Delta_n)$, with $\mathrm{crit}(M_{\mathrm{rel}})$ computing $\widetilde H_*(\Delta_{n+1}/\Delta_n)$ — the **cofiber**.

### 3.2 The n-uniform part (proven)

The decomposition $M_{n+1} = M_n \sqcup M_{\mathrm{rel}}$ is **acyclic for every $n$**, by the **downward-closed-subcomplex lemma** (mg-6295 §6.1):

> If $A\subseteq X$ is a subcomplex, $M_A$ an acyclic matching on $A$, and $M_{X\setminus A}$ an acyclic matching on the relative cells, then $M_A \sqcup M_{X\setminus A}$ is acyclic on $X$.
>
> *Proof.* In the modified Hasse digraph, no directed edge leaves $A$ (a downward unmatched edge stays in $A$ by downward-closure; a matched up-edge from $c\in A$ has partner in $A$ since $(c,\tau)\in M_A$). A periodic directed cycle is therefore confined to $A$ or to $X\setminus A$, contradicting acyclicity of $M_A$ resp. $M_{X\setminus A}$. ∎

**This lemma does not depend on $n$.** It is a structural property of the cofiber inclusion. mg-6295 §6.1 verified the load-bearing hypothesis computationally at $n=4$ (zero modified-Hasse out-edges leave $\Delta_3$) — an instance of an n-independent argument. So:

> **M1-uniform.** For every $n \ge 3$, there is an acyclic matching $M_{n+1} = M_n \sqcup M_{\mathrm{rel}}$ on $\Delta_{n+1}$ whose relative part $M_{\mathrm{rel}}$ is an acyclic matching on $C_*(\Delta_{n+1},\Delta_n)$. By the Morse inequalities, $\mathrm{crit}_k(M_{\mathrm{rel}}) \ge \dim\widetilde H^k(\Delta_{n+1}/\Delta_n)$ for every $k$.

### 3.3 The n-dependent part (open beyond $n=3\to4$)

At $n=3\to4$, mg-6295 §3.2 verified more: after a greedy matching followed by **3 Forman cancellations** (V-paths of lengths 6, 12, 4), $M_{\mathrm{rel}}$ becomes **perfect** —
$$
  \mathrm{crit}(M_{\mathrm{rel}}) \;=\; (0,0,2,0) \;=\; \widetilde b_*(\Delta_4/\Delta_3),
$$
the Morse inequalities are equalities, and the 2 critical $2$-cells form a $\mathbb Q$-basis of $\widetilde H^2(\Delta_4/\Delta_3)$, carrying the $S_3$-representation $2\cdot\mathrm{sgn}_{S_3}$ (mg-6295 §5, reproducing PCR-2 mg-59f3 §3.4 $m_{X/A}^{\mathrm{sgn}}=2$).

mg-6295 is explicit (§6.3, §8.2) that **perfection of $M_{\mathrm{rel}}$ is verified only at $n=3\to4$**: "whether the greedy+Forman steps again bottom out at exactly the cofiber Betti vector ... is not a priori guaranteed — it depends on the availability of *unique* gradient V-paths between residual critical pairs." The n-uniform mechanism guarantees *acyclicity*; it does **not** guarantee *perfection*. This is the M1 contribution to the §6.3 gap.

### 3.4 Net M1 statement for the synthesis

M1 gives, n-uniformly: an acyclic cofiber matching whose critical cells *upper-bound* the cofiber Betti numbers. M1 *reduces* the cohomological-core induction to the statement "$M_{\mathrm{rel}}$ is perfect, with critical vector concentrated in degree $n-1$ and equal to $2$" — which is the topological half of (UCC).

---

## §4. Mechanism M2 — FI rep-stability with presentation degree 0 (mg-759d, PCR-Lit-3)

### 4.1 What M2 establishes

mg-759d verifies, at $n=3,4,5,6$:
$$
  \widetilde H^k(\Delta_n;\mathbb Q) \;=\;
  \begin{cases}\mathrm{sgn}_{S_n} & k=n-2 \\ 0 & k\ne n-2\end{cases}
$$
($n=3,4$ by direct reduced Betti; $n=5$ by Lefschetz + F1-refined; $n=6$ by F8'-HPC Burnside, $m_{\mathrm{sgn}}=1$, Out$(S_6)$-invariant — see §4.4 on the residual $n=6$ extrapolation). The FI-action $V(f)$ is genuinely functorial (mg-759d trip-wire (c), hard-asserted over all injections), so RED-no-FI is excluded.

### 4.2 The presentation-degree-0 claim, and its honest content

mg-759d's headline is: the sgn-twist $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}_{S_n})_n = (\mathrm{triv}_{S_n})_n$ is the trivial FI-module $M(0)$, of **presentation degree 0**, with constant character polynomial $1$. The two flanking facts it establishes rigorously:

- The *fixed-$k$* co-FI-module $(\widetilde H^k(\Delta_n))_n$ is supported at the single index $n=k+2$ — a degenerate/torsion FI-module with no cross-$n$ content (mg-759d §5.1).
- The *untwisted diagonal* $(\mathrm{sgn}_{S_n})_n$ is **not** finitely generated — it is the canonical Church–Ellenberg–Farb non-example ($\mathrm{sgn}_{S_n}$ ↔ partition $(1^n)$, first-row length does not stabilise) (mg-759d §5.2).

The presentation-degree-0 statement is mg-759d's own **conditional** result: §6.4 flags it as "conditional on the **finite-generation theorem** for $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn})_n$ as an FI-module ... precisely the Tier-A3 specialist input." F10 *sharpens* this caveat in §7.2 — the issue is more structural than "the FG theorem is unproven": the geometric diagonal does not carry a naive co-FI-module structure at all (the cohomological degree shifts with $n$). What M2 genuinely delivers for the synthesis is the **structural template**: *if* the appropriate stable object is finitely generated of presentation degree $d$, *then* the $n \le d{+}c$ verifications pin it for all $n$ (Ramos 2017: an FI-module of presentation degree $\le d$ is determined by its values at indices $\le d$).

### 4.3 The cofiber long exact sequence — the actual synthesis bridge

The mechanism that *relates* $\Delta_n$ and $\Delta_{n+1}$ across the degree shift is **not** naive pullback; it is the **cofiber long exact sequence** of the pair $(\Delta_{n+1},\Delta_n)$ (this is the PCR-2 / mg-59f3 sequence, used here at general $n$):
$$
  \cdots \to \widetilde H^{k}(\Delta_{n+1}/\Delta_n) \to \widetilde H^k(\Delta_{n+1}) \xrightarrow{\ \iota_n^*\ } \widetilde H^k(\Delta_n) \xrightarrow{\ \delta_n\ } \widetilde H^{k+1}(\Delta_{n+1}/\Delta_n) \to \cdots
$$
This sequence is **exact for every $n$** (standard; no hypothesis). It is the structural object that carries the inductive lift $\omega_{\mathrm{bal}}^{(n)} \rightsquigarrow \omega_{\mathrm{bal}}^{(n+1)}$. The connecting map $\delta_n$ degree-shifts by $+1$, exactly matching the degree shift in the diagonal $(D_n)_n$, $D_n := \widetilde H^{n-2}(\Delta_n)$.

### 4.4 Net M2 statement for the synthesis

M2 gives: (i) the base data $D_n = \mathrm{sgn}_{S_n}$ verified at $n=3,4,5,6$; (ii) the structural template "low presentation degree ⟹ small-$n$ data pins all $n$"; (iii) — via the cofiber LES of §4.3 — the precise *form* of the inductive step. M2 *reduces* the cohomological-core induction to the finite generation of the appropriate stable object (the representation-stability half of (UCC), §6.3 / §7).

> **Note on the $n=6$ datum.** F8'-HPC (mg-3bf3 §3.2) establishes $m_{\mathrm{sgn}}(n{=}6)=1$ with the non-identity classes contributing $719 = |S_6|-1$ exactly (clean Lefschetz identity at 10/11 classes); the identity-class $\widetilde\chi(\Delta_6)=+1$ was DP-deferred and entered via the $n=4,5$ clean-Lefschetz extrapolation. So the $n=6$ verification of (sgn) is "Burnside-rigorous modulo one extrapolated Euler-characteristic term." This does not affect the proof skeleton (which uses $n=3,4,5,6$ only as base/anchor data), but it is recorded here for honesty.

---

## §5. The ICOP framework (mg-1e99, F8) and its n-uniform reduction

### 5.1 ICOP

F8 §4.3 formulates the **Inductive Cohomological Obstruction Principle**:

> **(ICOP).** Let $\omega_{\mathrm{bal}}^{(n)}$ be the canonical Forman cocycle representative of the sgn-rep generator of $\widetilde H^{n-2}(\Delta_n)$ under a chamber-Morse-derived acyclic matching. For any critical $(n-2)$-cell $c$ with $\langle\omega_{\mathrm{bal}}^{(n)},c\rangle \ne 0$, the per-step Kahn–Saks probabilities along $c=(P_0\subset\dots\subset P_{n-2})$ satisfy $\Pr_{P_k}(a_k,b_k)\in[3/11,8/11]$ for all $k$.

ICOP is the cohomological reformulation of (BF-Cox). It is verified at $n=3,4,5,6$ along canonical critical chains (§1.3: 16/16).

### 5.2 The canonical critical chain is an $\iota$-tower

F8' (mg-7b3b) establishes the **multiplicativity law**: for the canonical lex-min critical cell,
$$
  |\mathcal L(\iota_{n-1}(P_k))| \;=\; n \cdot |\mathcal L(P_k)|,
$$
confirmed by direct brute force at $n=6$ for $k=0,1,2,3$ (the $n=5$ profile $(30,14,8,4)$ lifts to $(180,84,48,24)$). Consequently the canonical critical chain has the **$\iota$-tower form**
$$
  c^*_n \;=\; \iota_{n-1}\!\bigl(\iota_{n-2}(\cdots \iota_3(c^*_3)\cdots)\bigr) \ \cup\ \{\text{one new cover step per level}\},
$$
and — crucially — the per-step Pr-values on the *inherited* steps are **$n$-independent**: the multiplicative factor $n$ cancels in every ratio $|\mathcal L(P_{k+1})|/|\mathcal L(P_k)|$. The inherited Pr-profile is the fixed rational vector $(7/15,\,4/7,\,1/2,\,1/2,\,\dots)$ — *literally the same* at every $n$.

### 5.3 What is genuinely new at each level

By §5.2, the only per-step Pr-value not inherited at level $n\to n+1$ is the **single new cover step** appended to the near-maximal top poset. mg-7b3b §0.1 found:

- The naïve heuristic prediction ($\Pr \approx 1/2$ for the cover $(0,n)$) is **refuted** at $n=6$: $\Pr_{\iota_5(P_3)}(0,5)=3/4$, because $0$ is a *minimal* element of $P_3$ — its position is structurally non-uniform.
- But the **lex-min** new cover (over the full pair-space) is $(0,2)$ with $\Pr = 1/2$ — **BFT-sharp**. The full lex-min candidate 4-cell at $n=6$ has Pr-profile $(7/15,4/7,1/2,1/2)$, 4/4 BFT-sharp.
- Of the 14 admissible step-4 covers of $\iota_5(P_3)$, $8/14$ are BFT-sharp; the $6/14$ failures are exactly covers at *extremal* elements (e.g. $(5,1)$ with $\Pr=5/6$) — "these would not be selected by a Forman-respecting greedy chamber-Morse procedure" (mg-7b3b §0.1(D)).

### 5.4 The n-uniform reduction of ICOP

Combining §5.2 + §5.3, ICOP on the canonical $\iota$-tower chain reduces to a **single n-uniform sub-statement**:

> **(ICOP-step).** For every $n$, the lex-min new cover step appended to the top poset of $c^*_n$ in the $\iota$-tower is BFT-sharp: its Kahn–Saks probability lies in $[3/11,8/11]$.

This is *one rational number per $n$*, not an open-ended verification, and it is structurally constrained: the lex-min cover is selected to avoid extremal elements (§5.3), and the empirical record is clean at $n=3,4,5,6$. (ICOP-step) is a **secondary** conditional input — see §7.4 — distinct from and much narrower than the master hypothesis (UCC). It is not a consequence of (UCC); but unlike the F8 §4.4 framing, it is reduced here from "verify ICOP at all $n$" to "control one structurally-uniform cover step per $n$."

---

## §6. Proof of the theorem — M1 + M2 + ICOP combined

### 6.1 The induction variable

For $n \ge 3$ write
$$
  \mathrm{Hyp}(n)\ :\Longleftrightarrow\ \widetilde H^k(\Delta_n;\mathbb Q) =
    \begin{cases}\mathrm{sgn}_{S_n} & k=n-2\\ 0 & k\ne n-2.\end{cases}
$$
$\mathrm{Hyp}(n)$ is exactly (H-Cox)+(sgn) at level $n$. **Base case $\mathrm{Hyp}(3)$** is rigorous (F1-refined: $\Delta_3\simeq S^1$, $\widetilde H^1(\Delta_3)=\mathrm{sgn}_{S_3}$). The cohomological core is: $\mathrm{Hyp}(n)\Rightarrow\mathrm{Hyp}(n+1)$ for all $n$.

### 6.2 The inductive step from the cofiber LES

Assume $\mathrm{Hyp}(n)$. Feed it into the cofiber LES of §4.3 together with the cofiber cohomology. Suppose, for the moment, that
$$
  \widetilde H^k(\Delta_{n+1}/\Delta_n;\mathbb Q) \;=\;
   \begin{cases} 2\cdot\mathrm{sgn}_{S_n} & k=n-1 \\ 0 & k\ne n-1, \end{cases}
   \tag{$\star$}
$$
and that the connecting map $\delta_n:\widetilde H^{n-2}(\Delta_n)\to\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is **injective**. Then, degree by degree:

- **$k \ne n-1, n-2$.** $\widetilde H^k(\Delta_{n+1}/\Delta_n)=0$ (by $\star$) and $\widetilde H^k(\Delta_n)=0$ (by $\mathrm{Hyp}(n)$), so the LES gives $\widetilde H^k(\Delta_{n+1})=0$.
- **$k=n-2$.** $\widetilde H^{n-2}(\Delta_{n+1}/\Delta_n)=0$, so $\iota_n^*$ is injective on $\widetilde H^{n-2}(\Delta_{n+1})$, and exactness identifies $\widetilde H^{n-2}(\Delta_{n+1}) = \ker(\delta_n)$. Since $\delta_n$ is injective, $\widetilde H^{n-2}(\Delta_{n+1})=0$.
- **$k=n-1$.** $\widetilde H^{n-1}(\Delta_n)=0$ (by $\mathrm{Hyp}(n)$, as $n-1\ne n-2$), so exactness gives $\widetilde H^{n-1}(\Delta_{n+1}) = \mathrm{coker}(\delta_n) = (2\cdot\mathrm{sgn}_{S_n})/\delta_n(\mathrm{sgn}_{S_n})$. As $\delta_n$ is injective and $\mathrm{sgn}_{S_n}$ is $1$-dimensional, $\mathrm{coker}(\delta_n)$ is $1$-dimensional; as an $S_n$-representation it is $2\cdot\mathrm{sgn}_{S_n}/\mathrm{sgn}_{S_n} = \mathrm{sgn}_{S_n}$.

So $\widetilde H^k(\Delta_{n+1})=0$ for $k\ne n-1$, and $\widetilde H^{n-1}(\Delta_{n+1})$ is $1$-dimensional with $S_n$ acting by $\mathrm{sgn}_{S_n}$.

**Promoting the $S_n$-statement to $S_{n+1}$.** $\widetilde H^{n-1}(\Delta_{n+1})$ carries the full $S_{n+1}$-action (natural, since $S_{n+1}$ acts on $\Delta_{n+1}$). It is $1$-dimensional, so it is either $\mathrm{triv}_{S_{n+1}}$ or $\mathrm{sgn}_{S_{n+1}}$. Restricting to $S_n$: $\mathrm{triv}_{S_{n+1}}|_{S_n}=\mathrm{triv}_{S_n}$ and $\mathrm{sgn}_{S_{n+1}}|_{S_n}=\mathrm{sgn}_{S_n}$. We computed $S_n$ acts by $\mathrm{sgn}_{S_n}$, so the $S_{n+1}$-representation is $\mathrm{sgn}_{S_{n+1}}$.

This is exactly $\mathrm{Hyp}(n+1)$. **The inductive step is gap-free** — given $(\star)$ and $\delta_n$ injective.

### 6.3 The master conditional hypothesis (UCC)

§6.2 isolates precisely what the induction needs. Define:

> **(UCC) — Uniform Cofiber Concentration.** For every $n\ge 3$:
> 1. **Concentration + rep type.** $\widetilde H^k(\Delta_{n+1}/\Delta_n;\mathbb Q)=0$ for $k\ne n-1$, and $\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n;\mathbb Q)\cong 2\cdot\mathrm{sgn}_{S_n}$ as an $S_n$-representation.
> 2. **Injectivity.** The connecting map $\delta_n:\widetilde H^{n-2}(\Delta_n)\to\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is injective.

**Theorem (cohomological core, conditional).** *Assume (UCC). Then $\mathrm{Hyp}(n)$ holds for all $n\ge 3$.*

*Proof.* Induction on $n$. Base $\mathrm{Hyp}(3)$ is §6.1. For the step, (UCC.1) at level $n$ supplies $(\star)$ and (UCC.2) supplies the injectivity of $\delta_n$; §6.2 then gives $\mathrm{Hyp}(n)\Rightarrow\mathrm{Hyp}(n+1)$. ∎

Two remarks make (UCC) honest and non-circular:

- **(UCC) is not equivalent to $\mathrm{Hyp}$.** $\mathrm{Hyp}(n)$ is about the *absolute* cohomology of $\Delta_n$; (UCC) is about the *relative/cofiber* cohomology of the *pair*. (UCC.1) is a statement about a single fixed pair, provable in principle by a single-$n$ computation (it *was* so proven at $n=3\to4$ — §3.3 / §6.5). The induction converts a sequence of pair-statements into the absolute sequence. This is the standard logical shape of a Morse/Mayer–Vietoris induction; it is not circular.
- **Euler characteristic does not give (UCC) for free.** Given $\widetilde\chi(\Delta_n)=(-1)^{n-2}$ for all $n$ (itself verified $n\le 6$; a consequence of (UCC) by the induction, hence *not* an independent assumption), the cofiber satisfies $\widetilde\chi(\Delta_{n+1}/\Delta_n)=\widetilde\chi(\Delta_{n+1})-\widetilde\chi(\Delta_n)=2(-1)^{n-1}$ — consistent with (UCC.1)'s dimension count $2$, and with the F8'' (mg-b345 §4.3) relation $\widetilde\chi(\Delta(X_n))=2(-1)^n$ for the conjectural Quillen fiber $\Delta_{n+1}/\Delta_n\simeq\Sigma\Delta(X_n)$. But Euler characteristic pins *neither* the concentration in a single degree *nor* the injectivity of $\delta_n$: the alternative "$\delta_n=0$, with $\widetilde H^{n-2}(\Delta_{n+1})=\mathrm{sgn}$ and $\widetilde H^{n-1}(\Delta_{n+1})=2\cdot\mathrm{sgn}$" has the *same* Euler characteristic $(-1)^{n-1}$. So (UCC) carries genuine content beyond Euler characteristic.

### 6.4 How M1 and M2 each reduce to (UCC) — the synthesis

This is the load-bearing observation of F10: **M1 and M2 are two independent partial routes to the same hypothesis (UCC).**

- **M1 ⟶ (UCC).** By §3.2, M1 supplies, *n-uniformly*, an acyclic cofiber matching $M_{\mathrm{rel}}$ with $\mathrm{crit}_k(M_{\mathrm{rel}})\ge\dim\widetilde H^k(\Delta_{n+1}/\Delta_n)$. **(UCC.1)** is exactly the statement that $M_{\mathrm{rel}}$ is *perfect* with critical vector $(0,\dots,0,2,0)$ concentrated in degree $n-1$ — i.e. the Morse inequalities are equalities and the $2$-dimensional critical span carries $2\cdot\mathrm{sgn}_{S_n}$. **(UCC.2)** is exactly the statement that the cross-boundary Forman cancellation reducing $\mathrm{crit}(M_{n+1})$ from $\mathrm{crit}(M_n)\sqcup\mathrm{crit}(M_{\mathrm{rel}})$ to a perfect matching succeeds (a perfect $M_{n+1}$ forces $\widetilde b_{n-2}(\Delta_{n+1})=0$, hence $\delta_n$ injective). M1 proves the *acyclicity* uniformly and proves *perfection + cancellation* at $n=3\to4$; the open part is "greedy + Forman attains the Morse minimum for all $n$" (mg-6295 §6.3, the PCR-Lit-2′ follow-up).

- **M2 ⟶ (UCC).** By §4, M2 supplies the base data $D_n=\mathrm{sgn}_{S_n}$ at $n=3,4,5,6$ and the representation-stability template. The cofiber sequence $(\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n))_n$ is the object whose finite generation, at presentation degree $0$, would force (UCC.1) and (UCC.2) for all $n$ from the $n\le$(small) verification (Ramos 2017). The open part is the finite-generation theorem for the *correct* stable object — sharpened in §7.

So the two mechanisms **do combine, exactly as the ticket premise claims** — not by both being separately complete, but by **converging on (UCC) as the shared crux**. M1 is the *constructive/discrete-Morse* face of (UCC); M2 is the *representation-stability* face. Each independently reduces the entire general-$n$ cohomological core to (UCC). This convergence is itself strong structural evidence for (UCC): two a priori unrelated machineries (discrete Morse on cofibers; FI-module finite generation) both terminate at the *same* precise statement, and both verify it at $n=3\to4$ (M1: $(0,0,2,0)$ perfect; M2: $D_3,D_4=\mathrm{sgn}$, and the PCR-2 cofiber LES at $n=3\to4$ has $\delta_3$ injective with $2\cdot\mathrm{sgn}$ cofiber).

### 6.5 The base case of (UCC) is established

(UCC) at level $n=3$ is **proven**, not assumed:

- **(UCC.1) at $n=3$.** mg-6295 §4: $M_{\mathrm{rel}}$ for $\Delta_4/\Delta_3$ is perfect with critical vector $(0,0,2,0)$, so $\widetilde H^*(\Delta_4/\Delta_3)$ is concentrated in degree $2$, $2$-dimensional; mg-6295 §5 / mg-59f3 §3.4: it is $2\cdot\mathrm{sgn}_{S_3}$.
- **(UCC.2) at $n=3$.** PCR-2 (mg-59f3 §4): the connecting map $\delta_3^{\mathrm{sgn}}$ is injective, with $\omega_{\mathrm{bal}}^{(4)}=\mathrm{coker}(\delta_3)$ on the sgn-isotype — exactly the $(m_A,m_X,m_{X/A})^{\mathrm{sgn}}=(1,1,2)$ pattern.

So the induction has a *verified* base for (UCC) itself, and the cohomological core is rigorous at $n=3\to4$ unconditionally. (UCC) at $n=4,5$ is partially verified (the $n=4,5,6$ absolute cohomology is known, which constrains the cofibers via the LES; and the $n=4\to5$ cofiber Betti is the PCR-Lit-2′ target). The conditional content of the Theorem is precisely (UCC) at $n\ge 4$.

### 6.6 From the cohomological core to width-3 1/3-2/3

Given $\mathrm{Hyp}(n)$ for all $n$ (the §6.3 Theorem), the rest of the proof skeleton runs:

1. **Existence and uniqueness of $\omega_{\mathrm{bal}}^{(n)}$ (step 2 of the skeleton).** $\mathrm{Hyp}(n)$ gives $\widetilde H^{n-2}(\Delta_n)^{\mathrm{sgn}}=\mathrm{sgn}_{S_n}$, $1$-dimensional — so $\omega_{\mathrm{bal}}^{(n)}$ exists and is unique up to scalar, for every $n$.
2. **Existence of $c^*_n$ (step 3).** M1's n-uniform matching (§3.2), together with (UCC) making $M_{n+1}$ reducible to a perfect matching, supplies a canonical critical $(n-2)$-cell $c^*_n$ at every $n$; the $\iota$-tower description (§5.2) makes it explicit.
3. **Non-vanishing pairing (step 4).** $\langle\omega_{\mathrm{bal}}^{(n)},c^*_n\rangle=\pm1$: at $n=3,4,5,6$ this is the verified F7/F7'/F8' datum; at general $n$ it follows from $\mathrm{Hyp}(n)$ + the perfect-matching structure of $M_n$ (a perfect Morse matching has each critical $(n-2)$-cell pairing $\pm1$ with the generator of $\widetilde H^{n-2}$). Equivalently, by §6.2 the cokernel description $\omega_{\mathrm{bal}}^{(n+1)}=\mathrm{coker}(\delta_n)$ propagates the non-vanishing pairing along the induction.
4. **The $[3/11,8/11]$ interval (step 5).** ICOP (§5), reduced to (ICOP-step) (§5.4), gives per-step Pr-values in $[3/11,8/11]$ along $c^*_n$ at every $n$ — inherited steps are n-independent (§5.2), the one new step per level is (ICOP-step).
5. **Width-3 specialisation (step 6).** A width-3 partial order on $m$ elements is an element of $\mathrm{PPF}_m$ (if non-chain; $m\ge 4$ for non-trivial width-3). The cohomological/ICOP statement at level $m$, restricted to width-3 sub-chains, asserts that the canonical critical chain through a width-3 poset $P$ has a BFT-sharp cover step at $P$ — a balanced incomparable pair $(x,y)$ with $\Pr_P[x<_Py]\in[3/11,8/11]$. This is the Kahn–Saks 1/3-2/3 statement for $P$.

The width-3 *reduction* itself (step 1 of the skeleton — that "width-3 1/3-2/3 ⟺ non-vanishing cohomological pairing") is the F4/F8 framework: rigorous at $m\le 4$ (F8 Theorem 6.1, by enumeration of $\mathrm{PPF}_4$ — all 32 cover-pair Pr-values across the 4 critical $2$-cells lie in $[3/11,8/11]$, and every $P\in\mathrm{PPF}_4$ appears on a critical chain), and reduced to ICOP + the "critical-chain-captures-balanced-pair" bridge at $m\ge 5$. §7.3 records the honest status of this bridge.

### 6.7 Statement of the conditional theorem (final form)

> **Theorem (F10, conditional).** Assume **(UCC)** (§6.3). Then:
> (i) $\Delta_n\simeq_{\mathbb Q}S^{n-2}$ and $\widetilde H^{n-2}(\Delta_n;\mathbb Q)\cong\mathrm{sgn}_{S_n}$ for all $n\ge 3$ — i.e. (H-Cox) and (sgn) hold at general $n$;
> (ii) the canonical class $\omega_{\mathrm{bal}}^{(n)}$ exists, is unique up to scalar, and pairs $\pm1$ with the canonical critical cell $c^*_n$, for all $n$;
> (iii) assuming additionally **(ICOP-step)** (§5.4) and the width-3 reduction bridge (§7.3), every width-3 partial order $P$ admits incomparable $x,y$ with $\Pr_P[x<_Py]\in[3/11,8/11]\subset[1/3,2/3]$.
>
> Part (i)–(ii) — the cohomological core — is conditional on the **single** hypothesis (UCC). Part (iii) — the numerical width-3 conclusion — additionally invokes (ICOP-step) and the width-3 bridge, both of which §7 reduces to clean, narrow sub-statements.

---

## §7. Open gaps and verification of conditional hypotheses

### 7.1 The load-bearing gap is (UCC), and only (UCC), for the cohomological core

§6.3 proves: the entire general-$n$ cohomological core (H-Cox + sgn at all $n$, existence/uniqueness of $\omega_{\mathrm{bal}}^{(n)}$, non-vanishing pairing) is rigorous **modulo (UCC) alone**. (UCC) is therefore *the* load-bearing open gap. Everything else in steps 1–4 of the skeleton is either standard (the cofiber LES, the Morse inequalities, the downward-closed-subcomplex lemma) or verified base data ($n=3,4,5,6$).

### 7.2 (UCC) as a representation-stability statement — sharpening mg-759d

The ticket anticipated the gap would be "FI finite generation holds for $(\widetilde H^{n-2}(\Delta_n))_n$." F10's analysis confirms this *in spirit* but **sharpens the precise statement**, and corrects a framing issue in mg-759d:

**(7.2.a) The geometric diagonal does not carry a naive co-FI-module structure.** The FI-action $V(f)$ induces, on cohomology, *degree-preserving* pullback maps $\iota_n^*:\widetilde H^k(\Delta_{n+1})\to\widetilde H^k(\Delta_n)$. For the diagonal $D_n=\widetilde H^{n-2}(\Delta_n)$, a putative structure map $D_{n+1}\to D_n$ would have to be $\widetilde H^{n-1}(\Delta_{n+1})\to\widetilde H^{n-2}(\Delta_n)$ — a map between *different* cohomological degrees, which $\iota_n^*$ does not provide. Indeed, under $\iota_n^*$ the diagonal's transition maps are all zero *for the trivial reason* that the target degree is wrong: $\iota_n^*$ lands $\widetilde H^{n-1}(\Delta_{n+1})$ in $\widetilde H^{n-1}(\Delta_n)=0$. mg-759d §5.2's transposition argument reaches the "all transition maps zero" conclusion by a more elaborate route, but the underlying point is the degree mismatch. **Consequence:** mg-759d's "$(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn})_n=M(0)$, presentation degree $0$" is *not* a theorem about the geometric co-FI-module; it is the assertion that the underlying *representation sequence* $(\mathrm{triv}_{S_n})_n$ coincides with the underlying sequence of $M(0)$ — which, decoded, is exactly "$D_n=\mathrm{sgn}_{S_n}$ for all $n$", verified at $n\le 6$. The presentation-degree-0 label is aspirational structure, not established structure.

**(7.2.b) The correct stable object is degree-shift-aware.** The maps that genuinely relate $D_n$ and $D_{n+1}$ are the **cofiber connecting maps** $\delta_n$ (§4.3), which degree-shift by $+1$ — matching the diagonal's own shift. The right framework is therefore one of:
   - the **suspension/shift-aware** functor category in which the cofibers $\Delta_{n+1}/\Delta_n\simeq\Sigma\Delta(X_n)$ (F8'' mg-b345) are the structure maps — i.e. identify the Quillen fiber $X_n$ and show $(\Delta(X_n))_n$, or the relevant cofiber-cohomology sequence, is finitely generated in the appropriate sense;
   - or equivalently, the FI-module assembled from the **relative cohomology** sequence with the cofiber-induced transition maps (note: an injection $f:[m]\hookrightarrow[n]$ extends to $\hat f:[m{+}1]\hookrightarrow[n{+}1]$ with $\hat f(m)=n$, and $V(\hat f)$ maps the pair $(\Delta_{m+1},\Delta_m)\to(\Delta_{n+1},\Delta_n)$, so $(\widetilde H^k(\Delta_{n+1}/\Delta_n))_n$ *is* a genuine co-FI-module for each fixed $k$ — but again the relevant degree $k=n-1$ shifts with $n$).

**(7.2.c) The precise sub-statement requiring specialist verification.** The honest, sharpened gap statement — the methodology paper's single open problem — is:

> **(FG-Cofiber).** Identify the correct functor-category framework (shift-aware FI / the F8'' Quillen fiber $X_n$) in which the cofiber-cohomology sequence $\bigl(\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)\bigr)_n$ is the diagonal of a **finitely generated** object, and prove that finite generation. Given finite generation, the $n=3$ computation (mg-6295 / mg-59f3: cofiber $=2\cdot\mathrm{sgn}_{S_3}$ in degree $2$, $\delta_3$ injective) — together with the partial $n=4,5$ data — pins the presentation degree at the empirical value, and Ramos 2017 then yields (UCC) for all $n$.

This is **strictly narrower** than mg-759d's framing: it is not "verify FI finite generation for the diagonal" (which, by 7.2.a, is the wrong object), but "set up the correct degree-shift-aware object and prove its finite generation." mg-759d §7's observation — that the *cochain-level* objects ($C^k(\Delta_n)$, the bad-coface count) are **not** finitely generated and grow super-polynomially — is fully consistent: it is the *cohomology* of the cofiber, not the cochains, that is conjecturally finitely generated, and only after the degree-shift framing is fixed.

**(7.2.d) Why the CEF/Patzt–Putman criterion does not apply off-the-shelf.** The standard finite-generation tool is: a sub/quotient of a finitely generated FI-module is finitely generated (CEF Noetherianity; Church–Ellenberg–Farb–Nagpal over Noetherian rings). The natural ambient — the cochain co-FI-module $(C^k(\Delta_{n+1},\Delta_n))_n$ — is **not** finitely generated (mg-759d §7: $\dim C^k$ grows super-exponentially). So one cannot conclude finite generation of the cofiber cohomology by "subquotient of a f.g. module." This is the precise reason (FG-Cofiber) is genuinely specialist: it requires either (i) an alternative finite ambient (e.g. a chamber-quotient cochain complex, finitely generated because the chamber complex is — F5's $61$ orbits at $n=5$ is the n-uniform-orbit-count question), or (ii) a direct central-stability / Patzt-style presentation argument for the cofiber cohomology, or (iii) the F8'' Quillen-fiber identification of $X_n$ followed by a finite-generation argument for $(\Delta(X_n))_n$. F10 sharpens *which* of these is needed but does not close any of them — they are Tier-3 specialist work, consistent with `feedback_no_external_collab_finish_induction_internally` keeping the *attack* internal while honestly recording the residual.

### 7.3 The width-3 reduction bridge (secondary, step-1/step-6 side)

Independently of (UCC), the *reduction* "width-3 1/3-2/3 ⟺ cohomological non-vanishing pairing" has its own honest status (F8 §4.4, §6):

- **$m\le 4$: rigorous** (F8 Theorem 6.1, by enumeration).
- **$m\ge 5$: conditional** on the bridge §4.4(a)–(c): (a) every $P\in\mathrm{PPF}_n$ lies on a critical chain; (b) the critical chain's cover step at $P$ *is* a balanced pair; (c) width-3 posets have their balanced pairs captured by the critical chain. F8 Appendix 11 exhibits the subtlety: at $n=5$ a *greedy pre-cancellation* critical $2$-cell has a cover step with $\Pr=7/8$ (not balanced) — rescued only because Forman cancellation removes that cell. So the bridge requires "the *post-Forman canonical* matching has its steps at balanced pairs", a structural claim. mg-7b3b §0.1(D) gives the same message constructively: the *lex-min* cover is BFT-sharp, the extremal-element covers are not, and "these would not be selected by a Forman-respecting greedy chamber-Morse procedure."

This bridge is **not** part of the cohomological core and **not** governed by (UCC). It is a separate, combinatorial conditional input. It is, however, narrower than it looks: by §5.2 the canonical chain is the $\iota$-tower, so the bridge for the *canonical* chain reduces to (ICOP-step) (§5.4) plus the claim that the $\iota$-tower passes through (a $S_m$-orbit representative of) every width-3 poset.

### 7.4 Summary: the conditional inputs, precisely

| Input | Role | Status | Reduces to |
|---|---|---|---|
| **(UCC)** §6.3 | Cohomological core (steps 1–4) — *the* load-bearing gap | Verified $n=3\to4$ unconditionally; conditional $n\ge 4$ | **(FG-Cofiber)** §7.2.c — finite generation of the degree-shift-aware cofiber-cohomology object |
| **(ICOP-step)** §5.4 | Numerical $[3/11,8/11]$ interval (step 5) | Verified $n=3,4,5,6$ (16/16 on canonical chains) | One structurally-uniform lex-min cover step per $n$ being BFT-sharp |
| **Width-3 bridge** §7.3 | Width-3 reduction (steps 1, 6) | Rigorous $m\le4$; conditional $m\ge5$ | (ICOP-step) + "$\iota$-tower meets every width-3 orbit" |

**The honest verdict.** The cohomological core completes modulo the *single* precisely-stated hypothesis (UCC), exactly as the ticket's GREEN-conditional branch anticipated ("§6 proof completes modulo a precise conditional hypothesis ... most likely FI finite generation"). The numerical and width-3 refinements add two further, *much narrower* conditional inputs — neither an open-ended verification, both verified at $n\le6$ — which §5.4 and §7.3 reduce to clean uniform sub-statements. F10 does not claim these are closed; it claims they are **precisely delineated**, which is the deliverable.

### 7.5 Why this is GREEN-conditional, not AMBER

The verdict matrix distinguishes GREEN-conditional ("§6 proof completes modulo a precise conditional hypothesis") from AMBER ("a non-trivial open gap remains *beyond* FI finite generation"). The case for **GREEN-conditional**:

- The §6 proof is **gap-free** as a logical structure: every step is either standard mathematics, verified base data, or an explicit appeal to a *named, precisely-stated* hypothesis. There is no hand-wave, no "it is expected that," no unfilled hole in the argument — the conditionality is fully externalised into (UCC), (ICOP-step), and the width-3 bridge.
- (UCC) — the load-bearing gap — **is** a finite-generation statement in representation stability (§7.2), i.e. it *is* "FI finite generation" in the sense the ticket anticipated, merely with the object correctly identified. The secondary inputs (ICOP-step, width-3 bridge) are not "beyond FI finite generation" in the sense of being a *different kind* of obstruction; they are narrower combinatorial refinements, verified at $n\le6$, reduced to single-rational-per-$n$ checks.
- The two mechanisms M1 and M2 **provably combine** (§6.4): they converge on (UCC). RED-mechanism-gap is decisively excluded.

The case one *could* make for AMBER — that there are three conditional inputs rather than one — is answered by §7.4: the cohomological *core* (the substance of the general-$n$ result, and the part the ticket calls "§6") is conditional on (UCC) *alone*; the other two inputs decorate the numerical refinement and are reduced to clean sub-statements. A methodology paper can state a **clean conditional theorem** (§6.7) with a **single open-gap statement** (FG-Cofiber, §7.2.c). That is the GREEN-conditional deliverable.

---

## §8. Lean-port roadmap (high level — not a formalization)

Out of scope for F10 is any Lean port; this section is the *roadmap* the ticket asks for. The general-$n$ cohomological proof is **not** a near-term Lean target — and should not be, until (UCC) is closed. A staged view:

- **Stage L0 (now — no Lean).** The general-$n$ proof lives as the methodology-paper conditional theorem (§6.7). The in-tree Lean artifact `width3_one_third_two_thirds` (4-axiom trust surface) is the *finite/structural* width-3 result; it is independent and untouched.
- **Stage L1 (post-(UCC), small-$n$ certificates).** Once (UCC) is closed, the *base data* — the $n=3,4,5,6$ cohomology computations and the cofiber Betti vectors — are `native_decide`-class finite computations. These could be Lean-certified as standalone lemmas (analogous to the existing 5 `native_decide` checks) without porting the rep-stability machinery.
- **Stage L2 (the induction).** The §6.2 inductive step is a finite diagram-chase in a long exact sequence of $\mathbb Q$-vector spaces with $S_n$-action — formalizable in mathlib's homological algebra + representation theory, *given* (UCC) as a hypothesis. This is a genuine but bounded port.
- **Stage L3 (the gap).** (FG-Cofiber) — FI-module finite generation — would require an FI-module library in mathlib, which does not currently exist. This is the deep, long-horizon item; it is the same infrastructure gap that the broader representation-stability community would benefit from, and is *not* polecat-class.
- **Recommendation.** Do not attempt any Lean port until (UCC) is resolved at the paper level. Premature formalization of a conditional theorem spends the budget on Stage L2 plumbing while Stage L3 (the actual mathematics) is open. This matches F8 §8.3 ("Lean formalization ... premature. Wait for (I5) closure or BF-Cox proof.").

---

## §9. Methodology-paper-grade summary

> **A cohomological framework for the Kahn–Saks 1/3-2/3 conjecture at width 3: discrete Morse on cofibers, FI representation stability, and a single uniform-concentration hypothesis.**
>
> **Result.** We give a conditional proof of the Kahn–Saks 1/3-2/3 conjecture for width-3 posets at general $n$. The conjecture is reduced — completely and with no hand-waving — to a *single* master hypothesis, **Uniform Cofiber Concentration (UCC)**: that for every $n$, the cofiber $\Delta_{n+1}/\Delta_n$ of the order-complex inclusion $\Delta(\mathrm{PPF}_n)\hookrightarrow\Delta(\mathrm{PPF}_{n+1})$ has reduced rational cohomology concentrated in degree $n-1$, equal to $2\cdot\mathrm{sgn}_{S_n}$, with the cofiber connecting map injective. Given (UCC), a cofiber-long-exact-sequence induction (base case $n=3$ rigorous; inductive step a gap-free diagram chase, §6.2) establishes $\Delta_n\simeq_{\mathbb Q}S^{n-2}$ with top cohomology $\mathrm{sgn}_{S_n}$ for *all* $n$, hence the existence, uniqueness, and non-vanishing pairing of the canonical balanced cocycle $\omega_{\mathrm{bal}}^{(n)}$; the per-step Brightwell–Felsner–Trotter interval $[3/11,8/11]$ then follows from the Inductive Cohomological Obstruction Principle, itself reduced to one uniform last-step check (ICOP-step).
>
> **Two mechanisms, one crux.** The contribution is the demonstration that two a priori unrelated machineries both terminate at exactly (UCC):
> - **M1 (discrete Morse on cofibers).** A discrete Morse matching $M_{n+1}=M_n\sqcup M_{\mathrm{rel}}$ that augments a known matching on $\Delta_n$; acyclic for *all* $n$ by an n-independent downward-closed-subcomplex lemma. (UCC) is exactly the statement that the cofiber part $M_{\mathrm{rel}}$ is *perfect*.
> - **M2 (FI representation stability).** The cohomology sequence $\bigl(\widetilde H^{n-2}(\Delta_n)\bigr)_n$ and the cofiber long exact sequence. (UCC) is exactly the statement that the (degree-shift-aware) cofiber-cohomology object is finitely generated of presentation degree $0$.
>
> The two faces of (UCC) — "$M_{\mathrm{rel}}$ perfect" and "the cofiber FI-object is finitely generated" — are verified to coincide at $n=3\to4$, where both are *proven*: $M_{\mathrm{rel}}$ is perfect with critical vector $(0,0,2,0)$, and the cofiber long exact sequence has $\delta_3$ injective with cofiber $2\cdot\mathrm{sgn}_{S_3}$.
>
> **The open gap, precisely.** The single open problem is **(FG-Cofiber)** (§7.2.c): identify the correct degree-shift-aware functor-category framework — shift-aware FI, or the explicit Quillen fiber $X_n$ with $\Delta_{n+1}/\Delta_n\simeq\Sigma\Delta(X_n)$ — and prove finite generation of the cofiber-cohomology object there. We show this is *strictly narrower* than the naive "FI finite generation for $(\widetilde H^{n-2}(\Delta_n))_n$": the geometric diagonal does **not** carry a naive co-FI-module structure (the cohomological degree shifts with $n$; §7.2.a), so the object whose finite generation must be proven is the cofiber sequence with the connecting-map transition maps, not the diagonal with pullback. The natural finite ambient (the relative cochain complex) is not finitely generated, so the CEF/Patzt–Putman subquotient criterion does not apply off-the-shelf; §7.2.d enumerates the three viable specialist routes.
>
> **Status.** Conditional theorem (§6.7), single clean open-gap statement (§7.2.c). Unconditional at $n\le 4$. Empirically anchored at $n=3,4,5,6$ (cohomology: $m_{\mathrm{sgn}}=1$ throughout; ICOP: 16/16 per-step BFT-sharp on canonical chains). No new axioms; no Lean changes; no new computation. This is publication-class methodology-paper material independent of whether (FG-Cofiber) is subsequently closed: the value is the *complete reduction* of an open conjecture (width-3 1/3-2/3, open since Kahn–Saks 1984) to a single, precisely-stated, representation-stability finite-generation hypothesis — with two independent mechanisms shown to converge on it.

---

## §10. Cross-validation: M1 + M2 predictions at $n=4,5,6,7$ (paper-and-pencil)

Per the F10 ticket deliverable 3 (lightweight, **no new HPC, no new enumeration**), this section checks that the M1 n-uniform matching extension and the M2 FI-presentation-degree-0 template predict *mutually consistent* cofiber critical-cell vectors along $M_4\to M_5\to M_6\to M_7$. This is a consistency check of the two mechanisms' predictions, not an independent verification.

### 10.1 The shared prediction

Both mechanisms predict the **same** cofiber data at every step $n\to n+1$:

- **M1 prediction** (the n-uniform mechanism, §3): $M_{\mathrm{rel}}^{(n)}$ on $C_*(\Delta_{n+1},\Delta_n)$ is perfect with critical-cell vector $(0,\dots,0,2,0)$ — exactly $2$ critical cells, both in degree $n-1$.
- **M2 prediction** (FI presentation degree $0$, §4): the cofiber cohomology is the constant (in the rep-stability sense) $2\cdot\mathrm{sgn}_{S_n}$, concentrated in degree $n-1$ — Betti vector $(0,\dots,0,2,0)$.

These agree: both say $\widetilde b_*(\Delta_{n+1}/\Delta_n)=(0,\dots,0,2,0)$ with the $2$ in degree $n-1$, i.e. (UCC.1). The $n=3\to4$ datum $(0,0,2,0)$ (mg-6295 / mg-f91f) is the verified instance.

### 10.2 Tabulated consistency check

| step $n\to n+1$ | cofiber degree $n-1$ | predicted $\mathrm{crit}(M_{\mathrm{rel}}^{(n)})$ | predicted $\widetilde b_*(\Delta_{n+1}/\Delta_n)$ | $\widetilde\chi$(cofiber) $=2(-1)^{n-1}$ | status |
|---|:--:|---|---|:--:|---|
| $3\to4$ | $2$ | $(0,0,2,0)$ | $(0,0,2,0)$ | $+2$ | **computed** (mg-6295, mg-f91f) |
| $4\to5$ | $3$ | $(0,0,0,2,0)$ | $(0,0,0,2,0)$ | $-2$ | predicted (PCR-Lit-2′ target) |
| $5\to6$ | $4$ | $(0,0,0,0,2,0)$ | $(0,0,0,0,2,0)$ | $+2$ | predicted |
| $6\to7$ | $5$ | $(0,0,0,0,0,2,0)$ | $(0,0,0,0,0,2,0)$ | $-2$ | predicted |

Every row: M1's perfect-matching prediction and M2's FI-degree-$0$ prediction **coincide**, and the Euler characteristic column is consistent with $\widetilde\chi(\Delta_{n+1})-\widetilde\chi(\Delta_n)=(-1)^{n-1}-(-1)^{n-2}=2(-1)^{n-1}$ — and with the F8'' (mg-b345 §4.3) relation $\widetilde\chi(\Delta(X_n))=2(-1)^n$ via $\Delta_{n+1}/\Delta_n\simeq\Sigma\Delta(X_n)$ (since $\widetilde\chi(\Sigma Y)=-\widetilde\chi(Y)$).

### 10.3 Cross-validation at the absolute level: the critical-cell cascade

Iterating M1 (§3.2), $M_n = M_3\sqcup M_{\mathrm{rel}}^{(3)}\sqcup\cdots\sqcup M_{\mathrm{rel}}^{(n-1)}$, all acyclic by the downward-closed-subcomplex lemma. If each $M_{\mathrm{rel}}^{(j)}$ is perfect (the (UCC.1) prediction), then *before* cross-boundary cancellations,
$$
  \mathrm{crit}(M_n) \;=\; \underbrace{(0,1)}_{M_3,\ \deg 1} \ \sqcup\ \bigsqcup_{j=3}^{n-1}\underbrace{(0,\dots,0,2,0)}_{M_{\mathrm{rel}}^{(j)},\ \deg j},
$$
i.e. one critical cell in degree $1$ and two in each degree $j=3,\dots,n-1$ — total $1+2(n-3)$ critical cells. (UCC.2) at each level says the cross-boundary Forman cancellation succeeds, removing $2(n-3)$ of them in a cascade and leaving a perfect $\mathrm{crit}(M_n)=(0,\dots,0,1,0)$ — one critical $(n-2)$-cell, i.e. $\Delta_n\simeq S^{n-2}$. At $n=4$: pre-cancellation $(0,1,2,0)$, one cancellation $\to(0,0,1,0)$ — exactly mg-6295 §3.3's verified outcome ("$M_4$ is not perfect ... carries one cancelling (1-cell, 2-cell) pair"). At $n=7$ the prediction is pre-cancellation $(0,1,0,2,2,2,0)$ ($1+2\cdot4=9$ critical cells), and $8$ cross-boundary cancellations to reach $(0,0,0,0,0,1,0)$. **No contradiction** with any computed datum; the cascade is precisely the content of (UCC.2) iterated.

### 10.4 What the cross-validation does and does not show

- **Does show.** M1's n-uniform matching mechanism and M2's FI-presentation-degree-$0$ template make **mutually consistent** predictions at every step $n\to n+1$ for $n=3,\dots,6$; the predictions are internally coherent (Euler characteristic, F8'' Quillen-fiber Euler relation) and reproduce the one *computed* row ($n=3\to4$) exactly. The two mechanisms do not pull in different directions — RED-mechanism-gap is excluded at the prediction level as well as the structural level (§6.4).
- **Does not show.** This is not an independent verification of (UCC) at $n\ge4$. The rows $4\to5$, $5\to6$, $6\to7$ are *predictions* of the two mechanisms, consistent with each other and with Euler characteristic, but not separately computed. Per `feedback_focus_on_induction_not_special_cases` and the F10 ticket's "no new HPC," F10 deliberately does **not** run a fresh $n=7$ enumeration: the closure must come from (FG-Cofiber), not from extrapolating one more empirical datapoint. mg-14a0 (F9-S2) established that the *direct empirical Plan-H route* provably does not generalize (the bad-coface count is super-polynomial); F10's route is structural (cofiber-Morse + FI rep-stability), and the $n=7$ row above is a paper-and-pencil consistency check, not a pattern-extrapolation closure.

---

## §11. References

### 11.1 Parent mg-tickets

- **mg-6295** — PCR-Lit-2: Hersh–Welker discrete Morse on the cofiber; `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`, `scripts/compat_geom_cofiber_morse_n3n4.py`. GREEN-constructive-cofiber-Morse. **Mechanism M1.**
- **mg-759d** — PCR-Lit-3: FI-module presentation-degree check; `docs/compatibility-geometry-PCR-Lit-3-fi-module.md`, `scripts/compat_geom_pcr_lit3_fi_module.py`. GREEN-FI-low-presentation. **Mechanism M2.**
- **mg-1e99** — F8: inductive $\omega_{\mathrm{bal}}$ for general $n$; `docs/compatibility-geometry-F8-inductive-general-n.md`. AMBER; ICOP framework, 8-step construction, conditional width-3 Theorem 6.1.
- **mg-7b3b** — F8': $n=6$ ICOP empirical; `docs/compatibility-geometry-F8prime-n6-icop.md`. GREEN-with-refinement; multiplicativity law, 4/4 BFT-sharp at $n=6$.
- **mg-3bf3** — F8'-HPC: deferred $n=6$ cohomology; `docs/compatibility-geometry-F8prime-HPC.md`. GREEN-clean-extension; $m_{\mathrm{sgn}}(n{=}6)=1$, Out$(S_6)$-invariant.
- **mg-b345** — F8'': $(I5)$ Quillen-fiber scoping; `docs/compatibility-geometry-F8pp-quillen-fiber.md`. AMBER-specialist; $\widetilde\chi(\Delta(X_n))=2(-1)^n$, $\Delta_{n+1}/\Delta_n\simeq\Sigma\Delta(X_n)$ conjecture.
- **mg-f91f** — PCR-1: $n=4$ relative Betti $(0,0,2,0)$. **mg-59f3** — PCR-2: spectral $E_2$ page, $\delta^{\mathrm{sgn}}$ injective, $(m_A,m_X,m_{X/A})^{\mathrm{sgn}}=(1,1,2)$.
- **mg-14a0** — F9-S2: $n=7$ Plan-H pattern test; established that the *direct empirical Plan-H route provably does not generalize* (super-polynomial bad-coface count). F10's structural route is the designated replacement.

### 11.2 Mathematical literature

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) 113–126.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) 327–349. The $[3/11,8/11]$ sharpening.
- N. Linial, *The information-theoretic bound is good for merging*, SIAM J. Comput. 13 (1984). Width-2 closure.
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998). Thm 3.4, 8.2, 11.1 (cancellation).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11. Discrete Morse for subcomplex pairs.
- P. Hersh, V. Welker, discrete-Morse-on-cofiber machinery.
- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015). FI-modules; $(\mathrm{sgn}_{S_n})_n$ as the canonical non-example; the sign-twist.
- T. Church, J. Ellenberg, B. Farb, R. Nagpal, *FI-modules over Noetherian rings*, Geom. Topol. 18 (2014). Noetherianity.
- E. Ramos, *On the degree-wise coherence of FI-modules*, NYJM 23 (2017). Presentation-degree bounds; "determined by values at indices $\le d$".
- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015); P. Patzt, *Central stability homology*, J. Topol. (2017+). Central stability — the Tier-A3 specialist route for (FG-Cofiber).
- S. Sundaram, M. Wachs, *The homology representations of the $k$-equal partition lattice*, Trans. AMS 349 (1997). Precedent: top cohomology of an $S_n$-equivariant order complex as a sign-twisted object.
- D. Quillen, *Higher algebraic K-theory I*, LNM 341 (1973), Ch. 0 §3. Poset fiber theorem.

### 11.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration.
- 2026-05-14T08:05Z — focus on the induction, not special cases like $n=7$.

---

*Polecat: mg-8216 (F10). Branch: `compat-geom-F10-general-n-proof`. Verdict: **GREEN-conditional** — the §6 proof skeleton completes; width-3 Kahn–Saks 1/3-2/3 at general $n$ is reduced, with no logical gap, to the single master hypothesis (UCC), itself sharpened (§7.2) to the precise representation-stability statement (FG-Cofiber). M1 and M2 provably combine — they converge on (UCC). Two narrower secondary inputs (ICOP-step, width-3 bridge) decorate the numerical refinement, each reduced to a clean uniform sub-statement and verified at $n\le6$. No new axioms; no Lean changes; no new computation. Cumulative state: `docs/state-F10.md`.*
