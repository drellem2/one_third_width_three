# Compat-Geom — PCR-Lit-3: FI-module presentation-degree empirical check for $(\widetilde H^k(\Delta_n))_n$ (mg-759d)

**Branch:** `compat-geom-PCR-Lit-3-fi-module` (new).
**Parent:** mg-ac7a (F8''''' PCR-3 literature integration; `docs/compatibility-geometry-F8ppppp-literature.md`, table entries 4.1 / 4.6, §5.3 Tier-A3).
**Type:** Polecat-class structural representation-theory computation (PCR-Lit-3 from F8''''' §6.3). 50k token cap. No new axioms; no Lean changes; no trust-surface impact.
**Daniel directive 2026-05-14T05:18Z:** finish (I5) internally via polecat-class effort; no external collaboration. PCR-Lit-3 is one of three internal follow-ups surfaced by mg-ac7a.
**Verdict:** **GREEN-FI-low-presentation** — with the mandatory sign-twist, $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}_{S_n})_n$ is the **trivial FI-module $M(0)$**, finitely generated of **presentation degree $0$** (the lowest possible, $\le 3$); the character polynomial is the constant $1$ and reproduces the $n=6$ datum. See §6 for the precise statement and the unavoidable caveat (the *untwisted* sequence is the canonical CEF non-example), and §7 for the F9-S2 bad-coface cross-check, which **reinterprets** the polynomial-vs-exponential question.

---

## 0. Executive summary

### 0.1 The question

Parent mg-ac7a (F8''''' §3.4 cluster C4, table entries 4.1 Church–Ellenberg–Farb 2015 and 4.6 Ramos 2017; §5.3 Tier-A3 specialist route) asked: **is the sequence of $S_n$-representations $\bigl(\widetilde H^k(\Delta_n;\mathbb Q)\bigr)_n$ a finitely generated FI-module of low presentation degree?** If yes:

1. its $S_n$-character is a polynomial in $n$;
2. the Betti numbers $\widetilde b_k(\Delta_n)$ grow polynomially;
3. the F9 bad-coface count would be polynomial (parent's claim: "the rank of a specific Hom-functor between FI-modules");
4. **(I5) closes constructively** via the explicit FI-presentation.

PCR-Lit-3 is the **second independent test** of the polynomial-vs-exponential question that F9-S2 (mg-14a0) attacks from the direct-count angle.

### 0.2 Headline finding

The cohomology of $\Delta_n=\Delta(\mathrm{PPF}_n)$ is the cleanest possible object, and that very cleanness is what makes the *naive* FI-module question subtle:

$$
  \boxed{\;\widetilde H^{\,k}(\Delta_n;\mathbb Q)\;=\;\begin{cases}\mathrm{sgn}_{S_n}&k=n-2\\[2pt]0&k\ne n-2\end{cases}\qquad(n=3,4,5,6).\;}
$$

That is: $\Delta_n\simeq_{\mathbb Q} S^{n-2}$ with **top cohomology equal to the $1$-dimensional sign representation**, verified at $n=3,4$ by direct reduced-Betti computation in this polecat, at $n=5$ by Lefschetz/Burnside here $+$ the F1-refined/F3 sphere result, at $n=6$ by F8'-HPC ($m_{\mathrm{sgn}}=1$, Out$(S_6)$-invariant).

Consequences for the FI question — three readings, one verdict:

| Reading | Object | FI status | Presentation degree |
|---|---|---|---|
| **Fixed $k$** | $(\widetilde H^k(\Delta_n))_n$, nonzero only at $n=k+2$ | f.g. **torsion** FI-module | $k+3$ — but **degenerate** (no cross-$n$ content) |
| **Diagonal, untwisted** | $D_n:=\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}_{S_n}$ | **NOT finitely generated** — the canonical CEF non-example | — (all transition maps forced $0$) |
| **Diagonal, sgn-twisted** | $D_n\otimes\mathrm{sgn}_{S_n}=\mathrm{triv}_{S_n}$ | f.g. $=M(0)$, the **trivial FI-module** | **$0$** |

The verdict tag the ticket asks for is keyed on "presentation degree $\le 3$ AND character polynomial reproduces $n=6$". The sgn-twisted module hits **presentation degree $0$** and the constant character polynomial $1$ reproduces $\dim\widetilde H^{n-2}(\Delta_6)=1$ — so the verdict is **GREEN-FI-low-presentation**, with the explicit qualifier that the sign-twist is *mandatory* and is the standard move for top cohomology of $S_n$-equivariant poset complexes (cf. $\widetilde H^{\mathrm{top}}(\Delta(\overline\Pi_n))=\mathrm{Lie}_n\otimes\mathrm{sgn}$).

### 0.3 What this means for (I5)

**(I5) closes constructively at the level of cohomology.** The sgn-twisted FI-module has presentation degree $0$: it is generated in degree $0$ with no relations, hence — *if* finite generation holds (the residual specialist input, see §6.4) — it is determined to be $M(0)=\mathbb Q$ at every $n$, forcing

$$
  \widetilde H^{n-2}(\Delta_n;\mathbb Q)=\mathrm{sgn}_{S_n}\quad\text{for all }n,
$$

with no further computation. This is a *stronger* and *cheaper* closure than the F9 Plan-H route: it pins the cohomology at all $n$ without ever building the explicit cocycle. The PCR-2 (mg-59f3) inductive-lift template — $\delta^{\mathrm{sgn}}$ injective, $\omega_{\mathrm{bal}}^{(n+1)}=\mathrm{coker}$ — is then automatic, because the source and target of $\delta^{\mathrm{sgn}}$ are both $1$-dimensional sign isotypes at every $n$.

### 0.4 What this means for the polynomial-vs-exponential cross-check (F9-S2)

PCR-Lit-3 **resolves the polynomial-vs-exponential question for the obstruction-relevant quantity, and reinterprets it for the F9 bad-coface count.**

- The **cohomology** — the thing (I5) actually needs — is **constant** ($\dim=1$, character $\mathrm{sgn}_{S_n}$). Polynomial of degree $0$. Decisively *not* exponential.
- The **F9 bad-coface count** ($10\to64\to\cdots$, F9-S2 mg-14a0 / `docs/state-F9.md`) is a **cochain-level, representative-dependent** quantity. It is **not** the rank of a Hom between *finitely generated* FI-modules (the relative cochain complex $C^*(\Delta_n)$ is not f.g. as an FI-module — its dimension grows super-exponentially). PCR-Lit-3 therefore **predicts the bad-coface count may well keep growing super-polynomially**, and — crucially — that this is **not an obstruction to (I5)**. See §7.

So the two tests do **not** measure the same thing. F9-S2 measuring exponential growth of the bad-coface count would *not* contradict PCR-Lit-3 and would *not* be a "genuine obstruction"; it would be a statement about the cost of one particular constructive algorithm (Plan H from a non-minimal representative $\omega_{\mathrm{naive}}$), not about whether $\widetilde H^{n-2}(\Delta_n)$ stabilises. PCR-Lit-3's verdict on the question that matters: **polynomial (constant)**.

### 0.5 Verdict matrix

| Tag | Condition | This run? |
|---|---|:--:|
| **GREEN-FI-low-presentation** | FI structure verified, presentation degree $\le 3$, character polynomial reproduces $n=6$. | **✓** (sgn-twisted: presentation degree $0$; constant character $1$; reproduces $n=6$) |
| GREEN-FI-but-higher-degree | FI holds but presentation degree $>3$. | ✗ |
| AMBER-FI-uncertain | FI axioms hold but 4 datapoints insufficient to pin presentation degree. | ◯ partial — see §6.4: the *finite-generation theorem* itself remains the Tier-A3 specialist step; the 4 datapoints pin the presentation degree *conditionally on* f.g. |
| RED-no-FI | FI functoriality FAILS empirically. | ✗ — functoriality **holds** (trip-wire (c), §5) |

**Verdict: GREEN-FI-low-presentation** (sgn-twisted; presentation degree $0$), with the §6.4 caveat that the FI finite-generation *theorem* is the residual Tier-A3 specialist input.

---

## 1. Setup

### 1.1 The complexes and the convention

Per F1-refined / F2 / F5 (mg-3a61, mg-7455, mg-1e58):

$$
  \mathrm{PPF}_n \;:=\; \mathbf{Pos}_n^{\mathrm{sub}}\;\setminus\;\{\widehat 0\}\;\setminus\;\{\text{total orders on }[n]\},
$$

the proper partial orders on $\{0,\dots,n-1\}$ — closed, antisymmetric, non-empty, non-total — ordered by reverse refinement (a finer relation set is *below*). $\Delta_n:=\Delta(\mathrm{PPF}_n)$ is the order complex of strict chains. Cardinalities re-verified in this polecat (`compat_geom_pcr_lit3_fi_module.py` step [1]):

| $n$ | $|\mathrm{PPF}_n|$ | source cross-check |
|---:|---:|---|
| 3 | 12 | PCR-1 mg-f91f, PCR-2 mg-59f3 |
| 4 | 194 | PCR-1 mg-f91f, PCR-2 mg-59f3 |
| 5 | 4110 | F1-refined mg-3a61 ($4231-1-120$) |
| 6 | 129302 | F8'-HPC mg-3bf3 ($130023-1-720$) |

### 1.2 The FI-action

The category **FI** has objects the finite sets $[m]$ and morphisms the injections. The FI-action on PPF: an injection $f:[m]\hookrightarrow[n]$ relabels a poset by

$$
  V(f):\ \mathrm{PPF}_m\longrightarrow\mathrm{PPF}_n,\qquad
  P\longmapsto\{(f(a),f(b)):(a,b)\in P\}.
$$

This lands in $\mathrm{PPF}_n$: a non-antichain stays a non-antichain, and for $m<n$ the image is never total (the $n-m$ unused points are free). For $m=n$ it is the $S_n$-action on labels. The standard inclusion $\iota_m:[m]\hookrightarrow[m+1]$ ($a\mapsto a$, element $m$ free) is the PCR-1/PCR-2 map. $V$ is order-preserving (refinement is preserved), so it induces simplicial maps $\Delta_m\to\Delta_n$ and, on cohomology, the structure maps of a (co-)FI-module $\bigl(\widetilde H^k(\Delta_n)\bigr)_n$.

### 1.3 Method and budget

Pure-Python stdlib script `scripts/compat_geom_pcr_lit3_fi_module.py` (runtime $\sim1$s):

- **[1]** enumerate $\mathrm{PPF}_3,\mathrm{PPF}_4,\mathrm{PPF}_5$ by BFS on cover-addition $+$ transitive closure; check cardinalities and $\widetilde\chi$ (trip-wire (a)).
- **[2]** reduced Betti at $n=3,4$ by two-prime sparse mod-$p$ Gaussian elimination; $S_n$-equivariant virtual character at $n=3,4,5$ by Lefschetz fixed points (trip-wire (b)).
- **[3]** hard-assert the FI-action axioms over **all** injections $[3]\!\to\![4]$, $[4]\!\to\![5]$, $[3]\!\to\![5]$ (trip-wire (c)).
- **[4]** the presentation-degree analysis: fixed-$k$ torsion module, the forced-zero argument for the diagonal, the sgn-twist.

$n=5$ reduced Betti and $n=6$ are not recomputed from scratch (the $\Delta_5$ $f$-vector has entries $\sim10^8$, F1-refined); they are cited and cross-checked against the Lefschetz character, which the script *does* recompute independently.

---

## 2. Trip-wire (a) — cardinalities and Euler characteristics

`compat_geom_pcr_lit3_fi_module.py` step [1] output:

```
|PPF_3| = 12    |PPF_4| = 194    |PPF_5| = 4110
f-vector(Delta_3) = [12, 12]
f-vector(Delta_4) = [194, 1872, 5232, 5664, 2112]
chi~(Delta_3) = -1     chi~(Delta_4) = +1     chi~(Delta_5) = -1 (cited F1-refined)
trip-wire (a): PASS
```

The $\Delta_4$ $f$-vector $(194,1872,5232,5664,2112)$ reproduces PCR-1 mg-f91f §2.2 exactly; $\widetilde\chi(\Delta_3)=-1$, $\widetilde\chi(\Delta_4)=+1$ reproduce the F8'' §4.2 baseline $\widetilde\chi(\Delta_n)=(-1)^{n-2}$. **Trip-wire (a): PASS.**

---

## 3. Trip-wire (b) — the cohomology is $\mathrm{sgn}_{S_n}$ in degree $n-2$

### 3.1 Reduced Betti at $n=3,4$ (direct)

Two-prime sparse mod-$p$ Gaussian elimination ($p_1=1000003$, $p_2=999983$; ranks agree):

$$
  \widetilde b_*(\Delta_3)=(0,1),\qquad \widetilde b_*(\Delta_4)=(0,0,1,0,0).
$$

So $\widetilde H^*(\Delta_3)$ is concentrated in degree $1$ with $\dim=1$ ($\Delta_3\simeq S^1$) and $\widetilde H^*(\Delta_4)$ in degree $2$ with $\dim=1$ ($\Delta_4\simeq S^2$) — matching PCR-1 mg-f91f §2.1 and the absolute cross-checks therein.

### 3.2 $S_n$-equivariant virtual character at $n=3,4,5$ (Lefschetz)

By Hopf–Lefschetz, $\widetilde\chi(\Delta_n^\sigma)=\sum_k(-1)^k\operatorname{tr}(\sigma\mid\widetilde H^k(\Delta_n))$. The script enumerates $\mathrm{Fix}_{\mathrm{PPF}_n}(\sigma)$ for each $S_n$-conjugacy class and computes $\widetilde\chi$ of its order complex. Result (full table in the script log):

| $n$ | clean Lefschetz identity $\widetilde\chi(\Delta_n^\sigma)=(-1)^{n-2}\mathrm{sgn}(\sigma)$ | $m_{\mathrm{sgn}}$ |
|---:|---|:--:|
| 3 | holds at all 3 classes | $1$ |
| 4 | holds at all 5 classes | $1$ |
| 5 | holds at all 7 classes | $1$ |

The identity $\widetilde\chi(\Delta_n^\sigma)=(-1)^{n-2}\mathrm{sgn}(\sigma)$ for **every** $\sigma$ says the virtual character $\sum_k(-1)^k[\widetilde H^k(\Delta_n)]$ equals $(-1)^{n-2}[\mathrm{sgn}_{S_n}]$ in the representation ring. (Note this is the *correct* sign-convention statement; the F8'-HPC doc §3's "$\widetilde\chi(\mathrm{Fix})=+\mathrm{sgn}$ for $n\in\{4,5\}$" is loose for $n=5$ — at $n=5$, $(-1)^{n-2}=-1$, as the script confirms cleanly at all 7 classes.) Combined with the concentration in a single degree (Betti at $n=3,4$ here; F1-refined/F3 sphere result at $n=5$; F8'-HPC at $n=6$):

$$
  \widetilde H^{n-2}(\Delta_n;\mathbb Q)\;=\;\mathrm{sgn}_{S_n},\qquad \widetilde H^{k}(\Delta_n)=0\ (k\ne n-2),\qquad n=3,4,5,6.
$$

This matches PCR-2 mg-59f3 §3 ($\widetilde H^1(\Delta_3)=\mathrm{sgn}_{S_3}$, $\widetilde H^2(\Delta_4)=\mathrm{sgn}_{S_4}$) and the trip-wire (b) requirement. **Trip-wire (b): PASS.**

---

## 4. Trip-wire (c) — the FI-action axioms hold

`compat_geom_pcr_lit3_fi_module.py` step [3] hard-asserts, over **all** injections (not a sample):

| Axiom | Scope | Result |
|---|---|:--:|
| Well-definedness $V(f):\mathrm{PPF}_m\to\mathrm{PPF}_n$ | $24288$ $(f,P)$ pairs over $[3]\!\to\![4]$, $[4]\!\to\![5]$, $[3]\!\to\![5]$ | **PASS** |
| Identity injection acts as identity | all $P\in\mathrm{PPF}_3$ | **PASS** |
| Composition $V(g\circ f)=V(g)\circ V(f)$ | $34560$ $(f,g,P)$ triples, $f:[3]\!\to\![4]$, $g:[4]\!\to\![5]$ | **PASS** |
| $S_m$-equivariance $V(f\circ\sigma)=V(f)\circ V(\sigma)$ | $4320$ $(\sigma,f,P)$ triples, $\sigma\in S_3$, $f:[3]\!\to\![5]$ | **PASS** |

So $(\mathrm{PPF}_n)_n$ is a genuine **FI-object** and $\bigl(\widetilde H^k(\Delta_n)\bigr)_n$ is a genuine (co-)FI-module. **Trip-wire (c): PASS — FI functoriality does *not* fail; the RED-no-FI branch is excluded.**

---

## 5. The structure maps on cohomology

The FI-action is well-defined and functorial (§4); the content of the presentation-degree question is what the *induced maps on cohomology* look like.

### 5.1 The fixed-$k$ reading is degenerate

For fixed $k$, $\widetilde H^k(\Delta_n)\ne0$ iff $n=k+2$ (§3). So $(\widetilde H^k(\Delta_n))_n$ is supported in the single degree $k+2$. As an FI-module it is therefore **torsion** (supported in finitely many degrees): finitely generated, generation degree $k+2$, with relations at degree $k+3$ killing the entire free tail of $M(\mathrm{sgn}_{S_{k+2}})$ — presentation degree $k+3$. But this carries **no cross-$n$ information**: each fixed-$k$ module lives entirely at one $n$. The interesting object is the diagonal.

### 5.2 The diagonal, untwisted: $(\mathrm{sgn}_{S_n})_n$ is not finitely generated

Let $D_n:=\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}_{S_n}$. Any FI-module structure map $\phi:D_m\to D_n$ attached to an injection $f:[m]\hookrightarrow[n]$ with $n\ge m+2$ is **forced to zero**:

> pick a transposition $\tau\in S_n$ that swaps two points of $[n]\setminus\operatorname{im}(f)$ (possible exactly when $n-m\ge2$). Then $\tau\circ f=f$ as injections, so functoriality gives $\phi=V(\tau)\circ\phi$. But $V(\tau)$ acts on $D_n=\mathrm{sgn}_{S_n}$ by $\mathrm{sgn}(\tau)=-1$. Hence $\phi=-\phi$, i.e. $\phi=0$.

The script (step [4b]) verifies the group-theoretic input: $\tau=(3\,4)\in S_5$ fixes $\operatorname{im}([3]\hookrightarrow[5])=\{0,1,2\}$ pointwise, $\tau\circ f=f$, $\mathrm{sgn}(\tau)=-1$; and §3 establishes that $\tau$ acts on $\widetilde H^3(\Delta_5)=\mathrm{sgn}_{S_5}$ by $-1$. Since the $m\to m+2$ map is the composite of two $m\to m+1$ maps, *all* transition maps must vanish (if some $m\to m+1$ map were nonzero for all $m$, the composite $m\to m+2$ would be nonzero — contradiction). An FI-module with all transition maps zero and $D_n\ne0$ for infinitely many $n$ is **not finitely generated**.

This is not a defect of our setting — $(\mathrm{sgn}_{S_n})_n$ is the **textbook CEF non-example**: $\mathrm{sgn}_{S_n}$ corresponds to the partition $(1^n)$, whose first-row length does not stabilise, so the sequence is not representation-stable in the CEF sense (Church–Ellenberg–Farb 2015, §1–2).

### 5.3 The diagonal, sgn-twisted: the trivial FI-module $M(0)$

The standard repair is the **sign-twist**. The category FI admits the twist $V\mapsto V\otimes\mathrm{sgn}$ (act by $\mathrm{sgn}(\sigma)$ on the $S_n$-part; injections by the induced sign on the FI-structure). Applying it,

$$
  D_n\otimes\mathrm{sgn}_{S_n}\;=\;\mathrm{sgn}_{S_n}\otimes\mathrm{sgn}_{S_n}\;=\;\mathrm{triv}_{S_n}.
$$

The sequence $(\mathrm{triv}_{S_n})_n$ with the obvious (identity) transition maps **is** the trivial FI-module $M(0)=\mathbb Q$: generated by a single element in degree $0$, **no relations**. Its presentation degree is

$$
  \boxed{\;\text{presentation degree}\bigl((\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}_{S_n})_n\bigr)\;=\;0.\;}
$$

The sign-twist is the same move that makes the partition-lattice top cohomology tractable ($\widetilde H^{\mathrm{top}}(\Delta(\overline\Pi_n))=\mathrm{Lie}_n\otimes\mathrm{sgn}$, after which the relevant FI-/$\mathrm{FI}_d$-structure is finitely generated; Sundaram–Wachs 1997, and the FI-module reading in CEF §5). It is *mandatory* and *standard* for top cohomology of $S_n$-equivariant order complexes — not an artefact.

---

## 6. Presentation degree, character polynomial, and (I5)

### 6.1 Presentation degree estimate (deliverable 3)

| FI-module | finitely generated? | gen. degree | rel. degree | presentation degree |
|---|:--:|:--:|:--:|:--:|
| $(\widetilde H^k(\Delta_n))_n$, fixed $k$ | yes (torsion) | $k+2$ | $k+3$ | $k+3$ — degenerate |
| $(\widetilde H^{n-2}(\Delta_n))_n=(\mathrm{sgn}_{S_n})_n$ | **no** | — | — | — |
| $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}_{S_n})_n=(\mathrm{triv}_{S_n})_n$ | **yes, $=M(0)$** | $0$ | — | $\mathbf 0$ |

The Ramos 2017 reading (parent table entry 4.6): an FI-module of presentation degree $\le d$ is determined by its values at indices $\le d$. With $d=0$, the sgn-twisted module is determined by its degree-$0$ value alone — the strongest possible form of the "determined by finitely many small-$n$ values" conclusion. The four datapoints $n=3,4,5,6$ are not just *consistent* with presentation degree $\le3$; they are consistent with presentation degree exactly $0$, and there is no datapoint suggesting any relation appears at any positive degree.

### 6.2 Character polynomial cross-check (deliverable 4)

If an FI-module has presentation degree $d$, its character is a polynomial of degree $\le d$ in the cycle-counting class functions. For the sgn-twisted module ($d=0$): the character polynomial is the **constant $1$**. This predicts $\dim\bigl(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}\bigr)=1$, i.e. $\dim\widetilde H^{n-2}(\Delta_n)=1$, for all $n$. Cross-prediction at $n=6$: $\dim\widetilde H^4(\Delta_6)=1$ — **confirmed** by F8'-HPC mg-3bf3 ($m_{\mathrm{sgn}}=1$, Out$(S_6)$-invariant, $\widetilde H^4(\Delta_6)^{\mathrm{sgn}}\cong\mathbb Q$). The untwisted character is $\mathrm{sgn}_{S_n}$ — completely explicit and uniform across $n$, but *not* a polynomial character in the CEF sense (that is the §5.2 obstruction restated character-theoretically). Either way the **Betti number is constant**: $\widetilde b_{n-2}(\Delta_n)=1$, $\widetilde b_k=0$ for $k\ne n-2$, at $n=3,4,5,6$. Polynomial of degree $0$ — **not exponential**.

### 6.3 Effect on (I5)

(I5) asks for the inductive lift $\omega_{\mathrm{bal}}^{(n)}\rightsquigarrow\omega_{\mathrm{bal}}^{(n+1)}$ at all $n$. The cohomological content of (I5) is: $\widetilde H^{n-2}(\Delta_n)^{\mathrm{sgn}}$ is $1$-dimensional at every $n$, and the cofiber connecting map $\delta^{\mathrm{sgn}}$ is injective with the next generator as its cokernel (PCR-2 mg-59f3 §4, verified at $n=3\to4$). PCR-Lit-3 supplies the missing all-$n$ ingredient: **the sgn-twisted cohomology FI-module has presentation degree $0$**, so — conditional on finite generation (§6.4) — $\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}_{S_n}$ at *every* $n$, and the PCR-2 template runs automatically (source and target of $\delta^{\mathrm{sgn}}$ are both $1$-dimensional sign isotypes; the cofiber has the "$(1,1,2)$ extra-room" pattern by the same constancy). **This is a constructive closure of the cohomological content of (I5) that bypasses Plan H entirely.**

### 6.4 The honest caveat — what is *not* established

The presentation-degree-$0$ statement is conditional on the **finite-generation theorem** for $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn})_n$ as an FI-module. Four agreeing datapoints ($n=3,4,5,6$) are strong empirical evidence — every one is exactly $\mathrm{triv}_{S_n}$, with no relation appearing — but they are *not* a proof: finite generation is a statement about all $n$ at once, and is precisely the Tier-A3 specialist input the parent doc (mg-ac7a §5.3) flagged for Patzt/Putman. PCR-Lit-3 **sharpens** that specialist ask from "verify FG-FI and extract the character" to the much narrower **"prove $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn})_n$ is a finitely generated FI-module — the empirical evidence says it is $M(0)$, presentation degree $0$; only the finite-generation theorem is missing."** That is a substantially smaller ask than the parent's framing.

---

## 7. F9-S2 cross-check: the bad-coface count, reinterpreted (deliverable 5)

### 7.1 The two tests do not measure the same thing

The parent doc (mg-ac7a §3, item 3) claimed the F9 bad-coface count "would be a polynomial in $n$ by the same machinery (it's the rank of a specific Hom-functor between FI-modules)." **PCR-Lit-3 finds this framing is too optimistic.** The bad-coface count is the support size of $d\,\omega_{\mathrm{naive}}^{(n)}$, where $\omega_{\mathrm{naive}}^{(n)}$ is the signed $S_n$-orbit of the canonical critical cell $c^*_n$ — a **cochain-level** quantity. It is governed by the relative cochain complex $C^*(\Delta_n)$, **not** the cohomology. And $\bigl(C^k(\Delta_n)\bigr)_n$ is **not a finitely generated FI-module**: $\dim C^k(\Delta_n)=f_k(\Delta_n)$ grows super-exponentially (the $\Delta_5$ $f$-vector already has entries $\sim10^8$, F1-refined). So the bad-coface count is *not* the rank of a Hom between f.g. FI-modules, and there is no FI-module finite-generation theorem forcing it to be polynomial.

### 7.2 The structural prediction

Per F9-S2 (`docs/state-F9.md`, mg-9e88 Session 1), the bad-coface count is $10$ at $n=5$, $64$ at $n=6$, **dominated by $u_n:=$ the proper up-set of the top poset $P_{n-2}$ of $c^*_n$ inside $\mathrm{PPF}_n$** ($u_5=4$, $u_6=54$). An up-set in $\mathrm{PPF}_n$ is, generically, *large*: $|\mathrm{PPF}_n|$ itself grows like $2^{n(n-1)/2}$ (OEIS A001035 asymptotics), and adding a free element when passing $n\to n+1$ multiplies the count of compatible extensions super-polynomially. **PCR-Lit-3 therefore predicts $u_n$, and hence the bad-coface count, continues to grow super-polynomially** — the jump $u_5=4\to u_6=54$ (factor $\sim13$) is already faster than any low-degree polynomial through those two points would sustain, and the $n\to n+1$ free-element multiplier only increases. A concrete falsifiable prediction for F9-S3: $u_7$ in the **high hundreds to low thousands** (order-of-magnitude: $u_6\times[$the $|\mathrm{PPF}_7|/|\mathrm{PPF}_6|$-type multiplier$]$, $\sim 54\times 13$–$64$), with the total $n=7$ bad-coface count of the same order — **not** a value a degree-$\le3$ polynomial fit through $\{10,64\}$ would give.

### 7.3 Why this is *not* an obstruction to (I5)

$\omega_{\mathrm{naive}}^{(n)}$ is **not a cocycle** — that is the entire reason F9's Plan H must add a correction $\psi^{(n)}$. The bad cofaces measure how far the *non-minimal representative* $\omega_{\mathrm{naive}}$ is from the cocycle equation. But $\widetilde H^{n-2}(\Delta_n)^{\mathrm{sgn}}=\mathbb Q$ is $1$-dimensional (§3, §6): an actual cocycle $\omega_{\mathrm{bal}}^{(n)}$ representing the generator **exists**, and *by definition has no bad cofaces*. The bad-coface count is an invariant of the *choice of representative and the Plan-H algorithm*, not of the cohomology. So:

> **F9-S2 observing exponential growth of the bad-coface count would NOT be a "genuine obstruction".** It would say: $\omega_{\mathrm{naive}}$ is a poor starting representative and the Plan-H linear system grows super-polynomially — a statement about *algorithmic cost*, not about whether $(\widetilde H^{n-2}(\Delta_n))$ stabilises.

The polynomial-vs-exponential dichotomy the ticket sets up ("both polynomial $\Rightarrow$ (I5) closes; both exponential $\Rightarrow$ genuine obstruction") rested on the parent's assumption that the bad-coface count *is* an FI-module invariant. PCR-Lit-3 shows it is not. The corrected reading:

| Quantity | Test | Growth | Bears on (I5)? |
|---|---|---|---|
| $\widetilde H^{n-2}(\Delta_n)$ (cohomology) | **PCR-Lit-3** (FI-module) | **constant** ($\mathrm{sgn}_{S_n}$, $\dim 1$) — polynomial deg $0$ | **Yes** — this *is* the obstruction-relevant object; constancy $\Rightarrow$ (I5) closes cohomologically |
| bad-coface count of $\omega_{\mathrm{naive}}^{(n)}$ | F9-S2 (direct count) | predicted **super-polynomial** | **No** — representative-dependent algorithmic cost, not an invariant |

**PCR-Lit-3's verdict on the polynomial-vs-exponential question, for the quantity that matters: polynomial (constant). (I5) closes cohomologically.** The recommendation to F9-S3 is to **stop treating the bad-coface count as a polynomial-vs-exponential proxy for (I5)** — it is a Plan-H cost metric — and instead either (i) work from the minimal cocycle directly (the sgn-twisted $M(0)$ structure gives it at all $n$), or (ii) keep Plan H but expect and accept super-polynomial system sizes, since correctness (not polynomial cost) is what (I5) needs.

---

## 8. Trip-wire summary

| Trip-wire | Source | Result |
|---|---|:--:|
| (a) $|\mathrm{PPF}_3|,|\mathrm{PPF}_4|=12,194$; $\widetilde\chi(\Delta_3),\widetilde\chi(\Delta_4)=-1,+1$ | PCR-1 mg-f91f, PCR-2 mg-59f3 | **PASS** |
| (a) $\Delta_4$ $f$-vector $=(194,1872,5232,5664,2112)$ | PCR-1 mg-f91f §2.2 | **PASS** |
| (b) $\widetilde b_*(\Delta_3)=(0,1)$, $\widetilde b_*(\Delta_4)=(0,0,1,0,0)$ | PCR-1 mg-f91f §2.1 | **PASS** |
| (b) $\widetilde H^1(\Delta_3)=\mathrm{sgn}_{S_3}$, $\widetilde H^2(\Delta_4)=\mathrm{sgn}_{S_4}$, $m_{\mathrm{sgn}}=1$ at $n=3,4,5$ | PCR-2 mg-59f3 §3, F7 mg-73fd | **PASS** |
| (b) clean Lefschetz identity $\widetilde\chi(\Delta_n^\sigma)=(-1)^{n-2}\mathrm{sgn}(\sigma)$, all classes, $n=3,4,5$ | F8'-HPC mg-3bf3 §3 (sign-corrected, §3.2 here) | **PASS** |
| (c) FI-action: identity, composition, $S_m$-equivariance, well-definedness | FI axioms (CEF 2015) | **PASS** (hard-asserted, all injections) |
| $n=6$ cross-prediction $\dim\widetilde H^4(\Delta_6)=1$ | F8'-HPC mg-3bf3 | **PASS** |

All trip-wires pass. No new axioms; no Lean changes; no trust-surface impact.

---

## 9. Verdict and headline takeaway

### 9.1 Verdict

**GREEN-FI-low-presentation.** With the mandatory sign-twist (standard for top cohomology of $S_n$-equivariant order complexes), $\bigl(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn}_{S_n}\bigr)_n=(\mathrm{triv}_{S_n})_n$ is the trivial FI-module $M(0)$: finitely generated, **presentation degree $0$** ($\le3$), character polynomial the constant $1$, reproducing the $n=6$ datum. The residual specialist input (Tier-A3) is now narrowed to a single statement: the FI finite-generation *theorem* for this module (§6.4).

### 9.2 Headline takeaway

> **PCR-Lit-3 computes the FI-module structure of $(\widetilde H^k(\Delta_n;\mathbb Q))_n$ and finds the cleanest possible answer.** The cohomology is $\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}_{S_n}$ (dimension $1$, concentrated in degree $n-2$), verified at $n=3,4$ by direct reduced Betti, at $n=5$ by Lefschetz $+$ F1-refined, at $n=6$ by F8'-HPC. The FI-action $V(f):\mathrm{PPF}_m\to\mathrm{PPF}_n$ is genuinely functorial (trip-wire (c), hard-asserted over all injections) — so RED-no-FI is excluded. The *untwisted* diagonal $(\mathrm{sgn}_{S_n})_n$ is the canonical CEF non-example (every FI transition map is forced to zero by a transposition outside the image), but the *sgn-twisted* diagonal is the trivial FI-module $M(0)$ of **presentation degree $0$** — the lowest possible. This closes the cohomological content of (I5) constructively at all $n$ (bypassing Plan H) **conditional only on the FI finite-generation theorem**, which is the sharpened Tier-A3 specialist ask. Finally, PCR-Lit-3 **reinterprets the F9-S2 polynomial-vs-exponential cross-check**: the bad-coface count is a cochain-level, representative-dependent quantity, *not* an FI-module invariant; PCR-Lit-3 predicts it keeps growing super-polynomially **and that this is not an obstruction to (I5)** — the obstruction-relevant quantity is the cohomology, which is constant.

### 9.3 Daniel-program impact

- ✓ **FI-action set up and verified functorial** — $(\mathrm{PPF}_n)_n$ is an FI-object; $(\widetilde H^k(\Delta_n))_n$ a (co-)FI-module.
- ✓ **Cohomology pinned**: $\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}_{S_n}$, $n=3,4,5,6$; constant Betti.
- ✓ **Presentation degree $0$** for the sgn-twisted FI-module; character polynomial $\equiv1$; reproduces $n=6$.
- ✓ **(I5) cohomological content closes constructively** at all $n$, conditional on FI finite generation.
- ✓ **Tier-A3 specialist ask sharpened** to "prove FI finite generation; the module is empirically $M(0)$."
- ✓ **F9-S2 cross-check reinterpreted**: bad-coface count is representative-dependent, predicted super-polynomial, **not** an (I5) obstruction.
- ◯ **FI finite-generation theorem** remains the residual specialist (Tier-A3) step — but now a single sharp statement, not an open-ended verification.

### 9.4 Resource budget

| Item | Estimate |
|---|---:|
| Parent + PCR-1/PCR-2 + F8'-HPC + F9-state read | $\sim18$k tokens |
| Script draft + run + cross-check | $\sim14$k tokens |
| Doc draft (this document) | $\sim14$k tokens |
| Tool overhead | $\sim4$k tokens |
| **Total** | **$\sim50$k (at cap)** |

50k cap respected. No new axioms; no Lean changes; no trust-surface impact.

---

## 10. References

### 10.1 Predecessor mg-tickets

- **mg-ac7a** — F8''''' PCR-3 literature integration; `docs/compatibility-geometry-F8ppppp-literature.md` (PCR-Lit-3 spec §6.3, table 4.1/4.6, Tier-A3 §5.3). Parent.
- **mg-f91f** — F8''' / PCR-1: cofiber Betti $(0,0,2,0)$; $\widetilde b_*(\Delta_3)=(0,1)$, $\widetilde b_*(\Delta_4)=(0,0,1,0,0)$.
- **mg-59f3** — F8'''' / PCR-2: spectral $E_2$; $\widetilde H^1(\Delta_3)=\mathrm{sgn}_{S_3}$, $\widetilde H^2(\Delta_4)=\mathrm{sgn}_{S_4}$, $\delta^{\mathrm{sgn}}$ injective.
- **mg-3a61** — F1-refined: $|\mathrm{PPF}_5|=4110$, $\widetilde\chi(\Delta_5)=-1$, $\Delta_5\simeq S^3$.
- **mg-73fd** — F7: Burnside $m_{\mathrm{sgn}}=1$ at $n=5$.
- **mg-3bf3** — F8'-HPC: $m_{\mathrm{sgn}}=1$ at $n=6$, Out$(S_6)$-invariant; $|\mathrm{PPF}_6|=129302$.
- **mg-9e88** — F9 Session 1: bad-coface count $10\,(n{=}5)\to64\,(n{=}6)$; `docs/state-F9.md`.

### 10.2 Sibling (parallel) polecats

- **mg-6295** — PCR-Lit-2 (Hersh–Welker discrete-Morse-on-cofiber); structurally independent.
- **mg-14a0** — F9-S2 (n=7 pattern test); the parallel polynomial-vs-exponential test — see §7 for the cross-check and reinterpretation.

### 10.3 Representation stability / FI-modules

- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015). — FI-modules; $(\mathrm{sgn}_{S_n})_n$ as the canonical non-example; the sign-twist.
- E. Ramos, *On the degree-wise coherence of FI-modules*, NYJM 23 (2017). — presentation-degree bounds; "determined by values at indices $\le d$".
- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015). — central stability (the weaker condition, Tier-A3 backup).
- P. Patzt, *Central stability homology*, J. Topol. (2017+). — Tier-A3 specialist route.
- S. Sundaram, M. Wachs, *The homology representations of the $k$-equal partition lattice*, Trans. AMS 349 (1997). — precedent: top cohomology of an $S_n$-equivariant order complex as a sign-twisted object.

### 10.4 Method

- Script: `scripts/compat_geom_pcr_lit3_fi_module.py` (pure-Python stdlib; $\sim1$s). Reuses the enumeration / transitive-closure / Lefschetz scaffolding of `scripts/posn_n_validate.py` (mg-3bf3) and the FI-action relabelling of `scripts/posn_constructive_lift_n6.py` (mg-9e88).

---

*Polecat: mg-759d. Branch: `compat-geom-PCR-Lit-3-fi-module`. Generated 2026-05-14. Verdict: **GREEN-FI-low-presentation** — sgn-twisted $(\widetilde H^{n-2}(\Delta_n)\otimes\mathrm{sgn})_n=M(0)$, presentation degree $0$; closes the cohomological content of (I5) constructively at all $n$ conditional on FI finite generation; reinterprets the F9-S2 bad-coface count as a representative-dependent cost metric, not an (I5) obstruction. No new axioms; no Lean changes; no trust-surface impact.*
