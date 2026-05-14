# Compat-Geom — Structural-analogy scoping: the 1/3-2/3 column (mg-26fc)

**Branch:** `compat-geom-mg26fc-bruhat-expansion-lens`.
**Source:** Daniel structural-analogy avalanche (28-piece Apple-split reminder, forwarded + consolidated by mayor 2026-05-14T12:55Z). Meta-thesis: both the 1/3-2/3 (Kahn–Saks) conjecture and the Union-Closed (Frankl) conjecture are statements that *"a constrained compatibility geometry cannot remain globally isotropic."*
**Type:** Paper-and-pencil scoping / research-capture. No new axioms; no Lean changes; no computation. LaTeX-style Markdown, matching the F-series house style. 150k cap.
**Scope:** ONLY the 1/3-2/3 column of Daniel's `1/3-2/3 ⟷ Union-Closed` dictionary. The Union-Closed column and the proposed cross-product repo are explicitly **out of scope** (Daniel's structural call, parked). This doc does **not** touch, edit, or redirect the route-(ii) chain (F15 / mg-8355 and successors).

---

**Verdict: GREEN-distinct-complementary.**

The 1/3-2/3 column of Daniel's avalanche — *linear extensions / adjacent swaps / BK graph / Bruhat geometry / balanced obstruction / "curvature-bottleneck-expansion-defect"* — is rigorized in §1. It is **not a speculative new lens**: it is, essentially verbatim, the proof spine of the in-tree width-3 paper (`main.tex` §"Approach: Cheeger-type expansion on the BK graph"; `step8.tex` Theorem E). The F-series cohomological program (F10–F15) is recapped in §2. The two-framings dictionary is built in §3, and the same-vs-distinct question is decided in §4.

The honest answer to the ticket's key question is **distinct-but-resonant**, and a scoping pass *can* deliver this verdict cleanly (it is not AMBER):

- The two framings are **not the same mathematical object**. The expansion lens lives on the BK graph $G_{\mathrm{BK}}(P)$ — a *graph* (a $1$-complex) on the linear extensions of a *fixed* poset $P$. The F-series lens lives on $\Delta(\mathrm{PPF}_n)$ — an $(n{-}2)$-dimensional complex on the *space of all posets* on $n$ points. Different dimension, different vertex set, different symmetry group in the load-bearing role.
- The two framings extract the balanced pair by **different mechanisms** and have **different open gaps**: the expansion lens via a Cheeger lower bound on a pair-cut, gap = Hypothesis A (arithmetic richness, `step8.tex`); the F-series via a non-vanishing sign-isotypic cohomological pairing, gap = (FG-Cofiber) / (UCC) (FI finite generation, F10 §7.2). Neither proof route uses the other's machinery.
- They are nonetheless **resonant**, not unrelated. They share a common *substrate* — the pair-orientation linear-extension counts $|\mathcal L_{x<y}(P)|$ — and they are linked by a genuine *meta-principle*: expansion and (co)homology vanishing are quantitatively tied (Cheeger; Garland's method; coboundary/topological expansion). Daniel's independent description of the expansion defect as a *"cohomological/curvature phenomenon"* is **correct as resonance** — expansion *does* have a cohomological shadow — but the cohomology the expansion lens naturally produces is that of the *BK graph / a complex on $\mathcal L(P)$*, **not** $\widetilde H^{\,*}(\Delta(\mathrm{PPF}_n))$. They are cohomological cousins, not the same cohomology.

For the meta-thesis this is the **stronger** outcome, not a weaker one: the non-isotropy principle is *robust* — it surfaces independently in two different geometric organizations of the same combinatorial data, with two independent proof attacks. The meta-thesis becomes "two non-isotropy mechanisms for 1/3-2/3," and the cross-product comparison with Union-Closed gains two reference points instead of one.

§4.4 records precisely what a *literal* unification would require (and why it is not in hand, and is unlikely to be a literal identity). §5 is the verdict; §6 lists follow-ups; none is on the route-(ii) critical path.

---

## §0. What this document is and is not

The mayor's consolidation of Daniel's avalanche frames a `1/3-2/3 ⟷ Union-Closed` dictionary whose 1/3-2/3 column reads (Daniel's words, lightly normalized):

| Slot | Daniel's 1/3-2/3 entry |
|---|---|
| State space | linear extensions $\mathcal L(P)$ of a poset $P$ |
| Ambient geometry | permutahedral / Bruhat geometry |
| Local moves | adjacent swaps preserving order |
| Balanced obstruction | $\lvert\mathcal L_{x<y}\rvert \approx \lvert\mathcal L_{y<x}\rvert$ for every incomparable pair |
| Conjectural mechanism | local swap symmetries cannot globally coexist because order constraints induce **curvature / bottlenecks / expansion defects** |

This document does two things and only two things:

1. **Rigorize that column** (§1) — state each row precisely in standard terms, and pin down what "curvature / bottleneck / expansion defect" means concretely.
2. **Decide whether that lens is the same obstruction as the F-series cohomological program, or a distinct attack** (§2–§5) — by recapping the F-series 1/3-2/3 framing, building the dictionary between the two, and emitting a verdict.

It is **paper-and-pencil**: no new axioms, no Lean changes, no computation, no new empirical datapoint. It introduces no objects into the trust surface. It is research-capture, sequenced behind the route-(ii) critical path (F15 / mg-8355), and **must not** be read as redirecting it: §6 explicitly keeps every recommendation off that chain.

Notation throughout. $P=(X,\le_P)$ a finite poset, $|X|=n$, width $w(P)\le 3$ where stated. $\mathcal L(P)$ = its linear extensions. For incomparable $x\parallel y$, $\mathcal L_{x<y}(P) := \{L\in\mathcal L(P): x<_L y\}$ and $p_{xy} := \Pr_L[x<_L y] = |\mathcal L_{x<y}(P)|/|\mathcal L(P)|$ under uniform $L$. The F-series notation ($\mathrm{PPF}_n$, $\Delta_n$, $\iota_n$, $\omega_{\mathrm{bal}}$, (UCC), (FG-Cofiber)) is as in F10 (`docs/general-n-proof-synthesis.md`) and F11 (`docs/state-F11.md`); it is restated where used.

---

## §1. The 1/3-2/3 column, rigorized

### 1.1 State space — the linear extensions $\mathcal L(P)$

The state space is $\mathcal L(P)$, the set of linear extensions of $P$: total orders $L$ on $X$ with $a<_P b \Rightarrow a<_L b$. Fixing a reference labelling $X=\{1,\dots,n\}$ realizes each $L\in\mathcal L(P)$ as a permutation in $S_n$, so $\mathcal L(P)\subseteq S_n$. Uniform measure $\pi$ on $\mathcal L(P)$ is the law under which the conjecture is stated: the conjecture asks for an incomparable pair $(x,y)$ with $p_{xy}\in[1/3,2/3]$.

This is exactly the `step1.tex` setup ("Poset, linear extensions, BK graph"): $\mathcal L(P)$ is the vertex set everything else is built on.

### 1.2 The graph of local moves — the BK graph

**Naming reconciliation.** The avalanche and the mayor's consolidation call this the "BK graph" and gloss BK as "Bollobás–Kahn / Linial." The in-tree paper (`main.tex`, `step1.tex`, `step8.tex`) fixes the canonical name: **BK = Bubley–Karzanov**, after Bubley–Karzanov 1998, who introduced the adjacent-transposition Markov chain on $\mathcal L(P)$ and proved its spectral gap controls mixing. (Linial 1984 is the width-2 base case; the adjacent-transposition idea is older folklore, but the in-tree convention and the abbreviation "BK" are Bubley–Karzanov.) This document uses **Bubley–Karzanov** and the abbreviation $G_{\mathrm{BK}}(P)$, consistently with the repo.

**Definition (BK graph).** $G_{\mathrm{BK}}(P)$ has vertex set $\mathcal L(P)$; two extensions $L,L'$ are adjacent iff they differ by transposing a pair of *adjacent incomparable* elements (an "adjacent swap preserving order" — a BK move). Equivalently: $L'=\tau_i L$ where $\tau_i$ swaps the elements in positions $i,i{+}1$, and those two elements are incomparable in $P$ (so $L'$ is still a linear extension).

This is Daniel's "local moves: adjacent swaps preserving order," verbatim. The BK move is the atomic operation; the BK graph is the local-move geometry.

### 1.3 The ambient geometry — the permutahedron / weak Bruhat order

Daniel's "ambient geometry: permutahedral / Bruhat geometry" is made precise as follows. The Cayley graph of $S_n$ with respect to the adjacent transpositions $\{s_1,\dots,s_{n-1}\}$ is the $1$-skeleton of the **permutahedron** $\Pi_{n-1}$, equivalently the Hasse diagram of the **weak (Bruhat) order** on $S_n$. The BK graph $G_{\mathrm{BK}}(P)$ is precisely the **induced subgraph** of this $1$-skeleton on the vertex subset $\mathcal L(P)\subseteq S_n$:

- vertices: the linear extensions, a subset of the permutahedron's vertices;
- edges: those permutahedron edges (adjacent transpositions) whose swap stays inside $\mathcal L(P)$ — i.e. swaps an *incomparable* pair.

Two standard facts give this ambient its teeth:

- **Connectivity (Bubley–Karzanov 1998).** $G_{\mathrm{BK}}(P)$ is connected: any two linear extensions are joined by a sequence of BK moves. This is what makes the BK Markov chain irreducible.
- **Convexity flavour.** $\mathcal L(P)$ sits inside the weak order as a "Bruhat-flavoured" region: a permutation $L$ is a linear extension iff its inversion set contains no inversion *against* a $P$-relation, a downward-closed-type condition on inversions. (The precise lattice-theoretic status of $\mathcal L(P)$ in the weak order is not load-bearing for this scoping pass; the in-tree paper uses only connectivity plus the *local* grid structure of fibers, §1.5 below.)

So "permutahedral / Bruhat geometry" is not metaphor: $G_{\mathrm{BK}}(P)$ is literally a sub-object of the permutahedron skeleton, and the conjecture is a statement about how that sub-object sits inside the ambient.

### 1.4 The balanced obstruction — a cut in the BK graph

Daniel's "$|\mathcal L_{x<y}| \approx |\mathcal L_{y<x}|$ for every incomparable pair" is the balanced-pair obstruction. Made precise as a cut: for each incomparable pair $x\parallel y$ define
$$
  S_{xy} \;:=\; \{L\in\mathcal L(P): x<_L y\} \;=\; \mathcal L_{x<y}(P),
\qquad
  f_{xy} := \mathbf 1_{S_{xy}}.
$$
$S_{xy}$ is a cut of $G_{\mathrm{BK}}(P)$ with volume fraction $\pi(S_{xy})=p_{xy}$. Its edge boundary $\partial S_{xy}$ is exactly the set of BK moves that swap $x$ and $y$ themselves (the only moves that can change which of $x,y$ comes first). The conjecture, restated in this language:

> **(1/3-2/3, cut form).** Every non-chain width-$\le 3$ poset $P$ has an incomparable pair $x\parallel y$ whose cut $S_{xy}$ has *balanced volume* $p_{xy}\in[1/3,2/3]$.

A **$\gamma$-counterexample** (the `step8.tex` term) is a $P$ with $p_{xy}\notin[1/3,2/3]$ for every pair and $\inf_{x\parallel y}\min(p_{xy},1-p_{xy})\ge\gamma$ — i.e. *every* pair-cut is volume-imbalanced *and bounded away* from $0$ and $1$.

### 1.5 "Curvature / bottleneck / expansion defect," concretely

This is the row the ticket asks to pin down. Daniel's "local swap symmetries cannot globally coexist because order constraints induce curvature / bottlenecks / expansion defects" is, concretely, a **Cheeger-type expansion statement on $G_{\mathrm{BK}}(P)$**. Three equivalent concretizations, in increasing sharpness, all already present in the repo:

**(a) Conductance / Cheeger constant.** For a cut $S$, the conductance is $\Phi(S)=|\partial S|/\min(\mathrm{vol}\,S,\mathrm{vol}\,S^c)$. The BK Markov chain is the lazy random walk on $G_{\mathrm{BK}}(P)$; its Cheeger constant $\Phi(G_{\mathrm{BK}}(P))=\min_S\Phi(S)$ is the "expansion." "Expansion defect" = a low-conductance cut = a *bottleneck*: a sparse set of BK moves separating two large regions of $\mathcal L(P)$.

**(b) Spectral gap.** By Cheeger's inequality for reversible chains, the spectral gap $\lambda_2$ of the BK chain satisfies $\Phi^2/2 \le \lambda_2 \le 2\Phi$. So "expansion defect" $\Leftrightarrow$ "small spectral gap" — the Bubley–Karzanov slow-mixing regime. This is the most literal reading of Daniel's "curvature": in the discrete-geometry sense (Ollivier–Ricci, Bakry–Émery), a small spectral gap *is* a curvature deficit. The repo does **not** use Ollivier–Ricci curvature explicitly — its concretization is the Dirichlet-form / conductance route (c) — but the "curvature" word is faithful to the spectral-gap content; an Ollivier–Ricci formulation would be an *alternative* concretization of the same row, not the in-tree one.

**(c) The in-tree concretization — Theorem E (`step8.tex`, §"Theorem E").** The repo proves the exact quantitative form:
$$
  \text{$P$ a width-3 indecomposable $\gamma$-counterexample on $n$ elements}
  \;\Longrightarrow\;
  \exists\, S \text{ with } \mathrm{vol}(S)\ge\gamma\,\mathrm{vol}(\mathcal L(P)),\ \ \Phi(S)\le \tfrac{2}{\gamma n}.
$$
The proof is a Dirichlet-form comparison (`lem:dirichlet-conductance`: $\Phi(S)\le\mathcal E(\mathbf 1_S)/\mathrm{Var}(\mathbf 1_S)$) plus an averaging argument producing a "BK-frozen" pair. So: **a counterexample forces a low-conductance pair-cut**, with conductance $\to 0$ as $n\to\infty$.

**The conjectural mechanism.** The contrapositive is the conjecture: *a width-3 BK graph cannot have a low-conductance pair-cut.* The "order constraints induce expansion defects" mechanism is then the **rigidity argument of `step1.tex`–`step7.tex`**, which shows the bottleneck is *structurally impossible*:

1. **Local interface / grid coordinates (Step 1).** For each *rich* incomparable pair (one with many common neighbours), $\mathcal L(P)$ fibers over a $2$-dimensional grid region $D_{xy}\subseteq[0,t]^2$, and BK moves within a fiber are unit grid moves. The "compatibility geometry" is locally a $\mathbb Z^2$ grid (plus a sign) — `generalization.md` §4 calls it "dimension 2.5."
2. **Weak grid stability (Step 2).** A low-boundary subset of a grid region is close to a monotone staircase — fiberwise, a low-conductance cut must be *locally monotone*.
3. **Coherence + two-interface incompatibility (Steps 3–4).** Two rich interfaces that are *incoherent* (their monotone directions disagree on the overlap) cannot both be locally monotone without forcing many BK boundary crossings. This is the **expansion engine**: incoherence ⟹ high conductance.
4. **Richness + dichotomy + collapse (Steps 5–7).** A width-3 counterexample has enough rich interfaces for the engine to bite; either many are incoherent (immediate contradiction) or almost all are coherent, in which case $P$ collapses to a layered $1$-dimensional form that is balanced by inspection.

That is the precise content of "local swap symmetries cannot globally coexist": you cannot make every rich-interface fiber monotone *and* keep all the interfaces mutually coherent — the order constraints over-determine the local monotone directions, and the residual mismatch *is* the expansion defect. The in-tree status is **conditional on Hypothesis A** (arithmetic richness, `step8.tex` `hyp:arith`), which pins the small-$\gamma$, large-$n$ tail; the rest of the cascade is unconditional.

### 1.6 Summary of the rigorized column

| Daniel's slot | Rigorous form (in-tree) |
|---|---|
| State space | $\mathcal L(P)\subseteq S_n$, uniform $\pi$ |
| Ambient geometry | $G_{\mathrm{BK}}(P)$ = induced subgraph of the permutahedron $1$-skeleton / weak-order Hasse diagram on $\mathcal L(P)$ |
| Local moves | BK moves = adjacent transpositions of incomparable pairs (permutahedron edges that stay in $\mathcal L(P)$) |
| Balanced obstruction | the pair-cut $S_{xy}$ has volume $p_{xy}$; conjecture ⟺ some pair-cut is volume-balanced |
| Curvature / bottleneck / expansion defect | low conductance $\Phi(S_{xy})$ / small spectral gap $\lambda_2$ of the BK chain; Theorem E: counterexample ⟹ low-conductance pair-cut; mechanism = Steps 1–7 rigidity (incoherent interfaces force expansion) |
| Status | conditional on Hypothesis A |

**Key finding of §1.** Daniel's 1/3-2/3 column is *not a new speculative lens*. It is, row for row, the methodology of the in-tree width-3 paper — `main.tex` §"Approach: Cheeger-type expansion on the BK graph" states exactly this program. The avalanche is Daniel re-deriving, from the meta-thesis viewpoint, the spine of his own paper. Any same-vs-distinct verdict must therefore compare the **F-series cohomological program** against **the existing BK-expansion proof**, not against a hypothetical.

---

## §2. The other 1/3-2/3 framing — the F-series cohomological program

The F-series (F1–F15; load-bearing nodes F10 mg-8216, F11 mg-b352, F15 mg-8355) is the second attack on width-3 1/3-2/3. Recap, in the form needed for the dictionary.

### 2.1 State space and ambient

- $\mathrm{PPF}_n$ = the **proper partial orders** on $\{0,\dots,n-1\}$ — non-empty, non-total partial orders, ordered by *reverse refinement* (a finer relation set is *lower*). This is the **space of all posets** on $n$ points, not the linear extensions of one poset.
- $\Delta_n := \Delta(\mathrm{PPF}_n)$, its order complex of strict chains — an $(n{-}2)$-dimensional simplicial complex.
- $S_n$ acts on $\Delta_n$ by relabelling. The inclusion $\iota_n:\mathrm{PPF}_n\hookrightarrow\mathrm{PPF}_{n+1}$ adds an element incomparable to all, realizing $\Delta_n$ as a subcomplex of $\Delta_{n+1}$.

The "local move" here is a **refinement cover** $Q\lessdot Q'$ in $\mathrm{PPF}_n$: $Q'$ adds one relation to $Q$. An edge of $\Delta_n$.

### 2.2 The cohomological obstruction — sphericity + sign-concentration

The F-series obstruction is the pair of statements (F10 §1.2):

- **(H-Cox).** $\Delta_n\simeq_{\mathbb Q}S^{n-2}$: $\widetilde H^k(\Delta_n;\mathbb Q)=0$ for $k\ne n-2$, and $\widetilde H^{n-2}(\Delta_n;\mathbb Q)$ is $1$-dimensional.
- **(sgn).** $\widetilde H^{n-2}(\Delta_n;\mathbb Q)\cong\mathrm{sgn}_{S_n}$ as an $S_n$-representation.

Together: $\Delta_n$ is a rational homology sphere whose top cohomology is forced into the *sign representation*. Note the obstruction has **two faces**:

- a **vanishing** face — $\widetilde H^k=0$ for $0<k<n-2$ — which is an *acyclicity / expansion-type* statement (the complex has no intermediate homology);
- a **non-vanishing** face — $\widetilde H^{n-2}\ne 0$, and specifically $=\mathrm{sgn}$ — which is a *non-degeneracy / sphericity* statement (there is a forced top class, and it is sign-isotypic).

### 2.3 $\omega_{\mathrm{bal}}$ and the ICOP pairing

$\omega_{\mathrm{bal}}^{(n)}$ is the unique-up-to-scalar generator of $\widetilde H^{n-2}(\Delta_n)^{\mathrm{sgn}}$ — the "balanced cocycle." The link to the *numerical* 1/3-2/3 statement is the **Inductive Cohomological Obstruction Principle** (ICOP, F8 / F10 §5): along a canonical critical $(n{-}2)$-cell $c^*_n=(P_0\subset\dots\subset P_{n-2})$ with $\langle\omega_{\mathrm{bal}}^{(n)},c^*_n\rangle\ne 0$, the per-step Kahn–Saks probabilities $\Pr_{P_k}(a_k,b_k)$ lie in the Brightwell–Felsner–Trotter interval $[3/11,8/11]\subset[1/3,2/3]$. The cohomology class is the *certificate*; the critical chain is the *witness*; the cover step at a poset $P$ on the chain is its balanced pair.

### 2.4 "Cannot remain globally isotropic," cohomological form

F11 §3.3 makes the meta-thesis phrase precise on this side. For the $S_n$-action, rational transfer gives $\widetilde H^{\,*}(\Delta_n/S_n;\mathbb Q)=\widetilde H^{\,*}(\Delta_n;\mathbb Q)^{S_n}=(\mathrm{sgn}_{S_n})^{S_n}=0$: the **rational orbit-quotient is contractible**. All cohomological content lives in the sign-isotypic part, *invisible* to the quotient. That is "the constrained geometry cannot remain globally isotropic," cohomological form: the content cannot be spread $S_n$-symmetrically — it is forced into the one non-trivial $1$-dimensional isotype.

### 2.5 The open gap

F10 reduces width-3 1/3-2/3 at general $n$, gap-free, to **(UCC)** — Uniform Cofiber Concentration: for every $n$, $\widetilde H^{\,*}(\Delta_{n+1}/\Delta_n)=2\cdot\mathrm{sgn}_{S_n}$ concentrated in degree $n-1$, with the cofiber connecting map $\delta_n$ injective. F10 §7.2 sharpens (UCC) to **(FG-Cofiber)**: identify the correct degree-shift-aware functor-category framework in which the cofiber-cohomology sequence $(\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n))_n$ is the diagonal of a *finitely generated* object, and prove that finite generation. F11 narrowed the three routes to route (ii) — a central-stability presentation, with the degree-shift transition map identified as the triple connecting homomorphism $\partial_n$. F15 (mg-8355) found $\partial_3$ has rank $1$, **not** an isomorphism, so route (ii)'s simplest form ($M(0)^{\oplus2}$ free) is dead; the weaker bounded-central-stability form is still live. **This doc does not touch that chain** — it is recorded only as the F-series open gap, for the dictionary.

---

## §3. The two-framings dictionary

### 3.1 The shared substrate

Both framings are ultimately about the **same atomic data**: for each poset $P$ and each incomparable pair $x\parallel y$, the two counts
$$
  \lvert\mathcal L_{x<y}(P)\rvert
  \quad\text{and}\quad
  \lvert\mathcal L_{y<x}(P)\rvert,
  \qquad
  \lvert\mathcal L_{x<y}(P)\rvert + \lvert\mathcal L_{y<x}(P)\rvert = \lvert\mathcal L(P)\rvert,
$$
and the "decide one incomparable pair" move. This is visible on both sides:

- **Expansion side.** $p_{xy}=|\mathcal L_{x<y}(P)|/|\mathcal L(P)|$ is the *volume fraction* of the pair-cut $S_{xy}$.
- **F-series side.** Adding the relation $x<y$ to $P$ is the refinement cover $P\lessdot P^{+}$ in $\mathrm{PPF}_n$, and $|\mathcal L(P^{+})| = |\mathcal L_{x<y}(P)|$ — the linear extensions of the refined poset are exactly the extensions of $P$ that put $x$ before $y$. So $p_{xy} = |\mathcal L(P^{+})|/|\mathcal L(P)|$ is a *cover-step weight* in the refinement lattice.

So the two framings are **two different geometric organizations of one underlying set of numbers** — the linear-extension counts of the refinement lattice. This is the deepest layer of the dictionary, and it is solid.

### 3.2 The refinement cover ⟷ pair-cut correspondence

The shared substrate gives the cleanest single dictionary entry:

> A refinement cover $P\lessdot P^{+}$ in $\mathrm{PPF}_n$ (adding the relation $x<y$) corresponds to the pair-cut $S_{xy}$ of $G_{\mathrm{BK}}(P)$: the *upper* side of the cut, $\mathcal L_{x<y}(P)$, is $\mathcal L(P^{+})$; the cut's volume is the cover-step weight; the cut's boundary $\partial S_{xy}$ is the set of BK moves swapping $x,y$, i.e. the moves that "undo the cover."

This correspondence is **real and exact** at the level of the atomic move. It is the hinge of the whole dictionary.

### 3.3 The candidate dictionary table

The ticket asks specifically for three rows. Built out, with a status flag for each (✓ holds / ◐ partial / ✗ breaks):

| F-series 1/3-2/3 object | BK / Bruhat-expansion object | Status |
|---|---|---|
| $\mathrm{PPF}_n$, the refinement lattice of *all* posets on $[n]$ | — *no per-$P$ analog* — the BK lens fixes $P$; the closest object is the *single interval* $[\,\widehat 0,\ \text{total orders}\,]$ above $P$, whose maximal elements are $\mathcal L(P)$ | ◐ |
| $\Delta_n=\Delta(\mathrm{PPF}_n)$, the order complex (dim $n{-}2$) | $G_{\mathrm{BK}}(P)$, the BK graph (a $1$-complex) — *or* a complex on $\mathcal L(P)$ such as the order complex of $\mathcal L(P)$ in the weak order | ✗ different objects (see §3.4) |
| refinement cover $P\lessdot P^{+}$ (edge of $\Delta_n$) | pair-cut $S_{xy}$ of $G_{\mathrm{BK}}(P)$ / a BK move swapping $x,y$ | ✓ (§3.2) |
| $\omega_{\mathrm{bal}}^{(n)}$, the sign-rep cocycle in $\widetilde H^{n-2}(\Delta_n)^{\mathrm{sgn}}$ | the *expansion defect*: the low-conductance pair-cut / the small-$\lambda_2$ eigenvector of the BK chain | ◐ resonant, not equal (see §3.4, §4) |
| ICOP pairing $\langle\omega_{\mathrm{bal}}^{(n)},c^*_n\rangle\ne0$ along a critical chain | Theorem E + Steps 1–7: a counterexample's pair-cut *cannot* be made low-conductance | ◐ both certify "a balanced pair exists," by different mechanisms |
| cofiber LES induction $\Delta_n\hookrightarrow\Delta_{n+1}$, lifting $\omega_{\mathrm{bal}}^{(n)}\rightsquigarrow\omega_{\mathrm{bal}}^{(n+1)}$ | **no analog** — the BK-expansion proof does *not* induct on $n$ (see §3.4) | ✗ |
| $S_n$-equivariance; $\mathrm{sgn}_{S_n}$ isotype; orbit-quotient contractible | $\mathrm{Aut}(P)$ + the positional structure of $\mathcal L(P)$; the sign marker $\sigma(L)\in\{\pm\}$ of `step1.tex` | ◐ a sign appears on both sides, but the groups differ (see §3.4) |

### 3.4 Where the dictionary holds and where it breaks

**Holds (✓).** The atomic-move row, §3.2. The pair-orientation counts and the "decide a pair" operation are genuinely common. Any honest verdict must keep this: the two framings are *not* about unrelated mathematics.

**Partial (◐), with the discrepancy named.**

- *$\mathrm{PPF}_n$ vs. fixed $P$.* The F-series object is **global over all posets on $[n]$ at once** — $\mathrm{PPF}_n$ contains every $P$, and a single critical chain threads through many of them. The BK lens is **per-$P$**: it fixes one width-3 poset and studies *its* $\mathcal L(P)$. A given $P$ appears as a *vertex* of $\Delta_n$ in the F-series and as the *whole ambient* in the BK lens. The translation "F-series statement at level $n$, restricted to width-3 sub-chains through $P$" exists (F10 §6.6 step 5) but it is a *specialization*, not an identification.
- *The sign.* Both sides carry a sign. F-series: the $\mathrm{sgn}_{S_n}$ isotype of the *relabelling* action $S_n\curvearrowright\mathrm{PPF}_n$. BK side: the marker $\sigma(L)=+$ iff $x<_L y$ (`step1.tex` §"The fiber and the sign marker"), and the Step-3 canonical sign $\eta_{xy}$ of a rich interface. These are *both* $\mathbb Z/2$-gradings tied to the orientation of a pair — a real resonance — but the F-series sign is a representation of the *global* symmetric group acting on the space of posets, while the BK sign is a *local* orientation datum of a single interface inside one $\mathcal L(P)$. Same flavour, different group, different role.
- *$\omega_{\mathrm{bal}}$ vs. the expansion defect.* This is the row the ticket most wants pinned. On the F-series side $\omega_{\mathrm{bal}}$ is a *cohomology class that is forced to be present* — the **non-vanishing** face of the obstruction (§2.2). On the BK side the "expansion defect" is a *low-conductance cut / small-$\lambda_2$ eigenvector* — and the conjecture wants this to be **absent** (no low-conductance pair-cut). Up to the sign of the statement, these are *dual*: "a forced top cohomology class" (sphere) vs. "no sparse cut" (expander). They are linked — see §4.2 — but they are not the same object, and they even point in opposite directions of the "homology present / homology absent" axis.

**Breaks (✗).**

- *The complexes are different.* $\Delta(\mathrm{PPF}_n)$ is $(n{-}2)$-dimensional, on partial-order vertices, with $S_n$ relabelling. $G_{\mathrm{BK}}(P)$ is $1$-dimensional, on linear-extension vertices, per fixed $P$. There is no known map identifying one's cohomology with the other's spectral data. (One *can* build a complex on $\mathcal L(P)$ — e.g. the order complex of $\mathcal L(P)$ under the weak order — but that is again a per-$P$ object and is not $\Delta(\mathrm{PPF}_n)$.)
- *The cofiber LES induction has no BK-side analog.* The F-series proof **inducts on $n$** via $\Delta_n\hookrightarrow\Delta_{n+1}$ and the cofiber long exact sequence — this is its spine (F10 §6.2). The BK-expansion proof does **not** induct on $n$ at all: Theorem E holds *uniformly* for all $n\ge n_0$, and the contradiction comes from *fixed-$P$* geometry (Steps 1–7); the only recursion in the BK proof is the *width* recursion capped by Linial's width-2 theorem (`generalization.md` §3, obstacle O4) — a recursion on $w$, not $n$. The F-series $\iota_n$ move (add an isolated element) *does* have a BK-side shadow — it multiplies $|\mathcal L(P)|$ by $n+1$, exactly F8's multiplicativity law — but on the BK side this operation is structurally inert (it just rescales), whereas in the F-series it is load-bearing. The *operation* corresponds; its *role* does not. This is a genuine, important structural divergence.

---

## §4. Same obstruction, or distinct attack?

### 4.1 Three reasons they are not the same object

1. **Different geometric carrier.** Expansion lens: the BK graph $G_{\mathrm{BK}}(P)$ — a $1$-complex on $\mathcal L(P)$, per fixed $P$. F-series: $\Delta(\mathrm{PPF}_n)$ — an $(n{-}2)$-complex on the space of all posets. Different dimension, different vertex set, different symmetry group in the load-bearing role ($\mathrm{Aut}(P)$ + positional structure vs. $S_n$ relabelling). §3.4.
2. **Opposite sign of the (co)homological statement.** The F-series obstruction *forces a class to exist* ($\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}\ne 0$: $\Delta_n$ is a homology *sphere*). The expansion obstruction *forbids a cut from being sparse* ($G_{\mathrm{BK}}(P)$ is an *expander* on pair-cuts). Sphericity and expansion are, in the relevant degree, *dual* phenomena, not the same one.
3. **Different proof machinery and different open gaps.** The BK-expansion proof (the in-tree paper) uses Dirichlet-form comparison, grid-stability, interface coherence — and is gated on **Hypothesis A** (arithmetic richness). The F-series uses cofiber discrete Morse, FI representation stability, cofiber long exact sequences — and is gated on **(FG-Cofiber)** (FI finite generation of a degree-shift-aware object). Neither proof invokes the other's tools; neither open gap is the other. Two genuinely independent routes, with two independent residual hypotheses.

### 4.2 The meta-principle that nonetheless links them

They are *not* unrelated, and the verdict must say why. Three layers of genuine connection:

- **Shared substrate (§3.1–§3.2).** Both organize the same pair-orientation linear-extension counts; the refinement cover ⟷ pair-cut correspondence is exact.
- **The expansion ⟷ cohomology meta-principle.** There is a real, classical bridge between graph expansion and (co)homology vanishing: Cheeger's inequality (graph expansion ⟺ spectral gap of the degree-$0$ Laplacian), Garland's method (vanishing of higher cohomology of a complex from spectral gaps of vertex links), and coboundary / topological expansion (Linial–Meshulam–Wallach, Gromov: quantitative cohomology vanishing *is* a higher expansion). Under this principle, "expander" and "acyclic in the relevant degree" are two faces of one phenomenon. So Daniel's instinct that the expansion defect is "a cohomological/curvature phenomenon" is **correct** — expansion genuinely *has* a cohomological shadow.
- **Both instantiate the meta-thesis.** "A constrained compatibility geometry cannot remain globally isotropic" is a true description of *both*: the BK graph cannot have a structured sparse cut (isotropy = uniform low-expansion would mean a bottleneck); $\Delta_n$ cannot spread its content $S_n$-symmetrically (isotropy = trivial-isotype content). The meta-thesis is a *family resemblance* that both framings satisfy.

### 4.3 Why the resonance is not identity

The crucial distinction. The expansion ⟷ cohomology meta-principle, applied to the **BK lens**, produces the (co)homology of the **BK graph itself** — the degree-$0$/degree-$1$ Laplacian spectral data of $G_{\mathrm{BK}}(P)$, or at most the cohomology of a complex *built on $\mathcal L(P)$* (e.g. its weak-order complex). It does **not** produce $\widetilde H^{\,*}(\Delta(\mathrm{PPF}_n))$. The F-series cohomology is the cohomology of a *different complex* — the order complex of the poset-of-posets — and there is no theorem (and no evident reason) identifying the BK-chain spectral gap of a fixed $P$ with the sign-isotypic cohomology of $\Delta(\mathrm{PPF}_n)$.

So Daniel's "cohomological/curvature" description is **resonance, not identity**: the expansion defect *is* cohomological in flavour, but it is the cohomology of $G_{\mathrm{BK}}(P)$ / a $\mathcal L(P)$-complex, a *cousin* of — not equal to — the F-series $\widetilde H^{\,*}(\Delta_n)$. Calling the two framings "the same obstruction" would conflate two different cohomologies that happen to be siblings under one meta-principle.

### 4.4 What a literal unification would require

For a **GREEN-same-mechanism** verdict one would need, at minimum, *one* of:

- **(U1)** A natural complex $K(P)$ built from a *fixed* poset $P$ — e.g. on $\mathcal L(P)$, or a per-$P$ "Quillen fiber" $X(P)$ — whose sign-isotypic (or otherwise distinguished) cohomology *is* the BK-chain expansion data of $G_{\mathrm{BK}}(P)$, **and** a comparison map $K(P)\to\Delta(\mathrm{PPF}_n)$ identifying that cohomology with the F-series $\omega_{\mathrm{bal}}$ slice. No such $K(P)$ is in hand. (The F8'' "Quillen fiber $X_n$" is per-$n$, not per-$P$, and is parked.)
- **(U2)** A theorem of the form "the Cheeger constant of $G_{\mathrm{BK}}(P)$ is controlled by $\langle\omega_{\mathrm{bal}},c\rangle$ for chains $c$ through $P$" — turning the ICOP pairing into a *direct* expansion bound. The F-series currently extracts only a *single per-step probability* in $[3/11,8/11]$ from the pairing, not a *cut conductance*; bridging "one balanced cover step" to "the whole cut $S_{xy}$ is non-sparse" is exactly the gap between the cohomological certificate and the expansion statement, and is not bridged.
- **(U3)** A common generalized-Laplacian object specializing to *both* the BK Markov-chain Laplacian and the F-series cofiber/coboundary operator. The dimensions ($1$ vs. $n-2$) and carriers ($\mathcal L(P)$ vs. $\mathrm{PPF}_n$) make this implausible *as a literal identity*; it is more likely that both are *shadows* of a yet-unformulated object than that one *is* the other.

None of (U1)–(U3) is established, and (U3) in particular looks implausible as literal identity. A scoping pass cannot *refute* a future deep unification — but it can, and does, establish that **as currently formulated the two framings are distinct objects with distinct machinery and distinct open gaps**, related by a meta-principle and a shared substrate but not by an identification. That is a definite verdict, not an open question — hence GREEN-distinct-complementary, not AMBER.

---

## §5. Verdict

**GREEN-distinct-complementary.**

The 1/3-2/3 column of Daniel's structural-analogy avalanche is rigorized (§1) and is — row for row — the proof spine of the in-tree width-3 paper (the Bubley–Karzanov-graph / Cheeger-expansion program of `main.tex` + `step8.tex`), not a new speculative lens. The "curvature / bottleneck / expansion defect" row is concretely: low conductance / small spectral gap of the BK Markov chain, with the in-tree concretization being `step8.tex` Theorem E (counterexample ⟹ low-conductance pair-cut) and the mechanism being the Steps 1–7 interface-rigidity argument.

Compared against the F-series cohomological program (§2), the two 1/3-2/3 framings are:

- **Distinct** as mathematical objects (BK graph on $\mathcal L(P)$, a $1$-complex, per fixed $P$ — vs. $\Delta(\mathrm{PPF}_n)$, an $(n{-}2)$-complex on the space of all posets; §4.1.1), **distinct** in the sign of their (co)homological content (expander / no sparse cut — vs. homology sphere / forced top class; §4.1.2), and **distinct** as proof attacks with **distinct open gaps** (Hypothesis A / arithmetic richness — vs. (FG-Cofiber) / FI finite generation; §4.1.3).
- **Complementary and resonant**, not unrelated: they share the substrate of pair-orientation linear-extension counts, with an exact refinement-cover ⟷ pair-cut correspondence (§3.2); they are linked by the genuine expansion ⟷ cohomology meta-principle (Cheeger / Garland / topological expansion; §4.2); and both faithfully instantiate the meta-thesis "constrained compatibility geometry cannot remain globally isotropic" (§4.2).

Daniel's independent description of the expansion defect as a *"cohomological/curvature phenomenon"* is **correct as resonance**: expansion *does* carry a cohomological shadow. But it is the cohomology of the *BK graph / an $\mathcal L(P)$-complex*, a cousin of — not equal to — the F-series $\widetilde H^{\,*}(\Delta(\mathrm{PPF}_n))$ (§4.3). A literal unification (GREEN-same-mechanism) would require one of the three specific bridges of §4.4, none of which is in hand and one of which (a common generalized Laplacian) looks implausible as a literal identity.

**For the meta-thesis, this is the stronger outcome.** "Two non-isotropy mechanisms for width-3 1/3-2/3" — an expansion/spectral mechanism and a cohomological/representation-stability mechanism, independently formulated, with independent residual hypotheses — shows the non-isotropy principle is *robust*: it survives re-organization of the same combinatorial data into two different geometries. The cross-product comparison with Union-Closed (Daniel's parked scope decision) gains *two* 1/3-2/3 reference points rather than one.

This is a clean scoping verdict, not AMBER: §3 builds the dictionary to the extent it is buildable (with every row's status — ✓/◐/✗ — named and justified), §4.4 states precisely what would upgrade the verdict to GREEN-same-mechanism, and the same-vs-distinct question is *answered* (distinct-but-resonant), not deferred.

---

## §6. Recommendations and follow-ups

All recommendations are **off the route-(ii) critical path** (F15 / mg-8355) — they neither depend on it nor feed it, per the ticket's scope discipline.

1. **(Low priority, methodology-paper material.)** The expansion ⟷ cohomology meta-principle (§4.2) deserves one explicit paragraph in the F-series methodology paper: it explains *why* Daniel's expander instinct and the F-series cohomological framing "rhyme," and it correctly positions them as two routes, not one. This is write-up, not research.
2. **(Speculative, parked — only if Daniel signals.)** The bridge (U2) of §4.4 — "does the ICOP pairing $\langle\omega_{\mathrm{bal}},c\rangle$ control a BK-graph conductance?" — is the single most concrete same-vs-distinct sharpening. It would need a per-$P$ reformulation of the F-series pairing and is genuinely open; it is *not* recommended as a near-term ticket (it is harder than either framing's current critical path) but is logged here as the precise locus where a future unification, if any, would have to act.
3. **(Cross-product input, parked with Daniel's scope decision.)** When Daniel rules on the `1/3-2/3 ⟷ Union-Closed` cross-product scope, the Union-Closed column should be checked against *both* 1/3-2/3 mechanisms (expansion *and* cohomological), since §5 establishes there are two. Whether Union-Closed resonates with one, both, or neither is a sharper test of the meta-thesis than a single-mechanism comparison.
4. **No follow-up touches F15 / mg-8355 or its successors.** The route-(ii) chain is the critical path; this doc is parallel research-capture and ends here.

---

## §7. References

### 7.1 In-tree (the BK-expansion 1/3-2/3 column)

- `main.tex` — §"The 1/3–2/3 conjecture," §"Main result," §"Approach: Cheeger-type expansion on the BK graph," §"Comparison with previous approaches." The eight-step BK-expansion program; conditional on Hypothesis A.
- `step1.tex` — §"Poset, linear extensions, BK graph"; §"The fiber and the sign marker." The state space, the BK graph definition, the rich-pair fiber / $\mathbb Z^2$-grid local model, the sign marker $\sigma(L)$.
- `step8.tex` — §"Theorem E: counterexample implies low BK conductance"; `lem:dirichlet-conductance`; `hyp:arith` (Hypothesis A). The Cheeger/conductance concretization of "expansion defect."
- `generalization.md` — §4 "How the BK graph changes with width"; §3 "The Linial-width-2 ceiling" (obstacle O4 — the BK proof's recursion is on *width*, not $n$).

### 7.2 The F-series cohomological 1/3-2/3 column

- mg-8216 (F10) — `docs/general-n-proof-synthesis.md`. §1.2 (H-Cox)+(sgn); §5 ICOP; §6.2–§6.3 the cofiber-LES induction and (UCC); §7.2 (FG-Cofiber); §6.6 the width-3 specialization.
- mg-b352 (F11) — `docs/state-F11.md`. §3.3 the rational orbit-quotient is contractible ("cannot remain globally isotropic," cohomological form); §4 the triple connecting map $\partial_n$; route survey.
- mg-8355 (F15) — `docs/state-F15.md`, `docs/compatibility-geometry-F15-e2-partial-test.md`. $\partial_3$ rank $1$, not iso; route-(ii) status. **The route-(ii) critical-path chain — referenced only, not touched.**
- mg-1e99 (F8) — ICOP framework, $\omega_{\mathrm{bal}}$ inductive construction. mg-6295 / mg-759d — M1 (cofiber Morse) / M2 (FI rep-stability). mg-b345 (F8'') — the parked Quillen-fiber route.

### 7.3 Mathematical literature

- M. Bubley, M. Karzanov, *Faster random generation of linear extensions* (1998). The BK Markov chain; spectral gap controls mixing.
- S. Kislitsyn (1968); M. Fredman (1976); N. Linial, *The information-theoretic bound is good for merging*, SIAM J. Comput. 13 (1984). The 1/3-2/3 conjecture; Linial's width-2 theorem (the BK proof's recursion base).
- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984). G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — the $[3/11,8/11]$ interval.
- J. Cheeger (1970); the discrete Cheeger inequality for reversible Markov chains (Lawler–Sokal, Sinclair–Jerrum). Graph expansion ⟺ spectral gap.
- H. Garland, *p-adic curvature and the cohomology of discrete subgroups of p-adic groups*, Ann. of Math. 97 (1973). Spectral-gap ⟹ cohomology-vanishing — the meta-principle of §4.2.
- N. Linial, R. Meshulam, *Homological connectivity of random 2-complexes* (2006); M. Gromov, *Singularities, expanders and topology of maps* (2010). Coboundary / topological expansion — quantitative cohomology vanishing as higher expansion.
- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability...*, Duke Math. J. 164 (2015); E. Ramos (2017); A. Putman (2015); P. Patzt (2017). The F-series representation-stability machinery — distinct from the expansion machinery (§4.1.3).

### 7.4 Source

- Mayor forward 2026-05-14T12:55Z — the consolidated 28-piece Daniel structural-analogy avalanche (source mail IDs `1778761991854309000.*`–`1778763227573643000.*`). Meta-thesis; the `1/3-2/3 ⟷ Union-Closed` dictionary; the 1/3-2/3 column rigorized here.

---

*Polecat: mg-26fc. Branch: `compat-geom-mg26fc-bruhat-expansion-lens`. Verdict: **GREEN-distinct-complementary** — the 1/3-2/3 column = the in-tree BK-expansion proof spine; it and the F-series cohomological program are distinct mathematical objects with distinct machinery and distinct open gaps (Hypothesis A vs. FG-Cofiber), but resonant — shared substrate (pair-orientation linear-extension counts), exact refinement-cover ⟷ pair-cut correspondence, linked by the expansion ⟷ cohomology meta-principle. Daniel's "cohomological/curvature" instinct is correct as resonance, not identity. Two non-isotropy mechanisms, not one — the stronger meta-thesis outcome. No new axioms; no Lean changes; no computation. Route-(ii) chain (F15/mg-8355) untouched.*
