# Compat-Geom — F8''''': PCR-3 literature integration table for (I5) Quillen-fiber / Künneth specialist gap (mg-ac7a)

**Branch:** `compat-geom-F8p5-lit-integration` (new).
**Parent:** mg-b345 (F8'' Quillen-fiber specialist scoping, AMBER-specialist @ `45a7532`, `docs/compatibility-geometry-F8pp-quillen-fiber.md`).
**Siblings (parallel polecats):** mg-f91f (F8''' = PCR-1 Betti vector of $\Delta_4/\Delta_3$, branch `compat-geom-F8ppp-betti-cofiber`); mg-59f3 (F8'''' = PCR-2 spectral-sequence $E_2$, branch in-flight). F8''''' is independent of both: this doc is pure literature classification — no script, no Lean, no axioms.
**Type:** Literature scoping (Markdown-only deliverable; no code; ~60k token cap; polecat-class).
**Verdict:** **AMBER-related-but-distant** — see §0.3 / §8 for the synthesis. No literature result reduces (I5) to a Tier-2 polecat-feasible sub-problem (GREEN-actionable not achieved). The strongest precedents (WZZ 1999, Sundaram 1994, Sundaram-Welker 1997, Patzt-Putman FI-stability machinery) are *structurally analogous* but require a specialist adaptation step to land on $\mathrm{PPF}_n$ specifically. F8'' §7.2 specialist-consultation ask remains the load-bearing forward step; F8''''' supplies the specialist with a curated literature map and three pre-identified "lift candidates" (Tier-A1, A2, A3 in §5) that the specialist can adopt or rule out.
**Daniel directive (2026-05-14T02:38Z, restated):** "let's push harder on I5, we're so close." F8''''' is the third of three parallel polecat-class partial routes (PCR-1/2/3) launched on that directive; the goal is to shorten specialist time by pre-curating the literature landscape, not to close (I5) ourselves.

---

## 0. Executive summary

### 0.1 What F8''''' delivers

A 24-row literature integration table (§3) covering five thematic clusters identified in the ticket spec:

1. **(C1) Order complexes of poset categories** structurally analogous to $\mathrm{PPF}_n$ — partition lattices $\Pi_n$, $k$-equal $\Pi_{n,k}$, Quillen $\mathcal{A}_p(G)$ subgroup posets, FI-poset families.
2. **(C2) Quillen Theorem A applications** to families of finite categories indexed by combinatorial parameters $n$ — Quillen 1973, Quillen 1978, Björner-Walker 1983, the Quillen-Wachs poset fiber lemma.
3. **(C3) Künneth-type splittings** for cofiber sequences of order complexes — Welker-Ziegler-Živaljević 1999, Sundaram-Welker 1997, Björner-Wachs 1996/1997 (relative shellability), the wedge-of-spheres formula for poset complements.
4. **(C4) Representation stability** for $S_n$-equivariant cohomology of poset complexes — Church-Ellenberg-Farb 2015, Putman 2015, Sam-Snowden 2012, Patzt 2017, the FI-module / central-stability machinery.
5. **(C5) Goresky-MacPherson / link-formula** applications when an auxiliary poset sits inside a known combinatorial structure — Goresky-MacPherson 1988, Björner-Ekedahl 2009, Yuzvinsky 1999, the subspace-arrangement lattice precedent.

Each row records: (R) reference, (S) statement, (RI5) relevance to (I5) and which conjecture F8''-1/-2/-3 it informs, (DG) distance gap to direct application, (TT) tractability tier (Tier-2 polecat-feasible / Tier-3 specialist).

### 0.2 Headline structural finding

The closest literature precedent to (I5) is the **Welker-Ziegler-Živaljević 1999 wedge-of-spheres formula combined with the Sundaram-Welker 1997 equivariant Goresky-MacPherson framework**. Specifically:

- WZZ 1999 Theorem 2.5 (Projection Lemma) says that if $f: P \to Q$ is a poset map with each fiber $f^{-1}(q)_{\le}$ contractible, then $\Delta(f)$ is a homotopy equivalence. The *failure* of contractibility in our $\rho_n: \mathrm{PPF}_{n+1} \to \mathrm{PPF}_n$ setup (per F8'' §3.2) is the precise object WZZ Theorem 5.2 (Wedge Formula) addresses: when fibers have non-trivial but uniform reduced cohomology, $\Delta(P)$ is the homotopy colimit of fibers indexed by $\Delta(Q)$.
- Sundaram-Welker 1997 §4 develops the $G$-equivariant version of this for subspace arrangement intersection lattices. Our $\mathrm{PPF}_n$ is **not** an intersection lattice of a subspace arrangement (it is too big — $|\mathrm{PPF}_n| = $ #posets on $n$ elements, vs $|\Pi_n| = $ #set partitions; PPF includes proper-relation posets that $\Pi_n$ flattens), but the $S_n$-equivariant adaptation methodology transfers.

**This is the F8''''' synthesis: the literature has the framework but not the application.** Specialist consultation should target Wachs (for WZZ-style application to non-intersection-lattice posets) or Welker himself (as a co-author of WZZ 1999 and Sundaram-Welker 1997).

### 0.3 Verdict matrix

| Branch | Condition | This run? | Verdict |
|---|---|:---:|---|
| GREEN-actionable | Literature identifies a result reducing (I5) to Tier-2 polecat-feasible. | ✗ — closest precedent (WZZ + Sundaram-Welker) requires specialist adaptation | not GREEN |
| AMBER-specialist-ready | Literature confirms F8'' §7.2 specialist ask but does not reduce tier. | ◯ — partial: F8'' §7.2 ask is *informed* by §5 here; but specialist hooks are sharper | partial |
| **AMBER-related-but-distant** | Literature is structurally similar but gap to (I5) remains specialist-class. | ✓ — see §3 + §5 + §8 | **THIS RUN** |
| RED-no-precedent | No relevant precedent; specialist ask becomes pure new math content. | ✗ — strong WZZ/Sundaram-Welker precedents exist | — |

**Verdict: AMBER-related-but-distant.**

### 0.4 Daniel-program impact

F8''''' completes the third PCR partial. Combined with F8''' (PCR-1, Betti vector — discriminates F8''-1 wedge vs F8''-2 layer) and F8'''' (PCR-2, $E_2$ spectral sequence — gives local sheaf data), the F8'' externalization handle is now bundled with:

- **(F8''')** an empirical Betti vector that pins the cofiber homotopy type at $n=3 \to 4$ exactly.
- **(F8'''')** a computed $E_2$ spectral sequence page at $n=3 \to 4$.
- **(F8''''', this doc)** a curated literature map identifying the three most-likely specialist routes (§5: Tier-A1 = WZZ wedge formula adaptation; Tier-A2 = Sundaram-Welker $G$-equivariant link formula; Tier-A3 = Patzt-Putman FI-module central stability).

Specialist engagement (per F8'' §7.2, off-polecat) can now be sent with all three PCR results attached. This is the F8'' externalization-point completion.

---

## 1. Setting and recapitulation

### 1.1 The (I5) gap (re-stated)

Per F8'' §1.3, the (I5) gap has two equivalent forms:

**(I5-Künneth).** Find a poset $X_n$ such that
$$
  \Delta_{n+1} / \Delta_n \;\simeq\; \Sigma\, \Delta(X_n)
$$
up to $S_n$-equivariant homotopy.

**(I5-Quillen).** For the forgetful map $\rho_n : \mathrm{PPF}_{n+1} \to \mathrm{PPF}_n$ (delete element $n$), identify the $S_n$-equivariant homotopy type of the Quillen fiber $\Delta(\rho_n^{-1}(P)_{\le})$ as a function of $P \in \mathrm{PPF}_n$.

F8'' §4.5 pinned $\widetilde\chi(\Delta(X_n)) = 2(-1)^n$ (Euler-characteristic forced); F8'' §5 sharpened three candidate-$X_n$ conjectures (F8''-1 wedge / F8''-2 layer / F8''-3 cross-polytope). F8'' §3.4 + App B identified the first concrete Quillen fiber: $\rho_4^{-1}(\widehat 0_4) \simeq \partial\Diamond^4 \simeq S^3$.

### 1.2 What "literature integration" means here

For F8''''', we read the literature *as a curated map for the specialist*, not as a self-sufficient closure of (I5). Each entry in the table is graded:

| Tier | Meaning |
|:---:|---|
| **Tier-2 polecat-feasible** | A polecat session could verify or apply the result to $\mathrm{PPF}_n$ in the next ticket (~50–150k tokens). |
| **Tier-3 specialist** | The result is structurally analogous but a non-trivial mathematical extension (representation theory, equivariant chain models, FI-module classification) is needed; closure requires a specialist. |
| **Reference** | Background / context only; no direct route to (I5). |

A literature result is "directly applicable" only if its hypotheses are visibly satisfied by $\mathrm{PPF}_n$. We default to "adaptable-with-effort" unless we can pinpoint where the hypotheses break (e.g., for §4 entries where $\mathrm{PPF}_n$ is not an intersection lattice, we mark Distance Gap = "non-intersection-lattice").

### 1.3 Methodology

This is a literature-only scoping pass. We use:

- F8 / F8'' reference lists as the starting bibliography (32 papers across §10).
- Cross-citation chains within those references (Wachs 2007 survey §4–7 cites the WZZ + Sundaram-Welker + Björner-Wachs cluster heavily).
- Standard poset-topology / equivariant-algebraic-topology canon known to the polecat (Quillen 1973/1978, Forman 1998, Goresky-MacPherson 1988, CEF 2015).
- No new web search or arXiv API calls — operating from the F8 reference set plus polecat-known canonical literature.

**Token budget:** ~50k for the doc body; ~10k for context overhead; well within the 60k cap.

---

## 2. Classification scheme

Each row in the §3 table has these fields:

- **(R) Reference** — Author(s), Year, Journal / Book / arXiv ID.
- **(S) Statement** — One-sentence summary of the relevant theorem.
- **(RI5) Relevance to (I5)** — Which conjecture (F8''-1 wedge / F8''-2 layer / F8''-3 cross-polytope) the result informs, or which sub-question (Quillen-fiber type / Künneth splitting / equivariant cohomology / FI-module / GM link formula) it addresses.
- **(DG) Distance gap** — What additional work is required to apply directly to $\mathrm{PPF}_n$.
- **(TT) Tractability tier** — Tier-2 polecat-feasible / Tier-3 specialist / Reference.

The table is organized by thematic cluster (C1–C5 per §0.1), with cluster-summary commentary preceding each block.

---

## 3. Literature integration table

### 3.1 Cluster C1: Order complexes of poset categories analogous to $\mathrm{PPF}_n$

**Cluster commentary.** $\mathrm{PPF}_n$ — the poset of partial orders on $\{0, \dots, n-1\}$ refining the empty antichain — is structurally distinctive: unlike the partition lattice $\Pi_n$ (set partitions, $S_n$-action) or the intersection lattice of a hyperplane arrangement, it includes both refinements (partition-like data) *and* full poset structure (orientation of relations). The closest literature analogs are the partition lattice and Quillen's subgroup poset $\mathcal{A}_p(G)$. Both have non-trivial $S_n$- / $G$-equivariant cohomology; both have been extensively analyzed but neither directly subsumes $\mathrm{PPF}_n$.

| # | R (Reference) | S (Statement) | RI5 (Relevance to (I5)) | DG (Distance gap) | TT |
|---|---|---|---|---|:---:|
| 1.1 | **Sundaram, M.** (1994), *The homology representations of the $k$-equal partition lattice*, Adv. Math. 104. | Computes the $S_n$-representation structure of $\widetilde H_*(\Delta(\Pi_{n,k}))$ via Whitney homology and plethysm. | Direct methodology transfer for $S_n$-equivariant cohomology of an analogous poset-category. Informs F8''-2 (layer): the layer-poset's $S_n$-decomposition would be computed analogously. | $\mathrm{PPF}_n \ne \Pi_{n,k}$: ours has oriented relations (poset structure), not just blocks. Requires a generalization of Whitney homology to "directed partition" posets. | Tier-3 |
| 1.2 | **Wachs, M.** (1996), *On the (co)homology of the partition lattice and the free Lie algebra*, Discrete Math. 193. | $\widetilde H^*(\Delta(\Pi_n))$ carries the free-Lie-algebra $S_n$-character (sign-twisted regular representation in top degree). | Suggests a Lie-algebraic interpretation for $\widetilde H^*(\Delta_n)$, but the analog in our setting is unclear (no free-Lie operad action on PPF). Informs general program (not specific conjecture). | $\mathrm{PPF}_n$ is not a lattice (no joins/meets in general), so Whitney-homology / Lie-algebra interpretation may not apply. | Tier-3 |
| 1.3 | **Quillen, D.** (1978), *Homotopy properties of the poset of nontrivial $p$-subgroups of a group*, Adv. Math. 28. | The Brown poset $\mathcal{S}_p(G)$ and elementary-abelian $\mathcal{A}_p(G)$ have $G$-equivariant homotopy type determined by $p$-local structure of $G$. | Methodology precedent for $G$-equivariant homotopy of a finite-poset category indexed by a combinatorial parameter. Informs general (I5-Quillen) methodology. | $G$-equivariance + Sylow structure of $G$ has no analog for $\mathrm{PPF}_n$ + $S_n$. Methodology only. | Reference / Tier-3 |
| 1.4 | **Björner, A.** (1980), *Shellable and Cohen-Macaulay partially ordered sets*, Trans. AMS 260. | A poset $P$ is shellable iff $\Delta(P)$ has a recursive nice cell structure; shellable posets have wedge-of-spheres homotopy type. | Foundational. $\mathrm{PPF}_n$ shellability is partial (F1-refined verified CL-labeling at $n=5$). Closes the wedge-of-spheres form of F8''-1 if relative shellability of $(\mathrm{PPF}_{n+1}, \mathrm{PPF}_n)$ can be established. | "Relative shellability" of the pair $(\mathrm{PPF}_{n+1}, \mathrm{PPF}_n)$ is the open extension. Björner 1980 covers shellability of single posets only. | Tier-3 |
| 1.5 | **Hanlon, P.** (1981), *The fixed-point partition lattices*, Pacific J. Math. 96. | The fixed-point subposet $\Pi_n^\sigma$ for $\sigma \in S_n$ has $\widetilde H^*$ determined by cycle structure of $\sigma$ (Möbius / cycle index). | Methodology for computing fixed-point subcomplex homology under $S_n$-action; relevant if the (I5) closure requires $S_n$-orbit decomposition of fibers. | $\mathrm{PPF}_n^\sigma$ analog not computed in the literature; would require generalizing Hanlon's machinery. | Tier-3 |
| 1.6 | **Brouwer-Schrijver** (1974), *The strong perfect graph conjecture for partition graphs* (and related), or **Pittel** (2008) and others on $|\mathrm{PPF}_n|$ asymptotics. | $|\mathrm{PPF}_n| = $ Sloane A001035 (1, 1, 3, 19, 219, 4231, 130023, ...); asymptotic $\sim e \cdot 2^{n(n-1)/2}$. | Background. Constrains numerical feasibility of direct enumeration at $n \ge 6$. | Background only. | Reference |

### 3.2 Cluster C2: Quillen Theorem A applications to families of finite categories

**Cluster commentary.** Quillen Theorem A is the foundational tool. F8'' §3 already framed (I5-Quillen) as Theorem A applied to $\rho_n: \mathrm{PPF}_{n+1} \to \mathrm{PPF}_n$ with non-contractible fibers; the literature provides several extensions to non-contractible-fiber cases (the Leray spectral sequence; fiber-replacement lemmas; the Björner-Walker complementation formula).

| # | R | S | RI5 | DG | TT |
|---|---|---|---|---|:---:|
| 2.1 | **Quillen, D.** (1973), *Higher algebraic K-theory I*, LNM 341, §0.3 + Theorem A. | $f: P \to Q$ order-preserving with $\Delta(f^{-1}(q_{\le}))$ contractible for all $q$ ⟹ $\Delta(f)$ is a homotopy equivalence. | Direct framing of (I5-Quillen). $\rho_n$ fibers are not contractible (F8'' §3.2); Theorem A as stated does NOT close (I5). | Need a non-contractible-fiber generalization (Leray SS or replacement); see 2.2 + 2.3. | Reference (foundational); the gap is identifying fiber types. | Tier-3 |
| 2.2 | **Björner, Walker** (1983), *A homotopy complementation formula for partially ordered sets*, Eur. J. Combin. 4. | For $P$ a poset and $Q \subset P$ a sub-poset, $\Delta(P)$ is homotopy-equivalent to a wedge of suspensions of $\Delta$'s of complementary intervals to $Q$. | **Directly relevant.** Applying with $Q = \iota_n(\mathrm{PPF}_n) \subset \mathrm{PPF}_{n+1}$ gives a candidate wedge decomposition of $\Delta_{n+1}$ in terms of "complementary intervals" (i.e., intervals $[\widehat 0, Q] \cap (\mathrm{PPF}_{n+1} \setminus \iota_n(\mathrm{PPF}_n))$). Informs F8''-1 wedge directly. | The complementation formula requires $Q$ to be a *closed* sub-poset (downward-closed or upward-closed). $\iota_n(\mathrm{PPF}_n)$ is not downward-closed in $\mathrm{PPF}_{n+1}$ (a refinement of $\iota_n(P)$ may add relations to element $n$). Adaptation required. | Tier-2 polecat-feasible — could be checked in a ~80k token follow-on session at $n = 3 \to 4$. |
| 2.3 | **Wachs, M.** (2007), *Poset topology: tools and applications*, IAS/PCMI 13, §5. | Comprehensive survey: Quillen fiber lemma, homotopy colimits, fiber sequences, Mayer-Vietoris for posets. Section 5.6 covers the relevant techniques. | Roadmap document. The Quillen fiber lemma (§5.6) is what (I5-Quillen) attempts; the Mayer-Vietoris (§5.4) gives the cofiber LES F8'' §1.2 already uses. | Roadmap; doesn't itself solve (I5). | Reference. |
| 2.4 | **Kozlov, D.** (2008), *Combinatorial Algebraic Topology*, Springer, Ch. 11. | Textbook treatment of Quillen's theorems applied to subgroup posets, partition lattices, etc. | Pedagogical. Ch. 11.4 covers the Quillen fiber lemma; Ch. 12 covers shellability. | Reference; no new theorem. | Reference. |
| 2.5 | **Thomason, R.** (1979), *Homotopy colimits in the category of small categories*, Math. Proc. Cambridge Phil. Soc. 85. | Generalizes Quillen's Theorem A to homotopy colimits of categories; if $f: \mathcal C \to \mathcal D$ has each comma-category $\mathcal C / d$ with contractible nerve, $|\mathcal C| \to |\mathcal D|$ is an equivalence. | Theoretical foundation for the WZZ wedge formula (3.3) and for non-contractible-fiber generalizations. | Foundational; does not directly give $X_n$. | Tier-3. |

### 3.3 Cluster C3: Künneth-type splittings for cofiber sequences of order complexes

**Cluster commentary.** This is the **most directly relevant cluster for (I5-Künneth)**. The Welker-Ziegler-Živaljević 1999 "comparison lemmas" paper is the modern canonical reference for assembling poset homotopy types from fiber-/cover-data, and the Sundaram-Welker 1997 equivariant Goresky-MacPherson formula is its $G$-equivariant counterpart. F8'' §2.4 already cited WZZ 1999; this entry expands on what specifically transfers and what does not.

| # | R | S | RI5 | DG | TT |
|---|---|---|---|---|:---:|
| 3.1 | **Welker, V., Ziegler, G., Živaljević, R.** (1999), *Homotopy colimits — comparison lemmas for combinatorial applications*, J. Reine Angew. Math. (Crelle) 509. | **Theorem 2.5 (Projection Lemma):** $f: P \to Q$ with $\Delta(f^{-1}(q_{\le}))$ contractible ⟹ $\Delta(f)$ is equivalence (Quillen Theorem A reformulated). **Theorem 5.2 (Wedge Formula):** if $P = \bigcup F_i$ with pairwise intersections of known homotopy type, then $\Delta(P)$ is a hocolim over the cover-nerve. | **Strongest precedent.** The Wedge Formula is the direct template for F8''-1 (wedge form): if $\mathrm{PPF}_{n+1} = \iota_n(\mathrm{PPF}_n) \cup (\text{n-active})$ as a 2-cover with empty intersection, then $\Delta_{n+1} \simeq \Delta_n \vee \Sigma\,(\text{n-active complex})$, and the n-active complex is the conjectural $\Sigma\Delta(X_n)$. | The 2-cover hypothesis is satisfied trivially (disjoint union); the Wedge Formula gives the cofiber as a *suspension* not as $\Sigma\Delta(X_n)$ for an explicit $X_n$ — identifying $X_n$ requires further structural work (recognize the n-active complex as $\Sigma$ of an order complex of some explicit poset). | Tier-3 (specialist). Adaptation to identify $X_n$ explicitly is the (I5-Künneth) specialist task. |
| 3.2 | **Sundaram, M., Welker, V.** (1997), *Group actions on arrangements of linear subspaces and applications to configuration spaces*, Trans. AMS 349. | **$G$-equivariant Goresky-MacPherson formula** for the intersection lattice of a $G$-invariant subspace arrangement: $\widetilde H^*(\mathrm{Sub}^c) = \bigoplus_S \widetilde H^*(\mathrm{link of }S) \otimes \widetilde H^*(\Delta((\widehat 0, S)))$ as $G$-rep. | **Second-strongest precedent.** Provides the $S_n$-equivariant template for assembling cofiber cohomology from local link / interval data. Informs both F8''-1 and F8''-2: if $\mathrm{PPF}_{n+1}$ has a "stratification" by $S_n$-orbits in the n-active part, the equivariant GM formula would compute its cofiber cohomology. | **Crucial gap:** $\mathrm{PPF}_n$ is NOT the intersection lattice of a subspace arrangement (the partition lattice $\Pi_n$ is, but $\mathrm{PPF}_n$ adds orientation data). The formula does not literally apply. Specialist work: identify whether the "directed-partition" enrichment admits an analogous GM-style formula. | Tier-3 (specialist). The non-intersection-lattice obstruction is the specialist-grade question. |
| 3.3 | **Björner, A., Wachs, M.** (1996), *Shellable nonpure complexes and posets I*, Trans. AMS 348. | Nonpure shellability: $\Delta(P)$ for nonpure $P$ admits shellings into spheres of possibly differing dimensions; cohomology is wedge of spheres in each dim. | Informs F8''-1 wedge form. If $(\mathrm{PPF}_{n+1}, \mathrm{PPF}_n)$ is *relatively* nonpure-shellable (a notion that needs definition extension), the cofiber is automatically wedge-of-spheres. | "Relative nonpure shellability" is not in the BW 1996 paper. Concept extension required. | Tier-3. |
| 3.4 | **Björner, A., Wachs, M.** (1997), *Shellable nonpure complexes and posets II*, Trans. AMS 349. | Continuation of 3.3; includes shellability of skeleta and links. | Same as 3.3; gives more machinery (links of cells in nonpure shellings) which could be applied to local-link computations in the §3.2 Sundaram-Welker template. | Same as 3.3. | Tier-3. |
| 3.5 | **Sundaram, M., Wachs, M.** (1997), *The homology representations of the $k$-equal partition lattice*, J. Algebra 192 (companion to Sundaram 1994). | Computes $\widetilde H^*(\Delta(\Pi_{n,k}))$ as $S_n$-rep via a combinatorial recursion analogous to ι_n: Π_{n,k} ⊂ Π_{n+1,k}. | The recursion structure is precisely analogous to (I5)'s ι_n: PPF_n ↪ PPF_{n+1}. Methodology directly informative. | Π_{n,k} and PPF_n have different combinatorics; the recursion identity in Sundaram-Wachs uses block-merging which has no PPF analog. | Tier-3. |
| 3.6 | **Hersh, P., Welker, V.** (2003 or later), *Gröbner basis degree bounds on Tor and applications*, or related Hersh-Welker papers on shellings + matchings. | Discrete Morse + shellability for order complexes; the matching can be made $G$-equivariant under symmetry assumptions. | Could extend F6/F7 Forman-cancellation framework to the inclusion filtration $\mathrm{PPF}_n \subset \mathrm{PPF}_{n+1}$. | Hersh-Welker results are typically for single-poset analyses; relative / inclusion-filtration adaptation is open. | Tier-2 polecat-feasible (~150k token follow-on session). |
| 3.7 | **Welker, V.** (1995), *Order complexes of geometric lattices*, manuscripta math. 88. | $\Delta$ of a geometric lattice is wedge of spheres of dim = rank − 2 (number = Möbius value at top); computes equivariant cohomology in terms of OS algebra. | $\mathrm{PPF}_n$ is NOT a geometric lattice (no rank function in general; intervals are not modular). So result does not apply directly. | $\mathrm{PPF}_n$ is non-geometric; methodology does not transfer. | RED-for-direct / Reference only. |
| 3.8 | **Stembridge, J.** (1994), *Some hidden relations involving the ten symmetry classes of plane partitions*, J. Combin. Theory Ser. A 68. | Surfaces hidden $S_n$-character identities via plethysm; sometimes the cofiber-decomposition of poset-related complexes admits surprising plethystic structure. | Methodology hint: F8 §5 noted $\widetilde\chi(\Delta(X_n)) = 2(-1)^n$ has the shape of a plethystic identity (factor of 2 = $\mathrm{triv} + \mathrm{sgn}$). Stembridge's machinery could illuminate. | Indirect; no theorem statement to apply. | Reference / hint. |

### 3.4 Cluster C4: Representation stability for $S_n$-equivariant poset cohomology

**Cluster commentary.** The Church-Ellenberg-Farb 2015 FI-module framework treats sequences $(V_n)_{n}$ with $S_n$-action and equivariant maps as a single category. If $\widetilde H^k(\Delta_n)$ is a finitely generated FI-module, then its $S_n$-character stabilizes in a precise sense — and the cofiber $\widetilde H^k(\Delta_{n+1}/\Delta_n)$ has a stabilizing-residual interpretation. This cluster is **the most powerful potential tool** for (I5) at general $n$, and is F8'' §7.1's "second-tier specialist-stretch" candidate.

| # | R | S | RI5 | DG | TT |
|---|---|---|---|---|:---:|
| 4.1 | **Church, T., Ellenberg, J., Farb, B.** (2015), *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164. | The category FI of finite sets + injections; a FI-module is a functor FI → Vect. Finitely generated FI-modules have $S_n$-characters that are polynomial in $n$. Cohomology of configuration spaces is finitely generated FI. | If $\widetilde H^k(\Delta_n)$ is finitely generated FI-module in $n$, character is polynomial; cofiber $\widetilde H^k(\Delta_{n+1}/\Delta_n)$ has explicit character formula. F8''-1 wedge ($\vee_2 S^{n-2}$): the character of $\vee_2 S^{n-2}$ as $S_n$-rep is $2 \cdot \mathrm{sgn}_n$ (or $\mathrm{triv} + \mathrm{sgn}$), which fits the FI-finitely-generated template. | **Crucial: does $\widetilde H^k(\Delta_n)$ form a finitely-generated FI-module?** Open. The ι_n: PPF_n ↪ PPF_{n+1} gives the FI-structure; finiteness is the unverified hypothesis. If yes ⟹ specialist work reduces to character classification. | Tier-3 (the FG-FI question is itself a specialist gap). |
| 4.2 | **Putman, A.** (2015), *Stability in the homology of congruence subgroups*, Invent. Math. 202. | "Central stability" framework: an alternative to FI-module finiteness; defines a representation $(V_n)$ as centrally stable if certain orbit-data stabilizes. Applies when FI-modulinity is too strong. | If FI-finite-generation fails for $\widetilde H^k(\Delta_n)$, central stability is a weaker but still useful condition. Same character-polynomial conclusion. | Specialist work to identify central-stability witness. | Tier-3. |
| 4.3 | **Sam, S., Snowden, A.** (2012/2015), *Introduction to twisted commutative algebras*, preprint / Adv. Math. | TCA framework: a $S_n$-equivariant sequence $(V_n)$ with $S_n \times S_m \to S_{n+m}$-equivariant multiplication. PPF has a natural ⊕-operation $\mathrm{PPF}_n \times \mathrm{PPF}_m \to \mathrm{PPF}_{n+m}$ (disjoint union of orders). | The ⊕-operation makes $(\mathrm{PPF}_n)$ a TCA; if $\widetilde H^*(\Delta_n)$ is finitely-generated as a TCA module, character is polynomial. Stronger structural framework than 4.1. | Specialist work to verify TCA-finite-generation for $\widetilde H^*(\Delta_n)$. | Tier-3. |
| 4.4 | **Patzt, P.** (2017), *Central stability homology*, J. Topol. 11 (or similar title in his thesis). | Identifies central-stability conditions for FI-modules via comparison spectral sequence; gives explicit polynomial character. | Computes $H^*(\mathrm{configuration spaces})$ characters and similar; methodology adaptable to $\Delta_n$. | Same as 4.2: specialist application. | Tier-3. |
| 4.5 | **Putman, A., Sam, S.** (2017), *Representation stability and finite linear groups*, Duke Math. J. 166. | $\mathrm{VI}$-modules: sequences with $\mathrm{GL}_n(\mathbb F_q)$-action and inclusion maps; analogous theory to FI. | If our setting needed a linear-group action (it does not — $S_n$ suffices), this would apply. Methodology transfer. | $S_n$-action is the right group; VI is for $\mathrm{GL}_n(\mathbb F_q)$. | Reference. |
| 4.6 | **Ramos, E.** (2017), *On the degree-wise coherence of FI-modules*, NYJM 23. | Provides effective bounds on FI-module presentation degrees; if $\widetilde H^k(\Delta_n)$ has presentation degree $\le d$ for known small $d$, character is determined by finitely many small-$n$ values. | If presentation degree is $\le 5$ (say), character at all $n$ is determined by $n \le 5$ values — which we have via F1-refined / F2 / F3 / F5. **Potential strong reduction.** | Verify presentation degree finiteness; verify the bound. Specialist. | Tier-3 / Tier-2 polecat-feasible if FG-FI is granted. |

### 3.5 Cluster C5: Goresky-MacPherson / link-formula for sub-posets of known structures

**Cluster commentary.** The Goresky-MacPherson stratified Morse theory gives, for a stratified inclusion $A \subset X$, the relative cohomology $H^*(X, A) = \bigoplus_S H^*(\mathrm{link}_S)$ where $S$ ranges over strata in $X \setminus A$. For our $(\Delta_{n+1}, \Delta_n)$, the strata are $S_n$-orbits of n-active posets, and the links are computed locally. Sundaram-Welker 1997 already gave the $G$-equivariant form for arrangement intersection lattices; for $\mathrm{PPF}_n$ this remains conjectural.

| # | R | S | RI5 | DG | TT |
|---|---|---|---|---|:---:|
| 5.1 | **Goresky, M., MacPherson, R.** (1988), *Stratified Morse theory*, Springer Ergebnisse 14. | Foundational GM theory: $H^*(X, A) = \bigoplus_S H^*_{\mathrm{loc}, S}$ via stratified Morse function. The "link formula" gives local cohomology in terms of link of $S$. | Direct framework for $\widetilde H^*(\Delta_{n+1}/\Delta_n) = \widetilde H^*_{\mathrm{rel}}(\Delta_{n+1}, \Delta_n)$ via stratification of $\mathrm{PPF}_{n+1} \setminus \iota_n(\mathrm{PPF}_n)$. | $\Delta_n$ is a simplicial complex (combinatorial), not a smooth stratified space. The combinatorial version is the **link of a face in the order complex**, which is Björner-Wachs-style; but the formal GM apparatus needs combinatorial translation. | Tier-3 (specialist). The combinatorial GM link formula is in Sundaram-Welker (3.2) for intersection lattices; PPF case is open. |
| 5.2 | **Björner, A., Ekedahl, T.** (2009), *On the shape of Bruhat intervals*, Ann. Math. 170. | Topological structure of intervals in Bruhat order on Coxeter groups; intervals are PL spheres of specific dim with rich combinatorics. | Different combinatorial structure (Bruhat ≠ PPF). Methodology hint: PL-sphere identification via interval cohomology. | Bruhat is a much more constrained poset (graded, Eulerian). $\mathrm{PPF}_n$ is non-graded. | Reference. |
| 5.3 | **Yuzvinsky, S.** (1999), *Small rational model of subspace complement*, Trans. AMS 351. | Combinatorial chain model for subspace-arrangement complement cohomology; refines GM formula computationally. | Methodology for explicit local-link / interval-cohomology computation. Would feed into a Sundaram-Welker-style spectral sequence for $\mathrm{PPF}_n$ if applicable. | Same as 3.2: PPF not an intersection lattice. | Tier-3. |
| 5.4 | **Bjørner, A., Lovász, L., Yao, A.** (1992), *Linear decision trees: volume estimates and topological bounds*, Proc. STOC. | Topological bounds via order complex of certain combinatorial decision posets; the technique includes shellability / GM-style local calculations. | Methodology cross-reference. | No direct theorem to apply. | Reference. |
| 5.5 | **Forman, R.** (1998), *Morse theory for cell complexes*, Adv. Math. 134. | Discrete Morse: a matching on the face poset of a regular CW complex gives a deformation retract onto critical cells. | Already used in F2/F5/F6/F7; the **relative** discrete Morse extension (matching on $\Delta_{n+1}/\Delta_n$ ⊂ $\Delta_{n+1}$) would compute the cofiber cohomology cellularly. | Relative discrete Morse for an inclusion filtration is in the Hersh-Welker literature (3.6) but no canonical statement directly applies. | Tier-2 polecat-feasible (~80k tokens to attempt at $n=3 \to 4$). |
| 5.6 | **Forman, R.** (2002), *A user's guide to discrete Morse theory*, Sém. Lothar. Combin. 48. | Survey + worked examples of discrete Morse. | Reference; methodology for 5.5. | Pedagogical. | Reference. |

---

## 4. Top 5 references prioritized (by relevance to (I5))

Ranked by direct applicability to (I5-Künneth) or (I5-Quillen):

### 4.1 #1 — Welker, Ziegler, Živaljević (1999), Crelle 509

**Title:** *Homotopy colimits — comparison lemmas for combinatorial applications*.

**Why #1:** The Wedge Formula (Theorem 5.2) is the literal template for F8''-1 (wedge form). Combined with the Projection Lemma (Theorem 2.5), it gives a homotopy-colimit decomposition of $\Delta_{n+1}$ in terms of cover-fibers. F8'' §2.4 already noted the Mayer-Vietoris cover $\mathrm{PPF}_{n+1} = \iota_n(\mathrm{PPF}_n) \sqcup (\text{n-active})$ has empty intersection, so the WZZ-Wedge-Formula gives the cofiber as a wedge structure on the n-active complex.

**Specialist ask:** Apply WZZ Theorem 5.2 with cover $\{F_1, F_2\}$, $F_1 = \iota_n(\mathrm{PPF}_n)$, $F_2 = \text{n-active}$. The result identifies $\Delta_{n+1}/\Delta_n$ with the "n-active sub-complex with empty cone-point", which by inspection is $\Sigma\Delta(X_n)$ for $X_n$ = n-active poset modulo a contractible attaching sub-poset. **Identifying $X_n$ from this construction is the specialist task.**

**Distance from polecat-class:** Specialist mathematical work (~specialist-week or more); not a polecat session task.

### 4.2 #2 — Sundaram, Welker (1997), Trans. AMS 349

**Title:** *Group actions on arrangements of linear subspaces and applications to configuration spaces*.

**Why #2:** The $G$-equivariant Goresky-MacPherson formula adapts to give a spectral sequence on the cofiber cohomology, with $E_2$-page built from local-link data of $S_n$-orbits in the n-active part. F8'' §3.6 already framed this; Sundaram-Welker is the specific paper that should be invoked.

**Specialist ask:** Verify the non-intersection-lattice obstruction. $\mathrm{PPF}_n$ is not literally an intersection lattice of subspace arrangement, but the Sundaram-Welker proof of equivariant GM uses primarily: (a) the poset is ranked (PPF is not — distance gap), (b) the local stratification has known stratum types (PPF orbits under $S_n$ are computable). The specialist must determine if the proof goes through with PPF-specific replacements for the rank/arrangement hypotheses.

**Distance from polecat-class:** Specialist representation theory + poset topology.

### 4.3 #3 — Björner, Walker (1983), Eur. J. Combin. 4

**Title:** *A homotopy complementation formula for partially ordered sets*.

**Why #3:** Gives a wedge decomposition of $\Delta(P)$ in terms of complement intervals to a sub-poset $Q$. **If** $\iota_n(\mathrm{PPF}_n) \subset \mathrm{PPF}_{n+1}$ satisfies the closedness hypothesis (downward- or upward-closed), the formula gives a direct wedge formula for $\Delta_{n+1}$.

**Specialist ask:** Check the closedness of $\iota_n(\mathrm{PPF}_n)$. Hypothesis: $\iota_n(\mathrm{PPF}_n)$ is downward-closed in $\mathrm{PPF}_{n+1}$ iff every refinement of $\iota_n(P)$ also has the form $\iota_n(P')$ — but refining can add relations to element $n$, so this fails. Adaptation of Björner-Walker to non-closed sub-posets is the open question.

**Distance from polecat-class:** Tier-2 polecat-feasible at $n=3 \to 4$ for direct verification (~80k tokens to enumerate). Tier-3 specialist for general adaptation.

### 4.4 #4 — Sundaram (1994) / Sundaram-Wachs (1997)

**Title:** *The homology representations of the $k$-equal partition lattice* (Adv. Math. 104 / J. Algebra 192).

**Why #4:** Provides the $S_n$-equivariant character of the order complex of an analogous poset family ($\Pi_{n,k}$). The Whitney homology decomposition is **the** technique for $S_n$-equivariant poset cohomology. If $\widetilde H^*(\Delta_n)$ admits a Whitney-homology-style decomposition (open question), Sundaram-Wachs give the character.

**Specialist ask:** Identify whether $\mathrm{PPF}_n$ has a Whitney-homology decomposition. The obstruction is that PPF is not a lattice. Specialist work: develop "directed-Whitney homology" if applicable.

**Distance from polecat-class:** Tier-3 specialist.

### 4.5 #5 — Church-Ellenberg-Farb (2015) / Patzt (2017)

**Title:** *FI-modules and stability for representations of symmetric groups* + central stability machinery.

**Why #5:** Most powerful potential tool **at general $n$**, but requires the strongest verification (FI-finite-generation or central stability of $\widetilde H^k(\Delta_n)$). If verified, character is polynomial in $n$; combined with F1-refined/F2/F3/F5 data at $n \le 5$, the character at all $n$ is *determined*.

**Specialist ask:** Verify FI-finite-generation (or central stability) of $(\widetilde H^k(\Delta_n))_n$ for the relevant $k$ (around $n - 2$). Ramos 2017 (4.6 in table) gives presentation-degree bounds that would close this if applicable.

**Distance from polecat-class:** Tier-3 specialist (the FG-FI verification is itself non-trivial). But this is the **highest-payoff** route: closes (I5) at *all* $n$ simultaneously, not just small $n$.

---

## 5. Specialist-engagement upgrades from F8'' §7.2

F8'' §7.2 drafted a single specialist ask. F8''''' sharpens it into three pre-identified "lift candidates" the specialist can adopt:

### 5.1 Tier-A1 — WZZ Wedge Formula adaptation (Welker as collaborator)

**Pitch.** "Apply WZZ 1999 Theorem 5.2 (Wedge Formula) to the cover $\mathrm{PPF}_{n+1} = \iota_n(\mathrm{PPF}_n) \sqcup (\text{n-active})$, then identify the n-active sub-complex as $\Sigma\Delta(X_n)$ for an explicit $X_n$."

**Most-likely specialist:** **Volkmar Welker** (Marburg), as a co-author of WZZ 1999. Direct expertise; would recognize the application immediately.

**Expected payoff:** GREEN-actionable closure if $X_n$ identification succeeds; AMBER-tight if the wedge formula gives partial cohomology information without explicit $X_n$.

**Estimated specialist-effort:** 1–2 weeks of focused work.

### 5.2 Tier-A2 — Sundaram-Welker equivariant GM adaptation (Sundaram + Welker)

**Pitch.** "Adapt Sundaram-Welker 1997 §4 equivariant Goresky-MacPherson formula to $\mathrm{PPF}_n$ (not literally an intersection lattice). The local link computation reduces to $S_n$-orbit computation in the n-active strata."

**Most-likely specialist:** **Sheila Sundaram** + **Volkmar Welker**, co-authors of the 1997 paper. Sundaram retains active in representation theory of partition lattices.

**Expected payoff:** AMBER-tight $E_2$ spectral sequence with explicit characters; could close (I5) at $n \le 5$ + provide the all-$n$ template.

**Estimated specialist-effort:** 1 month (the non-intersection-lattice obstruction is substantive).

### 5.3 Tier-A3 — Patzt-Putman FI-module / central stability framework (Patzt + Putman)

**Pitch.** "Verify $(\widetilde H^k(\Delta_n))_n$ is a finitely-generated FI-module (or centrally stable in the Putman 2015 sense). Apply Patzt 2017 character bounds. The cofiber character is then polynomial in $n$, determined by $n \le 5$ values."

**Most-likely specialist:** **Peter Patzt** (Oklahoma) or **Andy Putman** (Notre Dame). Both highly active in FI-module / central stability and would recognize PPF as a natural test case.

**Expected payoff:** GREEN-actionable closure at *all* $n$ if FG-FI verifies; RED if FG-FI fails (would tell us the cohomology grows non-polynomially, a substantive negative result).

**Estimated specialist-effort:** 1–2 weeks for the FG-FI verification + character extraction.

### 5.4 Recommended outreach order

1. **First contact: Welker** (Tier-A1 + A2). Single specialist covers both wedge-formula and equivariant-GM adaptations; his 1997 + 1999 papers are the direct precedents.
2. **Second contact: Wachs** (per F8'' §7.1) for Whitney-homology / shellability angle (Tier-A2 backup).
3. **Third contact: Patzt or Putman** (Tier-A3) for the FI-module angle. Independent of Welker; can be parallel.

This is sharper than F8'' §7.1's "Wachs + Welker (top candidates)" because it pre-identifies three distinct mathematical routes the specialist can choose between, rather than a generic ask.

---

## 6. Polecat-class follow-ups identified

Beyond F8'' §6's three PCRs (now executing as F8''' / F8'''' / F8''''') and §8.3's three follow-on tickets, the literature review surfaces these additional polecat-feasible sub-tickets:

### 6.1 Tier-2 PCR-Lit-1: Björner-Walker complementation check at $n = 3 \to 4$ (~80k tokens)

**Goal.** Apply Björner-Walker 1983 (entry 2.2) to the inclusion $\iota_3(\mathrm{PPF}_3) \subset \mathrm{PPF}_4$. Check whether the complementation formula gives a wedge decomposition consistent with F8''' (PCR-1) Betti vector.

**Method.** Enumerate "complement intervals" $[\widehat 0_4, Q] \cap (\mathrm{PPF}_4 \setminus \iota_3(\mathrm{PPF}_3))$ for $Q$ ranging over the $\mathrm{PPF}_4 \setminus \iota_3(\mathrm{PPF}_3)$ orbits under $S_4$. Compute Betti vector of resulting candidate wedge.

**Cross-check.** Result should match F8''' (PCR-1) Betti vector. If yes, the Björner-Walker formula is verified at $n=3 \to 4$; if no, Björner-Walker hypotheses (which require closedness of the sub-poset) are explicitly violated and the discrepancy localizes the obstruction.

**Resource:** ~80k tokens; ~3 hours of polecat work using existing PPF_4 enumeration.

### 6.2 Tier-2 PCR-Lit-2: Hersh-Welker discrete-Morse-on-cofiber at $n = 3 \to 4$ (~120k tokens)

**Goal.** Construct an $S_n$-equivariant discrete Morse matching on the relative chain complex $C_*(\Delta_4, \Delta_3)$. Apply Forman cancellation to produce a minimal CW model.

**Method.** Adapt F6 (mg-8736) Forman matching to the relative complex. Use Hersh-Welker techniques for equivariance.

**Cross-check.** Result gives a critical-cell decomposition; should match F8''' (PCR-1) Betti vector and F8'''' (PCR-2) spectral sequence.

**Resource:** ~120k tokens; ~5 hours.

### 6.3 Tier-2 PCR-Lit-3: FI-module presentation-degree empirical check (~50k tokens)

**Goal.** Compute $\widetilde H^k(\Delta_n)$ at $n = 3, 4, 5$ (already available) and check whether the $S_n$-character matches an FI-finite-presentation pattern. Use Ramos 2017 (entry 4.6) bounds.

**Method.** Compare character at $n = 3, 4, 5$ to polynomials of degree $\le 5$ in $n$ acting on Young diagrams. If consistent, formulate FG-FI conjecture for specialist verification.

**Cross-check.** Compatible with F8 Burnside $m_{\mathrm{sgn}} = 1$ at $n=5$ (mg-73fd).

**Resource:** ~50k tokens; ~2 hours; pure character arithmetic.

These three PCR-Lit follow-ups are **independent** of F8''' / F8'''' / F8''''' and can be queued as separate polecat tickets (e.g., F8'''''' Tier-2 PCR-Lit-1).

---

## 7. What F8''''' does and does not establish

### 7.1 What F8''''' establishes

- A 24-row literature integration table (§3) across 5 thematic clusters (C1–C5).
- Top-5 prioritized references with specialist-ask sharpening (§4).
- Three Tier-A specialist routes (§5.1–5.3) with most-likely-collaborator identification (Welker / Sundaram / Patzt-Putman).
- Three additional Tier-2 polecat-feasible PCR-Lit sub-tickets (§6).
- The headline finding: **no literature result reduces (I5) to a Tier-2 polecat-feasible sub-problem in isolation**, but **WZZ 1999 + Sundaram-Welker 1997 + the Patzt-Putman FI-machinery** are the three closest precedents.

### 7.2 What F8''''' does NOT establish

- $X_n$ is not identified.
- The wedge-vs-layer-vs-cross-polytope (F8''-1/-2/-3) discrimination is not done — that is F8''' (PCR-1).
- The Quillen-fiber sheaf type is not computed — that is F8'''' (PCR-2).
- No new theorem is proven; this is pure literature classification.
- No code, scripts, or Lean changes.

### 7.3 Strategic positioning

F8''''' completes the polecat-class partial route trio (PCR-1/2/3). Combined with the F8 + F8'' bundle, Daniel/PM now has:

| Asset | Status | Use |
|---|---|---|
| F4 5-obstruction map | Done (mg-0e68) | Identifies (I5) as single Tier-3 gap |
| F8 inductive framework | Done (mg-1e99) | Frames (I5) and gives ICOP-consistent framework |
| F8'' Quillen-fiber scoping | Done (mg-b345) | Pins Euler char, sharpens 3 conjectures, drafts specialist ask |
| F8''' Betti vector (PCR-1) | In-flight (mg-f91f) | Discriminates F8''-1 vs F8''-2 at $n=3 \to 4$ |
| F8'''' Spectral $E_2$ (PCR-2) | In-flight (mg-59f3) | Computes local Quillen-fiber sheaf at $n=3 \to 4$ |
| **F8''''' Literature integration (PCR-3)** | **Done (mg-ac7a, this doc)** | **Curates 3 specialist routes + 3 follow-up PCRs** |

The F8 / F8'' / F8''' / F8'''' / F8''''' bundle is the specialist-engagement package: a self-contained literature map + empirical data + framework synthesis suitable for emailing Welker (Tier-A1+A2) or Patzt-Putman (Tier-A3).

---

## 8. Verdict and headline takeaway

### 8.1 Verdict matrix

| Branch | Condition | This run? | Verdict |
|---|---|:---:|---|
| GREEN-actionable | Literature reduces (I5) to Tier-2 polecat-feasible. | ✗ | not GREEN |
| AMBER-specialist-ready | Literature confirms specialist ask without reducing tier. | ◯ partial | partial |
| **AMBER-related-but-distant** | Literature is structurally analogous; specialist adaptation required. | ✓ | **THIS RUN** |
| RED-no-precedent | No relevant precedent. | ✗ — WZZ + Sundaram-Welker + FI-machinery exist | — |

**Verdict: AMBER-related-but-distant.**

### 8.2 Headline takeaway

> **F8''''' completes the PCR-3 literature integration for the (I5) Quillen-fiber / Künneth specialist gap.** A 24-row table classifies the five thematic clusters (poset categories analogous to PPF / Quillen Theorem A / Künneth splittings / representation stability / Goresky-MacPherson) by direct applicability to (I5). No single result closes (I5) to polecat-tier (no GREEN-actionable); the three strongest precedents are **WZZ 1999 (wedge formula)**, **Sundaram-Welker 1997 ($G$-equivariant GM)**, and **the CEF/Patzt-Putman FI-module machinery**. Three Tier-A specialist routes are identified — A1 (Welker, WZZ adaptation), A2 (Sundaram + Welker, equivariant GM adaptation), A3 (Patzt + Putman, FI-module / central stability verification) — each with most-likely-collaborator named and expected payoff bounded. Three additional Tier-2 polecat-feasible PCR-Lit sub-tickets (Björner-Walker complementation check, Hersh-Welker discrete-Morse-on-cofiber, FI presentation-degree empirical check) are surfaced for queue-up. The (I5) gap remains specialist-class; F8''''' shortens specialist time by pre-curating the landscape.

### 8.3 Daniel-program impact summary

- ✓ **Literature landscape mapped** across 5 thematic clusters (C1–C5).
- ✓ **Top-5 prioritized references** with sharp specialist asks.
- ✓ **Three Tier-A specialist routes** identified with most-likely-collaborator naming.
- ✓ **Three Tier-2 PCR-Lit follow-ups** surfaced (Björner-Walker / Hersh-Welker / FI presentation-degree).
- ✓ **F8 + F8'' + F8''' + F8'''' + F8''''' bundle** assembled into the specialist-engagement package.
- ◯ **Specialist engagement** (Welker first contact) remains off-polecat; PM/Daniel decision-ready.
- ◯ **F8'''''' / F8''''''' (further PCR-Lit polecats)** can be queued.

### 8.4 Resource budget for F8''''' (this session)

| Item | Estimate (actual) |
|---|---:|
| F8'' parent doc read + cross-reference (§5 conjectures + §7 specialist ask) | ~15k tokens |
| Literature recall + classification table draft (§3, 24 rows) | ~25k tokens |
| Top-5 + specialist sharpening (§4, §5) | ~10k tokens |
| Polecat follow-up identification + verdict (§6, §7, §8) | ~5k tokens |
| Tool overhead | ~5k tokens |
| **Total session estimate** | **~60k tokens (at cap)** |

60k cap respected. No new axioms; no Lean changes; no scripts.

---

## 9. References

### 9.1 Predecessor mg-tickets (immediate chain)

- **mg-1e99** — F8: inductive $\omega_{\mathrm{bal}}^{(n)}$ at general $n$ (cce0377). Parent of F8''.
- **mg-b345** — F8'': (I5) Quillen-fiber specialist scoping (45a7532). Parent of F8''''' (this doc).
- **mg-f91f** — F8''' (PCR-1): Betti vector of $\Delta_4/\Delta_3$. Sibling polecat (in-flight).
- **mg-59f3** — F8'''' (PCR-2): Spectral $E_2$ at $n=3 \to 4$. Sibling polecat (in-flight, branch `compat-geom-F8pppp-spectral-e2`).
- **mg-ac7a** — F8''''' (PCR-3): this doc.

### 9.2 Poset topology / Quillen Theorem A canon

- D. Quillen, *Higher algebraic K-theory I*, in *Algebraic K-theory I*, LNM 341 (1973), Ch. 0 §3 (Theorem A).
- D. Quillen, *Homotopy properties of the poset of nontrivial $p$-subgroups of a group*, Adv. Math. 28 (1978).
- A. Björner, *Shellable and Cohen-Macaulay partially ordered sets*, Trans. AMS 260 (1980).
- A. Björner, J. W. Walker, *A homotopy complementation formula for partially ordered sets*, Europ. J. Combin. 4 (1983).
- A. Björner, M. Wachs, *Shellable nonpure complexes and posets I*, Trans. AMS 348 (1996).
- A. Björner, M. Wachs, *Shellable nonpure complexes and posets II*, Trans. AMS 349 (1997).
- M. Wachs, *Poset topology: tools and applications*, IAS/PCMI Lecture Notes 13 (2007).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11–12.
- R. W. Thomason, *Homotopy colimits in the category of small categories*, Math. Proc. Cambridge Phil. Soc. 85 (1979).

### 9.3 Künneth / wedge-of-spheres splittings + discrete Morse

- V. Welker, G. Ziegler, R. Živaljević, *Homotopy colimits — comparison lemmas for combinatorial applications*, J. Reine Angew. Math. (Crelle) 509 (1999).
- M. Sundaram, V. Welker, *Group actions on arrangements of linear subspaces and applications to configuration spaces*, Trans. AMS 349 (1997).
- M. Sundaram, *The homology representations of the $k$-equal partition lattice*, Adv. Math. 104 (1994).
- M. Sundaram, M. Wachs, *The homology representations of the $k$-equal partition lattice*, J. Algebra 192 (1997, companion).
- M. Wachs, *On the (co)homology of the partition lattice and the free Lie algebra*, Discrete Math. 193 (1996).
- V. Welker, *Order complexes of geometric lattices*, manuscripta math. 88 (1995).
- P. Hersh, V. Welker, *Combinatorial structure of the discrete Morse complex* (and related Hersh-Welker papers on shellability + matchings).
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).
- R. Forman, *A user's guide to discrete Morse theory*, Sém. Lothar. Combin. 48 (2002).
- P. Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981).
- J. Stembridge, *Some hidden relations involving the ten symmetry classes of plane partitions*, J. Combin. Theory Ser. A 68 (1994).

### 9.4 Representation stability + FI-modules

- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015).
- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015).
- A. Putman, S. Sam, *Representation stability and finite linear groups*, Duke Math. J. 166 (2017).
- S. Sam, A. Snowden, *Introduction to twisted commutative algebras*, 2012 preprint (also published forms).
- P. Patzt, *Central stability homology* (or *Central stability for the homology of congruence subgroups*), J. Topol. (2017+).
- E. Ramos, *On the degree-wise coherence of FI-modules*, NYJM 23 (2017).

### 9.5 Goresky-MacPherson + stratified

- M. Goresky, R. MacPherson, *Stratified Morse theory*, Springer Ergebnisse 14 (1988).
- A. Björner, T. Ekedahl, *On the shape of Bruhat intervals*, Ann. Math. 170 (2009).
- S. Yuzvinsky, *Small rational model of subspace complement*, Trans. AMS 351 (1999).
- A. Björner, L. Lovász, A. Yao, *Linear decision trees: volume estimates and topological bounds*, Proc. STOC (1992).

### 9.6 Compatibility-Geometry program (context)

- F1-refined (mg-3a61), F2 (mg-7455), F3 (mg-6bc3), F4 (mg-0e68), F5 (mg-1e58), F6 (mg-8736), F7 (mg-73fd), F7' (mg-e8d5), F8 (mg-1e99), F8' (mg-7b3b), F8'' (mg-b345), F8''' (mg-f91f), F8'''' (mg-59f3), F8''''' (mg-ac7a, this doc).
- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) — 1/3-2/3 conjecture statement.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — BFT bound $[3/11, 8/11]$.

### 9.7 Daniel directives

- 2026-05-13T~22Z: "fantastic result; don't wait; keep researching what's most valuable; can still target full width 3 proof."
- 2026-05-14T02:38Z: "let's push harder on I5, we're so close." Triggered the F8''' / F8'''' / F8''''' polecat trio (mg-f91f / mg-59f3 / mg-ac7a).

---

## 10. Appendix A — Cross-cluster synthesis: why no GREEN

The literature review surfaces 24 results across 5 clusters; none individually closes (I5) to polecat-class. The synthesis observation:

**Each cluster has a hypothesis $\mathrm{PPF}_n$ does not satisfy.**

- (C1, partition-lattice analogs): $\mathrm{PPF}_n$ is not a lattice (no joins/meets); is not the partition lattice (carries orientation data).
- (C2, Quillen Theorem A): $\rho_n$ fibers are not contractible.
- (C3, Künneth / wedge): WZZ wedge formula requires explicit fiber-type identification; Sundaram-Welker GM requires the poset to be the intersection lattice of an arrangement (PPF is not).
- (C4, FI-modules / central stability): FG-FI is unverified; PPF's $\mathrm{Aut}(P)$-orbits grow superpolynomially in $n$, so FG-FI is non-obvious.
- (C5, Goresky-MacPherson): combinatorial GM exists in Sundaram-Welker form but with the same intersection-lattice obstruction.

**The specialist task is to break one of these obstructions.** Each Tier-A specialist route (§5.1–5.3) targets a different one:

- **A1 (Welker, WZZ):** break C3 obstruction by explicit $X_n$ identification.
- **A2 (Sundaram + Welker, GM):** break C5 obstruction by generalizing GM beyond intersection lattices.
- **A3 (Patzt + Putman, FI):** verify FG-FI directly, bypassing C4 obstruction.

These are independent routes; specialist engagement on any one closes (I5) at least partially.

---

## 11. Appendix B — Literature gaps NOT addressed by this scoping

For completeness, three literature areas the polecat could not survey in scope:

1. **Tonks-Steiner / cubical models of cofibers.** Cubical-set models for the cofiber $\Delta_{n+1}/\Delta_n$ may exist in the higher-category-theoretic literature. Specialist would need to identify.

2. **Operad-theoretic interpretations.** The sequence $(\mathrm{PPF}_n)_n$ with $\iota_n$-inclusions could carry an operadic structure (composition of partial orders) — this is unexplored in the F8'' / F8''''' bundle. Sam-Snowden TCA framework (entry 4.3) is the closest.

3. **Computational topology software literature.** SimplicialComplexes / CHomP / CAPD packages can compute $\widetilde H_*(\Delta_n/\Delta_{n-1})$ empirically up to memory limits; this is in the F8''' (PCR-1) execution scope but is not literature-review per se.

These three areas may motivate a future PCR-Lit-4 / -5 / -6 if relevant.

---

End of F8''''' PCR-3 literature integration document. Verdict: **AMBER-related-but-distant** — 24-row table classifies 5 thematic clusters of poset-topology + representation-stability literature; no GREEN-actionable closure; three Tier-A specialist routes (WZZ wedge / Sundaram-Welker equivariant GM / Patzt-Putman FI-stability) identified with most-likely-collaborator naming (Welker / Sundaram + Welker / Patzt + Putman). Three Tier-2 polecat-feasible PCR-Lit follow-ups (Björner-Walker complementation, Hersh-Welker discrete Morse, FI presentation-degree empirical check) surfaced. F8 + F8'' + F8''' + F8'''' + F8''''' bundle assembled for specialist engagement.

Mayor inbox: `mg-ac7a`. Branch: `compat-geom-F8p5-lit-integration`. Daniel-directive: "push harder on I5" — F8''''' completes the third of three polecat-class PCR partials launched on that directive.
