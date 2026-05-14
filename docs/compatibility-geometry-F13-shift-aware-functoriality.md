# Compat-Geom — F13 (E1): Functoriality of the degree-shift-aware cofiber-cohomology object (mg-ecf6)

**Branch:** `compat-geom-F13-E1-functoriality` (new).
**Parent:** mg-b352 (F11, GREEN-route-traction, `11a75d6`) — `docs/state-F11.md` §4.2–§4.3 (the $\partial_n$ identification + sketch), §4.6 (entry sub-problem (E1)), §6.2 follow-up A (the do-first recommendation).
**Grandparent:** mg-8216 (F10, GREEN-conditional, `3c173df`) — `docs/general-n-proof-synthesis.md` §7.2 (the (FG-Cofiber) sharpening, the degree-shift-aware framework question).
**Type:** Paper-and-pencil structural homological algebra. LaTeX-style Markdown; **no new axioms; no Lean changes; no new computation / no HPC**. Polecat-class. Multi-session-able; cumulative state ledger in `docs/state-F13.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: GREEN-functoriality-established.** The triple $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$ is rigorously a module over a precisely-defined degree-shift-aware functor category $\mathcal{C}$. All four caveats F11 §4.3 flagged honestly are closed:

1. **Choice-independence (§3).** The cofiber relabelling $V(f)^*$ is canonical: the extension $f \rightsquigarrow \hat f \rightsquigarrow \tilde f$ used to define it is **uniquely determined** by $f$ — it is the unique extension inducing a non-degenerate map on cofiber cohomology (Lemma 3.3), and every other extension induces the zero map. There is no actual choice; "choice-independence" is resolved as *canonicity*.
2. **Full functoriality across all injections (§4).** For every injection $f:[m]\hookrightarrow[n]$ — not only the standard inclusion — $V(\hat f)^*$ is functorial on cofiber cohomology (Prop. 4.4: each fixed-degree $H^k$ is a genuine co-FI-module), and the F11 §4.3 commuting square holds for every $f$ (Thm. 5.3: $\partial$ is an FI-natural transformation $H^k \Rightarrow \Sigma^\ast H^{k+1}$).
3. **$\partial$-composite compatibility / coherence (§6).** $\partial$-composites are unconstrained associative composites; the iterated naturality squares cohere automatically from functoriality of the canonical extension; no relation among the $\partial_n$ is imposed or needed (Prop. 6.1–6.2). The combined structure is coherent.
4. **The precise functor category (§7).** $\mathcal{C}$ is $\mathrm{FI}^{\mathrm{op}}$ "with a compatible degree-$(+1)$ shift", made precise two ways — by generators-and-relations (Def. 7.1) and intrinsically as graded co-FI-modules equipped with an FI-natural map $H^k \Rightarrow \Sigma^\ast H^{k+1}$ (Thm. 7.4). "Finitely generated" for the diagonal $(B_n)_n$ is defined (Def. 7.6), and the F11 §4.4 reduction ("$\partial_n$ iso for all $n$") is recovered as: the diagonal is finitely generated in generation degree $\le 3$ with the $\partial_n$ as the only structure maps (Cor. 7.7).

No RED, no AMBER: the structure **coheres**, by standard naturality of the triple long exact sequence plus the FI-functoriality of the relabelling — exactly as F11 anticipated. Route (ii)'s **framework half is closed**. The remaining content of route (ii) is the *finiteness* half — concretely "$\partial_n$ is an isomorphism for all $n$" — which is genuinely open and belongs to (E2) / PCR-Lit-2′, out of E1's scope (§8).

---

## §0. What E1 is, and is not

F11 (`11a75d6`) reduced route (ii) of (FG-Cofiber) to two entry sub-problems (F11 §4.6): **(E1)** the rigorous functoriality writeup for the degree-shift-aware cofiber-cohomology object, and **(E2)** the computation of $\partial_3$. F11 §6.2 named (E1) "the single most polecat-tractable entry sub-problem... the prerequisite for everything else in route (ii)" and the recommended do-first follow-up. This document is (E1).

**(E1) is** the rigorous proof — paper-and-pencil structural homological algebra — that the data F11 §4.2–§4.3 *sketched* assembles into a genuine algebraic object: a module over a degree-shift-aware functor category. F11 §4.3 flagged, honestly, four points that "still need a careful written proof": choice-independence of the cofiber relabelling, full functoriality across *all* injections (not just the standard inclusion $\iota_n$), $\partial$-composite compatibility, and the precise identification of the functor category with its notion of "finitely generated". E1 closes all four.

**(E1) is not** a proof that the object is *finitely generated* — that is the finiteness half of route (ii), reduced by F11 §4.4 to "$\partial_n$ is an isomorphism for all $n$", which requires the $n=4\to5$ cofiber Betti vector (PCR-Lit-2′) and the $\partial_3$ computation (E2). E1 sets up the category in which "finitely generated" is even a well-posed question, and states the definition (§7.6); it does not answer it. Per the F11 constraints inherited by this ticket: **no new axioms, no Lean changes, no new computation, no new $n$-datapoint.** Everything here is naturality of the triple long exact sequence and the functoriality of the FI-relabelling — both standard, neither requiring computation.

**Notation** (from F10 §1.1 / M2 §1 / F11 §0). $[n] = \{0,\dots,n-1\}$. $\mathrm{PPF}_n$ is the poset (ordered by refinement, $P \le Q \iff P \subseteq Q$ as relations) of proper partial orders on $[n]$ — non-empty relation, non-total; $|\mathrm{PPF}_n| = 12,194,4110,129302$ at $n=3,4,5,6$, and $\mathrm{PPF}_n = \varnothing$ for $n \le 2$. $\Delta_n := \Delta(\mathrm{PPF}_n)$ is its order complex. $\iota_n : \mathrm{PPF}_n \hookrightarrow \mathrm{PPF}_{n+1}$ is the standard inclusion: $P$ on $[n]$ goes to the same relation viewed on $[n+1]$, with $n$ incomparable to all of $[n]$. For an injection $f:[m]\hookrightarrow[n]$, $V(f):\mathrm{PPF}_m\to\mathrm{PPF}_n$ is the FI-relabelling (Def. 1.2). $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is the cofiber-cohomology diagonal; $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ is proven (mg-6295/mg-59f3). All (co)homology is reduced, with $\mathbb{Q}$-coefficients.

---

## §1. Setup: the relabelling functor, the standard tower, and the cofiber

### 1.1 The order complexes form an FI-object

We first record, in usable form, the FI-structure that M2 §4 verified computationally.

**Definition 1.1 (FI).** $\mathrm{FI}$ is the category of finite sets $[n]$ ($n \ge 0$) and injections. We write $\mathrm{FI}(m,n)$ for the set of injections $[m]\hookrightarrow[n]$; it is empty unless $m \le n$. $\mathrm{Aut}_{\mathrm{FI}}([n]) = S_n$.

**Definition 1.2 (the relabelling $V(f)$).** For $f \in \mathrm{FI}(m,n)$ and $P \in \mathrm{PPF}_m$, define $V(f)(P) \in \mathrm{PPF}_n$ to be the partial order on $[n]$ whose strict relation is
$$
  V(f)(P) \;=\; \bigl\{\,(f(a),f(b)) : (a,b) \in P\,\bigr\},
$$
i.e. $P$ relabelled along $f$, with the $n-m$ points of $[n]\setminus\mathrm{im}(f)$ adjoined as isolated elements.

**Lemma 1.3 ($V$ is a well-defined FI-functor to posets).** For every $f\in\mathrm{FI}(m,n)$, $V(f)$ is a well-defined order-preserving map $\mathrm{PPF}_m\to\mathrm{PPF}_n$; moreover $V(\mathrm{id}_{[n]})=\mathrm{id}$ and $V(g\circ f)=V(g)\circ V(f)$. Hence $n\mapsto\mathrm{PPF}_n$, $f\mapsto V(f)$ is a functor $\mathrm{FI}\to\mathbf{Poset}$, and $n\mapsto\Delta_n$, $f\mapsto\Delta(V(f))$ a functor $\mathrm{FI}\to\mathbf{SimpCplx}$.

*Proof.* **Well-defined into $\mathrm{PPF}_n$.** Relabelling along an injection carries a strict partial order to a strict partial order (irreflexivity and transitivity are preserved because $f$ is injective). The relation $V(f)(P)$ is non-empty iff $P$ is (relabelling is a bijection on the relation set). It is non-total: if $n>m$ there is an isolated point, hence an incomparable pair; if $n=m$ then $f$ is a bijection and totality is preserved/reflected, so non-total $P$ gives non-total $V(f)(P)$. Thus $V(f)(P)\in\mathrm{PPF}_n$. **Order-preserving.** If $P\subseteq Q$ in $\mathrm{PPF}_m$ then $V(f)(P)\subseteq V(f)(Q)$, since relabelling is monotone for inclusion of relations and the adjoined isolated set $[n]\setminus\mathrm{im}(f)$ is the same for both. **Functoriality.** $V(\mathrm{id})$ relabels along the identity and adjoins nothing, so $V(\mathrm{id})=\mathrm{id}$. For $f\in\mathrm{FI}(m,n)$, $g\in\mathrm{FI}(n,p)$: relabelling along $f$ then along $g$ relabels along $g\circ f$; the isolated set produced is $g\bigl([n]\setminus\mathrm{im}(f)\bigr)\cup\bigl([p]\setminus\mathrm{im}(g)\bigr) = [p]\setminus g(\mathrm{im}(f)) = [p]\setminus\mathrm{im}(g\circ f)$, which is exactly the isolated set of $V(g\circ f)$. So $V(g)\circ V(f)=V(g\circ f)$. An order-preserving poset map induces a simplicial map of order complexes, functorially. $\square$

Consequently, for each fixed cohomological degree $k$, $n\mapsto\widetilde H^k(\Delta_n)$ with $f\mapsto V(f)^\ast$ is a contravariant functor $\mathrm{FI}\to\mathbf{Vect}_{\mathbb{Q}}$ — a **co-FI-module** (equivalently, an $\mathrm{FI}^{\mathrm{op}}$-module). This is the degree-preserving structure of F10 §7.2.a / M2 §4. The computational cross-check of Lemma 1.3 over all injections at $m,n\le 5$ is mg-759d §4 (M2 trip-wire (c), PASS); the proof above makes it $n$-uniform and structural.

### 1.2 The standard tower and its subcomplex inclusions

Write $s_n := (\text{the inclusion } [n]\hookrightarrow[n+1]) \in\mathrm{FI}(n,n+1)$, the identity on $[n]$. Then $\iota_n = V(s_n)$.

**Lemma 1.4 ($\Delta_n$ is an order ideal in $\Delta_{n+1}$).** $\iota_n(\mathrm{PPF}_n)$ is exactly the set of $Q\in\mathrm{PPF}_{n+1}$ in which the point $n$ is isolated, and this set is a **downward-closed** subposet (order ideal) of $\mathrm{PPF}_{n+1}$. Hence $\Delta_n$ is a subcomplex of $\Delta_{n+1}$ — in fact the order complex of an order ideal, so the pair $(\Delta_{n+1},\Delta_n)$ is a simplicial (CW) pair, in particular a *good pair*.

*Proof.* $V(s_n)(P)$ adjoins exactly the point $n$ as isolated, so $\iota_n(\mathrm{PPF}_n) = \{Q : n \text{ isolated in } Q\}$. If $Q'\subseteq Q$ with $n$ isolated in $Q$, then $n$ is isolated in $Q'$ (a sub-relation has no more comparabilities). So $\iota_n(\mathrm{PPF}_n)$ is downward closed. The order complex of a subposet that is an induced subposet is a subcomplex; downward-closedness is the input the M1 mechanism uses (mg-6295 §6.1's downward-closed-subcomplex lemma) but for E1 we need only that $\Delta_n\subseteq\Delta_{n+1}$ is a subcomplex inclusion, hence a cofibration and the pair is good. $\square$

Iterating: $\Delta_n\subseteq\Delta_{n+1}\subseteq\Delta_{n+2}\subseteq\cdots$ is a tower of subcomplex inclusions. For the triple $(\Delta_n\subseteq\Delta_{n+1}\subseteq\Delta_{n+2})$ we note $\Delta_n = V(s_{n+1}\circ s_n)(\mathrm{PPF}_n)$ is the set of $Q\in\mathrm{PPF}_{n+2}$ with both $n$ and $n+1$ isolated — again an order ideal, contained in the order ideal $\Delta_{n+1} = \{n+1 \text{ isolated}\}$.

### 1.3 The cofiber and the object of study

For a good pair $A\subseteq X$ of simplicial complexes, $\widetilde H^k(X/A)\cong H^k(X,A)$ canonically, and we compute everything with the **relative simplicial cochain complex** $C^\bullet(X,A) := \{\varphi\in C^\bullet(X):\varphi|_A = 0\} = \ker\bigl(C^\bullet(X)\twoheadrightarrow C^\bullet(A)\bigr)$ — the cochains vanishing on the subcomplex, a purely algebraic object, free of basepoint choices. We henceforth write
$$
  H^k_n \;:=\; \widetilde H^k(\Delta_{n+1}/\Delta_n) \;=\; H^k\bigl(C^\bullet(\Delta_{n+1},\Delta_n)\bigr),
\qquad
  B_n \;:=\; H^{n-1}_n .
$$
$B_n$ is the cofiber-cohomology **diagonal**, the object (FG-Cofiber) is about (F10 §7.2, F11 §4.2). $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ is proven (mg-6295 §5, mg-59f3 §3.4); (UCC.1) conjectures $B_n = 2\cdot\mathrm{sgn}_{S_n}$, concentrated in degree $n-1$, for all $n\ge 3$.

**Standing scope.** We set up the framework for $n\ge 3$ (so $\Delta_n\ne\varnothing$ and $B_3$ is the proven base). Nothing below requires concentration: we work with $H^k_n$ for *all* $k$, precisely because (UCC.1)'s concentration claim is the thing route (ii) aims to *prove*, and may not be assumed in the functoriality setup. This is the discipline F11 §4.4's parenthetical demanded.

---

## §2. The triple long exact sequence and the connecting map $\partial_n$

We recall the homological algebra E1 builds on; it is standard, stated here to fix variance and signs.

**The relative cochain SES of a triple.** Let $A\subseteq B\subseteq C$ be subcomplexes. With the convention $C^\bullet(X,Y) = \{\varphi\in C^\bullet(X):\varphi|_Y=0\}$ of §1.3, the relative simplicial cochain complexes sit in a short exact sequence of cochain complexes
$$
  0 \;\longrightarrow\; C^\bullet(C,B) \;\xrightarrow{\;j\;}\; C^\bullet(C,A) \;\xrightarrow{\;r\;}\; C^\bullet(B,A) \;\longrightarrow\; 0. \tag{2.1}
$$
Here $j$ is the inclusion: a cochain on $C$ vanishing on $B$ also vanishes on $A\subseteq B$, so $C^\bullet(C,B)\subseteq C^\bullet(C,A)$. The map $r$ is restriction $\varphi\mapsto\varphi|_B$: if $\varphi|_A=0$ then $\varphi|_B$ vanishes on $A$, so $r$ lands in $C^\bullet(B,A)$; it is surjective because a cochain on $B$ vanishing on $A$ extends to $C$ by zero on simplices outside $B$. Finally $\ker(r) = \{\varphi\in C^\bullet(C):\varphi|_A=0,\ \varphi|_B=0\} = C^\bullet(C,B) = \operatorname{im}(j)$. So (2.1) is exact.

**The triple LES.** The long exact cohomology sequence of (2.1) is the **triple long exact sequence**
$$
  \cdots \to \widetilde H^k(C/B) \xrightarrow{\,j^\ast\,} \widetilde H^k(C/A) \xrightarrow{\,r^\ast\,} \widetilde H^k(B/A) \xrightarrow{\;\partial\;} \widetilde H^{k+1}(C/B) \to \cdots \tag{2.2}
$$
with $\partial$ the connecting homomorphism of (2.1), raising cohomological degree by $+1$.

**Definition 2.1 ($\partial_n$).** Apply (2.2) to the triple $(A,B,C) = (\Delta_n,\Delta_{n+1},\Delta_{n+2})$ and take $k = n-1$:
$$
  \partial_n \;:\; B_n \;=\; \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n) \;\longrightarrow\; \widetilde H^{n}(\Delta_{n+2}/\Delta_{n+1}) \;=\; B_{n+1}.
$$
This is the degree-shift-$(+1)$ transition map F11 §4.2 identified. More generally, for every $k$ we have the connecting map of the triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$,
$$
  \partial_n^k \;:\; H^k_n \;=\;\widetilde H^k(\Delta_{n+1}/\Delta_n)\;\longrightarrow\;\widetilde H^{k+1}(\Delta_{n+2}/\Delta_{n+1})\;=\;H^{k+1}_{n+1},
$$
and $\partial_n = \partial_n^{\,n-1}$.

Two remarks fix the object precisely.

- **$\partial_n$ is the triple map, not the pair map.** F10 §6.2 uses $\delta_n$, the connecting map of the *pair* $(\Delta_{n+1},\Delta_n)$, of type $\widetilde H^k(\Delta_n)\to\widetilde H^{k+1}(\Delta_{n+1}/\Delta_n)$. $\partial_n$ is the connecting map of the *triple of cofibers*, of type $H^k_n\to H^{k+1}_{n+1}$. They are different maps with different domains; (UCC.2) is about $\delta_n$, the present document is about $\partial_n$ (cf. F11 §4.4 parenthetical). E1 does not relate them.
- **$\partial_n$ is genuinely open content.** From (2.2), $\partial_n$ injective $\iff r^\ast:\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)\to\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is zero, and $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)$ — the cohomology of a *double* cofiber — is not known a priori (F11 §4.4). Setting up functoriality (E1) does not assume anything about whether $\partial_n$ is injective/iso.

---

## §3. Item 1 — Choice-independence: the canonical extension is unique

F11 §4.3's caveat: "$V(\tilde f)^\ast$ on cofiber cohomology [must be shown] independent of the extension $\hat f\rightsquigarrow\tilde f$." We resolve this completely. The resolution is not "all extensions agree" — they do not — but **canonicity**: among all extensions, exactly one is non-degenerate, it is uniquely characterised, and the structure maps are *defined* to use it. So there is no choice to be independent of.

### 3.1 The hat (shift) operation

**Definition 3.1 (canonical extension / hat).** For $f\in\mathrm{FI}(m,n)$, define $\hat f\in\mathrm{FI}(m+1,n+1)$ by
$$
  \hat f|_{[m]} = f, \qquad \hat f(m) = n.
$$
This is the **standard FI-shift** of $f$: it sends the new point to the new point. Set $\tilde f := \widehat{\hat f}\in\mathrm{FI}(m+2,n+2)$, so $\tilde f|_{[m]}=f$, $\tilde f(m)=n$, $\tilde f(m+1)=n+1$.

**Lemma 3.2 (hat is a functor; $s$ is natural).** $\widehat{\mathrm{id}_{[m]}} = \mathrm{id}_{[m+1]}$ and $\widehat{g\circ f} = \hat g\circ\hat f$ for all composable $f,g$. Hence $\Sigma:\mathrm{FI}\to\mathrm{FI}$, $[n]\mapsto[n+1]$, $f\mapsto\hat f$, is a functor (the **FI-shift functor**), and the standard inclusions assemble into a natural transformation $s:\mathrm{Id}_{\mathrm{FI}}\Rightarrow\Sigma$.

*Proof.* $\widehat{\mathrm{id}}$ fixes $[m]$ and sends $m\mapsto m$, so it is $\mathrm{id}_{[m+1]}$. For $f\in\mathrm{FI}(m,n)$, $g\in\mathrm{FI}(n,p)$: on $[m]$, $(\hat g\circ\hat f)|_{[m]} = \hat g\circ f = g\circ f$ (as $f$ lands in $[n]$, where $\hat g = g$); and $(\hat g\circ\hat f)(m) = \hat g(\hat f(m)) = \hat g(n) = p$. So $\hat g\circ\hat f$ extends $g\circ f$ and sends $m\mapsto p$, i.e. equals $\widehat{g\circ f}$. Naturality of $s$: $\hat f\circ s_m = s_n\circ f$, since both send $a\in[m]$ to $f(a)\in[n]\subseteq[n+1]$. $\square$

In particular $\tilde f = \widehat{\hat f}$ is just $\Sigma^2 f$, and $\widetilde{g\circ f} = \tilde g\circ\tilde f$.

### 3.2 Uniqueness of the non-degenerate extension

**Lemma 3.3 (Maps of pairs; canonicity).** Let $f\in\mathrm{FI}(m,n)$ and let $g\in\mathrm{FI}(m+1,n+1)$ be *any* extension of $f$ (i.e. $g|_{[m]}=f$). Then:

1. $V(g)$ always restricts to a map of pairs $V(g):(\Delta_{m+1},\Delta_m)\to(\Delta_{n+1},\Delta_n)$.
2. If $g(m)\ne n$, then $V(g)$ sends *all* of $\Delta_{m+1}$ into $\Delta_n$; the induced map $V(g)^\ast:\widetilde H^\bullet(\Delta_{n+1}/\Delta_n)\to\widetilde H^\bullet(\Delta_{m+1}/\Delta_m)$ is **zero**.
3. If $g(m)=n$, then $g=\hat f$ — the canonical extension is the *unique* extension with $g(m)=n$.

Thus $\hat f$ is the unique extension of $f$ that can induce a non-zero map on cofiber cohomology, and it is determined by $f$ alone.

*Proof.* Recall $\Delta_m = \{P\in\mathrm{PPF}_{m+1}: m\text{ isolated}\}$ and $\Delta_n=\{Q\in\mathrm{PPF}_{n+1}:n\text{ isolated}\}$ (Lemma 1.4). For $P\in\mathrm{PPF}_{m+1}$, the isolated points of $V(g)(P)$ are $g(\{\text{isolated points of }P\})\cup([n+1]\setminus\mathrm{im}(g))$.

(1)+(2): Suppose $g(m)\ne n$. Since $f=g|_{[m]}$ maps into $[n]$ and $g(m)\ne n$, we have $n\notin\mathrm{im}(g)$. Then $n\in[n+1]\setminus\mathrm{im}(g)$ is isolated in $V(g)(P)$ for **every** $P\in\mathrm{PPF}_{m+1}$, so $V(g)(\mathrm{PPF}_{m+1})\subseteq\Delta_n$. In particular $V(g)$ maps $\Delta_m\to\Delta_n$ (a map of pairs) and factors as $\Delta_{m+1}\xrightarrow{V(g)}\Delta_n\hookrightarrow\Delta_{n+1}$. On relative cochains, $V(g)^\#$ factors through $C^\bullet(\Delta_n,\Delta_n)=0$, so $V(g)^\ast=0$ on $H^\bullet(\Delta_{n+1},\Delta_n)$.

(1)+(3): Suppose $g(m)=n$. For $P\in\Delta_m$ ($m$ isolated in $P$), $g(m)=n$ is isolated in $V(g)(P)$, so $V(g)(P)\in\Delta_n$: a map of pairs. Uniqueness: an extension $g$ of $f$ with $g(m)=n$ has all values prescribed ($g|_{[m]}=f$, $g(m)=n$), so $g=\hat f$.

Cases $g(m)=n$ and $g(m)\ne n$ are exhaustive and exclusive, proving the final claim. $\square$

**Remark 3.4 (this *is* choice-independence).** F11 §4.3 worried that $V(\tilde f)^\ast$ might depend on auxiliary choices in the extension. Lemma 3.3 shows the worry dissolves: the requirement "induce a (possibly) non-zero map on cofibers" pins the extension *uniquely* to $\hat f$. The degenerate extensions ($g(m)\ne n$) are not subtly-different competitors — they all induce the **same** map, namely $0$. So the cofiber relabelling is, unambiguously, a function of $f$:
$$
  V_{B}(f)^\ast \;:=\; V(\hat f)^\ast \;:\; H^k_n \longrightarrow H^k_m \qquad(f\in\mathrm{FI}(m,n)),
$$
with no choice involved. The triple version $V(\tilde f)^\ast$ is likewise canonical: applying Lemma 3.3 to $\hat f$ in place of $f$, $\tilde f=\widehat{\hat f}$ is the unique non-degenerate extension of $\hat f$, hence $V(\tilde f)$ is the unique non-degenerate map of pairs $(\Delta_{m+2},\Delta_{m+1})\to(\Delta_{n+2},\Delta_{n+1})$ extending $V(\hat f)$. Item 1 is closed.

**Lemma 3.5 ($V(\tilde f)$ is a map of triples).** For every $f\in\mathrm{FI}(m,n)$, $V(\tilde f)$ restricts to a map of triples
$$
  V(\tilde f):(\Delta_m\subseteq\Delta_{m+1}\subseteq\Delta_{m+2})\longrightarrow(\Delta_n\subseteq\Delta_{n+1}\subseteq\Delta_{n+2}).
$$

*Proof.* $\tilde f=\widehat{\hat f}$ is the canonical extension of $\hat f$, so by Lemma 3.3(3) applied to $\hat f$, $V(\tilde f)$ maps the pair $(\Delta_{m+2},\Delta_{m+1})\to(\Delta_{n+2},\Delta_{n+1})$. Also $\tilde f|_{[m+1]}=\hat f$, so $V(\tilde f)$ restricted to $\Delta_{m+1}$ equals $V(\hat f)$, which by Lemma 3.3(3) (applied to $f$) maps $(\Delta_{m+1},\Delta_m)\to(\Delta_{n+1},\Delta_n)$. The three inclusions are respected: $V(\tilde f)(\Delta_m)\subseteq\Delta_n$, $V(\tilde f)(\Delta_{m+1})\subseteq\Delta_{n+1}$, $V(\tilde f)(\Delta_{m+2})\subseteq\Delta_{n+2}$. $\square$

---

## §4. Item 2a — The fixed-degree cofiber co-FI-modules

We now show the *degree-preserving* half of the structure: for each fixed $k$, the family $(H^k_n)_n$ is a genuine co-FI-module, functorially in *all* injections. F11 §4.3 expected the fixed-degree co-FI-structure (F10 §7.2.b / M2 §4) to "presumably already handle the degree-preserving half"; here it is, made rigorous and $n$-uniform.

### 4.1 The shift of an FI-object

The standard inclusions $s:\mathrm{Id}\Rightarrow\Sigma$ (Lemma 3.2) make the tower $(\Delta_n)_n\hookrightarrow(\Delta_{n+1})_n$ a morphism of FI-objects. Precisely:

**Definition 4.1.** For an FI-object $X:\mathrm{FI}\to\mathcal{D}$, its **shift** is $\Sigma X := X\circ\Sigma$, with $(\Sigma X)_n = X_{n+1}$ and $f\in\mathrm{FI}(m,n)$ acting by $X(\hat f)$. For a co-FI-module $M:\mathrm{FI}^{\mathrm{op}}\to\mathbf{Vect}$, the shift $\Sigma^\ast M := M\circ\Sigma^{\mathrm{op}}$ has $(\Sigma^\ast M)_n = M_{n+1}$, $f$ acting by $M(\hat f)$.

**Lemma 4.2.** The assignment $n\mapsto\mathrm{PPF}_{n+1}$, $f\mapsto V(\hat f)$ is the FI-object $\Sigma\,\mathrm{PPF}$; the standard inclusions $\iota_n$ assemble into a morphism of FI-objects $\iota:\mathrm{PPF}\hookrightarrow\Sigma\,\mathrm{PPF}$, levelwise an order-ideal inclusion.

*Proof.* That $n\mapsto\mathrm{PPF}_{n+1}$, $f\mapsto V(\hat f)$ is a functor is Lemma 1.3 precomposed with the functor $\Sigma$ (Lemma 3.2). Naturality of $\iota$: for $f\in\mathrm{FI}(m,n)$ we need $V(\hat f)\circ\iota_m = \iota_n\circ V(f)$, i.e. $V(\hat f)\circ V(s_m) = V(s_n)\circ V(f)$; by Lemma 1.3 this is $V(\hat f\circ s_m) = V(s_n\circ f)$, which holds because $\hat f\circ s_m = s_n\circ f$ (naturality of $s$, Lemma 3.2). Each $\iota_n$ is an order-ideal inclusion by Lemma 1.4. $\square$

So the pair $(\Delta_{n+1},\Delta_n)$ is the pair $\bigl(\Delta(\Sigma\,\mathrm{PPF})_n,\,\Delta(\mathrm{PPF})_n\bigr)$, **natural in $n\in\mathrm{FI}$**: an injection $f$ acts on it by the map of pairs $V(\hat f)$.

### 4.2 $H^k$ is a co-FI-module

**Proposition 4.3 ($V$ acts functorially on pairs).** For every $f\in\mathrm{FI}(m,n)$, $V(\hat f)$ is a map of pairs $(\Delta_{m+1},\Delta_m)\to(\Delta_{n+1},\Delta_n)$ (Lemma 3.3(3)), and
$$
  \widehat{\mathrm{id}_{[n]}} = \mathrm{id}_{[n+1]}, \qquad \widehat{g\circ f} = \hat g\circ\hat f
$$
imply $V(\widehat{\mathrm{id}}) = \mathrm{id}$ and $V(\widehat{g\circ f}) = V(\hat g)\circ V(\hat f)$ as maps of pairs.

*Proof.* Immediate from Lemma 3.2 and Lemma 1.3. $\square$

**Proposition 4.4 (the fixed-degree cofiber co-FI-module).** Fix $k\in\mathbb{Z}$. Then
$$
  H^k:\;\mathrm{FI}^{\mathrm{op}}\to\mathbf{Vect}_{\mathbb{Q}},\qquad H^k_n = \widetilde H^k(\Delta_{n+1}/\Delta_n),\qquad H^k(f) = V(\hat f)^\ast
$$
is a well-defined co-FI-module. Equivalently, $H^k$ is the $k$-th relative cohomology of the FI-pair $\iota:\mathrm{PPF}\hookrightarrow\Sigma\,\mathrm{PPF}$.

*Proof.* A map of pairs induces, contravariantly, a map on relative cochain complexes and hence on relative cohomology; this is functorial. By Prop. 4.3 the assignment $f\mapsto V(\hat f)$ is functorial into the category of pairs $(\Delta_{m+1},\Delta_m)$, so $f\mapsto V(\hat f)^\ast$ is a contravariant functor $\mathrm{FI}\to\mathbf{Vect}$: $V(\widehat{\mathrm{id}})^\ast = \mathrm{id}$ and $V(\widehat{g\circ f})^\ast = V(\hat f)^\ast\circ V(\hat g)^\ast$. That is a co-FI-module. $\square$

**This closes Item 2a for the degree-preserving half.** Note the proof is uniform over **all** injections $f\in\mathrm{FI}(m,n)$, not merely the standard inclusions $s_n$ — the worry F11 §4.3 raised ("not just the standard inclusion"). The $S_n = \mathrm{Aut}_{\mathrm{FI}}([n])$-representation structure on each $B_n=H^{n-1}_n$ is the special case $m=n$, $f\in S_n$: $V(\hat f)^\ast$ with $\hat f\in S_{n+1}$ the permutation fixing $n$. So "$B_n$ is an $S_n$-rep" is not extra data — it is part of the co-FI-module structure.

**Remark 4.5 (the degree mismatch, restated).** On the *diagonal*, $V(\hat f)^\ast$ at degree $k=n-1$ is a map $B_n=H^{n-1}_n\to H^{n-1}_m$. For $m<n$ the target $H^{n-1}_m$ is *not* $B_m=H^{m-1}_m$ — it lives at the wrong cohomological degree. This is exactly F10 §7.2.a's degree-mismatch obstruction: the co-FI-maps alone do not relate consecutive diagonal entries. The diagonal needs the degree-shifting $\partial_n$ (§5) in addition. Hence the framework must carry *all* degrees $k$, and the genuine combined object is bigraded — §7.

---

## §5. Item 2b — $\partial$ is an FI-natural transformation $H^k\Rightarrow\Sigma^\ast H^{k+1}$

This is the heart of E1: the F11 §4.3 commuting square, for **every** injection. The clean statement is that $\partial$ is a morphism of co-FI-modules.

### 5.1 The target of $\partial$ is a shifted co-FI-module

$\partial_n^k$ has type $H^k_n\to H^{k+1}_{n+1}$. The target $H^{k+1}_{n+1}=\widetilde H^{k+1}(\Delta_{n+2}/\Delta_{n+1})$ is the value at $n$ of the **shifted** co-FI-module $\Sigma^\ast H^{k+1}$ (Def. 4.1): $(\Sigma^\ast H^{k+1})_n = H^{k+1}_{n+1}$, with $f\in\mathrm{FI}(m,n)$ acting by $H^{k+1}(\hat f) = V(\widehat{\hat f})^\ast = V(\tilde f)^\ast$. So the claim "$\partial$ commutes with the FI-structure" is precisely:

> $\partial^k = (\partial_n^k)_n$ is a morphism of co-FI-modules $H^k\Rightarrow\Sigma^\ast H^{k+1}$.

### 5.2 Naturality of the connecting homomorphism for maps of triples

**Lemma 5.1 (naturality of $\partial$).** A map of triples $\phi:(A'\subseteq B'\subseteq C')\to(A\subseteq B\subseteq C)$ induces a commuting ladder between the triple LES of $(A,B,C)$ and that of $(A',B',C')$; in particular, for every $k$,
$$
\begin{array}{ccc}
  \widetilde H^k(B/A) & \xrightarrow{\ \partial\ } & \widetilde H^{k+1}(C/B) \\[2pt]
  {\scriptstyle\phi^\ast}\big\downarrow & & \big\downarrow{\scriptstyle\phi^\ast} \\[2pt]
  \widetilde H^k(B'/A') & \xrightarrow{\ \partial'\ } & \widetilde H^{k+1}(C'/B')
\end{array}
$$
commutes.

*Proof.* This is the standard naturality of the connecting homomorphism of a short exact sequence of cochain complexes. A map of triples $\phi$ induces, contravariantly, cochain maps $C^\bullet(C)\to C^\bullet(C')$ carrying $C^\bullet(B)\to C^\bullet(B')$ and $C^\bullet(A)\to C^\bullet(A')$, hence a morphism of the SES (2.1):
$$
\begin{array}{ccccccccc}
  0 &\to& C^\bullet(C,B) &\xrightarrow{j}& C^\bullet(C,A) &\xrightarrow{r}& C^\bullet(B,A) &\to& 0\\
  && \big\downarrow && \big\downarrow && \big\downarrow &&\\
  0 &\to& C^\bullet(C',B') &\xrightarrow{j'}& C^\bullet(C',A') &\xrightarrow{r'}& C^\bullet(B',A') &\to& 0
\end{array}
$$
with both rows exact (§2). The connecting homomorphism is natural with respect to morphisms of short exact sequences of (co)chain complexes (e.g. Weibel, *An Introduction to Homological Algebra*, Thm. 1.3.1 — the naturality clause), giving the commuting square. $\square$

### 5.3 The main naturality theorem

**Theorem 5.3 ($\partial$ is FI-natural).** For each $k$, the family $\partial^k=(\partial_n^k)_n$ is a morphism of co-FI-modules
$$
  \partial^k:\;H^k\;\Longrightarrow\;\Sigma^\ast H^{k+1}.
$$
Explicitly, for every injection $f\in\mathrm{FI}(m,n)$ the square
$$
\begin{array}{ccc}
  H^k_n & \xrightarrow{\ \partial_n^k\ } & H^{k+1}_{n+1} \\[2pt]
  {\scriptstyle V(\hat f)^\ast}\big\downarrow & & \big\downarrow{\scriptstyle V(\tilde f)^\ast} \\[2pt]
  H^k_m & \xrightarrow{\ \partial_m^k\ } & H^{k+1}_{m+1}
\end{array}
\tag{5.1}
$$
commutes.

*Proof.* By Lemma 3.5, $V(\tilde f)$ is a map of triples $(\Delta_m,\Delta_{m+1},\Delta_{m+2})\to(\Delta_n,\Delta_{n+1},\Delta_{n+2})$. Apply Lemma 5.1 with $\phi = V(\tilde f)$: the induced map on $\widetilde H^k(B/A) = H^k_n$ is $\phi^\ast = V(\tilde f)|_{(\Delta_{m+1},\Delta_m)}^\ast = V(\hat f)^\ast$ (since $\tilde f|_{[m+1]}=\hat f$, Lemma 3.2), and the induced map on $\widetilde H^{k+1}(C/B) = H^{k+1}_{n+1}$ is $\phi^\ast = V(\tilde f)|_{(\Delta_{m+2},\Delta_{m+1})}^\ast = V(\tilde f)^\ast$. Lemma 5.1's square is exactly (5.1). Naturality holds for all $f$, so $\partial^k$ is a co-FI-module morphism $H^k\Rightarrow\Sigma^\ast H^{k+1}$. $\square$

**This closes Item 2b.** Three consequences worth stating explicitly:

- **Full functoriality, all injections.** Square (5.1) holds for *every* $f\in\mathrm{FI}(m,n)$, settling F11 §4.3's "not just the standard inclusion". The F11 §4.3 displayed square is the special case $k=n-1$, modulo the degree-mismatch caveat of Remark 4.5: F11 wrote it as "$B_n\to B_m$" verticals, but the honest fixed-degree square has the left vertical at degree $k=n-1$ landing in $H^{n-1}_m$ and the right vertical at degree $k+1=n$ landing in $H^n_{m+1}$. Only after concentration (UCC.1) is proven do the off-diagonal terms vanish and the square collapse onto the diagonal.
- **$S_n$-equivariance of $\partial_n$, for free.** Take $m=n$, $f=\sigma\in S_n$ in (5.1): $\hat\sigma\in S_{n+1}$ fixes $n$, $\tilde\sigma\in S_{n+2}$ fixes $n,n+1$, and the square says $\partial_n^k\circ V(\hat\sigma)^\ast = V(\tilde\sigma)^\ast\circ\partial_n^k$ — i.e. $\partial_n$ is $S_n$-equivariant for the inclusion $S_n\hookrightarrow S_{n+1}$ fixing the added point. F11 §4.2 asserted this; here it is a special case of FI-naturality, not a separate check. (This is also consistent with mg-6295 §5's "the cofiber carries an $S_n$-action, not $S_{n+1}$": $B_n$ is the value of a co-FI-module at $[n]$, so its symmetry group is $\mathrm{Aut}_{\mathrm{FI}}([n])=S_n$.)
- **The combined object is bigraded.** $\partial^k$ relates $H^k$ to $\Sigma^\ast H^{k+1}$: it raises the cohomological degree $k$ by one *and* the FI-degree $n$ by one (the $\Sigma^\ast$). The diagonal $B_n = H^{n-1}_n$ is exactly the locus where the cohomological and FI degrees track each other, and $\partial_n:B_n\to B_{n+1}$ moves *along* the diagonal. This is the precise sense in which the framework is "degree-shift-aware".

---

## §6. Item 3 — $\partial$-composite compatibility and coherence

We must check that iterating $\partial$ and combining it with the $V$-maps is coherent — no hidden relations, no associativity failure.

### 6.1 $\partial$-composites are unconstrained

**Proposition 6.1 ($\partial$-composites).** For each $k,n$ the composite
$$
  \partial_{n+1}^{k+1}\circ\partial_n^k\;:\;H^k_n\longrightarrow H^{k+2}_{n+2}
$$
is a well-defined linear map; on the diagonal, $\partial_{n+1}\circ\partial_n:B_n\to B_{n+2}$. No relation is imposed among the $\partial$'s: in particular $\partial_{n+1}\circ\partial_n$ is **not** required to vanish (and route (ii) §4.4 needs it not to — if each $\partial_n$ is an isomorphism then so is every composite).

*Proof.* $\partial_n^k$ is the connecting map of the triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$ and $\partial_{n+1}^{k+1}$ that of the *different* triple $(\Delta_{n+1},\Delta_{n+2},\Delta_{n+3})$. They are connecting maps of distinct short exact sequences, so no "$d^2=0$"-type identity applies; the composite is simply a composite of linear maps, defined because the target of the first is the source of the second ($H^{k+1}_{n+1}$). Associativity of $\partial$-composites is associativity of composition of linear maps. $\square$

So the only coherence to verify is the interaction of $\partial$-composites with the $V$-maps.

### 6.2 Iterated naturality coheres automatically

**Proposition 6.2 (iterated naturality).** For every $f\in\mathrm{FI}(m,n)$ and every $k$, the rectangle
$$
\begin{array}{ccccc}
  H^k_n & \xrightarrow{\ \partial_n^k\ } & H^{k+1}_{n+1} & \xrightarrow{\ \partial_{n+1}^{k+1}\ } & H^{k+2}_{n+2} \\[2pt]
  {\scriptstyle V(\hat f)^\ast}\big\downarrow & & {\scriptstyle V(\tilde f)^\ast}\big\downarrow & & \big\downarrow{\scriptstyle V(\widehat{\tilde f})^\ast} \\[2pt]
  H^k_m & \xrightarrow{\ \partial_m^k\ } & H^{k+1}_{m+1} & \xrightarrow{\ \partial_{m+1}^{k+1}\ } & H^{k+2}_{m+2}
\end{array}
$$
commutes, where $\widehat{\tilde f} = \Sigma^3 f\in\mathrm{FI}(m+3,n+3)$. Consequently $\partial^{k+1}\circ\partial^k:H^k\Rightarrow(\Sigma^\ast)^2H^{k+2}$ is a morphism of co-FI-modules, and more generally every iterated composite $\partial^{k+r-1}\circ\cdots\circ\partial^k:H^k\Rightarrow(\Sigma^\ast)^rH^{k+r}$ is FI-natural.

*Proof.* The left square is Theorem 5.3 (square (5.1)) for the injection $f\in\mathrm{FI}(m,n)$ at degree $k$. The right square is Theorem 5.3 applied to the injection $\hat f\in\mathrm{FI}(m+1,n+1)$ at degree $k+1$: that instance of (5.1) has top horizontal $\partial_{n+1}^{k+1}$, bottom horizontal $\partial_{m+1}^{k+1}$, left vertical $V(\widehat{\hat f})^\ast = V(\tilde f)^\ast$, and right vertical $V(\widehat{\widehat{\hat f}})^\ast = V(\widehat{\tilde f})^\ast$. The two squares share the edge $V(\tilde f)^\ast$, so pasting them gives the rectangle. The shared edge is genuinely common to both — not merely equal by coincidence — because the canonical-extension operation is functorial (Lemma 3.2): the "$\Sigma^\ast H^{k+1}$ target of $\partial^k$" and the "source of $\partial^{k+1}$" carry one and the same FI-action $V(\tilde f)^\ast = H^{k+1}(\hat f)$, with no ambiguity to reconcile. The general statement follows by induction on $r$, pasting one Theorem-5.3 square at a time. $\square$

**Remark 6.3 (why coherence is automatic — the single load-bearing fact).** All higher coherence of the combined structure reduces to one fact: **the canonical extension is functorial**, $\widehat{g\circ f}=\hat g\circ\hat f$ and $\Sigma$ is a functor (Lemma 3.2). Given that, (i) the $V$-maps are functorial on every pair-level (Prop. 4.4), (ii) the $V$-maps at adjacent pair-levels are intertwined by $\partial$ (Thm. 5.3), and (iii) these squares paste consistently because the intertwining map at each level is determined by the *same* injection $f$ via iterated hatting (Prop. 6.2). There is no independent coherence datum to check and no obstruction can arise: the structure is as coherent as $\mathrm{FI}$ itself. **Item 3 is closed.**

---

## §7. Item 4 — The degree-shift-aware functor category, and "finitely generated"

We now name the object. F11 §4.3 described it as "$\mathrm{FI}^{\mathrm{op}}$ enriched with a compatible shift endomorphism." We give two equivalent precise forms.

### 7.1 The category $\mathcal{C}$ by generators and relations

**Definition 7.1 (the category $\mathcal{C}$).** Let $\mathcal{C}$ be the category with:

- **Objects:** pairs $(n,k)$ with $n\ge 3$ and $k\in\mathbb{Z}$.
- **Generating morphisms:**
  - for each $f\in\mathrm{FI}(m,n)$ and each $k$, a morphism $V_f:(n,k)\to(m,k)$ (degree-preserving, contravariant in $\mathrm{FI}$);
  - for each $(n,k)$, a morphism $\sigma_{n,k}:(n,k)\to(n+1,k+1)$ (the shift).
- **Relations:**
  - **(R1) $V$ is an $\mathrm{FI}^{\mathrm{op}}$-action at each fixed $k$:** $V_{\mathrm{id}_{[n]}}=\mathrm{id}_{(n,k)}$, and for composable injections $g\in\mathrm{FI}(m,n)$, $g'\in\mathrm{FI}(\ell,m)$ — giving $V_g:(n,k)\to(m,k)$ and $V_{g'}:(m,k)\to(\ell,k)$ — the contravariance relation $V_{g'}\circ V_g = V_{g\circ g'}$ holds (where $g\circ g'\in\mathrm{FI}(\ell,n)$);
  - **(R2) $\sigma$ is natural with respect to $V$:** for every $f\in\mathrm{FI}(m,n)$ and every $k$,
    $$
      \sigma_{m,k}\circ V_f \;=\; V_{\hat f}\circ\sigma_{n,k}\qquad\text{as morphisms }(n,k)\to(m+1,k+1).
    $$

A **module over the degree-shift-aware functor category** is a covariant functor $\mathcal{C}\to\mathbf{Vect}_{\mathbb{Q}}$.

In (R2), $V_{\hat f}:(n+1,k+1)\to(m+1,k+1)$ is the $V$-generator of the injection $\hat f\in\mathrm{FI}(m+1,n+1)$; no separate generator is needed for $\tilde f$, since $V_{\hat f}$ already names "$f$ acting one pair-level up". The category $\mathcal{C}$ is, by construction, the free category on the generators modulo (R1), (R2).

### 7.2 $H$ as a $\mathcal{C}$-module

**Theorem 7.2 ($H$ is a $\mathcal{C}$-module).** The assignment
$$
  H:\mathcal{C}\to\mathbf{Vect}_{\mathbb{Q}},\qquad
  H(n,k) = H^k_n = \widetilde H^k(\Delta_{n+1}/\Delta_n),\qquad
  H(V_f) = V(\hat f)^\ast,\quad H(\sigma_{n,k}) = \partial_n^k
$$
is a well-defined functor. Hence $\bigl((B_n)_n,\{V(f)^\ast\},\{\partial_n\}\bigr)$ — the diagonal restriction $n\mapsto H(n,n-1)$ together with the $\partial_n$ and the $V$-action — is a genuine module over the degree-shift-aware functor category.

*Proof.* A functor out of a category presented by generators and relations is well-defined iff the images of the generators satisfy the relations. (R1) holds: by Prop. 4.4, $f\mapsto V(\hat f)^\ast$ is, for each fixed $k$, a contravariant functor on $\mathrm{FI}$ — i.e. a co-FI-module $H^k$. (R2) holds: it is exactly the commuting square (5.1) of Theorem 5.3, $\partial_m^k\circ V(\hat f)^\ast = V(\tilde f)^\ast\circ\partial_n^k$, with $V(\tilde f)^\ast = H(V_{\hat f})$. So $H$ respects all relations and is a well-defined functor $\mathcal{C}\to\mathbf{Vect}$. The diagonal is the restriction along the embedding $\mathbb{N}_{\ge 3}\to\mathcal{C}$, $n\mapsto(n,n-1)$, $\sigma$-arrows $n\mapsto n+1$; the $V$-action and the $\partial_n=H(\sigma_{n,n-1})$ are the structure maps. $\square$

### 7.3 Intrinsic description: graded co-FI-modules with a shift-compatible degree-$(+1)$ map

The generators-and-relations form is concrete but opaque. Here is the intrinsic one.

**Theorem 7.4 (intrinsic form).** A $\mathcal{C}$-module is the same thing as the data of:
- a $\mathbb{Z}$-graded co-FI-module $H^\bullet = (H^k)_{k\in\mathbb{Z}}$, each $H^k:\mathrm{FI}^{\mathrm{op}}\to\mathbf{Vect}$ (supported on $n\ge 3$);
- for each $k$, a morphism of co-FI-modules $\partial^k:H^k\Rightarrow\Sigma^\ast H^{k+1}$,
where $\Sigma^\ast$ is the FI-shift on co-FI-modules (Def. 4.1). Equivalently: $\mathcal{C}$-$\mathrm{Mod}$ is the category of $\mathbb{Z}$-graded co-FI-modules equipped with a degree-$(+1)$ endomorphism *twisted by the shift* — "$\mathrm{FI}^{\mathrm{op}}$ with a compatible shift endomorphism" in the precise sense that $\partial$ is a natural transformation $H^\bullet\Rightarrow\Sigma^\ast H^{\bullet+1}$.

*Proof.* Given a $\mathcal{C}$-module $G$: set $H^k_n := G(n,k)$ with $f$ acting by $G(V_f)$ — (R1) says each $H^k$ is a co-FI-module. Set $\partial^k_n := G(\sigma_{n,k})$ — (R2) says $\partial^k$ commutes with the FI-action in the sense $\partial^k_m\circ G(V_f) = G(V_{\hat f})\circ\partial^k_n$, i.e. $\partial^k:H^k\Rightarrow\Sigma^\ast H^{k+1}$ is a co-FI-module morphism (recall $(\Sigma^\ast H^{k+1})_n = H^{k+1}_{n+1}$ with $f$ acting by $H^{k+1}(\hat f) = G(V_{\hat f})$). Conversely, the data $(H^\bullet,\partial^\bullet)$ defines $G$ on objects and generators, and (R1),(R2) are satisfied by construction. The two assignments are mutually inverse. $\square$

By Theorem 5.3, **the cofiber-cohomology $H^\bullet$ with the triple connecting maps $\partial^\bullet$ is exactly such an object** — a $\mathbb{Z}$-graded co-FI-module with an FI-natural degree-$(+1)$-and-shift map. This is the rigorous form of F10 §7.2.b–c's "the correct degree-shift-aware functor-category framework" and F11 §4.3's "$\mathrm{FI}^{\mathrm{op}}$ enriched with a compatible shift endomorphism". **Item 4's identification is closed.**

**Remark 7.5 (relation to known structures).** $\mathcal{C}$ is *not* exotic. Forgetting the shift, it is $\bigsqcup_k\mathrm{FI}^{\mathrm{op}}$; the $\sigma$-generators glue the $k$-graded pieces along the FI-shift $\Sigma$. An object is a "co-FI-module with a self-extension" — formally a module over the "FI with shift" monoidal data. The closest standard analogue is an **$\mathrm{FI}$-module with its derivative/shift map** (the shift $\Sigma$ and the natural map are the standard tools in Church–Ellenberg–Farb's and Nagpal's treatment of FI-homology); here the natural map raises an auxiliary cohomological grading as well. We do not need the analogy for E1 — Def. 7.1 / Thm. 7.4 stand on their own — but it places the object in known territory and is why central-stability machinery (Putman/Patzt) is expected to apply (F11 §4.5).

### 7.4 "Finitely generated" for the diagonal

**Definition 7.6 (finite generation).** A $\mathcal{C}$-module $G$ is **finitely generated in degree $\le d$** if there is a finite-dimensional subspace $\Gamma\subseteq\bigoplus_{n\le d,\,k}G(n,k)$ such that the only sub-$\mathcal{C}$-module of $G$ containing $\Gamma$ is $G$ itself — equivalently, every $G(n,k)$ is spanned by the images of $\Gamma$ under composites of the structure maps $G(V_f)$ and $G(\sigma)$. The **diagonal** $(B_n)_n = (H(n,n-1))_n$ is **finitely generated** if the $\mathcal{C}$-module $H$ is finitely generated in some degree $\le d$.

Unwinding via Theorem 7.4: $H$ is finitely generated in degree $\le d$ iff every $H^k_n$ ($n>d$) is spanned by images, under composites of $V$-maps and $\partial$-maps, of $\bigoplus_{n\le d,k}H^k_n$. On the diagonal, the $V$-maps $V(\hat f)^\ast:B_n=H^{n-1}_n\to H^{n-1}_m$ land *off* the diagonal (Remark 4.5), so reaching $B_n$ from $B_{\le d}$ uses *alternating* composites of $\partial$'s (which move up the diagonal) and $V$'s (which move within a cohomological degree). This is exactly F11 §4.3's "generated by $B_{\le d}$ under $\partial$-composites and $V$-maps".

**Corollary 7.7 (recovering the F11 §4.4 reduction).** Suppose (UCC.1)'s *concentration* holds — $H^k_n = 0$ for $k\ne n-1$, all $n\ge 3$ (proven at $n=3$; conjectural beyond). Then:
1. $H^\bullet$ collapses onto its diagonal: the only non-zero spaces are $B_n = H^{n-1}_n$, and the only non-zero structure maps are the $\partial_n:B_n\to B_{n+1}$ (every off-diagonal $V$-map has zero source or zero target; every diagonal $V$-map $B_n\to H^{n-1}_m$, $m<n$, has zero target).
2. $H$ is finitely generated in degree $\le d$ $\iff$ for every $n>d$, $B_n = \sum$ of images $\partial_{n-1}\circ\cdots\circ\partial_j(\text{stuff in }B_j)$, $j\le d$ — i.e. the composite $\partial_{n-1}\circ\cdots\circ\partial_d:B_d\to B_n$ is surjective for all $n>d$ (using also the $S_n$-action, which is already part of $V$).
3. In particular, **if every $\partial_n$ is an isomorphism** (F11 §4.4's sufficient condition for route (ii)), then $H$ is finitely generated in degree $\le 3$, generated by $B_3 = 2\cdot\mathrm{sgn}_{S_3}$. This is the cleanest form of F11 §4.5's "$(\widetilde B_n)_n = M(0)^{\oplus 2}$".

*Proof.* (1): under concentration the bigraded $H$ is supported on $\{(n,n-1)\}$; a $V$-map $H^k_n\to H^k_m$ is non-zero only if both $H^k_n,H^k_m\ne 0$, forcing $k=n-1=m-1$, i.e. $n=m$ and $f\in S_n$ — so off-diagonal $V$-maps vanish and the surviving $V$-maps are the $S_n$-actions. $\partial_n^k:H^k_n\to H^{k+1}_{n+1}$ is non-zero only if $k=n-1$, i.e. $\partial_n=\partial_n^{n-1}$. (2): with only $\partial_n$ and $S_n$-actions as structure maps, the sub-$\mathcal{C}$-module generated by $\bigoplus_{n\le d}B_n$ has $n$-th diagonal piece $\sum_{j\le d}\operatorname{im}(\partial_{n-1}\cdots\partial_j)$ (closed under $S_n$ automatically); it equals $H$ iff this is all of $B_n$ for every $n>d$. (3): $\partial_n$ iso $\Rightarrow\partial_{n-1}\cdots\partial_3:B_3\to B_n$ iso, in particular surjective, for all $n>3$; apply (2) with $d=3$. $\square$

So the framework E1 builds is *exactly* the one in which F11 §4.4–§4.5's reduction lives: with the functor category $\mathcal{C}$ in hand, "route (ii) reduces (FG-Cofiber)'s representation-type half to '$\partial_n$ iso for all $n$'" becomes the precise statement "the $\mathcal{C}$-module $H$ is finitely generated in degree $\le 3$, and concentrated". E1 does **not** prove $\partial_n$ is an isomorphism — that is (E2), gated on PCR-Lit-2′ — but it makes the claim a well-posed statement about a genuine algebraic object.

### 7.5 Compatibility with the sign-twist

F11 §4.5 applies the mandatory sign-twist $\widetilde B_n := B_n\otimes\mathrm{sgn}_{S_n}$. The twist $M\mapsto M\otimes\mathrm{sgn}$ is the standard automorphism of the category of co-FI-modules (M2 §5.3): it acts by $\mathrm{sgn}(\sigma)$ on each $S_n$-part and by the induced sign on FI-structure maps. It commutes with the shift $\Sigma^\ast$ up to the canonical sign identification $\mathrm{sgn}_{S_{n+1}}|_{S_n} = \mathrm{sgn}_{S_n}$, so it lifts to an automorphism of $\mathcal{C}$-$\mathrm{Mod}$: $(H^\bullet,\partial^\bullet)\mapsto(\widetilde H^\bullet,\widetilde\partial^\bullet)$ with $\widetilde\partial^k = \partial^k\otimes\mathrm{sgn}$. Hence finite generation is twist-invariant, and F11 §4.5's reformulation "$(\widetilde B_n)_n$ with $\widetilde\partial_n$ is $M(0)^{\oplus 2}$" is a statement *internal to* $\mathcal{C}$-$\mathrm{Mod}$ — well-posed by E1, to be settled (or not) by (E2)/PCR-Lit-2′. We record this for completeness; no twist is needed for §3–§7.4.

---

## §8. Verdict, scope boundary, and what E1 unblocks

### 8.1 Verdict: GREEN-functoriality-established

Per the F13 verdict matrix: **GREEN-functoriality-established** — *"$\bigl((B_n)_n,\{V(f)^\ast\},\{\partial_n\}\bigr)$ is rigorously a module over the identified degree-shift-aware functor category; route (ii)'s framework half is closed."* All four caveats F11 §4.3 flagged are closed:

| # | F11 §4.3 caveat | E1 resolution | Where |
|---|---|---|---|
| 1 | Choice-independence of the cofiber relabelling | The non-degenerate extension is **unique** (Lemma 3.3); all others induce $0$. The relabelling is canonical — no choice exists. | §3 |
| 2a | Full functoriality across all injections (degree-preserving half) | Each $H^k$ is a genuine co-FI-module over **all** of $\mathrm{FI}$ (Prop. 4.4), via the FI-shift $\Sigma$. | §4 |
| 2b | The commuting square for every injection (shift half) | $\partial^k:H^k\Rightarrow\Sigma^\ast H^{k+1}$ is an FI-natural transformation (Thm. 5.3); the square holds for all $f$; $S_n$-equivariance is a special case. | §5 |
| 3 | $\partial$-composite compatibility / coherence | $\partial$-composites are unconstrained associative composites; iterated naturality coheres automatically from functoriality of the canonical extension (Prop. 6.1–6.2, Rmk. 6.3). | §6 |
| 4 | Identify the functor category + define "finitely generated" | $\mathcal{C}$ defined by generators/relations (Def. 7.1) and intrinsically as graded co-FI-modules with $\partial:H^k\Rightarrow\Sigma^\ast H^{k+1}$ (Thm. 7.4); $H$ proven a $\mathcal{C}$-module (Thm. 7.2); finite generation defined (Def. 7.6); F11 §4.4 reduction recovered (Cor. 7.7). | §7 |

No RED, no AMBER. **RED-structure-fails is excluded:** $\partial_n$ *does* commute with $V(f)^\ast$ for every injection — it is the naturality of the connecting homomorphism of the triple LES (Lemma 5.1) applied to the map of triples $V(\tilde f)$ (Lemma 3.5), and the map-of-triples property holds for *every* $f$ because the canonical extension always exists and is unique (Lemma 3.3). **AMBER-partial is excluded:** there is no residual coherence point — Remark 6.3 isolates the single load-bearing fact (functoriality of the canonical extension, Lemma 3.2), and everything else is standard homological algebra with no obstruction. The combined structure coheres.

### 8.2 Scope boundary — what E1 deliberately does *not* establish

E1 is the **framework half** of route (ii). It does **not** touch the **finiteness half**:

- **E1 does not prove concentration** (UCC.1's claim $H^k_n=0$ for $k\ne n-1$). The framework is set up for all $k$ precisely because concentration is not available; Corollary 7.7 is stated *conditionally* on it.
- **E1 does not prove $\partial_n$ is injective / surjective / an isomorphism.** That is genuinely open content (Def. 2.1, second remark): it involves the double-cofiber cohomology $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)$. Settling it at $n=3$ is **(E2)**, which needs the $n=4\to5$ cofiber Betti vector $B_4=\widetilde H^3(\Delta_5/\Delta_4)$ — the **PCR-Lit-2′** computation — and is therefore out of E1's (and F11's) "no new computation / no new $n$-datapoint" scope.
- **E1 does not prove finite generation.** Definition 7.6 makes "finitely generated" a well-posed question about the $\mathcal{C}$-module $H$; answering it is the central-stability / Patzt-style argument F11 §4.5 scopes, downstream of (E2).

### 8.3 What E1 unblocks

E1 is, per F11 §6.2, "the prerequisite for everything else in route (ii)". With the framework rigorous:

- **(E2)** — compute $\partial_3:B_3\to B_4$ and test it for isomorphism — is now a well-posed question about a *defined* structure map of a *defined* $\mathcal{C}$-module, not a heuristic. It remains gated on PCR-Lit-2′ (sibling-class computation; cf. F14 / mg-3839).
- **The general-$n$ central-stability argument** (F15's general-$n$ phase, F11 §6.2 follow-up C) now has its object of study pinned down: it must show the $\mathcal{C}$-module $H$ is finitely generated (Def. 7.6) — sufficiently, that the $\partial_n$ are eventually surjective (Cor. 7.7(2)); cleanly, isomorphisms (Cor. 7.7(3)). Putman/Patzt central stability is the expected tool (Rmk. 7.5, F11 §4.5).
- The F10 §7.2.b–c open framework question — "identify the correct degree-shift-aware functor-category framework" — is **answered**: it is $\mathcal{C}$-$\mathrm{Mod}$ (Thm. 7.4). What F10 left as the open problem (FG-Cofiber) is now cleanly bisected into *framework* (closed here) and *finiteness* (open, (E2)→central-stability).

### 8.4 Trust-surface impact

**None.** E1 introduces no new axioms, makes no Lean changes, runs no computation. It is naturality of the triple long exact sequence (standard homological algebra, §2, §5) plus the functoriality of the FI-relabelling (Lemma 1.3, cross-checked computationally in M2 §4; proven structurally and $n$-uniformly here). The in-tree Lean artifact `width3_one_third_two_thirds` (4-axiom trust surface) is untouched, as is the general-$n$ paper-level track.

---

## §9. References

### 9.1 Parent / sibling mg-tickets

- **mg-b352** — F11: attack on (FG-Cofiber), routes (i)/(ii) survey. `11a75d6`; `docs/state-F11.md` §4.2 ($\partial_n$ identification), §4.3 (commuting square + the four caveats E1 closes), §4.4 ($\partial_n$ iso ⇒ rep-type propagation), §4.5 (sgn-twist, central stability), §4.6 (entry sub-problems (E1)/(E2)), §6.2 (follow-up recommendations). **Parent — E1 is F11's recommended do-first follow-up A.**
- **mg-8216** — F10: general-$n$ unified proof synthesis. `3c173df`; `docs/general-n-proof-synthesis.md` §7.2.a (degree-mismatch obstruction; the geometric diagonal has no naive co-FI-structure), §7.2.b (the degree-shift-aware framework question — answered here), §7.2.c ((FG-Cofiber)), §7.2.d (three routes). **Grandparent.**
- **mg-6295** — PCR-Lit-2 / M1: discrete Morse on the cofiber. `f169345`; `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`. $\Delta_n\hookrightarrow\Delta_{n+1}$ subcomplex inclusion (§1.1), order-ideal / downward-closed (§6.1); $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ via the perfect cofiber matching $M_{\mathrm{rel}}$, $(0,0,2,0)$; "the cofiber carries an $S_n$-action, not $S_{n+1}$" (§5). §6.3 designates PCR-Lit-2′ (the $n=4\to5$ cofiber Betti).
- **mg-759d** — PCR-Lit-3 / M2: FI-module presentation-degree check. `e5d9b08`; `docs/compatibility-geometry-PCR-Lit-3-fi-module.md`. §4 — FI-action axioms verified over all injections (trip-wire (c), PASS) — the computational cross-check of Lemma 1.3; §5.1 (fixed-$k$ degenerate), §5.3 (sgn-twist $M(0)$).
- **mg-3839** — F14 / PCR-Lit-2′: $n=4\to5$ cofiber computation. Sibling of F13, runs in parallel, no dependency either way; supplies $B_4$ for (E2).
- **mg-59f3** — PCR-2: spectral $E_2$ page, $\delta_3^{\mathrm{sgn}}$ injective, $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ cross-validated. **mg-f91f** — PCR-1: $n=4$ relative Betti $(0,0,2,0)$.

### 9.2 Mathematical literature

- C. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Adv. Math. 38 (1994), Thm. 1.3.1 — the long exact sequence of a short exact sequence of (co)chain complexes and the **naturality** of the connecting homomorphism (the load-bearing standard fact behind Lemma 5.1).
- A. Hatcher, *Algebraic Topology*, Cambridge (2002), §2.1–§2.2 — good pairs, the long exact sequence of a triple, relative (co)homology and $\widetilde H^\bullet(X/A)\cong H^\bullet(X,A)$ for good pairs (Lemma 1.4, §2).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11 — order complexes, subcomplex pairs, simplicial maps from poset maps (§1).
- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015) — FI-modules, co-FI-modules, the shift functor, the sign-twist; $(\mathrm{sgn}_{S_n})_n$ as the canonical non-example.
- T. Church, J. Ellenberg, B. Farb, R. Nagpal, *FI-modules over Noetherian rings*, Geom. Topol. 18 (2014) — Noetherianity; the shift/derivative of an FI-module (Rmk. 7.5).
- E. Ramos, *On the degree-wise coherence of FI-modules*, NYJM 23 (2017) — presentation degree; "determined by values at indices $\le d$" (the downstream tool, Cor. 7.7).
- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015); P. Patzt, *Central stability homology*, J. Topol. (2017+) — central stability, finite generation from bounded presentation (the downstream route-(ii) machinery; Rmk. 7.5, §8.3).

### 9.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration.
- 2026-05-14T08:05Z — focus on the induction, not special cases. (E1 is pure structural homological algebra — squarely "the induction", no special-case computation.)

---

*Polecat: mg-ecf6 (F13, E1). Branch: `compat-geom-F13-E1-functoriality`. Verdict: **GREEN-functoriality-established** — $\bigl((B_n)_n,\{V(f)^\ast\},\{\partial_n\}\bigr)$ is rigorously a module over the degree-shift-aware functor category $\mathcal{C}$ (Thm. 7.2, Thm. 7.4). All four F11 §4.3 caveats closed: choice-independence resolved as canonicity (Lemma 3.3), full functoriality across all injections (Prop. 4.4, Thm. 5.3), $\partial$-composite coherence automatic (Prop. 6.1–6.2), functor category identified with its notion of finite generation (Def. 7.1/7.6, Thm. 7.4, Cor. 7.7). Route (ii)'s framework half is closed; the finiteness half ("$\partial_n$ iso for all $n$") is genuinely open and belongs to (E2)/PCR-Lit-2′. No new axioms; no Lean changes; no new computation. Cumulative state: `docs/state-F13.md`.*
