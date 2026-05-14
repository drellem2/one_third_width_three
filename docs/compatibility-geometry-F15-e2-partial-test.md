# Compat-Geom — F15 (E2): the $\partial_3$ isomorphism test + the general-$n$ diagnosis (mg-8355)

**Branch:** `compat-geom-F15-E2-partial-d3-iso` (new).
**Parent:** mg-b352 (F11, GREEN-route-traction, `11a75d6`) — `docs/state-F11.md` §4.4–§4.6 (the "$\partial_n$ iso" reduction; entry sub-problem (E2)), §6.2 follow-up C.
**Depends:** mg-3839 (F14, GREEN-cofiber-perfect) — supplies $B_4 = \widetilde H^3(\Delta_5/\Delta_4) = 2\cdot\mathrm{sgn}_{S_4}$ and $\widetilde b_*(\Delta_5/\Delta_4) = (0,0,0,2,0)$.
**Also uses:** mg-ecf6 (F13, E1, GREEN-functoriality-established) — the degree-shift-aware functor category and the triple-LES conventions (its §2). **Verified GREEN before this writeup** (per `feedback_pre_execution_dependency_verification`).
**Type:** Computation ($\partial_3$, via a factorisation) + structural argument (the general-$n$ diagnosis). LaTeX-style Markdown; **no new axioms; no Lean changes.** Multi-session-able; cumulative state ledger in `docs/state-F15.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: AMBER-partial3-not-iso.** $\partial_3 : B_3 \to B_4$ has **rank exactly $1$** — it is **not an isomorphism** (not injective, not surjective). This is established rigorously by two independent routes and is *unconditional* at $n=3$ (every input is proven: Hyp(3), Hyp(4), Hyp(5), mg-6295's $B_3$, F14's $B_4$). The result is not a computational gap (RED-computational-gap excluded) and not a fragile numerical accident: $\partial_3$ **factors** through the $1$-dimensional space $\widetilde H^2(\Delta_4) = \mathrm{sgn}_{S_4}$, so its rank is structurally capped at $1$. The same factorisation is **$n$-uniform** and yields the general-$n$ diagnosis: $\partial_n$ is an isomorphism **if and only if** $\delta_n = 0$ — which **contradicts (UCC.2)**. So F11 §4.4's reduction "$\partial_n$ iso for all $n$" is not merely unproven, it is **incompatible with (UCC.2)**, a part of the very (UCC) the program is establishing. Route (ii)'s *simplest* form — "$(B_n)_n$ is the free object $M(0)^{\oplus 2}$" — is **dead**, uniformly. Route (ii)'s *weaker* form — a **bounded central-stability presentation** — is **not** killed by this finding, and the factorisation $\partial_n = \delta_{n+1}\circ q_n$ is the precise structural handle a revised route (ii) would use (§6). Phase 2 (the iso-based general-$n$ argument) is moot and not executed, per the ticket; the general-$n$ *diagnosis* (§6) is delivered in its place — it pinpoints exactly where the degree-shift-aware object is not free. **PM/Daniel decision input requested** (§7.3).

**Deliverables:**
- `scripts/compat_geom_partial_3.py` — the $\partial_3$ construction + isomorphism test (pure-Python stdlib; runtime $\approx 1.5$ s).
- `docs/compatibility-geometry-F15-e2-partial-test.md` (this doc).
- `docs/state-F15.md` (cumulative state ledger).

---

## §0. Executive summary

### 0.1 The target

F11 (mg-b352) advanced route (ii) of (FG-Cofiber): the representation-type half of (UCC.1) reduces to the single uniform statement "the triple connecting homomorphism $\partial_n : B_n \to B_{n+1}$ is an isomorphism for all $n$", where $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is the cofiber-cohomology diagonal and $\partial_n$ is the connecting map of the triple $(\Delta_n \subset \Delta_{n+1} \subset \Delta_{n+2})$ (F11 §4.2–§4.4). Entry sub-problem **(E2)**, this ticket, is the first concrete test: **compute $\partial_3 : B_3 \to B_4$ and decide whether it is an isomorphism.**

With F14 (mg-3839) now GREEN, the codomain is known: $B_4 = \widetilde H^3(\Delta_5/\Delta_4) = 2\cdot\mathrm{sgn}_{S_4}$, $2$-dimensional. The domain $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ is known (mg-6295/mg-59f3). So $\partial_3$ is, as F11 §4.6 anticipated, a $2\times 2$ $S_3$-equivariant matrix between two known $2$-dimensional spaces — and the iso test is the question "is its determinant non-zero?".

### 0.2 The result

> **$\partial_3$ has rank exactly $1$. It is *not* an isomorphism.**

The reason is structural, not numerical. The triple connecting homomorphism **factors** (§3):
$$
  \partial_3 \;=\; \delta_4 \circ q_3 \;:\;
  B_3 = \widetilde H^2(\Delta_4/\Delta_3)
  \xrightarrow{\ q_3\ } \widetilde H^2(\Delta_4)
  \xrightarrow{\ \delta_4\ } \widetilde H^3(\Delta_5/\Delta_4) = B_4 ,
$$
where $q_3$ and $\delta_4$ are **pair-LES maps** (not triple maps). Both legs are pinned by the cohomology of $\Delta_3,\Delta_4,\Delta_5$ and the cofibers:

- $q_3 : B_3 \twoheadrightarrow \widetilde H^2(\Delta_4)$ is **surjective** with **$1$-dimensional kernel** (§4). Surjectivity is exactness of the pair LES of $(\Delta_4,\Delta_3)$ at $\widetilde H^2(\Delta_4)$ given $\widetilde H^2(\Delta_3)=0$; the kernel is $\mathrm{im}(\delta_3)$, $1$-dimensional because $\delta_3$ is injective (mg-59f3 / (UCC.2) at $n=3$). So $\mathrm{rank}(q_3) = \dim\widetilde H^2(\Delta_4) = 1$.
- $\delta_4 : \widetilde H^2(\Delta_4) \hookrightarrow B_4$ is **injective** (§4), because the pair LES of $(\Delta_5,\Delta_4)$ has $\widetilde H^2(\Delta_5)=0$ (Hyp(5)). This is exactly the LES F14 itself used (F14 doc §3.3).

Hence $\mathrm{rank}(\partial_3) = \mathrm{rank}(\delta_4\circ q_3) = \mathrm{rank}(q_3) = 1 < 2 = \dim B_3$.

An **independent** cross-check (§5) — exactness of the *triple* LES of $(\Delta_3,\Delta_4,\Delta_5)$, using the directly-computed Betti numbers and the cited F14/Hyp(5) inputs — gives the **same** answer, $\mathrm{rank}(\partial_3)=1$.

The companion script computes, *from scratch* and by sparse mod-$p$ rank over two primes, the Betti vectors $\widetilde b_*(\Delta_3) = (0,1)$, $\widetilde b_*(\Delta_4) = (0,0,1,0,0)$ (Hyp(4)), $\widetilde b_*(\Delta_4/\Delta_3) = (0,0,2,0,0)$ (mg-6295) — every number the §3–§5 argument needs that lives in $\Delta_4$ — and verifies every link in the chain. Runtime $\approx 1.5$ s.

### 0.3 The general-$n$ diagnosis

The factorisation $\partial_n = \delta_{n+1}\circ q_n$ is **$n$-uniform** — the cochain-level identity (§3.1) holds for every triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$. It yields (§6):

> **$\partial_n$ is an isomorphism $\iff \delta_n = 0$.**

But (UCC.2) at level $n$ asserts $\delta_n : \widetilde H^{n-2}(\Delta_n) = \mathrm{sgn}_{S_n} \hookrightarrow B_n$ is **injective**, hence $\delta_n \ne 0$. So **(UCC.2)$(n) \Rightarrow \partial_n$ is not an isomorphism**, for every $n$. The "$\partial_n$ iso for all $n$" hypothesis is *incompatible* with (UCC.2). Equivalently: under the program's own target Hyp$(n{+}1)$, $\widetilde H^{n-1}(\Delta_{n+1}) = \mathrm{sgn}_{S_{n+1}}$ is $1$-dimensional, and $\partial_n$ factors through it — so $\mathrm{rank}(\partial_n) \le 1$ for all $n$.

### 0.4 What this does and does not kill

| | status |
|---|---|
| Route (ii), **simplest form**: $(\widetilde B_n)_n = M(0)^{\oplus 2}$, i.e. every $\partial_n$ iso (F11 §4.4–§4.5) | **DEAD** — incompatible with (UCC.2). |
| Route (ii), **weaker form**: a *bounded central-stability presentation* (Putman/Patzt; F11 §4.5 "minimally...") | **NOT killed.** The factorisation $\partial_n = \delta_{n+1}\circ q_n$ is a precise structural input for it (§6.3). |
| F13's framework (E1) — $((B_n)_n,\{V(f)^*\},\{\partial_n\})$ a module over the degree-shift-aware functor category | **Untouched.** F13 set up the *framework*; F15 computes a *structure map* in it. |
| (UCC.1) concentration half (M1, "$M_{\mathrm{rel}}$ perfect") | **Untouched** — orthogonal to $\partial_n$. |
| F14, mg-6295, F10's reductions | **Untouched** — F15 *uses* them. |

**Verdict: AMBER-partial3-not-iso.** Decisive negative information: route (ii)'s simplest form fails, uniformly and for a precise structural reason, and the failure is exactly localised (§6.4). PM/Daniel decision input requested on whether to pursue the weaker bounded-central-stability form, or revisit route (iii) (§7.3).

---

## §1. Setting and the object

**Notation** (F1-refined / F2 / F5 / mg-6295 / F13 §0 convention). $[n] = \{0,\dots,n-1\}$. $\mathrm{PPF}_n$ is the set of proper partial orders on $[n]$ — non-empty relation, non-total — ordered by refinement ($P \le Q \iff P \subseteq Q$ as relation sets); $|\mathrm{PPF}_n| = 12,194,4110$ at $n=3,4,5$. $\Delta_n := \Delta(\mathrm{PPF}_n)$ is its order complex. $\iota_n : \mathrm{PPF}_n \hookrightarrow \mathrm{PPF}_{n+1}$ is the standard inclusion ($n$ incomparable to all of $[n]$); it is an **order-ideal** inclusion (a sub-relation of an $n$-isolated poset is $n$-isolated — verified directly in the script, §[A]), so $\Delta_n \subseteq \Delta_{n+1}$ is a subcomplex inclusion and $(\Delta_{n+1},\Delta_n)$ is a **good pair** (F13 Lemma 1.4). All (co)homology is reduced, with $\mathbb{Q}$-coefficients.

$$
  B_n \;:=\; \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n) \;=\; H^{n-1}\bigl(C^\bullet(\Delta_{n+1},\Delta_n)\bigr)
$$
is the cofiber-cohomology diagonal (F11 §4.2, F13 §1.3), the object (FG-Cofiber) is about. We use F13's relative-cochain convention: $C^\bullet(X,A) := \{\varphi \in C^\bullet(X) : \varphi|_A = 0\}$, the cochains vanishing on the subcomplex (F13 §1.3) — basepoint-free, purely algebraic.

**Established inputs.** Three facts are *proven* and used as inputs (none recomputed for $\Delta_5$ — its relative complex has $\approx 3.3\times 10^8$ cells, out of scope for direct enumeration; the $\Delta_3,\Delta_4$ facts the script *does* recompute from scratch):

| fact | content | source |
|---|---|---|
| Hyp(3) | $\widetilde H^*(\Delta_3) = \mathrm{sgn}_{S_3}$, concentrated in degree $1$ | F10; script §[B] re-derives $\widetilde b_*(\Delta_3)=(0,1)$ + $\mathrm{sgn}$ |
| Hyp(4) | $\widetilde H^*(\Delta_4) = \mathrm{sgn}_{S_4}$, concentrated in degree $2$ | F10; script §[B] re-derives $\widetilde b_*(\Delta_4)=(0,0,1,0,0)$ + $\mathrm{sgn}$ |
| Hyp(5) | $\widetilde H^*(\Delta_5) = \mathrm{sgn}_{S_5}$, concentrated in degree $3$ | F10, verified $n\le 6$ |
| $B_3$ | $B_3 = \widetilde H^2(\Delta_4/\Delta_3) = 2\cdot\mathrm{sgn}_{S_3}$ | mg-6295 (PCR-Lit-2), mg-59f3; script §[B] re-derives $\widetilde b_*(\Delta_4/\Delta_3)=(0,0,2,0,0)$ + $2\cdot\mathrm{sgn}$ |
| $B_4$ | $B_4 = \widetilde H^3(\Delta_5/\Delta_4) = 2\cdot\mathrm{sgn}_{S_4}$, $\widetilde b_*(\Delta_5/\Delta_4)=(0,0,0,2,0)$ | F14 (mg-3839), GREEN-cofiber-perfect |
| (UCC.2) at $n=3$ | $\delta_3 : \widetilde H^1(\Delta_3) \hookrightarrow B_3$ injective | mg-59f3 §4 |

Everything in §3–§5 for the **concrete $n=3$ case** uses only proven inputs — the $\partial_3$ result is **unconditional**.

---

## §2. The triple LES and $\partial_3$ — recall (F13 §2)

For a triple of subcomplexes $A \subseteq B \subseteq C$, F13 §2 records the short exact sequence of relative cochain complexes
$$
  0 \to C^\bullet(C,B) \xrightarrow{\ j\ } C^\bullet(C,A) \xrightarrow{\ r\ } C^\bullet(B,A) \to 0
  \tag{2.1}
$$
($j$ = inclusion of cochains vanishing on $B$; $r$ = restriction to $B$) and its long exact cohomology sequence, the **triple LES**
$$
  \cdots \to \widetilde H^k(C/B) \xrightarrow{j^*} \widetilde H^k(C/A) \xrightarrow{r^*} \widetilde H^k(B/A)
  \xrightarrow{\ \partial\ } \widetilde H^{k+1}(C/B) \to \cdots
  \tag{2.2}
$$
**Definition** (F13 Def. 2.1). $\partial_n := \partial$ for the triple $(A,B,C) = (\Delta_n,\Delta_{n+1},\Delta_{n+2})$ at $k = n-1$:
$$
  \partial_n \;:\; B_n = \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)
  \;\longrightarrow\; \widetilde H^n(\Delta_{n+2}/\Delta_{n+1}) = B_{n+1}.
$$
For $n=3$: $\partial_3 : B_3 = \widetilde H^2(\Delta_4/\Delta_3) \to \widetilde H^3(\Delta_5/\Delta_4) = B_4$, with $(A,B,C) = (\Delta_3,\Delta_4,\Delta_5)$, $k=2$.

F13 also records the **pair LES** of a good pair $(X,A)$:
$$
  \cdots \to \widetilde H^k(X/A) \xrightarrow{\ q\ } \widetilde H^k(X) \xrightarrow{\ \iota^*\ } \widetilde H^k(A)
  \xrightarrow{\ \delta\ } \widetilde H^{k+1}(X/A) \to \cdots
  \tag{2.3}
$$
with $q$ induced by the cochain inclusion $C^\bullet(X,A)\hookrightarrow C^\bullet(X)$, $\iota^*$ the restriction, and $\delta$ the connecting map. Write $q_n, \iota_n^*, \delta_n$ for the pair $(X,A) = (\Delta_{n+1},\Delta_n)$. **Note** (F13 §2, second remark): $\delta_n$ is the **pair** connecting map (of type $\widetilde H^k(\Delta_n)\to\widetilde H^{k+1}(\Delta_{n+1}/\Delta_n)$); it is the subject of (UCC.2). $\partial_n$ is the **triple** connecting map (of type $B_n \to B_{n+1}$). They are different maps with different domains — F13 deliberately did not relate them. **§3 relates them.**

---

## §3. The key lemma: $\partial_n = \delta_{n+1}\circ q_n$

This is the structural heart of F15. It is **standard homological algebra** — the well-known fact that a triple connecting map factors through a pair connecting map — written out at the cochain level in F13's conventions, so that nothing is assumed beyond the SES (2.1) and the definitions of $\partial$, $q$, $\delta$.

### 3.1 The cochain-level identity

**Lemma 3.1.** *For every $n$, with $\partial_n$, $q_n$, $\delta_{n+1}$ as in §2,*
$$
  \boxed{\ \partial_n \;=\; \delta_{n+1}\circ q_n \;:\;
  B_n = \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)
  \xrightarrow{\ q_n\ } \widetilde H^{n-1}(\Delta_{n+1})
  \xrightarrow{\ \delta_{n+1}\ } \widetilde H^n(\Delta_{n+2}/\Delta_{n+1}) = B_{n+1}.\ }
$$
*Here $q_n$ is the pair-LES map (2.3) of $(\Delta_{n+1},\Delta_n)$ at degree $n{-}1$, and $\delta_{n+1}$ is the pair-LES connecting map (2.3) of $(\Delta_{n+2},\Delta_{n+1})$ at degree $n{-}1$.*

*Proof.* Write $A,B,C = \Delta_n,\Delta_{n+1},\Delta_{n+2}$, $k = n-1$. Let $[\varphi]\in B_n = H^k(C^\bullet(B,A))$, $\varphi$ a cocycle in $C^k(B,A)$ — a $k$-cochain on $B$ with $\varphi|_A = 0$ and $d\varphi = 0$.

*Compute $\partial_n[\varphi]$ from the SES (2.1).* The connecting map: choose a preimage of $\varphi$ under $r$. Since $r$ is restriction $C^k(C,A)\to C^k(C,B)\dots$ — more precisely $r : C^k(C,A)\twoheadrightarrow C^k(B,A)$, $\psi \mapsto \psi|_B$ — a preimage is $\psi := $ ($\varphi$ extended by zero off $B$): $\psi\in C^k(C)$ with $\psi|_B = \varphi$ and $\psi$ vanishing on every simplex of $C$ not in $B$. Then $\psi|_A = \varphi|_A = 0$, so $\psi\in C^k(C,A)$, and $r(\psi) = \varphi$. Apply $d$: $r(d\psi) = d(r\psi) = d\varphi = 0$, so $d\psi \in \ker(r) = \mathrm{im}(j) = C^{k+1}(C,B)$, and $\partial_n[\varphi] = [d\psi] \in H^{k+1}(C^\bullet(C,B)) = B_{n+1}$.

*Compute $\delta_{n+1}(q_n[\varphi])$.* $q_n[\varphi] = [\varphi]\in\widetilde H^k(B)$: the map $q_n$ is induced by the cochain inclusion $C^\bullet(B,A)\hookrightarrow C^\bullet(B)$, i.e. it simply *forgets* that $\varphi$ vanishes on $A$ — the representing cocycle is the same $\varphi$, now viewed in $C^k(B)$. Now $\delta_{n+1}$ is the connecting map of the **pair** SES $0\to C^\bullet(C,B)\to C^\bullet(C)\xrightarrow{\mathrm{res}}C^\bullet(B)\to 0$. Its recipe on $[\varphi]\in\widetilde H^k(B)$: choose a preimage of $\varphi$ under restriction $C^k(C)\twoheadrightarrow C^k(B)$ — namely $\psi' := $ ($\varphi$ extended by zero off $B$) — then $\delta_{n+1}[\varphi] = [d\psi']$, and $d\psi'$ vanishes on $B$ (as $d\varphi=0$) so $d\psi'\in C^{k+1}(C,B)$.

But $\psi' = \psi$: both are "$\varphi$ extended by zero off $B$", the same cochain on $C$. Hence $d\psi' = d\psi$ and
$$
  \delta_{n+1}(q_n[\varphi]) \;=\; [d\psi'] \;=\; [d\psi] \;=\; \partial_n[\varphi]. \qquad\square
$$

The proof uses nothing but the definitions of the three maps and the fact that "extend by zero off $B$" is *simultaneously* a valid $r$-preimage (for the triple SES) and a valid restriction-preimage (for the pair SES) — because $A\subseteq B$, so a cochain vanishing off $B$ automatically vanishes on $A$. This is exactly why $A\subseteq B\subseteq C$ being *nested* makes the factorisation work.

### 3.2 Consequence

**Corollary 3.2.** $\mathrm{rank}(\partial_n) \le \mathrm{rank}(q_n) \le \dim\widetilde H^{n-1}(\Delta_{n+1})$, and $\mathrm{rank}(\partial_n) \le \dim\widetilde H^{n-1}(\Delta_{n+1})$. In particular, $\partial_n$ factors through the cohomology of the *single complex* $\Delta_{n+1}$ — not a cofiber.

This is the structural cap. Whatever $B_n$ and $B_{n+1}$ are, $\partial_n$ can have rank no larger than $\dim\widetilde H^{n-1}(\Delta_{n+1})$. For $\partial_n$ to be an isomorphism between $2$-dimensional spaces one needs $\dim\widetilde H^{n-1}(\Delta_{n+1})\ge 2$. §6 shows the program forces it to be exactly $1$.

---

## §4. Phase 1: $\partial_3$ has rank $1$ — the factorisation route

We instantiate Lemma 3.1 at $n=3$ and pin both legs. Everything in this section is computed or proven; nothing is conjectural.

### 4.1 The right leg: $q_3$ is surjective with $1$-dimensional kernel

Apply the pair LES (2.3) of $(\Delta_4,\Delta_3)$ around degree $2$:
$$
  \widetilde H^1(\Delta_4) \xrightarrow{\iota_3^*} \widetilde H^1(\Delta_3)
  \xrightarrow{\ \delta_3\ } \underbrace{\widetilde H^2(\Delta_4/\Delta_3)}_{B_3}
  \xrightarrow{\ q_3\ } \widetilde H^2(\Delta_4)
  \xrightarrow{\iota_3^*} \widetilde H^2(\Delta_3).
$$
The script (§[B]) computes, *directly and from scratch* (sparse mod-$p$ rank, two primes, every rank cross-checked):
$$
  \widetilde b_*(\Delta_3) = (0,1), \qquad
  \widetilde b_*(\Delta_4) = (0,0,1,0,0), \qquad
  \widetilde b_*(\Delta_4/\Delta_3) = (0,0,2,0,0).
$$
(The first two re-derive Hyp(3), Hyp(4); the third re-derives the mg-6295 / PCR-1 cofiber Betti vector — a trip-wire against an independently-known answer.) So the sequence reads, in dimensions,
$$
  \widetilde H^1(\Delta_4)=0 \to \widetilde H^1(\Delta_3)=1
  \xrightarrow{\delta_3} B_3 = 2 \xrightarrow{q_3} \widetilde H^2(\Delta_4)=1
  \xrightarrow{\iota_3^*} \widetilde H^2(\Delta_3)=0.
$$
Exactness then **forces every rank** with no induced-map computation:

- **At $\widetilde H^1(\Delta_3)$:** $\ker(\delta_3) = \mathrm{im}(\iota_3^* : \widetilde H^1(\Delta_4)\to\widetilde H^1(\Delta_3)) = 0$ (the source is $0$). So $\delta_3$ is **injective**, $\mathrm{rank}(\delta_3) = 1$. *(This recovers, purely from Betti numbers, the mg-59f3 result (UCC.2) at $n=3$ — $\delta_3$ injective. The script flags the agreement.)*
- **At $B_3$:** $\ker(q_3) = \mathrm{im}(\delta_3)$, which is $1$-dimensional. So $\mathrm{rank}(q_3) = \dim B_3 - 1 = 2 - 1 = 1$.
- **At $\widetilde H^2(\Delta_4)$:** $\ker(\iota_3^*) = \mathrm{im}(q_3)$, dimension $1 = \dim\widetilde H^2(\Delta_4)$. So $q_3$ is **surjective** and $\iota_3^* = 0$ (consistent with the target $\widetilde H^2(\Delta_3) = 0$).

> **$q_3 : B_3 \twoheadrightarrow \widetilde H^2(\Delta_4)$ is surjective, $\mathrm{rank}(q_3) = 1$, $\ker(q_3) = \mathrm{im}(\delta_3)$ is $1$-dimensional.**

This is non-circular: the Betti numbers are computed *directly* (independent of the LES); exactness of the pair LES is a theorem (no hypothesis); the conclusion is a finite linear-algebra deduction.

### 4.2 The left leg: $\delta_4$ is injective

Apply the pair LES (2.3) of $(\Delta_5,\Delta_4)$ around degree $2$:
$$
  \widetilde H^2(\Delta_5) \xrightarrow{\iota_4^*} \widetilde H^2(\Delta_4)
  \xrightarrow{\ \delta_4\ } \widetilde H^3(\Delta_5/\Delta_4) = B_4.
$$
By Hyp(5), $\widetilde H^*(\Delta_5)$ is concentrated in degree $3$, so $\widetilde H^2(\Delta_5) = 0$. Exactness at $\widetilde H^2(\Delta_4)$: $\ker(\delta_4) = \mathrm{im}(\iota_4^*) = 0$. So $\delta_4$ is **injective**, $\mathrm{rank}(\delta_4) = \dim\widetilde H^2(\Delta_4) = 1$.

This is exactly the LES F14 itself used: F14 doc §3.3, "the LES of the pair $(\Delta_5,\Delta_4)$ ... gives $0\to\mathrm{sgn}_{S_5}\to B_4\to\mathrm{sgn}_{S_4}\to 0$". The injection $\mathrm{sgn}_{S_4}\hookrightarrow B_4$ there *is* $\delta_4$. So this leg is not even a new input — it is a fact F14 already established and relied upon.

### 4.3 The conclusion

By Lemma 3.1, $\partial_3 = \delta_4\circ q_3$. Since $\delta_4$ is **injective** (§4.2), $\mathrm{rank}(\delta_4\circ q_3) = \mathrm{rank}(q_3)$. And $\mathrm{rank}(q_3) = 1$ (§4.1). Therefore

> **$\mathrm{rank}(\partial_3) = 1$.**

$\partial_3 : B_3 \to B_4$ is a linear map between two $2$-dimensional spaces with rank $1$: it is **not injective** ($1$-dimensional kernel), **not surjective** ($1$-dimensional cokernel), **not an isomorphism**. As a $2\times 2$ matrix in any bases, $\det(\partial_3) = 0$, rank $1$ — and "is it an isomorphism?" has answer **NO**, independently of the basis choice.

Concretely, the $2\times 2$ matrix is the rank-$1$ product
$$
  [\partial_3] \;=\; [\delta_4]\,[q_3] \;=\;
  \begin{pmatrix} \ast \\ \ast \end{pmatrix}_{\!2\times 1}
  \begin{pmatrix} \ast & \ast \end{pmatrix}_{\!1\times 2},
$$
where $[q_3]$ is a non-zero $1\times 2$ row (surjection onto the $1$-dimensional $\widetilde H^2(\Delta_4)$) and $[\delta_4]$ a non-zero $2\times 1$ column (injection of the $1$-dimensional $\widetilde H^2(\Delta_4)$ into $B_4$). Any rank-$1$ $2\times 2$ matrix arises this way; the precise entries depend on the chosen bases of $B_3$ (e.g. mg-6295's two critical $2$-cells) and $B_4$ (e.g. F14's $\{z_D,z_U\}$), but **rank and determinant — the only invariants the iso test needs — are basis-free, and they say: rank $1$, $\det = 0$, not an isomorphism.**

### 4.4 The precise structure of $\partial_3$

The factorisation gives more than the rank — it gives the kernel and image *exactly*:

- $\ker(\partial_3) = \ker(q_3) = \mathrm{im}(\delta_3)$ — the $1$-dimensional subspace of $B_3$ that is the image of the **pair** connecting map $\delta_3 : \widetilde H^1(\Delta_3)\to B_3$. This is precisely the (UCC.2) line: the "part of $B_3$ inherited from $\Delta_3$'s own cohomology." $\partial_3$ **annihilates exactly the inherited line.**
- $\mathrm{im}(\partial_3) = \delta_4(\mathrm{im}\,q_3) = \delta_4(\widetilde H^2(\Delta_4)) = \mathrm{im}(\delta_4) = \ker(\iota_4^*) \subset B_4$ — the $1$-dimensional subspace of $B_4$ that *is not seen by* $\iota_4^* : B_4\to\widetilde H^3(\Delta_5)$. (Cf. F14 §3.3's $0\to\mathrm{sgn}_{S_5}\to B_4\to\mathrm{sgn}_{S_4}\to 0$: $\mathrm{im}(\partial_3) = \mathrm{im}(\delta_4)$ is the $\mathrm{sgn}_{S_5}$ sub-line.)
- $\partial_3$ is **injective on the complementary line** $B_3 / \mathrm{im}(\delta_3) \cong \widetilde H^2(\Delta_4)$ — it carries that line isomorphically onto $\mathrm{im}(\delta_4)$.

So $\partial_3$ is not "randomly" rank-$1$: it is the specific rank-$1$ map that *quotients $B_3$ by its inherited line, then injects the quotient into $B_4$ as the un-restricted line.* This is the precise sense in which the degree-shift-aware object fails to be free at the base step (§6.4).

---

## §5. Cross-check: the triple LES of $(\Delta_3,\Delta_4,\Delta_5)$

An entirely independent derivation, not using the factorisation Lemma 3.1 at all — only exactness of the *triple* LES (2.2) and the Betti numbers.

**Step 1 — the double-cofiber cohomology.** $\widetilde H^*(\Delta_5/\Delta_3)$ is computed from the pair LES (2.3) of $(\Delta_5,\Delta_3)$:
$$
  \widetilde H^1(\Delta_5)=0 \to \widetilde H^1(\Delta_3)=1
  \xrightarrow{\delta} \widetilde H^2(\Delta_5/\Delta_3) \to \widetilde H^2(\Delta_5)=0
  \;\;\Rightarrow\;\; \widetilde H^2(\Delta_5/\Delta_3) = 1,
$$
$$
  \widetilde H^2(\Delta_3)=0 \to \widetilde H^3(\Delta_5/\Delta_3)
  \to \widetilde H^3(\Delta_5)=1 \to \widetilde H^3(\Delta_3)=0
  \;\;\Rightarrow\;\; \widetilde H^3(\Delta_5/\Delta_3) = 1.
$$
(Uses Hyp(3), Hyp(5) only.) **Remark.** F11 §4.4 flagged $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)$ — the "double-cofiber cohomology" — as "not known a priori". It *is* known: this pair-LES chase computes it from Hyp$(n)$, Hyp$(n{+}2)$. For $n=3$ it equals $\widetilde H^1(\Delta_3) = \mathrm{sgn}_{S_3}$ — and is **non-zero**. That non-vanishing is exactly the obstruction to $\partial_3$ injectivity (next step). F11's caution was warranted (it *is* real content) but its resolution is now in hand.

**Step 2 — the triple LES.** The triple LES (2.2) of $(\Delta_3\subset\Delta_4\subset\Delta_5)$, with $C/B=\Delta_5/\Delta_4$, $C/A=\Delta_5/\Delta_3$, $B/A=\Delta_4/\Delta_3$, around degree $2$:
$$
  \underbrace{\widetilde H^2(\Delta_5/\Delta_4)}_{0}
  \xrightarrow{j^*} \underbrace{\widetilde H^2(\Delta_5/\Delta_3)}_{1}
  \xrightarrow{r^*} \underbrace{\widetilde H^2(\Delta_4/\Delta_3)}_{B_3 = 2}
  \xrightarrow{\partial_3} \underbrace{\widetilde H^3(\Delta_5/\Delta_4)}_{B_4 = 2}
  \xrightarrow{j^*} \underbrace{\widetilde H^3(\Delta_5/\Delta_3)}_{1}
  \xrightarrow{r^*} \underbrace{\widetilde H^3(\Delta_4/\Delta_3)}_{0}.
$$
Dimensions: $0 \to 1 \to 2 \to 2 \to 1 \to 0$ ($\widetilde H^2(\Delta_5/\Delta_4)=0$ and $\widetilde H^3(\Delta_4/\Delta_3)=0$ from the F14 / script-§[B] Betti vectors). Exactness solves the rank recursion uniquely (for an exact sequence $V_0\to V_1\to\cdots$ with maps $f_i$: $\mathrm{rank}(f_{i-1}) + \mathrm{rank}(f_i) = \dim V_i$):
$$
  \mathrm{rank}(j^*_{\deg 2}) = 0,\quad
  \mathrm{rank}(r^*_{\deg 2}) = 1,\quad
  \boxed{\mathrm{rank}(\partial_3) = 1},\quad
  \mathrm{rank}(j^*_{\deg 3}) = 1,\quad
  \mathrm{rank}(r^*_{\deg 3}) = 0.
$$
In particular $\mathrm{rank}(\partial_3) = \dim B_3 - \mathrm{rank}(r^*_{\deg 2}) = 2 - 1 = 1$: the kernel of $\partial_3$ is the image of $r^*_{\deg 2}$, which is the (injective) image of the $1$-dimensional $\widetilde H^2(\Delta_5/\Delta_3)$. *(By naturality of the pair connecting map under the inclusion of pairs $(\Delta_4,\Delta_3)\hookrightarrow(\Delta_5,\Delta_3)$, $\mathrm{im}(r^*_{\deg 2}) = \mathrm{im}(\delta_3)$ — the §5 kernel and the §4.4 kernel coincide, as they must.)*

> **The triple-LES route and the factorisation route give the same answer: $\mathrm{rank}(\partial_3) = 1$.** Two independent derivations concur. The script asserts their agreement.

---

## §6. The general-$n$ diagnosis

The ticket directs: *if $\partial_3$ is not an isomorphism, STOP — Phase 2 (the iso-based general-$n$ argument) is moot.* It is. But the AMBER-partial3-not-iso verdict explicitly calls for *documenting precisely where/why the degree-shift-aware object is not free* — and Lemma 3.1 is **$n$-uniform**, so the diagnosis below costs nothing extra and is exactly that documentation. It is **not** Phase 2 (which was "assume $\partial_n$ iso, run the central-stability argument"); it is the Phase-1 fallout.

### 6.1 $\partial_n = \delta_{n+1}\circ q_n$ for all $n$, and what it forces

Lemma 3.1 holds verbatim for every triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$. Pin the two legs in general:

- **$q_n$.** Pair LES (2.3) of $(\Delta_{n+1},\Delta_n)$ at degree $n{-}1$: $\;\widetilde H^{n-2}(\Delta_n)\xrightarrow{\delta_n}B_n\xrightarrow{q_n}\widetilde H^{n-1}(\Delta_{n+1})\xrightarrow{\iota_n^*}\widetilde H^{n-1}(\Delta_n)$. Under **Hyp$(n)$**, $\widetilde H^{n-1}(\Delta_n)=0$, so $q_n$ is **surjective** with $\ker(q_n)=\mathrm{im}(\delta_n)$.
- **$\delta_{n+1}$.** Pair LES of $(\Delta_{n+2},\Delta_{n+1})$ at degree $n{-}1$: $\;\widetilde H^{n-1}(\Delta_{n+2})\xrightarrow{\iota_{n+1}^*}\widetilde H^{n-1}(\Delta_{n+1})\xrightarrow{\delta_{n+1}}B_{n+1}$. Under **Hyp$(n{+}2)$**, $\widetilde H^{n-1}(\Delta_{n+2})=0$, so $\delta_{n+1}$ is **injective**.

Hence, under Hyp$(n)$ and Hyp$(n{+}2)$:
$$
  \mathrm{rank}(\partial_n) \;=\; \mathrm{rank}(\delta_{n+1}\circ q_n)
  \;=\; \mathrm{rank}(q_n) \;=\; \dim\widetilde H^{n-1}(\Delta_{n+1}).
$$

### 6.2 The dichotomy: $\partial_n$ iso $\iff \delta_n = 0$

$\partial_n$ is an isomorphism between the $2$-dimensional $B_n$ and $B_{n+1}$ iff $\mathrm{rank}(\partial_n)=2$, i.e. (by §6.1) iff $\dim\widetilde H^{n-1}(\Delta_{n+1}) = 2$ **and** $q_n$ is injective. And $q_n$ injective $\iff \ker(q_n) = \mathrm{im}(\delta_n) = 0 \iff \delta_n = 0$ (the domain $\widetilde H^{n-2}(\Delta_n) = \mathrm{sgn}_{S_n}\ne 0$, so $\delta_n=0$ is the only way its image vanishes). If $\delta_n = 0$ then $q_n$ is injective *and* surjective, forcing $\dim\widetilde H^{n-1}(\Delta_{n+1}) = \dim B_n = 2$ automatically. So:

> **$\partial_n$ is an isomorphism $\;\iff\; \delta_n = 0$.**

### 6.3 Incompatibility with (UCC.2)

**(UCC.2)** at level $n$ is the statement that the **pair** connecting map $\delta_n : \widetilde H^{n-2}(\Delta_n) = \mathrm{sgn}_{S_n}\to B_n$ is **injective** (F10 §6.2; F11 §1.3; proven at $n=3$, mg-59f3). Injective with non-zero domain $\Rightarrow \delta_n\ne 0$. Combined with §6.2:

> **(UCC.2)$(n) \;\Longrightarrow\; \partial_n$ is *not* an isomorphism.** For every $n$.

So F11 §4.4's reduction — "(UCC.1)'s representation-type half $\Leftarrow$ $\partial_n$ iso for all $n$" — rests on a hypothesis that is **incompatible with (UCC.2)**, another component of the *same* master hypothesis (UCC) the program is establishing. The "$\partial_n$ iso" route cannot be made to work: proving it would *refute* (UCC.2), and (UCC.2) is true at $n=3$ (and is a program target for all $n$).

Equivalently and more vividly: under the program's own target **Hyp$(n{+}1)$** — $\widetilde H^*(\Delta_{n+1}) = \mathrm{sgn}_{S_{n+1}}$, concentrated in degree $(n{+}1)-2 = n-1$, hence $\widetilde H^{n-1}(\Delta_{n+1})$ is **$1$-dimensional** — Corollary 3.2 gives $\mathrm{rank}(\partial_n)\le 1 < 2$ for **all** $n$. $\partial_n$ factors through $\mathrm{sgn}_{S_{n+1}}$, a $1$-dimensional space; it is *structurally* incapable of being an isomorphism between $2$-dimensional spaces. F11 §4.4 already half-saw this: it observed "$\partial_n$ iso $\Leftrightarrow$ [a map] is zero, ... not a formality." The non-formality is real — and the answer is that the map in question is *never* zero, so $\partial_n$ is *never* iso.

### 6.4 Where the degree-shift-aware object is *not* free — precisely

The AMBER tag asks for the precise localisation. Here it is. The degree-shift-aware diagonal $((B_n)_n, \{\partial_n\})$ would be the free/induced object $M(0)^{\oplus 2}$ (F11 §4.5) exactly if every $\partial_n$ were an isomorphism — i.e. if the tower
$$
  B_3 \xrightarrow{\partial_3} B_4 \xrightarrow{\partial_4} B_5 \xrightarrow{\partial_5}\cdots
$$
were a tower of isomorphisms. It is not — and the failure is **uniform and exactly described**:

- Every $\partial_n$ has **rank exactly $1$** (under Hyp, §6.1 + §6.3): it is "half an isomorphism."
- Every $\partial_n$ **factors through $\widetilde H^{n-1}(\Delta_{n+1}) = \mathrm{sgn}_{S_{n+1}}$** — the cohomology of the single complex $\Delta_{n+1}$, *not* a cofiber.
- The kernel is $\ker(\partial_n) = \mathrm{im}(\delta_n)$ — the $\mathrm{sgn}_{S_n}$-line of $B_n$ *inherited* from $\Delta_n$'s cohomology via the pair connecting map.
- The image is $\mathrm{im}(\partial_n) = \mathrm{im}(\delta_{n+1}) = \ker(\iota_{n+1}^*)$ — the $\mathrm{sgn}$-line of $B_{n+1}$ *not restricted* to $\widetilde H^n(\Delta_{n+2})$.

In words: $B_n = 2\cdot\mathrm{sgn}_{S_n}$ splits (non-canonically, but with canonical *sub*) as $\mathrm{im}(\delta_n)\oplus(\text{complement})$, where $\mathrm{im}(\delta_n)$ is the "old" sgn-line and the complement maps isomorphically (via $q_n$) onto $\widetilde H^{n-1}(\Delta_{n+1})$. $\partial_n$ kills the old line and shifts the complement up. The degree-shift-aware object is therefore **not free** — but it is also not formless: it is a tower of rank-$1$ maps, each killing a $1$-dimensional "inherited" piece and injecting a $1$-dimensional "new" piece. That is a *bounded* amount of structure per step.

### 6.5 What this means for route (ii)

| route (ii) form | F15 verdict |
|---|---|
| **Simplest** (F11 §4.4–§4.5): every $\partial_n$ iso $\iff (\widetilde B_n)_n = M(0)^{\oplus 2}$ free | **DEAD.** $\partial_n$ has rank $1$, never $2$; incompatible with (UCC.2). |
| **Weaker / sufficient** (F11 §4.5 "minimally..."; Putman/Patzt): a *bounded central-stability presentation* — bounded generators + bounded relations, checkable from small-$n$ data | **NOT killed.** $\partial_n$ rank $1$ with kernel/image $1$-dimensional is *bounded* structure per step; the factorisation $\partial_n=\delta_{n+1}\circ q_n$ is a precise, $n$-uniform handle. A revised route (ii) targeting the bounded presentation — rather than freeness — is consistent with everything F15 found. |

The factorisation does not just *kill* the simplest form; it *supplies the input* for the weaker form. The structure maps of the degree-shift-aware object are now known explicitly ($\partial_n = \delta_{n+1}\circ q_n$, both pair-LES maps), $S_n$-equivariantly, $n$-uniformly. Whether $((B_n)_n,\{\partial_n\})$ admits a bounded central-stability presentation — a genuinely weaker and possibly-true statement — is the natural continuation, and is now a *better-posed* question than before F15. **But it is not in F15's scope** (the ticket scopes Phase 2 as the iso-based argument, which is moot) and it needs PM/Daniel direction (§7.3).

---

## §7. What F15 establishes and does not

### 7.1 Establishes

- **Lemma 3.1** ($\partial_n = \delta_{n+1}\circ q_n$): the triple connecting map of $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$ factors through the pair-LES maps $q_n$ and $\delta_{n+1}$. Standard homological algebra, written out in F13's cochain conventions; $n$-uniform; unconditional.
- **$\mathrm{rank}(\partial_3) = 1$ — $\partial_3$ is *not* an isomorphism.** Unconditional at $n=3$ (every input proven). Established twice: via the factorisation (§4) and via triple-LES exactness (§5).
- **The precise structure of $\partial_3$** (§4.4): $\ker(\partial_3) = \mathrm{im}(\delta_3)$ (the (UCC.2) line), $\mathrm{im}(\partial_3) = \mathrm{im}(\delta_4) = \ker(\iota_4^*)$.
- **$S_3$-equivariant refinement** (§4, script §[F]): $\widetilde H^1(\Delta_3) = \mathrm{sgn}_{S_3}$, $\widetilde H^2(\Delta_4) = \mathrm{sgn}_{S_4}$ ($\mathrm{sgn}_{S_3}$ restricted), $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ — all by direct Lefschetz character computation; $\partial_3$ is an $S_3$-map $2\cdot\mathrm{sgn}_{S_3}\to 2\cdot\mathrm{sgn}_{S_3}$ of rank $1$.
- **The general-$n$ diagnosis** (§6): $\partial_n$ iso $\iff\delta_n=0$ $\iff\neg$(UCC.2)$(n)$; under Hyp, $\mathrm{rank}(\partial_n)\le 1$ for all $n$. Route (ii)'s simplest form is dead, uniformly; the failure is exactly localised (§6.4).
- **Independent re-derivation** of Hyp(4), the mg-6295 cofiber Betti $(0,0,2,0)$, and (UCC.2) at $n=3$ — all fall out of the script's direct sparse-rank computation + exactness (a built-in trip-wire against known answers; all PASS).

### 7.2 Does NOT establish

- **The literal $2\times 2$ matrix entries** of $\partial_3$ in mg-6295's critical-$2$-cell basis of $B_3$ and F14's $\{z_D,z_U\}$ basis of $B_4$ are *not* tabulated. They are basis-dependent; rank and determinant — the only invariants the iso test needs — are basis-free and are computed (rank $1$, $\det 0$). The matrix *is* exhibited as the rank-$1$ product $[\delta_4][q_3]$ (§4.3). Tabulating entries would require reconstructing mg-6295's perfect Morse matching and F14's reduction dictionary to track cocycle representatives through both — substantial machinery for zero gain on the iso question. *(If a future ticket needs the entries — e.g. for a refined central-stability computation — that is a clean, scoped follow-up.)*
- **Route (ii)'s weaker form** — a bounded central-stability presentation — is **not** decided. It is not killed by F15 (§6.5), and the factorisation is the handle for it, but attempting it is out of F15's scope (the ticket scopes Phase 2 as the *iso-based* argument).
- **(UCC.1)'s concentration half** ("$M_{\mathrm{rel}}$ perfect", $B_n$ supported in one degree, $2$-dimensional) is untouched — that is M1's, orthogonal to $\partial_n$.
- **(UCC.2) for general $n$** is not proven — F15 *uses* (UCC.2) at $n=3$ (proven) and shows the *general* $\partial_n$ result is governed by (UCC.2)$(n)$.
- **Nothing about $n\ge 6$ cohomology is computed** — Hyp(5) and F14's $B_4$ are cited inputs; the $\Delta_5$ relative complex ($\approx 3.3\times 10^8$ cells) is not enumerated. The core $n=3$ result needs only the single cited fact $\widetilde H^2(\Delta_5) = 0$ (and that is a fact F14 already used).
- **No new axioms; no Lean changes.** Pure-Python computation + Markdown. The in-tree Lean $4$-axiom trust surface is untouched.

### 7.3 PM / Daniel decision input requested

Route (ii)'s simplest form is dead. Three options for the program; this is a PM/Daniel call, not a polecat call:

1. **Pursue route (ii)'s weaker form** — a bounded central-stability presentation for $((B_n)_n,\{\partial_n\})$, *not* freeness. Not killed by F15; the factorisation $\partial_n=\delta_{n+1}\circ q_n$ is the handle. This is the natural continuation and is internal/polecat-or-HPC-tractable. Recommended as the next ticket if route (ii) is to continue.
2. **Revisit route (iii)** — the F8'' Quillen-fiber identification (mg-b345), currently PARKED per Daniel. F11 §5 noted it stays parked "unless routes (i)+(ii) both stall." Route (i) is closed-negative (F11 §3); route (ii)'s *simplest* form is now dead — but its *weaker* form is live, so route (ii) has not fully stalled. A judgement call.
3. **Re-examine whether (UCC.1)'s rep-type half needs the degree-shift-aware object at all** — M1's equivariant cofiber-Morse (F11 §3.4) computes $B_n$'s representation type *directly* at each $n$ (F14 just did, for $n=4$, getting $2\cdot\mathrm{sgn}_{S_4}$); the open question is its $n$-uniformity, which is M1's "$M_{\mathrm{rel}}$ perfect + equivariant" — possibly a cleaner target than the $\partial_n$ tower.

F15's own recommendation (a polecat recommendation, for the PM to weigh): **option 1.** The weaker central-stability form is the honest survivor of route (ii), F15 has handed it a precise structural handle, and it is squarely in the "finish the induction internally" spirit.

---

## §8. Verdict

**AMBER-partial3-not-iso.**

$\partial_3 : B_3 \to B_4$ has rank exactly $1$ — **not an isomorphism**. Unconditional at $n=3$; established by two independent rigorous routes (the factorisation $\partial_3=\delta_4\circ q_3$, §4; triple-LES exactness, §5), with the script re-deriving every $\Delta_4$-resident Betti number from scratch. The result is structural, not a numerical accident: $\partial_3$ factors through the $1$-dimensional $\widetilde H^2(\Delta_4)$. The $n$-uniform factorisation $\partial_n = \delta_{n+1}\circ q_n$ gives the general-$n$ diagnosis: $\partial_n$ iso $\iff\delta_n=0\iff\neg$(UCC.2)$(n)$ — so F11 §4.4's "$\partial_n$ iso for all $n$" reduction is **incompatible with (UCC.2)**. Route (ii)'s **simplest form** ($(B_n)_n$ free $= M(0)^{\oplus 2}$) is **dead, uniformly**; its **weaker form** (a bounded central-stability presentation) is **not** killed, and the factorisation is its handle. Phase 2 (the iso-based general-$n$ argument) is moot and not executed; the general-$n$ *diagnosis* (§6) is delivered in its place — it pinpoints exactly where the degree-shift-aware object is not free (§6.4). **RED-computational-gap is excluded** ($\partial_3$ was constructible — indeed factorable — from F14's deliverables; no F14 re-scope needed). PM/Daniel decision input requested (§7.3).

**Trust-surface impact: none.** No new axioms, no Lean changes, no HPC. Pure-Python computation (runtime $\approx 1.5$ s) + Markdown.

---

## §9. References

### 9.1 Predecessor and sibling mg-tickets

- **mg-b352** — F11: attack on (FG-Cofiber). `11a75d6`; `docs/state-F11.md`. §4.2–§4.3 ($\partial_n$ identified as the triple connecting map; commutes with the co-FI-structure), §4.4 ("$\partial_n$ iso $\Rightarrow$ rep-type propagation"; "$\partial_n$ iso is genuinely open"), §4.5 (central stability, the $M(0)^{\oplus 2}$ picture, "minimally, the bounded presentation"), §4.6 (entry sub-problems (E1)/(E2)), §6.2 follow-up C. **Parent.**
- **mg-ecf6** — F13 (E1): functoriality of the degree-shift-aware object. **GREEN-functoriality-established** (verified before this writeup). `docs/compatibility-geometry-F13-shift-aware-functoriality.md`, `docs/state-F13.md`. §1 (FI-relabelling, the standard tower, good pairs), §2 (the triple LES (2.1)/(2.2), $\partial_n$ Def. 2.1, the $\partial_n$-vs-$\delta_n$ distinction), §3 (canonical extension). **F15 uses F13's conventions and §2 verbatim.**
- **mg-3839** — F14 (PCR-Lit-2′): the $n=4\to5$ cofiber cohomology. **GREEN-cofiber-perfect.** `docs/compatibility-geometry-F14-pcr-lit2prime.md`, `scripts/compat_geom_cofiber_morse_n4n5.py`, `docs/state-F14.md`. $B_4 = \widetilde H^3(\Delta_5/\Delta_4) = 2\cdot\mathrm{sgn}_{S_4}$, $\widetilde b_*(\Delta_5/\Delta_4) = (0,0,0,2,0)$; §3.3 the pair-LES cross-check $0\to\mathrm{sgn}_{S_5}\to B_4\to\mathrm{sgn}_{S_4}\to 0$ (the source of §4.2's $\delta_4$-injectivity). **Dependency.**
- **mg-6295** — PCR-Lit-2 (M1): Hersh–Welker discrete Morse on the cofiber $\Delta_4/\Delta_3$. `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`, `scripts/compat_geom_cofiber_morse_n3n4.py`. $B_3 = 2\cdot\mathrm{sgn}_{S_3}$, the perfect $M_{\mathrm{rel}}$ with critical vector $(0,0,2,0)$, the two critical $2$-cells. Poset/chain enumeration, sparse mod-$p$ rank, $S_3$ Lefschetz machinery — transcribed/adapted into `scripts/compat_geom_partial_3.py` (identical convention).
- **mg-59f3** — PCR-2: spectral $E_2$ page; $\delta_3^{\mathrm{sgn}}$ injective — (UCC.2) at $n=3$. **mg-f91f** — PCR-1: $n=4$ relative Betti $(0,0,2,0)$.
- **mg-8216** — F10: general-$n$ unified proof synthesis. `3c173df`. §6.2 (the cofiber-LES inductive step), §6.3 (UCC), §7.2 (FG-Cofiber sharpening, the three routes). Hyp$(n)$ verified $n\le 6$.

### 9.2 Mathematical literature

- A. Hatcher, *Algebraic Topology*, CUP (2002), §2.1–2.2 — the pair and triple long exact sequences; the connecting homomorphism; the standard factorisation of a triple connecting map through a pair connecting map (Lemma 3.1 is this fact, in cochains).
- C. Weibel, *An Introduction to Homological Algebra*, CUP (1994), Thm 1.3.1 — naturality of the connecting homomorphism of a SES of (co)chain complexes.
- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015); P. Patzt, *Central stability homology*, J. Topol. (2017+). Central stability — finite generation from a *bounded* presentation, no a priori finite ambient. The machinery route (ii)'s **weaker** form (§6.5, §7.3 option 1) would use.
- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015) — FI-modules, the free/induced object $M(0)$, the sign-twist.

### 9.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration.
- 2026-05-14T08:05Z — focus on the induction, not special cases. (F15 is the gating *mechanism* test of route (ii), not a fixed-$n$ datapoint hunt: it decides whether the "$\partial_n$ iso" general-$n$ mechanism is viable. The answer — no — is general-$n$ information, §6.)

---

*Polecat: mg-8355 (F15, E2). Branch: `compat-geom-F15-E2-partial-d3-iso`. Verdict: **AMBER-partial3-not-iso** — $\partial_3$ has rank $1$, not an isomorphism (unconditional at $n=3$; two independent derivations); the $n$-uniform factorisation $\partial_n=\delta_{n+1}\circ q_n$ shows $\partial_n$ iso $\iff\delta_n=0\iff\neg$(UCC.2), so route (ii)'s simplest form ($(B_n)_n$ free) is dead uniformly, while the weaker bounded-central-stability form survives and is handed a precise handle. No new axioms; no Lean changes. Cumulative state: `docs/state-F15.md`.*
