# Compat-Geom — F16: Route (ii) weaker form — the bounded central-stability presentation, and why it provably does not exist (mg-f893)

**Branch:** `compat-geom-F16-route-ii-weaker-central-stability` (new).
**Parent:** mg-8355 (F15, AMBER-partial3-not-iso) — `docs/compatibility-geometry-F15-e2-partial-test.md` §3 (Lemma 3.1, the factorisation $\partial_n=\delta_{n+1}\circ q_n$), §6.4–§6.5 (the per-step structure; the weaker form), §7.3 option 1/3.
**Chain:** mg-b352 (F11, GREEN-route-traction) → mg-ecf6 (F13, GREEN-functoriality-established) → mg-3839 (F14, GREEN-cofiber-perfect) → mg-8355 (F15, AMBER-partial3-not-iso).
**Type:** Structural argument (representation stability / central stability). LaTeX-style Markdown; **no new axioms; no Lean changes.** Multi-session-able; cumulative state ledger in `docs/state-F16.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: AMBER-route-ii-stalls** *(sub-case: the bounded presentation **provably does not exist**)*. The route (ii) weaker form — "the degree-shift-aware cofiber-cohomology object $((B_n)_n,\{\partial_n\})$ admits a **bounded central-stability presentation** (Putman 2015 / Patzt 2017)" — is **dead**. The reason is one line of homological algebra, unconditional and $n$-uniform: combining F15's factorisation $\partial_n=\delta_{n+1}\circ q_n$ (Lemma 3.1, unconditional) with exactness of the pair long exact sequence gives

$$\boxed{\ \partial_{n+1}\circ\partial_n \;=\; 0\quad\text{for all }n,\ \text{with no hypotheses.}\ }$$

The diagonal tower $B_3\xrightarrow{\partial_3}B_4\xrightarrow{\partial_4}B_5\to\cdots$ is therefore a **cochain complex**: consecutive structure maps annihilate. Under concentration — (UCC.1)'s concentration half, M1's deliverable, the half F16 was told to combine with — the $\mathcal C$-module $H$ collapses onto this diagonal (F13 Cor. 7.7(1)), so $\partial$ is the **only** degree-raising structure map. With $\partial^2=0$ and the only "up" map being $\partial$, no bounded set of generators can reach $B_n$ for large $n$: the **generation degree is unbounded**. A bounded central-stability presentation requires bounded generation degree (this is presentation-independent — it is a property of the indecomposables $\widetilde H_0(H)$). So no such presentation exists. F15 §6.4's "tower of rank-1 maps, bounded structure per step" is real — but "bounded **new** structure **per step**, forever" is exactly **unbounded total** generation, the opposite of what central stability needs. Route (ii) is not merely stalled; sharpened by (UCC.2) it is **circular** — its level-$n$ generator is precisely $\widetilde H^{n-1}(\Delta_{n+1})$, conjecturally $\mathrm{sgn}_{S_{n+1}}$, the canonical non-finitely-generated FI-module. The documented pivot (F15 §7.3 option 3 — M1 equivariant cofiber-Morse, representation type per $n$) is now the program's route to (UCC.1)'s representation-type half; route (iii) (mg-b345) returns to a PM/Daniel decision.

**Deliverables:**
- `docs/compatibility-geometry-F16-central-stability-presentation.md` (this doc).
- `docs/state-F16.md` (cumulative state ledger).
- `scripts/compat_geom_partial_squared.py` — verification harness: re-runs the F15 $n=3$ trip-wire; **verifies $q_3\circ\delta_3=0$ at the cochain level with explicit cocycle representatives** (the $n=3$ engine of $\partial^2=0$); re-derives $\delta_3$ injective ((UCC.2) at $n=3$); does the generation-degree bookkeeping. Pure-Python stdlib, runtime $\approx 18$ s.

---

## §0. Executive summary

### 0.1 The target — route (ii)'s weaker form

F11 (mg-b352) advanced route (ii) of (FG-Cofiber): the representation-type half of (UCC.1) reduces to a finite-generation statement about the **degree-shift-aware cofiber-cohomology object** $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$, where $B_n:=\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ and $\partial_n:B_n\to B_{n+1}$ is the connecting map of the triple $(\Delta_n\subset\Delta_{n+1}\subset\Delta_{n+2})$. F13 (mg-ecf6) made the framework rigorous: this data is a module $H$ over a precisely-defined functor category $\mathcal C$ ("$\mathrm{FI}^{\mathrm{op}}$ with a compatible degree-$(+1)$ shift"). F15 (mg-8355) killed route (ii)'s **simplest** form — "$H$ is the free object $M(0)^{\oplus2}$, i.e. every $\partial_n$ an isomorphism" — by proving $\partial_n$ has rank $\le 1$, never $2$, incompatibly with (UCC.2).

F15 §6.5 / §7.3 then handed F16 the **weaker** form: not freeness, but a **bounded central-stability presentation** — bounded generators $+$ bounded relations, checkable from small-$n$ data (Putman 2015, Patzt 2017). A bounded presentation gives finite generation *without* freeness; finite generation is (FG-Cofiber); (FG-Cofiber) closes (UCC.1)'s representation-type half for all $n$, and combined with M1's concentration half makes the F10 cohomological core unconditional. The F15 handle: the explicit $n$-uniform factorisation $\partial_n=\delta_{n+1}\circ q_n$, with the per-step structure (F15 §6.4) — $\ker\partial_n=\operatorname{im}\delta_n$, $\operatorname{im}\partial_n=\operatorname{im}\delta_{n+1}$ — "a tower of rank-1 maps, bounded structure per step."

### 0.2 The result

> **The weaker form is also dead. $((B_n)_n,\{\partial_n\})$ admits *no* bounded central-stability presentation — provably, not merely "out of internal reach."**

The argument is short and almost entirely unconditional.

**Step 1 — the unconditional lemma (§2).** F15's factorisation $\partial_n=\delta_{n+1}\circ q_n$ is unconditional (F15 Lemma 3.1, pure cochain algebra). The pair-LES maps $q_{n+1}$ and $\delta_{n+1}$ are **consecutive** maps in the (exact) pair long exact sequence of $(\Delta_{n+2},\Delta_{n+1})$, so $q_{n+1}\circ\delta_{n+1}=0$. Hence
$$\partial_{n+1}\circ\partial_n=\delta_{n+2}\circ(q_{n+1}\circ\delta_{n+1})\circ q_n=0,\qquad\text{for all }n,\ \text{unconditionally.}$$
The diagonal tower is a **cochain complex**. (F13 Prop. 6.1 had explicitly left $\partial$-composites "unconstrained" — F16 resolves this: they vanish.)

**Step 2 — collapse to the diagonal (§3.1).** Under **concentration** ((UCC.1)'s concentration half — $H^k_n=0$ for $k\ne n-1$, $\dim B_n=2$; M1's deliverable, proven $n\le6$, the half F16 is to combine with), F13 Cor. 7.7(1) collapses the $\mathcal C$-module $H$ onto its diagonal: the only non-zero spaces are the $B_n$, and the only structure maps are the $\partial_n$ (degree-raising) and the $S_n$-actions (degree-preserving). **$\partial$ is the only degree-raising structure map.**

**Step 3 — unbounded generation degree (§3).** The "generators" object of a $\mathcal C$-module — its indecomposables $\widetilde H_0(H)$, presentation-independent — has, under concentration, $\widetilde H_0(H)_n=B_n/\operatorname{im}(\partial_{n-1})$. With $\partial^2=0$ and $\dim B_n=2$: if $\widetilde H_0(H)_n=0$ then $\operatorname{im}\partial_n=\partial_n(\operatorname{im}\partial_{n-1})=0$, forcing $\widetilde H_0(H)_{n+1}=B_{n+1}\ne0$. So $\widetilde H_0(H)$ is non-zero for infinitely many $n$ — its **support is unbounded**.

**Step 4 — no bounded presentation (§4).** A bounded central-stability presentation requires $\widetilde H_0(H)$ supported in bounded degree. It is not. **QED — no bounded presentation.** Equivalently: under concentration, $H$ admits a bounded central-stability presentation **if and only if** $B_n=0$ for $n\gg0$ — which is false ($\dim B_n=2$, M1).

### 0.3 The (UCC.2) interaction — the load-bearing clarification

The ticket flags as load-bearing: does the presentation argument **need** (UCC.2), **produce** it, or is it **independent**? The answer:

> **Independent — and the argument never reaches (UCC.2).** The obstruction (§3) uses only $\partial^2=0$ (unconditional) and concentration ($\dim B_n=2$, M1's half). It does **not** use (UCC.2) ($\delta_n$ injective). (UCC.2) only **sharpens** the conclusion (§3.5, §5): *with* (UCC.2), $\widetilde H_0(H)_n$ is *exactly* $1$-dimensional for **every** $n$ — exactly one genuinely new generator per level, forever — and that generator is canonically $\widetilde H^{n-1}(\Delta_{n+1})$. The coarse failure (unbounded generation) happens before (UCC.2) is relevant; (UCC.2) makes the failure *precise and uniform*, not better. Route (ii)'s presentation argument neither needs nor produces (UCC.2): it **stalls upstream of it.**

This also pins down *why* route (ii) fails, not just *that* it does (§4.3): with (UCC.2)+concentration, $\widetilde H_0(H)_n\cong\widetilde H^{n-1}(\Delta_{n+1})$ — the level-$n$ generator of the degree-shift-aware object **is** the absolute cohomology of $\Delta_{n+1}$, conjecturally $\mathrm{sgn}_{S_{n+1}}$. So "route (ii) finite generation" would require $(\mathrm{sgn}_{S_{n+1}})_n$ to be a finitely generated FI-module — which is the **canonical non-example** (CEF 2015) and is *exactly* the difficulty the degree-shift framework was invented to circumvent. The circumvention does not happen: $\partial^2=0$ means the shift map cannot carry generators. **Route (ii) does not reduce (FG-Cofiber); it reproduces it.**

### 0.4 What this kills, what survives, the pivot

| | status after F16 |
|---|---|
| Route (ii), **simplest form** ($H=M(0)^{\oplus2}$, every $\partial_n$ iso) | **DEAD** (F15: $\partial_n$ rank $\le1$; F16 §2.3: $\partial^2=0$ gives a second, more elementary proof). |
| Route (ii), **weaker form** (bounded central-stability presentation) | **DEAD** (F16: $\partial^2=0$ $\Rightarrow$ unbounded generation degree $\Rightarrow$ no bounded presentation). The bounded presentation **provably does not exist.** |
| **Route (ii) as a whole** | **CLOSED — negative.** Both forms eliminated, for one clean structural reason: $\partial^2=0$. |
| F13's framework ($\mathcal C$, the $\mathcal C$-module $H$) | **Untouched and sound.** F16 *uses* F13; it resolves F13 Prop. 6.1's deliberately-open question ($\partial$-composites: they vanish). |
| (UCC.1) **concentration** half (M1, "$M_{\mathrm{rel}}$ perfect") | **Untouched** — F16 *assumes* it as input (§3.1), per the ticket. |
| (UCC.1) **representation-type** half — what F16 was after | **NOT closed by route (ii).** Returns to **option 3** (F15 §7.3): M1 equivariant cofiber-Morse, computing the representation type of $B_n$ directly per $n$ (as F14 did at $n=4$). |
| (UCC.2) for general $n$ | **Untouched** — F16 is independent of it (§5). |
| Route (iii) (mg-b345, PARKED) | Route (ii) has now **fully** stalled, so revisiting route (iii) is a **PM/Daniel decision** (F15 §7.3 anticipated exactly this trigger). |

**This is an AMBER with decisive, valuable content.** It is not "we could not find a presentation"; it is "we proved no bounded presentation exists, for a one-line structural reason, $n$-uniformly." It *closes* route (ii) cleanly (sparing further effort on a dead route, exactly as F11 §3.5's route-(i) closure did), resolves F13's open coherence question, gives a second proof that route (ii)'s simplest form is dead, and redirects the program to the documented pivot.

---

## §1. Setting and the object (recap)

**Notation** (F1-refined / F2 / F5 / mg-6295 / F13 §0). $[n]=\{0,\dots,n-1\}$. $\mathrm{PPF}_n$ is the poset of proper partial orders on $[n]$ (non-empty relation, non-total), ordered by refinement; $|\mathrm{PPF}_n|=12,194,4110,\dots$ at $n=3,4,5,\dots$. $\Delta_n:=\Delta(\mathrm{PPF}_n)$ its order complex. $\iota_n:\mathrm{PPF}_n\hookrightarrow\mathrm{PPF}_{n+1}$ the standard inclusion ($n$ incomparable to all of $[n]$) — an order-ideal inclusion, so $(\Delta_{n+1},\Delta_n)$ is a good pair (F13 Lemma 1.4). All (co)homology reduced, $\mathbb Q$-coefficients. F13's relative-cochain convention: $C^\bullet(X,A)=\{\varphi\in C^\bullet(X):\varphi|_A=0\}$.

**The object** (F11 §4.2, F13 §1.3, F15 §1):
$$B_n:=\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)\ \text{(the cofiber-cohomology diagonal)},\qquad
\partial_n:B_n\to B_{n+1}\ \text{(triple connecting map of }(\Delta_n,\Delta_{n+1},\Delta_{n+2})).$$
$B_3=2\cdot\mathrm{sgn}_{S_3}$ (mg-6295), $B_4=2\cdot\mathrm{sgn}_{S_4}$ (F14). $S_n$ acts on $B_n$ (it fixes the added points $n,n+1$).

**The framework** (F13). $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$ is the diagonal of a module $H$ over the **degree-shift-aware functor category** $\mathcal C$ (F13 Def. 7.1, Thm. 7.2, Thm. 7.4). Intrinsically: $H$ is a $\mathbb Z$-graded co-FI-module $H^\bullet=(H^k)_k$, $H^k_n=\widetilde H^k(\Delta_{n+1}/\Delta_n)$, equipped with co-FI-module morphisms $\partial^k:H^k\Rightarrow\Sigma^*H^{k+1}$ ($\Sigma^*$ = the FI-shift). The diagonal is $B_n=H^{n-1}_n$; $\partial_n=\partial_n^{n-1}$. "Finitely generated" is F13 Def. 7.6 (generated by bounded-degree elements under the structure maps $V$ and $\partial$).

**The factorisation handle** (F15 Lemma 3.1, **unconditional**). For every $n$,
$$\partial_n\;=\;\delta_{n+1}\circ q_n\;:\;B_n=\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)\xrightarrow{\ q_n\ }\widetilde H^{n-1}(\Delta_{n+1})\xrightarrow{\ \delta_{n+1}\ }\widetilde H^n(\Delta_{n+2}/\Delta_{n+1})=B_{n+1},$$
where $q_n$ is the pair-LES map of $(\Delta_{n+1},\Delta_n)$ at degree $n-1$ (induced by the cochain inclusion $C^\bullet(\Delta_{n+1},\Delta_n)\hookrightarrow C^\bullet(\Delta_{n+1})$), and $\delta_{n+1}$ is the pair-LES connecting map of $(\Delta_{n+2},\Delta_{n+1})$ at degree $n-1$. The proof (F15 §3.1) is that "extend a relative cocycle by zero off $\Delta_{n+1}$" is *simultaneously* a valid preimage for the triple SES and for the pair SES — it needs nothing but the definitions and the nesting $\Delta_n\subseteq\Delta_{n+1}\subseteq\Delta_{n+2}$.

**The pair LES** (F13 §2, eq. 2.3). For the good pair $(\Delta_{n+1},\Delta_n)$, the cochain SES $0\to C^\bullet(\Delta_{n+1},\Delta_n)\to C^\bullet(\Delta_{n+1})\xrightarrow{\mathrm{res}}C^\bullet(\Delta_n)\to0$ has the long exact cohomology sequence
$$\cdots\to\widetilde H^{k}(\Delta_{n+1}/\Delta_n)\xrightarrow{\ q_n^{k}\ }\widetilde H^{k}(\Delta_{n+1})\xrightarrow{\ \iota_n^*\ }\widetilde H^{k}(\Delta_n)\xrightarrow{\ \delta_n^{k}\ }\widetilde H^{k+1}(\Delta_{n+1}/\Delta_n)\to\cdots\tag{1.1}$$
**exact for every $n$ and every $k$, with no hypothesis** (standard; the LES of a SES of cochain complexes). We write $q_n:=q_n^{n-1}$, $\delta_n:=\delta_n^{n-2}$ for the diagonal-relevant instances, matching F15.

---

## §2. The unconditional lemma: $\partial_{n+1}\circ\partial_n=0$

This is the structural heart of F16, and it is short.

### 2.1 Statement

> **Lemma 2.1.** *For every $n$, $\partial_{n+1}\circ\partial_n=0$ as a map $B_n\to B_{n+2}$. The diagonal tower*
> $$B_3\xrightarrow{\ \partial_3\ }B_4\xrightarrow{\ \partial_4\ }B_5\xrightarrow{\ \partial_5\ }\cdots$$
> *is a cochain complex. The statement is unconditional and $n$-uniform — it uses no Hyp$(n)$, no (UCC), no concentration.*

### 2.2 Proof

By F15 Lemma 3.1 (unconditional), $\partial_n=\delta_{n+1}\circ q_n$ and $\partial_{n+1}=\delta_{n+2}\circ q_{n+1}$. Hence
$$\partial_{n+1}\circ\partial_n\;=\;\delta_{n+2}\circ q_{n+1}\circ\delta_{n+1}\circ q_n\;=\;\delta_{n+2}\circ\bigl(q_{n+1}\circ\delta_{n+1}\bigr)\circ q_n.$$
Now examine $q_{n+1}\circ\delta_{n+1}$. By F15 Lemma 3.1's own type-bookkeeping:
- $\delta_{n+1}$ is the pair-LES **connecting** map of $(\Delta_{n+2},\Delta_{n+1})$ **at degree $n-1$**: $\;\delta_{n+1}=\delta_{n+1}^{\,n-1}:\widetilde H^{n-1}(\Delta_{n+1})\to\widetilde H^n(\Delta_{n+2}/\Delta_{n+1})=B_{n+1}$.
- $q_{n+1}$ is the pair-LES map of $(\Delta_{n+2},\Delta_{n+1})$ **at degree $n$**: $\;q_{n+1}=q_{n+1}^{\,n}:\widetilde H^n(\Delta_{n+2}/\Delta_{n+1})\to\widetilde H^n(\Delta_{n+2})$.

So $\delta_{n+1}^{\,n-1}$ and $q_{n+1}^{\,n}$ are **consecutive maps in one and the same pair long exact sequence** — the LES (1.1) of the pair $(\Delta_{n+2},\Delta_{n+1})$:
$$\cdots\to\widetilde H^{n-1}(\Delta_{n+1})\xrightarrow{\ \delta_{n+1}^{\,n-1}\ }\underbrace{\widetilde H^{n}(\Delta_{n+2}/\Delta_{n+1})}_{=\,B_{n+1}}\xrightarrow{\ q_{n+1}^{\,n}\ }\widetilde H^{n}(\Delta_{n+2})\to\cdots$$
Exactness at $B_{n+1}$ gives $\operatorname{im}(\delta_{n+1}^{\,n-1})=\ker(q_{n+1}^{\,n})$, hence $q_{n+1}^{\,n}\circ\delta_{n+1}^{\,n-1}=0$. Therefore
$$\partial_{n+1}\circ\partial_n\;=\;\delta_{n+2}\circ\underbrace{\bigl(q_{n+1}\circ\delta_{n+1}\bigr)}_{=\,0}\circ q_n\;=\;0.\qquad\square$$

The proof invokes exactly two facts, both unconditional: F15's factorisation Lemma 3.1 (pure cochain algebra), and exactness of a pair long exact sequence (standard). It is $n$-uniform — the same two facts hold for every triple.

### 2.3 Remarks

**(a) F16 resolves F13 Prop. 6.1's deliberately-open question.** F13 Prop. 6.1 stated: "*No relation is imposed among the $\partial$'s: in particular $\partial_{n+1}\circ\partial_n$ is **not** required to vanish (and route (ii) §4.4 needs it not to — if each $\partial_n$ is an isomorphism then so is every composite).*" F13 was correct that *a priori* nothing in the $\mathcal C$-module *axioms* forces $\partial^2=0$ (free $\mathcal C$-modules have $\partial$ injective, $\partial^2\ne0$). But the *specific* $\mathcal C$-module $H$ coming from the cofiber cohomology of *these* nested complexes **does** satisfy $\partial^2=0$ — and for a reason internal to the geometry (the factorisation through pair-LES maps), not to the abstract category. F16 closes the question F13 left open.

**(b) A second, more elementary proof that route (ii)'s simplest form is dead.** F15 killed "every $\partial_n$ an isomorphism" via the (UCC.2) route ($\partial_n$ iso $\iff\delta_n=0\iff\neg$(UCC.2)). Lemma 2.1 gives an *independent* and *more elementary* proof: if every $\partial_n$ were an isomorphism then $\partial_{n+1}\circ\partial_n$ would be an isomorphism, in particular non-zero (each $B_n\ne0$); but $\partial_{n+1}\circ\partial_n=0$. So **not all $\partial_n$ can be isomorphisms** — using only Lemma 2.1, no reference to (UCC.2) at all. The two proofs are consistent and complementary: F15's identifies *which* $\partial_n$ fail to be iso and *why* (via (UCC.2)); F16's shows the failure is forced by the *complex* structure alone.

**(c) Consistency with F15 §6.4.** F15 §6.4 recorded (conditionally on Hyp) $\ker\partial_n=\operatorname{im}\delta_n$ and $\operatorname{im}\partial_n=\operatorname{im}\delta_{n+1}$. These give $\operatorname{im}\partial_n=\operatorname{im}\delta_{n+1}$ and $\ker\partial_{n+1}\supseteq\ker q_{n+1}=\operatorname{im}\delta_{n+1}$, so $\operatorname{im}\partial_n\subseteq\ker\partial_{n+1}$ — i.e. $\partial_{n+1}\circ\partial_n=0$. F15 had every ingredient; it did not connect them, because its scope (Phase 1: test $\partial_3$ for iso) did not call for the $\partial$-composite. F16's Lemma 2.1 makes the conclusion *unconditional* (it does not route through the conditional F15 §6.4 description — it uses only $q_{n+1}\circ\delta_{n+1}=0$, pure exactness) and draws the consequence.

### 2.4 The cochain-level transparency

The identity $q_{n+1}\circ\delta_{n+1}=0$ has a one-line cochain reading that makes Lemma 2.1 fully transparent and is what the companion script verifies explicitly at $n=3$. The connecting map $\delta_{n+1}$ of the pair $(\Delta_{n+2},\Delta_{n+1})$ applied to a class $[\varphi]\in\widetilde H^{n-1}(\Delta_{n+1})$ is computed by: extend $\varphi$ by zero off $\Delta_{n+1}$ to $\psi\in C^{n-1}(\Delta_{n+2})$, then $\delta_{n+1}[\varphi]=[d\psi]\in\widetilde H^n(\Delta_{n+2}/\Delta_{n+1})=B_{n+1}$. The pair-LES map $q_{n+1}$ then *forgets the relative structure* — it views the relative cocycle $d\psi$ as an absolute cochain on $\Delta_{n+2}$. But $d\psi$ is, in the absolute complex $C^\bullet(\Delta_{n+2})$, **an honest coboundary** — it is literally $d$ of $\psi$. So $q_{n+1}(\delta_{n+1}[\varphi])=[d\psi]=0$ in $\widetilde H^n(\Delta_{n+2})$. The same cochain $d\psi$ is a (generically non-trivial) *relative* class and a *trivial* absolute class; that gap is exactly $q\circ\delta=0$. The companion script (§7, `[C]`) exhibits this for $n=3$: it constructs an explicit $\varphi$ generating $\widetilde H^1(\Delta_3)$, forms $d\psi\in C^2(\Delta_4)$, and verifies (mod $p$, two primes) that $[d\psi]\ne0$ in $B_3$ (so $\delta_3$ is injective — re-deriving (UCC.2) at $n=3$) while $[d\psi]=0$ in $\widetilde H^2(\Delta_4)$ (so $q_3\circ\delta_3=0$).

---

## §3. The diagonal complex and its generation degree

### 3.1 Under concentration, $H$ collapses onto the diagonal complex

**Concentration** is (UCC.1)'s first half: $H^k_n=\widetilde H^k(\Delta_{n+1}/\Delta_n)=0$ for $k\ne n-1$, and $\dim B_n=2$ for all $n$ (M1's "$M_{\mathrm{rel}}$ perfect with critical vector $(0,\dots,0,2,0)$"). It is proven for $n\le6$, conjectured for all $n$, and is **M1's deliverable** — the "concentration half" the ticket instructs F16 to combine with. *It is logically independent of the representation-**type** half (whether $B_n$ is $2\,\mathrm{sgn}$ vs. $2\,\mathrm{triv}$ vs. $\mathrm{triv}\oplus\mathrm{sgn}$), which is the open thing route (ii) was meant to settle.* F16 assumes concentration and shows route (ii) cannot settle the type.

> **Proposition 3.1 (F13 Cor. 7.7(1)).** *Under concentration, the $\mathcal C$-module $H$ collapses onto its diagonal: the only non-zero spaces are the $B_n=H^{n-1}_n$, and the only non-zero structure maps are the $\partial_n:B_n\to B_{n+1}$ and the $S_n$-actions $B_n\to B_n$. In particular, $\partial$ is the only structure map that raises the FI-degree $n$.*

*Proof (F13 Cor. 7.7(1)).* A $V$-map $V(\hat f)^*:H^k_n\to H^k_m$ ($m\le n$) is non-zero only if $H^k_n\ne0$ and $H^k_m\ne0$, i.e. $k=n-1$ and $k=m-1$, forcing $m=n$, $f\in S_n$ — an $S_n$-action. A $\partial$-map $\partial^k_n:H^k_n\to H^{k+1}_{n+1}$ is non-zero only if $k=n-1$ (and then $k+1=(n+1)-1$ ✓), i.e. $\partial^k_n=\partial_n$. $V$-maps preserve $n$ ($S_n$-actions) or lower it; only $\partial$ raises it. $\square$

### 3.2 $\partial$-composites vanish — including interleaved with $V$

A path from $B_m$ to $B_n$ ($m<n$) through the $\mathcal C$-module structure is a composite of $V$-maps and $\partial$-maps. Under concentration (Prop. 3.1): every $V$-map in the composite is an $S$-action (degree-preserving), and the net FI-degree rise $n-m$ is achieved entirely by $\partial$-maps — so the composite contains exactly $n-m$ applications of $\partial$, interleaved with $S$-actions. Since $\partial$ is $S$-equivariant (F13 Thm. 5.3), the $S$-actions commute past the $\partial$'s up to sign, and the composite equals $\pm(S\text{-action})\circ\partial_{n-1}\circ\partial_{n-2}\circ\cdots\circ\partial_m$. By Lemma 2.1, $\partial_{j+1}\circ\partial_j=0$, so this composite is **$0$ whenever $n-m\ge2$**. The only non-trivial degree-raising composites are the single steps $\partial_{n-1}:B_{n-1}\to B_n$ (and their $S$-twists).

### 3.3 The generators object $\widetilde H_0(H)$

For a module over a category with a notion of "degree", the **generators object** (the indecomposables, or "$0$-th central-stability homology") is
$$\widetilde H_0(H)_x\;:=\;H_x\;\big/\;\sum_{\phi:\,y\to x\ \text{non-iso}}\operatorname{im}\bigl(H(\phi)\bigr),$$
the cokernel of all structure maps into $x$ from strictly lower degree. It is **presentation-independent** — it depends only on $H$, not on any chosen generators-and-relations. It measures "the generators genuinely needed at $x$". $H$ is generated in degree $\le g$ **iff** $\widetilde H_0(H)$ is supported in degrees $\le g$.

> **Proposition 3.2.** *Under concentration, on the diagonal $x=(n,n-1)$,*
> $$\widetilde H_0(H)_n\;=\;B_n\big/\operatorname{im}(\partial_{n-1}).$$

*Proof.* By Prop. 3.1 and §3.2, the structure maps into $B_n$ from strictly lower FI-degree, modulo $S_n$-actions (which are isomorphisms, excluded from the sum) and modulo $\partial$-composites of length $\ge2$ (which vanish, §3.2), reduce to the single map $\partial_{n-1}:B_{n-1}\to B_n$. (Off-diagonal $V$-maps into $B_n$ from $H^{n-1}_m$, $m>n$, are zero under concentration since $H^{n-1}_m=0$ for $m\ne n$.) $\square$

### 3.4 Theorem: the generation degree is unbounded

> **Theorem 3.3.** *Assume concentration. Then $\widetilde H_0(H)$ has unbounded support: for every $d$ there is an $n>d$ with $\widetilde H_0(H)_n\ne0$. Consequently the $\mathcal C$-module $H$ has unbounded generation degree.*

*Proof.* By Prop. 3.2, $\widetilde H_0(H)_n=B_n/\operatorname{im}(\partial_{n-1})$.

**Claim.** For every $n$: either $\widetilde H_0(H)_n\ne0$, or $\widetilde H_0(H)_{n+1}=B_{n+1}\ne0$.

Suppose $\widetilde H_0(H)_n=0$, i.e. $B_n=\operatorname{im}(\partial_{n-1})$. Then
$$\operatorname{im}(\partial_n)\;=\;\partial_n(B_n)\;=\;\partial_n\bigl(\operatorname{im}(\partial_{n-1})\bigr)\;=\;(\partial_n\circ\partial_{n-1})(B_{n-1})\;=\;0$$
by Lemma 2.1. Hence $\widetilde H_0(H)_{n+1}=B_{n+1}/\operatorname{im}(\partial_n)=B_{n+1}/0=B_{n+1}$, which is non-zero since $\dim B_{n+1}=2$ (concentration). This proves the Claim.

The Claim shows $\widetilde H_0(H)_n\ne0$ for at least every other $n$ — so for every $d$ there is an $n>d$ with $\widetilde H_0(H)_n\ne0$. Thus $\widetilde H_0(H)$ has unbounded support, and $H$ is not generated in any bounded degree. $\square$

### 3.5 The dichotomy, and the sharp form under (UCC.2)

**The dichotomy.** Theorem 3.3's Claim gives a clean equivalence. If $\widetilde H_0(H)_n=0$ for all $n>d$, then (by the Claim, contrapositive) $B_{n+1}=\widetilde H_0(H)_{n+1}=0$ for all $n>d$, i.e. $B_n=0$ for all $n>d+1$. So:
> **Under concentration: $H$ has bounded generation degree $\iff$ $B_n=0$ for all large $n$.**

And $B_n=0$ for large $n$ is **false** — $\dim B_n=2$ for all $n$ is part of M1's concentration deliverable (the critical vector is $(0,\dots,0,2,0)$, not $(0,\dots,0)$). So $H$ has unbounded generation degree, unconditionally given M1.

**The sharp form, with (UCC.2).** Assume additionally (UCC.2) ($\delta_n$ injective) and Hyp$(n)$ for the relevant range. Then $q_{n-1}$ is surjective (pair LES (1.1), $\widetilde H^{n-2}(\Delta_{n-1})=0$ under Hyp), so $\operatorname{im}(\partial_{n-1})=\operatorname{im}(\delta_n\circ q_{n-1})=\operatorname{im}(\delta_n)$, which is $1$-dimensional ((UCC.2): $\delta_n$ injective on the $1$-dimensional $\widetilde H^{n-2}(\Delta_n)=\mathrm{sgn}_{S_n}$). Hence
$$\dim\widetilde H_0(H)_n\;=\;\dim B_n-\dim\operatorname{im}(\partial_{n-1})\;=\;2-1\;=\;1\qquad\text{for \emph{every} }n.$$
**Exactly one genuinely new generator appears at every level, forever.** This is the precise, uniform form of F15 §6.4's "tower of rank-1 maps, bounded structure per step" — and it is exactly *unbounded total generation*. F15's "bounded *per step*" intuition is correct; the inference "good for central stability" is the error F16 corrects — central stability needs bounded *total* generators, and "$1$ new per step $\times\infty$ steps" $=\infty$.

---

## §4. Why central stability cannot run — the precise diagnosis

### 4.1 A bounded central-stability presentation requires bounded $\widetilde H_0$

Central stability (Putman 2015; Patzt 2017, *Central stability homology*) presents a module $M$ as the cokernel of a map $P_1\to P_0$ of **free/induced** modules whose generators live in **bounded degree**. The relevant finiteness invariants are the central-stability homology groups: $\widetilde H_0^{\mathrm{CS}}(M)$ — the **generators** — and $\widetilde H_1^{\mathrm{CS}}(M)$ — the **relations**. "$M$ has a bounded central-stability presentation" $\Rightarrow$ both are supported in bounded degree; in particular $\widetilde H_0^{\mathrm{CS}}(M)=\widetilde H_0(M)$ (the indecomposables of §3.3) is bounded.

This is the **non-negotiable, presentation-independent** part: $\widetilde H_0(M)$ is intrinsic to $M$. If $\widetilde H_0(M)$ is supported in unbounded degree, then **no** presentation — free or not, with any relations — can have bounded generators. (A bounded $P_0\twoheadrightarrow M$ would force $\widetilde H_0(M)$ bounded; the surjection factors through $\widetilde H_0(P_0)$, which is bounded by hypothesis, and $\widetilde H_0$ is right-exact.)

### 4.2 Corollary: no bounded central-stability presentation

> **Corollary 4.1.** *Assume concentration (M1's half). Then the degree-shift-aware cofiber-cohomology object $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$ — the $\mathcal C$-module $H$ — admits **no** bounded central-stability presentation. Route (ii)'s weaker form is dead.*

*Proof.* By Theorem 3.3, $\widetilde H_0(H)$ has unbounded support. By §4.1, a bounded central-stability presentation would force $\widetilde H_0(H)$ to have bounded support. Contradiction. $\square$

The same conclusion phrased via F13 Def. 7.6: $H$ is **not finitely generated** as a $\mathcal C$-module. F13 Cor. 7.7(2) said "$H$ f.g. in degree $\le d$ $\iff$ $\partial_{n-1}\circ\cdots\circ\partial_d:B_d\to B_n$ surjective for all $n>d$" — and by Lemma 2.1 those composites are *zero* for $n\ge d+2$, so the criterion fails for every $d$. (FG-Cofiber) is **not** provable by route (ii): the object route (ii) studies is genuinely, provably, not finitely generated.

### 4.3 The generators *are* the absolute cohomologies — route (ii) is circular

Corollary 4.1 says route (ii) *stalls*. The sharp form (§3.5) says *why* — and the "why" is worse than a stall: it is a **circularity**.

Under (UCC.2)+Hyp, $q_n$ is surjective and $\ker q_n=\operatorname{im}\delta_n=\operatorname{im}\partial_{n-1}$ (F15 §4.1, §6.4). Therefore
$$\widetilde H_0(H)_n\;=\;B_n/\operatorname{im}(\partial_{n-1})\;=\;B_n/\ker(q_n)\;\xrightarrow[\ \cong\ ]{\ q_n\ }\;\widetilde H^{n-1}(\Delta_{n+1}).$$
> **The level-$n$ generator of the degree-shift-aware cofiber-cohomology object is canonically the absolute cohomology $\widetilde H^{n-1}(\Delta_{n+1})$** — which, under the program's own target Hyp$(n+1)$, is $\mathrm{sgn}_{S_{n+1}}$.

So "route (ii): the $\mathcal C$-module $H$ is finitely generated" unwinds to: "the sequence of generators $\bigl(\widetilde H^{n-1}(\Delta_{n+1})\bigr)_n=(\mathrm{sgn}_{S_{n+1}})_n$ is boundedly generated." But $(\mathrm{sgn}_{S_n})_n$ is **the canonical non-finitely-generated FI-module** (Church–Ellenberg–Farb 2015) — and controlling it is *precisely the difficulty (FG-Cofiber) was posed to overcome*. The degree-shift-aware framework was invented (F10 §7.2.b, F11 §4) exactly to route around the degree-mismatch that makes $(\mathrm{sgn}_{S_n})_n$ intractable as a naive FI-module. Lemma 2.1 shows the routing-around does not happen: because $\partial^2=0$, the shift map $\partial$ **cannot carry a generator from one level to the next** — each level's $\mathrm{sgn}$-line is genuinely new, genuinely uncaptured. **Route (ii) does not reduce (FG-Cofiber); it reproduces it**, level by level, in the guise of $\widetilde H_0(H)$.

### 4.4 Contrast with route (i): both founder on the same rock

This is the same rock route (i) hit. F11 §3 closed route (i) (the chamber-quotient finite ambient) negatively because the chamber complex's cell count is super-exponential — *not* polynomially bounded — and a finitely generated FI-module has eventually-polynomial dimension; and because the rational chamber quotient is contractible, invisible to the $\mathrm{sgn}$-isotypic cohomology. The common cause: **$(\mathrm{sgn}_{S_n})_n$ is not a finitely generated FI-module**, and neither the chamber quotient (route i) nor the degree-shift $\partial$-tower (route ii) actually escapes that fact. F11 narrowed three routes to one (route ii); F16 closes that one. The effective internal route count for (FG-Cofiber)'s representation-type half is now: route (i) dead, route (ii) dead, route (iii) parked — see §7.

---

## §5. The (UCC.2) interaction — resolved

The ticket: *"Determine whether the central-stability presentation argument NEEDS (UCC.2) as input, or PRODUCES it, or is independent. This is load-bearing — clarify it explicitly."* Here is the explicit clarification.

**The argument is INDEPENDENT of (UCC.2), and stalls upstream of it.** Trace the dependencies:

| F16 step | what it uses | (UCC.2)? |
|---|---|---|
| Lemma 2.1 ($\partial^2=0$) | F15 Lemma 3.1 (unconditional) + pair-LES exactness (unconditional) | **no** |
| Prop. 3.1 (collapse to diagonal) | concentration (M1's half) | **no** |
| Prop. 3.2 ($\widetilde H_0(H)_n=B_n/\operatorname{im}\partial_{n-1}$) | Prop. 3.1 + Lemma 2.1 | **no** |
| Theorem 3.3 (unbounded generation) | Prop. 3.2 + Lemma 2.1 + $\dim B_n=2$ (M1) | **no** |
| Corollary 4.1 (no bounded presentation) | Theorem 3.3 + §4.1 | **no** |

The entire negative chain runs on $\partial^2=0$ (unconditional) and concentration ($\dim B_n=2$; M1's deliverable) — **(UCC.2) is never invoked.** The presentation argument does not *need* (UCC.2): it fails before (UCC.2) would be relevant.

**It does not PRODUCE (UCC.2) either.** A *successful* central-stability presentation might have produced (UCC.2) as a by-product (a bounded presentation pins all structure maps, $\delta_n$ included, from small-$n$ data). But the presentation does not exist — so it produces nothing. F16's actual output regarding (UCC.2) is orthogonal: the companion script *re-derives* (UCC.2) at $n=3$ (it verifies $\delta_3$ injective via the explicit cochain computation, §7 `[C]`) — but that is a re-confirmation of the known $n=3$ fact (mg-59f3), a trip-wire, not a general-$n$ production.

**(UCC.2) only SHARPENS the negative result (§3.5).** *Without* (UCC.2): Theorem 3.3 gives "$\widetilde H_0(H)$ unbounded support" (non-zero for at least every other $n$) — enough for Corollary 4.1. *With* (UCC.2)+Hyp: $\widetilde H_0(H)_n$ is *exactly* $1$-dimensional for *every* $n$, and is canonically $\widetilde H^{n-1}(\Delta_{n+1})$ (§4.3). So (UCC.2) upgrades "unbounded, somewhere" to "$1$ new generator at every single level, and we know exactly what it is." (UCC.2) makes the obstruction **precise, uniform, and identifiable** — it does not soften it. F15 §6.4's framing ("not free yet not formless — (UCC.2)-governed bounded structure per step — exactly the input central stability needs") had the structure right and the conclusion inverted: the (UCC.2)-governed structure is exactly the obstruction, made precise.

**Summary line for the ticket.** *The central-stability presentation argument is **independent** of (UCC.2): it needs only $\partial^2=0$ (unconditional) and concentration (M1). It neither needs nor produces (UCC.2). (UCC.2), when assumed, only sharpens the negative conclusion to "exactly one new, identifiable generator per level."*

---

## §6. What F16 establishes and does not establish

### 6.1 Establishes

- **Lemma 2.1** — $\partial_{n+1}\circ\partial_n=0$ for all $n$, **unconditional and $n$-uniform.** The diagonal tower is a cochain complex. Resolves F13 Prop. 6.1's deliberately-open question; gives a second, elementary proof that route (ii)'s simplest form is dead (§2.3).
- **Theorem 3.3 + Corollary 4.1** — under concentration (M1's half), the $\mathcal C$-module $H$ has **unbounded generation degree** and admits **no bounded central-stability presentation.** Route (ii)'s weaker form is dead. The bounded presentation *provably does not exist* (the strong AMBER sub-case).
- **The dichotomy (§3.5)** — under concentration, $H$ has bounded generation degree $\iff$ $B_n=0$ for $n\gg0$; the latter is false (M1).
- **The diagnosis (§4.3)** — under (UCC.2)+Hyp, $\widetilde H_0(H)_n\cong\widetilde H^{n-1}(\Delta_{n+1})$: route (ii)'s generators *are* the absolute cohomologies; route (ii) reproduces (FG-Cofiber) rather than reducing it. Route (i) and route (ii) founder on the same rock — $(\mathrm{sgn}_{S_n})_n$ not f.g. as an FI-module.
- **The (UCC.2) clarification (§5)** — the presentation argument is independent of (UCC.2); (UCC.2) only sharpens the negative conclusion.
- **Cochain-level verification (script `[C]`)** — $q_3\circ\delta_3=0$ exhibited with explicit cocycle representatives; $\delta_3$ injective ((UCC.2) at $n=3$) re-derived; the F15 $n=3$ trip-wire ($\dim B_3=2$, $\dim\widetilde H^2(\Delta_4)=1$) reproduced.

### 6.2 Does NOT establish

- **F16 does not prove (FG-Cofiber).** It proves route (ii) cannot. (FG-Cofiber) — (UCC.1)'s representation-type half — remains open; F15 §7.3 option 3 (M1 equivariant cofiber-Morse, per-$n$ representation type) is the surviving internal route. F16 does not attempt option 3 (per the ticket: "do not fan out preemptively").
- **F16 does not touch (UCC.1) concentration half.** It *assumes* it (M1's deliverable, proven $n\le6$) as input, per the ticket. The assumption is used only via "$H$ collapses onto the diagonal" + "$\dim B_n=2$".
- **F16 does not touch (UCC.2) for general $n$.** It is independent of it (§5); the companion script only re-confirms the known $n=3$ case.
- **F16 does not re-audit F15 or F13.** It *uses* F15 Lemma 3.1 (verified independently at the cochain level for $n=3$ by the companion script) and F13's framework. No RED-handle-fails: the F15 factorisation handle is sound and load-bearing — Lemma 2.1 is *built on* it. (The handle did exactly what F15 said it would; it just leads to a negative answer.)
- **The "without concentration" question.** Theorem 3.3 assumes concentration. Without concentration, the off-diagonal terms $H^k_n$ ($k\ne n-1$) exist, and $V$-$\partial$ interleaved composites could in principle propagate generators differently — the analysis would be more delicate. But concentration is **not in doubt**: it is M1's deliverable, proven $n\le6$, and is the half F16 is explicitly told to combine with. The *open* half is the representation type, which is irrelevant to the $\partial^2=0$ obstruction. So the assumption is exactly the intended regime, and the result is the intended combination "F16 $+$ M1-concentration".
- **No new axioms; no Lean changes.** Pure structural homological algebra + a stdlib verification script. The in-tree Lean 4-axiom trust surface is untouched.

---

## §7. Verdict, the pivot, and the route-(iii) decision

### 7.1 Verdict: AMBER-route-ii-stalls

Per the F16 verdict matrix: **AMBER-route-ii-stalls** — *"the weaker form also does not close; the bounded presentation provably does not exist."* This is the strong sub-case: not "out of internal reach" but **provably non-existent**, by Corollary 4.1, for the unconditional structural reason $\partial^2=0$ (Lemma 2.1).

It is not GREEN-bounded-presentation (the presentation does not exist) and not GREEN-partial (nothing of a presentation is "substantially developed" — there is provably nothing to develop). It is not RED-handle-fails: the F15 factorisation handle is sound and is *exactly* what powers Lemma 2.1. AMBER-route-ii-stalls is the honest tag, and — like F11's route-(i) closure — it is a **decisive, valuable** AMBER: route (ii) is *closed*, both forms eliminated for one clean reason, sparing the program further effort on a dead route.

### 7.2 The companion script

`scripts/compat_geom_partial_squared.py` (pure-Python stdlib, $\approx18$ s):
- `[A]` enumerates $\mathrm{PPF}_3,\mathrm{PPF}_4$, $\iota_3$, the relative cells — cardinalities/f-vectors match mg-6295/F15.
- `[B]` mod-$p$ ranks (two primes) of $d^1(\Delta_4)$, $d^1_{\mathrm{rel}}$, $d^2(\Delta_4)$ re-derive $\dim\widetilde H^2(\Delta_4)=1$ and $\dim B_3=2$ (light F15 trip-wire).
- `[C]` **the cochain-level check**: constructs an explicit $\varphi$ generating $\widetilde H^1(\Delta_3)$, forms $d\psi\in C^2(\Delta_4)$ (extend-by-zero, apply $d$), verifies $d\psi$ is a relative $2$-cocycle, that $[d\psi]\ne0$ in $B_3$ (so $\delta_3$ injective — (UCC.2) at $n=3$), and that $[d\psi]=0$ in $\widetilde H^2(\Delta_4)$ (so $q_3\circ\delta_3=0$). The $n=3$ engine of $\partial^2=0$, with explicit representatives.
- `[D]` records that $\partial_4\circ\partial_3=0$ reduces to $q_4\circ\delta_4=0$ — the same theorem one level up, no $\Delta_5$ needed.
- `[E]` the generation-degree bookkeeping (Theorem 3.3, §3.5).
- `[F]` verdict.

All assertions pass. The script is a harness — Lemma 2.1 and Corollary 4.1 are theorems, rigorous without computation — but `[C]` gives a genuine independent cochain-level confirmation of the load-bearing exactness identity.

### 7.3 The pivot — option 3

F15 §7.3 anticipated this exactly: *"If F16 stalls (AMBER-route-ii-stalls), option 3 becomes the next ticket."* **Option 3:** M1's equivariant cofiber-Morse computes the representation type of $B_n$ **directly per $n$** — F14 did exactly this at $n=4$ (getting $B_4=2\,\mathrm{sgn}_{S_4}$ by an $S_4$-equivariant order-ideal reduction). The open question becomes the $n$-uniformity of "$M_{\mathrm{rel}}$ perfect $+$ equivariant" — which is (UCC.1)'s concentration half *together with* equivariance, i.e. an upgrade of M1 rather than a new mechanism. This is the surviving internal route to (UCC.1)'s representation-type half. **F16 does not fan out to option 3** (per the ticket: "do not fan out preemptively") — it is the recommended next ticket.

### 7.4 Route (iii) — now a PM/Daniel decision

F11 §5 and F15 §7.3 both stated: route (iii) (mg-b345, the F8″ Quillen-fiber identification) stays PARKED *"unless routes (i)+(ii) both stall."* Route (i) was closed-negative by F11. **Route (ii) is now closed-negative by F16 — both forms.** So the condition F11/F15 named is met: revisiting route (iii) is now a genuine **PM/Daniel decision**. F16's recommendation (a polecat recommendation, for the PM to weigh): **prioritise option 3** — it is an upgrade of M1, which is already in flight and already succeeded at $n\le4$, and it is squarely "finish the induction internally"; route (iii) is Tier-3 specialist by F8″'s own grading and should be the fallback if option 3 also stalls.

### 7.5 Trust-surface impact

**None.** F16 introduces no new axioms, makes no Lean changes, runs no HPC. It is structural homological algebra (Lemma 2.1: F15 Lemma 3.1 $+$ pair-LES exactness; Theorem 3.3: F13 Cor. 7.7 $+$ Lemma 2.1) plus a pure-Python stdlib verification harness ($\approx18$ s). The in-tree Lean artifact `width3_one_third_two_thirds` (4-axiom trust surface) is untouched, as is the general-$n$ paper-level track.

---

## §8. References

### 8.1 Predecessor and sibling mg-tickets

- **mg-8355** — F15 (E2): the $\partial_3$ isomorphism test + the general-$n$ diagnosis. **AMBER-partial3-not-iso.** `docs/compatibility-geometry-F15-e2-partial-test.md`, `docs/state-F15.md`, `scripts/compat_geom_partial_3.py`. §3 (**Lemma 3.1**, the unconditional factorisation $\partial_n=\delta_{n+1}\circ q_n$ — F16's Lemma 2.1 is built on it), §4 ($\partial_3$ rank $1$), §6.4 (the per-step structure $\ker\partial_n=\operatorname{im}\delta_n$, $\operatorname{im}\partial_n=\operatorname{im}\delta_{n+1}$), §6.5 (route (ii)'s weaker form named), §7.3 (the options, incl. option 3 the F16 pivot). **Parent.**
- **mg-ecf6** — F13 (E1): functoriality of the degree-shift-aware object. **GREEN-functoriality-established.** `docs/compatibility-geometry-F13-shift-aware-functoriality.md`, `docs/state-F13.md`. §1–§2 (the FI-tower, the triple/pair LES conventions, the SES (2.1)), §7 (the category $\mathcal C$, Def. 7.1/Thm. 7.4; "finitely generated" Def. 7.6; **Cor. 7.7** — collapse onto the diagonal under concentration, the F11 §4.4 reduction recovered), **Prop. 6.1** ($\partial$-composites left "unconstrained" — **F16 §2.3 resolves this: they vanish**).
- **mg-3839** — F14 (PCR-Lit-2′): the $n=4\to5$ cofiber cohomology. **GREEN-cofiber-perfect.** `docs/compatibility-geometry-F14-pcr-lit2prime.md`. $B_4=\widetilde H^3(\Delta_5/\Delta_4)=2\,\mathrm{sgn}_{S_4}$; an $S_4$-equivariant order-ideal reduction — the template for option 3.
- **mg-b352** — F11: attack on (FG-Cofiber); routes (i)/(ii) survey. **GREEN-route-traction.** `docs/state-F11.md`. §3 (route (i) closed NEGATIVE — chamber quotient super-exponential, not f.g.; $(\mathrm{sgn}_{S_n})_n$ not f.g. — **the same rock route (ii) hits, §4.4**), §4 (route (ii): the $\partial_n$ identification, the "$\partial_n$ iso" reduction, central stability, entry sub-problems), §5 (route (iii) parked "unless routes (i)+(ii) both stall" — **now met**).
- **mg-8216** — F10: general-$n$ unified proof synthesis. **GREEN-conditional.** `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. §6.2–§6.3 (the cofiber-LES inductive step; **(UCC)** — (UCC.1) concentration+rep-type, (UCC.2) $\delta_n$ injective), §7.2 ((FG-Cofiber); the degree-shift-aware framework question; the three routes).
- **mg-6295** — PCR-Lit-2 / M1: discrete Morse on the cofiber. $B_3=2\,\mathrm{sgn}_{S_3}$, $M_{\mathrm{rel}}$ perfect critical vector $(0,0,2,0)$ — M1's concentration deliverable at $n=3$. **mg-59f3** — PCR-2: $\delta_3$ injective, (UCC.2) at $n=3$ — re-derived by the F16 companion script `[C]`. **mg-b345** — F8″: route (iii), PARKED — now a PM/Daniel decision (§7.4).

### 8.2 Mathematical literature

- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015); P. Patzt, *Central stability homology*, J. Topol. (2017+). Central stability — finite generation from a *bounded* presentation, no a priori finite ambient; the central-stability homology groups $\widetilde H_0^{\mathrm{CS}}$ (generators), $\widetilde H_1^{\mathrm{CS}}$ (relations). **The route (ii) weaker-form machinery — F16 shows its bounded-presentation hypothesis provably fails for $H$ (Cor. 4.1).**
- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015). Finitely generated FI-modules have eventually-polynomial dimension; **$(\mathrm{sgn}_{S_n})_n$ as the canonical non-finitely-generated FI-module** — the rock both route (i) (F11 §3) and route (ii) (F16 §4.3–§4.4) founder on.
- C. Weibel, *An Introduction to Homological Algebra*, CUP (1994), §1.3 — the long exact sequence of a SES of cochain complexes, and its exactness (the load-bearing fact behind $q_{n+1}\circ\delta_{n+1}=0$, Lemma 2.1).
- A. Hatcher, *Algebraic Topology*, CUP (2002), §2.1–§2.2 — the pair and triple long exact sequences; the factorisation of a triple connecting map through a pair connecting map (F15 Lemma 3.1).
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11 — order complexes, subcomplex pairs.

### 8.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (F16 is pure internal structural homological algebra; route (iii)/mg-b345 stays parked pending the PM/Daniel decision §7.4.)
- 2026-05-14T08:05Z — focus on the induction, not special cases. (F16 is the *general-$n$ mechanism* test of route (ii)'s weaker form — Lemma 2.1 and Cor. 4.1 are $n$-uniform; the $n=3$ script is a trip-wire, not a datapoint hunt. The answer — route (ii) is dead — is general-$n$ information.)

---

*Polecat: mg-f893 (F16). Branch: `compat-geom-F16-route-ii-weaker-central-stability`. Verdict: **AMBER-route-ii-stalls** — the bounded central-stability presentation for the degree-shift-aware cofiber-cohomology object $((B_n)_n,\{\partial_n\})$ **provably does not exist**. Unconditional core: $\partial_{n+1}\circ\partial_n=0$ for all $n$ (F15 Lemma 3.1 $+$ pair-LES exactness). Under concentration (M1's half), $\partial$ is the only degree-raising structure map and $\partial^2=0$ forces unbounded generation degree, hence no bounded presentation (Cor. 4.1). The presentation argument is **independent** of (UCC.2); (UCC.2) only sharpens the negative result to "exactly one new generator — canonically $\widetilde H^{n-1}(\Delta_{n+1})$ — per level". Route (ii) closed (both forms dead); pivot to F15 §7.3 option 3; route (iii) now a PM/Daniel decision. No new axioms; no Lean changes. Cumulative state: `docs/state-F16.md`.*
