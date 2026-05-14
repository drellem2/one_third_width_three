# Compat-Geom — F11: Attack on (FG-Cofiber) — internal routes (i)/(ii) survey + chamber-quotient entry point (mg-b352)

**Branch:** `compat-geom-F11-fg-cofiber-attack` (new).
**Parent:** mg-8216 (F10, GREEN-conditional, `3c173df`) — `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`.
**Type:** Scoping + initial attack. LaTeX-style Markdown; **no new axioms; no Lean changes; no new HPC; no new empirical $n$-datapoint** (per `feedback_focus_on_induction_not_special_cases`). Multi-session-able; cumulative state ledger in §8 of this file.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: GREEN-route-traction.** F10's central claims survive the mandatory trip-wire (§1 — all three PASS; RED-f10-gap excluded). The route survey then **closes route (i)** and **substantially advances route (ii)**:

- **Route (i) — "alternative finite ambient (chamber-quotient cochain complex)" — is closed NEGATIVE (§3).** The n-uniform-orbit-count question of F10 §7.2.d is answered: the $S_n$-orbit count of $\mathrm{PPF}_n$ is **not** n-uniformly bounded — it grows *super-exponentially* (rigorous, from the Kleitman–Rothschild asymptotic $|\mathrm{PPF}_n| = 2^{n^2/4 + o(n^2)}$ divided by $n!$; F5's data $2, 12, 61$ at $n=3,4,5$ is the leading edge). So the chamber-quotient cochain complex is **not** a finitely generated FI-module — super-exponential growth violates the polynomial-growth necessary condition. Worse, even granting finiteness it is the *wrong* object: the rational chamber quotient is **contractible** (F5.B — $\widetilde H^*(\Delta_n)$ lives in $\mathrm{sgn}_{S_n}$, invisible to the rational orbit-quotient), so it computes $0$, not the cohomology (FG-Cofiber) needs. Route (i)'s "finite ambient" form is dead; its only constructive residue — an $S_n$-*equivariant* chamber-Morse matching — **folds into M1**, not a separate route.
- **Route (ii) — "direct central-stability / Patzt-style presentation" — substantially advanced (§4).** F10 §7.2.b left open "identify the correct degree-shift-aware functor-category framework." F11 supplies the concrete missing ingredient: the correct degree-shift-$(+1)$ transition map on the cofiber-cohomology diagonal $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is the **triple connecting homomorphism** $\partial_n : B_n \to B_{n+1}$ of the triple $(\Delta_n \subset \Delta_{n+1} \subset \Delta_{n+2})$. It is natural, $S_n$-equivariant, degree-shifting, and **commutes with the fixed-degree co-FI-structure** (§4.3) — so $(B_n)_n$ with the maps $\{\partial_n\}$ and $\{V(f)^*\}$ is a genuine module over a degree-shift-aware functor category. And $\partial_n$ is *not* a formality: $\partial_n$ iso $\Longleftrightarrow$ $B_{n+1} = 2\cdot\mathrm{sgn}_{S_{n+1}}$ given $B_n = 2\cdot\mathrm{sgn}_{S_n}$ + concentration (§4.4) — so route (ii) reduces (UCC.1)'s representation-type half to "$\partial_n$ is an isomorphism for all $n$." The single most polecat-tractable entry sub-problem is identified (§4.6).

So **(FG-Cofiber) is closer**: three routes narrowed to one with a concrete handle; the F10 §7.2.b open framework question is partially resolved; a follow-up ticket is recommended (§6) — and route (i) is eliminated, sparing wasted effort.

---

## §0. What F11 is and is not

F10 (`3c173df`) reduced width-3 Kahn–Saks 1/3-2/3 at general $n$, **gap-free**, to the single master hypothesis **(UCC)** (F10 §6.3), itself sharpened (F10 §7.2.c) to the precise representation-stability statement:

> **(FG-Cofiber).** Identify the correct degree-shift-aware functor-category framework in which the cofiber-cohomology sequence $\bigl(\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)\bigr)_n$ is the diagonal of a **finitely generated** object, and prove that finite generation. Given finite generation, the $n=3$ computation + partial $n=4,5$ data pins the presentation degree, and Ramos 2017 yields (UCC) for all $n$.

F10 §7.2.d enumerates three viable internal routes to (FG-Cofiber):

- **(i)** Alternative finite ambient — a chamber-quotient cochain complex, finitely generated because the chamber complex is (F5's 61 orbits at $n=5$ — the *n-uniform-orbit-count question*).
- **(ii)** A direct central-stability / Patzt-style presentation argument for the cofiber cohomology.
- **(iii)** The F8'' Quillen-fiber identification of $X_n$ followed by a finite-generation argument for $(\Delta(X_n))_n$.

F11 attacks routes **(i)** and **(ii)** internally. **Route (iii) = mg-b345 is PARKED per Daniel — noted in §5, not pursued.** F11 produces no Lean changes, no new axioms, and runs no new computation: it is paper-and-pencil structural cohomology + the asymptotic-counting literature. The deliverable is this document.

Notation (from F10 §1.1 / M2 §1): $\mathrm{PPF}_n$ = proper partial orders on $\{0,\dots,n-1\}$ (non-empty, non-total), $\Delta_n = \Delta(\mathrm{PPF}_n)$ its order complex, $\iota_n : \mathrm{PPF}_n \hookrightarrow \mathrm{PPF}_{n+1}$ the standard inclusion ($n$ incomparable to all of $[n]$), $V(f)$ the FI-relabelling for an injection $f$. Cardinalities: $|\mathrm{PPF}_n| = 12, 194, 4110, 129302$ at $n = 3,4,5,6$.

---

## §1. Trip-wire: re-verification of F10's central claims (mandatory)

Per the F11 ticket, before any attack, F10's load-bearing claims were re-verified against `docs/general-n-proof-synthesis.md` (`3c173df`). **All three PASS; RED-f10-gap is excluded.**

### 1.1 (a) — the §6.2 inductive step is genuinely gap-free given (UCC)

Re-checked the cofiber long-exact-sequence diagram chase of F10 §6.2 line by line. The cohomology LES of the pair $(\Delta_{n+1}, \Delta_n)$ is
$$
\cdots \to \widetilde H^k(\Delta_{n+1}/\Delta_n) \to \widetilde H^k(\Delta_{n+1}) \xrightarrow{\iota_n^*} \widetilde H^k(\Delta_n) \xrightarrow{\delta_n} \widetilde H^{k+1}(\Delta_{n+1}/\Delta_n) \to \cdots
$$
— exact for every $n$, no hypothesis (standard). Assume $\mathrm{Hyp}(n)$, (UCC.1) [$\widetilde H^*(\Delta_{n+1}/\Delta_n) = 2\cdot\mathrm{sgn}_{S_n}$ concentrated in degree $n-1$], (UCC.2) [$\delta_n$ injective]:

- **$k \notin \{n-2,n-1\}$.** Both $\widetilde H^k(\Delta_{n+1}/\Delta_n) = 0$ (UCC.1) and $\widetilde H^k(\Delta_n) = 0$ ($\mathrm{Hyp}(n)$); the LES segment is $0 \to \widetilde H^k(\Delta_{n+1}) \to 0$, so $\widetilde H^k(\Delta_{n+1}) = 0$. ✓
- **$k = n-2$.** $\widetilde H^{n-2}(\Delta_{n+1}/\Delta_n) = 0$ (UCC.1), so $0 \to \widetilde H^{n-2}(\Delta_{n+1}) \xrightarrow{\iota_n^*} \widetilde H^{n-2}(\Delta_n) \xrightarrow{\delta_n} \cdots$; exactness gives $\iota_n^*$ injective with $\mathrm{im}(\iota_n^*) = \ker(\delta_n) = 0$ (UCC.2), so $\widetilde H^{n-2}(\Delta_{n+1}) = 0$. ✓
- **$k = n-1$.** $\widetilde H^{n-1}(\Delta_n) = 0$ ($\mathrm{Hyp}(n)$, $n-1 \ne n-2$), so $\widetilde H^{n-1}(\Delta_{n+1}) = \mathrm{coker}(\delta_n) = (2\cdot\mathrm{sgn}_{S_n})/\delta_n(\mathrm{sgn}_{S_n})$; $\delta_n$ injective + $\mathrm{sgn}_{S_n}$ $1$-dimensional $\Rightarrow$ $\mathrm{coker}$ is $1$-dimensional, $\cong \mathrm{sgn}_{S_n}$ as $S_n$-rep. ✓

The promotion $S_n \rightsquigarrow S_{n+1}$: $\widetilde H^{n-1}(\Delta_{n+1})$ is $1$-dimensional, so as an $S_{n+1}$-rep it is $\mathrm{triv}_{S_{n+1}}$ or $\mathrm{sgn}_{S_{n+1}}$; restriction to $S_n$ gives $\mathrm{sgn}_{S_n}$, and only $\mathrm{sgn}_{S_{n+1}}|_{S_n} = \mathrm{sgn}_{S_n}$ — so it is $\mathrm{sgn}_{S_{n+1}}$. This is $\mathrm{Hyp}(n+1)$. **No hand-wave, no unfilled hole — the step is gap-free given (UCC).** **(a) PASS.**

### 1.2 (b) — M1 and M2 both reduce to (UCC) as F10 §6.4 claims

- **M1 $\to$ (UCC).** Re-checked against mg-6295 (`f169345`). The downward-closed-subcomplex lemma (mg-6295 §6.1) — "$M_A$ acyclic on subcomplex $A$, $M_{X\setminus A}$ acyclic on relative cells $\Rightarrow M_A \sqcup M_{X\setminus A}$ acyclic on $X$" — has a proof that is **manifestly $n$-independent** (no directed edge leaves $A$ since $A$ is downward-closed; a periodic cycle is confined to $A$ or to $X\setminus A$). So M1 supplies, n-uniformly, an acyclic cofiber matching $M_{\mathrm{rel}}$ with $\mathrm{crit}_k(M_{\mathrm{rel}}) \ge \dim\widetilde H^k(\Delta_{n+1}/\Delta_n)$. (UCC.1) is precisely "$M_{\mathrm{rel}}$ perfect, critical vector $(0,\dots,0,2,0)$ in degree $n-1$"; (UCC.2) is precisely "the cross-boundary Forman cancellation succeeds." M1 reduces the cohomological core to (UCC). ✓
- **M2 $\to$ (UCC).** Re-checked against mg-759d (`e5d9b08`). M2 supplies the base data $D_n = \mathrm{sgn}_{S_n}$ at $n=3,4,5,6$ and the Ramos-2017 template (presentation degree $\le d$ $\Rightarrow$ determined by values at indices $\le d$). The cofiber-cohomology sequence's finite generation at low presentation degree forces (UCC.1)+(UCC.2) for all $n$ from small-$n$ data. M2 reduces the cohomological core to (FG-Cofiber) $\Rightarrow$ (UCC). ✓

Two a priori unrelated machineries (discrete Morse on cofibers; FI-module finite generation) terminate at the *same* statement (UCC). **(b) PASS** — RED-mechanism-gap excluded, exactly as F10 §6.4 claims.

### 1.3 (c) — (UCC) at $n=3\to4$ is unconditionally proven (F10 §6.5)

- **(UCC.1) at level $n=3$.** mg-6295 §3.2/§4/§5: the cofiber matching $M_{\mathrm{rel}}$ for $\Delta_4/\Delta_3$ is **perfect** with critical vector $(0,0,2,0)$ — concentrated in degree $2$, $2$-dimensional; the $2$ critical $2$-cells generate $\widetilde H^2(\Delta_4/\Delta_3) = 2\cdot\mathrm{sgn}_{S_3}$ (Lefschetz character computation, mg-6295 §5, reproducing mg-59f3 §3.4 $m_{X/A}^{\mathrm{sgn}} = 2$). ✓
- **(UCC.2) at level $n=3$.** mg-59f3 §4: the connecting map $\delta_3^{\mathrm{sgn}}$ is injective, with $\omega_{\mathrm{bal}}^{(4)} = \mathrm{coker}(\delta_3)$ on the sgn-isotype — the $(m_A, m_X, m_{X/A})^{\mathrm{sgn}} = (1,1,2)$ pattern; cross-validated by mg-6295 §7. ✓

So (UCC) at $n=3$ is proven, not assumed; the cohomological core is rigorous at $n=3\to4$ unconditionally. **(c) PASS.**

### 1.4 Trip-wire verdict

**All three trip-wires PASS.** F10's GREEN-conditional verdict survives: the §6 proof skeleton is genuinely gap-free modulo (UCC) alone, and (FG-Cofiber) is the honest precise form of (UCC). F11 proceeds to the route survey. *(RED-f10-gap would have stopped F11 here; it does not.)*

---

## §2. The target restated, and the shape of the survey

(FG-Cofiber) has two halves, both of which F11's survey must keep distinct:

1. **The framework half.** Identify the functor category in which the diagonal $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is the diagonal of a single coherent object — in particular, identify the *transition maps* that respect the degree shift $k = n-1 \rightsquigarrow k+1 = n$. F10 §7.2.a established what the maps are **not**: the FI-pullback maps $V(f)^*$ are degree-*preserving*, so on the diagonal they are forced to zero by degree mismatch (the absolute diagonal $D_n = \widetilde H^{n-2}(\Delta_n)$ "does not carry a naive co-FI-module structure"). F10 §7.2.b noted the fixed-degree co-FI-module $(\widetilde H^k(\Delta_{n+1}/\Delta_n))_n$ exists for each fixed $k$, but "the relevant degree $k=n-1$ shifts with $n$" — leaving the framework question open.
2. **The finiteness half.** Prove the resulting object is finitely generated. F10 §7.2.d: the natural finite ambient (the relative cochain complex $C^*(\Delta_{n+1},\Delta_n)$) is **not** f.g. — its dimension is super-exponential — so the CEF/Patzt–Putman subquotient-Noetherianity criterion does **not** apply off-the-shelf.

Route **(i)** attacks the finiteness half by proposing a *smaller* ambient (the chamber quotient). Route **(ii)** attacks the framework half directly via a central-stability presentation. §3 and §4 take them in turn.

---

## §3. Route (i) — chamber-quotient finite ambient: ATTACK on the n-uniform-orbit-count question

### 3.1 What route (i) proposes

F10 §7.2.d, route (i): *"an alternative finite ambient (e.g. a chamber-quotient cochain complex, finitely generated because the chamber complex is — F5's 61 orbits at $n=5$ is the n-uniform-orbit-count question)."*

The idea: the relative cochain complex $C^*(\Delta_{n+1},\Delta_n)$ is super-exponentially large, hence not a finitely generated FI-module. But the $S_n$-action on $\mathrm{PPF}_n$ collapses it; the **chamber complex** $\Delta(C_n) := \Delta(\mathrm{PPF}_n / S_n)$ — the order complex of the orbit poset — is far smaller (F5: $61$ orbit-vertices at $n=5$, $f$-vector total $352{,}947$ cells). If the orbit count were *n-uniformly bounded* (or even polynomially bounded), the chamber-quotient cochain complex would be a finitely generated ambient, and Noetherianity could be applied to a subquotient.

The **entry sub-problem** route (i) reduces (FG-Cofiber) to is therefore exactly the F11 deliverable-3 question:

> **(n-uniform-orbit-count).** Is the $S_n$-orbit count of $\mathrm{PPF}_n$ — equivalently, the cell count of the chamber complex $\Delta(C_n)$ — n-uniformly bounded, or at least polynomially bounded in $n$? And does the chamber-quotient cochain complex give a finitely generated FI-module ambient to which CEF / Patzt–Putman Noetherianity applies?

F11 attacks this directly. It is paper-and-pencil tractable — no HPC required — because the answer is governed by a known asymptotic.

### 3.2 The orbit count is provably NOT n-uniformly bounded — it is super-exponential

The cardinality $|\mathrm{PPF}_n|$ is pinned to the labeled-poset count $a(n) := |\{\text{partial orders on } [n]\}|$ (OEIS **A001035**: $a(n) = 1, 1, 3, 19, 219, 4231, 130023, 6129859, \dots$ for $n = 0,1,2,\dots$). By the F1-refined / M2 convention $\mathrm{PPF}_n = \mathbf{Pos}_n^{\mathrm{sub}} \setminus \{\widehat 0\} \setminus \{\text{total orders}\}$:
$$
  |\mathrm{PPF}_n| \;=\; a(n) - 1 - n!.
$$
Check: $a(3)-1-6 = 19-1-6 = 12$; $a(4)-1-24 = 219-1-24 = 194$; $a(5)-1-120 = 4231-1-120 = 4110$; $a(6)-1-720 = 130023-1-720 = 129302$ — all four match the established cardinalities exactly.

**Kleitman–Rothschild (1975).** The number of labeled partial orders on $n$ points satisfies
$$
  \log_2 a(n) \;=\; \tfrac{n^2}{4} + \tfrac{3n}{2} + O(\log n), \qquad\text{i.e.}\qquad a(n) = 2^{\,n^2/4 + o(n^2)}.
$$
Hence $|\mathrm{PPF}_n| = 2^{\,n^2/4 + o(n^2)}$ as well (the $-1-n!$ correction is negligible: $n! = 2^{n\log_2 n + o(n\log n)}$ is dominated by $2^{n^2/4}$).

**The orbit count.** By Burnside, the number of $S_n$-orbits of $\mathrm{PPF}_n$ is $\frac{1}{n!}\sum_{\sigma\in S_n}|\mathrm{Fix}(\sigma)| \ge \frac{|\mathrm{PPF}_n|}{n!}$ (each orbit has size $\le n!$). Therefore
$$
  \#\bigl(\mathrm{PPF}_n / S_n\bigr) \;\ge\; \frac{|\mathrm{PPF}_n|}{n!} \;=\; 2^{\,n^2/4 - n\log_2 n + o(n^2)} \;\xrightarrow[n\to\infty]{}\; \infty
$$
**super-exponentially** — faster than $2^{cn}$ for *every* constant $c$, because the exponent $\tfrac{n^2}{4} - n\log_2 n$ is $\Theta(n^2)$.

This is consistent with — and explains — F5's data $2, 12, 61$ at $n = 3,4,5$ (and the lower bound $|\mathrm{PPF}_6|/6! = 129302/720 \approx 180$ at $n=6$): the orbit count is already growing faster than any geometric rate, and the asymptotic guarantees it never stops. **The answer to the n-uniform-orbit-count question is: NO. The chamber complex's cell count is not n-uniformly bounded, not polynomially bounded — it is super-exponential in $n$.** F5 itself flagged this in spirit (it *corrected* the naive $|\mathrm{PPF}_n|/n!$ estimate and treated each $n$ as a separate Burnside computation, asserting no growth law); F11 makes the negative answer rigorous via the Kleitman–Rothschild bound.

**Consequence for finite generation.** A finitely generated FI-module over a field has $\dim V_n$ *eventually polynomial* in $n$ (Church–Ellenberg–Farb 2015). The chamber-quotient cochain groups have dimension equal to the orbit counts of $k$-chains, which inherit the super-exponential growth of the underlying poset count. **So the chamber-quotient cochain complex is NOT a finitely generated FI-module** — it fails the polynomial-growth necessary condition, by exactly the same mechanism (super-exponential growth) that disqualifies the un-quotiented relative cochain complex (F10 §7.2.d). Passing to the orbit quotient buys a constant-factor-per-$n$ shrinkage ($\div n!$); it does **not** change the growth *class*. Route (i)'s premise — "finitely generated because the chamber complex is" — is false: the chamber complex is finite *at each $n$* (so is $C^*(\Delta_n)$), but its size is unbounded *in $n$* at a rate incompatible with f.g.

### 3.3 Second, independent obstruction: the rational chamber quotient is contractible

Even setting growth aside, the chamber quotient is the **wrong object** — it does not see the cohomology (FG-Cofiber) needs.

For a finite group $G$ acting on a finite complex, $\widetilde H^*(\,|{\cdot}|/G;\mathbb Q) = \widetilde H^*(\,|{\cdot}|;\mathbb Q)^G$ (rational transfer). For $\Delta_n$ with the $S_n$-action: by $\mathrm{Hyp}(n)$ (verified $n = 3,4,5,6$; conjectural beyond, but that is precisely the regime under study),
$$
  \widetilde H^*(\Delta_n/S_n;\mathbb Q) \;=\; \widetilde H^*(\Delta_n;\mathbb Q)^{S_n} \;=\; (\mathrm{sgn}_{S_n})^{S_n} \;=\; 0 .
$$
The chamber quotient is **rationally acyclic** — exactly F5's headline structural finding **(F5.B)**: $\widetilde\chi(\Delta(C_5)) = 0$ (vs. $\widetilde\chi(\Delta_5) = -1$), because "the cohomology of $\Delta_5$ lives in the sign representation of $S_5$, which is invisible to the rational orbit-quotient." The same computation applies to the **cofiber** quotient: $\widetilde H^*\bigl((\Delta_{n+1}/\Delta_n)/S_n;\mathbb Q\bigr) = \widetilde H^*(\Delta_{n+1}/\Delta_n;\mathbb Q)^{S_n} = (2\cdot\mathrm{sgn}_{S_n})^{S_n} = 0$ (using the (UCC.1) representation type, proven at $n=3$).

So the chamber-quotient cochain complex — even if it were finite/f.g. — computes $0$, not $B_n$. It is rationally invisible to *exactly* the sgn-isotypic cohomology that (FG-Cofiber) is about. Route (i) as a "finite ambient computing the cofiber cohomology" is doubly dead: the ambient is neither finitely generated **nor** does it compute the target.

### 3.4 The salvageable residue, and why it is not a separate route

The honest constructive content one *can* extract from the chamber idea is the **$S_n$-equivariant** version: instead of the rational quotient (which kills the sgn-class), work with the chamber complex carrying the **sign local system** — equivalently, the sgn-isotypic component $C^*(\Delta_n)^{\mathrm{sgn}}$ of the equivariant cochain complex. This *does* compute $\widetilde H^*(\Delta_n) = \mathrm{sgn}_{S_n}$, since the cohomology is entirely sgn-isotypic. F5 §3.3 calls this the "twisted chamber" picture and explicitly describes it as requiring "an $S_n$-equivariant matching on $\Delta_n$ that respects the sign-representation grading."

But (a) $\dim C^k(\Delta_n)^{\mathrm{sgn}}$ is the signed orbit count $\frac{1}{n!}\sum_\sigma \mathrm{sgn}(\sigma)|\mathrm{Fix}(\sigma)|$, still generically of order $\dim C^k(\Delta_n)/n!$ — **still super-exponential**, so still not a finite f.g. ambient; and (b) constructing the equivariant sign-respecting matching is *precisely* the program M1 already runs — an acyclic discrete Morse matching on the cofiber. The "equivariant chamber-Morse" refinement (F5 §3.3, F6, and mg-6295 §8.2's noted "natural further sub-ticket: an equivariant cofiber-Morse matching") is the discrete-Morse face of (UCC), i.e. **M1**, not a third independent ambient.

**Conclusion: route (i)'s constructive residue folds into M1.** It is not a separate route to (FG-Cofiber). The effective route count is therefore **two** — M1's equivariant cofiber Morse (subsuming the chamber idea) and route (ii)'s central-stability presentation — plus the parked route (iii).

### 3.5 Route (i) verdict

**Route (i) is closed NEGATIVE.** The n-uniform-orbit-count question is answered rigorously: the chamber complex's cell count grows super-exponentially in $n$ (Kleitman–Rothschild), so the chamber-quotient cochain complex is **not** a finitely generated FI-module; and the rational chamber quotient is contractible, so it does not compute the cofiber cohomology at all. There is no finite ambient here. This is a definitive, valuable elimination — it tells the program not to spend effort building chamber-quotient ambients, and redirects to route (ii). The only constructive residue (an equivariant sign-respecting Morse matching) is M1, already in flight.

---

## §4. Route (ii) — central-stability / Patzt-style presentation: survey + entry-point identification

### 4.1 What route (ii) proposes

F10 §7.2.d, route (ii): *"a direct central-stability / Patzt-style presentation argument for the cofiber cohomology."* Central stability (Putman 2015; Patzt 2017, "central stability homology") is a finite-generation technique that does **not** require an a priori finite ambient: a module is centrally stable if it is the cokernel of a map between "induced"/free FI-modules whose generators and relations live in *bounded* degree — and bounded generation + bounded relations is checkable from small-$n$ data. This is the natural tool once route (i)'s finite-ambient hope is dead (§3): it attacks the **framework half** of (FG-Cofiber) head-on.

For route (ii) to even be stated, one must first answer F10 §7.2.b's open question: *what are the transition maps?* F11's substantive contribution is here.

### 4.2 The correct degree-shift-aware transition map: the triple connecting homomorphism

Write $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ — the cofiber-cohomology diagonal, the object (FG-Cofiber) is about. F10 established: $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ (proven; mg-6295/mg-59f3), and (UCC.1) conjectures $B_n = 2\cdot\mathrm{sgn}_{S_n}$ concentrated in degree $n-1$ for all $n$.

The fixed-degree co-FI-structure (F10 §7.2.b) gives, for an injection $f:[m]\hookrightarrow[n]$ extended to $\hat f:[m{+}1]\hookrightarrow[n{+}1]$ with $\hat f(m)=n$, maps $V(\hat f)^* : \widetilde H^k(\Delta_{n+1}/\Delta_n) \to \widetilde H^k(\Delta_{m+1}/\Delta_m)$ — but these are **degree-preserving**, so on the diagonal ($k = n-1$ vs. $k = m-1$, $m < n$) they land in $\widetilde H^{n-1}(\Delta_{m+1}/\Delta_m) = 0$ and carry no information. This is F10 §7.2.a's degree-mismatch obstruction, transcribed to the cofiber.

**The missing ingredient — F11's identification.** The transition map that *does* respect the degree shift is the **connecting homomorphism of the triple** $(\Delta_n \subset \Delta_{n+1} \subset \Delta_{n+2})$. The cohomology long exact sequence of this triple reads
$$
  \cdots \to \widetilde H^k(\Delta_{n+2}/\Delta_{n+1}) \to \widetilde H^k(\Delta_{n+2}/\Delta_n) \to \widetilde H^k(\Delta_{n+1}/\Delta_n) \xrightarrow{\ \partial\ } \widetilde H^{k+1}(\Delta_{n+2}/\Delta_{n+1}) \to \cdots
$$
(standard; exact for every $n$). Its connecting map $\partial$ shifts cohomological degree by **$+1$**. Taking $k = n-1$:
$$
  \boxed{\;\partial_n \;:\; B_n \;=\; \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n) \;\longrightarrow\; \widetilde H^{n}(\Delta_{n+2}/\Delta_{n+1}) \;=\; B_{n+1}.\;}
$$
This is the natural, canonical, degree-shift-aware map relating consecutive entries of the diagonal. It is **$S_n$-equivariant**: $S_n$ (fixing the points $n, n+1$) acts on the entire triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$, hence on the triple LES, hence commutes with $\partial_n$; $B_n$ is an $S_n$-rep and $B_{n+1}$ is an $S_{n+1}$-rep restricted along $S_n \hookrightarrow S_{n+1}$, so $\partial_n$ has exactly the variance of an FI-module structure map for the standard inclusion $[n]\hookrightarrow[n+1]$.

This is the concrete content F10 §7.2.b left open ("the FI-module assembled from the relative cohomology sequence with the cofiber-induced transition maps" — F10 named the existence of "cofiber-induced transition maps" but did not identify them; $\partial_n$ is them).

### 4.3 $\partial_n$ commutes with the fixed-degree co-FI-structure — the combined object

A general injection $f:[m]\hookrightarrow[n]$ extends canonically to $\tilde f:[m{+}2]\hookrightarrow[n{+}2]$ by $\tilde f|_{[m]} = f$, $\tilde f(m) = n$, $\tilde f(m{+}1) = n{+}1$. The relabelling $V(\tilde f)$ then maps the triple $(\Delta_m,\Delta_{m+1},\Delta_{m+2})$ into $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$: a poset with element $m{+}1$ (resp. $m$) isolated maps to one with $n{+}1$ (resp. $n$) isolated, so $V(\tilde f)$ carries $\Delta_{m+1}\to\Delta_{n+1}$ and $\Delta_m\to\Delta_n$ — it is a **map of triples**. Naturality of the triple connecting homomorphism then gives a commuting square (with the contravariant variance of cohomology):
$$
\begin{array}{ccc}
B_n & \xrightarrow{\ \partial_n\ } & B_{n+1} \\[2pt]
{\scriptstyle V(\tilde f)^*}\big\downarrow & & \big\downarrow{\scriptstyle V(\tilde f)^*} \\[2pt]
B_m & \xrightarrow{\ \partial_m\ } & B_{m+1}
\end{array}
$$
So $(B_n)_n$ carries **two compatible structures**: the degree-preserving co-FI-pullbacks $\{V(f)^*\}$ and the degree-shifting connecting maps $\{\partial_n\}$, and they commute. This is exactly a module over a *degree-shift-aware functor category* — concretely, $\mathrm{FI}^{\mathrm{op}}$ enriched with a compatible shift endomorphism, the structure F10 §7.2.b/c asked to be identified. The diagonal $(B_n)_n$ with the maps $\partial_n$ going *up* in $n$ is the part on which "finitely generated" should mean "generated by $B_{\le d}$ under $\partial$-composites and $V$-maps."

*(Caveat, honestly flagged. The diagram above is the standard naturality of the triple LES; what still needs a careful written proof is choice-independence — that $V(\tilde f)^*$ on cofiber cohomology is independent of the extension $\hat f \rightsquigarrow \tilde f$ — and the full functoriality across composites of all injections, not just the standard inclusion. The fixed-degree co-FI-structure (F10 §7.2.b) presumably already handles the degree-preserving half; the shift half is new. This is **entry sub-problem (E1)** below — paper-and-pencil, polecat-tractable, standard homological algebra, started here and to be completed in the follow-up.)*

### 4.4 $\partial_n$ is not a formality: iso $\Longrightarrow$ representation-type propagation

The crux observation that makes route (ii) substantive. Suppose $B_n = 2\cdot\mathrm{sgn}_{S_n}$ and $B_{n+1}$ is concentrated in degree $n$ and $2$-dimensional (the concentration half of (UCC.1) at level $n+1$). Then:

> **Claim.** If $\partial_n : B_n \to B_{n+1}$ is an isomorphism, then $B_{n+1} = 2\cdot\mathrm{sgn}_{S_{n+1}}$.

*Proof.* $\partial_n$ is $S_n$-equivariant, so $\partial_n$ iso $\Rightarrow$ $B_{n+1} \cong 2\cdot\mathrm{sgn}_{S_n}$ as $S_n$-representations, i.e. $\mathrm{Res}^{S_{n+1}}_{S_n} B_{n+1} = 2\cdot\mathrm{sgn}_{S_n}$. Now $B_{n+1}$ is a $2$-dimensional $S_{n+1}$-representation. For $n{+}1 \ge 4$, $S_{n+1}$ has no $2$-dimensional irreducible (the smallest non-trivial irreducible is the $(n)$-dimensional standard representation), so $B_{n+1}$ is a sum of two $1$-dimensionals — i.e. one of $\mathrm{triv}^{\oplus 2}$, $\mathrm{triv}\oplus\mathrm{sgn}$, $\mathrm{sgn}^{\oplus 2}$. Restricting to $S_n$ these give $2\cdot\mathrm{triv}$, $\mathrm{triv}\oplus\mathrm{sgn}$, $2\cdot\mathrm{sgn}$ respectively. Only the last matches; so $B_{n+1} = 2\cdot\mathrm{sgn}_{S_{n+1}}$. $\square$

Combined with the verified base $B_3 = 2\cdot\mathrm{sgn}_{S_3}$, an induction gives:

> **Reduction.** *If $\partial_n$ is an isomorphism for every $n \ge 3$ (and each $B_{n+1}$ is concentrated, $2$-dimensional), then $B_n = 2\cdot\mathrm{sgn}_{S_n}$ for all $n$* — the representation-type half of **(UCC.1)** for all $n$.

So route (ii)'s framework, once set up, **reduces (UCC.1)'s representation-type statement to a single uniform statement: "$\partial_n$ is an isomorphism for all $n$."** And $\partial_n$ iso is genuinely open content, not a formality — from the triple LES, $\partial_n$ injective $\Longleftrightarrow$ the map $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n) \to \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is zero, and $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)$ (cohomology of a *double* cofiber) is **not** known a priori; assuming it vanishes is assuming a piece of (UCC) itself, so the argument is non-circular and the computation is real.

*(What this does and does not give. It cleanly handles the **representation-type propagation** of (UCC.1). It does **not** by itself give the **concentration** half of (UCC.1) — that $B_{n+1}$ is supported in a single degree and $2$-dimensional — which remains M1's "$M_{\mathrm{rel}}$ perfect"; nor does it directly give **(UCC.2)** $\delta_n$-injectivity, which is the *pair* connecting map, distinct from the *triple* map $\partial_n$, and would need a parallel analysis. Route (ii) is a route to the representation-stability face of (UCC), as F10 §6.4 framed M2 — not a standalone closure.)*

### 4.5 Connection to central stability and the sgn-twist

Apply the mandatory sign-twist (M2 §5.3, standard for top cohomology of $S_n$-equivariant order complexes): $\widetilde B_n := B_n \otimes \mathrm{sgn}_{S_n}$. If $B_n = 2\cdot\mathrm{sgn}_{S_n}$ then $\widetilde B_n = 2\cdot\mathrm{triv}_{S_n}$, and the transposition-forced-zero obstruction of M2 §5.2 vanishes (transpositions act trivially on $\widetilde B_n$, so the shift maps $\widetilde\partial_n := \partial_n\otimes\mathrm{sgn}$ are *not* forced to zero). The candidate structural statement becomes:

> $(\widetilde B_n)_n$ with the shift maps $\widetilde\partial_n$ is the free/induced FI-module $M(0)^{\oplus 2}$ — generated in degree $0$, no relations, **presentation degree $0$** — *if and only if* every $\widetilde\partial_n$ is an isomorphism.

This is the cleanest sufficient condition for finite generation, and it is exactly the M2 "presentation degree $0$" picture (mg-759d §6) made precise on the *correct degree-shift-aware object* rather than the naive diagonal. More weakly, **central stability** (Putman/Patzt) only needs the presentation — generators and relations — to live in *bounded* degree; here, generation in degree $3$ (if $\partial_3$ surjects, propagated) plus relations in bounded degree would suffice, and Patzt's central-stability-homology criterion is checkable from small-$n$ data without a finite ambient. Route (ii) thus reduces (FG-Cofiber) to:

> **(FG-Cofiber-ii).** The degree-shift-aware object $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$ is finitely generated — sufficiently, the shift maps $\partial_n$ are isomorphisms for all $n \ge 3$ (equivalently $(\widetilde B_n)_n = M(0)^{\oplus 2}$); minimally, the central-stability presentation is bounded.

### 4.6 The entry sub-problems — and the single most polecat-tractable one

Route (ii) decomposes into two entry sub-problems:

- **(E1) — Functoriality of the degree-shift-aware object.** Write out rigorously that $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$ is a genuine module over the degree-shift-aware functor category: the commuting square of §4.3 for *all* injections (not only the standard inclusion), choice-independence of the cofiber relabelling, and compatibility of $\partial$-composites. This is **paper-and-pencil, no HPC, polecat-class** — it is standard homological algebra (naturality of the triple LES + the FI-functoriality already partly established for the fixed-degree co-FI-module in F10 §7.2.b / M2 §4). F11 has sketched it (§4.2–§4.3); a focused follow-up completes it. **This is the single most polecat-tractable entry sub-problem** — it is the prerequisite for everything else in route (ii) and needs no new computation.
- **(E2) — Compute $\partial_3 : B_3 \to B_4$.** Once $B_4 = \widetilde H^3(\Delta_5/\Delta_4)$ is known, $\partial_3$ is a single concrete $S_3$-equivariant linear map between two known $2$-dimensional spaces ($B_3 = 2\cdot\mathrm{sgn}_{S_3}$ with explicit basis = the two critical $2$-cells of mg-6295's $M_{\mathrm{rel}}$); testing it for injectivity/isomorphism is a $2\times2$-matrix computation. **Blocker:** $B_4 = \widetilde H^3(\Delta_5/\Delta_4)$ — the $n=4\to5$ cofiber cohomology — is **not yet computed**; it is exactly the **PCR-Lit-2′** target (mg-6295 §6.3: "re-run the identical greedy+Forman recipe on $C_*(\Delta_5,\Delta_4)$"). Computing it is a fresh $n=5$ cofiber enumeration, which the F11 constraint "no new HPC, no new $n$-datapoint" forbids — so (E2) is correctly the *next* ticket's work, gated on PCR-Lit-2′.

The natural ordering: **PCR-Lit-2′** (compute the $n=4\to5$ cofiber Betti vector — mg-6295's own designated follow-up, independently motivated) $\to$ **(E1)** functoriality writeup (parallel, no dependency) $\to$ **(E2)** the $\partial_3$ computation $\to$ if $\partial_3$ iso, the central-stability presentation argument for general $n$.

---

## §5. Route (iii) — noted only (PARKED per Daniel directive)

Route (iii) — the F8'' Quillen-fiber identification of $X_n$ (with $\Delta_{n+1}/\Delta_n \simeq \Sigma\,\Delta(X_n)$, $\widetilde\chi(\Delta(X_n)) = 2(-1)^n$) followed by a finite-generation argument for $(\Delta(X_n))_n$ — **is mg-b345 and is PARKED per Daniel's no-external-collaboration directive (2026-05-14T05:18Z).** F11 does not pursue it. Recorded for completeness only:

- F8'' (mg-b345, `45a7532`) **conjectures** the identification but does **not** identify $X_n$ for any $n \ge 3$, does not prove $\Delta_{n+1}/\Delta_n \simeq \Sigma\Delta(X_n)$ for any $n$, and grades all the load-bearing pieces (closed-form $X_n$; Quillen spectral-sequence convergence; generalized cofiber Künneth) as **Tier-3, not polecat-feasible**.
- The structurally cleanest candidate (F8''-Conjecture 2, "most likely true") is the *layer poset* $X_n = X_n^{\downarrow}\sqcup X_n^{\uparrow}$ with $\Delta(X_n) \simeq \Delta_n \sqcup \Delta_n$.
- Relevant cross-link: F8'' is the only predecessor that *raises* (without proving) the FI-module / representation-stability framing of $(\mathrm{PPF}_n)_n$ — the same framing route (ii) now makes concrete. If route (ii) succeeds, it would partially subsume route (iii)'s goal without needing the explicit $X_n$.

If routes (i)+(ii) both ultimately stall, revisiting route (iii) becomes a PM/Daniel decision (it is Tier-3 specialist by F8''s own grading). F11's verdict (§6) is that route (ii) has not stalled — it has a concrete handle — so route (iii) stays parked.

---

## §6. Verdict and next-step recommendation

### 6.1 Verdict: GREEN-route-traction

Per the F11 verdict matrix: **GREEN-route-traction** — *"a route (i)/(ii) sub-problem is closed or substantially advanced; (FG-Cofiber) is closer. Pre-file or recommend the follow-up."* Both conditions are met:

1. **A route sub-problem is closed.** Route (i)'s entry sub-problem — the n-uniform-orbit-count question, F11 deliverable 3 — is **closed NEGATIVE, rigorously**: the chamber complex's cell count is super-exponential in $n$ (Kleitman–Rothschild), so the chamber-quotient cochain complex is not a finitely generated FI-module; and the rational chamber quotient is contractible, so it does not compute the cofiber cohomology. Route (i) as a "finite ambient" strategy is eliminated; its constructive residue folds into M1 (§3.4).
2. **A route sub-problem is substantially advanced.** Route (ii)'s framework half — F10 §7.2.b's open "identify the correct degree-shift-aware functor-category framework" — is substantially advanced: the degree-shift-$(+1)$ transition map is identified as the triple connecting homomorphism $\partial_n$ (§4.2), shown to commute with the fixed-degree co-FI-structure (§4.3), and shown to be *substantive* — $\partial_n$ iso $\Rightarrow$ (UCC.1) representation-type propagation (§4.4). The most polecat-tractable entry sub-problem (E1) is identified and started; (E2) is precisely scoped and gated.
3. **(FG-Cofiber) is closer.** Three routes are narrowed to one with a concrete handle (route (i) eliminated, route (iii) parked, route (ii) live with an identified transition map and a two-step entry plan). The follow-up is recommendable now.

This is a measured GREEN: route (i)'s closure is *negative* (valuable elimination, not progress toward a proof), and route (ii)'s advance is *structural, not numerical* (the decisive computation (E2) is gated on PCR-Lit-2′). But narrowing the route space, resolving part of the framework question, and producing a concrete pre-fileable follow-up is exactly the GREEN-route-traction profile — and decisively better than AMBER-scoped-not-closed (a sub-problem *was* closed) and than AMBER-internally-hard (route (ii) is *not* beyond internal/polecat reach — (E1) is squarely polecat-class and (E2) is one matrix computation behind an already-planned ticket).

### 6.2 Precise next-step recommendation

The next ticket should attack **route (ii)** along the (E1)→PCR-Lit-2′→(E2) path:

- **Recommended follow-up A — (E1), polecat-class, no dependency, do first.** Write out rigorously that $\bigl((B_n)_n,\{V(f)^*\},\{\partial_n\}\bigr)$ is a genuine module over the degree-shift-aware functor category: full functoriality across all injections, choice-independence of the cofiber relabelling, $\partial$-composite compatibility. Paper-and-pencil; this is the standalone prerequisite for route (ii) and needs no computation. F11 §4.2–§4.3 is the starting sketch.
- **Recommended follow-up B — PCR-Lit-2′, the gating computation.** Compute the $n=4\to5$ cofiber cohomology $B_4 = \widetilde H^3(\Delta_5/\Delta_4)$ — mg-6295's own designated follow-up (mg-6295 §6.3), independently motivated, and the prerequisite for (E2). *(This is an $n=5$ cofiber enumeration — out of F11's "no new HPC" scope, in scope for a dedicated computation ticket.)*
- **Recommended follow-up C — (E2), gated on B.** With $B_4$ in hand, compute $\partial_3 : B_3 \to B_4$ (a $2\times2$ $S_3$-equivariant matrix in the explicit mg-6295 critical-cell basis) and test injectivity/isomorphism. If $\partial_3$ is an isomorphism, proceed to the general-$n$ central-stability presentation argument (Patzt-style, bounded generators+relations); if not, the failure pinpoints precisely where the degree-shift-aware object is *not* free, which is itself decisive information.

Route (i) needs **no** follow-up — it is closed. Route (iii) stays parked unless routes (i)+(ii) both stall (they have not).

### 6.3 Trust-surface impact

**None.** F11 introduces no new axioms, makes no Lean changes, runs no new computation. It is paper-and-pencil structural cohomology + the standard asymptotic-counting literature (Kleitman–Rothschild; OEIS A001035). The in-tree Lean artifact `width3_one_third_two_thirds` (4-axiom trust surface) is untouched, as is the general-$n$ paper-level track.

---

## §7. References

### 7.1 Parent and sibling mg-tickets

- **mg-8216** — F10: general-$n$ unified proof synthesis. `3c173df`; `docs/general-n-proof-synthesis.md` §6.3 (UCC), §6.4 (M1+M2 converge), §7.2 (FG-Cofiber sharpening), §7.2.d (three routes); `docs/state-F10.md`. **Parent.**
- **mg-6295** — PCR-Lit-2 / M1: Hersh–Welker discrete-Morse on the cofiber. `f169345`; `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`. $M_{\mathrm{rel}}$ perfect at $n=3\to4$, $(0,0,2,0)$, $2\cdot\mathrm{sgn}_{S_3}$; downward-closed-subcomplex lemma ($n$-independent); §6.3 PCR-Lit-2′; §8.2 equivariant cofiber-Morse noted.
- **mg-759d** — PCR-Lit-3 / M2: FI-module presentation-degree check. `e5d9b08`; `docs/compatibility-geometry-PCR-Lit-3-fi-module.md`. §5.2 transposition-forced-zero; §5.3 sgn-twist $M(0)$; §6.4 finite-generation caveat.
- **mg-1e58** — F5: chamber-restricted Morse at $n=5$. `77440bd`; `docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md`. **(F5.A)** 61 orbits at $n=5$; **(F5.B)** $\widetilde\chi(\Delta(C_5))=0$, chamber quotient rationally contractible, cohomology lives in $\mathrm{sgn}$; §3.3 the "twisted chamber" equivariant picture.
- **mg-8736** — F6: Forman cancellation on F5 + BFT extension. `7125329`; `docs/compatibility-geometry-F6-forman-cancellation.md`. Chamber complex finite; $4\to2$ critical cells; no FI/Noetherianity content.
- **mg-b345** — F8'': (I5) Quillen-fiber / Künneth specialist scoping. `45a7532`; `docs/compatibility-geometry-F8pp-quillen-fiber.md`. **Route (iii) ticket — PARKED per Daniel.** $\Delta_{n+1}/\Delta_n \simeq \Sigma\Delta(X_n)$ conjecture; $\widetilde\chi(\Delta(X_n)) = 2(-1)^n$; raises FI-module framing of $(\mathrm{PPF}_n)_n$.
- **mg-f91f** — PCR-1: $n=4$ relative Betti $(0,0,2,0)$. **mg-59f3** — PCR-2: spectral $E_2$, $\delta_3^{\mathrm{sgn}}$ injective, $(m_A,m_X,m_{X/A})^{\mathrm{sgn}}=(1,1,2)$.
- **mg-1e99** — F8: ICOP framework.

### 7.2 Mathematical literature

- D. J. Kleitman, B. L. Rothschild, *Asymptotic enumeration of partial orders on a finite set*, Trans. AMS 205 (1975) 205–220. The $a(n) = 2^{n^2/4 + 3n/2 + O(\log n)}$ asymptotic — the rigorous basis for §3.2's super-exponential orbit-count bound.
- OEIS **A001035** — number of partial orders on $n$ labeled elements: $1,1,3,19,219,4231,130023,6129859,\dots$ Pins $|\mathrm{PPF}_n| = a(n)-1-n!$.
- T. Church, J. Ellenberg, B. Farb, *FI-modules and stability for representations of symmetric groups*, Duke Math. J. 164 (2015). Finitely generated FI-modules have eventually-polynomial dimension; the $(\mathrm{sgn}_{S_n})_n$ non-example; the sign-twist.
- T. Church, J. Ellenberg, B. Farb, R. Nagpal, *FI-modules over Noetherian rings*, Geom. Topol. 18 (2014). Noetherianity / subquotient finite generation.
- E. Ramos, *On the degree-wise coherence of FI-modules*, NYJM 23 (2017). Presentation degree $\le d$ $\Rightarrow$ determined by values at indices $\le d$.
- A. Putman, *Stability in the homology of congruence subgroups*, Invent. Math. 202 (2015); P. Patzt, *Central stability homology*, J. Topol. (2017+). Central stability — finite generation from bounded presentation, no a priori finite ambient. **The route (ii) machinery.**
- S. Sundaram, M. Wachs, *The homology representations of the $k$-equal partition lattice*, Trans. AMS 349 (1997). Precedent: top cohomology of an $S_n$-equivariant order complex as a sign-twisted object.
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998). Discrete Morse / Forman cancellation (M1, F5, F6 machinery).

### 7.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (Keeps the attack internal; parks route (iii)/mg-b345.)
- 2026-05-14T08:05Z — focus on the induction, not special cases. (No new HPC, no fresh $n$-datapoint enumeration in F11.)

---

## §8. Session ledger (cumulative state — `feedback_polecat_cumulative_state_doc`)

This file is the cumulative state doc for the multi-session (250k cap) F11 ticket. It survives polecat session boundaries; a future session should re-check the invariants below before extending.

### Session 1 — 2026-05-14 (this polecat, mg-b352) — DONE

**Goal:** Re-verify F10's central claims (trip-wire); survey routes (i) and (ii); attack route (i)'s entry point; emit a verdict + next-step recommendation. Route (iii) noted only.

| Item | Status | Output |
|---|---|---|
| Read parents: F10 (`3c173df`), M1 mg-6295 (`f169345`), M2 mg-759d (`e5d9b08`), F5 mg-1e58 (`77440bd`), F6 mg-8736 (`7125329`), F8'' mg-b345 (`45a7532`) | ✅ | — |
| **Trip-wire (a):** §6.2 inductive step gap-free given (UCC) | ✅ **PASS** | §1.1 — LES chase re-checked degree-by-degree |
| **Trip-wire (b):** M1 and M2 both reduce to (UCC) per §6.4 | ✅ **PASS** | §1.2 — downward-closed lemma $n$-independent; M2 Ramos template |
| **Trip-wire (c):** (UCC) at $n=3\to4$ unconditionally proven | ✅ **PASS** | §1.3 — mg-6295 §4/§5 + mg-59f3 §4 |
| Trip-wire verdict — RED-f10-gap excluded | ✅ | §1.4 — F10 GREEN-conditional survives |
| **Route (i) survey + ATTACK** (n-uniform-orbit-count question) | ✅ **closed NEGATIVE** | §3 — orbit count super-exponential (Kleitman–Rothschild); chamber quotient not f.g.; rational quotient contractible; residue folds into M1 |
| **Route (ii) survey + entry-point identification** | ✅ **substantially advanced** | §4 — triple connecting map $\partial_n$ identified as the degree-shift-aware transition; commutes with co-FI-structure; $\partial_n$ iso ⇒ (UCC.1) rep-type; (E1)/(E2) entry sub-problems |
| Route (iii) — noted only (PARKED per Daniel) | ✅ | §5 |
| **Verdict** | ✅ **GREEN-route-traction** | §6 |
| Next-step recommendation (E1 / PCR-Lit-2′ / E2) | ✅ | §6.2 |
| Trust-surface impact | ✅ none | §6.3 |

**Verdict: GREEN-route-traction.** Route (i) closed negative (definitive elimination); route (ii) substantially advanced (degree-shift-aware transition map identified, F10 §7.2.b framework question partially resolved, concrete two-step entry plan); (FG-Cofiber) is closer. Follow-up recommended, not yet pre-filed (left to the mayor/PM — the recommendation in §6.2 is precise enough to file directly).

**Nothing left undone within F11's scope.** F11's four deliverables are all addressed in Session 1: D1 trip-wire (§1), D2 route survey + most-tractable entry (§3, §4.6), D3 route-(i) attack (§3), D4 verdict + next-step (§6). The 250k cap was not approached — Session 1 used a small fraction; F11 did not need to be multi-session, but the ledger format is kept per `feedback_polecat_cumulative_state_doc` in case the mayor reopens it for the (E1) writeup.

**If F11 is reopened for a Session 2**, the natural in-scope continuation is **(E1)** — the rigorous functoriality writeup for the degree-shift-aware object (§4.6) — which is paper-and-pencil and needs no HPC, hence stays within F11's constraints. (E2) and PCR-Lit-2′ are out of F11's "no new HPC" scope and belong to dedicated follow-up tickets.

### Invariants (reproduce-on-resume)

Load-bearing facts for any future session; re-check against the cited parent docs before extending:

- F10 trip-wire all-PASS: §6.2 step gap-free given (UCC); M1+M2 both reduce to (UCC); (UCC) proven at $n=3\to4$. RED-f10-gap excluded.
- $|\mathrm{PPF}_n| = a(n) - 1 - n!$ where $a(n)$ = A001035 ($12, 194, 4110, 129302$ at $n=3,4,5,6$). $a(n) = 2^{n^2/4 + o(n^2)}$ (Kleitman–Rothschild).
- $S_n$-orbit count of $\mathrm{PPF}_n$: $2, 12, 61$ at $n=3,4,5$; $\ge |\mathrm{PPF}_n|/n! = 2^{n^2/4 - n\log_2 n + o(n^2)}$ — **super-exponential**, NOT n-uniformly/polynomially bounded.
- Chamber quotient $\Delta_n/S_n$ rationally contractible: $\widetilde H^*(\Delta_n;\mathbb Q)^{S_n} = (\mathrm{sgn}_{S_n})^{S_n} = 0$ (F5.B). Same for the cofiber quotient.
- Route (i) closed NEGATIVE; its constructive residue (equivariant sign-respecting Morse matching) = M1, not a separate route.
- $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$; $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ proven; (UCC.1) conjectures $B_n = 2\cdot\mathrm{sgn}_{S_n}$ concentrated in degree $n-1$.
- The degree-shift-aware transition map is $\partial_n : B_n \to B_{n+1}$, the connecting homomorphism of the triple $(\Delta_n \subset \Delta_{n+1} \subset \Delta_{n+2})$ — degree $+1$, $S_n$-equivariant, commutes with $\{V(f)^*\}$.
- $\partial_n$ iso (all $n$) + concentration $\Rightarrow$ $B_n = 2\cdot\mathrm{sgn}_{S_n}$ for all $n$ = (UCC.1) rep-type half. $\partial_n$ iso is genuinely open (involves $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)$, the double-cofiber cohomology).
- Route (ii) entry sub-problems: (E1) functoriality writeup — polecat-class, no HPC; (E2) compute $\partial_3$ — gated on PCR-Lit-2′ ($n=4\to5$ cofiber Betti).

---

*Polecat: mg-b352 (F11). Branch: `compat-geom-F11-fg-cofiber-attack`. Verdict: **GREEN-route-traction** — F10 trip-wire all-PASS; route (i) closed NEGATIVE (chamber-quotient ambient is super-exponential, not f.g., and rationally contractible — F5's n-uniform-orbit-count question answered: NO); route (ii) substantially advanced (degree-shift-aware transition map identified as the triple connecting homomorphism $\partial_n$; (FG-Cofiber) reduced to "$\partial_n$ iso for all $n$"; entry sub-problems (E1)/(E2) scoped). Route (iii) parked per Daniel. No new axioms; no Lean changes; no new computation. Cumulative state: this file, §8.*
