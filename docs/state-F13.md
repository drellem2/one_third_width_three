# state-F13 — cumulative state ledger for F13 (E1): functoriality of the degree-shift-aware cofiber-cohomology object (mg-ecf6)

**Ticket:** mg-ecf6 — F13, Route (ii) entry sub-problem (E1). Polecat-class, paper-and-pencil, 200k cap, multi-session-able.
**Branch:** `compat-geom-F13-E1-functoriality`.
**Parent:** mg-b352 (F11, `11a75d6`) — `docs/state-F11.md` §4.6, §6.2 follow-up A. **Grandparent:** mg-8216 (F10, `3c173df`) §7.2.
**Deliverables:** (D1) `docs/compatibility-geometry-F13-shift-aware-functoriality.md` — the rigorous writeup; (D2) this file — cumulative state.
**Constraints:** no new axioms; no Lean changes; no new computation / no HPC; no new $n$-datapoint. Standard homological algebra only.

This file is the cumulative state doc (`feedback_polecat_cumulative_state_doc`). It survives session boundaries; a future session re-checks the invariants in §3 before extending.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-ecf6) — DONE

**Goal:** Write out rigorously that $\bigl((B_n)_n,\{V(f)^\ast\},\{\partial_n\}\bigr)$ is a genuine module over the degree-shift-aware functor category — closing the four caveats F11 §4.3 flagged honestly.

| Item | Status | Output |
|---|---|---|
| Read parents: F11 (`11a75d6`, `docs/state-F11.md` §4), F10 (`3c173df`, synthesis §7.2), M1 mg-6295 (`f169345`), M2 mg-759d (`e5d9b08` §4–§6) | ✅ | — |
| **Item 1 — Choice-independence** | ✅ **closed** | D1 §3 — canonical extension $\hat f$ is the *unique* non-degenerate extension (Lemma 3.3); every other extension induces the zero map. "Choice-independence" resolved as *canonicity*: there is no choice. $V(\tilde f)$ is the unique map of triples (Lemma 3.5). |
| **Item 2a — Full functoriality, degree-preserving half** | ✅ **closed** | D1 §4 — each $H^k$ is a genuine co-FI-module over **all** of $\mathrm{FI}$ (Prop. 4.4), realised as relative cohomology of the FI-pair $\iota:\mathrm{PPF}\hookrightarrow\Sigma\,\mathrm{PPF}$ (Lemma 4.2). $V$-functoriality proven structurally + $n$-uniformly (Lemma 1.3), cross-checked by M2 §4. |
| **Item 2b — Commuting square for every injection, shift half** | ✅ **closed** | D1 §5 — $\partial^k:H^k\Rightarrow\Sigma^\ast H^{k+1}$ is an FI-natural transformation (Thm. 5.3); square (5.1) holds for **all** $f$, by naturality of the triple-LES connecting hom (Lemma 5.1) applied to the map of triples $V(\tilde f)$. $S_n$-equivariance of $\partial_n$ is the special case $f\in S_n$. |
| **Item 3 — $\partial$-composite compatibility / coherence** | ✅ **closed** | D1 §6 — $\partial$-composites are unconstrained associative composites, no relation imposed (Prop. 6.1); iterated naturality rectangles cohere automatically (Prop. 6.2). Single load-bearing fact: functoriality of the canonical extension (Rmk. 6.3). |
| **Item 4 — Identify the functor category + define "finitely generated"** | ✅ **closed** | D1 §7 — $\mathcal{C}$ by generators/relations (Def. 7.1); intrinsic form = graded co-FI-modules with $\partial:H^k\Rightarrow\Sigma^\ast H^{k+1}$ (Thm. 7.4); $H$ proven a $\mathcal{C}$-module (Thm. 7.2); finite generation defined (Def. 7.6); F11 §4.4 reduction recovered as Cor. 7.7. Sgn-twist compatibility noted (§7.5). |
| **Verdict** | ✅ **GREEN-functoriality-established** | D1 §8 — all four caveats closed; RED and AMBER both excluded. |
| Scope boundary + what E1 unblocks | ✅ | D1 §8.2–§8.3 — E1 is the *framework* half; finiteness half ("$\partial_n$ iso") is open, belongs to (E2)/PCR-Lit-2′. |
| Trust-surface impact | ✅ none | D1 §8.4 |

**Verdict: GREEN-functoriality-established.** $\bigl((B_n)_n,\{V(f)^\ast\},\{\partial_n\}\bigr)$ is rigorously a module over the degree-shift-aware functor category $\mathcal{C}$ (D1 Thm. 7.2 + Thm. 7.4). Route (ii)'s **framework half is closed**. F10 §7.2.b–c's open framework question is **answered**: the framework is $\mathcal{C}$-$\mathrm{Mod}$.

**Nothing left undone within E1's scope.** All four F11 §4.3 caveats + the two F13 deliverables are addressed in Session 1. The 200k cap was not approached — Session 1 used a small fraction. F13 did not need to be multi-session; the ledger format is kept per `feedback_polecat_cumulative_state_doc` in case the mayor reopens it.

**If F13 is reopened for a Session 2,** the only in-scope continuation (paper-and-pencil, no new computation) would be deepening the $\mathcal{C}$-$\mathrm{Mod}$ theory — e.g. spelling out free $\mathcal{C}$-modules and a Noetherianity discussion, or the precise central-stability presentation criterion in $\mathcal{C}$-$\mathrm{Mod}$ terms. But that shades into route (ii)'s *finiteness* half and is better left to the dedicated central-stability follow-up (F11 §6.2 follow-up C). (E2) and PCR-Lit-2′ are out of scope (they need the $n=4\to5$ cofiber computation).

---

## §2. The structure, in one screen (reproduce-on-resume)

- **Object.** $H^k_n := \widetilde H^k(\Delta_{n+1}/\Delta_n) = H^k(C^\bullet(\Delta_{n+1},\Delta_n))$; diagonal $B_n := H^{n-1}_n$. Framework set up for **all** $k$ (concentration not assumed — it is what route (ii) aims to prove). Scope $n\ge 3$; $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ proven.
- **Canonical extension (hat / FI-shift $\Sigma$).** $f\in\mathrm{FI}(m,n)\rightsquigarrow\hat f\in\mathrm{FI}(m+1,n+1)$: $\hat f|_{[m]}=f$, $\hat f(m)=n$. Functorial: $\widehat{g\circ f}=\hat g\circ\hat f$, $\widehat{\mathrm{id}}=\mathrm{id}$. $\tilde f:=\widehat{\hat f}=\Sigma^2 f$. **Uniqueness (Lemma 3.3):** $\hat f$ is the *unique* extension of $f$ inducing a non-zero map on cofibers; every other extension induces $0$. ⇒ choice-independence is canonicity.
- **Degree-preserving structure.** Each $H^k:\mathrm{FI}^{\mathrm{op}}\to\mathbf{Vect}$, $f\mapsto V(\hat f)^\ast$, is a co-FI-module (Prop. 4.4). $= $ relative cohomology of the FI-pair $\iota:\mathrm{PPF}\hookrightarrow\Sigma\,\mathrm{PPF}$. The $S_n$-rep structure on $B_n$ is the $\mathrm{Aut}_{\mathrm{FI}}([n])=S_n$ part.
- **Degree-shifting structure.** $\partial_n^k:H^k_n\to H^{k+1}_{n+1}$ = connecting hom of the triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$; $\partial_n=\partial_n^{n-1}:B_n\to B_{n+1}$. **Key theorem (Thm. 5.3):** $\partial^k:H^k\Rightarrow\Sigma^\ast H^{k+1}$ is a morphism of co-FI-modules — square (5.1) commutes for **every** injection $f$. Proof = naturality of the triple-LES connecting hom (Lemma 5.1) + $V(\tilde f)$ is a map of triples (Lemma 3.5).
- **The functor category $\mathcal{C}$.** Objects $(n,k)$; generators $V_f:(n,k)\to(m,k)$ and $\sigma_{n,k}:(n,k)\to(n+1,k+1)$; relations (R1) $V$ is $\mathrm{FI}^{\mathrm{op}}$ at each $k$, (R2) $\sigma_{m,k}\circ V_f = V_{\hat f}\circ\sigma_{n,k}$. **Intrinsically (Thm. 7.4):** $\mathcal{C}$-$\mathrm{Mod}$ = $\mathbb{Z}$-graded co-FI-modules $H^\bullet$ with FI-natural $\partial^k:H^k\Rightarrow\Sigma^\ast H^{k+1}$. $H$ is a $\mathcal{C}$-module (Thm. 7.2).
- **Finite generation (Def. 7.6).** $H$ is f.g. in degree $\le d$ iff every $H^k_n$, $n>d$, is spanned by images of $\bigoplus_{n\le d}H^\bullet_n$ under composites of $V$- and $\partial$-maps. **Cor. 7.7:** under concentration, this collapses to "$\partial_{n-1}\cdots\partial_d:B_d\to B_n$ surjective for all $n>d$"; if every $\partial_n$ is an iso, $H$ is f.g. in degree $\le 3$ (generated by $B_3$) — recovering F11 §4.4–§4.5.

---

## §3. Invariants (re-check against cited parent docs before extending)

- $\Delta_n\hookrightarrow\Delta_{n+1}$ is a subcomplex inclusion, in fact an order-ideal inclusion ($n$-isolated posets) — mg-6295 §1.1/§6.1; ⇒ $(\Delta_{n+1},\Delta_n)$ is a good pair. The triple $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$ is nested order ideals.
- $V(f)$ = relabel along $f$ + adjoin $[n]\setminus\mathrm{im}(f)$ as isolated points; functorial on $\mathrm{FI}$ (Lemma 1.3; M2 §4 computational cross-check, PASS over all injections at $m,n\le 5$).
- $\partial_n$ is the **triple** connecting map (cofibers), of type $H^k_n\to H^{k+1}_{n+1}$ — **distinct** from the **pair** connecting map $\delta_n$ of F10 §6.2 (type $\widetilde H^k(\Delta_n)\to\widetilde H^{k+1}(\Delta_{n+1}/\Delta_n)$, the subject of (UCC.2)). E1 does not relate them.
- $\partial_n$ iso is genuinely open: $\partial_n$ injective $\iff r^\ast:\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)\to\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$ is zero, involving the double-cofiber cohomology $\widetilde H^{n-1}(\Delta_{n+2}/\Delta_n)$ — not known a priori. E1 assumes nothing about it.
- E1 establishes the **framework half** of route (ii) only. It does NOT prove: concentration (UCC.1), $\partial_n$ injective/iso, or finite generation. Those are (E2) → central-stability, gated on PCR-Lit-2′ (the $n=4\to5$ cofiber Betti $B_4=\widetilde H^3(\Delta_5/\Delta_4)$ — F14/mg-3839, sibling, runs in parallel).
- Load-bearing standard fact: naturality of the connecting homomorphism of a SES of cochain complexes (Weibel Thm. 1.3.1) — no new axiom, standard homological algebra.
- Trust-surface impact: none. No new axioms, no Lean changes, no computation.

---

## §4. References

See `docs/compatibility-geometry-F13-shift-aware-functoriality.md` §9 for the full reference list. Key pointers:
- **mg-b352 / F11** (`11a75d6`, `docs/state-F11.md`) §4.2–§4.6, §6.2 — parent; the $\partial_n$ sketch and the four caveats E1 closes.
- **mg-8216 / F10** (`3c173df`, `docs/general-n-proof-synthesis.md`) §7.2 — the degree-shift-aware framework question, answered by E1.
- **mg-6295 / M1** (`f169345`) — subcomplex / order-ideal structure; $B_3=2\cdot\mathrm{sgn}_{S_3}$; PCR-Lit-2′ designation.
- **mg-759d / M2** (`e5d9b08`) §4 — FI-action axioms verified; §5.3 — sgn-twist.
- **mg-3839 / F14** — sibling, PCR-Lit-2′ ($n=4\to5$ cofiber); no dependency either way.
- Weibel, *Homological Algebra*, Thm. 1.3.1; Hatcher, *Algebraic Topology* §2.1–§2.2.

---

*Polecat: mg-ecf6 (F13, E1). Branch: `compat-geom-F13-E1-functoriality`. Session 1 DONE — verdict **GREEN-functoriality-established**. Route (ii)'s framework half closed; finiteness half remains open and out of scope.*
