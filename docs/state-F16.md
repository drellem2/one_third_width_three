# state-F16 — cumulative state ledger for F16 (route (ii) weaker form: bounded central-stability presentation) (mg-f893)

**Ticket:** mg-f893 — F16, route (ii) survivor / critical path. Structural argument (representation stability / central stability); 350k cap; multi-session-able.
**Branch:** `compat-geom-F16-route-ii-weaker-central-stability`.
**Parent:** mg-8355 (F15, AMBER-partial3-not-iso) — §3 (Lemma 3.1), §6.4–§6.5, §7.3 option 1/3.
**Chain:** mg-b352 (F11) → mg-ecf6 (F13) → mg-3839 (F14) → mg-8355 (F15).
**Deliverables:** (D1) `docs/compatibility-geometry-F16-central-stability-presentation.md`; (D2) `docs/state-F16.md` (this file); (D3) `scripts/compat_geom_partial_squared.py`.
**Constraints:** no new axioms; no Lean changes; 350k cap; cumulative state doc; internal only (route (iii)/mg-b345 stays PARKED — but see §3, the PM/Daniel trigger is now met).

This file survives session boundaries; a future session re-checks the invariants in §3 before extending.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-f893) — DONE

**Goal:** Pursue route (ii)'s weaker form — show $((B_n)_n,\{\partial_n\})$ admits a bounded central-stability presentation (Putman/Patzt), using F15's factorisation $\partial_n=\delta_{n+1}\circ q_n$ as the handle; OR give a precise statement of the residual gap. Resolve the load-bearing (UCC.2)-interaction sub-question explicitly.

| Item | Status | Output |
|---|---|---|
| Read parents: F15 (mg-8355) + doc + script; F13 (mg-ecf6); F14 (mg-3839); F11 (mg-b352, state-F11); F10 (mg-8216, general-n-proof-synthesis) | ✅ | — |
| **Lemma 2.1: $\partial_{n+1}\circ\partial_n=0$ for all $n$** | ✅ **proven — UNCONDITIONAL** | D1 §2 — F15 Lemma 3.1 ($\partial_n=\delta_{n+1}\circ q_n$, unconditional) + exactness of the pair LES of $(\Delta_{n+2},\Delta_{n+1})$ gives $q_{n+1}\circ\delta_{n+1}=0$, hence $\partial^2=0$. $n$-uniform; no Hyp, no (UCC), no concentration. The diagonal tower is a cochain complex. Resolves F13 Prop. 6.1's open question. |
| **Theorem 3.3: unbounded generation degree** | ✅ **proven** (given concentration) | D1 §3 — under concentration (M1's half), F13 Cor. 7.7(1) collapses $H$ onto the diagonal; $\partial$ is the only degree-raising structure map; $\partial^2=0$ + $\dim B_n=2$ ⟹ $\widetilde H_0(H)$ has unbounded support. |
| **Corollary 4.1: NO bounded central-stability presentation** | ✅ **proven** (given concentration) | D1 §4 — bounded presentation ⟹ bounded $\widetilde H_0$ (presentation-independent); $\widetilde H_0(H)$ unbounded; contradiction. Route (ii) weaker form DEAD. The bounded presentation **provably does not exist.** |
| The dichotomy | ✅ | D1 §3.5 — under concentration: bounded generation degree $\iff$ $B_n=0$ for $n\gg0$; the latter is false ($\dim B_n=2$, M1). |
| **(UCC.2) interaction — the load-bearing sub-question** | ✅ **resolved: INDEPENDENT** | D1 §5 — the negative chain (Lemma 2.1 → Thm 3.3 → Cor 4.1) uses only $\partial^2=0$ (unconditional) + concentration (M1); (UCC.2) is never invoked. Does not need it; does not produce it. (UCC.2) only SHARPENS: with it, $\widetilde H_0(H)_n$ is exactly 1-dim each $n$, $\cong\widetilde H^{n-1}(\Delta_{n+1})$. |
| The diagnosis: route (ii) is circular | ✅ | D1 §4.3 — under (UCC.2)+Hyp, $\widetilde H_0(H)_n\cong\widetilde H^{n-1}(\Delta_{n+1})$ = (conj.) $\mathrm{sgn}_{S_{n+1}}$, the canonical non-f.g. FI-module. Route (ii) reproduces (FG-Cofiber), does not reduce it. Same rock as route (i) (F11 §3). |
| 2nd proof route (ii) simplest form dead | ✅ | D1 §2.3(b) — $\partial^2=0$ + $B_n\ne0$ ⟹ not all $\partial_n$ iso; independent of F15's (UCC.2) route. |
| **Companion script** `compat_geom_partial_squared.py` | ✅ **runs, all assertions pass (~18s)** | D3 — re-runs F15 $n=3$ trip-wire ([A],[B]: $\dim B_3=2$, $\dim\widetilde H^2(\Delta_4)=1$); **[C] verifies $q_3\circ\delta_3=0$ at the cochain level with explicit cocycle reps** + re-derives $\delta_3$ injective ((UCC.2) at $n=3$); [D] the engine one level up; [E] generation-degree bookkeeping; [F] verdict. |
| **Verdict** | ✅ **AMBER-route-ii-stalls** | D1 §7 — sub-case: the bounded presentation **provably does not exist**. RED-handle-fails excluded (F15 handle is sound and load-bearing). |
| Pivot identified | ✅ | D1 §7.3 — F15 §7.3 option 3 (M1 equivariant cofiber-Morse, rep type per $n$). NOT fanned out (per ticket). |
| Route (iii) trigger | ✅ surfaced | D1 §7.4 — routes (i)+(ii) both now closed-negative ⟹ route (iii) revisit is a PM/Daniel decision (F11 §5 / F15 §7.3 condition met). F16 recommends prioritising option 3 first. |
| Trust-surface impact | ✅ none | D1 §7.5 — no new axioms, no Lean changes, no HPC. Script pure-Python stdlib ~18s. |

**Verdict: AMBER-route-ii-stalls** (sub-case: bounded presentation provably does not exist). Route (ii) is closed — both the simplest form (F15) and the weaker form (F16) are dead, for one clean unconditional structural reason: $\partial_{n+1}\circ\partial_n=0$. A decisive, valuable AMBER: it *closes* a route (sparing further effort, like F11's route-(i) closure), resolves F13 Prop. 6.1's open question, and redirects the program to the documented pivot (option 3).

**Nothing left undone within F16's scope.** All three deliverables emitted in Session 1. The 350k cap was not approached — Session 1 used a fraction. F16 did not need to be multi-session; the ledger format is kept per `feedback_polecat_cumulative_state_doc` in case the mayor reopens it.

**If F16 is reopened for a Session 2** — the natural in-scope continuations would be: (a) the "without concentration" analysis (D1 §6.2 last bullet — more delicate; off-diagonal $V$-$\partial$ interleaving; but concentration is M1's deliverable and not in doubt, so low value); or (b) sharpening the §4.3 circularity diagnosis into a formal statement "route (ii) finite generation $\iff$ Hyp". Neither is load-bearing. The genuine next step is a *new ticket* — option 3 (M1 equivariant cofiber-Morse for rep type per $n$), a PM call.

---

## §2. The result, in one screen (reproduce-on-resume)

- **Object.** $B_n:=\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$; $\partial_n:B_n\to B_{n+1}$ triple connecting map. $H$ = the $\mathcal C$-module (F13). $B_3=2\,\mathrm{sgn}_{S_3}$ (mg-6295), $B_4=2\,\mathrm{sgn}_{S_4}$ (F14).
- **Lemma 2.1 (the key, UNCONDITIONAL).** $\partial_{n+1}\circ\partial_n=0$ for all $n$. Proof: $\partial_n=\delta_{n+1}\circ q_n$ (F15 Lemma 3.1, unconditional); $q_{n+1}$ and $\delta_{n+1}$ are consecutive maps in the (exact) pair LES of $(\Delta_{n+2},\Delta_{n+1})$, so $q_{n+1}\circ\delta_{n+1}=0$; hence $\partial_{n+1}\circ\partial_n=\delta_{n+2}\circ(q_{n+1}\circ\delta_{n+1})\circ q_n=0$. The diagonal tower $B_3\to B_4\to B_5\to\cdots$ is a cochain complex.
- **Theorem 3.3 + Cor 4.1 (given concentration = M1's half).** Under concentration ($H^k_n=0$, $k\ne n-1$; $\dim B_n=2$), $H$ collapses onto the diagonal (F13 Cor 7.7(1)); $\partial$ is the only degree-raising structure map; $\widetilde H_0(H)_n=B_n/\operatorname{im}(\partial_{n-1})$. If $\widetilde H_0(H)_n=0$ then $\operatorname{im}\partial_n=\partial_n(\operatorname{im}\partial_{n-1})=0$ (Lemma 2.1), so $\widetilde H_0(H)_{n+1}=B_{n+1}\ne0$. Hence $\widetilde H_0(H)$ has unbounded support ⟹ unbounded generation degree ⟹ **no bounded central-stability presentation**.
- **Dichotomy.** Under concentration: bounded generation degree $\iff B_n=0$ for $n\gg0$ — FALSE (M1).
- **(UCC.2) interaction.** INDEPENDENT — the negative chain uses only $\partial^2=0$ + concentration. (UCC.2) only sharpens: with it, $\widetilde H_0(H)_n$ exactly 1-dim, $\cong\widetilde H^{n-1}(\Delta_{n+1})$ — route (ii)'s generators ARE the absolute cohomologies, conjecturally $(\mathrm{sgn}_{S_{n+1}})_n$ = canonical non-f.g. FI-module. Route (ii) reproduces (FG-Cofiber).
- **Verdict.** AMBER-route-ii-stalls (bounded presentation provably does not exist). Route (ii) closed (both forms). Pivot: option 3. Route (iii): PM/Daniel decision.

---

## §3. Invariants (re-check against cited parent docs before extending)

- **F15 Lemma 3.1** ($\partial_n=\delta_{n+1}\circ q_n$) is UNCONDITIONAL — pure cochain algebra (F15 §3.1; "extend by zero off $\Delta_{n+1}$" is simultaneously a valid preimage for the triple SES and the pair SES). F16's Lemma 2.1 is built on it. Script `[C]` re-verifies the $n=3$ instance at the cochain level.
- **Pair LES (1.1)** of $(\Delta_{n+1},\Delta_n)$ is exact for all $n,k$ — standard, no hypothesis. $q_{n+1}\circ\delta_{n+1}=0$ is exactness at $B_{n+1}=\widetilde H^n(\Delta_{n+2}/\Delta_{n+1})$.
- **Concentration** = (UCC.1) concentration half: $H^k_n=0$ for $k\ne n-1$, $\dim B_n=2$. M1's deliverable (mg-6295 "$M_{\mathrm{rel}}$ perfect, critical vector $(0,\dots,0,2,0)$"); proven $n\le6$; the half F16 combines with. Logically independent of the rep-TYPE half (the open thing). F16 §3 assumes it; §6.2 flags the "without concentration" case as more delicate but not in doubt.
- **F13 Cor. 7.7(1)** — under concentration, $H$ collapses onto the diagonal: only non-zero spaces $B_n$, only structure maps $\partial_n$ + $S_n$-actions. **F13 Prop. 6.1** left $\partial$-composites "unconstrained" — F16 Lemma 2.1 resolves it (they vanish).
- $\widetilde H_0(H)$ (indecomposables / $0$-th central-stability homology) is **presentation-independent** — bounded presentation ⟹ bounded $\widetilde H_0$. Under concentration, $\widetilde H_0(H)_n=B_n/\operatorname{im}(\partial_{n-1})$.
- The negative result is INDEPENDENT of (UCC.2) and of the representation TYPE. It uses: Lemma 2.1 (unconditional) + concentration ($\dim B_n=2$, M1). It does not touch (UCC.1) concentration (assumed) or (UCC.2) (independent).
- Route (i) closed-negative (F11 §3); route (ii) closed-negative (F16, both forms); route (iii) (mg-b345) PARKED but the F11 §5 / F15 §7.3 revisit-trigger ("routes (i)+(ii) both stall") is now MET → PM/Daniel decision.
- Trust-surface impact: none. No new axioms, no Lean changes, no HPC.

---

## §4. References

- mg-8355 (F15) — `docs/compatibility-geometry-F15-e2-partial-test.md`, `docs/state-F15.md`, `scripts/compat_geom_partial_3.py`. AMBER-partial3-not-iso. **Lemma 3.1** (the unconditional factorisation — F16's foundation); §6.4 per-step structure; §7.3 option 3 (the F16 pivot).
- mg-ecf6 (F13) — `docs/compatibility-geometry-F13-shift-aware-functoriality.md`, `docs/state-F13.md`. GREEN-functoriality-established. The category $\mathcal C$; Cor. 7.7 (collapse to diagonal under concentration; Def. 7.6 finite generation); **Prop. 6.1** ($\partial$-composites "unconstrained" — F16 resolves).
- mg-3839 (F14) — `docs/compatibility-geometry-F14-pcr-lit2prime.md`. GREEN-cofiber-perfect. $B_4=2\,\mathrm{sgn}_{S_4}$; the $S_4$-equivariant order-ideal reduction = the option-3 template.
- mg-b352 (F11) — `docs/state-F11.md`. GREEN-route-traction. Route (i) closed NEGATIVE ($(\mathrm{sgn}_{S_n})_n$ not f.g. — same rock as route (ii)); route (ii) survey ($\partial_n$, central stability); route (iii) parked "unless routes (i)+(ii) both stall".
- mg-8216 (F10) — `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. GREEN-conditional. (UCC) = (UCC.1) concentration+rep-type + (UCC.2) $\delta_n$ injective; (FG-Cofiber); the three routes.
- mg-6295 (PCR-Lit-2 / M1) — $B_3=2\,\mathrm{sgn}_{S_3}$, $M_{\mathrm{rel}}$ perfect $(0,0,2,0)$ — M1's concentration deliverable at $n=3$. mg-59f3 (PCR-2) — $\delta_3$ injective ((UCC.2) at $n=3$); re-derived by the F16 script `[C]`. mg-b345 (F8″) — route (iii), PARKED → PM/Daniel decision.
- Putman 2015 (*Stability in the homology of congruence subgroups*); Patzt 2017+ (*Central stability homology*) — the route (ii) machinery; F16 shows its bounded-presentation hypothesis provably fails for $H$. CEF 2015 (*FI-modules…*) — $(\mathrm{sgn}_{S_n})_n$ the canonical non-f.g. FI-module. Weibel §1.3 (LES exactness — behind Lemma 2.1); Hatcher §2.1–2.2 (pair/triple LES).

---

*Cumulative state doc for mg-f893 (F16). Session 1 DONE — verdict AMBER-route-ii-stalls (bounded presentation provably does not exist). Branch `compat-geom-F16-route-ii-weaker-central-stability`. Route (ii) closed; pivot to option 3; route (iii) → PM/Daniel decision.*
