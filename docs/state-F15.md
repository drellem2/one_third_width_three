# state-F15 — cumulative state ledger for F15 (E2): the $\partial_3$ isomorphism test + general-$n$ diagnosis (mg-8355)

**Ticket:** mg-8355 — F15, Route (ii) entry sub-problem (E2). Computation + structural argument; 300k cap; multi-session-able.
**Branch:** `compat-geom-F15-E2-partial-d3-iso`.
**Parent:** mg-b352 (F11, `11a75d6`) — `docs/state-F11.md` §4.4–§4.6, §6.2 follow-up C.
**Depends:** mg-3839 (F14, GREEN-cofiber-perfect) — $B_4$ + $\widetilde b_*(\Delta_5/\Delta_4)$.
**Also uses:** mg-ecf6 (F13, E1, GREEN-functoriality-established) — triple-LES conventions; **verified GREEN before Phase 1 per `feedback_pre_execution_dependency_verification`**.
**Deliverables:** (D1) `scripts/compat_geom_partial_3.py`; (D2) `docs/compatibility-geometry-F15-e2-partial-test.md`; (D3) this file.
**Constraints:** no new axioms; no Lean changes; 300k cap; cumulative state doc (`feedback_polecat_cumulative_state_doc`).

This file survives session boundaries; a future session re-checks the invariants in §3 before extending.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-8355) — DONE

**Goal:** Phase 1 — construct $\partial_3 : B_3 \to B_4$ and test it for isomorphism. Phase 2 (general-$n$ central-stability presentation) only if $\partial_3$ iso AND F13 GREEN.

| Item | Status | Output |
|---|---|---|
| Verify dependencies F14 (mg-3839) + F13 (mg-ecf6) GREEN | ✅ | F14 = GREEN-cofiber-perfect; F13 = GREEN-functoriality-established. Read both docs + F11 §4, mg-6295. |
| **Lemma 3.1: $\partial_n = \delta_{n+1}\circ q_n$** | ✅ **proven** | D2 §3 — cochain-level identity, $n$-uniform, unconditional. The triple connecting map factors through the pair-LES maps $q_n$ (of $(\Delta_{n+1},\Delta_n)$) and $\delta_{n+1}$ (of $(\Delta_{n+2},\Delta_{n+1})$). Standard homological algebra in F13's conventions. |
| **Phase 1: construct $\partial_3$, test isomorphism** | ✅ **DONE — NOT an iso** | D2 §4–§5 — $\mathrm{rank}(\partial_3) = 1$. Two independent routes: factorisation (§4, $q_3$ rank 1 + $\delta_4$ injective) and triple-LES exactness (§5). Unconditional at $n=3$. |
| Direct Betti computation ($\Delta_3,\Delta_4,\Delta_4/\Delta_3$) | ✅ | D1 §[B] — sparse mod-$p$ rank, 2 primes: $\widetilde b_*(\Delta_3)=(0,1)$, $\widetilde b_*(\Delta_4)=(0,0,1,0,0)$ [Hyp(4)], $\widetilde b_*(\Delta_4/\Delta_3)=(0,0,2,0,0)$ [mg-6295]. Re-derives the inputs from scratch — built-in trip-wire, all PASS. |
| $S_3$-equivariant refinement | ✅ | D1 §[F], D2 §4 — Lefschetz characters: $\widetilde H^1(\Delta_3)=\mathrm{sgn}_{S_3}$, $\widetilde H^2(\Delta_4)=\mathrm{sgn}_{S_4}$, $B_3=2\cdot\mathrm{sgn}_{S_3}$. $\partial_3$ is an $S_3$-map $2\cdot\mathrm{sgn}\to2\cdot\mathrm{sgn}$ of rank 1. |
| Precise structure of $\partial_3$ | ✅ | D2 §4.4 — $\ker(\partial_3)=\mathrm{im}(\delta_3)$ (the (UCC.2) line), $\mathrm{im}(\partial_3)=\mathrm{im}(\delta_4)=\ker(\iota_4^*)$. |
| **General-$n$ diagnosis** | ✅ | D2 §6 — $\partial_n$ iso $\iff\delta_n=0\iff\neg$(UCC.2)$(n)$. Under Hyp, $\mathrm{rank}(\partial_n)\le1$ for all $n$. Route (ii) simplest form ($M(0)^{\oplus 2}$ free) dead uniformly; weaker bounded-central-stability form NOT killed. |
| Phase 2 (iso-based general-$n$ argument) | ⛔ **moot, not executed** | Per ticket: "$\partial_3$ NOT iso $\Rightarrow$ STOP, Phase 2 moot." The general-$n$ *diagnosis* (D2 §6) is delivered instead — it is Phase-1 fallout, not Phase 2. |
| **Verdict** | ✅ **AMBER-partial3-not-iso** | D2 §8 — RED-computational-gap excluded ($\partial_3$ was constructible/factorable from F14). |
| PM/Daniel decision input | ✅ surfaced | D2 §7.3 — three options; F15 recommends option 1 (pursue route (ii)'s weaker bounded-central-stability form). Mailed mayor on completion. |
| Trust-surface impact | ✅ none | D2 §8 — no new axioms, no Lean changes, no HPC. Script runtime $\approx1.5$s. |

**Verdict: AMBER-partial3-not-iso.** $\partial_3$ has rank 1, not an isomorphism — decisive negative information for route (ii). The result is structural (the factorisation $\partial_3=\delta_4\circ q_3$ caps the rank at $\dim\widetilde H^2(\Delta_4)=1$) and $n$-uniform (the same factorisation kills "$\partial_n$ iso for all $n$" by incompatibility with (UCC.2)).

**Nothing left undone within F15's Phase-1 scope.** All three deliverables emitted in Session 1. The 300k cap was not approached — Session 1 used a small fraction. F15 did not need to be multi-session; the ledger format is kept per `feedback_polecat_cumulative_state_doc` in case the mayor reopens it.

**If F15 is reopened for a Session 2** — the natural in-scope continuation is *not* the original Phase 2 (the iso-based argument, moot), but route (ii)'s **weaker form**: attempt a bounded central-stability presentation for $((B_n)_n,\{\partial_n\})$ using the factorisation $\partial_n=\delta_{n+1}\circ q_n$ as the structural handle (D2 §6.5, §7.3 option 1). That is arguably a dedicated follow-up ticket rather than an F15 reopening — a PM call.

---

## §2. The result, in one screen (reproduce-on-resume)

- **Object.** $B_n := \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)$; $\partial_n : B_n\to B_{n+1}$ the triple connecting map of $(\Delta_n,\Delta_{n+1},\Delta_{n+2})$ (F13 Def. 2.1). $B_3 = 2\cdot\mathrm{sgn}_{S_3}$ (mg-6295), $B_4 = 2\cdot\mathrm{sgn}_{S_4}$ (F14).
- **Lemma 3.1 (the key).** $\partial_n = \delta_{n+1}\circ q_n$ — triple connecting map factors through pair-LES maps. $q_n : B_n\to\widetilde H^{n-1}(\Delta_{n+1})$ (pair-LES map of $(\Delta_{n+1},\Delta_n)$); $\delta_{n+1} : \widetilde H^{n-1}(\Delta_{n+1})\to B_{n+1}$ (pair connecting map of $(\Delta_{n+2},\Delta_{n+1})$). Cochain proof: "extend by zero off $\Delta_{n+1}$" is simultaneously a valid preimage for both the triple SES and the pair SES.
- **Phase 1 result.** $\mathrm{rank}(\partial_3) = 1$. $\partial_3$ is **not** an isomorphism. Because: $q_3$ surjective with $\mathrm{rank}\,1$ (pair LES of $(\Delta_4,\Delta_3)$: $\widetilde H^2(\Delta_3)=0\Rightarrow$ surjective, $\delta_3$ injective $\Rightarrow\ker = \mathrm{im}(\delta_3)$ 1-dim); $\delta_4$ injective (pair LES of $(\Delta_5,\Delta_4)$: $\widetilde H^2(\Delta_5)=0$, Hyp(5) — the LES F14 used in its §3.3). $\Rightarrow\mathrm{rank}(\partial_3)=\mathrm{rank}(q_3)=1$.
- **Cross-check.** Triple LES of $(\Delta_3,\Delta_4,\Delta_5)$: dims $0\to1\to2\to2\to1\to0$; exactness forces $\mathrm{rank}(\partial_3)=1$. (The "1"s: $\widetilde H^2(\Delta_5/\Delta_3)=\widetilde H^3(\Delta_5/\Delta_3)=1$, from the pair LES of $(\Delta_5,\Delta_3)$ + Hyp(3,5).)
- **General-$n$.** $\partial_n$ iso $\iff\delta_n=0\iff\neg$(UCC.2)$(n)$. (UCC.2)$(n)\Rightarrow\partial_n$ not iso. Under Hyp$(n{+}1)$, $\widetilde H^{n-1}(\Delta_{n+1})=\mathrm{sgn}_{S_{n+1}}$ is 1-dim $\Rightarrow\mathrm{rank}(\partial_n)\le1<2$ for all $n$.
- **Verdict.** AMBER-partial3-not-iso. Route (ii) simplest form (free $M(0)^{\oplus2}$) dead; weaker form (bounded central-stability presentation) alive, handed the factorisation as a handle.

---

## §3. Invariants (re-check against cited parent docs before extending)

- $\Delta_n\hookrightarrow\Delta_{n+1}$ is an order-ideal (downward-closed) subcomplex inclusion; $(\Delta_{n+1},\Delta_n)$ a good pair — mg-6295 §1.1, F13 Lemma 1.4; script §[A] re-verifies for $(\Delta_4,\Delta_3)$.
- F13's relative-cochain convention: $C^\bullet(X,A)=\{\varphi\in C^\bullet(X):\varphi|_A=0\}$. The triple LES (2.1)/(2.2) and pair LES (2.3) are as in F13 §2.
- $\partial_n$ is the **triple** connecting map ($B_n\to B_{n+1}$); $\delta_n$ is the **pair** connecting map ($\widetilde H^{n-2}(\Delta_n)\to B_n$). Distinct maps — F13 §2 deliberately kept them apart. **Lemma 3.1 is the bridge:** $\partial_n=\delta_{n+1}\circ q_n$.
- Established inputs (proven; not re-derived for $\Delta_5$): Hyp(3,4,5) [$\widetilde H^*(\Delta_n)=\mathrm{sgn}_{S_n}$ in degree $n{-}2$; F10, verified $n\le6$; script re-derives $n=3,4$]; $B_3=2\cdot\mathrm{sgn}_{S_3}$ [mg-6295]; $B_4=2\cdot\mathrm{sgn}_{S_4}$, $\widetilde b_*(\Delta_5/\Delta_4)=(0,0,0,2,0)$ [F14]; (UCC.2) at $n=3$ [$\delta_3$ injective; mg-59f3].
- The core $n=3$ result is **unconditional** — every input is proven. The only $\Delta_5$-fact the core needs is $\widetilde H^2(\Delta_5)=0$ (Hyp(5)), which F14 itself already used.
- $\partial_3$ rank 1 established **twice independently** (factorisation §4; triple-LES exactness §5) — they agree; the script asserts the agreement.
- (UCC.1) concentration half (M1, "$M_{\mathrm{rel}}$ perfect") is **orthogonal** to $\partial_n$ — untouched by F15.
- Trust-surface impact: none. No new axioms, no Lean changes, no HPC.

---

## §4. References

- mg-b352 (F11, `11a75d6`) — `docs/state-F11.md` §4.2–§4.6, §6.2. The $\partial_n$ identification, the "$\partial_n$ iso" reduction, entry sub-problems.
- mg-ecf6 (F13, E1) — `docs/compatibility-geometry-F13-shift-aware-functoriality.md`, `docs/state-F13.md`. GREEN-functoriality-established. Triple-LES conventions (§2), $\partial_n$ Def. 2.1.
- mg-3839 (F14) — `docs/compatibility-geometry-F14-pcr-lit2prime.md`, `docs/state-F14.md`, `scripts/compat_geom_cofiber_morse_n4n5.py`. GREEN-cofiber-perfect. $B_4=2\cdot\mathrm{sgn}_{S_4}$; §3.3 the pair-LES $\delta_4$.
- mg-6295 (PCR-Lit-2) — `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`, `scripts/compat_geom_cofiber_morse_n3n4.py`. $B_3=2\cdot\mathrm{sgn}_{S_3}$; the poset/chain/sparse-rank/Lefschetz machinery transcribed into this ticket's script.
- mg-59f3 (PCR-2) — $\delta_3$ injective, (UCC.2) at $n=3$. mg-f91f (PCR-1) — $n=4$ relative Betti.
- mg-8216 (F10, `3c173df`) — (UCC), §6.2 inductive step, §7.2 (FG-Cofiber), Hyp$(n)$ verified $n\le6$.
- Hatcher, *Algebraic Topology* §2.1–2.2 (triple/pair LES, the factorisation); Weibel, *Homological Algebra* Thm 1.3.1 (naturality of $\partial$); Putman 2015 / Patzt 2017 (central stability — route (ii)'s weaker form).

---

*Cumulative state doc for mg-8355 (F15, E2). Session 1 DONE — verdict AMBER-partial3-not-iso. Branch `compat-geom-F15-E2-partial-d3-iso`.*
