# state-F17 — cumulative state ledger for F17 (option 3: n-uniform S_n-equivariant cofiber Morse) (mg-4d3a)

**Ticket:** mg-4d3a — F17, the critical-path ticket. Structural argument (equivariant discrete Morse theory); 400k cap; multi-session-able.
**Branch:** `compat-geom-F17-nuniform-equivariant-morse`.
**Parent:** mg-f893 (F16, AMBER-route-ii-stalls) §7.3 (the option-3 pivot); mg-8355 (F15) §7.3 option 3.
**Chain:** mg-b352 (F11) → mg-ecf6 (F13) → mg-3839 (F14) → mg-8355 (F15) → mg-f893 (F16).
**Deliverables:** (D1) `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`; (D2) `docs/state-F17.md` (this file); (D3) `scripts/compat_geom_F17_equivariant_morse.py`.
**Constraints:** no new axioms; no Lean changes; 400k cap; cumulative state doc; internal only (route (iii)/mg-b345 stays PARKED — its escalation trigger did NOT fire, see §3).

This file survives session boundaries; a future session re-checks the invariants in §3 before extending.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-4d3a) — DONE

**Goal:** Establish the n-uniformity of "`M_rel` perfect + S_n-equivariant" — F14's `n = 4` S_4-equivariant order-ideal reduction as the template. Three sub-questions: (1) equivariance n-uniformly; (2) perfection n-uniformly; (3) representation type n-uniformly. If all three close, (UCC.1) is proven for all `n`.

| Item | Status | Output |
|---|---|---|
| Read parents: F16 (mg-f893) + doc; F14 (mg-3839) + doc + script; M1/PCR-Lit-2 (mg-6295) + doc; F10 (mg-8216) §3, §6; F15 (mg-8355); F11 (mg-b352) | ✅ | — |
| **Lemma 1.1: the `(Q,F)` model of `A_n`** | ✅ **proven** | D1 §1.1 — S_n-equivariant poset iso `A_n ≅ {(Q,F) : Q nonempty p.o. on [n], F nonempty filter of Q, ¬(F=[n]∧Q total)}`. Harness: exact set-equality with F14's direct `A_n` at `n=3,4` (`|A_3|=66`, `|A_4|=1420`). |
| **Lemma L1: `{Q : ∅≠Q⊊Q_0}` contractible** (chain `Q_0` on `[n]`, `n≥3`) | ✅ **proven — the one load-bearing lemma** | D1 §3 — closure operator `c(Q)=tc(Q∪{(a_1,a_n)})` lands in the poset; image has global min `{(a_1,a_n)}` ⟹ cone ⟹ contractible. n-uniform, no computation. Reused in MoveA + the `A_n^t` attachment. |
| **Prop. 2.1: MoveA n-uniform** | ✅ **proven** | D1 §2.1 — every fibre `Q_{<x}` is empty (`x|_{[n]}=∅`) / a cone (`x|_{[n]}` nonempty non-total: max `x|_{[n]}`) / Lemma L1 (`x|_{[n]}` total). Harness: direct over all `x∈R` at `n=3,4` (182, 3916 fibres); structural census at `n=5`. |
| **Prop. 2.2: MoveB n-uniform** | ✅ **proven** | D1 §2.2 — the Type-∅ ideal `S=S_↓⊔S_↑`, two components each `≅ B_{[n]}\{∅}`, S_n-equivariantly exchanged; every fibre a Boolean cone or empty. Gives `H̃_d(cofiber) ≅ 2·H̃_{d-1}(Δ(D_n))`. Harness: `n=3,4` direct (components `7+7`, `15+15`), `n=5` structural. |
| **Prop. 2.3: PEEL n-uniform** | ✅ **proven** | D1 §2.3 — `kill_up_n` is an S_n-equivariant interior operator `D_n→D_n` (the "stays proper" obligation holds because a total image forces a total pre-image), fixed set `A_n`. `Δ(D_n) ≃_{S_n} Δ(A_n)`. Harness: `n=3,4` direct (`|D_3|=96→|A_3|=66`, `|D_4|=2442→|A_4|=1420`), `n=5` structural. |
| **Theorem 2.4: the reduction identity** | ✅ **proven — UNCONDITIONAL, S_n-equivariant** | D1 §2.4 — `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ(A_n))` as S_n-reps, all `n≥3`, no hypothesis. The cluster lemma / patchwork theorem assembles the equivariant fibrewise matchings into a global S_n-equivariant acyclic cofiber matching `M_rel^{eq}`. |
| **Prop. 4.1: `A_n^{nt}` retracts onto `PPF_n`** | ✅ **proven** | D1 §4.1 — `A_n^{nt}` (`Q` non-total) is an order ideal; `c(Q,F)=(Q,[n])` is an S_n-equivariant closure operator; `c(A_n^{nt}) ≅ PPF_n`. `Δ(A_n^{nt}) ≃_{S_n} Δ_n`. Harness: all obligations `n=3,4,5`, `c(A_n^{nt})=PPF_n` exactly. |
| **Prop. 4.2: `A_n^t` attaches along contractible down-sets** | ✅ **proven** | D1 §4.2 — for every `y∈A_n^t`, `Δ((A_n)_{<y})` contractible: split `(A_n)_{<y}=D⊔T`, `D` has closure operator onto `\overline L(Q_0)` (Lemma L1), `T` a chain, induction on `|F_0|`. Harness: structural `n=3,4,5`, direct homology cross-check `n=3,4`. |
| **Theorem 4.3: `H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)`** | ✅ **proven — UNCONDITIONAL, as S_n-reps** | D1 §4.3 — compose Prop. 4.1 + Prop. 4.2 (both S_n-equivariant). Harness: direct at `n=3` (`H̃_∗(Δ(A_3))=H̃_∗(Δ_3)`, both `sgn`); `n=4` `H̃_∗(Δ_4)=(0,0,1)=sgn` direct + F14's `Δ(A_4)`; `n=5` structural. |
| **Theorem 5.1: (UCC.1) ⟺ Hyp(n)** | ✅ **proven** | D1 §5 — `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` as S_n-reps, all `n≥3`, unconditional. (UCC.1) at level `n` ⟺ Hyp(n). (UCC.1) discharged by the F10 induction; not an independent input. |
| **Sub-question 1 (equivariance, n-uniform)** | ✅ **YES** | D1 §6.1 — F14's reduction is an n-independent S_n-canonical rule; `M_rel^{eq}` is S_n-equivariant by construction (not "greedy+Forman", which is not equivariant — mg-6295 §8.2). |
| **Sub-question 2 (perfection, n-uniform)** | ✅ **YES (⟺ Hyp(n))** | D1 §6.2 — perfection of `M_rel^{eq}` at level `n` *is* Hyp(n). Resolves F10 §3.3's "perfection n-dependent, open beyond `n=3→4`". |
| **Sub-question 3 (rep type, n-uniform)** | ✅ **YES (⟺ Hyp(n))** | D1 §6.3 — the 2 critical `(n−1)`-cells carry `2·sgn_{S_n}` under Hyp(n), by S_n-equivariance of the whole reduction (structural, not character-theoretic). |
| **(UCC.2) interaction** | ✅ **resolved: INDEPENDENT** | D1 §7.3 — F17 builds the cofiber matching `M_rel^{eq}` alone; (UCC.2) is about the *gluing* `M_n ⊔ M_rel` (F10 §6.4), downstream of any single-pair cofiber computation. F17 neither needs nor produces (UCC.2). Mirrors F16 §5. |
| **Verification harness** `compat_geom_F17_equivariant_morse.py` | ✅ **runs, 21/21 checks pass (~46s)** | D3 — L1 (`n=3,4,5`), MoveA/MoveB/PEEL, the `A_n^{nt}` closure operator, the `A_n^t` attachment, the payoff. `(Q,F)` model = F14's `A_n` exactly at `n=3,4`. |
| **Verdict** | ✅ **GREEN-equivariant-uniform** | D1 §8 — (UCC.1) PROVEN for all `n` (both halves), reduced to Hyp(n). With the F10 core, only (UCC.2) remains. |
| Route (iii) trigger | ✅ **NOT fired** | D1 §8.2 — the escalation (AMBER-option-3-stalls) was conditioned on F17 *also* stalling; it did not. Route (iii)/mg-b345 stays PARKED. |
| Trust-surface impact | ✅ none | D1 §8.4 — no new axioms, no Lean changes, no HPC. Harness pure-Python stdlib ~46s. |

**Verdict: GREEN-equivariant-uniform.** Option 3 closes. The S_n-equivariant cofiber discrete Morse mechanism is n-uniform: F14's `n = 4` order-ideal reduction is the `n = 4` instance of an n-independent, S_n-equivariant construction whose every collapse hypothesis is proven for all `n ≥ 3` (Lemma L1 + Boolean cones + an interior operator). It yields `H̃_∗(Δ_{n+1}/Δ_n) ≅ 2·H̃_{∗-1}(Δ_n)` as S_n-representations, unconditionally — so **(UCC.1) ⟺ Hyp(n)**, both halves, discharged by the F10 induction. All three sub-questions close. With the F10 cohomological core, the **single** remaining conditional input of (UCC) is **(UCC.2)**.

**Nothing left undone within F17's scope.** All three deliverables emitted in Session 1. The 400k cap was not approached. F17 did not need to be multi-session; the ledger format is kept per `feedback_polecat_cumulative_state_doc` in case the mayor reopens it.

**If F17 is reopened for a Session 2** — the natural in-scope continuations: (a) upgrade Prop. 4.2 to a genuine *equivariant* homotopy equivalence (attach `A_n^t` orbit-by-orbit with the naturally-equivariant L1 contractions) — currently the result is stated at the homology level, which is exactly what (UCC.1) needs, so this is polish not substance; (b) make the cluster-lemma / patchwork assembly of `M_rel^{eq}` fully explicit as a single global acyclic matching with its critical-cell list (currently the reduction is justified *via* discrete Morse theory but the homology is computed through the order-ideal collapses, as in F14). Neither is load-bearing. The genuine next step is a **new ticket** — an F18 targeting (UCC.2) (§3, §8.3 of D1), a PM call.

---

## §2. The result, in one screen (reproduce-on-resume)

- **Object.** `Δ_n = Δ(PPF_n)`; cofiber `Δ_{n+1}/Δ_n`; `B_n = H̃^{n-1}(Δ_{n+1}/Δ_n)`. F14's reduction terminal complex `A_n = {x ∈ PPF_{n+1} : Down_n(x) ≠ ∅, Up_n(x) = ∅, x|_{[n]} ≠ ∅}`.
- **`(Q,F)` model (Lemma 1.1).** `A_n ≅ {(Q,F) : Q nonempty p.o. on [n], F nonempty filter of Q, ¬(F=[n]∧Q total)}`, S_n-equivariantly. `A_n^{nt}` (`Q` non-total) = order ideal; `A_n^t` (`Q` total) = order filter.
- **Lemma L1 (the key).** For a chain `Q_0` on `[n]`, `n≥3`: `{Q : ∅≠Q⊊Q_0}` is contractible. Proof: closure operator `c(Q)=tc(Q∪{(a_1,a_n)})`; image has global min `{(a_1,a_n)}` ⟹ cone.
- **Theorem 2.4 (the reduction, UNCONDITIONAL).** F14's MoveA/MoveB/PEEL is n-uniform & S_n-equivariant: MoveA fibres = empty/cone/L1 (Prop. 2.1); MoveB fibres = Boolean cones, 2 components `D_n ≅ U_n` (Prop. 2.2); PEEL = the S_n-equivariant interior operator `kill_up_n : D_n → A_n` (Prop. 2.3). Gives `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ(A_n))` as S_n-reps.
- **Theorem 4.3 (`A_n` analysis, UNCONDITIONAL).** `A_n^{nt}` carries the S_n-equivariant closure operator `(Q,F)↦(Q,[n])` with `c(A_n^{nt}) ≅ PPF_n` (Prop. 4.1) ⟹ `Δ(A_n^{nt}) ≃_{S_n} Δ_n`. `A_n^t` attaches along contractible down-sets (Prop. 4.2, Lemma L1 + induction on `|F_0|`). ⟹ `H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)` as S_n-reps.
- **Theorem 5.1 (the payoff).** `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` as S_n-reps, all `n≥3`, unconditional. ⟹ **(UCC.1) at level `n` ⟺ Hyp(n)**. The F10 induction becomes: `Hyp(n)` —[F17]→ `(UCC.1)@n` —[+ (UCC.2)@n, F10 §6.2]→ `Hyp(n+1)`.
- **(UCC.2) interaction.** INDEPENDENT — F17 builds the cofiber matching alone; (UCC.2) is about the cross-boundary gluing of `M_n` and `M_rel` (F10 §6.4). F17 neither needs nor produces it.
- **Verdict.** GREEN-equivariant-uniform. (UCC.1) proven for all `n`. Only (UCC.2) remains of (UCC). Route (ii) stays closed (F16); route (iii) stays parked (escalation trigger did not fire).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **F14's reduction** (`docs/compatibility-geometry-F14-pcr-lit2prime.md` §1) — MoveA/MoveB/PEEL, the terminal complex `A_n`, the identity `H̃_d(cofiber) = 2·H̃_{d-1}(Δ(A_n))`. F14 §4.2 explicitly: the *mechanism* is n-uniform but "each level's collapse hypotheses are re-verified computationally, not assumed" — **F17 (Prop. 2.1–2.3) closes exactly this**, proving the hypotheses for all `n ≥ 3` with n-independent arguments.
- **`A_n` convention** — relations are transitively-closed irreflexive sets; `(a,b)` means `a ≺ b`; `Down_n(x) = {b : (n,b)∈x}`, `Up_n(x) = {a : (a,n)∈x}`. (Matches `scripts/compat_geom_cofiber_morse_n4n5.py`.) The `(Q,F)` model: `x = Q ∪ {(n,b) : b∈F}`.
- **Lemma L1 needs `n ≥ 3`** — the witness `r_∗ = (a_1, a_n)` needs the chain to have ≥ 3 elements. The whole program is `n ≥ 3`, so this is the intended regime.
- **Order-homotopy lemma** (Björner, *Topological methods* §10) — a monotone `f : P → P` with `f ≥ id` (closure operator) or `f ≤ id` (interior operator) induces `Δ(P) ≃ Δ(f(P))`; equivariant if `f` commutes with the group action. Used in L1, Prop. 2.3, Prop. 4.1.
- **Theorems 2.4, 4.3, 5.1 are UNCONDITIONAL** — they use no `Hyp`, no `(UCC)`, no per-`n` computation. `(UCC.1) ⟺ Hyp(n)` is an *equivalence*, not a one-way implication: the reduction identity `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` holds with no hypothesis.
- **(UCC.1) is no longer an independent conditional input** of the F10 cohomological core — it is `Hyp(n)` transported through the F17 reduction. The F10 inductive step (F10 §6.2) now consumes only **(UCC.2)** beyond the inductive hypothesis.
- **(UCC.2)** (`δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` injective) is **the sole remaining conditional input**. Independent of the F17 mechanism (D1 §7.3): F17 builds the cofiber matching `M_rel^{eq}` alone; (UCC.2) is about the gluing of `M_n` and `M_rel` (F10 §6.4 Morse phrasing), equivalently `ι_n^∗ = 0` on `H̃^{n-2}` (cofiber-LES phrasing). The recommended F18 target.
- **Route (ii)** closed-negative (F16). **Route (iii)** / mg-b345 PARKED — F17's escalation trigger (AMBER-option-3-stalls) did **not** fire, so route (iii) is *not* a PM/Daniel decision now (contrast F16 §7.4: F16 *did* trigger it; F17 closing GREEN means option 3 succeeded, so the route-(iii) revisit is back off the table).
- **Cohomology vs homology** — F14 / F17 work in homology `H̃_d`; F10 / F16 state (UCC) in cohomology `H̃^k`. Over `ℚ` they agree as S_n-reps here (the reps are sums of self-dual `sgn`). D1 §5 notes this explicitly.
- Trust-surface impact: none. No new axioms, no Lean changes, no HPC.

---

## §4. References

- mg-f893 (F16) — `docs/compatibility-geometry-F16-central-stability-presentation.md`. AMBER-route-ii-stalls. §7.3 (the option-3 pivot — F17's mandate), §0.4 (representation-type half "returns to option 3"), §5 (the (UCC.2)-independence finding F17 §7.3 mirrors). **Parent.**
- mg-3839 (F14) — `docs/compatibility-geometry-F14-pcr-lit2prime.md`, `scripts/compat_geom_cofiber_morse_n4n5.py`. GREEN-cofiber-perfect. §1 (the MoveA/MoveB/PEEL reduction — **the template**), §4.2 ("collapse hypotheses re-verified computationally, not assumed" — **the gap F17 closes**). **THE TEMPLATE.**
- mg-6295 (PCR-Lit-2 / M1) — `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`, `scripts/compat_geom_cofiber_morse_n3n4.py`. GREEN-constructive-cofiber-Morse. `M_rel` perfect `(0,0,2,0)` at `n=3→4`; §6.3/§8.2 (perfection verified only at `n=3→4`; greedy+Forman matching **not** S_3-equivariant — F17 supplies the equivariant matching by a different route).
- mg-8216 (F10) — `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. GREEN-conditional. §3 (Mechanism M1 — **§3.3 perfection n-dependent, open — RESOLVED by F17 §6.2**), §6.2 (the inductive step), §6.3 ((UCC)), §6.4 (M1 → (UCC)).
- mg-8355 (F15) — `docs/compatibility-geometry-F15-e2-partial-test.md`. AMBER-partial3-not-iso. §7.3 option 3 (where the pivot was first documented).
- mg-ecf6 (F13) — `docs/compatibility-geometry-F13-shift-aware-functoriality.md`. GREEN-functoriality-established. Good-pair / triple-LES conventions.
- mg-b352 (F11) — `docs/state-F11.md`. GREEN-route-traction. Route (i) closed-negative; route (iii) parked.
- mg-b345 (F8″) — route (iii), PARKED. F17's escalation trigger did not fire.
- Forman 1998/2002 (discrete Morse theory); Hersh 2005 (cluster lemma); Jonsson 2008 (patchwork theorem); Björner 1995 (*Topological methods* §10 — order-homotopy lemma); Kozlov 2008 (*Combinatorial Algebraic Topology* Ch. 11–13); Quillen 1973 (Theorem A).

---

*Cumulative state doc for mg-4d3a (F17). Session 1 DONE — verdict GREEN-equivariant-uniform. Branch `compat-geom-F17-nuniform-equivariant-morse`. Option 3 closes: the S_n-equivariant cofiber Morse mechanism is n-uniform; (UCC.1) ⟺ Hyp(n), proven for all `n` (both halves); only (UCC.2) remains of (UCC). Route (ii) stays closed; route (iii) stays parked (escalation trigger un-fired).*
