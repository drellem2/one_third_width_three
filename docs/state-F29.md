# State F29 — Bad cut → Čech-bias cohomology class (mg-70b0) — cumulative state

**Ticket:** mg-70b0. **Branch:** `polecat-cat-mg-70b0`. **Parent:** Daniel two Apple-reminder messages 2026-05-15T23:20Z + 2026-05-15T23:38Z (post-F28 AMBER direction). Also F28 (mg-d0fa, **AMBER-framework-unclear**) — F28 walled the *functorial-sheaf-morphism* dialect of mg-26fc U1; F29 pursues the **chain-level / non-functorial** Daniel-articulated mechanism.
**Type:** paper-and-pencil structural scoping; no HPC; no Lean; no new axioms; no computation.
**Status:** multi-session-able; session 1 delivered.
**Verdict (after session 1):** **AMBER-one-load-bearing-residual** — the Daniel-articulated Čech-bias mechanism operationalises at the Čech-2-cocycle level; the chain-level cochain map `\Phi` (F29-OP) is the one load-bearing residual; F30 is the polecat-attackable target. U1-dialect-collision structurally dissolved, conditional on F30 operational delivery.

---

## Session 1 — 2026-05-15 → 2026-05-16 (scoping session, complete)

### Inputs read

- **`docs/compatibility-geometry-F28-sheaf-cohomology-on-POSET.md`** (full, 822 lines) — F28. The framework-search predecessor: AMBER-framework-unclear with the functorial-sheaf-morphism `F_{BK} → F_ℓ` gap (§7.6, §8.2). F29 takes Daniel's directive R1 ("inherently but not functorially") as explicit non-functorial mode that waives F28's functoriality requirement.
- **`docs/state-F28.md`** (full, 125 lines) — F28 cumulative ledger. Confirms F28 barrier = mg-26fc U1 in sheaf-theoretic dialect.
- **`docs/compatibility-geometry-F27-spectral-to-cohomology-scoping.md`** (partial, §0–§4.2) — F27 RED-mechanism-mismatch. The three walled literal-comparison candidates (Garland-on-Δ, ICOP↔Cheeger, F17+F18-as-Step-8-replacement). F29 is *not* one of these; F29 is the Daniel-articulated Čech-bias direction, structurally distinct.
- **`docs/state-F27.md`** (full, 82 lines) — F27 ledger; the three internal routes wall summary.
- **`docs/compatibility-geometry-structural-analogy-scoping.md`** (full, 325 lines) — mg-26fc. **§4.4 (U1, U2, U3)** — the three would-be bridges; F29's U1-collision-check baseline (§6 of F29 doc).
- **`docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`** (partial, §0.1–§0.4, §1) — F17. **(UCC.1) ⟺ Hyp(n) unconditionally;** `\widetilde H_d(Δ_{n+1}/Δ_n) ≅ 2·\widetilde H_{d-1}(Δ_n)` as `S_n`-reps.
- **`docs/compatibility-geometry-F18-ucc2-delta-injective.md`** (partial, §0.1–§0.4, §1) — F18. **Null-homotopy theorem; (UCC) complete; F10 cohomological core unconditional.** Together F17+F18 give: `\widetilde H^k(Δ_n; \mathbb{Q}) = \mathrm{sgn}_{S_n}` for `k = n-2`, `0` else (in degrees ≥ 1), all `n ≥ 3` — the F29 cohomology anchor.

### Findings, ordered

#### F29.1 — Setup: what Daniel articulated, parsed precisely

Daniel reminder 1 (2026-05-15T23:20Z): rules out factorial constructions; rules out functoriality; specifies the mechanism is *bad cut → cohomology class* via local biases on subposet refinements. *"For instance if we show bad cut -> nonspherical cohomology we could be done."*

Daniel reminder 2 (2026-05-15T23:38Z, ≈ 18 min later): names the assembly — bias on each subposet, contradicts in intersections, gives the cohomology class; the not-sign-like step *"sign is 100% boundary, highly commuting and the bad cut is the opposite."*

F29 parses these as a five-piece program (F29 doc §0.1):
- (D-1) bad cut = bias = low-conductance pair-cut;
- (D-2) local biases on subposet refinements;
- (D-3) contradictions on intersections → Čech-style class;
- (D-4) F17+F18 anchor (only sign-like at degree n-2);
- (D-5) not-sign-like step (sign is boundary/commuting; bad cut is opposite).

#### F29.2 — Subposet reading + bias function

F29 commits to **"subposet" = refinement `P' \ge P` in `PPF_n`** (F29 doc §1.2). The bias function `b_{P'}(x, y) := \Pr_{P'}[x <_{P'} y] - 1/2` is well-defined on the case-(R-a) sub-up-set (`(x, y)` incomparable in `P'`) and degenerates to `\pm 1/2` on case-(R-b) (`(x, y)` resolved in `P'`). The bias is `\mathrm{Stab}_{S_n}\{x, y\}`-equivariant with sign and bounded `|b_P| \ge \gamma/2` for γ-counterexample `P`.

#### F29.3 — The Čech cover (Č-1) and the bias sheaf `F_{\mathrm{bias}}`

For a fixed bad pair `(x, y)`, the up-set `↑P` partitions into three strata `U_\parallel, U_{\le}, U_{\ge}` (F29 doc §2.1, eq Č-1). The bias-sheaf `F_{\mathrm{bias}}` assigns three separate `\mathbb{Q}`-lines to the three strata (F29 doc §3.2), with affine restriction maps `b \mapsto \pm 1/2 - b` carrying the bias-jump amounts.

#### F29.4 — Naive Čech 1-cocycle is trivial; non-trivial class needs orbit-relaxation

The single-pair Čech 1-cocycle `\widetilde \psi_{\mathrm{BC}}^{(x, y)}` is **trivial in cohomology** as the coboundary of the globally-defined section `\widetilde b^{(x, y)}` (F29 doc §3.2, end). The non-trivial cohomological class lives in the **`S_n`-orbit-Čech complex** over the multi-pair cover, where strata for different pairs are *incompatible* — this gives a non-trivial Čech 2-cocycle `\widetilde \psi_{\mathrm{BC}}^{(2)}` measuring inter-pair-stratification contradictions (F29 doc §3.4).

#### F29.5 — Chain-level evaluation `\mathrm{eval}^{(x, y)}` (non-functorial)

A chain-level cochain map `\mathrm{eval}^{(x, y)}` sends `\widetilde \psi` to `c \mapsto \prod_i \Pr_{P_i}[x <_{P_i} y]` on chains where `(x, y)` is the cover relation at every step (F29 doc §4.3). This is **not a sheaf morphism** — explicitly respects Daniel R1's "not functorially" directive — but is a cochain map sending cocycles to cocycles. The output is a cocycle representative of `\omega_{bal}^{(n)}` up to scalar.

#### F29.6 — Not-sign-like step: precise (NS-a)/(NS-b) either-or-contradiction

If the bad cut's Čech 2-cocycle `\widetilde \psi_{\mathrm{BC}}^{(2)}` is non-trivial in `\check H^2(\ldots, F_{\mathrm{bias}}^{\mathrm{orb}})` but its image under `\mathrm{eval}^{\mathrm{orb}}` is a coboundary in `H^{n-2}(\Delta_n, \mathbb{Q})`, then either (NS-a) `F_{\mathrm{bias}}^{\mathrm{orb}}` carries strictly more cohomology than `\underline{\mathbb{Q}}` in the relevant degree (contradicting F17+F18 "only sign-like") or (NS-b) `\widetilde \psi_{\mathrm{BC}}^{(2)}` is forced exact (contradicting bad cut's non-trivial existence). Either way: contradiction — closing milestone-1 part (iii) (F29 doc §5.2).

#### F29.7 — Heuristic sgn-orbit-cancellation argument supports (NS-b)

The `S_n`-orbit-sum `\sum_g \mathrm{sgn}(g) \cdot b_{g \cdot P'}(g \cdot x, g \cdot y) = b_{P'}(x, y) \cdot \sum_g \mathrm{sgn}(g) = 0` (the alternating sum vanishes for `n ≥ 2`). This gives `c_{\mathrm{BC}}(P) = 0` — the `\mathrm{sgn}`-isotype-image vanishes, supporting (NS-b). **But the argument is load-bearing: §5.4 of F29 doc identifies a bookkeeping catch — the chain-level `\mathrm{eval}^{(x, y)}` is only defined on chains where `(x, y)` is the cover relation at every step, a sparse subset of all chains, and the F17+F18 constraint may not transpose to the subcomplex restriction.**

#### F29.8 — The load-bearing residual: F29-OP (chain-level cochain map `\Phi`)

F29 names the one load-bearing residual: explicit construction of `\Phi : \check C^2 \to C^{n-2}(\Delta_n, \mathbb{Q})` on **all chains** (not just bad-pair-cover-relation chains), with the orbit-sum well-defined and `c_{\mathrm{BC}}(P)` rigorously computed (F29 doc §5.5). **This is the F30 target.**

F30 should:
1. Define `\Phi` explicitly on all chains of `\Delta_n` (likely candidate: extend `\mathrm{eval}^{(x, y)}` by summing over chains containing `(x, y)` as some cover relation).
2. Verify `\Phi` is a cochain map.
3. Compute `c_{\mathrm{BC}}(P)` explicitly.
4. Pin (NS-a) vs. (NS-b) outcome.
5. Verify no hidden functoriality (dissolve criterion §6.2 of F29 doc met).

F30 is a *calculation*, not a framework search; single-session polecat-attackable; budget ≈ 400k–500k tokens.

#### F29.9 — U1-dialect-collision check (conditional dissolve)

mg-26fc U1 demands a refinement-respecting bridge `\mathcal{B}_P` from BK-data to F-series cohomology. F27 walled it for the literal-complex dialect; F28 walled it for the functorial-sheaf-morphism dialect. F29's chain-level cochain map `\Phi` is operationally lighter — Daniel directive R1 explicitly waives the refinement-functoriality requirement (F29 doc §6).

**Dissolve criterion:** `\Phi` is defined chain-level, sends cocycles to cocycles, respects `S_n`-action on cohomology classes, and is not secretly a sheaf morphism in disguise. **Collision criterion:** the orbit-sum argument hides a refinement-functorial dependence.

**Assessment.** Structurally, F29 dissolves U1 — Daniel's "not functorially" is the explicit non-functorial mode. Operationally, the chain-level `\Phi` construction has not been written; the relabelling-equivariance argument of §5.3 of F29 doc is *not* the F28-walled refinement-functoriality (it's relabelling, not refinement), but operational delivery is required to confirm no hidden dependence. **Conditional dissolve.**

#### F29.10 — Verdict: AMBER-one-load-bearing-residual

The Daniel-articulated mechanism operationalises at the bias-cochain → Čech-2-cocycle level (§2, §3 of F29 doc). F17+F18 anchor the "only sign-like cohomology" statement (§4). The not-sign-like step has a precise (either-or) reading with a heuristic vanishing argument (§5). The chain-level cochain map `\Phi` (F29-OP) is the one load-bearing residual (§5.5, §7.3). U1-dialect-collision structurally dissolved by Daniel's directive R1, conditional on F30 operational delivery (§6).

**Not GREEN** because F29-OP is not delivered (no explicit `\Phi` on all chains; no rigorous `c_{\mathrm{BC}}(P)` computation; no pinned (NS-a)/(NS-b) outcome). **Not RED** because the mechanism is plausible at every step and the residual is *one calculation* away from operational, not a research project of unknown size. AMBER-one-load-bearing-residual is the structurally accurate verdict.

### Deliverables (session 1)

- `docs/compatibility-geometry-F29-cech-bias-cohomology.md` — the F29 scoping doc (~600 lines), with §0 setup + §1 bad-cut precise + §2 Čech cover + §3 Čech-bias cocycle construction + §4 F17+F18 anchor + §5 not-sign-like step + §6 U1-dialect-collision check + §7 establishes/doesn't + §8 barrier + §9 references.
- `docs/state-F29.md` (this file).

### Trust surface

**Unchanged.** Paper-and-pencil scoping only. No Lean changes, no new axioms, no HPC, no computation. The F10 cohomological core (parts (i)–(ii), UNCONDITIONAL post F17+F18), F17, F18, F19–F23 chamber-Morse arc (parked), mg-b345 (route iii / Quillen fiber, parked), the in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact (separate), the methodology paper draft (separate), and `main.tex` + Steps 1–8 (unchanged — Route B remains mathematically correct conditional on Hyp A) are all untouched.

### Open scope items

- **F30 target:** explicit chain-level cochain map `\Phi` (F29-OP). Polecat-attackable as a single-session calculation; budget ≈ 400k–500k tokens.
- **F29-OP residual on hidden functoriality:** verify the orbit-sum argument's use of relabelling-equivariance does not hide a refinement-functorial dependence (dissolve criterion §6.2 of F29 doc).
- **Cross-thread coordination — union-closed emulation.** F29's chain-level / non-functorial mode is a *concrete* framework union-closed can emulate (per Daniel directive 2026-05-15T20:22Z), operationally lighter than F28's framework-search mode.
- **Width-3 bridge connection.** Even if F29 (via F30) closes the not-sign-like step at general `n`, the F10 §7.4 width-3 bridge remains a separate piece — F29 gives a cohomological obstruction at general `n`; connecting it to the width-3 conjecture statement requires an additional step not delivered in F29.

### Protocol log

- 2026-05-15 (claim) — claimed mg-70b0 at 2026-05-15T23:45:43Z; registered `pogo schedule` mail-check on `*/10 * * * *` (id `mail-check-mg-70b0`).
- 2026-05-16 (session 1) — read F28 doc (full) + state-F28 + F27 doc (partial) + state-F27 + mg-26fc (full) + F17 partial + F18 partial; wrote F29 scoping doc + state ledger; ready to commit.

---

## Future sessions

This is a multi-session ticket. If F30 lands (the load-bearing F29-OP), F29's verdict upgrades:
- **GREEN-closes-part-(iii)** if F30 explicitly delivers `\Phi`, computes `c_{\mathrm{BC}}(P) = 0`, confirms (NS-b) branch with no hidden functoriality, and the closure of milestone-1 part (iii) is operational.
- **AMBER-residual-narrowed** if F30 delivers `\Phi` but the (NS-a)/(NS-b) outcome surfaces an unforeseen complication.
- **RED-collision** if F30 surfaces a hidden refinement-functorial dependence (collision criterion §6.2 of F29 doc), in which case F29 hits U1 in a third dialect.

The remaining session work, if F29 is reopened pre-F30:
(i) Refine §3's Čech 2-cocycle definition for specific small `n` examples (e.g., `n = 4` width-3 γ-counterexamples) to surface concrete obstructions or surprises.
(ii) Explore alternative readings of "bias on subposet" — e.g., a *different* sub-up-set than `↑P`, or a different stratification than (Č-1).
(iii) Sharpen the (NS-a) branch — if `\Phi` cannot land in `H^{n-2}(\Delta_n, \mathbb{Q})` cleanly, perhaps it lands in a strictly larger module (`\mathrm{sgn}` plus extra content), and F17+F18 forbids this directly.
