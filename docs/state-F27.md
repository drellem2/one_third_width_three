# State F27 — Spectral → cohomology hybrid scoping (mg-a3e3) — cumulative state

**Ticket:** mg-a3e3. **Branch:** `polecat-cat-mg-a3e3`. **Parent:** mg-c6f2 (F25, RED). Daniel-pre-positioned fallback per 2026-05-15T09:06Z + `project_spectral_to_cohomology_fallback` memory.
**Type:** paper-and-pencil structural scoping; no HPC; no Lean; no new axioms; no computation.
**Status:** single-session, delivered.
**Verdict:** **RED-mechanism-mismatch** — the spectral → cohomology hybrid bridge does not exist in operational form; all three candidate operationalisations fail for different concrete reasons; none of these failures is the F25 K_0(γ, w) 1/γ-blowup reproducing.

---

## Session 1 — 2026-05-15 (sole session, complete)

### Inputs read

- **`docs/compatibility-geometry-F25-hypothesis-A-constants-audit.md`** (full, 367 lines) — the parent. F25 §3 (cubic γ-decay derivation); §5.1 (`K_0(γ, w)` precisely located in `lem:layered-reduction` G3); §5.2 (F26-equivalent rewrite declined as structural-research-grade); §5.4 (both F24 routes have located gaps).
- **`docs/compatibility-geometry-F24-route-fork-comparison.md`** (partial, key sections) — F24 §0–§1.3 (the BK/Cheeger spine; Hyp A's place; the `∃T` collapse); §4 (F25 scope and the three outcome verdicts).
- **`docs/compatibility-geometry-structural-analogy-scoping.md`** (full, 325 lines) — mg-26fc. The GREEN-distinct-complementary finding. **§4.2 (the Garland meta-principle)** — the bridge F27 makes precise. **§4.3 (resonance not identity)** — the inter-complex mismatch identified pre-F25. **§4.4 (U1/U2/U3, the three would-be bridges)** — the candidates F27 operationalises.
- **`docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`** (partial, §0.1–§0.4) — F17. GREEN-equivariant-uniform. The n-uniform `S_n`-equivariant cofiber Morse reduction: `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` unconditionally. (UCC.1) ⟺ Hyp(n).
- **`docs/compatibility-geometry-F18-ucc2-delta-injective.md`** (partial, §0.1–§0.4) — F18. GREEN-ucc2-proven. The null-homotopy theorem: `ι_n : Δ_n ↪ Δ_{n+1}` null-homotopic, hence `δ_n` injective. (UCC.2) holds for all `n`. **(UCC) COMPLETE; F10 cohomological core (parts (i)–(ii)) UNCONDITIONAL.**
- **`/Users/daniel/research/one_third_width_three/step8.tex`** (partial, key sections) — `lem:layered-reduction` (lines 2199–2311): the actual K_0 expression in the worktree is `K_0 = max(2w+2, ⌈2/γ⌉ + 6w + 4)` (proof, lines 2224–2226), not the slightly simpler `2w/γ + 4` quoted in F25 §2.1; F27 uses the worktree form. The structural `1/γ` content is identical (it's `⌈2/γ⌉` not `2w/γ`, but the upshot — `K_0 ∼ Θ(1/γ)` for fixed `w` — is unchanged).

### Findings, ordered

#### F27.1 — Setup: what the hybrid is supposed to be

Daniel 2026-05-15T09:06Z: *"If a direct contradiction doesn't work perhaps you can go directly from spectral behavior → cohomology."* Read as: route Theorem E's low-conductance pair-cut (BK spectral input, *unconditional*) into the F-series cohomological world (post F17+F18, *unconditional*), and obtain a γ-uniform contradiction there — bypassing Hyp A.

#### F27.2 — The F17+F18 unconditional core, restated

`H̃^k(Δ_n; ℚ) = 0` for `0 < k < n − 2`, `= sgn_{S_n}` for `k = n − 2`, all `n ≥ 3`, *unconditional*. `ω_bal^{(n)} ∈ H̃^{n-2}(Δ_n)^sgn` exists, unique up to scalar, pairs non-trivially against the canonical critical `(n−2)`-cell. **What is *not* delivered by F17+F18:** the *width-3 bridge* — for every width-3 `P`, some chain `c` through `P` with `⟨ω_bal, c⟩ ≠ 0`; the *(ICOP-step)* per-step control along `c` to `[3/11, 8/11]`. Both verified `n ≤ 6`; both open at general `n` (F23 §4–§5 HPC-per-n verdict on Route A).

#### F27.3 — The F25 barrier, recapped operationally

The 1/γ blowup in `K_0` of `lem:layered-reduction` (G3) gates the Hyp-A cascade closure for the small-γ tail. **Theorem E itself is unconditional** and γ-uniform-in-conclusion (`Φ(S) ≤ 2/(γn)` for a low-conductance pair-cut). The hybrid is *allowed* to use Theorem E as input; it sidesteps only if it does not invoke `lem:layered-reduction` deep-`K`.

#### F27.4 — The three candidate bridges, each fails

| candidate | what it would do | failure mode | locus |
|---|---|---|---|
| **1 — Garland on `Δ(PPF_n)`** | invert Garland: F17+F18 non-vanishing ⟹ some vertex link of `Δ(PPF_n)` has small spectral gap; identify that link's spectral gap with `G_BK(P)`'s Cheeger; contradict Theorem E | links of `Δ(PPF_n)` live on `PPF_n` (order complexes of refinement intervals); `G_BK(P)` lives on `L(P)` (linear extensions); **different combinatorial objects, no natural map** | mg-26fc §3.4 ✗ row, sharpened operationally |
| **2 — ICOP pairing ↔ BK Cheeger (mg-26fc U2)** | bridge `⟨ω_bal^{(n)}, c⟩ ≠ 0` ⟺ `Φ(G_BK(P)) ≥ Φ_0 > 0`; combined with Theorem E (`Φ ≤ 2/(γn)`), get contradiction for `n ≥ 2/(γΦ_0)` — γ-uniform, no K_0 | F-series pairing is a *per-step volume fraction* (`p_xy ∈ [3/11, 8/11]`); BK Cheeger is a *whole-cut conductance*; **the two quantities don't translate** — one controls one cut's volume, the other a cut's boundary-to-volume ratio | mg-26fc §4.4 (U2), still not bridged |
| **3 — F17+F18 replaces `lem:layered-reduction`** | substitute the F-series unconditional core into Step 8 to produce balanced pairs without K_0(γ, w) | **(a)** to use F17+F18 per-`P`, need the F10 part-(iii) width-3 bridge, which is itself open at general `n` — circular; **(b)** F17+F18 has no γ-input, so can't output a γ-dependent threshold — scope-blind | F-series core is global over `Δ(PPF_n)`; `lem:layered-reduction` is local at one size-minimal `P` |

#### F27.5 — Why RED, not AMBER

F27 ticket spec: AMBER-hybrid-inherits = "the K_0 1/γ-blowup reproduces somewhere in the bridge." F27 finding: **the bridge walls before reaching `lem:layered-reduction`**; the K_0 1/γ-blowup does *not* reproduce because the hybrid never gets there. RED-mechanism-mismatch is the structurally accurate description: "the Garland bridge does not actually exist in a form that connects BK spectral data to `Δ(PPF_n)` cohomology in the relevant regime; mg-26fc's distinct-but-resonant finding was about a more abstract resonance than a usable bridge." The two verdicts share the same *practical consequence* (Daniel-level escalation, milestone-1 redefinition next decision), but the mechanism description differs.

#### F27.6 — Operational consequence: three internal routes walled

| route | wall | nature |
|---|---|---|
| Route A — chamber-Morse HPC-per-n | F23 §4–§5: no `n`-uniform structural discriminator survives the 3-datapoint record; HPC-per-n | open structural research, evidence-disfavoured |
| Route B — BK/Cheeger | F25 §3: `K_0(γ, w) ∼ ⌈2/γ⌉` forces cubic γ-decay of Hyp-A LHS | structural to window-removal |
| Route Hybrid — spectral → cohomology | F27 §4: inter-complex mismatch / quantitative mismatch / scope mismatch; no operational bridge | structural research, missing comparison map |

**Milestone 1 part (iii) is not closed by any of the three documented internal routes.** The mayor's option 3 from F25-RED relay ("milestone-1 redefinition") is now operationally indicated. Plausible redefinition directions (F27 §6.3, not recommendations — Daniel/PM call): (1) accept Route B's small-γ-tail hole and narrow milestone 1; (2) settle for the `n ≤ 6` verified form + the unconditional cohomological certificate at all `n`; (3) reactivate mg-b345 (route iii / Quillen fiber); (4) cross-route patching (Route A small-`n` + Route B large-`n` large-γ, residual small-γ-large-`n` tail flagged).

### Deliverables

- `docs/compatibility-geometry-F27-spectral-to-cohomology-scoping.md` (~17k words) — the scoping doc, with full Garland-bridge precision + three-candidate walk + RED verdict + operational consequence.
- `docs/state-F27.md` (this file).

### Trust surface

**Unchanged.** Paper-and-pencil scoping only. No Lean changes, no new axioms, no HPC, no computation. The F10 cohomological core (parts (i)–(ii), UNCONDITIONAL post F17+F18), the F19–F23 chamber-Morse arc (parked), mg-b345 (route iii / Quillen fiber, parked), the in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact (separate), the methodology paper draft (separate), and `main.tex` + Steps 1–8 (unchanged — Route B remains mathematically correct conditional on Hyp A) are all untouched.

### What F27 does not establish / what F28 would have been

F27 does not propose a F28 sub-ticket — no candidate operationalisation supports one. The next decision is program-shape (milestone-1 redefinition), not research-execution. If Daniel/PM chooses to pursue a hybrid-style attack regardless, the most concrete entry point would be **constructing a per-`P` complex `K(P)` whose Garland data identifies with the spectral data of `G_BK(P)` AND that admits a comparison map to `Δ(PPF_n)`** (mg-26fc §4.4 U1). This is a research project of unknown size, not a polecat-attackable scoping pass.

### Open questions / open scope items

- Whether the resonance (mg-26fc §4.2 Cheeger / Garland / Linial–Meshulam–Wallach / Gromov) admits a future deep operationalisation. F27 documents that no such operationalisation is in hand and that the most direct candidates fail for concrete reasons; F27 does not refute the *possibility* of a future bridge, only its current existence.
- Whether the F-series width-3 bridge (F10 §7.3–§7.4) can be closed at general `n` without the F19–F23 chamber-Morse HPC-per-n character. This is a separate F-series question that F23 surfaced and F27 does not advance.
- Whether `lem:layered-reduction` admits a γ-independent rewrite (F25 §5.2 declined as structural-research). Not advanced by F27.

### Protocol log

- 2026-05-15 — claimed mg-a3e3; registered `pogo schedule` mail-check on `*/10 * * * *`; read F24, F25, mg-26fc, F17, F18 + step8 `lem:layered-reduction`; wrote scoping + state; ready to commit.

---

*Single-session F27; ledger frozen at session 1 close. F27 closes the third documented option (spectral → cohomology hybrid) with a clean, named-failure-mode verdict (RED-mechanism-mismatch), surfacing the Daniel-level milestone-1 redefinition trigger. The fallback memory `project_spectral_to_cohomology_fallback` has now been consumed and a follow-on memory update (if Daniel/PM elects) should record the actual outcome.*
