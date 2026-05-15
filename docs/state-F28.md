# State F28 — Sheaf cohomology on POSET (the category) as the spectral → cohomology bridge (mg-d0fa) — cumulative state

**Ticket:** mg-d0fa. **Branch:** `polecat-cat-mg-d0fa`. **Parent:** Daniel reminders 2026-05-15T19:59Z (intuition outline) + 2026-05-15T20:22Z (start immediately on the program; union\_closed lower priority and should emulate). Also mg-a3e3 (F27, **RED-mechanism-mismatch**) — F27 walled the *literal* complex-comparison-map candidates; F28 pursues the **categorical / sheaf-theoretic** framework Daniel pre-positioned.
**Type:** paper-and-pencil structural scoping; no HPC; no Lean; no new axioms; no computation.
**Status:** multi-session-able; session 1 delivered.
**Verdict (after session 1):** **AMBER-framework-unclear** — the framework is well-defined and operational at the constant-coefficient level (F17+F18 lands unconditionally), but no candidate BK-derived sheaf on `PPF_n` admits the sheaf-morphism that would let F17+F18 forbid low-conductance configurations.

---

## Session 1 — 2026-05-15 (scoping session, complete)

### Inputs read

- **`docs/compatibility-geometry-F27-spectral-to-cohomology-scoping.md`** (full, ≈ 429 lines) — the parent. F27 §4 (the three walled candidates: Garland-on-Δ, ICOP↔Cheeger, F17+F18-as-Step-8-replacement); §5.4 (RED-mechanism-mismatch rationale); §6 (three internal routes walled, milestone-1 redefinition); §7.2 (what F27 does not establish, including the U1-flavoured future direction).
- **`docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`** (partial, §0.1–§0.4, §1) — F17. GREEN-equivariant-uniform. `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` unconditionally; (UCC.1) ⟺ Hyp(n).
- **`docs/compatibility-geometry-F18-ucc2-delta-injective.md`** (partial, §0.1–§0.4, §1) — F18. GREEN-ucc2-proven. The null-homotopy theorem; (UCC.2) holds for all `n`. **(UCC) COMPLETE; F10 cohomological core (parts (i)–(ii)) UNCONDITIONAL.**
- **`docs/compatibility-geometry-poset-cohomology-scoping.md`** (full, ≈ 1000 lines) — mg-d60d. The original categorical / sheaf-cohomology scoping. The (T3) topology + Mitchell / Alexandrov cohomology + the `F_\ell` line bundle + the trivialisation `F_\ell \cong \underline{\mathbb{Q}}` via `β_P = |L(P)| · α_P` + the (C1)/(C2)/(C3) load-bearing conditional inputs. Verdict AMBER-specialist-conditional on cat-mg-5ee2. **F17+F18 close (C1) unconditionally**, upgrading the AMBER state.
- **`docs/compatibility-geometry-posn-sphere-scoping.md`** (partial, §1–§2.2) — mg-5ee2. The sibling sphere-topology scoping; mg-d60d's load-bearing dependency.
- **`docs/state-F27.md`** (full, ≈ 80 lines) — F27's state ledger; protocol log; the three walled internal routes.

### Findings, ordered

#### F28.1 — Setup: what the framework is supposed to be (Daniel's outline)

Daniel 2026-05-15T19:59Z: subposets of bk graph are uniform/expander-y; low-conductance cut is non-uniform; cohomology of the category of posets should stitch locally uniform pieces; cohomology related to poset + subposets; well limited by F17+F18.

F28 frame: small category `\mathcal{C}` = `PPF_n` with refinement morphisms (the F-series proper-and-proper sub-lattice), Alexandrov topology (every presheaf = sheaf), Mitchell / Baues–Wirsching cohomology theory. *Distinct from F27's literal-comparison-map approach* — F28 is categorical / sheaf-theoretic, not bridge-between-two-complexes.

#### F28.2 — F17+F18 unconditional categorical-cohomology input

Via Mitchell (1972): `H^k(PPF_n, \underline{\mathbb{Q}}) ≅ \widetilde H^k(\Delta_n; \mathbb{Q})` (plus `\mathbb{Q}` in degree 0). F17+F18 give: `H^k(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` in degree `n - 2`, else `0` (in degree `\ge 1`), all `n \ge 3`, **unconditional**.

`\omega_{bal}^{(n)} \in H^{n-2}(PPF_n, \underline{\mathbb{Q}})^{sgn}` exists, unique up to scalar, *unconditional*. Cocycle representative: `\omega(P_0 < \ldots < P_{n-2}) = \prod_i \Pr_{P_i}[a_i <_{P_i} b_i]` along the chain (mg-d60d §3.4). Non-vanishing on the canonical critical chain `c^*_n` *unconditional* (P-1 + P-4).

#### F28.3 — mg-d60d (C1) closed unconditionally by F17+F18

mg-d60d's load-bearing dependency on cat-mg-5ee2 — *is `\Delta(\overline{Pos_n^{sub}})` a topological sphere?* — is closed by F17+F18 *rationally and equivariantly*: `\Delta_n \simeq_\mathbb{Q} S^{n-2}` carrying `sgn_{S_n}` on top cohomology. This is the H-Cox + sgn theorem.

**Strict positive vs. mg-d60d.** F28 framework operates *unconditionally* on the cohomological side; only the bridge to BK-spectral data is unclear. mg-d60d's AMBER-specialist-conditional → F28's AMBER-framework-unclear-without-conditional.

#### F28.4 — Candidate sheaves (a)–(d) all wall, each differently

| candidate | what it would encode | functoriality of BK content | F17+F18-constraint |
|---|---|---|---|
| (a) `F_{cut}` | vertex sets `L(P)` | yes (induced restriction) | none (no canonical morphism `F_{cut} \to \underline{\mathbb{Q}}`) |
| (b) `F_{Lap}` | Laplacian spectra | **no** (induced-subgraph spectra ≠ restrictions) | none |
| (c) `F_{Cheeger}/F_{TE}` | optimal-cut conductance / Theorem-E witnesses | **no** (Cheeger not functorial) | none canonical |
| (d) `F_{obs}` | abstract SES `0 → F_{low} → F_{tot} → F_{unif} → 0` | not in hand (depends on (b)/(c)) | none in hand |

**The fundamental wall.** Refinement of `P` corresponds to induced-subgraph restriction on `G_{BK}(P)`, which is *not* spectrum-preserving / Cheeger-preserving / expansion-preserving. So a sheaf encoding *spectral / cut content* of `G_{BK}(P)` does not have natural restriction maps that preserve this content.

#### F28.5 — Three F17+F18 constraint mechanisms walk

| mechanism | what it would do | wall |
|---|---|---|
| 1 — global-sections (`\Gamma(F) = \mathbb{Q}^{sgn}` form) | F17+F18 controls `\Gamma(\underline{\mathbb{Q}}) = \mathbb{Q}`; lift via sheaf morphism `F \to \underline{\mathbb{Q}}` to constrain `F` | no canonical morphism `F_{cut} \to \underline{\mathbb{Q}}` (augmentation doesn't commute with restriction) |
| 2 — hypercohomology / spectral sequence | place `F` in a complex `F^\bullet` and use F17+F18 control of `H^q(\underline{\mathbb{Q}})` to constrain `\mathbb{H}^*(F^\bullet)` | requires the SES `0 \to F_{BK} \to F_{tot} \to F_\ell \to 0`; same wall as mechanism 1 |
| 3 — representability / Yoneda | natural transformation `F_{BK} \Rightarrow \underline{\mathbb{Q}}` | same wall |

All three mechanisms require a *canonical sheaf morphism* between a BK-derived sheaf and `F_\ell \cong \underline{\mathbb{Q}}`. None exists.

#### F28.6 — Locality-to-globality formalises only in the constant-coefficient regime

The operational regime: `F = F_\ell \cong \underline{\mathbb{Q}}`. Theorem (F28 candidate, conditional): chain-uniformity of `c` (per-step Pr's in `[3/11, 8/11]`) ⟺ non-vanishing of `\langle \omega_{bal}^{(n)}, c \rangle`. Unconditional for `c^*_n`; conditional for arbitrary width-3 `P`'s chain (F10 §7.4 width-3 bridge, open at general `n`).

The BK-spectral regime Daniel's intuition wants is *not* formalised — same wall as §3 / §5.

#### F28.7 — Verdict: AMBER-framework-unclear

The framework lands *halfway*: F17+F18 *does* unconditionally constrain `H^*(PPF_n, \underline{\mathbb{Q}})`, *does* unconditionally produce `\omega_{bal}^{(n)}`, and *does* provide a categorical home for the F-series ICOP target. But the specific BK-spectral sheaf + F17+F18-constraint combination is not in hand.

**Not GREEN** (no BK-side operational mechanism), **not RED** (framework has unconditional content on the constant-coefficient side). AMBER-framework-unclear, per the ticket spec.

#### F28.8 — Operational consequence: same as F27 (milestone-1 redefinition pending)

F28 does *not* propose a F29 sub-ticket that closes milestone 1 part (iii). The most concrete continuation is mg-26fc §4.4 U1 in sheaf-theoretic dialect — construct an explicit comparison sheaf morphism between a BK-stalk sheaf and `F_\ell` — and this is a research project of unknown size, not polecat-attackable.

Three named F29 directions (§8.1):
- **F29-A:** construct the sheaf morphism (research-project-grade)
- **F29-B:** are links of `\Delta_n` rationally spherical? (polecat-attackable structural scoping)
- **F29-C:** formalise the constant-coefficient regime as F-series ICOP target re-casting (polecat-attackable documentation pass)

None closes the part-(iii) gap. F27's three-routes-walled state stands; milestone-1 redefinition remains the Daniel/PM-level decision.

#### F28.9 — Precise F28 barrier (§8.2)

> F17+F18 unconditionally pin `H^k(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` in degree `n - 2`. The framework's load-bearing missing piece is a canonical sheaf morphism `\phi : F_{BK} \to F_\ell` where `F_{BK}` is a sheaf on `PPF_n` whose stalks encode BK-spectral / cut data faithfully and functorially under refinement. No candidate sheaf is both functorial under refinement and admits the required morphism. The barrier is structurally identical to mg-26fc §4.4 U1, recast in sheaf-theoretic dialect.

### Deliverables (session 1)

- `docs/compatibility-geometry-F28-sheaf-cohomology-on-POSET.md` — the scoping doc (≈ 700 lines), with the framework setup + candidate-sheaf survey + F17+F18-constraint-mechanism walk + AMBER verdict + operational consequence.
- `docs/state-F28.md` (this file).

### Trust surface

**Unchanged.** Paper-and-pencil scoping only. No Lean changes, no new axioms, no HPC, no computation. The F10 cohomological core (parts (i)–(ii), UNCONDITIONAL post F17+F18), F17, F18, F19–F23 chamber-Morse arc (parked), mg-b345 (route iii / Quillen fiber, parked), the in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact (separate), the methodology paper draft (separate), and `main.tex` + Steps 1–8 (unchanged) are all untouched.

### Open scope items

- **F29-A:** the sheaf-morphism construction (the §7.6 / §8.2 gap). Research project of unknown size; not polecat-attackable.
- **F29-B:** rational sphericity of links `\text{lk}_{\Delta_n}(P)`. Side question (§2.3); polecat-attackable structural scoping; would refine F17+F18 to up-set / link level.
- **F29-C:** formal categorical-language re-casting of the F-series ICOP target. Documentation pass.
- **What if F29-A succeeded?** It would not by itself close part (iii) — it would set up the F17+F18 constraint mechanism on the BK side, but actually deriving "low conductance forbidden" would require an additional argument relating the constrained cohomology class to the BK Cheeger constant. Both pieces would need to land.
- **Cross-thread coordination.** Daniel's directive (2026-05-15T20:22Z) said union\_closed should emulate F28's program. If F28 lands AMBER (as it does), the emulation target for union\_closed is "a categorical framework with F17+F18-style unconditional cohomology side but unclear bridge to the structural lemma side" — a known-AMBER target shape, not a known-GREEN.

### Protocol log

- 2026-05-15 — claimed mg-d0fa; registered `pogo schedule` mail-check on `*/10 * * * *`; read F27 (full), F17 (partial), F18 (partial), mg-d60d (full), mg-5ee2 (partial), state-F27; wrote scoping doc + state ledger; ready to commit.

---

## Future sessions

This is a multi-session ticket. Future sessions can:

(i) Refine §3's candidate-sheaf analysis by walking specific sub-cases (e.g., what does `F_{cut}` cohomology *actually* compute? Does it have a Künneth-like decomposition over `S_n`-orbits?).

(ii) Pursue F29-B as a structural scoping question (link cohomology refinement).

(iii) Attempt a more concrete `F_{BK}` candidate — e.g., a *cellular* sheaf that decomposes spectra by cellular pieces of `PPF_n`'s order complex, with explicit refinement-compatible structure. Daniel's "cohomology of category of posets" reading might admit a cellular variant that doesn't have the §3 functoriality issue.

(iv) Cross-reference with cat-mg-d60d's (T3) topology more carefully — does (T3) admit BK-derived sheaves that Alexandrov rejects?

(v) If union\_closed work generates a parallel framework that resolves the AMBER, the F28 program can adopt it. (Daniel directive 2026-05-15T20:22Z.)
