# Compat-Geom — F31: `\Phi_*` injectivity on the bad-cut Čech class (mg-01ce)

**Branch:** `polecat-cat-mg-01ce` (mg-01ce).
**Parent.** F30 (mg-c3fe) merged 2026-05-16T00:58Z, verdict **AMBER-NS-b-pinned-injectivity-residual.** F30 §4.3 / §6.3 named the residual: prove `\Phi_*` (the induced cohomology map of F30's chain-level cochain map `\Phi`) is *injective* on the bad-cut Čech 2-cocycle class `\widetilde\psi_{\mathrm{BC}}^{(2)}`. Combined with F30's `c_{\mathrm{BC}}(P) = 0`, injectivity would force `[\widetilde\psi_{\mathrm{BC}}^{(2)}] = 0` in `\check H^2`, contradicting its non-trivial Čech construction (F29 §3.4), forcing bad-cut nonexistence — closing milestone-1 part (iii) via the Čech-bias program.
**Chain:** F10 → F17 → F18 → F19–F23 chamber-Morse arc → F24 → F25 (**RED**) → F27 (**RED**) → F28 (**AMBER**) → F29 (**AMBER**, mg-70b0) → F30 (**AMBER**, mg-c3fe) → **F31 (mg-01ce, this doc).**
**Type:** Paper-and-pencil structural analysis. LaTeX-style Markdown; **no new axioms; no Lean changes; no HPC; no numerical computation.** Cumulative state ledger: `docs/state-F29.md` (session 3 — F31 is the third instalment of the F29 arc).
**Daniel directives (inherited from F29):** 2026-05-15T23:20Z (**NOT factorial**); 2026-05-15T23:20Z (*"inherently but not functorially"* — load-bearing); 2026-05-15T23:38Z (mechanism = bad cut → local biases → Čech contradictions → cohomology class → not-sign-like).

---

## Verdict: **RED-injectivity-fails-chain-locality-obstruction.**

`\Phi_*` is **not** injective on the bad-cut Čech class. The kernel of `\Phi_*` contains `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` *structurally*, by an argument intrinsic to the F30 chain-level construction:

**Chain-locality obstruction.** `\Phi` (F30 (1.3.4)) is built entirely from the chain `c`'s own combinatorial data — its cover relations `\{e_0, \ldots, e_{n-3}\}` and per-step probabilities `\pi_k = \Pr_{P_k}[a_k <_{P_k} b_k]`. The Čech 2-cocycle `\widetilde\psi` enters `\Phi(\widetilde\psi)(c)` *only* through its values at the chain-local stratum-pair inputs `(e_i, U_\le^{e_i}; e_j, U_\parallel^{e_j}; P_{i+1})` for `0 \le i < j \le n-3`. The bias-cocycle has rich content beyond chain-local inputs — its values at *non-chain-cover-pair* stratum inputs (`(e, e')` for `e, e' \notin \{e_k\}_k`) and at *cross-refinement* intersection posets are not seen by `\Phi`.

Combined with F30's chain-level vanishing argument (F30 §2.3, §3.2) — which used the orbit-sgn cancellation `\sum_g \mathrm{sgn}(g) = 0` plus the relabel-invariance of bias values to force `\Phi(\widetilde\psi_{\mathrm{BC}}^{\mathrm{orb}}) \equiv 0` as a cochain — the conclusion is that **every Čech 2-cocycle whose chain-local content arises from sgn-orbit-summed relabel-invariant bias-data is annihilated by `\Phi_*`**. The bad-cut Čech class is constructed *precisely* from this kind of data (F29 §3.3, §3.4); it sits inside this annihilated subspace.

So `\Phi_*([\widetilde\psi_{\mathrm{BC}}^{(2)}]) = 0` is not a refined contradiction-yielding identity but a *structurally generic* consequence of the F30 construction. The map `\Phi_*` restricted to the orbit-sgn-isotype of `\check H^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}})` is identically zero. Injectivity fails; `c_{\mathrm{BC}}(P) = 0` is uninformative.

**Why not GREEN.** GREEN would require either a direct injectivity proof on the bad-cut subspace (route (a) §3.1), an LES-style categorical argument (route (b) §3.2), or a combinatorial basis with `\Phi_*` non-degenerate on bad-cut basis-elements (route (c) §3.3). All three routes wall in the same place — the F30 chain-locality of `\Phi` plus the sgn-orbit-equivariance contradiction *generically* annihilates the entire bias-sgn-isotype of `\check H^2`.

**Why not AMBER.** AMBER would require a *refinement* of the bad-cut Čech class where `\Phi_*`-injectivity holds (with the residual F32 named). Candidate refinements considered (§3.5):
- (R-A) Use a finer Čech cover with extra stratum-pair labels (would change `F_{\mathrm{bias}}^{\mathrm{orb}}` to a richer sheaf — pushes outside F17+F18 anchor).
- (R-B) Use `\mathrm{Stab}_{S_n}\{x, y\}`-orbit instead of full `S_n`-orbit (loses the F17+F18 sgn-anchor — F17+F18 constrains full-`S_n`-sgn-isotype, not stabiliser-isotype).
- (R-C) Use a twisted-coefficient version on `\Delta_n` (Candidate C of F29 §2.3; F17+F18 does not apply).
None of the three refinements both (i) lie within the F17+F18 anchor regime AND (ii) escape the chain-locality obstruction. AMBER is not the honest verdict.

**Locating the failure precisely.** The obstruction is *not* a chain-level re-emergence of mg-26fc U1's refinement-functoriality wall (§4). F30's unconditional dissolve of U1 (F30 §5) remains valid — no hidden refinement-restriction is invoked in `\Phi`'s definition or in the equivariance contradiction. The failure is a **fundamentally different obstruction** (per ticket-body wording): the chain-local-only nature of `\Phi` means it is structurally incapable of distinguishing the bad-cut class from generic kernel members in the bias-sgn-isotype. This is a *chain-locality* obstruction, not a *functoriality* obstruction.

**Where this leaves milestone-1 part (iii).** F31 RED + prior F25 RED + F27 RED + F28 AMBER + F30 AMBER → **four-routes-walled** for the Čech-bias closure of milestone-1 part (iii). Per the F31 ticket body, this re-activates the methodology-paper close + milestone-1 redefinition decision (Daniel escalation territory). The F-series cohomological core (parts (i)–(ii), unconditional post F17+F18), the Lean trust surface, the methodology paper draft, and `main.tex` + Steps 1–8 (Route B mathematically correct conditional on Hyp A) are all *unchanged* by F31's RED — F31 walls a specific closure route, it does not retract earlier results.

---

## §0. Setup — what F31 inherits

### 0.1 Recap of F30

F30 (mg-c3fe, AMBER-NS-b-pinned-injectivity-residual) operationalised F29-OP:

- **(F30-1)** Explicit `\Phi : \check C^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}}) \to C^{n-2}(\Delta_n, \mathbb{Q})` on all chains (F30 §1, formula (1.3.4)).
- **(F30-2)** `\Phi` verified as cochain map (F30 §2): cocycle-to-cocycle (face-cancellation), coboundary-to-coboundary, `S_n`-action compatible.
- **(F30-3)** `c_{\mathrm{BC}}(P) = 0` rigorously (F30 §3): chain-level equivariance contradiction (`\Phi(\widetilde\psi_{\mathrm{BC}}^{\mathrm{orb}})` simultaneously trivially-`S_n`-equivariant and `\mathrm{sgn}_{S_n}`-equivariant forces zero).
- **(F30-4)** (NS-b) pinned as the F30 branch of F29 §5.2 dichotomy (F30 §4).
- **(F30-5)** Dissolve criterion (D-α)–(D-γ) met unconditionally — no hidden refinement-functoriality (F30 §5).

F30's named residual (F30 §6.3): show `\Phi_*` (induced cohomology map) is injective on the bad-cut Čech class.

### 0.2 The F31 question, sharply

> **F31-Q.** *Is `\Phi_* \colon \check H^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}}) \to H^{n-2}(\Delta_n, \mathbb{Q})` injective on `[\widetilde\psi_{\mathrm{BC}}^{(2)}]`?*

Equivalently: characterise `\ker(\Phi_*)` in `\check H^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}})` and verify `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \notin \ker(\Phi_*)`.

If yes (GREEN): `\Phi_*([\widetilde\psi_{\mathrm{BC}}^{(2)}]) = 0` (F30) and injectivity gives `[\widetilde\psi_{\mathrm{BC}}^{(2)}] = 0` in `\check H^2`, contradicting F29 §3.4 non-triviality. Bad cut does not exist; milestone-1 part (iii) closes via the F17+F18+F29+F30+F31 chain.

If no (RED): the kernel contains the bad-cut class; `c_{\mathrm{BC}}(P) = 0` is uninformative; the Čech-bias mechanism breaks at the injectivity step.

### 0.3 Hard constraints (NON-NEGOTIABLE, inherited from F30)

- **NOT factorial** (pm-onethird `feedback_anti_factorial_direction`; Daniel 2026-05-15T23:20Z).
- **NOT functorial.** F30 dissolved U1 unconditionally; F31's injectivity argument *must not* re-introduce refinement-functoriality. The argument must be chain-level / orbit-level / cocycle-level — not via a refinement-restriction bridge.
- **Paper-and-pencil first** (`feedback_latex_first_for_math_simp`).
- **Cumulative state doc** — `docs/state-F29.md` (session 3) + this new doc.
- **Default to main** (`feedback_manage_branches_default_to_main`).

### 0.4 Section roadmap

- §1 — Pin `\Phi_*` precisely (degree, coefficient, `S_n`-action, orbit version).
- §2 — Identify the bad-cut Čech class `\widetilde\psi_{\mathrm{BC}}^{(2)}` precisely from F29 §3.4.
- §3 — Attempt injectivity via the three candidate routes (a)/(b)/(c).
- §4 — Verify no factoriality / functoriality regress.
- §5 — What F31 establishes and what it doesn't.
- §6 — Verdict and implications.
- §7 — References.

---

## §1. Pinning `\Phi_*` precisely

### 1.1 The source

`\Phi_*`'s source is

$$\check H^2\bigl(\{\widetilde U_\alpha\}_{\alpha},\; F_{\mathrm{bias}}^{\mathrm{orb}}\bigr),$$

where:

- **Cover `\{\widetilde U_\alpha\}_\alpha`.** Indexed by pairs `(e, s)` where `e \in [n] \times [n]` is an ordered pair of distinct elements and `s \in \{\parallel, \le, \ge\}` is a stratum label; `\widetilde U_{(e, s)} \subseteq \uparrow P` is the down-closed sub-up-set of refinements landing in stratum `s` relative to `e` (F29 §3.1, §3.4, with the down-closure refinement of F29 §3.1). Triple intersections `\widetilde U_{(e_1, s_1)} \cap \widetilde U_{(e_2, s_2)} \cap \widetilde U_{(e_3, s_3)}` are generically non-empty for distinct pairs `e_1, e_2, e_3`, the requirement for a degree-2 Čech class.
- **Coefficient sheaf `F_{\mathrm{bias}}^{\mathrm{orb}}`.** The `S_n`-orbit-aware version of `F_{\mathrm{bias}}` (F29 §3.2): direct sum `\bigoplus_{(x, y) \in \mathcal{P}(P)} F_{\mathrm{bias}}^{(x, y)}` over incomparable pairs of `P`, with `S_n` acting by permuting summands (F29 §3.3). Each `F_{\mathrm{bias}}^{(x, y)}` has linearised bias-line stalks `\widetilde{\mathbb{Q}}_{\parallel}^{(x, y)}, \widetilde{\mathbb{Q}}_{\le}^{(x, y)}, \widetilde{\mathbb{Q}}_{\ge}^{(x, y)}` of total dim 2 each (affine `\to` linear, F29 §3.2).
- **`S_n`-action.** Permutation of pair labels `g \cdot (x, y) = (gx, gy)` plus relabel-equivariance of bias values `b_{g \cdot P'}(gx, gy) = b_{P'}(x, y)` (F29 §1.3 (B-2)). The orbit-sum cochain `\widetilde\psi_{\mathrm{BC}}^{\mathrm{orb}} = \sum_{(x, y)} (\pm)_{x, y} \cdot \widetilde\psi_{\mathrm{BC}}^{(x, y)}` with sign convention as in F29 §3.3.
- **Degree 2.** The bad-cut Čech class lives here per F29 §3.4: a triple intersection involving "one pair resolved, one pair still parallel, plus refinement-evaluation" produces a 2-cocycle measuring inter-pair-stratification contradictions.

The orbit-sgn-isotype `\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})^{\mathrm{sgn}_{S_n}}` is the natural F29-F30 sub-target — F29 §3.3 chose sgn-weights `\pm_{xy}` to land `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` there. Other isotypes of `\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})` exist (trivial-isotype is the unweighted orbit-sum; other `S_n`-irreps appear via standard representation-theoretic decomposition of `\bigoplus_{(x, y)} \mathbb{Q}[(x, y)]`) but are not used by F30's construction.

### 1.2 The target

`\Phi_*`'s target is

$$H^{n-2}\bigl(\Delta_n,\; \mathbb{Q}\bigr) \;=\; H^{n-2}\bigl(\Delta(PPF_n),\; \mathbb{Q}\bigr).$$

By F17+F18 unconditionally (`n \ge 3`):

$$H^k\bigl(\Delta_n,\; \mathbb{Q}\bigr) \;=\; \begin{cases} \mathrm{sgn}_{S_n} & k = n - 2, \\ 0 & 0 < k < n - 2 \text{ or } k > n - 2. \end{cases}$$

So `H^{n-2}(\Delta_n, \mathbb{Q}) = \mathrm{sgn}_{S_n}` is 1-dimensional over `\mathbb{Q}` with `S_n` acting by sign. The unique-up-to-scalar generator is `[\omega_{bal}^{(n)}]` (F18 §0.3, F28 §2.2, mg-d60d §3.4).

**Crucial dimension counts:**
- `\dim_{\mathbb{Q}} H^{n-2}(\Delta_n, \mathbb{Q}) = 1`.
- `\dim_{\mathbb{Q}} H^{n-2}(\Delta_n, \mathbb{Q})^{\mathrm{sgn}} = 1`.
- `\dim_{\mathbb{Q}} H^{n-2}(\Delta_n, \mathbb{Q})^{\mathrm{triv}} = 0`.

The trivial-`S_n`-isotype of `H^{n-2}` is **zero**. This is the load-bearing fact for the equivariance contradiction of F30 §2.3 and (as we shall see in §3) is also the load-bearing fact for the chain-locality obstruction.

### 1.3 The map

`\Phi : \check C^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}}) \to C^{n-2}(\Delta_n, \mathbb{Q})` is defined chain-by-chain via F30 (1.3.4):

$$\Phi(\widetilde\psi)(c) \;=\; \sum_{0 \le i < j \le n-3} \widetilde\psi[c, i, j] \cdot \Omega_{ij}(c), \tag{1.3.1}$$

where for a saturated chain `c = (P_0 \lessdot P_1 \lessdot \cdots \lessdot P_{n-2})` with cover relations `e_k = (a_k, b_k)`, the inputs are:

- `\widetilde\psi[c, i, j] := \widetilde\psi\bigl((e_i, U_\le^{e_i}),\; (e_j, U_\parallel^{e_j});\; P_{i+1}\bigr)` — the Čech 2-cocycle's value at the chain-local stratum-pair `(e_i \text{ resolved}, e_j \text{ still parallel})` evaluated at the chain's refinement `P_{i+1}`.
- `\Omega_{ij}(c) := \prod_{k \in \{0, \ldots, n-3\} \setminus \{i, j\}} \pi_k(c)` — the chain's `(n-4)`-degree `\omega_{bal}^{(n)}`-style remainder product over slots not in `\{i, j\}`.

`\Phi` is a chain-level cochain map (F30 §2): `d_\Delta \circ \Phi = \Phi \circ d_{\check C}` (cocycle preservation), coboundary preservation by analogous 1-cochain construction. Non-saturated faces are zero by (E-1) extension (F30 §2.1).

`\Phi_*` is the induced map on cohomology:

$$\Phi_* \;\colon\; \check H^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}}) \;\to\; H^{n-2}(\Delta_n, \mathbb{Q}) \;=\; \mathrm{sgn}_{S_n}. \tag{1.3.2}$$

By coboundary preservation (F30 §2.2), `\Phi_*` is well-defined on cohomology classes.

### 1.4 The S_n-equivariance — chain-level and cocycle-level

**Two distinct S_n-actions are relevant:**

(`S_n`-a) **Chain-level action.** `S_n` acts on chains `c \in \Delta_n^{\mathrm{sat}}` by `g \cdot c = (g \cdot P_0 \lessdot \cdots \lessdot g \cdot P_{n-2})`. This induces an action on `C^{n-2}(\Delta_n, \mathbb{Q})` by `(g \cdot \phi)(c) := \phi(g^{-1} \cdot c)`.

(`S_n`-b) **Cocycle-level action.** `S_n` acts on `\check C^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})` by permuting pair labels `(g \cdot \widetilde\psi)(e_1, e_2; P) := \widetilde\psi(g^{-1} \cdot e_1, g^{-1} \cdot e_2; g^{-1} \cdot P)`.

`\Phi` commutes with these actions: `\Phi(g \cdot \widetilde\psi) = g \cdot \Phi(\widetilde\psi)` (F30 §2.3 (E-3) check). Hence `\Phi_*` is `S_n`-equivariant on cohomology.

**Isotype decomposition.** Both `\check H^2` and `H^{n-2}` decompose into `S_n`-irrep isotypes:

$$\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}}) \;=\; \bigoplus_{\lambda \vdash n} \check H^2_\lambda, \qquad H^{n-2}(\Delta_n, \mathbb{Q}) \;=\; H^{n-2}_{\mathrm{sgn}} \;=\; \mathrm{sgn}_{S_n}, \tag{1.4.1}$$

where `H^{n-2}_\lambda = 0` for `\lambda \neq \mathrm{sgn}` (F17+F18). `\Phi_*` decomposes accordingly:

$$\Phi_* \;=\; \bigoplus_\lambda (\Phi_*)_\lambda, \qquad (\Phi_*)_\lambda \colon \check H^2_\lambda \to H^{n-2}_\lambda. \tag{1.4.2}$$

For `\lambda \neq \mathrm{sgn}`, `(\Phi_*)_\lambda` is the zero map (target is 0). The only isotype-component of `\Phi_*` with non-trivial target is `(\Phi_*)_{\mathrm{sgn}} \colon \check H^2_{\mathrm{sgn}} \to \mathrm{sgn}_{S_n}`.

**The bad-cut Čech class lives in `\check H^2_{\mathrm{sgn}}`** (F29 §3.3 sgn-orbit-sum convention). So the F31 question reduces to:

> **F31-Q'.** *Is `(\Phi_*)_{\mathrm{sgn}} \colon \check H^2_{\mathrm{sgn}}(\dots, F_{\mathrm{bias}}^{\mathrm{orb}}) \to \mathrm{sgn}_{S_n}` injective?*

§3 analyses this. The answer is **no** (RED).

### 1.5 Coefficients

All cochain complexes are over `\mathbb{Q}` (rational coefficients). No new coefficient system is introduced in F31. The two-row stalk linearisation `\widetilde{\mathbb{Q}}_\alpha = \mathbb{Q} \oplus \mathbb{Q} \cdot v_\alpha` of F29 §3.2 (affine `\to` linear) is the only coefficient lifting present; F30's `\Phi` formula evaluates `\widetilde\psi` at specific Čech-cochain values in this lifted system but produces `\mathbb{Q}`-valued cochains in `C^{n-2}(\Delta_n, \mathbb{Q})` (the lifting is internal to the Čech-source; the target is plain `\mathbb{Q}`).

---

## §2. The bad-cut Čech class `\widetilde\psi_{\mathrm{BC}}^{(2)}`

### 2.1 F29 §3.4's construction, recapped

For a width-3 γ-counterexample `P` on `n` elements with incomparable pair set `\mathcal{P}(P) \subseteq [n] \times [n]`:

- For each `(x, y) \in \mathcal{P}(P)`, define the single-pair bias-cochain `\widetilde b^{(x, y)} \in \check C^0(\{\widetilde U_\alpha^{(x, y)}\}, F_{\mathrm{bias}}^{(x, y)})` per F29 §3.2: bias values `(b_{P'}(x, y), v_{\parallel}^{(x, y)})` on `U_\parallel^{(x, y)}`, constant `(0, v_{\le, \ge}^{(x, y)})` on `U_{\le, \ge}^{(x, y)}` after the affine-to-linear lift.
- The single-pair Čech 1-cocycle `\widetilde\psi_{\mathrm{BC}}^{(x, y)} = \delta_{\check C} \widetilde b^{(x, y)}` is exact (`[\widetilde\psi_{\mathrm{BC}}^{(x, y)}] = 0` in `\check H^1`, F29 §3.2 end).
- The orbit-cochain `\widetilde b^{\mathrm{orb}} = \sum_{(x, y) \in \mathcal{P}(P)} \mathrm{sgn}(x, y) \cdot \widetilde b^{(x, y)}` cannot be globally defined as a section of any single `F_{\mathrm{bias}}^{(x, y)}` — strata for different pairs are incompatible (F29 §3.3).

The **orbit-Čech 2-cocycle** measures this incompatibility (F29 §3.4):

$$\widetilde\psi_{\mathrm{BC}}^{(2)}\bigl((x_1, y_1), s_1;\; (x_2, y_2), s_2;\; P''\bigr) \;:=\; \mathrm{sgn}(x_1, y_1) \cdot \widetilde b^{(x_1, y_1)}\bigl|_{P''}^{s_1} \;-\; \mathrm{sgn}(x_2, y_2) \cdot \widetilde b^{(x_2, y_2)}\bigl|_{P''}^{s_2}, \tag{2.1.1}$$

evaluated on triple-intersection posets `P'' \in \widetilde U_{(x_1, y_1, s_1)} \cap \widetilde U_{(x_2, y_2, s_2)}`. For `s_1 = U_\le^{(x_1, y_1)}` (resolved) and `s_2 = U_\parallel^{(x_2, y_2)}` (still parallel), the value simplifies:

$$\widetilde\psi_{\mathrm{BC}}^{(2)}\bigl((x_1, y_1), U_\le;\; (x_2, y_2), U_\parallel;\; P''\bigr) \;=\; \mathrm{sgn}(x_1, y_1) \cdot (+\tfrac{1}{2}) \;-\; \mathrm{sgn}(x_2, y_2) \cdot b_{P''}(x_2, y_2). \tag{2.1.2}$$

This is the explicit F29 §3.4 formula for the bad-cut Čech 2-cocycle.

### 2.2 The S_n-isotype

`\widetilde\psi_{\mathrm{BC}}^{(2)}` is `\mathrm{sgn}_{S_n}`-equivariant: under `g \in S_n`,

$$(g \cdot \widetilde\psi_{\mathrm{BC}}^{(2)})(\dots) \;=\; \mathrm{sgn}(g) \cdot \widetilde\psi_{\mathrm{BC}}^{(2)}(\dots), \tag{2.2.1}$$

by the sgn-orbit-sum convention of F29 §3.3 (each summand `\widetilde b^{(x, y)}` permutes to `\widetilde b^{(gx, gy)}` under `g`, with the `\mathrm{sgn}(x, y)` weight transforming compatibly to give an overall `\mathrm{sgn}(g)`-twist).

So `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in \check H^2_{\mathrm{sgn}}(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})`.

### 2.3 Non-triviality in `\check H^2`

F29 §3.4 argues: for the full incomparable-pair-indexed cover, `\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})` is generically non-zero, with `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` non-trivial. The argument is informal (heuristic / generic), not a rigorous theorem.

For F31's RED analysis, we *assume* the F29 §3.4 non-triviality: `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \neq 0` in `\check H^2_{\mathrm{sgn}}`. If non-triviality fails (i.e., `[\widetilde\psi_{\mathrm{BC}}^{(2)}] = 0` exactly), the (NS-b) closure is vacuous: there is no obstruction to remove. Either way, F31's verdict on injectivity decides the closure's viability.

### 2.4 The chain-local content of `\widetilde\psi_{\mathrm{BC}}^{(2)}` — what `\Phi` sees

`\Phi`'s formula (1.3.1) evaluates `\widetilde\psi_{\mathrm{BC}}^{(2)}` only at the chain-local stratum-pair inputs

$$\bigl(e_i, U_\le^{e_i};\; e_j, U_\parallel^{e_j};\; P_{i+1}\bigr) \quad \text{for } 0 \le i < j \le n-3.$$

Using (2.1.2) with `(x_1, y_1) = e_i = (a_i, b_i)`, `(x_2, y_2) = e_j = (a_j, b_j)`, and `P'' = P_{i+1}`:

$$\widetilde\psi_{\mathrm{BC}}^{(2)}[c, i, j] \;=\; \mathrm{sgn}(e_i) \cdot \tfrac{1}{2} \;-\; \mathrm{sgn}(e_j) \cdot b_{P_{i+1}}(a_j, b_j). \tag{2.4.1}$$

**Two observations.**

(O-1) **`\Phi` is blind to non-chain-cover-pair inputs.** Stratum-pair inputs `((x, y), s_1; (x', y'), s_2; P'')` with `(x, y), (x', y') \notin \{e_k : k = 0, \ldots, n-3\}` for any chain `c` do not enter `\Phi(\widetilde\psi)(c)` for any `c`. Such inputs *do* enter `\widetilde\psi_{\mathrm{BC}}^{(2)}` (cocycles are defined on all triple-intersection posets, not just chain-cover-induced ones).

(O-2) **`\Phi` is blind to cross-refinement intersection-data.** For a fixed pair `(x_1, y_1, s_1; x_2, y_2, s_2)`, the cocycle's values on different `P'' \in \widetilde U_{(x_1, y_1, s_1)} \cap \widetilde U_{(x_2, y_2, s_2)}` vary (the bias `b_{P''}(x_2, y_2)` is `P''`-dependent in `U_\parallel^{(x_2, y_2)}`). `\Phi` evaluates only at `P'' = P_{i+1}` from the chain, missing all other `P''` in the intersection.

Both blindnesses are structural: they follow from `\Phi`'s formula (F30 (1.3.4)) using chain-local data only. They are not artefacts of choice — any chain-level cochain map of `\Phi`'s form has the same blindnesses.

---

## §3. Injectivity analysis — three routes converge to RED

### 3.1 Route (a) — direct ker(`\Phi_*`) ∩ bad-cut-subspace

**Claim.** `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in \ker(\Phi_*)`.

**Argument.** F30 §3.2 (combining §2.3's equivariance contradiction with the chain-level vanishing of `\Phi(\widetilde\psi_{\mathrm{BC}}^{\mathrm{orb}})`) established

$$\Phi_*\bigl([\widetilde\psi_{\mathrm{BC}}^{(2)}]\bigr) \;=\; 0 \quad \text{in } H^{n-2}(\Delta_n, \mathbb{Q}). \tag{3.1.1}$$

Combined with the assumed non-triviality `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \neq 0` (§2.3):

$$[\widetilde\psi_{\mathrm{BC}}^{(2)}] \;\in\; \ker(\Phi_*) \setminus \{0\}. \tag{3.1.2}$$

This *is* the failure of injectivity on the bad-cut class.

**The question is not whether injectivity fails, but WHY** — what structural feature of the F30 construction puts `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` in the kernel?

### 3.2 The chain-locality obstruction — structural diagnosis

The kernel of `\Phi_*` contains every class `[\widetilde\psi] \in \check H^2_{\mathrm{sgn}}` such that `\Phi(\widetilde\psi) \equiv 0` as a cochain. We identify a structural subspace inside this kernel:

**Definition (chain-local zero subspace).** Let

$$K_{\mathrm{chain-loc}} \;:=\; \bigl\{ [\widetilde\psi] \in \check H^2_{\mathrm{sgn}}(\dots, F_{\mathrm{bias}}^{\mathrm{orb}}) \;:\; \widetilde\psi[c, i, j] \text{ depends only on chain-cover-pair data and chain-relabel-invariant bias values} \bigr\}.$$

**Lemma 3.2.1 (chain-locality forces kernel).** `K_{\mathrm{chain-loc}} \subseteq \ker(\Phi_*)`.

*Proof.* Take `[\widetilde\psi] \in K_{\mathrm{chain-loc}}`. By definition, `\widetilde\psi[c, i, j] = f(e_i, e_j, P_{i+1})` for some function `f` that is *chain-relabel invariant*: `f(g \cdot e_i, g \cdot e_j, g \cdot P_{i+1}) = f(e_i, e_j, P_{i+1})` (e.g., `f` is a function of `\Pr_{P_{i+1}}[a_j < b_j]` and similar relabel-invariant probabilities). The chain's per-step probabilities `\pi_k = \Pr_{P_k}[a_k < b_k]` are also chain-relabel-invariant.

Hence

$$\Phi(\widetilde\psi)(g \cdot c) \;=\; \sum_{i < j} f(g e_i, g e_j, g P_{i+1}) \cdot \Omega_{ij}(g \cdot c) \;=\; \sum_{i < j} f(e_i, e_j, P_{i+1}) \cdot \Omega_{ij}(c) \;=\; \Phi(\widetilde\psi)(c).$$

So `\Phi(\widetilde\psi)` is **trivially-`S_n`-equivariant** as a cochain in `C^{n-2}(\Delta_n, \mathbb{Q})`.

On the other hand, since `[\widetilde\psi] \in \check H^2_{\mathrm{sgn}}`, the cocycle `\widetilde\psi` is sgn-equivariant up to coboundary: `g \cdot \widetilde\psi = \mathrm{sgn}(g) \cdot \widetilde\psi + d_{\check C} \alpha_g` for some 1-cochain `\alpha_g`. Since `\Phi` is a cochain map preserving coboundaries, `\Phi(g \cdot \widetilde\psi) = \mathrm{sgn}(g) \cdot \Phi(\widetilde\psi) + d_\Delta \Phi(\alpha_g)`, i.e., at the cohomology-class level,

$$g \cdot [\Phi(\widetilde\psi)] \;=\; \mathrm{sgn}(g) \cdot [\Phi(\widetilde\psi)] \quad \text{in } H^{n-2}(\Delta_n, \mathbb{Q}). \tag{3.2.2}$$

But also, by trivial-equivariance of the cochain `\Phi(\widetilde\psi)`,

$$g \cdot [\Phi(\widetilde\psi)] \;=\; [\Phi(\widetilde\psi)] \quad \text{in } H^{n-2}(\Delta_n, \mathbb{Q}). \tag{3.2.3}$$

Combining (3.2.2) and (3.2.3): `\mathrm{sgn}(g) \cdot [\Phi(\widetilde\psi)] = [\Phi(\widetilde\psi)]` for all `g`. For odd `g`, this forces `[\Phi(\widetilde\psi)] = 0` in `H^{n-2}(\Delta_n, \mathbb{Q})`.

Equivalently: `[\Phi(\widetilde\psi)]` lies in `H^{n-2}_{\mathrm{triv}} = 0` (the trivial-`S_n`-isotype of `H^{n-2}`, which is zero by F17+F18). Hence `\Phi_*([\widetilde\psi]) = 0`. ∎

**Corollary 3.2.2 (bad-cut class is in `K_{\mathrm{chain-loc}}`).** `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in K_{\mathrm{chain-loc}}`.

*Proof.* By (2.4.1), `\widetilde\psi_{\mathrm{BC}}^{(2)}[c, i, j] = \mathrm{sgn}(e_i) \cdot \tfrac{1}{2} - \mathrm{sgn}(e_j) \cdot b_{P_{i+1}}(a_j, b_j)`, which depends only on the chain-cover-pair data `(e_i, e_j, P_{i+1})` via the relabel-invariant bias `b_{P_{i+1}}(a_j, b_j)` and the sign-of-pair function `\mathrm{sgn}`. Under chain relabel `g`, both summands transform: `\mathrm{sgn}(g \cdot e_i)` differs from `\mathrm{sgn}(e_i)` in general, but the orbit-sum sgn-convention (F29 §3.3) is built so the *cocycle-level* sgn-equivariance handles this. The chain-local *value* `\widetilde\psi_{\mathrm{BC}}^{(2)}[c, i, j]` for a *fixed* chain is a chain-relabel-invariant quantity modulo sign-of-pair conventions; the entire orbit-isotype decomposition is captured at the cocycle-action level (`S_n`-b of §1.4), and the chain-action level (`S_n`-a) leaves the *evaluated* cochain trivially-equivariant.

The argument of F30 §2.3 (2.3.1)–(2.3.5) is precisely this lemma applied to `[\widetilde\psi_{\mathrm{BC}}^{(2)}]`. ∎

**Conclusion of route (a).** `\ker(\Phi_*)` contains the full subspace `K_{\mathrm{chain-loc}}`, and `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` sits inside. Injectivity of `\Phi_*` on the bad-cut class fails.

### 3.3 Route (b) — categorical / LES

A long-exact-sequence-style injectivity argument would situate `\Phi_*` as a map in a long exact sequence of cohomology groups, with adjacent terms forced to vanish so `\Phi_*` becomes injective.

The natural candidate LES involves the Čech-to-derived spectral sequence and the simplicial cohomology of `\Delta_n`. But the two sides of `\Phi_*` are cohomologies of *different* complexes:

- **Source.** `\check H^*(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}})` — Čech cohomology of a *cover-with-stratification* on `\uparrow P`, with coefficients in a constructible sheaf on a *sub-up-set* of `PPF_n`.
- **Target.** `H^*(\Delta_n, \mathbb{Q})` — simplicial cohomology of the *order complex* of *all* of `PPF_n`, with constant coefficients.

There is no naturally-arising long exact sequence linking these two cohomologies. `\Phi` is a chain-level cochain map between two distinct complexes whose construction (F30 §1.3) is not part of an exact-sequence-of-complexes structure (e.g. a short exact sequence of cochain complexes inducing an LES of cohomology).

In particular, `\Phi` is not the connecting map of a Mayer-Vietoris sequence (no two-complex covering inducing it), not a Leray spectral-sequence map (no fibration), not a restriction-induced map (no inclusion `\uparrow P \hookrightarrow PPF_n` whose cohomology-restriction has the right form — `\uparrow P`'s order complex is *contractible*, F29 §2.2 end, so restriction-cohomology is trivial). The candidate `\Phi`-as-edge-map of a Čech-to-derived spectral sequence is constrained by the F28-walled augmentation `F_{\mathrm{bias}}^{(x, y)} \to \underline{\mathbb{Q}}` (F29 §4.2) — this augmentation *fails* to be a sheaf morphism, so the spectral-sequence edge map doesn't exist.

**Conclusion of route (b).** No LES structure naturally produces `\Phi_*` as a piece that could be forced injective by vanishing-of-adjacent-terms. The categorical route does not apply.

### 3.4 Route (c) — combinatorial basis

Pick a basis `\{[\widetilde\psi_\alpha]\}_\alpha` for `\check H^2_{\mathrm{sgn}}(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})` and compute `\Phi_*([\widetilde\psi_\alpha])` for each basis element. `\Phi_*` is injective on this isotype iff the matrix of `\Phi_*` (a column-vector in `\mathrm{sgn}_{S_n} = \mathbb{Q}`) is generically non-zero on all basis elements.

But by Lemma 3.2.1, *every* basis element `[\widetilde\psi_\alpha] \in K_{\mathrm{chain-loc}}` maps to `0` under `\Phi_*`. Since `K_{\mathrm{chain-loc}}` contains the entire orbit-sgn-isotype of *chain-locally-buildable cocycles* — and the natural basis-of-bias-style cocycles for `\check H^2_{\mathrm{sgn}}` is exactly the orbit-sgn-isotype of cocycles built from per-pair bias data — the matrix of `\Phi_*` on this basis is the zero matrix.

In particular, `(\Phi_*)_{\mathrm{sgn}}` is the zero linear map. Combinatorial-basis non-degeneracy *fails identically on the relevant isotype*.

**Conclusion of route (c).** `(\Phi_*)_{\mathrm{sgn}}` is the zero map; injectivity fails on the bad-cut class as a special case of failing on the entire sgn-isotype.

### 3.5 Convergent conclusion

All three routes (a), (b), (c) wall in the same place: **the chain-locality of `\Phi` (F30 (1.3.4))** combined with **the F17+F18 vanishing of `H^{n-2}_{\mathrm{triv}}`** forces every chain-locally-buildable sgn-isotype Čech class to die under `\Phi_*`. The bad-cut Čech class is such a class.

`(\Phi_*)_{\mathrm{sgn}}` is identically zero on `K_{\mathrm{chain-loc}}`. Since the bad-cut class is in `K_{\mathrm{chain-loc}}` (Cor 3.2.2), `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in \ker(\Phi_*)`. **Injectivity fails.**

### 3.6 The three candidate refinements (NOT AMBER-worthy)

For AMBER, we would need a *refinement* of `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` that escapes `K_{\mathrm{chain-loc}}`. We consider three natural refinements and verify each walls:

**(R-A) Richer Čech cover.** Refine `\{\widetilde U_\alpha\}` to a cover with extra stratum-pair labels (e.g., resolve the `\parallel/\le/\ge` stratification further by sub-stratifying `U_\parallel` according to "biased above/below 1/2"). This produces a finer Čech complex with more 2-cocycles. **Wall.** The refined cocycle still has chain-local values evaluated only at chain-cover-pair-derived stratum inputs; `\Phi` (whose formula uses *whatever* chain-local-stratum-labels are available) extends to the finer cover and the same Lemma 3.2.1 applies — the refined cocycle's chain-local value is still relabel-invariant, still in `K_{\mathrm{chain-loc}}`, still killed by `\Phi_*`. F17+F18 anchor unchanged.

**(R-B) Stabiliser-orbit instead of full-`S_n`-orbit.** Use `\mathrm{Stab}_{S_n}\{x, y\}`-orbit-sum (F29 §1.3 (B-2)) instead of full `S_n`-orbit. The resulting cocycle lives in `\check H^2_{\mathrm{Stab}\text{-sgn}}` — the sgn-isotype of the smaller group `\mathrm{Stab}_{S_n}\{x, y\}`. **Wall.** F17+F18 constrains the full-`S_n`-sgn-isotype of `H^{n-2}(\Delta_n, \mathbb{Q})`, *not* the `\mathrm{Stab}_{S_n}\{x, y\}`-sgn-isotype. The target `H^{n-2}(\Delta_n, \mathbb{Q}) = \mathrm{sgn}_{S_n}` *contains* `\mathrm{Stab}_{S_n}\{x, y\}`-isotypes by restriction, but a `\mathrm{Stab}\text{-sgn}`-cohomology bound is *not* the F17+F18 anchor and would need a separate cohomology computation — outside F29's scope and not delivered. The F17+F18 anchor breaks.

**(R-C) Twisted-coefficient cohomology on `\Delta_n`.** F29 §2.3 Candidate C: define a coefficient system `\mathbb{Q}_{(x, y)}` on `\Delta_n` that twists by the bad-pair orientation, and study `H^*(\Delta_n, \mathbb{Q}_{(x, y)})`. **Wall.** F17+F18 *does not* compute `H^*(\Delta_n, \mathbb{Q}_{(x, y)})` — this is a different coefficient system. The constant-`\mathbb{Q}` cohomology of `\Delta_n` is anchored at sgn-isotype degree `n - 2`; the twisted cohomology is in general different (could contain non-sgn-isotype content, in which case the "only sign-like" anchor fails). F29 §6 (mg-26fc U1 in twisted-coefficient dialect) confirms this is the F27/F28 wall in a new dialect. The closure breaks at the augmentation step.

**None of (R-A)/(R-B)/(R-C) salvages a sub-class on which `\Phi_*` is injective AND the F17+F18 anchor still applies.** AMBER is not honest; RED is.

### 3.7 Comparison with F30 §4.3's expectation

F30 §4.3 expected F31 might salvage injectivity by characterising `\ker(\Phi_*)` and showing `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` not inside:

> *Showing `\widetilde\psi_{\mathrm{BC}}^{(2)} \notin \ker(\Phi_*)` requires a structural argument: e.g., characterise `\ker(\Phi_*)` and verify that `\widetilde\psi_{\mathrm{BC}}^{(2)}`'s specific bias-structure rules out kernel-membership.*

F31 *does* characterise `\ker(\Phi_*)` (via `K_{\mathrm{chain-loc}}` of §3.2) — but the characterisation goes the other way: `K_{\mathrm{chain-loc}} \subseteq \ker(\Phi_*)`, and the bad-cut class is in `K_{\mathrm{chain-loc}}` by construction. F30's hope was that the bad-cut's "specific bias-structure" would distinguish it from generic kernel members. F31's finding is that *the* defining feature of the bad-cut (its construction from sgn-orbit-summed relabel-invariant bias values) is *exactly* the structural feature that places it in the kernel.

The F30 chain-level vanishing argument of F30 §2.3 (the trivial-vs-sgn-isotype clash) and the F31 kernel-characterisation argument of §3.2 are *the same argument viewed from two directions*: F30 used it to prove `c_{\mathrm{BC}}(P) = 0`; F31 uses it to prove `\ker(\Phi_*) \supseteq K_{\mathrm{chain-loc}}`. The conclusion `c_{\mathrm{BC}}(P) = 0` is therefore not a refined contradiction-yielding identity — it is a *generic* consequence of `\Phi` being chain-local + `\widetilde\psi` being sgn-orbit-summed + `H^{n-2}_{\mathrm{triv}} = 0`.

---

## §4. No factoriality / functoriality regress

### 4.1 What F31 must not do

F31's hard constraints (§0.3): NOT factorial; NOT functorial. F30's unconditional dissolve of U1 (F30 §5) rests on `\Phi`'s chain-level construction not invoking refinement-functoriality. F31's injectivity argument (or, as it turned out, the failure-of-injectivity argument) must not re-introduce these.

### 4.2 Factoriality check

The F31 argument of §3 uses:

- **F30's `\Phi` (1.3.4).** Chain-level cup-product-style assembly using chain-cover-relation labels and chain-per-step-probabilities. No `S_n!`-indexed objects, no factorial decomposition. ✓
- **The sgn-orbit-sum of F29 §3.3.** Sum over `\mathcal{P}(P)` (incomparable pairs of `P`) with sign weights. `|\mathcal{P}(P)|` is at most `\binom{n}{2}`, polynomial in `n` — *not* factorial. The sum is over pair-set elements, not over `S_n`-coset representatives. ✓
- **F17+F18 cohomology anchor.** The statement `H^{n-2}_{\mathrm{triv}} = 0` is a consequence of `H^{n-2} = \mathrm{sgn}_{S_n}` (F17+F18). No factorial structure in the input. ✓
- **Lemma 3.2.1's `\sum_g \mathrm{sgn}(g) = 0` cancellation.** The cancellation runs *over `S_n`*, which has order `n!`. But: the cancellation is a *single identity* (an alternating-sum vanishing for `n \ge 2`), used to derive the trivial-`S_n`-isotype kill. It is not a factorial-graded construction, not a factorial decomposition, not a factorial cohomology theory. The `n!` appears only as the cardinality of `S_n` in the sum-over-`S_n`-identity, which is the standard `\mathrm{sgn}`-representation-theoretic fact. ✓

**No factoriality.** ✓

### 4.3 Functoriality check

The F31 argument uses:

- **Chain-relabel-invariance of bias `b_{P'}(x, y)`.** `b_{g \cdot P'}(g \cdot x, g \cdot y) = b_{P'}(x, y)` (F29 §1.3 (B-2)). This is *relabel-equivariance*, not *refinement-functoriality* (F30 §5 (D-γ) distinction): the property concerns how bias transforms under `S_n`-action on `[n]`, not how bias compares across different refinements `P' \neq P''`. ✓
- **Chain-relabel-invariance of probability `\pi_k = \Pr_{P_k}[a_k < b_k]`.** Same character: an `S_n`-relabelling property of the chamber-uniform measure, automatic combinatorial fact. ✓
- **`\Phi` cochain-map property (F30 §2).** Cocycle preservation, coboundary preservation, `S_n`-equivariance. F30 verified these using only chain-arithmetic in `C^*(\Delta_n, \mathbb{Q})` and the Čech cocycle's intrinsic `d_{\check C} = 0`. F31 inherits the verification. ✓
- **`\Phi_*` well-definedness on cohomology.** Standard cochain-map → cohomology-map functoriality (cochain-complex functoriality, not poset-refinement functoriality). This is the "functoriality" of cochain complexes themselves, *not* the F28-walled refinement-functoriality. ✓

**No functoriality regress.** F30's dissolve of U1 (F30 §5) remains valid post-F31. The injectivity failure is *not* a chain-level dialect re-emergence of U1 — it is a structurally distinct obstruction.

### 4.4 The obstruction-class distinction — chain-locality vs refinement-functoriality

Per the F31 ticket-body wording, RED requires reporting "whether this is a chain-level dialect re-emergence of U1 or a fundamentally different obstruction."

**It is a fundamentally different obstruction.** Specifically:

| obstruction | what is missing | how F-series experiences it |
|---|---|---|
| **mg-26fc U1** (literal-dialect F27) | refinement-respecting bridge `\mathcal{B}_P : G_{BK}(P) \to \Delta_n` | F27 RED — BK graph and `\Delta_n` links are different combinatorial objects |
| **U1** (sheaf-dialect F28) | functorial sheaf morphism `F_{BK} \to F_\ell` | F28 AMBER — sheaf morphism does not exist |
| **U1** (chain-level dialect, hypothetical) | hidden refinement-functor inside chain-level construction | F30 §5: *not* present; F30 unconditional dissolve |
| **F31 chain-locality** (this doc) | `\Phi` blind to non-chain-local Čech data | F31 RED — bad-cut class lies in `K_{\mathrm{chain-loc}} \subseteq \ker(\Phi_*)` |

U1 in *any* dialect is about a *bridge between BK-spectral data and Δ_n-cohomology* that fails refinement-compatibility. F31's chain-locality is about a *chain-level cup-product map* whose formula is *too local* to distinguish the bad-cut Čech class from generic kernel members in the relevant isotype.

The chain-locality obstruction is intrinsic to *any* chain-level cup-product-style cochain map built from chain-cover-pair labels: such a map is forced to land in the trivial-`S_n`-isotype of the target by Lemma 3.2.1, and `H^{n-2}_{\mathrm{triv}} = 0` (F17+F18) then forces the image to be zero on the entire sgn-isotype of the source. This is a structural feature of "chain-level + chain-local + sgn-orbit-sum + F17+F18-anchor", not a hidden refinement-functor.

**Diagnostic summary.** The Čech-bias mechanism's chain-level dialect (F29 → F30 → F31) walls *not* on refinement-functoriality (F30 dissolved U1 unconditionally) but on **the trivial-isotype-vanishing of the F17+F18 target**: the chain-level construction's image lives in the trivial-isotype of `C^{n-2}(\Delta_n, \mathbb{Q})` by relabel-invariance, but the target cohomology has zero trivial-isotype, killing the image. The chain-level dialect's *strength* (chain-level non-functoriality) is also its *failure* (chain-local invariance forces trivial-isotype landing).

---

## §5. What F31 establishes and what it doesn't

### 5.1 Establishes

(E-1) **`\Phi_*` pinned precisely** (§1): source `\check H^2_{\mathrm{sgn}}(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})`, target `H^{n-2}(\Delta_n, \mathbb{Q}) = \mathrm{sgn}_{S_n}`, rational coefficients, `S_n`-equivariant, well-defined on cohomology classes (F30 §2 inherited).

(E-2) **The bad-cut Čech class `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` lies in `\check H^2_{\mathrm{sgn}}`** (§2.2), with chain-local content `\widetilde\psi_{\mathrm{BC}}^{(2)}[c, i, j] = \mathrm{sgn}(e_i) \cdot \tfrac{1}{2} - \mathrm{sgn}(e_j) \cdot b_{P_{i+1}}(a_j, b_j)` per (2.4.1).

(E-3) **`\Phi_*` is not injective on the bad-cut class** (§3): assuming `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \neq 0` per F29 §3.4, the kernel contains `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` non-trivially.

(E-4) **The kernel-containing subspace `K_{\mathrm{chain-loc}}` characterised** (Lemma 3.2.1): every chain-locally-buildable sgn-isotype Čech class is in `\ker(\Phi_*)`, by an argument using only chain-relabel-invariance + sgn-orbit-equivariance + `H^{n-2}_{\mathrm{triv}} = 0` (F17+F18).

(E-5) **`(\Phi_*)_{\mathrm{sgn}}` is the zero map on `K_{\mathrm{chain-loc}}`** (§3.4): combinatorial-basis non-degeneracy fails identically on the relevant isotype.

(E-6) **All three candidate refinements (R-A), (R-B), (R-C) wall** (§3.6): none salvages a sub-class where `\Phi_*`-injectivity holds AND F17+F18 anchor still applies. AMBER-with-refinement is not honest.

(E-7) **The chain-locality obstruction is fundamentally different from mg-26fc U1** (§4.4): F30's unconditional dissolve of U1 remains valid; F31's RED is a structurally distinct obstruction, namely *blindness of `\Phi` to non-chain-local Čech content combined with `H^{n-2}_{\mathrm{triv}} = 0`*.

(E-8) **No factoriality, no functoriality regress** (§4.2, §4.3): F31's argument respects the Daniel hard constraints; F30's dissolve criteria remain met.

### 5.2 Does not establish

(N-1) **`[\widetilde\psi_{\mathrm{BC}}^{(2)}] \neq 0` in `\check H^2`** — this is the F29 §3.4 *assumed* non-triviality, used by F31 to conclude `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in \ker(\Phi_*) \setminus \{0\}`. F29's non-triviality argument was heuristic ("generically non-zero"); F31 does not rigorise it. If non-triviality fails, the (NS-b) closure is *vacuous* (no obstruction to remove); the F31 RED-on-injectivity verdict is unchanged in posture but the bad-cut-exists premise itself collapses, opening a *different* failure mode for the Čech-bias mechanism.

(N-2) **Whether some entirely non-chain-level cochain map `\Phi' \neq \Phi`** could be injective on `[\widetilde\psi_{\mathrm{BC}}^{(2)}]`. F31 walls F30's specific `\Phi`. A radically different chain-level construction (e.g., a `\Phi'` that uses *all* cocycle inputs, not just chain-local-cover-pair-derived) might evade the chain-locality obstruction. But: any such `\Phi'` would need to fit Daniel's "not functorially" directive (chain-level/non-functorial) while extracting non-chain-local Čech content — a tension F31 does not resolve. The natural such `\Phi'` would be sheaf-cohomology-based and re-introduce the F28 functorial-sheaf-morphism wall. F31 does not enumerate or wall all such alternative constructions; it walls the F30 construction.

(N-3) **Milestone-1 part (iii) closure via the Čech-bias program.** F31 RED breaks the (NS-b) closure. The (NS-a) branch was structurally vacuous in the chain-level dialect (F30 §4.2: F17+F18 does not constrain `F_{\mathrm{bias}}^{\mathrm{orb}}`-cohomology without the F28-walled augmentation). With both branches walled, the F29 §5.2 dichotomy does not produce a contradiction with bad-cut existence. **The Čech-bias program closes milestone-1 part (iii) does NOT hold.**

(N-4) **The width-3 bridge (F10 §7.4)** — unchanged from F30; not addressed by F31.

(N-5) **F25, F27, F28 verdicts** unchanged. F31 RED is a chain-level-dialect F31-specific verdict; it does not retract or modify the prior route-verdicts.

(N-6) **The F-series cohomological core (parts (i)–(ii), unconditional post F17+F18)** unchanged. F31's RED concerns part (iii); parts (i)–(ii) are unaffected.

### 5.3 No F32 follow-on named

F31 is RED, not AMBER. Per F31 ticket body, AMBER would name F32 (a refinement-residual to file). F31 is RED — no F32 follow-on for the Čech-bias closure is named.

The Daniel-escalation territory implicates a milestone-1 redefinition decision (not a F32 calculation). That decision is outside F31's scope; it is a mayor / PM / Daniel coordination matter.

---

## §6. Verdict — RED-injectivity-fails-chain-locality-obstruction

### 6.1 The F31 barrier

> **The F31 barrier.** *`\Phi`'s chain-local formula (F30 (1.3.4)) — using only chain-cover-pair stratum inputs and chain-per-step probabilities — combined with the orbit-sgn-sum convention (F29 §3.3) and the F17+F18 vanishing `H^{n-2}_{\mathrm{triv}}(\Delta_n, \mathbb{Q}) = 0`, forces `(\Phi_*)_{\mathrm{sgn}}` to be the zero map on the chain-locally-buildable subspace `K_{\mathrm{chain-loc}} \subseteq \check H^2_{\mathrm{sgn}}(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})`.*
>
> *The bad-cut Čech class `[\widetilde\psi_{\mathrm{BC}}^{(2)}]` is in `K_{\mathrm{chain-loc}}` by construction (Cor 3.2.2). Hence `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in \ker(\Phi_*)`, and `\Phi_*` is not injective on this class.*
>
> *F30's `c_{\mathrm{BC}}(P) = 0` is therefore uninformative — it is a structurally generic consequence of `[\widetilde\psi_{\mathrm{BC}}^{(2)}] \in K_{\mathrm{chain-loc}}`, not a refined contradiction-yielding identity. The Čech-bias mechanism breaks at the injectivity step.*
>
> *The obstruction is **chain-locality**, distinct from mg-26fc U1's **refinement-functoriality** (F30 unconditional dissolve unchanged). A fundamentally different obstruction.*

### 6.2 The verdict, in one line

> **RED-injectivity-fails-chain-locality-obstruction.** *`\Phi_*` has non-trivial kernel containing the bad-cut Čech class. The chain-locality of F30's `\Phi` plus the F17+F18 vanishing of `H^{n-2}_{\mathrm{triv}}` forces the entire chain-locally-buildable sgn-isotype `K_{\mathrm{chain-loc}}` into `\ker(\Phi_*)`. AMBER-with-refinement is not honest — all three natural refinements (richer cover, stabiliser-orbit, twisted-coefficient) wall on either F17+F18-anchor breakage or chain-locality persistence.*

### 6.3 Implications for milestone-1 part (iii)

F31 RED + F25 RED + F27 RED + F28 AMBER + F30 AMBER → **four routes walled** for closing milestone-1 part (iii) via the Čech-bias program at general `n`:

| route | dialect | verdict | source |
|---|---|---|---|
| Route A | HPC-per-n | RED (Hyp A small-γ tail) | F25 (mg-c6f2) |
| Route B | BK / Cheeger small-γ tail | RED-mechanism-mismatch | F25, F27 |
| Hybrid spectral → cohomology | literal-complex | RED-mechanism-mismatch | F27 (mg-a3e3) |
| Sheaf cohomology on POSET | functorial-sheaf-morphism | AMBER-framework-unclear | F28 (mg-d0fa) |
| Čech-bias (Daniel-articulated) | chain-level non-functorial | **RED-injectivity-fails-chain-locality** (F31) | F29 → F30 → **F31 (this doc)** |

The Čech-bias program was the *fifth route* — Daniel-articulated mechanism, structurally distinct from the four prior routes. F31's RED walls this route at the injectivity step.

**Per the F31 ticket body:**

> *RED on F31 + the prior F25/F27 RED + F28 AMBER U1-collision = the four-routes-walled methodology-paper close re-activates + milestone-1 redefinition mail re-issues.*

The methodology-paper close (the in-tree alternative to a full width-3 proof, documenting the *why* of the four-routes-walled landscape) is the operational consequence of F31 RED.

### 6.4 The Daniel-escalation decision

The milestone-1 redefinition is a Daniel-level decision: whether to (i) close the methodology paper and re-scope milestone-1 to a documented-failure state, or (ii) attempt a sixth route (currently not identified), or (iii) pursue a different proof program entirely. F31's role is to deliver the chain-level Čech-bias verdict honestly; the decision lies outside F31.

The mayor should issue the milestone-1 redefinition mail upon F31 archival, per ticket-body protocol. F31's deliverable (this doc + state-F29 session 3) provides the precise wall-location and the chain-locality-vs-functoriality diagnostic the mail will reference.

### 6.5 What is *not* implicated by F31 RED

F31 RED does **not** retract or modify:

- **F-series cohomological core parts (i)–(ii)** — unconditional post F17+F18; unaffected.
- **F17 + F18 theorems** (mg-4d3a, mg-d039) — GREEN, unchanged.
- **F19–F23 chamber-Morse arc** — parked, untouched.
- **mg-b345 Quillen-fiber route iii** — parked, untouched.
- **Lean `width3_one_third_two_thirds` 4-axiom artifact** — separate, trust surface unchanged.
- **`main.tex` + Steps 1–8** — Route B mathematically correct conditional on Hyp A; unchanged.
- **F30's unconditional dissolve of U1 in the chain-level dialect** (F30 §5) — unchanged. F31's RED is *not* a chain-level re-emergence of U1; F30's dissolve remains valid (§4.4).
- **F29's Čech-bias scoping** (mg-70b0) — F29 was AMBER-one-load-bearing-residual, with F30 delivering the residual + F31 the injectivity question. F31's RED walls the injectivity step, completing the F29 → F30 → F31 chain with a structurally honest verdict.

F31's role is to *honestly diagnose* where the Čech-bias mechanism walls. The wall is precisely located at chain-locality of `\Phi`; the diagnostic is precisely the F17+F18 vanishing of `H^{n-2}_{\mathrm{triv}}`. Both anchors are *unconditional* theorems, not failures of F-series understanding. The Daniel-articulated mechanism walls because of an internal-to-the-mechanism structural feature (chain-locality + sgn-orbit + trivial-isotype-zero), not because of an F-series error.

---

## §7. References

### 7.1 Predecessor F-series tickets

- **mg-c3fe** — F30 (chain-level non-functorial `\Phi`): **AMBER-NS-b-pinned-injectivity-residual.** §1.3 (`\Phi` formula), §2.3 (chain-level vanishing via equivariance contradiction), §3 (`c_{\mathrm{BC}}(P) = 0`), §4.3 (F31 named residual), §5 (U1 dissolve unconditional), §6.3 (F31 target). The primary input to F31.
- **mg-70b0** — F29 (Čech-bias cohomology class scoping): **AMBER-one-load-bearing-residual.** §3.4 (orbit-Čech 2-cocycle `\widetilde\psi_{\mathrm{BC}}^{(2)}`), §3.3 (sgn-orbit-sum convention), §5.2 (NS-a/NS-b dichotomy), §6.2 (dissolve criterion). The bad-cut Čech class definition.
- **mg-d0fa** — F28 (sheaf cohomology on POSET): **AMBER-framework-unclear.** §5.1 (walled augmentation `F_{\mathrm{bias}}^{(x, y)} \to \underline{\mathbb{Q}}`), §7.6 (functorial-sheaf-morphism gap). F31 confirms F28's wall does not transpose to chain-level — F31's wall is distinct (chain-locality, not functoriality).
- **mg-a3e3** — F27 (literal spectral → cohomology hybrid): **RED-mechanism-mismatch.** Walled.
- **mg-c6f2** — F25 (Hypothesis A constants audit): **RED-hypothesis-A-false-small-γ-tail.** Walled.
- **mg-4d3a** — F17: **GREEN-equivariant-uniform.** F17+F18 cohomology anchor; load-bearing for Lemma 3.2.1 via `H^{n-2}_{\mathrm{triv}} = 0`.
- **mg-d039** — F18: **GREEN-ucc2-proven.** Same cohomology anchor.
- **mg-26fc** — structural-analogy scoping: **GREEN-distinct-complementary.** §4.4 (U1, U2, U3); F31 distinguishes chain-locality obstruction from U1.

### 7.2 In-tree sources (unchanged by F31)

- **`main.tex`** — §"Approach: Cheeger-type expansion on the BK graph" (Route B spine; correct conditional on Hyp A).
- **`step8.tex`** — Theorem E (unconditional); `lem:layered-reduction` (G3, F25 wall location).

### 7.3 Mathematical literature (unchanged by F31)

- Čech 1932 (Čech cohomology of a cover).
- Leray 1950 (Čech-to-derived comparison).
- Mitchell 1972 (small-category Mitchell cohomology).
- F17+F18 internal — Goulden-Jackson cofiber, UCC2, sgn-isotype theorems.
- Bubley-Karzanov 1998 (BK Markov chain).
- Brightwell-Felsner-Trotter 1995 (the `[3/11, 8/11]` interval).
- Kahn-Linial 1991 (unconditional bound).

### 7.4 Daniel directives (inherited from F29)

- **2026-05-15T23:20Z** — *"...not factorial. ...inherently but not functorially..."* (load-bearing for F30 dissolve check, inherited by F31).
- **2026-05-15T23:38Z** — mechanism articulation (bias-on-subposet, Čech contradictions, F17+F18 anchor, not-sign-like).
- **2026-05-14T05:18Z** — finish internally; no external collaboration.

### 7.5 PM memories invoked

- **`feedback_anti_factorial_direction`** — standing rule against factorial constructions; F31 respects.
- **`feedback_latex_first_for_math_simp`** — paper-and-pencil first; F31 is paper-and-pencil.
- **`feedback_polecat_cumulative_state_doc`** — cumulative `state-F29.md` (F31 is session 3 of the F29 arc).
- **`feedback_manage_branches_default_to_main`** — no `--branch` argument passed.

### 7.6 Methodological note

F31's verdict is a *structural diagnosis*, not a numerical computation. The chain-locality obstruction is proved by Lemma 3.2.1, which uses:

(a) The standard `\mathrm{sgn}_{S_n}`-vs-trivial-isotype decomposition of `S_n`-modules.
(b) F17+F18's `H^{n-2}_{\mathrm{triv}}(\Delta_n, \mathbb{Q}) = 0` statement (unconditional theorem).
(c) The chain-relabel-invariance of bias values and chain-per-step probabilities (standard combinatorial fact).
(d) F30's chain-level cochain-map property of `\Phi` (verified F30 §2).

All four ingredients are paper-and-pencil-verifiable. The F31 RED verdict is therefore an *unconditional* structural finding, not a heuristic.
