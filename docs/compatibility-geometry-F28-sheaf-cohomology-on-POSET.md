# Compat-Geom — F28: Sheaf cohomology on POSET as the spectral → cohomology bridge — scoping the Daniel-outlined Lemma C-prime program (mg-d0fa)

**Branch:** `polecat-cat-mg-d0fa` (mg-d0fa).
**Parent:** Daniel reminders 2026-05-15T19:59Z (intuition outline) + 2026-05-15T20:22Z (start immediately on the program; union\_closed lower priority and should emulate). Also mg-a3e3 (F27, **RED-mechanism-mismatch**) — F27 walled the *literal* complex-comparison-map candidates (Garland-on-Δ, ICOP↔Cheeger, F17+F18-as-Step-8-replacement). F28 pursues the **different mathematical framework** Daniel pre-positioned: sheaf / category cohomology on **POSET** (the small category of posets and refinement morphisms).
**Chain:** F10 → F17 (mg-4d3a) → F18 (mg-d039) → F19–F23 chamber-Morse arc → F24 → F25 (**RED**) → F27 (**RED**) → **F28 (mg-d0fa, this doc).**
**Type:** Structural research scoping (Grothendieck topos / sheaf cohomology on a small category). Paper-and-pencil, LaTeX-style Markdown; **no new axioms; no Lean changes; no HPC; no computation.** Multi-session-able; cumulative state ledger in `docs/state-F28.md`. Cross-repo read of `one_third_width_three` (`main.tex`, `step1.tex`–`step8.tex`) only when needed.
**Daniel directives:** 2026-05-14T05:18Z (finish internally; no external collaboration); 2026-05-15T19:59Z (the intuition: *"If you take any subposet of bk graph it should be sort of uniform and nice, expander-y. But a low conductance cut is non-uniform. Ideally the cohomology of the category of posets should help us to stitch together these locally uniform pieces and show that something globally non uniform has a certain shape. Now here the cohomology is related to the poset and its subposets rather than the whole category but it should be well limited by what we proved already."*); 2026-05-15T20:22Z (*"start on the 1/3-2/3 cohomology program immediately; union\_closed lower priority and should emulate."*).

---

## Verdict: **AMBER-framework-unclear.**

The categorical framework — sheaf cohomology on the small category **POSET** (concretely `PPF_n` with refinement morphisms, the proper-and-proper sub-lattice of all posets on `[n]`) — **is well-defined as math, and its principal cohomology theory is rendered unconditionally non-trivial by F17+F18**. Specifically (§2, §4):

- **The right cohomology theory is the Alexandrov / Mitchell cohomology** `H^k(PPF_n, F)` of the small category `PPF_n` with values in a sheaf `F` on its Alexandrov topology (equivalently the cohomology of the order complex `Δ_n = Δ(PPF_n)` with the corresponding constructible-coefficient system). For the constant sheaf `Q`, F17+F18 give the *unconditional* H-Cox + sgn answer: `H̃^k(PPF_n, Q) = 0` for `0 < k < n−2`, `= sgn_{S_n}` for `k = n−2`, all `n ≥ 3`.
- **The right obstruction class is `ω_bal^{(n)} ∈ H̃^{n-2}(PPF_n, Q)^{sgn}`** — the unique-up-to-scalar non-trivial top class. F17+F18 establish its existence *unconditionally*. This is the cohomological-balance class identified pre-F17 by mg-d60d §3.5 (the (CB) conjecture) and pre-F17 by `compatibility-geometry-poset-cohomology-scoping.md` §3.4: it had been *conditional* on the sphere topology of `Δ(\overline{Pos_n^{sub}})` (cat-mg-5ee2), and F17+F18 close that conditional unconditionally.

**This is the framework's first non-trivial content** and was not available to mg-d60d (2026-05-13): the load-bearing (C1) sphere-topology assumption of the earlier scoping is now **proven** (F17+F18, post 2026-05-14). The categorical home is real and unconditional in its cohomology-of-constant-sheaf incarnation.

**But the operational mechanism by which F17+F18 would constrain the BK-spectral side fails (§5, §7),** for the same fundamental reason F27 RED'd, sharpened in the categorical setting. The "right sheaf" that would encode BK-spectral data of `P` and its subposets such that F17+F18 forbids low-conductance cuts splits into two regimes, each blocked:

- **Constant-sheaf regime (§5.1).** If the BK-derived sheaf trivializes (canonically or up to weights) to the constant sheaf `Q` — as `F_ℓ` does in mg-d60d §2.4 by the rescaling `β_P = |L(P)| · α_P` — then F17+F18 fully constrains its cohomology, but the cohomology *output* is the F-series ICOP target: `⟨ω_bal^{(n)}, c\rangle ≠ 0` along the canonical critical chain `c*`, equivalent to a product of per-step Pr's being non-zero. This recovers the **existing F-series program** (F10 part (iii) at general `n`) — same open width-3 bridge, recast.
- **Non-constant-sheaf regime (§5.2).** If the sheaf genuinely encodes BK-graph data with per-`P` stalks varying in vertex set (e.g., `F_{cut}(P) = Q^{V(G_{BK}(P))}` or `F_{spec}(P) = Q[\text{Laplacian spectrum of } G_{BK}(P)]`), F17+F18 does *not* directly constrain its cohomology — the cohomology of a sheaf with non-constant stalks is governed by its own restriction maps, and F17+F18's sgn-isotype concentration is a statement about the *constant* sheaf only. Furthermore, the restriction maps `F_{cut}(P) → F_{cut}(P')` for refinements `P ≤ P'` exist only in the *induced-subgraph* direction (refinement *removes* linear extensions, shrinking the BK vertex set), which makes `F_{cut}` a presheaf with surjective restrictions — its higher cohomology in the Alexandrov topology has no manifest connection to the *cohomology of `Δ_n`*. This is F27's inter-complex mismatch in a sheaf-theoretic dialect.

The framework, in summary, is **operationally split**: F17+F18 *does* land as a constraint on the categorical cohomology, but only on the constant-coefficient / weights-trivialized regime, where it reproduces the existing F-series ICOP target without adding constraining power; and the BK-graph-stalk regime, where genuinely new constraining power *would* live, is *not* connected to F17+F18 by any mechanism in hand. F28 does **not** dissolve the F27 RED — it *re-locates* it from "literal comparison map between `Δ_n` and `G_{BK}(P)` cohomologies" to "missing sheaf-theoretic bridge between the constant-sheaf regime and the BK-graph-stalk regime on `PPF_n`."

**Why AMBER and not RED.** F27 ticket spec used RED-mechanism-mismatch for "the bridge as conceived doesn't exist." F28 is *not* in that position: the framework's primary halves *do* exist and have unconditional content. What is missing is the **specific operational mechanism** linking the two halves on the same site `PPF_n`. This is a *framework-unclear* state — the program's mathematical objects are pinned, the F17+F18 input lands, but the lever that would convert F17+F18 into a BK-spectral constraint is not in hand. This is the AMBER-framework-unclear verdict of the F28 ticket spec, verbatim:

> *AMBER-framework-unclear — sheaf-cohomology-on-POSET is well-defined but the specific BK-spectral sheaf + F17+F18-constraint combination does not have an obvious operationalisation. Name the precise gap.*

§7.3 names the precise gap: an **explicit sheaf-theoretic comparison map** `Φ : F_{BK} → F_ℓ`, or a **derived-functorial relation** in `D^b(\text{Sh}(PPF_n))`, between (i) a sheaf `F_{BK}` whose stalks encode BK-spectral cut-data and (ii) the weight-trivialized linear-extension sheaf `F_ℓ ≅ \underline{Q}`. The earlier mg-26fc §4.4 U1 candidate ("a per-`P` complex `K(P)` whose Garland spectral data identifies with `G_{BK}(P)`'s and that admits a comparison map to `Δ_n`") is the closest extant articulation; F28 sharpens it from a topological-complex form to its sheaf-theoretic equivalent and confirms it is not in hand.

**Why AMBER and not GREEN-partial.** GREEN-partial would require some sub-question — sheaf choice, cohomology degree, or constraint mechanism — to be *substantially* scoped, with the residual being a *named-and-prioritised* continuation. F28 substantially scopes the cohomology degree (`n − 2`, the sgn-isotype) and the obstruction class (`ω_bal^{(n)}`), both consequences of F17+F18 already established. But the *sheaf choice* — the load-bearing piece — is *not* substantially scoped: the four candidate sheaves (a)–(d) of the ticket spec all run into one of the two regime walls (§5.1 / §5.2). What survives is the F-series program in categorical dialect — useful **structural context**, but **not** a new operational handle on the BK side.

**Operational consequence for F29 / milestone 1 (§8).** F28 does *not* propose a F29 sub-ticket as a clear program-execution target. The most concrete continuation is **sharper:** **mg-26fc §4.4 U1**, recast in F28 language — *construct an explicit sheaf-theoretic comparison map between a BK-stalk sheaf and the linear-extension weight sheaf `F_ℓ`*. This is a research project of unknown size and is *not* polecat-attackable in a scoping pass; F28 does not advance it. The F-series program (F10 part (iii) width-3 bridge) remains the operationally indicated direction.

The framework's **positive structural finding** — that F17+F18 unconditionally fix the cohomological side of the categorical bridge, with `ω_bal^{(n)}` the explicit obstruction class — does upgrade the earlier mg-d60d *AMBER-specialist-conditional* verdict to AMBER *without* the cat-mg-5ee2 sphere-topology dependency. The cohomological side is now *unconditional*; only the bridge to BK-spectral data is unclear. This is a strict positive vs. the 2026-05-13 state.

---

## §0. Setup — what the F28 framework is supposed to be

### 0.1 Daniel's outline, verbatim

Daniel reminder 2026-05-15T19:59Z:

> *"If you take any subposet of bk graph it should be sort of uniform and nice, expander-y. But a low conductance cut is non-uniform. Ideally the cohomology of the category of posets should help us to stitch together these locally uniform pieces and show that something globally non uniform has a certain shape. Now here the cohomology is related to the poset and its subposets rather than the whole category but it should be well limited by what we proved already."*

Daniel reminder 2026-05-15T20:22Z:

> *"Please start on the 1/3-2/3 cohomology program I outlined immediately. Union closed is lower priority and likely should emulate what we do here."*

The five working components of this outline (F28 ticket §1):

1. **Locally uniform / expander-y subposets.** Each "subposet of bk graph" — a subgraph `G_{BK}(P')` for `P' \le P` a refinement of `P` (so `L(P') \subseteq L(P)` and `G_{BK}(P')` is an induced subgraph of `G_{BK}(P)`) — is, individually, well-mixing / expander-y. This is the BK-side property under Bubley–Karzanov mixing and Theorem E.

2. **Non-uniform global structure = low-conductance cut.** A specific `Q` for which `G_{BK}(Q)` has a low-conductance pair-cut violates the uniform pattern.

3. **Cohomology of the category of posets stitches together the locally uniform pieces.** A sheaf cohomology theory on `PPF_n` (or a sub-category) should detect the global obstruction created by non-uniformity.

4. **Cohomology of the poset and its subposets, not the whole category.** The relevant site is the down-set or up-set generated by a fixed `P`, not all of `PPF_n` at once. (Concretely: for a fixed `P`, the cohomology of `\uparrow P = \{P' \in PPF_n : P \le P'\}` — the refinements of `P` — with values in a sheaf encoding BK data of each refinement.)

5. **"Well limited by what we proved already."** F17+F18 (and consequently the cohomology of `Δ_n`) constrain the categorical cohomology in a way that should land as the constraint forbidding low-conductance configurations.

### 0.2 What F28 *distinguishes itself from* (F27 RED, recapped)

F27 (mg-a3e3) walled three candidate operationalisations of the *literal* "spectral → cohomology" hybrid: (1) Garland-on-`Δ(PPF_n)` (links of `Δ_n` are not `G_{BK}(P)`'s, inter-complex mismatch); (2) ICOP-pairing ↔ BK Cheeger (per-step volume fraction vs. cut conductance, quantitative mismatch); (3) F17+F18 as a replacement for `lem:layered-reduction` (cohomology has no γ-input, scope-blind / circular). All three are *bridges between two pre-existing complexes* (`Δ_n` and `G_{BK}(P)`).

F28's framework is **categorical and sheaf-theoretic**, not bridge-construction-based. It postulates:

- A small category `\mathcal{C}` — `PPF_n` with refinement morphisms, or a sub-category — with a Grothendieck topology `\tau` (most naturally the Alexandrov topology of down-closed sets, since `PPF_n` is a finite poset under refinement; see §2.1).
- A sheaf `F \in \text{Sh}(\mathcal{C}, \tau)` whose stalk `F(P)` encodes the BK-spectral data of `P` *and its subposets* (the "subposets" here being refinements `P' \ge P`, so that `G_{BK}(P')` is an induced subgraph of `G_{BK}(P)`; see §3).
- The sheaf cohomology `H^k(\mathcal{C}, F)` as the global obstruction-carrier.
- F17+F18 lands as a constraint on `H^k(\mathcal{C}, F)` via comparison with the constant sheaf `Q` (or another canonical reference sheaf) — *not* via a direct identification of `H^*(F)` with `H^*(\Delta_n)`.

The distinction is **direction of approach**: F27 tried to push BK-spectral data INTO F-series cohomology through an explicit comparison map; F28 tries to let F17+F18 LAND as a constraint on a categorical cohomology theory built around BK-spectral data. The constraint is *sheaf-theoretic / categorical-cohomological*, not a literal complex identification.

The questions F28 must answer (per ticket §1):

> 1. Pin the right sheaf precisely (the four candidates (a)–(d): cuts of `G_{BK}(P)`, Walsh / spectral data, chain-level Cheeger / conductance witness, sub-sheaf of obstruction sheaf).
> 2. Identify the right cohomological invariant (`H^*` vs. hypercohomology vs. derived sections vs. category cohomology).
> 3. Pin the F17+F18 constraint mechanism (global-sections, hypercohomology-limit, representability).
> 4. Assess operational viability.
> 5. State the locality-uniform → globality-non-uniform argument precisely.

§3–§7 walk these questions, in order.

### 0.3 The earlier scoping — mg-d60d, mg-5ee2 — and what F17+F18 unlocked

The categorical / sheaf-cohomology approach was previously scoped in `docs/compatibility-geometry-poset-cohomology-scoping.md` (mg-d60d, 2026-05-13). That scoping landed **AMBER-specialist-conditional**, with three load-bearing conditional inputs:

- **(C1)** `|\Delta(\overline{Pos_n^{sub}})|` is a topological sphere `S^{d_n}` of explicit dimension. *Deferred to cat-mg-5ee2.*
- **(C2)** The top fundamental class `\omega_{bal}` admits a Poincaré-dual representation as a balance functional.
- **(C3)** *(RC = balance)* for width 3 — every refinement-collapse exception is order-visible (i.e., visible via transitive closure of `<_P`).

F17 (mg-4d3a) + F18 (mg-d039), delivered 2026-05-14 / 2026-05-15, established **(C1)** *unconditionally and in a much stronger rational form*: the H-Cox + sgn theorem `\widetilde H^k(\Delta_n; \mathbb{Q}) = sgn_{S_n}` for `k = n−2`, else `0`, for all `n \ge 3`. This is the **rational sphere statement** for `\Delta_n = \Delta(PPF_n)` — equivalent (rationally and as `S_n`-representations) to `\Delta_n \simeq_{\mathbb{Q}} S^{n-2}` carrying `sgn_{S_n}` on top cohomology. *F17+F18 fully discharge (C1).*

**The mg-d60d framework was conditional on the sphere topology; F17+F18 unconditional makes it operational.** F28 picks up exactly here, with (C1) released, and asks whether the remaining (C2) and (C3) — which are about the BK-spectral / cut-data side, not the cohomology — can be advanced through the F17+F18-constrained categorical framework. This is the precise content of the F28 ticket.

### 0.4 What F28 does **not** do, by mandate

- F28 does **not** introduce new axioms, Lean changes, HPC artifacts, or computation. It is paper-and-pencil structural scoping (ticket §"Constraints").
- F28 does **not** propose to re-walk F27's RED'd candidates (Garland-on-Δ, ICOP-Cheeger, F17+F18-as-Step-8-replacement). Those are **walled** and stay walled.
- F28 does **not** propose to attack the F-series part (iii) width-3 bridge directly — that is the **target** (or close to it) of the framework, not the method.
- F28 does **not** touch the F-series cohomological core (parts (i)–(ii)) — those are *unconditional* post F17+F18 and untouched here.
- F28 does **not** touch the `width3_one_third_two_thirds` Lean 4-axiom artifact; trust surface unchanged.

The two deliverables (ticket §"Deliverables") are this doc + `docs/state-F28.md`.

---

## §1. The site — what "POSET (the category)" means precisely

The F28 framework requires a small category `\mathcal{C}` of posets, with morphisms encoding the "subposet" relation Daniel's intuition refers to. Several inequivalent choices exist; we walk them and commit.

### 1.1 Four candidate categories

| candidate | objects | morphisms | dimensionality | role |
|---|---|---|---|---|
| **`PPF_n`** | proper partial orders on `[n]` (non-empty and non-total relations) | unique `P \to P'` iff `<_P \subseteq <_{P'}` (refinement) | dim `Δ(PPF_n) = n − 2` (rationally a sphere of dim `n − 2` by F17+F18) | the F-series cohomological side |
| **`Pos_n^{sub}`** | all partial orders on `[n]`, including antichain `\hat 0` and total orders | refinement | contractible (cone from `\hat 0`); proper part `\overline{Pos_n^{sub}}` is `PPF_n` up to `\hat 0` removal | mg-d60d / mg-5ee2's site |
| **POSET** (large) | all finite posets on any `[n]`, modulo isomorphism | order-preserving maps (not just refinements) | infinite-dimensional category | analogous to FI, central-stability scoping |
| **`L(P)`** for fixed `P` | linear extensions of `P` (vertices of `G_{BK}(P)`) | adjacent-transposition edges | 1-dimensional graph | the BK-spectral side |

The Daniel-outline phrase *"cohomology of the category of posets"* most naturally refers to candidate 1 or 2 — small categories with refinement morphisms. The choice between `PPF_n` and `Pos_n^{sub}` is essentially: include or exclude the antichain and total orders. F17+F18 are stated on `\Delta(PPF_n) = \Delta(Pos_n^{sub} \setminus \{\hat 0, \text{total orders}\})`, so for direct application of F17+F18 we want the proper part — which is exactly **`PPF_n`** in the F-series notation.

### 1.2 Commitment: `\mathcal{C} = PPF_n` with the Alexandrov topology

We commit to `\mathcal{C} = PPF_n` for all of §2–§8. Justifications:

(i) **F17+F18 are stated on `\Delta(PPF_n)`.** Direct use of their unconditional content (H-Cox + sgn) requires the small category whose nerve is `\Delta(PPF_n)`. This is `PPF_n` with refinement morphisms.

(ii) **The "subposet" reading is natural.** A "subposet of bk graph `G_{BK}(P)`" is, most naturally, the induced subgraph `G_{BK}(P') \subseteq G_{BK}(P)` for `P'` a *refinement* of `P` (so `L(P') \subseteq L(P)` and the vertex set restricts). This corresponds to the upward-refinement direction in `PPF_n`: the up-set `\uparrow P = \{P' \in PPF_n : P \le P'\}` parametrises the subposets of `G_{BK}(P)`. (Note the *opposite* would be `\downarrow P = \{P' \le P\}`, which parametrises *coarsenings* of `P` and *supergraphs* of `G_{BK}(P)`; not the BK-subposet reading.)

(iii) **F-series compatibility.** F17 / F18 / F25 / F27 all work over `PPF_n`. Using the same site makes cross-citation clean.

(iv) **mg-d60d compatibility.** The earlier scoping used `\overline{Pos_n^{sub}}` which is `PPF_n` up to antichain/total-order removal; the cohomology theories are the same.

**The Alexandrov topology.** `PPF_n` is a finite poset; its **Alexandrov topology** has open sets = up-closed subsets (i.e., for `P \in U` and `P' \ge P`, `P' \in U`). Equivalently, presheaves on `PPF_n` are functors `PPF_n^{op} \to \text{Vec}_\mathbb{Q}`, and a presheaf is a sheaf in the Alexandrov topology iff it satisfies the limit condition over basic opens `\downarrow P = \{P' : P' \le P\}` — which for a poset is *automatic* (the Alexandrov topology has enough points = the posets themselves, and the sheaf condition over the cone-like covers is trivially satisfied for presheaves).

So in the Alexandrov topology on `PPF_n`:

$$\text{Sh}(PPF_n, \tau_{\text{Alex}}) \;\cong\; \text{Fun}(PPF_n^{op}, \text{Vec}_\mathbb{Q})$$

(every presheaf is a sheaf). The Alexandrov topology is the maximally permissive choice; it puts no sheaf condition beyond functoriality. This is **convenient for F28** because we don't have to argue separately about the sheaf condition — any functor `F : PPF_n^{op} \to \text{Vec}_\mathbb{Q}` qualifies.

(The (T3) linear-extension-restriction topology of mg-d60d §1.1 is a *non-trivial* refinement; we discuss it as a comparison in §4.4. For the bulk of F28 the Alexandrov topology is sufficient and avoids the (T3) complications.)

### 1.3 The Alexandrov topology has a clean cohomology — Mitchell / Baues–Wirsching

For a small category `\mathcal{C}` and a presheaf `F : \mathcal{C}^{op} \to \text{Vec}_\mathbb{Q}`, the **Mitchell cohomology** / **Baues–Wirsching cohomology** of `\mathcal{C}` with coefficients in `F` is

$$H^k(\mathcal{C}, F) \;:=\; H^k\bigl(\text{Tot}\, C^\bullet(\mathcal{C}, F)\bigr), \qquad C^k(\mathcal{C}, F) := \prod_{P_0 < P_1 < \cdots < P_k} F(P_0),$$

with the alternating-sum-of-restrictions coboundary (mg-d60d §2.3). When `\mathcal{C}` is the Alexandrov topology of a finite poset `\mathcal{P}` and `F` is a presheaf, `H^k(\mathcal{P}, F)` agrees with the **sheaf cohomology** of `F` (viewed as a sheaf in the Alexandrov topology) and with the **constructible-coefficient cohomology** of the order complex `|\Delta(\mathcal{P})|` (Mitchell 1972; Baues–Wirsching 1985; Quillen 1973 Thm 1).

For the *constant* presheaf `F = \underline{\mathbb{Q}}`, `H^k(\mathcal{P}, \underline{\mathbb{Q}}) = H^k(|\Delta(\mathcal{P})|; \mathbb{Q})` is the ordinary rational cohomology of the order complex (Mitchell 1972 Cor. 4).

**This gives F28 its primary identification:**

$$\boxed{\ H^k(PPF_n, \underline{\mathbb{Q}}) \;\cong\; \widetilde H^k(\Delta_n; \mathbb{Q}) \cdot \text{(plus a degree-0 } \mathbb{Q}\text{ summand)}.\ }$$

F17+F18 then give the unconditional sgn-isotype content:

$$H^k(PPF_n, \underline{\mathbb{Q}}) \;=\; \begin{cases} \mathbb{Q} & k = 0 \\ 0 & 0 < k < n - 2 \\ sgn_{S_n} & k = n - 2 \\ 0 & k > n - 2 \end{cases} \qquad \text{unconditionally, all } n \ge 3.$$

This is the F28 framework's **first unconditional fact** — the categorical home of F17+F18.

### 1.4 The `S_n`-action and the equivariant cohomology

`S_n` acts on `PPF_n` by relabelling `[n]`. This action lifts to all the categorical machinery: `\text{Sh}(PPF_n) \to \text{Sh}(PPF_n)` by pullback, `H^k(PPF_n, F)` carries an `S_n`-action for `F` an `S_n`-equivariant sheaf, etc.

F17+F18 are stated equivariantly: `H^{n-2}(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` as `S_n`-representations. The unique-up-to-scalar generator is `\omega_{bal}^{(n)}`, the "balance class."

The categorical framework therefore comes equipped with a canonical equivariant top class, *unconditionally*. This is the F28 framework's **second unconditional fact**.

### 1.5 Up-sets and down-sets — the F28 sub-category

Daniel's outline §5: "cohomology related to the poset and its subposets rather than the whole category." This points to a *sub-site*: for fixed `P \in PPF_n`, the up-set

$$\uparrow P \;:=\; \{P' \in PPF_n : P \le P'\}$$

parametrising the refinements of `P`. (Equivalently in BK terms, the subposets-of-`G_{BK}(P)` story: `L(P') \subseteq L(P)` for `P' \in \uparrow P`, so `G_{BK}(P') \subseteq G_{BK}(P)` as an induced subgraph.)

`\uparrow P` is itself a finite poset, Alexandrov-topologised, with its own Mitchell cohomology `H^k(\uparrow P, F|_{\uparrow P})`. The order complex `\Delta(\uparrow P)` is a sub-complex of `\Delta_n`.

For *constant* coefficients, the cohomology of `\uparrow P` is related to that of `PPF_n` by **Mayer–Vietoris** / **restriction sequences**:

$$\cdots \to H^k(PPF_n, \underline{\mathbb{Q}}) \xrightarrow{\text{res}} H^k(\uparrow P, \underline{\mathbb{Q}}) \to H^{k+1}_{c}(PPF_n \setminus \uparrow P, \underline{\mathbb{Q}}) \to \cdots,$$

where `H^*_c` denotes compactly-supported (or rather, *not-extended-to-`\uparrow P`*) cohomology.

If `\uparrow P` is well-understood (e.g., rationally spherical with explicit dimension `n − 2 - \text{rk}(P)`), F17+F18's `\omega_{bal}^{(n)}` *restricts* to a class `\omega_{bal}^{(n)}|_{\uparrow P} \in H^{n-2}(\uparrow P, \underline{\mathbb{Q}})`. The restriction's vanishing or non-vanishing is a local-to-global constraint.

**This is the framework's third structural fact:** the restriction of `\omega_{bal}^{(n)}` to up-sets parametrising BK-subposet families gives an explicit, computable, equivariant local-to-global obstruction.

### 1.6 What the framework has, summarised

After §1, the framework has:

(F-1) **Site.** `PPF_n` with the Alexandrov topology. (`S_n`-equivariant.)
(F-2) **Cohomology theory.** Mitchell / Baues–Wirsching cohomology, equivalent to constructible-coefficient cohomology of `\Delta_n`.
(F-3) **F17+F18 unconditional content.** `H^k(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` in degree `n−2`, else trivial.
(F-4) **Canonical obstruction class.** `\omega_{bal}^{(n)} \in H^{n-2}(PPF_n, \underline{\mathbb{Q}})^{sgn}` exists, unique up to scalar, *unconditional*.
(F-5) **Sub-site framework.** Up-sets `\uparrow P` parametrise BK-subposet families; restriction maps carry local-to-global content.

What the framework *needs* next:

(N-1) **A sheaf encoding BK-spectral data of subposets** — concrete construction (§3).
(N-2) **A bridge between that sheaf's cohomology and the F17+F18 obstruction class** — the lever that lets F17+F18 forbid low-conductance cuts (§5).
(N-3) **A precise locality-uniform → globality-non-uniform statement** — formalising Daniel's intuition (§6).
(N-4) **An operational viability assessment** — does the framework, with (N-1)–(N-3) attempted, actually constrain the BK side (§7)?

§2 expands (F-1)–(F-5); §3 walks the candidate sheaves for (N-1); §4 / §5 walk (N-2); §6 walks (N-3); §7 walks (N-4) and lands the AMBER verdict.

---

## §2. What F17+F18 actually give us in the categorical framework

This section restates F17+F18 in the categorical language, as input to §3–§7. No new content — just the rephrasing.

### 2.1 F17+F18 unconditionally compute `H^*(PPF_n, \underline{\mathbb{Q}})`

**F17 (mg-4d3a)** — `\widetilde H_d(\Delta_{n+1}/\Delta_n) \cong 2 \cdot \widetilde H_{d-1}(\Delta_n)` as `S_n`-reps, all `n \ge 3`, unconditionally. So `(UCC.1)(n) \iff Hyp(n)` — discharged by induction.

**F18 (mg-d039)** — `\iota_n : \Delta_n \hookrightarrow \Delta_{n+1}` is null-homotopic by an explicit `S_n`-equivariant poset zig-zag (κ_n combination with `ω_n`); hence `\iota_n^* = 0`, hence `\delta_n` injective, hence (UCC.2) for all `n`. The F10 induction closes.

**Joint consequence (F18 §0.3).** F10 cohomological core (parts (i)–(ii)) is UNCONDITIONAL:

$$\widetilde H^k(\Delta_n; \mathbb{Q}) \;=\; \begin{cases} sgn_{S_n} & k = n - 2 \\ 0 & 0 < k < n - 2 \text{ or } k > n - 2 \end{cases} \qquad \text{all } n \ge 3.$$

**Categorical re-statement.** Via Mitchell's identification of Alexandrov-sheaf cohomology with order-complex cohomology (§1.3):

$$H^k(PPF_n, \underline{\mathbb{Q}}) \;\cong\; \widetilde H^k(\Delta_n; \mathbb{Q}) \oplus (\mathbb{Q} \text{ if } k = 0),$$

so for `k \ge 1`:

$$H^k(PPF_n, \underline{\mathbb{Q}}) \;=\; \begin{cases} sgn_{S_n} & k = n - 2 \\ 0 & 1 \le k < n - 2 \text{ or } k > n - 2 \end{cases}$$

**This is the categorical input to F28.** Every subsequent constraint argument in §5 must route through this.

### 2.2 The canonical balance class `\omega_{bal}^{(n)}`

The 1-dimensional `sgn`-isotype in degree `n − 2` is spanned by `\omega_{bal}^{(n)} \in H^{n-2}(PPF_n, \underline{\mathbb{Q}})^{sgn}`. Concretely (mg-d60d §3.4):

$$\omega_{bal}^{(n)}(P_0 < P_1 < \cdots < P_{n-2}) \;=\; \prod_{i=0}^{n-3} \Pr_{P_i}[a_i <_{P_i} b_i] \cdot (\text{normalisation}),$$

where `(a_i, b_i)` is the cover relation added in `P_i \to P_{i+1}` and `\Pr_{P_i}[\cdot]` is the chamber-uniform-measure probability that `a_i < b_i` in a random linear extension of `P_i`. This is a *cocycle* representative — the cohomology class is well-defined up to coboundaries.

**Properties** (F17 §0.2 + F18 §0.2 + mg-d60d §3.4–§3.5):

(P-1) `\omega_{bal}^{(n)} \ne 0` in `H^{n-2}(PPF_n, \underline{\mathbb{Q}})` (F17+F18 unconditional non-vanishing in `sgn`-isotype).
(P-2) `\omega_{bal}^{(n)}` lies in `sgn_{S_n}`-isotype (F17+F18 isotype-pinned).
(P-3) `\omega_{bal}^{(n)}` is unique up to scalar (F17+F18 isotype is 1-dimensional).
(P-4) `\langle \omega_{bal}^{(n)}, c^*_n \rangle \ne 0` for *some* explicit critical `(n−2)`-chain `c^*_n` — call this the "canonical critical chain" (F10 §5; verified `n \le 6` by ICOP machinery).
(P-5) The pairing value `\langle \omega_{bal}^{(n)}, c \rangle` for a general `(n−2)`-chain `c = (P_0 < \cdots < P_{n-2})` is, by (the cocycle formula), the product `\prod_i \Pr_{P_i}[a_i <_{P_i} b_i]` (up to normalisation).

(P-4) and (P-5) jointly are the **operational content** of `\omega_{bal}^{(n)}`: it pairs against `(n−2)`-chains in `PPF_n` to give Pr-products, with non-vanishing somewhere along some critical chain.

(P-1)–(P-3) are UNCONDITIONAL post F17+F18. (P-4) is *open at general `n`* — this is the "width-3 bridge" of F10 §7.3–§7.4, verified `n \le 6` by ICOP, with the F19–F23 chamber-Morse arc concluding HPC-per-n with no `n`-uniform discriminator (F23 §4–§5). **F28's framework does not by itself close (P-4) at general `n`** — see §7.2.

### 2.3 The restriction to up-sets

For `P \in PPF_n`, restriction `\text{res}_{\uparrow P} : H^{n-2}(PPF_n, \underline{\mathbb{Q}}) \to H^{n-2}(\uparrow P, \underline{\mathbb{Q}})` gives a class `\omega_{bal}^{(n)}|_{\uparrow P}`. Its non-vanishing carries local-to-global content (cf. §1.5).

`\uparrow P` is rationally the link of `P` in `\Delta_n` (more precisely: `\Delta(\uparrow P \setminus \{P\}) = \text{lk}_{\Delta_n}(P)`, since `\uparrow P` includes `P` as its minimum but `\Delta(\uparrow P)` is the cone of this over `P`). For F17+F18-style constraints to apply to `\text{lk}_{\Delta_n}(P)`, we need this link's rational cohomology. **This is not in hand for general `P`** — F17+F18 control `\Delta_n` globally, not its links.

Honest observation: the F17+F18 unconditional `\Delta_n \simeq_\mathbb{Q} S^{n-2}` *rational sphere* statement does NOT immediately give `\text{lk}(P)` is a rational sphere of dimension `n − 2 − \text{rk}(P) - 1`. Spheres have spherical links, but `\Delta_n` is only *rationally* a sphere, and rational-spherical links is a strictly weaker conclusion (requires integral / homotopy-spherical, not just `\mathbb{Q}`-spherical). So this is an open question — and an *interesting* one for F28's framework, though not in scope for this scoping pass.

(Side note for §8: a F29 sub-question could be — *are the links `\text{lk}_{\Delta_n}(P)` rationally spherical of the predicted dimension `n − 2 − \text{rk}(P) - 1`?* This would refine F17+F18 to the link level.)

### 2.4 The `S_n`-equivariant decomposition

`H^{n-2}(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` as an `S_n`-rep. Decomposing by `S_n`-isotype:

$$H^{n-2}(PPF_n, F) \;=\; \bigoplus_{\lambda \vdash n} (V_\lambda \otimes \text{mult}_\lambda),$$

with multiplicity `\text{mult}_\lambda = 1` for `\lambda = (1^n)` (the sign rep) and `0` otherwise.

This isotype-concentration is `(UCC)` and is F17+F18's *unconditional* core.

For a *non-constant* sheaf `F`, the equivariant cohomology `H^{n-2}(PPF_n, F)` has no such concentration a priori — it depends on `F`. F17+F18's constraint applies *directly* only to sheaves with isotype structure matching the constant case (most cleanly: `F` related to `\underline{\mathbb{Q}}` by a sheaf map). This is exactly the §5 constraint mechanism.

---

## §3. Candidate sheaves on `PPF_n` encoding BK-spectral data of subposets

The ticket §"Goal" §1 names four candidates: (a) cuts; (b) Walsh / spectral data; (c) chain-level Cheeger / conductance witness; (d) sub-sheaf of an obstruction sheaf. We walk each.

For all candidates, the relevant "subposet" reading is **refinements** of a fixed `P`: for `P' \in \uparrow P` (i.e., `P \le P'` in refinement), `L(P') \subseteq L(P)` and `G_{BK}(P')` is the induced subgraph of `G_{BK}(P)`. The restriction maps `F(P) \to F(P')` for `P \le P'` go in the direction of *induced-subgraph restriction* — natural for the Alexandrov topology where opens are up-closed.

### 3.1 Candidate (a) — `F_{cut}`: signed cuts of `G_{BK}(P)`

**Definition.** `F_{cut}(P) := \mathbb{Q}[V(G_{BK}(P))] = \mathbb{Q}^{|L(P)|}` — the vector space spanned by the vertices of `G_{BK}(P)`. A "signed cut" of `G_{BK}(P)` is a vector `v \in \mathbb{Q}^{L(P)}` with `\sum_\sigma v_\sigma = 0`; equivalently the augmentation ideal, the kernel of the augmentation `\epsilon : \mathbb{Q}^{L(P)} \to \mathbb{Q}, \sigma \mapsto 1`.

**Restriction.** For `P \le P'`, `L(P') \subseteq L(P)`. Define `F_{cut}(P) \to F_{cut}(P')` by restriction to the sub-vertex-set:

$$\rho_{P \to P'}\bigl(\sum_\sigma c_\sigma [\sigma]\bigr) \;=\; \sum_{\sigma \in L(P')} c_\sigma [\sigma].$$

This is a surjective linear map (since `L(P')` is a strict subset for `P' > P`).

**Sheaf properties.** `F_{cut}` is a presheaf on `PPF_n^{op}` with the Alexandrov topology; it is automatically a sheaf (§1.2). It is `S_n`-equivariant: for `g \in S_n`, `g \cdot F_{cut}(P) = F_{cut}(g \cdot P) = \mathbb{Q}^{L(g \cdot P)} = \mathbb{Q}^{g \cdot L(P)} = g \cdot \mathbb{Q}^{L(P)}`.

**Cohomology.** `H^k(PPF_n, F_{cut})` is computable via the Mitchell cochain complex `C^k(PPF_n, F_{cut}) = \prod_{P_0 < \cdots < P_k} F_{cut}(P_0)`. Each cochain entry is `\mathbb{Q}^{L(P_0)}`, restrictable to `\mathbb{Q}^{L(P_{0,i})}` via the (P_0 \to P_{0,i})-direction.

This is the **natural** candidate for "BK-spectral data of subposets" — it carries the BK-vertex-set information at each `P`, with restrictions matching the induced-subgraph structure.

**Honest issue (anticipating §5).** `F_{cut}(P)` has non-constant rank: `|L(P)|` varies from `1` (total orders) to `n!/c_P` (`c_P` = chamber-stabiliser size) across `P`. The cohomology of `F_{cut}` is *not* `H^*(PPF_n, \underline{\mathbb{Q}})` — it has its own structure depending on the linear-extension counts and how restrictions identify chambers between different `P`'s. The F17+F18 constraint, which is at the level of constant-coefficient cohomology, does *not* apply to `F_{cut}` directly. This is the §5.2 wall.

**Operational status.** The sheaf is well-defined and computable per `n` (though enumeration is exponential in `n`). It encodes BK-vertex-set data, *not* BK-edge or BK-spectral-gap data — those would require additional sheaf structure on the bonds/edges, which is a strictly richer object (`F_{adj}` or `F_{Lap}` below).

### 3.2 Candidate (b) — `F_{Lap}`: Laplacian / Walsh data of `G_{BK}(P)`

**Definition.** `F_{Lap}(P) := \mathbb{Q}^{L(P)} \otimes \mathbb{Q}^{L(P)}` or, more refinedly, the symmetric algebra `\text{Sym}^{\le N}(\mathbb{Q}^{L(P)})` (with `N` cohomological degree control) — and equip with the BK Laplacian `\mathcal{L}_{BK}^{(P)} : \mathbb{Q}^{L(P)} \to \mathbb{Q}^{L(P)}` acting fibrewise.

The "spectral data" of `G_{BK}(P)` is encoded as the spectral decomposition of `\mathcal{L}_{BK}^{(P)}`: eigenvalues `0 = \lambda_0(P) < \lambda_1(P) \le \cdots \le \lambda_{|L(P)|-1}(P)`, eigenvectors `\psi_0(P), \ldots, \psi_{|L(P)|-1}(P) \in \mathbb{Q}^{L(P)}` (in the rational closure; over `\bar{\mathbb{Q}}` or `\mathbb{R}` if needed). The Walsh data of `G_{BK}(P)` is its Fourier-on-the-Cayley-graph spectral decomposition (when applicable to the BK-graph generator set).

**Restriction.** For `P \le P'`, `L(P') \subseteq L(P)` and `G_{BK}(P')` is an induced subgraph. The Laplacian `\mathcal{L}_{BK}^{(P')}` is the induced-subgraph Laplacian, *not* a restriction of `\mathcal{L}_{BK}^{(P)}` (induced-subgraph Laplacians lose the edges connecting `L(P')` to `L(P) \setminus L(P')`). So the restriction `F_{Lap}(P) \to F_{Lap}(P')` is:

$$\rho_{P \to P'}(\psi) = \text{restriction of }\psi\text{ to }L(P') \in \mathbb{Q}^{L(P')},$$

with the *new* (induced-subgraph) Laplacian acting on the target.

**Honest issue.** This restriction is *not* spectrum-preserving: the eigenvalues of `\mathcal{L}_{BK}^{(P)}|_{L(P') \times L(P')}` are generally *different* from those of `\mathcal{L}_{BK}^{(P')}`. So `F_{Lap}` is *not* a sheaf of `\mathcal{L}_{BK}`-eigenspaces — the eigenspace decomposition is *not* functorial under refinement.

This is a deep structural issue: refinement of `P` removes vertices and edges from `G_{BK}(P)`, and the induced-subgraph Laplacian is a non-trivial perturbation of the restriction. The spectral data is not Markov-functorial under induced-subgraph restriction. (This is essentially Cheeger-inequality-style content: cuts and spectra are related but not identically — restriction can dramatically alter spectra while leaving the vertex set unchanged.)

**Operational status.** `F_{Lap}` is well-defined as a vector-space-valued presheaf, but the *spectral content* — what makes it BK-spectral — is *not* functorial. The Walsh-data form has the same issue: the Walsh basis depends on the graph's edge set, which changes under restriction.

**Verdict (candidate (b)).** The sheaf is *not* a faithful encoding of BK-spectral data: refinement loses spectral information. F28's framework wants a sheaf whose stalks "encode BK-spectral data of `P` and its subposets" — but `F_{Lap}` only encodes vertex-set data, with the Laplacian being a *separate* operator at each `P` not assembled into a sheaf morphism. The Bubley–Karzanov mixing-time bound applies to each `G_{BK}(P)` individually but does not pull back to a constraint on the sheaf.

This is candidate (b)'s wall. The reading "Walsh / spectral data" was promising; the operational form is not.

### 3.3 Candidate (c) — `F_{Cheeger}`: chain-level Cheeger / conductance witness

**Definition.** `F_{Cheeger}(P) := \mathbb{Q}` (a 1-dim space) for each `P`, with the structure data being a *witness*: the choice of an optimal pair-cut `S^*(P) \subseteq L(P)` realising `\Phi(G_{BK}(P)) = \Phi(S^*(P))`, plus the conductance value `\Phi^*(P) := \Phi(S^*(P)) \in (0, 1]`.

This is a *constructible 1-dim sheaf with a function* — the cohomological content is in the function `\Phi^* : PPF_n \to (0, 1]`, not in the vector spaces.

**Restriction.** For `P \le P'`, the optimal cut `S^*(P) \subseteq L(P)` restricts to `S^*(P) \cap L(P') \subseteq L(P')`. This restriction is *not* in general an optimal cut for `G_{BK}(P')`: induced-subgraph Cheeger constants are not restrictions of larger-graph Cheeger constants.

**Honest issue (analogous to candidate (b)).** Cheeger is not functorial. `\Phi^*(P')` is generally not related to `\Phi^*(P) \cap L(P')`. The natural restriction map fails.

**A different angle — Theorem E witnesses.** Step 8's Theorem E states: a width-3 indecomposable γ-counterexample on `n` elements forces a *specific* pair-cut `S_{xy}` of `G_{BK}(P)` with explicit volume/boundary control. Define `F_{TE}(P) := \mathbb{Q}` with structure data = the existence-or-not of such a Theorem-E-witnessed cut at `P` (and if it exists, the witness data `(x, y, S_{xy})`).

This is a *predicate sheaf* — `F_{TE}(P) = \mathbb{Q}` if `P` is a γ-counterexample, else `0`. As a sheaf, this is a *constructible* sheaf supported on the locus of γ-counterexamples in `PPF_n`.

**Operational status.** This is closer to what Daniel's outline wants — a sheaf detecting the non-uniform (low-conductance) configurations. But:

- The locus of γ-counterexamples is *not* described by `PPF_n` order-structure alone: γ is an extrinsic parameter, and the locus depends on which `P`'s happen to admit a γ-counterexample (a property of the *whole* width-3 family, not of `P` alone).
- The cohomology of a constructible sheaf supported on a single locus has *no* general relation to F17+F18's constant-sheaf cohomology of `\Delta_n`. The connecting map would have to factor through a specific exact sequence relating `F_{TE}` and `\underline{\mathbb{Q}}` — and no such exact sequence is canonical.

**Verdict (candidate (c)).** The Cheeger / Theorem-E-witness sheaf is the closest categorical reading of Daniel's "detect non-uniform pieces" idea, but the support is *extrinsic* (depends on γ) and the connection to F17+F18 is not canonical. Without an explicit comparison sheaf morphism, F17+F18 does not constrain `H^*(PPF_n, F_{TE})`.

### 3.4 Candidate (d) — `F_{obs}`: sub-sheaf of an obstruction sheaf detecting low-conductance configurations

This is the most abstract candidate. It postulates a *short exact sequence* of sheaves on `PPF_n`:

$$0 \to F_{low} \to F_{tot} \to F_{unif} \to 0,$$

where:

- `F_{tot}` = the "total" BK-spectral-data sheaf (e.g., `F_{Lap}` or a derived variant).
- `F_{unif}` = the "uniform-expander" sub-sheaf: at each `P`, the part of `F_{tot}(P)` corresponding to the *uniform* spectral regime (e.g., the subspace where `\lambda_1(\mathcal{L}_{BK}^{(P)}) \ge \lambda_{thresh}`).
- `F_{low}` = the "low-conductance" cokernel sheaf: at each `P`, the part of `F_{tot}(P)` *not* in the uniform regime.

The Bockstein / connecting map `\delta : H^k(PPF_n, F_{unif}) \to H^{k+1}(PPF_n, F_{low})` is the **obstruction**: a uniform spectral configuration globally exists iff `\delta` is the zero map; a low-conductance configuration somewhere is an obstruction class `\delta(c) \ne 0`.

**Honest issue.** This formulation is *abstract*. To operationalise it, we need:

(i) A precise definition of `F_{tot}`, `F_{unif}`, `F_{low}` as sheaves of vector spaces with functorial restriction maps. Candidate (b)'s `F_{Lap}` already failed functoriality of spectral content; the same issue propagates to (d).

(ii) A definition of "uniform spectral regime" that is *functorial under refinement* — but spectra are not functorial (§3.2), so the subspace `F_{unif}(P) \subset F_{tot}(P)` does not have well-defined behavior under restriction. The short exact sequence does not make sheaf-theoretic sense as stated.

(iii) Even if (i) and (ii) are resolved (e.g., by restricting to a sub-category where spectra are nice), the connection to F17+F18 — which constrains `H^*(PPF_n, \underline{\mathbb{Q}})` — requires `F_{tot}, F_{unif}, F_{low}` to relate to `\underline{\mathbb{Q}}` via canonical maps. This is the §5 problem.

**Operational status.** Candidate (d) is a *target structure* — the kind of exact sequence one would *like* to write down. The pieces are not in hand. F28 cannot produce them in a scoping pass; this is a research project of unknown size (mg-26fc §4.4 U3 in spirit).

### 3.5 Summary of §3 — none of the candidate sheaves operationalises BK-spectral content functorially

| candidate | what it would encode | functoriality of BK content | sheaf well-defined? | connection to F17+F18 |
|---|---|---|---|---|
| (a) `F_{cut}` | vertex sets `L(P)` | yes (induced restriction) | yes | not direct: stalks vary in dimension |
| (b) `F_{Lap}` | Laplacian spectra | **no** (induced-subgraph spectra ≠ restrictions) | partial (vector spaces ok; spectra not) | none |
| (c) `F_{Cheeger}/F_{TE}` | optimal-cut conductance / Theorem-E witnesses | **no** (Cheeger not functorial) | partial (constructible, not canonical) | none canonical |
| (d) `F_{obs}` | abstract obstruction in SES | **no** (depends on (b)/(c) being functorial) | not in hand | none in hand |

**The fundamental issue is functoriality of BK-spectral content under refinement.** Refinement of `P` corresponds to *induced-subgraph restriction* on the BK side, which is not spectrum-preserving, not Cheeger-preserving, not expansion-preserving. So a sheaf encoding *spectral / cut content* of `G_{BK}(P)` does not have natural restriction maps that preserve this content.

The *vertex-set* sheaf `F_{cut}` (a) is the only one that is functorial under refinement, but it carries only vertex-set data — *not* the spectral / cut / expansion content that Daniel's intuition wants. So F28 has two regimes:

- **Functorial sheaves** (e.g., `F_{cut}`) — well-defined, but encode only vertex-set data, *not* the BK-spectral / cut content.
- **Non-functorial pretend-sheaves** (e.g., `F_{Lap}`, `F_{Cheeger}`) — encode the right content but are not sheaves (restriction maps don't preserve content).

This is the **first wall** of the F28 framework: there is no candidate sheaf on `PPF_n` that is both (i) genuinely a sheaf (functorial under refinement) and (ii) carries BK-spectral / cut / expansion content. Refinement of `P` and BK-spectral content of `G_{BK}(P)` are *opposite-direction* invariants in a precise sense — refinement *destroys* BK-graph structure (vertices and edges removed), and spectral content of the destroyed graph is not a function of the surviving graph.

§5 sharpens this into the F17+F18-constraint-mechanism analysis.

---

## §4. The cohomological invariant — which cohomology theory

For each candidate sheaf in §3, the cohomology theory is the Alexandrov / Mitchell cohomology of `PPF_n` (§1.2–§1.3), which equals constructible-coefficient cohomology of `\Delta_n`. We make four sub-choices precise here.

### 4.1 Mitchell cohomology of the small category `PPF_n`

For `F : PPF_n^{op} \to \text{Vec}_\mathbb{Q}` a functor (= presheaf = sheaf in Alexandrov topology):

$$H^k(PPF_n, F) \;:=\; H^k\bigl(\text{Tot}\, C^\bullet\bigr), \quad C^k = \prod_{P_0 < P_1 < \cdots < P_k} F(P_0),$$

with `(d^k c)_{P_0 < \cdots < P_{k+1}} = \sum_i (-1)^i \rho_{P_0 \to P_{0,i}}(c_{P_0 < \cdots < \widehat{P_i} < \cdots})` and the convention that `\rho_{P_0 \to P_0} = \text{id}`.

For `F = \underline{\mathbb{Q}}`: `H^k(PPF_n, \underline{\mathbb{Q}}) = H^k(|\Delta_n|; \mathbb{Q})` by Mitchell (1972), which by F17+F18 is `sgn_{S_n}` in degree `n−2`, else `0` (in degree `\ge 1`).

For `F = F_{cut}` (candidate (a)): `H^k(PPF_n, F_{cut})` is *not* `H^k(\Delta_n; \mathbb{Q})` — the non-constant stalks alter the cochain complex.

For `F = F_{Lap}` (candidate (b)) etc., `F` is not even a presheaf in the strict sense (spectral content not functorial), so Mitchell cohomology is not directly defined.

### 4.2 Hypercohomology — a complex of sheaves

For a *complex* of sheaves `F^\bullet : \cdots \to F^{-1} \to F^0 \to F^1 \to \cdots`, the hypercohomology `\mathbb{H}^k(PPF_n, F^\bullet)` is the cohomology of the Cech-totalisation. For F28, a candidate complex is:

$$F^\bullet : \quad 0 \to F_{low} \to F_{tot} \to F_{unif} \to 0,$$

with `F^\bullet` placed in degrees `−1, 0, 1` (or similar). The hypercohomology

$$\mathbb{H}^k(PPF_n, F^\bullet) = H^k(\text{Tot}\, C^\bullet_{F^\bullet})$$

has a spectral sequence `E_1^{p,q} = H^q(PPF_n, F^p) \Rightarrow \mathbb{H}^{p+q}(PPF_n, F^\bullet)` (Hartshorne III.7).

**Operational status.** Hypercohomology is the right machinery *if* the complex of sheaves is in hand. For F28, it is the *target* form of the candidate (d) SES — but the sheaves themselves are not in hand. Hypercohomology is a useful *language* but not yet an operational tool.

### 4.3 Derived sections — `R\Gamma`

`R\Gamma(PPF_n, F) := R\text{Hom}_{\text{Sh}}(\underline{\mathbb{Q}}, F)` — the derived functor of global sections. For a sheaf `F`, `R^i\Gamma(F) = H^i(PPF_n, F)` (Mitchell, Alexandrov-topology agreement). For a complex `F^\bullet`, `R\Gamma(F^\bullet)` is the hypercohomology object in `D^b(\text{Vec}_\mathbb{Q})`.

**Operational status.** Derived-section language is conceptually clean; computationally equivalent to Mitchell cohomology for sheaves. No additional content for F28 beyond §4.1.

### 4.4 Comparison with the (T3) chamber-cover topology

The mg-d60d scoping used the (T3) linear-extension-restriction topology, not the Alexandrov topology (mg-d60d §1.1). For F28's candidate sheaves, the (T3) topology has *strictly stronger* sheaf conditions, requiring agreement at chamber covers. This pins more cocycles than Alexandrov.

For the BK-derived sheaves §3.1–§3.4, the (T3) sheaf condition would require:

- `F_{cut}(P) \xrightarrow{\cong} \lim_{\sigma \in L(P)} F_{cut}(P_\sigma)`, where `P_\sigma` is the chamber σ viewed as a total-order refinement of `P`. For `F_{cut}(P) = \mathbb{Q}^{L(P)}` and `F_{cut}(P_\sigma) = \mathbb{Q}` (1-dim), the limit is `\mathbb{Q}^{L(P)}` (product over `L(P)`). The isomorphism `F_{cut}(P) \to \prod_\sigma \mathbb{Q}` is the obvious projection; *holds*. So `F_{cut}` is a (T3)-sheaf.

- `F_{Lap}(P)` etc. fail (T3) since the spectral content is not chamber-determined.

So the (T3) topology *also* admits `F_{cut}` but excludes the non-functorial pretend-sheaves. For F28's purposes the (T3) and Alexandrov topologies give the same operational picture; we use Alexandrov for convenience (every presheaf is automatically a sheaf).

### 4.5 Commitment — Mitchell / Alexandrov cohomology

We commit to **Mitchell cohomology of `PPF_n` in the Alexandrov topology** as the F28 cohomology theory. For candidate (a) `F_{cut}`, this is well-defined; for (b)–(d) it is well-defined only if the sheaf structure is in hand (which it is not for (b)–(d)). The F17+F18 input lands in this theory unconditionally at the constant-sheaf level.

The cohomology degree of interest is `k = n − 2`: the F17+F18 sgn-isotype concentration degree.

---

## §5. The F17+F18 constraint mechanism — three candidate operationalisations

This is the load-bearing section of F28. The framework wants F17+F18 to constrain `H^k(PPF_n, F)` for some BK-derived `F`, in a way that lets us forbid global low-conductance configurations.

Three candidate mechanisms exist; each is walked.

### 5.1 Constraint mechanism 1 — global-sections / `\Gamma(F) = \mathbb{Q}^{sgn}` form

**The statement.** A sheaf `F` on `PPF_n` with `\Gamma(PPF_n, F) = \mathbb{Q}^{sgn}` (= `sgn_{S_n}`-isotype of global sections) inherits from F17+F18 the conclusion: any cocycle representative for `\omega_{bal}^{(n)}` lifts to a global section of `F`, and the BK data carried by `F`'s stalks gets "constrained" to satisfy the sgn-isotype condition at the global-sections level.

**Operational form.** For `F = F_{cut}` (candidate (a)), `\Gamma(PPF_n, F_{cut}) = \lim_{P} F_{cut}(P)` = the limit over all `P` of `\mathbb{Q}^{L(P)}`. By the *induced-restriction* structure (restriction `F_{cut}(P) \to F_{cut}(P')` is restriction to a sub-vertex-set), the limit picks out functions `c : L(?) \to \mathbb{Q}` defined coherently across all `P` — which collapses to a single function on the *intersection* `\bigcap_P L(P) = L(\text{top total orders})`. But `L(\text{a total order}) = \{\sigma\}` for that single `\sigma`. The limit is therefore the vector space of constant-on-each-`\{σ\}` functions, which is `\prod_\sigma \mathbb{Q} = \mathbb{Q}^{n!}` (one factor per total order in `PPF_n^{top}`)... actually, the limit depends on the direction of the cone. For the Alexandrov limit over `P \to P'` with `P \le P'`, restrictions go in the `\rho_{P \to P'}` direction; the limit is the inverse limit over the *down-cone* {P ≤ P'} for fixed `P`. Since `PPF_n` is connected and finite, this limit is something concrete.

Concretely: in the Alexandrov topology, `\Gamma(PPF_n, F) = \lim_{P \in PPF_n} F(P)` (limit over `PPF_n` viewed as a category). For `F_{cut}(P) = \mathbb{Q}^{L(P)}` with surjective restrictions, the limit is a sub-space of `F_{cut}(P_{\min})` for any minimal `P_{\min}` — concretely, the limit is `\mathbb{Q}^{S_n}` (the full symmetric group, when `P_{\min}` is at the bottom — but `PPF_n` excludes `\hat 0`, so the "minimal" elements of `PPF_n` are 1-relation posets, each with `L = (n-1)!/(n-2)! = n − 1` extensions... wait this is getting confused).

Let me redo this carefully. `PPF_n` is the poset of proper partial orders: non-empty, non-total. Its *minimum* elements (in refinement order, so the *least refined* — fewest relations) are the partial orders with a single non-trivial relation, e.g. `\{a < b\}` for some pair. Its *maximum* elements (most refined while non-total) are the partial orders one cover relation short of being total — "near-total" orders.

The Alexandrov topology has *opens = up-closed* (under refinement). Sheaf restrictions go from `\downarrow$-larger to `\uparrow$-larger$ — for `P \le P'` in refinement (`P'` more refined), the sheaf map `F(P) \to F(P')` corresponds to restricting attention to a more refined poset (= smaller chamber set). For `F_{cut}`, this is the restriction `\mathbb{Q}^{L(P)} \to \mathbb{Q}^{L(P')}`, projecting to the sub-vertex-set.

The limit `\lim_{P \in PPF_n} F_{cut}(P)` is therefore the *inverse limit* under these surjections. For the Alexandrov topology on a finite poset, the inverse limit is computed at the *minimum* (or here, the join of all minima = the bottom of the connected component). `PPF_n` is connected: every `P` is refinement-comparable to a 1-relation poset, which in turn is comparable to its own refinements. The minimum of `PPF_n` would be the antichain `\hat 0` — but `\hat 0 \notin PPF_n` (we excluded it). So `PPF_n` has *multiple* minimal elements (the 1-relation posets, one per ordered pair `(a, b) \in [n]^2`).

For a connected category with multiple minima, the limit picks out the *intersection* of stalks restricted from each component. For `F_{cut}` over `PPF_n`, the global sections are functions on the *common* vertex set across all `P` — which is the empty set (different `P`'s have entirely different `L(P)`'s; e.g., `L(\{0 < 1\}) \cap L(\{1 < 0\}) = \emptyset` since linear extensions of `\{0 < 1\}` have 0 before 1, vs. the opposite).

Conclusion: `\Gamma(PPF_n, F_{cut}) = 0` (no global sections except the zero function, since restrictions are inconsistent at the multi-minima level).

**So F17+F18 via global sections does not constrain `F_{cut}` non-trivially.** The cohomological constraint operates at higher degree (`k = n − 2`), not at `\Gamma`.

**At degree `n − 2`.** The cohomology `H^{n-2}(PPF_n, F_{cut})` is a non-trivial vector space depending on the cocycle structure. F17+F18 give the *constant-coefficient* `H^{n-2}(PPF_n, \underline{\mathbb{Q}}) = sgn`. The relationship between `H^{n-2}(F_{cut})` and `H^{n-2}(\underline{\mathbb{Q}})` is governed by sheaf maps.

The *augmentation* sheaf map `\epsilon : F_{cut} \to \underline{\mathbb{Q}}, c \mapsto \sum_\sigma c_\sigma` is *not* a map of presheaves: it does not commute with restriction. Under `\rho_{P \to P'}` (restriction to sub-vertex-set), `\epsilon(\rho(c)) = \sum_{\sigma \in L(P')} c_\sigma \ne \sum_{\sigma \in L(P)} c_\sigma = \epsilon(c)`. So the natural augmentation is *not* a sheaf morphism `F_{cut} \to \underline{\mathbb{Q}}`.

A *different* candidate sheaf morphism: `\phi(c) := \frac{1}{|L(P)|} \sum_\sigma c_\sigma` (the average). This *also* fails to commute with restriction: `\phi(\rho(c)) = \frac{1}{|L(P')|} \sum_{σ \in L(P')} c_\sigma \ne \frac{1}{|L(P)|} \sum_{σ \in L(P)} c_\sigma`. Not a sheaf morphism either.

**A weighted form.** Multiply by `|L(P)|`: `\psi(c) := \sum_\sigma c_\sigma`. Restriction:

$$\psi(\rho_{P \to P'}(c)) = \sum_{\sigma \in L(P')} c_\sigma \ne \psi(c) = \sum_{\sigma \in L(P)} c_\sigma.$$

Still fails.

**The fundamental issue.** There is no canonical sheaf morphism `F_{cut} \to \underline{\mathbb{Q}}` because the natural reduction (sum-over-vertices) is not preserved under sub-vertex-set restriction. So F17+F18's constraint on `H^{n-2}(\underline{\mathbb{Q}}, PPF_n)` does *not* pull back to a constraint on `H^{n-2}(F_{cut})`.

**Verdict (constraint mechanism 1).** F17+F18 *does* constrain `H^{n-2}(PPF_n, \underline{\mathbb{Q}})` unconditionally, but the sheaf `F_{cut}` does *not* admit a canonical morphism to `\underline{\mathbb{Q}}`. Higher candidates (`F_{Lap}`, `F_{Cheeger}`, `F_{obs}`) are even less functorial. So the constraint mechanism *via* `\underline{\mathbb{Q}}` does not directly work on the BK-derived sheaves.

The exception is mg-d60d's `F_\ell`: this *is* canonically `\cong \underline{\mathbb{Q}}` via `\beta_P = |L(P)| \cdot \alpha_P`. But `F_\ell(P) = \mathbb{Q}` (a 1-dim space encoding the *count* `|L(P)|`), not BK-graph data. F17+F18 fully constrains `H^*(PPF_n, F_\ell) = H^*(PPF_n, \underline{\mathbb{Q}})`, and the operational content is the *cocycle-level* statement `\langle \omega_{bal}, c \rangle = \prod_i \Pr_{P_i}[a_i < b_i]` — which is the F-series ICOP target.

**Constraint mechanism 1 is operational for `F_\ell`, not for `F_{cut}` / `F_{Lap}` / `F_{Cheeger}` / `F_{obs}`. And the operational content for `F_\ell` is the *existing F-series program*, not a new BK constraint.**

### 5.2 Constraint mechanism 2 — hypercohomology limit / spectral sequence

**The statement.** Even if no canonical sheaf morphism `F \to \underline{\mathbb{Q}}` exists, a *complex* of sheaves `F^\bullet` with `F^0 = F` and other entries chosen carefully might have hypercohomology `\mathbb{H}^*(PPF_n, F^\bullet)` constrained by F17+F18 via a spectral sequence.

**Operational form.** The Cech-totalisation spectral sequence: `E_1^{p,q} = H^q(PPF_n, F^p) \Rightarrow \mathbb{H}^{p+q}(PPF_n, F^\bullet)`. If `F^\bullet` has *some* term `F^p \cong \underline{\mathbb{Q}}` (or a `sgn`-isotype twist of it), F17+F18 controls `E_1^{p, n-2}` for that `p`, and the spectral sequence's `E_\infty` page yields a constraint on `\mathbb{H}^*`.

**Where this would help.** If we can write a short exact sequence

$$0 \to F_{BK} \to F_{tot} \to F_\ell \to 0,$$

with `F_\ell \cong \underline{\mathbb{Q}}` (mg-d60d §2.4), the long exact sequence gives

$$\cdots \to H^{n-2}(PPF_n, F_{BK}) \to H^{n-2}(PPF_n, F_{tot}) \to H^{n-2}(PPF_n, F_\ell) \xrightarrow{\delta} H^{n-1}(PPF_n, F_{BK}) \to \cdots$$

F17+F18 give `H^{n-2}(PPF_n, F_\ell) = sgn`. The connecting `\delta` is the obstruction; non-trivial `H^{n-1}(F_{BK})` would lift constraint to the BK side.

**The fatal issue.** Defining `F_{tot}` and the map `F_{tot} \to F_\ell` requires a *canonical* relation between a BK-graph-data sheaf and the linear-extension-count sheaf. The natural map `F_{cut} \to F_\ell` would be summation (or weighted summation), but neither commutes with restriction (§5.1). So the SES doesn't exist at the level of sheaves.

A *derived* SES would require deriving `F_{cut} \to F_\ell` to a derived-category morphism `F_{cut} \to F_\ell` in `D^b(\text{Sh}(PPF_n))` — which exists abstractly (everything has a derived map) but is *trivial* unless we identify the specific derived enhancement. This identification is the mg-26fc §4.4 U1-flavoured missing ingredient — a per-`P` derived comparison.

**Verdict (constraint mechanism 2).** Hypercohomology / spectral sequence is the correct abstract machinery if the sheaf-theoretic comparison map existed; it does not, so the machinery is *unactivated*. Same wall as mechanism 1.

### 5.3 Constraint mechanism 3 — representability / Yoneda

**The statement.** `H^k(PPF_n, F)` represents (when `F` is constructible) homotopy classes of maps `\Delta_n \to K(F, k)` (Eilenberg–MacLane-style). F17+F18's unconditional content for `\underline{\mathbb{Q}}` makes `H^{n-2}(\Delta_n, \mathbb{Q}) = sgn` a *representability fact*. If `F_{BK}` is "co-represented" or "Yoneda-related" to `\underline{\mathbb{Q}}` via an explicit construction (an *evaluation* map `F_{BK}(P) \to \mathbb{Q}` that is sheaf-functorial), the same representability could constrain `F_{BK}`.

**Operational form.** This is the most abstract candidate. Concretely it requires a *natural transformation* `F_{BK} \Rightarrow \underline{\mathbb{Q}}` (= a sheaf morphism). §5.1 showed the candidates fail.

A *weakening*: a natural transformation between sheaf cohomology *functors*, induced by Yoneda. This requires `F_{BK}` and `\underline{\mathbb{Q}}` to be related by a functor in `\text{Sh}(PPF_n)`-mod or higher-categorical structure. Not in hand.

**Verdict (constraint mechanism 3).** Representability is the right framework if Yoneda or a derived equivalent applies; it does not, so this mechanism is *unactivated*. Same wall.

### 5.4 Summary of §5 — F17+F18 lands on the constant-coefficient side, does not directly cross to BK

The three candidate constraint mechanisms all fail for the *same* reason in the non-trivial cases: there is no canonical sheaf morphism (or derived analog) between a BK-graph-data sheaf and the linear-extension-count / constant sheaf. F17+F18's unconditional control of `H^*(PPF_n, \underline{\mathbb{Q}})` is *real* — but the BK-side sheaves don't admit the maps that would translate this control.

The one regime where F17+F18 fully lands is `F_\ell \cong \underline{\mathbb{Q}}` (the canonical trivialisation of mg-d60d §2.4). In this regime:

- F17+F18 unconditionally controls `H^{n-2}(PPF_n, F_\ell) = sgn_{S_n}`.
- `\omega_{bal}^{(n)}` is the canonical class, *unconditional*.
- The operational content is the cocycle pairing `\langle \omega_{bal}, c \rangle = \prod_i \Pr_{P_i}[a_i < b_i]` for `(n-2)`-chains `c` in `PPF_n`.
- This is the F-series ICOP target — non-vanishing of `\omega_{bal}` along the canonical critical chain `c^*_n`, equivalently per-step Pr's bounded away from 0 along `c^*_n`.

**This is the same target as F10 part (iii), in categorical dialect.** F28's framework gives a clean *home* for this target — `H^{n-2}(PPF_n, F_\ell)^{sgn}` with `\omega_{bal}` the canonical generator — but does *not* close the target. The width-3 bridge (= the non-vanishing of `\omega_{bal}` along *every* width-3 `P`'s associated critical chain) is the F10 §7.4 open piece, *same wall as before*.

§7 unfolds this into the AMBER verdict.

---

## §6. Locality-uniform → globality-non-uniform — precise formalisation

Daniel's intuition §5: locally uniform (subposet expander-y) + global non-uniform (low-conductance cut) implies a non-trivial cohomology class. We attempt to formalise.

### 6.1 The candidate theorem statement (in the operational regime)

In the regime where the framework operationalises — i.e., `F = F_\ell \cong \underline{\mathbb{Q}}` — the locality-to-globality argument formalises as follows.

**Definition (local uniformity at `P`).** A poset `P \in PPF_n` is *locally uniform* if `\Pr_P[a <_P b] \in [3/11, 8/11]` for *some* incomparable pair `(a, b)`. (This is the Brightwell–Felsner–Trotter F-series local target.)

**Definition (chain uniformity at `(n-2)`-chain `c`).** A chain `c = (P_0 < P_1 < \cdots < P_{n-2})` in `PPF_n` is *uniform along `c`* if for the cover relation `(a_i, b_i)` added at step `i`, `\Pr_{P_i}[a_i <_{P_i} b_i] \in [3/11, 8/11]` for every `i`.

**Theorem (the F28 candidate, conditional).** *Let `P \in PPF_n` be a width-3 indecomposable poset with a `(n−2)`-chain `c` through `P` (i.e., `P` appearing as a vertex of `c`). Then chain-uniformity of `c` ⟺ non-vanishing of `\langle \omega_{bal}^{(n)}, c \rangle`. The non-vanishing is unconditional (F17+F18) for the canonical critical chain `c^*_n`; globalising to every width-3 `P`'s associated chain is the F10 §7.4 width-3 bridge.*

**This is the operational content of F28 in the operational regime.** It is the F10 width-3 bridge re-cast in categorical language.

### 6.2 What this is and is not

What it **is**:

- A precise statement of how *local uniformity* (per-step Pr bounded in `[3/11, 8/11]`) connects to *global non-trivial cohomology* (`\omega_{bal} \ne 0` along the chain) via the cocycle pairing formula.
- A categorically natural reading of Daniel's "stitching together locally uniform pieces" intuition: each step's Pr-being-balanced is a local datum, the chain's *product* is the global cocycle value, and non-vanishing of the product is forced if all local data are balanced.
- A statement that uses F17+F18 *unconditionally* (the non-vanishing of `\omega_{bal}` on `c^*_n`) and converts it to a local uniformity statement on `c^*_n`.

What it is **not**:

- A statement about BK-spectral data / cut conductances. The Pr's are *chamber-uniform-measure probabilities* — they relate to BK-stationary-measure quantities but are not BK-graph spectral quantities. (The BK-Cheeger constant `\Phi(G_{BK}(P))` is *not* the Pr-product; it's a different quantity, related to bandwidth / spectral gap of the BK chain.)
- A statement about a `(n - 2)`-chain `c` for arbitrary `P` — only for `c` *containing* `P` as a vertex and matching the canonical critical chain pattern. The chain through *every* width-3 `P` is the F10 §7.4 width-3 bridge, *open at general `n`*.
- A NEW handle on Theorem E's low-conductance pair-cut. F28's framework re-casts the F-series ICOP target as categorical cohomology but does not constrain Theorem E.

### 6.3 The non-operational regime — what Daniel's intuition seems to want

Daniel's full intuition wants:

(D-1) The sheaf `F` on `PPF_n` (or `\uparrow P` for some `P`) encoding BK-spectral / cut-conductance data of each subposet (refinement) of `P`.
(D-2) "Locally uniform" = every `G_{BK}(P')` for `P' \in \uparrow P` is expander-y.
(D-3) "Globally non-uniform" = at some `P' \in \uparrow P`, `G_{BK}(P')` has a low-conductance pair-cut.
(D-4) Non-trivial cohomology of `F` on `\uparrow P` ⟹ obstruction class detecting (D-3).
(D-5) F17+F18 (cohomology of `\Delta(\uparrow P) \subset \Delta_n`) constrains the obstruction.

§5 walled (D-1) + (D-2): no canonical sheaf `F` exists with BK-spectral content that is functorial under refinement and admits a canonical morphism to `\underline{\mathbb{Q}}`. So (D-4) is undefined.

(D-5) is well-defined for `F = \underline{\mathbb{Q}}` (F17+F18 controls `H^*(PPF_n, \underline{\mathbb{Q}})`), but in that regime (D-1)–(D-4) are not BK-coupled. The bridge between (D-5) and (D-1)–(D-4) is the missing piece.

**The locality-to-globality argument operationalises only in the constant-coefficient / weights-trivialised regime, which is the F-series ICOP target — not the BK-spectral regime Daniel's intuition asks for.**

### 6.4 A precise statement of the gap

> **F28 framework gap (the AMBER content).** *Define a sheaf `F : PPF_n^{op} \to \text{Vec}_\mathbb{Q}` and a sheaf morphism `\phi : F \to F_\ell` (where `F_\ell \cong \underline{\mathbb{Q}}`) such that:*
> (i) `F(P)` carries the BK-spectral / Cheeger / cut-data of `G_{BK}(P)` faithfully;
> (ii) `\phi` is sheaf-functorial (commutes with refinement-restriction);
> (iii) `\phi` induces a non-trivial map on cohomology `H^{n-2}(PPF_n, F) \to H^{n-2}(PPF_n, F_\ell) = sgn`;
> (iv) `\phi`'s kernel `K_\phi := \ker(\phi) \subset F` has cohomology controllable in terms of F17+F18-style invariants.

*Such a sheaf + morphism is the F28 framework's load-bearing piece. F28 does not produce it; the framework is operational only conditional on its existence.*

This is the gap. F29 (if it happens) would target this construction — but as §7.3 details, this is a research project of unknown size (same flavour as mg-26fc §4.4 U1), not a polecat-scoping target.

---

## §7. Operational viability assessment — why AMBER

### 7.1 What is well-defined as math

(W-1) **The site `PPF_n` with the Alexandrov topology** — well-defined; finite category; Mitchell cohomology applies (§1.2–§1.3).

(W-2) **The Mitchell / Baues–Wirsching cohomology `H^*(PPF_n, F)`** for any presheaf `F` — well-defined (§4.1).

(W-3) **F17+F18's unconditional content on `H^*(PPF_n, \underline{\mathbb{Q}})`** — well-defined and *unconditional*: H-Cox + sgn (§2.1, F18 §0.3).

(W-4) **The canonical obstruction class `\omega_{bal}^{(n)} \in H^{n-2}(PPF_n, \underline{\mathbb{Q}})^{sgn}`** — well-defined and unique up to scalar, *unconditional* (§2.2; F17+F18; mg-d60d §3.4 in cocycle form).

(W-5) **The candidate sheaf `F_{cut}` (cuts of `G_{BK}(P)`)** — well-defined as a sheaf on `PPF_n`; carries induced-subgraph vertex-set data; functorial under refinement (§3.1).

(W-6) **The cocycle interpretation of `\omega_{bal}^{(n)}`** as the per-step Pr-product `\prod_i \Pr_{P_i}[a_i <_{P_i} b_i]` along an `(n-2)`-chain — well-defined and matches the F-series ICOP machinery (§2.2 (P-5); mg-d60d §3.4).

(W-7) **The framework's distinction from F27's literal-comparison candidates** — well-defined: F28 is categorical / sheaf-theoretic on `PPF_n`, not a bridge between two pre-existing complexes (§0.2).

### 7.2 What is computable / provable from F17+F18

(C-1) **The constant-coefficient cohomology** `H^*(PPF_n, \underline{\mathbb{Q}})` is *fully computed*: H-Cox + sgn, unconditional (§2.1).

(C-2) **The constant-coefficient obstruction class** `\omega_{bal}^{(n)}` *exists* unconditionally, and its non-vanishing on `c^*_n` (the canonical critical chain) is unconditional (§2.2).

(C-3) **The cocycle formula** `\langle \omega_{bal}, c \rangle = \prod_i \Pr_{P_i}[a_i < b_i]` is *unconditional* on the cocycle representative (it's a calculation, not a theorem requiring F17+F18 input).

(C-4) **The locality-to-globality argument in the operational regime** — chain-uniformity ⟹ `\omega_{bal} \ne 0` on the chain — is *unconditional* on `c^*_n`, *conditional* on the width-3 bridge for arbitrary width-3 `P`'s chain (= F10 §7.4 open piece).

What is **not** computable from F17+F18:

(N-1) **The cohomology `H^*(PPF_n, F_{cut})`** of the cuts sheaf — depends on `F_{cut}`'s own structure, not the constant sheaf.

(N-2) **A canonical sheaf morphism `F_{cut} \to F_\ell` or `F_{cut} \to \underline{\mathbb{Q}}`** — does not exist, by §5.1.

(N-3) **A faithful BK-spectral sheaf** — does not exist, by §3.2–§3.4 (Laplacian / Cheeger non-functorial under refinement).

(N-4) **The F10 §7.4 width-3 bridge** — open at general `n` (F23's HPC-per-n verdict on Route A, F25 RED on Route B, F27 RED on the literal hybrid).

### 7.3 Is the framework genuinely constraining?

**For the constant-coefficient / weights-trivialised regime (W-3)–(W-4), yes — but it's the existing F-series target.**

The cohomology `H^{n-2}(PPF_n, \underline{\mathbb{Q}}) = sgn` *unconditionally*. The obstruction class `\omega_{bal}^{(n)}` *unconditionally* exists. Its cocycle pairing against `(n-2)`-chains is the per-step Pr-product. Non-vanishing of the pairing on the canonical critical chain is unconditional (F17+F18). The widening to *every* width-3 `P`'s chain is the F10 §7.4 width-3 bridge — *open at general `n`*.

F28 in this regime *re-casts* the F-series ICOP target in categorical language. It does **not** advance the target's closure — F17+F18's unconditional content was already F-series machinery; the categorical re-casting is a notational refinement, not a new lever.

**For the BK-spectral-data regime, no.**

The candidate sheaves (b) `F_{Lap}` / (c) `F_{Cheeger}` / (d) `F_{obs}` are not genuinely sheaves (functoriality failures, §3.2–§3.4). Even if patched to be sheaves on a sub-category, they don't admit canonical morphisms to `\underline{\mathbb{Q}}` (§5.1), so F17+F18 doesn't constrain them.

The candidate sheaf (a) `F_{cut}` is a genuine sheaf but only carries vertex-set data, not spectral / cut content; and doesn't admit a canonical morphism to `\underline{\mathbb{Q}}` either.

**The framework therefore operationalises in the constant-coefficient regime (where it re-casts the F-series program) but not in the BK-spectral regime (where it would add new content).** This is the AMBER state.

### 7.4 Why not GREEN

GREEN-program-viable would require the framework to *operationalise* in the BK-spectral regime — i.e., produce a sheaf `F` with BK-derived stalks, a sheaf morphism `\phi : F \to F_\ell`, and a non-trivial constraint from F17+F18 forcing balance on `H^*(F)`. None of these exist for any of the candidate sheaves (a)–(d).

GREEN-partial would require *substantial* progress on the sheaf choice with a named-and-prioritised continuation. F28 has substantial progress on the *cohomology degree* (`n - 2`) and the *obstruction class* (`\omega_{bal}^{(n)}`), but these are F17+F18 consequences, not F28 contributions. The *sheaf choice* itself — the load-bearing piece — is *not* substantially scoped (the candidate sheaves wall).

### 7.5 Why not RED

RED-program-doesnt-operationalize would require the entire framework to fail to land. F28's framework lands halfway: F17+F18 *does* unconditionally constrain `H^*(PPF_n, \underline{\mathbb{Q}})`, and *does* unconditionally produce `\omega_{bal}^{(n)}`. This is genuine operational content — it just re-casts the F-series program rather than adding a new BK-constraint.

The framework is **operational on one side, unclear on the other**. Hence AMBER-framework-unclear, not RED.

### 7.6 The precise AMBER content

**AMBER-framework-unclear.** The categorical / sheaf-cohomology framework on `PPF_n` is well-defined, has unconditional content from F17+F18 at the constant-sheaf level, and provides a clean categorical home for the F-series ICOP / `\omega_{bal}` machinery. But the specific BK-spectral sheaf + F17+F18-constraint combination that would let the framework forbid low-conductance configurations is *not* in hand: no candidate sheaf is both (i) functorial under refinement and (ii) admits a canonical morphism to `\underline{\mathbb{Q}}` that F17+F18 can constrain.

The framework's positive findings vs. mg-d60d:

- **(C1) of mg-d60d is closed** unconditionally by F17+F18 (the sphere-topology assumption for `\Delta(\overline{Pos_n^{sub}})` is now the H-Cox + sgn theorem). This is a strict positive: mg-d60d's AMBER-specialist *conditional on cat-mg-5ee2* is upgraded to AMBER *unconditional on cohomological side*.

- **The obstruction class `\omega_{bal}^{(n)}`** is now unconditional and isotype-pinned (sgn). mg-d60d §3.4 had it conditional on (C1).

The framework's negative findings — the precise gap:

- **No BK-derived sheaf `F` with sheaf morphism to `F_\ell \cong \underline{\mathbb{Q}}`** that is functorial under refinement. This is the *load-bearing missing piece* for translating F17+F18 into BK constraints.

- **The locality-uniform → globality-non-uniform argument** operationalises only as the F-series ICOP target re-casting; in the BK-spectral interpretation Daniel's intuition wants, it's undefined.

---

## §8. F29 scope or precise barrier — what comes after F28

F28's verdict (AMBER-framework-unclear) does not directly trigger a F29 sub-ticket in the same sense F23 → F24 → F25 → F27 were direct continuations. The framework's *load-bearing gap* (§7.6) is a research project of unknown size, not a polecat-attackable scoping pass.

### 8.1 Three candidate F29 directions, named for completeness

**F29-A — construct the sheaf morphism `F_{BK} \to F_\ell`.** Direct attack on the §7.6 gap. Specifically: find a sheaf `F_{BK}` on `PPF_n` whose stalks `F_{BK}(P)` encode BK-spectral / Cheeger / cut data of `G_{BK}(P)` *functorially under refinement* (i.e., with restriction maps `F_{BK}(P) \to F_{BK}(P')` for `P \le P'` that preserve the relevant content), and admits a sheaf morphism `\phi : F_{BK} \to F_\ell` whose induced map on cohomology is non-trivial. This is the categorical incarnation of mg-26fc §4.4 U1 (the per-`P` complex `K(P)` with BK-Garland data + comparison to `Δ(PPF_n)`). **Research project of unknown size; not polecat-scoping-attackable; matches F27's RED'd direction in a different dialect.**

**F29-B — links of `Δ_n` are rationally spherical.** Side question (§2.3): are the links `\text{lk}_{\Delta_n}(P)` rationally spherical of dimension `n - 2 - \text{rk}(P) - 1`? F17+F18 gives rational sphericity for `\Delta_n`; a link-level refinement would extend the F17+F18 unconditional content to up-sets `\uparrow P`, sharpening (§2.3) the framework's local-to-global content. **Polecat-attackable as a structural scoping pass; would refine F17+F18 to up-set / link level; does not address the §7.6 gap directly but provides more F17+F18-side machinery.**

**F29-C — formalise the constant-coefficient operational regime as the F-series ICOP target re-casting.** Make explicit, in categorical language, that `H^{n-2}(PPF_n, F_\ell) = sgn` with `\omega_{bal}` the canonical generator, and that the F10 §7.4 width-3 bridge IS the categorical width-3 bridge for `\omega_{bal}`-restriction to width-3 strata. **Polecat-attackable as a documentation pass; does not advance new mathematics but consolidates the framework as a structural home for the existing F-series program.**

None of F29-A / F29-B / F29-C closes the milestone-1 part-(iii) gap. F29-A is the program-genuine attack but is research-project-grade; F29-B and F29-C are structural-consolidation passes.

### 8.2 The precise barrier statement

> **The F28 barrier.** *F17+F18 unconditionally pin the cohomology of the small category `PPF_n` with constant `\mathbb{Q}`-coefficients: `H^k(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` in degree `k = n - 2`, else trivial (in degree `\ge 1`). The canonical obstruction class `\omega_{bal}^{(n)} \in H^{n-2}(PPF_n, \underline{\mathbb{Q}})^{sgn}` exists unconditionally and pairs with `(n-2)`-chains via the per-step Pr-product formula. F28's framework provides a clean categorical home for this F-series unconditional core.*
>
> *F28's framework does **not** operationalise the BK-spectral-data regime. The four candidate BK-derived sheaves on `PPF_n` (cuts, Laplacian / Walsh, Cheeger / Theorem-E-witness, obstruction-sub-sheaf) split into (i) genuinely functorial but content-impoverished (the vertex-set sheaf `F_{cut}`) and (ii) content-rich but non-functorial (the spectral / Cheeger sheaves). No candidate is both functorial under refinement and admits a canonical sheaf morphism to `F_\ell \cong \underline{\mathbb{Q}}`, so F17+F18 does not constrain any BK-derived sheaf cohomology.*
>
> *The barrier is structurally identical to mg-26fc §4.4 U1 — the missing per-`P` complex `K(P)` with BK-Garland data + comparison to `Δ_n` — re-cast in sheaf-theoretic dialect. F28 confirms this missing piece is the **same** load-bearing missing ingredient as F27 RED's, in a different mathematical setting (categorical / sheaf-theoretic rather than topological / complex-comparison).*

### 8.3 What F28 does NOT do — same as F27

F28 does **not** propose a F29 that closes milestone 1 part (iii). F28 does **not** refute the framework's potential — a future construction of `F_{BK}` + sheaf morphism (§7.6) is *not* refuted, only *unattested*. F28 does **not** touch the F-series cohomological core (parts (i)–(ii)) — those are *unconditional* post F17+F18 and untouched here. F28 does **not** propose alternative routes to part (iii) — the F23 §4–§5 HPC-per-n verdict on Route A, F25's structural barrier on Route B, and F27's mechanism-mismatch on the literal hybrid all stand.

**Operational consequence for milestone 1:** unchanged from F27 §6. All three documented internal routes (A / B / Hybrid-literal) walled in different ways; the F28 categorical-hybrid re-cast is AMBER-framework-unclear with a load-bearing missing piece identical to mg-26fc §4.4 U1. Milestone-1 redefinition remains the Daniel/PM-level decision (F27 §6.3 options 1–4).

---

## §9. What F28 establishes and does not establish

### 9.1 Establishes

(E-1) **The categorical / sheaf-cohomology framework on `PPF_n`** is well-defined and operational at the constant-coefficient level. Site, topology, cohomology theory, obstruction class — all in hand (§1, §2, §4).

(E-2) **F17+F18 unconditionally compute the constant-coefficient categorical cohomology**: `H^k(PPF_n, \underline{\mathbb{Q}}) = sgn_{S_n}` for `k = n - 2`, `0` for `1 \le k < n - 2` or `k > n - 2`, all `n \ge 3` (§2.1).

(E-3) **The canonical obstruction class `\omega_{bal}^{(n)}`** exists unconditionally as the unique-up-to-scalar generator of the sgn-isotype in degree `n − 2`, with explicit cocycle representative given by the per-step Pr-product formula (§2.2).

(E-4) **mg-d60d's (C1)** (sphere topology of `Δ(\overline{Pos_n^{sub}})`) is closed unconditionally by F17+F18 — strict positive vs. mg-d60d's AMBER-specialist-conditional verdict (§0.3).

(E-5) **The four candidate sheaves (a)–(d) of the ticket spec all wall**, each for a *different* concrete reason (vertex-set-only / spectra-not-functorial / Cheeger-not-functorial / not-in-hand). The fundamental issue is the **opposite-direction structural incompatibility** between refinement of `P` (destroys BK-graph structure) and BK-spectral content (depends on the destroyed structure) (§3.5).

(E-6) **The three candidate F17+F18 constraint mechanisms (global-sections, hypercohomology, representability)** all wall on the *same* missing piece: a canonical sheaf morphism between a BK-derived sheaf and the linear-extension-count / constant sheaf (§5.4).

(E-7) **The locality-uniform → globality-non-uniform argument** formalises in the constant-coefficient / weights-trivialised regime as the F-series ICOP target re-casting (§6.1); it does **not** formalise in the BK-spectral regime Daniel's intuition asks for (§6.3).

(E-8) **The F28 barrier — a missing sheaf-theoretic comparison map between a BK-stalk sheaf and the linear-extension-count sheaf** — is structurally identical to mg-26fc §4.4 U1, in a categorical / sheaf-theoretic dialect (§7.6, §8.2).

### 9.2 Does not establish

(N-1) **A future construction of `F_{BK}` + sheaf morphism is not refuted.** F28 establishes that *as currently formulated* the candidate sheaves don't operationalise, but a deep future construction (e.g., a per-`P` derived enhancement, a Coxeter-arrangement-style BK chamber complex with explicit refinement-functorial spectral data, or a Garland-style upgrade specific to `PPF_n`'s refinement geometry) could in principle thread the needle.

(N-2) **The categorical framework is not equivalent to mg-d60d's AMBER-specialist verdict.** F28 *upgrades* it: the (C1) conditional input is now closed unconditionally. The framework is genuinely more operational than in 2026-05-13. The remaining gap is the §7.6 sheaf-morphism gap, not the sphere-topology gap.

(N-3) **The F10 §7.4 width-3 bridge is not closed.** Same as before — the categorical re-casting (§6.1) does not advance this.

(N-4) **Route A's HPC-per-n and Route B's structural barrier are not addressed.** F28 is about a different route (categorical hybrid); the A/B verdicts stand (F23 §4–§5, F25 §3).

(N-5) **F27's mechanism-mismatch is not dissolved.** F28's framework is *distinct* from F27's literal-comparison-map approach but the *load-bearing missing piece* (a comparison between BK-derived and `F_\ell`-style sheaves) is the *same*; F28 confirms this in a different dialect.

(N-6) **The width-3 conjecture is not refuted.** Conjecture is open at general `n`, verified `n \le 6`. F28 is a scoping audit of one of three internal proof attacks (the categorical-hybrid attack), not an attack on the conjecture itself.

---

## §10. References

### 10.1 Predecessor F-series tickets

- **mg-a3e3** — F27 (the spectral → cohomology hybrid scoping, *literal*-comparison-map approach): **RED-mechanism-mismatch.** F28 is the **categorical / sheaf-theoretic** counterpart that F27 §6 / §7.2 flagged as a future direction. F27 §4 (the three walled candidates) is the bridge F28 distinguishes itself from.
- **mg-4d3a** — F17: **GREEN-equivariant-uniform.** F17 §0.2 (n-uniform reduction identity); §0.3 (UCC.1 ⟺ Hyp(n)). The unconditional input to F28's constant-coefficient cohomology.
- **mg-d039** — F18: **GREEN-ucc2-proven.** F18 §0.2 (null-homotopy theorem); §0.3 (UCC complete; F10 cohomological core unconditional). The other unconditional input.
- **mg-c6f2** — F25 (Hypothesis A constants audit): **RED-hypothesis-A-false-small-γ-tail.** F25 §3 (cubic γ-decay), §5.1 (`K_0(γ, w)` precisely located). Route B walled; F28 is one of three internal routes after F25-RED.
- **mg-531f** — F23: **GREEN-descent-pinned (HPC-per-n).** F23 §4–§5 (n-uniform discriminator refutation). Route A walled in HPC sense.
- **mg-26fc** — the two 1/3-2/3 mechanisms (structural-analogy scoping): **GREEN-distinct-complementary.** mg-26fc §4.4 (U1, U2, U3) — the three would-be bridges; F28's §7.6 / §8.2 gap is mg-26fc U1 in sheaf-theoretic dialect.

### 10.2 The mg-d60d / mg-5ee2 prior scoping

- **mg-d60d** — `docs/compatibility-geometry-poset-cohomology-scoping.md`: the original categorical / sheaf-cohomology scoping, 2026-05-13. **AMBER-specialist-conditional on cat-mg-5ee2.** F28's framework descends directly from mg-d60d; F17+F18 close mg-d60d's (C1) input, upgrading the AMBER to F28's AMBER-framework-unclear-without-conditional-input.
- **mg-5ee2** — `docs/compatibility-geometry-posn-sphere-scoping.md`: the sibling sphere-topology scoping for `Δ(\overline{Pos_n^{sub}})`. F17+F18's H-Cox + sgn theorem closes the rational-sphere statement unconditionally.
- **mg-296d** — `docs/compatibility-geometry-eigensheaves-scoping.md`: predecessor of mg-d60d, defining `F_\ell` (the linear-extension count line bundle) and its `\Delta_{(a,b)}`-eigensheaf structure with eigenvalue `1 - \Pr_P[a <_P b]`.

### 10.3 In-tree sources

- **`main.tex`** — §"Approach: Cheeger-type expansion on the BK graph" (Route B spine).
- **`step8.tex`** — Theorem E (Cheeger-conductance statement, unconditional); `lem:layered-reduction` (G3); `hyp:arith` (Hypothesis A).
- **`step1.tex`** — `G_{BK}(P)` definition.

### 10.4 F-series sources

- F18 §0.3 — F10 cohomological core (parts (i)–(ii)) UNCONDITIONAL.
- F17 §1.1 — the `(Q, F)` model of `A_n`.
- F25 §3.5 / §5.1 — `K_0(γ, w)` precisely located.
- F27 §4 — the three walled literal-comparison-map candidates.

### 10.5 Mathematical literature

- **Mitchell 1972** — *Rings with several objects*. The Mitchell cohomology of a small category.
- **Baues–Wirsching 1985** — *Cohomology of small categories*. The Baues–Wirsching dialect.
- **Quillen 1973** — *Higher algebraic K-theory I*. The nerve construction (§1).
- **Grothendieck 1957 (Tohoku)** — *Sur quelques points d'algèbre homologique*. Sheaf cohomology on a small category as right derived functors of `\Gamma`.
- **SGA 4** (Artin–Grothendieck–Verdier 1972) — *Théorie des topos et cohomologie étale des schémas*. Sheaf cohomology on a site; comparison theorems (Čech vs. derived).
- **Tamme 1994** — *Introduction to étale cohomology*. §I.3 — comparison of sheaf cohomology theories.
- **Bjorner–Wachs 2007** — *Combinatorial topology of poset complexes*. Poset cohomology / order complex cohomology.
- **Wachs 2007** — *Poset topology: tools and applications*. The order-complex cohomology survey.
- **Kashiwara–Schapira 1990** — *Sheaves on Manifolds*. Derived sheaf cohomology.
- **Lurie 2009** — *Higher Topos Theory*. Higher topoi (a more modern view).
- **Garland 1973** — `p-adic curvature and cohomology of discrete subgroups of p-adic groups`. The Garland meta-principle (mg-26fc §4.2).
- **Cheeger 1970** — discrete Cheeger inequality for reversible Markov chains.
- **Linial–Meshulam 2006** / **Meshulam–Wallach 2009** — coboundary expansion / higher expansion.
- **Bubley–Karzanov 1998** — BK Markov chain; spectral gap controls mixing.
- **Brightwell–Felsner–Trotter 1995** — the `[3/11, 8/11]` interval.
- **Kahn–Linial 1991** — unconditional `δ_{KL} = 0.276393…` bound.

### 10.6 Daniel directives

- **2026-05-15T19:59Z** — the intuition outline: *"If you take any subposet of bk graph it should be sort of uniform and nice, expander-y. But a low conductance cut is non-uniform. Ideally the cohomology of the category of posets should help us to stitch together these locally uniform pieces and show that something globally non uniform has a certain shape. Now here the cohomology is related to the poset and its subposets rather than the whole category but it should be well limited by what we proved already."*
- **2026-05-15T20:22Z** — *"Please start on the 1/3-2/3 cohomology program I outlined immediately. Union closed is lower priority and likely should emulate what we do here."* F28 implements this directive as a scoping pass.
- **2026-05-14T05:18Z** — finish internally; no external collaboration. (F28 is pure internal scoping.)
- **2026-05-15T09:06Z** — *"If a direct contradiction doesn't work perhaps you can go directly from spectral behavior → cohomology."* (Implemented by F27 as the literal-comparison version, RED'd. F28 implements the categorical-framework version, AMBER-framework-unclear'd.)

---

*Polecat: mg-d0fa (F28). Branch: `polecat-cat-mg-d0fa`. Verdict: **AMBER-framework-unclear** — the categorical / sheaf-cohomology framework on `PPF_n` is well-defined and operational at the constant-coefficient level (where F17+F18 unconditionally provide the H-Cox + sgn cohomology and the canonical obstruction class `\omega_{bal}^{(n)}`); the framework re-casts the F-series ICOP target as `\omega_{bal}` pairing against `(n-2)`-chains in `PPF_n`. The four candidate BK-derived sheaves on `PPF_n` (cuts, Laplacian, Cheeger, obstruction-sub-sheaf) all wall: either functorial-but-content-impoverished (the vertex-set sheaf `F_{cut}`) or content-rich-but-non-functorial (spectra and Cheeger not preserved under refinement-restriction). None admits a canonical sheaf morphism to `F_\ell \cong \underline{\mathbb{Q}}` that F17+F18 can constrain. The F28 barrier is structurally identical to mg-26fc §4.4 U1 — the missing per-`P` complex / sheaf-morphism comparison — re-cast in sheaf-theoretic dialect. F28 upgrades mg-d60d's AMBER-specialist-conditional verdict (the sphere-topology dependency is now closed by F17+F18) but does not dissolve the F27 RED — it relocates it to the sheaf-morphism gap. No new axioms; no Lean changes; no HPC; no computation. Cumulative state: `docs/state-F28.md`.*
