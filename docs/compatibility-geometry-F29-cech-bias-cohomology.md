# Compat-Geom — F29: Bad cut → Čech-bias cohomology class via local biases on subposets; can the class be sign-like? (mg-70b0)

**Branch:** `polecat-cat-mg-70b0` (mg-70b0).
**Parent.** Daniel two Apple-reminder messages, 2026-05-15T23:20Z and 2026-05-15T23:38Z, forwarded post-F28 AMBER. The reminders explicitly articulate the next direction after F28 (mg-d0fa) merged AMBER-framework-unclear with the U1-dialect collision. They are **not a framework search** — they pre-specify the mechanism: a bad cut decomposes into local biases on subposets that contradict in intersections, the contradictions assemble into a Čech-style cohomology class, F17+F18 say the only cohomology at the relevant degree is sign-like, and a bad cut's class cannot be sign-like ("sign is 100 % boundary, highly commuting; bad cut is the opposite").
**Chain:** F10 → F17 (mg-4d3a) → F18 (mg-d039) → F19–F23 chamber-Morse arc → F24 → F25 (**RED**) → F27 (**RED**) → F28 (mg-d0fa, **AMBER**) → **F29 (mg-70b0, this doc).**
**Type:** Structural research scoping (Čech / chain-level cohomology assembly on `PPF_n`). Paper-and-pencil, LaTeX-style Markdown; **no new axioms; no Lean changes; no HPC; no computation.** Multi-session-able; cumulative state ledger in `docs/state-F29.md`. Cross-repo read of `one_third_width_three` (`main.tex`, `step1.tex`–`step8.tex`) only when needed.
**Daniel directives:** 2026-05-14T05:18Z (finish internally; no external collaboration); 2026-05-15T23:20Z (*"agents seem to think I want something factorial in the new cohomology program and I dont. I want a bad cut, eg a bias, to be difficult to construct out of all the posets that can be patched together to form it. This inherently, but not functorially, relates to what we proved about Pos\_n cohomology. For instance if we show bad cut -> nonspherical cohomology we could be done."*); 2026-05-15T23:38Z (*"potentially more clarity in case it helps. The bad cut has a bias on each subposet, and this contradicts in intersections sometimes, which gives its cohomology class. Since from what I understand we proved the only cohomology is sign-like, we then show a bad cut cant be sign-like. Morally this is because sign is 100% boundary, highly commuting and the bad cut is the opposite."*). **Hard constraints (NON-NEGOTIABLE):** NOT factorial; inherently but NOT functorially related to `Pos_n` cohomology; paper-and-pencil/LaTeX-first; cumulative `state-F29.md`.

---

## Verdict: **AMBER-one-load-bearing-residual.**

The Daniel-articulated mechanism is operational at the bias-cochain → Čech-cocycle level (§2–§3): a bad cut on a width-3 γ-counterexample `P` gives rise, on the up-set `↑P ⊆ PPF_n`, to an `S_n`-action-aware cochain whose values are the local biases `b(P') := \Pr_{P'}[x <_{P'} y] - 1/2` of the bad pair `(x, y)` along each refinement `P' \in ↑P`, and whose Čech-style coboundary at intersections of bias-coherent subfamilies is *generically non-zero*. F17+F18 pin the only non-trivial constant-`Q` cohomology of `Δ_n = Δ(PPF_n)` to **`H^{n-2}(PPF_n, Q) = sgn_{S_n}`**, with `ω_{bal}^{(n)}` the unique-up-to-scalar generator. The Daniel "not-sign-like" step — "sign is 100 % boundary, highly commuting; bad cut is the opposite" — admits a precise reading (§5): the bad cut's `S_n`-orbit-data factors through the stabiliser `\mathrm{Stab}_{S_n}\{x, y\}`, not through full `S_n` with `sgn`-equivariance — and the orbit-aware Čech class therefore lives in an `S_n`-representation that *contains* `sgn_{S_n}` only as a sub-component, with strict additional content that cannot be in the `sgn`-isotype.

If the bad-cut Čech cocycle is built to land in **constant-`Q` cohomology** in degree `n - 2`, F17+F18 force the class into the `sgn`-isotype, and the not-sign-like step then reads as: the bad cut's Čech cocycle is *forced to be a coboundary* (i.e. assemble-able from purely local data), contradicting the bad cut's existence as a low-conductance configuration. This is the **GREEN-closes-part-(iii) shape** of the argument and would close milestone-1 part (iii) at general `n` if delivered unconditionally.

However (§5.4, §5.5): rendering "the bad-cut Čech cocycle has values incompatible with `sgn`-isotype as a cohomology class in `H^{n-2}(PPF_n, Q)`" rigorous requires an explicit, **non-functorial** chain-level comparison between the bad-cut cocycle representative `\psi_{\mathrm{BC}}^{(x,y)} \in C^{n-2}(PPF_n, Q)` and any chosen cocycle representative of `\omega_{bal}^{(n)}`. The natural map `\psi_{\mathrm{BC}}^{(x,y)} \mapsto \omega_{bal}^{(n)}` *is* exactly the cocycle assignment `c \mapsto \prod_i \Pr_{P_i}[a_i <_{P_i} b_i]` with `(a_i, b_i) = (x, y)` for the bad pair — and this is, formally, *a* cocycle representative of `\omega_{bal}^{(n)}` (the cohomology class is independent of cover-step choice, mg-d60d §3.4 + F28 §2.2). So **the bad-cut Čech cocycle, as currently defined, IS a cocycle representative of `\omega_{bal}^{(n)}`** — `[\psi_{\mathrm{BC}}^{(x,y)}] = c_{x, y} \cdot [\omega_{bal}^{(n)}]` in `H^{n-2}(PPF_n, Q)` for some scalar `c_{x, y}`, and is therefore *automatically* sign-like as a cohomology class. The argument that "bad cut → not sign-like" requires the Čech cocycle to carry **more data than its cohomology class** — i.e. it must be read as a *cochain* or as a *labelled* class (with `(x, y)` and orbit decoration) and the contradiction has to live in the cochain / labelled-class level, not at the bare-class level.

**Where that lands.** The Daniel "boundary / commuting" articulation maps onto a precise question (§5.5): is there a natural sheaf, twisted coefficient system, or labelled cochain complex `\widetilde C^*` on `PPF_n` where:
- (i) the bad-cut Čech cocycle gives a non-trivial cohomology class `[\widetilde\psi_{\mathrm{BC}}]`,
- (ii) F17+F18 (or a refined statement on `\widetilde C^*`) constrains the only possible non-trivial class to be `sgn`-like,
- (iii) and the labelled / orbit-aware structure of `[\widetilde\psi_{\mathrm{BC}}]` is provably *not* `sgn`-like?

(i)+(ii)+(iii) together would close part (iii). F29 gives a precise candidate `\widetilde C^*` (§4.2: the `(x, y)`-labelled Čech complex on the `S_n`-orbit cover of `↑P`), pins the bias-cocycle class living there (§4.3), and walks the not-sign-like step (§5). The walk is *plausible but load-bearing*: the bias-cocycle class on `\widetilde C^*` is not automatically constant-`Q`-cohomology-equivalent to a `sgn`-isotype class — the comparison map between the two complexes is itself the construction that has to land. This is the **one load-bearing residual** the AMBER verdict names.

**Why AMBER and not GREEN.** GREEN-closes-part-(iii) would require the labelled-Čech ⇄ constant-Q comparison to be in hand, with an explicit cochain-level non-`sgn`-equivariance witness for `[\widetilde\psi_{\mathrm{BC}}]`. The construction sketch in §4–§5 produces the right shape but does not produce the explicit comparison. The remaining work is structurally similar to mg-26fc U2 (a per-`P` quantitative bridge between the cohomological pairing and a cut conductance), and to F28 §7.6 (a sheaf-theoretic comparison between BK-derived and `F_\ell`-style sheaves), **in a more permissive setting** — F29 needs only a chain-level comparison, not a functor — so the residual is meaningfully *less* than F28's missing piece.

**Why AMBER and not RED.** RED would require either (i) the bias-cochain mechanism to fail to land any cohomology class (the Čech assembly is vacuous), or (ii) the not-sign-like step to be structurally impossible (e.g., the `S_n`-orbit structure forces the labelled class back into `sgn` automatically). Neither is the case: §3.3 shows the Čech 1-cocycle is generically non-zero on the bias-coherent cover, and §5.3 argues the stabiliser-`\mathrm{Stab}\{x, y\}`-equivariant cochain `\widetilde\psi_{\mathrm{BC}}` is not, *a priori*, forced into the global `sgn_{S_n}`-isotype. The mechanism is *plausible*; the operational delivery is *not in hand*.

**U1-dialect-collision check (§6).** The Daniel-articulated direction is materially different from F28 / mg-26fc U1 in three respects: (a) Daniel explicitly **rules out functoriality**, where F28's wall was the absence of a *functorial* sheaf morphism `F_{BK} \to F_\ell`; (b) the Čech-bias construction is **chain-level**, not sheaf-level, so the F28 candidate-sheaf functoriality failures (§3.2–§3.4) do not directly transpose; (c) the "not sign-like" target shifts the work from constructing a forward bridge (F28: `F_{BK} \to F_\ell`) to constructing a **backward obstruction witness** (F29: a labelled-Čech class incompatible with `sgn`-isotype) — formally easier in that *non-existence* of a `sgn`-equivariant resolution suffices. F29's *load-bearing residual* — the chain-level labelled-Čech ⇄ constant-Q comparison — **may or may not be a third dialect of U1**; §6.2 lays out the dissolve criterion (a chain-level comparison without a functorial bridge) and the collision criterion (the comparison forces, against Daniel's directive, an effective sheaf-morphism in disguise). On current evidence the dissolve criterion is met *structurally* (Daniel's "not functorially" is the explicit non-functorial mode), but *operationally* the chain-level comparison has not been written. **Conditional dissolve, pending operational delivery.** This is recorded as a feature of the AMBER verdict, not a third-dialect U1 hit.

**Operational consequence (§7).** F29 does not, in this scoping pass, close milestone-1 part (iii). It does:

- (a) Operationalise the Daniel-articulated mechanism precisely (§2–§5).
- (b) Identify the one load-bearing residual (the labelled-Čech ⇄ constant-Q chain-level comparison).
- (c) Surface the *structural* dissolve of the U1-collision in this dialect, conditional on operational delivery.
- (d) Name an F30 target (the chain-level labelled-Čech comparison; §7.1).

F29's mathematical positive vs. F28: the chain-level / non-functorial mode is, on inspection, the *right* mode for the bad-cut construction — F28's functorial-sheaf-morphism wall does not apply, and the Daniel directive that explicitly rules out functoriality is *not* a constraint on the construction but a re-direction *away* from the dialect that already walled. F28's AMBER-framework-unclear was a function-theoretic obstruction; F29's AMBER-one-load-bearing-residual is a chain-construction obstruction one degree of explicitness short of operational.

---

## §0. Setup — what "bad cut → Čech-bias cohomology class" means precisely

### 0.1 Daniel's reminders, verbatim

**2026-05-15T23:20Z** (reminder 1, the direction):

> *"agents seem to think I want something factorial in the new cohomology program and I dont. I want a bad cut, eg a bias, to be difficult to construct out of all the posets that can be patched together to form it. This inherently, but not functorially, relates to what we proved about Pos\_n cohomology. For instance if we show bad cut -> nonspherical cohomology we could be done."*

**2026-05-15T23:38Z** (reminder 2, the mechanism, ≈ 18 min later):

> *"potentially more clarity in case it helps. The bad cut has a bias on each subposet, and this contradicts in intersections sometimes, which gives its cohomology class. Since from what I understand we proved the only cohomology is sign-like, we then show a bad cut cant be sign-like. Morally this is because sign is 100% boundary, highly commuting and the bad cut is the opposite."*

These two reminders, taken together, articulate a five-piece program:

(D-1) **Bad cut as bias** (R1, R2). A bad cut = a bias = a low-conductance pair-cut on `G_{BK}(P)` for some width-3 γ-counterexample `P` — operationally, the existence of an incomparable pair `(x, y)` with `\Pr_P[x <_P y] \notin [3/11, 8/11]`.

(D-2) **Local-bias decomposition on subposets** (R2). The global bias is reconstructed from local biases on subposets (refinements of `P`); the local biases are *patched together* to form the global object.

(D-3) **Contradictions on intersections** (R2). The local biases sometimes contradict on intersections of subposets; the contradiction is the source of the *Čech-style cohomology class*.

(D-4) **Anchor to F17+F18** (R2). F17+F18 prove the only non-trivial cohomology of `\Delta(PPF_n)` at the relevant degree is sign-like (i.e. `sgn_{S_n}`-isotype in degree `n - 2`).

(D-5) **Not-sign-like step** (R2). The bad cut's Čech class is not sign-like, *because* sign is "100 % boundary, highly commuting" and the bad cut is the *opposite* (non-boundary / non-commuting).

The hard constraints (R1) — **not factorial; inherently but not functorially** — are *also* in scope, and they re-shape the construction (§0.3).

### 0.2 The F28 background, recapped

F28 (mg-d0fa, AMBER-framework-unclear) searched for the right framework: sheaf cohomology on **POSET** (the small category of posets and refinement morphisms), with stalks carrying BK-spectral / Cheeger / cut data. The framework operationalises at the **constant-coefficient level** (F17+F18 unconditional H-Cox + sgn theorem; `\omega_{bal}^{(n)}` the canonical obstruction class), but every BK-derived candidate sheaf walls — either *functorial-but-content-impoverished* (`F_{cut}`, vertex-set-only) or *content-rich-but-non-functorial* (`F_{Lap}`, `F_{Cheeger}`, `F_{TE}`). The F28 barrier (§7.6, §8.2):

> *No BK-derived sheaf `F_{BK}` on `PPF_n` is both functorial under refinement AND admits a canonical sheaf morphism `\phi : F_{BK} \to F_\ell \cong \underline{Q}` whose induced cohomology map F17+F18 can constrain.*

F28 §7.6 identified this as *structurally identical to mg-26fc §4.4 U1* (the missing per-`P` complex with BK-Garland data and comparison map to `Δ(PPF_n)`), recast in sheaf-theoretic dialect.

### 0.3 What "not factorial, inherently but not functorially" means for the construction

Daniel reminder 1 explicitly **rules out two patterns**:

- **Factorial** — *anything that introduces `S_n!` / factorial structure / factorial-cohomology / factorial-decompositions / `S_n`-factorial spines*. Per pm-onethird memory `feedback_anti_factorial_direction`, this is a standing constraint: if a candidate construction requires factoriality, drop it.
- **Functorial** — *a functor `\{\text{bad cuts}\} \to \{\text{cohomology classes}\}`*. If a candidate formulation requires this, the formulation is suspect.

Both rule-outs are operationalised in F29 by:

(C-1) **No `S_n!`-indexed objects.** All cochain complexes are indexed by structures intrinsic to `PPF_n` (chains, refinement covers, subposets) — not by `S_n`-cosets, `S_n`-decompositions, or factorial-graded objects.

(C-2) **No sheaf-morphism construction.** The `\widetilde\psi_{\mathrm{BC}}`-class is *not* the image of a sheaf morphism `F_{BC} \to F_\ell`. The link to `H^{n-2}(PPF_n, Q)` is a *chain-level* identification: a specific cocycle representative `\psi_{\mathrm{BC}}^{(x, y)} \in C^{n-2}(PPF_n, Q)`, evaluated by an explicit formula, whose *class* is then compared with `\omega_{bal}^{(n)}`. The comparison happens at the level of cocycles, not at the level of sheaves.

The phrase "**inherently but not functorially**" (R1) is then operationalised as: the relation between bad cuts and the F-series cohomology is *structural* (the cocycle formula is a number-theoretic identity, the cohomology class lands in `H^{n-2}`), but does **not** lift to a functorial map of cohomology theories. F29's construction respects this: no functor `\mathrm{Cuts} \to \mathrm{Cohom}` is built; instead, an *evaluation map* `\mathrm{Cuts}(P) \to \mathbb{Q}` is given per-chain, and the resulting cocycle is compared against the canonical `\omega_{bal}^{(n)}` cocycle.

### 0.4 What F29 distinguishes itself from (F28 framework search)

| | F28 (mg-d0fa) | F29 (mg-70b0, this doc) |
|---|---|---|
| direction | search for the right framework | take Daniel's mechanism directly |
| object | sheaf on `PPF_n` with BK-spectral stalks | Čech-style cochain on subposet covers with bias values |
| functoriality | required (sheaf morphism F_{BK} → F_ℓ) | **explicitly ruled out** by Daniel R1 |
| F17+F18 mode | constrains target sheaf cohomology via comparison map | constrains cocycle class via chain-level identification with ω_{bal} |
| not-sign-like step | not in scope (F28 was about constructing the bridge, not refuting sign-likeness) | **central** — Daniel R2 says sign is "boundary/commuting", bad cut is "opposite" |
| wall location | functorial sheaf morphism F_{BK} → F_ℓ does not exist | chain-level labelled-Čech ⇄ constant-Q comparison not in hand |

F29 is structurally **complementary** to F28: same target (F17+F18 forbids low-conductance configurations), but a different operational mode (chain-level vs. functor-level) and a different *direction* of bridge (backward obstruction witness vs. forward sheaf morphism).

### 0.5 What F29 does **not** do, by mandate

- F29 does **not** introduce new axioms, Lean changes, HPC artifacts, or computation. Paper-and-pencil only.
- F29 does **not** re-walk F28's framework search or F27's literal-comparison candidates. Those wall and stay walled.
- F29 does **not** propose to advance Route A (HPC-per-n) or Route B (BK/Cheeger small-γ tail). Those wall (F23, F25) and stay walled.
- F29 does **not** touch the F-series cohomological core (parts (i)–(ii)) — those are *unconditional* post F17+F18.
- F29 does **not** touch the `width3_one_third_two_thirds` Lean 4-axiom artifact; trust surface unchanged.
- F29 does **not** propose to redefine milestone 1; the milestone-1 redefinition decision sits with Daniel / PM, pre-F29 + post-F29.

---

## §1. The bad cut, precisely

This section pins the operational meaning of "bad cut" used throughout F29.

### 1.1 Bad cut = low-conductance pair-cut = bias

For width-3 1/3-2/3 (Kahn–Saks, `main.tex` §"Main result"), the conjectural conclusion is: every non-chain width-`\le 3` poset `P` has an incomparable pair `(x, y)` with `\Pr_P[x <_P y] \in [1/3, 2/3]`. A **γ-counterexample** (`step8.tex` notation) is a width-3 indecomposable `P` such that *every* incomparable pair `(x, y)` has `\Pr_P[x <_P y] \notin [3/11, 8/11]` *and* `\min(\Pr_P[x <_P y], 1 - \Pr_P[x <_P y]) \ge \gamma`.

For a γ-counterexample `P` on `n` elements, **Theorem E** (`step8.tex`, *unconditional*; recapped F25 §0, F28 §0.3, mg-26fc §1.5) gives a pair-cut `S \subseteq L(P)` with `\mathrm{vol}(S) \ge \gamma \cdot \mathrm{vol}(L(P))` and BK-conductance `\Phi(S) \le 2 / (\gamma n)`. This is the *operational* low-conductance pair-cut. The pair `(x, y)` realising `S = \{L \in L(P) : x <_L y\}` is the **bad pair**; `S = S_{xy}` is the **bad cut**.

Equivalent / paired bookkeeping (mg-26fc §1.4, §3.2): the bad cut `S_{xy}` has volume fraction `p_{xy}(P) := |L_{x < y}(P)| / |L(P)| = \pi(S_{xy})`, and the **bias** is

$$b_P(x, y) \;:=\; p_{xy}(P) \;-\; \tfrac{1}{2}.$$

The γ-counterexample condition forces `|b_P(x, y)| \ge \gamma/2` and `p_{xy}(P) \notin (3/11, 8/11)` for *every* incomparable pair `(x, y)`. Daniel reminder 1's "bad cut, eg a bias" identifies the two: the bias is the *scalar value* of the bad cut's pair-volume offset.

### 1.2 Subposets — the F29 reading

Daniel reminder 2 — *"the bad cut has a bias on each subposet"* — requires fixing a notion of "subposet" that supports the local-bias decomposition. The F29 reading, consistent with the F28 / mg-26fc setup:

> **A "subposet" of the bad cut on `P` is a refinement `P' \ge P` in `PPF_n`** — equivalently, a poset `P'` on `[n]` whose relation set strictly contains `P`'s, with `L(P') \subseteq L(P)`. The bad pair `(x, y)` of `P` remains incomparable in `P'` if and only if `P'` does not add a relation involving `(x, y)`; in this case the local bias

$$b_{P'}(x, y) \;:=\; \Pr_{P'}[x <_{P'} y] - \tfrac{1}{2}$$

> is well-defined.

**Two cases for refinement.**

(R-a) **`(x, y)` remains incomparable in `P'`.** The local bias `b_{P'}(x, y)` is defined and is, in general, different from `b_P(x, y)`. The cut `S_{xy}(P')` is the restriction of the bad cut to `L(P')`.

(R-b) **`(x, y)` becomes comparable in `P'`** (either `x <_{P'} y` is added or `y <_{P'} x` is added). The local bias *degenerates*: `\Pr_{P'}[x <_{P'} y] \in \{0, 1\}`, so `b_{P'}(x, y) \in \{\pm 1/2\}` (the cut becomes trivial: either all of `L(P')` or none).

Case (R-b) is the **resolution** of the bad pair: refining `P` to commit to `x < y` or `y < x` resolves the incomparability. Either resolution sits *strictly below* the global bad-cut bias `b_P(x, y)` in cohomological content — the resolution carries no "bias" data, only a 0/1 selection.

**Subposets *of `P`'s linear extensions*, not subposets of `P`'s element set.** Note an important reading clarification: "subposet" in F29 means *refinement of `P` in `PPF_n`* — not a sub-element-poset of `P` (the latter would mean `P \cap [n]'` for `[n]' \subsetneq [n]`, which is a different object). The Daniel-articulated bias-on-subposet decomposition is most natural for refinements: `L(P') \subseteq L(P)`, and the bias `b_{P'}` is computed on the *sub-vertex-set* `L(P') \subseteq L(P)`. This matches F28's reading of "subposet of `G_{BK}(P)`" as "induced subgraph `G_{BK}(P') \subseteq G_{BK}(P)`" (F28 §0.1).

### 1.3 The up-set `↑P` as the F29 site

The natural site for the bias-decomposition is the **up-set**

$$\uparrow P \;:=\; \{ P' \in PPF_n : P \le P' \}$$

(refinements of `P`, including `P` itself). `↑P` is itself a finite poset under refinement; its order complex `Δ(↑P)` is a subcomplex of `Δ_n = Δ(PPF_n)`. The minimum of `↑P` is `P` itself; the maximal elements of `↑P` are the *near-total* refinements of `P` (one cover relation away from a total order on `[n]`).

**Key observation.** The cardinality `|L(P')|` *decreases* under refinement: `|L(P')| \le |L(P)|` with equality iff `P' = P`. The bias `b_{P'}(x, y)`, when defined (case (R-a) of §1.2), is therefore computed on a strict sub-vertex-set. F29's Čech assembly works on `↑P` with the natural restriction direction `b_P \to b_{P'}` (going *up* refinement order, i.e. into smaller `L(P')`).

**`S_n` and stabiliser action.** `S_n` permutes `PPF_n` by relabelling `[n]`. The up-set `↑P` is in general *not* `S_n`-invariant — `g \cdot P` is in general different from `P`. The stabiliser `\mathrm{Stab}_{S_n}(P) := \{g \in S_n : g \cdot P = P\}` acts on `↑P`. Even smaller, the stabiliser `\mathrm{Stab}_{S_n}\{x, y\} := \{g : \{g \cdot x, g \cdot y\} = \{x, y\}\}` (the elementwise stabiliser of the unordered bad pair) acts on the bias datum: for `g \in \mathrm{Stab}_{S_n}\{x, y\}` fixing the pair as a set, the bias transforms as `b_{P'}(x, y) \mapsto \pm b_{g \cdot P'}(x, y)` with sign `+1` if `g` fixes the ordered pair and `-1` if `g` swaps `x` and `y`.

This stabiliser structure is the load-bearing input to the not-sign-like step in §5: the bias datum naturally lives over `\mathrm{Stab}_{S_n}\{x, y\}`, **not** over the full `S_n`.

### 1.4 What a "bad cut on `↑P`" carries — operational data

For F29's purposes, the data of the bad cut on `↑P` is the **bias function**

$$b : \uparrow P^{\mathrm{(R-a)}} \to \mathbb{Q}, \qquad P' \mapsto b_{P'}(x, y),$$

where `\uparrow P^{(\mathrm{R-a})} := \{P' \in \uparrow P : (x, y) \text{ incomparable in } P'\}` is the case-(R-a) sub-up-set (refinements not resolving the bad pair). The case-(R-b) refinements (resolving the bad pair) are *boundary*: in cohomological language, they are where the bias-cochain *vanishes* or *degenerates*.

**Three structural facts about `b`.**

(B-1) `|b| \ge \gamma/2` at `P` (the γ-counterexample assumption).

(B-2) `b` is **`\mathrm{Stab}_{S_n}\{x, y\}`-equivariant** with sign: `b_{P'}(x, y) = \mathrm{sgn}_{xy}(g) \cdot b_{g \cdot P'}(x, y)`, where `\mathrm{sgn}_{xy}(g) = +1` if `g` fixes the ordered pair and `-1` if `g` swaps.

(B-3) `b` is **`P'`-monotone with respect to refinement** in a precise weak sense — but this is *not* monotone in the naive direction: refining `P` to `P'` can *increase* or *decrease* `|b|` depending on which relations are added.

The interplay between (B-1)–(B-3) and the case-(R-b) boundary is the content of §2.

---

## §2. Local-bias decomposition on subposets — the Čech setup

This section operationalises Daniel reminder 2's "bias on each subposet, contradicts in intersections."

### 2.1 The Čech cover of `↑P`

For Čech-style cohomology on `↑P`, we need a **cover** by sub-up-sets. The natural cover, given the bad pair `(x, y)`:

$$\uparrow P \;=\; U_{\le} \;\cup\; U_{\ge} \;\cup\; U_{\parallel}, \tag{Č-1}$$

where

- `U_{\parallel} := \{P' \in \uparrow P : x \parallel_{P'} y\}` (refinements where `(x, y)` remains incomparable) `= \uparrow P^{(\mathrm{R-a})}`;
- `U_{\le} := \{P' \in \uparrow P : x \le_{P'} y\}` (refinements committing to `x < y`);
- `U_{\ge} := \{P' \in \uparrow P : y \le_{P'} x\}` (refinements committing to `y < x`).

These three pieces *partition* `↑P` (every refinement either keeps `(x, y)` incomparable or resolves it one way). **As an order-cover** the three pieces *do not overlap on actual posets* (intersection of `U_{\le}` and `U_{\ge}` is empty — no refinement is both `x < y` and `y < x`), but as **order-cover-with-boundary** the closures `\overline{U_{\le}}, \overline{U_{\ge}}` share `U_{\parallel}`'s closure as a *boundary stratum*: refining inside `U_{\parallel}` and then committing to either side lands in `U_{\le}` or `U_{\ge}`.

So the Čech-cover structure of (Č-1) is best read as a **stratification with boundary identifications**:

- top stratum: `U_\parallel` (incomparable interior);
- two open strata: `U_{\le}, U_{\ge}` (resolved exteriors);
- shared boundary: refinement-boundary `\partial U_\parallel` = refinements where a cover relation involving `(x, y)` is added.

**The Čech 1-cocycle of (Č-1).** A bias-cochain `b : U_\parallel \to \mathbb{Q}` extends naturally to `U_{\le}` (constant value `+1/2`) and `U_{\ge}` (constant value `-1/2`), giving a globally-defined function

$$\widehat b : \uparrow P \to \mathbb{Q}, \qquad \widehat b(P') = \begin{cases} b_{P'}(x, y) & P' \in U_\parallel \\ +1/2 & P' \in U_{\le} \\ -1/2 & P' \in U_{\ge} \end{cases}$$

`\widehat b` is *not* locally constant: it varies on `U_\parallel`. The Čech "contradiction on intersections" of the Daniel reminder is then: along a refinement chain `P' \le P'' \le P'''` passing from `U_\parallel` into `U_{\le}` (i.e. `P'' \in U_\parallel` but `P''' \in U_{\le}`), the bias `\widehat b(P''')` jumps from `b_{P''}(x, y) \in (-1/2, 1/2)` to `+1/2` discontinuously.

This is the source of the Čech 1-cocycle: the jump-data along refinement covers between strata.

### 2.2 The bias-jump 1-cochain `\delta \widehat b`

For each refinement cover `P' \lessdot P''` in `\uparrow P` (i.e. `P''` adds one relation to `P'`), define the **bias-jump**

$$(\delta \widehat b)(P' \lessdot P'') \;:=\; \widehat b(P'') - \widehat b(P').$$

This is a 1-cochain in `C^1(\Delta(\uparrow P), \mathbb{Q})` (the simplicial cochain complex of the order complex). Its values:

- **Within `U_\parallel`** (both `P', P''` in `U_\parallel`): `(\delta \widehat b) = b_{P''}(x, y) - b_{P'}(x, y)`, a generic real number in `(-1, 1)`.
- **Crossing into `U_{\le}`** (`P' \in U_\parallel`, `P'' \in U_{\le}`): `(\delta \widehat b) = +1/2 - b_{P'}(x, y) \in (0, 1)` (positive jump up).
- **Crossing into `U_{\ge}`** (`P' \in U_\parallel`, `P'' \in U_{\ge}`): `(\delta \widehat b) = -1/2 - b_{P'}(x, y) \in (-1, 0)` (negative jump down).
- **Within `U_{\le}` or `U_{\ge}`**: `(\delta \widehat b) = 0` (constant on the resolved strata).

`\delta \widehat b` is, by definition, the coboundary of the 0-cochain `\widehat b`. As a coboundary it is automatically a 1-cocycle: `d(\delta \widehat b) = d^2 \widehat b = 0`. As an element of `H^1(\Delta(\uparrow P), \mathbb{Q})`, **the class `[\delta \widehat b] = 0`** (it's an exact 1-form). This is the *trivial* Čech case: the bias-jump 1-cocycle is a coboundary of the global function `\widehat b`.

**So a naive Čech 1-cocycle in degree 1 is trivial.** This is *expected*: Daniel reminder 2's "contradicts in intersections sometimes" cannot be at this naive level — `H^1(\Delta(\uparrow P), \mathbb{Q})` is typically zero (the order complex `\Delta(\uparrow P)` is contractible: it has `P` as a global minimum, and the cone over `P` collapses the complex). The non-triviality has to come from a different cohomology theory.

### 2.3 Where the non-trivial class lives — three candidates

The Čech 1-cocycle of §2.2 is trivial. The Daniel-articulated cohomology class must live elsewhere. Three candidates, in order of operational specificity:

**Candidate A — degree `n - 2` cocycle on `\Delta_n = \Delta(PPF_n)`.** This is the F17+F18 degree where the only non-trivial constant-`Q` cohomology lives. The natural cocycle in this degree (mg-d60d §3.4, F28 §2.2):

$$\psi_{\mathrm{BC}}^{(x, y)}(P_0 < P_1 < \cdots < P_{n-2}) \;:=\; \prod_{i = 0}^{n-3} \Pr_{P_i}[x <_{P_i} y] \cdot [\![\, (x, y) \text{ incomp. in } P_i \,]\!]$$

(with the product taken over `i` where `(x, y)` is incomparable in `P_i`, and the product set to 0 if some `P_i` has `(x, y)` comparable in a *contradicting* sense to the chain's bias). This `\psi_{\mathrm{BC}}^{(x, y)}`-cocycle *is* a cocycle representative for `\omega_{bal}^{(n)}` (with the bad-pair-specific normalisation; mg-d60d §3.4 cocycle formula). Its cohomology class is some scalar multiple of `\omega_{bal}^{(n)}`, by F17+F18 1-dimensionality of the `sgn`-isotype.

**Candidate B — Čech `H^*` on the *stabiliser-equivariant* cover of `↑P`.** The cover (Č-1) is `\mathrm{Stab}_{S_n}\{x, y\}`-invariant. The Čech complex `\check C^*(\{U_\parallel, U_{\le}, U_{\ge}\}, \mathbb{Q})` carries a `\mathrm{Stab}_{S_n}\{x, y\}`-action. Its cohomology decomposes into `\mathrm{Stab}_{S_n}\{x, y\}`-isotypes. The natural non-trivial class lives in the **non-trivial swap-isotype** — the part where swapping `x` and `y` acts by `-1`. This is *not* `sgn_{S_n}`, it is a smaller subgroup's sign.

**Candidate C — Twisted-coefficient cohomology on `\Delta_n`.** Introduce a coefficient system `Q_{(x, y)}` on `\Delta_n` that twists by the bad-pair orientation. The bias data lives in `H^*(\Delta_n, Q_{(x, y)})`. F17+F18 do *not* directly constrain this — it is a different coefficient system. This is the "twisted-coefficient" reading; it walls in the same place as F28 §5 (no canonical bridge between twisted and constant cohomology), which is precisely the U1-dialect-collision worry.

**F29's commitment: Candidate B as the primary, Candidate A as the comparison target, Candidate C as the U1-collision-check.** §3 walks the Čech assembly of Candidate B; §4 connects it to Candidate A's `\psi_{\mathrm{BC}}^{(x, y)}`-cocycle; §5 walks the not-sign-like step; §6 returns to Candidate C as the U1-collision check.

---

## §3. The Čech-bias cocycle — explicit construction

### 3.1 The Čech complex of `\{U_\parallel, U_{\le}, U_{\ge}\}` on `↑P`

For a cover `\{U_\alpha\}_{\alpha \in I}` of a topological space `X`, Čech cohomology with values in a sheaf `F` is the cohomology of the Čech complex

$$\check C^k(\{U_\alpha\}, F) \;:=\; \prod_{\alpha_0 < \cdots < \alpha_k} F(U_{\alpha_0} \cap \cdots \cap U_{\alpha_k}),$$

with the alternating-restriction coboundary. For our `↑P` cover (Č-1), the three opens `\{U_\parallel, U_{\le}, U_{\ge}\}` have **empty pairwise intersections** as subsets of `↑P` (a single refinement is either keeping `(x, y)` incomparable or resolving it, never both). So `\check C^k = 0` for `k \ge 1` *naively* — the cover is too coarse / disjoint.

**Refinement to a usable cover.** Replace `\{U_\parallel, U_{\le}, U_{\ge}\}` with their **down-closures** in `↑P` under refinement: `\widetilde U_\parallel := \{P'' \in \uparrow P : \exists P' \le P'' \text{ with } P' \in U_\parallel\}`, similarly `\widetilde U_{\le}, \widetilde U_{\ge}`. Now intersections are non-empty *along refinement chains*: `\widetilde U_\parallel \cap \widetilde U_{\le}` contains every `P'' \in U_{\le}` such that some `P' \le P''` is in `U_\parallel` (i.e., the refinement passes from incomparable to `x < y` along the chain). The same holds for `\widetilde U_\parallel \cap \widetilde U_{\ge}`. The triple intersection `\widetilde U_\parallel \cap \widetilde U_{\le} \cap \widetilde U_{\ge}` is empty (a chain can't pass to both `x < y` and `y < x` simultaneously).

This gives a usable Čech 2-term complex:

$$\check C^0 \;=\; \mathbb{Q}^3 \;\to\; \check C^1 \;=\; \mathbb{Q}^2 \;\to\; \check C^2 \;=\; 0$$

(plus the contributions of `F` values on intersections). With `F = \underline{\mathbb{Q}}` (constant sheaf), `\check H^0 = \mathbb{Q}` (connected cover), `\check H^1 = 0` (acyclic for the constant sheaf on the cover). **Constant-coefficient Čech cohomology on this cover is trivial in positive degrees.**

The non-triviality has to come from a richer coefficient system. The natural choice (Candidate B of §2.3): take `F = F_{\mathrm{bias}}` where `F_{\mathrm{bias}}(U_\parallel) := \mathbb{Q}` (the bias-line, with the bias value), `F_{\mathrm{bias}}(U_{\le}) := \mathbb{Q}` (the resolved-`x<y` line), `F_{\mathrm{bias}}(U_{\ge}) := \mathbb{Q}` (the resolved-`y<x` line). These are *three separate `\mathbb{Q}`-lines* — copies of `\mathbb{Q}` indexed by the *stratum-orientation* — *not* canonically identified.

### 3.2 The bias sheaf `F_{\mathrm{bias}}` and its non-trivial 1-cohomology

`F_{\mathrm{bias}}` is defined as a constructible sheaf on `↑P` adapted to the stratification (Č-1):

- `F_{\mathrm{bias}}(U_\parallel) := \mathbb{Q}_{\parallel}` (a copy of `\mathbb{Q}`, the "bias line");
- `F_{\mathrm{bias}}(U_{\le}) := \mathbb{Q}_{\le}` (a copy of `\mathbb{Q}`, the "resolved-`x<y` line");
- `F_{\mathrm{bias}}(U_{\ge}) := \mathbb{Q}_{\ge}` (a copy of `\mathbb{Q}`, the "resolved-`y<x` line").

**Restriction maps along the stratification boundaries.**

- `U_\parallel \to U_{\le}`: restriction `\mathbb{Q}_{\parallel} \to \mathbb{Q}_{\le}`, `b \mapsto +1/2 - b`. (The bias-jump amount: how much the bias *jumps up* on resolving to `x < y`.)
- `U_\parallel \to U_{\ge}`: restriction `\mathbb{Q}_{\parallel} \to \mathbb{Q}_{\ge}`, `b \mapsto -1/2 - b`. (The bias-jump amount: how much the bias *jumps down* on resolving to `y < x`.)
- `U_{\le} \to U_{\ge}`: no direct boundary — these strata don't share a face directly.

Note the restriction maps are *affine*, not linear: they translate by `\pm 1/2`. This is a feature: the "bias zero" of `U_\parallel` is *not* the same `0` as the constant value `+1/2` of `U_{\le}` — they sit in different affine lines.

To make `F_{\mathrm{bias}}` a sheaf of `\mathbb{Q}`-vector spaces (linearity), we **linearise the affine structure**: replace each `\mathbb{Q}_\alpha` with a 2-dimensional space `\widetilde{\mathbb{Q}}_\alpha := \mathbb{Q} \oplus \mathbb{Q} \cdot v_\alpha`, where `v_\alpha` is an "offset vector" carrying the affine origin. Restriction becomes linear: `(b, v_\parallel) \mapsto (1/2 - b, v_{\le})`, expressed as a `\mathbb{Q}`-linear map.

**The linearised bias-cochain `\widetilde b`.** Define a 0-cochain `\widetilde b \in \check C^0(\{U_\alpha\}, F_{\mathrm{bias}})` by:

- `\widetilde b|_{U_\parallel} := (b_P(x, y), v_\parallel) \in \widetilde{\mathbb{Q}}_\parallel`;
- `\widetilde b|_{U_{\le}} := (0, v_{\le}) \in \widetilde{\mathbb{Q}}_{\le}`;
- `\widetilde b|_{U_{\ge}} := (0, v_{\ge}) \in \widetilde{\mathbb{Q}}_{\ge}`.

The Čech coboundary `\delta_Č \widetilde b` is a 1-cochain in `\check C^1(\{U_\alpha\}, F_{\mathrm{bias}})`. Its values on the non-empty 2-intersections:

- on `\widetilde U_\parallel \cap \widetilde U_{\le}`: `\delta_Č \widetilde b = \widetilde b|_{U_{\le}} - \rho_{\parallel \to \le}(\widetilde b|_{U_\parallel}) = (0, v_{\le}) - (1/2 - b_P, v_{\le}) = (b_P - 1/2, 0)`;
- on `\widetilde U_\parallel \cap \widetilde U_{\ge}`: `\delta_Č \widetilde b = (b_P + 1/2, 0)`.

**Both 1-cochain values are non-zero in general** (for a γ-counterexample, `b_P(x, y) \neq \pm 1/2`, so `b_P - 1/2 \neq 0` and `b_P + 1/2 \neq 0`). This is the **Čech 1-cocycle** of the bad cut on `↑P`:

$$\boxed{\ \widetilde \psi_{\mathrm{BC}} \;\in\; \check C^1(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}), \qquad (\widetilde \psi_{\mathrm{BC}})_{\parallel, \le} = b_P - \tfrac{1}{2}, \quad (\widetilde \psi_{\mathrm{BC}})_{\parallel, \ge} = b_P + \tfrac{1}{2}.\ }$$

(The class `[\widetilde \psi_{\mathrm{BC}}] \in \check H^1(\{\widetilde U_\alpha\}, F_{\mathrm{bias}})` is `\widetilde b`'s coboundary, hence trivial as a cohomology class.)

**Operational consequence.** The naive Čech 1-cocycle `\widetilde \psi_{\mathrm{BC}}` is **non-zero as a cochain** but **trivial as a cohomology class** (it's the coboundary of the global section `\widetilde b`). This matches the §2.2 expectation: any 1-cocycle that comes from a globally-defined function is exact.

### 3.3 The non-trivial cocycle: relax "global section" via `S_n`-orbit decoration

The bias-cochain `\widetilde b` is *globally defined* on `↑P` because we fixed a bad pair `(x, y)`. To get a non-trivial class, we **relax**: instead of fixing one bad pair, consider the **`S_n`-orbit** of bad pairs.

For a γ-counterexample `P`, each incomparable pair `(x, y)` of `P` is *some* bad pair (γ-counterexample condition: every pair is bad). The `S_n`-action permutes pairs: `g \cdot (x, y) = (g \cdot x, g \cdot y)`. For each pair `(x, y)`, the bias-cochain `\widetilde b^{(x, y)}` is defined as in §3.2. The *orbit-sum*

$$\widetilde b^{\mathrm{orb}} \;:=\; \sum_{(x, y) \in \mathcal{P}(P)} \pm_{xy} \cdot \widetilde b^{(x, y)}$$

(with signs `\pm_{xy}` to be chosen) carries the `S_n`-action by permutation. The choice of signs determines the `S_n`-isotype of `\widetilde b^{\mathrm{orb}}`.

**The natural sign choice — `sgn`-isotype.** Set `\pm_{xy} := +1` if `x < y` in some fixed reference order, `-1` otherwise. Then `\widetilde b^{\mathrm{orb}}` transforms under `S_n` by `sgn`: `g \cdot \widetilde b^{\mathrm{orb}} = \mathrm{sgn}(g) \cdot \widetilde b^{\mathrm{orb}}`. The corresponding orbit-Čech-1-cocycle `\widetilde \psi_{\mathrm{BC}}^{\mathrm{orb}}` lives in the `sgn`-isotype of `\check C^1(\dots, F_{\mathrm{bias}})`.

**Is `[\widetilde \psi_{\mathrm{BC}}^{\mathrm{orb}}]` zero or non-zero in cohomology?** If `\widetilde b^{\mathrm{orb}}` is a *valid* global section of `F_{\mathrm{bias}}^{\mathrm{orb}}` (the orbit-sum sheaf), then `\widetilde \psi_{\mathrm{BC}}^{\mathrm{orb}}` is its coboundary, hence exact. But the sum `\widetilde b^{\mathrm{orb}}` requires *simultaneous* assignment of `+1/2` to all `U_{\le, (x, y)}` and `-1/2` to all `U_{\ge, (x, y)}`, which is *not* consistent across different `(x, y)` pairs (different pairs have different strata).

This is the **contradiction on intersections** of Daniel reminder 2: each individual `\widetilde b^{(x, y)}` is globally defined on `↑P`, but the orbit-sum `\widetilde b^{\mathrm{orb}}` cannot be globally defined as a section of any one sheaf — the strata for different pairs are *incompatible*. The Čech-style obstruction class lives in the failure of `\widetilde b^{\mathrm{orb}}` to be a global section.

### 3.4 The Čech 2-cocycle from incompatible strata

For the refined cover where each pair `(x, y)` gives its own three strata `\{U_\parallel^{(x, y)}, U_{\le}^{(x, y)}, U_{\ge}^{(x, y)}\}`, the union over pairs gives a cover with *non-empty triple intersections*:

$$U_\parallel^{(x_1, y_1)} \cap U_\le^{(x_1, y_1)} \cap U_\parallel^{(x_2, y_2)}$$

is the locus where pair `(x_1, y_1)` is resolving to `x_1 < y_1` but pair `(x_2, y_2)` remains incomparable. As we move along refinement chains, the bias data for `(x_2, y_2)` keeps varying, while the bias data for `(x_1, y_1)` is *fixed* at `+1/2` (resolved).

The Čech 2-cocycle measures the incompatibility:

$$(\widetilde \psi_{\mathrm{BC}}^{(2)})_{(x_1, y_1) \in U_\le, (x_2, y_2) \in U_\parallel} \;:=\; \widetilde b^{(x_1, y_1)}|_{\text{(intersection)}} - \widetilde b^{(x_2, y_2)}|_{\text{(intersection)}}$$

evaluated on chambers of `↑P` that lie in both strata. The difference is generically non-zero (one term is `0` for the resolved pair, the other is the bias `b_{P''}(x_2, y_2) \neq 0` for the unresolved pair).

**This is the Čech 2-cocycle of Daniel's "contradicts on intersections."** It is non-trivial as a cohomology class because the corresponding global section of `\bigoplus_{(x, y)} F_{\mathrm{bias}}^{(x, y)}` would require *simultaneous* resolution of all pairs in `\mathcal{P}(P)` — which is impossible for a γ-counterexample (each pair is incomparable in `P`, and resolving one pair does not resolve others).

**Formally.** Let `n_2 := |\mathcal{P}(P)|` (number of incomparable pairs of `P`). For a width-3 poset on `n` elements, `n_2 \le \binom{n}{2}` and grows polynomially. The Čech 2-cocycle `\widetilde \psi_{\mathrm{BC}}^{(2)}` lives in `\check C^2` and is generically non-zero.

Whether `[\widetilde \psi_{\mathrm{BC}}^{(2)}]` is non-zero in `\check H^2` depends on the cover acyclicity. For the **full incomparable-pair-indexed cover** on `↑P`, `\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})` is generically non-zero: the cover is sufficiently fine to detect the multi-pair-stratification structure. **This is where the bad cut's Čech class lives.**

### 3.5 Summary of §3

The Čech-bias construction is:

(S3-1) Fix a bad pair `(x, y)` and the cover (Č-1).
(S3-2) Define `F_{\mathrm{bias}}^{(x, y)}` as in §3.2.
(S3-3) The single-pair Čech 1-cocycle `\widetilde \psi_{\mathrm{BC}}^{(x, y)}` is trivial in cohomology (coboundary of the globally-defined `\widetilde b^{(x, y)}`).
(S3-4) Take the `S_n`-orbit over all incomparable pairs of `P` (or over `\mathrm{Stab}_{S_n}(P)`-orbits in the equivariant setting).
(S3-5) The orbit-Čech-cohomology of the multi-pair cover **carries a non-trivial 2-cocycle** `\widetilde \psi_{\mathrm{BC}}^{(2)}` measuring the inter-pair-stratification contradictions.
(S3-6) This 2-cocycle is the **`\widetilde \psi_{\mathrm{BC}}` of the F29 program** — the bad cut's Čech cohomology class.

§4 connects this Čech 2-cocycle to the constant-coefficient `H^{n-2}(PPF_n, Q)` of F17+F18.

---

## §4. Anchoring to F17+F18 — what "only sign-like at the relevant degree" means

This section restates F17+F18 in the form needed for the not-sign-like step of §5.

### 4.1 F17+F18, unconditionally

F17 (mg-4d3a, GREEN-equivariant-uniform) + F18 (mg-d039, GREEN-ucc2-proven) jointly prove (F17 §0.2, F18 §0.2, F18 §0.3):

$$\widetilde H^k(\Delta_n; \mathbb{Q}) \;=\; \begin{cases} \mathrm{sgn}_{S_n} & k = n - 2 \\ 0 & 0 < k < n - 2 \text{ or } k > n - 2 \end{cases} \qquad \text{all } n \ge 3.$$

**`\omega_{bal}^{(n)}` is the unique-up-to-scalar generator** of `\widetilde H^{n-2}(\Delta_n)^{\mathrm{sgn}}` (F28 §2.2, mg-d60d §3.4). Its cocycle representative on `(n-2)`-chains `c = (P_0 < P_1 < \cdots < P_{n-2})` in `PPF_n` is

$$\omega_{bal}^{(n)}(c) \;=\; \prod_{i = 0}^{n - 3} \Pr_{P_i}[a_i <_{P_i} b_i] \cdot (\text{normalisation}),$$

where `(a_i, b_i)` is the cover relation added in `P_i \lessdot P_{i+1}`. F17+F18 give: this cocycle is non-zero in cohomology, lies in the `sgn`-isotype, and pairs non-trivially against the canonical critical chain `c^*_n` (F10 §5, P-4 of F28 §2.2).

### 4.2 The F29 reading of "only sign-like at the relevant degree"

Daniel reminder 2 — *"the only cohomology is sign-like"* — refers, in the F29 dialect, to:

> **(F29 cohomology anchor)** For `n \ge 3`, the only non-trivial cohomology of `\Delta_n = \Delta(PPF_n)` with constant `\mathbb{Q}`-coefficients in degrees `\ge 1` is at degree `n - 2`, and is the `\mathrm{sgn}_{S_n}`-isotype `\langle \omega_{bal}^{(n)} \rangle`.

**Degree match.** The Čech 2-cocycle `\widetilde \psi_{\mathrm{BC}}^{(2)}` of §3.4 lives in `\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})`. For the F17+F18 anchor to apply, we need the 2-cocycle to be compared with a *constant-`Q`* cohomology class in some matching degree. The natural matching is: **`F_{\mathrm{bias}}^{\mathrm{orb}}` admits a natural augmentation to `\underline{\mathbb{Q}}`** (the constant sheaf), and the induced map on Čech cohomology lands in `\check H^2(\{\widetilde U_\alpha\}, \underline{\mathbb{Q}})`.

**The augmentation.** Define `\epsilon : F_{\mathrm{bias}}^{(x, y)} \to \underline{\mathbb{Q}}` per pair: `\epsilon|_{U_\parallel} : \mathbb{Q}_\parallel \to \mathbb{Q}, b \mapsto b` (project the bias onto the value); `\epsilon|_{U_{\le, \ge}} : \mathbb{Q}_{\le, \ge} \to \mathbb{Q}` is the obvious projection (`\pm 1/2 \mapsto \pm 1/2`).

**This is precisely the F28-§5.1-walled augmentation:** it does *not* commute with restriction (the bias `b_{P''}` differs from `b_{P'}` under refinement, but `\epsilon` would force them equal). So `\epsilon` is *not* a sheaf morphism `F_{\mathrm{bias}}^{(x, y)} \to \underline{\mathbb{Q}}`.

This is the **F28 functorial-bridge wall, recurring in F29**: a canonical sheaf morphism between the bias sheaf and the constant sheaf does not exist. **But — and this is the F29 escape — Daniel reminder 1 explicitly rules out functoriality.** So we are *not* required to build `\epsilon` as a sheaf morphism. We can build it as a *chain-level* map: a `\mathbb{Q}`-linear map between cochain complexes that is *not* a sheaf morphism but does send cocycles to cocycles.

### 4.3 The chain-level evaluation — `\widetilde \psi_{\mathrm{BC}}^{(2)} \leadsto \omega_{bal}^{(n)}`

The chain-level evaluation that sends the bad-cut Čech cocycle to a degree-`n-2` cocycle on `\Delta_n` is:

$$\mathrm{eval}^{(x, y)} : \check C^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{(x, y)}) \to C^{n-2}(\Delta_n, \mathbb{Q})$$

defined on chains `c = (P_0 < P_1 < \cdots < P_{n-2})` in `PPF_n` by

$$\mathrm{eval}^{(x, y)}(\widetilde \psi)(c) \;:=\; \begin{cases} \prod_{i = 0}^{n-3} \Pr_{P_i}[x <_{P_i} y] & \text{if } (x, y) \text{ incomp. in all } P_i, \text{ adding cover rel. at each step} \\ 0 & \text{otherwise} \end{cases}$$

**This map is *not* a sheaf-cohomology map** (no commutation with sheaf restrictions); it is a *cochain-level* evaluation. Its key property: applied to *any* cocycle `\widetilde \psi` whose restrictions encode the bias `b_{P'}(x, y)` along chains through `P'`, the output `\mathrm{eval}^{(x, y)}(\widetilde \psi)` is a cocycle representative of `\omega_{bal}^{(n)}` (with normalisation depending on `(x, y)`).

**This is a *chain-level* identification, not a sheaf morphism. It is exactly the "inherently but not functorially" Daniel directive.**

**Consequence.** The bad-cut Čech 2-cocycle `\widetilde \psi_{\mathrm{BC}}^{(2)}`, evaluated via `\mathrm{eval}^{(x, y)}` for each `(x, y)` pair and summed over the `S_n`-orbit with appropriate signs, gives a cocycle in `C^{n-2}(\Delta_n, \mathbb{Q})` whose class **must, by F17+F18, lie in the `\mathrm{sgn}_{S_n}`-isotype** of `H^{n-2}(\Delta_n, \mathbb{Q}) = \mathrm{sgn}_{S_n}`. Specifically:

$$[\mathrm{eval}^{\mathrm{orb}}(\widetilde \psi_{\mathrm{BC}}^{(2)})] \;=\; c_{\mathrm{BC}}(P) \cdot [\omega_{bal}^{(n)}] \quad \text{for some scalar } c_{\mathrm{BC}}(P) \in \mathbb{Q}.$$

**This scalar `c_{\mathrm{BC}}(P)` is the load-bearing object of F29's not-sign-like step.** If `c_{\mathrm{BC}}(P) = 0`, the Čech 2-cocycle of the bad cut is *cohomologically equivalent* to the trivial sgn-isotype class (i.e., bad cut → 0 in cohomology). If `c_{\mathrm{BC}}(P) \neq 0`, the Čech 2-cocycle is some non-zero scalar of `\omega_{bal}^{(n)}` — i.e., the bad cut is sign-like up to scalar.

**§5 walks the not-sign-like step.** The argument has to show that *neither* `c_{\mathrm{BC}}(P) = 0` *nor* `c_{\mathrm{BC}}(P) \neq 0` is compatible with the bad cut's existence — *or* that the scalar `c_{\mathrm{BC}}(P)` is not the full content of the Čech 2-cocycle, and the residual content (the "orbit-data beyond the scalar") is precisely what fails to be sign-like.

---

## §5. The not-sign-like step — Daniel's "boundary / commuting" intuition

This is the load-bearing section of F29.

### 5.1 The Daniel articulation, parsed precisely

Daniel reminder 2: *"sign is 100 % boundary, highly commuting and the bad cut is the opposite."*

"Sign is 100 % boundary." Two readings, both viable:

(B-1) **Cohomological-boundary reading.** The `sgn` class is, in some refined cohomology theory or extended complex, a *coboundary*. F17 (mg-4d3a §5) gives the cofiber-LES sandwich `\widetilde H^{n-1}(\Delta_{n+1}/\Delta_n) = 2 \cdot \widetilde H^{n-2}(\Delta_n)`, which expresses `\omega_{bal}^{(n+1)}` as a connecting-map output of `\omega_{bal}^{(n)}`. In this sense `\omega_{bal}^{(n+1)}` is *generated* by `\omega_{bal}^{(n)}` via `\delta_n` — a "boundary"-like construction inside the extended complex `\widetilde C^*(\Delta_{n+1}, \Delta_n)`.

(B-2) **Set-theoretic boundary reading.** The `sgn` class is the *boundary* of a top-cell-orientation function. For an `(n-2)`-sphere, the `sgn` class is the top-cell-orientation cocycle — *defined* as a global orientation assignment with sign-consistent restrictions on cell boundaries. This is "boundary" in the simplicial-orientation sense.

Both readings converge to: **`\omega_{bal}^{(n)}` is the cohomology class of a *globally orientable* structure** — the boundaries of cells admit a coherent `\pm`-labelling under the `S_n`-action.

"Highly commuting." The `S_n`-action on `\omega_{bal}^{(n)}` is the `\mathrm{sgn}_{S_n}`-representation: every transposition acts by `-1`, every product of two disjoint transpositions by `+1`, etc. This is the *most abelian* `S_n`-action of degree 1: it factors through the abelianisation `S_n^{ab} = \mathbb{Z}/2`. "Highly commuting" = factors through abelianisation = `\mathrm{sgn}`.

"Bad cut is the opposite." The bad cut's `S_n`-action does *not* factor through abelianisation, because the bad pair `(x, y)` carries explicit (non-abelian) data — its position in `P`, the structure of the refinement strata it generates. Specifically: the bad-cut data is naturally an `S_n`-module that **does not** lie in the `\mathrm{sgn}`-isotype.

### 5.2 Precise statement of the not-sign-like step

> **(F29 not-sign-like conjecture).** *Let `P` be a width-3 γ-counterexample on `n \ge n_0(\gamma)` elements. Let `\widetilde \psi_{\mathrm{BC}}^{(2)} \in \check C^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}})` be the orbit-Čech 2-cocycle of §3.4–§3.5. Then the chain-level evaluation `\mathrm{eval}^{\mathrm{orb}}(\widetilde \psi_{\mathrm{BC}}^{(2)})` is a cochain in `C^{n-2}(\Delta_n, \mathbb{Q})` whose `\mathrm{sgn}_{S_n}`-isotypic component vanishes in cohomology — i.e., the orbit-Čech 2-cocycle, when projected to constant-`Q` cohomology, gives `c_{\mathrm{BC}}(P) = 0`.*

> **Combined with the non-triviality of `\widetilde \psi_{\mathrm{BC}}^{(2)}` (§3.4), this means: the bad cut's Čech 2-cocycle is non-trivial in `\check H^2(\dots, F_{\mathrm{bias}}^{\mathrm{orb}})` but its image under `\mathrm{eval}^{\mathrm{orb}}` is a coboundary in `H^{n-2}(\Delta_n, \mathbb{Q})`. Then either:*
>
> *(NS-a) `F_{\mathrm{bias}}^{\mathrm{orb}}` carries cohomology *strictly more* than `\underline{Q}`-cohomology in the relevant degree (a non-`sgn`-isotype contribution), contradicting F17+F18's "only sign-like";*
>
> *or*
>
> *(NS-b) `\widetilde \psi_{\mathrm{BC}}^{(2)}` is *forced* to be exact in `F_{\mathrm{bias}}^{\mathrm{orb}}`-cohomology, contradicting its non-trivial construction (§3.4) — which requires the bias data to be *globally patchable*, contradicting the bad cut's existence as a non-uniform configuration.*

The **either-or-contradiction** is the F29 closure shape. Both (NS-a) and (NS-b) refute the existence of `P` as a γ-counterexample.

### 5.3 Why the conjecture is plausible — the stabiliser argument

`\widetilde \psi_{\mathrm{BC}}^{(2)}` is built from data of *incomparable-pair stratifications* `(x, y) \in \mathcal{P}(P)`. The `S_n`-action permutes pairs; the stabiliser of an *individual* pair `(x, y)` is `\mathrm{Stab}_{S_n}\{x, y\} = \mathbb{Z}/2 \times S_{n-2}` (swap `\{x, y\}`, plus arbitrary permutation of the other `n - 2` elements). The stabiliser of the *whole* set of pairs `\mathcal{P}(P)` is `\mathrm{Stab}_{S_n}(P) \subseteq S_n` — for a width-3 indecomposable `P` of generic shape, `\mathrm{Stab}_{S_n}(P)` is small or trivial.

`\widetilde \psi_{\mathrm{BC}}^{(2)}` is then a cocycle that is `\mathrm{Stab}_{S_n}(P)`-equivariant *but not `S_n`-equivariant*. The natural `S_n`-orbit of `\widetilde \psi_{\mathrm{BC}}^{(2)}` (taking `g \cdot \widetilde \psi_{\mathrm{BC}}^{(2)}` for all `g \in S_n / \mathrm{Stab}_{S_n}(P)`) gives a *family* of cocycles, parametrised by the `S_n`-orbit of `P`.

To compare with `\omega_{bal}^{(n)}` (which is `\mathrm{sgn}_{S_n}`-equivariant), the natural orbit-sum is `\sum_g \mathrm{sgn}(g) \cdot (g \cdot \widetilde \psi_{\mathrm{BC}}^{(2)})`. **Whether this orbit-sum vanishes is the load-bearing question of F29.**

**Heuristic argument for vanishing (NS-a route).** The orbit-sum involves summing over `S_n` cosets with `sgn`-weights. The bad-cut data at each coset representative carries the bias-values of *all incomparable pairs of `g \cdot P`*. For width-3 `P`, the incomparable pairs of `g \cdot P` are the relabellings of `P`'s pairs. The bias-values transform under `g`: `b_{g \cdot P'}(g \cdot x, g \cdot y) = b_{P'}(x, y)` (relabel-equivariance) — *not* `\mathrm{sgn}(g) \cdot b_{P'}(x, y)`.

So the orbit-sum

$$\sum_{g} \mathrm{sgn}(g) \cdot b_{g \cdot P'}(g \cdot x, g \cdot y) \;=\; \sum_{g} \mathrm{sgn}(g) \cdot b_{P'}(x, y) \;=\; b_{P'}(x, y) \cdot \sum_{g} \mathrm{sgn}(g) \;=\; 0$$

(the alternating sum of `\mathrm{sgn}(g)` over `S_n` is zero for `n \ge 2`).

**This says: the bias-value, summed `\mathrm{sgn}`-equivariantly over the `S_n`-orbit, vanishes.** Hence `\mathrm{eval}^{\mathrm{orb}}` applied to the `\mathrm{sgn}`-orbit of `\widetilde \psi_{\mathrm{BC}}^{(2)}` is *not* a `\mathrm{sgn}`-isotype cocycle representative of `\omega_{bal}^{(n)}` — it's the zero cocycle representative. **`c_{\mathrm{BC}}(P) = 0`.** (NS-a) holds.

### 5.4 The catch — why the argument is load-bearing, not concluded

The §5.3 heuristic argument has an obstruction: the relabelling-equivariance `b_{g \cdot P'}(g \cdot x, g \cdot y) = b_{P'}(x, y)` holds *only when both sides are well-defined*. For arbitrary `g \in S_n`, `g \cdot P'` may *not* be a refinement of `g \cdot P`, and the bias `b_{g \cdot P'}(g \cdot x, g \cdot y)` may *not* refer to the same incomparable pair. The orbit-sum has to be done carefully, with explicit reference to which `(g \cdot P, g \cdot x, g \cdot y)`-tuple is being averaged.

**The chain-level evaluation `\mathrm{eval}^{\mathrm{orb}}` requires bookkeeping that has not been pinned down in this scoping pass.** Specifically:

(L-1) For a `(n-2)`-chain `c = (P_0 < \cdots < P_{n-2})`, the cocycle value `\mathrm{eval}^{(x, y)}(\widetilde \psi)(c)` is the product `\prod_i \Pr_{P_i}[x <_{P_i} y]` *with `(x, y)` matching the cover relation `(a_i, b_i)` of `P_i \lessdot P_{i+1}` for each `i`*. This is the cocycle formula of `\omega_{bal}^{(n)}` (mg-d60d §3.4). But the bad pair `(x, y)` of `P` is in general *not* the cover relation pair of `P \lessdot P_1` in `c` — the chain `c` adds different cover relations at each step.

So the chain-level evaluation `\mathrm{eval}^{(x, y)}` is *not* well-defined on a generic chain through `P`. It is well-defined on the **subset of chains that resolve `(x, y)` step-by-step** — but that subset is sparse.

(L-2) The `\mathrm{sgn}`-orbit-sum argument of §5.3 then runs on this sparse subset of chains, *not* on all chains of `\Delta_n`. F17+F18's "only `\mathrm{sgn}`-isotype in degree `n - 2`" is about all chains; restricting to a sparse subset can lose the `\mathrm{sgn}`-isotype constraint.

(L-3) Equivalently: `[\mathrm{eval}^{\mathrm{orb}}(\widetilde \psi_{\mathrm{BC}}^{(2)})]` lives in `H^{n-2}(\Delta_n^{(x, y)}, \mathbb{Q})` where `\Delta_n^{(x, y)}` is the subcomplex of `(n-2)`-chains resolving `(x, y)` step-by-step. F17+F18 does *not* directly constrain `H^{n-2}(\Delta_n^{(x, y)}, \mathbb{Q})` — that's a relative / subcomplex cohomology, *not* `\Delta_n`'s.

This is the load-bearing residual: the chain-level evaluation as defined is too restrictive to land in `\Delta_n`'s cohomology, and the constraint F17+F18 provides may not apply to the subcomplex `\Delta_n^{(x, y)}`.

### 5.5 What is needed for closure — the chain-level labelled-Čech ⇄ constant-Q comparison

To complete the not-sign-like step, F29 needs:

> **(F29-OP) The chain-level operationalisation.** A specific cochain-level map `\Phi : \check C^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}}) \to C^{n-2}(\Delta_n, \mathbb{Q})` that:
> (i) sends `\widetilde \psi_{\mathrm{BC}}^{(2)}` to a cocycle representative of some class in `H^{n-2}(\Delta_n, \mathbb{Q})`;
> (ii) is `S_n`-orbit-aware (the orbit-sum makes sense);
> (iii) is **not** a sheaf morphism (consistent with Daniel's "not functorially");
> (iv) has the property that `[\Phi(\widetilde \psi_{\mathrm{BC}}^{(2)})] = 0` in the `\mathrm{sgn}_{S_n}`-isotype.

The §5.3 heuristic argument gives (iv) in a particular orbit-sum *if* `\Phi` is well-defined. The §5.4 catch shows the natural candidate for `\Phi` is *not* well-defined on all of `\Delta_n` (only on the subcomplex of chains resolving `(x, y)`).

**The load-bearing residual is the construction of `\Phi`.** Once `\Phi` is in hand, F29 closes: either (NS-a) `c_{\mathrm{BC}}(P) = 0` (closure via (NS-b) of §5.2) or — if `\Phi` is forced to land in a strictly larger cohomology than `H^{n-2}(\Delta_n, \mathbb{Q})` — (NS-a) of §5.2 (contradicting F17+F18's "only sign-like").

This is the **F29-OP load-bearing residual**. It is *one step* — the explicit chain-level evaluation — and is *not* a research project of unknown size. It is a calculation. **It is the F30 target.**

### 5.6 Why F29-OP is not a U1-dialect collision

F28's barrier was a **functorial sheaf morphism** `F_{BK} \to F_\ell` — a structural map between sheaf-theoretic objects. The wall was that no candidate sheaf is *both* functorial under refinement *and* admits the right morphism.

F29's load-bearing residual is a **chain-level cochain map** `\Phi : \check C^2 \to C^{n-2}`. This is *not* a sheaf morphism. Crucially:

- `\Phi` does not need to commute with all refinement-restrictions in the sheaf-theoretic sense.
- `\Phi` only needs to send cocycles to cocycles and respect the `S_n`-action *in cohomology*, not as a sheaf morphism.
- `\Phi` can be defined piecewise on subcomplexes of `\Delta_n` (e.g., the bias-resolution subcomplex of §5.4), with the chain-level cocycle property checked directly.

So F29-OP is **operationally lighter** than F28's functorial-sheaf-morphism construction. The F28 §7.6 / §8.2 wall does *not* directly transpose: F29-OP can succeed in dialects where F28 cannot.

§6 walks the U1-dialect-collision check in detail.

---

## §6. U1-dialect-collision check

mg-26fc §4.4 U1 named a **missing per-`P` complex `K(P)` with BK-Garland spectral data + a comparison map to `\Delta(PPF_n)`** as the central piece needed for any operational identification between BK-spectral data and F-series cohomology. F27 RED'd at U1; F28 AMBER'd with U1 recurring in sheaf-theoretic dialect (a *functorial sheaf morphism*). F29's job: check whether the Čech-bias construction hits U1 in a third dialect (e.g., as a chain-level comparison that *implicitly* requires the same bridge).

### 6.1 What U1 demands across dialects

The U1 demand is, schematically: a *bridge* `\mathcal{B}_P : (\text{BK-data of } P) \to (\text{F-series } \Delta_n \text{ data})` that:

(U1-i) is **refinement-respecting**: `\mathcal{B}_P` for `P` and `\mathcal{B}_{P'}` for refinement `P'` are compatible (in some dialect — sheaf morphism / functor / chain map);
(U1-ii) carries **BK-spectral / Cheeger / cut content** faithfully (no information loss);
(U1-iii) lands in **`\Delta_n`-cohomology** in a form F17+F18 can constrain (`\mathrm{sgn}`-isotype in degree `n - 2`).

| dialect | what `\mathcal{B}_P` is | wall reason |
|---|---|---|
| F27 (literal-complex) | Garland-style comparison `G_{BK}(P) \to \Delta_n` | (U1-i) wall: BK graph and links of `\Delta_n` are different combinatorial objects |
| F28 (sheaf-morphism) | sheaf morphism `F_{BK} \to F_\ell \cong \underline{Q}` | (U1-i) wall: functoriality of BK-spectral content under refinement fails |
| **F29 (chain-level)** | chain map `\Phi : \check C^*(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}}) \to C^*(\Delta_n, \mathbb{Q})` | **(U1-i) waived by Daniel directive ("not functorially"); operational delivery in F29-OP** |

The F29 dialect's distinguishing feature: **(U1-i) is explicitly waived**. Daniel reminder 1 rules out functoriality; F29 is allowed to construct `\Phi` without sheaf-morphism / refinement-functor compatibility.

### 6.2 The dissolve criterion vs. the collision criterion

**Dissolve criterion (F29 dissolves U1).** If `\Phi` can be defined as a chain-level cochain map that:
(D-α) carries the bias-data into `C^{n-2}(\Delta_n, \mathbb{Q})` faithfully (i.e., satisfies (U1-ii) at the chain level);
(D-β) sends cocycles to cocycles and respects `S_n`-action on cohomology classes (a *cohomology* equivariance, not a sheaf-theoretic functoriality);
(D-γ) is **not** secretly a sheaf morphism in disguise (no hidden refinement-functor structure required for well-definedness),

then F29 dissolves U1: the bridge `\mathcal{B}_P` is given chain-level by `\Phi`, without requiring the functorial structure F28 walled on.

**Collision criterion (F29 hits U1 in third dialect).** If the natural definition of `\Phi` requires, at some technical step:
(C-α) implicit functoriality of BK-spectral content under refinement;
(C-β) a refinement-compatible identification of bias values across different `P''`s;
(C-γ) or any other refinement-respecting structural input,

then F29's chain-level construction is **secretly** a functorial bridge, and walls in the same place as F28.

### 6.3 Assessment — conditional dissolve

The §3–§5 sketch suggests F29 *can* be made to satisfy the dissolve criterion, but the operational delivery (F29-OP, §5.5) is not in hand. Specifically:

- (D-α) is *plausibly* met: the chain-level evaluation `\mathrm{eval}^{(x, y)}(\widetilde \psi)(c) = \prod_i \Pr_{P_i}[x <_{P_i} y]` carries bias data faithfully (it *is* the bias data, integrated along the chain).
- (D-β) is *plausibly* met: cocycle preservation under `\Phi` reduces to verifying that `d \mathrm{eval}(\widetilde \psi) = 0` whenever `d_Č \widetilde \psi = 0`, which is a routine cochain-level computation.
- (D-γ) is the *critical* check. The §5.3 heuristic argument constructs the orbit-sum `\sum_g \mathrm{sgn}(g) (g \cdot \mathrm{eval})` and derives `c_{\mathrm{BC}}(P) = 0` from cancellation. This step uses *relabelling-equivariance* `b_{g \cdot P'}(g \cdot x, g \cdot y) = b_{P'}(x, y)` — a property of the bias-data that is *itself* refinement-functorial when restricted to `\mathrm{Stab}_{S_n}(P)`-orbits. **Is this the hidden functoriality of (C-α)?**

The honest answer: **conditional dissolve**.

- The §5.3 argument uses `S_n`-relabelling-equivariance of the bias, *not* refinement-functoriality. Relabelling-equivariance is *not* the F28-walled property; it's an automatic consequence of how bias-data is defined (the bias of a pair under a relabelling is the same as the bias of the relabelled pair).
- However, the orbit-sum requires comparing biases at *different* posets `g \cdot P'`. If those `g \cdot P'` are *also* refinements of `g \cdot P`, the cross-orbit-pair comparison is automatic; but if some `g \cdot P'` is not a refinement of `g \cdot P`, the comparison degenerates.

**Conclusion of §6.** F29 *plausibly* dissolves U1 by waiving functoriality (per Daniel directive R1) and constructing `\Phi` chain-level. The operational delivery of `\Phi` (F29-OP) is not in hand, and the *manner* in which `\Phi` is constructed (specifically, whether the orbit-sum argument hides a refinement-functorial dependence) determines the verdict. **On current evidence, F29 dissolves U1 structurally** (Daniel's "not functorially" is the explicit non-functorial mode), but operational delivery of `\Phi` is required to confirm no hidden functoriality. This is the **AMBER-conditional-dissolve** posture of F29.

### 6.4 Comparison with mg-26fc U2 and U3

mg-26fc §4.4 listed U2 (the ICOP-pairing ↔ BK-Cheeger bridge) and U3 (a common generalised Laplacian) alongside U1. F29 is *most similar* to U2 in spirit (a chain-level evaluation of the bias-data into a Cheeger-flavoured statement) but with a key difference: U2 demanded a *quantitative* bridge `|\langle \omega_{bal}, c\rangle| \le F(\Phi(G_{BK}(P)))`, mapping the F-series pairing to a BK-conductance bound. F29 demands a *cohomological* bridge: the bad-cut Čech 2-cocycle maps to a `\mathrm{sgn}`-isotype cocycle representative of `\omega_{bal}` (and the not-sign-like step says this scalar `c_{\mathrm{BC}}(P) = 0`).

The qualitative difference: U2 is a *quantitative* bridge (monotone function `F`); F29 is a *structural* bridge (chain-level cocycle map). Quantitative bridges are typically harder than structural bridges; F29's reduction *plus* the not-sign-like step is more like a clean argument than U2's missing quantification.

**F29 vs. F28.** F28's `\mathcal{B}_P` was a sheaf morphism — a *functor* between sheaf-theoretic objects. F29's `\Phi` is a *chain map* between cochain complexes. The shift from functor to chain map is the key escape from F28's wall: chain maps need not commute with sheaf restrictions; only with cochain coboundaries. The Daniel directive R1 ("inherently but not functorially") is *exactly* the directive to make this shift.

---

## §7. What F29 establishes and what it doesn't

### 7.1 Establishes

(E-1) **The Daniel-articulated mechanism operationalises at the bias-cochain → Čech-cocycle level.** The cover (Č-1), the bias-sheaf `F_{\mathrm{bias}}`, the orbit-Čech 2-cocycle `\widetilde \psi_{\mathrm{BC}}^{(2)}` are well-defined for any width-3 γ-counterexample `P` (§2, §3).

(E-2) **The Čech 2-cocycle is non-trivial as a cohomology class** in `\check H^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}})` (§3.4) — measuring the inter-pair-stratification contradictions Daniel R2 names.

(E-3) **F17+F18 unconditionally pin the only non-trivial constant-`Q` cohomology of `\Delta_n` to `\mathrm{sgn}_{S_n}` in degree `n - 2`** (§4.1). This is the F29 cohomology anchor.

(E-4) **A chain-level (non-functorial) evaluation map `\mathrm{eval}^{(x, y)}` from the Čech complex to `C^{n-2}(\Delta_n, \mathbb{Q})` exists** (§4.3), respecting Daniel's "inherently but not functorially" directive.

(E-5) **The not-sign-like step admits a precise reading** (§5.2): the orbit-Čech 2-cocycle's image under `\mathrm{eval}^{\mathrm{orb}}` either (NS-a) lies outside the `\mathrm{sgn}`-isotype (contradicting F17+F18) or (NS-b) is a coboundary (contradicting the bad cut's non-trivial existence). Either outcome closes part (iii).

(E-6) **The heuristic `\mathrm{sgn}`-orbit-sum argument** (§5.3) gives `c_{\mathrm{BC}}(P) = 0` from the `\sum_g \mathrm{sgn}(g) = 0` identity, supporting (NS-b).

(E-7) **The U1-dialect-collision is structurally dissolved** by Daniel's directive R1 ("not functorially") — F29 operates in a non-functorial dialect that F28's wall does not directly hit (§6). Operational delivery of `\Phi` is required to confirm no hidden functoriality; conditional dissolve.

(E-8) **F29 is operationally lighter than F28** — it requires a chain-level cochain map, not a functorial sheaf morphism (§5.6, §6).

### 7.2 Does not establish

(N-1) **The chain-level cochain map `\Phi` is not explicitly constructed.** §4.3 gives the formula on chains where the bad pair is the cover relation at every step; on generic chains, `\Phi` is not defined. The operational extension to all chains is the F29-OP load-bearing residual (§5.4, §5.5).

(N-2) **The scalar `c_{\mathrm{BC}}(P)` is not rigorously computed.** §5.3 heuristically argues `c_{\mathrm{BC}}(P) = 0` via `\mathrm{sgn}`-orbit-cancellation, but the cancellation argument has the §5.4 catch (relabelling-equivariance vs. refinement-functoriality).

(N-3) **The (NS-a) vs. (NS-b) dichotomy is not pinned to one branch.** The argument shape allows either outcome; F29 does not decide *which* outcome `\Phi` would yield.

(N-4) **The width-3 bridge (F10 §7.4)** is not closed by F29. F29's not-sign-like step, even if fully delivered, gives a *cohomological* obstruction at general `n`; the F10 §7.4 width-3 bridge would need to be connected to this — that's an additional step, not delivered.

(N-5) **F25's RED (Hyp A small-γ tail) and F27's RED (literal hybrid) and F28's AMBER (sheaf morphism)** are not dissolved by F29. F29 is a *parallel* attack on the F10 part-(iii) gap, not a route to closing Route B or the literal hybrid.

(N-6) **The width-3 conjecture is not closed by F29.** F29 proposes a structural mechanism that *would* close part (iii) at general `n` *if* F29-OP delivers cleanly; F29 does not deliver F29-OP.

### 7.3 The F30 target

F29's load-bearing residual (§5.5) is **F29-OP**: the chain-level cochain map `\Phi : \check C^2(\{\widetilde U_\alpha\}, F_{\mathrm{bias}}^{\mathrm{orb}}) \to C^{n-2}(\Delta_n, \mathbb{Q})` with explicit definition on all chains, the orbit-sum well-defined, and the (NS-a) vs. (NS-b) outcome pinned.

**This is the F30 target.** F30 should:

(F30-1) Define `\Phi` explicitly on all chains of `\Delta_n`, including those not built from bad-pair cover relations. Likely candidate: extend `\mathrm{eval}^{(x, y)}` by summing over the orbit of chains containing each `(x, y)` as some cover relation, normalised by chain count.

(F30-2) Verify `\Phi` is a cochain map (sends cocycles to cocycles).

(F30-3) Compute `c_{\mathrm{BC}}(P) = [\mathrm{eval}^{\mathrm{orb}}(\widetilde \psi_{\mathrm{BC}}^{(2)})]` explicitly — either via direct chain-evaluation or via the `\mathrm{sgn}`-orbit-sum argument with all bookkeeping pinned.

(F30-4) Pin the (NS-a) vs. (NS-b) branch based on the value of `c_{\mathrm{BC}}(P)`.

(F30-5) Verify no hidden functoriality is used (i.e., the dissolve criterion of §6.2 is met).

**Budget estimate.** F30 is a *calculation*, not a framework search. Single-session polecat-attackable, with token budget similar to or smaller than F29's (≈ 400k–500k). If F30 lands GREEN, milestone-1 part (iii) closes at general `n` via the Daniel-articulated mechanism.

### 7.4 Cross-thread coordination

- **Union-closed program** (Daniel directive 2026-05-15T20:22Z: union\_closed should emulate). F29's "Čech-bias / not-sign-like" mode is a *concrete* framework that union-closed could emulate: identify the analogue of "bad cut" (= constraint-violating configuration); identify the analogue of "local biases on subposets" (= sub-family contradictions); build the Čech assembly; check the F17+F18-analogous "only one cohomology type" statement; show the constraint-violating Čech class is not of that type. This is a stronger emulation target than F28's "sheaf with bridge to constant sheaf" — F29's chain-level mode is operationally lighter.

- **F-series cohomological core (parts (i)–(ii))** is UNCONDITIONAL post F17+F18 and untouched by F29.

- **Lean trust surface** unchanged. No new axioms, no Lean changes, no HPC, no computation.

- **Route A (HPC-per-n)** and **Route B (BK/Cheeger small-γ tail)** verdicts unchanged. F29 is a parallel structural attack on part (iii); it does not address Route A's HPC-per-n character or Route B's small-γ-tail Hyp-A blowup.

---

## §8. The precise F29 barrier and the residual

### 8.1 The F29 barrier

> **The F29 barrier.** *Daniel articulated a Čech-bias mechanism: a bad cut decomposes into local biases on subposet refinements; the contradictions on intersections assemble into a Čech cohomology class; F17+F18 anchor the "only sign-like cohomology" statement; the bad cut's Čech class is shown to be not-sign-like, contradicting F17+F18.*
>
> *F29 operationalises this at the Čech-2-cocycle level (§3.4), pinning the orbit-Čech class `\widetilde \psi_{\mathrm{BC}}^{(2)}` and connecting it to `\omega_{bal}^{(n)}` via a chain-level evaluation `\mathrm{eval}^{(x, y)}` (§4.3). The not-sign-like step has a precise (either-or) reading (§5.2) and a heuristic argument supporting the (NS-b) branch via `\mathrm{sgn}`-orbit-cancellation (§5.3).*
>
> *The load-bearing residual is the construction of the chain-level cochain map `\Phi` (§5.5, F29-OP): explicit on all chains, orbit-aware, with `c_{\mathrm{BC}}(P)` rigorously computed. This is one step short of operational closure, polecat-attackable in F30.*
>
> *U1-dialect-collision: structurally dissolved (Daniel's "not functorially" is the explicit non-functorial mode); operationally conditional on F30 confirming no hidden functoriality (§6.3).*

### 8.2 The verdict, in one line

> **AMBER-one-load-bearing-residual.** *The Daniel-articulated Čech-bias mechanism operationalises at the bias-cochain → Čech-2-cocycle level, with a precise not-sign-like reading and a heuristic vanishing argument. The chain-level cochain map `\Phi` is the one load-bearing residual; F30 is the polecat-attackable target. The U1-dialect-collision is structurally dissolved by Daniel's non-functorial directive, conditional on F30's operational delivery.*

---

## §9. References

### 9.1 Predecessor F-series tickets

- **mg-d0fa** — F28 (sheaf cohomology on POSET): **AMBER-framework-unclear.** §7.6 / §8.2 — the load-bearing functorial-sheaf-morphism gap (mg-26fc U1 in sheaf-theoretic dialect). F29's chain-level dialect waives this functoriality.
- **mg-a3e3** — F27 (literal spectral → cohomology hybrid): **RED-mechanism-mismatch.** §4 — the three walled candidates. F29 is *not* one of these — F29 is the Daniel-articulated Čech-bias direction, distinct from all three.
- **mg-c6f2** — F25 (Hypothesis A constants audit): **RED-hypothesis-A-false-small-γ-tail.** §3, §5.1 — Route B walled. F29 does not address Route B.
- **mg-531f** — F23: **GREEN-descent-pinned (HPC-per-n).** Route A walled in HPC sense.
- **mg-4d3a** — F17: **GREEN-equivariant-uniform.** §0.2 — (UCC.1) ⟺ Hyp(n). F29 cohomology anchor (constant-`Q` cohomology of `\Delta_n`).
- **mg-d039** — F18: **GREEN-ucc2-proven.** §0.2 — null-homotopy theorem; (UCC) complete; F10 cohomological core unconditional. F29 anchor.
- **mg-26fc** — structural-analogy scoping: **GREEN-distinct-complementary.** §4.2 (Garland meta-principle); §4.3 (resonance not identity); §4.4 (U1, U2, U3). F29's U1-collision-check baseline.
- **mg-b345** — F8'' (Quillen-fiber route iii): PARKED. Untouched by F29.

### 9.2 In-tree sources

- **`main.tex`** — §"Approach: Cheeger-type expansion on the BK graph" (Route B spine).
- **`step1.tex`** — `G_{BK}(P)` definition; rich pairs; fiber + sign marker.
- **`step8.tex`** — Theorem E (Cheeger-conductance, unconditional); `lem:layered-reduction` (G3, the `K_0(γ, w)` 1/γ-blowup F25 walled).

### 9.3 F-series sources

- F10 §6.7(iii) / §7.3 / §7.4 — the width-3 bridge (open at general `n`).
- F10 §5 — ICOP framework; canonical critical chain `c^*_n`.
- F11 §3.3 — rational orbit-quotient is contractible ("cannot remain globally isotropic," cohomological form).
- F28 §2.2, §5.1, §7.6 — `\omega_{bal}` cocycle formula; functorial-sheaf-morphism gap; F28 barrier.

### 9.4 Mathematical literature

- **Čech 1932** — *Théorie générale des espaces de recouvrement*. Čech cohomology of a cover.
- **Leray 1950** — *L'anneau spectral et l'anneau filtré d'homologie d'un espace localement compact et d'une application continue*. The Čech-to-derived comparison.
- **Mitchell 1972** — *Rings with several objects*. Mitchell cohomology of small categories.
- **Cheeger 1970** — discrete Cheeger inequality.
- **Garland 1973** — *p-adic curvature and cohomology of discrete subgroups of p-adic groups*. The Garland meta-principle (mg-26fc §4.2).
- **Bubley–Karzanov 1998** — BK Markov chain.
- **Brightwell–Felsner–Trotter 1995** — the `[3/11, 8/11]` interval.
- **Kahn–Linial 1991** — unconditional `\delta_{KL} = 0.276393\ldots` bound.

### 9.5 Daniel directives

- **2026-05-15T23:20Z** — reminder 1: *"agents seem to think I want something factorial in the new cohomology program and I dont. I want a bad cut, eg a bias, to be difficult to construct out of all the posets that can be patched together to form it. This inherently, but not functorially, relates to what we proved about Pos\_n cohomology. For instance if we show bad cut -> nonspherical cohomology we could be done."*
- **2026-05-15T23:38Z** — reminder 2: *"potentially more clarity in case it helps. The bad cut has a bias on each subposet, and this contradicts in intersections sometimes, which gives its cohomology class. Since from what I understand we proved the only cohomology is sign-like, we then show a bad cut cant be sign-like. Morally this is because sign is 100% boundary, highly commuting and the bad cut is the opposite."*
- **2026-05-14T05:18Z** — finish internally; no external collaboration.
- **2026-05-15T20:22Z** — union\_closed lower priority; should emulate the 1/3-2/3 cohomology program.

### 9.6 PM memories invoked

- **`feedback_anti_factorial_direction`** — standing rule against factorial constructions in the cohomology program.
- **`feedback_latex_first_for_math_simp`** — paper-and-pencil first.
- **`feedback_polecat_cumulative_state_doc`** — cumulative `state-F29.md`.
- **`feedback_multisession_pre_file_depends_chain`** — F30 follow-on filed separately if F29 lands AMBER (not GREEN).
- **`feedback_manage_branches_default_to_main`** — no `--branch` argument passed.

---

*Polecat: mg-70b0 (F29). Branch: `polecat-cat-mg-70b0`. Verdict: **AMBER-one-load-bearing-residual** — the Daniel-articulated Čech-bias mechanism operationalises at the Čech-2-cocycle level (§3), connects to `\omega_{bal}^{(n)}` via a chain-level (non-functorial) evaluation map (§4), and admits a precise not-sign-like reading (§5) with a heuristic `\mathrm{sgn}`-orbit-cancellation argument supporting (NS-b). The chain-level cochain map `\Phi` (F29-OP) is the one load-bearing residual; F30 is the polecat-attackable target. The U1-dialect-collision is structurally dissolved by Daniel's non-functorial directive R1 ("not functorially"), conditional on F30's operational delivery confirming no hidden functoriality. No new axioms; no Lean changes; no HPC; no computation. Cumulative state: `docs/state-F29.md`.*
