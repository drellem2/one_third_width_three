# Compat-Geom — F27: Spectral → cohomology hybrid scoping — does it sidestep the F25 small-γ-tail barrier? (mg-a3e3)

**Branch:** `polecat-cat-mg-a3e3` (mg-a3e3).
**Parent:** mg-c6f2 (F25, **RED-hypothesis-A-false-small-γ-tail**) §5.2 / §5.4 — F25 walled Route B's direct BK/Cheeger contradiction route in the small-γ tail (the `K_0(γ, w) ≥ ⌈2/γ⌉ + 6w + 4` 1/γ-blowup in `step8.tex` Lemma `lem:layered-reduction` is **structural** to window-removal, not constants-tightening). Daniel-pre-positioned fallback per 2026-05-15T09:06Z and the *project_spectral_to_cohomology_fallback* memory.
**Chain:** F10 → F17 (mg-4d3a) → F18 (mg-d039) → F19–F23 chamber-Morse arc → F24 (mg-a30d, pivot to Route B) → F25 (mg-c6f2, **RED**) → **F27 (mg-a3e3)**.
**Type:** Structural scoping — does the spectral → cohomology hybrid bridge sidestep the small-γ-tail barrier (via F17+F18 unconditional core, NOT going through Hypothesis A), or does it inherit it? **Paper-and-pencil; no new axioms; no Lean; no HPC; no computation.** Cross-repo read of `one_third_width_three` (`main.tex`, `step1.tex`–`step8.tex`). Single-session; cumulative state ledger in `docs/state-F27.md`. LaTeX-style Markdown, F-series house style.
**Daniel directives:** 2026-05-14T05:18Z (finish internally; no external collaboration); 2026-05-14T17:23Z (milestone 1 — full gap-free width-3 proof); 2026-05-14T22:32Z ("keep pushing"); 2026-05-15T09:06Z (*"If a direct contradiction doesn't work perhaps you can go directly from spectral behavior → cohomology"* — the suggestion this ticket implements).

---

## Verdict: **RED-mechanism-mismatch.**

The spectral → cohomology *hybrid bridge* — taken in the most literal Garland-style reading of Daniel's 2026-05-15T09:06Z suggestion (low BK conductance ⟹ vanishing of F-series cohomology of `Δ(PPF_n)` ⟹ contradicts the unconditional F17+F18 non-vanishing) — **does not exist in a form that connects BK spectral data on `G_BK(P)` to the cohomology of `Δ(PPF_n)`.** mg-26fc §4.3 / §4.4's "distinct-but-resonant" finding was about an abstract resonance under a *common meta-principle* (Cheeger / Garland / Linial–Meshulam–Wallach / Gromov), not a usable inter-complex bridge. F27 sharpens this: each of the three candidate operationalisations of the bridge (§4.1, §4.2, §4.3 below) fails for a *concrete, named reason*, and the failure is **not** the F25 K_0(γ, w) 1/γ-blowup — it is a **different** structural mismatch, located between the two complexes themselves.

Concretely (§4):

- **Candidate 1 (Garland-on-Δ(PPF_n)).** Running Garland's method directly on `Δ(PPF_n)` requires spectral-gap bounds on the *links of vertices in `Δ(PPF_n)`* — those links are order complexes of intervals in `PPF_n`, **not** the BK graph `G_BK(P)`. BK spectral data on `G_BK(P)` does not feed Garland's input. (§4.1)
- **Candidate 2 (ICOP-pairing ↔ Cheeger).** A quantitative bridge ⟨ω_bal, c⟩ ↔ `Φ(G_BK(P))` would let Theorem E (`step8.tex`, *unconditional*: counterexample ⟹ `Φ ≤ 2/(γn)`) contradict F17+F18's *unconditional* non-vanishing. But the F-series pairing extracts only a single per-step probability in `[3/11, 8/11]` along a critical chain — not a cut conductance, not even of an `L(P)`-complex; this is mg-26fc §4.4 (U2), still not in hand. (§4.2)
- **Candidate 3 (F17+F18 replaces `lem:layered-reduction`).** Substituting the F-series unconditional core into Step 8 of `main.tex` does not yield a γ-uniform replacement for the deep-`K` layered-reduction step: F17+F18 pin the *cohomology of `Δ(PPF_n)`*, not the *BK-chain mixing of a specific `P`*, and the Step 8 cascade needs the latter. This isn't a "hybrid" so much as an unrelated structural-lemma rewrite, which F25 §5.2 already declined to enter. (§4.3)

**The hybrid does not inherit F25's K_0(γ, w) 1/γ-blowup** — because it never reaches a place where `lem:layered-reduction` is invoked. Instead it walls **earlier**, at the inter-complex bridge itself. This is structurally distinct from F25's barrier (which is *within* Route B's cascade), and the failure mode is "the bridge doesn't exist in operational form," not "the bridge exists but reproduces a 1/γ factor." Hence **RED-mechanism-mismatch**, not AMBER-hybrid-inherits.

**Operational consequence for milestone 1** (§5). All three documented internal routes are now walled, each in a *different* way:

| route | nature of wall | source |
|---|---|---|
| Route A — chamber-Morse HPC-per-n | the `n`-uniform `(CM-rel)` proof is "not attempted"; F23's evidence refutes every `n`-uniform structural discriminator on the 3-datapoint record `c*_3, c*_4, c*_5` | F23 §4–§5 |
| Route B — BK/Cheeger | small-γ-tail failure of Hyp A: `K_0(γ, w) ≥ ⌈2/γ⌉ + 6w + 4` in `lem:layered-reduction` forces `δ_0(γ) ∼ γ/(4w²)` and hence cubic γ-decay of the Hyp-A LHS against a fixed positive RHS; structural to window-removal | F25 §3 |
| Route Hybrid — spectral → cohomology | the bridge between BK spectral data on `G_BK(P)` and the cohomology of `Δ(PPF_n)` does not exist in operational form; the three candidate operationalisations (Garland-on-Δ, ICOP↔Cheeger, F17+F18 as Step-8 replacement) each fail for a concrete, named reason | F27 §4 |

This is the **AMBER-hybrid-inherits-equivalent escalation case promoted to RED**: the ticket's AMBER tag was reserved for the specific "K_0 1/γ reproduces in the bridge" outcome; F27 finds the bridge walls earlier and differently. The *practical consequence* — three internal routes walled in different ways, milestone-1 redefinition is the next Daniel-level decision — is the same as AMBER. This is surfaced for Daniel/PM decision in §6.

**Deliverables (this session):**

- `docs/compatibility-geometry-F27-spectral-to-cohomology-scoping.md` (this doc).
- `docs/state-F27.md` (cumulative state ledger).

---

## §0. Setup — what the hybrid is supposed to be

### 0.1 The precise statement of Daniel's 2026-05-15T09:06Z suggestion

Daniel's reminder, 2026-05-15T09:06Z, given as a fallback for the (then-anticipated) F25-RED scenario:

> *"If a direct contradiction doesn't work perhaps you can go directly from spectral behavior → cohomology."*

"Direct contradiction" refers to Route B's structural plan: a γ-counterexample `P` forces (by `step8.tex` Theorem E, unconditional) a low-conductance pair-cut in the Bubley–Karzanov graph `G_BK(P)`; the cascade (Hyp A) then turns "low conductance" into a numerical contradiction with the Bubley–Karzanov mixing-time bound on width-3 chains. F25 showed this cascade has a small-γ tail it does not unconditionally cover (`lem:layered-reduction` G3's `K_0 ∼ 2w/γ` is structural).

"Spectral → cohomology" then means: **route the spectral input (Theorem E's low-conductance pair-cut) into the F-series cohomological world rather than into the cascade-closure world**. The cohomological world is now, post F17+F18, *unconditional* — `H̃^k(Δ_n; ℚ)` is concentrated in degree `n−2` and equals `sgn_{S_n}` there (`H-Cox + sgn`), with `ω_bal^{(n)}` existing, unique, and pairing non-trivially against the canonical `(n−2)`-cell `c*_n`. If "low BK conductance" can be made to imply "vanishing of the relevant F-series cohomology", we contradict the unconditional non-vanishing directly — bypassing Hyp A.

### 0.2 The mg-26fc Garland meta-principle, recapped

mg-26fc §4.2 / §4.3 (`compatibility-geometry-structural-analogy-scoping.md`) established the *meta-principle* that links the two 1/3-2/3 mechanisms:

> *Cheeger 1970; Garland 1973; Linial–Meshulam–Wallach 2006; Gromov 2010 — graph expansion / spectral gap and (co)homology vanishing are quantitatively tied.*

The meta-principle, as applied in mg-26fc, is twofold:

- **Cheeger.** For a reversible chain on a graph `G`, `Φ²/2 ≤ λ_2 ≤ 2Φ`. Spectral gap ⟺ graph expansion. This is a one-complex statement; it makes "expansion defect = small spectral gap = curvature deficit" precise.
- **Garland.** For a finite simplicial complex `K`, if every vertex link has spectral gap `> 1 − 1/(d+1)` (the "Garland threshold" in degree `d`), then `H̃^d(K; ℝ) = 0`. This is the route to *cohomology vanishing* from local spectral data — but the input is spectral data on the *links of `K`*, not on a separate, smaller graph.

The mg-26fc verdict was **GREEN-distinct-complementary**: the BK lens and the F-series cohomological lens are linked by this meta-principle but are *not the same mathematical object*. §4.3 was explicit:

> *"The expansion ⟷ cohomology meta-principle, applied to the BK lens, produces the (co)homology of the BK graph itself … or at most the cohomology of a complex built on `L(P)`. It does not produce `H̃^∗(Δ(PPF_n))`. The F-series cohomology is the cohomology of a different complex … and there is no theorem (and no evident reason) identifying the BK-chain spectral gap of a fixed `P` with the sign-isotypic cohomology of `Δ(PPF_n)`."*

mg-26fc §4.4 listed three candidate bridges (U1, U2, U3) that *would* upgrade the resonance to identity; **none was in hand**.

F27's job is to take this 2026-05-14 scoping finding and **decide it operationally for the F25-RED context**: post F17+F18, with Hyp A walled in the small-γ tail, can any of (U1)/(U2)/(U3) — or a fourth, hybrid-style mechanism — be operationalised in a form that sidesteps F25's barrier?

### 0.3 What "sidesteps" vs. "inherits" means precisely

The barrier (F25 §3.3, §5.1): the `K_0(γ, w) = max(2w + 2, ⌈2/γ⌉ + 6w + 4)` threshold of `step8.tex` Lemma `lem:layered-reduction` (G3) forces `δ_0(γ) ∼ γ/(4w²)` for small γ, hence forces the Hyp-A LHS `γ² · c_5(T_0) · c_6 · δ_0(γ)` to cubic γ-decay against the constant RHS `8`. The `1/γ` factor in `K_0` is *necessary* for window-removal in the proof of `lem:layered-reduction` to preserve the γ-counterexample property: `|W|/|X| ≲ γ` forces `K ≥ Ω(w/γ)`.

"Sidesteps the barrier" means: **the hybrid argument does not invoke `lem:layered-reduction`, the Hyp A cascade, or any other place where the `|W|/|X| ≲ γ` constraint enters.** In particular it does *not* go through Steps 1–8's deep-`K` regime as currently written.

"Inherits the barrier" means: **somewhere in the hybrid, a `1/γ` factor of the same structural origin reproduces** — typically because the hybrid invokes `lem:layered-reduction` (directly or via a wrapper), or because a parallel window-removal step is forced by the bridge's own input.

The Daniel-level redefinition trigger (per the F27 ticket spec) was: "all three internal routes walled in different ways, milestone-1 redefinition is the next decision." F27's verdict-tag chart maps to:

- **GREEN-hybrid-sidesteps** — the bridge is operational, doesn't invoke `lem:layered-reduction`, and yields a γ-uniform contradiction. F28 (the execution) scoped precisely.
- **GREEN-partial** — partly real; some aspect sidesteps, some inherits; recommend continuation.
- **AMBER-hybrid-inherits** — the bridge is operational *enough* to write down, but reproduces the K_0 1/γ-blowup at some specific step. Daniel-level escalation: three routes walled, the third one inheriting the second one's barrier.
- **RED-mechanism-mismatch** — the bridge does *not* exist operationally; mg-26fc's resonance is real but not usable. *Equivalent escalation as AMBER in practical terms*; differs in shape of the wall.

F27's task is to walk each candidate operationalisation and pin the verdict.

---

## §1. What F17+F18 actually give us — the unconditional core, restated

Before stating any candidate bridge, we need to be precise about what the F-series cohomological core delivers *without conditional input*, and what part of milestone 1 part (iii) remains open even with F17+F18 in hand.

### 1.1 The unconditional half (F17 + F18, restated)

F17 (mg-4d3a, GREEN-equivariant-uniform) — `compatibility-geometry-F17-equivariant-cofiber-morse.md` §0.2 — proved:

> **(F17 reduction identity).** *For every `n ≥ 3`, as `S_n`-representations,*
> $$\widetilde H_d(\Delta_{n+1}/\Delta_n) \;\cong\; 2 \cdot \widetilde H_{d-1}(\Delta(A_n)) \;\cong\; 2 \cdot \widetilde H_{d-1}(\Delta_n) \qquad \text{for every }d,\ \text{unconditionally}.$$

So (UCC.1) at level `n` is *equivalent* to Hyp(n) — discharged by the induction.

F18 (mg-d039, GREEN-ucc2-proven) — `compatibility-geometry-F18-ucc2-delta-injective.md` §0.2 — proved:

> **(F18 null-homotopy theorem).** *For every `n ≥ 3`, the order-ideal inclusion `ι_n : Δ_n ↪ Δ_{n+1}` is null-homotopic by an explicit `S_n`-equivariant poset zig-zag. Hence `ι_n^* = 0` in every degree, and by exactness of the cofiber LES `δ_n` is injective in every degree.*

Together: the F10 induction `Hyp(n) ⇒ Hyp(n+1)` closes with no free-standing hypothesis. The F10 cohomological core (parts (i)–(ii)) is **UNCONDITIONAL**:

- `H̃^k(Δ_n; ℚ) = 0` for `0 < k < n − 2`, `= sgn_{S_n}` for `k = n − 2`, all `n ≥ 3`.
- `ω_bal^{(n)} ∈ H̃^{n-2}(Δ_n)^{\mathrm{sgn}}` exists, is unique up to scalar, and pairs non-trivially against the canonical critical `(n−2)`-cell.

This is the cohomological side the hybrid would target.

### 1.2 The open half (part (iii)'s residual)

F10 §6.7(iii) / §7.3 / §7.4 — the numerical width-3 conclusion — additionally requires:

- **(ICOP-step).** Along a canonical critical `(n−2)`-cell `c*_n = (P_0 ⊊ ⋯ ⊊ P_{n-2})` with `⟨ω_bal^{(n)}, c*_n⟩ ≠ 0`, the per-step Kahn–Saks probabilities `Pr_{P_k}(a_k, b_k)` lie in `[3/11, 8/11] ⊂ [1/3, 2/3]`. Verified `n ≤ 6`; reduced to clean uniform sub-statements; not part of (UCC).
- **The width-3 bridge.** For every width-3 poset `P` (not just `P` appearing on the canonical chain), there is some chain `c` through `P` with `⟨ω_bal^{(n)}, c⟩ ≠ 0` and the per-step probabilities along `c` controlled. Verified `n ≤ 6`; F19–F23 chamber-Morse arc concluded "HPC-per-n" (F23 §4–§5 evidence-refuted every `n`-uniform structural discriminator). Not part of (UCC).

So **the F-series unconditional core does not by itself close milestone 1 part (iii)** — it gives the cohomology, not the bridge from cohomology to the width-3 numerical statement. F25's RED finding is about **the alternate Route B** (BK/Cheeger), and the hybrid is about **using the spectral side to help close part (iii)**, not part (i)/(ii).

This matters for the hybrid scoping below: the hybrid does not have to *reprove* what F17+F18 already give; what it must do is *connect* (a) the spectral input from Theorem E to (b) the cohomological output of F17+F18, in a way that produces a γ-uniform contradiction.

---

## §2. What the F25 small-γ-tail barrier actually gates

F25 §3.5 / §5.1 located the barrier precisely: the `K_0(γ, w)` threshold in `step8.tex` `lem:layered-reduction` (G3). To assess inheritance, F27 needs to be specific about *which* steps in the BK/Cheeger spine the barrier gates, and which steps it leaves untouched.

### 2.1 What is unconditional in Steps 1–8

`step8.tex` (mg-c6f2 §5.1, mg-a30d §1.3, `main.tex` §"Main result"):

- **Steps 1–7 are unconditional.** The width-3 structural cascade (interface coherence, richness dichotomy, layered collapse) holds without Hyp A.
- **Step 8 items G1–G5 are discharged inside `step8.tex`**, except for the single hypothesis Hyp A.
- **Theorem E** (`step8.tex` Cheeger-conductance statement): *unconditional*. Specifically (F25 §0, mg-26fc §1.5):
  > *width-3 indecomposable γ-counterexample on `n` elements ⟹ ∃ pair-cut `S` of `G_BK(P)` with `vol(S) ≥ γ · vol(L(P))`, `Φ(S) ≤ 2/(γn)`.*
- **`lem:layered-reduction`** (G3): proven inside `step8.tex` *with* the `K_0(γ, w) = max(2w + 2, ⌈2/γ⌉ + 6w + 4)` threshold. The lemma itself is unconditional **but its `K_0` is the locus of the `1/γ` blowup**. It is invoked by the Hyp-A cascade for deep-`K` layered counterexamples.

### 2.2 What needs Hyp A

The cascade `γ → T_0 → δ_0 → ε → n_0` (F25 §0.2, §4) closes only with Hyp A. The cascade's role is to turn the Steps-1–7 + Theorem E + `lem:layered-reduction` infrastructure into a *uniform* contradiction across the Hyp-A window `γ ∈ (0, 0.057)`. The specific failure mode (F25 §3.2): `c_5^⋆(T_0, γ) ≤ c < 1` universally, and `δ_0(γ) ∼ γ/(4w²)` for small γ via `K_0`, so the Hyp-A LHS → 0 cubically.

### 2.3 The implication for the hybrid

**The hybrid sidesteps if and only if it produces the contradiction without invoking the cascade closure** — equivalently, without invoking `lem:layered-reduction` for deep-`K` regimes (the place where `K_0(γ, w)` enters). Theorem E itself is unconditional and γ-uniform-in-its-conclusion (it gives `Φ ≤ 2/(γn)`, which is "small" exactly when `n ≫ 1/γ`); so the hybrid is *allowed* to use Theorem E as a spectral input. What it cannot do is reroute through `lem:layered-reduction` deep-`K` regime — that would inherit the barrier.

So: **the hybrid's spectral input is Theorem E's low-conductance pair-cut for `G_BK(P)`. The hybrid's cohomological output target is non-vanishing of F-series `H̃^{n-2}(Δ_n)` (or a quantitative variant). The question is whether any operational bridge connects them, *without* invoking the cascade.**

---

## §3. The hybrid's three candidate operationalisations

mg-26fc §4.4 named three would-be bridges (U1, U2, U3). F27 adds a fourth Daniel-flavoured candidate (the one most-directly suggested by "go directly from spectral behavior → cohomology" + the F17+F18 unconditional core's existence): **use F17+F18 as a *replacement* for `lem:layered-reduction` in Step 8**, not as a separate cohomological target.

The four candidates are walked in §4.1–§4.3 (folding U1 and the Garland-on-Δ form into Candidate 1, U2 into Candidate 2, and U3 + the F17+F18-replacement form into Candidate 3, since U3 is implausible as a literal identity and the F17+F18-replacement form is the more concrete version of "use cohomology to bypass cascade").

Each candidate is scored on:

1. **Operationality** — can the bridge be stated as a non-vacuous theorem with concrete input/output?
2. **Inheritance** — does the operational form (if any) invoke `lem:layered-reduction` deep-`K`?
3. **Verdict contribution** — which F27 verdict tag does this candidate support?

---

## §4. Walking the candidates

### 4.1 Candidate 1 — Garland's method on `Δ(PPF_n)` (folds mg-26fc U1 + the Garland-direct reading)

**The bridge in its most-literal form.** Apply Garland's method to `K = Δ(PPF_n)`. Garland's theorem: if every vertex link `lk_K(v)` has Laplacian spectral gap `> 1 − 1/(d+1)` (the Garland threshold in degree `d`), then `H̃^d(K; ℝ) = 0`.

Used in the reverse direction: if `H̃^d(K) ≠ 0` (which F17+F18 guarantee unconditionally for `d = n − 2`), then *some* vertex link must have spectral gap *below* the Garland threshold — i.e. some link is *not* expanding enough. So F17+F18's non-vanishing converts into a *local spectral defect* on `Δ(PPF_n)`'s links.

**Where it would have to plug into BK.** For Daniel's hybrid to operationalise this way, we would need the local spectral defect on a link `lk_{Δ(PPF_n)}(P)` to *correspond to* a low BK conductance of `G_BK(P)`. Then Theorem E's spectral input could be inverted to claim a *non*-spectral-defect, contradicting F17+F18's *forced* spectral defect from non-vanishing.

**The fatal mismatch.** The link `lk_{Δ(PPF_n)}(P)` is the order complex of the *open interval* `(P, P_top) ∪ (P_bot, P)` in `PPF_n`'s refinement order — the partial orders strictly comparable to `P` under refinement, *not* the linear extensions of `P`. Concretely (F1-refined / F17 §1):

- vertices of `lk_{Δ(PPF_n)}(P)`: partial orders `Q ∈ PPF_n` with `Q ⊊ P` or `P ⊊ Q`;
- edges: chains of refinement.

The Bubley–Karzanov graph `G_BK(P)` is, by contrast (mg-26fc §1.2):

- vertices: `L(P) ⊂ S_n`, the linear extensions of `P`;
- edges: pairs `L, L'` differing by transposing two adjacent incomparable elements.

**These are different combinatorial objects.** `lk_{Δ(PPF_n)}(P)` lives over `{Q : Q\,\square\,P}` in the *poset-of-posets* `PPF_n` (a quotient-flavour space); `G_BK(P)` lives over `L(P)` in the *symmetric group* `S_n` (a permutahedral-flavour space). There is no natural map between them; in particular there is no natural identification of their Laplacian spectral data.

This was already the §3.4 ✗ finding of mg-26fc — confirmed in the F27 operational setting:

> *"$\Delta(\mathrm{PPF}_n)$ is $(n−2)$-dimensional, on partial-order vertices, with $S_n$ relabelling. $G_{\mathrm{BK}}(P)$ is $1$-dimensional, on linear-extension vertices, per fixed $P$. There is no known map identifying one's cohomology with the other's spectral data."*

Garland-on-Δ delivers a spectral statement on `lk_{Δ(PPF_n)}(P)`, *not* on `G_BK(P)`. Theorem E delivers a spectral statement on `G_BK(P)`, *not* on `lk_{Δ(PPF_n)}(P)`. The bridge would have to *identify* the two, and no such identification exists in the literature or in the F-series.

**Operationality.** ✗ — the bridge cannot be stated as a non-vacuous theorem; its two ends do not connect.

**Inheritance.** N/A — never reaches `lem:layered-reduction`.

**Verdict contribution.** RED-mechanism-mismatch. The Garland-direct form of the hybrid is not operational.

**Caveat — a different choice of complex.** One could try to choose a *different* high-dimensional complex `K(P)` per `P` whose vertex links *are* related to `G_BK(P)` — e.g. the order complex of `L(P)` under the weak order, or a thickening. mg-26fc §4.4 (U1) flagged this: it would be a per-`P` object, and would require an additional *comparison map* `K(P) → Δ(PPF_n)` to land the spectral conclusion in the right cohomology. No such `K(P)` is in hand; constructing one is a research project of unknown size, and it would be a *new* mechanism, not "the spectral → cohomology hybrid" Daniel suggested.

### 4.2 Candidate 2 — ICOP pairing controls BK Cheeger (mg-26fc U2)

**The bridge.** Suppose there were a theorem:

> *(Conjectural bridge U2.) For every width-3 `P` on `[n]` and every chain `c` through `P` (i.e. with `P` a vertex of `c` as an `(n−2)`-cell of `Δ_n`),*
> $$|\langle \omega_{\mathrm{bal}}^{(n)},\ c \rangle| \;\le\; F\bigl(\Phi(G_{\mathrm{BK}}(P))\bigr)$$
> *for some monotone `F` with `F(\Phi) \to 0` as `\Phi \to 0`.*

Then: F17+F18 give some chain `c*` through some `P` with `⟨ω_bal, c*⟩ ≠ 0` (this is the unconditional non-vanishing of the pairing at the canonical critical chain — assuming the width-3 bridge of F10 §7.4 is closed, which is the part-(iii) open piece). The conjectural bridge would force `Φ(G_BK(P)) ≥ Φ_0 > 0` for some `Φ_0`. Theorem E forces `Φ(G_BK(P)) ≤ 2/(γn)`. For `n \ge 2/(γ \Phi_0)`, contradiction. **And this contradiction is γ-uniform: the bound `n ≥ 2/(γΦ_0)` is the new `n_0(γ)`, polynomial in `1/γ` — same shape as `step8.tex` `eq:n0-def`'s existing `n_0`, but driven by `Φ_0` rather than by the Hyp-A LHS. No 1/γ-blowup; no `K_0(γ, w)`; no `lem:layered-reduction`.**

If U2 existed, the hybrid would **GREEN-sidestep**: F17+F18 unconditional non-vanishing → ω_bal non-trivial along some chain through `P` → bridge → BK Cheeger bounded below → contradicts Theorem E → done. The cascade Hyp A and `lem:layered-reduction` would be retired.

**The fatal gap.** mg-26fc §4.4 (U2) names this gap precisely:

> *"The F-series currently extracts only a single per-step probability in `[3/11, 8/11]` from the pairing, not a cut conductance; bridging 'one balanced cover step' to 'the whole cut `S_{xy}` is non-sparse' is exactly the gap between the cohomological certificate and the expansion statement, and is not bridged."*

The F-series pairing `⟨ω_bal^{(n)}, c⟩` is, when non-zero, a statement about a *single refinement cover step* in `PPF_n` — adding one relation to `P`. Its quantitative content is a per-step probability `Pr_P(a_k, b_k)`, an element of `[3/11, 8/11]` along the canonical chain (mg-26fc §3.3, F10 §5). It is *not* a sum over the boundary `∂S_{xy}` of a cut; it is *not* a Cheeger constant of any graph; it is one number per cover step.

To bridge this to BK Cheeger, one would need:

(a) A way to convert "one balanced cover step at `P`" to "the whole pair-cut `S_{xy}` of `G_BK(P)` is non-sparse." But Cheeger constant is the *minimum* over cuts of `(boundary)/(volume)`, while one balanced cover step controls only *one* cut's *volume fraction* `p_{xy}`, not its boundary. A volume-fraction control is *not* a conductance control — `p_{xy} ∈ [1/3, 2/3]` says the cut is volume-balanced but says nothing about how many BK moves cross it.

(b) Or, in the other direction: a way to convert BK Cheeger of `G_BK(P)` (a `P`-level graph invariant) into a statement about `⟨ω_bal^{(n)}, c⟩` (an `n`-level cohomology pairing over `Δ(PPF_n)`). This is U1-flavoured (Candidate 1) and shares the inter-complex mismatch — there is no natural transport from `G_BK(P)`-cuts to `Δ(PPF_n)`-cochains.

So the U2 bridge is stuck between two non-translating quantities: a *per-step volume fraction* and a *whole-cut conductance*. mg-26fc §4.4 names this gap as "the precise locus where a future unification, if any, would have to act" — and notes it is "harder than either framing's current critical path."

**Operationality.** ✗ — the bridge cannot be stated as a non-vacuous theorem; the two ends are non-translating quantities.

**Inheritance.** N/A — never reaches `lem:layered-reduction`.

**Verdict contribution.** RED-mechanism-mismatch. The U2 hybrid is not operational.

**Caveat — a softer form.** A weaker bridge — "non-vanishing of `⟨ω_bal, c⟩` along *every* chain through `P` implies *some* spectral non-degeneracy of `G_BK(P)`" — might be more tractable, but (i) F-series non-vanishing is per-canonical-chain, not per-every-chain; (ii) any spectral non-degeneracy that is not a Cheeger lower bound does not contradict Theorem E. The softening doesn't bridge the actual barrier.

### 4.3 Candidate 3 — F17+F18 as a replacement for `lem:layered-reduction` (folds mg-26fc U3 + the Daniel-flavoured "use cohomology to bypass cascade")

**The bridge.** Replace the deep-`K` use of `lem:layered-reduction` in `step8.tex`'s Hyp-A cascade with a cohomological argument drawing on F17+F18. Concretely: in the cascade `γ → T_0 → δ_0 → ε → n_0`, the role of `lem:layered-reduction` is to convert "size-minimal width-3 γ-counterexample on a layered structure of depth `K ≥ K_0(γ, w)`" into "balanced pair exists, contradiction." Substitute: "use F17+F18 to produce a balanced pair from the cohomological side, without the `K_0` threshold."

If this substitution worked, the cascade would close without `K_0`, and Hyp A would be released from its small-γ-tail failure mode.

**The fatal scope mismatch.** F17+F18 are statements about `H̃^∗(Δ(PPF_n); ℚ)` — the cohomology of the *space of all posets* on `[n]`. They are *not* statements about a *specific* size-minimal layered counterexample `P` and its mixing on `L(P)`. The deep-`K` step of `lem:layered-reduction` operates on a *single* `P` and produces a balanced pair *inside* `L(P)` via window-removal and ordinal-sum coupling on `P`'s extensions. F17+F18 produce no such per-`P` balanced-pair witness — they pin a cohomology class, not a Markov-chain mixing certificate.

The substitution would therefore have to:

(a) Take "F17+F18 says `H̃^{n-2}(Δ_n) = sgn`" and convert it into "for *this specific* size-minimal layered `P`, a balanced pair exists." The cohomological statement is global over `PPF_n`; the balanced-pair conclusion is local at `P`. This conversion is exactly the F-series part (iii) **width-3 bridge** (F10 §7.3–§7.4), which is itself open at general `n` (verified `n ≤ 6`; F19–F23 chamber-Morse arc concluded HPC-per-n with no `n`-uniform structural discriminator). So the substitution proposes to *use the open piece of F10 part (iii) to close `lem:layered-reduction`* — a circular substitution: it would close the Hyp-A cascade only if F10 part (iii) were already closed at general `n`, which it is not.

(b) Or, more modestly, produce a γ-uniform replacement for the *quantitative* `K_0(γ, w)` threshold — i.e. derive a different threshold `K_0^{coh}(γ, w)` whose `γ`-dependence is better than `1/γ`. But F17+F18 do not involve `γ` at all; they are paper-and-pencil topology of `Δ(PPF_n)`. They cannot output a `γ`-dependent threshold — they have no γ-input.

So this candidate is either circular (sub-(a)) or scope-blind (sub-(b)).

**A meta-objection.** This candidate isn't really "spectral → cohomology" in the Garland-meta-principle sense. It is "use cohomology *instead of* the spectral cascade." It is an entirely different structural-lemma proposal — the kind of thing F25 §5.2 declined to enter as "a structurally new deep-layering reduction." It is a valid research direction but not a hybrid bridge — and F27's mandate is to scope the hybrid, not to scope alternate Step-8 replacements.

**Operationality.** ✗ — the substitution is either circular or scope-blind; in the form most-charitable to Daniel's suggestion, it is a different research project (an `lem:layered-reduction` rewrite, F25 §5.2's "structurally new deep-layering reduction"), not a bridge.

**Inheritance.** N/A in form (a) (circular before reaching cascade); inheritance-question-bypassed in form (b) (the substitution doesn't even produce a threshold).

**Verdict contribution.** RED-mechanism-mismatch — sharpened to: even the most generous reading of "use cohomology in place of the cascade" does not yield an operational hybrid bridge.

### 4.4 Summary of §4

All three candidate operationalisations of "spectral → cohomology" fail, each for a *different* concrete reason:

| candidate | failure mode | locus |
|---|---|---|
| 1 — Garland on `Δ(PPF_n)` | input ends of the bridge live on different combinatorial objects (links of `PPF_n` vs `G_BK(P)`); no natural identification | inter-complex mismatch (mg-26fc §4.3) |
| 2 — ICOP pairing ↔ BK Cheeger | F-series pairing is a per-step volume-fraction, not a conductance; the two quantities don't translate | quantitative mismatch (mg-26fc §4.4 U2) |
| 3 — F17+F18 replaces `lem:layered-reduction` | either circular (uses F10 part (iii) open piece to close Step 8) or scope-blind (F17+F18 has no γ-input) | scope mismatch |

**None of the three failures is the F25 K_0(γ, w) 1/γ-blowup reproducing inside the bridge.** The bridge *never reaches the place where `lem:layered-reduction` is invoked*, because the bridge itself does not operationalise. Hence: **RED-mechanism-mismatch**, *not* AMBER-hybrid-inherits.

---

## §5. Why the verdict is RED and not AMBER or GREEN

### 5.1 Why not GREEN-hybrid-sidesteps

GREEN would require: at least one candidate operationalisation that (i) can be stated as a non-vacuous theorem with concrete input/output, (ii) does not invoke `lem:layered-reduction` deep-`K`, (iii) yields a γ-uniform contradiction. Candidate 2 would satisfy all three *if* U2 existed; but U2 does not exist as a theorem, only as a hypothetical. No candidate satisfies (i). GREEN is not the verdict.

### 5.2 Why not GREEN-partial

GREEN-partial would require: some aspect of the bridge is operational and γ-uniform, even if not the whole. The bridge has two ends — BK spectral data on `G_BK(P)` and F-series cohomology on `Δ(PPF_n)` — and **neither end alone produces a contradiction without the bridge**. F17+F18 give the F-series cohomology unconditionally, but without a bridge to BK spectral data, the cohomology does not interact with the γ-counterexample assumption. Theorem E gives BK spectral data γ-uniformly, but without a bridge to F-series cohomology, the spectral data only feeds the Hyp-A cascade, which is exactly the F25-walled route. No partial operationalisation is available; GREEN-partial is not the verdict.

### 5.3 Why not AMBER-hybrid-inherits

AMBER-hybrid-inherits, per the F27 ticket spec, requires the K_0(γ, w) 1/γ-blowup *to reproduce somewhere in the bridge*. For inheritance, the bridge would have to be operational *enough* to walk through (else there is no "somewhere" inside the bridge for the K_0 factor to reappear), and to *invoke* either `lem:layered-reduction` or a parallel window-removal step.

F27's finding is that no candidate operationalisation walks all the way through to a place where `lem:layered-reduction` would even be invoked — the bridge fails before that point. So the K_0 1/γ-blowup *does not reproduce inside the bridge*; the bridge walls earlier and for a different reason.

A natural objection: "but in the meta-sense, the hybrid still doesn't work, so milestone 1 is still in trouble — isn't that what AMBER captures?" Yes, in *practical consequence* AMBER and RED are equivalent for the F27-decision (both trigger Daniel-level milestone-1 redefinition). But the F27 ticket explicitly distinguishes them by *failure mode*: AMBER is "same barrier reproduces," RED is "different barrier / no usable bridge." F27's finding is the second. The two verdicts share the same operational consequence (§6) but not the same mechanism description.

### 5.4 Why RED-mechanism-mismatch

The four-line statement: **the Garland bridge does not actually exist in a form that connects BK spectral data to `Δ(PPF_n)` cohomology in the relevant regime; mg-26fc's "distinct-but-resonant" finding was about a more abstract resonance than a usable bridge.** F27 ticket spec lines for RED-mechanism-mismatch, verbatim. §4 walks the three candidates and confirms each fails for a concrete, named reason — none of which is K_0 1/γ-blowup.

The resonance is real — mg-26fc §4.2 documented Cheeger / Garland / coboundary expansion as a genuine meta-principle, and Daniel's "cohomological/curvature" instinct (2026-05-14 avalanche) is correct as resonance. But the resonance is between the BK lens and the F-series lens as *abstract mechanisms* — they share a substrate (pair-orientation linear-extension counts) and a meta-principle (expansion ⟷ cohomology vanishing). The resonance does *not* upgrade to an operational identification of the two cohomologies, because they are cohomologies of *different complexes* on *different vertex sets*. mg-26fc §4.4 listed three would-be identifications (U1, U2, U3); F27 confirms none has been operationalised, and the most direct path (Candidate 3) is either circular or scope-blind.

This is the cleanest available characterisation of the F27 outcome.

---

## §6. Operational consequence — milestone 1 redefinition is the next decision

### 6.1 All three internal routes are walled, each in a different way

| route | nature of wall | located in | follow-on character |
|---|---|---|---|
| **Route A — chamber-Morse HPC-per-n** | the `n`-uniform `(CM-rel)` proof is not attempted; F23 §4–§5 evidence refutes every `n`-uniform structural discriminator (top-poset OSA signature, new-element locus, size-2-block position) on the 3-datapoint record `c*_3, c*_4, c*_5`; the only `n`-uniform selector is chamber-Morse criticality, which is the definition and is HPC-per-n | F23 (mg-531f) §4–§5 | open structural research, evidence-disfavoured; HPC-treadmill |
| **Route B — BK/Cheeger** | `K_0(γ, w) ≥ ⌈2/γ⌉ + 6w + 4` in `step8.tex` `lem:layered-reduction` (G3) forces `δ_0(γ) ∼ γ/(4w²)` and hence cubic γ-decay of the Hyp-A LHS against the constant RHS = 8; `c_5^⋆ ≤ c < 1` universally seals the LHS upper bound; barrier is structural to window-removal | F25 (mg-c6f2) §3 | a structural-lemma rewrite of G3 ("structurally new deep-layering reduction"); F25 §5.2 declined |
| **Route Hybrid — spectral → cohomology** | the bridge between BK spectral data on `G_BK(P)` and the cohomology of `Δ(PPF_n)` does not exist in operational form; the three candidate operationalisations (Garland-on-Δ, ICOP-Cheeger, F17+F18-replacement) each fail for a concrete, named reason (different complexes / per-step vs. cut quantity / scope mismatch) | F27 (this doc) §4 | constructing a new comparison map between an `L(P)`-complex and `Δ(PPF_n)` (a research project of unknown size, not in hand); OR a per-`P` complex `K(P)` whose Garland data IS `G_BK(P)`'s spectral data AND that admits a comparison to `Δ(PPF_n)` |

All three walls are *structural*; none is a constants-tightening or audit-attackable gap.

### 6.2 What this means for milestone 1

Milestone 1 (Daniel 2026-05-14T17:23Z) is the full gap-free width-3 1/3-2/3 proof — no sketches, no gaps. After F27, no documented internal route closes milestone 1 part (iii) gap-free at general `n`:

- **Parts (i)–(ii)** (the F10 cohomological core) — UNCONDITIONAL post F17+F18.
- **Part (iii)** (the numerical width-3 conclusion at general `n`) — open, with three walled routes:
  - Route A: HPC-per-n; F23 evidence refuted every `n`-uniform structural discriminator.
  - Route B: Hyp A walled in small-γ tail; structural to `lem:layered-reduction`.
  - Route Hybrid: no operational bridge between BK spectral data and `Δ(PPF_n)` cohomology; failure mode is inter-complex mismatch / quantitative mismatch / scope mismatch.

**The Lean `width3_one_third_two_thirds` 4-axiom artifact** remains a separate, narrow result; untouched.

### 6.3 The next decision is Daniel-level

The F27 ticket spec named the trigger:

> *"AMBER-hybrid-inherits is the Daniel-level redefinition trigger (three routes walled in different ways)."*

F27's actual finding (RED-mechanism-mismatch) is the AMBER-equivalent escalation in practical terms — three internal routes walled, each differently. The mayor's option 3 from the F25 RED relay ("milestone-1 redefinition") is now operationally indicated. F27 does not propose a new route; F27's job was to scope the third documented option (the Daniel-pre-positioned hybrid), and it returns the third "walled" verdict.

Plausible redefinition directions, surfaced for completeness (not recommendations — Daniel/PM call):

1. **Narrow milestone 1.** Accept Route B's small-γ-tail hole and ship width-3 1/3-2/3 *conditional on* the small-γ-tail-window — i.e. the in-tree paper as written, with `γ ∈ (0, γ_crit)` and `n > n_0(γ, T_0)` as a flagged open regime. Document the hole; surface it.
2. **Settle for the `[3/11, 8/11]` conditional form.** F10 parts (i)–(ii) give the cohomological certificate unconditionally; part (iii) at general `n` remains open, but the *verified-`n` ≤ 6* form is itself a strong intermediate result. Pivot the headline to "width-3 1/3-2/3, gap-free for `n ≤ 6`, with the unconditional cohomological certificate for all `n` and a precisely-located residual at general `n`."
3. **Pursue route (iii) / mg-b345 (Quillen fiber).** The fourth documented route family (F8'', mg-b345) was parked. F18 §0.3 records that the internal track delivered both (UCC.1) and (UCC.2) without needing it, but the part-(iii) walls were unforeseen there; reactivating it is an option.
4. **Cross-route patching.** Use Routes A and B as *complementary* — Route A's HPC closes small-`n`, Route B's BK/Cheeger closes the large-`n` large-γ regime (Kahn–Linial covers γ ≥ 0.276), and a residual small-γ + large-`n` tail remains. This is a "partial proof" approach; not gap-free at general `n`, but characterises the residual precisely.

None of these is a F-series follow-on F28 — they are PM/Daniel-level program-shape decisions. F27 surfaces them; it does not recommend among them.

### 6.4 What F27 does *not* do

F27 does not propose a F28 sub-ticket (none of the three candidates supports one), does not refute the F-series cohomological core (F17+F18 unchanged), does not refute Route B's mathematical correctness (the in-tree paper remains correct conditional on Hyp A), does not refute Route A's correctness (F23's chamber-Morse machinery is correct, just HPC-per-n), and does not touch:

- the F10 cohomological core (parts i–ii) — UNCONDITIONAL, untouched;
- the F19–F23 chamber-Morse arc — parked, untouched;
- mg-b345 (route iii / Quillen fiber) — parked, untouched;
- the in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact — separate, untouched;
- the methodology paper draft — separate, untouched.

**Trust surface impact: none.** F27 is paper-and-pencil scoping; no new axioms; no Lean changes; no HPC; no computation.

---

## §7. What F27 establishes and does not establish

### 7.1 Establishes

- **The "spectral → cohomology" hybrid bridge, as suggested by Daniel 2026-05-15T09:06Z and pre-positioned in the `project_spectral_to_cohomology_fallback` memory, does not have an operational form** that connects BK spectral data on `G_BK(P)` to `H̃^∗(Δ(PPF_n))`.
- **Each of three candidate operationalisations fails for a concrete, named reason** (§4.4): Garland-on-Δ by inter-complex mismatch (links of `Δ(PPF_n)` vs `G_BK(P)`); ICOP-Cheeger by quantitative mismatch (per-step volume-fraction vs cut conductance); F17+F18-replacement by scope mismatch (cohomology is γ-blind; substitution is circular or scope-blind).
- **The bridge's failure is structurally distinct from F25's small-γ-tail barrier**: it walls *before* reaching `lem:layered-reduction`, so does *not* "inherit" the K_0(γ, w) 1/γ-blowup — it never reaches the place where K_0 would enter.
- **All three documented internal routes (A / B / Hybrid) are now walled, each in a different way** (§6.1).
- **Milestone-1 redefinition is the next Daniel/PM-level decision** (§6.3) — F27 does not propose a F28 sub-ticket because no candidate supports one.
- **F-series cohomological core (parts (i)–(ii)) remains UNCONDITIONAL** post F17+F18; F25 RED and F27 RED affect part (iii) only.

### 7.2 Does not establish

- **A future deep unification is not refuted.** F27 establishes that *as currently formulated* the bridge does not operationalise. A new comparison map `K(P) → Δ(PPF_n)` (per mg-26fc §4.4 U1) or a new Cheeger-cohomology theorem specific to refinement-of-poset complexes (a U3-flavoured genuinely new theorem) could in principle upgrade the resonance to identity. F27 does not refute this; it documents that no such bridge is in hand and that constructing one is a research project of unknown size.
- **The Garland meta-principle is not refuted.** Cheeger / Garland / Linial–Meshulam–Wallach / Gromov continue to link expansion and cohomology in each lens *separately*. mg-26fc §4.2 (the meta-principle) is intact. What F27 refutes is the *operational* form of "BK spectral → `Δ(PPF_n)` cohomology" — the meta-principle does not deliver such an operational identification.
- **Route B is not refuted as mathematics.** F25 and F27 jointly show Route B has a structural small-γ-tail hole as currently written, but do not refute the route as a valid attack — a structural-lemma rewrite of `lem:layered-reduction` (F25 §5.2) could in principle close it.
- **The width-3 1/3-2/3 conjecture is not refuted.** F27 is a scoping audit of one of three internal proof attacks; the conjecture remains open at general `n`, verified for `n ≤ 6` by both ICOP and (small-`n`) by chamber-Morse machinery.
- **F27 does not propose F28.** No candidate operationalisation supports a sub-ticket; the next decision is program-shape, not research-execution.

---

## §8. References

### 8.1 Predecessor mg-tickets

- **mg-c6f2** — F25 (the Hypothesis A constants audit): **RED-hypothesis-A-false-small-γ-tail.** Parent — F25 §3 (the cubic γ-decay); §5.1 (`K_0(γ, w)` precisely located); §5.2 (F26-equivalent rewrite declined as structural research); §5.4 (both F24 routes have located gaps).
- **mg-a30d** — F24 (the part-(iii) route fork): **GREEN-route-B-recommended.** F24 §1.2 (Hyp A statement), §1.3 (`∃T` collapse), §4 (F25 scope and the three outcome verdicts).
- **mg-26fc** — the two 1/3-2/3 mechanisms (structural-analogy scoping): **GREEN-distinct-complementary.** mg-26fc §1 (the BK column rigorised); §2 (the F-series column recapped); §3 (the two-framings dictionary); §4.2 (the expansion ⟷ cohomology meta-principle); §4.3 (the resonance is not identity); **§4.4 (U1, U2, U3 — the three would-be bridges)**.
- **mg-4d3a** — F17: **GREEN-equivariant-uniform.** F17 §0.2 (the n-uniform reduction identity `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)`); §0.3 ((UCC.1) ⟺ Hyp(n)).
- **mg-d039** — F18: **GREEN-ucc2-proven.** F18 §0.2 (the null-homotopy theorem `ι_n` null-homotopic ⟹ `δ_n` injective); §0.3 ((UCC) is COMPLETE; F10 cohomological core UNCONDITIONAL).
- **mg-531f** — F23: **GREEN-descent-pinned (HPC-per-n).** F23 §4–§5 (the `n`-uniform-pattern probe and its refutation).
- **mg-43fb / mg-0c5d** — F22-HPC. F23's HPC evidence base.
- **mg-a2cb** — F21. Chamber-Morse machinery.
- **mg-b345** — route (iii) / Quillen-fiber. Parked. Untouched by F27.

### 8.2 In-tree sources

- **`main.tex`** — §"Approach: Cheeger-type expansion on the BK graph" (Route B spine); Theorem `thm:conclusion-main` (the width-3 1/3-2/3 conclusion, conditional on Hyp A).
- **`step8.tex`** — `hyp:arith` (Hypothesis A, line ~506); `rem:final-constants-audit` (lines 1752–1870); `lem:layered-reduction` (G3, lines 2199–2311) with the load-bearing `K_0 = max(2w+2, ⌈2/γ⌉ + 6w + 4)` (proof, lines 2224–2226); Theorem E (Cheeger-conductance statement, unconditional, near the top of Step-8).
- **`step1.tex`** — `G_BK(P)` definition; fiber-and-sign-marker.
- **`generalization.md`** — §3 (the Linial width-2 ceiling); §4 (how the BK graph changes with width).

### 8.3 F-series sources

- **mg-26fc** — `docs/compatibility-geometry-structural-analogy-scoping.md`. §1 (BK column rigorised); §3 (dictionary); §4.2 (meta-principle); §4.3 (resonance not identity); §4.4 (U1/U2/U3). The pre-F27 scoping that F27 operationalises.
- **mg-4d3a** — `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`. F17 cohomological core, half 1.
- **mg-d039** — `docs/compatibility-geometry-F18-ucc2-delta-injective.md`. F17 cohomological core, half 2.
- **mg-c6f2** — `docs/compatibility-geometry-F25-hypothesis-A-constants-audit.md`. F25 RED finding; precise barrier localisation.
- **mg-a30d** — `docs/compatibility-geometry-F24-route-fork-comparison.md`. The pre-F25 route-comparison; F24 §1.2–§1.3 Hyp A statement.

### 8.4 Mathematical literature

- **Cheeger 1970** — discrete Cheeger inequality for reversible Markov chains. The expansion ⟷ spectral-gap half of the meta-principle.
- **Garland 1973** — *p-adic curvature and the cohomology of discrete subgroups of p-adic groups*, Ann. of Math. 97. The spectral-gap ⟹ cohomology-vanishing half of the meta-principle; the prototype of Candidate 1.
- **Linial–Meshulam 2006**; **Meshulam–Wallach 2009** — homological connectivity of random 2-complexes; quantitative cohomology vanishing as higher expansion. Coboundary expansion.
- **Gromov 2010** — *Singularities, expanders and topology of maps*. Topological expansion.
- **Bubley–Karzanov 1998** — the BK Markov chain; spectral gap controls mixing.
- **Kahn–Linial 1991** — unconditional `δ_KL = 0.276393…` bound (defines the Hyp-A γ window).
- **Brightwell–Felsner–Trotter 1995** — the `[3/11, 8/11]` interval (the F-series ICOP target).
- **Lovász 1979**; **Stanley 1981** — sphericity and `H-Cox + sgn` for order complexes of distributive-flavour lattices; ancestor of `Δ(PPF_n)` ≃_{ℚ} `S^{n-2}` for the F-series.

### 8.5 Daniel directives

- **2026-05-14T05:18Z** — finish internally; no external collaboration. *(F27 is pure internal scoping; no external input.)*
- **2026-05-14T17:23Z** — milestone 1 = full gap-free width-3 proof, no sketches or gaps. *(F27's finding bears on this: the hybrid does not close milestone 1; combined with F25 RED and F23's HPC-per-n verdict on Route A, milestone-1 redefinition is the next decision per §6.3.)*
- **2026-05-14T22:32Z** — "keep pushing." *(F27 pushes by closing the third documented option with a clean, named-failure-mode verdict, surfacing the redefinition trigger.)*
- **2026-05-15T09:06Z** — *"If a direct contradiction doesn't work perhaps you can go directly from spectral behavior → cohomology."* *(F27 implements this suggestion as a scoping question; the operational answer is RED-mechanism-mismatch — the bridge as conceived does not exist, but F27 confirms Daniel's *resonance* intuition (mg-26fc §4.2) is correct: the meta-principle is real, just not operationally identifying.)*

---

*Polecat: mg-a3e3 (F27). Branch: `polecat-cat-mg-a3e3`. Verdict: **RED-mechanism-mismatch** — the spectral → cohomology hybrid bridge between BK spectral data on `G_BK(P)` and the cohomology of `Δ(PPF_n)` does not have an operational form. The three candidate operationalisations (Garland-on-Δ, ICOP-Cheeger, F17+F18-as-Step-8-replacement) each fail for a different concrete reason — inter-complex mismatch, quantitative mismatch, scope mismatch — and none of these is the F25 K_0(γ, w) 1/γ-blowup reproducing inside the bridge; the bridge walls *before* reaching `lem:layered-reduction`. Operational consequence: all three documented internal routes walled, each differently — Route A by HPC-per-n + F23 refutation of `n`-uniform structural discriminators, Route B by F25's small-γ-tail structural barrier, Route Hybrid by F27's mechanism-mismatch — and milestone-1 redefinition is the next Daniel/PM-level decision (this is the AMBER-trigger-equivalent escalation in practical terms; mechanism description differs). F-series cohomological core (parts (i)–(ii)) remains UNCONDITIONAL post F17+F18; only part (iii) is affected. No new axioms; no Lean changes; no HPC; no computation. Cumulative state: `docs/state-F27.md`.*
