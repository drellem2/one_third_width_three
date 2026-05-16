# Compat-Geom — F32-scope: Union-Closed → 1/3-2/3 bridge program scope (mg-c9d9)

**Branch:** `polecat-cat-mg-c9d9` (mg-c9d9).
**Parent.** Daniel reminder 2026-05-16T11:29:58Z articulating a 10-step proof program at `~/files/union_closed_1323_proof_steps.txt` that turns a minimal 1/3-2/3 counterexample into a union-closed family on 3-antichains, applies the just-proven Frankl-Holds (union_closed/UC13+UC14, mg-83f0 merged), and produces a numerical contradiction via entropy + ERZ-style counting. Cross-repo: the program *invokes* Frankl-Holds (which we own via UC10+UC12+UC11+UC13+UC14) but lives on the 1/3-2/3 side.
**Chain:** F10 → F17 → F18 → F19–F23 chamber-Morse arc → F24 → F25 (**RED**) → F27 (**RED**) → F28 (**AMBER**) → F29 (**AMBER**, mg-70b0) → F30 (**AMBER**, mg-c3fe) → F31 (**RED**, mg-01ce, chain-locality obstruction). **F32 (mg-c9d9, this doc)** opens a structurally distinct closure route — the Union-Closed → 1/3-2/3 bridge — that *routes around* F31 rather than breaks through it (§6).
**Type:** Paper-and-pencil structural scoping. LaTeX-style Markdown; **no new axioms; no Lean changes; no HPC; no numerical computation beyond per-pencil arithmetic.** Cumulative state ledger: `docs/state-F32.md` (new; session 1 = this scoping ticket; execution sessions follow if GREEN).
**Daniel directives (inherited and re-confirmed):** 2026-05-15T23:20Z (**NOT factorial**); 2026-05-15T23:20Z (**NOT functorial in the refinement sense**); 2026-05-16T11:29Z (high priority alongside union-closed Lean formalization); pm-onethird `feedback_pre_execution_dependency_verification` (scope before execute); pm-onethird `feedback_latex_first_for_math_simp` (LaTeX-first for math-strategy work); pm-onethird `feedback_manage_branches_default_to_main` (default to main).

---

## Verdict: **AMBER-one-lemma-tractability-uncertain (L3 weighted-UCC depends on UC-side strengthening; L4 local-vs-global ERZ status unresolved).**

The four-phase scoping decomposes as:

- **Phase A (numerical-constant verification): GREEN.** Both constants verify exactly to the digits Daniel quoted: `\Delta_{\mathrm{can}} = \log_2 6 - [1 + \tfrac{1}{2}\log_2 5] = 0.42400\ldots` bits; `\Delta_{\mathrm{ERZ}} = \log_2(4/3) = 0.41504\ldots` bits; gap `\Delta_{\mathrm{can}} - \Delta_{\mathrm{ERZ}} = 0.00896\ldots` bits, positive. The gap is *robust to sharpening the canonical-frequency lower bound* (Frankl giving `\ge 1/2 + \varepsilon` only widens the gap) but is **fragile to weakening** (any concentration bound below 1/2 collapses the deficit to zero). Phase A does not invalidate the program; the program is non-vacuous.
- **Phase B (Lemma tractability survey, L1–L4):**
  - **L1 (Local Acyclicity of `\ll` on 3-antichains): GREEN — essentially proved inline below (§3.1).** Reduces to the pair-orientation sum bound `\Pr[a<b] + \Pr[b<c] + \Pr[c<a] \le 2` (§3.1.3), which conflicts with three `>2/3` strict inequalities. Tractability: trivial; the proof fits in 8 lines. L1 is **not a real residual** and can be inlined in the F32 execution doc; no separate sub-ticket needed.
  - **L2 (Union-Closure of `F(P)`): AMBER.** All four of Daniel's candidate fixes (L2-A no-extras, L2-B `\ll`-consistent restriction, L2-C representation, L2-D upward closure) have substantive failure surfaces. L2-C (representation lemma) and L2-D (upward-closure + weighted transfer) are the most tractable; both depend on L3-B. Multi-session, ~400–800k tokens. **Structurally hardest of the four.**
  - **L3 (Measure Transfer `\Pr_Q \to \Pr_L`): AMBER.** L3-A (direct) is **dead** (explicit counterexample in §3.3.2). L3-B (weighted UCC with `w(Q) = e(Q)`) is the load-bearing candidate but requires a **strict strengthening of Frankl** (weighted-UCC with positive real weights) that **is not delivered by the UC13+UC14 chain as proved**. L3-B needs a new sub-ticket on the union_closed side. L3-C (injection) is structurally cleanest if it works but requires explicit construction. Cross-repo dependency makes this the **highest-uncertainty lemma** of the four.
  - **L4 (ERZ Entropy Contradiction): AMBER, with the local-vs-global question unresolved.** Daniel's program *requires* a local form ("every 3-antichain has `H(\sigma_A) > 2.170` bits") for the contradiction step to work. Standard ERZ-style entropy bounds in the literature (Brightwell-Tetali, Kahn-Saks) are typically **global** (averaged over antichains), not local per-antichain. **The 0.009-bit gap is too tight to survive a global-only reformulation**: a global bound says "average per-antichain entropy is `\ge 2.170`", which is compatible with one antichain at 2.161 if others compensate. The program must either find a local-ERZ strengthening or reformulate to "*many* canonical antichains" rather than "*one* canonical antichain".
- **Phase C (attack-order proposal): refined below (§4).** Phase A verifies up front (already done in this doc). L1 inlines in execution (no sub-ticket needed). L4-literature-pass + L3-B weighted-UCC scoping run concurrently as Phase 0 of execution. L2 follows once L3-B's status is known. Beachhead: width-3 first.
- **Phase D (failure modes): enumerated below (§5).** Five distinct ways the program fails, ordered by likelihood. **Highest-likelihood failures: D.5 (L4 global-only) and D.4 (L3-B weighted-UCC not derivable).**

**Honest scoping verdict.** The program *survives* Phase A (numerical gap is real) and Phase B for L1 (acyclicity essentially trivial). But two of the four lemmas (L3, L4) sit on substantive open questions whose resolution is not delivered by current machinery:

- L3-B (weighted-UCC) requires a strict UC-side strengthening of UC13+UC14.
- L4 requires either a literature-supported local-ERZ bound or a program reformulation.

Either lemma walling would close the program. The 0.009-bit gap is the tightness that makes the program promising *and* makes it brittle to any looseness in the lemma-side reductions. **Verdict honestly registered as AMBER-one-lemma-tractability-uncertain**, with two lemmas (L3, L4) effectively forming a *combined* uncertainty — both are tractable only conditionally, and the program needs both. **Execution sub-ticket recommendation (§4.3): file L3-B-UC and L4-lit as the next two polecats** before any L2 work, because their RED-outcomes would moot the L2 work entirely.

---

## §0. Setup — what F32 inherits

### 0.1 Source program

Daniel articulated a 10-step proof program at `~/files/union_closed_1323_proof_steps.txt` (275 lines, 2026-05-16T11:29Z). The program structure:

- **Core objects.** For a minimal 1/3-2/3 counterexample `P`: every incomparable pair `x \| y` carries a strict canonical orientation `x \ll y` iff `\Pr_L[x <_L y] > 2/3` (so `\ll` is total on each pair). For each 3-antichain `A = \{a, b, c\}`, the canonical order of `A` is the total order induced by `\ll` on `A` (assuming `\ll` is acyclic — Step 2 / Lemma L1). For each poset extension `Q \ge P`: `S(Q) = \{A : A \text{ is a 3-antichain of } P, Q \text{ orients } A \text{ canonically}\}`. The family `F(P) = \{S(Q) : Q \ge P\} \subseteq 2^U` where `U = \text{3-antichains of } P`.
- **Steps 1–10.** (1) Minimal-counterexample setup (every pair strictly biased). (2) Local acyclicity of `\ll` on 3-antichains (= L1). (3) Define `F(P)`. (4) Prove `F(P)` is union-closed (= L2, the "hard part"). (5) Apply Frankl-Holds: some 3-antichain `A^*` appears in `\ge 1/2` of `F(P)`. (6) Transfer `\Pr_Q \to \Pr_L`: `A^*` appears in canonical order in `\ge 1/2` of linear extensions (= L3, "most important technical gap after union-closure"). (7) Entropy consequence: `H(\sigma_{A^*}) \le 1 + \tfrac{1}{2}\log_2 5 \approx 2.161` bits. (8) Compare to ERZ 3-antichain bit bound: `\log_2(4/3) \approx 0.415` compatibility allowance. (9) Prove the counting / entropy contradiction (= L4). (10) Contradiction → 1/3-2/3 holds (at least in width-3 / minimal-counterexample setting).
- **Four open lemmas (file's "Open Lemmas / Technical Gaps" section).** L_A = Local Acyclicity (Step 2). L_B = Union-Closure (Step 4). L_C = Measure Transfer (Step 6). L_D = ERZ Entropy Contradiction (Step 9). The in-text Lemma labels (Lemma A / B / C in Steps 4 / 6 / 9) are *offset by one* from the Open-Lemmas section's labels; F32-scope adopts the cleaner four-way Open-Lemmas naming, renamed **L1 / L2 / L3 / L4** to avoid collision with in-text labels.

### 0.2 Disambiguated lemma naming (carry into all execution work)

| F32-scope label | "Open Lemmas" label | In-text Step | What it says |
|---|---|---|---|
| **L1** | A | Step 2 | `\ll` is acyclic on every 3-antichain. |
| **L2** | B | Step 4 (Lemma A) | `F(P)` is union-closed (or has a union-closed enlargement preserving the argument). |
| **L3** | C | Step 6 (Lemma B) | Frequency `\ge 1/2` over poset extensions transfers to frequency `\ge 1/2` over linear extensions. |
| **L4** | D | Step 9 (Lemma C / C') | A 3-antichain with one relative order at probability `\ge 1/2` is impossible in a minimal counterexample (local ERZ form), OR the program reformulates to averaged-ERZ + many-bad-triples (global ERZ form). |

### 0.3 Hard constraints (inherited; non-negotiable)

- **NOT factorial** — pm-onethird `feedback_anti_factorial_direction`. F32 execution and any sub-ticket must not invoke factorial constructions or `n!`-indexed decompositions.
- **NOT functorial in the refinement sense** — Daniel directive 2026-05-15T23:20Z. The bridge program does not require a `\mathrm{Pos}_n`-functor. F(P) is defined chain-level on extensions; UCC application is set-theoretic.
- **Paper-and-pencil first** — pm-onethird `feedback_latex_first_for_math_simp`. The scoping doc (this) and all per-lemma sub-tickets land as LaTeX-style Markdown before any Lean execution.
- **Cumulative state doc** — `docs/state-F32.md` (new; session 1 = this scoping; future sessions track execution-lemma progress).
- **Default to main** — pm-onethird `feedback_manage_branches_default_to_main`. F32 branches as `polecat-cat-mg-c9d9` off `main`; PRs target `main`; no nested branch hierarchies.
- **U1-dialect check** — F32 routes around the F31 chain-locality wall rather than re-attempting it. Explicit verification in §6.

### 0.4 Strategic context

If the bridge program closes (GREEN), the asymmetric outcome from earlier today (Frankl-Holds COMPLETE via UC10+...+UC14, 1/3-2/3 WALLED at F31 RED-chain-locality) **inverts**: 1/3-2/3 follows from Frankl via the F32 bridge, making F31's chain-locality wall *moot for the headline 1/3-2/3 problem* (still interesting as a structural obstruction in the Čech-bias cohomology dialect, but no longer load-bearing for the conjecture itself). The F31 escalation territory (methodology-paper close + milestone-1 redefinition) is re-evaluated under this potential inversion.

If the bridge program walls (RED), F31's status as "milestone-1 part (iii) closure walled along five routes" stands.

### 0.5 Section roadmap

- §1 — Source program parsed precisely (objects, lemmas, contradiction structure).
- §2 — **Phase A**: numerical-constant verification with explicit arithmetic.
- §3 — **Phase B**: tractability survey on L1–L4 (one subsection per lemma).
- §4 — **Phase C**: attack-order proposal + per-lemma budget estimates.
- §5 — **Phase D**: failure modes + early-exit conditions per lemma.
- §6 — Hard-constraint compliance + U1-dialect-collision check.
- §7 — What this scoping establishes and what it doesn't.
- §8 — Execution sub-ticket recommendations.
- §9 — References.

---

## §1. Source program parsed precisely

### 1.1 Objects, recapped formally

Fix `P` a minimal counterexample to the 1/3-2/3 conjecture on `n` elements (Daniel's Step 1 setup; minimality formalised in the standard sense — `P` violates 1/3-2/3 but no proper sub-poset does).

- **Strict canonical orientation `\ll`.** By minimality, for every incomparable pair `x \| y \in \mathcal{P}(P)`, exactly one of `\Pr_L[x <_L y] > 2/3` or `\Pr_L[y <_L x] > 2/3` holds (where `L \sim \mathrm{Unif}(\mathcal{L}(P))` and `\mathcal{L}(P)` is the set of linear extensions). Write `x \ll y` iff `\Pr_L[x <_L y] > 2/3`. So `\ll` is a tournament on `\mathcal{P}(P)`.
- **Canonical order on 3-antichain.** For `A = \{a, b, c\} \in \binom{\mathcal{P}(P)}{3}_{\mathrm{antichain}}`, the canonical order of `A` (Daniel's Step 2 definition) is the total order induced by `\ll` on `A`, *assuming `\ll` is acyclic on `A`* (= L1). If acyclic, the canonical order is well-defined and is one of the six total orders on `\{a, b, c\}`.
- **Extension family.** `\mathcal{Q}(P) := \{Q : Q \ge P \text{ in } \mathrm{PPF}_n\}` (poset extensions of `P`, partially ordered by refinement). For `Q \in \mathcal{Q}(P)`:

$$S(Q) \;:=\; \bigl\{A \in U : Q \text{ contains all comparabilities of the canonical order of } A\bigr\},\quad U := \tbinom{\mathcal{P}(P)}{3}_{\mathrm{antichain}}.$$

  Concretely if `A = \{a, b, c\}` has canonical order `a \ll b \ll c`, then `A \in S(Q)` iff `a <_Q b`, `b <_Q c`, and `a <_Q c`.
- **Family.** `F(P) := \{S(Q) : Q \in \mathcal{Q}(P)\} \subseteq 2^U`. Note: `F(P)` is the set of *distinct* `S(Q)` values, not the indexed family. Multiple `Q`'s may collapse to the same `S(Q)`.

### 1.2 The contradiction structure

The program's contradiction is a four-link chain:

(C1) Frankl-Holds applied to `F(P)` → `\exists A^* \in U : |\{S \in F(P) : A^* \in S\}| \ge |F(P)| / 2`.

(C2) Measure transfer (L3) → `\Pr_{L \sim \mathrm{Unif}(\mathcal{L}(P))}[\sigma_L|_{A^*} = \text{canonical order of } A^*] \ge 1/2`.

(C3) Entropy bound (Step 7) → `H(\sigma_L|_{A^*}) \le 1 + \tfrac{1}{2}\log_2 5`.

(C4) Local-ERZ lower bound (L4) → `H(\sigma_L|_{A^*}) > \log_2 6 - \log_2(4/3) = \log_2(9/2) \approx 2.170`.

(C3) and (C4) are incompatible: `2.161 < 2.170`. Contradiction.

For (C1) we need `F(P)` union-closed and non-empty (= L2; non-empty is trivial: `S(P)` is a valid member, possibly the empty set). For (C2) we need the transfer lemma (= L3). For (C4) we need the local form of ERZ (= L4) — global ERZ does not suffice (§3.4).

### 1.3 What the program does NOT assume

For clarity, the program does **not** require:

- A specific representative of Frankl-Holds — any form `F` union-closed `\Rightarrow \exists x : |F_x|/|F| \ge 1/2` works (UC13+UC14 chain delivers this).
- A specific form of ERZ — but `\Delta_{\mathrm{ERZ}} = \log_2(4/3)` must be the right per-antichain compatibility allowance, *interpreted as a lower bound on per-antichain entropy in a minimal counterexample* (= L4's local-form statement).
- Width-3 in general — but Daniel's note "at least in width-3 / minimal-counterexample setting" hints that the natural beachhead is `\mathrm{width}(P) = 3`, where 3-antichains have cleanest geometry.

---

## §2. Phase A — Numerical-constant verification

### 2.1 The canonical-frequency entropy deficit `\Delta_{\mathrm{can}}`

**Setup.** Let `\sigma` be a `\{1, 2, 3, 4, 5, 6\}`-valued random variable (representing the 6 possible relative orders of a 3-antichain in a linear extension). Suppose `\Pr[\sigma = 1] \ge 1/2` (WLOG label the canonical order as outcome 1). The entropy `H(\sigma)` is maximised under this constraint by:

- `\Pr[\sigma = 1] = 1/2` exactly (relaxing toward `1/6` increases entropy by concavity, but `1/6 < 1/2` violates the constraint).
- `\Pr[\sigma = i] = 1/10` for `i = 2, \ldots, 6` (uniform among non-canonical outcomes maximises their entropy contribution).

So:

$$H_{\max}(\sigma \mid \Pr[\sigma = 1] \ge 1/2) \;=\; -\tfrac{1}{2}\log_2\tfrac{1}{2} - 5 \cdot \tfrac{1}{10}\log_2\tfrac{1}{10} \;=\; \tfrac{1}{2} + \tfrac{1}{2}\log_2 10. \tag{2.1.1}$$

Using `\log_2 10 = 1 + \log_2 5`:

$$H_{\max} \;=\; \tfrac{1}{2} + \tfrac{1}{2}(1 + \log_2 5) \;=\; 1 + \tfrac{1}{2}\log_2 5. \tag{2.1.2}$$

**Numerical value.** `\log_2 5 = 2.3219280948\ldots`, so `H_{\max} = 1 + 1.1609640474\ldots = 2.1609640474\ldots` bits.

**Uniform-baseline entropy.** `\log_2 6 = \log_2 2 + \log_2 3 = 1 + 1.5849625007\ldots = 2.5849625007\ldots` bits.

**Deficit.**

$$\boxed{\Delta_{\mathrm{can}} \;:=\; \log_2 6 - H_{\max} \;=\; 0.4239984533\ldots \;\approx\; 0.42400 \text{ bits.}} \tag{2.1.3}$$

This matches Daniel's quoted `\approx 0.424`. **Verification: GREEN, to 5 decimal places.**

### 2.2 The ERZ compatibility allowance `\Delta_{\mathrm{ERZ}}` — *narrow* derivation

**Daniel's narrative.** "Naively, 3 binary pair orientations give `2^3 = 8` possible orientation patterns. But only `3! = 6` are transitive total orders. Therefore the compatibility penalty per 3-antichain is `\log_2(8/6) = \log_2(4/3) \approx 0.415` bits."

**Narrow arithmetic.**

$$\boxed{\Delta_{\mathrm{ERZ}} \;:=\; \log_2(4/3) \;=\; 2 - \log_2 3 \;=\; 0.4150374993\ldots \;\approx\; 0.41504 \text{ bits.}} \tag{2.2.1}$$

This matches Daniel's quoted `\approx 0.415`. **Verification: GREEN, to 5 decimal places.**

### 2.3 The gap

$$\boxed{\Delta_{\mathrm{can}} - \Delta_{\mathrm{ERZ}} \;=\; 0.4239984533 - 0.4150374993 \;=\; 0.0089609540 \;\approx\; 0.00896 \text{ bits.}} \tag{2.3.1}$$

The gap is positive (`\Delta_{\mathrm{can}} > \Delta_{\mathrm{ERZ}}`), so the program's contradiction is *non-vacuous arithmetically*. **Phase A GREEN.**

### 2.4 Robustness checks

#### 2.4.1 Robustness to *strengthening* canonical-frequency

If Frankl-Holds gave us `\Pr[\sigma = 1] \ge 1/2 + \varepsilon` for some `\varepsilon > 0` (stronger than 1/2), the max entropy would be achieved at `\Pr[\sigma = 1] = 1/2 + \varepsilon`, uniform `(1/2 - \varepsilon)/5` on others:

$$H_{\max}(\varepsilon) = -(\tfrac{1}{2} + \varepsilon)\log_2(\tfrac{1}{2} + \varepsilon) - 5 \cdot \tfrac{1/2 - \varepsilon}{5} \log_2 \tfrac{1/2 - \varepsilon}{5}.$$

Differentiating at `\varepsilon = 0` gives `\partial H / \partial \varepsilon = -\log_2(1/2) + \log_2((1/2)/5) = -(-1) + (-1 + \log_2(1/5)) = -\log_2 5 < 0`. So `H_{\max}` *decreases* as `\varepsilon` increases — the deficit `\Delta_{\mathrm{can}}(\varepsilon)` *widens*. **Sharper Frankl conclusions only help.**

#### 2.4.2 Brittleness to *weakening* canonical-frequency

Conversely, if the union-closure / measure-transfer chain only delivers `\Pr[\sigma = 1] \ge 1/2 - \varepsilon` for `\varepsilon > 0` (weaker than 1/2), then the constraint is not binding at the entropy-maximising point (which is uniform `\Pr[\sigma = i] = 1/6` for all `i`, giving `H = \log_2 6` and deficit zero). **The deficit collapses immediately for any weakening below 1/2.** The 1/2 threshold is a sharp cliff edge, not a smooth boundary.

**Consequence for L2 and L3:** the union-closure / measure-transfer pipeline must deliver *exactly* `\Pr \ge 1/2` (not `\Pr \ge 1/2 - o(1)`). This rules out asymptotic / probabilistic-amplification proofs of L2 or L3.

#### 2.4.3 Robustness to *sharpening* ERZ

If literature ERZ delivers a per-antichain allowance smaller than `\log_2(4/3)` (e.g., `\log_2(4/3) - \delta` for some `\delta > 0`), the gap widens: `\Delta_{\mathrm{can}} - (\Delta_{\mathrm{ERZ}} - \delta) = 0.00896 + \delta`. **Sharper ERZ only helps.**

#### 2.4.4 Brittleness to *weakening* ERZ

Conversely, if the literature ERZ allowance is *larger* than `\log_2(4/3)` (i.e., the "0.415" figure is itself a loose underestimate of the true allowance), the gap shrinks or vanishes. The 0.00896-bit gap is **too small to survive even a 1% increase in `\Delta_{\mathrm{ERZ}}`**: an ERZ allowance of `0.424` already closes the gap; `0.43` opens a *negative* gap (program fails).

**Phase-A consequence for L4:** the program is *especially* sensitive to L4's quantitative form. Daniel's `\log_2(4/3) \approx 0.415` is presented as if it were the standard ERZ allowance, but the literature ERZ-style bounds may have different forms (with different constants). L4 scoping must identify the *exact* form of the bound being invoked and verify the `\log_2(4/3)` figure is sharp.

### 2.5 Structural reading of `\Delta_{\mathrm{ERZ}}`

The arithmetic `\Delta_{\mathrm{ERZ}} = \log_2(4/3) = \log_2 8 - \log_2 6` is tautological at the surface — it's just the ratio of "naive 3-bit pair-orientation count" to "actual 6 transitive total orders". The *structural* interpretation as an "ERZ allowance" requires one of:

- **(SR-i) Local ERZ reading.** For every 3-antichain `A` in a minimal counterexample, `H(\sigma_A) \ge \log_2 6 - \log_2(4/3) = \log_2(9/2) \approx 2.170` bits. This is what L4 (Lemma C in Daniel's in-text labelling, Step 9 statement) requires.
- **(SR-ii) Global ERZ reading.** Averaged over 3-antichains, `\mathbb{E}_A H(\sigma_A) \ge \log_2(9/2)`. This is what most ERZ-style results in the literature (Kahn-Saks 1984; Brightwell-Tetali 2003; Friedman 1993) deliver.
- **(SR-iii) Tautological reading.** `\log_2(4/3)` is just an arithmetic identity with no bound-statement content. In this case, the "contradiction" of (C3) vs (C4) is empty: a single 3-antichain's entropy can be anything in `[0, \log_2 6]`, and 2.161 is in this range — no contradiction.

The program requires **(SR-i)**. (SR-ii) does not deliver a single-antichain contradiction; (SR-iii) is empty. L4 scoping must verify (SR-i) is the right reading, derive it (if novel) or cite it (if literature), and confirm the `\log_2(4/3)` constant is sharp.

### 2.6 Phase A summary

- **Numerical constants verify exactly to 5 decimals.** Gap `\approx 0.00896` bits is real.
- **Robust to sharpening** (Frankl tighter than 1/2, ERZ tighter than `\log_2(4/3)`): gap widens.
- **Brittle to weakening** (Frankl weaker than 1/2: gap collapses immediately; ERZ allowance larger than `\log_2(4/3)`: gap shrinks linearly).
- **Structural reading**: program requires local-ERZ reading (SR-i); global-ERZ reading does not suffice; tautological reading is empty.
- **Phase A verdict: GREEN-arithmetic, but flags two robustness concerns that bind on L2/L3 (must deliver exactly `\ge 1/2`, not asymptotic) and on L4 (must deliver local ERZ, with `\log_2(4/3)` sharp).**

---

## §3. Phase B — Tractability survey on Lemmas L1–L4

### 3.1 L1 — Local Acyclicity of `\ll` on 3-antichains

**Statement.** For minimal counterexample `P` and every 3-antichain `A = \{a, b, c\}` of `P`, the relation `\ll` has no directed cycle on `A`.

**Tractability: GREEN. The lemma admits an 8-line proof, given below.**

#### 3.1.1 The proof

Suppose for contradiction `\ll` has a cycle on `\{a, b, c\}`, say `a \ll b \ll c \ll a`. By definition of `\ll`:

$$\Pr_L[a < b] > 2/3, \quad \Pr_L[b < c] > 2/3, \quad \Pr_L[c < a] > 2/3. \tag{3.1.1}$$

Summing:

$$\Pr_L[a < b] + \Pr_L[b < c] + \Pr_L[c < a] > 2. \tag{3.1.2}$$

But this sum is bounded:

$$\Pr_L[a < b] + \Pr_L[b < c] + \Pr_L[c < a] \le 2. \tag{3.1.3}$$

(Proof of (3.1.3): for any linear extension `L`, the indicators `\mathbb{1}[a <_L b], \mathbb{1}[b <_L c], \mathbb{1}[c <_L a]` form one of the six possible relative orders of `\{a, b, c\}` in `L`. By case enumeration:

| Order | `\mathbb{1}[a<b]` | `\mathbb{1}[b<c]` | `\mathbb{1}[c<a]` | Sum |
|---|---|---|---|---|
| `a < b < c` | 1 | 1 | 0 | 2 |
| `a < c < b` | 1 | 0 | 0 | 1 |
| `b < a < c` | 0 | 1 | 0 | 1 |
| `b < c < a` | 0 | 1 | 1 | 2 |
| `c < a < b` | 1 | 0 | 1 | 2 |
| `c < b < a` | 0 | 0 | 1 | 1 |

Every row sums to 1 or 2, with maximum 2. So the per-`L` sum is `\le 2` always; taking expectation `\le 2`.)

Combining (3.1.2) and (3.1.3): `2 < 2`, contradiction. So `\ll` has no cycle on `\{a, b, c\}`. `\square`

#### 3.1.2 Observations

- The proof does **not** use minimality of `P` beyond the strict-bias `>2/3` (Step 1 setup).
- The proof works for *any* poset where every pair on the 3-antichain has `\Pr > 2/3` for some orientation. Minimality enters only via Step 1, which guarantees strict bias.
- The bound `\le 2` is sharp: achieved on the three "cyclic" orders `abc, bca, cab`, each contributing exactly 2 to the sum.
- The same argument generalises to `k`-antichains: `\Pr[\text{cyclic chain of length } k] > 2/3 \cdot k`, but pairwise sum on `k` cyclic pairs is bounded by `k - 1` (each ordering contributes at most `k-1` "agreeing" pairs out of `k` directed edges). So acyclicity follows from strict bias whenever `(k-1) > 2k/3` ⟺ `k > 3`. For `k = 3`: `(k-1) = 2 < 2k/3 = 2`, *just* equal — but `>` is strict so the argument works as shown. For `k = 4`: `(k-1) = 3 > 8/3 \approx 2.67`, works comfortably. For `k = 5`: `4 > 10/3`, works. **So L1 generalises trivially to all `k \ge 3`.** This is a free bonus not needed for the program but worth noting.

#### 3.1.3 What L1 does NOT establish

- L1 says `\ll` is *acyclic* on each 3-antichain. It does **not** say `\ll` is transitive on the full set `\mathcal{P}(P)` — there could be 4-antichains where `\ll` is acyclic on every 3-subset but not transitive on the whole 4-set (e.g., a single 4-cycle `a \ll b \ll c \ll d \ll a` with all 3-subsets acyclic).
- L1 says nothing about whether the canonical order of a 3-antichain `A` is realised by *any* given extension `Q` — that's a separate Step-3-onwards question.

#### 3.1.4 Tractability verdict for L1

**GREEN. Inline in F32 execution doc; no separate sub-ticket needed.** Budget: ~50k tokens to formalise (with explicit verification of the case table and the strict-vs-non-strict edge case at `k = 3`).

**Failure mode:** none within the program's framing. The proof depends only on Step 1's strict-bias setup; if Step 1 fails (i.e., minimal counterexample admits some pair with `\Pr \in [1/3, 2/3]`), then `\ll` is not defined on that pair and the bridge program needs separate handling — but that's a Step 1 failure, not an L1 failure.

### 3.2 L2 — Union-Closure of `F(P)`

**Statement.** `F(P) = \{S(Q) : Q \ge P\}` is union-closed: for every `S(Q_1), S(Q_2) \in F(P)`, there exists `Q_3 \ge P` with `S(Q_3) = S(Q_1) \cup S(Q_2)`.

**Tractability: AMBER. Multi-session; structurally hardest of the four lemmas.**

#### 3.2.1 The natural-candidate failure

The natural candidate is `Q_3 = Q_1 \vee Q_2 := \mathrm{TransitiveClosure}(Q_1 \cup Q_2)` (transitive closure of the union of relations). Two questions:

- **(Q-easy) `S(Q_1) \cup S(Q_2) \subseteq S(Q_1 \vee Q_2)`?** Yes: if `A \in S(Q_i)` for either `i`, then `Q_i` contains the canonical comparabilities of `A`, hence so does `Q_1 \vee Q_2 \supseteq Q_i`.
- **(Q-hard) `S(Q_1 \vee Q_2) \subseteq S(Q_1) \cup S(Q_2)`?** **No, in general.** Counterexample sketch: take `A = \{a, b, c\}` with canonical order `a \ll b \ll c`. Suppose `Q_1` contains `a < b` but neither `b < c` nor `a < c`; `Q_2` contains `b < c` but neither `a < b` nor `a < c`. Then `A \notin S(Q_1)` and `A \notin S(Q_2)`. But `Q_1 \vee Q_2` contains `a < b` and `b < c`, hence transitively `a < c`, so `A \in S(Q_1 \vee Q_2)`. The natural-candidate union creates an extra canonical triple.

So `F(P)` is **not** union-closed under the natural join. Daniel's Step 4 calls this the "hard part" and lists four candidate fixes:

- **L2-A.** Prove no extra canonical triples are created in a minimal counterexample.
- **L2-B.** Restrict to `\ll`-consistent extensions `Q`.
- **L2-C.** Representation lemma: even if the join creates extras, `\exists Q_3 \ge P` with `S(Q_3) = S(Q_1) \cup S(Q_2)`.
- **L2-D.** Work with the upward closure of `F(P)` and show it still corresponds to valid extensions for purposes of the argument.

#### 3.2.2 Per-candidate analysis

**L2-A (no extras in minimal counterexample).** The claim: for `P` minimal, the natural join `Q_1 \vee Q_2` does not create extra canonical triples beyond `S(Q_1) \cup S(Q_2)`.

- *Plausibility:* Minimality of `P` might enforce some sparsity in canonical-triple creation. But the counterexample mechanism in §3.2.1 (single-edge `a < b` in `Q_1`, single-edge `b < c` in `Q_2`, transitive-closure creates `a < c`) is robust to minimality: it only requires the existence of a 3-antichain `\{a, b, c\}` with canonical order `a \ll b \ll c`, which is *exactly* what minimality + L1 *gives us*.
- *Verdict:* L2-A is **likely false in general** for minimal counterexamples. To salvage, would need a much stronger structural property of minimal counterexamples (e.g., "every 3-antichain has at most one pair in any extension where another pair is unresolved"). No evidence for such a property.
- *Tractability:* LOW. Computational falsification on small posets (n ≤ 5) is feasible.

**L2-B (`\ll`-consistent extensions).** The claim: restrict `F(P) := \{S(Q) : Q \ge P, Q \text{ is `\ll`-consistent}\}` (i.e., for every incomparable pair `x \| y` of `P` resolved in `Q`, the resolution direction matches `\ll`). Then `F(P)` is union-closed.

- *Plausibility:* If `Q_1, Q_2` are both `\ll`-consistent, is `Q_1 \vee Q_2` also `\ll`-consistent? Not necessarily: transitive closure may force a comparability `x < y` that contradicts `y \ll x`. Concrete: `Q_1` has `a < b` (matches `a \ll b`); `Q_2` has `b < c` (matches `b \ll c`); `Q_1 \vee Q_2` has `a < c` transitively. If the canonical order of `\{a, b, c\}` were `a \ll c \ll b` instead (different from what we assumed in §3.2.1), then `a < c` is `\ll`-consistent but `b < c` from `Q_2` violates `c \ll b`. Wait, we assumed `Q_2` has `b < c` matching `b \ll c`; the inconsistency arises from `Q_2`'s edge, not from the closure. So `Q_2` was already inconsistent in this scenario.
- Let's redo: `Q_1` consistent means all its non-`P` edges match `\ll`. `Q_2` likewise. The transitive-closure question: can `Q_1 \vee Q_2` introduce an edge `x < y` where `y \ll x` is canonical? This requires `x < z < y` chain via `Q_1 \cup Q_2` edges. If all edges in `Q_1, Q_2` match `\ll`, then `x \ll z \ll y` along the chain. So `x \ll y` is canonical by acyclicity of `\ll` (which is L1 on the triple `\{x, y, z\}`) AND transitivity of `\ll`. **But L1 only gives acyclicity on each 3-antichain, not transitivity across the full poset.** So `x \ll z \ll y` does not force `x \ll y`; we could have `y \ll x` canonically, and the closure-edge `x < y` would be `\ll`-inconsistent.
- *Conclusion:* L2-B union-closure depends on **transitivity of `\ll`** (a stronger property than L1 acyclicity). If `\ll` is transitive on `\mathcal{P}(P)` (i.e., a total order on the antichain set), then L2-B works. **Question:** is `\ll` transitive in minimal counterexamples? Not in general — `\ll` is defined pairwise from probabilities; transitivity is a global constraint not directly forced by minimality.
- *Tractability:* MEDIUM-LOW. Needs an auxiliary lemma "`\ll` is transitive on incomparable-pair set in minimal counterexamples" (call this L1+). L1+ is plausible (probabilistic transitivity-like results exist) but non-trivial.
- *Cross-program note:* if L1+ holds, the bridge program could simplify dramatically — `\ll` total on `\mathcal{P}(P)` defines a unique global canonical refinement `Q^* \ge P`, and the entire union-closure machinery might be unnecessary. **L1+ exploration is a worthy fork.**

**L2-C (representation lemma).** The claim: for every `S(Q_1), S(Q_2) \in F(P)`, there exists `Q_3 \ge P` (not necessarily `Q_1 \vee Q_2`) with `S(Q_3) = S(Q_1) \cup S(Q_2)` exactly.

- *Plausibility:* This is a *realisability* question: given a target set `T = S(Q_1) \cup S(Q_2) \subseteq U`, construct an extension `Q_3 \ge P` whose canonical-triple set is exactly `T`. Realisability is harder than it sounds — we need `Q_3` to contain canonical comparabilities for all `A \in T` *and* fail to contain at least one canonical comparability for every `A \notin T`.
- *Tractability:* MEDIUM. Realisability questions for extension-poset families have been studied in the order-theory literature (e.g., Aigner, Brightwell-Trotter work). Specific to `\ll`-canonical-triples, no off-the-shelf result; would need custom construction.
- *Concrete construction sketch.* Start with `Q_3 := P`. For each `A \in T` with canonical order `a \ll b \ll c`, add the comparabilities `a < b, b < c, a < c` to `Q_3` (taking transitive closure). The resulting `Q_3` contains all canonical comparabilities for `A \in T`. But: the transitive closure may add comparabilities forcing `A' \in S(Q_3)` for some `A' \notin T`. Need to verify: can we always *block* `A' \notin T` from becoming canonical, by judicious choice of construction?
- *Verdict:* L2-C is the **cleanest candidate** but requires explicit realisability proof. Multi-session, ~400-600k tokens.

**L2-D (upward closure).** The claim: replace `F(P)` with its upward closure `\widehat F(P) := \{S \subseteq U : S \supseteq S(Q_1) \cup \ldots \cup S(Q_k) \text{ for some } Q_1, \ldots, Q_k \ge P\}` (the smallest union-closed family containing `F(P)`). UCC applies to `\widehat F(P)`; some `A^*` is `\ge 1/2`-frequent in `\widehat F(P)`. Translate back to a statement about `F(P)`.

- *Plausibility:* Replacing `F(P)` by its upward closure is always valid (any superfamily is union-closed if the original is, and `\widehat F(P)` is the union-closed completion). UCC gives `\exists A^* : |\widehat F(P)_{A^*}| / |\widehat F(P)| \ge 1/2`.
- *The catch:* "uniform over `\widehat F(P)`" is not the same as "uniform over `F(P)`". `\widehat F(P)` is exponentially larger than `F(P)` (it includes all unions of arbitrary subcollections), so `A^*` being frequent in `\widehat F(P)` does not imply `A^*` is frequent in `F(P)`.
- *Bridge to L3:* If we use a weighted-UCC version (weight `w(\widehat S) = |\{(Q_1, \ldots, Q_k) : S(Q_1) \cup \ldots \cup S(Q_k) = \widehat S\}|` or similar), we might be able to relate the `\widehat F(P)`-frequency back to the `F(P)`-frequency. **This couples L2 with L3.**
- *Verdict:* L2-D is most natural as **L2-D + L3-B combined**. The combined lemma is "weighted UCC on (union-closed completion of `F(P)`) gives `\Pr_L \ge 1/2`-frequent antichain". Cleanly formal but requires weighted-UCC strengthening of Frankl-Holds. Multi-session, ~500-800k tokens.

#### 3.2.3 L2 verdict

- L2-A: **likely false in minimal counterexamples**; not viable.
- L2-B: viable iff L1+ (transitivity of `\ll`) holds; L1+ is a non-trivial auxiliary lemma. **Conditional viability.**
- L2-C: **cleanest standalone candidate**; requires explicit realisability proof. ~400-600k.
- L2-D: requires combining with L3-B (weighted UCC). ~500-800k for the combined lemma.

**Best L2 path:** L2-C (representation) if a clean construction can be found; else L2-B + L1+ (transitivity); else L2-D + L3-B (combined).

**Tractability verdict:** **AMBER, multi-session, 400-800k tokens depending on candidate.** Failure mode: all four candidates wall, program needs a different `F(P)` definition (e.g., restrict to 3-antichains satisfying additional hypotheses, or use a different combinatorial object).

### 3.3 L3 — Measure Transfer `\Pr_Q \to \Pr_L`

**Statement.** Given some `A^* \in U` is `\ge 1/2`-frequent in `F(P)` (under uniform-over-distinct-`S(Q)` measure), conclude `A^*` is `\ge 1/2`-frequent in `\mathcal{L}(P)` under canonical-order matching: `\Pr_{L \sim \mathrm{Unif}(\mathcal{L}(P))}[\sigma_L|_{A^*} = \text{canonical order}] \ge 1/2`.

**Tractability: AMBER. The most uncertain of the four; cross-repo dependency makes it the highest-risk lemma.**

Daniel: "the most important technical gap after union-closure". Three candidate approaches: L3-A direct, L3-B weighted-UCC, L3-C injection.

#### 3.3.1 L3-A (direct) — DEAD

**Claim:** `\Pr_{S \in F(P)}[A \in S] \ge 1/2 \Rightarrow \Pr_{L \in \mathcal{L}(P)}[\sigma_L|_A = \text{canonical}] \ge 1/2`.

**Counterexample.** Take `P` with `|\mathcal{Q}(P)| = 2` extensions: `Q_1 = P` (trivial extension) and `Q_2 = P + \text{(all canonical-triple edges for some single } A^*)`. Suppose `A^* \in S(Q_2)` but `A^* \notin S(Q_1)` (because `P` itself does not contain all of `A^*`'s canonical comparabilities). Then `|F(P)| = 2` and `|F(P)_{A^*}| = 1`, so `\Pr_S[A^* \in S] = 1/2` exactly. But `\mathcal{L}(P)` might have, say, 720 linear extensions with `A^*` canonical in only 100 of them (proportion `\approx 0.14 \ll 0.5`).

The asymmetry: `F(P)` counts *distinct extension shapes*; `\mathcal{L}(P)` counts *linear extensions* (which weight extensions by their respective extension-counts). A "small" `Q` with few linear extensions counts equally to a "large" `Q` with many linear extensions in `F(P)`, but not in `\mathcal{L}(P)`.

**Verdict:** L3-A is **false** as stated. **Not viable.**

#### 3.3.2 L3-B (weighted UCC) — load-bearing, requires UC-side strengthening

**Claim:** Frankl-Holds extends to a weighted form. For any union-closed family `F` over universe `U` with positive real weights `w: F \to \mathbb{R}_{>0}`, there exists `x \in U` with

$$\sum_{S \in F : x \in S} w(S) \;\ge\; \tfrac{1}{2} \sum_{S \in F} w(S). \tag{3.3.2.1}$$

If (3.3.2.1) holds, apply it to `F(P)` with weights `w(S(Q)) := \sum_{Q' : S(Q') = S(Q)} e(Q')` (the total number of linear extensions over all `Q'` collapsing to the same `S(Q)`). Then weighted-frequency of `A^*` in `F(P)` equals:

$$\frac{\sum_{Q : A^* \in S(Q)} e(Q)}{\sum_Q e(Q)}. \tag{3.3.2.2}$$

**Question 1.** Does (3.3.2.2) equal `\Pr_L[\sigma_L|_{A^*} = \text{canonical}]`?

**Answer.** Not directly. Compute the denominator:

$$\sum_Q e(Q) \;=\; \sum_Q |\{L \in \mathcal{L}(P) : L \ge Q\}| \;=\; \sum_{L \in \mathcal{L}(P)} |\{Q : P \le Q \le L\}|. \tag{3.3.2.3}$$

The inner cardinality `|\{Q : P \le Q \le L\}|` is the number of poset extensions of `P` contained in `L`. This depends on `L` in general (each `L` has a different "interval of `Q`'s below it" depending on which `P`-comparabilities `L` extends).

If we assume — as is roughly the case for minimal counterexamples — that `|\{Q : P \le Q \le L\}|` is constant over `L`, equal to `2^{k}` where `k = \binom{n}{2} - |P|` is the number of incomparable pairs in `P`, then:

$$\sum_Q e(Q) \;=\; |\mathcal{L}(P)| \cdot 2^k. \tag{3.3.2.4}$$

Similarly the numerator: `\sum_{Q : A^* \in S(Q)} e(Q) = \sum_L \mathbb{1}[\sigma_L|_{A^*} = \text{canonical}] \cdot |\{Q : P \cup \text{(canonical edges of } A^*\text{)} \le Q \le L\}|`. The inner cardinality is `2^{k - 3}` if `L` extends `A^*` canonically (with 3 of the `k` pair-orientations fixed by canonical `A^*`), else 0. So:

$$\sum_{Q : A^* \in S(Q)} e(Q) \;=\; |\{L : \sigma_L|_{A^*} = \text{can}\}| \cdot 2^{k-3}. \tag{3.3.2.5}$$

Dividing:

$$\frac{\sum_{Q : A^* \in S(Q)} e(Q)}{\sum_Q e(Q)} \;=\; \frac{|\{L : \sigma_L|_{A^*} = \text{can}\}|}{|\mathcal{L}(P)|} \cdot \frac{2^{k-3}}{2^k} \;=\; \tfrac{1}{8} \Pr_L[\sigma_L|_{A^*} = \text{can}]. \tag{3.3.2.6}$$

So weighted-`F(P)`-frequency `\ge 1/2` translates to `\Pr_L[\text{canonical}] \ge 4` — **impossible** (probabilities are `\le 1`). The factor `1/8` *kills* the transfer.

**Wait — there's a subtlety in the weight choice.** The weight `w(S(Q)) := \sum_{Q' : S(Q') = S(Q)} e(Q')` sums `e(Q')` over all `Q'`'s collapsing to the same `S` value — *not* just `e(Q)`. The collapsing is non-trivial; the correction factor isn't simply `1/8`.

**Corrected calculation.** Let `F(P)` have distinct elements `S_1, S_2, \ldots, S_m` (one per distinct `S(Q)` value). Let `\mathcal{Q}_i := \{Q : S(Q) = S_i\}`. Weights: `w(S_i) = \sum_{Q \in \mathcal{Q}_i} e(Q)`. Total weight: `\sum_i w(S_i) = \sum_Q e(Q)` (as before). Weighted-frequency of `A` in `F(P)`: `\sum_{i : A \in S_i} w(S_i) / \sum_i w(S_i) = \sum_{Q : A \in S(Q)} e(Q) / \sum_Q e(Q)`.

So the calculation (3.3.2.6) stands. The factor `1/8` arises from the *over-counting of `Q`'s per `L`*: each linear extension `L` corresponds to `2^k` poset extensions `Q \le L`, but only `2^{k-3}` of those `Q`'s contain the canonical-`A^*` edges.

**This is a real problem.** Even with weighted UCC delivering `\ge 1/2` weighted frequency, the translation to `\Pr_L` gives `\ge 4`, which is vacuous (always false).

**Where the program goes wrong.** Daniel's program assumes the weighted-UCC conclusion translates "directly" to `\Pr_L`. The translation should be: `\Pr_Q[A \in S(Q) \mid Q \in \mathcal{Q}(P), Q \text{ weighted by } e(Q)] \ge 1/2`. This IS `\sum_{Q : A \in S(Q)} e(Q) / \sum_Q e(Q)`. Re-checking: this quantity equals `\sum_L \mathbb{1}[\sigma_L|_A = \text{can}] \cdot (2^{k-3}) / \sum_L 2^k = (1/8) \Pr_L[\sigma_L|_A = \text{can}]`.

So `\Pr_Q^{\text{weighted}}[A \in S(Q)] = (1/8) \Pr_L[\sigma_L|_A = \text{can}]`. Weighted UCC `\ge 1/2` on `F(P)` gives `(1/8) \Pr_L \ge 1/2`, i.e., `\Pr_L \ge 4`. Vacuous.

#### 3.3.3 The L3-B obstruction is structural, not a calculation error

The 1/8 factor is unavoidable: it comes from the fact that for each `L`, only `2^{k-3}` out of `2^k` poset-extensions `Q \le L` contain the canonical edges of a *specific* `A^*`. Weighting by `e(Q)` over-counts `L`'s by `2^k`, but the relevant `Q`'s are over-counted by only `2^{k-3}`.

**To avoid the 1/8 factor, the weighting must be different.** Candidate weightings:

- **w(Q) = 1** (uniform over `Q`): gives unweighted UCC, which Frankl delivers, but maps to `(\text{frequency in } Q) / |\mathcal{Q}(P)|` — not directly to `\Pr_L`.
- **w(Q) = e(Q) / 2^{k(Q)}**: normalises by extension-count of `Q` itself, but this is `\le 1` and doesn't give the right transfer either.
- **w(Q) = 2^{(k - k(Q))}**: weight inversely by "how many edges `Q` has added beyond `P`". Unclear interpretation.

**No natural weighting** seems to make the weighted-UCC conclusion translate to `\Pr_L \ge 1/2`. The transfer L3-B has a structural obstruction.

#### 3.3.4 L3-C (injection) — open

**Claim:** Construct an injection `\iota: \{L : \sigma_L|_{A^*} \ne \text{can}\} \hookrightarrow \{L : \sigma_L|_{A^*} = \text{can}\}` for some `A^*` provided by Frankl-Holds. If such an injection exists, the canonical-fraction is `\ge 1/2` directly.

- *Tractability:* MEDIUM. Injection constructions for poset linear extensions exist in the literature (e.g., for the 1/3-2/3 conjecture itself in special cases via Brightwell-Tetali-style swap injections). But the injection here needs to be `A^*`-specific and aware of the Frankl-Holds output, which is a non-standard combinatorial setup.
- *Cleanness:* If a clean injection exists, it bypasses the 1/8 obstruction in 3.3.3. But "if" is doing a lot of work.
- *Verdict:* L3-C is **structurally cleanest** if it works, but its existence is an open question.

#### 3.3.5 L3 verdict

- L3-A: **dead** (counterexample in 3.3.1).
- L3-B: **structurally obstructed** by the 1/8 factor (3.3.3); the natural weighting `w(Q) = e(Q)` doesn't translate weighted-UCC to `\Pr_L`. **Salvage requires either a different weighting or a fundamentally different approach.**
- L3-C: **open**; potentially cleanest but no concrete construction.

**Tractability verdict:** **AMBER, with high failure-risk.** Cross-repo dependency: any salvage of L3-B requires a UC-side strengthening of Frankl-Holds beyond what UC13+UC14 deliver, which would mean filing a new union_closed sub-ticket. Even with such a strengthening, the 1/8 obstruction may persist.

**Best L3 path:** investigate L3-C (injection) first, since it bypasses the weighted-UCC obstruction. ~400-600k for an injection-construction attempt. If L3-C walls, escalate to L3-B salvage attempts (~600-1000k including a UC-side ticket).

**Failure mode:** L3 walls entirely; program breaks at Step 6.

### 3.4 L4 — ERZ Entropy Contradiction

**Statement (local form, Daniel's Lemma C).** In a minimal counterexample `P`, every 3-antichain `A` has `H(\sigma_L|_A) > 1 + \tfrac{1}{2}\log_2 5 \approx 2.161` bits.

**Statement (global form, Daniel's Lemma C').** Total extension-count lower bound forces *average* 3-antichain entropy loss `\le \log_2(4/3)`, so a single canonical triple with entropy deficit `> \log_2(4/3)` is impossible *in the minimal/critical case*.

**Tractability: AMBER, with the local-vs-global question UNRESOLVED.**

#### 3.4.1 What standard ERZ-style bounds deliver

The literature on entropy bounds for linear extensions includes:

- **Kahn-Saks (1984)** "Balancing poset extensions". Proves `H(\sigma_L) \ge ` linear-in-`n` bounds via entropy compression arguments.
- **Brightwell-Tetali (2003)** "The 1/3-2/3 conjecture". Uses entropy-style arguments for 1/3-2/3 in specific classes.
- **Friedman (1993)** "A note on poset geometries". Entropy bounds for linear extensions.
- **Various surveys (Brightwell, Bollobas).** Standard reference for entropy compression in posets.

The form of these bounds is typically **global / averaged**: a bound on `\log_2 |\mathcal{L}(P)| = H_{\text{linear-extension}}(L)` in terms of sums of marginal entropies. For instance:

$$H(L) \;=\; \sum_{i=1}^n H(\text{position of } x_i \mid \text{positions of } x_1, \ldots, x_{i-1}) \;\le\; \sum_{\text{antichains}} (\text{antichain entropy}) - (\text{compatibility correction}). \tag{3.4.1.1}$$

This is **global**: it constrains the *sum* of per-antichain entropies, not individual ones.

#### 3.4.2 Why local-form L4 is non-standard

The local form claims: for *every* 3-antichain `A`, individually, `H(\sigma_L|_A) > 2.161`. This is much stronger than the global form: it forbids any single 3-antichain from being concentrated.

**Why this is non-standard.** Consider a generic poset `P` with a "near-trivial" 3-antichain (e.g., `\{a, b, c\}` where `\Pr_L[a < b < c] = 0.9` because `P` already has near-rigid structure on `\{a, b, c\}` from contexts elsewhere). Then `H(\sigma_L|_{\{a,b,c\}}) \approx -0.9 \log 0.9 - 0.1 \cdot (0.1/5)... \approx ` very low. The local-form L4 would forbid this — which seems too strong.

**The minimality saving.** L4-local doesn't claim this for all posets — only for *minimal* counterexamples. The hope: minimality forces every 3-antichain to be "balanced enough" that no single antichain can concentrate at `\ge 1/2` on one outcome. **But this is essentially the 1/3-2/3 conjecture at the triple level**, which is *exactly what we're trying to prove*. **Circular.**

#### 3.4.3 Non-circular reading

The non-circular reading: L4-local is **not** a consequence of minimality alone. It's a separate combinatorial-entropic lemma. The proof would need to argue: in any poset where *some* 3-antichain has canonical concentration `\ge 1/2`, you can construct a sub-poset that contradicts minimality (e.g., a sub-counterexample to 1/3-2/3 on a smaller element set). This is a *reduction* argument, not direct.

**Tractability of the reduction argument.** Open. The reduction would need:

- "Sub-poset" technique: identify a witness sub-poset `P' \subset P` whose 1/3-2/3 status is determined by `\sigma_{A^*}` concentration.
- "Counterexample transfer": show `P'` is also a counterexample.
- "Element-count strict decrease": `|P'| < |P|`, contradicting minimality.

Each step is non-trivial. The combinatorial intuition: a 3-antichain at `\Pr \ge 1/2` canonical implies some specific structural property of `P` (e.g., one pair of `A^*` is "almost determined" by the others), which might be projectable onto a smaller counterexample. But formalising is open.

#### 3.4.4 Global-form fallback

If local-form L4 fails (or is too hard), the program reformulates with global ERZ:

- **(GR-1)** Frankl-Holds + L2 + L3 deliver: ONE 3-antichain `A^*` has canonical-concentration `\ge 1/2`.
- **(GR-2)** Global ERZ delivers: average per-antichain entropy is `\ge 2.170` (averaged over all 3-antichains of `P`).
- **(GR-3)** *Reformulation needed:* if (GR-1) yielded MANY 3-antichains at concentration `\ge 1/2`, the average could be pulled below 2.170. So the reformulation is: "Frankl-Holds + L2 + L3 deliver `\ge (1 - \epsilon)` 3-antichains at concentration `\ge 1/2`", which combined with global-ERZ contradicts.

**Problem:** Frankl-Holds delivers *one* element at frequency `\ge 1/2`, not a positive-fraction-of-elements at frequency `\ge 1/2`. The reformulation requires a fundamentally stronger UCC-style result, e.g., "in any union-closed family, a positive fraction of elements is `\ge 1/2`-frequent". **This is much stronger than Frankl-Holds** and likely false in general (consider a union-closed family where one element is `\ge 1/2`-frequent and all others are `< 1/2`).

So the global-form fallback **does not save the program**. Either local-form L4 holds, or the program fails.

#### 3.4.5 The `\log_2(4/3)` constant

Where does `\log_2(4/3)` come from as the "ERZ per-antichain allowance"?

- **Source 1: tautological arithmetic.** `\log_2 8 - \log_2 6` is just the ratio of "naive 3-bit count" to "actual 6-outcome entropy". This has no bound-statement content.
- **Source 2: structural ERZ.** A specific theorem in some ERZ-style reference would deliver this constant. **Polecat could not identify a specific cited source for `\log_2(4/3)`** — Daniel's program presents it as if it's a known bound, but no citation is given. **This is a load-bearing gap in scoping.**
- **Source 3: derivable lower bound.** Possibly the bound `H(\sigma_L|_A) \ge \log_2 6 - \log_2(4/3) = \log_2(9/2)` can be derived from first principles for minimal counterexamples — but the derivation is precisely L4, which is open.

**L4 scoping is gated by identifying Source 2 (a literature citation) or proving Source 3 (a derivation).** Until that is done, the 0.415-bit allowance is suggestive arithmetic without a structural footing.

#### 3.4.6 L4 verdict

- **Local form (Lemma C)** is what the program needs. It is **non-standard, possibly circular without minimality, and requires either a literature citation (currently unidentified) or a novel reduction argument.**
- **Global form (Lemma C')** does not save the program.
- The `\log_2(4/3)` constant has no identified literature source; it may be tautological arithmetic.

**Tractability verdict:** **AMBER, with high failure-risk.** Two distinct concerns:

- (L4-α) Identify the literature ERZ form delivering the per-antichain bound. **Single-session, 100-200k tokens.** If no such form exists, immediately escalate to (L4-β).
- (L4-β) Derive a local-ERZ bound from scratch via a sub-poset reduction argument. **Multi-session, 400-800k tokens.** Failure mode: reduction doesn't work; program walls at L4.

**Failure mode:** L4 fails locally; program needs reformulation to "many canonical antichains" form; reformulation requires stronger-than-Frankl UCC result; result likely false; program fails.

### 3.5 Phase B summary

| Lemma | Status | Best path | Budget | Failure mode |
|---|---|---|---|---|
| L1 | **GREEN** | Inline proof (§3.1.1) | 50k | none |
| L2 | AMBER | L2-C representation OR L2-B + L1+ OR L2-D + L3-B | 400-800k | All four candidates wall |
| L3 | AMBER (high risk) | L3-C injection OR L3-B + UC-side strengthening (with 1/8-obstruction salvage) | 400-1000k | Structural 1/8-obstruction (3.3.3) persists |
| L4 | AMBER (high risk) | L4-α literature → L4-β derivation | 100-800k | Local form unavailable; global doesn't save |

**Two of four lemmas are high-risk.** L3 and L4 are *combined* in the sense that a failure of either walls the program — Phase D enumerates this.

---

## §4. Phase C — Attack-order proposal + budget

### 4.1 Refinement of Daniel's attack order

Daniel's "Likely Attack Order" section proposes:

1. Test Lemma A (L1) on small posets computationally.
2. Test whether `S(Q_1 \vee Q_2)` creates extra canonical triples.
3. If extra triples appear, search for a representation lemma or restrict the extension class.
4. Reformulate union-closed in weighted form to avoid measure mismatch.
5. Re-derive the ERZ inequality in entropy language and check whether it gives local or only average control.
6. Try to prove the entropy contradiction first in width 3.

Refined order (based on Phase B findings):

**Phase 0: Already done in this scoping doc.**

- (0.1) Phase A numerical-constant verification → DONE (§2). Gap `\approx 0.00896` bits, verified.
- (0.2) L1 essentially proved (§3.1.1). No separate sub-ticket needed; inline in F32 execution doc.
- (0.3) L2 natural-candidate failure verified (§3.2.1). Sub-tickets must work with the non-trivial four-candidate fix space.

**Phase 1: Parallel literature passes (run concurrently).**

- (1.1) **L4-α-lit.** Identify literature ERZ-style per-antichain bound, or prove no such bound exists. **Budget: 100-200k, single session.** Polecat outcome: GREEN (citation found, `\log_2(4/3)` sharp) → proceed to (3); AMBER (citation found but constant different) → re-verify Phase A with corrected constant; RED (no citation, no derivation in literature) → escalate to L4-β.
- (1.2) **L3-B-UC.** Cross-repo scoping ticket: does the UC13+UC14 mechanism extend to weighted UCC? File on union_closed side. **Budget: 200-300k, single session.** Polecat outcome: GREEN (weighted-UCC derivable) → still need to address 1/8-obstruction; AMBER (partial result) → proceed to L3-C; RED (weighted-UCC not derivable from current mechanism) → L3-B fully walled, escalate to L3-C.

**Phase 2: Conditional on Phase 1 outcomes.**

- (2.1) If L4-α RED: **L4-β-derive.** Attempt local-ERZ derivation via sub-poset reduction. **Budget: 400-800k, multi-session.** Polecat outcome: GREEN → L4 closed; RED → program walls at L4, no recovery.
- (2.2) If L3-B walls regardless of (1.2) outcome (due to 1/8-obstruction): **L3-C-injection.** Attempt direct injection construction. **Budget: 400-600k, multi-session.** Polecat outcome: GREEN → L3 closed; RED → L3 fully walled.

**Phase 3: Conditional on Phases 1-2.**

- (3.1) **L2-C-rep.** Representation-lemma construction. **Budget: 400-600k, multi-session.** Best to attempt only after L3 status (Phases 1.2 / 2.2) is known, to avoid wasted effort.
- (3.2) Alternative L2-B: if L2-C walls, attempt L2-B + L1+ (transitivity of `\ll`). **Budget: 400-600k.**

**Phase 4: Integration.**

- (4.1) **F32-final.** Assemble L1 (inline) + L2 + L3 + L4 into final contradiction proof, width-3 first then general-width. **Budget: 200-300k.**

### 4.2 Total budget estimate

| Phase | Sub-ticket | Budget |
|---|---|---|
| Phase 0 (this doc) | F32-scope | 400k (used) |
| Phase 1.1 | L4-α-lit | 100-200k |
| Phase 1.2 | L3-B-UC | 200-300k |
| Phase 2.1 (conditional) | L4-β-derive | 400-800k |
| Phase 2.2 (conditional) | L3-C-injection | 400-600k |
| Phase 3.1 | L2-C-rep | 400-600k |
| Phase 3.2 (alternative) | L2-B + L1+ | 400-600k |
| Phase 4 | F32-final | 200-300k |
| **Total (typical path: 1.1 + 1.2 + 2.2 + 3.1 + 4)** | | **1,300–2,400k** |
| **Total (worst case: all conditionals + alt L2)** | | **2,500–4,200k** |

The full program is **1.3M–2.4M tokens in the typical path, up to 4.2M tokens worst case**. This is a substantial commitment — comparable in scale to the UC10+UC12+UC11+UC13+UC14 Frankl-Holds chain (~3M tokens total for that program).

### 4.3 Execution sub-ticket recommendations — STRICT ORDER

**File these two sub-tickets first (before any L2 work):**

1. **L4-α-lit** (Phase 1.1): identify literature ERZ form. RED-outcome moots the entire program (no point in L2 work if L4 walls).
2. **L3-B-UC** (Phase 1.2): cross-repo weighted-UCC scoping on union_closed side. RED-outcome forces L3-C path; AMBER/GREEN provides clarity for L3 attack.

**Both sub-tickets are single-session, 100-300k each, total 300-500k for Phase 1.** They run **concurrently** (no dependency).

**Pause after Phase 1.** Evaluate outcomes:

- L4-α RED + L3-B RED: **program walled at gates**, **escalate to Daniel for redirection**.
- L4-α RED + L3-B GREEN: L4-β-derive (long, risky). L2 work blocked until L4 resolves.
- L4-α GREEN + L3-B RED: L3-C-injection (medium, risky). L2 work blocked until L3 resolves.
- L4-α GREEN + L3-B GREEN: proceed to L2-C-rep (Phase 3.1). Cleanest path.

**Do not file L2 sub-tickets before Phase 1 results.** The risk of wasted L2 work if L3 or L4 walls is too high (L2-C alone is 400-600k tokens).

### 4.4 Beachhead

Daniel's note: "at least in width-3 / minimal-counterexample setting". Beachhead choice:

- **Width-3 first.** All 3-antichains in a width-3 poset are *full antichains* (no element above all three), which simplifies the canonical-order construction and (potentially) sharpens the L4 reduction argument.
- **General width as follow-up.** If width-3 closes, generalisation to higher widths is a separate sub-program with its own scoping ticket. Generalisation may require new ideas (3-antichains in width-`w` posets carry more structure than in width-3).
- **Width-3 specialisation in F32 execution docs.** All sub-tickets (L1, L2, L3, L4) should default to width-3 unless explicitly noted otherwise.

---

## §5. Phase D — Failure modes + early-exit conditions

Ordered by likelihood (most likely first).

### 5.1 D.1 — L4 local form unavailable (highest likelihood)

**Failure description:** Literature search reveals no ERZ-style local bound on per-antichain entropy. Derivation attempt via sub-poset reduction (L4-β) fails or produces a weaker bound (e.g., 2.5 bits rather than 2.170 bits, which would not contradict 2.161).

**Detection:** Phase 1.1 (L4-α-lit, 100-200k). RED outcome detected after one session.

**Likelihood:** HIGH. Standard ERZ-style bounds are global; local bounds are uncommon. Even if a local bound exists, the constant `\log_2(4/3)` is not a widely-cited figure.

**Recovery / pivot:**

- (R-1) Attempt L4-β-derive (Phase 2.1) — long, risky. If successful, program continues. If unsuccessful, program walls at L4.
- (R-2) Reformulate program to "many canonical antichains" with a stronger UCC result. **As shown in §3.4.4, this requires stronger-than-Frankl UCC, which is likely false.** Not a viable recovery.
- (R-3) Restrict to even-narrower posets (e.g., width-2) where ERZ might be tractable. But the 1/3-2/3 conjecture is known for width-2 already; recovery is uninteresting.

**Outcome if no recovery:** program walls at L4. **F32 RED-L4.**

### 5.2 D.2 — L3 1/8-obstruction unresolvable (high likelihood)

**Failure description:** L3-B weighted-UCC, even if proven on UC side, suffers the 1/8 transfer factor (§3.3.3). L3-C injection attempt fails (no constructive injection found).

**Detection:** Phase 1.2 (L3-B-UC) and Phase 2.2 (L3-C). Both may take multiple sessions.

**Likelihood:** HIGH. The 1/8 factor in (3.3.2.6) is structural; no obvious alternative weighting addresses it. L3-C injection is an open problem with no obvious solution.

**Recovery / pivot:**

- (R-1) Find an alternative weight `w(Q)` that produces a clean transfer. As discussed in §3.3.3, no natural choice works. Long-shot.
- (R-2) Replace `F(P)` with a different combinatorial object whose UCC application directly maps to `\Pr_L`. E.g., `F^{lin}(P) = \{S(L) : L \in \mathcal{L}(P)\}` where `S(L) = \{A : \sigma_L|_A = \text{canonical}\}`. But `F^{lin}(P)` is **not union-closed** (the union of canonical-triple sets from two linear extensions is not generally a canonical-triple set of a third linear extension). Recovery fails.
- (R-3) Bypass Step 6 entirely with a direct argument: show some 3-antichain has `\Pr_L[\text{canonical}] \ge 1/2` without invoking UCC. But this would be a separate proof entirely, decoupled from the union-closed framework.

**Outcome if no recovery:** program walls at L3. **F32 RED-L3.**

### 5.3 D.3 — L2 has no clean fix-candidate (medium likelihood)

**Failure description:** L2-A (no extras) falsified on small posets; L2-B requires L1+ (transitivity of `\ll`), which is unproven; L2-C representation construction has unblockable extras; L2-D requires L3-B which is itself walling.

**Detection:** Phase 3.1 (L2-C-rep) attempt, after Phase 1-2 completes. Multi-session.

**Likelihood:** MEDIUM. L2-C is plausible but requires explicit construction; if all four candidates wall, the natural `F(P)` is *not* union-closed in a usable way.

**Recovery / pivot:**

- (R-1) Define a different `F(P)`: e.g., restrict to 3-antichains in width-3 layers, or 3-antichains satisfying a specific structural condition. Different family → different lemmas. Likely a separate scoping ticket (F33?).
- (R-2) Use a different combinatorial object than "canonical 3-antichains". E.g., 2-element chains (Frankl's classical setting). But this is essentially abandoning the bridge program.

**Outcome if no recovery:** program walls at L2. **F32 RED-L2.**

### 5.4 D.4 — Numerical gap evaporates (low likelihood, but high impact)

**Failure description:** Phase A re-derivation reveals an arithmetic error or sharper bound. E.g., the ERZ allowance is `\log_2(4/3) + \epsilon` for some literature-derived `\epsilon > 0.009`. Or the canonical-frequency deficit is sharper than 0.424 (impossible — we showed equality at p_can=1/2).

**Detection:** Phase 0 (this scoping doc, §2). **ALREADY DONE. Gap survives.** Could be re-triggered by Phase 1.1 (L4-α-lit) if the literature ERZ gives a different constant.

**Likelihood:** LOW (Phase A already verified). MEDIUM if Phase 1.1 reveals a literature constant different from `\log_2(4/3)`.

**Recovery:** if Phase 1.1 reveals ERZ allowance `> 0.424`, program is **dead**; immediate RED. No recovery.

**Outcome:** **F32 RED-Phase-A** (if triggered).

### 5.5 D.5 — Width-3 works but general-width doesn't (low likelihood, MEDIUM impact)

**Failure description:** L1, L2, L3, L4 all close in width-3 setting, but generalisation to width ≥ 4 introduces new obstacles (e.g., 3-antichains in width-4 posets have more structural constraints).

**Detection:** Phase 4 (F32-final) for width-3 closes, then general-width sub-ticket walls.

**Likelihood:** LOW (no immediate evidence). MEDIUM if width-3 closure reveals width-specific structures (e.g., L4 reduction depends on `width = 3`).

**Recovery:** width-3 closure is a meaningful result (1/3-2/3 for width-3 minimal counterexamples) but not a full closure. **F32 AMBER-width-3-only**.

### 5.6 D.6 — L1+ (transitivity of `\ll`) needed but unprovable (low likelihood)

**Failure description:** L2-B is the only viable L2 path (L2-A, L2-C, L2-D all wall), but L2-B requires L1+ (transitivity of `\ll`), which is independently unprovable.

**Detection:** Phase 3.2 attempt after Phase 3.1 walls.

**Likelihood:** LOW (L2-C is currently the most promising path; L2-B is fallback).

**Recovery:** none beyond R-1 of D.3 (different `F(P)`).

### 5.7 Phase D summary

| Failure | Likelihood | Detection phase | Recovery | Impact |
|---|---|---|---|---|
| D.1 L4 local form unavailable | HIGH | Phase 1.1 | None viable | RED |
| D.2 L3 1/8-obstruction | HIGH | Phase 1.2 / 2.2 | None viable | RED |
| D.3 L2 four-candidate-wall | MEDIUM | Phase 3.1 | New `F(P)` (separate program) | RED for F32 |
| D.4 Numerical gap evaporates | LOW (resurfaces in 1.1) | Phase 0 / 1.1 | None | RED |
| D.5 Width-3 only | LOW | Phase 4 | Width-3 partial result | AMBER |
| D.6 L1+ unprovable | LOW | Phase 3.2 | None beyond D.3 | RED for L2-B path |

**Most likely overall failure mode:** D.1 (L4 local form). **Most likely program-walling outcomes:** D.1 or D.2, detected after Phase 1 (300-500k tokens).

**Strongly recommend:** file Phase 1 sub-tickets *first*, pause to evaluate, then commit to multi-session L2/L3/L4 work only after Phase 1 GREEN-GREEN.

---

## §6. Hard-constraint compliance + U1-dialect-collision check

### 6.1 Constraint compliance

- **NOT factorial:** The program uses Frankl-Holds (UCC) on a family `F(P)` indexed by poset extensions. No `n!` factorial decomposition; no `S_n`-orbit construction. **Compliant.**
- **NOT functorial in the refinement sense:** The program does **not** require a `\mathrm{Pos}_n`-functor or refinement-respecting bridge `\mathcal{B}_P`. `F(P)` is defined chain-level on extensions (a set, not a functor); UCC application is set-theoretic; entropy / ERZ steps work pointwise on linear extensions. **Compliant.**
- **Paper-and-pencil first:** This scoping doc is paper-and-pencil. Future sub-tickets default to paper-and-pencil until execution converges, at which point Lean formalisation may follow. **Compliant.**
- **Cumulative state doc:** `docs/state-F32.md` (new). **Compliant.**
- **Default to main:** `polecat-cat-mg-c9d9` off `main`. **Compliant.**

### 6.2 U1-dialect-collision check

The mg-26fc structural-analogy scoping doc (§4.4) named three would-be bridges (U1, U2, U3) from BK-data to F-series cohomology. **U1 demands a refinement-respecting bridge `\mathcal{B}_P : (\text{BK objects}) \to (\text{F-series cohomology})`.** F25, F27, F28, F30, F31 each attempted a different dialect of U1 and walled (RED or AMBER) for distinct reasons. F31 RED specifically walled the chain-locality obstruction in the chain-level cochain dialect.

**Does F32 re-attempt U1?** No. F32 routes around U1 entirely:

- F32 does **not** require any bridge from BK-data to F-series cohomology.
- F32 does **not** invoke `\check H^*`, `\Phi`, `\omega_{\mathrm{bal}}^{(n)}`, or any cohomological apparatus.
- F32 is purely a **combinatorial-probabilistic** argument: union-closed families on antichain universes, with Frankl-Holds as the hammer and entropy/ERZ as the contradiction-deriving step.

**The Frankl-Holds invocation does not re-introduce U1.** Frankl-Holds (UC13+UC14) is a *set-theoretic* result about union-closed families. Its application to `F(P)` is purely combinatorial; no cohomological or refinement-functorial structure is invoked.

**Conclusion:** F32 **structurally bypasses** the U1-dialect-collision territory. F31's chain-locality wall remains valid but **non-load-bearing** for the F32 bridge program. **Compliant.**

### 6.3 Cross-program consistency

- F31 (RED-chain-locality) and F32 (this scoping) are **structurally independent attempts** to close 1/3-2/3, in two different dialects (cohomological vs combinatorial). Neither's success/failure constrains the other.
- If F32 GREEN-closes, F31's wall is moot for 1/3-2/3 but remains a valid structural result on the Čech-bias cohomology side.
- If F32 RED-walls, F31's status as "milestone-1 part (iii) closure walled" stands, and Daniel-escalation territory (methodology-paper close, milestone-1 redefinition) reactivates.

---

## §7. What this scoping establishes and what it doesn't

### 7.1 Established

- **Phase A numerical-constant verification (GREEN).** Both constants verified exactly to 5 decimals; gap `\approx 0.00896` bits is real. Robustness analysis: gap widens under sharper Frankl/ERZ; collapses under weaker.
- **L1 (Local Acyclicity) is essentially proved** (§3.1.1). 8-line proof via pair-orientation sum bound. **No separate sub-ticket needed; L1 inlines in F32 execution doc.**
- **L2 natural-candidate failure verified** (§3.2.1). Transitive closure of joined extensions creates extra canonical triples. Four candidate fixes (L2-A/B/C/D) survive in differentiated ways: L2-A likely false, L2-B conditional on L1+, L2-C cleanest standalone, L2-D coupled with L3-B.
- **L3-A (direct transfer) is dead** (§3.3.1). Concrete counterexample given.
- **L3-B (weighted UCC) suffers structural 1/8-obstruction** (§3.3.3). Even if weighted-UCC is proven on UC side, the natural weighting does not transfer to `\Pr_L \ge 1/2`.
- **L3-C (injection) is the cleanest remaining L3 path**, but its existence is open.
- **L4 (Local ERZ) is non-standard and lacks identified literature source** (§3.4). Global ERZ does not save the program.
- **Attack-order proposal** (§4) refined to file Phase 1 sub-tickets (L4-α-lit, L3-B-UC) first, pause for evaluation, then commit to multi-session L2/L3/L4 work.
- **Failure-mode enumeration** (§5) identifies D.1 (L4 local form) and D.2 (L3 1/8-obstruction) as highest-likelihood program-walling failures.
- **U1-dialect-collision check** (§6.2): F32 structurally bypasses U1; F31 wall is non-load-bearing.

### 7.2 NOT established

- **Whether L4 local form is true.** This is the central open question. Phase 1.1 (L4-α-lit) addresses it.
- **Whether L3-B weighted UCC is derivable from UC13+UC14 mechanism.** Cross-repo question. Phase 1.2 (L3-B-UC) addresses it.
- **Whether L3-C injection exists.** Open. Phase 2.2 addresses it.
- **Whether L2-C representation lemma admits a clean construction.** Open. Phase 3.1 addresses it.
- **Whether the program works for width ≥ 4.** Beachhead is width-3; generalisation is separate.

### 7.3 Honest scoping verdict

**AMBER-one-lemma-tractability-uncertain.** Two lemmas (L3, L4) carry substantive tractability uncertainty:

- L3: structurally obstructed by the 1/8-factor for L3-B; L3-C is open.
- L4: local form non-standard; literature source unidentified.

The program is non-vacuous arithmetically (Phase A GREEN) and admits one trivial-to-prove lemma (L1 GREEN). The remaining three lemmas (L2, L3, L4) carry execution risk; L3 and L4 are the binding constraints.

**Recommended next action:** file Phase 1 sub-tickets (L4-α-lit + L3-B-UC) as concurrent polecats; pause to evaluate before committing to L2 work.

---

## §8. Execution sub-ticket recommendations

**Sub-ticket 1: F32-L4-α-lit** (Phase 1.1, FILE FIRST).

- **Title:** F32-L4-α-lit: identify literature ERZ form delivering per-3-antichain entropy bound `\ge \log_2(9/2)` for minimal counterexamples.
- **Scope:** Single-session paper-and-pencil + literature search. Identify the specific ERZ-style result (Kahn-Saks, Brightwell-Tetali, Friedman, or other) that gives a *per-antichain* lower bound on entropy, with constant `\log_2(4/3)` for the compatibility allowance. Verify constant is sharp.
- **Budget:** 150-250k tokens.
- **Verdict outcomes:** GREEN (citation found, constant sharp); AMBER (citation found, constant different — triggers Phase A re-verification); RED (no literature source; escalate to L4-β-derive).
- **Output:** `docs/compatibility-geometry-F32-L4-alpha-lit.md` + `state-F32.md` session 2 entry.

**Sub-ticket 2: F32-L3-B-UC** (Phase 1.2, FILE CONCURRENTLY with sub-ticket 1).

- **Title:** F32-L3-B-UC: does the UC13+UC14 mechanism extend to weighted-UCC with positive real weights?
- **Repo:** `union_closed` (cross-repo from F32 home).
- **Scope:** Single-session paper-and-pencil. Examine the UC13+UC14 proof structure (the load-bearing closure mechanism in UC13 §7) and determine if it extends to:
  - (W-rational) Rational weights with positive integer values (multiset Frankl).
  - (W-real) Real positive weights.
  - **Note the 1/8-obstruction** from F32-scope §3.3.3: even if weighted-UCC holds, the natural `w(Q) = e(Q)` weighting on `F(P)` doesn't translate to `\Pr_L \ge 1/2`. So the sub-ticket has two parts: (a) is weighted-UCC derivable from UC13+UC14?; (b) does it bypass the 1/8-obstruction (separately, via an alternative weighting)?
- **Budget:** 200-300k tokens.
- **Verdict outcomes:** GREEN (weighted-UCC derivable AND 1/8-obstruction bypassed); AMBER (weighted-UCC derivable, 1/8-obstruction persists — escalates to L3-C); RED (weighted-UCC not derivable, L3-B fully walled — also escalates to L3-C).
- **Output:** `union_closed/docs/union-closed-weighted-UCC-scope.md` + cross-link to `one_third_width_three/docs/state-F32.md` session 3 entry.

**Sub-tickets 3+: contingent on Phase 1 results.** Detailed sub-ticket specifications deferred to post-Phase-1 mayor decision. The Phase 1 verdict combination dictates which of L4-β-derive, L3-C-injection, L2-C-rep, L2-B-trans go next.

### 8.1 Do NOT file these sub-tickets yet

- L2 sub-tickets (any variant): wait for Phase 1 results.
- L4-β-derive: wait for L4-α-lit.
- L3-C-injection: wait for L3-B-UC.
- F32-final-integration: wait for all four lemmas to land.

Filing L2 / L3-C / L4-β before Phase 1 results risks 400-800k tokens of wasted multi-session work if Phase 1 walls.

### 8.2 Mayor decision after Phase 1

Mayor should review Phase 1 verdicts and either:

- (M-1) **GREEN-GREEN** (both Phase 1 sub-tickets pass): proceed to Phase 3 (L2-C-rep), with L4-β-derive deferred (already covered by L4-α-lit GREEN).
- (M-2) **GREEN-RED or RED-GREEN** (one walls): file the conditional Phase 2 sub-ticket for the walling lemma, defer L2 work until that resolves.
- (M-3) **RED-RED** (both wall): escalate to Daniel for program redirection. F32 RED at gates.

---

## §9. References

- **Daniel reminders.**
  - 2026-05-16T11:29:58Z — articulates the 10-step program at `~/files/union_closed_1323_proof_steps.txt`. High priority alongside union-closed Lean formalization.
  - 2026-05-15T23:20Z — NOT factorial; NOT functorial in the refinement sense.
- **Source program.** `~/files/union_closed_1323_proof_steps.txt` (Daniel 2026-05-16T11:29Z, 275 lines).
- **Frankl-Holds (the hammer).** `union_closed/docs/union-closed-UC13-frankl-closure.md` (mg-83f0, merged). Load-bearing closure form is §7.
- **Prior cohomology-side attempts at milestone-1 part (iii).**
  - F25: `docs/compatibility-geometry-F25-hypothesis-A-constants-audit.md` (RED).
  - F27: `docs/compatibility-geometry-F27-spectral-to-cohomology-scoping.md` (RED).
  - F28: `docs/compatibility-geometry-F28-sheaf-cohomology-on-POSET.md` (AMBER).
  - F29: `docs/compatibility-geometry-F29-cech-bias-cohomology.md` (AMBER, mg-70b0).
  - F30: `docs/compatibility-geometry-F30-chain-level-phi.md` (AMBER, mg-c3fe).
  - F31: `docs/compatibility-geometry-F31-phi-star-injectivity.md` (RED, mg-01ce).
- **F-series cohomological core.** F17 (`docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`); F18 (`docs/compatibility-geometry-F18-ucc2-delta-injective.md`). Provide the `H^k(\Delta_n, \mathbb{Q})` only-sign-like-at-`n-2` anchor used by F29-F31. **NOT directly invoked by F32** (F32 is combinatorial-probabilistic, not cohomological).
- **U1-dialect-collision baseline.** `docs/compatibility-geometry-structural-analogy-scoping.md` (mg-26fc) §4.4 (U1, U2, U3).
- **Literature ERZ-style entropy bounds for linear extensions** (to be identified in Phase 1.1):
  - Kahn-Saks (1984), "Balancing poset extensions."
  - Brightwell-Tetali (2003), entropy-style arguments for 1/3-2/3.
  - Friedman (1993), entropy bounds for linear extensions.
  - Brightwell, Bollobas surveys.
- **State ledger.** `docs/state-F32.md` (new; session 1 = this scoping).

---

*F32-scope (mg-c9d9) ends. Phase A GREEN, L1 GREEN-inline, L2/L3/L4 AMBER — verdict AMBER-one-lemma-tractability-uncertain. Recommended next action: file F32-L4-α-lit + F32-L3-B-UC as concurrent Phase 1 polecats.*
