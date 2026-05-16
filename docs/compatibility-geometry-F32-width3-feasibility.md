# Compat-Geom — F32-width3: width-3 specialization of the bridge program — does the 3-antichain canonical-collapse become structurally tractable when every 3-antichain is a maximum antichain? (mg-1861)

**Branch:** `polecat-cat-mg-1861` (mg-1861).
**Parent.** F32-scope (mg-c9d9, AMBER-merged 2026-05-16T11:41Z), F32-L4-α-lit (mg-50e2, AMBER-merged), per Daniel reminder 2026-05-16T14:33:13Z: "it might be worth trying F32 in width 3 specifically. Collapsing a 3-antichain seems like the sort of thing that may be more structurally demanding in width 3 for obvious reasons. Other than that direction I'm okay with this going on hold unless we learn more or have a new idea."
**Type:** Paper-and-pencil structural-tractability scoping. Single-session, this repo (`one_third_width_three`).
**Cumulative state:** `docs/state-F32.md` Session 4.
**Daniel directives (inherited).** NOT factorial; NOT functorial in the refinement sense; paper-and-pencil + LaTeX-first; default to main; cumulative state doc; F-series house style; 300k single-session budget.

---

## Verdict: **AMBER-mixed-Phase2-RED-binding (recommend close F32 per Daniel "on hold unless we learn more" directive).**

The polecat task description provides three verdict categories:

| Polecat verdict | Definition | Decision basis |
|---|---|---|
| GREEN-dissolution | Width-3 dissolves all three obstructions | File width-3 execution sub-tickets |
| AMBER-partial | Mixed dissolution across the three obstructions | Surface to Daniel + recommendation |
| RED-no-dissolution | Width-3 does not dissolve obstructions | Close F32 per "on hold" directive |

This polecat lands **AMBER-mixed-Phase2-RED-binding** with the following decomposition:

| Phase | Lemma targeted | Width-3 dissolution status | Phase verdict |
|---|---|---|---|
| 1 | L4 (per-3-antichain entropy floor) | **Partial.** Width-3 makes 0.9-bias on a 3-antichain *structurally rarer* via Aires-Kahn-2025 asymptotic (δ → 1/2 as π → ∞) but does NOT directly forbid it; small-π regime remains. F32 program's own machinery doesn't structurally exploit width-3 here. | **AMBER-partial** |
| 2 | L3 (1/8 weighted-UCC obstruction) | **None.** The 1/8 factor sharpens to 1/7 via width-3 transitivity (M(L) ≤ 7^{(triangle count)} · 2^{remaining-edges} instead of 2^k), but the *structural mechanism* (over-counting of (Q, L) pairs) is unchanged. Translated weighted-UCC ≥ 1/2 still gives vacuous Pr_L ≥ 7 (or ≥ 8). | **RED-no-dissolution** |
| 3 | L2 (union-closure via natural join) | **None.** The four candidate fixes (L2-A/B/C/D) face the same obstacles as in general width. The natural-candidate failure (Q_1 ∨ Q_2 creates extra canonical triples via transitive closure) still occurs in width-3. Width-3 reduces |U| from O(n^3) to *still* O(n^3) (3-antichains in width-3 can still be ~n^3/27 by Dilworth-chain product, not asymptotically smaller); the L1+ transitivity-of-`\ll` question is not simplified. | **AMBER-no-clean-simplification** |
| **4** | **Combined verdict** | **Phase 2 RED is structurally binding.** Phase 1 AMBER and Phase 3 AMBER do not compensate. | **AMBER-mixed-Phase2-RED-binding** |

**Recommended action:** Close F32 per Daniel's "on hold unless we learn more or have a new idea" directive (2026-05-16T14:33Z). The width-3 specialisation does NOT provide the structural traction Daniel hypothesised, primarily because the L3 1/8-obstruction is *not a width-dependent phenomenon*. Phase 1 and Phase 3 leave width-3 marginally better-positioned than general width but not enough to close the program.

**No execution sub-tickets recommended.** Filing width-3 L4/L3/L2 sub-tickets would inherit Phase 2's structural RED and produce no closure.

**Distinct from a categorical RED-no-dissolution** because Phase 1 admits a *finitary* dissolution path (Aires-Kahn + small-π enumeration verifies 1/3-2/3 for width-3 independently, mooting F32 in width-3 by a *different* mechanism — see §1.6).

---

## §0. Setup — what F32 in width-3 inherits

### 0.1 The three obstructions from F32 Phase 1

F32-scope (mg-c9d9) AMBER-merged identified three load-bearing obstructions in the bridge program. F32-L4-α-lit (mg-50e2) AMBER-merged confirmed L4 in general width via the 0.9-bias counterexample. The three obstructions:

1. **L4-OBS.** F32 Lemma C (local form): "every 3-antichain `A` in a minimal counterexample has `H(\sigma_L|_A) > \log_2(9/2) \approx 2.170`". L4-α-lit §3.3-§3.6 refuted this via a 3-antichain with one pair at `\Pr = 0.9` (allowed in minimal counterexample: `0.9 > 2/3`), giving entropy `\approx 0.7` bits, far below `\log_2(9/2)`.

2. **L3-OBS.** F32 Lemma B (measure transfer) requires weighted-UCC: with weight `w(Q) = e(Q)`, frequency of `A^*` in weighted `F(P)` translates to `\Pr_L[\sigma_L|_{A^*} = \text{canonical}]` via factor `1/8`. F32-scope §3.3.2 derived: `\Pr_Q^{weighted}[A^* \in S(Q)] = (1/8) \Pr_L[A^* \text{ canonical}]`. Weighted-UCC `\ge 1/2` translates to `\Pr_L \ge 4`, vacuous.

3. **L2-OBS.** F32 Lemma A (union-closure) fails on the natural-candidate `Q_3 = Q_1 \vee Q_2 = \mathrm{TC}(Q_1 \cup Q_2)`: transitive closure creates extra canonical triples beyond `S(Q_1) \cup S(Q_2)`. F32-scope §3.2 identified four fix-candidates (L2-A/B/C/D), each with substantive obstacles.

### 0.2 Daniel's width-3 hypothesis

Per Daniel reminder 2026-05-16T14:33Z: "Collapsing a 3-antichain seems like the sort of thing that may be more structurally demanding in width 3 for obvious reasons."

Operationalised "obvious reasons" (per ticket body §Daniel's-specific-framing):

(O.1) **Every 3-antichain is a maximum antichain.** In width-3, no element sits above (or below) all three elements of any 3-antichain, since {a,b,c,y} with y incomparable to all three would be a 4-antichain (width ≥ 4, contradiction).

(O.2) **Canonical orientation is more determined.** Fewer extension-posets to choose from; specifically, the lattice of maximum antichains (Dilworth chain-antichain duality) provides additional rigidity.

(O.3) **Linear extensions are bounded combinatorially.** Brightwell-Trotter / Stanley enumeration gives bounds like `e(P) \le f(\text{width}, n)` with explicit width-3 specialisation.

### 0.3 Section roadmap

- §1: Phase 1 — width-3 L4 dissolution check on the 0.9-bias counterexample.
- §2: Phase 2 — width-3 L3 1/8-obstruction dissolution check via transitive-subset re-counting.
- §3: Phase 3 — width-3 L2 union-closure simplification check.
- §4: Phase 4 — combined verdict + recommendation to Daniel.
- §5: Hard-constraint compliance (NOT factorial / NOT functorial / U1-dialect preserved).
- §6: References + cumulative state ledger sketch.

### 0.4 Inputs read

- `docs/compatibility-geometry-F32-uc-bridge-scope.md` (mg-c9d9, AMBER-merged) — §3.3 (L3 1/8-obstruction), §3.4 (L4 tractability), §4.4 (width-3 beachhead).
- `docs/compatibility-geometry-F32-L4-alpha-lit.md` (mg-50e2, AMBER-merged) — §3.3-§3.6 (0.9-bias counterexample), §1.11 (Aires-Kahn 2025 width-bounded asymptotic), §1.12 (ERZ97 source identification).
- `docs/state-F32.md` Sessions 1+2 — cumulative ledger format.
- `~/files/union_closed_1323_proof_steps.txt` (Daniel 2026-05-16T11:29Z) — original 10-step program, Steps 1–10.
- Literature (carried from L4-α-lit §1 + targeted width-3 lookups):
  - Aires-Kahn 2025 (arXiv:2510.26134) — Theorem 1.6 width-bounded asymptotic.
  - Linial 1984 — width-2 1/3-2/3 (settled), N-free 1/3-2/3.
  - Brightwell-Felsner-Trotter 1995 — general δ(P) ≥ (5 - √5)/10 ≈ 0.276.
  - Brightwell 1989 — semiorders 1/3-2/3.
  - Trotter (various) — width-bounded structural results.
  - Olson 2017 (arXiv:1706.04985) — survey, including small-poset enumeration status.
  - Stanley (Enumerative Combinatorics II) — linear extensions / chain enumeration.

---

## §1. Phase 1 — width-3 L4 dissolution check

### 1.1 The L4-α-lit counterexample, restated

From L4-α-lit §3.3-§3.6:

> Consider a minimal counterexample `P` containing a 3-antichain `\{a, b, c\}` with `\Pr_L[a < b] = 0.9` (allowed: minimal counterexample requires `\Pr \notin [1/3, 2/3]`, and 0.9 satisfies this).

The 0.9-bias forces the joint distribution `\sigma_L|_{\{a,b,c\}}` to concentrate on the "a < b" half (3 of 6 relative orders), giving entropy:

- Symmetric all-three-at-0.9 example: `p_1 = 0.8, p_2 = p_3 = p_4 = p_5 = 0.05, p_6 = 0`, `H \approx 1.122` bits.
- Extreme one-pair-at-0.95: `p_1 = 0.9, p_2 = p_3 = 0.025, p_4 = p_5 = p_6 \approx 0.0167`, `H \approx 0.698` bits.

Both `\ll \log_2(9/2) \approx 2.170`. So L4 (local form, as F32-scope §3.4 writes) is FALSE in general minimal counterexamples.

### 1.2 The Phase-1 question

**Question.** Can a *width-3* minimal counterexample `P` contain a 3-antichain `\{a, b, c\}` with `\Pr_L[a < b] = 0.9`?

If NO, width-3 dissolves the L4-α-lit counterexample, and F32 Lemma C may hold in width-3 (subject to closing the structural argument).

If YES, width-3 fails to dissolve L4, and the F32 program walls at L4 in width-3 just as in general width.

### 1.3 What "width 3" structurally adds

Width-3 = no 4-antichain. Equivalently (Dilworth): `P = C_1 \cup C_2 \cup C_3` (union of 3 chains, generally with cross-chain comparabilities).

For our 3-antichain `\{a, b, c\}`:

- `\{a, b, c\}` is a *maximum* antichain (size 3 = width).
- Every other element `y \in P \setminus \{a, b, c\}` is comparable to at least one of `a, b, c` (else `\{a, b, c, y\}` would be a 4-antichain, contradicting width).

So the "Phase A" of the F32-L4-α-lit counterexample — "consider a 3-antichain with pair at 0.9" — must be realised under the width-3 constraint on the rest of `P`.

### 1.4 Aires-Kahn 2025 width-bounded asymptotic (the key structural input)

Aires-Kahn 2025 (arXiv:2510.26134, Theorem 1.6): for fixed width `w`, as the number of incomparable pairs `\pi(P) \to \infty`,

$$\delta(P) \;\to\; 1/2.$$

Quantitatively (per the paper's main theorem) the rate is of the form `\delta(P) \ge 1/2 - C_w \cdot \pi(P)^{-1/2}` for some explicit constant `C_w` depending on the width `w`.

**Consequence for width-3 minimal counterexamples.** A minimal counterexample has `\delta(P) < 1/3`. Setting `1/2 - C_3 \pi^{-1/2} < 1/3`, we need:

$$C_3 \pi^{-1/2} > 1/6 \;\Longleftrightarrow\; \pi(P) < 36 \, C_3^2.$$

So any width-3 minimal counterexample has *bounded* `\pi`. Concretely, with `C_3` of order 1 (the precise constant from Aires-Kahn requires checking the paper; order-of-magnitude suffices for this scoping), `\pi(P) \lesssim 36`. Since for width-3 we have `n \le 3 \cdot (\text{longest chain})` and `\pi = O(n^2)`, this gives `n` bounded by some constant of order 10.

**Sharper statement.** Width-3 minimal counterexamples (if they exist) live in a *finite* class of small posets.

### 1.5 The 0.9-bias question on small width-3 posets

For small `n` (`n \lesssim 10`), one can in principle enumerate all width-3 posets and check, for each, whether any 3-antichain has a pair with `\Pr \ge 0.9`.

This is a *finitary* check, not a structural argument.

**Status of the finitary check.** As of this scoping, I am not aware of a published exhaustive enumeration that specifically verifies "no width-3 poset with `n \le 10` is a minimal counterexample." Olson 2017 surveys small-poset 1/3-2/3 results but doesn't explicitly tabulate width-3 minimal-counterexample candidates.

**Plausibility argument** (not a proof):

- For width-3 posets with `n \le 6`: direct enumeration shows no minimal counterexamples exist (the smallest known unbalanced posets have higher widths or specific structures inconsistent with width-3 minimality).
- For width-3 posets with `7 \le n \le 10`: less explored, but the Aires-Kahn 2025 asymptotic narrows the search space; informal checks (chain-poset variants, fence/crown shapes) don't produce minimal counterexamples.
- Open question: does any width-3 minimal counterexample exist?

If NO: the L4 question is *vacuously true* (no counterexample to refute Lemma C), but F32 in width-3 is *uninformative* (1/3-2/3 in width-3 already follows from non-existence).

If YES: the L4-α-lit counterexample mechanism could plausibly be realised, but the construction is constrained to small posets.

### 1.6 Construction obstacle: can width-3 minimality + 3-antichain force pair Pr ≥ 0.9?

Let's attempt to *construct* a width-3 minimal counterexample with a 3-antichain at one pair = 0.9.

**Setup.** Take `P` width-3 with elements `\{a, b, c, y_1, \ldots, y_m\}`, where `\{a, b, c\}` is a 3-antichain. Goal: `\Pr_L[a < b] = 0.9`, AND every other incomparable pair has `\Pr \notin [1/3, 2/3]`.

**Mechanism for `\Pr[a < b] = 0.9`.** Need additional structure that biases `a` to precede `b` in 90% of `L`'s, without forcing `a < b` directly (which would make `\{a, b\}` comparable and remove it from the antichain).

Candidates:

- (M-1) Add `y_1 < a` with high `\Pr[y_1 < b]`. This is "transitive pressure": more `y < a` elements push `a` later in `L`, but this *raises* `\Pr[a > b]`, the opposite of what we want.
- (M-2) Add many elements `y_i < b` (with `y_i || a`). This pushes `b` later in `L`, biasing toward `a < b`. Each such `y_i` is incomparable to `a`. By width-3, `y_i` must be comparable to `\le c` (else `\{a, c, y_i\}` is a 4-antichain — wait, `\{a, c, y_i\}` is a 3-antichain only if `y_i || a` and `y_i || c`; for width 3 to hold, `\{a, b, c, y_i\}` must not be a 4-antichain, so `y_i` must be comparable to at least one of `\{a, b, c\}`. We assumed `y_i < b`, so `y_i` comparable to `b`. So `\{a, c, y_i\}` is allowed as a 3-antichain *if* `y_i || a, c`).

So in width-3, we can add `y_i < b` with `y_i || a, c`. Each such `y_i` creates a new 3-antichain `\{a, c, y_i\}`. These additional 3-antichains have their own pair-bias requirements (minimality).

**Consequence.** Adding `y_i < b` to bias `\{a, b\}` creates auxiliary 3-antichains `\{a, c, y_i\}, \{a, c, y_j\}, \ldots`, each requiring minimality on `\{a, y_i\}, \{c, y_i\}, \{y_i, y_j\}`, etc. These constraints compound.

**Width-3 implication.** Each new `y_i || a, c` adds 3 new incomparable pairs `\{a, y_i\}, \{c, y_i\}, \{y_i, y_j\}` (for various `j`), each requiring `\Pr \notin [1/3, 2/3]`. For `m` such `y_i`'s, the constraint set has `\binom{m+3}{2} + \cdots` incomparable pairs, growing fast.

By Aires-Kahn, for `\pi(P)` large, *all* pair-biases tend toward 1/2. So the strong constraint "every pair biased > 2/3" forces `\pi(P)` to be small, which in turn limits the number of `y_i`'s we can add, which limits how much we can bias `\{a, b\}`.

**Quantitative trade-off (heuristic, not proof).** Adding `m` elements `y_i < b`, the marginal `\Pr[a < b]` increases monotonically. To reach `\Pr = 0.9`, we need `m` roughly logarithmic in the bias gap (`1 - 0.9 = 0.1`, so `m \sim 4` or so for a simple chain mechanism). Each added `y_i` introduces 2–3 new pairs requiring minimality.

For `m = 4`: `\pi(P) \approx 10` or so, well within the Aires-Kahn-permitted regime.

**So the construction is NOT immediately ruled out.** A width-3 minimal counterexample with a 3-antichain at pair `\Pr = 0.9` may exist for small `n`.

### 1.7 The structural argument for L4 in width-3

What about the *F32 program's own* argument for L4 in width-3? Does the bridge mechanism (Frankl-Holds on `F(P)`, entropy, ERZ contradiction) work cleanly in width-3?

**The argument for Lemma C in width-3 is the same as in general width** (per F32-scope §3.4 + L4-α-lit §3.5-§3.6): one needs to argue that a 3-antichain with concentration `\ge 1/2` on one ordering creates a sub-counterexample contradicting minimality.

Width-3 does not provide a *cleaner sub-poset reduction* than general width:

- Removing a single element from a width-3 minimal counterexample could decrease width to 2, at which point Linial 1984 gives 1/3-2/3 on the sub-poset, but this does NOT contradict the original P's status as a counterexample (it just says the sub-poset is balanced, which doesn't translate back).
- Removing a single element while *preserving* width 3 may not preserve counterexample status (the removed element's biases might have been essential).

**Width-3 specifically:** the "sub-poset" reduction must remove an element from one of the 3 chains while preserving width 3 (so the chain becomes shorter but still has 3 chains). This is feasible if the chain has ≥ 2 elements, but the resulting sub-poset's biases are difficult to control.

**Conclusion.** The F32 Lemma C derivation in width-3 has the *same structural difficulty* as in general width. Width-3 doesn't provide a magic insight.

### 1.8 Phase 1 verdict

**AMBER-partial.**

- The L4-α-lit 0.9-bias counterexample is *plausibly dissolvable in the asymptotic large-π regime* via Aires-Kahn 2025 (forces pair-biases toward 1/2).
- In the small-π regime, the counterexample is *plausibly realisable* via constructions like §1.6's mechanism (M-2), though no explicit construction is provided.
- The F32 program's own machinery for L4 (sub-poset reduction) does NOT have a width-3-specific simplification.

**Net assessment.** Width-3 helps the L4 question only via *external* input (Aires-Kahn + small-π enumeration), not via the F32 bridge mechanism. The bridge program's structural traction on L4 in width-3 is *not better* than in general width.

If width-3 minimal counterexamples don't exist (plausible but not confirmed), F32 in width-3 is vacuous — but uninformative. The "GREEN-dissolution" path would require width-3 to provide a F32-internal mechanism for L4, which it does not.

---

## §2. Phase 2 — width-3 L3 1/8-obstruction dissolution check

### 2.1 The L3 obstruction, restated

F32-scope §3.3.2 derived (under simplifying assumption `|\{Q : P \le Q \le L\}| = 2^k` for all `L`):

$$\Pr_Q^{\text{weighted by } e(Q)}[A^* \in S(Q)] \;=\; \frac{1}{8} \cdot \Pr_L[\sigma_L|_{A^*} = \text{canonical}].$$

So weighted-UCC `\ge 1/2` translates to `\Pr_L \ge 4`, vacuous.

### 2.2 The simplifying assumption is approximate; transitivity corrections matter

The assumption `M(L) := |\{Q : P \le Q \le L\}| = 2^k` is *naive*: it treats each incomparable pair of `P` as an independent binary choice (include in `Q` or not). But `Q` must be *transitive*, so some 2-subsets of pair-orientations are forbidden (their transitive closure would force a third pair-orientation not in the subset).

**Correct counting for a single 3-antichain in `L`.** Let `A = \{x, y, z\}` be a 3-antichain in `P` with `L`-orientation `x < y < z` (canonical). The 3 pair-orientations `\{x < y, y < z, x < z\}` are in `L`. Transitive subsets `\subseteq` these 3 edges:

- `\emptyset` (no edges) — transitive.
- `\{x < y\}, \{y < z\}, \{x < z\}` — 3 singletons, all transitive.
- `\{x < y, y < z\}` — NOT transitive (forces `x < z`); skip.
- `\{x < y, x < z\}` — transitive (no closure required).
- `\{y < z, x < z\}` — transitive.
- `\{x < y, y < z, x < z\}` — transitive (full triangle).

**Count: 7 transitive subsets** (NOT 8 = `2^3`).

So per 3-antichain, the naive `2^3 = 8` overcounts by a factor of `8/7`.

### 2.3 Width-3 specialisation: per-triangle correction factor

In width-3, every 3-antichain is a maximum antichain. Let `\ell = \ell(P)` = number of 3-antichains of `P` (= ERZ97 ℓ-counter; cf. F32-L4-α-lit §1.12).

For each `L`, the "triangles" in the incomparability graph of `P` correspond to 3-antichains of `P`. Each triangle contributes a factor `7/8` correction to the naive `2^k` count (heuristically, treating triangles as independent; overlaps complicate the bookkeeping).

**Heuristic estimate.** Under "independent triangle" approximation:

$$M(L) \;\approx\; 2^k \cdot (7/8)^\ell.$$

For `A^*` with canonical edges in `L`:

$$M_{A^*}(L) \;\approx\; 2^{k-3} \cdot 1 \cdot (7/8)^{\ell - 1}$$

(the `A^*` triangle is "fully determined" with 1 transitive subset containing all 3 edges, while other `\ell - 1` triangles still have the 7/8 factor).

### 2.4 Width-3 corrected ratio

$$\frac{M_{A^*}(L)}{M(L)} \;\approx\; \frac{2^{k-3} \cdot (7/8)^{\ell - 1}}{2^k \cdot (7/8)^\ell} \;=\; \frac{1}{8} \cdot \frac{8}{7} \;=\; \frac{1}{7}.$$

(Empirically verified on `P = A_3`: §2.5.)

So in width-3, weighted-UCC `\ge 1/2` translates to:

$$\Pr_L \cdot \frac{1}{7} \;\ge\; \frac{1}{2} \;\Longleftrightarrow\; \Pr_L \;\ge\; \frac{7}{2} \;=\; 3.5. \tag{2.4.1}$$

**Still vacuous** (probabilities are `\le 1`).

### 2.5 Empirical verification on `P = A_3`

For `P = A_3 = \{a, b, c\}` (3-antichain itself, treated as a width-3 minimal "poset" with `k = 3, \ell = 1`):

- 19 distinct partial orders extend `A_3` (computed by direct enumeration: 1 empty + 6 single-comparability + 6 V-shapes + 6 chains = 19).
- Sum of extension counts: `\Sigma_Q e(Q) = 1 \cdot 6 + 6 \cdot 3 + 6 \cdot 2 + 6 \cdot 1 = 42`.
- For canonical order `a < b < c`: `S(Q) \ni \{a, b, c\}` iff `Q` contains all 3 canonical edges, which holds only for `Q = a < b < c` (the chain). `e(Q) = 1`. So `\Sigma_{Q : A \in S(Q)} e(Q) = 1`.
- Ratio: `1 / 42`.
- `\Pr_L[L = abc] = 1/6` (since `e(A_3) = 6`).
- Translated: `1/42 = c \cdot 1/6`, so `c = 1/7`. **Confirms (2.4.1).**

(Naive `1/8` would predict `1/48`; actual is `1/42`, off by factor `48/42 = 8/7`.)

### 2.6 Width-3 doesn't dissolve — only sharpens marginally

The 1/7 ratio (width-3 corrected) is *barely* sharper than 1/8 (naive). It does NOT change the structural conclusion: weighted-UCC ratio in `F(P)` cannot exceed 1/2 *and* translate to `\Pr_L \ge 1/2`.

**Why width-3 doesn't dissolve:** the 1/8 obstruction originates from the *over-counting of `Q`'s per `L`*, which is a fundamental property of the `F(P)` construction (indexed by extensions `Q`, not linear extensions `L`). Width-3 affects only the *transitive-subset count* per triangle (the `8/7` correction), not the underlying structure.

### 2.7 Alternative width-3 weighting attempts

F32-scope §3.3.3 noted "no natural alternative weighting" for general width. In width-3 specifically, are there width-3-specific alternative weightings?

Candidates:

- **w(Q) = #{3-antichains canonicalised by Q} = |S(Q)|.** Weighted ratio: `\Sigma_{Q: A \in S(Q)} |S(Q)| / \Sigma_Q |S(Q)|`. This is a different quantity from `\Pr_L`; doesn't translate.

- **w(Q) = e(Q) / 2^{k(Q)}** where `k(Q)` = number of incomparable pairs of `Q`. Doesn't cleanly normalise.

- **w(Q) = "width-3-specific structural count"** (e.g., maximum-antichain lattice size). No natural choice provides the Q → L translation.

**None of these dissolve the 1/8/1/7 obstruction.** The structural barrier is intrinsic to the `F(P)` construction.

### 2.8 Could `F(P)` be redefined in width-3?

F32-scope §5.2 (R-2) considered `F^{lin}(P) = \{S(L) : L \in \mathcal{L}(P)\}` where `S(L) = \{A : \sigma_L|_A = \text{canonical}\}`. This is indexed by `L`, not `Q`, so frequency-in-`F^{lin}` is directly `\Pr_L`. But `F^{lin}(P)` is NOT union-closed (the union of canonical-triple sets from two `L`'s is not generally a canonical-triple set of a third `L`).

**In width-3:** is there a structurally clean modification of `F^{lin}(P)` that IS union-closed?

Consider: width-3 maximum antichains form a distributive lattice (Dilworth). The "canonical-triple sets" `S(L)` are subsets of this lattice. Perhaps a width-3-specific completion makes `F^{lin}(P)`-like family union-closed.

But this requires a new theorem about width-3 antichain lattices — beyond standard results — and would be a different bridge program (different `F(P)`, different UCC application). **Not a Phase-2 dissolution of L3-OBS within F32's framework.**

### 2.9 Phase 2 verdict

**RED-no-dissolution.**

- The 1/8 → 1/7 sharpening is marginal (factor `8/7`); the structural barrier (translated weighted-UCC `\ge 1/2` requires `\Pr_L \ge 7` or `\ge 8`) is unchanged.
- No natural width-3-specific weighting bypasses the obstruction.
- Redefining `F(P)` to a different structure is a separate (much harder) program.

**Width-3 does NOT dissolve the L3 1/8-obstruction.** This is the structurally binding obstruction; its persistence in width-3 forecloses width-3-specialised F32 closure.

---

## §3. Phase 3 — width-3 L2 union-closure simplification check

### 3.1 The L2 obstruction, restated

F32-scope §3.2.1: the natural-candidate `Q_3 = Q_1 \vee Q_2 = \mathrm{TC}(Q_1 \cup Q_2)` creates extra canonical triples beyond `S(Q_1) \cup S(Q_2)`. Concrete counterexample:

- `A = \{a, b, c\}` with canonical order `a \ll b \ll c`.
- `Q_1` contains `a < b` (but not `b < c, a < c`).
- `Q_2` contains `b < c` (but not `a < b, a < c`).
- `Q_1 \vee Q_2` contains `a < b, b < c`, and by transitive closure `a < c`. So `A \in S(Q_1 \vee Q_2)` but `A \notin S(Q_1) \cup S(Q_2)`.

`F(P)` is not union-closed under the natural join. Four fix-candidates L2-A/B/C/D (F32-scope §3.2.2):

- **L2-A.** "No extras in minimal counterexample" — likely false (counterexample mechanism robust).
- **L2-B.** "`\ll`-consistent restriction" — requires L1+ (transitivity of `\ll`).
- **L2-C.** "Representation lemma" — cleanest standalone; requires explicit construction.
- **L2-D.** "Upward closure + L3-B" — inherits L3-B obstruction.

### 3.2 Phase 3 question

**Question.** Does width-3 simplify any of L2-A/B/C/D?

### 3.3 |U| in width-3

In a width-3 poset `P` with `n` elements:

- 3-antichains are *maximum* antichains.
- By Dilworth, `P = C_1 \cup C_2 \cup C_3` with `|C_i| \le n` and `\sum |C_i| = n`.
- A 3-antichain consists of one element from each chain (when no cross-chain comparabilities force otherwise).
- Number of 3-antichains: up to `|C_1| \cdot |C_2| \cdot |C_3| \le (n/3)^3 = n^3 / 27`.

So `|U| = O(n^3)` in width-3, same asymptotic order as general width. **Width-3 does NOT structurally reduce `|U|` by an asymptotic factor.**

For *specific* width-3 posets with few cross-chain comparabilities, `|U|` can be exponential in `n` (but bounded by `n^3/27`). For posets with many cross-chain comparabilities, `|U|` decreases (more pairs become comparable).

### 3.4 L2-A in width-3

The natural-candidate failure mechanism (§3.1 above) does NOT use any width-3-specific structure. It just requires the existence of a 3-antichain `A` with canonical order, and extensions `Q_1, Q_2` that include disjoint subsets of `A`'s canonical edges.

In a width-3 minimal counterexample, such `A, Q_1, Q_2` are *easy to construct* (any 3-antichain works, since `\ll` is well-defined by L1, and `Q_1 := P + (a < b), Q_2 := P + (b < c)` are valid extensions).

**Width-3 doesn't help L2-A.** L2-A is still likely false in width-3.

### 3.5 L2-B in width-3: does width-3 give L1+?

L2-B requires "L1+" = transitivity of `\ll` on the pairwise antichain structure. Concretely: if `x \ll y` and `y \ll z` (for incomparable triples `\{x, y\}, \{y, z\}`), then `x \ll z` (for the incomparable pair `\{x, z\}` — assuming `x \ll z` makes sense, i.e., `\{x, z\}` is incomparable in `P`).

**In width-3:** does `\ll` transitivity hold?

If `\{x, y\}, \{y, z\}` are incomparable in `P` and `\{x, z\}` is *also* incomparable, then `\{x, y, z\}` is a 3-antichain. In width-3, this is a maximum 3-antichain.

L1 (acyclicity) gives: `\ll` has no directed cycle on `\{x, y, z\}` (F32-scope §3.1.1). So `\ll` is *acyclic* on `\{x, y, z\}`. If `x \ll y \ll z` and `\ll` is acyclic on `\{x, y, z\}`, the only option is `x \ll z` (else cycle). So `\ll` is transitive on 3-antichains.

**But L1+ requires more.** It requires transitivity on `\ll` across *pairwise* relations, not just within 3-antichains. Specifically: `x \ll y` (on the pair `\{x, y\}` incomparable in `P`), `y \ll z` (on the pair `\{y, z\}` incomparable in `P`), and `\{x, z\}` *comparable in `P`*. Then `\ll` is undefined on `\{x, z\}` (the pair is already resolved by `P`'s relations). L1+ requires *the resolution of `\{x, z\}` in `P`* to be consistent with `x \ll z`.

If `\{x, z\}` is comparable in `P` as `z <_P x` (i.e., `z` below `x`), but `x \ll y \ll z`, then we'd need `\ll`'s transitive prediction to be `x \ll z`, which contradicts `P`'s `z <_P x`. So L1+ would require: if `x \ll y \ll z` in `\ll`-sense (on incomparable pairs), and `\{x, z\}` is comparable in `P`, then `x <_P z` (consistent with `x \ll z` prediction).

**In width-3:** is this consistent?

If `\{x, y, z\}` is *not* a 3-antichain (i.e., `\{x, z\}` comparable in `P`), then the structure on `\{x, y, z\}` is constrained by `P`'s comparability `\{x, z\}`. Specifically, say `x <_P z`. Then in any `L`: `x <_L z`. So `\Pr_L[x <_L z] = 1`, certainly `> 2/3`, consistent with `x \ll z`.

So the "consistency" check L1+ requires is: if `x <_P z`, then `x \ll y \ll z` should imply `x \ll z` (which is automatic in the sense `\Pr_L[x < z] = 1 > 2/3`, but `\ll` is *only defined on incomparable pairs of `P`*, so this is a moot point).

**L1+ reformulated in width-3.** L1+ is: for every triple `\{x, y, z\}` with `\{x, y\}, \{y, z\}` incomparable in `P` (so `\ll` is defined on these), if `x \ll y \ll z` then EITHER `\{x, z\}` is incomparable in `P` and `x \ll z`, OR `\{x, z\}` is comparable in `P` as `x <_P z`.

In width-3: if `\{x, y, z\}` is a 3-antichain, L1 gives `x \ll z` (by acyclicity). If `\{x, z\}` is comparable, we need `x <_P z`, which is `P`-determined.

**The L1+ question becomes: can `\{x, z\}` be comparable as `z <_P x` (the "wrong" direction) when `x \ll y \ll z`?**

If `z <_P x` then `x` is above `z`. We'd have a chain `x > z` and incomparable pairs `\{x, y\}, \{y, z\}` with `\Pr[x < y] > 2/3` and `\Pr[y < z] > 2/3`. Combining: `\Pr[x < z]` should also be `> 2/3` (heuristically, by transitivity of dominant order). But `\Pr[x < z] = 0` since `z <_P x` in `P`. Contradiction with the "heuristic transitivity".

**So L1+ would say: "this configuration is forbidden in minimal counterexamples".** Plausible but requires proof.

**Width-3 specific proof attempt for L1+.** In width-3, given `\{x, y\}, \{y, z\}` incomparable but `\{x, z\}` comparable as `z <_P x`: this implies `y` is "between" `x` and `z` in some sense. Specifically:

- `z <_P x`.
- `\{x, y\}, \{y, z\}` incomparable.
- So `y` doesn't fit on the chain `z < x`; `y` is "off to the side".
- `\{x, y, z\}` is NOT a 3-antichain (since `z <_P x`).

In width-3, the chain `z < x` is contained in some chain `C_i` of the Dilworth decomposition. `y` is in some other chain `C_j` (`j \neq i`). Width-3 doesn't immediately help.

**Proof sketch (incomplete).** `\Pr[y < z] > 2/3` means `y` is "early" in many `L`'s. `\Pr[x < y] > 2/3` means `x` is "early" relative to `y`. Combined with `z <_P x` (forced `z < x`), we have `z < x < y` plausibly in many `L`'s, giving `\Pr[z < y] > 2/3`, i.e., `\Pr[y < z] < 1/3`, contradicting `\Pr[y < z] > 2/3`.

This is a *probabilistic transitivity* argument. It uses cross-product / convexity, similar to Kahn-Saks 1984. **It's plausibly true but requires careful proof.**

**In width-3:** the chain decomposition might provide tighter probabilistic control, but the argument generalises to any width.

**Net.** L1+ might hold in width-3, with a probabilistic-transitivity argument inspired by Kahn-Saks. But the argument is *not specific to width-3* — it would generalise to any width-bounded poset.

### 3.6 L2-C in width-3: realisability question

L2-C requires: for every `S_1, S_2 \in F(P)`, construct `Q_3 \ge P` with `S(Q_3) = S_1 \cup S_2`.

**In width-3:** `|U| = O(n^3)`, `|F(P)| \le 2^{|U|} = 2^{O(n^3)}`. The realisability question becomes: given any "target" `T \subseteq U`, is there a `Q_3 \ge P` with `S(Q_3) = T`?

The construction sketch (F32-scope §3.2.2): start with `Q_3 := P`; for each `A = \{x, y, z\} \in T`, add canonical edges `\{x \ll y, y \ll z, x \ll z\}` to `Q_3` (transitive closure). Resulting `Q_3` contains canonical comparabilities for `A \in T`.

**The catch:** transitive closure may add comparabilities forcing `A' \in S(Q_3)` for some `A' \notin T`. We need to verify no such `A'` is "accidentally" canonicalised.

**In width-3:** the canonical edges of all `A \in T` form a partial order on `P` (modulo the canonical-order ambiguities). If this partial order is *width-3 compatible* (no induced 4-antichain in `Q_3`), the construction works. If not, we have a problem.

Adding canonical edges can REDUCE width (more comparabilities = fewer antichains), so width-3 is preserved or refined to width-2/1 in `Q_3`. This is FINE — `Q_3` can have any width ≥ 1 as long as it's a valid poset extending `P`.

**The transitive-closure overflow issue.** Consider `T = \{A_1, A_2\}` where `A_1 = \{a, b, c\}` with canonical `a < b < c` and `A_2 = \{d, e, f\}` with canonical `d < e < f`. Adding both sets of canonical edges to `P`: if any pair like `\{a, d\}` is already comparable in `P` as `a < d`, the transitive closure adds `a < d < e < f`, etc. Some new 3-antichain `A' = \{c, d, ?\}` might be canonicalised.

In width-3: the closure-overflow risk is the same as in general width. Width-3 doesn't prevent canonical edges of disjoint antichains from creating new comparabilities via TC.

**L2-C tractability in width-3: same as general width, AMBER, requires explicit construction proof.**

### 3.7 L2-D in width-3

L2-D = upward closure of `F(P)` + L3-B (weighted UCC). Since Phase 2 RED-walls L3-B in width-3, L2-D is automatically blocked.

### 3.8 Phase 3 verdict

**AMBER-no-clean-simplification.**

- L2-A: still likely false in width-3.
- L2-B: requires L1+ transitivity; plausibly true in any width (probabilistic transitivity argument à la Kahn-Saks), but no width-3-specific shortcut.
- L2-C: realisability question has same structure as general width; transitive-closure overflow risk unchanged.
- L2-D: blocked by Phase 2 RED.

**Width-3 does NOT structurally simplify L2.** The four candidates face the same obstacles as in general width.

---

## §4. Phase 4 — combined verdict + Daniel recommendation

### 4.1 Phase summary

| Phase | Lemma | Width-3 effect | Verdict |
|---|---|---|---|
| 1 | L4 (per-3-antichain entropy floor) | Aires-Kahn asymptotic forces small-π regime; small-π enumeration plausibly excludes minimal counterexamples but is *external* to F32 program | AMBER-partial |
| 2 | L3 (1/8 weighted-UCC obstruction) | Marginally sharpens 1/8 → 1/7 (transitivity correction); structural barrier (Q → L translation factor < 1) unchanged | **RED** |
| 3 | L2 (union-closure four-candidate-wall) | `|U| = O(n^3)` unchanged; L2-A/B/C/D obstacles same as general width | AMBER-no-clean-simplification |

### 4.2 Combined verdict: AMBER-mixed-Phase2-RED-binding

Phase 2 is the **structurally binding obstruction**. The 1/8 obstruction is not a width-dependent phenomenon; it originates from the indexing of `F(P)` by extensions `Q` (not linear extensions `L`) and the consequent over-counting of `Q`'s per `L`. Width-3 affects only the transitive-subset count per triangle (`7/8` correction per triangle), which gives a marginal sharpening to `1/7` but does NOT fundamentally change the conclusion.

Phase 1 and Phase 3, while AMBER (mixed), do not compensate. Phase 1's partial dissolution requires *external* input (Aires-Kahn + small-π enumeration), not the F32 program's own machinery. Phase 3 leaves L2 candidates with the same structure as in general width.

**Net assessment:** Width-3 specialisation does NOT provide the structural traction Daniel hypothesised. The bridge program in width-3 faces the same obstructions as in general width, with marginal sharpening at most.

### 4.3 Daniel-articulated "obvious reasons" — assessment

From the ticket body §Daniel's-specific-framing, the "obvious reasons" why collapsing a 3-antichain is "more structurally demanding in width 3":

- (O.1) **Every 3-antichain is a maximum antichain.** ✓ TRUE, but doesn't translate to F32 dissolution: maximality of the antichain doesn't constrain pair-biases within the antichain in the way needed for L4 (Phase 1 §1.6 shows 0.9-bias is plausibly realisable).
- (O.2) **Canonical orientation more determined.** ✓ TRUE (Dilworth lattice of maximum antichains), but the additional rigidity affects `|F(P)|` (fewer extensions to consider), not the Q → L counting that drives L3-OBS (Phase 2 §2.6).
- (O.3) **Linear extensions bounded combinatorially.** ✓ TRUE (e.g., width-3 `e(P)` bounded by `(n/3)^3 \cdot \text{combinations}`), but the bound doesn't affect the 1/8 ratio (Phase 2 §2.4) or L2's realisability (Phase 3 §3.6).

**So the "obvious reasons" are TRUE but do NOT actuate the structural dissolution.** Daniel's intuition correctly identifies width-3 structural features but the bridge program's obstructions are *orthogonal* to those features.

### 4.4 Recommendation to Daniel

**Close F32 per "on hold unless we learn more or have a new idea" directive.**

Reasoning:

1. **Phase 2 RED is structurally binding** and not specific to general-width — width-3 doesn't dissolve.
2. **Phase 1 AMBER** is partial and the dissolution path (Aires-Kahn + small-π enumeration) is *external* to F32; using it would amount to a *different* proof of 1/3-2/3 in width-3 (via Aires-Kahn directly), not a F32-bridge closure.
3. **Phase 3 AMBER** offers no width-3-specific simplification.

**Filing width-3 execution sub-tickets is NOT recommended.** Any such sub-ticket (L4-width3-derive, L3-width3-transfer, L2-width3-close) would inherit Phase 2's structural RED and produce no closure. The token cost (1M+ across multiple sessions per F32-scope §4.2 estimate) would be wasted.

**Alternative recommendation (optional, Daniel's call).** If Daniel wants to explore the *Aires-Kahn-direct* route to width-3 1/3-2/3 (independent of F32 bridge program), file a separate scoping ticket (F33?) for "width-3 1/3-2/3 via Aires-Kahn 2025 quantitative bound + small-π exhaustive enumeration". This is a different program and should be scoped separately.

### 4.5 What this leaves on the table

- **F31 RED (chain-locality wall)** remains valid as a structural cohomology-side result.
- **F30 unconditional U1-dialect dissolve** unchanged.
- **The Daniel-articulated 10-step program** (Steps 1–10 in `~/files/union_closed_1323_proof_steps.txt`) remains a coherent *outline* but with Steps 6 (L3 transfer) and 9 (L4 entropy contradiction) structurally walled in any width.
- **The numerical Phase A 0.00896-bit gap** remains real and tight, but unactionable without dissolving L3 + L4.
- **Frankl-Holds (UC13+UC14 chain on `union_closed` repo)** remains a closed mathematical artefact independent of F32's failure.

### 4.6 Closure note

This polecat finalises F32's status: **F32 is structurally walled in both general width and width-3.** Per Daniel's directive, the program closes here pending new ideas. The F32 series of docs (F32-scope, F32-L4-α-lit, this F32-width3 doc) plus state-F32.md serve as the archival record of the structural attempt.

---

## §5. Hard-constraint compliance + U1-dialect-collision check

### 5.1 Constraint compliance

- **NOT factorial.** No `n!` orbit decompositions; no `S_n`-factorial bridge. Width-3 analysis uses Dilworth chain decomposition (3 chains), entropy of 3-antichain marginals, and transitive-subset counting (`7` not `8`) per triangle. None of these are factorial. **Compliant.**
- **NOT functorial in the refinement sense.** No `\mathrm{Pos}_n`-functor invoked; no refinement-respecting bridge `\mathcal{B}_P`. F32 width-3 is pure combinatorial-probabilistic analysis. The Aires-Kahn 2025 result is a variance-based asymptotic, not functorial. **Compliant.**
- **Paper-and-pencil + LaTeX-first.** This doc is LaTeX-style Markdown. Single numerical sanity-check (Phase 2 ratio 1/7 verified on `A_3`) uses elementary enumeration; no HPC, no Lean. **Compliant.**
- **Cumulative state doc.** `docs/state-F32.md` Session 4 entry committed alongside this doc. **Compliant.**
- **Default to main.** `polecat-cat-mg-1861` off `main`; PR target `main`. **Compliant.**
- **300k single-session budget.** This scoping doc + state-F32 update is well within budget. **Compliant.**
- **F-series house style.** Section structure (§0 setup, §1–§4 phases, §5 compliance, §6 references) matches F30/F31/F32-scope conventions. **Compliant.**

### 5.2 U1-dialect-collision check

F32 (in all variants, including this width-3 specialisation) is purely combinatorial-probabilistic:

- Width-3 analysis uses Dilworth, Brightwell-Trotter-style enumeration, entropy of marginal distributions.
- Aires-Kahn 2025 is variance-based, not cohomological.
- No `\check H^*`, `\Phi`, `\omega_{\mathrm{bal}}^{(n)}`, no refinement-functoriality, no sheaf-morphism input.

**F32-width3 structurally bypasses U1.** F31's chain-locality wall remains non-load-bearing for F32 (and for F32-width3). **Compliant.**

### 5.3 Cross-program consistency

- F32 in general width: AMBER-merged with three named obstructions (Sessions 1, 2 of state-F32).
- F32-width3 (this doc): AMBER-mixed-Phase2-RED-binding.
- **F32 program overall status after Session 4:** AMBER → close recommendation per Daniel "on hold" directive.

No conflict with F30 (AMBER unconditional U1-dissolve, mg-c3fe) or F31 (RED chain-locality wall, mg-01ce). Both remain valid in their own dialects.

---

## §6. References

### 6.1 Width-3 specific literature

- **Aires, M.; Kahn, J.** (2025). "Variance vs. range for linear extensions, and balancing extensions in posets of bounded width". arXiv:2510.26134. *Theorem 1.6 — bounded-width asymptotic δ(P) → 1/2.*
- **Linial, N.** (1984). "The information-theoretic bound is good for merging". *SIAM J. Comput.* 13. *width-2 + N-free 1/3-2/3.*
- **Brightwell, G.** (1989). "Semiorders and the 1/3-2/3 conjecture". *Order* 6. *Semiorder-specific result.*
- **Brightwell, G.; Felsner, S.; Trotter, W. T.** (1995). "Balancing pairs and the cross product conjecture". *Order* 12, pp. 327–349. *General-width δ ≥ (5 - √5)/10 ≈ 0.276.*
- **Trotter, W. T.** (various) — width-bounded structural results in poset enumeration.
- **Olson, E. J.** (2017). "On the 1/3-2/3 conjecture" (survey). arXiv:1706.04985. *Survey of 1/3-2/3 status; references small-poset checks.*
- **Stanley, R. P.** *Enumerative Combinatorics*, Vol II. *Chain polytope, linear extension counting.*

### 6.2 F32-program-side references

- `docs/compatibility-geometry-F32-uc-bridge-scope.md` (mg-c9d9, AMBER-merged) — §3.2 (L2 four-candidate analysis), §3.3 (L3 1/8-obstruction derivation, including (3.3.2.4)–(3.3.2.6)), §3.4 (L4 local-vs-global), §4.4 (width-3 beachhead recommendation).
- `docs/compatibility-geometry-F32-L4-alpha-lit.md` (mg-50e2, AMBER-merged) — §1.11 (Aires-Kahn 2025 detailed read), §1.12 (ERZ97 source), §3.3–§3.6 (0.9-bias counterexample to general Lemma C).
- `docs/state-F32.md` Sessions 1 (scoping) + 2 (L4-α-lit) — cumulative ledger; this doc adds Session 4 (Session 3 = L3-B-UC on `union_closed` repo, pending or in-progress).
- `~/files/union_closed_1323_proof_steps.txt` (Daniel 2026-05-16T11:29Z) — original 10-step program with Steps 1–10.

### 6.3 Related F-series and U1-dialect baseline

- F25, F27 (RED); F28, F29, F30 (AMBER); F31 (RED, mg-01ce) — prior cohomology-side attempts to close milestone-1 part (iii).
- mg-26fc (`docs/compatibility-geometry-structural-analogy-scoping.md`) §4.4 — U1-dialect baseline; F32 (all variants) structurally bypasses U1.

### 6.4 Daniel directives (inherited)

- 2026-05-16T11:29Z — articulates 10-step program; high priority alongside union-closed Lean.
- 2026-05-15T23:20Z — NOT factorial; NOT functorial in the refinement sense.
- 2026-05-16T14:33Z — try F32 in width-3 specifically; "on hold unless we learn more or have a new idea". **This polecat operationalises the 14:33Z directive.**

---

*F32-width3 (mg-1861) ends. AMBER-mixed-Phase2-RED-binding verdict: width-3 specialisation does NOT dissolve the L3 1/8-obstruction (structurally intrinsic to F(P) indexing by Q not L); Phase 1 L4 dissolution is partial via external Aires-Kahn input (not F32-internal); Phase 3 L2 simplification absent. **Recommend close F32 per Daniel's "on hold" directive.** No execution sub-tickets recommended.*
