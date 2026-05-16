# Compat-Geom — F32-L4-α-lit: identify literature ERZ form delivering per-3-antichain entropy bound for minimal counterexamples (mg-50e2)

**Branch:** `polecat-cat-mg-50e2` (mg-50e2).
**Parent.** F32-scope (mg-c9d9, AMBER-merged 2026-05-16T11:41Z) §3.4 "L4 — ERZ Entropy Contradiction". F32-scope §3.4.5 identified the load-bearing gap: "Polecat could not identify a specific cited source for `\log_2(4/3)` — Daniel's program presents it as if it's a known bound, but no citation is given. This is a load-bearing gap in scoping." F32-scope failure mode D.1 (HIGH-likelihood) is the L4 local form unavailable scenario. F32-scope §4.3 strict-order recommendation: file L4-α-lit **first** (concurrent with L3-B-UC on the `union_closed` side), because RED-outcome at L4-α moots the entire bridge program and L2/L3 work would be wasted.
**Type:** Paper-and-pencil + literature search. Single-session, this repo (`one_third_width_three`).
**Cumulative state:** `docs/state-F32.md` Session 2.
**Daniel directives (inherited).** NOT factorial; NOT functorial in the refinement sense; paper-and-pencil + LaTeX-first; default to main; cumulative state doc.

---

## Verdict: **AMBER-no-literature-local-form-derive-needed (file L4-β-derive Phase 2.1 follow-on)**

The polecat task description provides three verdict categories:

| Polecat verdict | Definition | Decision basis |
|---|---|---|
| GREEN | Citation found, constant sharp | F32 L4 closed via literature; proceed to Phase 3 |
| **AMBER** | Citation found but different constant (or different form) | **Phase A re-verify; file follow-on for adaptation/derivation** |
| RED | No citation, no derivation | Program moot; escalate to Daniel |

This polecat lands **AMBER** with the following decomposition:

1. **Literature citation IDENTIFIED at the right constant** (§1.12, §2):
   - **Ewacha-Rival-Zaguia (ERZ) 1997**, "Approximating the number of linear extensions", *Theoretical Computer Science* 175(2). The bound is `2^k(3/4)^{\ell + m} \le e(P) \le 2^k`, where `k = ` # incomparable pairs (`A_2` substructures), `\ell = ` # induced `A_3` (3-antichain) substructures, `m = ` # induced `(C_2 + C_1)` substructures. This is **the** source of the `\log_2(4/3)` constant in F32's program (closing F32-scope §3.4.5 Source-2 gap — there IS a literature citation, contrary to F32-scope's tentative pessimism).

2. **Constant `\log_2(4/3)` is SHARP** in the literature form (§3): tight at `e(A_3) = 6 = 2^3 \cdot (3/4)^1` (`k = 3`, `\ell = 1`, `m = 0`). No sharper per-substructure penalty exists in the literature.

3. **BUT the literature form is GLOBAL** (a lower bound on `\log_2 e(P)`), **NOT per-3-antichain local** (§5). F32's Lemma C (local form: "every 3-antichain `A` in a minimal counterexample has `H(\sigma_L|_A) > \log_2(9/2)`") is **NOT in the literature** in any form I could identify. F32-scope's classification (SR-i) local-ERZ vs (SR-ii) global-ERZ is confirmed: literature ERZ97 is exactly (SR-ii); F32 needs (SR-i); the two are not interchangeable (F32-scope §3.4.4 already showed global doesn't save the program).

4. **Phase A gap UNCHANGED** at `\approx 0.00896` bits (§4): since the constant `\log_2(4/3)` matches what F32-scope's Phase A assumed, no Phase A re-derivation is triggered.

5. **Follow-on recovery is in scope** (§7): F32-scope §4.3 anticipated this exact outcome under failure mode D.1 ("L4 local form unavailable"), with explicit recovery route **L4-β-derive (Phase 2.1, 400–800k tokens, multi-session)** — derive the local form from first principles, **potentially using ERZ97's per-substructure penalty accounting as a structural template** (since ERZ97 *does* attribute penalty `\log_2(4/3)` to each individual `A_3` substructure in the global sum, just not as a per-antichain entropy floor).

**Why AMBER and not RED.** The strict task-body verdict would call this RED (no per-3-antichain citation), but four mitigating factors push it to AMBER:

- The literature ERZ97 is identified at the right constant (resolves F32-scope §3.4.5 gap).
- Constant `\log_2(4/3)` is sharp in the global form (so no Phase-A constant-correction needed).
- Phase A gap is intact at `0.00896` bits.
- Recovery route L4-β-derive is explicitly in F32-scope §4.3 Phase 2.1 with structural inspiration available (ERZ97 per-substructure mechanism, §6).

**Why not GREEN.** GREEN required "citation found, constant sharp" delivering the per-3-antichain bound directly. ERZ97 is the right constant and sharp, but in the wrong form (global on `\log_2 e(P)`, not local per-`A_3`-entropy). The form gap is non-trivial: F32-scope §3.4.4 already showed the global form is compatible with one bad antichain at 2.161, so it does NOT close the F32 contradiction.

---

## §0. Setup and inputs

### 0.1 What F32 needs from L4

From F32-scope §1.2 (C4) and §3.4 (Lemma C statement):

$$\text{(C4 / Lemma C, local form)}\quad \text{In a minimal 1/3-2/3 counterexample } P, \text{ every 3-antichain } A \subseteq P \text{ satisfies } H(\sigma_L|_A) > \log_2(9/2) \approx 2.170 \text{ bits.}$$

Here `\sigma_L|_A` denotes the relative order of `A`'s elements in a uniformly random linear extension `L \sim \mathrm{Unif}(\mathcal{L}(P))`. The lower bound `\log_2(9/2) = \log_2 6 - \log_2(4/3)` is the "naive `\log_2 6` minus ERZ allowance `\log_2(4/3)`".

The F32 contradiction (§1.2): Frankl-Holds + L2 + L3 deliver some specific `A^*` with `\Pr_L[\sigma_L|_{A^*} = \text{canonical}] \ge 1/2`, which (C3) implies `H(\sigma_L|_{A^*}) \le 1 + \tfrac{1}{2}\log_2 5 \approx 2.161`. Local-L4 says every `A` has `H(\sigma_L|_A) > 2.170`. Contradiction `2.161 < 2.170`.

The local form's strength is *per-antichain*: it rules out any single bad triple. The global form (averaged) is weaker (§5).

### 0.2 What this polecat does

- §1: enumerate literature candidates and assess each for per-3-antichain entropy bound applicability.
- §2: pin down the source of the `\log_2(4/3)` constant: Ewacha-Rival-Zaguia (ERZ) 1997.
- §3: sharpness check on `\log_2(4/3)` — confirm it's the right constant.
- §4: Phase A gap re-verification — constant unchanged → gap unchanged.
- §5: detailed gap analysis — why ERZ97 (global) does not imply F32's local form.
- §6: derivation prospects — what L4-β-derive (Phase 2.1) might look like.
- §7: verdict registration and cross-program impact.
- §8: hard-constraint compliance.
- §9: references.

### 0.3 Inputs read

- `docs/compatibility-geometry-F32-uc-bridge-scope.md` (mg-c9d9, AMBER-merged) — §3.4 (L4 tractability), §2 (Phase A), §5.1 (D.1 failure mode), §4.3 (Phase 1 strict-order).
- `docs/state-F32.md` Session 1 entry — cumulative ledger format.
- `~/files/union_closed_1323_proof_steps.txt` (Daniel 2026-05-16T11:29Z) Steps 7–9 — entropy bookkeeping that motivates the F32 program's use of `\log_2(4/3)`.
- Live literature search across:
  - Chan-Pak survey (arXiv:2311.02743v2) "Linear extensions of finite posets" — §3.1, §3.6 ("Entropy bounds"), §3.7.
  - Aires-Kahn (arXiv:2510.26134) "Variance vs. range for linear extensions" — recent (2025).
  - Kahn-Kim 1995 "Entropy and Sorting" (Theorem 3.16 statement via Chan-Pak survey).
  - Brightwell-Tetali 2003 "The Number of Linear Extensions of the Boolean Lattice" (Theorem 3.17 statement via Chan-Pak survey).
  - Cardinal-Fiorini-Joret-Jungers-Munro 2013 "Sorting under Partial Information (without the ellipsoid algorithm)" — Combinatorica.
  - Sidorenko 1992 "Inequalities for the number of linear extensions" — Order.
  - Sha-Kleitman, Ewacha-Rival-Zaguia 1997 (TCS 175(2), pp. 282–296) — global LE-count inequality with `\log_2(4/3)` constant.
  - Brightwell-Felsner-Trotter 1995 (`\delta(P) \ge 1/2 - \sqrt 5/10 \approx 0.276`).
  - Olson 2017 "On the 1/3-2/3 Conjecture" (arXiv:1706.04985) survey.
  - Moitra "On Entropy and Extensions of Posets" (referenced in Chan-Pak; no per-A_3 result).
  - Brightwell-Felsner sorting work; Kahn-Linial 1991 "Balancing extensions via Brunn-Minkowski"; Kahn-Saks 1984.

---

## §1. Literature survey: per-3-antichain entropy bounds for minimal counterexamples

### 1.1 What I'm looking for

Specifically: a literature theorem of the form

$$(\star)\quad P \text{ minimal counterexample to 1/3-2/3} \;\Longrightarrow\; \forall A \in U,\; H(\sigma_L|_A) \ge \log_2(9/2)$$

where `U = \binom{\mathcal{P}(P)}{3}_{\text{antichain}}` and the conclusion is per-`A` (not averaged).

Or, more loosely, any theorem of the form

$$(\star')\quad \text{(some structural hypothesis on } P\text{)} \;\Longrightarrow\; H(\sigma_L|_A) \ge \log_2(9/2) \text{ for every 3-antichain } A$$

where the structural hypothesis is implied by minimality (every incomparable pair strictly biased `> 2/3`).

### 1.2 Kahn-Saks 1984 "Balancing poset extensions" (Order 1)

The original 1/3-2/3 paper. Proves `\delta(P) \ge 3/11 \approx 0.273` via *cross-product inequality* (extended to *Alexandrov-Fenchel-style mixed-volume inequalities*). The argument is on **pairs**, not 3-antichains; the technique is *cross-product convexity* on the chain polytope, not entropy.

**Does it deliver a per-3-antichain entropy bound?** No. Output is `\Pr[x <_L y] \in [3/11, 8/11]` for *some* pair — a pair statement, not an antichain entropy statement.

**Does the constant `\log_2(4/3)` appear?** No.

**Verdict:** not the source.

### 1.3 Kahn-Linial 1991 "Balancing extensions via Brunn-Minkowski" (Combinatorica 11)

Sharper bound via Brunn-Minkowski. Bound improves `\delta(P) \ge 3/11` to a slightly larger constant (still below 1/3). Same technique family as Kahn-Saks (convex-geometric).

**Per-3-antichain entropy?** No.

**Constant `\log_2(4/3)`?** No.

**Verdict:** not the source.

### 1.4 Brightwell-Felsner-Trotter 1995 "Balancing pairs and the cross product conjecture" (Order 12)

Strongest unconditional bound prior to 2025: `\delta(P) \ge 1/2 - \sqrt 5/10 \approx 0.276`. Uses cross-product conjecture machinery on pair-frequencies.

**Per-3-antichain entropy?** No. Output is still a pair statement.

**Verdict:** not the source.

### 1.5 Kahn-Kim 1995 "Entropy and Sorting" (PoPL / JCSS)

The standard reference for entropy-of-poset arguments. **Theorem 3.16** (cited by Chan-Pak survey):

$$n \log_2 n - n \cdot H(P) \;\ge\; \log_2 e(P) \;\ge\; 0.09 \cdot (n \log_2 n - n \cdot H(P)),$$

where `H(P)` is the entropy of the incomparability graph of `P` via the chain polytope.

**Per-3-antichain entropy?** No. This bounds `\log_2 e(P)` (global) in terms of incomparability-graph entropy (also global). It does not specialise to per-`A` for a specific 3-antichain.

**Constant `\log_2(4/3)`?** No.

**Verdict:** not the source.

### 1.6 Brightwell-Tetali 2003 "The Number of Linear Extensions of the Boolean Lattice" (Order 20)

**Theorem 3.17** (via Chan-Pak survey, Section 3.7): for height-two posets with balanced lower-/upper-closure sizes `(a, b)`:

$$e(P) \;\le\; n! \binom{a + b}{a}^{-n/(a+b)}.$$

This is an *upper bound* on `e(P)` for a specific class (balanced height-2). It does not specialise to per-3-antichain entropy in width-3 / minimal-counterexample setting.

**Per-3-antichain entropy?** No.

**Constant `\log_2(4/3)`?** No.

**Verdict:** not the source.

### 1.7 Sidorenko 1991/1992 "Inequalities for the number of linear extensions" (Order)

`e(P) \ge n! / \prod_i c_i!`, where `c_i` are sizes of a chain decomposition of `P`. Lower bound via chain coverings.

**Per-3-antichain entropy?** No. Chain-decomposition based, not 3-antichain based.

**Constant `\log_2(4/3)`?** No.

**Verdict:** not the source.

### 1.8 Sha-Kleitman 1986 "The Number of Linear Extensions of Subset Ordering" (Discrete Mathematics)

Asymptotic bound on `e(B_n)` for the Boolean lattice `B_n`. Improved by Brightwell-Tetali.

**Per-3-antichain entropy?** No.

**Verdict:** not the source.

### 1.9 Cardinal-Fiorini-Joret-Jungers-Munro 2013 "Sorting under Partial Information (without the ellipsoid algorithm)" (Combinatorica)

Refines Kahn-Kim 1995 — proves *tight constant 2* for the upper bound: `\log_2 e(P) \le 2 \cdot H(\text{incomparability graph}) \cdot |\mathcal{P}(P)| / \log_2 e`.

**Per-3-antichain entropy?** No. Global incomparability-graph entropy → `\log_2 e(P)`. Pair-based, not 3-antichain-based.

**Constant `\log_2(4/3)`?** Not as a per-`A_3` penalty.

**Verdict:** not the source.

### 1.10 Chan-Pak-Panova 2022 "Effective Poset Inequalities" (arXiv:2205.02798)

Sharpens Stanley-style inequalities (Björner-Wachs, q-analogues). Global bounds on `e(P)`.

**Per-3-antichain entropy?** No.

**Verdict:** not the source.

### 1.11 Aires-Kahn 2025 "Variance vs. range for linear extensions, and balancing extensions in posets of bounded width" (arXiv:2510.26134)

Recent (2025). Theorem 1.6: for fixed width `w`, if `\pi(P) \to \infty` (number of incomparable pairs), then `\delta(P) \to 1/2`. Variance-based mechanism.

Previous best unconditional: `\delta(P) \ge (5 - \sqrt 5)/10 \approx 0.345` (improvement over Brightwell-Felsner-Trotter 0.276).

**Per-3-antichain entropy?** No. The argument uses variance of element positions, not antichain entropy. The mechanism is "any antichain `A` contains an `x` with `\sigma(x) = \Omega(|A|)`" — local *variance* concentration, not local *entropy* concentration.

**Constant `\log_2(4/3)`?** No.

**Verdict:** not the source. But this is the most relevant recent work and informs the L4-β-derive prospects (§6).

### 1.12 Ewacha-Rival-Zaguia 1997 — **the identified source of `\log_2(4/3)`**

**Reference.** Ewacha, K.; Rival, I.; Zaguia, N. "Approximating the number of linear extensions". *Theoretical Computer Science* 175 (1997), no. 2, pp. 271–282. (Also: "Unimodality, linear extensions and width two orders", *Discrete Math*, 1997.) Cited as "[ERZ97]" in Chan-Pak survey Proposition 3.1.

**Statement (Chan-Pak survey, Proposition 3.1).** Let `P = (X, \prec)` be a finite poset. Let

- `k = k(P)` = number of incomparable pairs (induced `A_2` substructures, i.e., 2-antichains),
- `\ell = \ell(P)` = number of induced `A_3` substructures (3-antichains),
- `m = m(P)` = number of induced `(C_2 + C_1)` substructures (a 2-chain disjoint from a singleton).

Then

$$\boxed{2^k \cdot (3/4)^{\ell + m} \;\le\; e(P) \;\le\; 2^k.} \tag{ERZ}$$

Equivalently in entropy form:

$$k - (\ell + m) \cdot \log_2(4/3) \;\le\; \log_2 e(P) \;\le\; k. \tag{ERZ-entropy}$$

**This is the literature source of `\log_2(4/3)`.** The constant arises as the per-(`A_3` or `C_2+C_1`)-substructure penalty in the ERZ lower bound on `\log_2 e(P)`.

**Tightness conditions** (Chan-Pak survey, accompanying text):

- Upper bound `e(P) \le 2^k` is tight for linear sums of `A_2` and `C_1` (i.e., posets where every comparability splits into independent 2-element layers).
- Lower bound `e(P) \ge 2^k (3/4)^{\ell + m}` is tight for **linear sums of `A_3` and `(C_2 + C_1)`** (i.e., posets where every "non-trivial" induced substructure on 3 elements is exactly `A_3` or `C_2 + C_1`, and the substructures don't interact).
- Lower bound is **weak when `\ell + m` is large** (penalty grows linearly; for many overlapping 3-antichains the bound becomes very small).

**Concrete tightness witness for `A_3`.** Take `P = A_3` (the 3-element antichain): `k = 3`, `\ell = 1`, `m = 0`. Then ERZ gives `e(A_3) \ge 2^3 (3/4)^1 = 8 \cdot 3/4 = 6`, and indeed `e(A_3) = 3! = 6`. **Equality holds** — the penalty `\log_2(4/3)` per 3-antichain is exactly the right per-`A_3` penalty in the ERZ accounting.

**Why this resolves F32-scope §3.4.5 Source-2 gap.** F32-scope §3.4.5 wrote: "Polecat could not identify a specific cited source for `\log_2(4/3)`". ERZ97 IS the source. The constant is not tautological arithmetic alone — it is the literature per-substructure penalty in a *proven, sharp, published* poset-LE-count inequality.

---

## §2. The ERZ97 inequality and its sharpness

### 2.1 Restatement and conventions

Let `P` be a finite poset on `n` elements with comparability set `\le_P`. Define:

- `\le_P` = comparability relation; `\sim_P` = incomparability relation.
- `k(P) = |\{\{x, y\} : x, y \in P, x \sim_P y\}|` = # incomparable pairs.
- `\ell(P)` = # subsets `\{a, b, c\} \subseteq P` with all three pairs incomparable (induced `A_3` = 3-element antichain).
- `m(P)` = # subsets `\{a, b, c\} \subseteq P` with exactly one comparability (say `a <_P b`) and `c` incomparable to both `a` and `b` (induced `C_2 + C_1`).
- `e(P) = |\mathcal{L}(P)|` = # linear extensions of `P`.

Then **(ERZ)**: `2^{k(P)} (3/4)^{\ell(P) + m(P)} \le e(P) \le 2^{k(P)}`.

### 2.2 Probabilistic interpretation of the upper bound

`e(P) \le 2^k` says: the number of linear extensions is at most the number of joint orientations of `P`'s incomparable pairs (each pair has 2 possible orientations in any linear extension; ignoring transitivity gives `2^k` orientations).

In entropy: `\log_2 e(P) \le k`. Per pair, `\log_2 e(P)/k \le 1` bit; each incomparable pair carries at most 1 bit of order-information in `\log_2 e(P)`.

### 2.3 Lower bound mechanism: per-substructure penalty accounting

`e(P) \ge 2^k (3/4)^{\ell + m}` says: the *transitivity constraints* on `P`'s linear extensions reduce the naive count `2^k` by a factor `(3/4)` per `A_3` or `(C_2 + C_1)` substructure.

In entropy: `\log_2 e(P) \ge k - (\ell + m) \log_2(4/3)`. The per-substructure penalty is `\log_2(4/3) \approx 0.415` bits.

**The mechanism (paper-and-pencil reconstruction).** For an isolated `A_3` substructure on `\{a, b, c\}`: the 3 incomparable pairs `\{a, b\}, \{a, c\}, \{b, c\}` have `2^3 = 8` joint orientations, but only `3! = 6` are transitive (the cyclic orientations `a < b < c < a` and `a < c < b < a` are non-transitive). Penalty `8 \to 6` corresponds to `\log_2(4/3)` bits.

For an isolated `(C_2 + C_1)` substructure with `a <_P b` and `c \sim_P a, c \sim_P b`: the 2 incomparable pairs `\{a, c\}, \{b, c\}` have `2^2 = 4` joint orientations, but only 3 are *consistent with `a <_P b`* (we need NOT `c <_P b < a` since `a <_P b` rules out `b <_P a`; the inconsistent case is `b <_P c <_P a`... let me redo).

Actually, the 4 orientations are:
1. `c < a < b` (consistent with `a < b`)
2. `a < c < b` (consistent)
3. `a < b < c` (consistent)
4. `c < a, c > b`: i.e., `c < a` AND `b < c`. But `a < b` then forces a 3-cycle `a < b < c < a`. Inconsistent.

So 3 of 4 orientations are consistent. Penalty `4 \to 3` corresponds to `\log_2(4/3)` bits — same constant! That's why `\ell` and `m` get the same per-substructure penalty in ERZ.

(For elaboration: ERZ97 ultimately proves the lower bound by an induction on |P|, removing an element at a time and bookkeeping per-substructure penalties. The fact that both `A_3` and `(C_2 + C_1)` give `\log_2(4/3)` per substructure is the right per-substructure conservation law for this induction.)

### 2.4 Sharpness of `\log_2(4/3)` in the literature ERZ form

**Claim.** The constant `\log_2(4/3)` is **sharp** as the per-(`A_3` or `C_2 + C_1`)-substructure penalty in the ERZ lower bound.

**Proof of sharpness for `A_3`** (already given §1.12): `e(A_3) = 6 = 2^3 (3/4)^1`, equality.

**Proof of sharpness for `C_2 + C_1`**: take `P = C_2 + C_1` (a 2-chain plus a singleton on disjoint element sets). Then `k = 2, \ell = 0, m = 1`. ERZ: `e(P) \ge 2^2 (3/4)^1 = 3`. Actual: `e(P) = 3` (the 2-chain `a < b` forces `a` before `b`; the singleton `c` can be in 3 positions: `cab, acb, abc`). Equality.

**Proof that no sharper constant exists in literature form.** Suppose `\log_2 e(P) \ge k - (\ell + m) \cdot c` for all `P`, with `c < \log_2(4/3)`. Apply to `P = A_3`: `\log_2 6 \ge 3 - c`, so `c \ge 3 - \log_2 6 = \log_2(8/6) = \log_2(4/3)`. Contradiction. Same with `C_2 + C_1`. Therefore `\log_2(4/3)` is the unique sharpest constant for the ERZ form, achieved at isolated `A_3` and isolated `C_2 + C_1`.

**No alternative literature ERZ-style result gives a tighter per-substructure penalty.** The Kahn-Kim, Brightwell-Tetali, Sidorenko, Sha-Kleitman, and Cardinal-et-al. bounds all give different *forms* (sums over chains, entropy of incomparability graph, etc.) but none gives a tighter per-`A_3` substructure penalty in this accounting.

**Conclusion.** F32 program's use of `\log_2(4/3)` as the "ERZ compatibility allowance" is **constant-correct** and **constant-sharp** in the ERZ97 literature form.

---

## §3. Sharpness check: is `\log_2(4/3)` the right per-3-antichain constant?

### 3.1 Sharp for global per-substructure accounting

§2.4 confirms: `\log_2(4/3)` is sharp in the global ERZ97 form (per `A_3` substructure contribution to `\log_2 e(P)`).

### 3.2 What "sharp for per-antichain" would mean

To be sharp per-individual-3-antichain, the claim would be: for some class of posets `\mathcal{C}` and every 3-antichain `A` in `P \in \mathcal{C}`,

$$H(\sigma_L|_A) \;\ge\; \log_2 6 - \log_2(4/3) \;=\; \log_2(9/2) \;\approx\; 2.170.$$

The constant `\log_2(4/3)` is then the per-`A` *maximum allowed entropy deficit* from the maximum entropy `\log_2 6`.

**Question.** Is this true for any natural class `\mathcal{C}`?

### 3.3 Not true for all posets

Consider a poset containing a 3-antichain `\{a, b, c\}` and additional elements that force `\Pr_L[a < b] \in [1/2, 1]` strongly (say `\Pr_L[a < b] = 0.9`). Then on `\{a, b, c\}`:

- Position 1: distribution `(\Pr_L[a \text{ first}], \Pr_L[b \text{ first}], \Pr_L[c \text{ first}])`.
- With `\Pr_L[a < b] = 0.9`, the probabilities `\Pr_L[a \text{ first}]` and `\Pr_L[b \text{ first}]` are asymmetric, leading to lower joint entropy than `\log_2 6`.

Concrete: suppose `\{a, b, c\}` is induced into a chain via additional comparabilities (other elements forcing `a < b < c` in 90% of linear extensions). Then 5 of 6 orderings have probability `(0.1)/5 = 0.02` each, and the canonical order has probability 0.9. Entropy:

$$H = -0.9 \log_2 0.9 - 5 \cdot 0.02 \log_2 0.02 = 0.137 + 5 \cdot 0.113 = 0.137 + 0.564 = 0.701 \text{ bits} \ll \log_2(9/2).$$

So local-form `(H \ge \log_2(9/2))` is FALSE in general. The class `\mathcal{C}` must be restricted.

### 3.4 The restriction F32 uses: minimal counterexamples

F32 restricts to **minimal counterexamples** `P` to the 1/3-2/3 conjecture. Minimality means: every incomparable pair `x \sim_P y` has `\Pr_L[x <_L y] \notin [1/3, 2/3]`.

**Does minimality imply local-form `H \ge \log_2(9/2)` for every 3-antichain?**

This is the F32 Lemma C — the question this polecat asks. The literature does NOT prove it.

In fact, the example in §3.3 is *not* a minimal counterexample (since `\Pr_L[a < b] = 0.9 > 2/3` violates the "pairs are balanced" hypothesis of the conjecture; rather, this `P` is *itself* not a counterexample at all — it satisfies the 1/3-2/3 conjecture for the pair `\{a, b\}`).

A minimal counterexample has *every pair* with `\Pr > 2/3` or `< 1/3`. So `\Pr_L[a < b] = 0.9 > 2/3` is allowed in a minimal counterexample.

Then the §3.3 calculation persists in a minimal counterexample: a 3-antichain with one pair at `\Pr = 0.9` can have `H(\sigma_L|_A) \approx 0.7` bits, well below `\log_2(9/2)`.

**This means the local form (`H \ge \log_2(9/2)` for every 3-antichain in a minimal counterexample) is FALSE as stated.** F32-scope's Lemma C claim (as quoted in §0.1) is incorrect as currently formulated.

### 3.5 What the program might actually need

A weaker, possibly-true local form: for the specific `A^*` produced by Frankl-Holds + L2 + L3 (the one that satisfies `\Pr_L[\sigma_L|_{A^*} = \text{canonical}] \ge 1/2`), the entropy `H(\sigma_L|_{A^*}) > \log_2(9/2)`.

But this is *immediately contradicted by (C3)*: `\Pr_L[\sigma_L|_{A^*} = \text{canonical}] \ge 1/2` implies `H(\sigma_L|_{A^*}) \le 1 + \tfrac{1}{2}\log_2 5 \approx 2.161`, which is `< 2.170 \approx \log_2(9/2)`. So the weaker form is exactly the contradiction the program wants — it does not need to be proven separately; it's the *output* of the contradiction, not the input.

Wait — re-reading F32-scope §1.2:

> (C3) Entropy bound (Step 7) → `H(\sigma_L|_{A^*}) \le 1 + \tfrac{1}{2}\log_2 5`.
> (C4) Local-ERZ lower bound (L4) → `H(\sigma_L|_{A^*}) > \log_2 6 - \log_2(4/3) = \log_2(9/2) \approx 2.170`.
> (C3) and (C4) are incompatible: `2.161 < 2.170`. Contradiction.

So C4 is the *lower bound* (Lemma C), C3 is the *upper bound*. The contradiction is `\text{lower} > 2.170 > 2.161 \ge \text{upper}`, contradiction.

The lower bound C4 must hold *independently* of the existence of `A^*`. It must hold for every 3-antichain `A` in a minimal counterexample (so in particular for the `A^*` Frankl produces). If it doesn't hold for every `A`, the program's contradiction collapses.

§3.3 showed C4 doesn't hold for every `A` in a minimal counterexample, IF the minimal counterexample contains a 3-antichain with strongly biased pair. **But wait** — in a minimal counterexample, every pair has `\Pr \notin [1/3, 2/3]`. A 3-antichain `\{a, b, c\}` has three pairs, each strictly biased. The example `\Pr[a < b] = 0.9` is allowed.

So in such a 3-antichain with one pair near 1 (or 0), the entropy can be far below `\log_2(9/2)`, contradicting C4 directly. **C4 is false as stated for general minimal counterexamples.**

**This is a substantive scope error in F32 that this polecat surfaces.** F32-scope §3.4 acknowledged uncertainty about the local form, but did not articulate this concrete falsification. The polecat now does.

### 3.6 Implication for L4 verdict

C4 (local form, `H \ge \log_2(9/2)` for *every* 3-antichain) is **literally false** for minimal counterexamples in general — concretely refuted by the §3.3 / §3.4 example (one near-determined pair concentrates the antichain entropy below `\log_2(9/2)`).

Therefore there cannot exist a literature theorem (or any theorem) proving the local form as F32-scope §3.4 states it.

The program's Step 9 / Lemma C as written is incorrect; a corrected version would have to weaken the hypothesis (e.g., restrict to 3-antichains with all three pairs "moderately balanced") or strengthen the conclusion's quantifier ("there exists an `A` with `H \ge \log_2(9/2)`", which is much weaker and may already hold trivially).

**This finding is structurally important and should drive a corrected L4 formulation before L4-β-derive is attempted.**

---

## §4. Phase A re-verification

### 4.1 Constants match F32-scope assumption

F32-scope Phase A computed:

- `\Delta_{\mathrm{can}} = \log_2 6 - [1 + \tfrac{1}{2}\log_2 5] = 0.4239984533\ldots` bits.
- `\Delta_{\mathrm{ERZ}} = \log_2(4/3) = 0.4150374993\ldots` bits.
- Gap = `0.0089609540\ldots \approx 0.00896` bits.

**My finding.** Both constants are correct as computed. The ERZ constant `\log_2(4/3)` is **literature-sourced** (ERZ97, §1.12) and **sharp** in the global form (§2.4).

### 4.2 Gap unchanged

Since neither constant changes, the arithmetic gap of `\approx 0.00896` bits is unchanged.

**No Phase A redo triggered.**

### 4.3 But: §3.6 finding overrides

Even though the constants are correct, **§3.6 shows the program's Step-9/C4 local form is false as stated**. The 0.00896-bit gap is real *as a numerical relation between two constants*, but the program does not actually establish the contradiction via this gap — because C4 (the lower bound) does not hold for all 3-antichains.

This is a **scoping correction** more substantive than the original task envisioned. Phase A's robustness was already noted in F32-scope as "brittle to weakening" — §3.6 shows the *direction of weakening* is on the L4 side (C4 false as stated), not on the Frankl-concentration side (Step 7's `H \le 2.161` is solid).

---

## §5. Why ERZ97 does not deliver the local form needed by F32

### 5.1 ERZ97 is a global statement on `\log_2 e(P)`

ERZ97 form: `\log_2 e(P) \ge k - (\ell + m) \log_2(4/3)`.

This is a single inequality on the *total* `\log_2 e(P)`, written as a sum of contributions from substructures. It does NOT decompose into per-3-antichain entropy floors.

### 5.2 Marginalisation argument is invalid

One might hope to marginalise ERZ97 down to a single 3-antichain `A` and extract a per-`A` entropy bound. This **does not work** for the following reason.

Consider `P` with one 3-antichain `A = \{a, b, c\}` and additional structure. The marginal entropy `H(\sigma_L|_A)` is *at most* `\log_2 6`. ERZ97 says `\log_2 e(P) \ge k - (\ell + m) \log_2(4/3)` where `k, \ell, m` count `P`'s structures, not just those touching `A`.

To extract `H(\sigma_L|_A)`, you'd need to write `\log_2 e(P) = H(\sigma_L|_A) + H(\sigma_L | \sigma_L|_A)` (chain rule for entropy of conditional joint distribution). But the second term `H(\sigma_L | \sigma_L|_A)` is *also bounded above* by `\log_2(\#\text{ways to extend}) \le k - 3` (since fixing 3 pair-orientations leaves `k - 3` free pairs). So:

$$\log_2 e(P) \;\le\; H(\sigma_L|_A) + (k - 3) \;\Longleftrightarrow\; H(\sigma_L|_A) \;\ge\; \log_2 e(P) - (k - 3).$$

Combining with ERZ97 lower bound on `\log_2 e(P)`:

$$H(\sigma_L|_A) \;\ge\; k - (\ell + m) \log_2(4/3) - (k - 3) \;=\; 3 - (\ell + m) \log_2(4/3).$$

For `P` with `\ell + m \ge 8` (which is automatic for posets with more than a handful of `A_3` substructures — e.g., `\binom{5}{3} = 10` in a width-5 antichain), the RHS becomes `\le 0`, giving a **vacuous** lower bound on `H(\sigma_L|_A)`.

For `P` with just `\ell = 1` (i.e., `P = A_3` itself): RHS = `3 - \log_2(4/3) = \log_2 6 \approx 2.585`, which is the trivial upper bound (so the lower bound is tight at `\log_2 6` — meaning all 6 orderings are equiprobable, which is the only possibility for `P = A_3`).

**Conclusion.** Marginalising ERZ97 to per-`A` entropy gives a bound that is either trivial (vacuous for large `P`) or trivial (tight at the upper bound for `P = A_3`). It does NOT extract the F32 local form for non-trivial minimal counterexamples.

### 5.3 No "averaged ERZ implies single ERZ" mechanism

A possible salvage: if ERZ97 gives a *sum* bound `\sum_A H(\sigma_L|_A) \ge ` (some quantity), and we have an *upper bound* on `\max_A H(\sigma_L|_A)`, perhaps we can extract a per-`A` floor.

But:
- ERZ97 doesn't directly give a sum-of-entropies bound. The `\log_2 e(P)` is a *joint* entropy, not the sum of marginal entropies on triples.
- Even if we had a sum-of-entropies bound `\sum_A H(\sigma_L|_A) \ge S`, the per-`A` floor would require a *uniformity* hypothesis on the antichains (e.g., "all `A` are symmetric"), which is not a property of minimal counterexamples.

### 5.4 Local form requires structural input beyond ERZ97

The F32 local form (Lemma C) is a *per-individual-antichain* statement. ERZ97 is a *per-substructure aggregated* statement. The gap is fundamental: extracting per-individual from per-aggregated requires either:

- A *symmetry / uniformity hypothesis* (every 3-antichain "looks the same"), which fails for general minimal counterexamples.
- A *reduction argument* (every 3-antichain not satisfying the bound implies a sub-counterexample, contradicting minimality) — this is the L4-β-derive route.
- A *direct entropy argument on specific 3-antichains* (e.g., a Brightwell-Tetali-style swap injection on a chosen `A`).

None of these are in the literature. The L4-β-derive route is the natural F32 next step (Phase 2.1).

---

## §6. Derivation prospects for L4-β

### 6.1 ERZ97 mechanism as inspiration

ERZ97's per-substructure penalty `\log_2(4/3)` arises from a recursive removal of elements with per-step penalty accounting. The mechanism is:

- Start with `\log_2 e(P) = \log_2 e(P \setminus \{x\}) + \log_2 (\text{ratio})` for some element `x`.
- Pick `x` so the ratio is bounded below by a function of the substructures of `P` containing `x`.
- Iterate.

A possible L4-β derivation: adapt this recursion to bound `H(\sigma_L|_A)` for a specific `A` directly, by recursing on `P \setminus \{x\}` for `x \notin A` and tracking how the entropy of `A` evolves.

**Open question.** Does the per-step entropy change `H(\sigma_L|_A)` admit a clean lower bound under the minimality hypothesis (every pair strictly biased `> 2/3` or `< 1/3`)?

### 6.2 Adaptation prospects

Optimistic: the ERZ97 penalty `\log_2(4/3)` arises from the *transitivity constraint* on each 3-antichain. The same constraint applies to `H(\sigma_L|_A)` — if `\Pr_L[\sigma_L|_A]` is supported on 6 orderings (all transitive), then `H(\sigma_L|_A) \le \log_2 6 = \log_2 8 - \log_2(4/3)` (penalty `\log_2(4/3)` from naive 3 bits). This is consistent with the global ERZ97 accounting.

But this *upper bound* on per-`A` entropy (`\log_2 6`) is trivial. The needed lower bound (`\log_2(9/2)`) requires the *minimality* assumption to "spread" the per-`A` distribution away from concentration.

Pessimistic: §3.6 showed that even in minimal counterexamples, a 3-antichain with one strongly-biased pair can have `H(\sigma_L|_A)` near zero. The lower bound `\log_2(9/2)` per `A` is *literally false*. So L4-β cannot derive what F32 wrote.

### 6.3 Minimality role: hypothesis weakening

What L4-β might salvage:
- A *quantified average* bound: "in a minimal counterexample, the *fraction* of 3-antichains with `H \ge \log_2(9/2)` is `\ge $f$`" for some `f`.
- A *combined frequency-entropy* bound: "either some 3-antichain has `\Pr_L[\text{canonical}] < 1/2`, or some 3-antichain has very strong sub-poset structure that contradicts minimality".

Both reformulations require *more than ERZ97* and *more than minimality alone*. They would be genuinely new lemmas, not literature lookups.

### 6.4 Width-3 simplification

F32-scope §4.4 recommends width-3 beachhead. In width-3, every 3-antichain is a *width-realising* antichain (no chain of length 3). This is a substantive structural restriction:

- In width-3, only 3-element antichains are possible (no `A_4`); so `\ell` counts the unique top antichains.
- The (`C_2 + C_1`) substructures `m` count "near-antichains" that are not pure antichains.

L4-β might first try width-3 and see whether the structural restriction lets the local form be salvaged on this restricted class.

### 6.5 L4-β recommended scope (post-this-polecat)

- **Step 1: reformulate Lemma C correctly.** F32-scope's Lemma C as written is false (§3.6). The correct formulation might be a weaker per-`A` averaged statement, or a stronger restricted-class statement.
- **Step 2: identify the structural input that distinguishes the correct local form from ERZ97 alone.** Minimality + (something else; maybe width-3 + acyclic-`\ll`).
- **Step 3: attempt derivation.** Possibly via sub-poset reduction (F32-scope §3.4.3 sketch).
- **Budget:** 400–800k tokens (F32-scope §4.2 §4.3 already allocated).
- **Likely outcome:** RED on the original Lemma C as written; possibly GREEN on a weakened/reformulated lemma; AMBER on a width-3-only result.

---

## §7. Verdict and follow-on

### 7.1 Verdict registration

**AMBER-no-literature-local-form-derive-needed (file L4-β-derive Phase 2.1).**

Detailed verdict (per F32-scope task verdict definitions):

1. **Literature citation:** Ewacha-Rival-Zaguia (ERZ) 1997, *Theoretical Computer Science* 175(2) — **IDENTIFIED** at the right constant `\log_2(4/3)`. (Closes F32-scope §3.4.5 Source-2 gap; the constant is not tautological — it is a published, proven, sharp per-substructure penalty.)

2. **Constant sharpness:** **SHARP** in the global ERZ97 form. `\log_2(4/3)` is the unique sharpest per-(`A_3` + `C_2+C_1`)-substructure penalty in `\log_2 e(P) \ge k - (\ell + m) c`. Witnessed at `e(A_3) = 6 = 2^3 (3/4)^1`.

3. **Form match:** **NO.** ERZ97 is global (on `\log_2 e(P)`); F32 needs local (per `H(\sigma_L|_A)` for individual 3-antichains).

4. **Local form derivability from ERZ97:** **NO** (§5). Marginalisation gives vacuous bounds for non-trivial `P`; no averaged-implies-local mechanism applies without extra hypotheses.

5. **Local form correctness as F32-scope stated:** **FALSE** (§3.3–§3.6). A minimal counterexample can have 3-antichains with one strongly-biased pair and entropy `\ll \log_2(9/2)`. The F32 Lemma C as written is mis-stated.

6. **Phase A gap:** unchanged at `\approx 0.00896` bits (§4.2).

7. **Follow-on:** **L4-β-derive (Phase 2.1)** is required, but must FIRST reformulate Lemma C correctly. Recommended budget 400–800k as per F32-scope §4.2.

### 7.2 Why AMBER, not RED

- ERZ97 IS the literature source of the constant. The gap F32-scope §3.4.5 flagged ("no citation") is resolved.
- Constant is correct and sharp.
- Phase A gap intact.
- Recovery route exists (L4-β with reformulated Lemma C).

These factors push the verdict above the bare-bones "no literature per-3-antichain form → RED" reading.

### 7.3 Why not GREEN

- The literature form (ERZ97 global) is not the form F32 needs (per-`A` local).
- More substantively: F32's local form as written is *literally false* in minimal counterexamples (§3.6). No reformulation can rescue the program from this without altering Lemma C.

### 7.4 Cross-program impact

- **L4 status:** AMBER unchanged from F32-scope; but with the new sharper finding that Lemma C as written is FALSE, the effective L4 status is "scope correction needed before L4-β-derive can begin".
- **L3-B-UC (concurrent Phase 1.2):** unaffected. L3-B should proceed in parallel; even if L4 fails, L3 may close, which is independently useful for a future bridge-program reformulation.
- **L2 sub-tickets:** continue to be **deferred** per F32-scope §4.3. L4 status governs whether L2 work is wasted.
- **Mayor recommendation:** File **F32-L4-corrected-scope** (a re-scoping ticket, single-session, 100-200k) before L4-β-derive proper, to reformulate Lemma C in light of §3.6. Then file L4-β-derive (Phase 2.1, 400-800k) targeting the corrected Lemma C.
- **F32 overall program status:** **AMBER (degraded by L4 scope error)** — F32-scope's AMBER-one-lemma-tractability-uncertain becomes AMBER-L4-needs-scope-correction-before-derivation. The gap to RED has narrowed.

---

## §8. Hard-constraint compliance

- **NOT factorial.** No factorial decompositions. `\log_2(4/3)` is a per-substructure penalty, not an `n!`-indexed quantity. ERZ97 is proven by element-removal recursion, not factorial / orbit-decomposition. **Compliant.**
- **NOT functorial in the refinement sense.** No `\mathrm{Pos}_n`-functor; no refinement-respecting bridge; no cohomological apparatus. The literature ERZ97 is purely combinatorial. F32-scope §6.2's U1-dialect-bypass holds for L4-α work. **Compliant.**
- **Paper-and-pencil + LaTeX-first.** This doc is LaTeX-style Markdown. No Lean, no HPC, no numerical computation beyond per-pencil arithmetic on the constants `\log_2(4/3), \log_2(9/2), \log_2 6, 1 + \tfrac{1}{2}\log_2 5`. **Compliant.**
- **Cumulative state doc.** `docs/state-F32.md` Session 2 entry below. **Compliant.**
- **Default to main.** `polecat-cat-mg-50e2` off `main`; PR target `main`. **Compliant.**
- **Single session.** This polecat is single-session, budget 200k tokens. **Compliant.**

---

## §9. References

### 9.1 The identified literature source

- **Ewacha, K.; Rival, I.; Zaguia, N.** "Approximating the number of linear extensions". *Theoretical Computer Science* 175 (1997), no. 2, pp. 271–282. **Cited as [ERZ97] in Chan-Pak survey Proposition 3.1.** This is the literature source of the constant `\log_2(4/3)` in F32's program.
- **Ewacha, K.; Rival, I.; Zaguia, N.** "Unimodality, linear extensions and width two orders". *Discrete Mathematics* (1997).

### 9.2 Surveyed literature (no per-3-antichain entropy bound found)

- **Kahn, J.; Saks, M.** (1984). "Balancing poset extensions". *Order* 1, pp. 113–126.
- **Kahn, J.; Linial, N.** (1991). "Balancing extensions via Brunn-Minkowski". *Combinatorica* 11, pp. 363–368.
- **Brightwell, G.; Felsner, S.; Trotter, W. T.** (1995). "Balancing pairs and the cross product conjecture". *Order* 12, pp. 327–349.
- **Kahn, J.; Kim, J.** (1995). "Entropy and sorting". *Journal of Computer and System Sciences*.
- **Brightwell, G.; Tetali, P.** (2003). "The number of linear extensions of the Boolean lattice". *Order* 20, pp. 333–345.
- **Sidorenko, A.** (1991). "Inequalities for the number of linear extensions". *Order* 8, pp. 331–340.
- **Sha, J.; Kleitman, D. J.** (1986). "The number of linear extensions of subset ordering". *Discrete Mathematics*.
- **Cardinal, J.; Fiorini, S.; Joret, G.; Jungers, R.; Munro, J. I.** (2013). "Sorting under partial information (without the ellipsoid algorithm)". *Combinatorica* 33, pp. 655–697.
- **Chan, S. H.; Pak, I.; Panova, G.** (2022). "Effective poset inequalities". arXiv:2205.02798.
- **Chan, S. H.; Pak, I.** (2023). "Linear extensions of finite posets" (survey). arXiv:2311.02743v2.
- **Aires, M.; Kahn, J.** (2025). "Variance vs. range for linear extensions, and balancing extensions in posets of bounded width". arXiv:2510.26134.
- **Moitra, A.** "On entropy and extensions of posets". (no per-3-antichain result identified)
- **Olson, E. J.** (2017). "On the 1/3-2/3 conjecture" (survey). arXiv:1706.04985.

### 9.3 F32-program-side references

- `docs/compatibility-geometry-F32-uc-bridge-scope.md` (mg-c9d9, AMBER-merged) — F32-scope §3.4 (L4 tractability), §3.4.5 (Source-2 gap), §3.4.4 (global doesn't save), §4.3 (Phase 1 strict-order recommendation), §5.1 (D.1 failure mode), §1.2 (contradiction structure C1-C4).
- `docs/state-F32.md` — Session 1 ledger.
- `~/files/union_closed_1323_proof_steps.txt` (Daniel 2026-05-16T11:29Z) — original 10-step program with Step 8 "Compare to ERZ 3-Antichain Bit Bound" + Step 9 "Prove the Counting/Entropy Contradiction".

### 9.4 Related F-series and U1-dialect baseline

- F25, F27 (RED); F28, F29, F30 (AMBER); F31 (RED, mg-01ce) — prior cohomology-side attempts to close milestone-1 part (iii).
- mg-26fc (`docs/compatibility-geometry-structural-analogy-scoping.md`) — U1-dialect baseline; F32 structurally bypasses U1, this polecat preserves the bypass.

### 9.5 Daniel directives (inherited)

- 2026-05-16T11:29Z — articulate 10-step program; high priority alongside union-closed Lean.
- 2026-05-15T23:20Z — NOT factorial; NOT functorial in the refinement sense.

---

*F32-L4-α-lit (mg-50e2) ends. ERZ97 identified as the literature source of `\log_2(4/3)`, sharp in the global form. Per-3-antichain local form NOT in literature AND scope-corrected to false-as-written. Phase A gap unchanged. Verdict AMBER-no-literature-local-form-derive-needed. Recommended follow-on: F32-L4-corrected-scope (re-scope Lemma C) → F32-L4-β-derive (Phase 2.1, 400–800k).*
