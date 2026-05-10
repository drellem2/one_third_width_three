# `InnerInequality_axiom` — independent verification

**Ticket.** mg-2f8c (cat-mg-2f8c), 2026-05-10. Trust-surface gate
ticket per Daniel directive 2026-05-08T16:11Z, parallel to mg-d731
(`cellMass_AD` GREEN at `f1c4a66`) and mg-e22f (`stanley_log_supermod`
GREEN at `f1c4a66`).

**Predecessor.** mg-87de (commit `3e509ff`), which introduced the
**fifth** named project axiom
`OneThird.RelationPoset.InnerInequality_axiom` (file
`lean/OneThird/Mathlib/RelationPoset/InnerInequalityAxiom.lean`)
under EX-7 Session C.6 / Option β.  mg-87de's audit-bar 4-condition
table is in `lean/AXIOMS.md`; this ticket extends that entry with a
"Separate verification" subsection cross-linking back to this
document.

**Scope.** Verification only.  **No Lean code changes** beyond the
AXIOMS.md write-up.  **No Lean source changes** to the axiom file
itself.

**Template.** Same structure as mg-d731
(`docs/path-alpha-execution-arc/cellMass-AD-verification.md`) and
mg-e22f
(`docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`).

> **TL;DR — TRIP-WIRE FIRED.**  §3 numerical sanity check finds
> **133 180 violations** of the axiom across 19 test posets / 1 431 564
> instances — including a **minimal counterexample on the 2-element
> antichain** where the inequality fails by `0 < 1`.  The axiom as
> declared in `InnerInequalityAxiom.lean:159–165` is mathematically
> **false**: it allows the master theorem
> `probEvent'_mono_of_subseteq_upClosed` to derive `1/2 ≤ 0` on the
> same minimal instance, exposing an unsoundness in the EX-7 trust
> surface.  Per the polecat brief's trip-wire spec ("numerical
> violation = URGENT mail Daniel + revert mg-87de + halt sub-α-C"),
> this triggers immediate URGENT mail to Daniel and a recommendation
> to revert mg-87de.  Verdict: **RED.**

---

## §1 Recap of the statement

For a finite poset `Q : RelationPoset α` with carrier `α`, a pair
`(a, b)` of `Q`-incomparable elements (`hba : ¬ Q.le b a`,
`hab : ¬ Q.le a b`), a level `k ∈ {0, …, |α|}`, and an event
`S : Finset α → Prop` that is **up-closed** under inclusion
(`I ⊆ J → S(I) → S(J)`), write

* `Q⁺ := addRel Q a b hba` — `Q` augmented by the relation `a ≤ b`;
* `Q⁻ := addRel Q b a hab` — `Q` augmented by the relation `b ≤ a`.

The **single-edge inner inequality** as declared in
`lean/OneThird/Mathlib/RelationPoset/InnerInequalityAxiom.lean:159–165`
asserts:

$$
N(Q^-)\,\bigl|\{L \in \mathcal{L}(Q^+) : S(L_k)\}\bigr|
\;\ge\;
N(Q^+)\,\bigl|\{L \in \mathcal{L}(Q^-) : S(L_k)\}\bigr|,
\qquad (\star)
$$

where `N(R) := |L(R)|` is the number of `R`-linear-extensions, and
`L_k := {x : (L.pos x).val < k}` is the level-`k` initial ideal
(the set of the first `k` elements of `L`).  The Lean encoding
(verbatim, `InnerInequalityAxiom.lean:159–165`):

```lean
axiom InnerInequality_axiom
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    InnerInequality Q hba hab k S
```

with `InnerInequality` unfolding (per
`DropsHeadlineMaster.lean:478–490`) to the rational-arithmetic
inequality `(Nm : ℚ) * (Mp : ℚ) ≥ (Np : ℚ) * (Mm : ℚ)` where the
four factors are the natural cardinality counts.

The **master theorem** `probEvent'_mono_of_subseteq_upClosed`
(`InnerInequalityAxiom.lean:213–222`) is derived from the axiom by
single-edge induction (`subseteq_addRel_induction`, mg-934f), and
reads

$$
\Pr_{L \sim \operatorname{Unif}\mathcal{L}(Q)}[S(L_k)]
\;\le\;
\Pr_{L \sim \operatorname{Unif}\mathcal{L}(Q')}[S(L_k)]
\qquad \text{for } Q \subseteq Q' \text{ and } S \text{ up-closed.}
$$

---

## §2 Cross-literature verification (≥ 3 sources, ≥ 3 decades)

The audit-bar `External` and `Low-risk` conditions per
`feedback_audit_bar_for_axioms` are met **as a literature claim** as
follows.  Each source listed below states or cites a "drops headline" /
"single-edge inner inequality" lemma in the spirit of `(\star)`;
coverage spans **four decades** (1970s, 1980s, 1990s, 2020s).

### §2.1 1970s — Preston (statistical-mechanics route)

#### S1. Preston 1974

* **Citation.**  C. J. Preston, *A generalization of the FKG
  inequalities*, Comm. Math. Phys. **36** (1974), no. 3, 233–241.
  **DOI:** 10.1007/BF01645981.
* **Verification.**  Project Euclid record confirmed at
  `https://projecteuclid.org/euclid.cmp/1103859733`.  Already cited
  in the project's `cellMass-AD-verification.md` (mg-d731 §2.1, S2).
* **Coverage.**  Preston's spatial-birth-and-death / continuous-spin
  extension of FKG / Holley involves a chamber-by-chamber pairing
  argument that is the literature ancestor of the LE-adjacent
  swap-with-conditional-AD (mg-afcf, `InnerInequalityAdjacent.lean`).
  Theorem 5.4 inner content is sometimes cited as a precursor to the
  drops headline single-edge step.

### §2.2 1980s — Daykin–Saks (the canonical citation)

#### S2. Daykin & Saks 1981

* **Citation.**  D. E. Daykin and M. Saks, *A natural generalization
  of the FKG inequality*, J. Combin. Theory Ser. A **30** (1981), no.
  2, 127–142.  (Some sources record the title as "*A poset version of
  the FKG inequality*"; both refer to the same paper.)
* **Verification.**  ScienceDirect record at
  `https://www.sciencedirect.com/science/article/pii/0097316581900536`
  (paper title and venue confirmed by independent search).
* **Coverage.**  Daykin–Saks 1981 is the canonical citation for the
  drops headline in the poset literature.  **However** (see §3 below
  and §4 verdict), the project has been citing Theorem 1 for the
  precise statement `(\star)` — and the numerical sanity check finds
  this statement **mathematically false** as written.  The Daykin–Saks
  1981 result must therefore be a **different** statement (most likely
  an FKG-style positive correlation between two up-closed events,
  not a single-event monotonicity-in-Q claim).  This is a **literature
  scope mismatch** that is the substantive root cause of the trip-wire
  (§4).

### §2.3 1990s — Brightwell §4 (project's primary cite)

#### S3. Brightwell 1999

* **Citation.**  G. Brightwell, *Balanced pairs in partial orders*,
  Discrete Mathematics **201** (1999), nos. 1–3, 25–52.
  **DOI:** 10.1016/S0012-365X(98)00311-2.
* **Verification.**  ScienceDirect record confirmed at
  `https://www.sciencedirect.com/science/article/pii/S0012365X98003112`.
  Cited verbatim in this tree as `\bibitem{Brightwell1999}`,
  `main.tex:557`; underpins the project's first named axiom
  `OneThird.LinearExt.brightwell_sharp_centred`.
* **Coverage.**  Brightwell §4 references the drops-headline-style
  argument as a chamber-by-chamber pairing via continuous AD.  Per
  the analysis in mg-7b85 / mg-afcf (state.md §1.29 / §1.30), the
  **natural pointwise four-function setup**
  `(𝟙_{O(Q⁻)}, 𝟙_{O(Q⁺)}·𝟙_S, 𝟙_{O(Q⁺)}, 𝟙_{O(Q⁻)}·𝟙_S)`
  was already verified to **fail** the pointwise four-function AD
  inequality at cube vertices.  This was a known structural finding
  (an early indication that something subtler was required), and
  the chamber-restricted-to-LE-adjacent infrastructure was landed
  in mg-afcf.  The numerical violation in §3 below is consistent
  with this picture: the literature-standard argument requires
  non-trivial additional structure (specifically, conditioning on
  the LE-adjacent chamber-pairing) that does **not** reduce to a
  universally-quantified-over-up-closed-S statement.

### §2.4 2020s — modern surveys

#### S4. Chan–Pak 2024 (linear-extensions survey)

* **Citation.**  S. H. Chan and I. Pak, *Linear extensions of finite
  posets*, EMS Surveys Math. Sci. (to appear); arXiv:2311.02743.
* **Verification.**  Already cited in
  `stanley-log-supermod-verification.md` §2.4 (mg-e22f, S6) and
  `cellMass-AD-verification.md` §2.5 (mg-d731, S10).
* **Coverage.**  The survey references the Daykin–Saks /
  Brightwell-style drops headline.  As with S2 / S3, the survey's
  presentation does **not** state `(\star)` for "any up-closed S"
  in the precise lean form — the closer reading distinguishes
  positive-correlation FKG (§9) from monotonicity-in-Q (which is
  a more restrictive statement).

### §2.5 Decade coverage and uncontested-status assessment

**Decades represented: 4** (1970s, 1980s, 1990s, 2020s).
**Sources cited: 4** (Preston, Daykin–Saks, Brightwell, Chan–Pak).
The **External** + **Low-risk** audit-bar conditions are met **for a
literature-standard "drops headline"** in the broad sense.

**However** — and this is the substantive finding of this
verification — **the precise universal-up-closed-S form of `(\star)`
encoded in the lean axiom does not match the literature**.  §3
below provides explicit numerical witnesses that `(\star)` (as
written) fails.  Inspection of the literature route (Brightwell §4
chamber-by-chamber argument; Preston cell-averaging; Daykin–Saks 4FT
framework) suggests the actual literature statement is **conditional
on additional structure** (chamber-restriction; LE-adjacent
sub-class; a specific four-tuple) that is not captured by "any
up-closed S".

The cross-literature §2 condition is therefore **PASS for the broad
drops-headline result** but **FAIL for the exact `(\star)` form** —
a literature-scope-mismatch finding rather than a literature-absence
finding.

**Verdict on §2.**  **PARTIAL PASS** (literature-scope mismatch).
The literature supports a drops-headline-flavoured result; the
specific universal-up-closed-S form is overgeneralised relative to
what the literature proves.

---

## §3 Numerical sanity check

### §3.1 Method

Brute-force verification of `(\star)` on small finite posets, every
`Q`-incomparable pair `(a, b)`, every level `k ∈ {0, …, |α|}`, and
every up-closed event `S : Finset α → Prop`.  The script
`scripts/innerInequality_check.py` (in this commit):

1. enumerates a representative collection of 19 finite posets
   spanning `|α| ∈ {2, 3, 4, 5}` (the same shape spectrum as
   `stanley_log_supermod_check.py` from mg-e22f, plus the project's
   downstream-relevant width-2 / width-3 layered shapes);
2. for each test poset `Q`, finds every `Q`-incomparable pair
   `(a, b)` with `a < b` lexicographically;
3. constructs `Q⁺ := addRel Q a b hba` and `Q⁻ := addRel Q b a hab`
   by adding the cover edge and taking transitive closure;
4. enumerates `L(Q⁺)` and `L(Q⁻)` exhaustively (small `|α|` makes
   this feasible);
5. for each level `k ∈ {0, …, |α|}` and each up-closed predicate
   `S` (enumerated as up-sets of `2^α` — the Dedekind-`D(|α|)`
   monotone Boolean functions), computes `Mp`, `Mm` and checks
   `Nm · Mp ≥ Np · Mm`.

The up-closed predicates are enumerated **exhaustively** for
`|α| ≤ 5`: `D(2) = 6`, `D(3) = 20`, `D(4) = 168`, `D(5) = 7581`
up-sets respectively (verified against the OEIS A000372 / Dedekind
numbers), so every up-closed event on the test posets is checked.

The script is independent of the Lean codebase: linear-extension
enumeration is implemented from scratch via maximal-element peeling
on the bitmask state.  Computations are exact over `ℕ` / `ℤ`, no
floating-point.

### §3.2 Test posets

19 posets spanning `|α| ∈ {2, 3, 4, 5}`, covering antichains,
chains, V/Λ/N/Diamond/Y/2+2 4-vertex shapes, width-2 / width-3
layered shapes (the project's downstream-relevant shapes per mg-87de
brief), the 2×2 product (a width-2 distributive lattice), and small
5-vertex extensions.

### §3.3 Result

| Quantity | Value |
|----------|------:|
| Posets tested | 19 |
| Total `Q`-incomparable pairs `(a,b)` | 63 |
| Total instances `(Q, a, b, k, S)` | **1 431 564** |
| Total tight (equality) instances | 1 160 490 |
| Total **violations** of `(\star)` | **133 180** |

**Coverage by `|α|`** (1 violation = 1 instance where
`Nm · Mp < Np · Mm`):

| `|α|` | Posets | Up-set families `D(n)` | Instances | Tight | Violations |
|------:|-------:|-----------------------:|----------:|------:|-----------:|
| 2     |      1 |                      6 |        18 |    16 |          1 |
| 3     |      5 |                     20 |       480 |   426 |         27 |
| 4     |      9 |                    168 |    21 000 | 18 278 |     1 361 |
| 5     |      4 |                  7 581 | 1 410 066 |1 141 770 |  131 791 |
| **Total** | **19** | (varies)             | **1 431 564** |**1 160 490** | **133 180** |

**Violation density.**  About 9.3 % of all checked instances violate
the inequality; the violations are not numerical-noise edge cases
but substantively fail by O(N) factors (e.g., `0 < 6` on the
3-antichain, `0 < 72` on the 4-antichain).

### §3.4 Minimal counterexample (n = 2)

The **smallest** counterexample is on the **2-element antichain** —
the simplest non-trivial case.

* **Poset.**  `Q = (α, ∅)` where `α = {0, 1}` and `Q.le x y ↔ x = y`
  (no relations beyond reflexivity).
* **Pair.**  `a = 0`, `b = 1`.  Both `hba : ¬ Q.le 1 0` and
  `hab : ¬ Q.le 0 1` are satisfied (Q is the antichain).
* **Augmented posets.**  `Q⁺ := addRel Q 0 1 hba` adds `0 ≤ 1`;
  `Q⁻ := addRel Q 1 0 hab` adds `1 ≤ 0`.
* **Linear extensions.**
  * `L(Q)`  has 2 elements: identity `(0, 1)` and swap `(1, 0)`.
  * `L(Q⁺)` has 1 element: identity `(0, 1)` (forces `0` before `1`).
  * `L(Q⁻)` has 1 element: swap `(1, 0)` (forces `1` before `0`).
* **Counts.**  `N(Q) = 2`, `Np = N(Q⁺) = 1`, `Nm = N(Q⁻) = 1`
  (and `N(Q) = Np + Nm = 1 + 1 = 2 ✓`).
* **Up-closed event.**  `S(I) := 1 ∈ I`.  Verify up-closedness: if
  `1 ∈ I` and `I ⊆ J`, then `1 ∈ J` ✓.  So `S` satisfies the lean
  axiom's `hSmono` precondition.
* **Filter cards at `k = 1`.**
  * `L(Q⁺) = {(0, 1)}`: `L_1 = {x : pos(x) < 1} = {0}`.
    `S({0}) = (1 ∈ {0}) = ⊥`.  `Mp = 0`.
  * `L(Q⁻) = {(1, 0)}`: `L_1 = {x : pos(x) < 1} = {1}`.
    `S({1}) = (1 ∈ {1}) = ⊤`.  `Mm = 1`.
* **Inner-inequality check.**  `(\star)` requires
  `Nm · Mp ≥ Np · Mm`:

$$
1 \cdot 0 \;\stackrel{?}{\ge}\; 1 \cdot 1
\quad\Longleftrightarrow\quad
0 \ge 1 \quad\textbf{FALSE.}
$$

* **Master theorem check.**  The lean
  `probEvent'_mono_of_subseteq_upClosed` (with `Q ⊆ Q⁺`) requires
  `Pr[S | Q] ≤ Pr[S | Q⁺]`:

$$
\Pr[S \mid Q] \;=\; \frac{|\{L \in L(Q) : 1 \in L_1\}|}{|L(Q)|} \;=\; \frac{1}{2},
\qquad
\Pr[S \mid Q^+] \;=\; \frac{0}{1} \;=\; 0,
$$

  $$
  \tfrac{1}{2} \stackrel{?}{\le} 0 \quad\textbf{FALSE.}
  $$

This is a **single concrete numerical instance** demonstrating the
unsoundness of `InnerInequality_axiom` (and consequently of the
master theorem `probEvent'_mono_of_subseteq_upClosed`) as currently
declared in lean.  The inputs (Q, a, b, k, S) all type-check against
the axiom's signature (`α : Type*` with `[DecidableEq] [Fintype]`,
`Q : RelationPoset α`, the two `¬ Q.le` hypotheses, `k : Fin 3`,
`S` decidable up-closed via `hSmono`).

### §3.5 Why the master theorem inherits the unsoundness

The lean axiom is consumed exactly once, at
`InnerInequalityAxiom.lean:222`, to discharge the
`InnerInequality`-hypothesis of the (sound) `_of_inner` reduction:

```lean
theorem probEvent'_mono_of_subseteq_upClosed ... :=
  probEvent'_mono_of_subseteq_upClosed_of_inner hQQ' k S hSmono
    (fun R _hRQ' _a _b hba hab => InnerInequality_axiom R hba hab k S hSmono)
```

The `_of_inner` lemma (mg-7a4f §5, `DropsHeadlineMaster.lean:548`)
is a **sound** implication: given the inner inequality on every
single-edge augmentation, derive the master inequality.  But because
the axiom asserts a **false** hypothesis universally, the lean
master theorem `Pr[S|Q] ≤ Pr[S|Q']` proves the same false statement
as `(\star)` does, on the same minimal `Q ⊂ Q⁺` / `S` instance.

Concretely: in lean, the term

```lean
probEvent'_mono_of_subseteq_upClosed
  (subseteq_addRel Q 0 1 hba) ⟨1, by decide⟩ (fun I => 1 ∈ I) hSmono
```

would have type `1/2 ≤ 0` after definitional unfolding — a `Prop`
the kernel will accept on the strength of the axiom alone.  This
exposes a **genuine logical unsoundness**: with `InnerInequality_axiom`
on the trust surface, `False` is derivable.

### §3.6 Trip-wire status

Per the polecat brief (mg-2f8c) §"Trip-wires":

> Trip-wires: numerical violation = URGENT mail Daniel + revert
> mg-87de + halt sub-α-C.

**Trip-wire status: FIRED.**

* 133 180 numerical violations across 19 test posets.
* Minimal counterexample on the **2-element antichain** —
  unambiguously inside the axiom's signature scope.
* Master theorem `probEvent'_mono_of_subseteq_upClosed` likewise
  fails on the same minimal instance (`1/2 ≤ 0` derivable from
  the axiom).

**Mandated actions (executed by this ticket):**

1. **URGENT mail to Daniel** (this commit; mailed at submission).
2. **URGENT mail to mayor** recommending revert of mg-87de
   (this commit; mailed at submission).
3. **Halt sub-α-C** advisory: any downstream sub-α-C ticket that
   consumes `probEvent'_mono_of_subseteq_upClosed` (EX-8 / EX-9 /
   case3-port / Brightwell-port-A) **must not proceed** until the
   axiom is corrected or replaced.

### §3.7 Likely root cause (for the revert / re-statement decision)

The numerical violations cluster around up-closed events `S` where
`b` "favours being early" (e.g., `S = (b ∈ I)`).  Adding `a ≤ b`
in `Q⁺` forces `b` to be later in linear extensions, which
**decreases** `Pr[S | Q⁺]` for such `S` — but the lean master
theorem claims `Pr[S | Q] ≤ Pr[S | Q⁺]`, i.e. that this probability
**increases**.  The implied inequality direction is the opposite of
what the underlying combinatorics gives.

Several diagnostic observations from this verification:

* **Reversing the inequality direction does not save the axiom.**
  The reversed form `Nm · Mp ≤ Np · Mm` (equivalently
  `Pr[S | Q] ≥ Pr[S | Q⁺]`) also fails on a 2-element-antichain
  counterexample, this time using `S = (0 ∈ I)`:
  `Mp = 1, Mm = 0`, so `1 · 1 ≤ 1 · 0` is also `False`.
* **Replacing "up-closed" with "down-closed" does not save it.**
  Both directions still admit counterexamples on `|α| = 2` for
  some down-closed `S`.
* **The natural pointwise four-function AD setup
  `(𝟙_{O(Q⁻)}, 𝟙_{O(Q⁺)}·𝟙_S, 𝟙_{O(Q⁺)}, 𝟙_{O(Q⁻)}·𝟙_S)`
  was already verified to fail pointwise** at cube vertices in
  mg-7b85 (state.md §1.29) and mg-afcf (state.md §1.30).
  The natural-direction continuous-AD route was therefore known
  to be insufficient — the axiom was added (mg-87de) on the
  premise that the literature still proves `(\star)` via a
  more delicate chamber-restricted argument.  The numerical
  evidence above suggests the literature actually proves a
  **different** (more restrictive / structurally constrained)
  statement than the lean encoding.

The most plausible correct restatement (not verified by this ticket;
flagged for Daniel / future polecat investigation) is that
Daykin–Saks 1981 / Brightwell §4 prove a **chamber-restricted** or
**FKG-positive-correlation** statement, not a single-event
monotonicity-in-Q for arbitrary up-closed `S`.  Either way, the
current lean encoding is over-general relative to the literature,
and the axiom must be either revised in scope, reversed in
direction (with a correspondingly restricted hypothesis), or
removed.

### §3.8 Sanity probes (the script is honest)

To rule out implementation bugs in the verifier:

* **`L(Q⁺) = 1` on the 2-antichain.** Hand-verified: the only LE
  respecting `0 ≤ 1` is `(0, 1)`. ✓
* **`L_1` semantics.** `L.initialIdeal' k = {x : pos(x) < k}` per
  `Birkhoff.lean:59`; for `k = 1` this is `{first element}`. ✓
* **`addRel Q a b hba` adds `a ≤ b`, not `b ≤ a`.**  Confirmed
  via `addRel_le` (`RelationPoset.lean:411–414`).
* **Up-set enumeration matches Dedekind numbers.**  Counts at
  `D(2), D(3), D(4), D(5)` are `6, 20, 168, 7581` per OEIS
  A000372. ✓
* **`MS = Mp + Mn` partition** (`filter_card_addRel_addRel_partition`,
  used in lean's `_of_inner` proof).  Confirmed numerically:
  every test poset satisfies `MS = Mp + Mm` for the underlying
  filter cards on the parent `Q`.

The verifier produces no false positives on chains (zero
incomparable pairs → zero instances → zero violations).  Its only
output on antichains is a count of substantive `lhs < rhs` failures.

---

## §4 Verdict

| Sub-check | Verdict | Evidence |
|-----------|---------|----------|
| §2 Cross-literature: ≥ 3 sources, ≥ 3 decades | **PARTIAL PASS** (literature-scope mismatch) | 4 sources / 4 decades support the broad drops-headline result; the precise universal-up-closed-S form is not what the literature proves |
| §3 Numerical sanity: 19 posets / 1 431 564 instances / **133 180 violations** | **FAIL** | `scripts/innerInequality_check.py` (this commit); minimal counterexample on the 2-antichain (`Q = empty antichain`, `a = 0, b = 1, k = 1, S = (1 ∈ I)`): `Nm · Mp = 0 < 1 = Np · Mm` |
| §2.5 Uncontested in literature | **N/A — preempted by §3 FAIL** | The numerical violation alone is decisive; further literature triage is the responsibility of the revert / re-statement decision |

**Overall verdict: RED.** Per the polecat brief's trip-wire spec:

> Trip-wires: numerical violation = URGENT mail Daniel + revert
> mg-87de + halt sub-α-C.

`InnerInequality_axiom` (mg-87de) is **mathematically false as
declared** in lean.  The minimal 2-element-antichain counterexample
makes the unsoundness fully concrete: `Pr[(1 ∈ L_1) | Q = ∅] = 1/2`,
`Pr[(1 ∈ L_1) | Q⁺ = (0 ≤ 1)] = 0`, and the master theorem claims
`1/2 ≤ 0` is provable in lean from the axiom.  This is a **genuine
logical unsoundness** of the EX-7 master theorem
`probEvent'_mono_of_subseteq_upClosed` and **all downstream sub-α-C
work that consumes it**.

**The `width3_one_third_two_thirds` headline trust surface is
UNCHANGED** by this finding (the headline does not consume the new
axiom — it remains on `brightwell_sharp_centred`,
`case3Witness_hasBalancedPair_outOfScope`, `stanley_log_supermod`,
and `cellMass_AD`).  The unsoundness is **localised to the EX-7
master theorem and forward-pointing sub-α-C tickets**.

**Trip-wires fired.** This commit:

1. URGENT-mails Daniel with full diagnostic;
2. URGENT-mails mayor recommending revert of mg-87de;
3. flags downstream sub-α-C consumers as halted pending
   axiom-re-evaluation.

---

## §5 References

* **S1.** C. J. Preston, *A generalization of the FKG inequalities*,
  Comm. Math. Phys. **36** (1974), no. 3, 233–241.
  DOI 10.1007/BF01645981.
* **S2.** D. E. Daykin and M. Saks, *A natural generalization of the
  FKG inequality*, J. Combin. Theory Ser. A **30** (1981), no. 2,
  127–142.
* **S3.** G. Brightwell, *Balanced pairs in partial orders*,
  Discrete Math. **201** (1999), nos. 1–3, 25–52.
  DOI 10.1016/S0012-365X(98)00311-2.
* **S4.** S. H. Chan and I. Pak, *Linear extensions of finite posets*,
  EMS Surveys Math. Sci. (to appear); arXiv:2311.02743.

**Ancillary references** (cited in adjacent project tree):

* `lean/AXIOMS.md` `OneThird.RelationPoset.InnerInequality_axiom`
  entry (mg-87de, audit-bar 4-condition table) — primary on-Lean
  disclosure surface; this ticket extends it with the §3 FAIL
  verdict.
* `lean/OneThird/Mathlib/RelationPoset/InnerInequalityAxiom.lean`
  — axiom declaration site (mg-87de).
* `lean/OneThird/Mathlib/RelationPoset/DropsHeadlineMaster.lean`
  — `_of_inner` reduction (mg-7a4f §5, sound).
* `lean/OneThird/Mathlib/RelationPoset/InnerInequality.lean`
  — chamber-integral / volume-form bridge (mg-7b85 §3, sound).
* `lean/OneThird/Mathlib/RelationPoset/InnerInequalityAdjacent.lean`
  — LE-adjacent swap infrastructure (mg-afcf, sound; the
  combinatorial input that **any** correct closure will reuse).
* `docs/path-alpha-execution-arc/state.md` §1.28–§1.31 — Sessions
  C.3–C.6 + this trip-wire (§1.32 to be added by this commit).
* `docs/path-alpha-execution-arc/cellMass-AD-verification.md`
  (mg-d731) — sister deliverable for the fourth project axiom
  (GREEN); this document is the parallel inner-inequality analog
  (RED).
* `docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`
  (mg-e22f) — sister deliverable for the third project axiom
  (GREEN).

---

*Verification complete; this document is part of the mg-2f8c
deliverable.  The trust-surface separate-verification bar of Daniel
directive 2026-05-08T16:11Z FIRED on this axiom: numerical sanity
sub-check FAILED with a minimal 2-element-antichain counterexample,
exposing a genuine logical unsoundness in
`InnerInequality_axiom` (mg-87de) and downstream consumers.  Per
the brief, mg-87de is recommended for revert and sub-α-C is halted
pending corrective action.*
