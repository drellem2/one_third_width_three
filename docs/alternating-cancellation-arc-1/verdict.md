# Alternating-Cancellation Lemma — verdict on conclusion-narrowness

> **EXPLORATORY ONLY — NOT a live program.**
>
> Deliverable C for `mg-acc8` (alternating-cancellation arc 1.0
> kickoff, polecat `pacc8`). This file aggregates the verdict
> on whether the Alternating-Cancellation Lemma's conclusion is
> narrow enough to drive Daniel's three-component "saturation
> lemma" trichotomy (N-poset core / reducible / balanced
> pair).
>
> See `lemma-statement.md` (Deliverable A) for the lemma
> formalisation and `verification.md` (Deliverable B) for the
> K=2 obstruction-family computations.

---

## 0. Aggregate verdict — **AMBER**

**The Alternating-Cancellation Lemma works in spirit as a
rigorous, tight inequality on `|Σ(α)|`, but its conclusion is
not narrow enough on its own to drive the trichotomy. The
"additional input" needed is paper-level math (a structure
theorem connecting LE-thinness patterns to poset-structural
properties), beyond polecat scoping authority.**

The three-deliverable summary:

* **Deliverable A** (`lemma-statement.md`): the lemma is
  rigorous in two equivalent forms (single direction,
  multi-direction commuting). The Bruhat-convex hypothesis
  is unnecessary. The "≪" form is `|Σ|/|L| ≤ 1 −
  m(α)/|L|` with `m(α) := max_{S non-adj} |D_S(α)|`.
* **Deliverable B** (`verification.md`): the bound is
  **tight** on every K=2 obstruction-family configuration
  tested (7 configs, including 3 case-2-strict siblings).
  Saturation (`|Σ|/|L| = 1/3`) is attained by exactly two
  small irreducible configs: K=2 N-poset and F1
  3-element minimal.
* **Deliverable C (this file)**: the lemma's saturation
  contrapositive identifies a `|L|/3`-sized set of "thin"
  LEs but does **not** by itself classify `α` into the
  trichotomy's three branches. Upgrading requires either
  (α) a bespoke combinatorial structure theorem (paper-tier),
  (β) a BK-walk spectral comparison theorem (the F5
  prerequisite from arc 4.0, paper-tier and unsolved in
  cited literature), or (γ) Steps 5–7 invocation (the F4-b
  trap, an explicit STOP trigger per the ticket's
  stop-loss). None are polecat-doable.

So **AMBER**: the lemma works, but its productive use
requires a follow-on input that is **not another polecat
session** — it is research-level conceptual / paper-level
math work, which falls under Daniel-only scope per
`feedback_audit_bar_for_axioms` and the ticket's
§Constraints.

---

## 1. What the lemma DOES give

### 1.1 The two rigorous lemma forms

**Lemma (single-direction).** For any finite poset `α` and
any `i ∈ {1, …, n−1}`,
`|Σ(α)| ≤ |L(α)| − |D_i(α)|`, where
`D_i(α) := { L : L[i], L[i+1] are α-incomparable }`.

**Lemma (multi-direction).** For any pairwise-non-adjacent
`S ⊆ {1, …, n−1}`,
`|Σ(α)| ≤ |L(α)| − |D_S(α)|`, where
`D_S(α) := ∩_{i ∈ S} D_i(α)`.

Both are tight on the K=2 obstruction family (Deliverable B
§8.1).

### 1.2 The saturation contrapositive

If `|Σ(α)|/|L(α)| = 1/3` (saturation), then
`m(α)/|L(α)| ≤ 2/3`. Equivalently, **at least `|L(α)|/3`
linear extensions are "thin"**: for each thin LE `L` and
every pairwise-non-adjacent `S`, at least one `i ∈ S` has
`τ_i · L ∉ L(α)`.

This is **rigorous, finite-`n`, exact-rational**. It is the
useful content of the lemma.

### 1.3 What the contrapositive identifies on saturating configs

On K=2 N-poset (`|Σ|/|L| = 1/3`): the 2 thin LEs are
exactly the **interleaving** extensions
`(x_1, y_1, x_2, y_2)` and `(x_2, y_2, x_1, y_1)`. The lemma
correctly singles them out as the LEs in which neither the
within-band-1 swap nor the within-band-2 swap is supported.

On F1-min (`|Σ|/|L| = 1/3`): the 1 thin LE is the
boundary-LE involving the strict ⪯-pair. The lemma
identifies it.

**This is a non-trivial structural identification.** The
thin LEs *are* the combinatorial signature of the
saturation. The lemma sees them.

---

## 2. What the lemma DOES NOT give

### 2.1 No classifier of `α` itself

The lemma's conclusion is about *which LEs* are thin, not
about *which structural class* `α` belongs to. From
"`α` has `≥ |L|/3` thin LEs," we cannot derive:

* `α` has an N-poset core.
* `α` is reducible.
* `α` admits a balanced pair.

These are properties of `α`, not of its LE-set's BK-graph
structure. To bridge the gap, a separate combinatorial
result is needed.

### 2.2 No converse on non-saturating configs

The contrapositive only fires when `|Σ|/|L|` is at
saturation. For non-saturating configs (most of the K=2
family at `n ≥ 5`), the lemma gives the inequality but no
structural pinch-point.

In particular, configurations like K2-N+e (`|Σ|/|L| = 1/5`)
have the lemma tight (`|Σ| = |L| − m = 1`), but the
saturation contrapositive doesn't fire — leaving the
case-2-strict structural inference unmade.

### 2.3 No connection to the trichotomy branches

Concretely, the trichotomy goal is:

> **Trichotomy:** sign-saturation `|Σ|/|L| = 1/3` ⟹ at
> least one of:
> * (i) `α` has an **N-poset-like core** (rigid 4-elem
>   irreducible structure with balanced pair at exactly
>   `1/3`);
> * (ii) `α` is **reducible** (admits a B1-style ordinal
>   cut);
> * (iii) `α` directly admits a **balanced pair** in
>   `[1/3, 2/3]`.

The lemma alone gives **none** of these. It only gives:
"there exist thin LEs". Whether thin LEs imply (i), (ii),
or (iii) is a **separate combinatorial question**.

The polecat could not locate a published theorem connecting
"BK-graph thin-LE pattern" to "α has structural property
P" in any form. The closest published frameworks (Bubley–
Dyer 1999 path coupling, Wilson 2004 sharp gap, Caputo 2008
octopus inequality, Diaconis–Saloff-Coste 1993 comparison
theorems) all operate at the spectral / mixing-time level,
not at the LE-structural level.

---

## 3. The "additional input" — three options, each blocked

To upgrade the lemma's contrapositive to a trichotomy
driver, one of the following is required:

### 3.1 Option (α) — Bespoke combinatorial structure theorem

A theorem of the form: *"For a layered width-3 poset `α`
with K = 2, if at least `|L(α)|/3` LEs are 'thin' (as
defined in §1.2), then `α` has structural property P," where
P is one of (i)/(ii)/(iii) of the trichotomy.*

**Plausibility.** The K=2 obstruction family is small
(small `n`, bounded width); the structure theorem is
plausibly tractable. The verification table (Deliverable B
§8.2) shows that on saturating configs (K2-N, F1-min), the
thin LEs exhibit a **specific combinatorial shape**
(interleaving / boundary). Generalising to "all K=2 layered
width-3 with `≥ |L|/3` thin LEs have one of (i)/(ii)/(iii)"
is an open combinatorial conjecture.

**Status.** **Unproven.** The polecat could not derive it
within budget. Per the ticket §Constraints:

> **No fresh paper-level math.** If proving the lemma
> requires a substantively new spectral / combinatorial
> theorem, STOP and escalate.

This is exactly the trigger.

**Disposition.** Daniel-only escalation. The structure
theorem is plausibly tractable as a research-level question
(the K=2 family is small enough), but the polecat does not
have the authority to produce paper-level math.

### 3.2 Option (β) — BK-walk eigenvalue / spectral comparison

Use the fact that `Σ(α)/|L(α)|` is the sign-isotypic
component of `1_{L(α)} ∈ L²(S_n)`, derive a BK-walk
eigenvalue bound, then apply Cheeger + Theorem E to
extract a balanced pair.

**Status.** This is the **F5 prerequisite** from arc 4.0
§6 (mg-0bc8). Per arc 4.0:

> The polecat believes Step 5 is **the** load-bearing
> prerequisite for Steps 1–2 to be even well-defined.
> Without it, the eigenvalue bounds are heuristic targets,
> not theorems.

Per the cross-field literature audit (mg-8baf §2.4 / 2.5.5):

> A SUGGESTIVE cluster (Caputo 2008 octopus / DSC 1993
> comparison / Bubley–Dyer 1999 path coupling / Wilson
> 2004 sharp gap) addresses adjacent infrastructure but
> applying it to "L(P) ⊆ S_n with adjacent-only,
> LE-restricted transitions" requires substantively new
> mathematical work (paper-tier infrastructure, ~2000+ LoC
> if formalised).

**Disposition.** Per the ticket §Stop-loss-triggers:

> **The polecat realizes the lemma is fundamentally a
> Caputo / octopus result** already in the SUGGESTIVE
> cluster (mg-8baf §2.4 / 2.1). If applying that machinery
> to L(P) directly works, GREEN; if it requires the F5
> prerequisite (S_n ↔ BK matching) that mg-8baf flagged as
> paper-tier, STOP and escalate.

The polecat investigated. **The lemma is not a Caputo /
octopus result directly applied to `L(P)`** — the
alternating-cancellation argument is purely combinatorial
(orbit-counting on `(Z/2)^k` actions) and gives the
inequality `|Σ| ≤ |L| − m(α)` without any spectral
machinery. So this stop-loss trigger does not fire on the
lemma *as a combinatorial inequality*.

But to convert **small `|Σ|`** to **balanced pair**
(trichotomy branch (iii)) **does** require the F5 spectral
prerequisite. Without F5, the lemma's contrapositive (small
`|Σ|`) gives no balanced-pair conclusion. **F5 is paper-tier
and outside polecat authority.**

### 3.3 Option (γ) — Steps 5–7 invocation

Appeal to the in-tree fiber-coherence / globalisation
machinery to convert "many low-fire LEs" into structural
rigidity.

**Status.** **F4-b trap** per arc 4.0 §4.2:

> If the proof of step 3 ("large E[fix] ⇒ rigidity")
> collapses to invoking the existing Steps-5-7 machinery,
> that's a sign the spectral framing is just relabelling.

**Disposition.** Explicit ticket stop-loss trigger:

> **The polecat's "locally thin" notion conflates with
> Steps 5-7 content** (the F4-b trap). If the proof of
> "locally thin → quotient-to-chain collapse" requires
> invoking fiber / coherence / globalization, STOP and
> report — the lemma reproduces arc 4.0's F4-b risk.

The polecat *did* investigate whether the lemma's
"thin-LE → structural collapse" implication requires
Steps 5–7. **Verdict:** the implication is not derivable
from the lemma alone, and the natural way to produce it
*does* require either (α) — a fresh combinatorial result —
or (γ) — Steps 5–7 invocation (which would be the F4-b
trap).

So **(γ) is the F4-b trap and is explicitly forbidden**.
The lemma cannot be promoted to a trichotomy driver by
invoking Steps 5–7.

---

## 4. Comparison to F1–F5

The lemma's status relative to the six structural facts
(F1/F2/F3 from `docs/why-hC3-is-structural.md`; F4-a/F4-b/F5
from arc 4.0):

| obstruction | how the lemma navigates / fails                                                        | verdict     |
|-------------|----------------------------------------------------------------------------------------|-------------|
| **F1** (cardinality / no order-preserving swap on strict ⪯-pair) | Lemma uses `L(α) ⊆ S_n`, not `Aut(α)`. **Genuinely navigates around F1.** | ✓ avoided |
| **F2** (Brightwell vacuity at K=2 / `|Q| ≤ 6`)                  | Lemma uses adjacent-transposition combinatorics, not single-element Brightwell. **Genuinely navigates around F2.** | ✓ avoided |
| **F3** (published `[0.276, 1/3)` gap)                            | Lemma is NOT a correlation-inequality refinement. **Genuinely navigates around F3.** | ✓ avoided |
| **F4-a** (K=2 N-poset has `|Σ|/|L| = 1/3` saturating)            | Lemma is *consistent* with F4-a — the saturation level is exactly at lemma's tight-bound on K=2 N-poset. The lemma uses F4-a as input, not as obstacle. | ✓ used as input |
| **F4-b** (Steps 5-7 collapse risk)                                | Promoting the lemma to a trichotomy driver requires either (α) or (γ); option (γ) IS the F4-b trap. **Explicit stop-loss.** | ✗ blocked   |
| **F5** (S_n ↔ BK matching / spectral comparison)                  | Option (β) requires F5; F5 is paper-tier per mg-8baf. **Beyond polecat authority.** | ✗ blocked   |

So the lemma navigates F1/F2/F3 cleanly (good — better than
arc 4.0, which also navigated them but introduced F4-a as a
new terminal obstruction). The lemma USES F4-a as an input
rather than tripping over it. But promoting the lemma to a
**trichotomy driver** runs into F4-b or F5, both blocked.

---

## 5. Trichotomy sketch — does the lemma support each branch?

For completeness, the polecat sketches what **would** be
needed to derive each trichotomy branch from the lemma's
output, *if* the additional input were available.

### 5.1 Branch (i) — N-poset-like core

**Goal:** `|Σ|/|L| = 1/3 ⟹ α` has 4 elements forming a
sub-poset isomorphic to N-poset (or 3 elements forming F1-min
sub-poset), with the rest of `α` "extending" via reducibility
or balanced pair.

**What the lemma supplies:** the `|L|/3` thin LEs are
identified. On K2-N and F1-min, these thin LEs **are** the
interleaving extensions characteristic of the structure.

**What's missing:** a result of the form *"if `α` has at
least `|L(α)|/3` interleaving thin LEs (in the lemma's
sense), then α contains a structural sub-N-poset / F1-pair
witnessed by the thin LEs."* This is option (α): a bespoke
combinatorial structure theorem.

**Sketch of how this might be proved** (non-rigorous, from
the polecat's reading): the thin LE patterns
identify pairs `(a, a')` with `upper(a) ⊊ upper(a')` (F1
pattern) or pairs of disjoint chains `x_i < y_i, x_j < y_j`
(N-poset pattern). A combinatorial counting argument might
show that `≥ |L|/3` thin LEs forces such a pair to exist.
But the polecat **cannot make this rigorous within budget**.

### 5.2 Branch (ii) — reducible

**Goal:** `|Σ|/|L| = 1/3 ⟹ α` admits a B1-style ordinal
cut (deep layered case).

**What the lemma supplies:** **nothing directly**. The
lemma's data is the BK fire-set `m(α)`, which doesn't
directly correspond to ordinal-cut structure.

**Counter-example to a naive bridge:** the K2-N is
**irreducible** but saturating; if "saturating ⟹ reducible"
held, we'd contradict K2-N's irreducibility (per
`feedback_n_poset_is_not_ordinal_sum`). So this branch
**cannot fire on K2-N** — but K2-N is supposed to be the
canonical `|Σ|/|L| = 1/3` config. **Reducibility cannot be
the universal dispatch.**

The trichotomy must therefore include branch (i) (N-poset
core) explicitly to cover K2-N. The lemma supports this only
if option (α) is unlocked.

### 5.3 Branch (iii) — direct balanced pair

**Goal:** `|Σ|/|L| = 1/3 ⟹ α` admits some pair `(a, b)`
with `Pr_α[a < b] ∈ [1/3, 2/3]`.

**What the lemma supplies:** small `|Σ|` ⇒ near-balance of
parity classes `|L_+|, |L_−|`. But parity classes are
**not** the same as balanced pairs (parity is sign-imbalance;
balanced pair is two-element-position-imbalance, a different
combinatorial measure).

**What's missing:** option (β) — a BK-walk spectral bound
turning small `Σ` into small λ_2(BK) into Cheeger
conductance into balanced pair. Per arc 4.0 §6, this is the
F5 prerequisite, paper-tier.

**Sanity check on K2-N:** K2-N has `|Σ|/|L| = 1/3`
(saturating, so this branch's antecedent fires). It also
has balanced pairs `{x_1, x_2}` and `{y_1, y_2}` at exactly
`1/2` (well within `[1/3, 2/3]`). So branch (iii) DOES fire
on K2-N. But the lemma alone doesn't produce this; we
verified by direct enumeration.

### 5.4 Net trichotomy verdict

The lemma supports each branch only conditionally on the
additional input:

* Branch (i): requires (α). Plausibly tractable.
* Branch (ii): requires (α). Sub-question of (α).
* Branch (iii): requires (β). Paper-tier (F5
  prerequisite).

**No combination of these is polecat-doable within scope.**

---

## 6. Stop-loss audit

Per the ticket §Stop-loss/block-and-report-triggers:

| trigger | fired? | response |
|---------|--------|----------|
| **Verification on the K=2 N-poset reveals the lemma is false** | NO  | Lemma is **true and tight** on K=2 N-poset (Deliverable B §1.5). |
| **The polecat's "locally thin" notion conflates with Steps 5-7 content (F4-b trap)** | YES (for trichotomy promotion) | The lemma itself is independent of Steps 5-7; **but** promoting it to a trichotomy driver via option (γ) IS the F4-b trap. **Explicit stop-loss; flagged §3.3.** |
| **The polecat realizes the lemma is fundamentally a Caputo / octopus result** | NO (the inequality is purely combinatorial) | The lemma's *inequality* is not a Caputo result. But option (β) (using small Σ to derive a balanced pair) **does** require the F5 prerequisite. F5 is paper-tier. **Escalation triggered for option (β); flagged §3.2.** |
| **Budget overrun > 350k tokens** | NO | This arc closed well under budget (~80k tokens estimated). |
| **Polecat surfaces a substantively new theorem required for the lemma's proof** | NO | The lemma's *proof* (Lemmas 2.1, 3.2 in `lemma-statement.md`) is elementary. The structural classifier (option (α)) IS substantively new but is **not** required to *state* the lemma; it is required to *use* the lemma for the trichotomy. **Escalation triggered for option (α).** |

So **two stop-loss-related triggers fire**:

1. **F4-b trap on option (γ)** — explicit forbid. We do not
   pursue this option.
2. **Paper-tier escalation on options (α) and (β)** — both
   require substantively new mathematical work. Daniel-only
   escalation per `feedback_audit_bar_for_axioms` and
   §Constraints.

The lemma itself (the rigorous inequality) is **fine** — it
is not flagged. What is flagged is its **usability for the
trichotomy**, which requires inputs the polecat cannot
produce.

---

## 7. Daniel-actionable next steps

If Daniel wishes to continue the bespoke-finite-rigid-
combinatorics direction (mg-344a) using this lemma as a
component:

### 7.1 Question to research (option α)

**"Is it true that any layered width-3 K=2 poset `α` with
at least `|L(α)|/3` thin LEs must satisfy one of: (i)
contains an N-poset sub-structure on 4 elements, (ii) is an
ordinal sum, or (iii) admits a balanced pair?"**

This is **a research-level combinatorial conjecture**. It is
plausibly tractable on the K=2 family (small enough). It
would need to be proved by:

* Direct case analysis on K=2 obstruction-family
  isomorphism classes (overlaps with mg-e112 §A
  enumeration when that lands).
* Or by a structural argument (e.g., a "thin LE structure
  theorem" extracting an N-poset / F1-pair from the BK fire
  pattern).

The polecat has **no existing path** to such a theorem in
cited literature. It would be a **fresh combinatorial
result**.

### 7.2 Question to research (option β)

**"Can the BK walk on `L(α) ⊆ S_n` be related to the
random-transposition walk on a larger ambient space such
that the sign-isotypic eigenvalue bound (for irrep `[1^n]`)
on the ambient walk transfers to the restricted BK walk?"**

This is the **F5 prerequisite** flagged in arc 4.0 §6. It
is paper-tier representation-theoretic / spectral-comparison
work; the polecat could not locate any published derivation.

The SUGGESTIVE cluster from mg-8baf §2.4 (Caputo 2008
octopus / DSC 1993 / Bubley–Dyer 1999 / Wilson 2004) is the
closest published machinery, but **applying it to `L(α)`
directly requires substantively new work** (paper-tier
infrastructure, ~2000+ LoC if formalised).

### 7.3 Recommendation

**The polecat recommends NOT commissioning a follow-on
polecat session.** Per the ticket §Daniel's framing:

> Daniel's directive included: *"this may have to be part
> of a larger effort to explore this part of the proof."*
> The polecat should treat this arc as **the first focused
> investigation**, not the comprehensive treatment. If
> verdict is AMBER and PM agrees with the polecat's
> "additional input needed" sketch, follow-on tickets file.

The "additional input" identified is **paper-tier
mathematics** (option α) or **the F5 prerequisite** (option
β). Per `feedback_audit_bar_for_axioms` and the ticket's
§Constraints, this is **Daniel-only conceptual work**, not
another polecat session.

If Daniel pursues this, the natural workspace is mg-344a's
"larger effort" framing. The polecat's three deliverables
(this arc) provide:

* A precise lemma statement (Deliverable A) — usable as a
  component in any future bespoke-combinatorics package.
* A verification table (Deliverable B) — usable as a test
  bed for any candidate "thin-LE structure theorem".
* A verdict (Deliverable C, this file) — usable as a
  reference for what's blocked and why.

---

## 8. References and memory anchors

### Internal documents

* `lemma-statement.md` (Deliverable A, this arc) — the
  lemma formalisation.
* `verification.md` (Deliverable B, this arc) — the K=2
  obstruction-family computation table.
* `docs/math-simp-arc-4.0/scoping.md` (mg-0bc8) — F4-a /
  F4-b / F5 obstructions.
* `docs/conceptual-arc-1/lit-audit.md` (mg-8baf) — F5
  SUGGESTIVE cluster references.
* `docs/why-hC3-is-structural.md` (mg-cda8) — F1/F2/F3
  framing.
* `docs/path-c-track-1-status-1.md` §2 (mg-b666) — F1
  minimal counterexample.

### Memory anchors applied

* `feedback_latex_first_for_math_simp` — applied (no Lean
  changes).
* `feedback_audit_bar_for_axioms` — applied (no axiom
  candidates surfaced; option β escalation flagged).
* `feedback_signature_regressions` — applied (no
  replacement of `hC3`).
* `feedback_n_poset_is_not_ordinal_sum` — applied (K2-N is
  the canonical first verification target; trichotomy
  branch (ii) cannot universally dispatch).
* `feedback_distinguish_arc_chunk_outcomes` — applied
  (outcome class: substantive scoping + verification, no
  parallel cleanup; AMBER verdict reported honestly).

### Cross-references to other tickets

* `mg-acc8` (this arc) — alternating-cancellation arc 1.0.
* `mg-344a` — Daniel's parallel workspace; this arc scopes
  one component of his three-component package.
* `mg-e112` — proof-approaches catalog (parallel polecat);
  potential parallel input on K=2 family enumeration.
* `mg-8baf` — cross-field lit audit; SUGGESTIVE cluster
  reference for option (β).
* `mg-0bc8` — arc 4.0; F4-a / F4-b / F5 framings.
* `mg-cda8` — F1/F2/F3 synthesis.

### Daniel directives

* In-session ~2026-05-05T~12Z: lemma sketch + "this may
  have to be part of a larger effort" framing.
* In-session ~2026-05-05T~11Z: "bespoke finite / rigid
  combinatorics on the quotient-to-chain frame" direction
  (mg-344a).

---

## 9. What this arc does NOT claim

Per `feedback_distinguish_arc_chunk_outcomes` and arc 3.0
§4.5 / arc 4.0 §9:

* Does **not** claim the trichotomy is unprovable — only
  that **the lemma alone is insufficient** to drive it.
* Does **not** claim that option (α) (a structure
  theorem) is impossible — only that the polecat could
  not derive it within budget and the work is paper-tier.
* Does **not** claim that option (β) (BK-walk spectral
  comparison) is impossible — only that it is the F5
  prerequisite, known paper-tier.
* Does **not** claim a refutation of Daniel's
  bespoke-combinatorics direction. The lemma works as a
  rigorous inequality; it just isn't a complete trichotomy
  driver on its own.
* Does **not** propose any change to `hC3` retention,
  `lean/AXIOMS.md`, or the headline. Outcome class:
  scoping + verification, no parallel cleanup.

---

*This file is Deliverable C for `mg-acc8`, filed 2026-05-05
by polecat `pacc8` on branch `alternating-cancellation-arc-1`.
It is doc-only (no Lean source changes). See
`lemma-statement.md` (Deliverable A) and `verification.md`
(Deliverable B) for the full deliverable package.*
