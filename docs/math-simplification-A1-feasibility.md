# Math-simplification arc — Chunk A1 feasibility study

**Filed under `mg-3d9d` by polecat `r3d9d` on 2026-05-02.**
**Branch:** `math-simp-arc` (this commit).
**Parent:** `docs/math-simplification-scoping.md@638ad1e` (scoping
chunk filed under `mg-3e53` by polecat `pc-3e53` on 2026-05-02).

This document is the deliverable for chunk A1 of the math-
simplification arc. It investigates whether the perturbation bound
required by Candidate A's "near-ordinal" case,

```
  | Pr_P[x < y] − Pr_A[x < y] |  ≤  f(ε(P))     for x, y ∈ A,    (★)
```

with `f(ε) → 0` as `ε → 0`, is derivable from the in-tree
`brightwell_sharp_centred` axiom alone, *without* introducing a new
project axiom.

The deliverable is a **VERDICT**: GREEN (A2 greenlit), AMBER (A2
greenlit with caveat), or RED-fallback (escalate, fall back to
Candidate B). The investigation is non-executing — no Lean code
is added in this chunk.

## TL;DR — Verdict

**RED-fallback.** The in-tree axiom — even composed with the full
in-tree FKG infrastructure and the iterated single-element bound
(`exc_perturb`, `step8.tex:1025-1062`) — produces only a
**size-based** perturbation bound `2|B|/(|A|+1)`. This is **NOT** a
function of `ε(P)` and does **NOT** vanish as `ε → 0` for balanced
cuts (`|A| ≈ |B|`).

To bridge the gap, **either**

  (a) a new project axiom (a multi-element /
      ordinal-cut variant of Brightwell) is required — flagged
      under `feedback_audit_bar_for_axioms`, RED-fallback per the
      scoping doc's protocol; **or**

  (b) a substantive new mathematical argument (essentially Risk 1
      of the scoping doc — re-deriving the content of Steps 1–7
      under a different framing) is required, which is
      out-of-scope for chunk A1's 500k budget and most likely
      illusory (the reductio framing forces the same content
      back in).

Recommendation per the scoping doc's protocol: **fall back to
Candidate B** (`docs/math-simplification-scoping.md` §3,
"Fallback path"). Candidate A is not feasible as scoped.

## 1. Target and constraints

Candidate A's near-ordinal case (`docs/math-simplification-
scoping.md` §1, Candidate A) requires (★) for `x, y` in the
larger of the two pieces of an ε-minimizing cut, with `f(0) = 0`
and `f(ε₀) < γ` for the project's `γ < 1/3 − δ_KL ≈ 0.057`. The
scoping doc's success bracket: `f(ε) = O(ε^c)` for some `c > 0`.

Per the scoping doc's brief and the polecat charter, the
investigation respects the following constraints:

* **No new axiom.** A new project axiom is a signature regression
  (`feedback_audit_bar_for_axioms`) and triggers RED-fallback.
* **No new paper-level math.** A "fundamentally new" mathematical
  argument is out of scope and triggers escalation.
* **Doc-only deliverable.** No source changes; no `sorry`,
  `axiom`, or hypothesis weakening is introduced even
  hypothetically.

## 2. Inventory: what the in-tree axiom gives

### 2.1 The axiom statement

`OneThird.LinearExt.brightwell_sharp_centred`
(`lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`)
is the **single-element perturbation** bound. For a finite poset
`α`, pred/succ finsets `Pred, Succ ⊆ α` (witnessing a single
element `z` of an ambient `Q := α ⊔ {z}`), `m = |Q| ≥ 2`, and
`x, y ∈ α`:

```
  m · | N' · Σ_{L' ∈ A} f(L') − |A| · N |  ≤  2 · N · N',
```

equivalently (axiom-derived `brightwell_sharp_centred_rat`,
`BrightwellAxiom.lean:195`),

```
  | Σ_{L' ∈ A} (f(L') − f̄) |  ≤  2 N / m,
```

with `N := Σ_{L' : L(α)} f(L') = |L(Q)|`, `N' := |L(α)|`,
`f̄ := N / N'`, and `A := { L' ∈ L(α) : x <_{L'} y }`.

### 2.2 Direct corollary: per-element perturbation

`OneThird.LinearExt.one_elem_perturb` (`step8.tex:911-1023`,
`lean/OneThird/Step8/OneElemPerturb.lean:709`) packages this as

```
  | Pr_Q[x < y] − Pr_{Q∖{z}}[x < y] |  ≤  2 / |Q|.
```

This is the *only* downstream form the axiom is consumed in.

### 2.3 Iterated corollary: exceptional-set perturbation (F6b)

`OneThird.LinearExt.exc_perturb` (`step8.tex:1025-1062`,
`lean/OneThird/Step8/ExcPerturb.lean:351`) iterates `one_elem_perturb`
along an arbitrary deletion sequence. For `α` with `|α| = n`,
`S ⊆ α` with `|S| = k` and `n − k ≥ 2`, `x, y ∉ S`:

```
  | Pr_α[x < y] − Pr_{α∖S}[x < y] |  ≤  2k / (n − k + 1).      (☆)
```

This is the *strongest* multi-element perturbation bound derivable
from the axiom in tree, and it is the bound that any candidate-A
near-ordinal argument would have to consume.

### 2.4 What the axiom does NOT give

The axiom is uniform in `(Pred, Succ)`: the bound `2/m` per
deletion is independent of how "comparable" `z` is to other
elements. There is no in-tree refinement that yields a tighter
single-element bound when `z` is "almost above" or "almost below"
all of the surviving elements. In particular, the per-element
bound cannot be improved to `o(1/m)` in any structural regime
without re-doing the FKG / Kahn–Saks / Brightwell argument from
scratch.

The in-tree FKG primitives (`fkg_uniform_correlation`,
`fkg_uniform_initialLowerSet`,
`OneThird.Mathlib.LinearExtension.FKG.lean:124, 452`) bound
positive correlation of monotone functions on `LinearExt α`, but
the Brightwell sharp-centred bound combines FKG with the
*per-term Kahn–Saks covariance bound* `|Cov_μ(1_A, S)|,
|Cov_μ(1_A, P)| ≤ f̄/m`, which is the "non-trivial Lean input
estimated at 500–800 LoC of mathlib-tier covariance / set-system
infrastructure" left as the axiom's stub
(`BrightwellAxiom.lean:55-62`, `lean/AXIOMS.md:34-49`).

## 3. The gap: target vs. what is derivable

### 3.1 What (★) requires

For Candidate A's near-ordinal case to close the trichotomy at
`ε ≤ ε₀(γ)`, we need (★) to hold *with* `f(ε₀) < γ ≈ 0.057` for
*every* width-3 non-chain `P` admitting a cut `(A, B)` with
`ε(P) ≤ ε₀`.

The "ordinal-sum lift" downstream consumer
(`OrdinalDecomp.hasBalancedPair_lift`,
`lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152`) covers
the `ε = 0` case exactly (`probLT_restrict_eq` is exact when the
cut is a genuine ordinal sum, `Subtype.lean:1065`); the
near-ordinal case must extend this to `ε > 0` with a
quantitative perturbation budget.

### 3.2 What (☆) provides

Specializing (☆) to `S = B` and `α = P`, with `n = |P|`, `k = |B|`:

```
  | Pr_P[x < y] − Pr_A[x < y] |  ≤  2|B| / (|A| + 1)            (◇)
```

for `x, y ∈ A`. Symmetrically, deleting `A` instead gives a bound
`2|A|/(|B|+1)` for `x, y ∈ B`.

### 3.3 The gap is real for balanced cuts

The bound (◇) **does not depend on `ε`**. It depends only on the
*sizes* `|A|, |B|`. For the most natural / structural ε-minimizing
cuts — those with `|A| ≈ |B| ≈ |P|/2` — the bound becomes

```
  2|B|/(|A|+1)  ≈  2 · (n/2) / (n/2 + 1)  →  2  as  n → ∞,
```

i.e., `(◇)` is `Θ(1)` for balanced cuts, regardless of how small
`ε(P)` is. It does **not** clear `γ ≈ 0.057`.

**Concrete witness.** Take `P = A ⊕ B` with `|A| = |B| = n/2` and
add a single bad cross-edge: change one pair `(a₀, b₀) ∈ A × B`
from `a₀ < b₀` to `a₀ ⫨ b₀` (incomparable). Then

```
  ε_per-pair(P) = 1 / (|A| · |B|) = 4/n²,
```

which is `O(1/n²) → 0`. Yet (◇) still gives `2|B|/(|A|+1) ≈ 2`,
because the bound is structurally insensitive to the cut's defect
ratio. There is no value of `ε` that triggers a smaller bound from
(☆).

### 3.4 Normalization sub-question (Q2 of scoping doc)

The scoping doc raises three normalization candidates for `ε`.
None of them recover an in-tree-derivable f(ε):

| Normalization | Definition | In-tree bound |
| --- | --- | --- |
| **Per-pair** `ε_pp` | `\|{(a,b) : a⊀b}\| / (\|A\|\|B\|)` | `2\|B\|/(\|A\|+1)` (size-based, not `ε`-aware) |
| **Per-element** `ε_pe` | `\|{(a,b) : a⊀b}\| / \|P\|` | same — bound is on cut size, not bad-edge count |
| **Per-volume** `ε_pv` | `1 − θ`, `θ = \|L_factored(P)\| / \|L(P)\|` | `\|p_P − p_A\| ≤ ε_pv` is *automatic* via the union/factorisation argument; but `ε_pv` has no in-tree structural lower bound, and FKG applied to `θ` gives `θ ≥ ∏ p_{ab}` which is exponentially small in the # of bad pairs (FKG goes the wrong way for our needs in this regime). |

The per-volume normalization is the cleanest target *if* we had a
structural bound on `θ` from `ε_pp` or `ε_pe`; in tree, no such
bound is derivable. (FKG on `LinearExt α` bounds positive
correlation of *monotone* events; the event "all of `A` precedes
all of `B`" is monotone in the right lattice, but FKG yields the
*lower* bound `θ ≥ ∏_{(a,b)} p_{ab}(P)`, which equals
`(1/2)^{Θ(ε|A||B|)}` in expectation — useless for our regime.)

### 3.5 Iterating (☆) tighter? No.

The induction in `exc_perturb_aux` (`ExcPerturb.lean:212-338`)
loses `2/(n − k')` per step. Even the *harmonic-sum*
optimization — `Σ_{m=|A|+1}^{n} 2/m = 2(H_n − H_{|A|}) ≈ 2 ln(n/|A|)`
— is still `Θ(1)` for balanced cuts and `Θ(ln n)` for asymmetric
cuts where `|A|` is small. Neither form is `f(ε) → 0`.

The in-tree iteration is structurally maximal: each per-step
bound `2/(n−k')` is the axiom's per-element rate, and the axiom
gives no sharper rate. (Iterating in a *random order* and
averaging does not help: the worst-case step rate is the
operative quantity.)

### 3.6 Why a non-axiom route is dim

The natural non-axiom route is to derive a sharper many-element
bound directly from the in-tree FKG primitives (`FKG.lean`),
*without* invoking the per-element axiom as a black box. The
relevant Brightwell-style bound for many-element deletion is
exactly the content of step 8 G3's window-perturbation argument
(`step8.tex:2280-2305`), which produces an `o_K(1)` bound for
windows of size `K` independent of `n`.

But that argument is **exactly the content of Steps 5–7** (the
fiber-model rigidity argument): the `o_K(1)` window bound is a
structural consequence of the layered decomposition's coherence,
not a direct FKG consequence. The Lean code reflects this
honestly: `LayeredReduction.lean:426-434` packages the
`o_K(1)` bound as a `ReductionWitness.conclusion` field passed
in by the caller, *not* derived in-file from FKG / Brightwell.

This is **Risk 1 of the scoping doc firing as predicted**: any
multi-element `ε`-aware bound strong enough to clear γ would be
re-deriving Steps 1–7 under a different name. The simplification
is illusory along this route.

## 4. Lean pseudo-code and LoC estimate

For completeness, the lemma the trichotomy *would* need (were it
derivable) is:

```lean
-- HYPOTHETICAL — NOT derivable from in-tree axioms without either
-- a new axiom or new paper-level math (see §3).
theorem perturbation_bound_eps_aware
    {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (A B : Finset α) (hCover : A ∪ B = Finset.univ)
    (hDisj : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (ε : ℚ)
    (hEps : ((A.product B).filter (fun p => ¬ (p.1 ≤ p.2))).card
              ≤ ε * (A.card * B.card : ℚ)) :
    ∀ x y, (hx : x ∈ A) → (hy : y ∈ A) →
      |probLT x y - probLT (⟨x, hx⟩ : ↥A) ⟨y, hy⟩| ≤ f ε
```

with `f : ℚ → ℚ` an explicit function having `f 0 = 0` and
`f ε ≤ γ` for `ε ≤ ε₀(γ)`.

**LoC estimates:**

* **Path (i): in-tree-only, via `exc_perturb`.** ~50–100 LoC
  to wrap `exc_perturb` for the ordinal-cut shape. The bound
  delivered is `2|B|/(|A|+1)`, which is *not* an `f(ε)` —
  this LoC is essentially wasted because the resulting lemma
  is not strong enough for the trichotomy. **Not viable.**

* **Path (ii): new axiom (multi-element Brightwell variant).**
  Axiom statement ~30 LoC; downstream `f(ε)` derivation
  ~150–250 LoC. **RED-fallback per the scoping doc protocol.**

* **Path (iii): re-derive from FKG without a new axiom.**
  ~600–1500 LoC of FKG / Kahn–Saks / Brightwell covariance
  infrastructure — comparable to or exceeding the existing
  `OneElemPerturb.lean` (837 LoC) plus the deferred 500–800 LoC
  of mathlib-tier per-term covariance work flagged in
  `lean/AXIOMS.md`. Plus, mathematically speculative: see §3.6.
  **Out of bracket** (scoping doc's bracket: 100–400 LoC).

None of the three paths land in the scoping doc's 100–400 LoC
bracket *and* yield (★).

## 5. Risk and signature audit

### 5.1 Axiom audit

`feedback_audit_bar_for_axioms` is the project's standing
guardrail against axiom regressions. Per the scoping doc
(§2, "Signature regression check"):

> If Chunk A1 (feasibility) requires introducing a new axiom for
> the perturbation scaling (e.g., a chain-form Brightwell bound
> that isn't derivable from the existing axiom), that *would* be
> a signature regression and must be flagged.

A multi-element / ordinal-cut Brightwell variant (path (ii) above)
is exactly such a new axiom. Its mathematical content — a
Brightwell-style bound that scales with the *defect* `ε` rather
than the *cut size* `|B|` — is **not** a faithful transcription
of the existing Brightwell 1999 §4 Theorem 4.1 + Kahn–Saks 1984
Lemma 2.2 combination. It would be a *new* claim, not a packaging
choice. Per `feedback_audit_bar_for_axioms` and the polecat
charter ("If new math turns out to need its own axiom: report
back"), this triggers escalation, not introduction.

### 5.2 Signature regression

Candidate A's headline goal is *positive* signature change
(drops `hC3`, no new hypotheses). A path (ii) execution would
*add* a new axiom alongside `brightwell_sharp_centred`, turning
the headline's signature regression sign from `(+1, 0)` to
`(+1, +1)` — net neutral or worse. The scoping doc explicitly
flags this as a regression that must be reported, not silently
absorbed.

## 6. Verdict and recommendation

**VERDICT: RED-fallback.**

The protocol RED triggers from the scoping doc's "block-and-report
triggers" (§3, Chunk A1) fire as follows:

* ✅ "No `f(ε) → 0` bound derivable from existing axioms" —
  confirmed in §3.3.
* ✅ "`f(ε)` not strong enough to clear γ for γ < 1/3 − δ_KL ≈
  0.057" — confirmed in §3.3 (bound is `Θ(1)` for balanced cuts,
  any γ-clearing requires `|B|/|A| ≤ γ/(2+γ) ≈ 0.028`, not
  guaranteed from `ε(P)` smallness).
* ✅ "New axiom required" (for an alternative path that *would*
  work) — confirmed in §4 path (ii).

Per the scoping doc's protocol: **fall back to Candidate B**,
the size-minimality cleanup of `lem:layered-reduction`. That
candidate is independently scoped at LOW risk, ~−400 LoC, no
signature regression, and is fully articulated in the in-tree
`simplifications.md` §1.

### 6.1 Specific recommendation to PM

1. **Halt commitment of A2, A3, A4.** Candidate A's near-ordinal
   case is the load-bearing chunk, and chunk A1 has now produced
   evidence that it is not feasible without a new axiom or
   new paper-level math.

2. **Commission Chunk B1** (per scoping doc's Fallback path,
   `docs/math-simplification-scoping.md` §3, "Fallback path —
   Candidate B"). Budget: 400k tokens. Deliverable: rewritten
   `LayeredReduction.lean` per `simplifications.md` §1
   ("Layered reduction via direct minimality contradiction").
   This ships a real simplification (~−400 LoC) without the
   structural risk that A carried.

3. **Park Candidate A** as a research-level open question (along
   with Candidate D from the scoping doc) for a future external
   collaboration or longer-horizon arc. The blocker is
   mathematical (a stronger Brightwell-type bound for ordinal
   cuts) and not amenable to polecat-budget Lean work.

4. **Optional: file an mg for the Brightwell-multi-element
   research question.** A future iteration could attempt to
   derive a multi-element Brightwell bound from the in-tree FKG
   infrastructure as a self-contained Lean exercise; the
   estimated 600–1500 LoC and uncertain mathematical content
   make this a scoped research arc rather than a chunk of
   Candidate A. Not recommended for the current product cycle.

### 6.2 What chunk A1 *did* learn

* The scoping doc's "Risk 2 (medium)" — that the perturbation
  bound iterates to `O(1)` — is **confirmed sharp**. The
  optimistic reading ("plausibly derivable but not trivially so")
  is overturned: it is *not* derivable from in-tree axioms in
  the relevant balanced-cut regime.
* The scoping doc's "Risk 1 (likely)" — that
  `far_from_ordinal_balanced` is just Steps 1–7 in disguise —
  has been *partially* confirmed for the *near-ordinal* case
  too: any non-axiom route to `f(ε)` runs through the same
  rigidity content as Steps 5–7 (per §3.6).
* The headline N-poset benefit of Candidate A (auto-discharge of
  `hC3` via the decomposable `ε = 0` case) is preserved as a
  motivating observation — but it requires Candidate A's
  trichotomy to actually close, which (per this chunk's verdict)
  it does not without new axiomatic content.
* Candidate B's scope and viability are unaffected by this
  result; the in-tree `simplifications.md` §1 articulation
  remains a clean, low-risk path forward.

## 7. References

### Code anchors

* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
  — the in-tree axiom statement.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:195`
  — `brightwell_sharp_centred_rat`, the rational-form rearrangement.
* `lean/OneThird/Step8/OneElemPerturb.lean:709` —
  `one_elem_perturb`, single-element perturbation bound.
* `lean/OneThird/Step8/ExcPerturb.lean:212-338` —
  `exc_perturb_aux`, the iterated bound's induction.
* `lean/OneThird/Step8/ExcPerturb.lean:351` — `exc_perturb`,
  exposed multi-element bound `2k/(n−k+1)`.
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean:124, 209, 218,
  240, 259, 452` — uniform / lattice / product / pi / initial-
  lower-set FKG primitives.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1065` —
  `OrdinalDecomp.probLT_restrict_eq`, exact `ε = 0` marginal
  invariance.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152, 1227,
  1237` — `OrdinalDecomp.hasBalancedPair_lift{,_lower,_upper}`,
  the exact ordinal-sum lifts.
* `lean/OneThird/Step8/LayeredReduction.lean:426-460` —
  `ReductionWitness` and `lem_layered_reduction` showing that
  Step 8 G3's `o_K(1)` window bound is a *Prop input* in tree,
  not derived from Brightwell.
* `lean/AXIOMS.md` — axiom inventory and audit bar.

### Doc anchors

* `docs/math-simplification-scoping.md@638ad1e` (parent scoping
  doc, Candidate A description, Risk 1 / Risk 2 statements,
  block-and-report triggers).
* `simplifications.md` §1 (top-level repo file) — Candidate B
  source for the fallback recommendation.
* `lean/AXIOMS.md` §"`OneThird.LinearExt.brightwell_sharp_centred`"
  — the audit + retain decision.
* `~/.pogo/agents/pm/pm-onethird/memory/feedback_audit_bar_for_axioms.md`
  — the standing guardrail invoked here.

### Paper anchors

* `step8.tex:911-1023` — `lem:one-elem-perturb` (F6a paper proof).
* `step8.tex:1025-1062` — `lem:exc-perturb` (F6b paper proof).
* `step8.tex:1042` — `eq:sharp-centred` (the axiom's
  paper-source equation).
* `step8.tex:2164-2186` — `lem:cut` (Step 8 G3 cut existence).
* `step8.tex:2280-2305` — the `o_K(1)` window-perturbation
  argument referenced in §3.6.
* `step8.tex:2386-2519` — `def:ordinal-decomp`,
  `lem:ordinal-factorisation`, `cor:ordinal-marginal` (the
  in-tree Lean infrastructure for the `ε = 0` lift).

## Provenance

Filed under `mg-3d9d` ("Math-simp arc Chunk A1 — Feasibility:
perturbation bound …") by polecat `r3d9d` on 2026-05-02. Branch
`math-simp-arc` (this commit). Parent ticket: `mg-3e53` (scoping
pass). Verdict for PM action: **RED-fallback → fall back to
Candidate B (file Chunk B1)**.
