# Path α sub-A scoping — per-level FKG normalization without global LE distributive lattice

**Polecat:** mg-21a4 (cat-mg-21a4).
**Date:** 2026-05-06.
**Branch:** `polecat-p21a4` → `a8-s2-cont-execution-arc`.
**Predecessor:** mg-dc9d (`docs/path-alpha-execution-arc/hibi-1-stop-report.md`,
commit `a95020e`). Earlier ancestor: mg-b10a
(`docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`, commit `256f0da`).
**Verdict:** **RED.** A specific structural obstruction is identified and
exhibited by a concrete counterexample on the discrete 3-antichain.
**Recommendation.** PM closes Path α. Surface "exhausted" framing on
path-α-vs-γ to Daniel. mg-fb16 unhold becomes Daniel's call between
**Path γ (retain `case3Witness_hasBalancedPair_outOfScope` as a project
axiom; recommended)** and **sub-α-C (Hibi polytope chamber infrastructure;
mathlib-PR-class, multi-author quarter scale, not recommended)**.

This document is the latex-first deliverable per
`feedback_latex_first_for_math_simp` and per the polecat brief §3.
No Lean source touched.

---

## §1 State of art recap — what FKG-on-LE infrastructure already exists

### §1.1 Project-side infrastructure: the product-lattice route

The repo already contains a working FKG-on-LE pathway in
`lean/OneThird/Mathlib/LinearExtension/FKG.lean`. The headline is

```lean
-- lean/OneThird/Mathlib/LinearExtension/FKG.lean:452
lemma fkg_uniform_initialLowerSet
    (k : Fin (Fintype.card α + 1)) (F G : LowerSet α → β)
    (hF₀ : 0 ≤ F) (hG₀ : 0 ≤ G) (hF : Monotone F) (hG : Monotone G) :
    (∑ L : LinearExt α, F (L.initialLowerSet k.val)) *
      (∑ L : LinearExt α, G (L.initialLowerSet k.val)) ≤
    (Fintype.card (Fin (Fintype.card α + 1) → LowerSet α) : β) *
      (∑ ω : Fin (Fintype.card α + 1) → LowerSet α, F (ω k) * G (ω k))
```

The route is:
1. Embed `LinearExt α ↪ Fin (n+1) → LowerSet α` via the chain map
   `L ↦ L.initialLowerSetChain` (`FKG.lean:317`).
2. Apply `pi_fkg_uniform_correlation` (`FKG.lean:259`) on the **product
   distributive lattice** `Fin (n+1) → LowerSet α`. This step is sound —
   `LowerSet α` is distributive (Birkhoff), products of distributive
   lattices are distributive.
3. Use non-negativity to upper-bound the LinearExt-sum by the
   product-lattice-sum (`FKG.lean:371`).

The data-version mirror lives in
`lean/OneThird/Mathlib/RelationPoset/FKG.lean:325`
(`fkg_uniform_initialLowerSet'`).

### §1.2 The lossy normalization factor

The factor on the right is `Fintype.card (Fin (n+1) → LowerSet α) =
|LowerSet α|^{n+1}`, which for a width-3 poset of size `n` is up to
`(2^{|J(α)|})^{n+1}`. This factor is **exponentially larger** than the
target `numLinExt α`. mg-b10a §3.3 already noted:

> This factor is `(2^{n^2})^{n+1}` worst-case versus `numLinExt' Q ≤ n!`,
> an exponential loss. **Tightening this factor to `numLinExt' Q` is
> exactly the work the ticket asks for, and is the substantive
> Daykin–Saks content.**

### §1.3 Mathlib-side: `Mathlib.Combinatorics.SetFamily.FourFunctions`

* `fkg` — for log-supermodular `μ : L → ℝ` on a finite distributive
  lattice `L`, monotone non-negative `f, g`:
  `(∑ μ·f)(∑ μ·g) ≤ (∑ μ)(∑ μ·f·g)`.
* `four_functions_theorem`, `four_functions_theorem_univ`,
  `holley` — Ahlswede–Daykin variants and Holley's inequality.

All require a **finite distributive lattice carrier** with appropriate
log-supermodular weight.

### §1.4 The mg-dc9d STOP and what it RED'd

mg-dc9d (`docs/path-alpha-execution-arc/hibi-1-stop-report.md`,
commit `a95020e`) **disproved** the Path α scoping's central claim
that `(LinearExt α, ≤_τ)` is distributive for fixed `τ`. The
counterexample is the discrete 3-antichain `α = {a, b, c}`, where
`(LinearExt α, ≤_τ)` is the right weak Bruhat order on `S₃` — the
**six-element non-distributive hexagon**. mg-dc9d §2 includes the
explicit Hasse diagram and the failure of the distributive law
`(U ∨ V) ∧ X = (U ∧ X) ∨ (V ∧ X)`.

### §1.5 What Stanley's log-supermodularity gives

A standard fact (Stanley, *Two combinatorial applications of the
Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A, 1981):

> For a finite poset `P`, the function `e : J(P) → ℕ` counting linear
> extensions of a lower set is log-supermodular:
> `e(I ∪ J) · e(I ∩ J) ≥ e(I) · e(J)` for all `I, J ∈ J(P)`.

Applied also to `P` reversed: `e(P \ I)` is log-supermodular in `I`
(treated dually). So the product `μ(I) := e(I) · e(P \ I)` is also
log-supermodular on `J(P)`:

```
μ(I) μ(J) = e(I) e(J) · e(P\I) e(P\J)
       ≤ e(I∪J) e(I∩J) · e(P\(I∪J)) e(P\(I∩J))   -- Stanley + dual
       = μ(I ∪ J) μ(I ∩ J).
```

Crucially, `μ(I) = e(I) · e(P \ I) = |{L ∈ L(P) : L_{|I|} = I}|` is the
number of linear extensions whose initial ideal of size `|I|` equals
`I`. So `μ` ranges over different sizes simultaneously, and
`∑_I μ(I) = (n+1) · |L(P)|`.

This is the **strongest available log-supermodular structure** on
`J(P)`. The remaining question is whether it can be massaged into a
**level-`k`-specific** FKG inequality usable by the drops application.

---

## §2 The question restated, precisely

The polecat brief §2 asks: for the level-`k` pullback events that the
drops application needs, can the existing FKG-on-LE infrastructure be
tightened with a per-level normalization such that the multiplicative
factor becomes `numLinExt α`-sized (or polynomially close), using
**only** the distributivity of `LowerSet α`?

There are two distinct sub-questions, in increasing strength:

* **(Q1)** Does FKG positive correlation hold under uniform LE measure
  between two level-`k` pullback events? Concretely, for `k` fixed and
  `S, T : Finset α → Prop` up-closed:
  `Pr_L[S(L_k) ∧ T(L_k)] ≥ Pr_L[S(L_k)] · Pr_L[T(L_k)]`?
* **(Q2)** Does the drops headline `probEvent'_mono_of_subseteq_upClosed`
  follow from such a per-level FKG?

(Q2) is what consumers actually need. (Q1) is a strictly easier
question — and even (Q1) fails. (Q2) fails for an *additional*
independent reason discussed in §3.3.

---

## §3 Specific obstruction — the RED proof sketch

### §3.1 The counterexample to (Q1) on the discrete 3-antichain

**Poset.** `α = {a, b, c}` with the empty relation. So `J(α) = 2^α`
and `L(α) = S_3` (six linear extensions).

**Level.** `k = 1`. Level-1 lower sets are `{a}, {b}, {c}` (the only
size-1 subsets, all three are lower sets since `α` is discrete).

**Level-1 measure under uniform `L`.** For each level-1 ideal `I = {x}`:
`e(I) · e(α \ I) = 1 · 2 = 2`, so `μ_1(I) = 2 / 6 = 1/3`.
Hence `μ_1` is uniform on `{ {a}, {b}, {c} }`.

**The two up-closed events.** Take
`S := {I ⊆ α : a ∈ I}`, `T := {I ⊆ α : b ∈ I}`.
Both are up-closed in inclusion order on `Finset α`.

**Compute.**
* `Pr_L[S(L_1)]` — the probability that the level-1 ideal contains `a`.
  Only `{a}` does. Mass `1/3`.
* `Pr_L[T(L_1)] = 1/3` symmetrically.
* `Pr_L[S(L_1) ∧ T(L_1)]` — the level-1 ideal contains both `a` and `b`.
  But `|L_1| = 1`, so this is impossible. Mass `0`.

**Conclusion.** `Pr[S ∧ T] = 0 < 1/9 = Pr[S] · Pr[T]`. The two events
are **negatively** correlated; (Q1) fails.

This is not a degenerate failure mode — the same mechanism (level-`k`
slice of `J(P)` is *not* closed under join/meet, so events that "want"
to coexist at level `k` cannot) generalizes: any antichain at level
`k` produces mutually exclusive level-`k` containment events, hence
negative correlation.

### §3.2 Why Stanley's log-supermodular `μ` does *not* rescue (Q1)

`μ(I) = e(I) · e(α \ I)` on `J(α)` IS log-supermodular (§1.5). So
mathlib's `fkg` applies on `J(α)` with this weight. But the inequality
delivered is:

```
( ∑_I μ(I) · F(I) ) · ( ∑_I μ(I) · G(I) )
    ≤ ( ∑_I μ(I) ) · ( ∑_I μ(I) · F(I) · G(I) )
```

for monotone non-negative `F, G : J(α) → β`. Translating via
`∑_I μ(I) F(I) = ∑_L ∑_{k=0}^n F(L_k)` gives an inequality **summed
over all levels**, not at a specific level.

To project to a fixed level `k` while preserving log-supermodularity,
the natural moves all fail:

* **(Restrict)** `μ_k(I) := μ(I) · 𝟙[|I| = k]` — fails log-supermodularity
  because for `|I| = |J| = k` incomparable, `|I ∩ J| < k` and
  `|I ∪ J| > k`, so `μ_k(I ∩ J) = μ_k(I ∪ J) = 0` while
  `μ_k(I) μ_k(J) > 0`. (mg-b10a §3.5 already documented this exact
  failure mode for the cross-poset Holley variant.)
* **(Tilt)** `μ_z(I) := μ(I) · z^{|I|}` for a parameter `z > 0` — log-supermodular
  for every `z`, but concentrates approximately (not exactly) at
  level `k` for the right choice of `z`. The resulting inequality is
  level-averaged with a Gaussian-like envelope; not a level-`k`
  inequality.
* **(Condition on up- or down-set)** preserves FKG, but the level set
  `{|I| = k}` is neither up- nor down-closed.

Every route from log-supermodular `μ` on `J(α)` to a level-`k`-specific
FKG runs into the antichain obstruction of §3.1. The counterexample
shows the desired statement is *false*, not merely unprovable by a
particular method — so no clever encoding of Stanley's inequality on
the existing distributive lattice `J(α)` can produce it.

### §3.3 Why even a hypothetical (Q1) would not solve the drops application

This is an *additional* RED reason that holds independently of §3.1.

The drops headline `probEvent'_mono_of_subseteq_upClosed`
(`mg-8d39 §2.1`, brief §2 referent) reduces (mg-b10a §2, mg-8d39 §2.2
Strategy A) by single-edge `addRel` induction to FKG positive
correlation between two events on `LinearExt' Q`:

* `A := {L : S(L.iI k)}` — level-`k` pullback of an up-closed `S`.
* `R := {L : L.lt a b}` — "the new edge `(a, b)` is respected".

The required inequality is `Pr_L[A] · Pr_L[R] ≤ Pr_L[A ∩ R]`
(direction verified by mg-b10a §2 on a 3-element example).

`A` is a level-`k` pullback of an up-closed event on `Finset α`. `R`
**is not**: `R` is the global property "`a` precedes `b` in `L`". For
no fixed level `k` does `R` factor through `L ↦ L.iI k`. The level
decomposition

```
R = ⋂_{k=0}^n ( { b ∉ L.iI k } ∪ { a ∈ L.iI k } )
```

writes `R` as an intersection of single-level events, but each piece
is the *complement of "`a ∉ I, b ∈ I`"* on `L.iI k` — which is **not
monotone** in inclusion order on `Finset α`. So `R` has no
level-`k`-monotone-pullback expression.

Consequence: even if FKG between two level-`k` pullback events were
true (it isn't), it would not bound `Pr[A ∩ R]` from below, because
`R` is not such an event. The drops application requires FKG on a
lattice on `LinearExt' Q` itself — which is what mg-dc9d §6 option 1
("sub-α-A") sought to avoid.

So sub-α-A as described is doubly REDed: by §3.1 (the per-level FKG it
asks for is false) *and* by §3.3 (the per-level FKG it asks for, even
if true, would not solve drops).

### §3.4 Comparison with the literature

The classical proofs of Daykin–Saks 1981 / Brightwell 1999 §4 derive
the drops headline via the **τ-inversion lattice on `LinearExt α`**
(equivalently, the order polytope chamber decomposition; Stanley 1986).
This lattice fails to be distributive in general (mg-dc9d §2; right
weak Bruhat order on `S_3` is the canonical non-distributive hexagon).

For width-2 posets, the τ-inversion lattice becomes a sublattice of
the order ideal lattice `J(\bar P)` of the *incomparability graph*,
and IS distributive (Brightwell §3.5.1 in the width-2 special case).
For width-3 (the OneThird scope), this rescue does not apply.

**There is no known proof of Daykin–Saks drops that bypasses the
chamber lattice / τ-inversion lattice / order polytope structure**.
The literature treats the lattice as load-bearing.

### §3.5 The brief's "may admit a different mitigation" hypothesis

mg-dc9d §6.1 hedged:

> may admit a different mitigation (e.g., a per-level FKG with
> `numLinExt α`-sized normalization that works for level-`k` pullback
> events specifically, even without a global LE lattice).

This investigation closes that hedge. The hypothetical mitigation does
not exist:

| Candidate route                                           | Why it fails                                                                                  |
|-----------------------------------------------------------|-----------------------------------------------------------------------------------------------|
| FKG on `J(α)` with `μ(I) := e(I) · e(P\I)`                | Sums over levels; cannot project to level `k` (§3.2)                                          |
| Restrict `μ` to level `k`                                 | Fails log-supermodularity by size-mismatch (mg-b10a §3.5 / §3.2 here)                         |
| Tilted measure `μ_z(I) := μ(I) · z^{|I|}`                 | Level-averaged with Gaussian envelope; not exact level `k` (§3.2)                             |
| Condition `μ` on `{|I| = k}`                              | `{|I| = k}` is not up- or down-closed, so conditioning breaks FKG                             |
| Per-level FKG between two level-`k` pullback events       | False on discrete 3-antichain at `k = 1` (§3.1); negative correlation                          |
| Even if it held: bound `Pr[A ∩ R]`                       | `R` is not a level-`k` pullback event (§3.3); FKG inapplicable                                |

All routes are RED.

---

## §4 Lean signatures

Per `feedback_pre_execution_dependency_verification`: explicit Lean
signatures, consumer-side primitives enumerated and verified in-tree,
missing primitives surfaced and scoped. Because the verdict is RED,
the deliverable here is *negative*: no new primitives are proposed,
and the consumer-side primitive that mg-8d39 §2.1 specified
(`probEvent'_mono_of_subseteq_upClosed`) **cannot be proved via the
sub-α-A route**.

### §4.1 Existing in-tree consumer-side primitive

The closest available consumer is the strictly weaker

```lean
-- lean/OneThird/Mathlib/RelationPoset/FKG.lean:464
theorem probLT'_mono_of_relExt
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    (Finset.univ.filter
        (fun L' : LinearExt' Q' => S (L'.initialIdeal' k.val))).card ≤
      (Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card
```

This is a **counting-only** inequality (numerator only) that holds by
the embedding `LinearExt' Q' ↪ LinearExt' Q`. It does not normalize
by the respective LE counts and so does not give the genuine drops
inequality. Its docstring (`FKG.lean:506-516`) explicitly notes:

> The standard form requires FKG positive correlation between the
> `S`-event and the "`L` respects new `Q'`-comparabilities" event in
> the LinearExt' Q lattice, recorded as a follow-up in
> `docs/a8-s2-status.md`.

### §4.2 Target primitive (the drops headline) — RED'd by sub-α-A

```lean
-- target (mg-8d39 §2.1; not in tree; would close case3 + Brightwell axioms)
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val))
```

This is the missing primitive that the case3-port and Brightwell-port
both consume. **sub-α-A does not provide a proof route for it.**

### §4.3 Hypothetical sub-α-A Lean primitives — none survive

If sub-α-A had GREENed, the new primitives would have been:

```lean
-- HYPOTHETICAL — would have been the sub-α-A deliverable, but cannot exist:
theorem fkg_uniform_LE_initialLowerSet_per_level
    (k : Fin (Fintype.card α + 1)) (F G : LowerSet α → β)
    (hF₀ : 0 ≤ F) (hG₀ : 0 ≤ G) (hF : Monotone F) (hG : Monotone G) :
    (∑ L : LinearExt α, F (L.initialLowerSet k.val)) *
      (∑ L : LinearExt α, G (L.initialLowerSet k.val)) ≤
    (Fintype.card (LinearExt α) : β) *
      (∑ L : LinearExt α,
          F (L.initialLowerSet k.val) * G (L.initialLowerSet k.val))
```

The §3.1 counterexample disproves this in the form: take `α = {a,b,c}`
discrete, `k = 1`, `F = 1_{ a ∈ I }`, `G = 1_{ b ∈ I }`. Then LHS
`= 2 · 2 = 4`, while RHS `= 6 · 0 = 0`. **`4 ≤ 0` is false.** So this
signature has no inhabitant.

### §4.4 Lean signatures consumed downstream of the missing primitive

For completeness, downstream consumer chains (per scoping.md §4.1)
that are blocked by the missing drops primitive:

* **case3-port-2** — Step 1 of `case3Witness_hasBalancedPair_outOfScope`
  axiom-removal (mg-75ef §3 + mg-5bf9 §3). Consumes the drops headline
  at fixed `k` for an up-closed `S` derived from the case3 bipartite
  structure. Blocked.
* **case3-port-3+4+axiom-removal** — Step 2 (band-restricted FKG
  sub-coupling) and Step 3 (final reduction). Both downstream of
  case3-port-2. Blocked transitively.
* **Brightwell-port** (`brightwell_sharp_centred` axiom-removal) —
  uses the τ-inversion product lattice `L(α) × {1,…,m}` with AD
  applied twice. mg-dc9d §6 sub-α-A does not address this branch
  directly; the τ-inversion lattice failure on `L(α)` (width-3)
  blocks it for the same reason. Brightwell-port-A and -B remain
  blocked.

Path-α-as-scoped (mg-ff7f) is fully RED.

---

## §5 Verdict

### §5.1 Headline

**RED** with explicit obstruction (§3.1 counterexample) and explicit
follow-on-killer (§3.3 mismatch between `R` and any level-`k` pullback).

### §5.2 What this means for Path α

* **mg-fb16 unhold** is now Daniel's call between Path γ and sub-α-C.
* **Path γ** (retain `case3Witness_hasBalancedPair_outOfScope` as a
  project axiom) — recommended. Per cont-4 §6, the axiom is
  QA-audited (mg-7377), forum-readiness (mg-d7fd) signed off on the
  trust surface with this axiom in place, and audit-bar economics
  (cont-4 §6) favour retention over a quarter-scale mathlib-PR effort.
* **sub-α-B** (restrict to width-2 sub-posets) — does not fit the
  case3 application (case3 needs width-3). Not viable.
* **sub-α-C** (Hibi polytope chamber infrastructure) — viable but
  mathlib-PR-class, multi-author, quarter scale. cont-4 §6 estimate
  ~2000-4000 LoC for the FKG-on-LE primitive alone, plus ~1450-2700
  LoC for the application chain. **Not recommended** unless Daniel
  prioritizes axiom elimination over ship velocity (cont-4 §6
  recommendation already preferred Path γ here).

### §5.3 Trip-wires

Per the polecat brief §5:

* **Trip-wire #1 (token blow-up).** Not fired. Approximate token
  spend on this report is well under the 400k cap. No Lean coding
  attempted.
* **Trip-wire #2 (structural obstruction).** **Fires.** §3.1's
  counterexample is a fresh structural fact that REDs sub-α-A.
  Per the brief: STOP, report, do not try to rescue. This document
  is the report. (Echoes mg-b10a §3.5's earlier slice-by-level
  Holley failure on the same size-mismatch principle, generalised
  here to the level-`k` measure on `J(α)`.)
* **Trip-wire #3 (drift to non-sub-α-A).** Not fired. This polecat
  did not attempt to pivot to sub-α-C or another path; the verdict
  surfaces the call to PM as required.

All trip-wires honored per `feedback_complexity_blowup_means_wrong_path`
and `feedback_polecat_stop_runaway`.

### §5.4 Follow-on tickets PM might file

1. **PM mails Daniel** with the Path α exhausted framing and the
   path-γ-vs-α-C call. (Mayor-level coordination action; not a
   polecat ticket.)
2. **(If Path γ chosen)** No new tickets needed. mg-fb16 stays
   unheld pending Daniel's confirmation. Forum-post draft already
   articulates the two-named-axiom trust surface (cont-4 §10 #3).
3. **(If sub-α-C chosen)** File a long-arc ticket
   `mathlib-gap-FKG-on-LE` (or equivalent), explicitly long-arc,
   multi-polecat, mathlib-PR-class. Not recommended.
4. **(Either way)** Update `lean/AXIOMS.md` disclosures if Daniel's
   choice changes the framing (Path γ — "definitively retained"; Path
   sub-α-C — "scheduled for replacement via shared mathlib-gap port").
   Trivial, ~10–20 LoC of doc edits.

---

## §6 Cross-references

* **mg-dc9d** (predecessor STOP):
  `docs/path-alpha-execution-arc/hibi-1-stop-report.md`, commit
  `a95020e`. §2 (S₃ hexagon counterexample); §6 option 1 (sub-α-A
  hedge that this report closes).
* **mg-b10a** (earlier STOP on same arc):
  `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`, commit
  `256f0da`. §3.2 (lattice candidate enumeration); §3.3 (product
  factor `(2^{n^2})^{n+1}`); §3.5 (slice-by-level Holley size-mismatch
  — the precursor to §3.2 here); §6 (Path γ recommendation).
* **mg-ff7f** (earlier scoping, retracted):
  `docs/path-alpha-scoping/scoping.md`, commit `6b62a77`. §2.5
  (false distributivity claim, retracted by mg-dc9d). §4 (ticket
  decomposition; entire cascade now blocked).
* **mg-8d39** (earlier scoping, partially retracted):
  `docs/a8-s2-cont-scoping-arc/scoping.md`. §2.1 (target headline);
  §2.2 (Strategy A reduction).
* **mg-75ef** (case3-port verdict β math artifact):
  `docs/case3-port-arc/rem-enumeration-proof.md`. Requires drops
  primitive; blocked.
* **`lean/OneThird/Mathlib/LinearExtension/FKG.lean`** — existing
  product-lattice FKG-on-LE infrastructure. `:452` is the headline
  with the lossy factor; remains valid as a sub-optimal but
  axiom-free pathway. Not consumed by case3.
* **`lean/OneThird/Mathlib/RelationPoset/FKG.lean`** — data-version
  mirror. `:464` is the strictly weaker counting-only consumer
  primitive. `:506-516` docstring records the gap that drops would
  close.
* **`lean/AXIOMS.md`** — `case3Witness_hasBalancedPair_outOfScope`
  (`:226–454`) and `brightwell_sharp_centred` (`:13–225`). Both
  remain on the trust surface; both are RED-by-sub-α-A from being
  removable through this route.
* **`feedback_polecat_stop_runaway.md`** — applied (STOP, report, no
  rescue, no auto-extension).
* **`feedback_complexity_blowup_means_wrong_path.md`** — applied
  (counterexample on the *minimal* width-3 instance is a structural
  signal, not an artefact of formalisation).
* **`feedback_latex_first_for_math_simp.md`** — applied (this
  document is the deliverable; no Lean source touched).
* **`feedback_pre_execution_dependency_verification.md`** — applied
  (§4 enumerates consumer primitives; missing primitive surfaced and
  scoped via the negative result).
* **`feedback_polecat_cumulative_state_doc.md`** — applied via
  `docs/path-alpha-execution-arc/state.md` (companion deliverable).

---

*End of sub-α-A scoping. Lean source unchanged. Verdict: RED.*

— polecat mg-21a4 (cat-mg-21a4), 2026-05-06.
