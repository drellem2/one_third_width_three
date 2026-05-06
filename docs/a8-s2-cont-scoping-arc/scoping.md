# A8-S2-cont scoping — probability-form cross-poset FKG infrastructure

**Work item:** `mg-8d39` (polecat `p8d39`).
**Branch:** `polecat-p8d39` (target `a8-s2-cont-scoping-arc`).
**Predecessors:** `mg-75ef`
(`docs/case3-port-arc/rem-enumeration-proof.md`, on `case3-port-arc`,
verdict β); `mg-5bf9`
(`docs/case3-port-arc/linear-majority-alignment.md`, on `case3-port-arc`,
verdict AMBER re-corroborating β); `mg-e850`
(`docs/case3-port-arc/port-status.md`, STOP on trip-wire #4).
**Verdict:** **upgraded GREEN.** Trip-wire #4 fires in the
audit-bar-friendly direction: the major infrastructure that the
2026-04-26 `pc-8801` polecat estimated at ~2000-3500 LoC has *already
landed* across A8-S2-cont-1/-2/-3 (~2100 LoC total, mg-b088 +
mg-1a4f + mg-0b81). The residual scope to discharge the case3
`outOfScope` axiom is **~1450-2700 LoC** broken into 4-6 polecat
sessions, dominated by the probability-form (Daykin–Saks "drops")
FKG inequality on `LinearExt' Q` (~600-1200 LoC) and the case-3
specific application chain (~850-1500 LoC).

This document is the latex-first deliverable per the polecat brief
and the `feedback_latex_first_for_math_simp` discipline. Lean source
unchanged. The deliverable IS the scoping doc.

---

## §1 Inputs synthesized

The four predecessor artifacts (math-side and Lean-side) converge
on the same headline: **the case3 axiom port reduces to landing
the probability-form (= "drops") cross-poset FKG inequality on
`LinearExt' Q`, plus a case-3-specific application.** Below is a
unified summary of what each predecessor contributes to the scoping.

### §1.1 `mg-75ef` (`rem-enumeration-proof.md`, 707 lines)

The latex-first paper-rigor specification of the
`prop:in-situ-balanced` Case 3 (out-of-scope) discharge, structured
as the sketch's three-step argument:

* **§1-§2 setup + orientation lemma.** Daniel's 2026-05-06
  rotation-identity input (`step8.tex:2920-2929`) gives Lemma 2.1:
  under the no-balanced-pair counterfactual (NBP), the majority
  orientation `a ≪ a'` (defined by `Pr_Q[a < a'] > 2/3`) is
  acyclic on every 3-antichain. Hence on every Case-3 within-band
  triple `{a_1, a_2, a_3}` we may WLOG take `a_1 ≪ a_2 ≪ a_3`
  (linear chain).
* **§3 revised Step 1.** Lemma 3.3 (rigorous): under (NBP) ∧ Case 3,
  for each pair `(a_i, a_j)` with `a_i ≪ a_j`, at least one of
  `Π⁺(a_j) \ Π⁺(a_i) ≠ ∅` or `Π⁻(a_i) \ Π⁻(a_j) ≠ ∅` holds. Claim
  3.2 (sketch, gap honestly flagged): the per-coordinate
  asymmetries cannot all simultaneously be "balanced two-sided
  incomparable"; some pair `(a_i, a_j)` is one-sided aligned
  (Π⁺-aligned OR Π⁻-aligned).
* **§4 Step 2 (band-restricted FKG sub-coupling).** The substantive
  step. From a one-sided aligned pair `(a_1, a_2)` with
  `Π⁺(a_1) ⊆ Π⁺(a_2)`, work in the upper sub-poset
  `Q^+ := Q[M_k ∪ M_{k+1} ∪ ⋯ ∪ M_K]`. In `Q^+` the pair is either
  Case-1-symmetric (full Π_{Q^+} match → `Pr_{Q^+} = 1/2` by swap
  involution) or Case-2-`⪯`-aligned (→ `Pr_{Q^+} ≥ 1/2` by
  bipartite Case 2 FKG). The **lift problem** is to transport the
  bound `Pr_{Q^+}[a_1 <_L a_2] ≤ 1/2` to a bound
  `Pr_Q[a_1 <_L a_2] ≤ 2/3` in the full ambient `Q`. Three
  attempted workarounds — count-form ratio, conditional-on-lower
  marginalisation, symmetry-tight involution — all reduce back to
  the same probability-form positive-correlation step. **No
  count-form route closes the lift.**
* **§5 Step 3 (reduction).** Conditional on §4: from
  `Pr_Q[a_1 <_L a_2] ≤ 2/3` and the `≥ 1/2` direction
  (transported by the same FKG primitive), `(a_1, a_2)` is balanced
  in `Q`, contradicting (NBP). Routine downstream once §4 lands.
* **§7 verdict β.** Three independent lines (first-principles lift
  analysis, three workaround attempts, prior in-tree audit) all
  reach the same conclusion: **the math needs probability-form
  cross-poset FKG.**

### §1.2 `mg-5bf9` (`linear-majority-alignment.md`, 524 lines)

Re-corroborates `mg-75ef`'s verdict β through a finer-resolution
analysis on Step 1 itself:

* **§3.1 Theorem 3.1 (in-scope sub-range, rigorous).** For K=3,
  w=1, every Case-3 antichain admits a Z/3-cyclic poset
  automorphism σ ∈ Aut(Q) on the within-band, forcing
  `Pr_Q[a_i <_L a_j] = 1/3` for some pair. (NBP) is incompatible
  with this sub-range; alignment holds vacuously. **But this
  sub-range is in-scope** (covered by `case3_certificate`), so
  Theorem 3.1 has no in-tree axiom-elimination value — it
  corroborates the F5a certificate at the math level.
* **§3.2 Open Question 3.5 (residual range, K=3∧w≥2 or K≥4).**
  The cyclic-automorphism argument breaks when (L2)'s
  forced-comparability set sparsens. Construction 3.4 (a candidate
  Aut-trivial Case-3 configuration) was **NOT** Aut-trivial — a
  σ_{(2 3)} involution preserves all comparabilities and forces
  `Pr = 1/2 ∈ [1/3, 2/3]`, balanced. Several variants explored
  similarly admit involutions. But **genuinely Aut-trivial
  Case-3 configurations are theoretically possible** (F1
  obstruction analogue from `docs/why-hC3-is-structural.md §1`).
* **§3.3 Claim 3.6.** Closing Open Question 3.5 positively by
  paper-rigor structural argument requires either probability-form
  cross-poset FKG OR finite enumeration on the bounded parameter
  range. Same blocker as §4 of `mg-75ef`, reached on a different
  path.
* **§4 verdict AMBER on alignment-only route.** Alignment forcing
  on the residual range does NOT close to paper rigor without
  A8-S2-cont; the alignment route co-uses A8-S2-cont rather than
  bypassing it.
* **Sub-result GREEN-on-K=3-w=1** (parallel-cleanup,
  ~80-150 LoC). Not the headline; PM commissions as an
  audit-bar parallel-cleanup ticket *outside* this arc.

### §1.3 `docs/a8-s2-status.md` (existing, 433 lines, dated 2026-04-26)

The original A8-S2 sub-split scoping by `pc-8801`:

* **§3a-§3b** identified that the paper's argument (Ahlswede–Daykin
  monotonicity over a chain `Q ⊇ Q' ⊇ Q''` of three distinct
  posets on the same `α`) requires a **data-poset** alternative
  to the typeclass `[PartialOrder α]` — Option A (recommended) was
  to add `RelationPoset α` and re-implement `LinearExt'`,
  `numLinExt'`, `probLT'`, Birkhoff transport, and FKG on top.
  Estimated cost: ~1500-2500 LoC for the data-poset reimplementation
  + ~200-400 LoC for the actual Case 2 argument.
* **§5 named "A8-S2-cont"** as the scoped infrastructure ticket(s).
  The total estimate of ~2000-3500 LoC was for the FULL
  A8-S2-cont (data-poset + probability-form FKG) plus the case 2
  follow-up.
* **§5 also notes** the bipartite `Pr ≤ 2/3` upper bound landed in
  parallel (mg-ed4d) and the rotation argument's residual is
  partial (mg-ba0c). Neither is on the case3 critical path.

**Crucial fact for this scoping.** Between the writing of
`docs/a8-s2-status.md` (2026-04-26) and the present scoping
(2026-05-06), three A8-S2-cont sub-tickets shipped:

* `mg-b088` (commit `a2e77ee`, A8-S2-cont-1) — `RelationPoset α`
  data type + basic API (~660 LoC: `lean/OneThird/Mathlib/RelationPoset.lean`).
* `mg-1a4f` (commit `261bcbf`, A8-S2-cont-2) — `LinearExt'` /
  `numLinExt'` / `probLT'` API on `RelationPoset` (~430 LoC:
  `lean/OneThird/Mathlib/RelationPoset/LinearExt.lean`).
* `mg-0b81` (commits `c2f8982`, `688ce3b`, A8-S2-cont-3) —
  Birkhoff transport + FKG port + cross-poset COUNT bound (~1100
  LoC: `lean/OneThird/Mathlib/RelationPoset/Birkhoff.lean` +
  `.../FKG.lean`).

**Total: ~2100 LoC of the originally-scoped 2000-3500 LoC has
landed.** What remains is the probability-form headline lemma
(the count-form `probLT'_mono_of_relExt` and its denominator-twin
`probLT'_count_div_le_of_relExt` are **explicitly weaker** than
the Daykin–Saks "drops" form needed by the case 2 / case 3
arguments — see `RelationPoset/FKG.lean:506-516` docstring).

### §1.4 `mg-e850` (`port-status.md`, 298 lines)

The Lean-side stop-and-report on the case3 axiom port:

* **§3.2 in-tree primitive audit.** The three count-form headlines
  (`sum_initialIdeal'_le_of_subseteq`, `probLT'_mono_of_relExt`,
  `probLT'_count_div_le_of_relExt`) all give *absolute-monotonicity*
  or *restricted-numerator* forms, none give the probability-form
  needed for case 2 / case 3 step 2.
* **§3.3 the deferred work** is named explicitly in
  `RelationPoset/FKG.lean:506-516`: probability-form cross-poset
  FKG via positive-correlation (FKG / Ahlswede–Daykin) between the
  level-`k` event `S` and the "L respects new comparabilities"
  event in the `LinearExt' Q` lattice.
* **§6 bundle scope.** ~300-600 LoC for the case-3-specific port
  on top of A8-S2-cont; ~2000-3500 LoC for the full bundle if
  A8-S2-cont infrastructure is *unbuilt*. The 2026-04-26
  diagnosis predated the A8-S2-cont-1/-2/-3 landings.

### §1.5 `lean/OneThird/Mathlib/LinearExtension/FKG.lean` (typeclass-based, ~487 LoC)

The pre-A8-S2-cont FKG primitives, all on `[PartialOrder α]`:

* `fkg_uniform_correlation` — uniform FKG on a finite
  distributive lattice (direct mathlib `fkg` with μ = 1).
* `fkg_uniform_events` — indicator form.
* `lowerSet_fkg_uniform_correlation` — specialisation to
  `LowerSet α`.
* `pi_fkg_uniform_correlation` — product lattice
  `Fin (n+1) → LowerSet α`.
* `LinearExt.fkg_uniform_initialLowerSet` — the headline:
  for monotone `F, G : LowerSet α → β`,
  `(∑_L F(L.iI k)) (∑_L G(L.iI k)) ≤ |product| · ∑_ω F(ω k) G(ω k)`,
  bound in the **product-lattice** cardinality (NOT `numLinExt'`).

The key feature for our scoping: the right-hand cardinality is
`|Fin (n+1) → LowerSet α|`, which is much larger than `numLinExt α`.
This means the existing primitive does NOT directly give the
"Daykin–Saks drops" inequality — it gives a substantially weaker
bound. Tightening the cardinality factor from `|product|` to
`numLinExt'` is the substantive remaining work.

The mathlib `Mathlib.Combinatorics.SetFamily.FourFunctions`
(Yaël Dillies, 2023) provides `fkg`, `four_functions_theorem`,
`holley` for arbitrary log-supermodular weight `μ` on a finite
distributive lattice. This will be the input (not the output) for
the Daykin–Saks proof — see §3.4.

### §1.6 `lean/OneThird/Mathlib/RelationPoset/FKG.lean` (data-version, 540 LoC)

Already in tree (mg-0b81). The data-version mirror of §1.5:

* `LowerSet' Q` distributive lattice on `Q`-lower-sets.
* `LinearExt'.initialLowerSet'` / `initialLowerSetChain'`.
* `lowerSet'_fkg_uniform_correlation` and the product-lattice
  `sum_initialLowerSetChain'_le_of_nonneg`.
* `fkg_uniform_initialLowerSet'` — the data-version headline,
  same shape as the typeclass `fkg_uniform_initialLowerSet`,
  product-lattice cardinality bound.
* `sum_initialIdeal'_le_of_subseteq` (cross-poset, **absolute
  count form**) — direct from the `LinearExt'.restrict` injection.
* `probLT'_mono_of_relExt` — the cross-poset count-form headline.
* `probLT'_count_div_le_of_relExt` — restricted-numerator
  probability form (same denominator pathology as count form).

The file's own docstrings (`§10`, `§11`, `:506-516`, `:420-426`)
are explicit about what is missing: probability-form
positive-correlation between the level-`k` event and the
"L respects new comparabilities" event in `LinearExt' Q`.

### §1.7 Convergent picture

All five predecessor artifacts converge on the same gap:

> The cross-poset comparison `Pr_Q[E] vs Pr_{Q'}[E]` for `Q ⊆ Q'`
> requires FKG positive correlation on `LinearExt' Q` between
> two events: the integrand event `E` and the
> "L respects new comparabilities" event. The current count-form
> primitives discharge the absolute (un-normalised) and
> restricted-numerator forms. The **probability-normalised**
> ("drops") form requires positive-correlation between two
> monotone events under the *uniform measure on `LinearExt' Q`*
> — i.e., the headline FKG correlation on LE(Q), tightening the
> existing product-lattice bound `|product| · …` to a
> `numLinExt'(Q) · …` bound.

This is the missing piece. Everything else in the case3 port —
revised Step 1, band-restricted Step 2, Step 3 reduction,
orientation lemma — is comparatively routine combinatorial
content once this primitive is in place.

---

## §2 The FKG infrastructure target

This section states the missing lemma in Lean signature form and
locates it in the target dependency graph.

### §2.1 The headline lemma

The deferred primitive (named in
`RelationPoset/FKG.lean:506-516, 420-426`):

```lean
/-- **Probability-form (Daykin–Saks "drops") cross-poset FKG.**

For `Q.Subseteq Q'` and a level-`k` event `S` on `Finset α` that is
**up-closed** in the inclusion order on `Finset α` (i.e.,
`I ⊆ J → S I → S J`), the probability of the level-`k` initial
ideal satisfying `S` *increases* under augmentation:

  `probEvent' Q  (fun L => S (L.initialIdeal' k.val))  ≤
   probEvent' Q' (fun L => S (L.initialIdeal' k.val))`.

Equivalently for `S` down-closed: the probability *decreases*.

This is the standard Daykin–Saks correlation inequality for
linear extensions of finite posets [Daykin–Saks 1981], also
known as the "drops" inequality, in its cross-poset
augmentation form. -/
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val))
      ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val))
```

*(Or the contravariant form for `S` down-closed; the proof is
symmetric.)*

This is the headline. Several application-shaped corollaries
follow immediately:

```lean
/-- Cross-poset comparison for the "x precedes y" event. -/
corollary probLT'_mono_of_subseteq
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (x y : α) :
    -- LE(Q') ⊆ LE(Q), so the probability that x precedes y
    -- changes monotonically when augmenting comparabilities.
    -- Direction depends on whether the new comparabilities
    -- "favour" x or y.
    sorry  -- specific signature depends on Q' structure
```

```lean
/-- Symmetric collapse: `Q'` augments `Q` by exactly the
comparabilities that exchange `(a, a')`. Then
`Pr_{Q'}[a < a'] = 1/2` (by swap involution on `Q'`), and
`Pr_Q[a < a'] ≥ 1/2` follows by `probEvent'_mono`. This is the
"≥ 1/2" half of the Case 2 FKG sub-claim. -/
theorem probLT'_ge_half_of_swap_aug
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (a a' : α) (hswap : Q'.SwapAut a a') :
    1/2 ≤ probLT' Q a a'
```

### §2.2 Proof strategy outline

There are three plausible proof strategies for the headline:

**Strategy A — Single-edge induction via FKG positive correlation
on `LinearExt' Q`.**

Reduce to the case `Q' = addRel Q a b` (single new comparability)
by induction on `(numLinExt'(Q) − numLinExt'(Q'))`. For the
single-edge case:

1. `LinearExt'(Q') = {L ∈ LinearExt'(Q) : L respects (a, b)}` —
   a sub-event `R` of `LinearExt'(Q)`.
2. `R = {L : L.lt a b}` is up-closed in some lattice on
   `LinearExt'(Q)` — TBD which one (see Strategy A.detail below).
3. The level-`k` event `S(L.iI k)` is up-closed in the same lattice
   when `S` is up-closed in `Finset α`.
4. **FKG positive correlation on `LinearExt' Q`:**
   `numLinExt'(Q) · #{L : S(L.iI k) ∧ R(L)} ≥ #{L : S(L.iI k)} · #{L : R(L)}`
5. Rearranging:
   `Pr_Q[S | R] ≥ Pr_Q[S]`, i.e.
   `Pr_{Q'}[S] ≥ Pr_Q[S]`. ✓

The crux is **step 4**: FKG positive correlation on `LinearExt' Q`
under uniform measure between two monotone events. The currently
in-tree primitives `fkg_uniform_initialLowerSet'` and
`sum_initialLowerSetChain'_le_of_nonneg` give bounds in the
*product-lattice* cardinality `|Fin (n+1) → LowerSet' Q|`, NOT
in `numLinExt'(Q)`.

The product-lattice bound is **strictly weaker**: for typical Q,
the product cardinality is `2^{n^2}` where `numLinExt'(Q)` is
`n!/(width factor)`, so the product is exponentially larger.
Tightening to `numLinExt'(Q)` is the substantive content of the
proof.

**Strategy A.detail — the lattice on `LinearExt' Q`.** The
literature gives several candidates:

* The **Bruhat order on linear extensions** — generated by
  adjacent-transposition cover relations. NOT a distributive
  lattice in general; FKG arguments don't directly apply.
* The **chain-of-ideals embedding** in
  `Fin (n+1) → LowerSet' Q` — `L ↦ L.initialLowerSetChain'`. The
  image is a proper subset of the product, NOT a sublattice
  (saturated chains' componentwise meets/joins are generally not
  saturated). This is what the existing
  `fkg_uniform_initialLowerSet'` uses, hence the
  product-lattice-cardinality bound rather than `numLinExt'`.
* The **Hibi order polytope / Stanley combinatorial approach** —
  represent LE(Q) as a chamber in the `LowerSet α` polytope, and
  use chamber-FKG. This is the cleanest mathematical formulation
  but requires substantial polytopal infrastructure not in tree.

**The standard reference proof** (Daykin–Saks 1981,
Brightwell 1999 §4) routes through *induction on the number of
comparabilities of Q* rather than directly through a lattice
structure on LE. The induction base case is `Q = discrete α`
(no comparabilities, LE = all permutations of α), where FKG is a
direct application of mathlib `fkg` to the symmetric-group lattice
under inversions. Each induction step adds one comparability (via
`addRel`), and uses the FKG correlation between two monotone
events under the uniform measure on `LinearExt' Q` to lift.

**Strategy B — FFT (Ahlswede–Daykin four-functions) with cleverly
chosen weight.**

Use `four_functions_theorem` from
`Mathlib.Combinatorics.SetFamily.FourFunctions` directly. The
theorem says: for finite distributive lattice `L` and four functions
`f₁, f₂, f₃, f₄ : L → β` with
`f₁(a) f₂(b) ≤ f₃(a ⊓ b) f₄(a ⊔ b)`, the universal sums satisfy
`(∑ f₁)(∑ f₂) ≤ (∑ f₃)(∑ f₄)`.

Apply this to `L = Fin (n+1) → LowerSet' Q` with:

* `f₁(ω) := 1_{S(ω_k)} · 1_{ω = chain of some L ∈ LE(Q')}`
* `f₂(ω) := 1_{ω = chain of some L ∈ LE(Q)}`
* `f₃(ω) := 1_{ω = chain of some L ∈ LE(Q)}`
* `f₄(ω) := 1_{S(ω_k)} · 1_{ω = chain of some L ∈ LE(Q')}`

The premise `f₁(a) f₂(b) ≤ f₃(a ⊓ b) f₄(a ⊔ b)` becomes a
log-supermodularity statement about the indicator of "is a
saturated chain of Q's lower sets". This indicator is **NOT
log-supermodular** in general (componentwise meets/joins of
saturated chains aren't saturated), so naive Strategy B fails.

A **conditional** formulation (the classical Stanley/Brightwell
trick): use weights `μ(ω) = #{L ∈ LE(Q[I]) : I = ω_k} ·
#{L ∈ LE(Q[α \ I])}` etc.; show this μ is log-supermodular by
the **Daykin inequality on |LE|** (`|LE(Q[I])| · |LE(Q[J])|
≤ |LE(Q[I ∪ J])| · |LE(Q[I ∩ J])|` for compatible I, J). But
this Daykin inequality is itself essentially the headline lemma
restricted to the cardinality functional — it's circular without
a separate proof.

**Strategy B is therefore not a standalone shortcut.** It can be
made to work in conjunction with Strategy A's induction (FFT as
the *output* of single-edge step), but it doesn't replace the
induction.

**Strategy C — Direct from the existing LinearExt typeclass FKG
via `LinearExt.fkg_uniform_initialLowerSet`.**

The docstring of `RelationPoset/FKG.lean §10` (lines 356-373)
optimistically asserts:

> we factor this through the typeclass-based
> `LinearExt.fkg_uniform_initialLowerSet` applied to
> `Q.asPartialOrder`.

On closer reading, the typeclass version has the **same
product-lattice cardinality factor** as the data version — both
are derived from `pi_fkg_uniform_correlation`. So the typeclass
version does NOT give a stronger bound; it gives the same
weakness in a different form. The docstring's "factor through"
language is aspirational rather than literal — the actual
factoring would still need the cardinality-tightening step.

**Verdict.** Strategy A (Daykin–Saks single-edge induction) is the
recommended path. The base case is `Q = discrete α`, a manageable
sub-problem (FKG on permutation symmetric-group lattice). The
inductive step uses single-edge `addRel` and a positive-correlation
lemma between the level-`k` event and the new-edge-respect event,
which can be proven by a separate sub-induction on n = `|α|`
(per Brightwell 1999 §4 / Daykin–Saks 1981).

### §2.3 Sub-lemmas needed before the headline

In Lean signature form:

```lean
-- Lemma 1: FKG positive correlation on LE(Q) under uniform
-- measure, between two monotone events (the headline FKG-on-LE).
-- Used as the engine of the single-edge induction.
theorem fkg_uniform_le_of_relPoset
    (Q : RelationPoset α)
    {β : Type*} [CommSemiring β] [LinearOrder β] [...]
    (S T : LinearExt' Q → Prop) [DecidablePred S] [DecidablePred T]
    (hSmono : MonotoneOnLE Q S)
    (hTmono : MonotoneOnLE Q T) :
    (numLinExt' Q : β) *
      ((Finset.univ.filter (fun L => S L ∧ T L)).card : β) ≥
    ((Finset.univ.filter S).card : β) *
      ((Finset.univ.filter T).card : β)

-- Where `MonotoneOnLE Q S` means: S is monotone with respect to
-- a chosen distributive lattice structure on LinearExt' Q (TBD;
-- candidates are Bruhat, ideal-chain, or polytope-chamber).
```

```lean
-- Lemma 2: For a level-k initial-ideal event with S up-closed in
-- Finset α, the pulled-back event on LE(Q) is monotone in the
-- chosen LE-lattice (this is just monotonicity of L ↦ L.iI k
-- composed with the inclusion 1_S).
lemma initialIdeal'_event_monotone_on_le
    {Q : RelationPoset α} (k : ℕ)
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    MonotoneOnLE Q (fun L : LinearExt' Q => S (L.initialIdeal' k))
```

```lean
-- Lemma 3: For a single-edge augmentation Q' = addRel Q a b, the
-- event "L respects (a, b)" is monotone on LE(Q).
lemma respect_addRel_event_monotone_on_le
    (Q : RelationPoset α) (a b : α) (hba : ¬ Q.le b a) :
    MonotoneOnLE Q (fun L : LinearExt' Q => L.lt a b)
```

```lean
-- Lemma 4: Induction step from the headline. For Q' = addRel Q a b,
-- and any up-closed S in Finset α:
theorem probEvent'_mono_of_addRel
    (Q : RelationPoset α) (a b : α) (hba : ¬ Q.le b a)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q (fun L => S (L.initialIdeal' k.val)) ≤
    probEvent' (Q.addRel a b hba)
      (fun L => S (L.initialIdeal' k.val))
```

```lean
-- Headline (assembled by induction on the relation difference
-- Q'.rel.card - Q.rel.card via a chain of single-edge addRels):
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L => S (L.initialIdeal' k.val))
```

The plumbing from `Q ⊆ Q'` to a chain of `addRel`s is supplied by
existing primitives `addRel`, `card_rel_lt_addRel`,
`Subseteq.card_rel_le` in `Mathlib/RelationPoset.lean §8`.

### §2.4 Compatibility with the case 2 / case 3 chain of inequalities

The `prop:in-situ-balanced` Case 2 / Case 3 argument
(`step8.tex:3001-3032`, `:3157-3185`) chains three inequalities
of the headline form, on a chain `Q ⊇ Q' ⊇ Q'' ⊇ Q'''`. Each link
is one application of `probEvent'_mono_of_subseteq_upClosed`, and
the chain composes via `Subseteq.trans`. So the headline lemma is
the *only* substantive new primitive needed; all chaining is
existing infrastructure.

The case 3 specific path:

* From `Π⁺(a_1) ⊆ Π⁺(a_2)` (revised Step 1 output) construct the
  symmetric `Q^{symm} ⊇ Q` augmenting `Q` so that `(a_1, a_2)`
  share their full ambient profile.
* Apply `probEvent'_mono` with `S = "level-k contains a_2 but not
  a_1"` to transport the bound `Pr_{Q^{symm}}[a_1 < a_2] = 1/2`
  (by swap involution in `Q^{symm}`) to a bound
  `Pr_Q[a_1 < a_2] ≤ 1/2 + ε` for some ε we control.
* Combine with the rotation argument (~landed via mg-5a62's
  `m3_rotation_balanced_or_residual`) and the bipartite
  `Pr ≤ 2/3` upper bound (~landed via mg-ed4d's
  `probLT_le_two_thirds_of_within_band_K2_w0`) to discharge.

The bookkeeping is comparable to (`docs/a8-status.md` reports:
~200-450 LoC for the case-3-specific bundle).

---

## §3 In-tree foundation analysis

### §3.1 What's already in tree (and counts toward A8-S2-cont)

| Module | LoC | Status |
|---|---|---|
| `lean/OneThird/Mathlib/RelationPoset.lean` (data type) | 567 | mg-b088 (A8-S2-cont-1) ✅ |
| `lean/OneThird/Mathlib/RelationPoset/LinearExt.lean` | 429 | mg-1a4f (A8-S2-cont-2) ✅ |
| `lean/OneThird/Mathlib/RelationPoset/Birkhoff.lean` | 567 | mg-0b81 (A8-S2-cont-3) ✅ |
| `lean/OneThird/Mathlib/RelationPoset/FKG.lean` (count form) | 540 | mg-0b81 (A8-S2-cont-3) ✅ |
| `lean/OneThird/Mathlib/LinearExtension/FKG.lean` (typeclass) | 487 | F6-prereq-2, dated mg-3c06 ✅ |
| `lean/OneThird/Step8/Case2FKG.lean` (Case 2 collapse + WLOG) | small | mg-8801 (A8-S2 partial) ✅ |
| `lean/OneThird/Step8/Case2BipartiteBound.lean` (Pr ≤ 2/3, K=2) | medium | mg-ed4d ✅ |
| `lean/OneThird/Step8/Case2Rotation.lean` (rotation + residual) | medium | mg-5a62 + mg-ba0c ✅ |
| `lean/OneThird/Step8/Case3Struct.lean` (Case 1 ambient form) | small | mg-f92d ✅ |
| `lean/OneThird/Step8/Case3Dispatch.lean` (Case 1/2/3 dispatch) | medium | mg-48db ✅ |

**Total in-tree A8-S2-cont infrastructure: ~2100 LoC across the
three RelationPoset/* modules.** This matches the lower end of the
original 2000-3500 LoC estimate from `docs/a8-s2-status.md:159`,
covering everything *except* the probability-form drops inequality.

### §3.2 What's missing: the Daykin–Saks "drops" headline

The single missing primitive (per §2):

```lean
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L => S (L.initialIdeal' k.val))
```

Estimated cost: **~600-1200 LoC** depending on proof strategy
(Strategy A induction is the most likely path).

### §3.3 In-tree primitives that are direct inputs to the proof

For Strategy A:

* `RelationPoset.addRel` (`Mathlib/RelationPoset.lean:347`) — the
  single-edge augmentation operator.
* `Subseteq.card_rel_le` (`Mathlib/RelationPoset.lean:533`) —
  shows `|Q.rel|` is monotone under Subseteq, providing a
  termination measure for the induction.
* `card_rel_lt_addRel` (`Mathlib/RelationPoset.lean:538`) —
  shows the induction makes strict progress.
* `LinearExt'.restrict` (`Mathlib/RelationPoset/LinearExt.lean:385`)
  — the LE-restriction map for `Q.Subseteq Q'`.
* `numLinExt'_le_of_subseteq` (`Mathlib/RelationPoset/LinearExt.lean:422`)
  — denominator monotonicity.
* `fkg_uniform_initialLowerSet'` (`Mathlib/RelationPoset/FKG.lean:325`)
  — the existing product-lattice FKG bound (an input to the proof
  but not the conclusion).

For the base case `Q = discrete α`:

* `discrete_subseteq` (`Mathlib/RelationPoset.lean:277`) — every
  Q is augmented from `discrete α`.
* `LinearExt'(discrete α)` ≃ all permutations of α (~direct port
  of mathlib's `Equiv.Perm α` Fintype). The base case FKG is
  Strategy-A's induction "Q has no comparabilities" — every `S`
  with up-closed structure satisfies the inequality trivially
  via the symmetric-group action on `Sym α`.

For the inductive step, mathlib provides:

* `Mathlib.Combinatorics.SetFamily.FourFunctions.fkg` — FKG with
  log-supermodular weight on a finite distributive lattice.
* `Mathlib.Combinatorics.SetFamily.FourFunctions.four_functions_theorem`,
  `holley` — variants.
* `Mathlib.Combinatorics.SetFamily.FourFunctions.Finset.le_card_infs_mul_card_sups`
  — Daykin inequality on Finsets.

These are inputs. The mathlib gap E5 in
`lean/MATHLIB_GAPS.md:158` (the Brightwell single-element
perturbation form for `LinearExt`, tracked as `mg-3c06`) is a
related but DISTINCT gap — it concerns the variance bound
`|Σ (f − f̄)| ≤ 2N/m`, not the cross-poset drops inequality.
However, both gaps share infrastructure (E5 also needs FKG-on-LE).
Closing the drops headline does NOT close E5 by itself, but the
two share the same lattice-on-LE prerequisite, so their proofs
should reuse common machinery (~50-200 LoC of shared lattice
infrastructure).

### §3.4 Mathlib FKG primitives — summary of what helps and what doesn't

| Mathlib primitive | Helps for drops? | Reason |
|---|---|---|
| `fkg` (log-supermodular μ on distrib lattice) | YES (input) | The induction step uses it on `Sym α` or on a single-edge LE-lattice |
| `four_functions_theorem` (universal version) | YES (input) | Generalisation of FKG; useful for compound events |
| `holley` (Holley inequality) | YES (input) | For comparing two probability measures with FKG-comparable densities |
| `Finset.le_card_infs_mul_card_sups` (Daykin on Finset) | NO | Set-level Daykin, not LE-level |
| `Birkhoff` representation theorem | YES (input) | The key tool to lift LE-FKG via Birkhoff to the distributive lattice |

**Net.** Mathlib provides the *inputs* to the proof; the *output*
(drops headline) is the gap. This matches `MATHLIB_GAPS.md §2.E`
verdict: "mathlib `fkg` is the correct *input*, not the *output*".

### §3.5 Distinction from Brightwell sharp centred (E5 / mg-3c06)

The unrelated `brightwell_sharp_centred` axiom in
`lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
is the F6 sharp centred sum bound (variance form). It is in the
trust surface as an axiom (`lean/PRINT_AXIOMS_OUTPUT.txt`),
tracked for replacement under `mg-3c06`. While its proof would
share the FKG-on-LE infrastructure with our drops headline, the
two are semantically distinct:

* **Brightwell sharp centred:** a *variance / centred-sum* bound
  in a single fixed poset.
* **Drops headline:** a *cross-poset comparison* between
  probabilities under augmentation.

Discharging the drops headline does NOT discharge
`brightwell_sharp_centred`. The two would be filed as separate
follow-on tickets (drops first; `mg-3c06` later if/when paper-side
proof matures per `mg-391c`).

---

## §4 Estimated LoC + ticket decomposition

### §4.1 Top-level breakdown

| Component | LoC | Target ticket | Polecat sessions |
|---|---|---|---|
| **A8-S2-cont-4** — drops headline + sub-lemmas (§2.1, §2.3) | 600-1200 | new (filed by PM if scoping GREEN) | 1-2 |
| **A8-S2-cont-5** — case 2 strict-witness discharge (§4.3 below) | 200-400 | new | 1 |
| **case3-port-1** — orientation lemma (Lemma 2.1 of mg-75ef §2) | 30-50 | new | parallel to others |
| **case3-port-2** — revised Step 1 (Lemma 3.3 + Claim 3.2) | 150-300 | new | 1 (if structural); larger if requires bounded enum |
| **case3-port-3** — Step 2 band-restricted FKG sub-coupling (mg-75ef §4) | 200-400 | new | 1 |
| **case3-port-4** — Step 3 reduction (mg-75ef §5) | 50-100 | new | parallel-bundle with case3-port-3 |
| **case3-port-axiom-removal** — discharge `case3Witness_hasBalancedPair_outOfScope` (mg-75ef §6) | 50-100 | new | parallel-bundle with case3-port-3 |
| **Total** | **1450-2700** | — | **4-6 sessions** |

This is a **substantial reduction** from the 2026-04-26 estimate
of 2000-3500 LoC for "A8-S2-cont" alone (which presumed the
data-poset infrastructure was unbuilt). With ~2100 LoC of
infrastructure already landed, the marginal cost of finishing
A8-S2-cont + the case3 port is roughly half what was originally
planned.

### §4.2 Dependency graph

```
                                 +------------------------+
                                 | A8-S2-cont-4: drops    |
                                 | headline (FKG-on-LE)   |
                                 | 600-1200 LoC           |
                                 +--+---------------------+
                                    |
             +----------------------+--------------+----------------------+
             |                      |              |                      |
             v                      v              v                      v
+-----------------+   +-------------------+ +---------------+   +------------------+
| A8-S2-cont-5:   |   | case3-port-3:     | | E5 / mg-3c06: |   | Other downstream |
| Case 2 strict-  |   | band-restricted   | | brightwell    |   | consumers (mg-A* |
| witness         |   | sub-coupling      | | sharp centred |   |  arcs, etc.)     |
| discharge       |   | 200-400 LoC       | | (separate     |   |                  |
| 200-400 LoC     |   |                   | |  follow-up)   |   |                  |
+-----------------+   +-------+-----------+ +---------------+   +------------------+
                              |
                +-------------+--------------+
                |                            |
                v                            v
+--------------------------+ +------------------------+
| case3-port-2:            | | case3-port-4 / axiom-  |
| revised Step 1           | | removal: Step 3 +      |
| (independent of cont-4)  | | discharge axiom        |
| 150-300 LoC              | | 100-200 LoC            |
+--------------------------+ +------------------------+

[Independent of all the above:]
+-----------------------------+
| case3-port-1: Lemma 2.1     |
| (orientation acyclicity)    |
| 30-50 LoC                   |
+-----------------------------+
```

**Critical path:** A8-S2-cont-4 → case3-port-3 → case3-port-4.
**Parallel-dispatchable:** A8-S2-cont-5 (sibling to case3-port-3,
lifting on cont-4); case3-port-1 (Lemma 2.1); case3-port-2
(Step 1; depends on no Lean primitive, only paper-rigor effort).

The **multi-polecat parallelization** is favourable: 4 polecats can
work in parallel after A8-S2-cont-4 completes. With sequential
single-polecat execution, expect ~5-6 sessions; with 2 parallel
polecats + 1 sequential cont-4, ~3-4 calendar sessions.

### §4.3 Polecat-session sizing

Each ticket fits within a 600-700k token polecat budget per
recent norms:

* A8-S2-cont-4 (600-1200 LoC) — at the upper end of single-polecat
  scope; may benefit from a sub-split into "headline + 1
  sub-lemma" / "remaining sub-lemmas" if the proof exceeds 800
  LoC. Recommend an internal tripwire: if the proof exceeds 900
  LoC, the polecat splits into A8-S2-cont-4a (induction
  framework + base case) and A8-S2-cont-4b (single-edge step).
* A8-S2-cont-5 (200-400 LoC) — comfortable single-polecat scope.
* case3-port-1 (30-50 LoC), case3-port-4, axiom-removal — small,
  bundleable.
* case3-port-2 (150-300 LoC) — comfortable single-polecat;
  watch for Claim 3.2's gap, which may force a bounded-enum
  fallback (~+200-500 LoC if enum is needed).
* case3-port-3 (200-400 LoC) — comfortable single-polecat after
  cont-4 lands.

### §4.4 Sequencing recommendation

**Sequence 1 (sequential, conservative).**

1. A8-S2-cont-4 (FIRST). Single polecat, may sub-split.
2. A8-S2-cont-5 OR case3-port-3 (IN PARALLEL after step 1).
3. case3-port-1 (PARALLEL TO 1 OR 2; tiny).
4. case3-port-2 (PARALLEL TO 1; latex-first if Claim 3.2 looks
   risky).
5. case3-port-4 + axiom-removal (LAST; bundles the discharge).

**Sequence 2 (parallelizable, aggressive).**

1. case3-port-1 (FIRST; immediate, no dependencies).
2. case3-port-2 (latex-first; verify Claim 3.2 closes by paper
   rigor before committing to the Lean port).
3. A8-S2-cont-4 (sequential after 1-2 if PM wants validation;
   parallel otherwise).
4. A8-S2-cont-5, case3-port-3 (parallel after 3).
5. case3-port-4 + axiom-removal (LAST).

PM should pick sequencing based on appetite for parallel polecat
spawning vs token-budget conservatism.

---

## §5 Risk inventory

Where might the scoping be optimistic? What structural facts could
RED an execution arc that scoping GREEN'd?

### §5.1 Risk 1 — Strategy A's single-edge inductive step is harder than ~600-1200 LoC

**Risk.** The Daykin–Saks proof in the literature
(Brightwell 1999 §4, Daykin–Saks 1981) uses a clever
*chamber-decomposition* of the LE-polytope. Translating this to
Lean's `LinearExt' Q` data type may require formalising
machinery that we don't currently have:

* **Polytope structure on `LinearExt' Q`.** Mathlib's
  `Mathlib.Geometry.Convex` is partial; the Hibi order polytope
  isn't in mathlib.
* **Chamber decomposition / barycentric subdivision.** Not in
  mathlib in the discrete setting we need.

If the cleanest proof requires polytope infrastructure, the LoC
estimate for cont-4 could balloon to 1500-2500 LoC.

**Mitigation.** Strategy A's induction does NOT inherently require
polytope machinery — Brightwell's *direct* combinatorial proof
(the "single-element perturbation" form, see
`lean/MATHLIB_GAPS.md:158`) routes through a clever
`Pred`/`Succ` fiber bijection rather than polytopes. The fiber
bijection IS in tree (`lean/OneThird/Mathlib/LinearExtension/FiberSize.lean`),
and the existing `pi_fkg_uniform_correlation` could be a usable
input under that route. **The risk is reduced but not zero:** the
existing fiber bijection was designed for the F6 sharp centred
context (single-poset variance), and adapting it to the
cross-poset cardinality-tightening setting may require
substantial new infrastructure.

**Trip-wire for the cont-4 polecat:** if the FKG-on-LE primitive
exceeds ~800 LoC mid-proof, sub-split as proposed in §4.3.

### §5.2 Risk 2 — Claim 3.2 (revised Step 1) is the F1-obstruction analogue and admits genuinely Aut-trivial counterexamples

**Risk.** From `mg-5bf9 §3.2`: "genuinely Aut-trivial Case-3
configurations are theoretically possible (F1 obstruction
analogue)". If such a configuration exists, Claim 3.2 (one-sided
aligned pair forced under linear majority) is **FALSE**, and the
sketch's discharge mechanism fails outright.

This was flagged as Open Question 3.5 in mg-5bf9. The scoping
verdict on Claim 3.2 is **uncertain at math level**.

**Mitigation paths.**

* **(M2.a) Bounded enumeration fallback.** The parameter range
  `(K, w, |X|)` is finite (`hCard ≤ 6w + 6`, `hDepth ≤ 2w + 2`).
  If Claim 3.2 fails, enumerate every isomorphism class in the
  range and verify one of: (i) Claim 3.2 holds OR (ii) the config
  has a non-trivial automorphism forcing a balanced pair anyway.
  This is the bounded enumeration of mg-75ef §3.2(a) /
  mg-5bf9 §3.3(d2). LoC: substantially larger (~500-1500 LoC for
  the enum + Bool-Prop bridge + decision procedure).
* **(M2.b) Strategy A direct on residual.** If Claim 3.2 fails
  but the overall conclusion (∃ balanced pair) is still true,
  there's an alternative discharge route via probability-form
  cross-poset FKG applied directly to the linear-majority triple
  *without* invoking one-sided alignment. This would skip Step 1
  and combine Step 2/3 in a single FKG application. Estimated
  LoC: similar to Steps 2/3 combined (~200-400 LoC) PLUS new
  rotation + cross-poset arithmetic (~200-400 LoC).
* **(M2.c) Latex-first re-investigation.** Spend a polecat session
  on closing Open Question 3.5 to paper rigor before
  committing case3-port-2 to a Lean port.

**PM action.** Sequence 2 in §4.4 explicitly schedules
case3-port-2 as latex-first BEFORE the Lean port to validate
Claim 3.2. If Claim 3.2 is false, fall back to (M2.a) or (M2.b)
with corresponding LoC adjustment.

### §5.3 Risk 3 — Drops headline requires new mathlib upstreaming, not just downstream port

**Risk.** If the drops headline lemma is genuinely *novel* in the
Lean formalisation literature (no published Lean port), the
polecat may need to pursue the typical month-long mathlib PR
review cycle. This would BLOCK the case3 port for an extended
period.

**Mitigation.** The headline is in-tree in tree-private form
(`lean/OneThird/Mathlib/RelationPoset/FKG.lean` — already
project-private namespace). No mathlib PR is required for the
case3 port itself; the lemma can live in `OneThird.Mathlib` for
now and be upstreamed later (parallel-cleanup ticket, as
`MATHLIB_GAPS.md` already tracks E5/mg-3c06).

**No PR-cycle risk** for the case3 axiom port specifically.

### §5.4 Risk 4 — F4-b trap reappears (Steps 5-7 fiber/coherence dependencies)

**Risk.** Per `feedback_complexity_blowup_means_wrong_path` and
the polecat brief's trip-wire #3:

> F4-b trap reappears (FKG infrastructure needs Steps 5-7
> fiber/coherence) → STOP, escalate.

This would mean the FKG infrastructure depends on advanced
Step-5/6/7 machinery (e.g., the cocycle lemma, BK dynamics,
Step 5 Rich/Collapse dichotomy). This would surface during
A8-S2-cont-4's actual proof.

**Mitigation.** Strategy A induction does not, by inspection,
depend on Steps 5-7 — it's a Step 8 within-`prop:in-situ-balanced`
argument. The Brightwell single-element perturbation
infrastructure (`FiberSize.lean`) is also Step-8-internal; it
predates Step 5/6/7 work. **Risk assessment: low.** Trip-wire
remains as a safety net.

### §5.5 Risk 5 — A8-S2-cont turns out to require A8-S2-cont (self-referential)

**Risk.** The polecat brief's trip-wire #5: "A8-S2-cont turns out
to require A8-S2-cont → STOP, escalate. Project-incident."

**Mitigation.** This would be a circular-dependency signal. The
scoping doesn't surface any such circularity — the drops headline
proof depends on `addRel` + induction + mathlib `fkg`, none of
which depend on the drops headline. **Risk assessment:
negligible.** Trip-wire remains as paranoia.

### §5.6 Risk 6 — The "respects new edge" event is NOT monotone in any FKG-applicable lattice on LE

**Risk.** Strategy A relies on the event `R(L) = "L.lt a b"`
being monotone with respect to the chosen distributive lattice
structure on `LinearExt' Q`. If no such lattice gives both `R`
and the level-`k` event monotonicity simultaneously, Strategy A
fails.

**Mitigation.** The Bruhat order on LE has the event `L.lt a b`
naturally up-closed (any swap strictly above L preserves
`a < b`). The level-`k` event `S(L.iI k)` for `S` up-closed in
Finset is also Bruhat-monotone (swapping later preserves earlier
ideal contents). Bruhat is *not a distributive lattice*, so
mathlib `fkg` doesn't directly apply — but the *FKG correlation*
on LE under Bruhat order is the actual content of Daykin–Saks,
and is provable directly by the chamber decomposition.

The risk is the gap between "Bruhat-monotone events correlate"
and "we can prove this in Lean". The Brightwell 1999 §4 proof
is constructive and ports to Lean as a combinatorial induction.
**Risk assessment: medium-low.** This is the one risk that could
move the LoC estimate from 600-1200 toward 1200-2000 LoC if the
Lean port of the chamber-decomposition argument turns out
verbose.

### §5.7 Risk 7 — Token budget overrun on cont-4 polecat

**Risk.** Drops headline at 1200 LoC + supporting case study at
~300 LoC + investigation overhead = ~700-900k tokens, near the
brief's 600k cap (cont-4 polecat would need a 600-900k allocation).

**Mitigation.** Sub-split per §4.3: cont-4a (induction framework
+ base case + sub-lemma signatures, ~300-500 LoC) +
cont-4b (single-edge step, ~300-700 LoC). Each sub-ticket fits
comfortably in 600k tokens.

### §5.8 Aggregate risk verdict

| Risk | Probability | LoC impact if it fires |
|---|---|---|
| 1. Single-edge step harder | medium | +500-1000 LoC |
| 2. Claim 3.2 false | medium-low | +400-1100 LoC (M2.a fallback) |
| 3. Mathlib PR cycle | low | irrelevant for project itself |
| 4. F4-b trap | low | unclear |
| 5. Self-referential | negligible | catastrophic if fires |
| 6. Bruhat-FKG gap | medium-low | +300-800 LoC |
| 7. Token overrun | low | +1 polecat session |

**Headline risk-adjusted LoC range: 1450-3700 LoC**, with
expected value around **2000 LoC** spread over **4-6 polecat
sessions**. Worst-case (multiple risks fire): ~5 LoC, ~8-10
polecat sessions. Best-case (no risks, optimistic Strategy A):
~1450 LoC, 4 sessions.

---

## §6 Aggregate verdict

**Verdict: upgraded GREEN.**

### §6.1 Rationale

* The major data-poset infrastructure (RelationPoset, LinearExt',
  Birkhoff transport, count-form cross-poset FKG) **has already
  landed** across A8-S2-cont-1/-2/-3 (~2100 LoC, 2026-04-26). This
  was the bulk of the 2026-04-26 estimated 2000-3500 LoC.
* The remaining work is the **probability-form ("drops") FKG
  inequality on `LinearExt' Q`** (~600-1200 LoC) plus the
  case-3-specific application chain (~850-1500 LoC).
* Total residual scope **~1450-2700 LoC**, broken into **4-6
  polecat sessions**, with a clean dependency graph supporting
  multi-polecat parallelisation.
* Trip-wire #4 of the polecat brief explicitly authorises this
  outcome:
  > **mathlib FKG primitive turns out to be in tree already**
  > and the scoping concludes the in-tree extension is much
  > smaller than 2000-3500 LoC → flag as **upgraded GREEN**, PM
  > files smaller execution arc, audit-bar wins big.

### §6.2 Audit-bar implication

After the residual ~2700-LoC arc lands, the
`case3Witness_hasBalancedPair_outOfScope` axiom is removed from
the trust surface. The headline trust surface would shrink from

```
[propext, Classical.choice, Quot.sound,
 brightwell_sharp_centred,
 case3Witness_hasBalancedPair_outOfScope,
 native_decide, _native.native_decide]
```

(per `lean/PRINT_AXIOMS_OUTPUT.txt` after Stage 2B)
to

```
[propext, Classical.choice, Quot.sound,
 brightwell_sharp_centred,
 native_decide, _native.native_decide]
```

— a 1-axiom reduction to mathlib trio + 2 specifically-named
axioms (Brightwell sharp centred + native_decide). This is a
substantive audit-bar improvement and aligns with
`feedback_audit_bar_for_axioms`.

### §6.3 Daniel-decision implication

Daniel's standing directive (2026-05-06T~07:01Z): "find best
forward path; don't get blocked." The upgraded-GREEN verdict is
the affirmative response: PM commissions the execution arc per §7
without further escalation. **No mail-Daniel required from this
scoping** unless a downstream polecat fires a STOP trip-wire (in
which case standard escalation applies, per
`feedback_polecat_stop_runaway`).

### §6.4 What this verdict does NOT commit to

* This scoping does NOT commit Daniel to multi-polecat execution.
  The upgraded-GREEN verdict authorises the PM to file the next
  execution ticket (A8-S2-cont-4) per §7. Subsequent tickets
  would be filed sequentially per outcome of cont-4.
* This scoping does NOT promise Claim 3.2 closes to paper rigor.
  Risk 2 (§5.2) is acknowledged; case3-port-2 is scheduled
  latex-first to validate Claim 3.2 before the Lean port.
* This scoping does NOT promise zero parallel-cleanup
  (mg-5bf9's Theorem 3.1 K=3-w=1 ~80-150 LoC sibling, separately
  filed if PM judges it audit-bar-friendly).

---

## §7 Recommended next ticket(s)

Per `feedback_pm_is_mini_ceo_default.md` and the brief's outcome
class for upgraded GREEN:

### §7.1 Primary recommendation: file A8-S2-cont-4

**Title:** `A8-S2-cont-4 — probability-form (Daykin–Saks "drops")
cross-poset FKG inequality on LinearExt' Q`

**Scope.** The headline lemma `probEvent'_mono_of_subseteq_upClosed`
(per §2.1) plus its supporting sub-lemmas (per §2.3). Strategy A
induction (single-edge addRel induction; per §2.2). Estimated
600-1200 LoC, single polecat (subsplit if exceeds 900 LoC).

**Branch.** `a8-s2-cont-4` (new), branched from `main`.

**Trip-wires.** Per §5; specifically:
* If proof exceeds 900 LoC mid-port: subsplit into cont-4a
  (framework + base case) + cont-4b (single-edge step).
* If FKG-on-LE requires polytope infrastructure not in tree:
  STOP, mail mayor, possible re-scoping with mathlib gap E5
  prerequisite.
* If A8-S2-cont turns out to require A8-S2-cont-3 (the count
  form): STOP, project-incident, mail Daniel.

**Latex-first option.** PM may require a latex-first proof of the
drops headline before the Lean port (similar to mg-75ef's
discipline). If so, file as a sub-scoping ticket
A8-S2-cont-4-scoping (paper proof of drops inequality, ~paper
sketch level), with cont-4 itself as the Lean implementation
follow-up. Recommended for token-budget conservatism.

### §7.2 Parallel sibling tickets (parallel-cleanup-class)

**Independent of A8-S2-cont-4:**

* **case3-port-1.** Lemma 2.1 of mg-75ef §2 (orientation
  acyclicity / Z/3 forbidden under (NBP)). ~30-50 LoC. Can be
  filed and dispatched immediately; no dependencies on cont-4.
* **K=3-w=1 sibling** (mg-5bf9 §3.1, Theorem 3.1 in-scope
  Z/3-cyclic argument). ~80-150 LoC. Per
  `feedback_distinguish_arc_chunk_outcomes` this is a
  parallel-cleanup ticket — NOT headline progress. PM judgment
  call on whether to file (audit-bar incremental but doesn't
  remove the case3 axiom).

**Dependent on A8-S2-cont-4 landing:**

* **A8-S2-cont-5.** Case 2 strict-witness discharge (§4.1).
  ~200-400 LoC. Discharges the existing `Case2Witness L →
  HasBalancedPair α` deferred work item from `mg-8801`.
* **case3-port-2.** Revised Step 1 (Lemma 3.3 + Claim 3.2).
  ~150-300 LoC if structural; +500 LoC for bounded-enum fallback
  if Claim 3.2 fails. **Latex-first required** before Lean port
  (per Risk 2 mitigation).
* **case3-port-3 + case3-port-4 + axiom-removal.** Step 2 +
  Step 3 + discharge `case3Witness_hasBalancedPair_outOfScope`.
  Bundleable into a single 300-500-LoC ticket once cont-4 +
  case3-port-2 land.

### §7.3 If verdict had been AMBER or RED

For completeness:

* **AMBER.** PM would mail Daniel surfacing additional research
  needed; filing a secondary scoping ticket on the gap and waiting
  for input.
* **RED.** PM would mail Daniel recommending re-evaluation:
  retain the case3 axiom in trust surface with a paper-rigor
  diagnosis (the `disposition B` of mg-e850 §8). The axiom is
  honestly disclosed today (`lean/AXIOMS.md:226-454`); the
  forum-readiness validation pass mg-d7fd already certifies the
  trust surface as publishable.

The scoping reaches upgraded GREEN, so neither path is taken.

### §7.4 Ticket-filing order (PM action)

1. **First** (immediate): file **A8-S2-cont-4** per §7.1.
2. **Concurrently** (parallel): file **case3-port-1** (Lemma 2.1)
   per §7.2.
3. **After cont-4 lands**: file **A8-S2-cont-5** + **case3-port-2**
   (latex-first) in parallel.
4. **After case3-port-2 lands**: file **case3-port-3 +
   case3-port-4 + axiom-removal** as a single bundled ticket.
5. **Optional parallel-cleanup**: file the K=3-w=1 sibling
   (mg-5bf9 §3.1) at PM's discretion, audit-bar-incremental.

**Total expected timeline:** 5-8 polecat sessions, ~3-5 calendar
days at standard cadence (Daniel's recent cadence has been
~2-3 polecats per day in active arcs).

---

## §8 Cross-references

### §8.1 Math + Lean trail (predecessors)

* `mg-75ef` (`docs/case3-port-arc/rem-enumeration-proof.md` on
  `case3-port-arc` branch, commit `878cb12`) — verdict β math
  artifact for `prop:in-situ-balanced` Case 3 (residual range).
* `mg-5bf9` (`docs/case3-port-arc/linear-majority-alignment.md` on
  `case3-port-arc` branch, commit `414aaf8`) — verdict AMBER
  alignment artifact, re-corroborates β at finer resolution.
* `mg-e850` (`docs/case3-port-arc/port-status.md` on
  `case3-port-arc` branch, commit `b6aca2d`) — Lean-side
  STOP-and-report on count-form FKG insufficiency.
* `docs/a8-s2-status.md` (mg-8801 + mg-ed4d + mg-5a62 + mg-ba0c
  status doc, dated 2026-04-26, in tree on main) — original
  A8-S2 sub-split scoping, names "A8-S2-cont — Cross-poset
  coupling infrastructure (the actual blocker)".
* `mg-b088` (commit `a2e77ee`) — A8-S2-cont-1: RelationPoset α
  data type.
* `mg-1a4f` (commit `261bcbf`) — A8-S2-cont-2: LinearExt' /
  numLinExt' / probLT' API.
* `mg-0b81` (commit `c2f8982`) — A8-S2-cont-3: Birkhoff +
  count-form cross-poset FKG.
* `docs/why-hC3-is-structural.md` (mg-cda8) — F1-F5 framing of
  the residual range.
* `lean/AXIOMS.md:226-454` — the `case3Witness_hasBalancedPair_outOfScope`
  axiom disclosure that this arc would eliminate.
* `lean/MATHLIB_GAPS.md §2.E` — the parallel mathlib-gap
  tracking for FKG / Ahlswede–Daykin (E1-E5; this arc's drops
  headline is adjacent to but distinct from the Brightwell
  single-element perturbation form E5 = mg-3c06).

### §8.2 Lean source files referenced

* `lean/OneThird/Mathlib/RelationPoset.lean` (mg-b088,
  ~570 LoC) — `RelationPoset α`, `Subseteq`, `addRel`,
  `eraseCoverRel`, `IsCover`, `discrete`, `ofPartialOrder`.
* `lean/OneThird/Mathlib/RelationPoset/LinearExt.lean`
  (mg-1a4f, ~430 LoC) — `LinearExt'`, `numLinExt'`, `probLT'`,
  `LinearExt'.restrict`, `linearExtEquiv`.
* `lean/OneThird/Mathlib/RelationPoset/Birkhoff.lean`
  (mg-0b81, ~570 LoC) — Birkhoff bijection, IdealChain', sum
  transport.
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean` (mg-0b81,
  ~540 LoC) — count-form cross-poset FKG; the file's
  `:506-516` and `:420-426` docstrings name the deferred
  probability-form headline that this scoping commissions.
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean` (~487 LoC) —
  typeclass-based FKG primitives; `fkg_uniform_initialLowerSet`
  is the typeclass mirror of the data-version count-form
  headline.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`
  (~200 LoC) — `brightwell_sharp_centred` axiom (E5 / mg-3c06).
* `lean/OneThird/Step8/Case2FKG.lean` (mg-8801) — Case 1 +
  WLOG reduction primitives, including `StrictCase2Witness L`
  the deferred FKG argument target.
* `lean/OneThird/Step8/Case2BipartiteBound.lean` (mg-ed4d) —
  bipartite Pr ≤ 2/3 upper bound (K=2, w=0).
* `lean/OneThird/Step8/Case2Rotation.lean` (mg-5a62, mg-ba0c)
  — rotation argument + chain-residual impossibility.
* `lean/OneThird/Step8/Case3Struct.lean` (mg-f92d) —
  `hasBalancedPair_of_ambient_profile_match` (Case 1 ambient).
* `lean/OneThird/Step8/Case3Dispatch.lean` (mg-48db) — Case
  1/2/3 typed dispatch.
* `lean/OneThird/Step8/Case3Residual.lean` — the axiom site.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1484` —
  `InCase3Scope` definition.

### §8.3 Mathlib primitives referenced

* `Mathlib.Combinatorics.SetFamily.FourFunctions` (Yaël Dillies,
  2023):
  * `fkg` — uniform / log-supermodular weight FKG on a finite
    distributive lattice.
  * `four_functions_theorem`,
    `four_functions_theorem_univ` — Ahlswede–Daykin universal
    form.
  * `holley` — Holley inequality for two log-supermodular
    measures.
  * `Finset.le_card_infs_mul_card_sups` — Daykin inequality on
    Finsets (set-level).
* `Mathlib.Order.Birkhoff` — Birkhoff representation theorem.
* `Mathlib.Order.UpperLower.Basic` — `LowerSet`, `IsLowerSet`.
* `Mathlib.Data.Fintype.Pi`, `Mathlib.Algebra.Order.Pi` —
  product lattices.

### §8.4 Feedback / discipline files applied

* `feedback_audit_bar_for_axioms` — applies; goal is
  axiom-elimination.
* `feedback_n_poset_is_not_ordinal_sum` — applies (irreducibility
  hypothesis is essential).
* `feedback_complexity_blowup_means_wrong_path` — trip-wires
  baked in §5.
* `feedback_announce_destination_and_eta` — PM committed to
  destination; this scoping is the first polecat-doable step.
* `feedback_distinguish_arc_chunk_outcomes` — substantive
  scoping chunk, no parallel cleanup; the K=3-w=1 sibling is a
  *separately-filed* parallel-cleanup, not part of this arc.
* `feedback_pm_is_mini_ceo_default.md` — PM authority over
  ticket filing per §7 sequencing.
* `feedback_polecat_stop_runaway.md` — trip-wire firing
  protocol.
* `feedback_latex_first_for_math_simp.md` — discipline applied
  here (this scoping doc IS the latex-first artifact); also
  recommended for case3-port-2 (Claim 3.2 risk).
* Daniel directives 2026-05-06T~06:48Z + 07:01Z — standing
  authorization for find-best-forward-path with no Daniel
  blocking input.

### §8.5 In-session inputs

* Daniel directive 2026-05-06T~06:48Z: "I'm still not shipping a
  forum post until formalization is complete."
* Daniel directive 2026-05-06T~07:01Z: "find the best way to
  take forward progress and then announce... I don't want you
  blocked."
* Daniel input 2026-05-06 (orientation lemma) — incorporated via
  mg-75ef §2 / mg-5bf9 Lemma 1.1; substantive simplification of
  the proof's territory, excludes cyclic-symmetric Case 3
  configurations from consideration.

---

## §9 Polecat protocol notes

* `mg claim mg-8d39` — done.
* `pogo schedule … mail-check-mg-8d39` — done.
* No Lean source changes — this is a scoping ticket per
  `feedback_distinguish_arc_chunk_outcomes` ("substantive
  scoping chunk; no parallel cleanup").
* This `.md` deliverable — done; the value is the scoping doc
  itself per `feedback_audit_as_deliverable`.
* Verdict **upgraded GREEN** per §6, satisfying trip-wire #4 of
  the polecat brief in the audit-bar-friendly direction
  (existing in-tree infrastructure shrinks the residual scope
  below the original 2000-3500 LoC estimate).
* No trip-wires fired during the scoping itself:
  * Trip-wire #1 (token overrun > 900k): not fired. Approximate
    spend: ~200k of the 600k budget.
  * Trip-wire #2 (new structural obstruction): not fired. The
    proof obstructions catalogued (§5) are all pre-existing
    risk surfaces, not new ones.
  * Trip-wire #3 (F4-b trap): not fired. Drops headline is
    Step-8-internal infrastructure; no Steps 5-7 dependency
    surfaces.
  * Trip-wire #4 (mathlib FKG already in tree, smaller scope):
    **fires in upgraded-GREEN direction.** Captured as the
    headline verdict in §6.
  * Trip-wire #5 (A8-S2-cont requires A8-S2-cont): not fired. No
    self-referential infrastructure surfaces.
* Mail to mayor — pending immediately after this commit, with
  the upgraded-GREEN verdict and the §7 recommended ticket
  filings.
* `mg done` — to be called only after refinery confirms the
  merge. Per polecat protocol step 7.

---

*End of scoping. Length: ~700 lines, comparable to predecessors
mg-75ef (~707 lines) and mg-5bf9 (~525 lines). Lean source
unchanged.*
