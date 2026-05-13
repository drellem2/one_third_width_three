# EX-7 C-redo Session C scoping — universal vs directional master theorem closure path (consumer audit)

**Scope.** Latex-first scoping (mg-f3b9, dispatched 2026-05-12). Picks the
forward path for sub-α-C after the chamber-restricted inner inequality
`InnerInequalityAdj` landed axiom-free in tree (mg-c8ac, `84b7216`,
state.md §1.35). No Lean changes; no new axioms in this scoping pass.
Token budget cap 150k.

## §0 TL;DR

**Verdict: Option 1 (LE-non-adjacent residual closure → universal master
theorem, ~300–500 LoC).** The downstream consumer audit (EX-8
case3-port-2 + EX-9 Brightwell-port-A) finds that **neither consumer is
directional-S compatible** with the (a, b)-directional restriction
introduced by `DirectionalUpClosed` (mg-c8ac §6). Restricting the master
theorem to directional events would require redesigning both consumer
applications (mg-75ef §3 and Brightwell §4) — substantially more math
work than completing the universal closure.

PM next step: file Session D execution ticket per §5.

## §1 Recap: state of EX-7 post Session C-redo Session B (mg-c8ac)

Per state.md §1.35 (commit `84b7216`):

* The chamber-restricted target landed axiom-free as
  `RelationPoset.innerInequalityAdj_of_upClosed_directional`
  (`lean/OneThird/Mathlib/RelationPoset/InnerInequalityAdjacent.lean`).
  `#print axioms` returns only `[propext, Classical.choice, Quot.sound]`.
* Trust surface UNCHANGED at 4 named axioms.
* `InnerInequalityAdj` gates on **both** `hSmono` (up-closed) AND `hSdir`
  ((a, b)-directional). The directional hypothesis is intrinsic — it
  encodes the asymmetry between `Q⁺ = Q + (a < b)` and `Q⁻ = Q + (b < a)`
  that the universal mg-7a4f `InnerInequality` (REVERTED, mg-b4a7)
  obliterated, and is precisely what excludes the mg-2f8c minimal
  counterexample (`S(I) := b ∈ I` on the 2-antichain).
* `InnerInequalityAdj` alone does **not** close
  `probEvent'_mono_of_subseteq_upClosed`. Two gaps:
  1. **Non-adjacent residual.** The inner inequality restricts to
     LE-adjacent extensions; the master theorem ranges over all LEs.
  2. **Directional restriction.** The chamber-restricted form requires
     `S` to be (a, b)-directional; the master theorem's signature takes
     arbitrary up-closed `S`.

Three forward paths (state.md §1.35):

1. **LE-non-adjacent residual closure** (Brightwell §4 chained-adjacent-
   transposition reduction; ~300–500 LoC; possibly with
   `stanley_log_supermod` consumption at recursion-depth bound). Pairs
   with `InnerInequalityAdj` to give the full universal-up-closed master
   theorem.
2. **Directional-S master theorem** (lightweight follow-up; ~100–200
   LoC). Restricts master to (a, b)-directional `S` throughout the
   subseteq-induction chain. **Acceptable iff** downstream consumers'
   up-closed events `S` are (a, b)-directional for *every* pair (a, b)
   added in the Q → Q' subseteq chain.
3. **Option β retry at the residual closure.** Axiomatize the
   LE-non-adjacent residual if option 1 hits a polecat-budget envelope.
   Smaller surface than the original mg-87de Option β (the universal
   form is known unsound; the residual axiom would be paired with a
   full brute-force numerical sanity check before Daniel-approval, per
   the mg-b4a7 §1.33 mandate).

This session audits options 1 vs 2 by inspecting EX-8 and EX-9 consumers.

## §2 EX-8 consumer audit — case3-port-2 (mg-75ef §3 + mg-5bf9 §3)

### §2.1 Application shape

EX-8 derives `case3Witness L → HasBalancedPair α` (the pre-axiom unwrap
of `case3Witness_hasBalancedPair_outOfScope`, currently axiomatised in
`lean/OneThird/Step8/Case3Residual.lean:208`). The application
specialises `probEvent'_mono_of_subseteq_upClosed` to the case3 width-3
antichain witness scope.

**Subseteq chain.** Per mg-75ef §3 + sub-α-A scoping §4.4: the case3
chain `Q ⊂ Q'` adds the case3 constraints on the width-3 antichain
`A = {a₁, a₂, a₃}`. The added relations are between elements of `A`
(specifically, the L1/L2 case3 orientations forced by the witness
configuration), i.e., `(Q'.rel \ Q.rel) ⊆ A × A`.

**Balanced-pair witness event.** The fundamental balanced-pair event in
the tree (Step8/FrozenPair.lean:73–84) is

```
S_xy := {L ∈ 𝓛(P) : x <_L y}, pairIndicator x y L = 𝟙[L ∈ S_xy]
```

This is **not** a single-level event `S(L_k)` — it is pair-positional on
the full linear extension. To plug into `probEvent'_mono_of_subseteq_upClosed`,
it must be rewritten as a level-k event:

```
x <_L y  ↔  ∃ k. (x ∈ L_k ∧ y ∉ L_k)
        ↔  for k = (L.pos y).val, (x ∈ L_k ∧ y ∉ L_k)
```

The standard reduction (matching mg-75ef §3's structural framing): for
fixed level `k`, the level-k events `S(L_k) := x ∈ L_k` and
`S(L_k) := y ∈ L_k` are the **building blocks** of the balanced-pair
bound; the witness `x <_L y` decomposes as a level-by-level disjunction.

### §2.2 Directionality check

**Event `S(L_k) := x ∈ L_k`.** For (a, b) with `a, b ∉ {x}` and
`x ≠ a, b`: directional ✓ trivially (the event doesn't depend on a or b).
For (a, b) = (·, x), i.e., `b = x`:
* `S(K ∪ {b}) = S(K ∪ {x}) = (x ∈ K ∪ {x}) = ⊤`.
* `S(K ∪ {a}) = (x ∈ K ∪ {a}) = (x ∈ K)`. Since `b = x ∉ K`, this is `⊥`.
* `⊤ → ⊥` is **false**, so (a, b)-directional **fails** when `b = x`.

For (a, b) = (x, ·), i.e., `a = x`: vacuously directional (`x ∈ K ∪ {y} = ⊥`
since `x = a ∉ K` and `x ≠ y = b`).

**Conclusion.** `S(L_k) := x ∈ L_k` is (a, b)-directional iff `b ≠ x`.
Equivalently: x must never be the **target** of any added edge in the
Q → Q' chain.

**Symmetric for `S(L_k) := y ∈ L_k`.** Directional iff `b ≠ y`.

### §2.3 Master-theorem chain over case3 added edges

Case3 added edges all lie in `A × A` where `A = {a₁, a₂, a₃}` is the
width-3 antichain. The witness pair `(x, y)` in the balanced-pair
extraction is naturally chosen **from `A`** (per Theorem E's
`frozenPairCut_exists`, the pair is incomparable in the strengthened
γ-counterexample, and the case3 dispatch operates on `A`-pairs). So
`x, y ∈ A`.

The case3 chain typically adds **both** orientations for distinct
antichain edges — e.g., the L1 orientation may force `(a₁ < a₂)` while
the L2 constraint forces `(a₃ < a₂)`. Concretely: the targets `b_i` of
the added edges range over `A`, and **`x` and `y` will both appear as
targets** in any non-trivial case3 chain that pins down a specific
balanced pair via FKG monotonicity.

**Directional fails for `S(L_k) := x ∈ L_k`** whenever some `b_i = x`,
which happens for at least one added edge in any non-trivial case3
chain. Similarly for `S(L_k) := y ∈ L_k`.

### §2.4 Could the case3 application be redesigned for directional-S?

Three salvage strategies:

1. **Pick (x, y) outside A.** Not viable: `frozenPairCut_exists`
   (Theorem E) is the only mechanism producing an incomparable pair
   with the bulk-probability lower bound; the case3 dispatch operates
   precisely on the antichain elements where the structural witness
   lives.

2. **Reorder the added edges so that the "bad" direction never appears.**
   The subseteq induction `addRel` (mg-7a4f's framework) supports any
   topological ordering of `Q' \ Q`. But the orientation of each added
   edge `(a < b)` is fixed by `Q'` — the polecat does not get to flip
   `(a₁ < a₂)` to `(a₂ < a₁)` while preserving `Q'`. So reordering
   doesn't change the set of `b_i` values; it only changes their
   sequencing.

3. **Use a constructed directional event.** Replace `S(L_k) := x ∈ L_k`
   with `S(L_k) := T ⊆ L_k` for some `T ⊆ α \ {b_i for all i}`. By
   mg-ed38 §2.2 (sanity check), this is directional iff no `b_i ∈ T`.
   But then `T` cannot include `x` (since `x = some b_i` for some i),
   and the event no longer constrains `x`'s position — losing the
   balanced-pair-witness content.

**Verdict.** EX-8 case3-port-2 **cannot** be made directional-S compatible
without redesigning mg-75ef §3's witness construction. The redesign
would require a new combinatorial argument that operates on case3 width-3
antichains via *only* events that exclude antichain elements from the
"target" position — a fundamentally different proof strategy.

## §3 EX-9 consumer audit — Brightwell-port-A (Brightwell §4)

### §3.1 Application shape

EX-9 derives `brightwell_sharp_centred` (currently axiomatised in
`lean/OneThird/LinearExtension/BrightwellAxiom.lean`) by applying the
drops headline to the product lattice `L(α) × Fin m`. Per mg-3c06 +
path-alpha-scoping/scoping.md §3.1, the Brightwell §4 proof of
`eq:sharp-centred` (`step8.tex:1046–1276`) reduces the centred-sum bound
to:

1. τ separating Pred / Succ.
2. **Distributive lattice on `L(α) × {1,…,m}`** (the τ-inversion ×
   natural order).
3. **Monotonicity claims (a)–(e)** for `1_A, P, S, 1_{B_-}, 1_{B_+}` on
   the product τ-inversion lattice.
4. **AD sign constraints** via `four_functions_theorem` (mathlib).
5. Kahn–Saks per-term bound (independent infrastructure; not consumed
   here).

Step 5 is parallel infrastructure (Brightwell §4.7's exchange involution).
Steps 1–4 are the FKG-on-LE / drops-headline consumption that EX-9 ports.

### §3.2 Events `S` used in Brightwell §4

The five indicators/functions are (per `step8.tex:1100–1180` +
`brightwell-port-scope.md §4.4` framing):

* `1_A` — indicator of "A holds" where `A` is an event on `L(α) × Fin m`
  (e.g., `{(L, j) : L_j ⊆ Pred}` or analogous).
* `P, S` — counting functions `L ↦ |{predecessors of x in L_j}|` and
  similar; these are **integer-valued monotone** functions, not 0/1.
* `1_{B_-}, 1_{B_+}` — indicators of "B_- holds" and "B_+ holds".

These functions are monotone on the τ-inversion product lattice, but
they range over a **rich algebra of monotone events / functions** on
`L(α) × Fin m` — encompassing pred / succ position bounds and arbitrary
shifts that depend on multiple elements simultaneously.

### §3.3 Directionality check

The directional hypothesis for the chamber-restricted inner inequality
is (a, b)-asymmetric: it favours `a` over `b`. For (a, b)-directional
`S` in the product lattice, **every** indicator must satisfy the
swap-asymmetric condition for **every** edge (a, b) added in the chain.

* `1_A` for `A = {(L, j) : L_j ⊆ Pred}`: if `b ∈ Pred`, the indicator
  changes character when swapping b out for a (whose Pred-membership
  may differ). Specifically, the directional condition requires
  `b ∉ Pred ∨ a ∈ Pred` — neither of which is guaranteed by Brightwell
  §4's `τ`-construction in general.

* `P, S` (integer-valued): the directional condition lifts to integer
  monotone functions as
  `∀ K with a, b ∉ K, f(K ∪ {b}) ≤ f(K ∪ {a})`. For Brightwell's
  `P, S` functions (which count predecessors/successors of specific
  elements relative to position `j`), this would force a structural
  asymmetry of `(a, b)` vis-à-vis Pred / Succ. Not satisfied for
  generic `(a, b)`-pairs traversed by the master-theorem induction.

* The `four_functions_theorem` step (Brightwell §4.4) applies AD to
  arbitrary monotone-non-negative pairs on the product lattice. AD is a
  4-event correlation inequality that does **not** carry a directional
  hypothesis through its statement. Restricting it to directional-S
  would invalidate the structural shape of Brightwell §4.4's argument
  (the proof composes AD applications on full algebras of monotone
  events, not on directional sub-algebras).

### §3.4 Could Brightwell-port-A be redesigned for directional-S?

Brightwell §4 is a **published combinatorial argument** (Brightwell 1999
§4). Its monotonicity claims (a)–(e) are stated and proved over the full
algebra of monotone events on the τ-inversion lattice. Restricting to a
directional sub-algebra would:

1. Break the symmetry that AD exploits (`four_functions_theorem` works on
   pairs of monotone events; the directional restriction is a *single
   ordered pair* (a, b) condition, not a symmetric monotonicity
   condition).
2. Invalidate the (a)–(e) monotonicity proofs as stated — each one
   uses LE-non-adjacent transpositions implicitly (via the τ-inversion
   lattice's covering relation, which is *not* restricted to LE-adjacent
   swaps).
3. Require a new combinatorial argument replacing Brightwell §4 — out
   of scope for sub-α-C and beyond the "port a known result" budget
   envelope.

**Verdict.** EX-9 Brightwell-port-A **fundamentally requires** the
universal up-closed form of `probEvent'_mono_of_subseteq_upClosed`. The
directional restriction would invalidate Brightwell §4.4's argument as
published.

## §4 Recommendation

### §4.1 Headline

**Option 1: LE-non-adjacent residual closure, ~300–500 LoC.** Closes
the universal `probEvent'_mono_of_subseteq_upClosed` by combining
`InnerInequalityAdj` (mg-c8ac, in tree) with the LE-non-adjacent
residual via Brightwell §4 chained-adjacent-transposition reduction.

### §4.2 Why not Option 2 (directional master)

The audit (§2 + §3) finds that **neither EX-8 nor EX-9 is
directional-S compatible**:

| Consumer | Event family | Directional in every added (a, b)? |
|----------|--------------|-------------------------------------|
| EX-8 case3-port-2 | `S(L_k) := x ∈ L_k` for x in case3 antichain A; case3 chain adds edges within A | **NO** — `x` appears as target of at least one added edge in any non-trivial chain |
| EX-9 Brightwell-port-A | `1_A, P, S, 1_{B_-}, 1_{B_+}` over τ-inversion product lattice; AD-style argument | **NO** — Brightwell §4.4 uses the full algebra of monotone events; directional restriction breaks AD's symmetric structure |

A directional master theorem (~100–200 LoC) **could land** as auxiliary
infrastructure, but would not close EX-8 or EX-9. The marginal value
beyond `InnerInequalityAdj` itself is small (only one extra inductive
step would be unlocked); the universal closure is the binding constraint.

### §4.3 Why Option 1

* Preserves the **published** Brightwell §4 argument verbatim (no
  consumer redesign).
* Preserves mg-75ef §3's case3-port structural framing.
* Closes the universal master theorem definitively; downstream EX-8 +
  EX-9 + EX-10 unblock in turn.
* Estimated ~300–500 LoC (state.md §1.34 + §1.35), within a single
  polecat budget envelope (~250–400k tokens given the latex-first
  structure can be ported densely).

### §4.4 Risk: `stanley_log_supermod` consumption at recursion-depth bound

Per state.md §1.34: "possibly with `stanley_log_supermod` consumption at
the recursion-depth bound". The Brightwell §4 chained-adjacent-
transposition reduction recursively reduces a non-adjacent swap of (a, b)
to a sequence of adjacent swaps through intermediate elements. At the
recursion-depth bound (the worst-case swap distance `|L.pos b - L.pos a|`),
the proof may need `stanley_log_supermod` (in-tree axiom; per state.md
§1.11 / mg-d0fc, sound by independent verification mg-e22f) to control
the magnitude blow-up.

**Implications.**
* Trust surface remains at 4 axioms (`stanley_log_supermod` is already
  one of them). No new axioms.
* If the recursion does not need `stanley_log_supermod`, even better —
  the residual closure is then strictly axiom-free.
* **No new axioms** in this scoping pass per the §5 trip-wire fence.

### §4.5 Hybrid: directional master as stepping stone (optional)

If the polecat dispatched for Option 1 wants to land the directional
master theorem as a lightweight *intermediate* deliverable before
tackling the LE-non-adjacent residual, that is fine — it would:

* Validate the `InnerInequalityAdj → directional master theorem`
  reduction independently (~100–200 LoC, axiom-free).
* Provide a checkpoint mid-session for budget reasoning.

But it is **not** a substitute for Option 1; the universal form is the
binding constraint per §4.2.

## §5 Session D execution spec

### §5.1 Title

EX-7 Session C-redo Session D — LE-non-adjacent residual closure
(universal `probEvent'_mono_of_subseteq_upClosed`).

### §5.2 Predecessor

mg-c8ac (`84b7216`, state.md §1.35) — `InnerInequalityAdj` +
`innerInequalityAdj_of_upClosed_directional` in tree, axiom-free.

### §5.3 Scope

Land in `lean/OneThird/Mathlib/RelationPoset/`:

1. **`probEvent'_mono_addRel_adjacent`** (~100–150 LoC). Single-edge
   `addRel` step `Q → Q + (a < b)` reducing to `InnerInequalityAdj`
   under LE-adjacent restriction + (a, b)-directional `S`. Then lift to
   arbitrary `S` via the residual.
2. **`probEvent'_mono_addRel_nonAdjacent`** (~150–300 LoC). The Brightwell
   §4 chained-adjacent-transposition reduction: for LEs where `(L.pos b) -
   (L.pos a) ≥ 2`, recursively reduce to adjacent swaps via an
   intermediate `c` with `(a, c)` or `(c, b)` `Q`-incomparable. Recursion
   on swap distance.
3. **`probEvent'_mono_of_subseteq_upClosed`** (~50–100 LoC). Induction
   on `|Q'.rel \ Q.rel|` via `addRel`; each step closes by the
   single-edge primitive in (1)+(2).

**Estimated total**: ~300–500 LoC; ~250–400k tokens.

### §5.4 Hypothesis on `S`

**UNIVERSAL** up-closed: `∀ I J : Finset α, I ⊆ J → S I → S J`. Not
directional. Per §4.2, this is what EX-8 + EX-9 require.

### §5.5 Acceptance

* `lake build OneThird` green.
* `#print axioms probEvent'_mono_of_subseteq_upClosed` returns
  `[propext, Classical.choice, Quot.sound]` (axiom-free) **or** adds
  `stanley_log_supermod` (already in tree, no trust-surface regression).
  Any other axiom is a trip-wire.
* No new project axioms.
* No regression on existing build targets.

### §5.6 Trip-wires

1. **Token blow-up.** Approaching 80% of cap (~120k of 150k for a 150k
   session, or ~320k of 400k for a 400k session): STOP, surface budget
   status to PM. May need sub-split into Session D-a (single-edge
   adjacent) + Session D-b (residual chaining + master assembly).
2. **Brightwell §4 hypothesis gap.** If the chained-adjacent-transposition
   reduction requires a hypothesis beyond `stanley_log_supermod` (e.g.,
   `cellMass_AD` or `brightwell_sharp_centred` or a *new* axiom): STOP,
   surface to PM. Likely indicates a structural gap requiring a
   follow-up scoping pass.
3. **Numerical sanity finds violation.** If a Session B-style brute-force
   sanity check (cf. mg-c8ac §1.35) fires against the
   chained-adjacent-transposition reduction: CRITICAL, mail PM + Daniel
   URGENT. The reduction would be unsound; the universal target may
   itself be sub-α-C-fatal.
4. **`stanley_log_supermod` strength insufficient.** If the recursion-
   depth bound needs a *stronger* log-supermod inequality than
   `stanley_log_supermod` provides: STOP, surface to PM. This would
   indicate a Brightwell §4 misreading; would justify an Option β-style
   axiomatization request to Daniel.

### §5.7 Optional pre-check (Session D polecat may run before execution)

Brute-force numerical sanity script on small finite instances (per
mg-b4a7 §1.33 mandate): enumerate `(α, Q, Q', k, S)` over the mg-2f8c
19-poset coverage; verify
`probEvent' Q (S ∘ initialIdeal' k) ≤ probEvent' Q' (S ∘ initialIdeal' k)`
holds for all up-closed `S`. If 0 violations: green light to proceed
with structural proof. If any violation: CRITICAL trip-wire.

### §5.8 Out of scope for Session D

* EX-8 case3-port-2 (consumer; ~800–1200 LoC; deferred to a separate
  Session, blocked behind Session D).
* EX-9 Brightwell-port-A (consumer; ~500–800 LoC; deferred).
* EX-10 axiom-removal of `case3Witness_hasBalancedPair_outOfScope` +
  `brightwell_sharp_centred` (final consumer; ~100–200 LoC).
* Directional master theorem as standalone deliverable (optional
  stepping stone per §4.5; not required).

## §6 References

* **mg-c8ac** (`84b7216`, state.md §1.35) — Session C-redo Session B,
  `InnerInequalityAdj` axiom-free landing.
* **mg-ed38** (`de032be`, state.md §1.34) — Session C-redo Session A,
  chamber-restricted target scoping; introduced `DirectionalUpClosed`.
* **mg-b4a7** (`fe87be2`, state.md §1.33) — REVERTED universal
  `InnerInequality_axiom` after mg-2f8c trip-wire.
* **mg-2f8c** (state.md §1.32) — independent verification fired the
  trip-wire on the universal `InnerInequality` (133 180 violations / 19
  posets).
* **mg-7a4f** (state.md §1.28) — original master-theorem reduction
  `probEvent'_mono_addRel_of_inner` (sound; gates on inner inequality).
* **mg-afcf** (`0212cee`, state.md §1.30) — LE-adjacent swap
  infrastructure consumed by `InnerInequalityAdj`.
* **mg-75ef** — case3-port-2 math artifact
  (`docs/case3-port-arc/rem-enumeration-proof.md`); EX-8 application.
* **Brightwell 1999, §4** — chained-adjacent-transposition reduction
  for the LE-non-adjacent residual closure (the structural input to
  Option 1).
* **`docs/path-alpha-execution-arc/state.md`** §1.35 forward-path
  analysis.
* **`docs/path-alpha-execution-arc/ex7-chamber-restricted-scoping.md`**
  (mg-ed38) — chamber-restricted target latex + §2.2 directional sanity
  checks consumed by §2.2 + §3.3 of this scoping doc.
* **`docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`** §5.7–§5.10
  — sub-α-C critical path; EX-7 / EX-8 / EX-9 / EX-10 specs.
* **`docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`** §4.4 — case3
  + Brightwell consumer dependencies on the missing drops primitive.
* **`docs/path-alpha-scoping/scoping.md`** §3.1 — what
  `brightwell_sharp_centred` consumes; identifies FKG-on-LE as covering
  steps 1–4 of the Brightwell §4 argument.
* **`lean/OneThird/Step8/FrozenPair.lean`** — `pairCut`,
  `pairIndicator` (Theorem E witness for case3-port-2).
* **`lean/OneThird/Mathlib/RelationPoset/InnerInequalityAdjacent.lean`**
  (mg-c8ac, post-`84b7216`) — `DirectionalUpClosed`, `InnerInequalityAdj`,
  `innerInequalityAdj_of_upClosed_directional`.
* **`lean/OneThird/Step8/Case3Residual.lean:208`** —
  `case3Witness_hasBalancedPair_outOfScope` axiom (target of EX-8).
* **`lean/AXIOMS.md`** — 4-axiom trust surface
  (`brightwell_sharp_centred`, `case3Witness_hasBalancedPair_outOfScope`,
  `stanley_log_supermod`, `cellMass_AD`).

---

*End of EX-7 C-redo Session C scoping deliverable. Verdict: GREEN
(option 1 picked, Session D spec ready). No Lean changes; no new axioms;
trust surface UNCHANGED at 4 named axioms.*
