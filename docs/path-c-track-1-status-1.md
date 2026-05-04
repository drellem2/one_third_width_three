# Path C Track 1 status (round 1) — block-and-report (compound-automorphism cannot extend to case-2-strict; structural cardinality obstruction)

**Work item:** `mg-b666` (Track 1 — Resume Path C cleanup:
compound-automorphism extension to drop `hC3`).

**Status:** **Block and report**, by the brief's first
block-and-report trigger ("Compound-automorphism construction
proves intractable for the N-poset family"). The intractability
is **structural**, not budgetary: the case-2-strict residual
obstruction has an order-cardinality obstruction that rules out
*any* compound automorphism on the strict pair, regardless of how
much code is written. The path forward is **cross-track** —
defer to Track 2 (math-simp arc 2.0) or to A8-S2-cont
infrastructure (~2000-3500 LoC, multi-polecat) — not another
in-tree compound-automorphism iteration.

**Author:** `pb666` polecat, 2026-05-04.

---

## TL;DR

* The Track 1 brief asks: extend mg-84f2 / mg-c0c7 / mg-02c2's
  compound-automorphism infrastructure (which discharges
  Case 3 / `NoWithinBandPreceq L` cleanly via the matching
  lemma) to also discharge **case-2-strict** (the within-band
  ⪯-strict-pair regime that currently routes through the
  provably-false `Case2FKGSubClaim`, per `mg-a79e` /
  `mg-b0de`).

* **Structural impossibility (cardinality obstruction).** For
  any within-band ⪯-strict pair `(a, a')` with
  `upper(a) ⊊ upper(a')` strictly, **no** order-preserving
  permutation `σ : α ≃ α` with `σ a = a'` exists. Any such
  `σ` would restrict to a *bijection* between `upper(a)` and
  `upper(σ a) = upper(a')`, forcing `|upper(a)| = |upper(a')|`,
  contradicting strict inclusion. Symmetric argument for the
  lower-set strictness witness.

* **The compound-swap construction inherits this obstruction.**
  `CompoundSwap.compoundSwap L P₁ P₂` with `P₁.a₁ = a` and
  `P₁.a₂ = a'` requires `MatchingCompatible L P₁ P₂`, whose
  `preserves_le` field demands precisely the order-preserving
  permutation that the cardinality obstruction rules out. So no
  matching `P₂` (in any band) can yield a `MatchingCompatible`
  pair when `P₁` is the strict ⪯-pair.

* **Compound-automorphism on a different pair fails too.** In
  the minimal counterexample
  (`docs/a8-path-b-block-and-report-status.md` §3, `mg-a79e`):
  `α = {a, a', y}` with `a' < y` as the only comparability,
  `K = 2`, `w = 1`, satisfying every hypothesis of
  `bipartite_balanced_enum_general` and admitting the strict
  ⪯-pair `(a, a')`. Direct enumeration shows the ONLY
  poset automorphism of this `α` is the identity (every
  non-identity transposition or 3-cycle breaks the lone
  comparability `a' < y`). So compound-automorphism cannot
  produce ANY balanced witness on this 3-element configuration —
  not on `(a, a')`, not on any other pair.

* **Yet the headline holds for this configuration:**
  `probLT a a' = 1/3` by direct count over the 3 valid linear
  extensions, so `(a, a')` *is* a balanced pair (right at the
  `1/3` boundary). The witness comes from **counting**, not
  from symmetry. Compound-automorphism (a symmetry tool)
  cannot supply this; the missing ingredient is a probability
  bound.

* **The probability-bound route is the η₄ pivot — also blocked.**
  Per `mg-b0de` (`docs/a8-s2-restate-block-and-report-status.md`),
  the `≤ 2/3` upper bound for `probLT a' a` on the strict pair is
  not provable from in-tree machinery: Brightwell's sharp centred
  bound is too loose at `K = 2` (`|α| ≤ 6`), and the
  bipartite-extremal argument from `Case2BipartiteBound.lean` is
  `K = 2, w = 0` only. The genuine close requires A8-S2-cont's
  cross-poset probability-normalised FKG (~2000-3500 LoC,
  multi-polecat scope per `docs/a8-s2-status.md` §5).

* **Recommendation: cross-track pivot.** Track 1 (Path C cleanup
  via compound-automorphism over main) cannot proceed further
  this round. Two viable routes for the headline cleanup:

  1. **Defer to Track 2 (math-simp arc 2.0).** Track 2's "fresh
     framing" arc may find a reduction that bypasses case-2-strict
     entirely (e.g., a different witness organisation that doesn't
     hit the asymmetric-strict-pair regime). This is the natural
     scope-shift recommended by the brief's
     `feedback_block_and_report` clause.

  2. **Park, retain `hC3`, document.** Equivalent to `mg-94fd`'s
     option (δ) decision (2026-04-27) plus the new structural
     impossibility result. The headline keeps `hC3` indefinitely;
     the Track 1 audit trail (this doc + the four prior status
     docs + the `mg-a79e` / `mg-b0de` η₄ analyses) becomes the
     deliverable.

* **No code changes landed.** Per
  `feedback_block_and_report` and the brief's "Build breaks in
  any layered-related module → STOP" rule, this round is
  docs-only. `#print axioms width3_one_third_two_thirds`
  unchanged from baseline.

* **Token cost.** ~50K tokens of orientation + analysis + doc
  drafting. Well under the 1.5M ticket budget; the cap is
  irrelevant — the obstruction is structural, not effort-bound.

---

## 1. The Track 1 brief and what we knew going in

### 1a. The brief's substantive ask

From the `mg-b666` brief (verbatim in `## Substantive scope`):

> Extend the existing compound-automorphism infrastructure
> (`mg-84f2`, `mg-c0c7`, `mg-02c2` — landed for K=2 case-3) to
> handle the **K=2 + irreducible + w ≥ 1 + |β| ≥ 3 N-poset family**
> that is case-2-strict's residual obstruction. This is the
> family pure enumeration cannot close (uniform claim over an
> unbounded family); structural automorphism arguments are the
> in-tree path.

The brief then adds the standard `feedback_block_and_report`
escape clause:

> Compound-automorphism construction proves intractable for the
> N-poset family → file `docs/path-c-track-1-status-N.md` and
> STOP.

This document is the round-1 status for Track 1, filed under
that escape clause.

### 1b. What was landed before this round

Six "infrastructure floor" commits from the original Path C arc
(per `docs/path-c-cleanup-roadmap.md` §4):

* **mg-9568** — F5a inScope caller closure
  (`PredMaskBridge.lean`, `SymmetricLift.lean`, F5a §7-§8).
* **mg-7f06** — `OrdinalDecomp.hasBalancedPair_lift_lower` /
  `_upper` (Subtype.lean).
* **mg-a735** — width-3-threaded F3 strong-induction framework
  (`LayerOrdinal.lean`).
* **mg-27c2** — chain-form `Case2FKGSubClaim L` +
  `case2Witness_balanced_under_FKG` (`Case2Rotation.lean`).
* **mg-2e58** — `OrdinalDecomp.windowOfPairAt` (`WindowDecomp.lean`).
* **mg-26bb** — outer-loop `allBalanced → enumPosetsFor`
  bridge (`Case3Enum/AllBalancedBridge.lean`).

Three further compound-automorphism commits landed after the
roadmap was filed (between 2026-04-27's option (δ) park and the
2026-05-04 unpark):

* **mg-84f2** (`dfa923b`) — `CompoundSwap.lean` (~475 LoC):
  `SameBandPair`, `MatchingCompatible`, `compoundSwap`,
  `compoundSwap_preserves_le`, `compoundSwap_involutive`. N-poset
  canary verifies the K=2 / w=1 / 4-element instance.
* **mg-c0c7** (`235b502`) — `CompoundMatching.lean` (~682 LoC):
  `matching_exists_of_K2_irreducible_noWithinBand`. Under the
  `NoWithinBandPreceq L` hypothesis (i.e., explicitly NOT in
  case-2-strict), constructs a `MatchingCompatible` pair from
  the structural width-3 bipartite incidence pattern.
* **mg-02c2** (`c513c8d`) — `BipartiteEnumGeneral.lean` (~236 LoC):
  `bipartite_balanced_enum_general`, the three-way dispatch
  (Case 1 ambient match / Case 2 within-band ⪯-pair + `hFKG` /
  Case 3 NoWithinBandPreceq + compound swap).

The Case 2 branch of `bipartite_balanced_enum_general` consumes
`hFKG : Case2FKGSubClaim L`. **Subsequent work** discovered:

* **mg-a79e** (`64f2d87`) — `Case2FKGSubClaim L` is **provably
  false** in the K=2 strict case (3-element counterexample;
  `Pr_Q[a < a'] = 1/3 < 1/2`).
* **mg-b0de** (`8f97133`) — η₄ restate (correct direction
  `probLT a a' ≤ 1/2`) is mathematically straightforward, but the
  consumer-redesign requires a `≤ 2/3` upper bound that is **not**
  derivable from in-tree machinery.

So at unpark time, Cases 1 and 3 were structurally closed, but
Case 2 strict was open and not closeable from the existing
chain-swap + Brightwell + bipartite-extremal infrastructure.

### 1c. The case-2-strict gap, restated

`Case2Witness L` (`Case3Dispatch.lean:156`) is

```
∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧
  (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)
```

— a within-band pair `(a, a')` with `upper(a) ⊆ upper(a')` and
`lower(a') ⊆ lower(a)` (reversal-direction ⪯-comparable). The
**strict** sub-case adds a witness of inequality:

```
∃ z, a' < z ∧ ¬ (a < z)        -- upper-set strictness, OR
∃ z, z < a ∧ ¬ (z < a')         -- lower-set strictness
```

The `case2Witness_balanced_or_strict` decomposition (`mg-8801`)
sends the symmetric (non-strict) sub-case to Case 1's ambient-match
branch, leaving case-2-**strict** as the residual that
`bipartite_balanced_enum_general` routes through `hFKG`.

The Track 1 brief asks: discharge case-2-strict via **compound
automorphism** instead of `hFKG`.

---

## 2. The cardinality obstruction

This section is the substantive content of this status doc: a
rigorous structural argument that compound-automorphism cannot
extend to case-2-strict.

### 2a. The lemma

**Lemma (Order-cardinality obstruction).** Let `α` be a finite
poset and `(a, a')` a pair with `upper(a) ⊊ upper(a')` (strict
inclusion). Then there is **no** equivalence `σ : α ≃ α` such
that

* `σ a = a'`, and
* `σ` is `≤`-monotone (equivalently, `σ` is a poset
  automorphism, since `α` is finite and `σ` is a bijection).

(Symmetric statement holds for `lower(a') ⊊ lower(a)`.)

**Proof.** Suppose such `σ` exists. For any `z ∈ α`,

```
a < z   ⟺   σ a < σ z       (σ is a poset automorphism)
        ⟺   a' < σ z        (σ a = a')
```

So `σ` restricts to a map `upper(a) → upper(a')`,
`z ↦ σ z`. Because `σ` is a bijection on `α` with `σ⁻¹` also
a poset automorphism, the same argument with `σ⁻¹` (and `a' = σ a`,
`a = σ⁻¹ a'`) shows `σ⁻¹` restricts to a map
`upper(a') → upper(a)`. So `σ`'s restriction is a **bijection**
`upper(a) → upper(a')`, forcing

```
|upper(a)| = |upper(a')|.
```

But `upper(a) ⊊ upper(a')` strictly, so

```
|upper(a)| < |upper(a')|.
```

Contradiction. ∎

### 2b. Why this kills compound-automorphism on the strict pair

`CompoundSwap.compoundSwap L P₁ P₂ : Equiv.Perm α` with
`P₁ = ⟨a, a', _, _⟩` (the strict ⪯-pair) and any
`P₂ = ⟨b₁, b₂, _, _⟩` (a same-band pair in `α`) sends
`a ↦ a'` (the inner transposition flips them, and the outer
transposition leaves them alone modulo distinctness — see
`compoundSwap_a₁` at `CompoundSwap.lean:203`).

`MatchingCompatible L P₁ P₂` (`CompoundSwap.lean:169`) requires,
in its `preserves_le` field, that

```
∀ x y : α, x ≤ y →
  Equiv.swap b₁ b₂ (Equiv.swap a a' x) ≤
    Equiv.swap b₁ b₂ (Equiv.swap a a' y).
```

This is exactly the condition that `compoundSwap` is `≤`-monotone.
Combined with `compoundSwap a = a'`, it makes `compoundSwap` an
order-preserving permutation with `σ a = a'` — the kind of `σ`
the cardinality lemma forbids.

So **no `P₂` (in any band) can satisfy `MatchingCompatible L P₁ P₂`
when `P₁` is the strict ⪯-pair**. The
`matching_exists_of_K2_irreducible_noWithinBand` lemma's
hypothesis `NoWithinBandPreceq L` is not just a convenient
sufficient condition — it is **necessary** for a compound match
to exist with the strict pair in `P₁`'s slot.

### 2c. Why the obstruction is not avoidable by choosing a
different `P₁`

In some configurations, one could try `P₁ ≠` the strict pair.
But (i) for the headline to be closed uniformly, every
configuration in the K=2 / irreducible / w≥1 / |β|≥3 family must
admit *some* compound match; and (ii) the minimal counterexample
admits no nontrivial poset automorphism at all.

**Minimal counterexample** (`mg-a79e` §3): `α = {a, a', y}`,
`a' < y` as the only comparability, `K = 2`, `w = 1`,
`band a = band a' = 1`, `band y = 2`. Verified to satisfy every
hypothesis of `bipartite_balanced_enum_general`
(`HasWidthAtMost α 3`, `LayerOrdinalIrreducible L`, `K = 2`,
`w ≥ 1`, `|α| ≥ 3`).

Enumeration of poset automorphisms of `α`:

| `σ`                    | preserves `a' < y`? | poset auto? |
|------------------------|---------------------|-------------|
| `id`                   | ✓                   | ✓           |
| `(a, a')` (transp.)    | maps to `a < y`     | ✗ (`a ≮ y`) |
| `(a, y)` (transp.)     | maps to `a' < a`    | ✗ (`a' ≮ a`) |
| `(a', y)` (transp.)    | maps to `y < a'`    | ✗           |
| `(a, a', y)` (3-cycle) | maps to `y < a`     | ✗           |
| `(a, y, a')` (3-cycle) | maps to `a < a'`    | ✗ (`a ≮ a'`)|

Only `id` survives. So the automorphism group is trivial:
`Aut(α, ≤) = {id}`. Compound `Equiv.swap` is a non-identity
permutation by construction (it swaps two distinct same-band
elements at minimum); so there is **no `MatchingCompatible` pair
in this α at all**. Compound-automorphism produces zero balanced
pair witnesses on this configuration.

Yet the headline holds: `(a, a')` is a balanced pair with
`probLT a a' = 1/3` (one of three valid linear extensions has
`pos a < pos a'`), exactly at the `[1/3, 2/3]` boundary. The
witness comes from **counting linear extensions**, not from
symmetry.

This single counterexample is sufficient: any uniform
compound-automorphism dispatch over the K=2 / irreducible /
w≥1 / |β|≥3 family must close this 3-element configuration, but
compound-automorphism produces no witness here at all. ∎

### 2d. Why the obstruction is not a Lean-formalization
artefact

The cardinality argument in §2a is a one-paragraph proof in
ordinary mathematics. It does not depend on any Lean-specific
encoding choice. It applies equally to:

* The current `MatchingCompatible.preserves_le` formulation
  (`Equiv.swap b₁ b₂ ∘ Equiv.swap a₁ a₂` preserves `≤`);
* Any alternative formulation that asks for an order-preserving
  permutation swapping `a ↔ a'`;
* Any "weaker" formulation that only asks for *some* injection
  `upper(a) → upper(a')` and surjection `upper(a') → upper(a)`,
  since the two together still force `|upper(a)| = |upper(a')|`.

The obstruction is a property of the strict ⪯-pair regime, not
of the specific Lean construction. Reformulating the dispatch
predicate or the matching lemma cannot work around it.

---

## 3. What about extending the compound-automorphism API?

Two natural extensions of the existing
`CompoundSwap.MatchingCompatible` infrastructure suggest themselves
*a priori*; both fail for the same structural reason.

### 3a. "Triple-orbit" compound automorphism

Idea: swap three pairs simultaneously, e.g.,
`σ := (a a')(b₁ b₂)(c₁ c₂)`, allowing the third orbit to absorb
the asymmetry.

**Why it fails.** The cardinality obstruction in §2a is on the
**restriction of σ to upper(a)**, regardless of what σ does on
the rest of α. Any `σ` with `σ a = a'` restricts to a bijection
`upper(a) ↔ upper(a')` purely from being an order-preserving
bijection on `α`. Adding more orbits does not change the
cardinality of those two sets.

### 3b. "Partial" compound automorphism (poset embedding instead
of automorphism)

Idea: weaken `σ` to an injection `α → α` (not a bijection) that
preserves `≤` and sends `a ↦ a'`.

**Why it fails for our purpose.** The symmetry argument used in
`hasBalancedPair_of_matchingCompatible`
(`BipartiteEnumGeneral.lean:153`) requires `σ` to be an
*involution* (`compoundSwap_involutive`) so that the pullback of
linear extensions along `σ` is a **bijection** on `LinearExt α`,
exchanging the filters `{L : L.lt a a'}` and `{L : L.lt a' a}`.
Without bijectivity, the pullback produces only an inequality
between the two filter sizes, not equality, and `probLT a a' = 1/2`
does not follow.

The probability bound that *would* follow from a one-sided
order-preserving injection is something like
`probLT a a' ≤ 1/2` — exactly what `probLT_le_half_of_chain`
(mg-ba0c) already gives via the chain swap, with the same
direction. So this alternative collapses to (a special case of)
the existing chain-swap argument, providing no new bound.

### 3c. "Compound automorphism on a different witness"

Idea: don't try to swap `(a, a')`; instead find some *other*
pair `(u, v)` (not `(a, a')`) admitting a compound-automorphism
witness that gives `probLT u v = 1/2`.

**Why it fails.** The minimal counterexample in §2c has trivial
automorphism group: no non-identity poset automorphism of α
exists at all, so no compound automorphism on any pair is
available. This is a uniformity obstruction — even a single
configuration where the construction fails kills the dispatch
strategy for the whole family.

For larger configurations (4+ elements), one might find pairs
admitting compound matches, but the family includes the 3-element
configuration and any others where the trivial-automorphism-group
phenomenon recurs. Closing the family uniformly requires a
mechanism that handles such configurations — and counting (the
A8-S2-cont route) is the only one in scope.

---

## 4. The probability-bound route — already blocked

The complementary route to compound-automorphism is to discharge
case-2-strict via probability bounds:

* **Chain swap upper bound** (mg-ba0c, in tree):
  `probLT a a' ≤ 1/2` for any within-band ⪯-comparable pair.
* **Missing lower bound:** `probLT a a' ≥ 1/3` (or equivalently
  `probLT a' a ≤ 2/3` for the reverse pair) — required to land
  *some* member of `{(a, a'), (a', a)}` in `[1/3, 2/3]`.

Per `mg-b0de` (`docs/a8-s2-restate-block-and-report-status.md`),
this missing bound is **not** derivable from in-tree machinery:

* Brightwell sharp centred bound (mg-46d7's
  `BrightwellAxiom.lean:159`) gives
  `|p_{xy}(Q) − p_{xy}(Q − z)| ≤ 2/|Q|`. Specialised to the
  strict-witness `z`, with the symmetric configuration giving
  `Pr = 1/2`, this yields `Pr ∈ [1/2 − 2/|Q|, 1/2 + 2/|Q|]`.
  For `Pr ≥ 1/3` we need `|Q| ≥ 12`. **K=2 has `|α| ≤ 6`**;
  Brightwell is vacuous in our regime.
* `Case2BipartiteBound`'s
  `probLT_le_two_thirds_of_within_band_K2_w0` is `K=2, w=0` only
  (relies on `bipartite_balanced_enum`'s `hAB`, false at `w ≥ 1`).
* Cross-poset count-form FKG
  (`probLT'_count_div_le_of_relExt`) gives the wrong direction.

The genuine close requires the deferred A8-S2-cont
**probability-normalised** cross-poset FKG (paper's
`step8.tex:2916-2940`). Per `docs/a8-s2-status.md` §5, this is
~2000-3500 LoC of cross-poset infrastructure, multi-polecat or
Daniel-led milestone scope.

---

## 5. Cross-track recommendation

The Track 1 brief explicitly reserves "block-and-report"
authority and cites `feedback_block_and_report` and the
existence of Track 2 ("math-simp arc 2.0") in parallel as
risk absorbers. Per the brief's `## Block-and-report triggers`:

> Compound-automorphism construction proves intractable for the
> N-poset family → file `docs/path-c-track-1-status-N.md` and
> STOP.

Filing as round 1.

### 5a. Why not "another round" of compound-automorphism

The pc-94fd round-4 stop-loss (`mg-94fd`,
`docs/a5-g3e-path-c-wiring-v5-status.md`) was explicitly framed
as "rotation argument cannot extend; compound-automorphism is the
structural fact missing." That assessment held; mg-84f2 / mg-c0c7
/ mg-02c2 *did* extend the rotation infrastructure to compound-
automorphism, and *did* close Cases 1 and 3 cleanly. **The new
finding** is that compound-automorphism **also** has a structural
cap — it cannot extend to case-2-strict, by the cardinality
argument of §2.

This is **a different obstruction** from pc-94fd's "rotation
can't extend": pc-94fd named the right tool (compound
automorphism); pb666 names the *next* obstruction (cardinality
forbids it on strict pairs). Each round identifies a real
structural barrier and shows that the chosen tool cannot
overcome it. There is no "fifth round" of in-tree
compound-automorphism work that would help case-2-strict; the
tool itself is wrong for the regime.

### 5b. The two viable paths forward

* **(A) Defer to Track 2 (math-simp arc 2.0).** Track 2 is
  authorised to explore "fresh framing" — i.e., not compound-
  automorphism, not chain-swap-plus-Brightwell. A successful
  Track 2 reduction that bypasses case-2-strict (e.g.,
  reorganises the dispatch so the strict-pair regime is absorbed
  by a different argument upstream) would close Path C without
  needing the missing probability bound or the missing
  symmetry. **This is the recommended pivot.**

* **(B) Park, retain `hC3`, document.** Equivalent to mg-94fd's
  option (δ) plus this round's structural impossibility result.
  The headline `OneThird.width3_one_third_two_thirds` keeps
  `hC3` indefinitely; the audit trail (this doc, the four
  prior status docs, and the `mg-a79e` / `mg-b0de` η₄ analyses)
  becomes the deliverable.

  Path C cleanup remains revivable per
  `docs/path-c-cleanup-roadmap.md` §7 — the cited revival
  triggers (mathlib compound-automorphism, K=2 finite enumerator,
  the chain-form FKG sub-claim being discharged by Route B,
  the layered width-3 chain `1/3` lower-bound conjecture) are
  unchanged by this round, except that triggers gated on
  compound-automorphism (mathlib trigger, finite enumerator
  trigger) **must additionally** address the cardinality
  obstruction shown in §2 — e.g., by leaning on a full
  enumeration of the strict-pair regime rather than a single
  symmetry argument.

### 5c. What this round does NOT recommend

* **Not another K=2 + irreducible compound-automorphism
  iteration.** Round 5 of this arc would re-run the same
  structural obstruction.
* **Not axiomatising `Case2FKGSubClaim`** (any direction).
  The `1/2 ≤ probLT a a'` direction is provably FALSE per
  `mg-a79e`; the `probLT a a' ≤ 1/2` direction is a theorem
  via chain swap and adds nothing. Either way, axiomatisation
  is unsound or vacuous.
* **Not a multi-hypothesis `hStep` predicate.** Per the original
  c5d5a10 → mg-05d3 negative exemplar, "drop one opaque
  hypothesis, add another" is not Path C cleanup. Both Track 1
  and Track 2 must close case-2-strict structurally or via
  bona-fide probability bounds.

---

## 6. What this polecat lands

* **This status doc** (`docs/path-c-track-1-status-1.md`).
* **No Lean code changes.** Per the brief's STOP rule and
  `feedback_block_and_report`.
* **No new axioms, no `sorry` / `admit`.**
* `#print axioms width3_one_third_two_thirds` unchanged from
  baseline:

  ```
  [propext, Classical.choice, Quot.sound,
   OneThird.LinearExt.brightwell_sharp_centred]
  ```

* The η₅ park override
  (`override_pathB_parked_eta5_2026_04_27.md`, referenced in the
  brief) is **not** independently superseded by this round;
  this round confirms the park decision was correct and adds
  the structural impossibility that pc-94fd could not have
  surfaced (the impossibility is on the
  *compound-automorphism extension*, which had not been
  attempted at park time). PM may now formally retire the η₅
  memory as superseded by `path-c-cleanup-roadmap.md` plus
  this status doc.

---

## 7. References

### Primary

* **Track 1 brief** — `mg show mg-b666`.
* `lean/OneThird/MainTheorem.lean:52-57` — headline
  `width3_one_third_two_thirds` retaining `hC3`.
* `lean/OneThird/Step8/LayeredBalanced.lean:438-444` —
  `Case3Witness.{u}` definition (the predicate that would have
  to be proved as a theorem under cleanup).
* `lean/OneThird/Step8/CompoundSwap.lean` — `SameBandPair`,
  `MatchingCompatible`, `compoundSwap` (mg-84f2).
* `lean/OneThird/Step8/CompoundMatching.lean` —
  `matching_exists_of_K2_irreducible_noWithinBand` (mg-c0c7;
  conditioned on `NoWithinBandPreceq L`, which is exactly NOT
  case-2).
* `lean/OneThird/Step8/BipartiteEnumGeneral.lean` —
  `bipartite_balanced_enum_general` three-way dispatch
  (mg-02c2; Case 2 branch routes through `hFKG`).
* `lean/OneThird/Step8/Case2Rotation.lean:629` —
  `probLT_le_half_of_chain` (chain swap, mg-ba0c).
* `lean/OneThird/Step8/Case2Rotation.lean:772` —
  `Case2FKGSubClaim` structure (mg-27c2).
* `lean/OneThird/Step8/Case3Dispatch.lean:156` —
  `Case2Witness L`.
* `lean/OneThird/Step8/Case3Dispatch.lean:176` —
  `Case3Witness L` (the inner residual; do not confuse with the
  outer `Case3Witness.{u}` in `LayeredBalanced.lean`).

### Status-doc audit trail (newest first)

* `docs/path-c-track-1-status-1.md` — **this doc** (mg-b666).
* `docs/a8-s2-restate-block-and-report-status.md` — η₄
  block-and-report (mg-b0de): `≤ 2/3` upper bound not
  derivable from in-tree machinery.
* `docs/a8-path-b-block-and-report-status.md` — Route B
  block-and-report (mg-a79e): `Case2FKGSubClaim` provably
  false in strict case.
* `docs/path-c-cleanup-roadmap.md` (b75e6ad) — option (δ)
  park deliverable, mg-7261.
* `docs/a5-g3e-path-c-wiring-v6-status.md` — v6
  block-and-report (mg-5f0c): 5-axiom target infeasible.
* `docs/a5-g3e-path-c-wiring-v5-status.md` — v5
  block-and-report (mg-94fd): rotation cannot extend, compound
  is the structural fact missing.
* `docs/a5-g3e-path-c-wiring-v4-status.md` — v4
  block-and-report (mg-0fa0): K=2 + irreducible + w≥1 + |β|≥3
  surfaces.
* `docs/a5-g3e-path-c-wiring-v3-status.md` — v3
  block-and-report (mg-072c): two further infrastructure
  pieces surface.
* `docs/a5-g3e-fkg-route-status.md` — round-2
  block-and-report (mg-4a5b): three infrastructure pieces
  identified.
* `docs/a8-s2-strict-witness-status.md` — round-1
  block-and-report (mg-43f3): both signature shapes need
  Route B or chain `1/3` conjecture.

### Prior-art cross-references

* `step8.tex:2855-2940` — paper's case 2 / FKG sub-claim.
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:407-426` —
  Route B's deferred probability-normalised cross-poset FKG.
* `lean/AXIOMS.md` — `brightwell_sharp_centred` entry.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current baseline (this
  docs-only commit does not change it).

### Reminders / brief / governance

* `pm-onethird/1777914292578721000.5852.1000` — Daniel's
  2026-05-04 unpark reminder
  (reproduced verbatim in `mg show mg-b666`'s "Origin" section).
* `feedback_block_and_report` — STOP rule on intractability.
* `feedback_polecat_stop_runaway` — STOP rule on runaway
  behavior.
* `feedback_audit_bar_for_axioms` — no new axioms (this round
  adds none).
* `feedback_latex_first_for_math_simp` — math articulated in
  §2 of this doc; no `.tex` change since the cleanup target is
  Lean (and the math is a one-paragraph cardinality argument
  not requiring a formal `.tex` build-out).

---

## 8. Final state

* No code changes landed; `lake build` not invoked (no Lean
  files touched).
* `pb666` mailed mayor with the verdict per
  `feedback_block_and_report`'s "report" half (separately, via
  `mg mail send`).
* Headline still carries `hC3 : Step8.Case3Witness.{u}`.
* `pb666` calls `mg done mg-b666` only after the refinery
  confirms this docs-only commit merged to main.
* PM's next call: pivot to (A) Track 2 (math-simp arc 2.0) or
  (B) re-park with the obstruction now structurally
  documented. Track 1 (compound-automorphism over main) is
  exhausted.
