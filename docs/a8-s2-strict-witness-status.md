# A8-S2-strict-witness status — block-and-report (FKG-only closure)

**Work item:** `mg-43f3` (StrictCase2 closure to unblock mg-b329 Path C
structural seam).

**Status:** **blocked — FKG-only closure**. Both viable signature shapes
in the spec require either Route B (probability-normalised cross-poset
FKG, future work) or the layered width-3 chain `1/3` lower-bound
conjecture (open). Mailing mayor + pm-onethird per the task body's
HARD CONTINGENCY clause.

**Author:** `pc-43f3` polecat, 2026-04-26.

---

## TL;DR

* The spec offers two signature shapes:
  * **(a)** `strictCase2Witness_balanced : ∀ L, StrictCase2Witness L → HasBalancedPair α`
  * **(b)** drop the FKG hypothesis from `strictCase2WitnessChain_balanced_under_FKG`.
* Both fail unconditionally for the same reason: the chain hypothesis
  forces `probLT a a' ≤ 1/2` (chain swap, mg-ba0c), but produces no
  matching `≥ 1/3` lower bound. Without a lower bound, neither
  `(a, a')` nor the reverse `(a', a)` lands in `[1/3, 2/3]`.
* The `StrictCase2Witness` predicate carries only the witness pair and
  its forward chain; the surrounding layered context (width-3,
  irreducibility, `¬InCase3Scope`) lives at the *call site* in
  `Case3WitnessHStep`, not in the witness itself, so a witness-level
  closure cannot exploit it.
* Per task instructions: NOT axiomatizing the FKG case, NOT exiting.

---

## 1. Inventory

### 1a. The witness shape (Case2FKG.lean:217)

```lean
def StrictCase2Witness (L : LayeredDecomposition α) : Prop :=
  ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧ a ∥ a' ∧
    (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a) ∧
    ¬ ((∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a'))
```

Chain direction: `upper(a) ⊆ upper(a')`, `lower(a') ⊆ lower(a)`.
Strict negation: at least one reverse implication fails, so at least
one of the two inclusions is **proper** (i.e., the chain is strict).

### 1b. The closures already in tree

* `Step8.InSitu.probLT_le_half_of_chain` (Case2Rotation.lean:629,
  mg-ba0c). Under one-sided ⪯-chain `(a, a')`,
  `probLT a a' ≤ 1/2` via the chain-swap injection on linear extensions.
* `Step8.InSitu.chain_residual_impossible` (Case2Rotation.lean:689,
  mg-ba0c). The "all forward `> 2/3`" residual from
  `m3_rotation_balanced_or_residual` is structurally impossible under
  the chain hypothesis (immediate corollary of the above).
* `Step8.InSitu.strictCase2WitnessChain_balanced_under_FKG`
  (Case2Rotation.lean:717, mg-ba0c). The chain → balanced theorem
  conditional on the FKG sub-claim hypothesis `1/2 ≤ probLT a_i
  a_{i+1}` for each chain pair.

### 1c. The cross-poset infrastructure (RelationPoset/FKG.lean)

* `RelationPoset.probLT'_mono_of_relExt` (FKG.lean:464, mg-0b81).
  The **count-form** FKG monotonicity-under-augmentation: adding
  comparabilities can only shrink the count of LEs satisfying any
  level-`k` event.
* `RelationPoset.probLT'_count_div_le_of_relExt` (FKG.lean:521,
  mg-0b81). The restricted-numerator probability form.
* The genuine **probability-normalised** form `Pr_Q[E] ≥ Pr_{Q'}[E]`
  required by the paper's FKG sub-claim is acknowledged future work
  (`Mathlib/RelationPoset/FKG.lean:407-426`).

---

## 2. Why option (a) does not close

We have `(hne, hi, h_up, h_down)` for the pair `(a, a')`. Apply
`probLT_le_half_of_chain`:

```
probLT a a' ≤ 1/2,
equivalently probLT a' a ≥ 1/2.
```

For `HasBalancedPair α` we need some incomparable `(x, y)` with
`1/3 ≤ probLT x y ≤ 2/3`. The candidate pairs are `(a, a')` and
`(a', a)`:

* `(a, a')` balanced ⇔ `1/3 ≤ probLT a a'`. We have `probLT a a' ≤ 1/2`,
  but no lower bound is available.
* `(a', a)` balanced ⇔ `probLT a' a ≤ 2/3` (the lower bound `≥ 1/3`
  follows from `probLT a a' ≤ 1/2`). We have `probLT a' a ≥ 1/2`,
  but no `≤ 2/3` upper bound from chain alone.

The chain swap is **one-directional**: it injects `{L : a < a'}` into
`{L : a' < a}` but does *not* admit the reverse injection (precisely
because `lower(a) \ lower(a') ≠ ∅` in the strict case, blocking the
reverse swap on LEs that already have `a' <_L a`). So no upper bound
on `probLT a' a` falls out of chain alone.

The strict negation gives us `probLT a a' < 1/2` strictly, but does
not yield any `≥ 1/3` lower bound: the gap between `< 1/2` and
`≥ 1/3` is precisely the open part of the 1/3-2/3 conjecture.

---

## 3. Why option (b) does not close

The chain-witness version `StrictCase2WitnessChain L` has three
within-band ⪯-chain elements `a₁ ⪯ a₂ ⪯ a₃`. Chain swap on each
adjacent pair gives `probLT a_i a_{i+1} ≤ 1/2`, and on the (1,3)
direction `probLT a₁ a₃ ≤ 1/2`.

`m3_rotation_balanced_or_residual` (Case2Rotation.lean:356), invoked
with the chain-forward labelling, requires hypotheses
`1/2 ≤ probLT a_i a_{i+1}` (the FKG sub-claim direction). Combined
with the chain-swap upper bound, this forces `probLT a_i a_{i+1} = 1/2`
exactly — i.e., the **symmetric collapse** sub-case, which is already
absorbed into Case 1 by `case2Witness_balanced_or_strict`. So in the
**strict** chain case, the FKG sub-claim hypothesis is *false*, and
the dispatch cannot be applied with the forward labelling.

The mg-ba0c status doc `docs/a8-s2-rotation-residual-status.md` §4
documents the **reverse-labelling** alternative: invoke
`m3_rotation_balanced_or_residual` with `(a₃, a₂, a₁)` instead. The
hypotheses then become `1/2 ≤ probLT a_{i+1} a_i`, which **do** hold
by chain swap. The dispatch produces:

```
HasBalancedPair α ∨
  (2/3 < probLT a₃ a₂ ∧ 2/3 < probLT a₂ a₁ ∧ 2/3 < probLT a₃ a₁)
```

The new residual — equivalently, `probLT a_i a_{i+1} < 1/3` for all
three forward pairs — is **NOT closeable by chain alone**. Chain swap
gives `probLT a_i a_{i+1} ≤ 1/2`, which is **consistent** with
`< 1/3`. The mg-ba0c status doc explicitly flags this as the open
gap (§4b), citing two routes:

* **Route B (probability-normalised cross-poset FKG).** Future work in
  `Mathlib/RelationPoset/FKG.lean §11`.
* **The 1/3-2/3 conjecture for layered width-3 chains.** Open;
  empirically holds in small examples but no Lean proof exists.

Closing option (b) unconditionally requires one of these.

---

## 4. Why surrounding hypotheses cannot be threaded into a witness-level closure

The structural-dispatch composer (the `Case3WitnessHStep` whose
construction is one of the open obligations of mg-b329) has access at
the call site to `(L, hW3, ¬IsChainPoset, 2 ≤ card, K ≥ 2,
¬InCase3Scope, ih_for_smaller)`. None of this rich context is carried
inside the `StrictCase2Witness L` predicate, which is a bare
`∃ a a', ...` proposition.

Two ways one could address this:

1. **Thread context into the witness.** Change `case2Witness_balanced_or_strict`
   to return a witness predicate that also carries `(hW3, …,
   ¬InCase3Scope)`, allowing the closure to use them. But this is
   exactly what `case3Witness_hasBalancedPair_outOfScope` does
   (it's an axiom that takes the full layered + structural profile),
   and re-exposing it under a new name is just relabeling.

2. **Close inside the dispatch composer.** Have the
   `Case3WitnessHStep` constructor handle `StrictCase2Witness` inline,
   using whichever closure route is available. This is what
   `bounded_irreducible_balanced_hybrid` does — it composes Case 1 +
   Case 2 + Case 3 with the surrounding hypotheses available. But the
   StrictCase2 sub-branch *of* this composer needs the same closure
   we are trying to provide; without Route B or the 1/3 conjecture,
   the composer cannot complete.

Neither route is achievable in a single polecat session.

---

## 5. Implications for mg-b329 / `width3_one_third_two_thirds`

If the StrictCase2 closure is truly FKG-only, then mg-b329's Path C
cannot drop `hC3` cleanly without `width3_one_third_two_thirds`
gaining an FKG hypothesis. The current headline (after mg-b329's
partial landing) takes `hStep : Case3WitnessHStep` as an explicit
hypothesis; closing `hStep` constructively still requires the
StrictCase2 discharge.

Per task instructions, this is a signature change Daniel may not want
and requires guidance from pm-onethird before proceeding.

---

## 6. What I am doing

Per the task body's HARD CONTINGENCY clause:

* **Mailed pm-onethird** with the full analysis (subject:
  "HARD CONTINGENCY: StrictCase2 closure is FKG-only").
* **Mailed mayor** with summary.
* **NOT axiomatizing** any FKG case.
* **NOT exiting**; standing by for guidance.

This status doc lands as the block-and-report deliverable
(matching the precedent of `docs/a8-s2-rotation-residual-status.md`,
mg-ba0c).

---

## 7. References

* Polecat instructions: `mg-43f3` task body.
* `docs/a8-s2-status.md` — A8-S2 parent status (mg-8801, mg-5a62, mg-ed4d).
* `docs/a8-s2-rotation-residual-status.md` — mg-ba0c precedent: chain
  swap + the all-three-`< 1/3` gap analysis (§4-5).
* `docs/a5-g3e-status.md` — mg-b329 partial: F3 framework, `hC3`
  dropped, gap §3a flags this StrictCase2 closure as open.
* `lean/OneThird/Step8/Case2FKG.lean:217` — `StrictCase2Witness L`
  predicate.
* `lean/OneThird/Step8/Case2FKG.lean:226` —
  `case2Witness_balanced_or_strict`.
* `lean/OneThird/Step8/Case2Rotation.lean:629` —
  `probLT_le_half_of_chain` (mg-ba0c).
* `lean/OneThird/Step8/Case2Rotation.lean:689` —
  `chain_residual_impossible` (mg-ba0c).
* `lean/OneThird/Step8/Case2Rotation.lean:717` —
  `strictCase2WitnessChain_balanced_under_FKG` (mg-ba0c).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:407-426` — Route B
  documented future work.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (this docs-only
  commit does not change it).
