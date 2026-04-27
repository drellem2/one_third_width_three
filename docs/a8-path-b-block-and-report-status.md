# A8-Path-B status — block-and-report (Case2FKGSubClaim is provably false in strict case)

**Work item:** `mg-a79e` (lean: A8-Path-B — prove `Case2FKGSubClaim`
constructively via Route B cross-poset FKG; replaces planned new
axiom).

**Status:** **Block and report — case (a) of mg-a79e's hard
block-and-report rule.** The Route B proof is not just out of
single-polecat scope (~2000-3500 LoC of cross-poset infrastructure
per `docs/a8-s2-status.md` §5); the `Case2FKGSubClaim L` predicate
as currently stated is **provably FALSE on natural inputs**, so
neither (i) constructive proof, nor (ii) axiomatisation under
audit-bar, would be sound. PM should re-decide between
restating the SubClaim, dropping it from the discharge plan, or
pivoting per the brief's pre-committed options.

**Author.** `pc-a79e` polecat, 2026-04-27.

---

## TL;DR

* **The SubClaim is FALSE on natural Case 2 inputs.** A 3-element
  layered counterexample with `K = 2`, `w = 1`, `|α| = 3`,
  `LayerOrdinalIrreducible`, `HasWidthAtMost α 3` — i.e.
  satisfying *every* hypothesis of
  `bipartite_balanced_enum_general` — has a within-band chain pair
  `(a, a')` where the SubClaim's `pair` field's chain hypothesis
  holds vacuously but `probLT a a' = 1/3 < 1/2`, violating the
  conclusion. See §3 below.

* **Mathematically, Route B can't fix this.** The
  `docs/a8-s2-rotation-residual-status.md` (mg-ba0c) §3 already
  observes: chain swap forces `probLT a a' ≤ 1/2`, and any FKG
  sub-claim direction `1/2 ≤ probLT a a'` combined with chain swap
  forces equality, i.e., the *symmetric collapse* case. In the
  strict case (which is where `case2Witness_balanced_or_strict`
  routes), `1/2 ≤ probLT a a'` is **violated**, period — no
  amount of cross-poset infrastructure changes that.

* **The hard block-and-report rule fires under case (a).** The
  proof requires substantively new mathematical content beyond
  what's in tree, AND in fact the SubClaim's logical content is
  not what the paper proves. Per the candor clause, no proof
  attempt is going to land here.

* **No code changes landed.** Status doc only. The headline-wiring
  in mg-5f0c remains conditional on `hC3`/`hFKG` per the v6 status
  doc (`docs/a5-g3e-path-c-wiring-v6-status.md`).

---

## 1. What was supposed to land

mg-a79e's brief, under R3.1 (PM-onethird verdict on Daniel
axiom-clarification): replace the v6/v6.1 plan to *add* a
`Case2FKGSubClaim` axiom — instead, *prove* the chain-form FKG
sub-claim via Route B (probability-normalised cross-poset FKG).

Method (per the brief):

1. Per-term Kahn-Saks/Brightwell covariance bound on
   `LinearExt α × Fin (m+1)`.
2. FKG / Ahlswede-Daykin inequality application.

Estimated 200-500 LoC.

Hard block-and-report rule:
> (a) the proof requires substantively new mathematical
> infrastructure beyond Route-B-style probability-normalised
> cross-poset FKG (e.g., per-term covariance arguments that turn
> out to be substantively novel), OR
> (b) the proof requires a new axiom (any kind), OR
> (c) lake build fails after the new theorem in a way that
> suggests deeper API mismatches with mg-27c2's existing
> Case2FKGSubClaim structure
> STOP and block-and-report per standard protocol.

This polecat's verdict is **case (a)**, with the additional
finding that the SubClaim itself (not just the proof) is not what
the paper claims.

---

## 2. The structural problem

`Step8.InSitu.Case2FKGSubClaim L` (`Case2Rotation.lean:772`) is:

```lean
structure Case2FKGSubClaim (L : LayeredDecomposition α) : Prop where
  pair : ∀ a a' : α, a ≠ a' → L.band a = L.band a' → a ∥ a' →
    (∀ z, a < z → a' < z) → (∀ z, z < a' → z < a) →
    (1 : ℚ) / 2 ≤ probLT a a'
  chain : ∀ a₁ a₂ a₃ : α, … similar shape over chains …
```

The chain hypothesis says `upper(a) ⊆ upper(a')` and
`lower(a') ⊆ lower(a)` — i.e., `a'` has *more upper edges* and
*fewer lower edges* than `a`. The paper's intuition
(`step8.tex:2868`): "more forced edges means earlier in LE", so
`a'` tends to come before `a`.

That gives `Pr[pos a' < pos a] ≥ 1/2`, equivalently
`probLT a a' = Pr[pos a < pos a'] ≤ 1/2`. **This matches the chain
swap bound** `probLT_le_half_of_chain` (mg-ba0c, Case2Rotation
§6).

The SubClaim's `pair` field claims the OPPOSITE direction,
`1/2 ≤ probLT a a'`. The two combined force `probLT a a' = 1/2`
exactly — the symmetric collapse case, already absorbed by
`case2Witness_balanced_or_strict` (mg-8801) into Case 1.

In the **strict** chain case (chain forward but reverse fails),
chain swap is a *strict* injection (not surjection), so
`probLT a a' < 1/2` *strictly*, violating the SubClaim's
`1/2 ≤ probLT a a'`.

This is exactly what `docs/a8-s2-rotation-residual-status.md`
(mg-ba0c) §3 explicitly says:

> In the **strict** chain case (lower-set inclusions are proper
> inclusions), the chain swap injection is strict
> (`probLT a₁ a₂ < 1/2`), so `hFKG`'s `1/2 ≤ probLT a₁ a₂` is
> **violated**.

So the SubClaim's `pair` field is **provably false** for L's
admitting any strict within-band ⪯-chain pair.

---

## 3. Concrete counterexample

Let `α := {a, a', y}` with the partial order generated solely by
`a' < y` (so `a ∥ a'`, `a ∥ y`, `a' < y`).

**Layered decomposition `L`.** Define:
* `K := 2`, `w := 1`.
* `band a := 1`, `band a' := 1`, `band y := 2`.
* `band_size`: each band has size ≤ 3 ✓ (sizes 2, 1).
* `band_antichain`: band 1 = {a, a'} is an antichain (`a ∥ a'`);
  band 2 = {y} singleton ✓.
* `forced_lt`: requires `band x + w < band y`; with `w = 1` and
  `K = 2`, this is vacuous (max band gap is 1, not >1).
* `cross_band_lt_upward`: only comparability is `a' < y` with
  `band a' = 1 ≤ 2 = band y` ✓.

So `L : LayeredDecomposition α` is well-defined.

**Hypothesis check for `bipartite_balanced_enum_general`:**
* `hWidth3 : HasWidthAtMost α 3`: width(α) = max antichain size =
  `|{a, a'}| = 2 ≤ 3` ✓.
* `hIrr : LayerOrdinalIrreducible L`: only cut is at `k = 1`;
  reducibility at `k = 1` would require every element of band 2
  (just `y`) to be > every element of band 1 (`{a, a'}`), i.e.,
  `a < y` AND `a' < y`. We have `a' < y` but `a ∥ y`, so the cut
  is NOT reducible, hence `L` IS irreducible ✓.
* `hK2 : L.K = 2` ✓.
* `hw : 1 ≤ L.w` ✓ (`w = 1`).
* `hCard : 3 ≤ Fintype.card α` ✓ (`|α| = 3`).

**SubClaim's `pair` field at `(a, a')`:**
* `a ≠ a'` ✓.
* `L.band a = L.band a' = 1` ✓.
* `a ∥ a'` ✓.
* `∀ z, a < z → a' < z`: `upper(a) = ∅`, vacuous ✓.
* `∀ z, z < a' → z < a`: `lower(a') = ∅`, vacuous ✓.
* Conclusion: `1/2 ≤ probLT a a'`.

**Computing `probLT a a'`.** Linear extensions of `(α, ≤)` are
permutations of `{a, a', y}` respecting `a' < y`:

| LE          | `pos a` | `pos a'` | `pos y` | Valid (`pos a' < pos y`)? | `pos a < pos a'`? |
|-------------|---------|----------|---------|---------------------------|-------------------|
| (a, a', y)  | 0       | 1        | 2       | ✓                         | ✓                 |
| (a, y, a')  | 0       | 2        | 1       | ✗                         | —                 |
| (a', a, y)  | 1       | 0        | 2       | ✓                         | ✗                 |
| (a', y, a)  | 2       | 0        | 1       | ✓                         | ✗                 |
| (y, a, a')  | 1       | 2        | 0       | ✗                         | —                 |
| (y, a', a)  | 2       | 1        | 0       | ✗                         | —                 |

Valid LEs: 3. Of these, exactly one has `pos a < pos a'` (the
first row). So:

```
probLT a a' = 1 / 3.
```

**SubClaim conclusion check:** `1/2 ≤ 1/3`? **FALSE.**

**Chain swap bound check:** `probLT a a' ≤ 1/2`? `1/3 ≤ 1/2` ✓
(consistent with `probLT_le_half_of_chain`).

**Strict witness check:** Reverse chain
`(∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a')`. The first
conjunct fails at `z = y`: `a' < y` but `¬(a < y)`. So this is a
genuine STRICT chain pair (not symmetric).

So `(a, a')` in this `L` is a strict within-band ⪯-chain pair
satisfying every Lean-level hypothesis of `Case2FKGSubClaim.pair`,
yet the conclusion fails.

---

## 4. Why Route B does not save this

The brief's "Method" prescribes per-term Kahn-Saks/Brightwell
covariance bound + FKG/Ahlswede-Daykin. Even if that
infrastructure were ported (estimated 500-800 LoC for Brightwell
alone per `lean/AXIOMS.md`'s `brightwell_sharp_centred` entry, and
~2000-3500 LoC total per `docs/a8-s2-status.md` §5), the resulting
probability-normalised cross-poset FKG bound *cannot* prove
`1/2 ≤ probLT a a'` in the strict case, **because that conclusion
contradicts the chain swap bound `probLT a a' < 1/2` (strict in
the strict case)**.

Route B can only prove `probLT_Q[E] ≥ probLT_{Q'}[E]` for
`Q.Subseteq Q'` and down-closed `E`. Applied to the natural
augmentation `Q' := Q ∪ {a < a'}` (forcing the comparability), one
gets:

```
probLT_Q[a < a'] ≥ probLT_{Q'}[a < a'] = 1.
```

Trivially false: probability ≤ 1. So this isn't the right
augmentation.

The OTHER natural augmentation `Q'' := Q ∪ {a' < a}`:

```
probLT_Q[a < a'] ≥ probLT_{Q''}[a < a'] = 0.
```

Trivially true. No information.

The paper's argument (`step8.tex:2858-2875`) goes via a *third*
poset `Q'`: the one obtained by replacing `a_{i+1}`'s profile
with `a_i`'s (so they share the larger profile). With Lean's
labelling (`a' = a_i` having more upper edges), this means
*adding* upper edges to `a` to match `a'`'s upper set. In the
counterexample of §3, that means adding `a < y` to `Q`; the new
poset `Q'` has `a < y` and `a' < y`, making `a` and `a'` share
profile `{y}`.

In `Q'`, by symmetric collapse, `probLT_{Q'}[a < a'] = 1/2`.

By Route B (probability-normalised FKG):
`probLT_Q[a < a'] ≥ probLT_{Q'}[a < a'] = 1/2`?

We need to check the direction. `Q' ⊋ Q` (Q' has the extra
`a < y` comparability). So `LE(Q') ⊆ LE(Q)`. The event
`{a < a'}` is *up-closed* in some sense...

In our counterexample: LE(Q) has 3 LEs (computed above). LE(Q')
requires `a < y` AND `a' < y`. From the table:
* (a, a', y): pos a = 0 < pos y = 2 ✓; pos a' = 1 < pos y = 2 ✓. Valid in Q'.
* (a', a, y): pos a = 1 < pos y = 2 ✓; pos a' = 0 < pos y = 2 ✓. Valid in Q'.
* (a', y, a): pos a = 2 < pos y = 1? ✗. NOT valid in Q'.

So LE(Q') = {(a, a', y), (a', a, y)}, 2 LEs. Of these, 1 has
`a < a'`. So `probLT_{Q'}[a < a'] = 1/2`.

`probLT_Q[a < a'] = 1/3`. So `1/3 ≥ 1/2`? **FALSE.**

**The Route B inequality fails in the wrong direction in this
counterexample.** Either:
* The probability-normalised cross-poset FKG goes the *other*
  direction (which is what `probLT'_count_div_le_of_relExt` gives
  in count form: `Pr_{Q'}[E] ≤ Pr_Q[E]`), OR
* The paper's argument relies on additional structural facts
  beyond what Route B gives.

Indeed, `Mathlib/RelationPoset/FKG.lean:521`'s
`probLT'_count_div_le_of_relExt` shows the count-form inequality
`Pr_{Q'}[E] ≤ Pr_Q[E]` (numerator-only divided by denominator of
Q). The probability-normalised form (mathematical content of
Route B) goes the same way: probabilities can only DECREASE under
augmentation, not increase. So Route B cannot prove
`1/2 ≤ probLT a a'`.

This is not a Route B defect — Route B is genuinely about
*decreasing* probabilities under augmentation. The paper's
argument is going from the symmetric Q' (probLT = 1/2) to
the asymmetric Q (probLT = 1/3 in the counterexample), and the
direction is `Pr_Q ≤ Pr_{Q'}`, not `Pr_Q ≥ Pr_{Q'}`.

So the paper's `Pr_Q ≥ 1/2` claim, if read literally as
`probLT a a' ≥ 1/2` in Lean's convention, is **wrong**. The paper
is actually proving `probLT a' a ≥ 1/2` (= `probLT a a' ≤ 1/2`),
which matches chain swap.

The Lean SubClaim's `pair` field as currently stated has the
**wrong direction** relative to what the paper actually proves.

---

## 5. What this means for downstream

* **mg-27c2's `case2Witness_balanced_under_FKG`** is not
  applicable on real inputs: `hFKG : Case2FKGSubClaim L` cannot
  be constructed for L's admitting strict chain pairs (the
  natural Case 2 setup), and providing an unsound axiom would
  break consistency.

* **mg-02c2's `bipartite_balanced_enum_general`** (the K=2
  closure consumer) has the same issue: it threads `hFKG`
  through to `case2Witness_balanced_under_FKG`. The Case 2 path
  inside `bipartite_balanced_enum_general` is unreachable on
  L's admitting strict chain pairs.

* **mg-5f0c's planned headline wiring** would consume `hFKG`
  (whether axiomatised or proved) and discharge the K=2 leaf via
  `bipartite_balanced_enum_general`. Same issue: cannot
  construct `hFKG`.

The compound-automorphism dispatch (mg-84f2 / mg-c0c7 / mg-02c2)
*does* handle the K=2 + irreducible + w≥1 + |β|≥3 regime in
Case 1 and Case 3 paths (no SubClaim needed); only Case 2 (the
within-band ⪯-comparable pair regime) routes through `hFKG`.

---

## 6. Pre-committed pivot options (PM-side)

Per mg-a79e's "Pre-committed next-round pivot (PM-side)" §:

> If THIS ticket block-and-reports because the proof requires a
> new axiom, PM evaluates:
> * (η₁) Accept the new axiom under audit-bar treatment ...
> * (η₂) Pivot to R3.0 (axiomatize Case2FKGSubClaim under
>   audit-bar) ...
> * (η₃) Pivot to R3.2 (extend compound-aut at K≥3) ...

This polecat's finding is **stronger than "needs a new axiom"**:
the SubClaim as currently stated is **provably false** on natural
inputs. So:

* **(η₁) and (η₂) — axiomatisation under audit-bar — would be
  UNSOUND.** Adding `axiom case2FKGSubClaim_axiom (L) :
  Case2FKGSubClaim L` would let the polecat (or any user) derive
  `False` from the §3 counterexample's
  `probLT a a' = 1/3 < 1/2`. PM should **NOT** pursue
  axiomatisation.

* **(η₃) — pivot to R3.2 (extend compound-aut at K≥3) — is
  viable** but doesn't help K=2 Case 2.

The newly visible options are:

* **(η₄) Restate the SubClaim with the correct direction.**
  Change `Case2FKGSubClaim.pair`'s conclusion from
  `1/2 ≤ probLT a a'` to `probLT a a' ≤ 1/2`. With the new
  direction, the SubClaim becomes equivalent to chain swap
  (`probLT_le_half_of_chain`), so it is *already a theorem* —
  no axiom or new infrastructure needed. BUT: the consumer
  proof (`strictCase2Witness_m2_balanced` and its callers) uses
  `1/2 ≤ probLT a a'` as the *lower* bound that, combined with
  chain swap's *upper* bound `≤ 1/2`, gives equality. With both
  bounds being `≤ 1/2`, no equality is forced and the consumer
  proof breaks. So the consumer would need to be redesigned —
  the obvious redesign is to take the reverse pair `(a', a)` as
  the balanced pair, with chain swap giving
  `probLT a' a = 1 - probLT a a' ≥ 1/2`. We then need an upper
  bound `probLT a' a ≤ 2/3` to get `(a', a) ∈ [1/2, 2/3] ⊆
  [1/3, 2/3]`. This upper bound is **not** chain swap (chain
  swap gives `≤ 1/2` from below); it is a separate argument
  (`Pr ≤ 2/3` from bipartite extremal enumeration,
  `Case2BipartiteBound.lean`'s `probLT_le_two_thirds_of_within_band_K2_w0`,
  but only proven for `w = 0`). For general `w ≥ 1`, the upper
  bound is the *paper's* bipartite extremal argument
  (`step8.tex:2916-2940`), which is part of A8-S2's deferred
  scope.

* **(η₅) Drop the SubClaim path entirely; keep `hC3` in the
  headline.** This is essentially v6 status's option (3) —
  return to option (δ) park. The compound-automorphism
  infrastructure (mg-84f2 / mg-c0c7 / mg-02c2) remains landed
  and useful for the K=2 leaves of Path C / Path B; the K=2
  Case 2 sub-case stays handled by leaving `hC3` as an explicit
  hypothesis (per the v5 / v6 framing).

* **(η₆) Wait for the full A8-S2-cont infrastructure
  (~2000-3500 LoC, multi-polecat session) before re-attempting.**
  This is the genuine path forward for an unconditional Case 2
  closure, but it is firmly out of single-polecat scope and
  should be a multi-polecat or Daniel-led milestone.

---

## 7. What this polecat lands

* **This status doc** (`docs/a8-path-b-block-and-report-status.md`).
* **No Lean changes.** No code modifications to `Case2Rotation.lean`,
  `BipartiteEnumGeneral.lean`, or any other file.
* **No new axioms, no `sorry` / `admit`.**
* **`#print axioms width3_one_third_two_thirds`** unchanged from
  baseline.

---

## 8. References

* **mg-a79e** (this ticket) — task body with R3.1 / Path B / hard
  block-and-report rule.
* `docs/a8-s2-rotation-residual-status.md` (mg-ba0c) — earlier
  identification of the chain-swap / FKG sub-claim direction
  mismatch (§3, "the chain hypothesis's direction forces
  probLT a₁ a₂ ≤ 1/2 ... the FKG sub-claim asserts
  probLT a₁ a₂ ≥ 1/2 ... so hFKG cannot be discharged from chain
  alone in the strict case").
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — earlier
  block-and-report on the StrictCase2 closure (§2-3 cover the
  same gap from a different angle).
* `docs/a8-s2-status.md` (mg-8801) — A8-S2 parent split (§3, §5
  document the cross-poset infrastructure layer's
  ~2000-3500 LoC estimate).
* `docs/a5-g3e-path-c-wiring-v6-status.md` (mg-5f0c) — v6 status
  with the planned 5-axiom target and its block-and-report
  (different gap: K≥3 leaves needing
  `case3Witness_hasBalancedPair_outOfScope` /
  `Lean.ofReduceBool`).
* `lean/OneThird/Step8/Case2Rotation.lean:629` —
  `probLT_le_half_of_chain` (chain swap, mg-ba0c).
* `lean/OneThird/Step8/Case2Rotation.lean:772` —
  `Case2FKGSubClaim` structure (mg-27c2).
* `lean/OneThird/Step8/Case2Rotation.lean:894` —
  `case2Witness_balanced_under_FKG` (mg-27c2).
* `lean/OneThird/Step8/BipartiteEnumGeneral.lean:210` —
  `bipartite_balanced_enum_general` (mg-02c2; consumes
  `Case2FKGSubClaim`).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:464` —
  `probLT'_mono_of_relExt` (count-form cross-poset
  monotonicity).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:407-426` —
  documented future work for probability-normalised cross-poset
  FKG (Route B's deliverable).
* `lean/AXIOMS.md` — `brightwell_sharp_centred` entry estimates
  500-800 LoC for the Brightwell-Kahn-Saks per-term covariance
  bound port (the Route B per-term ingredient).
* `step8.tex:2855-2875` — the paper's FKG sub-claim and its
  proof sketch.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (this
  docs-only commit does not change it).

---

## 9. Final state

* No code changes landed. The headline still carries `hC3`.
* This status doc is the deliverable: it records why the
  Route B proof cannot land *and* why the SubClaim's stated
  direction is mathematically wrong, surfaces the (η₄)/(η₅)
  pre-committed and newly-visible pivot options, and confirms
  that axiomatisation (η₁/η₂) would be UNSOUND.
* `pc-a79e` mailed mayor and pm-onethird with the verdict.
* `pc-a79e` did **not** call `mg done`; the work item remains
  claimed pending PM re-decision.
