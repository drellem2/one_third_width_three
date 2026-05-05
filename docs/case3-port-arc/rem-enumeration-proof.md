# `rem:enumeration` for Case 3 (out-of-scope) — latex-first proof writeup

**Work item:** `mg-75ef` (polecat `p75ef`).
**Branch:** `polecat-p75ef` (target `case3-port-arc`).
**Predecessor:** `mg-e850` (`docs/case3-port-arc/port-status.md`) —
Lean-side STOP on probability-normalised cross-poset FKG dependency.
This document is the latex-first follow-on per the
`feedback_latex_first_for_math_simp` discipline: produce a
paper-rigor proof (or honest sketch) of the math BEFORE re-attempting
a Lean port, so the math/Lean separation is correct.

**Subject.** `prop:in-situ-balanced` Case 3
(`step8.tex:3033-3047`), restricted to the residual parameter range
`¬ InCase3Scope` of the F5a `case3_certificate`. The paper's
argument for this regime is the `rem:enumeration` sketch
(`step8.tex:3157-3185`), which is genuinely a sketch, not a
fleshed-out proof.

**Format.** Markdown of latex-comparable rigor (the `feedback_latex_first_for_math_simp` directive
permits `.tex` or `.md`). All assertions are stated with explicit
hypotheses; informal language is flagged "Sketch" / "Outline" /
"Gap" so the reader can immediately tell rigor level.

---

## §1 Setup

Throughout, fix a layered width-3 poset
`Q = (X, ≤_Q)` with layered decomposition
`X = M_1 ⊔ M_2 ⊔ ⋯ ⊔ M_K` of interaction width `w` and depth `K`,
satisfying axioms (L1)–(L4) of `step8.tex` Definition
`def:layered`:

* **(L1)** Each band `M_i` has `|M_i| ≤ 3` and is an antichain in
  `Q`.
* **(L2)** If `x ∈ M_i, y ∈ M_j` with `i < j − w`, then `x <_Q y`
  (far-apart bands are forced ordered).
* **(L3)** If `|i − j| > w`, then `x` and `y` are comparable.
* **(L4)** If `i < j` and `(x, y) ∈ M_i × M_j` is a comparable pair,
  then `x <_Q y` (band index is compatible with the order whenever
  comparability exists).

We work under the AXIOM hypotheses
(`lean/AXIOMS.md:226-454`):

* `hWidth3` — `Q` has width `≤ 3` (Dilworth).
* `hIrr` — layer-ordinal-sum irreducibility: no band-prefix
  `[1, k]` is below `[k+1, K]` uniformly.
* `hK3` — `K ≥ 3`.
* `hw` — `w ≥ 1`.
* `hCard` — `|X| ≤ 6w + 6` (the F5 C2 leaf cap; the paper uses the
  weaker `|X| ≤ 3(3w+1) = 9w + 3`, the Lean tighter cap subsumes
  the paper's for `w ≥ 1`).
* `hDepth` — `K ≤ 2w + 2`.
* `hScope` — `¬ InCase3Scope w |X| K`, where
  `InCase3Scope w c K := K = 3 ∧ 1 ≤ w ≤ 4 ∧ (w = 1 → c ≤ 9) ∧
   (2 ≤ w → c ≤ 7)`. So the parameter range covered by this writeup
  is `K ∈ [3, 2w+2]` MINUS the small-`K=3` cap window already
  discharged by `case3_certificate`.
* `hC3` — `Case3Witness L`, defined as
  `¬ Case1 ∧ ¬ Case2Witness L` where:
  * **Case 1.** `∃ a ≠ a' in same band with full ambient profile
    match`, i.e. `Π(a) = Π(a')` in `Q` (the swap involution gives
    `Pr[a <_L a'] = 1/2`).
  * **Case 2.** `∃ a ≠ a' in same band with ⪯-comparable two-sided
    profile`, i.e. `Π(a) ⪯ Π(a')` (one of `Π(a) ⪯ Π(a')` or
    `Π(a') ⪯ Π(a)` holds, where `⪯` is the order
    `Π(a) ⪯ Π(a') ⟺ Π⁺(a) ⊇ Π⁺(a') ∧ Π⁻(a) ⊆ Π⁻(a')`).

  Hence `Case3Witness L` is the complement: every band fails both.

We write `LE(Q)` for the set of linear extensions of `Q`,
`Pr_Q[E] := |{L ∈ LE(Q) : E(L)}| / |LE(Q)|` for the uniform
probability of an event `E`, and

```
Π⁺(a) := { z ∈ X : a <_Q z },     Π⁻(a) := { z ∈ X : z <_Q a }
Π(a)  := (Π⁺(a), Π⁻(a))
```

for the two-sided profile of `a`.

A pair `(a, a') ∈ X × X` with `a ⊥_Q a'` (incomparable) is
**balanced** if `Pr_Q[a <_L a'] ∈ [1/3, 2/3]`. The conclusion the
axiom asserts is `HasBalancedPair Q := ∃ (a, a') incomparable in Q,
Pr_Q[a <_L a'] ∈ [1/3, 2/3]`.

**Convention.** We prove `HasBalancedPair Q` *by contradiction*:
assume **(NBP)** "no balanced pair exists" — every incomparable pair
`(a, a')` has `Pr_Q[a <_L a'] ∉ [1/3, 2/3]`, hence either
`Pr_Q[a <_L a'] > 2/3` or `Pr_Q[a <_L a'] < 1/3`. The argument
derives a contradiction from (NBP) ∧ Case 3 hypothesis.

---

## §2 Orientation lemma (no-balanced-pair counterfactual)

This section records a foundational lemma (the "rotation /
3-cycle-forbidden" argument from `step8.tex:2917-2929`, here used
in its general form rather than only as the Case 2 closure step).
It dramatically restricts the structural patterns that need
analysis in Case 3.

**Definition (majority orientation).** Assume (NBP). For
`a, a' ∈ X` incomparable in `Q`, write `a ≪ a'` if
`Pr_Q[a <_L a'] > 2/3`. Under (NBP) every incomparable pair
satisfies exactly one of `a ≪ a'` or `a' ≪ a` (since the probability
must lie outside `[1/3, 2/3]`).

**Lemma 2.1 (Linear orientation on 3-antichains; user input
2026-05-06).** *Under (NBP), for any 3-element antichain
`{a, b, c} ⊆ X` (pairwise incomparable in `Q`), the orientation
`≪` restricted to `{a, b, c}` is a linear order. Equivalently,
`≪` is acyclic on every 3-antichain.*

**Proof.** Suppose for contradiction that `≪` cycles on
`{a, b, c}`: `a ≪ b ≪ c ≪ a`. Then each of
`Pr_Q[a <_L b], Pr_Q[b <_L c], Pr_Q[c <_L a]` exceeds `2/3`.
Equivalently the complementary probabilities satisfy
`Pr_Q[b <_L a], Pr_Q[c <_L b], Pr_Q[a <_L c] < 1/3`.

By the union bound,
```
Pr_Q[a <_L b ∧ b <_L c ∧ c <_L a]
   ≥ 1 − Pr_Q[b <_L a] − Pr_Q[c <_L b] − Pr_Q[a <_L c]
   > 1 − 1/3 − 1/3 − 1/3 = 0.
```
But the event `a <_L b ∧ b <_L c ∧ c <_L a` is empty: it would
require a 3-cycle in the linear order `<_L`, which is impossible
in any total order. Hence the displayed probability equals `0`,
contradicting `> 0`. ∎

**Remark 2.2 (paper provenance).** This is exactly the "three
rotations cover every total order" identity the paper records in
parenthetical at `step8.tex:2920-2929`:
> *the three "rotations" are the events `{a_2<_L a_1}`,
> `{a_3<_L a_2}`, `{a_1<_L a_3}`, and they cover every total order
> on `{a_1, a_2, a_3}` … if all three failed simultaneously we
> would have a 3-cycle forbidden for a total order. Hence
> `Pr[a_2<_L a_1] + Pr[a_3<_L a_2] + Pr[a_1<_L a_3] ≥ 1`.*

The paper invokes the identity inside the bipartite Case 2
discharge to extract a balanced pair from a *linear* `⪯`-chain of
sub-claim lower bounds. Lemma 2.1 invokes the same identity in
contrapositive form: under (NBP), no cyclic majority on a
3-antichain.

**Corollary 2.3 (WLOG linear majority on `{a_1, a_2, a_3}`).**
*In particular for any 3-antichain `{a_1, a_2, a_3} ⊆ M_k` of the
Case 3 setup, after relabeling we have `a_1 ≪ a_2 ≪ a_3` (and
hence by transitivity of `≪` on this set, also `a_1 ≪ a_3`). In
probabilistic terms:*
```
Pr_Q[a_1 <_L a_2] > 2/3,   Pr_Q[a_2 <_L a_3] > 2/3,
Pr_Q[a_1 <_L a_3] > 2/3.
```

**Remark 2.4 (cyclic-symmetric configurations are excluded).** A
naive reading of the AXIOMS Step 1 ("two of the three elements
agree on at least one coordinate") would seem to fail on
3-cycle-symmetric configurations: for `w = 1` one can construct
a layered poset
`Q` with `M_2 = {a_1, a_2, a_3}` whose two-sided profiles satisfy
`Π⁺(a_i) = {x_i}, Π⁻(a_i) = {y_j, y_k} (j, k ≠ i)`, all pairwise
distinct, all pairwise `⪯`-incomparable, all pairwise
`⊆`-incomparable on each coordinate. Such a `Q` admits the cyclic
poset automorphism `σ = (a_1 a_2 a_3)(x_1 x_2 x_3)(y_1 y_2 y_3)`,
which forces `Pr_Q[a_1 <_L a_2] = Pr_Q[a_2 <_L a_3] = Pr_Q[a_3 <_L
a_1] = 1/2` (sum is `3/2` by the rotation identity, equal by
σ-equivariance). So `(a_1, a_2)` is balanced.

Lemma 2.1 RULES OUT this configuration from the proof's territory:
the AXIOM is proven by contradiction from (NBP), and (NBP) FAILS
in the cyclic configuration (since `Pr = 1/2 ∈ [1/3, 2/3]` already
yields a balanced pair). So Step 1 of the AXIOMS-as-stated needs
no cyclic-case repair; the proof simply does not visit such
configurations. This was the resolution of the polecat's in-progress
candidate counterexample.

---

## §3 Step 1 — Forced one-sided coordinate alignment

Now operate under (NBP) ∧ Case 3 ∧ Corollary 2.3
(`a_1 ≪ a_2 ≪ a_3` linear majority).

The AXIOMS-stated Step 1 was: *two of `{a_1, a_2, a_3}` share
(equal) at least one coordinate of the two-sided profile.* Below we
state and prove a **revised Step 1** that fits the linear-majority
regime; the revised statement is what Step 2 actually consumes.

### §3.1 Revised statement

**Definition 3.1 (one-sided alignment).** A pair
`(a, a') ∈ M_k × M_k` is **upper-aligned** if
`Π⁺(a) ⊆ Π⁺(a')` (equivalently `Π⁺(a') ⊇ Π⁺(a)`); it is
**lower-aligned** if `Π⁻(a) ⊇ Π⁻(a')`. It is **one-sided
aligned** if it is upper-aligned OR lower-aligned.

(Note: under the Lean `Case2Witness` definition,
`a' < a` in the `⪯` sense iff `(a', a)` is BOTH upper-aligned and
lower-aligned. Case 3 = no pair is both-aligned.)

**Step 1 (revised).** *Under (NBP) ∧ Case 3 ∧ linear majority
`a_1 ≪ a_2 ≪ a_3`, there exist distinct `i, j ∈ {1, 2, 3}` such
that `(a_i, a_j)` is one-sided aligned (upper-aligned with
`Π⁺(a_i) ⊆ Π⁺(a_j)` OR lower-aligned with `Π⁻(a_j) ⊆ Π⁻(a_i)`).*

The original AXIOMS Step 1 ("share a coordinate", i.e. ⊆-equal) is
the strict-equality specialisation; the revised statement is the
weakening that includes proper ⊆.

### §3.2 Sketch / status of the revised Step 1

**Claim 3.2 (sketch — not fully discharged).** *Under the
hypotheses of Step 1 (revised), the existence of a one-sided
aligned pair is forced.*

**Outline.** The intuition is that the linear majority order
`a_1 ≪ a_2 ≪ a_3` reflects an asymmetry in the poset, and the
asymmetry must come from at least ONE coordinate being aligned in
the favoured direction.

Consider the pair `(a_1, a_3)` with `Pr_Q[a_1 <_L a_3] > 2/3`. By
the (FKG-coupling-style) **bipartite-Case-2 contrapositive** (cf.
`step8.tex:2840-2871`):
* if `(a_1, a_3)` were upper-aligned `Π⁺(a_1) ⊆ Π⁺(a_3)` AND
  lower-aligned `Π⁻(a_3) ⊆ Π⁻(a_1)`, then it would be `⪯`-aligned
  (Case 2), contradicting `Case3Witness L`. So **at most one
  alignment direction holds** for `(a_1, a_3)`.
* Conversely, the linear majority `a_1 ≪ a_3` forces ASYMMETRY:
  the "a_1-favouring" pull in `Q` (extra forcing on `a_1` to come
  early, or extra forcing on `a_3` to come late) must dominate
  the "a_3-favouring" pull. Since Case 3 incomparability allows
  asymmetry in BOTH directions per coordinate (Π⁺ has both
  Π⁺(a_1)\Π⁺(a_3) and Π⁺(a_3)\Π⁺(a_1) potentially non-empty), the
  net asymmetry can come from either coordinate alone or both
  together.

The **revised-Step-1 conjecture** is that under (NBP) ∧ Case 3 ∧
hC3 (`¬ Case2Witness L` in EVERY band, not just `M_k`) ∧ width-3
(no auxiliary 4-antichains) ∧ irreducibility, the per-coordinate
asymmetries cannot all be "balanced two-sided incomparable" for
all three pairs simultaneously. At least one of the three pairs
`(a_i, a_j)` must be one-sided aligned.

**Status.** The polecat could not close Claim 3.2 to paper rigor
within the token budget. The blocking sub-issue is constructive:
attempts to construct a counterexample (a Case 3 antichain with
linear majority but no one-sided aligned pair, all auxiliary bands
satisfying ¬ Case 2 witness, total width 3) repeatedly produced
configurations that violated `width-3` (introducing a 4-antichain
between the constructed antichain and a transversal upper/lower
band) or violated `¬ Case2Witness L` in some other band (the
asymmetric Π⁻ profile in `M_k` typically forces an aligned pair in
`M_{k-1}` via the symmetric-profile-of-the-`y_i`'s argument).

This is consistent with — but does NOT prove — Claim 3.2. The full
proof requires either:

* (a) A direct combinatorial argument bounding the joint
  configuration of `(Π⁺_var(a_i), Π⁻_var(a_i))_{i=1,2,3}` under
  width-3 + ¬Case2Witness-everywhere + linear-majority. This is
  finite finite parameter range (per `hCard ≤ 6w+6` and
  `hDepth ≤ 2w+2`) and could in principle be enumerated.
* (b) An indirect argument via the FKG-coupling that bounds
  `Pr_Q[a_1 <_L a_3]` from above by some
  function of the "per-coordinate asymmetry sizes" and shows it
  must drop below `2/3` whenever no alignment exists,
  contradicting linear majority.

Both routes are non-trivial. **This is the FIRST GAP** in the
sketch's "routine combinatorics" framing: even with the
orientation lemma simplification, Step 1 is more than
straightforward pigeonhole.

### §3.3 What goes through on a tight reading

What CAN be proven rigorously under (NBP) ∧ linear majority:

**Lemma 3.3 (per-coordinate asymmetries cannot both vanish).**
*For each pair `(a_i, a_j)` with `a_i ≪ a_j`, we have*
```
Π⁺(a_j) \ Π⁺(a_i) ≠ ∅  OR  Π⁻(a_i) \ Π⁻(a_j) ≠ ∅.
```
*(I.e., either some `b ∈ Π⁺(a_j) \ Π⁺(a_i)` pulls `a_j` early
relative to `a_i`, or some `b' ∈ Π⁻(a_i) \ Π⁻(a_j)` pushes `a_i`
late relative to `a_j` — at least one such asymmetry favouring
`a_j` exists.)*

**Proof.** Both `Π⁺(a_j) \ Π⁺(a_i) = ∅` AND `Π⁻(a_i) \ Π⁻(a_j) =
∅` would give `Π⁺(a_j) ⊆ Π⁺(a_i)` AND `Π⁻(a_i) ⊆ Π⁻(a_j)`,
i.e. `Π(a_i) ⪯ Π(a_j)` (upper-direction `Π⁺(a_i) ⊇ Π⁺(a_j)` ✓ and
lower-direction `Π⁻(a_i) ⊆ Π⁻(a_j)` ✓). This contradicts Case 3
(pairwise `⪯`-incomparable). ∎

But Lemma 3.3 is *one direction only*. Under Case 3, the
per-coordinate asymmetries also exist in the OPPOSITE direction
(`a_i`-favouring): some `b'' ∈ Π⁺(a_i) \ Π⁺(a_j)` exists, OR some
`b''' ∈ Π⁻(a_j) \ Π⁻(a_i)`, by the dual of Lemma 3.3 applied to
`a_j ≪ a_i` direction (which is `a_i`-direction since `a_i ≪
a_j`). Wait — under linear majority `a_i ≪ a_j` we have `a_j ≪̸
a_i`, so the dual of Lemma 3.3 doesn't fire immediately. Let me
recompute:

`Π(a_j) ⪯ Π(a_i)` would require `Π⁺(a_j) ⊇ Π⁺(a_i)` AND
`Π⁻(a_j) ⊆ Π⁻(a_i)`. Case 3 fails this: NOT `(Π⁺(a_j) ⊇ Π⁺(a_i)
AND Π⁻(a_j) ⊆ Π⁻(a_i))`. So either `Π⁺(a_j) ⊉ Π⁺(a_i)` (some
`b'' ∈ Π⁺(a_i) \ Π⁺(a_j)`) OR `Π⁻(a_j) ⊄ Π⁻(a_i)` (some `b''' ∈
Π⁻(a_j) \ Π⁻(a_i)`).

Combined with Lemma 3.3, FOUR per-coordinate asymmetries are
present in Case 3 (one of two `a_j`-favouring + one of two
`a_i`-favouring per pair). The linear majority `a_i ≪ a_j` says
the `a_j`-favouring asymmetries dominate (in the Pr ≥ 2/3 sense).

But "dominate in Pr" does not automatically translate to a
specific structural fact like "Π⁺(a_i) ⊆ Π⁺(a_j)". The translation
requires probability-FKG (positive correlation) to bound the
contributions.

So the rigorous part of Step 1 stops at Lemma 3.3; the bridge to
"one-sided aligned pair exists" is the gap.

---

## §4 Step 2 — Band-restricted FKG sub-coupling

Assume the revised Step 1 holds (one-sided aligned pair exists):
WLOG `(a_1, a_2)` is upper-aligned, `Π⁺(a_1) ⊆ Π⁺(a_2)`. We now
analyse the "band-restricted Case 2" discharge.

### §4.1 The sub-context

Let `Q^+ := Q[M_k ∪ M_{k+1} ∪ ⋯ ∪ M_K]` be the upper sub-poset
(the antichain band `M_k` plus everything strictly above it). The
restriction inherits the layered axioms (L1)–(L4) with the same
interaction width `w`, depth `K − k + 1`, and `M_k` becomes the
**bottom band** of `Q^+`.

In `Q^+`:
* `Π⁻_{Q^+}(a_i) = ∅` for all `a_i ∈ M_k` (no elements below the
  bottom band).
* `Π⁺_{Q^+}(a_i) = Π⁺(a_i)` (since `Π⁺(a_i) ⊂ M_{>k}` by L4, the
  upper profile is entirely inside `Q^+`).

So the `⪯_{Q^+}` order on `{a_1, a_2, a_3}` reduces to inclusion
on the `Π⁺` coordinate: `Π_{Q^+}(a) ⪯ Π_{Q^+}(a')` iff
`Π⁺(a) ⊇ Π⁺(a')`.

Under our Step 1 hypothesis `Π⁺(a_1) ⊆ Π⁺(a_2)`: the pair `(a_2,
a_1)` satisfies `Π_{Q^+}(a_2) ⪯ Π_{Q^+}(a_1)` in `Q^+` (sometimes
strict, sometimes equal). So in `Q^+`:

* If `Π⁺(a_1) = Π⁺(a_2)` strictly: `(a_1, a_2)` is a Case 1
  symmetric pair in `Q^+` (full `Π_{Q^+}` match), and the swap
  involution `(a_1 ↔ a_2)` is a poset automorphism of `Q^+`.
  Hence `Pr_{Q^+}[a_1 <_L a_2] = 1/2`.
* If `Π⁺(a_1) ⊊ Π⁺(a_2)` strictly: `(a_2, a_1)` is a Case 2
  `⪯`-aligned pair in `Q^+`, and by the bipartite-FKG sub-claim
  `Pr_{Q^+}[a_2 <_L a_1] ≥ 1/2`.

In either sub-case we obtain a useful bound IN `Q^+`:
`Pr_{Q^+}[a_1 <_L a_2] ≤ 1/2`.

### §4.2 The lift problem

The contradiction we want from (NBP) ∧ linear majority requires a
bound on `Pr_Q` (not `Pr_{Q^+}`). Specifically, from
`a_1 ≪ a_2`, `Pr_Q[a_1 <_L a_2] > 2/3`. We have a sub-context
bound `Pr_{Q^+}[a_1 <_L a_2] ≤ 1/2`. The **lift problem** is to
extract from these two facts a contradiction.

The natural attempted lift: "Pr_Q ≈ Pr_{Q^+} up to a small slack",
or equivalently a comparison inequality
`Pr_Q[a_1 <_L a_2] ≤ Pr_{Q^+}[a_1 <_L a_2] + ε` with `ε`
controlled by the strictly-below part of `Q`. If `ε < 1/6`, then
`Pr_Q[a_1 <_L a_2] ≤ 1/2 + 1/6 = 2/3`, contradicting `> 2/3`. □

### §4.3 The lift requires probability-normalised FKG

The lift is a **cross-poset comparison** between `Pr_Q` and
`Pr_{Q^+}`, where `Q^+` is a sub-poset of `Q` (taking only the
upper bands) and `Q` augments `Q^+` with the strictly-below bands
plus their cross-comparabilities to `M_k ∪ above`.

By the L4 direction-axiom and the L3 forced-comparability, every
`x ∈ M_j` for `j < k` is below or incomparable to every element of
`M_k ∪ above` in `Q`; lower-far elements (`j < k − w`) are
*forced* below by L2 and contribute nothing to the relative-order
distribution of `(a_1, a_2)`. Lower-near elements
(`j ∈ [k−w, k−1]`) are *variable*: each `b ∈ M_{k−w} ∪ ⋯ ∪
M_{k−1}` may be in `Π⁻(a_1)` and/or `Π⁻(a_2)` (and/or in
`Π⁻(a')` for any `a' ∈ M_k ∪ above bands`).

### §4.4 Why count-form FKG is insufficient

The in-tree count-form primitives (`lean/OneThird/Mathlib/RelationPoset/FKG.lean:381,464,521`):

* `sum_initialIdeal'_le_of_subseteq` — for `Q ⊆ Q'` (more
  comparabilities), absolute count of LE's satisfying any
  level-`k` event drops monotonically.
* `probLT'_mono_of_relExt` — derived restricted-numerator: smaller
  count over LARGER denominator.
* `probLT'_count_div_le_of_relExt` — direct corollary; same
  denominator pathology.

The lift we need in §4.2 is a *probability-normalised*
cross-poset comparison `Pr_Q[a_1 <_L a_2] ≤ Pr_{Q^+}[a_1 <_L a_2]
+ ε` (or its variants involving conditional expectations over
strictly-lower Brownian-bridge-style restrictions). This requires
**FKG positive correlation** between the event `{a_1 <_L a_2}`
(level-`k`-style event in the LE lattice) and the event `{L
respects the new comparabilities adding strictly-lower elements}`
in the `LE(Q^+)` lattice — equivalently, the standard
Daykin–Saks-style "drops" inequality between two genuine averages.

The in-tree count-form primitive `probLT'_mono_of_relExt` is
explicitly documented as the restricted-numerator weaker form
(`RelationPoset/FKG.lean:506-516` docstring):

> Strictly speaking, the displayed inequality compares the
> *restricted-numerator* probability — i.e. dividing the smaller
> count by the *larger* (`Q`-side) denominator `numLinExt' Q` —
> and is therefore weaker than the standard Daykin–Saks "drops"
> inequality between the two genuine averages. **The standard form
> requires FKG positive correlation between the `S`-event and the
> "`L` respects new `Q'`-comparabilities" event in the
> `LinearExt' Q` lattice, recorded as a follow-up in
> `docs/a8-s2-status.md`.**

The probability-normalised primitive is the named A8-S2-cont
infrastructure (`docs/a8-s2-status.md:159, 269, 391-409`),
estimated at ~2000–3500 LoC and not currently in tree.

### §4.5 Could a count-form workaround close the lift?

**Attempted workaround.** Define `Q_low` to be `Q` with all
lower-near comparabilities `b < a_i` removed for `b ∈ M_{<k}`,
`a_i ∈ M_k`. Then `Q_low ⊆ Q`. By count-form FKG monotonicity
(`sum_initialIdeal'_le_of_subseteq`), the count of LE's of `Q`
satisfying `a_1 <_L a_2` is bounded by the count in `Q_low`. But
the DENOMINATORS differ by exactly the "lower-near comparability
restriction factor", and the ratio depends on the specific
configuration of `Π⁻_var` for `(a_1, a_2)` AND for ALL OTHER
elements above `M_k`. The count-form bound is sharp on
numerators but vacuous on the ratio — reproducing the
denominator-pathology mg-e850's port-status §3.2-3.4 diagnosed.

**Direct probability bound.** A second attempt: for each fixed
linear order `σ` on `M_{<k}` (a LE of the strictly-lower part),
condition on `σ` and bound `Pr_Q[a_1 <_L a_2 | σ]` from above by
`Pr_{Q^+}[a_1 <_L a_2]`. Marginalising over `σ` would then give
`Pr_Q[a_1 <_L a_2] ≤ Pr_{Q^+}[a_1 <_L a_2]`. The conditional
bound, however, is exactly the FKG positive-correlation between
`{a_1 <_L a_2}` and `{L respects σ}` in `LE(Q')` for an
intermediate `Q'`. This is the same FKG primitive — the
conditioning rephrases but does not eliminate the
positive-correlation requirement.

**Symmetry-tight workaround?** A third attempt: when `(a_1, a_2)`
share `Π⁺` exactly in `Q^+` (the swap-involution branch of §4.1),
the involution `(a_1 ↔ a_2)` is an auto of `Q^+` but NOT of `Q`.
In `Q`, the involution lifts only when *also* `Π⁻(a_1) = Π⁻(a_2)`
in `Q`, which would be `Case 1` in the FULL `Q` — excluded by
`hC3`. So no swap-involution lift in this branch either.

**Verdict on the workarounds.** No count-form variant we can see
closes the lift. The probability-normalised cross-poset FKG (the
A8-S2-cont scope) is genuinely needed.

---

## §5 Step 3 — Reduction back to Case 1 / Case 2

This step is conditional on §4 closing.

If §4 closed (we had `Pr_Q[a_1 <_L a_2] ≤ 2/3`, and the orientation
sub-claim via the FKG sub-context gives `Pr_Q[a_1 <_L a_2] ≥ 1/2`
with the probability-normalised FKG monotonicity transferred to
the FULL `Q`), then `(a_1, a_2)` would be a balanced pair in `Q`,
contradicting (NBP). Discharge complete.

The reduction from `(a_1, a_2)` to a Case 1 or Case 2 pair in the
formal sense (via mg-f92d's `hasBalancedPair_of_ambient_profile_match`
or the A8-S2 `Case2Witness` discharge) is then a routine bookkeeping
step: Case 1 form when `Π⁺(a_1) = Π⁺(a_2)` holds AND the lift
preserves the symmetry; Case 2 form (via A8-S2's
`Case2Witness L → HasBalancedPair α`) when `Π⁺(a_1) ⊊ Π⁺(a_2)`
strictly. Both consumers exist in tree (`mg-f92d`, `mg-8801`) and
plug directly once §4 produces the witness.

This step inherits the §4 block. Conditional on §4, it adds at
most ~50–100 LoC of plumbing.

---

## §6 Composition — full `case3_outOfScope` theorem statement

Combining §§3–5 produces the discharge of:

```
Theorem (Case 3 residual; would-be replacement of axiom).
  Let Q be a layered width-3 poset with layered decomposition L
  satisfying:
    hWidth3, hIrr, hK3 (K ≥ 3), hw (w ≥ 1),
    hCard (|X| ≤ 6w + 6), hDepth (K ≤ 2w + 2),
    hScope (¬ InCase3Scope w |X| K),
    hC3 (Case3Witness L).
  Then Q admits a balanced pair, i.e. ∃ (a, a') incomparable in Q
  with Pr_Q[a <_L a'] ∈ [1/3, 2/3].
```

Conditional discharge: under §3 (revised Step 1) ∧ §4 (FKG
sub-coupling) ∧ §5 (reduction). All three steps are
reduced-to-conditionally-rigorous in this writeup; the
unconditional rigor depends on the §3 gap (Claim 3.2) and the §4
FKG infrastructure.

---

## §7 Verdict on the load-bearing question (α / β)

The polecat brief frames the load-bearing question as:

> Does the math actually require probability-normalised FKG?
> Or does count-form FKG (already in tree) suffice when the
> "sub-context" structure is properly exploited?

**Verdict:** **β — the math needs probability-normalised FKG.**

**Evidence.** Three independent lines of analysis (§4.4, §4.5,
plus mg-e850's prior in-tree-primitives audit) converge on the
same conclusion:

1. **§4.4 first-principles.** The lift step
   `Pr_{Q^+}[a_1 <_L a_2] ≤ 1/2` ⇒
   `Pr_Q[a_1 <_L a_2] ≤ 2/3` is a cross-poset comparison whose
   correct form is Daykin–Saks "drops" — i.e. probability-FKG
   positive correlation between an event and an
   "L-respects-augmenting-edges" event, in the LE-lattice of an
   intermediate poset. The orientation-lemma simplification of
   §2 does not change this requirement — it only removes the
   symmetric-cyclic case from consideration upstream of §4.

2. **§4.5 workaround attempts.** Three structurally different
   workarounds (count-form ratio, conditional-on-lower
   marginalisation, symmetry-tight involution lift) all reduce
   back to the same FKG positive-correlation step. No genuinely
   count-form route closes the lift.

3. **mg-e850 in-tree audit** (`docs/case3-port-arc/port-status.md
   §3.2-3.4`). The in-tree count-form primitives (`sum_initialIdeal'_le_of_subseteq`,
   `probLT'_mono_of_relExt`, `probLT'_count_div_le_of_relExt`)
   give absolute-monotonicity and restricted-numerator forms only;
   the file's own docstrings flag the probability-normalised form
   as the deferred A8-S2-cont follow-up.

The mg-e850 polecat reached verdict β by analysing the in-tree
primitives. This writeup reaches the same verdict β by analysing
the math directly. The two analyses corroborate each other.

**Caveat.** This verdict is **conditional on §3 (revised Step 1)
closing**. If §3's Claim 3.2 is FALSE (i.e., a Case 3 antichain
under linear majority can avoid having any one-sided aligned pair
while satisfying width-3 + ¬Case2Witness-everywhere), then the
sketch's discharge mechanism fails outright and a more sophisticated
argument is needed. The polecat could not close §3 to paper rigor.

**Secondary finding (orientation-lemma simplification).** The
user's input (2026-05-06) of the orientation lemma (§2) is a
substantive contribution: it removes the cyclic-symmetric
configurations (which would otherwise be a real obstacle to Step
1) from the proof's territory. The remaining configurations under
linear-majority orientation may still be hard, but the simpler
class has more structure.

---

## §8 Recommended Lean port shape (under verdict β)

Per the brief, "If (β): explain why probability-normalised FKG is
genuinely needed."

**Position.** The case3 out-of-scope axiom port is **genuinely
A8-S2-cont-dependent**. This corroborates mg-e850's stop verdict
at the math level.

**Sketch of Lean port LoC, conditional on A8-S2-cont landing.**

1. **A8-S2-cont — probability-normalised cross-poset FKG.**
   Pre-requisite. Estimated ~2000–3500 LoC per `docs/a8-s2-status.md:159`.
   Provides the headline lemma `Pr_{Q'}[S] ≤ Pr_Q[S]` (or the
   appropriate sign) for `Q ⊆ Q'`-augmented and a downward-closed
   level-`k` event `S`. Out of scope of this ticket, would be a
   separate multi-week multi-polecat arc.

2. **Step 1 (revised) — Lemma 3.3 + Claim 3.2.** A combinatorial
   lemma deriving the one-sided aligned pair from
   linear-majority + Case 3 + width-3 + ¬Case2Witness-everywhere.
   Estimated ~150–300 LoC if Claim 3.2 admits a structural proof;
   substantially more if it requires bounded enumeration on the
   parameter range `w ∈ {1,2,3,4}`, `K ∈ [3, 2w+2]`, `|X| ≤ 6w+6`.

3. **Step 2 — band-restricted FKG sub-coupling lemma.**
   Specialise A8-S2-cont's headline to the sub-poset
   `Q^+ := Q[M_k ∪ above]` with the bipartite-Case-2 sub-claim
   applied in `Q^+`. Estimated ~200–400 LoC after A8-S2-cont
   lands.

4. **Step 3 — reduction.** Compose with `mg-f92d`'s
   `hasBalancedPair_of_ambient_profile_match` (Case 1 ambient form)
   and A8-S2's `Case2Witness`-discharge. Estimated ~50–100 LoC.

5. **Orientation lemma (Lemma 2.1).** Standalone fact, depends only
   on the "rotation cover" identity. Estimated ~30–50 LoC.

**Total conditional bundle (steps 2–5): ~430–850 LoC** assuming
A8-S2-cont as a prerequisite. **Total including A8-S2-cont:
~2430–4350 LoC**.

This matches mg-e850's port-status §6 estimate (~2000–3500 LoC for
A8-S2-cont + ~200–450 LoC for the case-3-specific work) at the
math-derived level.

**Three Daniel-only options surface** (per brief outcome class for
verdict β):

1. **Commission A8-S2-cont arc.** Multi-week multi-polecat
   infrastructure. Once it lands, the case3 port becomes
   ~430–850 LoC. The orientation-lemma simplification (§2)
   reduces the per-step complexity meaningfully.
2. **Defer port indefinitely; accept axiom on forum-post
   disclosure.** The headline trust surface
   `[propext, Classical.choice, Quot.sound, brightwell_sharp_centred,
   case3Witness_hasBalancedPair_outOfScope, _native.native_decide]`
   (`lean/PRINT_AXIOMS_OUTPUT.txt`) is publishable as-is per
   `docs/case3-port-arc/port-status.md §8`. The disclosure now has
   a stronger factual basis — the AXIOMS.md "replacement path
   (open)" can cite this latex artifact as evidence that the
   axiom's gap is genuinely the probability-normalised
   cross-poset FKG, not a polecat-tractable gap.
3. **Investigate alternative proof structures** — e.g., is there a
   different attack on `prop:in-situ-balanced` Case 3 that avoids
   probability-normalised FKG entirely (perhaps via
   bounded-enumeration on the residual parameter range, since the
   range is finite per `hCard` and `hDepth`)? Would require its
   own scoping pass.

---

## §9 Cross-references

* **Paper.** `step8.tex:3033-3047` (`prop:in-situ-balanced` Case 3
  statement); `step8.tex:3157-3185` (`rem:enumeration` sketch);
  `step8.tex:2920-2929` (rotation identity used in §2 orientation
  lemma); `step8.tex:2840-2871` (bipartite Case 2 FKG sub-claim);
  `step8.tex:1888-1912` (`def:layered` (L1)–(L4)).

* **Lean tree.** `lean/OneThird/Step8/Case3Residual.lean:208`
  (axiom declaration);
  `lean/OneThird/Step8/Case3Dispatch.lean:156-180` (`Case2Witness`,
  `Case3Witness` definitions); `lean/AXIOMS.md:226-454` (axiom
  disclosure that this writeup investigates);
  `lean/OneThird/Mathlib/RelationPoset/FKG.lean:381,464,521`
  (in-tree count-form FKG primitives that §4.4-4.5 find
  insufficient); `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1484`
  (`InCase3Scope` definition).

* **Predecessor / mg-trail.** `mg-e850`
  (`docs/case3-port-arc/port-status.md`) — the Lean-side STOP
  whose math-side cause this ticket investigates;
  `docs/a8-s2-status.md:269` (A8-S2-cont scope);
  `docs/why-hC3-is-structural.md §2` (F2: K=2 sibling diagnosis with
  the same probability-normalisation gap).

* **Feedback / discipline.** `feedback_latex_first_for_math_simp`
  (Daniel 2026-05-02) — the discipline this ticket follows;
  `feedback_complexity_blowup_means_wrong_path` — trip-wires;
  `feedback_audit_as_deliverable` — applies (the latex artifact
  IS the value regardless of α/β).

* **In-session inputs.** Daniel directive 2026-05-05T~23:50Z
  (the latex-first re-scoping); user input 2026-05-06 (the
  orientation lemma of §2.1) — the substantive simplification that
  excludes cyclic-symmetric configurations from the proof's
  territory.

---

## §10 Polecat protocol notes

* `mg claim mg-75ef` — done.
* `pogo schedule … mail-check-mg-75ef` — done.
* No Lean source changes — this is a docs-only ticket per
  `feedback_distinguish_arc_chunk_outcomes` ("substantive math
  chunk; no parallel cleanup").
* This `.md` deliverable — done (the value regardless of α/β
  per `feedback_audit_as_deliverable`).
* Verdict β reached at math level, corroborating mg-e850's
  Lean-level β.
* No trip-wires fired (after the orientation lemma of §2.1 was
  incorporated): trip-wire #2 was a near-miss on a stale "Step 1 as
  stated literally" reading; the orientation simplification
  changed §3 from "FALSE on natural inputs" to "rigorous up to
  Lemma 3.3, sketch beyond (Claim 3.2)".
* Mail to mayor — pending immediately after this commit.
