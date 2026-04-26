# A8-S2-rotation-residual status — partial closure via chain swap

**Work item:** `mg-ba0c` (A8-S2-rotation-residual: Route A discharge of the
"`Pr > 2/3` residual" case from `m3_rotation_balanced_or_residual`).

**Status:** **partial — Route A's residual case closed; full
discharge of `strictCase2WitnessChain_balanced` is BLOCKED on the
FKG sub-claim hypothesis (Route B's deliverable).**

**Author:** `pc-ba0c2` polecat, 2026-04-26.

---

## TL;DR

* **What landed (`pc-ba0c2`).** A direct combinatorial proof that
  the chain hypothesis itself forces `probLT a a' ≤ 1/2` in the
  chain-forward direction, via a position-swap injection on linear
  extensions. Concretely:
  * `chainSwap_LE` — the swap construction on `LinearExt α`,
    valid for LEs with `a <_L a'` under one-sided ⪯-inclusion
    `(upper(a) ⊆ upper(a'), lower(a') ⊆ lower(a))`.
  * `probLT_le_half_of_chain` — the headline `Pr ≤ 1/2` bound.
  * `chain_residual_impossible` — the polecat-spec residual
    (`2/3 < probLT a₁ a₂ ∧ … ∧ 2/3 < probLT a₁ a₃`) is
    **structurally impossible** under chain alone (chain swap
    immediately contradicts `2/3 < · ≤ 1/2`).
  * `strictCase2WitnessChain_balanced_under_FKG` — the conditional
    full discharge: under chain + the FKG sub-claim hypothesis
    `hFKG`, `HasBalancedPair α` follows.

* **What is still open.** The unconditional theorem
  `strictCase2WitnessChain_balanced` (`StrictCase2WitnessChain L →
  HasBalancedPair α` with no `hFKG` input) requires either
  * **Route B** — establish `hFKG` (`1/2 ≤ probLT a_i a_{i+1}` in
    the chain-forward direction) from the
    probability-normalised cross-poset FKG bound, currently future
    work in `OneThird.Mathlib.RelationPoset.FKG` (`§11`,
    `Mathlib/RelationPoset/FKG.lean:407-426`); or
  * a tighter probability bound — show `1/3 ≤ probLT a a'` for
    some chain pair from width-3 + irreducibility +
    `¬ InCase3Scope` (essentially the `1/3-2/3` conjecture for
    layered width-3 chain antichains).

* **No new axioms, no `sorry`, no `admit`.** `#print axioms` on
  the four new declarations reports only the mathlib trio
  (`[propext, Classical.choice, Quot.sound]`); on
  `width3_one_third_two_thirds` reports the unchanged baseline
  (mathlib trio + `brightwell_sharp_centred`).

---

## 1. The chain swap argument

The polecat's `StrictCase2WitnessChain L` carries three within-band
elements `a₁, a₂, a₃` with the **one-sided** profile chain

```
upper(a₁) ⊆ upper(a₂) ⊆ upper(a₃)
lower(a₃) ⊆ lower(a₂) ⊆ lower(a₁)
```

(see `Case2Rotation.lean:167-172`; the convention follows
`Case2FKG.lean:152-153`'s discussion: `a` has more
lower-comparabilities, `a'` has more upper-comparabilities, hence
`a'` "tends to come earlier" in a uniformly random LE).

**Chain swap (`chainSwap_LE`).** Given any LE `L` with `L.lt a a'`
(i.e., `a` precedes `a'` in this LE), exchanging the positions of
`a` and `a'` in `L` produces a new valid LE with `a' <_L a`. The
construction is a position-swap (precomposition of `L.toFun` with
`Equiv.swap a a'`); monotonicity of the swapped extension follows
from a case-by-case argument on whether the two elements `x, y` of
the constraint `x ≤ y` lie in `{a, a'}`.

The four "interesting" cases:

| `x ∈ {a, a'}` | `y ∈ {a, a'}` | Goal | Proof input |
|---|---|---|---|
| `x = a`, `y ∉ {a, a'}` | — | `L.toFun a' ≤ L.toFun y` | `a < y → a' < y` (chain `h_up`) |
| `x = a'`, `y ∉ {a, a'}` | — | `L.toFun a ≤ L.toFun y` | `pos a < pos a' < pos y` |
| `x ∉ {a, a'}`, `y = a` | — | `L.toFun x ≤ L.toFun a'` | `pos x < pos a < pos a'` |
| `x ∉ {a, a'}`, `y = a'` | — | `L.toFun x ≤ L.toFun a` | `x < a' → x < a` (chain `h_down`) |

The two diagonal cases (`x = a, y = a'` and `x = a', y = a`) are
ruled out by the incomparability hypothesis `a ∥ a'` (which forbids
`a ≤ a'` and `a' ≤ a`).

**Bound (`probLT_le_half_of_chain`).** The map
`L ↦ chainSwap_LE L` is an injection from `{L : L.lt a a'}` into
`{L : L.lt a' a}` (its inverse on the source recovers `L` because
`Equiv.swap a a'` is an involution). Hence

```
|{L : L.lt a a'}| ≤ |{L : L.lt a' a}|
```

Combined with `Pr[a <_L a'] + Pr[a' <_L a] = 1`
(`probLT_add_probLT_of_ne`):

```
2 · probLT a a' ≤ 1, i.e., probLT a a' ≤ 1/2.
```

**Note on directionality.** The chain swap is *one-directional*:
the swap is only a valid LE-operation for LEs that *already* have
`a <_L a'`. Starting from an LE with `a' <_L a`, the swap may fail
(specifically, when some `x ∈ lower(a) \ lower(a')` lies between
`pos a'` and `pos a` in the LE, the swapped LE violates `x <
a`). This asymmetry is exactly what produces the strict
inequality `Pr[a < a'] < Pr[a' < a]` whenever the chain is
genuinely strict (lower-set inclusion is strict).

---

## 2. The residual case is closed

The polecat-spec **residual** is the disjunct of
`m3_rotation_balanced_or_residual` (`Case2Rotation.lean:362-366`):

```lean
(2 : ℚ) / 3 < probLT a₁ a₂ ∧
(2 : ℚ) / 3 < probLT a₂ a₃ ∧
(2 : ℚ) / 3 < probLT a₁ a₃
```

Under the chain hypothesis, `probLT a₁ a₂ ≤ 1/2` (chain swap on
`(a₁, a₂)`). So `2/3 < probLT a₁ a₂ ≤ 1/2` is a direct linarith
contradiction. Recorded as `chain_residual_impossible`.

Composed with the polecat's existing
`strictCase2WitnessChain_balanced_or_residual`
(`Case2Rotation.lean:485-515`), this immediately yields:

```lean
theorem strictCase2WitnessChain_balanced_under_FKG
    (L : LayeredDecomposition α) (hC : StrictCase2WitnessChain L)
    (hFKG : <forward FKG sub-claim hypothesis>) :
    HasBalancedPair α
```

i.e., **conditional** on the FKG sub-claim hypothesis (`hFKG`),
`HasBalancedPair α` follows from the chain witness.

---

## 3. Why this is **not** the unconditional theorem

The polecat's existing `strictCase2WitnessChain_balanced_or_residual`
takes `hFKG` as an explicit hypothesis. Concretely:

```lean
hFKG : ∀ a₁ a₂ a₃ : α, … →
  (1 : ℚ) / 2 ≤ probLT a₁ a₂ ∧
  (1 : ℚ) / 2 ≤ probLT a₂ a₃ ∧
  (1 : ℚ) / 2 ≤ probLT a₁ a₃
```

This is the forward direction of the paper's FKG sub-claim
(`step8.tex:2858-2875`). Combined with the chain swap bound
`probLT a₁ a₂ ≤ 1/2`, `hFKG` forces `probLT a₁ a₂ = 1/2` exactly,
which is the **symmetric/Case 1 collapse** sub-case (already
absorbed by `case2Witness_balanced_or_strict` in `Case2FKG.lean`).

In the **strict** chain case (lower-set inclusions are proper
inclusions), the chain swap injection is strict
(`probLT a₁ a₂ < 1/2`), so `hFKG`'s `1/2 ≤ probLT a₁ a₂` is
**violated**. In other words, **`hFKG` cannot be discharged from
chain alone in the strict case** — the only way to satisfy it is
to obtain the bound from outside the chain hypothesis, which is
exactly what Route B's probability-normalised FKG gives.

This sign mismatch is *not* a bug in the polecat's existing
`m3_rotation_balanced_or_residual` lemma — that lemma is
labelling-agnostic (just rational arithmetic on three pair
probabilities). The mismatch is between the chain hypothesis's
**direction** (which forces `probLT a₁ a₂ ≤ 1/2`, i.e., chain swap
direction) and the FKG sub-claim's **direction** (which asserts
`probLT a₁ a₂ ≥ 1/2`, i.e., the paper's labelling per
`step8.tex:2868`, "more forced edges means earlier in LE").

---

## 4. Path forward

### 4a. Reverse-labelling re-application of `m3_rotation_balanced_or_residual`

Apply `m3_rotation_balanced_or_residual` with **reverse** labelling
`(a₃, a₂, a₁)` instead of `(a₁, a₂, a₃)`:

* `hp12_rev : 1/2 ≤ probLT a₃ a₂` — holds by complement of chain
  swap on `(a₂, a₃)`: `probLT a₂ a₃ ≤ 1/2 ⇒ probLT a₃ a₂ ≥ 1/2`.
* `hp23_rev : 1/2 ≤ probLT a₂ a₁` — by chain swap on `(a₁, a₂)`.
* `hp13_rev : 1/2 ≤ probLT a₃ a₁` — by chain swap (transitive).

This **does** satisfy the FKG hypothesis direction, and yields:

```
HasBalancedPair α ∨
  (2/3 < probLT a₃ a₂ ∧ 2/3 < probLT a₂ a₁ ∧ 2/3 < probLT a₃ a₁)
```

The new residual — equivalently,
`probLT a₂ a₃ < 1/3 ∧ probLT a₁ a₂ < 1/3 ∧ probLT a₁ a₃ < 1/3`
— is the **all-three-`< 1/3`** case. **This residual is NOT
closeable by chain swap alone**: the chain swap bound
`probLT a a' ≤ 1/2` is consistent with `probLT a a' < 1/3`. So
applying `m3_rotation_balanced_or_residual` with the reverse
labelling produces a residual that requires *additional structural
input* to close.

This is the genuine open mathematical gap. See §5 for closure
strategies.

### 4b. Closing the all-three-`< 1/3` residual

Two routes:

* **Route B (FKG probability-normalised).** The
  `OneThird.Mathlib.RelationPoset.FKG.probLT'_mono_of_relExt`
  cross-poset count-form headline (`mg-0b81`) lifted to a
  probability-normalised form (acknowledged future work in
  `Mathlib/RelationPoset/FKG.lean:407-426`) would give the FKG
  sub-claim `1/2 ≤ probLT a_i a_{i+1}` in the **forward**
  direction. Combined with chain swap (`probLT a_i a_{i+1} ≤
  1/2`), this forces `probLT = 1/2` — the symmetric collapse
  case, fully absorbed by `case2Witness_balanced_or_strict`.

  Cost: ~2000-3500 LOC (the cross-poset infrastructure layer; see
  `docs/a8-s2-status.md` §5 "A8-S2-cont").

* **`1/3-2/3` for layered width-3 chain.** Show that under
  `(StrictCase2WitnessChain L, hW3, hIrr, ¬InCase3Scope)`, at
  least one chain pair has `probLT a_i a_{i+1} ≥ 1/3` (combined
  with chain swap's `≤ 1/2`, lands in `[1/3, 1/2] ⊆ [1/3, 2/3]`,
  giving `HasBalancedPair α`).

  Status: this is essentially the `1/3-2/3` conjecture
  specialised to layered width-3 chain configurations. **Open.**
  Empirical evidence from minimal examples (`5`-element K=3
  chain, `6`-element K=2 chain) suggests `probLT[a_1 < a_2] ≥
  1/3` always holds, but no Lean-checkable proof currently
  exists.

---

## 5. Concrete examples

### 5a. The polecat-spec residual `Pr > 2/3` is structurally impossible

A direct chain swap consequence: in **any** layered `L` with
`StrictCase2WitnessChain L`, `probLT a₁ a₂ ≤ 1/2 < 2/3`, so the
spec's "all three pair-probs > 2/3" residual *cannot* be exhibited.
**No counterexample exists** in this direction. (`pc-ba0c2`'s
`chain_residual_impossible` is a Lean-checked proof of this.)

### 5b. The all-three-`< 1/3` residual is consistent with chain alone

Smallest example: `α = {b₁, a₁, a₂, a₃, c₁}` with `b₁ < a₁`
(only) and `a₃ < c₁` (only). Layering: `K = 3` with `M_1 = {b_1}`,
`M_2 = {a_1, a_2, a_3}`, `M_3 = {c_1}`. Width 3, irreducible at
`k=1, 2`, `K = 3 ≠ 3` — wait, `K = 3` is **in scope** for
`InCase3Scope` (decidable predicate is `K = 3 ∧ 1 ≤ w ≤ 4 ∧
size constraints`). So this specific `(K = 3, w = 0)` triple may
or may not be `InCase3Scope` depending on the size cap. With
`card α = 5 ≤ 9`, w=0 fails the `1 ≤ w` requirement, so
`¬ InCase3Scope` ✓.

In this 5-element example:

* `probLT a₁ a₂ = 1/3` (boundary balanced).
* `probLT a₂ a₃ = 1/3`.
* `probLT a₁ a₃ = 1/6` (NOT balanced).

So pair `(a₁, a₂)` lies on the `1/3` boundary (just balanced), pair
`(a₂, a₃)` likewise, and pair `(a₁, a₃)` is below. **At least
one pair is balanced** (Pr ∈ [1/3, 2/3]), so `HasBalancedPair α`
holds — not as a counterexample to the conjecture, but as
empirical evidence that the conjecture *does* hold here.

### 5c. K=2 width-3 strict chain

`α = {b₁, b₂, b₃, a₁, a₂, a₃}` with lower-sets
`lower(a₁) = {b₁, b₂, b₃}`, `lower(a₂) = {b₁, b₂}`,
`lower(a₃) = {b₁}`. K=2, w=0, ¬InCase3Scope (K ≠ 3).

* `probLT a₁ a₂ = 24/57 ≈ 0.421` (balanced).
* `probLT a₂ a₃ = 24/57 ≈ 0.421` (balanced; by the symmetry
  `(b_i, b_j) ↔ (a_{4-i}, a_{4-j})`).
* `probLT a₁ a₃` is somewhat smaller but above `1/3`.

**Takeaway.** In all small in-scope chain examples, at least one
pair is balanced. The conjecture (4b's second route) appears
empirically to hold. A general proof, however, requires either
case-by-case enumeration of small layered configurations or the
full Route B FKG infrastructure.

---

## 6. References

* Polecat instructions: `mg-ba0c` task body.
* `lean/OneThird/Step8/Case2Rotation.lean` — `pc-ba0c2`'s addition:
  `chainSwap_LE`, `chainSwap_LE_pos`, `chainSwap_LE_lt`,
  `probLT_le_half_of_chain`, `chain_residual_impossible`,
  `strictCase2WitnessChain_balanced_under_FKG` (this file's §6).
* `lean/OneThird/Step8/Case2Rotation.lean` `:139-203` — the
  `StrictCase2WitnessChain` predicate (mg-5a62).
* `lean/OneThird/Step8/Case2Rotation.lean` `:317-384` — the
  `m3_rotation_balanced_or_residual` dispatch lemma (mg-5a62).
* `lean/OneThird/Step8/Case2FKG.lean` `:140-202` — the
  symmetric collapse / `StrictCase2Witness` extraction (mg-8801).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:407-426` — Route
  B's documented future work (probability-normalised FKG
  monotonicity).
* `step8.tex:2858-2875` — the paper's FKG sub-claim, m=2/m=3.
* `step8.tex:2900-2914` — the paper's residual argument with the
  documented transcription error (`Case2Rotation.lean §4`).
* `docs/a5-g2-status.md` — the `mg-53ce` precedent for
  block-and-report status docs.
* `docs/a8-s2-status.md` §A8-S2-rotation — the parent split's
  status (mg-5a62).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline
  (unchanged).
