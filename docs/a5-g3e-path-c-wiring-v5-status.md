# A5-G3e Path C wiring v5 — block-and-report

**Work item:** `mg-94fd` (Path C — generalise
`bipartite_balanced_enum` to drop the `hAB` hypothesis,
closing the K=2 + irreducible + w≥1 + |β|≥3 regime via
"the rotation argument from `Case2Rotation.lean`").

**Status:** **blocked** — the requested generalisation is
**substantively new math**, not a routine extension of the
existing rotation argument. The existing rotation
infrastructure (`Case2Rotation.lean`, mg-ba0c / mg-5a62 /
mg-27c2) operates on **within-band ⪯-comparable
pairs/chains**, while the K=2 + irreducible + w≥1 regime
contains configurations (e.g. the **N-poset**: |A|=|B|=2 with
x₁<y₁, x₂<y₂, all other pairs incomparable) where **every
within-band pair has ⪯-incomparable profiles** and the
existing rotation argument cannot apply. Closing these
configurations requires a *compound* poset automorphism
(simultaneous swap of two same-band pairs in different bands),
which is **not present in any existing file** and would be
a fresh ~300-500 LoC of structural infrastructure (matching
option (α) in pc-0fa0's audit, not option (γ) at 150-300 LoC).

Per pm-onethird's task body:

> CRITICAL: per pm-onethird's brief, BE CANDID — if
> 'extending the rotation argument' turns out to be
> substantively new math (not routine generalisation), flag
> explicitly via block-and-report. Round-4 stop-loss is
> FIRM: if this also blocks, pm-onethird pivots to option
> (δ) park (headline keeps `hC3` permanently, audit trail
> becomes the deliverable). No silent acceptance, no axioms.

I am exercising that candor clause now.

**Author:** `pc-94fd` polecat, 2026-04-27.

---

## TL;DR

* The existing **rotation infrastructure** in
  `Case2Rotation.lean` (mg-ba0c, mg-5a62, mg-27c2) consumes
  a **within-band ⪯-chain** (`StrictCase2WitnessChain L`:
  three within-band elements `a₁ ⪯ a₂ ⪯ a₃`) or a strict
  **within-band ⪯-pair** (`StrictCase2Witness L`).

* The **K=2 + irreducible + w≥1 + |β|≥3** regime contains
  configurations with **no within-band ⪯-pair at all**
  (every within-band pair has ⪯-incomparable two-sided
  profiles). The minimal such configuration is the N-poset
  (|A|=|B|=2). For these, neither
  `StrictCase2Witness L` nor `StrictCase2WitnessChain L`
  exists, so neither
  `case2Witness_balanced_under_FKG` nor
  `strictCase2WitnessChain_balanced_under_FKG` produces
  a balanced pair.

* `bipartite_balanced_enum`'s symmetry argument
  (`BipartiteEnum.lean:288`) crucially uses `hAB` to make the
  same-layer single-element transposition `Equiv.swap u v`
  a poset automorphism. Dropping `hAB` breaks the
  automorphism for cross-band configurations like the
  N-poset, since e.g. `(x₁ x₂)` swap maps `x₁<y₁` to
  `x₂<y₁` — but `x₂ ∥ y₁` in the N-poset.

* Closing the N-poset (and similar configurations) requires
  a **compound** poset automorphism — e.g. for N, the
  simultaneous transposition `(x₁ x₂)(y₁ y₂)` is the *only*
  swap that preserves the partial order. **No existing file
  constructs compound automorphisms.** Building this
  infrastructure (and the structural lemma matching same-band
  swap pairs across bands) is substantively new math.

* The estimated **150-300 LoC** in pc-0fa0's audit
  (`docs/a5-g3e-path-c-wiring-v4-status.md` §8 option (γ))
  was based on the unverified assumption that the rotation
  argument could be "extended". It cannot, under that name.
  A truthful re-estimate, based on either a finite
  enumeration of K=2 width-3 |β|≤6 posets or a structural
  case analysis with compound automorphisms, lands at
  **300-500+ LoC** of fresh infrastructure — which is the
  range pc-0fa0 attributed to option (α), not (γ). The
  PM choice between (α) and (γ) was based on a LoC
  difference that does not exist.

Per the **firm round-4 stop-loss**, this triggers the pivot
to **option (δ): park the FKG-hypothesis path**. The
headline `width3_one_third_two_thirds` retains `hC3`
permanently; the four status docs (mg-43f3, mg-4a5b,
mg-072c, mg-0fa0, mg-94fd) become the Path C cleanup
roadmap as a stand-alone deliverable.

---

## 1. The rotation argument as it stands

`Case2Rotation.lean` (mg-ba0c, mg-5a62, mg-27c2) provides
two end-user closure theorems and a chain-form FKG
sub-claim hypothesis:

* **`strictCase2Witness_balanced_under_FKG`**
  (`Case2Rotation.lean:870`):
  consumes `StrictCase2Witness L` (a within-band strict
  ⪯-pair) and `Case2FKGSubClaim L`, returns
  `HasBalancedPair α`.
* **`case2Witness_balanced_under_FKG`**
  (`Case2Rotation.lean:894`):
  the composed form, accepting any `Case2Witness L`
  (within-band ⪯-pair, possibly symmetric — Case 1 collapse
  handled inline).
* **`strictCase2WitnessChain_balanced_under_FKG`** (§5,
  used only on the `m = 3` branch internally): consumes
  three within-band ⪯-chain elements + chain-form FKG.

Each shape requires a within-band element pair (or chain)
satisfying the **one-sided ambient profile inclusion**
`(∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)`. Without
such a pair, none of these closure theorems fires.

The `Case2Witness L` predicate (`Case3Dispatch.lean:156`)
is itself defined as the existence of a within-band ⪯-pair:

```
def Case2Witness (L : LayeredDecomposition α) : Prop :=
  ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧
    (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)
```

The `Case3Witness L` predicate
(`Case3Dispatch.lean:176`) is the *negation* of (Case 1
ambient match) ∧ (Case 2 within-band ⪯-pair). The K=2
irreducible w≥1 regime can land in the `Case3Witness`
branch — and it does so **even at |β| ≥ 3**, where no
within-band ⪯-pair exists.

---

## 2. The N-poset: a concrete unhandled instance

**Configuration.** Let `α = {x₁, x₂, y₁, y₂}` with the
partial order generated by `x₁ < y₁` and `x₂ < y₂`; all
other pairs are incomparable. Set
`band(x₁) = band(x₂) = 1`, `band(y₁) = band(y₂) = 2`,
`L.K = 2`, `L.w = 1`.

**Layered axioms.**

* `band_pos`: `1 ≤ band x` ✓.
* `band_le`: `band x ≤ 2` ✓.
* `band_size`: each band has 2 ≤ 3 elements ✓.
* `band_antichain`: `{x₁, x₂}` and `{y₁, y₂}` are
  antichains ✓.
* `forced_lt`: `band x + w < band y` requires
  `1 + 1 < 2`, false; vacuous ✓.
* `cross_band_lt_upward`: `x < y ⟹ band x ≤ band y`,
  satisfied by the two cross-comparabilities `x_i < y_i` ✓.

**Layered properties.**

* **Width:** every 3-element subset contains a
  comparability (e.g. `{x₁, x₂, y₁}` has `x₁ < y₁`), so
  the largest antichain has size 2; `HasWidthAtMost α 3` ✓
  (with room to spare).
* **`LayerOrdinalIrreducible L`:** the only band-cut is
  `k = 1`. Reducibility at `k = 1` requires
  `∀ u v, band u = 1 → band v = 2 → u < v`, but
  `x₁ ∥ y₂` and `x₂ ∥ y₁` ⟹ no reducibility ✓.
* **`Fintype.card α = 4 ≥ 3`** ✓.
* **Not a chain** ✓ (4 incomparable pairs).

So the N-poset is a valid instance of the
**K=2 + irreducible + w≥1 + |β|≥3** regime that pc-0fa0
identified as the gap.

**Two-sided profiles.**

| element | up-set | down-set |
| --- | --- | --- |
| `x₁` | `{y₁}` | `∅` |
| `x₂` | `{y₂}` | `∅` |
| `y₁` | `∅` | `{x₁}` |
| `y₂` | `∅` | `{x₂}` |

**Case 1 (ambient profile match).** No within-band pair
matches both up and down profiles:

* `(x₁, x₂)`: up-sets `{y₁} ≠ {y₂}`. Fail.
* `(y₁, y₂)`: down-sets `{x₁} ≠ {x₂}`. Fail.

**Case 2 (within-band ⪯-pair).** Recall ⪯ is
"up-set inclusion + down-set reverse-inclusion".

* `(x₁, x₂)`: `up(x₁) = {y₁}` and `up(x₂) = {y₂}` are
  ⊆-incomparable. Fail.
* `(y₁, y₂)`: `down(y₁) = {x₁}` and `down(y₂) = {x₂}` are
  ⊆-incomparable. Fail.

**No `StrictCase2WitnessChain L`.** The chain shape
requires three within-band ⪯-chain elements. With only
2 elements per band, no such chain exists.

So **none** of the existing closure theorems
(`case2Witness_balanced_under_FKG`,
`strictCase2Witness_balanced_under_FKG`,
`strictCase2WitnessChain_balanced_under_FKG`) fires on the
N-poset.

**Yet a balanced pair exists.** Direct enumeration of the
6 linear extensions of N
(any of the 24 permutations of
`{x₁,x₂,y₁,y₂}` with `x₁` before `y₁` and `x₂` before
`y₂`, of which exactly 6 satisfy both):

```
(x₁, x₂, y₁, y₂), (x₁, x₂, y₂, y₁), (x₂, x₁, y₁, y₂),
(x₂, x₁, y₂, y₁), (x₁, y₁, x₂, y₂), (x₂, y₂, x₁, y₁).
```

Of these, 3 satisfy `x₁ <_L x₂` and 3 satisfy `x₂ <_L x₁`,
so `Pr[x₁ <_L x₂] = 1/2`. The pair `(x₁, x₂)` is
balanced.

The witness comes from the **compound automorphism**
`σ := (x₁ x₂)(y₁ y₂)`. This σ is a poset automorphism
because it maps `x₁ < y₁` to `x₂ < y₂` and vice versa
(both relations hold in N). The single-element
transposition `(x₁ x₂)` alone is **not** an automorphism:
it would map `x₁ < y₁` to `x₂ < y₁`, but `x₂ ∥ y₁`.

This is the structural fact the existing infrastructure
does not capture: no current file constructs compound
multi-orbit automorphisms.

---

## 3. Why `bipartite_balanced_enum`'s symmetry argument
breaks without `hAB`

`BipartiteEnum.lean`'s `swap_preserves_le` proof
(`BipartiteEnum.lean:105-193`) uses `hAB` in **every
branch** where one of `x, y` is the swap target `u` or
`v` and the other lies in the opposite band. Specifically,
when `x = u ∈ A` and `y ∈ B`, the proof needs `v ≤ y`,
which `hAB` directly provides. Without `hAB`, the bridge
fails: `v ∈ A` need not be `≤ y ∈ B`.

So `bipartite_balanced_enum`'s argument is **fundamentally
hAB-dependent**: dropping `hAB` is not a hypothesis weakening
of an existing proof — it requires a new proof strategy
(compound automorphisms, FKG with two-sided profiles, or
finite enumeration over the bipartite isomorphism classes).

---

## 4. What "extending the rotation argument" would
actually need

To close the N-poset (and the broader K=2 irreducible w≥1
|β|≥3 regime) by extending the rotation infrastructure,
one would need:

1. **A compound-automorphism constructor**: given a
   layered decomposition with two same-band pairs
   `(a₁, a₂) ⊆ M_i` and `(b₁, b₂) ⊆ M_j` such that the
   "matching" `a_k ↔ b_k` extends to a poset
   automorphism, build the compound `Equiv.swap` and
   prove it preserves `≤`. **~80-150 LoC** in a new
   file (analogous to `BipartiteEnum.lean:105-193` but
   handling two simultaneous orbits with the matching
   compatibility condition).

2. **A structural lemma** showing every
   K=2-irreducible-w≥1-|β|≥3 layered configuration with
   no within-band ⪯-pair admits such a matching. This
   is a finite combinatorial fact about subsets of
   `bandSet 2` indexed by `bandSet 1` (and symmetrically),
   and the "matching" is the bijection induced by some
   automorphism of the bipartite incidence structure.
   **~100-200 LoC** of case analysis or a finite
   enumeration framework.

3. **Generalised `bipartite_balanced_enum_general` head**:
   the dispatch on (Case 1 inline) → (Case 2 via
   `case2Witness_balanced_under_FKG`) → (compound
   automorphism via #1+#2). **~50-100 LoC** of dispatch.

**Total: ~230-450 LoC of new infrastructure**, of which
items #1 and #2 are entirely new content, not present in
`Case2Rotation.lean` or any other file. This is in the
range pc-0fa0's audit attributed to **option (α)**
(K=2 finite enumerator, 300-500 LoC), not the
**option (γ)** estimate of 150-300 LoC for "generalising
the rotation argument".

The "rotation argument" in `Case2Rotation.lean` is the
3-cycle inequality `Pr[a₂<a₁] + Pr[a₃<a₂] + Pr[a₁<a₃] ≥ 1`
on a within-band ⪯-chain. It does **not** address compound
swap automorphisms across bands; that is a different
mathematical content (Frobenius-style group action on
linear extensions, restricted to compatible matchings).

---

## 5. Why I am not silently accepting a workaround

The task body's hard gates:

* **NO `hAB`-shaped hypothesis** on the new theorem's
  signature.
* **NO new top-level FKG hypotheses** beyond `Case2FKGSubClaim L`.
* **NO new axioms.** No new `sorry` / `admit`.
* **NO paper-encoding deviation** (no `(L2)`
  strengthening).

Available single-session workarounds and why each fails a
gate:

* **Add a hypothesis "`L` admits a within-band
  ⪯-comparable pair"**: this is a re-statement of
  `Case2Witness L`, the same predicate `case2Witness_balanced_under_FKG`
  already consumes. Adding it as a top-level hypothesis to
  `bipartite_balanced_enum_general` doesn't generalise
  anything — the call site (the F3 step) cannot discharge
  it for the N-poset, because no such pair exists.
  Net effect: zero progress on the K=2 regime.

* **Restrict the conclusion to "if a within-band ⪯-pair
  exists"**: same problem. The F3 step can't pattern
  match to invoke this on the N-poset.

* **Axiomatise the N-poset (or the broader
  no-within-band-pair sub-case)**: forbidden by the "no
  new axioms" gate.

* **Strengthen `(L2)` to upward-strict**: this is option
  (β), explicitly rejected in pc-0fa0's audit and in the
  task body.

* **Add a `K = 2` finite enumeration as a new top-level
  hypothesis**: this re-creates the c5d5a10 multi-hypothesis
  failure mode under a different name, exactly the pattern
  the hard block-and-report rule forbids.

---

## 6. Stop-loss trigger: pivot to option (δ)

Per pm-onethird's task body:

> Round-4 stop-loss is FIRM: if this also blocks,
> pm-onethird pivots to option (δ) park (headline keeps
> hC3 permanently, audit trail becomes the deliverable).
> No silent acceptance, no axioms.

This is the round-4 block. The blocker history:

* **Round 1** (mg-4a5b → mg-072c): identified `mg-a735`,
  `mg-7f06`, `mg-27c2` as missing. All landed.
* **Round 2** (mg-072c → mg-0fa0): identified `mg-2e58`,
  `mg-26bb` as missing. Both landed.
* **Round 3** (mg-0fa0 → mg-94fd): identified
  `K = 2 + irreducible + w≥1 + |β|≥3` regime as missing.
  Strategic revisit triggered; PM picked option (γ).
* **Round 4** (mg-94fd → ?): this doc identifies that
  option (γ) is mis-scoped — the rotation argument
  cannot be extended in 150-300 LoC as the pc-0fa0 audit
  estimated. Truthful close requires option (α)
  infrastructure (~300-500 LoC) plus the option (γ)
  dispatch — and neither item exists in the form
  the task hypothesised.

The firm stop-loss applies. Option (δ) is the indicated
next step.

---

## 7. What I am doing

* **Writing this status doc** as the block-and-report
  deliverable, matching the precedent of
  `docs/a5-g3e-path-c-wiring-v4-status.md` (pc-0fa0),
  `docs/a5-g3e-path-c-wiring-v3-status.md` (pc-072c),
  `docs/a5-g3e-fkg-route-status.md` (pc-4a5b), and
  `docs/a8-s2-strict-witness-status.md` (pc-43f3).

* **Mailing mayor + pm-onethird** with summary + this doc
  reference, explicitly invoking the firm round-4 stop-loss
  for option (δ).

* **NOT** silently accepting any workaround that violates
  the hard gates (no new hypotheses on the headline, no
  axioms, no `sorry` / `admit`).

* **NOT** writing a partial `bipartite_balanced_enum_general`
  that only handles the within-band ⪯-pair sub-cases —
  that would be exactly the c5d5a10 multi-hypothesis
  failure mode in disguise, rejected at v3.

* **NOT exiting**; standing by per the polecat protocol for
  pm-onethird's next instruction (presumably to pivot to
  option (δ) or, if PM chooses, to commission a fresh
  ticket for the option (α) finite-enumeration route on a
  realistic LoC budget).

---

## 8. Recommended next step (option (δ) park)

Per pm-onethird's stated stop-loss procedure:

* Drop the dependency of `width3_one_third_two_thirds` on
  the chain-form `hFKG` swap. Keep `hC3` permanently as
  the residual hypothesis.
* Promote the five Path C status docs (mg-43f3, mg-4a5b,
  mg-072c, mg-0fa0, mg-94fd) to a stand-alone Path C
  cleanup roadmap. The roadmap documents what
  infrastructure would be needed to drop `hC3` (option
  (α) finite enumerator + the compound-automorphism
  infrastructure described in §4 of this doc), at a
  truthful LoC budget (~400-700 LoC across two or three
  fresh tickets).
* The `case3Witness_hasBalancedPair_outOfScope` axiom
  remains the closure for the K≥3 residual; its `K = 2`
  counterpart is the open infrastructure gap.

This is option (δ) as named in pc-0fa0's audit (§8) and
the task body (round-4 pivot).

Alternatively, if pm-onethird wishes to continue rather
than park, the *truthful* successor ticket is:

* **`mg-K2-finite-enum`**: option (α), K=2 width-3 |β|≤6
  finite enumeration analogous to F5a's
  `case3_certificate`. Realistic LoC budget 300-500.
  Covers the N-poset and all sibling configurations by
  enumeration of isomorphism classes (the bipartite
  incidence patterns on |A|, |B| ∈ {1, 2, 3}). Composes
  with `bipartite_balanced_enum_general`'s dispatch to
  close the K=2 regime end-to-end.

Either path requires PM signal before further
single-session attempts.

---

## 9. References

* `docs/a5-g3e-path-c-wiring-v4-status.md` (mg-0fa0) —
  pc-0fa0's audit; §8 four-option matrix and option (γ)
  selection.
* `docs/a5-g3e-path-c-wiring-v3-status.md` (mg-072c) —
  pc-072c's audit; first identifies the
  `K = 2` issue implicitly.
* `docs/a5-g3e-fkg-route-status.md` (mg-4a5b) — pc-4a5b's
  audit; original four-option strategic matrix.
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) —
  pc-43f3's block-and-report on the StrictCase2 closure
  (now resolved by mg-27c2).
* `lean/OneThird/Step8/Case2Rotation.lean:870`,`:894` —
  `strictCase2Witness_balanced_under_FKG` and
  `case2Witness_balanced_under_FKG` (the rotation
  closure; consumes within-band ⪯-pair, not compound
  swaps).
* `lean/OneThird/Step8/Case2Rotation.lean:167`-`:205` —
  `StrictCase2WitnessChain L` (the m=3 chain shape,
  consumed by §5's
  `strictCase2WitnessChain_balanced_under_FKG`).
* `lean/OneThird/Step8/BipartiteEnum.lean:105-193` —
  `swap_preserves_le`; uses `hAB` in every cross-band
  branch.
* `lean/OneThird/Step8/BipartiteEnum.lean:288` —
  `bipartite_balanced_enum`; the theorem to be
  generalised.
* `lean/OneThird/Step8/Case2BipartiteBound.lean:197` —
  `hasBalancedPair_of_K2_w0_incomp` (the current K=2
  w=0 lift, proper specialisation requiring `L.w = 0`).
* `lean/OneThird/Step8/Case3Dispatch.lean:156` —
  `Case2Witness L` predicate (within-band ⪯-pair).
* `lean/OneThird/Step8/Case3Dispatch.lean:176` —
  `Case3Witness L` predicate (the negation; the bin
  the N-poset lands in).
* `lean/OneThird/Step8/LayerOrdinal.lean:240` —
  `LayerOrdinalIrreducible L` definition (verifies the
  N-poset is irreducible).
* `lean/OneThird/Step8/LayeredReduction.lean:96` —
  `LayeredDecomposition` structure (verifies the N-poset
  satisfies all layered axioms with `K = 2`, `w = 1`).
* `step8.tex:2824-2940` — `prop:bipartite-balanced` (the
  paper's argument for the *bipartite* case with `hAB`;
  Case 1 is the swap, Case 2 is the FKG chain).
* `step8.tex:2965-3048` — `prop:in-situ-balanced` (the
  paper's `K ≥ 2` lift; Case 3 is the *width-3* finite
  enumeration, which does **not** cover the |A|=|B|=2
  N-poset configuration in the bipartite sense — the
  paper implicitly relies on `prop:bipartite-balanced`'s
  Case 1 for the within-band same-profile pair, which
  itself relies on `hAB`).
