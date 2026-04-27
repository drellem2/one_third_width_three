# Path C cleanup roadmap — option (δ) park deliverable

**Status:** Path C cleanup is **parked** under option (δ) per
pm-onethird's firm round-4 stop-loss (2026-04-27). The headline
`OneThird.width3_one_third_two_thirds`
(`lean/OneThird/MainTheorem.lean:38-43`) **retains its `hC3 :
Step8.Case3Witness` hypothesis permanently** under this decision.
Future readers tempted to "fix" this by dropping `hC3` should read
this roadmap before attempting that work — the obstruction is a
named structural gap (the `K=2` + irreducible + `w≥1` + `|β|≥3`
N-poset class), not an audit oversight, and the closing
infrastructure is substantively new mathematical content
(~300-500 LoC of compound-automorphism / finite-enumeration work
that does not exist in the tree today).

This document is the **audit-as-deliverable** for the four-round
arc that attempted Path C cleanup across mg-4a5b → mg-072c →
mg-0fa0 → mg-94fd (with mg-43f3 as the prelude). It supersedes
the five round-by-round status docs as the navigation entry
point, but does not delete them — they remain in place as the
detailed engineering record. Where this roadmap and a status doc
disagree, the status doc records what was true at its writing
moment; this roadmap is the post-hoc synthesis.

**Author:** `pc-7261` polecat, 2026-04-27 (under mg-7261).

---

## 1. The cleanup goal

The headline width-3 1/3–2/3 theorem currently has the shape

```lean
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α
```

at `lean/OneThird/MainTheorem.lean:38-43`. The third hypothesis
`hC3 : Step8.Case3Witness` is the universally-quantified Case-3
discharge

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 → ¬ IsChainPoset β →
    2 ≤ Fintype.card β → HasBalancedPair β
```

at `lean/OneThird/Step8/LayeredBalanced.lean:419`. Discharging it
inside the formalization is what Path C cleanup is about.

The intended cleanup, per the original mg-b329 Path C plan
(reverted in c5d5a10 → mg-05d3), was a **1-for-1 hypothesis
swap**: drop `hC3`, add a single hypothesis `hFKG` (the
chain-form FKG sub-claim hypothesis bundled by mg-27c2's
`Step8.InSitu.Case2FKGSubClaim`), and prove `Case3Witness` as a
theorem. The `Case3Witness` theorem would then route through
F3-strong-induction with the bounded-irreducible-balanced leaf
discharged via the project axiom
`case3Witness_hasBalancedPair_outOfScope`
(`lean/OneThird/Step8/Case3Residual.lean:208`) on its `K ≥ 3`
profile, the in-scope leaf via the F5a Bool certificate, and the
small / reducible / `K = 2` / `K = 1` cases via the descent
machinery.

The goal is paper-faithful: the `hC3` hypothesis is structurally
the closure of `prop:in-situ-balanced` against an (open
mathematical) FKG sub-claim, and the headline theorem should
ideally reduce to that sub-claim, not carry `hC3` itself as a
project hypothesis. The arc tried to make that reduction
constructive, in tree, with no new axioms.

**The arc concluded that this is not closeable under the current
mathematical infrastructure**, and the necessary new
infrastructure is substantively new math (not a routine
formalization extension). The headline keeps `hC3` until that new
math lands.

---

## 2. The negative exemplar: c5d5a10 (reverted via mg-05d3)

Round 0 of this arc was a single-shot polecat attempt
(`mg-b329`) to land the cleanup directly. It produced commit
`c5d5a10` ("lean: A5-G3e partial — F3 framework + drop hC3 from
width3_one_third_two_thirds"), which:

* Introduced a width-3-threaded F3 framework (the seed that later
  shipped cleanly as mg-a735).
* Dropped `hC3` from the headline.
* Added a `Case3WitnessHStep` predicate that bundled five-plus
  propositional hypotheses into a single step-function predicate.

The bundled-step predicate let the headline compile, but it
**re-encoded the closure obligation as a hypothesis** rather
than discharging it — i.e., it traded one opaque `hC3` for
another opaque `hStep`. The mayor rejected this as a violation of
the cleanup's spirit, and `mg-05d3` reverted the headline change.
Its lasting contribution was the F3 framework idea, which mg-a735
re-landed without the multi-hypothesis predicate.

Every round of the arc that followed had a **hard
block-and-report rule** in its task body, explicitly forbidding
this failure mode: "if the polecat finds it cannot close without
adding additional hypotheses (the option-(b) failure mode that
produced the rejected c5d5a10 commit), STOP. Mail mayor +
pm-onethird per the standard block-and-report protocol. Do NOT
silently accept a multi-hypothesis variant." Each polecat
honoured this rule and produced the corresponding status doc
instead of a partial wiring.

The cancel-pair `c5d5a10` + `mg-05d3` is preserved on `main` as
the audit trail; both are referenced from each status doc as the
negative exemplar.

---

## 3. The four-round arc

### Round 1 — mg-43f3 (prelude): the StrictCase2 closure shape

`docs/a8-s2-strict-witness-status.md` (commit `e6ce389`) is the
first audit document. The polecat `pc-43f3` was tasked with
closing the StrictCase2 sub-case (the `m=2` and `m=3` chain
discharges that `prop:in-situ-balanced` requires), and reported
that **both viable signature shapes for the closure are
FKG-only** — i.e., they need either Route B
(probability-normalised cross-poset FKG, future work flagged in
`Mathlib/RelationPoset/FKG.lean`) or the layered width-3 chain
`1/3` lower-bound conjecture (open). This is the document that
named the FKG sub-claim shape the cleanup arc would later try to
introduce as the new headline hypothesis.

Key positive output: pinned the closure target to a
**chain-form** (`m=3`) sub-claim, not pair-form. This is the
shape mg-27c2 later landed conditionally as
`Case2FKGSubClaim L` + `case2Witness_balanced_under_FKG`.

### Round 2 — mg-4a5b: first 1-for-1 swap attempt

`docs/a5-g3e-fkg-route-status.md` (commit `72cd563`). `pc-4a5b`
attempted the 1-for-1 swap directly and reported three missing
infrastructure pieces:

1. A **width-3-threaded F3 strong-induction framework** (the bare
   F3 in `LayerOrdinal.lean` drops `HasWidthAtMost α 3` through
   the IH). → later shipped as **mg-a735** (`cecd709`).
2. **`OrdinalDecomp` Lower / Upper `hasBalancedPair_lift`
   constructors** (only the Mid lift was in tree). → later
   shipped as **mg-7f06** (`76adc5e`).
3. The **chain-form FKG closure**
   `case2Witness_balanced_under_FKG`, bundling the
   `StrictCase2WitnessChain L` discharge from mg-43f3's analysis.
   → later shipped as **mg-27c2** (`38d1013`).

Estimated cost at this round: ~480-850 LoC across 4-6 files.
Block-and-report.

### Round 3 — mg-072c: with three deps landed, two more surface

`docs/a5-g3e-path-c-wiring-v3-status.md` (commit `b35949e`).
After the three round-2 deps landed, `pc-072c` revisited the
cleanup and found two further pieces that the round-2 audit had
not separated out:

1. A **Window-OrdinalDecomp constructor** for the F3 step's
   irreducible C1 branch. The natural window
   `[min(i,j) − w, max(i,j) + w]` has boundary pairs at distance
   `1 ≤ w` for `w ≥ 1`, violating `(L2-forced)`'s strict
   separation requirement (which needs distance `> w`). Closing
   this required a non-trivial cutoff selection. → later shipped
   as **mg-2e58** (`419cb35`), via maximal-`B_lo` /
   minimal-`B_hi` valid cutoffs.
2. An **outer-loop Bool→Prop bridge**
   `allBalanced w sizeLimit = true → ∀ bs ∈ bandSizesGen 3
   sizeLimit, enumPosetsFor w bs = true`. The inner
   `enumPosetsFor` bridge existed (mg-580e / mg-b487, ~300 LoC
   in `EnumPosetsForBridge.lean`); the outer one did not. →
   later shipped as **mg-26bb** (`0550d2f`).

Round-3 block-and-report. PM accepted one round of "new
infrastructure surfacing" and authorised round 4 with the
explicit pre-commitment that round 5 would trigger a strategic
revisit.

### Round 4 — mg-0fa0: the K=2 irreducible w≥1 regime

`docs/a5-g3e-path-c-wiring-v4-status.md` (commit `4034fa1`).
With all five infrastructure deps landed, `pc-0fa0` attempted
the F3 step proof and discovered that the universally quantified
`Case3Witness` predicate's step function must handle **every**
value of `LB.K`, including a regime that none of the in-tree
handlers cover:

* `bounded_irreducible_balanced_hybrid` requires `3 ≤ L.K`.
* `case3Witness_hasBalancedPair_outOfScope` requires `3 ≤ L.K`.
* `hasBalancedPair_of_K2_w0_incomp` requires `L.w = 0`.
* `OrdinalDecomp.windowOfPairAt` collapses to the degenerate
  `Mid = α` case at `L.K = 2`, `L.w ≥ 1` (every valid lower
  cutoff `≥ 2` requires an empty band-1, contradicting
  irreducibility).
* `LayerOrdinalIrreducible` at `K = 2` excludes the only
  available band-cut.

So `K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3` is a real,
unaccounted-for regime. Round 4 surfaced it as a third round of
"new infrastructure surfacing", triggering pm-onethird's
strategic revisit clause. PM picked **option (γ)**: "Generalise
`bipartite_balanced_enum` to drop the `hAB : ∀ a ∈ A, ∀ b ∈ B,
a ≤ b` hypothesis, closing the K=2 irreducible regime by
extending the rotation argument from `Case2Rotation.lean`."
Estimated 150-300 LoC.

### Round 5 — mg-94fd: option (γ) is mis-scoped (firm stop-loss)

`docs/a5-g3e-path-c-wiring-v5-status.md` (commit `2579db7`).
`pc-94fd` audited the option (γ) plan and reported that the
"extension of the rotation argument" is **substantively new
math, not a routine generalisation**.

The minimal failing instance is the **N-poset**:
`α = {x₁, x₂, y₁, y₂}` with `x₁ < y₁` and `x₂ < y₂`,
`band 1 = {x₁, x₂}`, `band 2 = {y₁, y₂}`, `K = 2`, `w = 1`. It
satisfies all layered axioms, has width ≤ 3, is irreducible
(neither `x₁ ∥ y₂` nor `x₂ ∥ y₁` is a `<`), and has
`Fintype.card α = 4 ≥ 3`. Both `(x₁, x₂)` and `(y₁, y₂)` have
incomparable two-sided profiles (`up(x₁) = {y₁}`,
`up(x₂) = {y₂}` are ⊆-incomparable), so **no within-band ⪯-pair
exists** — i.e., neither `Case1` (ambient match) nor `Case2`
(within-band ⪯-pair) fires. The pair is balanced
(`Pr[x₁ <_L x₂] = 1/2` by direct enumeration of N's six linear
extensions), but the witness comes from the **compound**
automorphism `σ := (x₁ x₂)(y₁ y₂)` — the single transposition
`(x₁ x₂)` alone is not a poset automorphism (it would map
`x₁ < y₁` to `x₂ < y₁`, but `x₂ ∥ y₁`).

The existing rotation infrastructure (`Case2Rotation.lean`,
mg-ba0c / mg-5a62 / mg-27c2) operates on **within-band
⪯-comparable pairs/chains**. It has no machinery for compound
multi-orbit automorphisms across bands. A truthful re-estimate of
the missing infrastructure lands at ~300-500+ LoC, in the range
pc-0fa0 had attributed to **option (α)** (K=2 finite
enumerator), not the **option (γ)** estimate. The PM choice
between (α) and (γ) was based on a LoC difference that does not
exist.

Per pm-onethird's pre-committed firm round-4 stop-loss, this is
the trigger for **option (δ): park**. The headline retains
`hC3` permanently; the audit trail (these five status docs +
this roadmap) becomes the deliverable.

---

## 4. Infrastructure that landed and remains useful

The arc shipped six substantive code commits. Each was
motivated by Path C cleanup, but each is independently useful for
future Step-8 / layered-poset work and should not be reverted.

| Commit | Tag | Adds | Where |
|---|---|---|---|
| `cdafbfe` | mg-9568 | `freeUVOf` refactor + `enumPredAtMaskOf_eq_predMaskOf` + `successorMasks_testBit` (closes 5 inScope caller obligations bottom-up) | `PredMaskBridge.lean`, `SymmetricLift.lean`, F5a §7-§8 |
| `76adc5e` | mg-7f06 | `OrdinalDecomp.hasBalancedPair_lift_lower` and `_upper` constructors (Mid-repackaging via `toMidOfLower` / `toMidOfUpper`) | `Mathlib/LinearExtension/Subtype.lean:1227`,`:1237` |
| `cecd709` | mg-a735 | `Step8.hasBalancedPair_of_layered_strongInduction_width3` and `_le` corollary, threading `HasWidthAtMost · 3` through both call site and IH | `lean/OneThird/Step8/LayerOrdinal.lean:472` |
| `38d1013` | mg-27c2 | `Case2FKGSubClaim L` (bundled `m=2` pair + `m=3` chain hypothesis), `strictCase2Witness_balanced_under_FKG`, `case2Witness_balanced_under_FKG` (the `Case2Witness L → HasBalancedPair α` form consumed by `hStruct_of_case2_discharge`) | `lean/OneThird/Step8/Case2Rotation.lean:870`,`:894` |
| `419cb35` | mg-2e58 | `OrdinalDecomp.windowOfPairAt L x y` constructor — produces an `OrdinalDecomp α` whose `Mid` contains both elements of an incomparable pair, via maximal-`B_lo` / minimal-`B_hi` valid cutoffs | `lean/OneThird/Step8/WindowDecomp.lean:375` |
| `0550d2f` | mg-26bb | `Case3Enum.allBalanced_imp_enumPosetsFor` outer-loop Bool→Prop bridge — unrolls the F5a Bool certificate's outer `for bs in bandSizesGen 3 sizeLimit` loop into the per-`bs` consequence | `lean/OneThird/Step8/Case3Enum/AllBalancedBridge.lean:218` |

These six commits collectively raise the "infrastructural floor"
for any future Step-8 work. In particular:

* **mg-a735** is the right F3 framework for any width-3-bounded
  inductive argument; without it, future work would have to
  re-derive width-3 threading.
* **mg-7f06** generalises `OrdinalDecomp.hasBalancedPair_lift`
  to all three slots (Lower, Mid, Upper); the Mid-only restriction
  was a real expressivity gap.
* **mg-27c2** is the chain-form FKG closure as a self-contained
  module — useful on its own as the conditional reduction of
  Case 2 to the chain FKG sub-claim, independent of whether the
  sub-claim itself is ever discharged.
* **mg-2e58** is the right window constructor (the natural
  cutoff choice fails for `w ≥ 1`; mg-2e58's maximal-valid
  selection works whenever any descent is possible at all).
* **mg-26bb** is the missing outer-loop bridge for any
  certificate-based discharge of `enumPosetsFor` consequences.
* **mg-9568** finishes the §7 / §8 cleanup of the F5a inScope
  caller obligations.

None of these depend on Path C cleanup landing. They are
prerequisites for it — but they are also general-purpose pieces
that future work in adjacent areas will reuse.

---

## 5. The named obstruction: K=2 + irreducible + w≥1 + |β|≥3

The remaining gap is structural, not bookkeeping. The
predicate's universal scope is

```lean
∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : LayeredDecomposition β),
    HasWidthAtMost β 3 → ¬ IsChainPoset β →
    2 ≤ Fintype.card β → HasBalancedPair β
```

Discharging it means handling every `LB.K` value. The
single-K row that has no in-tree handler is

* `LB.K = 2` (only band-cut excluded by irreducibility);
* `LB.w ≥ 1` (rules out `hasBalancedPair_of_K2_w0_incomp`);
* `Fintype.card β ≥ 3` (rules out the trivial 2-element chain);
* irreducible at the only band-cut `k = 1` (rules out
  reducibility descent);
* the bipartite incidence pattern admits no within-band
  ⪯-comparable pair (rules out `case2Witness_balanced_under_FKG`).

The prototype is the N-poset (`|A| = |B| = 2`, two
non-crossing comparabilities). Sibling configurations exist on
`|A|, |B| ∈ {1, 2, 3}` (e.g., `|A| = 2, |B| = 3` with three
non-crossing comparabilities). The full enumeration of
isomorphism classes under width-3 + irreducibility + non-trivial
cardinality is finite but non-trivial.

For the N-poset, the balanced-pair witness comes from the
**compound** automorphism `σ := (x₁ x₂)(y₁ y₂)`. The single
transposition `(x₁ x₂)` is not an automorphism. Compound
automorphisms across bands are not constructed in any
existing file.

---

## 6. What would close it (and at what cost)

### 6a. Compound-automorphism infrastructure (~300-500 LoC)

The minimum infrastructure for a structural close of the K=2
regime is roughly:

1. **Compound-automorphism constructor** (~80-150 LoC). Given a
   layered decomposition with two same-band pairs
   `(a₁, a₂) ⊆ M_i` and `(b₁, b₂) ⊆ M_j` such that the matching
   `a_k ↔ b_k` extends to a poset automorphism, build the
   compound `Equiv.swap` and prove it preserves `≤`. Analogous to
   `BipartiteEnum.lean:105-193`'s `swap_preserves_le` but
   handling two simultaneous orbits with the matching
   compatibility condition. New file, plausibly
   `Step8/CompoundSwap.lean`.

2. **Structural matching lemma** (~100-200 LoC). Show every K=2
   irreducible `w ≥ 1` `|β| ≥ 3` layered configuration with no
   within-band ⪯-pair admits such a matching. This is a finite
   combinatorial fact about subsets of `bandSet 2` indexed by
   `bandSet 1`; the matching is the bijection induced by some
   automorphism of the bipartite incidence structure. Either
   case-split or finite enumeration over isomorphism classes
   (the bipartite incidence patterns on `|A|, |B| ∈ {1, 2, 3}`).

3. **Generalised dispatch head** (~50-100 LoC). Replace
   `bipartite_balanced_enum`'s `hAB`-dependent argument with a
   three-way dispatch: Case 1 (ambient match) inline; Case 2
   (within-band ⪯-pair) via `case2Witness_balanced_under_FKG`;
   Case 3 (compound automorphism) via the new infrastructure.

This is option (α) + (γ') in pc-94fd's terminology. Total cost
~230-450 LoC of strictly new content (i.e., none of it overlaps
with what mg-a735 / mg-7f06 / mg-27c2 / mg-2e58 / mg-26bb
already provide).

### 6b. K=2 finite enumerator alternative (~300-500 LoC)

A more conservative route is a Bool certificate analogous to
F5a's `case3_certificate`, but for `K = 2`, `|α| ≤ 6`,
`w ∈ {1, 2, 3, 4}`. The K=2 + width-3 + bounded-cardinality
isomorphism classes are finite and machine-enumerable.
Estimated 300-500 LoC including the certificate, the
Bool→Prop bridge analogous to mg-26bb, and the dispatch wiring.

This route trades structural insight for raw enumeration; it
also requires extending the inScope discharge / certificate
pipeline to a second `(K = 2)` profile. Either route closes
the gap; the structural route is more re-usable downstream
(compound automorphisms appear in other Step-8 case analyses
that were elided in the current proof).

### 6c. What the cleanup would look like once closed

Assume the K=2 regime is closed by either route. Then the
remaining work is the **planned** items from mg-072c / mg-0fa0
that never got attempted:

* F3 step proof (K=1 base + K=2 dispatch via the new closure
  + K≥3 dispatch via reducible/irreducible split). Estimated
  150-250 LoC.
* Five caller obligations of
  `bounded_irreducible_balanced_inScope`, all unblocked by
  mg-9568 (each becomes a small composition). Estimated
  50-100 LoC.
* Promote `Case3Witness` from def to theorem
  (`LayeredBalanced.lean:419`). Estimated ~10 LoC.
* Drop `hC3` from `width3_one_third_two_thirds`, add the
  chain-form `hFKG : Step8.InSitu.Case2FKGSubClaim L`, and
  re-route the discharge through the new theorem. Estimated
  30-50 LoC.

Hard gate at the end: `#print axioms width3_one_third_two_thirds`
shows exactly the unchanged baseline (the mathlib trio +
`brightwell_sharp_centred` + `case3Witness_hasBalancedPair_outOfScope`).
The chain-form FKG sub-claim must remain a HYPOTHESIS, not a new
project axiom.

Total once the K=2 piece lands: ~240-410 LoC of routine
formalization on top of ~300-500 LoC of new infrastructure.

---

## 7. When to re-attempt Path C cleanup

Path C cleanup is parked, not abandoned. A future revival is
worth attempting if **any** of the following becomes true:

* **Compound-automorphism mathlib infrastructure lands.** If
  mathlib gains a generic `MultiOrbit.swap_preserves_le`-style
  constructor (e.g., for products of disjoint transpositions
  acting on a `PartialOrder` via a structural compatibility
  condition), §6a item #1 collapses from ~80-150 LoC to a
  small wrapper.
* **A finite-enumeration framework for K=2 layered isomorphism
  classes lands** (analogous to F5a's
  `Case3Enum/Certificate.lean` pipeline but for K=2). §6b
  becomes mostly a code-gen exercise.
* **An external collaborator with deep Step-8 expertise has a
  1-2 week focused arc to invest** — the per-round polecat
  pattern broke down because each round surfaced new
  blockers under the polecat's per-session budget. A focused
  multi-week pass could thread all five infrastructure pieces
  + the K=2 closure + the headline rewrite together with
  enough head-room to absorb mid-arc surprises.
* **The chain-form FKG sub-claim itself is discharged**
  (`Mathlib/RelationPoset/FKG.lean §11`, "Route B" of the
  original four-option matrix). At that point the chain-form
  `hFKG` hypothesis can be silently dropped from the headline
  (it discharges by Route B's theorem), and Path C cleanup
  becomes a closure rather than a hypothesis swap.
* **The 1/3-2/3 conjecture for layered width-3 chains
  is proved** (the open mathematical question that motivates
  everything downstream). If it is provable in tree, the chain
  swap argument supplies the missing lower bound and the
  StrictCase2 closure becomes unconditional.

If a future polecat is commissioned to revisit, they should:

1. Re-read this roadmap first.
2. Confirm `mg-5f0c` is still shelved (`mg show mg-5f0c` —
   the original mg-b329 successor that would have done the
   wiring; preserved by mayor's call as the natural revival
   point).
3. Verify the six infrastructure commits are still in tree
   (`git log --oneline | grep -E "(mg-9568|mg-7f06|mg-a735|mg-27c2|mg-2e58|mg-26bb)"`).
4. Pick option (α) or option (γ') from §6 based on the then-
   current state of mathlib's compound-automorphism support.
5. Budget for at least 1-2 weeks of focused work; do not attempt
   in a single polecat session. The arc demonstrated that
   single-session attempts surface unforeseen blockers at every
   round.

---

## 8. The five status docs (detailed engineering record)

Each status doc is the block-and-report deliverable from one
polecat session. They remain in place as the in-depth record of
what was tried, what was found, and what infrastructure surfaced.
This roadmap is the navigation entry point; the status docs are
the source material.

* **`docs/a8-s2-strict-witness-status.md`** (mg-43f3, `e6ce389`)
  — pc-43f3's FKG-only contingency analysis. Pins the
  StrictCase2 closure to the chain-form `m=3` shape. Round-1
  prelude.
* **`docs/a5-g3e-fkg-route-status.md`** (mg-4a5b, `72cd563`) —
  pc-4a5b's first audit. Identifies the F3 framework, Lower/Upper
  lifts, and chain-form FKG closure as missing. Round 2.
* **`docs/a5-g3e-path-c-wiring-v3-status.md`** (mg-072c,
  `b35949e`) — pc-072c's audit after rounds 1-2 deps land.
  Surfaces Window-OrdinalDecomp + outer allBalanced bridge.
  Round 3.
* **`docs/a5-g3e-path-c-wiring-v4-status.md`** (mg-0fa0,
  `4034fa1`) — pc-0fa0's audit after the round-3 deps land.
  Surfaces the K=2 + irreducible + w≥1 + |β|≥3 regime as the
  third tier of new blockers. Triggers strategic revisit.
  Round 4.
* **`docs/a5-g3e-path-c-wiring-v5-status.md`** (mg-94fd,
  `2579db7`) — pc-94fd's audit of the option (γ) plan. Reports
  the rotation argument cannot extend (operates on within-band
  ⪯-pairs/chains; N-poset has no within-band ⪯-pair); compound
  automorphism is the structural fact missing. Triggers firm
  round-4 stop-loss → option (δ) park. Round 5.

The five docs share a common idiom (each names what it tried,
what it found missing, why it cannot be silently worked around,
and what the indicated next step is). Reading them in order
gives the inside view; reading this roadmap gives the outside
view.

---

## 9. Why option (δ) and not another round

PM call documented in mail to mayor 2026-04-27 (post-pc-94fd
stop-loss). The round-4 firm clause was pre-committed in
mg-94fd's brief: "if mg-94fd block-and-reports with new tier-4
blockers, PM pivots to option (δ) park." pc-94fd's audit was
clean: rotation argument fundamentally doesn't apply to the
N-poset class (no within-band ⪯-pair exists for those
configurations); a different mathematical tool (compound
automorphisms) is needed; that's substantively new math, not an
audit gap. The honest cost is ~300-500+ LoC of structural
infrastructure that does not exist in the tree today.

The four rounds shipped six substantive code commits of
generally-useful infrastructure (mg-9568, mg-7f06, mg-a735,
mg-27c2, mg-2e58, mg-26bb) plus five careful gap-analysis status
docs. That is the dividend; the headline cleanup is the cost we
are not paying further at this time.

The decision is reversible. `mg-5f0c` (the shelved Path C
wiring v5 ticket) remains shelved (not closed); a future
revival can `mg unshelve mg-5f0c` and use it as the wiring
target after the compound-automorphism infrastructure lands.
The cancel-pair `c5d5a10` + `mg-05d3` revert is preserved on
main as the audit trail and negative exemplar.

---

## 10. References (code anchors)

Headline targets:

* `lean/OneThird/MainTheorem.lean:38-43` —
  `width3_one_third_two_thirds`, the headline that retains
  `hC3` under option (δ).
* `lean/OneThird/Step8/LayeredBalanced.lean:419` —
  `Case3Witness` def (would have been promoted to a theorem
  under cleanup).

Infrastructure that landed during the arc:

* `lean/OneThird/Step8/LayerOrdinal.lean:472` —
  `hasBalancedPair_of_layered_strongInduction_width3` (mg-a735).
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1227`,
  `:1237` — `hasBalancedPair_lift_lower` / `_upper` (mg-7f06).
* `lean/OneThird/Step8/Case2Rotation.lean:870`, `:894` —
  `strictCase2Witness_balanced_under_FKG` /
  `case2Witness_balanced_under_FKG` (mg-27c2).
* `lean/OneThird/Step8/WindowDecomp.lean:375` —
  `OrdinalDecomp.windowOfPairAt` (mg-2e58).
* `lean/OneThird/Step8/Case3Enum/AllBalancedBridge.lean:218` —
  `allBalanced_imp_enumPosetsFor` (mg-26bb).

Existing handlers that exclude the K=2 + w≥1 + |β|≥3 regime:

* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1660` —
  `bounded_irreducible_balanced_hybrid` (`3 ≤ L.K`).
* `lean/OneThird/Step8/Case3Residual.lean:208` —
  `case3Witness_hasBalancedPair_outOfScope` axiom (`3 ≤ L.K`).
* `lean/OneThird/Step8/Case2BipartiteBound.lean:197` —
  `hasBalancedPair_of_K2_w0_incomp` (`L.w = 0` only).
* `lean/OneThird/Step8/BipartiteEnum.lean:105-193` —
  `swap_preserves_le`, the `hAB`-dependent symmetry argument.

Predicates and dispatch:

* `lean/OneThird/Step8/Case3Dispatch.lean:156` —
  `Case2Witness L`.
* `lean/OneThird/Step8/Case3Dispatch.lean:176` —
  `Case3Witness L` (the bin the N-poset lands in).
* `lean/OneThird/Step8/LayerOrdinal.lean:240` —
  `LayerOrdinalIrreducible L`.
* `lean/OneThird/Step8/LayeredReduction.lean:96` —
  `LayeredDecomposition` structure.
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:407-426` —
  Route B (probability-normalised cross-poset FKG) future
  work, the alternative route to discharging the chain-form
  FKG sub-claim.

Audit trail:

* `git show c5d5a10` — the original mg-b329 partial wiring
  with multi-hypothesis `hStep` (rejected as the negative
  exemplar).
* `git show 2cd6bd5` (mg-05d3) — the revert that restored
  `hC3` after c5d5a10's rejection.
* `mg show mg-5f0c` — the shelved successor ticket; revival
  point if cleanup is re-attempted.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current `#print axioms`
  baseline (this docs-only commit does not change it).
