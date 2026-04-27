# A5-G3e Path C wiring v4 — block-and-report

**Work item:** `mg-0fa0` (Path C wiring v4 — F3 step + 5
inScope obligations + headline drop-`hC3` / add-`hFKG`,
replacing `mg-072c`).

**Status:** **blocked** — the 1-for-1 hypothesis swap (drop
`hC3`, add a single chain-form `hFKG`) cannot close in a single
polecat session even with the FIVE infrastructure dependencies
landed (`mg-a735` F3 framework, `mg-7f06` Lower/Upper lifts,
`mg-27c2` StrictCase2 chain-form FKG closure, `mg-2e58` Window
OrdinalDecomp constructor, `mg-26bb` allBalanced bridge). A
**third-tier** blocker — the **`K = 2` irreducible width-3
regime** — surfaces during the F3 step's promotion of
`Case3Witness` from def to theorem and is **not derivable from
the in-tree infrastructure**.

Mailing mayor + pm-onethird per the task body's **Hard
block-and-report rule**. Per pm-onethird's stop-loss rule: this
is the third round of new blockers, triggering the strategic
revisit of the four-option matrix.

**Author:** `pc-0fa0` polecat, 2026-04-27.

---

## TL;DR

The `mg-0fa0` task asks for the universal `Case3Witness`
predicate to be promoted from a hypothesis to a theorem. The
predicate's universal scope is

```
∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : LayeredDecomposition β),
    HasWidthAtMost β 3 → ¬ IsChainPoset β →
    2 ≤ Fintype.card β → HasBalancedPair β
```

— uniformly across **all** `(β, LB)` pairs. Discharging the
universal claim requires a step proof that handles every value
of `LB.K`, including **`K = 2` with all bands non-empty and
interaction width `w ≥ 1`**. This regime is reachable at
`(β, LB)` where `|β| ≥ 3` and `LB.K = 2` (e.g.
`bandSet 1 = {x, y}`, `bandSet 2 = {z}`).

The in-tree infrastructure does not cover this regime:

* `bounded_irreducible_balanced_hybrid`
  (`BoundedIrreducibleBalanced.lean:1660`) **requires `3 ≤ L.K`**.
* `case3Witness_hasBalancedPair_outOfScope` axiom
  (`Case3Residual.lean:208`) **requires `3 ≤ L.K`**.
* `Case2BipartiteBound.lean`'s `hasBalancedPair_of_K2_w0_incomp`
  (line 197) **requires `L.w = 0`**.

The window-localization descent (mg-2e58's
`OrdinalDecomp.windowOfPairAt`) collapses to the degenerate
`Mid = α` case when `L.K = 2` and `w ≥ 1`: every valid lower
cutoff `≥ 2` would require an empty band-1 (which contradicts
non-emptiness from irreducibility), and every valid upper cutoff
`≤ 1` would require an empty band-2.

The reducibility descent does not apply either: `K = 2`
irreducible by definition has no reducibility witness at the
single available band-cut `k = 1`.

Hence `K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3` is a real,
unaccounted-for case. Without new infrastructure, the F3 step
function cannot close the universal `Case3Witness` claim.

The cost-to-close estimate of mg-0fa0's task body
(`230-400 LoC`) **did not include** this regime; the v3 audit
(`docs/a5-g3e-path-c-wiring-v3-status.md`) and the v2
(pc-4a5b's) audit both missed it.

---

## 1. What `mg-0fa0` asks for

Per the task body:

> 1. F3 step proof — K = 1 base + K ≥ 2 dispatch +
>    bounded-hybrid wiring (~150-250 LoC).
> 2. Discharge the 5 caller obligations of
>    `bounded_irreducible_balanced_inScope` (~50-100 LoC).
> 3. Promote `Case3Witness` from a def to a theorem
>    (`LayeredBalanced.lean:419`).
> 4. Drop `hC3` from `width3_one_third_two_thirds`.
> 5. Add **EXACTLY ONE** new hypothesis: chain-form `hFKG`
>    (matching mg-27c2's `Case2FKGSubClaim L`).

Hard gate: `#print axioms width3_one_third_two_thirds` after
wiring shows the unchanged baseline (mathlib trio +
`brightwell_sharp_centred` +
`case3Witness_hasBalancedPair_outOfScope`). FKG sub-claim is a
**HYPOTHESIS**, not an axiom.

Hard block-and-report rule: do **not** silently accept a
multi-hypothesis variant.

---

## 2. Inventory: what is in tree (and what is missing)

### 2a. Now in tree (✓) — the dependency chain

* **F3 width-3 strong-induction framework** (`mg-a735`, commit
  cecd709). `hasBalancedPair_of_layered_strongInduction_width3`
  with `HasWidthAtMost · 3` threaded through both the call site's
  input and the IH (`LayerOrdinal.lean:472`).
* **Lower / Upper `hasBalancedPair_lift` constructors**
  (`mg-7f06`, commit 76adc5e).
  `OrdinalDecomp.hasBalancedPair_lift_lower` and `_upper`, via
  the `toMidOfLower` / `toMidOfUpper` repackaging
  (`Mathlib/LinearExtension/Subtype.lean:1227`,`:1237`).
* **StrictCase2 chain-form FKG closure** (`mg-27c2`, commit
  38d1013). `Case2FKGSubClaim L` (the bundled `m=2` pair +
  `m=3` chain hypothesis), `strictCase2Witness_balanced_under_FKG`,
  and `case2Witness_balanced_under_FKG` — the
  `Case2Witness L → HasBalancedPair α` form consumed by
  `hStruct_of_case2_discharge` (`Case2Rotation.lean:870`,`:894`).
* **Window `OrdinalDecomp` constructor** (`mg-2e58`, commit
  419cb35). `OrdinalDecomp.windowOfPairAt L x y` produces an
  `OrdinalDecomp α` whose `Mid` contains both `x` and `y`,
  using maximal-`B_lo` / minimal-`B_hi` valid cutoffs
  (`WindowDecomp.lean:375`).
* **`allBalanced → enumPosetsFor` outer-loop bridge**
  (`mg-26bb`, commit 0550d2f). `allBalanced_imp_enumPosetsFor`
  unrolls the F5a Bool certificate's outer `for bs in
  bandSizesGen 3 sizeLimit` loop into the per-`bs` consequence
  (`Case3Enum/AllBalancedBridge.lean:218`).

### 2b. Identified by mg-0fa0 but not in tree (the planned work)

* **F3 step proof** — the K = 1 / K = 2 / K ≥ 3 dispatch in
  the strong-induction step. ~150-250 LoC per the task body.
* **5 caller obligations** of
  `bounded_irreducible_balanced_inScope`. ~50-100 LoC.
* **Headline wiring** at `MainTheorem.lean`. ~30-50 LoC.
* **`Case3Witness` promotion** to a theorem. ~10 LoC.

These are the items mg-0fa0 is scoped to.

### 2c. NOT in tree, NOT identified by mg-0fa0 (the new blocker)

* **`K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3` regime**. See
  §3 below.

---

## 3. Blocker: `K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3`

### 3a. What we need

The promoted `Case3Witness` theorem must close

```
∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : LayeredDecomposition β),
    HasWidthAtMost β 3 → ¬ IsChainPoset β →
    2 ≤ Fintype.card β → HasBalancedPair β
```

uniformly. The strong-induction step function therefore has to
handle `(β, LB)` for every value of `LB.K`.

For `LB.K = 1`: direct via `bipartite_balanced_enum` with
`A = univ`, `B = ∅` (the single antichain band).

For `LB.K ≥ 3`: F3 reducible/irreducible dispatch lands in
either the descent branches or the `bounded_irreducible_balanced_hybrid`
leaf.

For `LB.K = 2`:
* If reducible at `k = 1`: descend via
  `OrdinalDecompOfReducible` to `Lower = bandSet 1`,
  `Upper = bandSet 2`. Apply IH to one of the strictly smaller
  pieces, then lift via the new `hasBalancedPair_lift_lower` /
  `_upper`.
* **If irreducible**: stuck — see §3b.

### 3b. Why `K = 2` + irreducible + `w ≥ 1` is uncovered

**Window descent collapses.** The mg-2e58 constructor
`OrdinalDecomp.windowOfPairAt L x y` produces cutoffs
`B_lo := lowerCutoff L (min (band x) (band y))` and
`B_hi := upperCutoff L (max (band x) (band y))`.

* For `L.K = 2`, the only band indices are `1` and `2` (by
  `band_pos`/`band_le`), and both are non-empty (otherwise the
  reducibility hypothesis at `k = 1` is vacuously satisfied,
  contradicting irreducibility).
* `B_lo` has range `1, 2`. `B_lo = 2` is invalid for `w ≥ 1`:
  `IsValidLowerCutoff L 2` requires no `z` with `band z ∈
  [2 - w, 2)` — but for `w ≥ 1`, `[2 - w, 2)` includes `1`,
  and `bandSet 1` is non-empty.
* Symmetrically, `B_hi = 1` is invalid for `w ≥ 1`.
* The only valid cutoff pair is `B_lo = 1`, `B_hi = 2`,
  yielding `Lower = ∅`, `Mid = α`, `Upper = ∅` — the
  degenerate decomposition with no descent.

**No reducibility descent.** `LayerOrdinalIrreducible` at
`K = 2` excludes the only available band-cut (`k = 1`).

**No bounded-irreducible-balanced leaf.** Both the
`bounded_irreducible_balanced_hybrid` theorem
(`BoundedIrreducibleBalanced.lean:1660`) and the
`case3Witness_hasBalancedPair_outOfScope` axiom
(`Case3Residual.lean:208`) hard-code `3 ≤ L.K` in their
hypothesis profile.

Hence the `K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3` regime
has no in-tree handler. The F3 step cannot close it.

### 3c. Why mg-0fa0's audit missed this

The mg-0fa0 task body (and the v3 status doc it builds on)
focused on the C1 window descent and on the inScope leaf's
five obligations. Both audits implicitly assumed the F3 step
either descends or routes through
`bounded_irreducible_balanced_hybrid`. The K = 2 case sits
between these — it admits no descent and is excluded from the
hybrid leaf — but neither audit walked through the full
`L.K ∈ {1, 2, 3, …}` enumeration of step-function branches at
the universally-quantified `Case3Witness` shape.

The earlier wirings (`mg-072c` / `mg-4a5b`) did not surface
this either: at those points, `Case3Witness` was a hypothesis,
so the `K = 2` discharge happened "outside the formalization".
Promoting it to a theorem moves the discharge inside, where the
gap becomes structural.

### 3d. Possible workarounds (none in scope for this ticket)

* **Restrict `Case3Witness`'s scope.** Tighten the predicate to
  `K ≥ 3 ∨ |β| ≤ 2` and handle `K = 2` + `|β| ≥ 3` in
  `lem_layered_balanced` directly. But `lem_layered_balanced`'s
  recursion through `Case3Witness` would still face the same
  `K = 2` gap on sub-posets reached through window
  restriction; the gap moves but is not closed.
* **Extend `case3Witness_hasBalancedPair_outOfScope` to `K = 2`.**
  Adds a new hypothesis to the project axiom (or splits it into
  two). Either change moves
  `#print axioms width3_one_third_two_thirds` away from the
  baseline, violating the hard gate.
* **K = 2 + irreducible + width-3 finite enumeration.** Build a
  fresh enumerator analogous to `case3_certificate` but for
  `K = 2`, covering `|α| ≤ 6` and `w ∈ {1, 2, 3, 4}`. ~300-500
  LoC of new infrastructure in a separate work item.
* **`bipartite_balanced_enum` extension to non-directed
  bipartite.** The current bipartite enumeration requires
  `hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b`; the K = 2 irreducible case
  has cross-band incomparable pairs. Generalising the enum to
  drop `hAB` would re-derive the rotation argument with a
  cross-band variant. ~150-300 LoC of FKG-flavoured work.
* **Strengthen `(L2)` to upward-strict in
  `LayeredDecomposition`.** Same caveat as v3 audit §3c: a
  one-time downstream rewrite, deviating from the paper's
  encoding.

Each workaround is a multi-day infrastructure ticket.

---

## 4. Cost estimate (revised)

| Piece | LoC | Status |
| --- | ---:| --- |
| width-3-threaded F3 framework | 100-150 | DONE (mg-a735) |
| Lower/Upper lifts | 50-100 | DONE (mg-7f06) |
| StrictCase2 chain-form FKG closure | 100-200 | DONE (mg-27c2) |
| Window-OrdinalDecomp constructor | 80-150 | DONE (mg-2e58) |
| `allBalanced → enumPosetsFor` outer bridge | 50-100 | DONE (mg-26bb) |
| F3 step proof (K=1 + K=2 + K≥3) | 150-250 | TODO (mg-0fa0) |
| 5 inScope caller obligations | 50-100 | TODO (mg-0fa0) |
| Headline wiring at `MainTheorem.lean` | 30-50 | TODO (mg-0fa0) |
| **`K = 2` irreducible width-3 regime (NEW)** | **150-500** | NEW BLOCKER |
| **mg-0fa0 remaining total** | **380-900** | spread across 4-7 files |

The new blocker adds ~150-500 LoC depending on the chosen
workaround. Combined with the elaborator / universe / typeclass
risk from cross-cutting changes to `lem_layered_balanced` /
`mainTheoremInputsOf` / `width3_one_third_two_thirds`, this is
beyond what one polecat session can land cleanly.

---

## 5. Why I am not silently accepting a workaround

The task body's **Hard block-and-report rule**:

> If the polecat finds it cannot close without adding additional
> hypotheses (the option-(b) failure mode that produced the
> rejected c5d5a10 commit), STOP. Mail mayor + pm-onethird per
> the standard block-and-report protocol. Do **NOT** silently
> accept a multi-hypothesis variant.

The viable single-session workarounds all violate this rule:

* **Add a `K = 2` discharge as a hypothesis.** Threading
  `hK2dispatch : ∀ β [...] (LB : LayeredDecomposition β),
  HasWidthAtMost β 3 → ¬ IsChainPoset β → 2 ≤ Fintype.card β →
  LB.K = 2 → HasBalancedPair β` re-creates the c5d5a10
  multi-hypothesis failure mode under a different name.
* **Axiomatize the missing case.** The hard gate
  (`#print axioms` unchanged from baseline) explicitly forbids
  new axioms.
* **Partial code changes** to `width3_one_third_two_thirds`
  that fail to compile, or that drop `hC3` while leaving a
  stub `sorry`. Would not pass the "builds clean. No new sorry
  / admit / axioms" gate.
* **Restrict `Case3Witness` to `K ≥ 3 ∨ |β| ≤ 2`.** Moves the
  gap to `lem_layered_balanced` without closing it; sub-posets
  reached through window restriction can still hit `K = 2` +
  `|β| ≥ 3`.

---

## 6. Stop-loss trigger: strategic revisit (per pm-onethird)

Per the task body:

> If THIS ticket also block-and-reports with a third tier of new
> blockers, that is the signal to revisit the strategic call
> (option (i) FKG-hypothesis path vs option (ii) Route B vs
> option (iii) prove-the-conjecture). Two rounds of "new
> infrastructure surfacing" is the limit before re-evaluating;
> we accept one (mg-072c → mg-2e58/mg-26bb) but not two.

The blocker history:

* **Round 1** (mg-4a5b → mg-072c): pc-4a5b's audit identified
  `mg-a735` (F3 framework), `mg-7f06` (Lower/Upper lifts),
  `mg-27c2` (StrictCase2 closure) as missing. All three landed.
* **Round 2** (mg-072c → mg-0fa0): pc-072c's audit identified
  `mg-2e58` (Window-OrdinalDecomp), `mg-26bb` (allBalanced
  bridge) as missing. Both landed.
* **Round 3** (mg-0fa0 → ?): pc-0fa0's audit (this doc)
  identifies `K = 2` + irreducible + `w ≥ 1` + `|β| ≥ 3` as
  missing. Strategic revisit triggered.

This is the third round. Per the stop-loss rule, the four-option
matrix should now be revisited before further single-session
attempts at Path C wiring.

---

## 7. What I am doing

* **Writing this status doc** as the block-and-report deliverable,
  matching the precedent of `docs/a5-g3e-path-c-wiring-v3-status.md`
  (pc-072c), `docs/a5-g3e-fkg-route-status.md` (pc-4a5b), and
  `docs/a8-s2-strict-witness-status.md` (pc-43f3).
* **Mailing mayor + pm-onethird** with summary + this doc
  reference, and explicitly flagging the stop-loss trigger.
* **NOT axiomatizing** any K = 2 dispatch.
* **NOT making partial code changes** to
  `width3_one_third_two_thirds` (those would either fail to
  compile or silently introduce extra hypotheses).
* **NOT adding new fields** to the headline (no
  multi-hypothesis variant).
* **NOT exiting**; standing by for guidance.

---

## 8. Suggested follow-up directions (for pm-onethird)

These are options for the strategic revisit; they are not
recommendations:

* **Option (α): Multi-step ticket sequence** (continuing the
  Path C decomposition).
  * `mg-0fa0-a` — `K = 2` + irreducible + width-3 finite
    enumerator (Bool certificate analogous to
    `case3_certificate` but for `K = 2`, `|α| ≤ 6`,
    `w ∈ {1, 2, 3, 4}`).
  * `mg-0fa0-b` — F3 step proof + inScope obligations +
    headline wiring (the original mg-0fa0, now closeable).
* **Option (β): Strengthen `(L2)`** to upward-strict in
  `LayeredDecomposition` — would unblock the Window descent at
  `K = 2`, `w ≥ 1`. Caveat: deviates from the paper's
  encoding.
* **Option (γ): Generalise `bipartite_balanced_enum`** to drop
  the `hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b` hypothesis. Closes
  `K = 2` + irreducible directly. Requires extending the
  rotation argument across cross-band incomparable pairs.
* **Option (δ): Park the option-(i) FKG-hypothesis path.** Keep
  the current `hC3` shape permanently and accept that
  `case3Witness_hasBalancedPair_outOfScope` axiomatization is
  the residual closure. The headline retains `hC3` and never
  acquires `hFKG`.
* **Option (ε): Pivot to option (ii) Route B** of the original
  four-option matrix (the structural Case 2 / Case 3 dispatch
  via residual configurations rather than the
  `Case2FKGSubClaim L` route). Requires re-deriving the
  Case 2 closure without the `m = 2 / m = 3` chain-form
  bundling.
* **Option (ζ): Pivot to option (iii) prove-the-conjecture** —
  attempt the original 1/3-2/3 conjecture at the source,
  bypassing the layered cascade entirely. Far the most
  speculative.

---

## 9. References

* Polecat instructions: `mg-0fa0` task body.
* `docs/a5-g3e-path-c-wiring-v3-status.md` (mg-072c) —
  pc-072c's audit; cost estimate §3 underspecifies the
  `K = 2` regime.
* `docs/a5-g3e-fkg-route-status.md` (mg-4a5b) — pc-4a5b's
  original audit.
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — pc-43f3's
  block-and-report on the StrictCase2 closure (now resolved by
  mg-27c2).
* `git show c5d5a10` (reverted via mg-05d3) — the negative
  exemplar (multi-hypothesis hStep at the headline).
* `lean/OneThird/MainTheorem.lean:38-43` — wiring target.
* `lean/OneThird/Step8/LayeredBalanced.lean:419` —
  `Case3Witness` def to be promoted to theorem.
* `lean/OneThird/Step8/Case3Residual.lean:208` —
  `case3Witness_hasBalancedPair_outOfScope` axiom (`3 ≤ L.K`).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1660` —
  `bounded_irreducible_balanced_hybrid` (`3 ≤ L.K`).
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean` —
  the inScope leaf with the 5 caller obligations.
* `lean/OneThird/Step8/WindowDecomp.lean:375` —
  `OrdinalDecomp.windowOfPairAt` (collapses to degenerate at
  `K = 2`, `w ≥ 1`).
* `lean/OneThird/Step8/Case2BipartiteBound.lean:197` —
  `hasBalancedPair_of_K2_w0_incomp` (`L.w = 0` only).
* `lean/OneThird/Step8/LayerOrdinal.lean:472` —
  `hasBalancedPair_of_layered_strongInduction_width3`.
* `lean/OneThird/Step8/Case2Rotation.lean:870` —
  `strictCase2Witness_balanced_under_FKG`.
* `lean/OneThird/Step8/Case2Rotation.lean:894` —
  `case2Witness_balanced_under_FKG`.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1227` —
  `OrdinalDecomp.hasBalancedPair_lift_lower`.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1237` —
  `OrdinalDecomp.hasBalancedPair_lift_upper`.
* `lean/OneThird/Step8/Case3Enum/AllBalancedBridge.lean:218` —
  `allBalanced_imp_enumPosetsFor`.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (this
  docs-only commit does not change it).
