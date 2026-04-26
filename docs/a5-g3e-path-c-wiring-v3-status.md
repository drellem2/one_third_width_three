# A5-G3e Path C wiring v3 — block-and-report

**Work item:** `mg-072c` (Path C wiring v3 — F3 step proof + headline
drop-`hC3` / add-`hFKG`, replacing `mg-4a5b`).

**Status:** **blocked** — the 1-for-1 hypothesis swap (drop `hC3`,
add a single chain-form `hFKG`) cannot close in a single polecat
session even with the three infrastructure dependencies
(`mg-a735`, `mg-7f06`, `mg-27c2`) landed. Mailing mayor +
pm-onethird per the task body's **Hard block-and-report rule**.

**Author:** `pc-072c` polecat, 2026-04-27.

---

## TL;DR

`mg-4a5b`'s pc-4a5b status doc (`docs/a5-g3e-fkg-route-status.md`,
commit 72cd563) identified five missing pieces. Three are now in
tree (`mg-a735`, `mg-7f06`, `mg-27c2`). Two further pieces — neither
called out in the cost estimate — surface during the F3 step
implementation and are **not derivable from the in-tree
infrastructure**:

1. **Window-OrdinalDecomp constructor** (Case C1 of the F3
   irreducible branch). The `windowLocalization` lemma
   (`LayeredBalanced.lean:103`) is a placeholder probability
   identity — it does **not** produce an `OrdinalDecomp α` whose
   `Mid` is the window. A fresh constructor would have to derive
   `Lower < Mid` and `Mid < Upper` from `(L2-forced)`, which
   requires a strict band-distance gap of `> w`. With the natural
   window `[min(i,j) − w, max(i,j) + w]`, the boundary cases
   (`band z = max(i,j) + w + 1`, `band w' = max(i,j) + w`,
   `|band z − band w'| = 1 ≤ w` for `w ≥ 1`) violate `(L2-forced)`'s
   strict separation. A wider window (e.g.,
   `[min(i,j) − 2w, max(i,j) + 2w]` with the buffer outside) would
   either fail the `|W| ≤ 3(3w + 1)` size bound used by F5 or push
   into different infrastructure.

2. **`allBalanced w sizeLimit = true` → `enumPosetsFor w bs = true`
   for `bs ∈ bandSizesGen 3 sizeLimit`** (`h_certificate` discharge
   inside the inScope obligations). The F5a Bool certificate
   (`Step8.Case3Enum.case3_certificate`) asserts
   `allBalanced w sizeLimit = true` for `(w, sizeLimit) ∈
   {(1,9), (2,7), (3,7), (4,7)}`, but `allBalanced` is an `Id.run
   do for-loop` over `bandSizesGen 3 sizeLimit`. There is **no
   in-tree** outer-loop Bool→Prop bridge analogous to
   `enumPosetsFor_iter_balanced` (`mg-b487`). Building one would be
   a separate ~50-100 LoC inductive argument over the for-loop
   state.

Without (1), the F3 step proof's irreducible branch cannot descend
on unbounded irreducible width-3 posets (the `K ≥ 2`,
`|α| > 6w + 6` regime). Without (2), the `bounded_irreducible_balanced_inScope`
caller obligations cannot be discharged from F5a's certificate.

The cost estimate in pc-4a5b's status doc (§3) correctly identified
the F3 step as `150-250 LoC` and the inScope obligations as
`50-100 LoC`, but it **did not include** these two pieces, which
together add roughly 150-250 LoC on top.

Per the task body's **Hard block-and-report rule** ("If the polecat
finds it cannot close without adding additional hypotheses … STOP.
Mail mayor + pm-onethird per the standard block-and-report
protocol"), I am surfacing this rather than silently reverting to a
multi-hypothesis variant.

---

## 1. What `mg-072c` asks for

Per the task body:

> 1. Write the F3 step proof — K = 1 base + K ≥ 2 dispatch +
>    bounded-hybrid wiring (~150-250 LoC per pc-4a5b's audit).
> 2. Discharge the 5 caller obligations of
>    `bounded_irreducible_balanced_inScope` (all unblocked by
>    mg-9568; ~50-100 LoC of composition).
> 3. Promote `Case3Witness` from a def to a theorem
>    (`LayeredBalanced.lean:419`).
> 4. Drop `hC3` from `width3_one_third_two_thirds`.
> 5. Add **EXACTLY ONE** new hypothesis: the chain-form `hFKG` (the
>    exact shape consumed by mg-27c2's StrictCase2 closure).

Hard gate: `#print axioms width3_one_third_two_thirds` after wiring
shows the unchanged baseline (mathlib trio + `brightwell_sharp_centred`
+ `case3Witness_hasBalancedPair_outOfScope`). FKG sub-claim is a
**HYPOTHESIS**, not an axiom.

Hard block-and-report rule: do **not** silently accept a
multi-hypothesis variant (the c5d5a10 failure mode).

---

## 2. Inventory: what is in tree (and what is missing)

### 2a. Now in tree (✓) — the dependency chain

* **Width-3-threaded F3 framework** (`mg-a735`, commit cecd709).
  `Step8.hasBalancedPair_of_layered_strongInduction_width3` and the
  `_le` corollary, with `HasWidthAtMost · 3` threaded through both
  the call site's input and the IH.
* **Lower / Upper `hasBalancedPair_lift` constructors** (`mg-7f06`,
  commit 76adc5e). `OrdinalDecomp.hasBalancedPair_lift_lower` and
  `_upper`, via the `toMidOfLower` / `toMidOfUpper` repackaging.
* **StrictCase2 closure under chain-form FKG** (`mg-27c2`, commit
  38d1013). `Case2FKGSubClaim L` (the bundled `m=2` pair + `m=3`
  chain hypothesis), `strictCase2Witness_balanced_under_FKG`, and
  `case2Witness_balanced_under_FKG` (the composed
  `Case2Witness L → HasBalancedPair α` form, exactly the shape
  consumed by `hStruct_of_case2_discharge`).

### 2b. Identified by pc-4a5b but not in tree (the planned work)

* **F3 step proof** — the K = 1 / K ≥ 2 dispatch in
  `hStep` form. ~150-250 LoC per pc-4a5b's estimate.
* **5 caller obligations** of
  `bounded_irreducible_balanced_inScope`. ~50-100 LoC.
* **Headline wiring** at `MainTheorem.lean`. ~30-50 LoC.

These are the items mg-072c is scoped to.

### 2c. NOT in tree, NOT identified by pc-4a5b (the new blockers)

* **Window-OrdinalDecomp constructor** (Case C1 of F3 irreducible
  branch). See §3 below.
* **`allBalanced → enumPosetsFor` outer-loop bridge** (h_certificate
  discharge). See §4 below.

---

## 3. Blocker A: Window-OrdinalDecomp constructor

### 3a. What we need

The F3 strong-induction step function has shape

```
hStep : ∀ α [...] (L : LayeredDecomposition α),
  HasWidthAtMost α 3 → 2 ≤ Fintype.card α → ¬ IsChainPoset α →
  IH → HasBalancedPair α
```

where `IH` is the strong-induction hypothesis on strictly smaller
non-chain layered width-3 posets. For the K ≥ 2 irreducible case
where `Fintype.card α > 6 * L.w + 6` (so the
`bounded_irreducible_balanced_hybrid` size bound fails), the paper's
proof (`step8.tex:3112-3116`, "Case C1") performs **window
descent**: pick an incomparable pair `(x, y)`, build the window
`W ⊆ α` of bands `[min(i,j) − w, max(i,j) + w]` containing both
elements, observe `|W| ≤ 3(3w + 1) < |α|`, and apply the IH to the
sub-poset `↥W`. The balanced pair in `↥W` then lifts to a balanced
pair in `α` via `OrdinalDecomp.hasBalancedPair_lift` on a fresh
`OrdinalDecomp α` of shape `α = X^− ⊔ W ⊔ X^+`.

The lift requires us to **construct** an `OrdinalDecomp α` whose
`Mid` is `W`.

### 3b. Why the natural construction fails

The fields of `OrdinalDecomp α` need:
* `Lower < Mid` element-wise (`hLM_lt`),
* `Mid < Upper` element-wise (`hMU_lt`),
* `Lower < Upper` element-wise (`hLU_lt`).

The only in-tree mechanism for cross-band comparability is
`(L2-forced) : ∀ x y, band x + w < band y → x < y`.

For the natural partition
* `Lower := {z | band z ≤ min(i,j) − w − 1}`,
* `Mid := {z | min(i,j) − w ≤ band z ≤ max(i,j) + w}`,
* `Upper := {z | band z ≥ max(i,j) + w + 1}`,

`Lower < Mid` follows: any `z ∈ Lower`, `m ∈ Mid` satisfies
`band z + w ≤ (min(i,j) − w − 1) + w = min(i,j) − 1 < min(i,j) − w + w
= min(i,j) ≤ band m`. Strict, so `(L2-forced)` fires.

`Mid < Upper` **fails** at the boundary: take `m ∈ Mid` with
`band m = max(i,j) + w` and `z ∈ Upper` with
`band z = max(i,j) + w + 1`. Then `band m + w = max(i,j) + 2w` and
`band z = max(i,j) + w + 1`. For `w ≥ 1`,
`max(i,j) + 2w ≥ max(i,j) + w + 1`, so `band m + w ≥ band z` — the
strict inequality `band m + w < band z` required by `(L2-forced)`
does **not** hold. So `(L2-forced)` does not fire and `m < z` is
not derivable from in-tree primitives.

The same boundary issue blocks any naive window definition for
`w ≥ 1`: `(L2-forced)` requires a band-distance gap of strictly
more than `w`, but the window's upper edge sits at exactly
`max(i,j) + w` and the immediate-next-band element is at
`max(i,j) + w + 1`, a distance of `1 ≤ w` for `w ≥ 1`.

### 3c. Possible workarounds (none in scope for this ticket)

* **Wider window with buffer absorbed into Mid.** Define
  `Lower := bands ≤ min(i,j) − 2w − 1`, `Mid := bands [min(i,j) − 2w,
  max(i,j) + 2w]`, `Upper := bands ≥ max(i,j) + 2w + 1`. Then
  `(L2-forced)` fires at the boundaries (band gaps `> w`), so
  `Lower < Mid < Upper` does hold. But the extended Mid has size
  `≤ 3 · (max(i,j) − min(i,j) + 4w + 1) ≤ 3 · (5w + 1) = 15w + 3`,
  which **exceeds** the hybrid profile's `|α| ≤ 6w + 6` size cap
  for the C2-leaf base case (`6w + 6 < 15w + 3` for `w ≥ 1`). So
  the C2 leaf — `Mid = α`, no descent available — would not fit
  `bounded_irreducible_balanced_hybrid`'s profile, leaving us
  stuck on the `15w + 3 ≥ |α| > 6w + 6` regime with no path to
  the leaf.
* **Strengthen `(L2)` to upward-strict.** Replace `(L2-forced)`'s
  `+w <` with `+w ≤` (or equivalently shrink `w` by 1 in the
  encoding). Would require a `LayeredDecomposition` field rewrite
  with downstream consequences across many files.
* **Sidestep window descent** by always reducing via `lem:cut`
  (the deep regime layered cut) on `K ≥ 2w + 2` and applying
  `bounded_irreducible_balanced_hybrid` only when `K ≤ 2w + 2`.
  But `lem:cut` produces a `LayeredCut` (almost-ordinal partition),
  not an `OrdinalDecomp`; transferring `HasBalancedPair` from the
  cut's pieces to `α` is the same problem in disguise.
* **Probability-direct argument** routed through the
  `windowLocalization` probability identity rather than the
  `OrdinalDecomp.hasBalancedPair_lift` shape. Requires a separate
  `HasBalancedPair α ↔ HasBalancedPair ↥W` characterization keyed
  on the `probLT` identity, ~80-150 LoC of new infrastructure.

Each workaround is a multi-day infrastructure ticket of its own.

---

## 4. Blocker B: `allBalanced → enumPosetsFor` outer-loop bridge

### 4a. What we need

`bounded_irreducible_balanced_inScope` (the discharge target of
`mg-072c` step 2) takes the obligation

```
(h_certificate : Case3Enum.enumPosetsFor L.w (bandSizes L) = true)
```

per `BoundedIrreducibleBalancedInScope.lean:114-115`. The F5a
certificate (`Case3Enum.case3_certificate`) provides

```
allBalanced 1 9 = true ∧ allBalanced 2 7 = true ∧
allBalanced 3 7 = true ∧ allBalanced 4 7 = true
```

via the per-`w` `case3_balanced_w{1,2,3,4}` lemmas
(`Case3Enum/Certificate.lean:57-62`). The shape of `allBalanced`
(`Case3Enum.lean:360-363`) is

```
def allBalanced (w : Nat) (sizeLimit : Nat) : Bool := Id.run do
  for bs in bandSizesGen 3 sizeLimit do
    if !enumPosetsFor w bs then return false
  return true
```

an outer `Id.run do for bs in bandSizesGen 3 sizeLimit do` loop
that returns `false` early if any inner `enumPosetsFor w bs` returns
`false`. The Bool→Prop direction we need is

```
allBalanced w sizeLimit = true →
  ∀ bs ∈ bandSizesGen 3 sizeLimit, enumPosetsFor w bs = true
```

### 4b. Why this is non-trivial

The codebase's pattern for Bool→Prop on `Id.run do for-loops` is the
factored body + `forIn` characterization established in
`mg-580e` / `mg-b487` for the **inner** `enumPosetsFor` loop (see
`Case3Enum/EnumPosetsForBridge.lean §1-§5`,
~300 LoC of reduction). The same pattern applies to the **outer**
`allBalanced` loop, but is **not in tree** — there is no
`allBalanced_outerBody`, no
`allBalanced_eq_outer_fst`, no
`allBalanced_imp_enumPosetsFor` lemma.

Building the outer bridge would be a separate ~50-100 LoC ticket
(less than the inner because the body is simpler — just one
`if !enumPosetsFor … then return false` check), but the structural
work of `forIn` characterization plus the outer
`bandSizes_mem_bandSizesGen` membership argument is non-trivial
elaboration.

### 4c. Why pc-4a5b's audit missed this

pc-4a5b's status doc §2a notes:

> `h_certificate` from F5a's `case3_certificate` Bool fact +
> `bandSizes_mem_bandSizesGen` + an `allBalanced` unrolling.

The "`allBalanced` unrolling" is the missing piece. pc-4a5b
classified it as in-tree-derivable; on close reading, it is
derivable in **principle** (the F5a Bool certificate plus
`bandSizes_mem_bandSizesGen` plus the unrolling) but the unrolling
itself does not exist as a named lemma and would have to be
written.

---

## 5. Cost estimate (revised)

| Piece | LoC | Status |
| --- | ---:| --- |
| width-3-threaded F3 framework | 100-150 | DONE (mg-a735) |
| Lower/Upper lifts | 50-100 | DONE (mg-7f06) |
| StrictCase2 chain-form FKG closure | 100-200 | DONE (mg-27c2) |
| F3 step proof (K=1 + K≥2) | 150-250 | TODO (mg-072c) |
| 5 inScope caller obligations | 50-100 | TODO (mg-072c) |
| Headline wiring at `MainTheorem.lean` | 30-50 | TODO (mg-072c) |
| **Window-OrdinalDecomp constructor (NEW)** | **80-150** | NEW BLOCKER |
| **`allBalanced → enumPosetsFor` outer bridge (NEW)** | **50-100** | NEW BLOCKER |
| **mg-072c remaining total** | **360-650** | spread across 4-6 files |

The two new blockers add ~130-250 LoC to the original ~230-400
estimate, putting the total at the upper end of single-session
viability. Combined with the elaborator / universe / typeclass risk
from cross-cutting changes to `lem_layered_balanced` /
`mainTheoremInputsOf` / `width3_one_third_two_thirds`, this is
beyond what one polecat session can land cleanly.

---

## 6. Why I am not silently accepting a workaround

The task body's **Hard block-and-report rule**:

> If the polecat finds it cannot close without adding additional
> hypotheses (the option-(b) failure mode that produced the
> rejected c5d5a10 commit), STOP. Mail mayor + pm-onethird per the
> standard block-and-report protocol. Do **NOT** silently accept a
> multi-hypothesis variant.

The viable single-session workarounds all violate this rule:

* **Add window-localization as a hypothesis.** Threading a
  hypothetical `windowDescent : ∀ α [...] (L : LayeredDecomposition α)
  (x y : α) (hxy : x ∥ y), HasBalancedPair ↥W → HasBalancedPair α`
  through the headline would re-create the c5d5a10 multi-hypothesis
  failure mode under a different name.
* **Add `enumPosetsFor` consequence as a hypothesis.** Same.
* **Axiomatize the missing pieces.** The hard gate
  (`#print axioms` unchanged from baseline) explicitly forbids new
  axioms.
* **Partial code changes** to `width3_one_third_two_thirds` that
  fail to compile, or that drop `hC3` while leaving a stub
  `sorry`. Would not pass the "builds clean. No new sorry / admit
  / axioms" gate.

Either deviation re-creates the c5d5a10 failure mode under a
slightly different name; pc-4a5b's status doc §4 makes the same
point.

---

## 7. What I am doing

* **Writing this status doc** as the block-and-report deliverable,
  matching the precedent of `docs/a5-g3e-fkg-route-status.md`
  (pc-4a5b) and `docs/a8-s2-strict-witness-status.md` (pc-43f3).
* **Mailing mayor** with summary + this doc reference.
* **NOT axiomatizing** any FKG case or window descent.
* **NOT making partial code changes** to
  `width3_one_third_two_thirds` (those would either fail to compile
  or silently introduce extra hypotheses).
* **NOT adding new fields** to the headline (no multi-hypothesis
  variant).
* **NOT exiting**; standing by for guidance.

---

## 8. Suggested follow-up directions (for pm-onethird)

Picking one is a strategic call that belongs with pm-onethird; these
are options, not recommendations:

* **Multi-step ticket sequence.** Split mg-072c into:
  * `mg-072c-a` — Window-OrdinalDecomp constructor in
    `Mathlib/LinearExtension/Subtype.lean` (or new
    `Step8/WindowDecomp.lean`).
  * `mg-072c-b` — `allBalanced → enumPosetsFor` outer-loop bridge
    in `Case3Enum/AllBalancedBridge.lean`.
  * `mg-072c-c` — F3 step proof + inScope obligations + headline
    wiring (the original mg-072c, but now closeable in a session).
* **Strengthen `(L2)` to non-strict.** Add a
  `(L2-forced-le) : band x + w ≤ band y → x < y` field (or change
  `+ w <` to `+ w + 1 ≤`) in `LayeredDecomposition`, with a
  one-time downstream rewrite. This unblocks the natural Window
  decomposition without additional infrastructure. Caveat: the
  paper's `(L2)` uses strict inequality, so this is a deviation
  from the paper's encoding.
* **Probability-direct window argument.** Skip the
  `OrdinalDecomp.hasBalancedPair_lift` route and instead lift
  `HasBalancedPair ↥W → HasBalancedPair α` via the `probLT`
  identity proved by `windowLocalization`. ~80-150 LoC of new
  infrastructure but no encoding change.
* **Park the option-(i) Path C path.** Keep the current `hC3` shape
  permanently and pursue a different elimination strategy (e.g.,
  inline the StrictCase2 case in the C2-leaf handler with a single
  FKG hypothesis there, leaving `Case3Witness` as a def — but the
  wider F3 step proof still needs Window-OrdinalDecomp infrastructure
  to descend in C1).
* **Accept axiomatization** of `Case3Witness` itself as the residual
  Path C closure, with an `lean/AXIOMS.md` gap disclosure analogous
  to `case3Witness_hasBalancedPair_outOfScope`. Trades the FKG
  hypothesis for a project axiom.

---

## 9. References

* Polecat instructions: `mg-072c` task body.
* `docs/a5-g3e-fkg-route-status.md` (mg-4a5b) — pc-4a5b's previous
  audit; cost estimate §3 underspecifies the two new blockers.
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — pc-43f3's
  block-and-report on the StrictCase2 closure (now resolved by
  mg-27c2).
* `git show c5d5a10` (reverted via mg-05d3) — the negative
  exemplar (multi-hypothesis hStep at the headline).
* `lean/OneThird/MainTheorem.lean:38-43` — wiring target.
* `lean/OneThird/Step8/LayeredBalanced.lean:419` — `Case3Witness`
  def to be promoted to theorem.
* `lean/OneThird/Step8/LayeredBalanced.lean:103` — placeholder
  `windowLocalization` (probability identity only, no
  `OrdinalDecomp` constructor).
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:99` —
  inScope leaf with the 5 caller obligations including
  `h_certificate : enumPosetsFor L.w (bandSizes L) = true`.
* `lean/OneThird/Step8/Case3Enum.lean:360-363` — `allBalanced`
  outer for-loop.
* `lean/OneThird/Step8/Case3Enum/EnumPosetsForBridge.lean` — the
  inner `enumPosetsFor` Bool→Prop bridge (template for the missing
  outer bridge).
* `lean/OneThird/Step8/Case3Enum/Certificate.lean:57-62` — F5a
  Bool certificate (`case3_certificate`).
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1146-1241` —
  Mid lift + new Lower/Upper lifts (mg-7f06).
* `lean/OneThird/Step8/Case2Rotation.lean:736+` — chain-form FKG
  closure (mg-27c2), `Case2FKGSubClaim` and
  `case2Witness_balanced_under_FKG`.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (this
  docs-only commit does not change it).
