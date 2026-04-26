# A5-G3e FKG-route status — block-and-report

**Work item:** `mg-4a5b` (Path C wiring v2 — option (i) FKG-hypothesis path,
replacement for `mg-b329` after the `c5d5a10` revert via `mg-05d3`).

**Status:** **blocked** — the 1-for-1 hypothesis swap (drop `hC3`,
add a single `hFKG`) is not closeable in a single polecat session
without additional in-tree infrastructure that is not currently
available. Mailing mayor + pm-onethird per the task body's
**Hard block-and-report rule**.

**Author:** `pc-4a5b` polecat, 2026-04-26.

---

## TL;DR

Closing `Case3Witness` as a theorem (rather than a def / hypothesis)
with **only** an `hFKG` sub-claim hypothesis as the new addition to
`width3_one_third_two_thirds` would require building three pieces of
infrastructure that are missing from the tree:

1. **A width-3-threaded F3 strong-induction framework.** The bare F3
   in `LayerOrdinal.lean:370` drops `HasWidthAtMost α 3` through the
   IH, which the `Case3Witness`-shaped leaf dispatch needs.
2. **`OrdinalDecomp` Lower / Upper `hasBalancedPair_lift` constructors**
   (or a Mid-repackaging trick). Only the Mid lift exists in tree
   (`Mathlib/LinearExtension/Subtype.lean:1146`); the F3 reducible
   case descends to Lower or Upper, which has no in-tree lift.
3. **The `case2Discharge` chain** — `Case2Witness L → HasBalancedPair α`
   wired through `hStruct_of_case2_discharge` — requires a closure
   theorem that does not yet exist. Even with `hFKG`, the `m = 2`
   single-pair version of the FKG closure (status doc §2) and the
   `m = 2 → m = 3` chain extension (status doc §3) are both missing.

Estimated total work: ~500–750 LoC of new Lean code spread across
4–6 files, with at least one open mathematical question (the chain
extension). This is well beyond a single polecat session and matches
the failure mode `c5d5a10` produced (unclosed step-function predicate).

Per the task body's **Hard block-and-report rule**: not silently
accepting a multi-hypothesis variant; not attempting partial wiring;
mailing mayor + pm-onethird and standing by for guidance.

---

## 1. What the spec asks for

`mg-4a5b` requires:

* Replace the `Case3Witness` **def** (`LayeredBalanced.lean:419`,
  the outer ∀-family) with a **theorem** (no longer a hypothesis at
  call sites that consume it).
* Drop `hC3 : Step8.Case3Witness` from
  `OneThird.width3_one_third_two_thirds` (`MainTheorem.lean:38-43`).
* Add **EXACTLY ONE** new hypothesis — the FKG sub-claim per
  `docs/a8-s2-strict-witness-status.md` §3.
* Hard gate: `#print axioms width3_one_third_two_thirds` adds
  `case3Witness_hasBalancedPair_outOfScope` (the existing project
  axiom, `Case3Residual.lean:208`) on top of the unchanged baseline.

The negative exemplar `c5d5a10` (now reverted) is explicitly named:
its multi-hypothesis `hStep` (5+ propositional hypotheses bundled
into a step-function predicate) is a do-not-do-this artifact.

## 2. Audit of dependencies

### 2a. What is in tree (✓)

* **F3 strong-induction framework** (bare form, no width-3 threading):
  `Step8.hasBalancedPair_of_layered_strongInduction`
  (`LayerOrdinal.lean:370`).
* **Bipartite K = 1 base case**: `Step8.bipartite_balanced_enum`
  (`BipartiteEnum.lean`).
* **Reducibility witness builder**:
  `Step8.OrdinalDecompOfReducible` (`LayerOrdinal.lean:108`) with
  `Lower` / `Mid = ∅` / `Upper` shape.
* **Mid `hasBalancedPair_lift`**:
  `Mathlib/LinearExtension/Subtype.lean:1146` —
  `OrdinalDecomp.hasBalancedPair_lift : HasBalancedPair ↥D.Mid →
  HasBalancedPair α`.
* **Bounded irreducible / hybrid dispatch**:
  `bounded_irreducible_balanced_hybrid`
  (`BoundedIrreducibleBalanced.lean:1660`) +
  `bounded_irreducible_balanced_inScope`
  (`BoundedIrreducibleBalancedInScope.lean:99`).
* **Caller obligations of `bounded_irreducible_balanced_inScope`** —
  all five now closeable in tree thanks to `mg-9568`:
  - `enumPredAtMaskOf_eq_predMaskOf` (`PredMaskBridge.lean:1644`).
  - `enumFreeUVOf = freeUVOf` (now `rfl` after the §7 freeUVOf
    refactor).
  - `successorMasks_testBit` (`SymmetricLift.lean:667`).
  - `hNonempty` derivable from irreducibility under `K ≥ 2`.
  - `h_certificate` from F5a's `case3_certificate` Bool fact +
    `bandSizes_mem_bandSizesGen` + an `allBalanced` unrolling.
* **Out-of-scope dispatch (axiomatised)**:
  `case3Witness_hasBalancedPair_outOfScope`
  (`Case3Residual.lean:208`).
* **Case-1 ambient match**:
  `hasBalancedPair_of_ambient_profile_match` (`Case3Struct.lean`,
  `mg-f92d`) → `hasBalancedPair_of_case1`
  (`Case3Dispatch.lean:194`).
* **Case-1 / Case-2 / Case-3 inner dispatch**:
  `case1_dispatch_balanced_or_witness` (`Case3Dispatch.lean:271`).
* **Chain-form FKG closure**:
  `strictCase2WitnessChain_balanced_under_FKG`
  (`Case2Rotation.lean:717`) — closes
  `StrictCase2WitnessChain L → HasBalancedPair α` from a
  three-pair-probability hFKG hypothesis, using chain swap
  (`probLT_le_half_of_chain`) to rule out the residual.

### 2b. What is **not** in tree (✗) — the blockers

* **Width-3-threaded F3 framework.** `lem_layered_balanced` at
  `LayeredBalanced.lean:469` short-circuits the recursion with
  `hC3` directly; no in-tree variant performs F3 strong induction
  while threading `HasWidthAtMost β 3` through the IH, which is
  what the in-scope leaf (`bounded_irreducible_balanced_inScope`)
  consumes. `c5d5a10` introduced a `Case3WitnessHStep` predicate
  with this threading, but it took the entire step as a hypothesis.
* **Lower / Upper `hasBalancedPair_lift` constructors.** Only the
  Mid lift is in tree (`Subtype.lean:1146`). The F3 reducible case
  descends to `OrdinalDecompOfReducible.Lower` or `.Upper`, neither
  of which is the `Mid` of the constructed decomposition (the
  reducibility-witness `Mid = ∅`). A Mid-repackaging trick (place
  `D.Lower` in a fresh decomposition's `Mid`) is sketchable, but
  not in tree.
* **`Case2Witness L → HasBalancedPair α` direct closure.**
  `case2Witness_balanced_or_strict` (`Case2FKG.lean:226`) hands off
  to a `StrictCase2Witness L → HasBalancedPair α` discharge which
  is a referenced-but-not-implemented theorem
  (`Case2FKG.lean:250` is a doc-comment skeleton).
* **`StrictCase2Witness L → HasBalancedPair α` (m = 2) closure.**
  Per `docs/a8-s2-strict-witness-status.md` §2, the m = 2
  single-pair argument requires a probability lower bound
  `probLT a a' ≥ 1/2`; combined with chain swap's `≤ 1/2` it gives
  `probLT a a' = 1/2 ∈ [1/3, 2/3]` — closing m = 2. **This is the
  smallest possible closure shape** and could be produced from a
  pair-level `hFKG`. But the spec's `hFKG` shape "references only
  `StrictCase2WitnessChain` data" (m = 3 chain shape), not pair
  data, so the spec's hFKG cannot be directly applied to the
  StrictCase2Witness pair without an m = 2 → m = 3 upgrade.
* **m = 2 → m = 3 chain extension.**
  `Case2Witness L → StrictCase2WitnessChain L`. Requires picking a
  third within-band element forming a ⪯-chain with the original
  pair, under width-3 + irreducibility + `¬ InCase3Scope`. Not in
  tree; the m = 3 case is what the paper handles in
  `step8.tex:2877-2914` and is documented as future work.

## 3. Cost estimate

Closing this 1-for-1 swap requires writing each of the following:

| Piece | LoC | Notes |
| --- | ---:| --- |
| width-3-threaded F3 framework | 100–150 | new theorem, mirrors `LayerOrdinal.lean:370` |
| Mid-repackaging + Lower/Upper lifts | 50–100 | new constructors + lift-by-repackaging proofs |
| F3 step proof (K = 1 base + K ≥ 2 dispatch) | 150–250 | reducible case + irreducible case + bounded-hybrid wiring |
| 5 caller obligations of `inScope` discharge | 50–100 | each is now closeable in-tree but needs explicit composition |
| StrictCase2Witness → HasBalancedPair α + chain extension | 100–200 | smallest open mathematical step beyond infrastructure |
| Tying together at `MainTheorem.lean` | 30–50 | drop hC3, add hFKG, prove Case3Witness theorem |
| **Total** | **480–850** | spread across 4–6 files, multiple new theorems each |

Each piece carries its own elaborator / universe / typeclass risk;
the m = 2 → m = 3 chain extension is the only piece with an open
**mathematical** question (the paper's argument is sketched but not
formalised). The remaining pieces are formalisation effort, not new
math, but each is non-trivial to land cleanly.

This is well beyond a single polecat session. `c5d5a10`'s 237-LoC
attempt landed only the F3 framework + the Case3Witness lift from
hStep, leaving the step itself (the bulk of the work) as a
multi-hypothesis predicate — exactly the failure mode the current
task body flags as "do-not-do-this".

## 4. Why I am not silently accepting a multi-hypothesis variant

The task body's **Hard block-and-report rule** is explicit:

> If the polecat finds it cannot close without adding additional
> hypotheses (the option-(b) failure mode that produced the
> rejected c5d5a10 commit), STOP. Mail mayor + pm-onethird per the
> standard block-and-report protocol. Do **NOT** silently accept a
> multi-hypothesis variant.

The cleanest non-multi-hypothesis path (pair-level hFKG closing
m = 2 directly) is mathematically viable but **violates the spec's
hFKG signature constraint** ("references only `StrictCase2WitnessChain`
data"). The closest spec-compliant path (chain hFKG + chain extension)
requires the m = 2 → m = 3 chain extension, which is not in tree and
would itself require new mathematical work.

Either deviation (different hFKG shape, or partial closure) would
re-create the c5d5a10 failure mode under a slightly different name.

## 5. What I am doing

* **Writing this status doc** as the block-and-report deliverable.
* **Mailing pm-onethird** with the full analysis (subject:
  "block: pc-4a5b cannot close FKG-hypothesis swap in single
  session").
* **Mailing mayor** with summary + this doc reference.
* **NOT axiomatizing** any FKG case.
* **NOT making partial code changes** to `width3_one_third_two_thirds`
  (those would either fail to compile or silently introduce extra
  hypotheses).
* **NOT exiting**; standing by for guidance.

## 6. Possible follow-up directions (for pm-onethird)

These are options, not recommendations — picking one is a strategic
call that belongs with pm-onethird:

* **Refine the hFKG shape.** Allow a pair-level FKG sub-claim
  (matching `StrictCase2Witness` data, m = 2). Closes the StrictCase2
  case directly via chain swap, avoiding the m = 2 → m = 3
  extension. Still leaves the F3 framework, lifts, and inScope
  wiring as open infrastructure work — but each is mechanical.
* **Multi-step ticket sequence.** Split this into independent tickets:
  * `mg-4a5b-a` — width-3-threaded F3 framework.
  * `mg-4a5b-b` — Lower/Upper lifts (or Mid-repackaging).
  * `mg-4a5b-c` — StrictCase2Witness → HasBalancedPair α (with
    pair-level hFKG).
  * `mg-4a5b-d` — wire all five `inScope` caller obligations.
  * `mg-4a5b-e` — final wiring at `width3_one_third_two_thirds`.
* **Accept the c5d5a10 framework partial.** Re-land the F3 framework
  + `Case3WitnessHStep` predicate (without the multi-hypothesis
  hStep substitution at the headline) as a piece of infrastructure
  that downstream tickets can fill in.
* **Park the option-(i) path.** Keep the current `hC3` shape and
  pursue a different elimination strategy (e.g., inline the
  StrictCase2 case in the C2-leaf handler with a single FKG
  hypothesis there, leaving `Case3Witness` as a def).

## 7. References

* Polecat instructions: `mg-4a5b` task body.
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) — pc-43f3's
  block-and-report on the StrictCase2 closure (FKG-only) — see
  §§ 2-3 for the m = 2 / m = 3 closure analysis.
* `docs/a5-g3e-status.md` (mg-b329) — c5d5a10's analysis of the
  three blockers (StrictCase2, in-scope obligations, Lower/Upper
  lifts), now partially obsolete because mg-9568 closed the
  in-scope obligations.
* `git show c5d5a10` (reverted via mg-05d3) — the negative
  exemplar.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current `#print axioms` baseline
  (this docs-only commit does not change it).
