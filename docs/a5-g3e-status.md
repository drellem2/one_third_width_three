# A5-G3e status — `pc-b329` polecat report (`mg-b329`)

**Work item:** `mg-b329` (A5-G3e: Path C wiring + Case3Witness elimination from `width3_one_third_two_thirds`).
**Status:** partial — F3 framework added, `hC3` dropped from headline; structural-dispatch wiring not in tree (genuine residual gaps).
**Author:** `pc-b329` polecat, 2026-04-26.

---

## 1. What was supposed to land

> Replace `Case3Witness` def with a theorem proved by F3 strong
> induction, dropping the `hC3` hypothesis from
> `width3_one_third_two_thirds` in `MainTheorem.lean:38-43`.
>
> Compose:
> * G3d's `bounded_irreducible_balanced_inScope` (in-scope path).
> * A8's structural argument: `case1_dispatch_inScope`,
>   `case2Witness_balanced_or_strict`,
>   `case3Witness_hasBalancedPair_outOfScope` axiom (out-of-scope path).
>
> Verify after: `#print axioms width3_one_third_two_thirds` should show
> mathlib trio + `brightwell_sharp_centred` +
> `case3Witness_hasBalancedPair_outOfScope`. No new axioms.

---

## 2. What this polecat delivers

* **`Step8.Case3WitnessHStep`** (`Step8/Case3WitnessProof.lean §1`) —
  the F3-shaped step-function predicate with explicit width-3
  threading. Required because the bare F3
  (`Step8.hasBalancedPair_of_layered_strongInduction`) does not thread
  `HasWidthAtMost β 3` through the IH.

* **`Step8.case3Witness_of_hStep`**
  (`Step8/Case3WitnessProof.lean §2`) — proves the
  `Step8.Case3Witness` ∀-family from any `Case3WitnessHStep` via
  strong induction on `Fintype.card β`, with the K = 1 case closed
  inline by `bipartite_balanced_enum` (no IH needed) and the K ≥ 2
  case dispatched to the parametric `hStep`.

* **Updated `OneThird.width3_one_third_two_thirds`**
  (`MainTheorem.lean:38-44`) — the prior `hC3 : Step8.Case3Witness`
  hypothesis is replaced by `hStep : Step8.Case3WitnessHStep`. The
  proof body invokes `case3Witness_of_hStep hStep` to construct the
  required `Case3Witness` term and forwards to the existing assembly.

* **Build & axiom audit.** Build is clean (no `sorry`, no `admit`,
  no new axioms, no `native_decide` shortcuts on the
  `width3_one_third_two_thirds` call graph). `#print axioms` reports:

  ```
  'OneThird.width3_one_third_two_thirds' depends on axioms:
    [propext, Classical.choice, Quot.sound,
     OneThird.LinearExt.brightwell_sharp_centred]
  ```

  Identical to the pre-merge baseline.

---

## 3. What this polecat does **not** deliver

The brief's expected axiom set after the merge includes
`Step8.InSitu.case3Witness_hasBalancedPair_outOfScope` — the existing
A8-S3 project axiom. My proof body **does not transitively reach
that axiom**, because the structural-argument dispatch that uses it
lives inside the parametric `hStep`, not in the proof body of
`width3_one_third_two_thirds` itself.

To reach the axiom, the brief implicitly assumes that `hStep` can be
*constructed* (not parametric) by composing:

* `bounded_irreducible_balanced_inScope` for the in-scope path; and
* `bounded_irreducible_balanced_hybrid` +
  `hStruct_of_case2_discharge` + `case3Witness_hasBalancedPair_outOfScope`
  for the out-of-scope path.

A constructed (non-parametric) `hStep` is *not* in tree because the
following gap closures are missing:

### 3a. `StrictCase2Witness L → HasBalancedPair α` is not closed

`Step8.InSitu.case2Witness_balanced_or_strict`
(`Case2FKG.lean:226`) produces `HasBalancedPair α ∨ StrictCase2Witness L`.
The `StrictCase2Witness L` residual is **not closed** anywhere in the
tree — only conditionally via `strictCase2WitnessChain_balanced_under_FKG`
(`Case2Rotation.lean:717`), which depends on a separate FKG sub-claim
hypothesis that is itself open (A8-S2 follow-up).

`case3Witness_hasBalancedPair_outOfScope` cannot absorb the
`StrictCase2Witness` residual: its hypothesis `Case3Witness L =
¬ Case1 ∧ ¬ Case2Witness L` requires `¬ Case2Witness L`, which is
*false* whenever a `StrictCase2Witness L` exists (a strict witness
*is* a Case2Witness).

### 3b. `bounded_irreducible_balanced_inScope` has open caller obligations

The G3d in-scope discharge
(`Step8/BoundedIrreducibleBalancedInScope.lean:99`) carries five
caller-side obligations:

1. `hNonempty` — every band non-empty;
2. `h_construction_eq` — the per-mask construction-equivalence;
3. `h_freeUV_eq` — the free-UV alignment;
4. `h_succ` — `successorMasks` bit-correctness (closed in
   `mg-792a` / G3a-followup);
5. `h_certificate` — derivable from `case3_certificate`.

Items (2) and (3) are explicitly **OPEN** (`G3c-followup`,
`mg-7268-followup`, currently in progress under sibling polecat
`pc-9568`). Without them, the in-scope path cannot be constructively
discharged.

### 3c. `OrdinalDecomp` Lower / Upper lift theorems are missing

Case B of the F3 induction (the `LayerOrdinalReducible` ordinal-sum
descent) requires lifting `HasBalancedPair P_i → HasBalancedPair α`
where `P_i` is the lower or upper piece of an ordinal-sum
decomposition. Only `OrdinalDecomp.hasBalancedPair_lift` for the
*Mid* piece (`Mathlib/LinearExtension/Subtype.lean:1146`) is in tree;
analogous Lower / Upper variants — or the `OrdinalDecomp` repackaging
trick that puts the smaller piece in `Mid` — are not.

### 3d. K = 2 (height-2) leaf is not connected to `prop:bipartite-balanced`

For the K = 2 case of the F3 induction, the paper invokes
`prop:bipartite-balanced` directly. The Lean form
`bipartiteBalanced` (`LayeredBalanced.lean:331`) requires an explicit
`(A, B)` antichain pair with `A < B` cross-comparability; the
construction of `A := bandSet 1`, `B := bandSet 2` is not in tree.

---

## 4. Why partial

The brief's estimate ("~100-200 LOC") underestimates the work by
~3-5×. A full Path C wiring with an axiom-clean
`case3Witness_hasBalancedPair_outOfScope` reach requires:

* `OrdinalDecomp` Lower/Upper lift (~80 LOC).
* K = 2 → `prop:bipartite-balanced` connection (~50 LOC).
* `case3WitnessHStep_via_dispatch` constructor (~100-150 LOC).
* `StrictCase2Witness` closure or axiom (independent A8-S2 work).
* `mg-7268-followup` G3c construction-equivalence
  (independent, in progress under `pc-9568`).

Total ~250-400 LOC of new infrastructure plus dependence on two
in-progress sibling work items. This is genuinely outside one
polecat session.

The shipped F3 framework is the *foundation* for that work: it
demonstrates the strong-induction shape with width-3 threading and
provides the entry point that downstream `hStep` constructors will
plug into.

## 5. Recommended follow-up

Spawn `mg-b329-followup` after `pc-9568` lands and a `StrictCase2`
closure is available, with deliverable:

1. `OrdinalDecomp` Lower/Upper lift theorems (or the in-`Mid`
   repackaging trick).
2. `case3WitnessHStep_via_dispatch` constructor that wires
   `bounded_irreducible_balanced_hybrid` +
   `hStruct_of_case2_discharge` (using the axiom) + parametric Case 2
   and in-scope closures.
3. K = 2 specialisation via `bipartiteBalanced`.
4. Update `width3_one_third_two_thirds` to take only the genuinely
   external closures (Case 2 strict residual + in-scope obligations);
   `case3Witness_hasBalancedPair_outOfScope` becomes a transitive
   dependency and appears in `#print axioms`.

---

## 6. References

* Polecat instructions: `mg-b329` task body.
* `step8.tex` `lem:layered-balanced` (`step8.tex:2336-3237`),
  Cases A/B/C; `prop:in-situ-balanced` (`2965-3048`); `lem:enum`
  (`3050-3067`); `rem:enumeration` (`3157-3173`).
* `lean/OneThird/Step8/LayeredBalanced.lean:419` —
  `Case3Witness` def.
* `lean/OneThird/Step8/LayerOrdinal.lean:370` —
  bare F3 (`hasBalancedPair_of_layered_strongInduction`).
* `lean/OneThird/Step8/Case3WitnessProof.lean` — this commit.
* `lean/OneThird/MainTheorem.lean:38-44` — updated headline theorem.
* `docs/gap-analysis.md` — full Case3Witness gap analysis.
* `docs/a5-glue-status.md` — A5-G3 deliverable scope.
* `docs/a8-status.md` — A8 sub-split rationale.
* `docs/a5-g3c-status.md` — G3c-followup status.
