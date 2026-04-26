/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Poset
import OneThird.Step8.Case3Struct
import OneThird.Step8.Case3Dispatch
import OneThird.Step8.BoundedIrreducibleBalanced

/-!
# Step 8 — Case 3 residual: `prop:in-situ-balanced` for `¬ InCase3Scope`
(`mg-A8` sub-split A8-S3, `mg-b846`)

This file discharges the `Case3Witness L → HasBalancedPair α` slot of the
`prop:in-situ-balanced` case dispatch (`Step8.Case3Dispatch.lean`, A8-S1)
restricted to the `¬ InCase3Scope` parameter range. It is the third and
final sub-task of the `mg-A8` sub-split (A8-S1 / `mg-48db` typed dispatch
already in tree, A8-S2 / `mg-8801` Case 2 FKG discharge a separate work
item).

## Mathematical scope

`prop:in-situ-balanced` Case 3 (`step8.tex:3033-3047`) is the paper's
residual after Case 1 (ambient profile match, `step8.tex:2984-2999`) and
Case 2 (`⪯`-comparable within-band profile, `step8.tex:3001-3032`) of the
within-band antichain dispatch. The paper splits Case 3 along the
parameter regime:

* **In-scope** (`InCase3Scope L.w (Fintype.card α) L.K` =
  `K = 3 ∧ w ∈ {1,2,3,4} ∧ size cap`): the F5a `case3_certificate`
  (`OneThird.Step8.Case3Enum.case3_certificate`) discharges Case 3 via
  finite Bool-level enumeration. This is `lem:enum` (`step8.tex:3050-3067`)
  with `rem:residual-base` (`step8.tex:3194-3236`) supplying the
  parameter-range cap.

* **Out-of-scope** (`¬ InCase3Scope`): `K ∈ [3, 2w+2]` with `w ≥ 1` and
  `|α| ≤ 6w+6`, minus the `InCase3Scope` window. The paper's
  `rem:enumeration` (`step8.tex:3157-3173`) **sketches** but does not
  carry out a structural argument for this regime: the sketch is

  > For `w ≥ 1`, the configurations with `|A| = 3` whose profiles form a
  > `⪯`-antichain are enumerated modulo the symmetries of (L1); each is
  > discharged by exhibiting either a Case 1 symmetric pair (after taking
  > into account that two of the three elements must share *some*
  > coordinate of the two-sided profile whenever `|Q| ≤ 3(3w+1)` and (L2)
  > restricts the profile codomain), or a Case 2 pair with aligned
  > one-sided profiles restricted to the bands strictly above (or
  > strictly below) the antichain under consideration.

  The "shared coordinate" pigeonhole reduction and the band-restricted
  Case 2 FKG sub-coupling are not fleshed out in the published source.

## What this file delivers

* `Step8.InSitu.case3Witness_hasBalancedPair_outOfScope` — a project
  axiom that captures the residual claim of `prop:in-situ-balanced`
  Case 3 outside `InCase3Scope`. Per the polecat-instruction guidance
  ("If new math turns out to need its own axiom: report honestly via
  paper-vs-formalization diagnosis"), the axiom is retained with full
  disclosure in `lean/AXIOMS.md`.

* `Step8.InSitu.hasBalancedPair_of_case3_outOfScope` — a `theorem`
  re-export of the axiom for call-site readability.

* `Step8.InSitu.hStruct_of_case2_discharge` — composed dispatch:
  given the Case 2 discharge as a hypothesis (filled by A8-S2 /
  `mg-8801` once landed), produces the `hStruct`-shaped function
  `¬ InCase3Scope … → HasBalancedPair α` that
  `bounded_irreducible_balanced_hybrid` expects.

The wiring is constructive: the Case 1 branch is closed via mg-f92d's
`hasBalancedPair_of_ambient_profile_match`; the Case 2 branch consumes
A8-S2's discharge; the Case 3 branch consumes the axiom. Together with
A5-G2's `hCert` (Path A), this composes the full `hStruct + hCert`
dispatch into `bounded_irreducible_balanced_hybrid`.

## Why a project axiom

The axiom transcribes `prop:in-situ-balanced` Case 3 for the residual
parameter range. Unlike `OneThird.LinearExt.brightwell_sharp_centred`,
this is **not** a port of an external published result: it is internal
to this paper. Faithfully porting it would require:

1. Formalising the "two of three share a profile coordinate" pigeonhole
   step under (L1)/(L2) and `|Q| ≤ 3(3w+1)`.
2. Formalising the band-restricted Case 2 FKG sub-coupling that turns
   the shared coordinate into a balanced pair.
3. Working out the exact reduction from the shared coordinate to either
   a Case 1 ambient match (consuming
   `hasBalancedPair_of_ambient_profile_match`, mg-f92d) or a Case 2
   within-band ⪯-comparable pair (consuming A8-S2 / `mg-8801`).

Steps (1) and (3) are routine combinatorial work. Step (2) requires the
A8-S2 FKG infrastructure together with a sub-coupling that is not
formalised in the development. The estimate from the original A8 brief
("~300-600 LoC including the missing mathematical content") is a lower
bound — it presumes a fleshed-out paper proof to port, whereas
`rem:enumeration` is only a sketch.

Per the saved guidance ("external-theorem axiomatize-first ordering
applies if there's a citable result; if not, surface the gap"), the
gap is surfaced here as a named axiom plus the AXIOMS.md disclosure.
A future fleshed-out proof can replace the axiom by simply restating the
theorem body without changing any call-site.

## What this file does NOT do

* It does **not** discharge `Case2Witness L → HasBalancedPair α`
  (deferred to A8-S2 / `mg-8801`); the Case 2 discharge is consumed
  as a hypothesis by `hStruct_of_case2_discharge`.
* It does **not** wire the `hStruct` slot of
  `bounded_irreducible_balanced_hybrid` directly (deferred to A5-G3 /
  Path C, which combines A8-S1 + A8-S2 + this file).
* It does **not** replace the F5a `case3_certificate` for `InCase3Scope`
  (orthogonal: that is Path A / A5-G2's `hCert`).
* Beyond the new project axiom
  `case3Witness_hasBalancedPair_outOfScope`, it introduces no new
  `sorry`'s, additional axioms, or `native_decide` shortcuts.

## References

* `step8.tex` `prop:in-situ-balanced` (`2965-3048`); `lem:enum`
  (`3050-3067`); `rem:enumeration` (`3157-3173`); `rem:residual-base`
  (`3194-3236`).
* `lean/OneThird/Step8/Case3Dispatch.lean` — A8-S1's typed dispatch
  (`mg-48db`).
* `lean/OneThird/Step8/Case3Struct.lean` — Case 1 ambient form
  (`mg-f92d`).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean` —
  `bounded_irreducible_balanced_hybrid` consumer.
* `lean/AXIOMS.md` — full axiom audit, including the gap disclosure
  for `case3Witness_hasBalancedPair_outOfScope`.
* `docs/a8-status.md` — full mg-A8 status report and sub-split rationale.
-/

namespace OneThird
namespace Step8
namespace InSitu

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### §1 — The Case 3 residual axiom

The single project axiom of A8-S3. It states the residual conclusion of
`prop:in-situ-balanced` Case 3 (`step8.tex:3033-3047`) outside
`InCase3Scope`: under the hybrid theorem's wider hypothesis profile,
once neither a Case 1 ambient profile match pair nor a Case 2 within-band
`⪯`-comparable pair exists, a balanced pair still exists in `α`.

The paper's proof of this conclusion in the residual regime is the
`rem:enumeration` sketch (`step8.tex:3157-3173`); see the AXIOMS.md
entry for the full paper-vs-formalisation diagnosis. -/

/-- **`prop:in-situ-balanced` Case 3, residual (`¬ InCase3Scope`)**
(`step8.tex:3033-3047`, `rem:enumeration` `3157-3173`). Axiomatized.

Under the wider hypothesis profile of
`Step8.bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean:1587`) restricted to
`¬ InCase3Scope`, the typed Case 3 witness of A8-S1
(`Step8.InSitu.Case3Witness L` — neither a Case 1 ambient profile match
pair nor a Case 2 within-band `⪯`-comparable pair exists) implies that
a balanced pair exists in `α`.

The axiom is the formalisation transcription of `prop:in-situ-balanced`
Case 3 for the residual parameter range outside the F5a
`case3_certificate`'s certified scope. The paper's proof of this
conclusion in this regime is the `rem:enumeration` sketch
(`step8.tex:3157-3173`):

> two of the three elements must share *some* coordinate of the
> two-sided profile whenever `|Q| ≤ 3(3w+1)` and (L2) restricts the
> profile codomain.

The shared coordinate either gives a Case 1 ambient profile match on a
restricted sub-poset (handled by mg-f92d's
`hasBalancedPair_of_ambient_profile_match`) or a Case 2 pair with
aligned one-sided profiles restricted to the bands strictly above/below
the antichain (handled by A8-S2 / `mg-8801`'s discharge). The explicit
case analysis and the band-restricted FKG sub-coupling are **not
fleshed out** in the published source. Per the polecat-instruction
guidance ("If new math turns out to need its own axiom: report
honestly"), the residual claim is retained as a project axiom; see
`lean/AXIOMS.md` for the full disclosure and replacement path.

**Hypotheses.** The hypothesis profile matches
`bounded_irreducible_balanced_hybrid`:

* `hWidth3 : HasWidthAtMost α 3` — width-3 hypothesis.
* `hIrr : LayerOrdinalIrreducible L` — no ordinal-sum reduction is
  possible.
* `hK3 : 3 ≤ L.K` — depth at least 3 (Case-3 of the F5a enumeration).
* `hw : 1 ≤ L.w` — non-trivial interaction width.
* `hCard : Fintype.card α ≤ 6 * L.w + 6` — the `|X| ≤ 6w + 6` size cap
  from the F5 C2 branch.
* `hDepth : L.K ≤ 2 * L.w + 2` — the depth upper bound from the F5 C2
  branch.
* `hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K` — out-of-scope
  parameter range (the F5a `case3_certificate` handles `InCase3Scope`
  separately via Path A / A5-G2).
* `hC3 : Case3Witness L` — neither Case 1 (ambient profile match) nor
  Case 2 (within-band `⪯`-comparable pair) applies. -/
axiom case3Witness_hasBalancedPair_outOfScope
    (L : LayeredDecomposition α)
    (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hK3 : 3 ≤ L.K) (hw : 1 ≤ L.w)
    (hCard : Fintype.card α ≤ 6 * L.w + 6)
    (hDepth : L.K ≤ 2 * L.w + 2)
    (hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K)
    (hC3 : Case3Witness L) :
    HasBalancedPair α

/-! ### §2 — Theorem re-export and dispatch wiring -/

/-- **Out-of-scope Case 3 discharge → balanced pair** (the `mg-b846`
deliverable).

A direct re-export of `case3Witness_hasBalancedPair_outOfScope` as a
named theorem, so call-sites cite the result rather than the underlying
axiom symbol. The name pattern matches the rest of the
`Step8.InSitu` API. -/
theorem hasBalancedPair_of_case3_outOfScope
    (L : LayeredDecomposition α)
    (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hK3 : 3 ≤ L.K) (hw : 1 ≤ L.w)
    (hCard : Fintype.card α ≤ 6 * L.w + 6)
    (hDepth : L.K ≤ 2 * L.w + 2)
    (hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K)
    (hC3 : Case3Witness L) :
    HasBalancedPair α :=
  case3Witness_hasBalancedPair_outOfScope L hWidth3 hIrr hK3 hw hCard hDepth
    hScope hC3

/-- **Composed `hStruct` discharge with axiomatised Case 3 residual**
(`mg-A8` sub-split, A8-S3 wiring).

Given a Case 2 discharge as a hypothesis (filled by A8-S2 / `mg-8801`
once landed), produces the `hStruct`-shaped function
`¬ InCase3Scope … → HasBalancedPair α` that
`bounded_irreducible_balanced_hybrid` expects.

**Composition.**

* **Case 1** branch: closed via mg-f92d's
  `hasBalancedPair_of_ambient_profile_match`, wired through
  `case1_dispatch_balanced_or_witness` (A8-S1, mg-48db).
* **Case 2** branch: closed via the supplied `case2Discharge`
  hypothesis (A8-S2 / `mg-8801`).
* **Case 3** branch: closed via the
  `case3Witness_hasBalancedPair_outOfScope` axiom (this file).

Together with A5-G2's `hCert` (Path A — F5a `case3_certificate` for
`InCase3Scope`), this provides the full `hStruct + hCert` discharge of
`bounded_irreducible_balanced_hybrid`. The actual A5-G3 / Path C wiring
of the discharge into `lem_layered_balanced` to eliminate the outer
`Case3Witness` hypothesis from `width3_one_third_two_thirds` is a
separate work item. -/
theorem hStruct_of_case2_discharge
    (L : LayeredDecomposition α)
    (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hK3 : 3 ≤ L.K) (hw : 1 ≤ L.w)
    (hCard : Fintype.card α ≤ 6 * L.w + 6)
    (hDepth : L.K ≤ 2 * L.w + 2)
    (case2Discharge : Case2Witness L → HasBalancedPair α) :
    ¬ InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α := by
  intro hScope
  rcases case1_dispatch_balanced_or_witness L hWidth3 hIrr hScope with
    h1 | h2 | h3
  · exact h1
  · exact case2Discharge h2
  · exact hasBalancedPair_of_case3_outOfScope L hWidth3 hIrr hK3 hw hCard
      hDepth hScope h3

end InSitu
end Step8
end OneThird
