/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.Case3Dispatch
import OneThird.Step8.Case3Struct

/-!
# Step 8 — Case 2 of `prop:in-situ-balanced` — partial deliverable
(`mg-A8` sub-split A8-S2, `mg-8801`)

This file collects the **reusable infrastructure** for the Case 2 FKG
profile-ordering argument of `prop:in-situ-balanced`
(`step8.tex:3001-3032`). The full discharge
`Case2Witness L → HasBalancedPair α` is **not** completed here; see
`docs/a8-s2-status.md` for the paper-vs-formalization gap analysis and
the recommended next steps.

## What is provable now (in this file)

* `Step8.InSitu.incomp_of_within_band` — the within-band condition of
  `Case2Witness` plus distinctness implies `a ∥ a'` (incomparability).
  Direct consequence of the `band_antichain` field of
  `LayeredDecomposition`. Reusable by A8-S3 as well.

* `Step8.InSitu.case2Witness_symmetric_collapse` — if a Case 2 witness
  pair `(a, a')` *also* satisfies the **reverse** profile inclusions —
  i.e., `(∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a')` — then the two
  one-sided inclusions become bi-implications, recovering the
  Case 1 ambient profile match
  (`prop:in-situ-balanced` Case 1, `step8.tex:2984-2999`). Composing
  with `hasBalancedPair_of_ambient_profile_match` (mg-f92d) yields
  `HasBalancedPair α`.

  This collapse is the reason the paper's wording of Case 2 emphasises
  *strict* `⪯`-comparability (one direction strict): the symmetric
  case is already absorbed into Case 1.

* `Step8.InSitu.case2Witness_or_case1_match` — every `Case2Witness L`
  is **either** part of a Case 1 ambient profile match (when the
  reverse inclusions also hold), **or** a strict `⪯`-comparability
  pair (the asymmetric case the paper's FKG argument operates on).
  The Case 1 sub-branch discharges to `HasBalancedPair α` directly
  via mg-f92d; the strict sub-branch is the input to the deferred
  FKG monotonicity argument.

## What is **not** provable here

The full FKG monotonicity argument
(`step8.tex:3001-3032`, sub-claim `Pr_Q[a <_L a'] ≥ 1/2`, plus the
`Pr_Q[a <_L a'] ≤ 2/3` direct check in the bipartite extremal
configuration, plus the rotation argument for the `m = 3` case) is
**not** in this file.

The blocker is **structural, not tactical**: the paper's argument
couples `𝓛(Q)` with `𝓛(Q')` for two distinct posets `Q` and `Q'`
on the *same* underlying ground set, where `Q'` is obtained from `Q`
by adding/removing a single comparability. In Lean, `PartialOrder α`
is a typeclass, so `α` carries a *fixed* partial order; comparing
`𝓛(Q)` with `𝓛(Q')` on the same `α` requires either:

* introducing a non-typeclass relation-as-data version of partial
  orders (a `Finset (α × α)` satisfying poset axioms), redoing
  `LinearExt`, `numLinExt`, `probLT`, etc. on top of it; or
* lifting to an "ambient" larger poset that contains both `Q` and
  `Q'` as sub-posets (e.g., the empty-relation poset, with `Q` and
  `Q'` as augmentations) — but this loses the cleanness of the
  Birkhoff transport.

Either route is a **substantial new infrastructure layer** (~600-1000
LOC in itself, before the actual Case 2 argument). See
`docs/a8-s2-status.md` for the full diagnosis.

## References

* `step8.tex` `prop:in-situ-balanced` Case 2 (`3001-3032`).
* `step8.tex` `prop:bipartite-balanced` Case 2 sub-claim
  (`2858-2875`) — the K=2 origin of the FKG argument.
* `lean/OneThird/Step8/Case3Dispatch.lean` — `Case2Witness` predicate
  (mg-48db / A8-S1).
* `lean/OneThird/Step8/Case3Struct.lean` —
  `hasBalancedPair_of_ambient_profile_match` (mg-f92d /
  Case 1 ambient form).
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean` — uniform FKG on
  `LowerSet α` and the level-`k` LinearExt projection
  (`fkg_uniform_initialLowerSet`).
* `docs/a8-s2-status.md` — full A8-S2 status report.
-/

namespace OneThird
namespace Step8
namespace InSitu

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### §1 — Within-band incomparability

The within-band condition `L.band a = L.band a'` of `Case2Witness`
plus distinctness `a ≠ a'` immediately yields `a ∥ a'` from the
`band_antichain` axiom of `LayeredDecomposition`. This is reused by
both A8-S2 (for the FKG monotonicity argument's preconditions) and
A8-S3 (for the residual antichain analysis). -/

/-- Within-band distinct elements of a layered decomposition are
incomparable. Direct consequence of `band_antichain`. -/
lemma incomp_of_within_band
    (L : LayeredDecomposition α)
    {a a' : α} (hne : a ≠ a') (hband : L.band a = L.band a') :
    a ∥ a' := by
  classical
  have hA := L.band_antichain (L.band a)
  have ha_mem :
      a ∈ ((((Finset.univ : Finset α).filter
              (fun x => L.band x = L.band a)) : Set α)) := by
    simp
  have ha'_mem :
      a' ∈ ((((Finset.univ : Finset α).filter
              (fun x => L.band x = L.band a)) : Set α)) := by
    simp [hband.symm]
  refine ⟨?_, ?_⟩
  · intro hle
    exact hA ha_mem ha'_mem hne hle
  · intro hle
    exact hA ha'_mem ha_mem (Ne.symm hne) hle

/-- Variant: if the witness is given as a packaged `Case2Witness L`
hypothesis, the underlying pair is incomparable. -/
lemma case2Witness_incomp
    (L : LayeredDecomposition α) (hC2 : Case2Witness L) :
    ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧ a ∥ a' ∧
      (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a) := by
  obtain ⟨a, a', hne, hband, h_up, h_down⟩ := hC2
  exact ⟨a, a', hne, hband, incomp_of_within_band L hne hband, h_up, h_down⟩

/-! ### §2 — Symmetric collapse to Case 1

The `Case2Witness L` predicate carries only the *one-sided* profile
inclusion `(∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)`. If the
*reverse* inclusion `(∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a')`
also holds, the two collapse to bi-implications — i.e., `a` and `a'`
have **identical ambient strict-`<` profile**, the hypothesis of
`prop:in-situ-balanced` Case 1 (`step8.tex:2984-2999`). Composing
with `hasBalancedPair_of_ambient_profile_match` (mg-f92d) yields
`HasBalancedPair α` directly.

This is why the paper's Case 2 implicitly assumes the `⪯`-comparability
is *strict*: the symmetric (= equal-profile) case is already absorbed
into Case 1, and the FKG monotonicity argument is only needed for the
strict-comparability case. -/

/-- **Symmetric collapse.** A pair `(a, a')` satisfying both the
forward Case 2 profile inclusions and their reverse forms has matching
ambient strict-`<` profile in both directions, so the Case 1 ambient
form (`hasBalancedPair_of_ambient_profile_match`, mg-f92d) gives a
balanced pair. -/
theorem case2Witness_symmetric_collapse
    {a a' : α} (hne : a ≠ a')
    (h_up_fwd : ∀ z, a < z → a' < z)
    (h_down_fwd : ∀ z, z < a' → z < a)
    (h_up_rev : ∀ z, a' < z → a < z)
    (h_down_rev : ∀ z, z < a → z < a') :
    HasBalancedPair α := by
  refine hasBalancedPair_of_ambient_profile_match a a' hne ?_ ?_
  · intro z; exact ⟨h_up_fwd z, h_up_rev z⟩
  · intro z; exact ⟨h_down_rev z, h_down_fwd z⟩

/-! ### §3 — Trichotomy: Case 1 collapse, strict `⪯`-comparability, or both

A `Case2Witness L` either has reverse-direction inclusions (and
collapses to Case 1, hence `HasBalancedPair α` via mg-f92d) or it does
not (and is the strict `⪯`-comparability case the paper's FKG
argument operates on). This trichotomy makes precise what the paper
is doing when it writes "Case 2 (strictly, by the failure of Case 1)"
on `step8.tex:3014`. -/

/-- A Case 2 witness pair is either symmetric in profile (and
discharged to `HasBalancedPair α` immediately via the Case 1 collapse)
or it is *strictly* one-sided in at least one direction. The
strictly-one-sided sub-case is the input to the deferred FKG
monotonicity argument; the symmetric sub-case is fully discharged in
this file. -/
theorem case2Witness_or_case1_match
    (L : LayeredDecomposition α) (hC2 : Case2Witness L) :
    HasBalancedPair α
      ∨ ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧ a ∥ a' ∧
          (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a) ∧
          ¬ ((∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a')) := by
  classical
  obtain ⟨a, a', hne, hband, h_up, h_down⟩ := hC2
  by_cases hRev : (∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a')
  · -- Symmetric: collapses to Case 1.
    obtain ⟨h_up_rev, h_down_rev⟩ := hRev
    exact Or.inl
      (case2Witness_symmetric_collapse hne h_up h_down h_up_rev h_down_rev)
  · -- Strict ⪯-comparability: the deferred FKG argument's input.
    exact Or.inr ⟨a, a', hne, hband,
      incomp_of_within_band L hne hband, h_up, h_down, hRev⟩

/-! ### §4 — Strict-comparability witness (target shape for the FKG argument)

Records the *strict* `⪯`-comparability shape — what the paper's Case 2
FKG monotonicity argument actually consumes — as a named predicate.
The deferred A8-S2 follow-up will discharge `StrictCase2Witness L →
HasBalancedPair α`; the symmetric sub-case is already discharged by
`case2Witness_or_case1_match`. -/

/-- The **strict** `⪯`-comparability sub-case of `Case2Witness`. This
is the shape the paper's Case 2 FKG monotonicity argument operates on:
a within-band incomparable pair `(a, a')` with one-sided ambient
profile inclusion such that the *reverse* inclusion fails (so the two
profiles are not equal, and Case 1 does not apply). -/
def StrictCase2Witness (L : LayeredDecomposition α) : Prop :=
  ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧ a ∥ a' ∧
    (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a) ∧
    ¬ ((∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a'))

/-- Every `Case2Witness L` is either Case 1 (giving `HasBalancedPair α`)
or a `StrictCase2Witness L`. This is the WLOG reduction that the
paper's wording on `step8.tex:3014` ("strictly, by the failure of
Case 1") makes implicitly. -/
theorem case2Witness_balanced_or_strict
    (L : LayeredDecomposition α) (hC2 : Case2Witness L) :
    HasBalancedPair α ∨ StrictCase2Witness L := by
  rcases case2Witness_or_case1_match L hC2 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### §5 — FKG monotonicity statement (target signature for follow-up)

The deferred discharge `StrictCase2Witness L → HasBalancedPair α`
is recorded here only as the doc-comment skeleton; the actual proof
requires the cross-poset coupling infrastructure described in
`docs/a8-s2-status.md`.

We do **not** introduce a `theorem` stub with `sorry` here, as that
would silently flow `sorrys` into `#print axioms` for downstream
declarations. Instead the follow-up should add
`strictCase2Witness_balanced` as a fully proved theorem, then derive

```
case2Witness_balanced (L : LayeredDecomposition α) (hC2 : Case2Witness L) :
    HasBalancedPair α := by
  rcases case2Witness_balanced_or_strict L hC2 with h | h
  · exact h
  · exact strictCase2Witness_balanced L h
```

at the call site (or in a follow-up commit), wiring into
`case1_dispatch_balanced_or_witness` of `Case3Dispatch.lean` to
collapse the three-way `HasBalancedPair α ∨ Case2Witness L ∨
Case3Witness L` disjunction down to `HasBalancedPair α ∨
Case3Witness L`. -/

end InSitu
end Step8
end OneThird
