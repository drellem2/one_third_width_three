/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.FKG
import OneThird.Mathlib.LinearExtension.OrderPolytope

/-!
# Drops headline — structural infrastructure (EX-7 Session B)

This file establishes the **structural infrastructure** for the
EX-7 drops headline `probEvent'_mono_of_subseteq_upClosed`,
deferring the master theorem itself to a follow-up Session C.

## Scope (mg-4a56, Session B = Option 3 per mayor override 2026-05-09)

The polecat brief framed this session as the math finale of sub-α-C
(targeting `probEvent'_mono_of_subseteq_upClosed` in ~150–270 LoC,
consuming the chamber + `continuous_ad_general` + `stanley_log_supermod`
pillars).  After scoping in-session, the substantive Daykin–Saks 1981
swap-induction inner step turned out to require ~500–1000 LoC of
measure-theory glue beyond budget; mid-session the polecat (mg-4a56)
mailed the mayor with three options, including a 5th project axiom
(Option 2, mirroring mg-071b's mid-session decision for `cellMass_AD`).
The mayor returned **Option 3** as the trust-surface-preserving call:
the project committed to a ≤4-axiom envelope in the previous evening
digest, so adding a 5th axiom would exceed the envelope.  EX-7 Session
C will land the master theorem via the chamber + AD + Stanley chain
(estimated ~600–1000 LoC, 2–3 polecat sessions), consuming the
infrastructure landed here.

## Main declarations

* `OrderPolytope' Q` — the order polytope of a `RelationPoset α`,
  defined parallel to the typeclass-based
  `OneThird.LinearExt.OrderPolytope` (mg-8c66) but parametrised at
  the value level by `Q : RelationPoset α`.
* `OrderPolytope'_eq_asPartialOrder` — the `rfl`-bridge to the
  typeclass-based `OneThird.LinearExt.OrderPolytope` under
  `Q.asPartialOrder`, allowing every chamber-side theorem from
  mg-8c66 / mg-10d9 to transport directly.
* `OrderPolytope'_subset_of_subseteq` —
  `Q.Subseteq Q' → OrderPolytope' Q' ⊆ OrderPolytope' Q`
  (the set-level FKG monotonicity-under-augmentation: more relations
  ⟹ smaller polytope).
* `OrderPolytope'_inf_mem` / `OrderPolytope'_sup_mem` — the
  **sublattice property** of order polytopes under componentwise
  `⊓, ⊔`.  This is the key structural fact for the chamber + AD
  reduction in EX-7 Session C (Brightwell 1999 §4.2 pointwise
  four-function inequality on the cube).
* `OrderPolytope'_measurableSet` — Borel measurability (transport of
  mg-8c66 `OneThird.LinearExt.OrderPolytope.measurableSet`).
* `OrderPolytope'_subset_cube` — inclusion in `[0,1]^α`.

## References

* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4.2 — chamber + AD argument.
* D. E. Daykin and M. E. Saks, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142, Theorem 1.
* R. P. Stanley, *Two poset polytopes*, Discrete Comput. Geom.
  **1** (1986), 9–23, §3 — chamber decomposition.
* `docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md`
  (mg-2746, `dcd0925`) — full latex proof + Lean strategy.
* `docs/path-alpha-execution-arc/state.md` §1.21 (Monotone-free
  `continuous_ad_general` motivation) and §3.4 (sub-α-C arc).
-/

namespace OneThird

open Finset MeasureTheory

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — `OrderPolytope' Q`: order polytope of a `RelationPoset α`

This is a thin wrapper around `OneThird.LinearExt.OrderPolytope`
parametrised by `Q.asPartialOrder`, providing a value-level analogue
that coexists with multiple `Q : RelationPoset α` on the same ground
set.  Under `letI : PartialOrder α := Q.asPartialOrder`, the two
definitions agree by `rfl`. -/

/-- The **order polytope** of a finite data poset
`Q : RelationPoset α`: the set of `Q.le`-monotone maps `α → [0,1]`. -/
def OrderPolytope' (Q : RelationPoset α) : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, Q.le x y → f x ≤ f y) }

lemma mem_OrderPolytope' {Q : RelationPoset α} {f : α → ℝ} :
    f ∈ OrderPolytope' Q ↔
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, Q.le x y → f x ≤ f y) :=
  Iff.rfl

/-- The order polytope of a `RelationPoset α` agrees definitionally
with the typeclass-based `OneThird.LinearExt.OrderPolytope` of
`Q.asPartialOrder`.  This `rfl`-bridge lets us transport every theorem
from the mg-8c66 / mg-10d9 typeclass-based development directly. -/
lemma OrderPolytope'_eq_asPartialOrder (Q : RelationPoset α) :
    OrderPolytope' Q =
      letI : PartialOrder α := Q.asPartialOrder
      OneThird.LinearExt.OrderPolytope α := by
  rfl

/-! ### §2 — Sub-poset monotonicity (set inclusion) -/

/-- **Sub-poset monotonicity (set-level).** If `Q.Subseteq Q'`, then
`OrderPolytope' Q' ⊆ OrderPolytope' Q`: a function respecting the
larger relation also respects the smaller relation.  Note the
**reversed direction** matches the standard FKG monotonicity-under-
augmentation pattern (more relations ⟹ smaller polytope). -/
theorem OrderPolytope'_subset_of_subseteq
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q') :
    OrderPolytope' Q' ⊆ OrderPolytope' Q := by
  intro f hf
  refine ⟨hf.1, fun x y hxy => ?_⟩
  exact hf.2 x y (hQQ' hxy)

/-! ### §3 — Sublattice property under componentwise `⊓, ⊔`

Order polytopes are closed under componentwise `⊓` (pointwise minimum)
and `⊔` (pointwise maximum).  This is the key structural fact for the
chamber + Ahlswede–Daykin reduction of the drops headline (Brightwell
1999 §4.2 inner step). -/

/-- **Sublattice property (`⊓`).** Order polytopes are closed under
componentwise `⊓` (pointwise minimum). -/
theorem OrderPolytope'_inf_mem (Q : RelationPoset α) {f g : α → ℝ}
    (hf : f ∈ OrderPolytope' Q) (hg : g ∈ OrderPolytope' Q) :
    f ⊓ g ∈ OrderPolytope' Q := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · -- pointwise: min(f x, g x) ∈ [0, 1].
    have hfx : f x ∈ Set.Icc (0 : ℝ) 1 := hf.1 x
    have hgx : g x ∈ Set.Icc (0 : ℝ) 1 := hg.1 x
    rw [Set.mem_Icc] at hfx hgx ⊢
    refine ⟨le_min hfx.1 hgx.1, ?_⟩
    exact min_le_iff.mpr (Or.inl hfx.2)
  · -- order-preservation: min(f x, g x) ≤ min(f y, g y) when Q.le x y.
    have hfxy : f x ≤ f y := hf.2 x y hxy
    have hgxy : g x ≤ g y := hg.2 x y hxy
    change min (f x) (g x) ≤ min (f y) (g y)
    exact min_le_min hfxy hgxy

/-- **Sublattice property (`⊔`).** Order polytopes are closed under
componentwise `⊔` (pointwise maximum). -/
theorem OrderPolytope'_sup_mem (Q : RelationPoset α) {f g : α → ℝ}
    (hf : f ∈ OrderPolytope' Q) (hg : g ∈ OrderPolytope' Q) :
    f ⊔ g ∈ OrderPolytope' Q := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · have hfx : f x ∈ Set.Icc (0 : ℝ) 1 := hf.1 x
    have hgx : g x ∈ Set.Icc (0 : ℝ) 1 := hg.1 x
    rw [Set.mem_Icc] at hfx hgx ⊢
    refine ⟨?_, max_le hfx.2 hgx.2⟩
    exact le_max_iff.mpr (Or.inl hfx.1)
  · have hfxy : f x ≤ f y := hf.2 x y hxy
    have hgxy : g x ≤ g y := hg.2 x y hxy
    change max (f x) (g x) ≤ max (f y) (g y)
    exact max_le_max hfxy hgxy

/-! ### §4 — Measurability and inclusion in the cube

These transport directly from the typeclass version (mg-8c66) via
`OrderPolytope'_eq_asPartialOrder`. -/

/-- The order polytope of a `RelationPoset α` is contained in the cube
`[0,1]^α`. -/
lemma OrderPolytope'_subset_cube (Q : RelationPoset α) :
    OrderPolytope' Q ⊆ Set.univ.pi (fun _ : α => Set.Icc (0 : ℝ) 1) :=
  fun _ hf x _ => hf.1 x

/-- The order polytope of a `RelationPoset α` is Borel-measurable.
Transports from mg-8c66 `OneThird.LinearExt.OrderPolytope.measurableSet`
via `Q.asPartialOrder`. -/
theorem OrderPolytope'_measurableSet (Q : RelationPoset α) :
    MeasurableSet (OrderPolytope' Q) := by
  letI : PartialOrder α := Q.asPartialOrder
  rw [OrderPolytope'_eq_asPartialOrder]
  exact OneThird.LinearExt.OrderPolytope.measurableSet (α := α)

/-! ### §5 — Sub-α-C: forward to EX-7 Session C

The master theorem `probEvent'_mono_of_subseteq_upClosed` is **deferred
to Session C** per the mayor's Option 3 override (mg-4a56).  The
intended proof structure (per
`docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md` §2.4
mg-2746) consumes this file's structural infrastructure together with:

* `OneThird.LinearExt.OrderPolytope.chamber_cover`,
  `chamber_volume`, `chamber_inter_meas_zero`, and
  `orderPolytope_volume` (all in tree, mg-10d9), transported through
  `OrderPolytope'_eq_asPartialOrder`;
* `OneThird.ContinuousFKG.continuous_ad_general` (mg-071b); and
* `OneThird.LinearExt.stanley_log_supermod` (mg-d0fc, externally
  verified mg-e22f) at the discrete-sum closure step.

Per mg-2746 §4.3, no new project axiom is anticipated for Session C
under Option 3; the assembly is bounded by ~600–1000 LoC of measure-
theory glue + structural induction over `Q'.rel.card - Q.rel.card`. -/

end RelationPoset

end OneThird
