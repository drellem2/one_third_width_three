/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.DropsHeadline
import OneThird.Mathlib.RelationPoset.LinearExt
import OneThird.Mathlib.LinearExtension.OrderPolytope

/-!
# Drops headline — chamber transport for `OrderPolytope' Q` (EX-7 Session C.1)

This file ports the Stanley 1986 chamber-decomposition machinery
(`OneThird.LinearExt.OrderPolytope.chamber*`, mg-10d9 / mg-497d) from
the typeclass-based `[PartialOrder α]` setting to the data-version
`Q : RelationPoset α`, laying the chamber-side groundwork for the
EX-7 Session C master theorem `probEvent'_mono_of_subseteq_upClosed`.

## Scope (mg-1f3a, EX-7 Session C.1; Option 1 closure path, no 5th axiom)

Per `docs/path-alpha-execution-arc/state.md` §1.25 EX-7 Session C handoff
brief, the master theorem is being closed in 2–3 sub-sessions over
**Option 1 (full closure)**: chamber + `continuous_ad_general` (mg-071b)
+ `stanley_log_supermod` (mg-d0fc); **no new project axiom**.  Session
C.1 lands the chamber-volume transport for `OrderPolytope' Q` (the
~150 LoC piece (a) per state.md §1.25 forward pointer).

Sessions C.2 + C.3 will land the single-edge induction / swap
involution (~200 LoC) and the master theorem assembly via continuous
AD + Stanley (~250–650 LoC).  See §6 below for the in-file forward
pointer.

## Design note: `letI` discipline

Both `OneThird.LinearExt.OrderPolytope.chamber*` and the mg-4a56
`OrderPolytope'_eq_asPartialOrder` `rfl`-bridge live under the
typeclass `[PartialOrder α]`.  We activate `Q.asPartialOrder` *inside
each proof body* via `letI`, then construct an explicit
`LinearExt α := ⟨L.toFun, L.monotone⟩` from a `LinearExt' Q` (the
two structures share the bijection-plus-monotonicity shape, with
`asPartialOrder.le = Q.le` definitionally).  This sidesteps the
elaboration friction `letI` introduces in type signatures, and keeps
the `chamber'`/`chamber` `rfl`-bridge inline at each call site.

## Main declarations

* `RelationPoset.chamber'` — the chamber simplex `σ_L ⊆ α → ℝ` for
  `L : LinearExt' Q`.
* `RelationPoset.chamber'_subset_orderPolytope'` — chambers lie inside
  the order polytope.
* `RelationPoset.chamber'_volume` — Stanley 1986 (1.5):
  `volume(σ_L) = 1/n!`.
* `RelationPoset.chamber'_inter_meas_zero` — Stanley 1986 (1.4)
  pairwise: `L ≠ L' → volume(σ_L ∩ σ_{L'}) = 0`.
* `RelationPoset.chamber'_cover` — Stanley 1986 (1.4) cover:
  `OrderPolytope' Q = ⋃ L : LinearExt' Q, chamber' L`.
* `RelationPoset.orderPolytope'_volume` — Stanley 1986 (1.4) master:
  `volume(O(Q)) = numLinExt' Q / n!`.
* `RelationPoset.measurableSet_chamber'` — Borel-measurability of each
  chamber.
* `RelationPoset.numLinExt'_eq_numLinExt_asPartialOrder` — count
  agreement under the `Q.asPartialOrder` typeclass.

All declarations transport via the `rfl`-bridges of mg-4a56
(`OrderPolytope'_eq_asPartialOrder`) and the natural
`{ toFun := L.toFun, monotone := L.monotone }`-construction; no new
mathematical content beyond the typeclass-side proofs in mg-10d9 /
mg-497d.

## References

* R. P. Stanley, *Two poset polytopes*, Discrete Comput. Geom.
  **1** (1986), 9–23, §3 — chamber decomposition + volume formula.
* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4.2 — drops headline chamber + AD argument.
* `docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md` (mg-79a9)
  — chamber decomp latex scoping.
* `docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md` (mg-2746)
  §2.1 — chamber reduction step of the drops headline.
* `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` (mg-8c66 +
  mg-497d + mg-10d9) — typeclass source.
-/

namespace OneThird

open Finset MeasureTheory

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — `chamber' L`: chamber simplex for `LinearExt' Q`

The chamber simplex `σ_L ⊆ α → ℝ` is defined identically to the
typeclass-based `OneThird.LinearExt.OrderPolytope.chamber` (mg-497d):
both depend only on `L.pos = L.toFun`, not on the ambient
`[PartialOrder α]` typeclass.  The `rfl`-bridge `chamber'_eq_chamber`
(below, inline at each call site) transports every chamber-side theorem
from mg-10d9 / mg-497d. -/

/-- The **chamber simplex** indexed by a data linear extension
`L : LinearExt' Q`: maps `α → [0,1]` non-decreasing along `L`'s
linear order. -/
def chamber' {Q : RelationPoset α} (L : LinearExt' Q) : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) }

lemma mem_chamber' {Q : RelationPoset α} {L : LinearExt' Q} {f : α → ℝ} :
    f ∈ chamber' L ↔
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) :=
  Iff.rfl

/-! ### §2 — Chamber inclusion in `OrderPolytope' Q`

A chamber lies inside the order polytope: `L`-monotone implies
`Q.le`-monotone since `L : LinearExt' Q` respects `Q.le`.  Direct
proof at the data level, no transport required. -/

/-- Each chamber lies inside the order polytope. -/
theorem chamber'_subset_orderPolytope' {Q : RelationPoset α}
    (L : LinearExt' Q) : chamber' L ⊆ OrderPolytope' Q := by
  intro f hf
  refine ⟨hf.1, fun x y hxy => ?_⟩
  exact hf.2 x y (L.monotone hxy)

/-! ### §3 — Chamber volume + measurability + pairwise overlap

These transport directly from mg-497d / mg-10d9 via the inline
`rfl`-bridge `chamber' L = chamber ⟨L.toFun, L.monotone⟩` once
`Q.asPartialOrder` is activated. -/

/-- **Stanley 1986 Theorem 1.4 (volume part), data version.** Each
chamber `σ_L` has Lebesgue volume `1/n!`. -/
theorem chamber'_volume {Q : RelationPoset α} (L : LinearExt' Q) :
    volume (chamber' L) =
      ENNReal.ofReal (1 / (Nat.factorial (Fintype.card α) : ℝ)) := by
  letI : PartialOrder α := Q.asPartialOrder
  let L' : OneThird.LinearExt α := { toFun := L.toFun, monotone := L.monotone }
  have h : chamber' L = OneThird.LinearExt.OrderPolytope.chamber L' := rfl
  rw [h]
  exact OneThird.LinearExt.OrderPolytope.chamber_volume L'

/-- Each chamber is Borel-measurable. -/
theorem measurableSet_chamber' {Q : RelationPoset α} (L : LinearExt' Q) :
    MeasurableSet (chamber' L) := by
  letI : PartialOrder α := Q.asPartialOrder
  let L' : OneThird.LinearExt α := { toFun := L.toFun, monotone := L.monotone }
  have h : chamber' L = OneThird.LinearExt.OrderPolytope.chamber L' := rfl
  rw [h]
  exact OneThird.LinearExt.OrderPolytope.measurableSet_chamber L'

/-- **Stanley 1986 Theorem 1.4 (overlap part), data version.** For
`L ≠ L'` in `LinearExt' Q`, the chambers `σ_L`, `σ_{L'}` intersect in
a Lebesgue-null set. -/
theorem chamber'_inter_meas_zero {Q : RelationPoset α} {L L' : LinearExt' Q}
    (h : L ≠ L') : volume (chamber' L ∩ chamber' L') = 0 := by
  letI : PartialOrder α := Q.asPartialOrder
  let L₁ : OneThird.LinearExt α := { toFun := L.toFun, monotone := L.monotone }
  let L₂ : OneThird.LinearExt α := { toFun := L'.toFun, monotone := L'.monotone }
  have h₁ : chamber' L = OneThird.LinearExt.OrderPolytope.chamber L₁ := rfl
  have h₂ : chamber' L' = OneThird.LinearExt.OrderPolytope.chamber L₂ := rfl
  rw [h₁, h₂]
  apply OneThird.LinearExt.OrderPolytope.chamber_inter_meas_zero
  intro hEq
  -- L₁ = L₂ as `LinearExt α` ⟹ L.toFun = L'.toFun ⟹ L = L' as `LinearExt' Q`.
  apply h
  apply LinearExt'.ext
  exact congrArg OneThird.LinearExt.toFun hEq

/-! ### §4 — Chamber cover + master volume formula

The cover identity `O(Q) = ⋃ L : LinearExt' Q, chamber' L` follows from
the typeclass `chamber_cover` plus a reindexing of the iUnion via the
bijection `LinearExt α (Q.asPartialOrder) ≃ LinearExt' Q`.  Established
explicitly via element chasing. -/

/-- **Stanley 1986 Theorem 1.4 (cover part), data version.** The order
polytope `O(Q)` is the union of the chambers `σ_L` over `LinearExt' Q`. -/
theorem chamber'_cover (Q : RelationPoset α) :
    (OrderPolytope' Q : Set (α → ℝ)) = ⋃ L : LinearExt' Q, chamber' L := by
  letI : PartialOrder α := Q.asPartialOrder
  rw [OrderPolytope'_eq_asPartialOrder, OneThird.LinearExt.OrderPolytope.chamber_cover]
  ext f
  simp only [Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  · rintro ⟨L, hL⟩
    -- L : LinearExt α (under Q.asPartialOrder); convert to LinearExt' Q.
    refine ⟨{ toFun := L.toFun, monotone := L.monotone }, ?_⟩
    -- The chamber sets coincide by the rfl-bridge.
    exact hL
  · rintro ⟨L, hL⟩
    refine ⟨{ toFun := L.toFun, monotone := L.monotone }, ?_⟩
    exact hL

/-- The number of linear extensions of `Q.asPartialOrder` (typeclass)
equals `numLinExt' Q` (data).  Established by `Fintype.card_congr` on
the natural bijection `LinearExt α ≃ LinearExt' Q`. -/
lemma numLinExt'_eq_numLinExt_asPartialOrder (Q : RelationPoset α) :
    (numLinExt' Q : ℕ) =
      letI _ : PartialOrder α := Q.asPartialOrder
      numLinExt α := by
  letI : PartialOrder α := Q.asPartialOrder
  unfold numLinExt' numLinExt
  -- Bijection `LinearExt' Q ≃ LinearExt α` via the natural shared shape.
  exact Fintype.card_congr
    { toFun := fun L : LinearExt' Q =>
        ({ toFun := L.toFun, monotone := L.monotone } : OneThird.LinearExt α)
      invFun := fun L : OneThird.LinearExt α =>
        ({ toFun := L.toFun, monotone := L.monotone } : LinearExt' Q)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Stanley 1986 Corollary 1.4, data version.** The Lebesgue volume of
the order polytope `O(Q)` equals `numLinExt' Q / n!`. -/
theorem orderPolytope'_volume (Q : RelationPoset α) :
    volume (OrderPolytope' Q : Set (α → ℝ)) =
      ENNReal.ofReal ((numLinExt' Q : ℝ) /
        (Nat.factorial (Fintype.card α) : ℝ)) := by
  letI : PartialOrder α := Q.asPartialOrder
  rw [OrderPolytope'_eq_asPartialOrder,
      OneThird.LinearExt.OrderPolytope.orderPolytope_volume]
  -- numLinExt α = numLinExt' Q under Q.asPartialOrder.
  congr 2
  exact_mod_cast (numLinExt'_eq_numLinExt_asPartialOrder Q).symm

/-! ### §5 — Forward to EX-7 Sessions C.2 + C.3

The Session C master theorem `probEvent'_mono_of_subseteq_upClosed`
(Daykin–Saks 1981 Theorem 1 / Brightwell 1999 §4) consumes this file's
chamber-volume transport plus:

* **Single-edge induction** (Session C.2) — induction on
  `Q'.rel.card - Q.rel.card`: for `Q.Subseteq Q'`, exhibit a chain
  `Q = Q₀ ⊆ Q₁ ⊆ … ⊆ Q_n = Q'` where each `Qᵢ₊₁ = addRel Qᵢ a b _`
  augments by a single `Qᵢ`-incomparable pair `(a, b)`.  Reduces the
  master theorem to the single-edge case.

* **Swap involution + chamber pairing** (Session C.2) — for `(a, b)`
  `Q`-incomparable, the swap `τ_{ab}` on `α` induces an involution on
  `LinearExt' Q` that maps `LinearExt' (addRel Q a b _)` (extensions
  with `a < b`) bijectively onto its complement (extensions with
  `b < a`).  The chamber identity
  `O(Q) = O(Q') ⊔ τ_{ab}(O(Q'))` (modulo a Lebesgue-null hyperplane)
  follows; volume splits as `vol(O(Q)) = 2 · vol(O(Q'))`.

* **Continuous AD inner step** (Session C.3) — the inner inequality
  `Pr_{Q'}[S(τ_{ab}(L)_k)] ≤ Pr_{Q'}[S(L_k)]` reduces to a
  four-function continuous-AD inequality on `(𝟙_{O(Q)}, …)` via the
  sublattice property `OrderPolytope'_inf_mem` /
  `OrderPolytope'_sup_mem` (mg-4a56) + monotonicity-free
  `continuous_ad_general` (mg-071b).

* **Stanley log-supermod closure** (Session C.3) — the discrete
  combinatorial sum at the swap boundary closes via
  `OneThird.LinearExt.stanley_log_supermod` (mg-d0fc, externally
  verified mg-e22f).

Per state.md §1.25, no new project axiom anticipated for the full
Session C closure under Option 1; trust surface remains the four
named axioms (`brightwell_sharp_centred`,
`case3Witness_hasBalancedPair_outOfScope`, `stanley_log_supermod`,
`cellMass_AD`). -/

end RelationPoset

end OneThird
