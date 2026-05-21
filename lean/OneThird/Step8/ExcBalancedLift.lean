/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.ExcPerturb
import OneThird.Step8.BridgeLayered
import OneThird.LinearExtension
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Step 8 — S7-F bridge sub-ticket D: the exceptional-set balanced-pair lift

This file is **FULL REFACTOR Phase-2, Piece 3 (the S7-F bridge),
sub-ticket D** (work item `mg-876f`). It ports **item (iii) of paper
`lem:layered-from-step7`** (`step8.tex:2080-2089`): the *perturbation
lift* that transfers a balanced pair on the deleted ground set
`X ∖ X^exc` back to a (near-)balanced pair on the full ground set `X`,
with `o(1)` error.

It is the exceptional-set-deletion analogue of
`OrdinalDecomp.hasBalancedPair_lift`
(`Mathlib/LinearExtension/Subtype.lean:1152`), which is scoped at
ordinal-sum decompositions and lifts **exactly** (the marginal
`probLT` is invariant). The exceptional-set variant lifts only
**approximately** — deleting `k := |X^exc|` elements perturbs every
marginal `probLT` by at most `2k/(n−k+1)` (`LinearExt.exc_perturb`,
F6b, `ExcPerturb.lean:351`).

## The honest conclusion shape — and a `MA-Sig §4.2 §F` correction

`OrdinalDecomp.hasBalancedPair_lift` transfers `HasBalancedPair` from
sub-poset to ambient **on the nose**. The exceptional-set lift
*cannot*: a balanced pair on `X ∖ X^exc` has `probLT ∈ [1/3, 2/3]`
*inside the subtype*, and `exc_perturb` only places its ambient
`probLT` in the **widened** window `[1/3 − ε, 2/3 + ε]` with
`ε = 2k/(n−k+1) > 0` (for `k ≥ 1`). So a free-standing theorem

```
  HasBalancedPair {a // a ∉ X^exc}  →  HasBalancedPair X
```

— which is how `docs/state-MA-Sig-Session1.md §4.2 §F` (the pinned
`excPerturbLift`) transcribed paper item (iii) — is **ill-posed**: it
is a *false* proposition for every `k ≥ 1` (the perturbation genuinely
moves the marginal off `[1/3, 2/3]`). The ticket body itself names the
honest target — "transfer … **with `o(1)` error**" — so this file
delivers the *honest* shapes and **block-reports** the §4.2 §F
transcription error (it should be re-pinned; see the state doc).

The honest content is two theorems:

* **`hasApproxBalancedPair_lift_exc`** — the genuine perturbation lift:
  a balanced pair on `{a // a ∉ S}` lifts to an **`ε`-approximately
  balanced** pair on `α`, `ε = 2|S|/(|α|−|S|+1)`. At `S = ∅` this is
  `ε = 0` and `HasApproxBalancedPair α 0 ↔ HasBalancedPair α`
  (`hasApproxBalancedPair_zero_iff`) — i.e. the extension genuinely
  *generalises* the exact `OrdinalDecomp.hasBalancedPair_lift` shape.

* **`not_isGammaCounterexample_of_exc_balanced`** (alias
  `excPerturbLift`) — the form the proof-by-contradiction headline
  actually needs: if `ε ≤ γ`, an exceptional-set balanced pair
  **refutes** `IsGammaCounterexample α γ`. This is sound because a
  `γ`-counterexample forbids *every* incomparable pair from having
  `min(p, 1−p) ≥ 1/3 − γ`, whereas the lifted pair has
  `min(p, 1−p) ≥ 1/3 − ε ≥ 1/3 − γ`. In the headline body
  (`MA-Sig §4.3 §10–§11`) the contradiction target is interchangeable:
  `n ≥ n₀(γ, T)` is chosen precisely so `ε < γ`.

## Non-vacuous instantiation (`§6`)

The lift is exercised on the genuine S7-F bridge object: the 3×3 grid
`Fin 3 × Fin 3` minus the corner `(0,0)` — which is exactly
`Xexc gridChainLiftData` (`grid_Xexc`, the F7a witness's exceptional
set). `gridMinusCorner_hasBalancedPair` discharges
`HasBalancedPair (X ∖ X^exc)` via the genuine coordinate-swap
automorphism, and `grid_hasApproxBalancedPair` runs the lift end to
end, producing `HasApproxBalancedPair (Fin 3 × Fin 3) (2/9)` with
`ε = 2/9 < 1/3` a genuine, non-degenerate window constraint.

## Cross-references

* `lean/OneThird/Step8/ExcPerturb.lean:351` — `LinearExt.exc_perturb`
  (F6b), the `probLT`-level perturbation bound this file lifts.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152` —
  `OrdinalDecomp.hasBalancedPair_lift`, the exact ordinal-sum lift
  this file extends.
* `lean/OneThird/Step8/BridgeLayered.lean` — sub-ticket C; produces
  the `LayeredDecomposition` on `X ∖ X^exc` whose balanced pair
  (delivered by Piece 6) this file lifts back to `X`.
* `step8.tex:2009-2089` — `lem:layered-from-step7`; item (iii) is the
  perturbation lift.
* `docs/state-MA-Sig-Session1.md §4.2 §F` — the pinned (ill-posed)
  `excPerturbLift`; block-reported here.

No `sorry`. No new `axiom` (`AXIOMS.md` unchanged).
-/

namespace OneThird

open Finset LinearExt

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — Approximately balanced pairs -/

/-- A pair `(x, y)` is **`ε`-approximately balanced** if
`1/3 − ε ≤ Pr[x <_L y] ≤ 2/3 + ε`. At `ε = 0` this is `IsBalanced`. -/
def IsApproxBalanced (ε : ℚ) (x y : α) : Prop :=
  (1 : ℚ) / 3 - ε ≤ probLT x y ∧ probLT x y ≤ 2 / 3 + ε

/-- `α` **has an `ε`-approximately balanced pair** iff some incomparable
pair is `ε`-approximately balanced. At `ε = 0` this is
`HasBalancedPair` (`hasApproxBalancedPair_zero_iff`); for `ε > 0` it is
the honest target of the exceptional-set perturbation lift — the paper's
"`HasBalancedPair` with `o(1)` error". -/
def HasApproxBalancedPair (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] (ε : ℚ) : Prop :=
  ∃ x y : α, (x ∥ y) ∧ IsApproxBalanced ε x y

/-- **At `ε = 0` the approximate notion is the exact one.** This is the
sanity check that `HasApproxBalancedPair` genuinely *generalises*
`HasBalancedPair`: the exceptional-set lift at `S = ∅` (no deletion,
`ε = 0`) collapses to the exact `OrdinalDecomp.hasBalancedPair_lift`
shape. -/
theorem hasApproxBalancedPair_zero_iff :
    HasApproxBalancedPair α 0 ↔ HasBalancedPair α := by
  unfold HasApproxBalancedPair HasBalancedPair IsApproxBalanced IsBalanced
  simp only [sub_zero, add_zero]

/-- The approximate-balance window only widens as `ε` grows. -/
theorem HasApproxBalancedPair.mono {ε ε' : ℚ}
    (h : HasApproxBalancedPair α ε) (hle : ε ≤ ε') :
    HasApproxBalancedPair α ε' := by
  obtain ⟨x, y, hinc, hb1, hb2⟩ := h
  exact ⟨x, y, hinc, by linarith, by linarith⟩

/-- An exact balanced pair is `ε`-approximately balanced for every
`ε ≥ 0`. -/
theorem HasBalancedPair.toApprox (h : HasBalancedPair α) {ε : ℚ}
    (hε : 0 ≤ ε) : HasApproxBalancedPair α ε := by
  obtain ⟨x, y, hinc, hb1, hb2⟩ := h
  exact ⟨x, y, hinc, by linarith, by linarith⟩

/-! ### §2 — Transport along an order iso; the swap-automorphism witness

`probLT_orderIso` (`ExcPerturb.lean:116`) already transports `probLT`
along an order iso; here we package the `HasBalancedPair` transport and
the swap-automorphism balanced-pair witness used by the non-vacuity
instantiation of `§6`. -/

/-- `HasBalancedPair` transports along an order isomorphism. -/
theorem hasBalancedPair_orderIso {β γ : Type*}
    [PartialOrder β] [Fintype β] [DecidableEq β]
    [PartialOrder γ] [Fintype γ] [DecidableEq γ]
    (e : β ≃o γ) (h : HasBalancedPair β) : HasBalancedPair γ := by
  obtain ⟨x, y, hinc, hbal⟩ := h
  refine ⟨e x, e y, ⟨fun hle => hinc.1 (e.le_iff_le.mp hle),
    fun hle => hinc.2 (e.le_iff_le.mp hle)⟩, ?_, ?_⟩
  · rw [← probLT_orderIso e x y]; exact hbal.1
  · rw [← probLT_orderIso e x y]; exact hbal.2

/-- **A swap automorphism forces `probLT = 1/2`.** If an order
automorphism `e` of `α` exchanges `x` and `y` (`x ≠ y`), then
`probLT x y = probLT y x` (by `probLT_orderIso`), and the two
one-sided probabilities sum to one, so each is `1/2`. -/
theorem probLT_eq_half_of_swap (e : α ≃o α) {x y : α}
    (hxy : e x = y) (hyx : e y = x) (hne : x ≠ y) :
    probLT x y = 1 / 2 := by
  have hsym : probLT x y = probLT y x := by
    have h := probLT_orderIso e x y
    rwa [hxy, hyx] at h
  have hsum := probLT_add_probLT_of_ne hne
  linarith

/-- **A swap automorphism witnesses a balanced incomparable pair.** If
an order automorphism exchanges `x ≠ y`, then `x ∥ y` (a comparability
either way would, by `e`-monotonicity, force the reverse, hence
equality) and `(x, y)` is balanced (`probLT = 1/2`). -/
theorem incomp_isBalanced_of_swap (e : α ≃o α) {x y : α}
    (hxy : e x = y) (hyx : e y = x) (hne : x ≠ y) :
    (x ∥ y) ∧ IsBalanced x y := by
  have hhalf := probLT_eq_half_of_swap e hxy hyx hne
  refine ⟨⟨fun hle => ?_, fun hle => ?_⟩, ?_, ?_⟩
  · have hle' : y ≤ x := by have := e.monotone hle; rwa [hxy, hyx] at this
    exact hne (le_antisymm hle hle')
  · have hle' : x ≤ y := by have := e.monotone hle; rwa [hxy, hyx] at this
    exact hne (le_antisymm hle' hle)
  · rw [hhalf]; norm_num
  · rw [hhalf]; norm_num

/-- A poset admitting a swap automorphism between two distinct elements
`HasBalancedPair`. -/
theorem hasBalancedPair_of_swap (e : α ≃o α) {x y : α}
    (hxy : e x = y) (hyx : e y = x) (hne : x ≠ y) :
    HasBalancedPair α :=
  ⟨x, y, (incomp_isBalanced_of_swap e hxy hyx hne).1,
    (incomp_isBalanced_of_swap e hxy hyx hne).2⟩

/-! ### §3 — The exceptional-set balanced-pair lift -/

/-- The cardinality of the deletion subtype: `|X ∖ S| = |X| − |S|`. -/
lemma card_compl_subtype (S : Finset α) :
    Fintype.card {a : α // a ∉ S} = Fintype.card α - S.card := by
  rw [Fintype.card_subtype_compl (fun a : α => a ∈ S)]
  congr 1
  exact Fintype.card_coe S

/-- If the deletion subtype `{a // a ∉ S}` has a balanced pair, it has
`≥ 2` elements, so `|S| + 2 ≤ |α|` — exactly the cardinality side
condition `exc_perturb` requires. Derived rather than assumed. -/
lemma card_le_of_hasBalancedPair_compl (S : Finset α)
    (h : HasBalancedPair {a : α // a ∉ S}) :
    S.card + 2 ≤ Fintype.card α := by
  obtain ⟨x, y, hinc, _⟩ := h
  have hne : x ≠ y := fun he => Incomp.irrefl x (he ▸ hinc)
  have h2 : 1 < Fintype.card {a : α // a ∉ S} :=
    Fintype.one_lt_card_iff.mpr ⟨x, y, hne⟩
  rw [card_compl_subtype] at h2
  omega

/-- **The exceptional-set balanced-pair lift** (paper
`lem:layered-from-step7` item (iii), `step8.tex:2080-2089`).

The exceptional-set-deletion analogue of
`OrdinalDecomp.hasBalancedPair_lift`. A balanced pair on the deletion
subtype `{a // a ∉ S}` lifts to an **`ε`-approximately balanced** pair
of `α`, with `ε = 2|S|/(|α|−|S|+1)` — the `exc_perturb` (F6b) bound.

The lift is *genuine*: the same pair `(x, y)` is carried (incomparability
transfers because the subtype order is the restricted ambient order), and
`exc_perturb` bounds how far deleting `S` moved its marginal. The
approximate window is unavoidable — see the module docstring on why the
exact `HasBalancedPair α` conclusion (`MA-Sig §4.2 §F`) is ill-posed. -/
theorem hasApproxBalancedPair_lift_exc (S : Finset α)
    (h : HasBalancedPair {a : α // a ∉ S}) :
    HasApproxBalancedPair α
      (2 * (S.card : ℚ) / (Fintype.card α - S.card + 1 : ℚ)) := by
  obtain ⟨x, y, hinc, hbal⟩ := h
  have hcard : S.card + 2 ≤ Fintype.card α :=
    card_le_of_hasBalancedPair_compl S ⟨x, y, hinc, hbal⟩
  have hpert := exc_perturb S hcard x y
  rw [abs_le] at hpert
  refine ⟨x.val, y.val, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro hle; exact hinc.1 hle
  · intro hle; exact hinc.2 hle
  · linarith [hpert.1, hbal.1]
  · linarith [hpert.2, hbal.2]

/-! ### §4 — The `γ`-counterexample refutation (the headline-ready form)

The proof-by-contradiction headline (`MA-Sig §4.3`) carries
`IsGammaCounterexample α γ` and needs the exceptional-set balanced pair
to *contradict* it. That contradiction is sound and honest: the lift
places the ambient marginal of the carried pair within `ε` of
`[1/3, 2/3]`, so `min(p, 1−p) ≥ 1/3 − ε`, and once `ε ≤ γ` this
overshoots the `γ`-counterexample ceiling `min(p, 1−p) < 1/3 − γ`. -/

/-- **An exceptional-set balanced pair refutes a `γ`-counterexample.**

If `{a // a ∉ S}` has a balanced pair and the `exc_perturb` error
`ε = 2|S|/(|α|−|S|+1)` satisfies `ε ≤ γ`, then `α` is **not** a
`γ`-counterexample.

This is the honest, satisfiable replacement for the ill-posed
`MA-Sig §4.2 §F` `excPerturbLift : … → HasBalancedPair α` (see the
module docstring): the proof transfers genuine content — both
one-sided marginals of the carried pair are pinned `≥ 1/3 − γ`, which a
`γ`-counterexample forbids. -/
theorem not_isGammaCounterexample_of_exc_balanced (γ : ℚ) (S : Finset α)
    (hε : 2 * (S.card : ℚ) / (Fintype.card α - S.card + 1 : ℚ) ≤ γ)
    (h : HasBalancedPair {a : α // a ∉ S}) :
    ¬ IsGammaCounterexample α γ := by
  intro hCex
  obtain ⟨x, y, hinc, hbal⟩ := h
  have hcard : S.card + 2 ≤ Fintype.card α :=
    card_le_of_hasBalancedPair_compl S ⟨x, y, hinc, hbal⟩
  have hincα : (x.val ∥ y.val) :=
    ⟨fun hle => hinc.1 hle, fun hle => hinc.2 hle⟩
  have hne : x ≠ y := fun he => Incomp.irrefl x (he ▸ hinc)
  have hsum := probLT_add_probLT_of_ne hne
  have hpxy := exc_perturb S hcard x y
  have hpyx := exc_perturb S hcard y x
  rw [abs_le] at hpxy hpyx
  -- Both one-sided ambient marginals are pinned `≥ 1/3 − γ`.
  have hlow_xy : (1 : ℚ) / 3 - γ ≤ probLT x.val y.val := by
    linarith [hpxy.1, hbal.1]
  have hlow_yx : (1 : ℚ) / 3 - γ ≤ probLT y.val x.val := by
    have hyx_sub : (1 : ℚ) / 3 ≤ probLT y x := by linarith [hbal.2, hsum]
    linarith [hpyx.1, hyx_sub]
  -- … which overshoots the `γ`-counterexample ceiling for this pair.
  have hCexPair := hCex x.val y.val hincα
  have hmin : (1 : ℚ) / 3 - γ ≤ min (probLT x.val y.val) (probLT y.val x.val) :=
    le_min hlow_xy hlow_yx
  linarith [hCexPair.2]

/-- **`excPerturbLift`** — the `MA-Sig §4.2 §F` contract name, re-pinned
to the honest conclusion.

`MA-Sig §4.2 §F` pinned `excPerturbLift` with conclusion
`HasBalancedPair α`; that is ill-posed (the perturbation widens the
balance window by `ε > 0` — module docstring). This is the corrected
contract endpoint: same role in the headline body (`MA-Sig §4.3 §10`),
honest conclusion `¬ IsGammaCounterexample α γ`. The unused `hγ_pos`
of the original pin is dropped (positivity of `γ` is not needed — the
`<` vs `≥` clash on `min(p, 1−p)` does not use it). -/
theorem excPerturbLift (γ : ℚ) (Xexc : Finset α)
    (hXexc_small : 2 * (Xexc.card : ℚ)
      / (Fintype.card α - Xexc.card + 1 : ℚ) ≤ γ)
    (hBP_sub : HasBalancedPair {a : α // a ∉ Xexc}) :
    ¬ IsGammaCounterexample α γ :=
  not_isGammaCounterexample_of_exc_balanced γ Xexc hXexc_small hBP_sub

/-! ### §5 — The `Xᶜ` carrier variant

The S7-F-C bridge (`BridgeLayered.lean`) builds its
`LayeredDecomposition` on `↥((Xexc D)ᶜ) = {a // a ∈ (Xexc D)ᶜ}`, while
`exc_perturb` is stated on `{a // a ∉ S}`. The two carriers are
order-isomorphic (`complNotMemOrderIso`); the variants below let the
S7-F-Z integration consume whichever shape the bridge emits. -/

/-- The order iso between the two ways of writing the deletion subtype:
`{a // a ∈ Tᶜ}` and `{a // a ∉ T}`. -/
def complNotMemOrderIso (T : Finset α) :
    {a : α // a ∈ Tᶜ} ≃o {a : α // a ∉ T} where
  toFun := fun x => ⟨x.val, Finset.mem_compl.mp x.2⟩
  invFun := fun x => ⟨x.val, Finset.mem_compl.mpr x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_rel_iff' := Iff.rfl

/-- **The exceptional-set lift, `Xᶜ`-carrier variant.** Same as
`hasApproxBalancedPair_lift_exc`, with the bridge's `↥(Tᶜ)` carrier. -/
theorem hasApproxBalancedPair_lift_exc_compl (T : Finset α)
    (h : HasBalancedPair {a : α // a ∈ Tᶜ}) :
    HasApproxBalancedPair α
      (2 * (T.card : ℚ) / (Fintype.card α - T.card + 1 : ℚ)) :=
  hasApproxBalancedPair_lift_exc T
    (hasBalancedPair_orderIso (complNotMemOrderIso T) h)

/-- **The `γ`-counterexample refutation, `Xᶜ`-carrier variant.** -/
theorem not_isGammaCounterexample_of_exc_balanced_compl (γ : ℚ)
    (T : Finset α)
    (hε : 2 * (T.card : ℚ) / (Fintype.card α - T.card + 1 : ℚ) ≤ γ)
    (h : HasBalancedPair {a : α // a ∈ Tᶜ}) :
    ¬ IsGammaCounterexample α γ :=
  not_isGammaCounterexample_of_exc_balanced γ T hε
    (hasBalancedPair_orderIso (complNotMemOrderIso T) h)

/-- Restrict an order automorphism `e` of `α` that fixes a finset `S`
setwise to an order automorphism of the deletion subtype
`{a // a ∉ S}`. Used by the `§6` non-vacuity witness; also a wiring
helper for S7-F-Z. -/
def restrictNotMemOrderIso (e : α ≃o α) (S : Finset α)
    (hS : ∀ a : α, a ∈ S ↔ e a ∈ S) :
    {a : α // a ∉ S} ≃o {a : α // a ∉ S} where
  toFun := fun x => ⟨e x.val, fun hmem => x.2 ((hS x.val).mpr hmem)⟩
  invFun := fun x => ⟨e.symm x.val, fun hmem => x.2 (by
    have h1 := (hS (e.symm x.val)).mp hmem
    rwa [e.apply_symm_apply] at h1)⟩
  left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
  right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
  map_rel_iff' := e.map_rel_iff'

/-! ### §6 — Non-vacuous instantiation: the 3×3 grid minus `X^exc`

The genuine S7-F bridge object. `gridChainLiftData` (the F7a witness,
`ConcreteChainLiftData.lean`) has `Xexc gridChainLiftData = {(0,0)}`
(`grid_Xexc`), so its ground set `X ∖ X^exc` is the 3×3 grid minus its
corner. We discharge `HasBalancedPair (X ∖ X^exc)` via the genuine
coordinate-swap automorphism (`(0,1)` and `(1,0)` are exchanged, hence
incomparable and balanced) and run the lift end to end. -/

namespace ExcBalancedLiftGrid

/-- The coordinate-swap order automorphism of the 3×3 grid. -/
def gridSwap : (Fin 3 × Fin 3) ≃o (Fin 3 × Fin 3) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv := Prod.swap_swap
  right_inv := Prod.swap_swap
  map_rel_iff' := by
    intro a b
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The 3×3 grid minus its corner `(0,0)` — the genuine ground set
`X ∖ X^exc` of the S7-F-C bridge witness (`Xexc gridChainLiftData`,
`grid_Xexc`). -/
abbrev GridMinusCorner : Type :=
  {a : Fin 3 × Fin 3 //
    a ∉ ({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3))}

/-- The coordinate swap, restricted to `GridMinusCorner` (it fixes the
corner `(0,0)`, hence the corner-complement is invariant). -/
def gridCornerSwap : GridMinusCorner ≃o GridMinusCorner :=
  restrictNotMemOrderIso gridSwap
    ({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3)) (by decide)

/-- The grid point `(0,1)`, off the corner. -/
def gridP01 : GridMinusCorner := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩

/-- The grid point `(1,0)`, off the corner. -/
def gridP10 : GridMinusCorner := ⟨((1 : Fin 3), (0 : Fin 3)), by decide⟩

/-- **`X ∖ X^exc` has a balanced pair.** The grid points `(0,1)` and
`(1,0)` are exchanged by the coordinate swap, hence incomparable and
balanced (`probLT = 1/2`). -/
theorem gridMinusCorner_hasBalancedPair : HasBalancedPair GridMinusCorner := by
  have hxy : gridCornerSwap gridP01 = gridP10 := by
    apply Subtype.ext; decide
  have hyx : gridCornerSwap gridP10 = gridP01 := by
    apply Subtype.ext; decide
  have hne : gridP01 ≠ gridP10 := by
    intro h; exact absurd (Subtype.ext_iff.mp h) (by decide)
  exact hasBalancedPair_of_swap gridCornerSwap hxy hyx hne

/-- The `exc_perturb` error for deleting the single corner from the
3×3 grid: `ε = 2·1/(9−1+1) = 2/9`. -/
theorem grid_exc_eps :
    2 * ((({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3)).card : ℚ))
      / ((Fintype.card (Fin 3 × Fin 3) : ℚ)
        - (({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3)).card : ℚ)
        + 1) = 2 / 9 := by
  rw [Finset.card_singleton]
  norm_num [Fintype.card_prod, Fintype.card_fin]

/-- **Non-vacuous instantiation of the exceptional-set lift.**
Running `hasApproxBalancedPair_lift_exc` on the genuine S7-F bridge
object — the 3×3 grid minus `Xexc gridChainLiftData = {(0,0)}` —
produces `HasApproxBalancedPair (Fin 3 × Fin 3) (2/9)`. The deletion is
genuinely non-empty (`S = {(0,0)} ≠ ∅`, so `ε = 2/9 > 0`); the lift
genuinely fires (the hypothesis `HasBalancedPair (X ∖ X^exc)` is a
true, non-vacuous proposition); and `ε = 2/9 < 1/3`, so the resulting
window `[1/9, 8/9]` is a genuine constraint, not a degenerate one. -/
theorem grid_hasApproxBalancedPair :
    HasApproxBalancedPair (Fin 3 × Fin 3) (2 / 9) := by
  have h := hasApproxBalancedPair_lift_exc
    ({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3))
    gridMinusCorner_hasBalancedPair
  rwa [grid_exc_eps] at h

/-- **Non-vacuous instantiation of the `γ`-counterexample refutation.**
`excPerturbLift` on the same grid object: the grid minus its corner has
a balanced pair, so the full grid is not a `(2/9)`-counterexample.
(`γ = 2/9` is a large threshold — the lift only needs `ε ≤ γ` — so the
demonstration exercises the refutation mechanism end to end; in the
headline body `n ≥ n₀(γ, T)` drives `ε` genuinely below the operative
`γ < 1/6`.) -/
theorem grid_not_isGammaCounterexample :
    ¬ IsGammaCounterexample (Fin 3 × Fin 3) (2 / 9) := by
  refine excPerturbLift (2 / 9)
    ({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3)) ?_
    gridMinusCorner_hasBalancedPair
  rw [grid_exc_eps]

end ExcBalancedLiftGrid

end OneThird
