/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.Step8.Case2Rotation

/-!
# Step 8 — Case-3 port: orientation lemma (`mg-8487`)

Lean port of **Lemma 2.1** of `docs/case3-port-arc/rem-enumeration-proof.md`
§2 (`mg-75ef`, *"Linear orientation on 3-antichains; user input
2026-05-06"*) — the **orientation lemma** that underpins the
case-3 out-of-scope discharge.

## Mathematical content

For any three pairwise distinct elements `x₁, x₂, x₃` of a finite
poset `α`, the **majority orientation**
`x ≪ y ⟺ Pr[x <_L y] > 2/3` (under the uniform linear-extension
distribution) is *acyclic* on the 3-set: it is **not** possible to
have all three cyclic majorities

```
Pr[x₁ <_L x₂] > 2/3,  Pr[x₂ <_L x₃] > 2/3,  Pr[x₃ <_L x₁] > 2/3.
```

## Proof outline (per `mg-75ef` §2)

Suppose for contradiction that all three exceed `2/3`. Each
forward-probability bound `Pr[xᵢ <_L xⱼ] > 2/3` is equivalent to the
backward-probability bound `Pr[xⱼ <_L xᵢ] < 1/3` via
`probLT_add_probLT_of_ne`. The "rotation cover" identity
(`rotation_sum_ge_one`, `step8.tex:2909-2914`) records that on every
linear extension at least one of the three events
`{x₂ <_L x₁}`, `{x₃ <_L x₂}`, `{x₁ <_L x₃}` holds (their
simultaneous negations would force the cycle `x₁ <_L x₂ <_L x₃ <_L x₁`,
impossible in a total order). Hence

```
Pr[x₂ <_L x₁] + Pr[x₃ <_L x₂] + Pr[x₁ <_L x₃] ≥ 1.
```

Substituting the three `< 1/3` complements gives `< 1`, a
contradiction.

The same identity is invoked in the paper's bipartite Case 2
discharge (`step8.tex:2904-2914`); here we use it in **contrapositive
form**, encoded as `OneThird.Step8.InSitu.rotation_sum_ge_one`
(`Case2Rotation.lean:253`).

## Foundational role (per `mg-5bf9` §3)

`docs/case3-port-arc/linear-majority-alignment.md` §3 identifies this
lemma as foundational for the case-3 out-of-scope chain:

* The orientation lemma rules out **3-cycle-symmetric configurations**
  (`mg-75ef` §2 Remark 2.4) from the proof's territory under (NBP),
  so the AXIOMS Step 1 ("share a coordinate") need not be repaired
  for cyclic configurations.
* Corollary: WLOG every Case-3 antichain `{x₁, x₂, x₃}` admits a
  *linear* majority order `x₁ ≪ x₂ ≪ x₃` after relabelling
  (`mg-75ef` §2 Cor 2.3).

## Dependencies and trust surface

Built on the in-tree primitives `probLT`, `probLT_add_probLT_of_ne`
(`Mathlib/LinearExtension/Fintype.lean`) and
`OneThird.Step8.InSitu.rotation_sum_ge_one`
(`Step8/Case2Rotation.lean`). `#print axioms` reports only the
mathlib trio `[propext, Classical.choice, Quot.sound]` — **no new
axioms**.

This file is **standalone and parallel-dispatchable**: it does not
depend on any in-flight A8-S2-cont infrastructure or other case-3 port
tickets.

## References

* `docs/case3-port-arc/rem-enumeration-proof.md` §2 (`mg-75ef`).
* `docs/case3-port-arc/linear-majority-alignment.md` §3 (`mg-5bf9`).
* `step8.tex:2909-2914` — the rotation-cover identity, in its
  bipartite Case 2 forward use.
* `OneThird.Step8.InSitu.rotation_sum_ge_one` —
  `Step8/Case2Rotation.lean:253` (mg-5a62, A8-S2-rotation).
-/

namespace OneThird
namespace Step8
namespace Case3Port

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-- **Orientation lemma — Lemma 2.1 of `mg-75ef` §2.**

For pairwise distinct `x₁, x₂, x₃ : α`, if both
`Pr[x₁ <_L x₂] > 2/3` and `Pr[x₂ <_L x₃] > 2/3`, then it is **not**
the case that `Pr[x₃ <_L x₁] > 2/3`. Equivalently, the majority
orientation `x ≪ y ⟺ Pr[x <_L y] > 2/3` is acyclic on every
3-set of pairwise distinct elements (and hence — under (NBP), where
every incomparable pair has probability outside `[1/3, 2/3]` — is a
linear order on every 3-antichain).

The hypotheses `h12, h23, h13` are pairwise distinctness; the
hypotheses `hp12, hp23` are the two given strict majorities. The
conclusion is the negation of the third strict majority that would
close a 3-cycle. -/
theorem majority_orientation_transitive_on_3antichain
    {x_1 x_2 x_3 : α} (h12 : x_1 ≠ x_2) (h23 : x_2 ≠ x_3) (h13 : x_1 ≠ x_3)
    (hp12 : (2 : ℚ) / 3 < probLT x_1 x_2)
    (hp23 : (2 : ℚ) / 3 < probLT x_2 x_3) :
    ¬ ((2 : ℚ) / 3 < probLT x_3 x_1) := by
  intro hp31
  -- Rotation-cover identity (contrapositive of the cycle
  -- `x₁ <_L x₂ <_L x₃ <_L x₁`):
  --   `probLT x₂ x₁ + probLT x₃ x₂ + probLT x₁ x₃ ≥ 1`.
  have hrot := OneThird.Step8.InSitu.rotation_sum_ge_one h12 h23 h13
  -- Each forward `> 2/3` gives the backward `< 1/3` via
  -- `probLT x y + probLT y x = 1`.
  have h21 : probLT x_2 x_1 = 1 - probLT x_1 x_2 := by
    have := probLT_add_probLT_of_ne h12; linarith
  have h32 : probLT x_3 x_2 = 1 - probLT x_2 x_3 := by
    have := probLT_add_probLT_of_ne h23; linarith
  have h13' : probLT x_1 x_3 = 1 - probLT x_3 x_1 := by
    have := probLT_add_probLT_of_ne (Ne.symm h13); linarith
  rw [h21, h32, h13'] at hrot
  linarith

end Case3Port
end Step8
end OneThird
