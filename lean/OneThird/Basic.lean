/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/

import Mathlib.Order.Antichain
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Preorder.Chain

/-!
# OneThird — scaffolding for the width-3 1/3–2/3 theorem

This module sets up shared imports and the `Incomp` incomparability
predicate used throughout the formalization.
-/

namespace OneThird

variable {α : Type*}

/-- `Incomp x y` holds iff `x` and `y` are incomparable in a preorder:
neither `x ≤ y` nor `y ≤ x`. Written `x ∥ y` in the mathematical text. -/
def Incomp [LE α] (x y : α) : Prop := ¬ x ≤ y ∧ ¬ y ≤ x

@[inherit_doc] scoped infix:50 " ∥ " => Incomp

namespace Incomp

variable [Preorder α]

lemma symm {x y : α} (h : x ∥ y) : y ∥ x := ⟨h.2, h.1⟩

lemma irrefl (x : α) : ¬ x ∥ x := fun h => h.1 (le_refl x)

end Incomp

end OneThird
