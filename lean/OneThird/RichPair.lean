/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset
import OneThird.LinearExtension
import OneThird.Step1.LocalCoords

/-!
# Rich pairs and the Step 1 local interface theorem

The core Step 1 definitions — `localCoord`, `signMarker`,
`ExternalEquiv`, `rawFiber`, `IsGoodFiber`, `goodFiberSet`, `badSet`,
and their basic API — live in `OneThird/Step1/LocalCoords.lean`.

This file states and proves the existence-level content of the Step 1
main theorem (`thm:interface` in `step1.tex`): the coordinate bound of
part (i) and the good/bad fiber partition of part (ii). The
BK-move classification (part (iii)) and the bad-set strip
decomposition (part (iv)) remain out of scope.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **Step 1 Local Interface Theorem** (`thm:interface`, `step1.tex`).
For a width-3 poset and a rich pair `(x, y)`, every linear extension
has coordinates bounded by `t(x, y)`, and `L(P)` partitions as the
disjoint union of the good-fiber set and the bad set.

This bundles parts (i) and (ii) of the paper. Parts (iii) (BK-move
classification) and (iv) (bad-set strip decomposition) are stronger
statements tracked in downstream formalization items. -/
theorem localInterfaceTheorem
    (_hP : HasWidthAtMost α 3) (T : ℕ) (x y : α) (_hxy : IsRich T x y) :
    (∀ L : LinearExt α,
        (localCoord x y L).1 ≤ commonNbhdLength x y ∧
        (localCoord x y L).2 ≤ commonNbhdLength x y) ∧
    (goodFiberSet x y ∪ badSet x y = Finset.univ) ∧
    (Disjoint (goodFiberSet x y) (badSet x y)) :=
  ⟨fun L => ⟨localCoord_fst_le x y L, localCoord_snd_le x y L⟩,
   goodFiberSet_union_badSet x y,
   goodFiberSet_disjoint_badSet x y⟩

end OneThird
