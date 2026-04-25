/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.Case3Enum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Case-3 enumeration: `countLinearExtensions ↔ numLinExt` (Path A3)

DP correctness theorem for `Case3Enum.countLinearExtensions`.  Given a
predecessor-bitmask `pred : Array Nat` of length `n` whose bits encode
a strict partial order on `Fin n`, the bottom-up subset DP

```
countLinearExtensions pred n  : ℕ
```

equals the number of linear extensions of `Fin n` with the partial order
derived from `pred`:

```
countLinearExtensions pred n = numLinExt (Fin n) [predOrder pred]
```

## Outline

* `predLT pred u v` — the strict relation `u <_pred v`, i.e.
  bit `u` of `pred[v]` is set.
* `ValidPredMask pred n` — irreflexivity and transitivity of `predLT`
  on `Fin n` (the closure-canonical partial-order axioms).
* `predOrder` — the resulting `PartialOrder (Fin n)`.
* `clERec pred n placed` — clean recursive form of the DP, defined by
  `Nat.strongRecOn`.
* `countLinearExtensions_eq_clERec` — the foldl-form imperative DP
  equals `clERec` at `placed = 2 ^ n - 1`.
* `clERec_eq_numLinExt` — `clERec` at the full mask equals
  `numLinExt`.

## References

`step8.tex` §G4 `lem:bounded-irreducible-balanced`.  Companion to
`OneThird.Step8.BoundedIrreducibleBalanced` §3 (caller-side discharge
of F5a's Bool certificate), which cites this identification as the
critical Bool↔Prop bridge for `Case3Enum.hasBalancedPair`.
-/

namespace OneThird
namespace Step8
namespace Case3Enum

open Finset

/-! ### §1 — Predecessor relation and partial order on `Fin n` -/

variable {n : ℕ}

/-- The strict relation `u <_pred v`: bit `u` of `pred[v]` is set. -/
def predLT (pred : Array Nat) (u v : Fin n) : Prop :=
  testBit' (pred.getD v.val 0) u.val = true

instance (pred : Array Nat) (u v : Fin n) :
    Decidable (predLT pred u v) := by
  unfold predLT; infer_instance

/-- A pred-mask `pred : Array Nat` *encodes a strict partial order*
on `Fin n` if `predLT pred` is irreflexive and transitive.
Antisymmetry follows automatically. -/
structure ValidPredMask (pred : Array Nat) (n : ℕ) : Prop where
  irrefl : ∀ v : Fin n, ¬ predLT pred v v
  trans : ∀ u v w : Fin n, predLT pred u v → predLT pred v w →
    predLT pred u w

namespace ValidPredMask

variable {pred : Array Nat}

/-- Asymmetry of `predLT`. -/
lemma asymm (h : ValidPredMask pred n) {u v : Fin n}
    (huv : predLT pred u v) (hvu : predLT pred v u) : False :=
  h.irrefl u (h.trans u v u huv hvu)

end ValidPredMask

/-- The partial order on `Fin n` induced by a valid pred-mask:
`u ≤ v ↔ u = v ∨ predLT pred u v`. -/
@[reducible]
def predOrder (pred : Array Nat) (h : ValidPredMask pred n) :
    PartialOrder (Fin n) where
  le u v := u = v ∨ predLT pred u v
  lt u v := predLT pred u v
  le_refl u := Or.inl rfl
  le_trans u v w huv hvw := by
    rcases huv with rfl | huv
    · exact hvw
    · rcases hvw with rfl | hvw
      · exact Or.inr huv
      · exact Or.inr (h.trans u v w huv hvw)
  le_antisymm u v huv hvu := by
    rcases huv with rfl | huv
    · rfl
    · rcases hvu with rfl | hvu
      · rfl
      · exact (h.asymm huv hvu).elim
  lt_iff_le_not_ge := by
    intro u v
    constructor
    · intro hlt
      refine ⟨Or.inr hlt, ?_⟩
      rintro (heq | hge)
      · exact h.irrefl v (heq ▸ hlt)
      · exact h.asymm hlt hge
    · rintro ⟨hle, hnle⟩
      rcases hle with heq | huv
      · exact (hnle (Or.inl heq.symm)).elim
      · exact huv

lemma predOrder_lt_iff (pred : Array Nat) (h : ValidPredMask pred n)
    (u v : Fin n) :
    @LT.lt (Fin n) (predOrder pred h).toLT u v ↔ predLT pred u v := Iff.rfl

lemma predOrder_le_iff (pred : Array Nat) (h : ValidPredMask pred n)
    (u v : Fin n) :
    @LE.le (Fin n) (predOrder pred h).toLE u v ↔ u = v ∨ predLT pred u v :=
  Iff.rfl

/-! ### §2 — Clean recursive form of the DP -/

/-- `clERec pred n placed` — the abstract recursion that the imperative
DP table fills bottom-up. -/
def clERec (pred : Array Nat) (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | placed + 1 =>
      cleStep pred n (placed + 1)
        (Array.ofFn (fun i : Fin (placed + 1) => clERec pred n i.val))

@[simp] lemma clERec_zero (pred : Array Nat) (n : ℕ) :
    clERec pred n 0 = 1 := by
  rw [clERec]

lemma clERec_succ (pred : Array Nat) (n pl : ℕ) :
    clERec pred n (pl + 1) =
      cleStep pred n (pl + 1)
        (Array.ofFn (fun i : Fin (pl + 1) =>
          clERec pred n i.val)) := by
  rw [clERec]

/-! ### §3 — Bridge: the foldl-form imperative DP equals `clERec` -/

/-- The intermediate array after `(List.range k).foldl` over the
DP fill loop, started from `f₀ = (Array.replicate (1<<<n) 0).set! 0 1`. -/
def cleArrUpTo (pred : Array Nat) (n : ℕ) (k : ℕ) : Array Nat :=
  (List.range k).foldl
    (fun (f : Array Nat) (placed : ℕ) =>
      if placed = 0 then f
      else f.set! placed (cleStep pred n placed f))
    ((Array.replicate (1 <<< n) 0).set! 0 1)

lemma cleArrUpTo_zero (pred : Array Nat) (n : ℕ) :
    cleArrUpTo pred n 0 =
      (Array.replicate (1 <<< n) 0).set! 0 1 := by
  simp [cleArrUpTo]

lemma cleArrUpTo_succ (pred : Array Nat) (n k : ℕ) :
    cleArrUpTo pred n (k + 1) =
      (if k = 0 then cleArrUpTo pred n k
       else (cleArrUpTo pred n k).set! k
              (cleStep pred n k (cleArrUpTo pred n k))) := by
  unfold cleArrUpTo
  rw [List.range_succ, List.foldl_append]
  simp

/-- The DP table has size `1 <<< n` throughout the loop. -/
lemma cleArrUpTo_size (pred : Array Nat) (n k : ℕ) :
    (cleArrUpTo pred n k).size = 1 <<< n := by
  induction k with
  | zero => simp [cleArrUpTo_zero]
  | succ k ih =>
    rw [cleArrUpTo_succ]
    split_ifs
    · exact ih
    · rw [show (cleArrUpTo pred n k).set! k _ = (cleArrUpTo pred n k).setIfInBounds k _ from rfl,
          Array.size_setIfInBounds, ih]

end Case3Enum
end Step8
end OneThird
