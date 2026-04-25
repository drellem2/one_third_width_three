/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.Case3Enum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Bitwise
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

/-! Bit-arithmetic helper for the recursion: `placed ^^^ bit e < placed`
when bit `e` of `placed` is set. -/

private lemma one_shiftLeft_eq (e : ℕ) : (1 <<< e : ℕ) = 2 ^ e := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private lemma bit_eq_two_pow (e : ℕ) : (bit e : ℕ) = 2 ^ e := by
  unfold bit; exact one_shiftLeft_eq e

/-- `testBit'` matches `Nat.testBit`. -/
lemma testBit'_iff_testBit {m e : ℕ} :
    testBit' m e = true ↔ Nat.testBit m e = true := by
  unfold testBit' bit
  rw [one_shiftLeft_eq]
  rw [bne_iff_ne, ne_eq]
  -- Goal: ¬ (m &&& 2^e = 0) ↔ Nat.testBit m e = true.
  -- Rewrite (m AND 2^e) using a testBit characterization.
  constructor
  · intro hne
    -- m AND 2^e ≠ 0 ⇒ ∃ i, testBit (m AND 2^e) i = true.
    -- The only candidate is i = e (testBit_and + testBit_two_pow filters).
    by_contra hb
    apply hne
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i = e
    · subst hi
      have hfalse : Nat.testBit m i = false := by
        cases ht : Nat.testBit m i with
        | true => exact absurd ht hb
        | false => rfl
      simp [hfalse]
    · simp [Nat.testBit_two_pow]
      intro _
      exact fun h => hi h.symm
  · intro h hzero
    have : (m &&& 2 ^ e).testBit e = false := by simp [hzero]
    rw [Nat.testBit_and, Nat.testBit_two_pow_self] at this
    simp at this
    rw [this] at h
    exact Bool.false_ne_true h

lemma xor_bit_lt {placed e : ℕ} (h : testBit' placed e = true) :
    placed ^^^ bit e < placed := by
  rw [bit_eq_two_pow]
  have hbit : Nat.testBit placed e = true := testBit'_iff_testBit.mp h
  apply Nat.lt_of_testBit e
  · -- testBit (placed ^^^ 2^e) e = false.
    rw [Nat.testBit_xor, hbit, Nat.testBit_two_pow_self]; rfl
  · exact hbit
  · intro j hj
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    have hne : e ≠ j := Nat.ne_of_lt hj
    simp [hne]

/-- Congruence: `cleStep` only reads `f` at indices strictly less than
`placed`, so any two arrays that agree on those indices yield equal
results. -/
lemma cleStep_congr (pred : Array Nat) (n placed : ℕ) (f g : Array Nat)
    (h : ∀ i, i < placed → f.getD i 0 = g.getD i 0) :
    cleStep pred n placed f = cleStep pred n placed g := by
  unfold cleStep
  -- Both sides are `(List.range n).foldl`.  Generalise the accumulator
  -- and induct on the list.
  suffices H : ∀ (L : List ℕ) (acc : ℕ),
      L.foldl
        (fun acc e =>
          if testBit' placed e then
            let prev := placed ^^^ bit e
            let pe := pred.getD e 0
            if (pe &&& prev) == pe then acc + f.getD prev 0
            else acc
          else acc) acc =
      L.foldl
        (fun acc e =>
          if testBit' placed e then
            let prev := placed ^^^ bit e
            let pe := pred.getD e 0
            if (pe &&& prev) == pe then acc + g.getD prev 0
            else acc
          else acc) acc by
    exact H (List.range n) 0
  intro L
  induction L with
  | nil => intro acc; rfl
  | cons e L ih =>
    intro acc
    simp only [List.foldl_cons]
    by_cases hbit : testBit' placed e = true
    · simp only [hbit, ↓reduceIte]
      by_cases hclo : ((pred.getD e 0) &&& (placed ^^^ bit e)) == (pred.getD e 0)
      · simp only [hclo, ↓reduceIte]
        have hlt : placed ^^^ bit e < placed := xor_bit_lt hbit
        rw [h _ hlt]
        exact ih _
      · simp only [hclo, ↓reduceIte]
        exact ih _
    · have hbit' : testBit' placed e = false := by
        cases h' : testBit' placed e with
        | true => exact absurd h' hbit
        | false => rfl
      simp only [hbit', Bool.false_eq_true, ↓reduceIte]
      exact ih _

/-- The DP table at indices already processed agrees with `clERec`. -/
lemma cleArrUpTo_getD_eq (pred : Array Nat) (n : ℕ) :
    ∀ k i : ℕ, i < k → i < 1 <<< n →
      (cleArrUpTo pred n k).getD i 0 = clERec pred n i := by
  intro k
  induction k with
  | zero => intro i hi _; omega
  | succ k ih =>
    intro i hi hN
    rw [cleArrUpTo_succ]
    by_cases hk : k = 0
    · -- k = 0: cleArrUpTo (k+1) = cleArrUpTo k.  i < k+1 = 1 forces i = 0.
      subst hk
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [↓reduceIte, cleArrUpTo_zero, clERec_zero]
      -- Show ((Array.replicate (1 <<< n) 0).set! 0 1).getD 0 0 = 1.
      rw [Array.getD_eq_getD_getElem?]
      have hN' : 0 < 1 <<< n := hN
      have : ((Array.replicate (1 <<< n) 0).set! 0 1)[0]? = some 1 := by
        rw [show ((Array.replicate (1 <<< n) 0).set! 0 1) =
              ((Array.replicate (1 <<< n) 0).setIfInBounds 0 1) from rfl]
        rw [Array.getElem?_setIfInBounds_self_of_lt]
        simp [Array.size_replicate]; exact hN'
      rw [this]; rfl
    · -- k ≥ 1.
      simp only [hk, ↓reduceIte]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · -- i < k: index unchanged by set!.
        have hki : k ≠ i := Nat.ne_of_gt hlt
        rw [show ((cleArrUpTo pred n k).set! k _) =
              ((cleArrUpTo pred n k).setIfInBounds k _) from rfl]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hki]
        rw [← Array.getD_eq_getD_getElem?]
        exact ih i hlt hN
      · -- i = k: f[k] gets set to cleStep pred n k (cleArrUpTo pred n k).
        subst heq
        rw [show ((cleArrUpTo pred n i).set! i _) =
              ((cleArrUpTo pred n i).setIfInBounds i _) from rfl]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt
              (by rw [cleArrUpTo_size]; exact hN)]
        -- Goal: cleStep pred n i (cleArrUpTo pred n i) = clERec pred n i.
        have hi_pos : 0 < i := Nat.pos_of_ne_zero hk
        obtain ⟨pl, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        rw [clERec_succ]
        apply cleStep_congr
        intro j hj
        have hjN : j < 1 <<< n := lt_of_lt_of_le hj (le_of_lt hN)
        -- LHS: ih gives the value at j.
        rw [ih j hj hjN]
        -- RHS: Array.ofFn at index j < size = pl.succ.
        have hj_size : j < (Array.ofFn (fun (i : Fin pl.succ) =>
            clERec pred n i.val)).size := by
          rw [Array.size_ofFn]; exact hj
        rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem hj_size,
            Array.getElem_ofFn]
        rfl

/-- **Main bridge:** the imperative DP equals `clERec` at the full mask. -/
theorem countLinearExtensions_eq_clERec (pred : Array Nat) (n : ℕ) :
    countLinearExtensions pred n = clERec pred n ((1 <<< n) - 1) := by
  have hN : 0 < 1 <<< n := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos n
  have hN' : (1 <<< n) - 1 < 1 <<< n := Nat.sub_lt hN Nat.one_pos
  unfold countLinearExtensions
  show (((List.range (1 <<< n)).foldl _
      ((Array.replicate (1 <<< n) 0).set! 0 1))).getD ((1 <<< n) - 1) 0 = _
  exact cleArrUpTo_getD_eq pred n (1 <<< n) ((1 <<< n) - 1) hN' hN'

/-! ### §4 — Combinatorial bijection: `clERec` at the full mask equals `numLinExt`.

The DP recursion `clERec pred n placed = Σ_e clERec pred n (placed XOR bit e)`
mirrors the maximum-element decomposition for `numLinExt` of the
sub-poset induced on the bitmask of `placed` (downward-closed).  Strong
induction on `placed.popCount` carries through.

The remaining content is the math: a `numLinExt`-side recursion identity
matching the DP recursion.  This is the standard "remove a maximal
element" decomposition of linear extensions and lives across roughly
the same line-count as the `OrdinalDecomp.numLinExt_eq` proof in
`OneThird/Mathlib/LinearExtension/Subtype.lean` (≈ 200 LoC).  It is
deferred to a follow-up work item; the §3 bridge above provides the
clean `clERec`-side target into which that math content will plug.
-/

end Case3Enum
end Step8
end OneThird
