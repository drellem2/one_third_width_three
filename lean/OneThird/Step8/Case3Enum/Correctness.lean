/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.Case3Enum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
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
      rw [hfalse, Bool.false_and]
    · rw [Nat.testBit_two_pow]
      have hne : e ≠ i := fun heq => hi heq.symm
      have : decide (e = i) = false := decide_eq_false hne
      rw [this, Bool.and_false]
  · intro h hzero
    have htest : (m &&& 2 ^ e).testBit e = false := by
      simp only [hzero, Nat.zero_testBit]
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at htest
    rw [htest] at h
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


/-! ### §4 — Combinatorial bijection: `clERec ((1<<<n) − 1) = numLinExt`.

The DP value `clERec pred n placed` counts *valid prefixes* whose
image is the support of `placed`: injections
`f : Fin (popcount placed) → Fin n` with `f i ∈` (support of `placed`)
and that respect the global pred order at every prefix (each
predecessor of `f i` appears at a strictly earlier position).  At
`placed = (1 <<< n) − 1` this count matches `numLinExt (Fin n)` for
`predOrder pred h`, via inversion.
-/

variable {n : ℕ}

/-! #### §4.1 — `maskSet`: bitmask ↔ `Finset (Fin n)` -/

/-- The `Finset (Fin n)` corresponding to a bitmask `placed`. -/
def maskSet (n placed : ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => testBit' placed i.val = true)

@[simp] lemma mem_maskSet {placed : ℕ} {i : Fin n} :
    i ∈ maskSet n placed ↔ testBit' placed i.val = true := by
  simp [maskSet]

@[simp] lemma maskSet_zero : maskSet n 0 = ∅ := by
  ext i
  simp only [mem_maskSet, Finset.notMem_empty, iff_false]
  rw [testBit'_iff_testBit, Nat.zero_testBit]
  exact Bool.false_ne_true

lemma testBit'_full {i : Fin n} :
    testBit' ((1 <<< n) - 1) i.val = true := by
  rw [testBit'_iff_testBit, one_shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true i.isLt

@[simp] lemma maskSet_full : maskSet n ((1 <<< n) - 1) = Finset.univ := by
  ext i
  simp only [mem_maskSet, Finset.mem_univ, iff_true]
  exact testBit'_full

/-- `testBit'` agrees pointwise with `Nat.testBit`. -/
lemma testBit'_eq (m i : ℕ) : testBit' m i = Nat.testBit m i := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h; exact testBit'_iff_testBit.mp h
  · intro h
    rcases h_eq : testBit' m i with _ | _
    · exfalso
      have := (testBit'_iff_testBit (m := m) (e := i)).mpr h
      rw [h_eq] at this; exact Bool.false_ne_true this
    · rfl

lemma testBit'_xor_eq {placed e i : ℕ} (he : i ≠ e) :
    testBit' (placed ^^^ bit e) i = testBit' placed i := by
  rw [testBit'_eq, testBit'_eq, bit_eq_two_pow,
      Nat.testBit_xor, Nat.testBit_two_pow]
  have h : decide (e = i) = false := decide_eq_false (fun h' => he h'.symm)
  rw [h]; cases Nat.testBit placed i <;> rfl

lemma testBit'_xor_self_of_set {placed e : ℕ}
    (he : testBit' placed e = true) :
    testBit' (placed ^^^ bit e) e = false := by
  rw [testBit'_eq] at he
  rw [testBit'_eq, bit_eq_two_pow, Nat.testBit_xor,
      Nat.testBit_two_pow_self, he]
  rfl

lemma maskSet_xor_bit {placed : ℕ} {e : Fin n}
    (he : testBit' placed e.val = true) :
    maskSet n (placed ^^^ bit e.val) = (maskSet n placed).erase e := by
  ext i
  simp only [mem_maskSet, Finset.mem_erase, ne_eq]
  by_cases hie : i = e
  · subst hie
    rw [testBit'_xor_self_of_set he]
    simp
  · have h_iv_ne : i.val ≠ e.val := fun h => hie (Fin.ext h)
    rw [testBit'_xor_eq h_iv_ne]
    exact ⟨fun h => ⟨hie, h⟩, fun ⟨_, h⟩ => h⟩

lemma card_maskSet_xor_bit {placed : ℕ} {e : Fin n}
    (he : testBit' placed e.val = true) :
    (maskSet n (placed ^^^ bit e.val)).card = (maskSet n placed).card - 1 := by
  rw [maskSet_xor_bit he, Finset.card_erase_of_mem (mem_maskSet.mpr he)]

/-! #### §4.2 — `ValidPrefix`: orderings of a Finset compatible with global pred -/

/-- A *valid prefix* on `S : Finset (Fin n)` is an injection
`Fin S.card → Fin n` whose image lies in `S`, and that respects the
global predecessor relation: every predecessor of `f i` (in the
global pred) appears at a strictly earlier position. -/
def ValidPrefix (pred : Array Nat) (n : ℕ) (S : Finset (Fin n)) : Type :=
  { f : Fin S.card → Fin n //
      Function.Injective f ∧
      (∀ i, f i ∈ S) ∧
      (∀ i, ∀ u : Fin n, predLT pred u (f i) →
        ∃ j : Fin S.card, j.val < i.val ∧ f j = u) }

namespace ValidPrefix

variable {pred : Array Nat} {S : Finset (Fin n)}

/-- The underlying function of a valid prefix. -/
@[reducible] def toFun (P : ValidPrefix pred n S) : Fin S.card → Fin n := P.val

lemma inj (P : ValidPrefix pred n S) : Function.Injective P.toFun := P.property.1

lemma mem (P : ValidPrefix pred n S) (i : Fin S.card) : P.toFun i ∈ S :=
  P.property.2.1 i

lemma predClosed (P : ValidPrefix pred n S) (i : Fin S.card) (u : Fin n)
    (h : predLT pred u (P.toFun i)) :
    ∃ j : Fin S.card, j.val < i.val ∧ P.toFun j = u := P.property.2.2 i u h

/-- Image of a valid prefix equals `S` (by pigeonhole). -/
lemma image_eq (P : ValidPrefix pred n S) :
    Finset.univ.image P.toFun = S := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    rw [← hi]; exact P.mem i
  · rw [Finset.card_image_of_injective _ P.inj, Finset.card_univ, Fintype.card_fin]

instance instFintype (pred : Array Nat) (n : ℕ) (S : Finset (Fin n)) :
    Fintype (ValidPrefix pred n S) := by
  classical
  unfold ValidPrefix
  exact Subtype.fintype _

end ValidPrefix

/-! #### §4.3 — DP-valid predicate -/

/-- The "DP-valid last element" predicate: `e ∈ S` and every predecessor
of `e` (in `pred`) is in `S \ {e}`. -/
def IsDPValid (pred : Array Nat) (n : ℕ) (S : Finset (Fin n)) (e : Fin n) : Prop :=
  e ∈ S ∧ ∀ u : Fin n, predLT pred u e → u ∈ S.erase e

instance (pred : Array Nat) (n : ℕ) (S : Finset (Fin n)) (e : Fin n) :
    Decidable (IsDPValid pred n S e) := by
  unfold IsDPValid; infer_instance

/-! #### §4.4 — Bijection: `ValidPrefix S` ≃ Σ_{e DP-valid} `ValidPrefix (S.erase e)` -/

/-- Forward map: a valid prefix on a nonempty `S` is sent to the pair
`(last element, restriction to all but last position)`. -/
private noncomputable def stripLast {pred : Array Nat} {S : Finset (Fin n)}
    (hS : S.Nonempty) (P : ValidPrefix pred n S) :
    Σ e : { e : Fin n // IsDPValid pred n S e },
      ValidPrefix pred n (S.erase e.val) := by
  classical
  set k : ℕ := S.card - 1 with hk_def
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS
  have hk_lt : k < S.card := by omega
  set e : Fin n := P.toFun ⟨k, hk_lt⟩ with he_def
  have he_mem : e ∈ S := P.mem ⟨k, hk_lt⟩
  have he_dp : IsDPValid pred n S e := by
    refine ⟨he_mem, ?_⟩
    intro u hu
    obtain ⟨j, hjlt, hju⟩ := P.predClosed ⟨k, hk_lt⟩ u hu
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hue
      apply Nat.ne_of_lt hjlt
      have h1 : P.toFun j = P.toFun ⟨k, hk_lt⟩ := by rw [hju, hue, he_def]
      have h2 : j = ⟨k, hk_lt⟩ := P.inj h1
      exact congrArg Fin.val h2
    · rw [← hju]; exact P.mem j
  have hcard_e : (S.erase e).card = k := by
    rw [Finset.card_erase_of_mem he_mem]
  refine ⟨⟨e, he_dp⟩, ?_⟩
  refine ⟨fun i => P.toFun ⟨i.val, ?_⟩, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_eq i.isLt hcard_e |>.trans hk_lt
  · intro i j hij
    have hi_lt : i.val < S.card :=
      lt_of_lt_of_eq i.isLt hcard_e |>.trans hk_lt
    have hj_lt : j.val < S.card :=
      lt_of_lt_of_eq j.isLt hcard_e |>.trans hk_lt
    have h1 : (⟨i.val, hi_lt⟩ : Fin S.card) = ⟨j.val, hj_lt⟩ := P.inj hij
    apply Fin.ext
    have : (⟨i.val, hi_lt⟩ : Fin S.card).val = (⟨j.val, hj_lt⟩ : Fin S.card).val :=
      congrArg Fin.val h1
    exact this
  · intro i
    have hi_lt : i.val < S.card :=
      lt_of_lt_of_eq i.isLt hcard_e |>.trans hk_lt
    refine Finset.mem_erase.mpr ⟨?_, P.mem ⟨i.val, hi_lt⟩⟩
    intro heq
    have h1 : P.toFun ⟨i.val, hi_lt⟩ = P.toFun ⟨k, hk_lt⟩ := by
      change _ = e; exact heq
    have h2 : (⟨i.val, hi_lt⟩ : Fin S.card) = ⟨k, hk_lt⟩ := P.inj h1
    have h3 : i.val = k := by
      have : (⟨i.val, hi_lt⟩ : Fin S.card).val = (⟨k, hk_lt⟩ : Fin S.card).val :=
        congrArg Fin.val h2
      exact this
    have hilt' : i.val < k :=
      lt_of_lt_of_eq i.isLt hcard_e
    omega
  · intro i u hu
    have hi_lt : i.val < S.card :=
      lt_of_lt_of_eq i.isLt hcard_e |>.trans hk_lt
    obtain ⟨j, hjlt, hju⟩ := P.predClosed ⟨i.val, hi_lt⟩ u hu
    have hi_lt_k : i.val < k :=
      lt_of_lt_of_eq i.isLt hcard_e
    have hj_lt_k : j.val < k := by omega
    have hj_bd : j.val < (S.erase e).card :=
      lt_of_lt_of_eq hj_lt_k hcard_e.symm
    refine ⟨⟨j.val, hj_bd⟩, hjlt, ?_⟩
    show P.toFun ⟨j.val, _⟩ = u
    convert hju

/-- Inverse map: a DP-valid `e` and a prefix on `S.erase e` reassemble
into a prefix on `S` by appending `e` at the last position. -/
private noncomputable def appendLast {pred : Array Nat} {S : Finset (Fin n)}
    {e : Fin n} (he : IsDPValid pred n S e)
    (Q : ValidPrefix pred n (S.erase e)) :
    ValidPrefix pred n S := by
  classical
  have he_mem : e ∈ S := he.1
  have hcard_eq : (S.erase e).card = S.card - 1 := Finset.card_erase_of_mem he_mem
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr ⟨e, he_mem⟩
  refine
    ⟨fun i =>
      if hi : i.val < (S.erase e).card then Q.toFun ⟨i.val, hi⟩ else e,
      ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val < (S.erase e).card
    · by_cases hj : j.val < (S.erase e).card
      · simp only [hi, hj, ↓reduceDIte] at hij
        have h1 : (⟨i.val, hi⟩ : Fin (S.erase e).card) = ⟨j.val, hj⟩ := Q.inj hij
        apply Fin.ext
        have := h1
        rw [Fin.mk.injEq] at this
        exact this
      · simp only [hi, hj, ↓reduceDIte] at hij
        have hQmem : Q.toFun ⟨i.val, hi⟩ ∈ S.erase e := Q.mem ⟨i.val, hi⟩
        rw [hij] at hQmem
        exact absurd hQmem (Finset.notMem_erase e S)
    · by_cases hj : j.val < (S.erase e).card
      · simp only [hi, hj, ↓reduceDIte] at hij
        have hQmem : Q.toFun ⟨j.val, hj⟩ ∈ S.erase e := Q.mem ⟨j.val, hj⟩
        rw [← hij] at hQmem
        exact absurd hQmem (Finset.notMem_erase e S)
      · have hi' : i.val = S.card - 1 := by have := i.isLt; omega
        have hj' : j.val = S.card - 1 := by have := j.isLt; omega
        exact Fin.ext (hi'.trans hj'.symm)
  · intro i
    by_cases hi : i.val < (S.erase e).card
    · simp only [hi, ↓reduceDIte]
      exact Finset.mem_of_mem_erase (Q.mem ⟨i.val, hi⟩)
    · simp only [hi, ↓reduceDIte]; exact he_mem
  · intro i u hu
    by_cases hi : i.val < (S.erase e).card
    · simp only [hi, ↓reduceDIte] at hu
      obtain ⟨j, hjlt, hju⟩ := Q.predClosed ⟨i.val, hi⟩ u hu
      have hj_lt_S : j.val < S.card :=
        lt_of_lt_of_eq j.isLt hcard_eq |>.trans_le (Nat.sub_le _ _)
      refine ⟨⟨j.val, hj_lt_S⟩, hjlt, ?_⟩
      simp only [show j.val < (S.erase e).card from j.isLt, ↓reduceDIte]
      convert hju
    · simp only [hi, ↓reduceDIte] at hu
      obtain ⟨huu_ne, huu_S⟩ := Finset.mem_erase.mp (he.2 u hu)
      have hQ_image : Finset.univ.image Q.toFun = S.erase e := Q.image_eq
      have hu_image : u ∈ Finset.univ.image Q.toFun := by
        rw [hQ_image]; exact Finset.mem_erase.mpr ⟨huu_ne, huu_S⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu_image
      obtain ⟨j, hju⟩ := hu_image
      have hj_S : j.val < S.card :=
        lt_of_lt_of_eq j.isLt hcard_eq |>.trans_le (Nat.sub_le _ _)
      have hi_eq : i.val = S.card - 1 := by have := i.isLt; omega
      have hjlt : j.val < i.val := by
        rw [hi_eq]
        exact lt_of_lt_of_eq j.isLt hcard_eq
      refine ⟨⟨j.val, hj_S⟩, hjlt, ?_⟩
      simp only [show j.val < (S.erase e).card from j.isLt, ↓reduceDIte]
      convert hju

/-! #### §4.5 — `lastOf`: the last element placed by a valid prefix

We pivot away from the dependent `Σ`-Equiv approach (whose `right_inv`
requires `HEq` across types `ValidPrefix (S.erase e)` for different
`e`).  Instead, for each fixed DP-valid `e`, the *fibre*
`{P : ValidPrefix S // lastOf P = e}` is in bijection with
`ValidPrefix (S.erase e)` over a *fixed* type, so no `HEq` is needed.
Summing fibre cardinalities recovers `#ValidPrefix S`. -/

/-- The last element placed by `P : ValidPrefix S` (assuming `S` is
nonempty). -/
private noncomputable def lastOf {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) (P : ValidPrefix pred n S) : Fin n :=
  P.toFun ⟨S.card - 1, Nat.sub_lt hS Nat.one_pos⟩

private lemma lastOf_isDPValid {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) (P : ValidPrefix pred n S) :
    IsDPValid pred n S (lastOf hS P) := by
  classical
  set k : ℕ := S.card - 1 with hk_def
  have hk_lt : k < S.card := Nat.sub_lt hS Nat.one_pos
  refine ⟨P.mem ⟨k, hk_lt⟩, ?_⟩
  intro u hu
  obtain ⟨j, hjlt, hju⟩ := P.predClosed ⟨k, hk_lt⟩ u hu
  refine Finset.mem_erase.mpr ⟨?_, by rw [← hju]; exact P.mem j⟩
  intro hueq
  apply Nat.ne_of_lt hjlt
  have h1 : P.toFun j = P.toFun ⟨k, hk_lt⟩ := by
    show _ = lastOf hS P
    rw [hju, hueq]
  exact congrArg Fin.val (P.inj h1)

/-! #### §4.6 — `fiberEquiv`: `{P // lastOf P = e} ≃ ValidPrefix (S.erase e)` -/

/-- Forward: the restriction of a valid prefix on `S` (with last
element fixed to `e`) to its first `S.card - 1` positions, viewed as
a valid prefix on `S.erase e`. -/
private noncomputable def stripAt {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) {e : Fin n} (he : IsDPValid pred n S e)
    (P : ValidPrefix pred n S) (hP : lastOf hS P = e) :
    ValidPrefix pred n (S.erase e) := by
  classical
  have hcard_e : (S.erase e).card = S.card - 1 :=
    Finset.card_erase_of_mem he.1
  have hcard_lt : S.card - 1 < S.card := Nat.sub_lt hS Nat.one_pos
  have hP' : P.toFun ⟨S.card - 1, hcard_lt⟩ = e := hP
  refine ⟨fun i => P.toFun ⟨i.val, ?_⟩, ?_, ?_, ?_⟩
  · -- bound: i.val < S.card
    have h := i.isLt.trans_eq hcard_e
    omega
  · -- injectivity
    intro i j hij
    have hi : i.val < S.card := by have := i.isLt.trans_eq hcard_e; omega
    have hj : j.val < S.card := by have := j.isLt.trans_eq hcard_e; omega
    have h1 : (⟨i.val, hi⟩ : Fin S.card) = ⟨j.val, hj⟩ := P.inj hij
    rw [Fin.ext_iff] at h1
    exact Fin.ext h1
  · -- image in `S.erase e`
    intro i
    have hi : i.val < S.card := by have := i.isLt.trans_eq hcard_e; omega
    refine Finset.mem_erase.mpr ⟨?_, P.mem ⟨i.val, hi⟩⟩
    intro hueq
    have h1 : P.toFun ⟨i.val, hi⟩ = P.toFun ⟨S.card - 1, hcard_lt⟩ :=
      hueq.trans hP'.symm
    have h2 : (⟨i.val, hi⟩ : Fin S.card) = ⟨S.card - 1, hcard_lt⟩ := P.inj h1
    have h3 : i.val = S.card - 1 := by rw [Fin.ext_iff] at h2; exact h2
    have hi_lt : i.val < S.card - 1 := i.isLt.trans_eq hcard_e
    omega
  · -- predClosed
    intro i u hu
    have hi : i.val < S.card := by have := i.isLt.trans_eq hcard_e; omega
    obtain ⟨j, hjlt, hju⟩ := P.predClosed ⟨i.val, hi⟩ u hu
    have hi_lt' : i.val < S.card - 1 := i.isLt.trans_eq hcard_e
    have hj_lt' : j.val < S.card - 1 := lt_trans hjlt hi_lt'
    refine ⟨⟨j.val, hj_lt'.trans_eq hcard_e.symm⟩, hjlt, ?_⟩
    show P.toFun ⟨j.val, _⟩ = u
    convert hju

/-- Inverse: append `e` at the last position. (This is the same
construction as `appendLast`, repackaged so its `lastOf` is visibly
`e`.) -/
private noncomputable def appendAt {pred : Array Nat} {S : Finset (Fin n)}
    {e : Fin n} (he : IsDPValid pred n S e)
    (Q : ValidPrefix pred n (S.erase e)) :
    ValidPrefix pred n S :=
  appendLast he Q

/-- Direct extraction lemma: the underlying function of `appendLast`,
in `.val` form so it patterns-matches the `↑` coercion that arises
after `Subtype.ext`. -/
private lemma appendLast_val_apply {pred : Array Nat} {S : Finset (Fin n)}
    {e : Fin n} (he : IsDPValid pred n S e) (Q : ValidPrefix pred n (S.erase e))
    (i : Fin S.card) :
    (appendLast he Q).val i =
      (if hi : i.val < (S.erase e).card then Q.val ⟨i.val, hi⟩ else e) := by
  rfl

/-- Direct extraction lemma: the underlying function of `stripAt`. -/
private lemma stripAt_val_apply {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) {e : Fin n} (he : IsDPValid pred n S e)
    (P : ValidPrefix pred n S) (hP : lastOf hS P = e)
    (i : Fin (S.erase e).card) :
    ∃ hi : i.val < S.card, (stripAt hS he P hP).val i = P.val ⟨i.val, hi⟩ := by
  classical
  have hcard_e : (S.erase e).card = S.card - 1 :=
    Finset.card_erase_of_mem he.1
  have hi : i.val < S.card := by have := i.isLt.trans_eq hcard_e; omega
  exact ⟨hi, rfl⟩

private lemma lastOf_appendLast {pred : Array Nat} {S : Finset (Fin n)}
    {e : Fin n} (he : IsDPValid pred n S e) (Q : ValidPrefix pred n (S.erase e))
    (hS : 0 < S.card) :
    lastOf hS (appendLast he Q) = e := by
  classical
  have hcard_e : (S.erase e).card = S.card - 1 :=
    Finset.card_erase_of_mem he.1
  show (appendLast he Q).val ⟨S.card - 1, _⟩ = e
  rw [appendLast_val_apply]
  have hge : ¬ (S.card - 1) < (S.erase e).card := by
    rw [hcard_e]; exact lt_irrefl _
  exact dif_neg hge

private lemma stripAt_appendLast {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) {e : Fin n} (he : IsDPValid pred n S e)
    (Q : ValidPrefix pred n (S.erase e)) :
    stripAt hS he (appendLast he Q) (lastOf_appendLast he Q hS) = Q := by
  classical
  apply Subtype.ext
  funext i
  -- Goal: `(stripAt ... (appendLast he Q) ...).val i = Q.val i`.
  -- stripAt's val applied at i is `(appendLast he Q).val ⟨i.val, _⟩`.
  show (appendLast he Q).val ⟨i.val, _⟩ = Q.val i
  rw [appendLast_val_apply]
  rw [dif_pos i.isLt]

private lemma appendLast_stripAt {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) {e : Fin n} (he : IsDPValid pred n S e)
    (P : ValidPrefix pred n S) (hP : lastOf hS P = e) :
    appendLast he (stripAt hS he P hP) = P := by
  classical
  have hcard_e : (S.erase e).card = S.card - 1 :=
    Finset.card_erase_of_mem he.1
  have hcard_lt : S.card - 1 < S.card := Nat.sub_lt hS Nat.one_pos
  have hP' : P.val ⟨S.card - 1, hcard_lt⟩ = e := hP
  apply Subtype.ext
  funext i
  rw [appendLast_val_apply]
  by_cases hi : i.val < (S.erase e).card
  · rw [dif_pos hi]
    -- Goal: (stripAt ...).val ⟨i.val, hi⟩ = P.val i
    show P.val ⟨i.val, _⟩ = P.val i
    rfl
  · rw [dif_neg hi]
    -- i.val ≥ (S.erase e).card = S.card - 1, and i.val < S.card, so i.val = S.card - 1.
    have hi_eq : i.val = S.card - 1 := by
      have h1 : i.val < S.card := i.isLt
      have h2 : (S.erase e).card ≤ i.val := Nat.le_of_not_lt hi
      rw [hcard_e] at h2
      omega
    have heq : i = ⟨S.card - 1, hcard_lt⟩ := Fin.ext hi_eq
    rw [heq]
    exact hP'.symm

/-- The fibre Equiv: avoiding the dependent `Σ`-Equiv right_inv `HEq`
issue, since both sides have the same fixed type. -/
private noncomputable def fiberEquiv {pred : Array Nat} {S : Finset (Fin n)}
    (hS : 0 < S.card) {e : Fin n} (he : IsDPValid pred n S e) :
    { P : ValidPrefix pred n S // lastOf hS P = e } ≃
      ValidPrefix pred n (S.erase e) where
  toFun := fun ⟨P, hP⟩ => stripAt hS he P hP
  invFun := fun Q => ⟨appendLast he Q, lastOf_appendLast he Q hS⟩
  left_inv := fun ⟨P, hP⟩ => by
    apply Subtype.ext
    exact appendLast_stripAt hS he P hP
  right_inv := fun Q => stripAt_appendLast hS he Q

/-! #### §4.7 — Cardinality decomposition

`#ValidPrefix S = Σ_{e DP-valid} #ValidPrefix (S.erase e)` -/

/-- The set of DP-valid elements of `S`, packaged as a `Finset`. -/
private def dpValidSet (pred : Array Nat) (S : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun e => IsDPValid pred n S e)

private lemma mem_dpValidSet {pred : Array Nat} {S : Finset (Fin n)} {e : Fin n} :
    e ∈ dpValidSet pred S ↔ IsDPValid pred n S e := by
  simp [dpValidSet]

/-- Card decomposition: partitioning `ValidPrefix S` by `lastOf`,
the fibre over each DP-valid `e` is `ValidPrefix (S.erase e)`. -/
private lemma card_validPrefix_eq_sum (pred : Array Nat) (S : Finset (Fin n))
    (hS : 0 < S.card) :
    Fintype.card (ValidPrefix pred n S) =
      ∑ e ∈ dpValidSet pred S, Fintype.card (ValidPrefix pred n (S.erase e)) := by
  classical
  -- Partition `ValidPrefix S` by `lastOf`, which lands in `dpValidSet pred S`.
  have hpart :
      Fintype.card (ValidPrefix pred n S) =
        ∑ e ∈ dpValidSet pred S,
          ((Finset.univ : Finset (ValidPrefix pred n S)).filter
            (fun P => lastOf hS P = e)).card := by
    rw [← Finset.card_univ (α := ValidPrefix pred n S)]
    apply Finset.card_eq_sum_card_fiberwise (f := lastOf hS)
    intro P _
    rw [Finset.mem_coe, mem_dpValidSet]
    exact lastOf_isDPValid hS P
  rw [hpart]
  apply Finset.sum_congr rfl
  intro e he_mem
  rw [mem_dpValidSet] at he_mem
  -- card of the fibre = card of {P : ValidPrefix S // lastOf P = e} = #ValidPrefix (S.erase e)
  rw [show ((Finset.univ : Finset (ValidPrefix pred n S)).filter
        (fun P => lastOf hS P = e)).card =
      Fintype.card { P : ValidPrefix pred n S // lastOf hS P = e } from ?_]
  · exact Fintype.card_congr (fiberEquiv hS he_mem)
  · rw [Fintype.card_subtype]

/-! #### §4.8 — `cleStep ↔ Finset.sum`

Convert `cleStep`'s `(List.range n).foldl` over conditional add into a
`Finset.sum` indexed by `Fin n` filtered to DP-valid elements.
Requires `predBitsBoundedBy`: `pred.getD e 0` has no bits at positions
`≥ n` (a sanity hypothesis: callers via `predMaskOf` provide this). -/

/-- Bounded-bit hypothesis on `pred`: for every `e : Fin n`, the
predecessor mask `pred.getD e 0` has no bits set at positions `≥ n`. -/
def predBitsBoundedBy (pred : Array Nat) (n : ℕ) : Prop :=
  ∀ e : Fin n, ∀ b : ℕ, n ≤ b → testBit' (pred.getD e.val 0) b = false

/-- Per-step contribution of `cleStep`. -/
private def cleStepStep (pred : Array Nat) (placed : ℕ) (f : Array Nat) (e : ℕ) : ℕ :=
  if testBit' placed e then
    if (pred.getD e 0 &&& (placed ^^^ bit e)) == pred.getD e 0
    then f.getD (placed ^^^ bit e) 0 else 0
   else 0

/-- `cleStep` rewritten as a `Finset.sum` over `Finset.range n`. -/
private lemma cleStep_eq_sum_range (pred : Array Nat) (n placed : ℕ)
    (f : Array Nat) :
    cleStep pred n placed f = ∑ e ∈ Finset.range n, cleStepStep pred placed f e := by
  unfold cleStep cleStepStep
  -- Generalize: relate the foldl with arbitrary acc to an offset sum.
  suffices H : ∀ (k acc : ℕ),
      (List.range k).foldl
        (fun acc e =>
          if testBit' placed e then
            let prev : Nat := placed ^^^ bit e
            let pe := pred.getD e 0
            if (pe &&& prev) == pe then acc + f.getD prev 0 else acc
          else acc) acc =
      acc + ∑ e ∈ Finset.range k,
        (if testBit' placed e then
          if (pred.getD e 0 &&& (placed ^^^ bit e)) == pred.getD e 0
          then f.getD (placed ^^^ bit e) 0 else 0
         else 0) by
    have := H n 0
    simpa using this
  intro k
  induction k with
  | zero => intro acc; simp
  | succ k ih =>
    intro acc
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h_bit : testBit' placed k = true
    · simp only [h_bit, ↓reduceIte]
      by_cases h_clo : (pred.getD k 0 &&& (placed ^^^ bit k)) == pred.getD k 0
      · simp only [h_clo, ↓reduceIte]; omega
      · simp only [h_clo, Bool.false_eq_true, ↓reduceIte]; omega
    · have h_bit' : testBit' placed k = false := by
        cases h : testBit' placed k with
        | true => exact absurd h h_bit
        | false => rfl
      simp only [h_bit', Bool.false_eq_true, ↓reduceIte]
      omega

/-- Sum reindexing: `Finset.range n` and `Fin n` give the same sum. -/
private lemma sum_range_eq_sum_fin (n : ℕ) (g : ℕ → ℕ) :
    ∑ e ∈ Finset.range n, g e = ∑ e : Fin n, g e.val :=
  (Fin.sum_univ_eq_sum_range g n).symm

/-- Bridge: under bit-boundedness, `IsDPValid` (defined via `predLT` on
`Fin n`) matches the bitmask check inside `cleStep`. -/
private lemma isDPValid_iff_bits {pred : Array Nat} {n : ℕ}
    (h_bnd : predBitsBoundedBy pred n)
    {placed : ℕ} (e : Fin n) :
    IsDPValid pred n (maskSet n placed) e ↔
      (testBit' placed e.val = true ∧
       ((pred.getD e.val 0 &&& (placed ^^^ bit e.val)) == pred.getD e.val 0) = true) := by
  classical
  -- Helper: rewrite Bool == as decidable equality.
  have h_beq_iff : ∀ a b : ℕ, (a == b) = true ↔ a = b := fun a b => beq_iff_eq
  -- Unfold IsDPValid; the first conjunct matches via `mem_maskSet`.
  unfold IsDPValid
  rw [mem_maskSet]
  apply and_congr_right
  intro hpe
  -- Goal: (∀ u : Fin n, predLT pred u e → u ∈ (maskSet n placed).erase e) ↔ bitmask AND check.
  rw [h_beq_iff]
  constructor
  · -- LHS_2 → RHS_2
    intro h_pred
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_and]
    rw [← testBit'_eq, ← testBit'_eq]
    by_cases hbn : b < n
    · set u : Fin n := ⟨b, hbn⟩ with hu_def
      by_cases hube : u = e
      · -- b = e.val: pe has no bit at e.val (else u = e ∈ erase contradicts notMem_erase).
        have hb_eq : b = e.val := congrArg Fin.val hube
        rw [hb_eq, testBit'_xor_self_of_set hpe]
        have hpred_e : testBit' (pred.getD e.val 0) e.val = false := by
          by_contra hh
          have htest : testBit' (pred.getD e.val 0) e.val = true := by
            cases ht : testBit' (pred.getD e.val 0) e.val with
            | true => rfl
            | false => exact absurd ht hh
          have hpr : predLT pred e e := htest
          have := h_pred e hpr
          exact (Finset.notMem_erase e _) this
        rw [hpred_e]; rfl
      · -- b < n, b ≠ e.val: testBit prev b = testBit placed b. Use h_pred.
        have hb_ne : b ≠ e.val := fun h => hube (Fin.ext h)
        rw [testBit'_xor_eq hb_ne]
        cases htpe : testBit' (pred.getD e.val 0) b with
        | true =>
          have hpr : predLT pred u e := htpe
          have hum : u ∈ (maskSet n placed).erase e := h_pred u hpr
          rw [Finset.mem_erase, mem_maskSet] at hum
          rw [hum.2]; rfl
        | false => rfl
    · -- b ≥ n: pe has no bit there.
      have htest : testBit' (pred.getD e.val 0) b = false :=
        h_bnd e b (Nat.le_of_not_lt hbn)
      rw [htest]; rfl
  · -- RHS_2 → LHS_2
    intro h_bit u hu
    have hpr : testBit' (pred.getD e.val 0) u.val = true := hu
    have htpe : Nat.testBit (pred.getD e.val 0) u.val = true := by
      rw [← testBit'_eq]; exact hpr
    have hub_eq : Nat.testBit (pred.getD e.val 0 &&& (placed ^^^ bit e.val)) u.val =
                   Nat.testBit (pred.getD e.val 0) u.val := by
      rw [h_bit]
    rw [Nat.testBit_and] at hub_eq
    rw [htpe, Bool.true_and] at hub_eq
    -- hub_eq : Nat.testBit (placed ^^^ bit e.val) u.val = true
    rw [show Nat.testBit (placed ^^^ bit e.val) u.val =
            testBit' (placed ^^^ bit e.val) u.val from (testBit'_eq _ _).symm] at hub_eq
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hue
      rw [hue] at hub_eq
      rw [testBit'_xor_self_of_set hpe] at hub_eq
      exact Bool.false_ne_true hub_eq
    · rw [mem_maskSet]
      have hub_ne : u.val ≠ e.val := by
        intro h
        have hub_e : u = e := Fin.ext h
        rw [hub_e] at hub_eq
        rw [testBit'_xor_self_of_set hpe] at hub_eq
        exact Bool.false_ne_true hub_eq
      rw [testBit'_xor_eq hub_ne] at hub_eq
      exact hub_eq

/-- Per-step contribution rewritten in terms of `IsDPValid`. -/
private lemma cleStepStep_eq_ite_isDPValid {pred : Array Nat} {n : ℕ}
    (h_bnd : predBitsBoundedBy pred n)
    (placed : ℕ) (f : Array Nat) (e : Fin n) :
    cleStepStep pred placed f e.val =
      (if IsDPValid pred n (maskSet n placed) e
       then f.getD (placed ^^^ bit e.val) 0 else 0) := by
  classical
  unfold cleStepStep
  by_cases hbit : testBit' placed e.val = true
  · simp only [hbit, ↓reduceIte]
    by_cases hclo : ((pred.getD e.val 0 &&& (placed ^^^ bit e.val)) == pred.getD e.val 0) = true
    · simp only [hclo, ↓reduceIte]
      have h_iff := (isDPValid_iff_bits h_bnd e).mpr ⟨hbit, hclo⟩
      rw [if_pos h_iff]
    · have hclo' : ((pred.getD e.val 0 &&& (placed ^^^ bit e.val)) == pred.getD e.val 0) =
          false := by
        cases h : (pred.getD e.val 0 &&& (placed ^^^ bit e.val)) == pred.getD e.val 0 with
        | true => exact absurd h hclo
        | false => rfl
      simp only [hclo', Bool.false_eq_true, ↓reduceIte]
      have h_iff : ¬ IsDPValid pred n (maskSet n placed) e := by
        intro h_dp
        have h_bnd' := (isDPValid_iff_bits h_bnd e).mp h_dp
        rw [hclo'] at h_bnd'
        exact Bool.false_ne_true h_bnd'.2
      rw [if_neg h_iff]
  · have hbit' : testBit' placed e.val = false := by
      cases h : testBit' placed e.val with
      | true => exact absurd h hbit
      | false => rfl
    simp only [hbit', Bool.false_eq_true, ↓reduceIte]
    have h_iff : ¬ IsDPValid pred n (maskSet n placed) e := by
      intro h_dp
      have h_bnd' := (isDPValid_iff_bits h_bnd e).mp h_dp
      rw [hbit'] at h_bnd'
      exact Bool.false_ne_true h_bnd'.1
    rw [if_neg h_iff]

/-- Helper: `cleStepStep` is 0 for indices `e ≥ n` when `placed < (1 <<< n)`. -/
private lemma cleStepStep_of_ge (n : ℕ) (pred : Array Nat) (f : Array Nat)
    {placed : ℕ} (h_placed : placed < (1 <<< n))
    {e : ℕ} (he : n ≤ e) :
    cleStepStep pred placed f e = 0 := by
  have hbit : testBit' placed e = false := by
    rw [testBit'_eq]
    apply Nat.testBit_lt_two_pow
    rw [one_shiftLeft_eq] at h_placed
    exact lt_of_lt_of_le h_placed (Nat.pow_le_pow_right (by omega) he)
  unfold cleStepStep
  simp [hbit]

/-- **Main `cleStep ↔ Finset.sum` bridge.** -/
private lemma cleStep_eq_sum_dpValidSet {pred : Array Nat} {n : ℕ}
    (h_bnd : predBitsBoundedBy pred n)
    (placed : ℕ) (f : Array Nat) :
    cleStep pred n placed f =
      ∑ e ∈ dpValidSet pred (maskSet n placed),
        f.getD (placed ^^^ bit e.val) 0 := by
  classical
  rw [cleStep_eq_sum_range, sum_range_eq_sum_fin]
  -- ∑ e : Fin n, cleStepStep pred placed f e.val
  rw [show (∑ e : Fin n, cleStepStep pred placed f e.val) =
      ∑ e : Fin n, (if IsDPValid pred n (maskSet n placed) e
                    then f.getD (placed ^^^ bit e.val) 0 else 0) from ?_]
  · -- ∑ over `Fin n` with conditional → ∑ over filtered subset
    rw [← Finset.sum_filter]
    rfl
  · apply Finset.sum_congr rfl
    intro e _
    exact cleStepStep_eq_ite_isDPValid h_bnd placed f e

/-! #### §4.9 — Strong induction: `clERec ↔ #ValidPrefix` -/

@[simp] private lemma card_validPrefix_empty (pred : Array Nat) :
    Fintype.card (ValidPrefix pred n (∅ : Finset (Fin n))) = 1 := by
  classical
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨fun i => i.elim0, ?_, ?_, ?_⟩, ?_⟩
  · intro i j _; exact i.elim0
  · intro i; exact i.elim0
  · intro i; exact i.elim0
  · rintro ⟨f, _⟩
    apply Subtype.ext
    funext i
    exact i.elim0

private lemma maskSet_card_pos {n placed : ℕ}
    (hpos : 0 < placed) (h_placed : placed < (1 <<< n)) :
    0 < (maskSet n placed).card := by
  classical
  rw [Finset.card_pos]
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  -- All bits of placed at positions < n are zero (from emptiness),
  -- and at positions ≥ n by `placed < 2^n`. So `placed = 0`.
  have h_all : ∀ b, testBit' placed b = false := by
    intro b
    by_cases hbn : b < n
    · have hi_notmem : (⟨b, hbn⟩ : Fin n) ∉ maskSet n placed := by
        rw [h_empty]; exact Finset.notMem_empty _
      rw [mem_maskSet] at hi_notmem
      cases h : testBit' placed b with
      | true => exact absurd h hi_notmem
      | false => rfl
    · push_neg at hbn
      rw [testBit'_eq]
      apply Nat.testBit_lt_two_pow
      rw [one_shiftLeft_eq] at h_placed
      exact lt_of_lt_of_le h_placed (Nat.pow_le_pow_right (by omega) hbn)
  have hzero : placed = 0 := by
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.zero_testBit, ← testBit'_eq]
    exact h_all b
  omega

/-- **Strong induction**: `clERec` equals `#ValidPrefix` at every
`placed < 2^n` (under bit-boundedness of `pred`). -/
theorem clERec_eq_card_validPrefix {pred : Array Nat} {n : ℕ}
    (h_bnd : predBitsBoundedBy pred n)
    (placed : ℕ) (h_placed : placed < (1 <<< n)) :
    clERec pred n placed = Fintype.card (ValidPrefix pred n (maskSet n placed)) := by
  classical
  induction placed using Nat.strong_induction_on with
  | _ placed ih =>
    cases placed with
    | zero =>
      rw [clERec_zero, maskSet_zero, card_validPrefix_empty]
    | succ k =>
      rw [clERec_succ]
      rw [cleStep_eq_sum_dpValidSet h_bnd (k+1)]
      have hcard_pos : 0 < (maskSet n (k+1)).card :=
        maskSet_card_pos (Nat.succ_pos _) h_placed
      rw [card_validPrefix_eq_sum pred (maskSet n (k+1)) hcard_pos]
      apply Finset.sum_congr rfl
      intro e he_mem
      rw [mem_dpValidSet] at he_mem
      have hbit : testBit' (k+1) e.val = true := mem_maskSet.mp he_mem.1
      have h_xor_lt : (k+1) ^^^ bit e.val < k+1 := xor_bit_lt hbit
      -- Rewrite the array lookup as `clERec` at the smaller index.
      have h_F_get :
          (Array.ofFn (fun i : Fin (k+1) => clERec pred n i.val)).getD
              ((k+1) ^^^ bit e.val) 0 =
          clERec pred n ((k+1) ^^^ bit e.val) := by
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact h_xor_lt)]
        rw [Array.getElem_ofFn]
        rfl
      rw [h_F_get]
      -- `maskSet (k+1).erase e = maskSet ((k+1) XOR bit e.val)`.
      rw [← maskSet_xor_bit hbit]
      -- Apply IH at the smaller index.
      have h_xor_bnd : (k+1) ^^^ bit e.val < (1 <<< n) := lt_trans h_xor_lt h_placed
      exact ih ((k+1) ^^^ bit e.val) h_xor_lt h_xor_bnd

/-! #### §4.10 — `ValidPrefix univ ≃ LinearExt (Fin n) [predOrder]`

The Birkhoff-style bridge from full-prefix valid orderings to linear
extensions of `(Fin n, predOrder pred h)`.  Deferred — typeclass
plumbing for `predOrder` vs `Fin.instPartialOrder` on `Fin n` is
non-trivial: `Fin (Fintype.card (Fin n))` def-reduces to `Fin n`, so
the LE on the codomain of `LinearExt.monotone` can synthesize either
`Fin.instPartialOrder` or `predOrder pred h` depending on context. -/

end Case3Enum
end Step8
end OneThird
